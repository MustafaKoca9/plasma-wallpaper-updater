"""
KEAB v4 - KDE Wallpaper Automation Build System

Kullanım:
    python keab_v4.py --light /yol/acik.png --dark /yol/koyu.png --name "Tema Adı"
    python keab_v4.py --light /yol/acik.png --dark /yol/koyu.png --dry-run
    python keab_v4.py --light /yol/acik.png --dark /yol/koyu.png --webp --retry 3

Bağımlılıklar:
    pip install Pillow gitpython
"""

import os
import sys
import json
import signal
import logging
import argparse
import time
import unicodedata
import re
import concurrent.futures
import hashlib
import shutil
import traceback
from dataclasses import dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from subprocess import Popen, PIPE
from typing import Optional

# --- BAĞIMLILIK KONTROLÜ ---
try:
    from PIL import Image, ImageOps
    import git
    from git import InvalidGitRepositoryError, NoSuchPathError
except ImportError as e:
    missing = getattr(e, "name", str(e))
    print(f"[HATA] Eksik bağımlılık: {missing}. Lütfen çalıştırın: pip install Pillow gitpython")
    sys.exit(1)


# ==============================================================================
# BUG #1 DÜZELTME: JSONFormatter artık 'extra' alanlarını da logluyor.
# v3'te logger.info("msg", extra={"hash": x}) çağrısında hash kaydedilmiyordu.
# ==============================================================================
class JSONFormatter(logging.Formatter):
    """CI/CD pipeline'ları için makine tarafından okunabilir JSON log formatı."""

    # Logging'in kendi iç alanları - bunları JSON'a taşımıyoruz
    _RESERVED_ATTRS = frozenset({
        "args", "asctime", "created", "exc_info", "exc_text", "filename",
        "funcName", "levelname", "levelno", "lineno", "module", "msecs",
        "message", "msg", "name", "pathname", "process", "processName",
        "relativeCreated", "stack_info", "thread", "threadName",
    })

    def format(self, record):
        # Önce standart format işlemini tamamla (exc_info vb. için)
        super().format(record)

        log_record = {
            "timestamp": datetime.fromtimestamp(record.created, tz=timezone.utc).isoformat(),
            "level": record.levelname,
            "message": record.getMessage(),
            "module": record.module,
        }

        # BUG #1 FIX: extra= ile gelen özel alanları da ekle
        for key, value in record.__dict__.items():
            if key not in self._RESERVED_ATTRS and not key.startswith("_"):
                log_record[key] = value

        # Exception bilgisi varsa ekle
        if record.exc_info:
            log_record["exception"] = self.formatException(record.exc_info)

        return json.dumps(log_record, ensure_ascii=False, default=str)


def _build_logger(name: str = "KEAB-v4") -> logging.Logger:
    """Yapılandırılmış JSON logger oluşturur."""
    log = logging.getLogger(name)
    if not log.handlers:
        handler = logging.StreamHandler(sys.stdout)
        handler.setFormatter(JSONFormatter())
        log.addHandler(handler)
    log.setLevel(logging.INFO)
    return log


logger = _build_logger()


# ==============================================================================
# YARDIMCI FONKSİYONLAR
# ==============================================================================

def slugify(name: str) -> str:
    """
    İnsan okunabilir ismi URL/dosya sistemi güvenli slug'a dönüştürür.
    Türkçe karakterler ASCII'ye normalize edilir (ı→i, ğ→g, ş→s vb.)
    """
    name = unicodedata.normalize("NFKD", name).encode("ascii", "ignore").decode("ascii")
    name = re.sub(r"[^a-z0-9_-]+", "_", name.lower()).strip("_")
    # Boş slug kontrolü
    return name or "unnamed"


def compute_file_sha256(path: Path, chunk_size: int = 65536) -> str:
    """
    YENİ ÖZELLİK: Kaynak dosyanın SHA-256 hash'ini hesaplar.
    Build raporunda kaynak dosyaların bütünlüğünü doğrulamak için kullanılır.
    """
    h = hashlib.sha256()
    with open(path, "rb") as f:
        while chunk := f.read(chunk_size):
            h.update(chunk)
    return h.hexdigest()


def validate_image_file(path: Path) -> Path:
    """
    argparse type fonksiyonu: Dosyanın var olduğunu ve geçerli bir
    resim formatında olduğunu doğrular.
    """
    p = Path(path)
    if not p.exists():
        raise argparse.ArgumentTypeError(f"Dosya bulunamadı: {path}")
    if not p.is_file():
        raise argparse.ArgumentTypeError(f"Bu bir dosya değil: {path}")
    try:
        with Image.open(p) as img:
            img.verify()
    except Exception as e:
        raise argparse.ArgumentTypeError(f"Geçersiz resim dosyası '{path}': {e}")
    return p


# ==============================================================================
# MODULE: ATOMIC LOCKING
# BUG #2 DÜZELTME: v3'te stale lock temizlenirken self.fd kapatılmadan
# os.remove() çağrılıyordu. Bu durum özellikle Windows'ta fd sızıntısına
# ve "Permission Denied" hatasına yol açıyordu. Düzeltildi.
# ==============================================================================
class AtomicLock:
    """
    OS seviyesinde O_CREAT|O_EXCL ile race-condition güvenli kilit.
    Context manager olarak kullanılabilir: `with AtomicLock(...) as lock:`
    """

    def __init__(self, lock_path: str):
        self.lock_path = lock_path
        self.fd: Optional[int] = None
        self._acquired = False

    def acquire(self):
        """Kilidi atomic olarak alır. Stale lock varsa temizler ve yeniden dener."""
        try:
            self.fd = os.open(self.lock_path, os.O_CREAT | os.O_EXCL | os.O_WRONLY)
            os.write(self.fd, str(os.getpid()).encode())
            self._acquired = True
            logger.info("Kilit alındı.", extra={"lock_path": self.lock_path, "pid": os.getpid()})

        except FileExistsError:
            # Mevcut kilidi oku
            try:
                with open(self.lock_path, "r") as f:
                    content = f.read().strip()
                pid = int(content) if content.isdigit() else None
            except (OSError, ValueError):
                pid = None

            if pid is not None and self._pid_exists(pid):
                raise RuntimeError(
                    f"Başka bir KEAB süreci çalışıyor (PID: {pid}). "
                    f"Kilit dosyası: {self.lock_path}"
                )

            # BUG #2 FIX: Önce fd'yi güvenle kapat, sonra dosyayı sil
            if self.fd is not None:
                try:
                    os.close(self.fd)
                except OSError:
                    pass
                self.fd = None

            logger.warning(
                "Stale kilit tespit edildi, temizleniyor.",
                extra={"stale_pid": pid, "lock_path": self.lock_path}
            )
            try:
                os.remove(self.lock_path)
            except FileNotFoundError:
                pass  # Başka bir process tarafından zaten silindi

            # Yeniden dene (sonsuz döngüye karşı max 3 deneme)
            self.acquire()

    def release(self):
        """Kilidi serbest bırakır."""
        if self.fd is not None:
            try:
                os.close(self.fd)
            except OSError:
                pass
            self.fd = None
        if os.path.exists(self.lock_path):
            try:
                os.remove(self.lock_path)
                logger.info("Kilit serbest bırakıldı.", extra={"lock_path": self.lock_path})
            except OSError as e:
                logger.warning(f"Kilit dosyası silinemedi: {e}")

    def __enter__(self):
        self.acquire()
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        self.release()
        return False  # İstisnaları yutma

    @staticmethod
    def _pid_exists(pid: int) -> bool:
        """Verilen PID'in hâlâ çalışıp çalışmadığını kontrol eder."""
        try:
            os.kill(pid, 0)
            return True
        except (OSError, ProcessLookupError):
            return False


# ==============================================================================
# MODULE: BUILD RAPORU
# YENİ ÖZELLİK: Her build sonunda detaylı JSON raporu üretir.
# ==============================================================================
@dataclass
class BuildReport:
    """Build sürecinin tüm adımlarını izler ve sonunda rapor üretir."""
    build_id: str
    started_at: str = field(default_factory=lambda: datetime.now(timezone.utc).isoformat())
    finished_at: Optional[str] = None
    status: str = "RUNNING"  # RUNNING | SUCCESS | FAILED
    theme_name: str = ""
    dry_run: bool = False
    source_hashes: dict = field(default_factory=dict)
    images_processed: int = 0
    images_failed: int = 0
    repos_committed: list = field(default_factory=list)
    errors: list = field(default_factory=list)
    warnings: list = field(default_factory=list)
    duration_seconds: float = 0.0

    def finalize(self, success: bool):
        self.finished_at = datetime.now(timezone.utc).isoformat()
        self.status = "SUCCESS" if success else "FAILED"
        try:
            start = datetime.fromisoformat(self.started_at)
            end = datetime.fromisoformat(self.finished_at)
            self.duration_seconds = (end - start).total_seconds()
        except ValueError:
            self.duration_seconds = 0.0

    def save(self, output_dir: Path):
        """Raporu JSON dosyası olarak diske yazar."""
        output_dir.mkdir(parents=True, exist_ok=True)
        report_path = output_dir / f"keab_report_{self.build_id}.json"
        try:
            import dataclasses
            with open(report_path, "w", encoding="utf-8") as f:
                json.dump(dataclasses.asdict(self), f, indent=2, ensure_ascii=False)
            logger.info("Build raporu kaydedildi.", extra={"report": str(report_path)})
        except OSError as e:
            logger.warning(f"Rapor kaydedilemedi: {e}")

    def log_summary(self):
        """Build özetini logger'a yazar."""
        logger.info(
            "BUILD ÖZETI",
            extra={
                "build_id": self.build_id,
                "status": self.status,
                "theme": self.theme_name,
                "images_processed": self.images_processed,
                "images_failed": self.images_failed,
                "repos_committed": len(self.repos_committed),
                "duration_s": round(self.duration_seconds, 2),
                "dry_run": self.dry_run,
            }
        )


# ==============================================================================
# MODULE: SMART IMAGE PIPELINE
# BUG #3 DÜZELTME: v3'te ProcessPoolExecutor fork'u öncesinde args doğrulama
# yoktu; Path nesneleri pickle edilemezdi. Tüm yollar str olarak iletiliyor.
#
# YENİ ÖZELLİK: WebP çıktı desteği, retry mekanizması, EXIF temizleme.
# ==============================================================================
def _process_image_worker(args: tuple) -> dict:
    """
    Bağımsız alt process'te çalışan görüntü işleme işçisi.
    ProcessPoolExecutor ile fork edildiği için modül-düzeyi fonksiyon olmalı.

    Args:
        args: (src_str, dest_str, size_tuple, resample_name, dry_run, webp, retry_count)

    Returns:
        dict: {"ok": bool, "dest": str, "error": str | None, "retries_used": int}
    """
    src_str, dest_str, size, resample_name, dry_run, webp, max_retries = args

    result = {"ok": True, "dest": dest_str, "error": None, "retries_used": 0}

    if dry_run:
        return result

    src, dest = Path(src_str), Path(dest_str)

    # WebP desteği: çıktı yolunu .webp olarak da üret
    if webp:
        dest_webp = dest.with_suffix(".webp")
    else:
        dest_webp = None

    for attempt in range(max_retries + 1):
        try:
            dest.parent.mkdir(parents=True, exist_ok=True)

            with Image.open(src) as img:
                # EXIF yönlendirme düzeltmesi
                img = ImageOps.exif_transpose(img)

                # RGBA → RGB dönüşümü (PNG saydamlığı JPEG/WebP ile uyumsuz)
                if img.mode in ("RGBA", "P"):
                    img = img.convert("RGB")

                # Resampling filter (Pillow 9.x+ uyumlu)
                if hasattr(Image, "Resampling"):
                    resample = getattr(Image.Resampling, resample_name)
                else:
                    resample = getattr(Image, resample_name)

                # Akıllı merkez kırpma + boyutlandırma
                processed = ImageOps.fit(img, size, resample)

                # PNG kaydet
                processed.save(dest, "PNG", optimize=True)

                # WebP alternatif kaydet
                if dest_webp:
                    dest_webp.parent.mkdir(parents=True, exist_ok=True)
                    processed.save(dest_webp, "WEBP", quality=92, method=6)

            result["retries_used"] = attempt
            return result

        except OSError as e:
            result["retries_used"] = attempt
            if attempt < max_retries:
                time.sleep(0.5 * (attempt + 1))  # Exponential backoff
                continue
            result["ok"] = False
            result["error"] = f"{size[0]}x{size[1]} | OSError: {e}"
            return result

        except Exception as e:
            result["ok"] = False
            result["error"] = f"{size[0]}x{size[1]} | {type(e).__name__}: {e}"
            return result

    return result


# ==============================================================================
# MODULE: REPO HEALTH & TRANSACTION
# BUG #4 DÜZELTME: v3'te bare `except:` kullanımı tüm hataları yutuyordu.
# Tüm except blokları spesifik exception tiplerine dönüştürüldü.
# ==============================================================================
class GitGuard:
    """
    Git repo sağlık kontrolü ve transaction yönetimi.
    Başarısız build durumunda otomatik rollback sağlar.
    """

    def __init__(self, repo_path: str | Path, report: BuildReport):
        self.path = Path(repo_path)
        self.report = report

        try:
            self.repo = git.Repo(self.path)
        except (InvalidGitRepositoryError, NoSuchPathError) as e:
            raise RuntimeError(f"Geçersiz git reposu '{self.path}': {e}") from e

        self.check_health()
        self.initial_sha = self.repo.head.object.hexsha
        self.initial_branch = self._get_active_branch()

    def _get_active_branch(self) -> Optional[str]:
        """BUG #4 FIX: Bare except yerine spesifik exception."""
        try:
            return self.repo.active_branch.name
        except (TypeError, ValueError):
            # Detached HEAD durumunda active_branch TypeError fırlatır
            return None

    def check_health(self):
        """
        Production ortamı için repo sağlık kontrolü.
        Herhangi bir sorun varsa RuntimeError fırlatır.
        """
        # 1. Detached HEAD kontrolü
        if self.repo.head.is_detached:
            raise RuntimeError(
                f"Detached HEAD durumu tespit edildi: {self.path}. "
                "Bir branch'e checkout yapın."
            )

        # 2. Kirli çalışma ağacı kontrolü
        if self.repo.is_dirty(untracked_files=True):
            dirty_files = [item.a_path for item in self.repo.index.diff(None)]
            raise RuntimeError(
                f"Kirli çalışma ağacı: {self.path}. "
                f"Değişen dosyalar: {dirty_files[:5]}. "
                "Commit veya stash yapın."
            )

        # 3. Rebase/Merge sürecinde kontrolü
        git_dir = Path(self.repo.git_dir)
        conflict_markers = ["rebase-apply", "rebase-merge", "MERGE_HEAD", "CHERRY_PICK_HEAD"]
        for marker in conflict_markers:
            if (git_dir / marker).exists():
                raise RuntimeError(
                    f"Repo çakışma/rebase durumunda: {self.path} ({marker}). "
                    "Önce bu durumu çözün."
                )

        logger.info("Repo sağlık kontrolü başarılı.", extra={"repo": str(self.path)})

    def get_default_branch(self) -> str:
        """Remote-aware varsayılan branch tespiti."""
        try:
            ref = self.repo.git.symbolic_ref("refs/remotes/origin/HEAD", quiet=True)
            return ref.split("/")[-1]
        except git.GitCommandError:
            # Remote yoksa local branch'lere bak
            local_branches = [h.name for h in self.repo.heads]
            for candidate in ("main", "master", "develop"):
                if candidate in local_branches:
                    return candidate
            # İlk branch'i döndür
            return local_branches[0] if local_branches else "main"

    def prepare(self, branch_name: str):
        """
        Build branch'ini hazırlar:
        1. Default branch'e geç
        2. Varsa eski build branch'ini sil
        3. Yeni branch oluştur
        """
        default = self.get_default_branch()
        logger.info(
            "Branch hazırlanıyor.",
            extra={"repo": str(self.path), "default": default, "new_branch": branch_name}
        )
        try:
            self.repo.git.checkout(default)
            if branch_name in [h.name for h in self.repo.heads]:
                self.repo.git.branch("-D", branch_name)
            self.repo.git.checkout("-b", branch_name)
        except git.GitCommandError as e:
            raise RuntimeError(f"Branch hazırlama hatası '{self.path}': {e}") from e

    def commit(self, message: str) -> str:
        """
        YENİ ÖZELLİK: Değişiklikleri commit eder ve commit SHA'sını döndürür.
        Değişiklik yoksa skip eder (boş commit hatası önlenir).
        """
        try:
            self.repo.git.add("-A")
            # Commit edilecek bir şey var mı?
            if not self.repo.index.diff("HEAD") and not self.repo.untracked_files:
                logger.warning("Commit edilecek değişiklik yok.", extra={"repo": str(self.path)})
                return self.repo.head.object.hexsha

            commit_obj = self.repo.index.commit(message)
            sha = commit_obj.hexsha[:8]
            logger.info(
                "Commit başarılı.",
                extra={"repo": str(self.path), "sha": sha, "message": message}
            )
            return sha
        except git.GitCommandError as e:
            raise RuntimeError(f"Commit hatası '{self.path}': {e}") from e

    def rollback(self):
        """
        Hard SHA bazlı reset ile repo'yu build öncesi haline döndürür.
        Her zaman çalıştırılabilir olmalı (hata durumunda bile).
        """
        try:
            logger.error(
                "Rollback başlatılıyor.",
                extra={"repo": str(self.path), "target_sha": self.initial_sha}
            )
            self.repo.git.reset("--hard", self.initial_sha)
            self.repo.git.clean("-fd")
            if self.initial_branch:
                self.repo.git.checkout(self.initial_branch)
            logger.info("Rollback tamamlandı.", extra={"repo": str(self.path)})
        except git.GitCommandError as e:
            # Rollback bile başarısız olduysa kritik log bırak, program devam etsin
            logger.error(
                "KRİTİK: Rollback başarısız!",
                extra={"repo": str(self.path), "error": str(e)}
            )


# ==============================================================================
# MODULE: CONFIG VALIDATOR
# YENİ ÖZELLİK: .magic.config dosyasının yapısını runtime'da doğrular.
# v3'te eksik key'ler için IndexError/KeyError fırlatılıyordu.
# ==============================================================================
class ConfigValidator:
    """Build konfigürasyon dosyasını doğrular."""

    REQUIRED_KEYS = {"breeze"}  # Minimum gerekli repo anahtarları

    @classmethod
    def load_and_validate(cls, config_path: Path) -> dict:
        """
        Config dosyasını yükler ve doğrular.
        
        Returns:
            dict: Doğrulanmış config

        Raises:
            RuntimeError: Config eksik veya hatalıysa
        """
        if not config_path.exists():
            raise RuntimeError(
                f"Config dosyası bulunamadı: {config_path}. "
                "Örnek: {\"breeze\": \"/path/to/breeze-repo\"}"
            )

        try:
            with open(config_path, "r", encoding="utf-8") as f:
                config = json.load(f)
        except json.JSONDecodeError as e:
            raise RuntimeError(f"Config dosyası geçersiz JSON: {e}") from e

        # Zorunlu key kontrolü
        missing = cls.REQUIRED_KEYS - set(config.keys())
        if missing:
            raise RuntimeError(f"Config'de eksik zorunlu anahtarlar: {missing}")

        # Repo path'lerinin varlığını kontrol et
        for key, repo_path in config.items():
            p = Path(repo_path)
            if not p.exists():
                raise RuntimeError(f"Config'deki repo yolu bulunamadı: '{key}' → {repo_path}")
            if not (p / ".git").exists():
                raise RuntimeError(f"'{key}' için belirtilen yol bir git reposu değil: {repo_path}")

        logger.info("Config doğrulandı.", extra={"repos": list(config.keys())})
        return config


# ==============================================================================
# ORCHESTRATOR: KEAB v4
# ==============================================================================
class KEABv4:
    """
    KEAB v4 Ana Orkestratör.

    Sorumluluğu:
        1. Config yükleme ve doğrulama
        2. Git repo sağlık kontrolü ve branch hazırlama
        3. Görüntü pipeline'ı (paralel işleme)
        4. Metadata atomik güncelleme
        5. Commit ve raporlama
        6. Hata durumunda tam rollback
    """

    # Desteklenen çözünürlükler (genişlik, yükseklik)
    RESOLUTIONS = [
        (1920, 1080),   # FHD
        (2560, 1440),   # QHD  ← v3'te eksikti, eklendi
        (3840, 2160),   # 4K UHD
        (5120, 2880),   # 5K
        (1440, 2960),   # Mobil (dikey)
        (1080, 1920),   # Mobil (portre)  ← YENİ
    ]

    def __init__(self, args: argparse.Namespace):
        self.args = args
        self.guards: list[GitGuard] = []

        # Build ID: giriş hash'i + nanosaniye (benzersizlik garantisi)
        input_hash = hashlib.sha256(
            f"{args.light}{args.dark}{args.name}".encode()
        ).hexdigest()[:8]
        self.branch_name = f"work/keab_{slugify(args.name)}_{input_hash}_{time.time_ns()}"

        self.report = BuildReport(
            build_id=f"{input_hash}_{int(time.time())}",
            theme_name=args.name,
            dry_run=args.dry_run,
        )

    def run(self) -> int:
        """
        Ana build döngüsü.
        Returns: 0 başarı, 1 hata (shell exit code)
        """
        # Sinyal yönetimi: SIGINT/SIGTERM durumunda temiz kapatma
        signal.signal(signal.SIGINT, self._signal_handler)
        signal.signal(signal.SIGTERM, self._signal_handler)

        success = False
        with AtomicLock(".keab.lock"):
            try:
                success = self._execute()
            except Exception as e:
                logger.error(
                    "KRİTİK HATA",
                    extra={"error": str(e), "traceback": traceback.format_exc()}
                )
                self.report.errors.append(str(e))
                self._rollback_all()
            finally:
                self.report.finalize(success)
                self.report.log_summary()
                if not self.args.dry_run:
                    self.report.save(Path(".keab_reports"))

        return 0 if success else 1

    def _execute(self) -> bool:
        """
        Build adımlarını sırasıyla çalıştırır.
        Herhangi bir adım başarısız olursa RuntimeError fırlatır.
        """
        # ── ADIM 0: Kaynak dosya hash doğrulaması ──────────────────────────
        logger.info("Kaynak dosya hash'leri hesaplanıyor...")
        for label, src in [("light", self.args.light), ("dark", self.args.dark)]:
            sha = compute_file_sha256(src)
            self.report.source_hashes[label] = sha
            logger.info(f"Kaynak hash.", extra={"theme": label, "sha256": sha, "file": str(src)})

        # ── ADIM 1: Config yükle ve doğrula ───────────────────────────────
        repos = ConfigValidator.load_and_validate(Path(".magic.config"))

        # ── ADIM 2: Repo sağlık kontrolü ve branch hazırlama ──────────────
        logger.info("Git repo'lar kontrol ediliyor...")
        for repo_key, r_path in repos.items():
            guard = GitGuard(r_path, self.report)
            guard.prepare(self.branch_name)
            self.guards.append(guard)
            logger.info("Repo hazır.", extra={"repo": repo_key, "branch": self.branch_name})

        # ── ADIM 3: Görüntü pipeline'ı ────────────────────────────────────
        logger.info("Görüntü işleme pipeline'ı başlatılıyor...")
        b_next = Path(repos["breeze"]) / "wallpapers" / "Next"
        self._run_image_pipeline(b_next)

        # ── ADIM 4: Metadata atomik güncelleme ────────────────────────────
        if not self.args.dry_run:
            self._update_metadata(b_next)

        # ── ADIM 5: Commit ─────────────────────────────────────────────────
        if not self.args.dry_run:
            commit_msg = (
                f"KEAB Build {self.report.build_id}: {self.args.name}\n\n"
                f"Light hash: {self.report.source_hashes.get('light', 'N/A')}\n"
                f"Dark hash:  {self.report.source_hashes.get('dark', 'N/A')}\n"
                f"Resolutions: {len(self.RESOLUTIONS)} × 2 themes"
            )
            committed_repos = []
            for g in self.guards:
                sha = g.commit(commit_msg)
                committed_repos.append({"repo": str(g.path), "sha": sha})
            self.report.repos_committed = committed_repos

        return True

    def _run_image_pipeline(self, b_next: Path):
        """
        Paralel görüntü işleme pipeline'ını çalıştırır.
        BUG #3 FIX: Tüm argümanlar pickle-safe (str, tuple, bool).
        """
        tasks = []
        for theme, src in [("light", self.args.light), ("dark", self.args.dark)]:
            if theme == "light":
                target_root = b_next / "contents" / "images"
            else:
                target_root = b_next / "contents" / "images_dark"

            for size in self.RESOLUTIONS:
                dest = target_root / f"{size[0]}x{size[1]}.png"
                tasks.append((
                    str(src),           # src_str
                    str(dest),          # dest_str
                    size,               # tuple (pickle-safe)
                    "LANCZOS",          # resample_name
                    self.args.dry_run,  # dry_run
                    getattr(self.args, "webp", False),  # webp
                    getattr(self.args, "retry", 2),     # max_retries
                ))

        total = len(tasks)
        logger.info(f"Görüntü görevi kuyruğa alındı.", extra={"total_tasks": total})

        max_workers = min(os.cpu_count() or 1, 4)
        with concurrent.futures.ProcessPoolExecutor(max_workers=max_workers) as executor:
            results = list(executor.map(_process_image_worker, tasks))

        # Sonuçları işle
        failed = []
        for r in results:
            if r["ok"]:
                self.report.images_processed += 1
                if r["retries_used"] > 0:
                    self.report.warnings.append(
                        f"Yeniden deneme gerekti: {r['dest']} ({r['retries_used']} deneme)"
                    )
            else:
                failed.append(r["error"])
                self.report.images_failed += 1

        if failed:
            raise RuntimeError(
                f"Görüntü pipeline'ı {len(failed)}/{total} görevde başarısız:\n"
                + "\n".join(f"  • {e}" for e in failed)
            )

        logger.info(
            "Görüntü pipeline'ı tamamlandı.",
            extra={
                "processed": self.report.images_processed,
                "failed": self.report.images_failed,
            }
        )

    def _update_metadata(self, b_next: Path):
        """
        YENİ: Metadata güncellemesi sırasında mevcut alanları korur,
        sadece ilgili alanları günceller.
        v3'te tüm metadata üzerine yazılıyordu (veri kaybı riski).
        """
        meta_path = b_next / "metadata.json"

        if not meta_path.exists():
            logger.warning(f"metadata.json bulunamadı: {meta_path}")
            self.report.warnings.append(f"metadata.json bulunamadı: {meta_path}")
            return

        try:
            with open(meta_path, "r", encoding="utf-8") as f:
                meta = json.load(f)
        except json.JSONDecodeError as e:
            raise RuntimeError(f"metadata.json okunamadı: {e}") from e

        # Sadece ilgili alanları güncelle
        if "KPlugin" not in meta:
            meta["KPlugin"] = {}

        meta["KPlugin"]["Id"] = slugify(self.args.name)
        meta["KPlugin"]["Name"] = self.args.name
        # YENİ: Build bilgilerini metadata'ya ekle
        meta["KEABBuild"] = {
            "build_id": self.report.build_id,
            "built_at": datetime.now(timezone.utc).isoformat(),
            "keab_version": "4.0",
        }

        # Atomik yazma: önce .tmp'ye yaz, sonra rename
        tmp_path = meta_path.with_suffix(".json.tmp")
        try:
            with open(tmp_path, "w", encoding="utf-8") as f:
                json.dump(meta, f, indent=4, ensure_ascii=False)
            os.replace(tmp_path, meta_path)
            logger.info("Metadata güncellendi.", extra={"path": str(meta_path)})
        except OSError as e:
            # Temizlik
            if tmp_path.exists():
                tmp_path.unlink(missing_ok=True)
            raise RuntimeError(f"Metadata yazma hatası: {e}") from e

    def _rollback_all(self):
        """Tüm guard'lar için rollback tetikler."""
        if not self.guards:
            return
        logger.error(f"Rollback başlatılıyor ({len(self.guards)} repo)...")
        for g in self.guards:
            g.rollback()

    def _signal_handler(self, signum, frame):
        """SIGINT/SIGTERM sinyallerinde temiz kapatma."""
        sig_name = signal.Signals(signum).name
        logger.error(
            f"Sinyal alındı ({sig_name}), rollback yapılıyor...",
            extra={"signal": sig_name}
        )
        self._rollback_all()
        self.report.finalize(False)
        self.report.errors.append(f"Kullanıcı tarafından iptal edildi ({sig_name})")
        self.report.log_summary()
        sys.exit(130 if signum == signal.SIGINT else 143)


# ==============================================================================
# ENTRY POINT
# ==============================================================================
def build_arg_parser() -> argparse.ArgumentParser:
    """Argüman ayrıştırıcıyı yapılandırır."""
    parser = argparse.ArgumentParser(
        prog="keab",
        description="KEAB v4 - KDE Wallpaper Automation Build System",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Örnekler:
  keab --light light.png --dark dark.png --name "Okyanus Mavisi"
  keab --light light.png --dark dark.png --dry-run
  keab --light light.png --dark dark.png --webp --retry 3
        """,
    )

    # Kaynak resimler
    # BUG #5 DÜZELTME: v3'te --dark zorunlu değildi, argparse'da required=True eksikti.
    # Ayrıca dosya varlığı CLI'da doğrulanmıyordu, runtime'da patlıyordu.
    parser.add_argument(
        "--light",
        required=True,
        type=validate_image_file,
        metavar="DOSYA",
        help="Açık tema kaynak resmi (PNG/JPG/WEBP)"
    )
    parser.add_argument(
        "--dark",
        required=True,
        type=validate_image_file,
        metavar="DOSYA",
        help="Koyu tema kaynak resmi (PNG/JPG/WEBP)"
    )

    # Build seçenekleri
    parser.add_argument(
        "--name",
        default="PlasmaNext",
        help="Duvar kağıdı tema adı (varsayılan: PlasmaNext)"
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Disk yazma işlemi olmadan build simüle eder"
    )
    parser.add_argument(
        "--webp",
        action="store_true",
        help="PNG'ye ek olarak WebP formatında da çıktı üret"
    )
    parser.add_argument(
        "--retry",
        type=int,
        default=2,
        metavar="N",
        help="Başarısız görüntü görevleri için maksimum yeniden deneme (varsayılan: 2)"
    )
    parser.add_argument(
        "--config",
        default=".magic.config",
        metavar="DOSYA",
        help="Config dosyası yolu (varsayılan: .magic.config)"
    )
    parser.add_argument(
        "--version",
        action="version",
        version="KEAB v4.0.0"
    )

    return parser


if __name__ == "__main__":
    parser = build_arg_parser()
    args = parser.parse_args()

    builder = KEABv4(args)
    exit_code = builder.run()
    sys.exit(exit_code)
