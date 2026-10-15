#!/usr/bin/env python3
"""
notgit.py  –  A local-only git clone.

Supported commands
  init [--initial-branch <name>]  Initialize a repository
  clone [--branch <name>] [--no-checkout] [--single-branch] [--no-tags] <src> [<dest>]
  import-git <git-repo> [<dest>]  Convert a .git repository into a new .notgit repo
  add [-A] [-p] <path>…  | add .   Stage files
  rm [--cached] [--force] [--dry-run] <path>…  Remove files from index/disk
  mv [-f] <source>… <dest>  Move or rename tracked files
  commit -m <msg> [--amend] [--dry-run] [--allow-empty]  Commit staged changes
  status [--short|--porcelain[=2]] [--ignored] [--show-stash]  Show status
  log [--oneline] [--max-count N] [--merges|--no-merges] [--stat|--patch]
  diff [--staged] [--stat|--name-only|--name-status|--check|--word-diff]
       [--exit-code|--quiet] [<rev> [<rev>]] [<path>…]  Show changes
  show [--stat|--name-only|--name-status|--no-patch] [<rev>]  Show an object
  rev-parse [opts] [<rev>…]  Parse revisions / show repository paths
  branch [name] [-d|-D|-m|-M] [--merged|--no-merged]   List / create / delete / rename branches
  checkout [-b|-B|--detach|--orphan] [--force] <tgt>  Switch branches/commits
  checkout [<rev>] -- <path>…    Restore paths from the index or <rev>
  reset [--soft|--mixed|--hard|--merge|--keep|-p] [<rev>] [-- <file>…]
  restore [--source <rev>] [--staged] [--worktree] [--patch] <file>…
  revert [--mainline N] [--no-commit|--continue|--abort|--skip] [<commit>]
  merge [--no-commit|--squash|--ff-only|--no-ff|--continue|--abort] [<branch>]
  tag [-a] [-m msg] [-d|-f] [<name> [<rev>]]  Create / list / delete tags
  config <section.key> [value]  Read / write config values
  stash [push -u|pop [stash@{N}]|apply [stash@{N}]|drop [stash@{N}]|show [stash@{N}]|list|clear]  Save and restore dirty state
  ls [<path>…]                  List tracked files with last-add and last-commit dates
  versions <file>                Write every committed version of a file
  grep [-n] [-i] [-l|-L] [-w] [-F] [-e] [--cached] <pattern> [<rev>] [<path>…]  Search tracked files
"""

import os
import posixpath
import sys
import re
import json
import glob
import hashlib
import shutil
import time
import argparse
import difflib
import fnmatch
import getpass
import socket
import io
import contextlib
import shlex
import subprocess
import zlib
import struct
import stat
import errno
import tempfile
import heapq
from collections import OrderedDict, deque
from functools import lru_cache

try:
    import fcntl
except ImportError:  # pragma: no cover - Windows fallback
    fcntl = None

try:
    import msvcrt
except ImportError:  # pragma: no cover - POSIX
    msvcrt = None

# ── directory layout ────────────────────────────────────────────────────────

VCS_DIR    = ".notgit"
OBJECTS_DIR = os.path.join(VCS_DIR, "objects")
REFS_DIR    = os.path.join(VCS_DIR, "refs")
HEADS_DIR   = os.path.join(REFS_DIR, "heads")
TAGS_DIR    = os.path.join(REFS_DIR, "tags")
INDEX_FILE  = os.path.join(VCS_DIR, "index")
HEAD_FILE   = os.path.join(VCS_DIR, "HEAD")
CONFIG_FILE = os.path.join(VCS_DIR, "config")
STASH_FILE       = os.path.join(VCS_DIR, "stash")
INDEX_TIMES_FILE = os.path.join(VCS_DIR, "index_times")
MERGE_HEAD_FILE  = os.path.join(VCS_DIR, "MERGE_HEAD")
MERGE_MSG_FILE   = os.path.join(VCS_DIR, "MERGE_MSG")
MERGE_CONFLICTS_FILE = os.path.join(VCS_DIR, "MERGE_CONFLICTS")
REVERT_HEAD_FILE = os.path.join(VCS_DIR, "REVERT_HEAD")
REVERT_MSG_FILE  = os.path.join(VCS_DIR, "REVERT_MSG")
REVERT_CONFLICTS_FILE = os.path.join(VCS_DIR, "REVERT_CONFLICTS")
TRANSACTION_FILE = os.path.join(VCS_DIR, "TRANSACTION")
IGNORE_FILE = ".notgitignore"          # like .gitignore, lives in work-tree root
MAX_IGNORE_FILE_BYTES = 1024 * 1024
MAX_GIT_OBJECT_BYTES = 256 * 1024 * 1024
MAX_GIT_DELTA_CHAIN = 10000
MAX_DELTA_BASE_CACHE_BYTES = 64 * 1024 * 1024
IO_CHUNK_SIZE = 1024 * 1024

_INVOCATION_CWD = os.getcwd()
_WORKTREE_ROOT = None
_STDOUT_IS_TTY_OVERRIDE = None
_WARNED_SYMLINKS: set = set()


# ── colour helpers ───────────────────────────────────────────────────────────

def _colour(code, text):
    is_tty = (sys.stdout.isatty() if _STDOUT_IS_TTY_OVERRIDE is None
              else _STDOUT_IS_TTY_OVERRIDE)
    if is_tty and os.name != "nt":
        return f"\033[{code}m{text}\033[0m"
    return text

red    = lambda t: _colour("31", t)
green  = lambda t: _colour("32", t)
yellow = lambda t: _colour("33", t)
cyan   = lambda t: _colour("36", t)


# ── basic I/O ────────────────────────────────────────────────────────────────

def _fsync_directory(path: str):
    """Persist directory-entry changes made by rename/unlink."""
    if os.name == "nt":  # Windows cannot fsync an opened directory.
        return
    flags = os.O_RDONLY | getattr(os, "O_DIRECTORY", 0)
    fd = os.open(path or ".", flags)
    try:
        try:
            os.fsync(fd)
        except OSError as e:
            if e.errno not in (errno.EBADF, errno.EINVAL, errno.ENOTSUP):
                raise
    finally:
        os.close(fd)


def _durable_unlink(path: str, *, missing_ok=True):
    try:
        os.unlink(path)
    except FileNotFoundError:
        if missing_ok:
            return
        raise
    _fsync_directory(os.path.dirname(path) or ".")


def _atomic_write_text(path: str, text: str):
    """Write via temp file + rename so refs/index never end up half-written."""
    directory = os.path.dirname(path) or "."
    os.makedirs(directory, exist_ok=True)
    fd, tmp = tempfile.mkstemp(prefix=".notgit-write-", dir=directory)
    stream = None
    try:
        stream = os.fdopen(fd, "w", encoding="utf-8")
        fd = None
        with stream as f:
            stream = None
            f.write(text)
            f.flush()
            os.fsync(f.fileno())
        os.replace(tmp, path)
        tmp = None
        _fsync_directory(directory)
    finally:
        if stream is not None:
            stream.close()
        if fd is not None:
            os.close(fd)
        if tmp is not None:
            try:
                os.unlink(tmp)
            except OSError:
                pass

def write_json(path, obj):
    _atomic_write_text(path, json.dumps(obj, indent=2))

def read_json(path, default=None):
    if not os.path.exists(path):
        return default
    try:
        with open(path, "r", encoding="utf-8") as f:
            return json.load(f)
    except json.JSONDecodeError as e:
        _die(f"could not parse {path}: {e}")
    except OSError as e:
        _die(f"could not read {path}: {e}")

def _require_json_type(path: str, value, expected_type, description: str):
    if not isinstance(value, expected_type):
        _die(f"invalid {description} in {path}")
    return value

def _find_repo_root(start: str) -> str | None:
    cur = os.path.abspath(start)
    while True:
        if os.path.isdir(os.path.join(cur, VCS_DIR)):
            return cur
        parent = os.path.dirname(cur)
        if parent == cur:
            return None
        cur = parent

def repo_exists():
    return _find_repo_root(os.getcwd()) is not None

def ensure_repo():
    global _WORKTREE_ROOT
    root = _find_repo_root(os.getcwd())
    if not root:
        _die(f"not a notgit repository (or any parent directory): {VCS_DIR}")
    _WORKTREE_ROOT = root
    os.chdir(root)


@contextlib.contextmanager
def _repository_lock_at(root: str):
    """Hold an advisory repository lock that dies with its descriptor."""
    lock_path = os.path.join(root, VCS_DIR, "LOCK")
    os.makedirs(os.path.dirname(lock_path), exist_ok=True)
    fd = os.open(lock_path, os.O_RDWR | os.O_CREAT, 0o600)
    locked = False
    try:
        if fcntl is not None:
            try:
                fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
                locked = True
            except BlockingIOError:
                _die("another notgit process is modifying this repository")
        elif msvcrt is not None:  # pragma: no cover - Windows
            os.lseek(fd, 0, os.SEEK_SET)
            if os.fstat(fd).st_size == 0:
                os.write(fd, b"\0")
            os.lseek(fd, 0, os.SEEK_SET)
            try:
                msvcrt.locking(fd, msvcrt.LK_NBLCK, 1)
                locked = True
            except OSError:
                _die("another notgit process is modifying this repository")
        os.ftruncate(fd, 0)
        os.write(fd, f"{os.getpid()}\n".encode("ascii"))
        os.fsync(fd)
        yield
    finally:
        try:
            if locked and fcntl is not None:
                fcntl.flock(fd, fcntl.LOCK_UN)
            elif locked and msvcrt is not None:  # pragma: no cover - Windows
                os.lseek(fd, 0, os.SEEK_SET)
                msvcrt.locking(fd, msvcrt.LK_UNLCK, 1)
        finally:
            os.close(fd)


@contextlib.contextmanager
def _repo_lock():
    """Serialize one repository-wide read/modify/write transaction."""
    root = _find_repo_root(os.getcwd())
    if not root:
        yield
        return
    with _repository_lock_at(root):
        _recover_repository_transaction(root)
        yield


def _contained_worktree_path(path: str) -> str:
    """Resolve the existing portion of a path and reject symlink escapes."""
    root = os.path.realpath(_WORKTREE_ROOT or os.getcwd())
    full = os.path.abspath(path if os.path.isabs(path) else os.path.join(root, path))
    if os.path.commonpath([root, full]) != root:
        _die(f"repository path escapes worktree: {path}")
    probe = full
    while not os.path.lexists(probe):
        parent = os.path.dirname(probe)
        if parent == probe:
            break
        probe = parent
    resolved = os.path.realpath(probe)
    if os.path.commonpath([root, resolved]) != root:
        _die(f"repository path escapes worktree through a symbolic link: {path}")
    return full

def normalize_pathspec(path: str) -> str:
    """Return a repo-root-relative path for an invocation-cwd-relative pathspec."""
    base = _INVOCATION_CWD
    root = os.path.abspath(_WORKTREE_ROOT or os.getcwd())
    full = os.path.abspath(path if os.path.isabs(path) else os.path.join(base, path))
    if os.path.commonpath([root, full]) != root:
        _die(f"pathspec '{path}' is outside repository")
    _contained_worktree_path(full)
    rel = os.path.relpath(full, root)
    return rel.replace("\\", "/")

def ensure_repo_relative_path(path: str):
    root = os.path.abspath(_WORKTREE_ROOT or os.getcwd())
    full = os.path.abspath(os.path.join(root, path))
    if os.path.commonpath([root, full]) != root:
        _die(f"repository path escapes worktree: {path}")
    _contained_worktree_path(full)

def _die(msg, code=128):
    print(f"fatal: {msg}", file=sys.stderr)
    sys.exit(code)

def _err(msg):
    print(f"error: {msg}", file=sys.stderr)


def _pager_command():
    pager = os.environ.get("GIT_PAGER") or os.environ.get("PAGER") or "less"
    if not pager:
        return None
    try:
        cmd = shlex.split(pager)
    except ValueError:
        return None
    if not cmd or cmd[0] == "cat" or not shutil.which(cmd[0]):
        return None
    return cmd


def _write_paged(text: str):
    if not text:
        return
    cmd = _pager_command()
    if not cmd:
        sys.stdout.write(text)
        return
    env = os.environ.copy()
    if os.path.basename(cmd[0]) == "less":
        env.setdefault("LESS", "FRX")
        if "-R" not in cmd and "-r" not in cmd:
            cmd = cmd + ["-R"]
    try:
        result = subprocess.run(cmd, input=text, text=True, env=env, check=False)
    except (BrokenPipeError, OSError):
        sys.stdout.write(text)
        return
    if result.returncode != 0:
        _err(f"pager exited with status {result.returncode}; writing output directly")
        sys.stdout.write(text)


def _run_with_pager(fn, args):
    global _STDOUT_IS_TTY_OVERRIDE
    if not sys.stdout.isatty():
        fn(args)
        return

    buf = io.StringIO()
    exit_code = None
    old_tty_override = _STDOUT_IS_TTY_OVERRIDE
    _STDOUT_IS_TTY_OVERRIDE = True
    try:
        with contextlib.redirect_stdout(buf):
            fn(args)
    except SystemExit as exc:
        exit_code = exc.code
    finally:
        _STDOUT_IS_TTY_OVERRIDE = old_tty_override

    _write_paged(buf.getvalue())
    if exit_code is not None:
        raise SystemExit(exit_code)


# ── object store ─────────────────────────────────────────────────────────────

def _sha1(data: bytes) -> str:
    return hashlib.sha1(data).hexdigest()

def hash_blob(data: bytes) -> str:
    """Return the OID a blob would get (same header as store_object uses)."""
    return _sha1(b"blob " + str(len(data)).encode() + b"\x00" + data)

def _open_worktree_file(path: str):
    """Open a regular work-tree file without blocking on FIFOs or devices."""
    flags = os.O_RDONLY | getattr(os, "O_BINARY", 0)
    flags |= getattr(os, "O_CLOEXEC", 0) | getattr(os, "O_NONBLOCK", 0)
    flags |= getattr(os, "O_NOFOLLOW", 0)
    fd = os.open(_contained_worktree_path(path), flags)
    try:
        file_stat = os.fstat(fd)
        if not stat.S_ISREG(file_stat.st_mode):
            raise OSError(errno.EINVAL, "not a regular file", path)
        stream = os.fdopen(fd, "rb")
    except:
        os.close(fd)
        raise
    return stream, file_stat

def _stream_blob(path: str, destination=None) -> str:
    """Hash a work-tree blob in bounded chunks, optionally copying its object."""
    source, initial_stat = _open_worktree_file(path)
    with source:
        header = f"blob {initial_stat.st_size}\0".encode()
        digest = hashlib.sha1()
        digest.update(header)
        if destination is not None:
            destination.write(header)

        remaining = initial_stat.st_size
        while remaining:
            chunk = source.read(min(IO_CHUNK_SIZE, remaining))
            if not chunk:
                raise OSError(errno.EIO, "file changed size while reading", path)
            digest.update(chunk)
            if destination is not None:
                destination.write(chunk)
            remaining -= len(chunk)

        if source.read(1):
            raise OSError(errno.EIO, "file changed size while reading", path)
        final_stat = os.fstat(source.fileno())
        if (final_stat.st_size != initial_stat.st_size
                or final_stat.st_mtime_ns != initial_stat.st_mtime_ns):
            raise OSError(errno.EIO, "file changed while reading", path)
    return digest.hexdigest()

def hash_blob_file(path: str) -> str:
    """Return a blob OID without retaining the complete file in memory."""
    return _stream_blob(path)

def store_blob_file(path: str) -> str:
    """Store a work-tree file as a blob using bounded, atomic passes."""
    # Hash first: re-adding content that is already stored must not pay for
    # a temporary copy and an fsync per file.
    known_oid = hash_blob_file(path)
    if os.path.exists(os.path.join(OBJECTS_DIR, known_oid[:2], known_oid[2:])):
        return known_oid
    os.makedirs(OBJECTS_DIR, exist_ok=True)
    fd, tmp = tempfile.mkstemp(prefix=".blob-", dir=OBJECTS_DIR)
    tmp_stream = None
    try:
        tmp_stream = os.fdopen(fd, "wb")
        fd = None
        with tmp_stream as destination:
            tmp_stream = None
            oid = _stream_blob(path, destination)
            destination.flush()
            os.fsync(destination.fileno())

        obj_dir = os.path.join(OBJECTS_DIR, oid[:2])
        os.makedirs(obj_dir, exist_ok=True)
        object_path = os.path.join(obj_dir, oid[2:])
        if os.path.exists(object_path):
            os.unlink(tmp)
        else:
            os.replace(tmp, object_path)
            _fsync_directory(obj_dir)
        tmp = None
        return oid
    finally:
        if tmp_stream is not None:
            tmp_stream.close()
        if fd is not None:
            os.close(fd)
        if tmp is not None:
            try:
                os.unlink(tmp)
            except OSError:
                pass

def store_object(obj_type: str, content: bytes) -> str:
    """Hash-object: write <type> <len>\0<content> and return the 40-char OID."""
    header = f"{obj_type} {len(content)}\0".encode()
    raw    = header + content
    oid    = _sha1(raw)
    prefix, suffix = oid[:2], oid[2:]
    obj_dir = os.path.join(OBJECTS_DIR, prefix)
    os.makedirs(obj_dir, exist_ok=True)
    path = os.path.join(obj_dir, suffix)
    if not os.path.exists(path):
        fd, tmp = tempfile.mkstemp(prefix=".object-", dir=obj_dir)
        stream = None
        try:
            stream = os.fdopen(fd, "wb")
            fd = None
            with stream as f:
                stream = None
                f.write(raw)
                f.flush()
                os.fsync(f.fileno())
            os.replace(tmp, path)
            tmp = None
            _fsync_directory(obj_dir)
        finally:
            if stream is not None:
                stream.close()
            if fd is not None:
                os.close(fd)
            if tmp is not None:
                try:
                    os.unlink(tmp)
                except OSError:
                    pass
    return oid

def _object_path(oid: str) -> str:
    if not isinstance(oid, str) or not re.fullmatch(r"[0-9a-f]{40}", oid):
        _die(f"invalid object id: {oid}")
    path = os.path.join(OBJECTS_DIR, oid[:2], oid[2:])
    if not os.path.exists(path):
        # backward-compat: flat layout from original myvcs
        path = os.path.join(OBJECTS_DIR, oid)
    if not os.path.exists(path):
        _die(f"object not found: {oid}")
    return path

def _parse_object_header(header: bytes, oid: str) -> tuple[str, int]:
    try:
        type_bytes, size_bytes = header.split(b" ", 1)
        obj_type = type_bytes.decode("ascii")
        declared_size = int(size_bytes.decode("ascii"))
    except (ValueError, UnicodeDecodeError):
        _die(f"object corrupt: {oid} (invalid header)")
    if obj_type not in {"blob", "tree", "commit", "tag"}:
        _die(f"object corrupt: {oid} (invalid type {obj_type!r})")
    return obj_type, declared_size

@lru_cache(maxsize=8192)
def read_object_type(oid: str) -> str:
    """Validate an object and return its type without retaining its content."""
    path = _object_path(oid)
    digest = hashlib.sha1()
    header = None
    content_size = 0
    try:
        with open(path, "rb") as f:
            first = f.read(IO_CHUNK_SIZE)
            digest.update(first)
            if b"\0" not in first:
                _die(f"object corrupt: {oid} (invalid header)")
            header, initial_content = first.split(b"\0", 1)
            content_size = len(initial_content)
            while True:
                chunk = f.read(IO_CHUNK_SIZE)
                if not chunk:
                    break
                digest.update(chunk)
                content_size += len(chunk)
    except OSError as e:
        _die(f"could not read object {oid}: {e}")
    if digest.hexdigest() != oid:
        _die(f"object corrupt: {oid} (hash mismatch)")
    obj_type, declared_size = _parse_object_header(header, oid)
    if declared_size != content_size:
        _die(f"object corrupt: {oid} (size mismatch)")
    return obj_type

def _read_object_uncached(oid: str):
    """Return (obj_type, content_bytes) for the given OID."""
    path = _object_path(oid)
    try:
        with open(path, "rb") as f:
            raw = f.read()
    except OSError as e:
        _die(f"could not read object {oid}: {e}")
    if _sha1(raw) != oid:
        _die(f"object corrupt: {oid} (hash mismatch)")
    try:
        header, content = raw.split(b"\0", 1)
        obj_type, declared_size = _parse_object_header(header, oid)
    except (ValueError, UnicodeDecodeError):
        _die(f"object corrupt: {oid} (invalid header)")
    if declared_size != len(content):
        _die(f"object corrupt: {oid} (size mismatch)")
    return obj_type, content


@lru_cache(maxsize=8192)
def _read_nonblob_object(oid: str):
    return _read_object_uncached(oid)


def read_object(oid: str):
    """Return an object without retaining blob payloads in the LRU cache."""
    if read_object_type(oid) == "blob":
        return _read_object_uncached(oid)
    return _read_nonblob_object(oid)


def _stream_blob_object(oid: str, destination):
    """Validate a stored blob while copying only its content in bounded chunks."""
    path = _object_path(oid)
    digest = hashlib.sha1()
    content_size = 0
    try:
        with open(path, "rb") as source:
            first = source.read(IO_CHUNK_SIZE)
            digest.update(first)
            if b"\0" not in first:
                _die(f"object corrupt: {oid} (invalid header)")
            header, content = first.split(b"\0", 1)
            obj_type, declared_size = _parse_object_header(header, oid)
            if obj_type != "blob":
                _die(f"expected blob object, got {obj_type}")
            destination.write(content)
            content_size += len(content)
            while True:
                chunk = source.read(IO_CHUNK_SIZE)
                if not chunk:
                    break
                digest.update(chunk)
                destination.write(chunk)
                content_size += len(chunk)
    except OSError as e:
        _die(f"could not read object {oid}: {e}")
    if digest.hexdigest() != oid:
        _die(f"object corrupt: {oid} (hash mismatch)")
    if declared_size != content_size:
        _die(f"object corrupt: {oid} (size mismatch)")

def find_objects(prefix: str) -> list:
    """Return all full OIDs whose hex starts with *prefix* (any length)."""
    hits = []
    if not os.path.isdir(OBJECTS_DIR):
        return hits
    # Fast path: a >=2-char prefix names exactly one subdir to scan.
    if len(prefix) >= 2:
        sub = prefix[:2]
        sub_dir = os.path.join(OBJECTS_DIR, sub)
        if os.path.isdir(sub_dir):
            tail = prefix[2:]
            for name in os.listdir(sub_dir):
                if name.startswith(tail):
                    hits.append(sub + name)
        # Also check the legacy flat layout at the top level.
        try:
            for entry in os.listdir(OBJECTS_DIR):
                if (entry.startswith(prefix)
                        and entry not in hits
                        and os.path.isfile(os.path.join(OBJECTS_DIR, entry))):
                    hits.append(entry)
        except OSError:
            pass
        return hits
    # Slow path: short prefix — must walk every 2-char dir + flat layer.
    for entry in os.listdir(OBJECTS_DIR):
        entry_path = os.path.join(OBJECTS_DIR, entry)
        if os.path.isdir(entry_path):
            for name in os.listdir(entry_path):
                oid = entry + name
                if oid.startswith(prefix):
                    hits.append(oid)
        elif os.path.isfile(entry_path):
            if entry.startswith(prefix) and entry not in hits:
                hits.append(entry)
    return hits


# ── config ───────────────────────────────────────────────────────────────────

def read_config():
    cfg = _require_json_type(CONFIG_FILE, read_json(CONFIG_FILE, {}), dict, "config")
    for section, values in cfg.items():
        if not isinstance(section, str) or not isinstance(values, dict):
            _die(f"invalid config section in {CONFIG_FILE}")
    return cfg

def write_config(cfg):
    write_json(CONFIG_FILE, cfg)

def get_author():
    cfg = read_config()
    name  = (cfg.get("user", {}).get("name")
             or os.environ.get("NOTGIT_AUTHOR_NAME")
             or getpass.getuser())
    email = (cfg.get("user", {}).get("email")
             or os.environ.get("NOTGIT_AUTHOR_EMAIL")
             or f"{getpass.getuser()}@{socket.gethostname()}")
    return name, email

def parse_timestamp(value: str) -> float:
    """Parse a small local-only subset of Git's date input.

    Date formats are tried before the epoch-seconds fallback so a bare year
    like "2024" means the year, not 2024 seconds past the epoch.
    """
    for fmt in ("%Y-%m-%d %H:%M:%S", "%Y-%m-%d %H:%M", "%Y-%m-%d", "%Y"):
        try:
            return time.mktime(time.strptime(value, fmt))
        except ValueError:
            continue
    try:
        return float(value)
    except ValueError:
        pass
    _die(f"invalid date '{value}'")


# ── HEAD / refs ──────────────────────────────────────────────────────────────

def init_head(branch_name="main"):
    os.makedirs(HEADS_DIR, exist_ok=True)
    os.makedirs(TAGS_DIR,  exist_ok=True)
    _atomic_write_text(HEAD_FILE, f"ref: refs/heads/{branch_name}")

def resolve_head():
    """Return ("ref", "refs/heads/<name>") or ("hash", "<oid>")."""
    if not os.path.exists(HEAD_FILE):
        return ("hash", "")
    with open(HEAD_FILE) as f:
        data = f.read().strip()
    if data.startswith("ref:"):
        return ("ref", data.split(" ", 1)[1].strip())
    return ("hash", data)

_OID_RE = re.compile(r"[0-9a-f]{40}")
_ABBREV_OID_RE = re.compile(r"[0-9a-f]{4,40}")


def _read_ref_file(path: str) -> str | None:
    """Return the OID stored in a ref file, or None for a missing/empty ref."""
    if not os.path.isfile(path):   # isfile guards against "." resolving to the dir
        return None
    with open(path) as f:
        oid = f.read().strip()
    if not oid:
        return None
    if not _OID_RE.fullmatch(oid):
        _die(f"corrupt ref {path}: invalid object id")
    return oid

def get_head_commit():
    kind, value = resolve_head()
    if kind == "hash":
        if value and not _OID_RE.fullmatch(value):
            _die(f"corrupt {HEAD_FILE}: invalid object id")
        return value or None
    return _read_ref_file(os.path.join(VCS_DIR, value))

def update_head(commit_oid: str):
    kind, value = resolve_head()
    if kind == "ref":
        _atomic_write_text(os.path.join(VCS_DIR, value), commit_oid)
    else:
        _atomic_write_text(HEAD_FILE, commit_oid)

def _head_update_path() -> str:
    kind, value = resolve_head()
    return os.path.join(VCS_DIR, value) if kind == "ref" else HEAD_FILE

def _merge_state_paths() -> tuple[str, str, str]:
    return (MERGE_HEAD_FILE, MERGE_MSG_FILE, MERGE_CONFLICTS_FILE)

def _revert_state_paths() -> tuple[str, str, str]:
    return (REVERT_HEAD_FILE, REVERT_MSG_FILE, REVERT_CONFLICTS_FILE)

def set_head_ref(branch_name: str):
    _atomic_write_text(HEAD_FILE, f"ref: refs/heads/{branch_name}")

def current_branch() -> str | None:
    kind, value = resolve_head()
    if kind == "ref" and value.startswith("refs/heads/"):
        return value[len("refs/heads/"):]
    return None          # detached HEAD

def get_branch_commit(name: str) -> str | None:
    if not _safe_ref_name(name):
        return None
    return _read_ref_file(os.path.join(HEADS_DIR, name))

def set_branch_commit(name: str, oid: str):
    _atomic_write_text(os.path.join(HEADS_DIR, name), oid)

def list_branches() -> list:
    return _list_ref_names(HEADS_DIR)

def list_tags() -> list:
    return _list_ref_names(TAGS_DIR)


def _list_ref_names(ref_dir: str) -> list:
    if not os.path.isdir(ref_dir):
        return []
    names = []
    for dirpath, _dirs, files in os.walk(ref_dir):
        for filename in files:
            full = os.path.join(dirpath, filename)
            names.append(os.path.relpath(full, ref_dir).replace(os.sep, "/"))
    return sorted(names)

def _ref_path_conflict(ref_dir: str, name: str) -> str | None:
    """Return an existing ref that prevents creating *name* (a/b vs a)."""
    parts = name.split("/")
    for i in range(1, len(parts)):
        prefix = "/".join(parts[:i])
        if os.path.isfile(os.path.join(ref_dir, prefix)):
            return prefix
    if os.path.isdir(os.path.join(ref_dir, name)):
        nested = _list_ref_names(os.path.join(ref_dir, name))
        return f"{name}/{nested[0]}" if nested else None
    return None

def _ensure_ref_creatable(ref_dir: str, name: str, kind: str):
    conflict = _ref_path_conflict(ref_dir, name)
    if conflict:
        prefix = "refs/heads" if kind == "branch" else "refs/tags"
        _die(f"cannot lock ref '{prefix}/{name}': '{prefix}/{conflict}' exists; "
             f"cannot create '{prefix}/{name}'")

def get_tag_commit(name: str) -> str | None:
    if not _safe_ref_name(name):
        return None
    oid = _read_ref_file(os.path.join(TAGS_DIR, name))
    if not oid:
        return None
    obj_type, content = read_object(oid)
    if obj_type == "tag":
        try:
            data = json.loads(content)
        except json.JSONDecodeError as e:
            _die(f"object corrupt: {oid} (invalid tag JSON: {e})")
        if not isinstance(data, dict):
            _die(f"object corrupt: {oid} (tag is not an object)")
        target = data.get("object")
        if not isinstance(target, str) or not _OID_RE.fullmatch(target):
            _die(f"object corrupt: {oid} (invalid tag target)")
        return target
    return oid


# ── revision resolution ──────────────────────────────────────────────────────

_REV_ANCESTRY_RE = re.compile(r"(.+?)((?:[~^]\d*)+)")


def resolve_rev(rev: str | None) -> str | None:
    """Resolve a rev, including ancestry suffixes like HEAD~2, main^, or
    abc123^2~1, and <rev>:<path> or :<path> object lookups, to a full OID."""
    if rev and ":" in rev:
        return _resolve_rev_path(*rev.split(":", 1))
    m = _REV_ANCESTRY_RE.fullmatch(rev) if rev else None
    if not m:
        return _resolve_base_rev(rev)
    oid = _resolve_base_rev(m.group(1))
    for op, num in re.findall(r"([~^])(\d*)", m.group(2)):
        if not oid:
            return None
        n = int(num) if num else 1
        if op == "^":
            # <rev>^0 is the commit itself; <rev>^<n> is its n-th parent.
            oid = _nth_parent(oid, n)
        else:
            for _ in range(n):
                oid = _nth_parent(oid, 1)
                if not oid:
                    return None
    return oid


def _resolve_rev_path(rev: str, path: str) -> str | None:
    """Resolve <rev>:<path> to the blob or tree at *path* in that commit's
    tree, or :<path> to the staged blob.  Like Git, *path* is relative to the
    repository root unless it starts with ./ or ../."""
    if path in (".", "..") or path.startswith(("./", "../")):
        path = normalize_pathspec(path)
    else:
        path = posixpath.normpath(path) if path else "."
        if path == ".." or path.startswith(("../", "/")):
            return None
    path = "" if path == "." else path

    if not rev:
        return read_index().get(path)
    commit_oid = resolve_commit(rev)
    if not commit_oid:
        return None
    return _tree_path_oid(read_commit(commit_oid)["tree"], path)


def _tree_path_oid(tree_oid: str, path: str) -> str | None:
    """The blob or tree OID at root-relative *path* ("" is the root itself)."""
    oid = tree_oid
    obj_type = "tree"
    for name in path.split("/") if path else []:
        if obj_type != "tree":
            return None
        entry = next((e for e in read_tree_entries(oid) if e["name"] == name), None)
        if entry is None:
            return None
        oid, obj_type = entry["oid"], entry["type"]
    return oid


def _nth_parent(oid: str, n: int) -> str | None:
    """The n-th (1-based) parent of commit *oid*; n == 0 checks it is a commit."""
    obj_type, _ = read_object(oid)
    if obj_type != "commit":
        return None
    if n == 0:
        return oid
    parents = read_commit(oid).get("parents", [])
    return parents[n - 1] if n <= len(parents) else None


def _resolve_base_rev(rev: str | None) -> str | None:
    """Resolve a branch name, tag, or abbreviated hash to a full commit OID."""
    if not rev or rev == "HEAD":
        return get_head_commit()
    # branch?
    bc = get_branch_commit(rev)
    if bc:
        return bc
    # tag?
    tc = get_tag_commit(rev)
    if tc:
        return tc
    # abbreviated hash?  Like Git, require at least four hex digits so short
    # words and file names are not mistaken for object ids.
    if not _ABBREV_OID_RE.fullmatch(rev):
        return None
    hits = find_objects(rev)
    if len(hits) == 1:
        return hits[0]
    if len(hits) > 1:
        _die(f"ambiguous argument '{rev}': {len(hits)} objects match")
    return None

def resolve_commit(rev: str | None) -> str | None:
    """Like resolve_rev, but only accept revs that name a commit.

    An abbreviated hash can resolve to a blob or tree object; callers that
    need a commit should use this so the user gets "bad revision" instead of
    a confusing object-type error.
    """
    oid = resolve_rev(rev)
    if not oid:
        return None
    obj_type, _ = read_object(oid)
    return oid if obj_type == "commit" else None

def _die_if_rev_path_ambiguous(arg: str, command: str):
    """Refuse an abbreviated object id that also names a path, like Git."""
    if (not _ABBREV_OID_RE.fullmatch(arg) or len(arg) == 40
            or get_branch_commit(arg) or get_tag_commit(arg)):
        return
    rel = normalize_pathspec(arg)
    if os.path.lexists(rel) or rel in read_index():
        _die(f"ambiguous argument '{arg}': both revision and filename\n"
             "Use '--' to separate paths from revisions, like this:\n"
             f"'notgit {command} [<revision>...] -- [<file>...]'")

def _peel_rev_suffix(rev: str) -> tuple[str, str | None]:
    """Split simple rev-parse peel suffixes like HEAD^{commit}."""
    for suffix in ("^{commit}", "^{object}"):
        if rev.endswith(suffix):
            return rev[:-len(suffix)], suffix[2:-1]
    return rev, None


# ── ignore ───────────────────────────────────────────────────────────────────

def _read_ignore_file() -> str | None:
    try:
        path_stat = os.lstat(IGNORE_FILE)
    except FileNotFoundError:
        return None
    except OSError as e:
        _die(f"could not inspect {IGNORE_FILE}: {e}")
    if not stat.S_ISREG(path_stat.st_mode):
        _die(f"{IGNORE_FILE} is not a regular file")
    if path_stat.st_size > MAX_IGNORE_FILE_BYTES:
        _die(f"{IGNORE_FILE} is too large (maximum {MAX_IGNORE_FILE_BYTES} bytes)")

    flags = os.O_RDONLY | getattr(os, "O_BINARY", 0)
    flags |= getattr(os, "O_CLOEXEC", 0) | getattr(os, "O_NONBLOCK", 0)
    flags |= getattr(os, "O_NOFOLLOW", 0)
    fd = None
    try:
        fd = os.open(IGNORE_FILE, flags)
        opened_stat = os.fstat(fd)
        if not stat.S_ISREG(opened_stat.st_mode):
            _die(f"{IGNORE_FILE} is not a regular file")
        if opened_stat.st_size > MAX_IGNORE_FILE_BYTES:
            _die(f"{IGNORE_FILE} is too large (maximum {MAX_IGNORE_FILE_BYTES} bytes)")
        stream = os.fdopen(fd, "rb")
        fd = None
        with stream:
            data = stream.read(MAX_IGNORE_FILE_BYTES + 1)
    except OSError as e:
        _die(f"could not read {IGNORE_FILE}: {e}")
    finally:
        if fd is not None:
            os.close(fd)
    if len(data) > MAX_IGNORE_FILE_BYTES:
        _die(f"{IGNORE_FILE} is too large (maximum {MAX_IGNORE_FILE_BYTES} bytes)")
    try:
        return data.decode("utf-8")
    except UnicodeDecodeError as e:
        _die(f"could not decode {IGNORE_FILE} as UTF-8: {e}")

def load_ignore():
    """Compile ordered root .gitignore-style rules, including negation."""
    raw = [(VCS_DIR + "/", False)]
    ignore_text = _read_ignore_file()
    if ignore_text is not None:
        for line in ignore_text.splitlines():
            line = line.rstrip()
            if not line or line.startswith("#"):
                continue
            negated = line.startswith("!")
            if negated:
                line = line[1:]
            elif line.startswith((r"\#", r"\!")):
                line = line[1:]      # escaped leading '#' or '!' is literal
            raw.append((line, negated))
    rules = []
    for pattern, negated in raw:
        if pattern:
            rules.append((_gitignore_regex(pattern), negated))
    return rules


def _gitignore_regex(pattern: str):
    anchored = pattern.startswith("/")
    if anchored:
        pattern = pattern[1:]
    directory = pattern.endswith("/")
    if directory:
        pattern = pattern[:-1]
    has_slash = "/" in pattern
    out, i = [], 0
    while i < len(pattern):
        char = pattern[i]
        if char == "*":
            if i + 1 < len(pattern) and pattern[i + 1] == "*":
                i += 1
                if i + 1 < len(pattern) and pattern[i + 1] == "/":
                    i += 1
                    out.append("(?:.*/)?")
                else:
                    out.append(".*")
            else:
                out.append("[^/]*")
        elif char == "?":
            out.append("[^/]")
        elif char == "[":
            start = i + 1
            negated_class = start < len(pattern) and pattern[start] in "!^"
            if negated_class:
                start += 1
            # A ']' directly after '[' or '[!' is a literal class member.
            end = pattern.find("]", start + 1 if start < len(pattern) and pattern[start] == "]" else start)
            if end >= 0:
                members = pattern[start:end].replace("\\", "\\\\")
                out.append(("[^/" if negated_class else "[") + members + "]")
                i = end
            else:
                out.append(r"\[")
        else:
            out.append(re.escape(char))
        i += 1
    prefix = "^" if anchored or has_slash else r"(?:^|.*/)"
    # Only file paths are matched, so a directory-only rule ("build/") must
    # match a leading directory component, never the file itself.
    suffix = r"/.*$" if directory else r"(?:/.*)?$"
    return re.compile(prefix + "".join(out) + suffix)

def is_ignored(rel_path: str, patterns) -> bool:
    ignored = False
    for regex, negated in patterns:
        if regex.fullmatch(rel_path):
            ignored = not negated
    return ignored


# ── index ────────────────────────────────────────────────────────────────────

def read_index() -> dict:
    return _require_json_type(INDEX_FILE, read_json(INDEX_FILE, {}), dict, "index")

def _validate_blob_map(file_map: dict, label: str):
    for path, oid in file_map.items():
        if not isinstance(path, str):
            _die(f"invalid {label}: path is not a string")
        ensure_repo_relative_path(path)
        obj_type = read_object_type(oid)
        if obj_type != "blob":
            _die(f"invalid {label}: '{path}' points to a {obj_type} object")

def write_index(index: dict):
    _require_json_type(INDEX_FILE, index, dict, "index")
    _validate_blob_map(index, "index")
    write_json(INDEX_FILE, index)

def read_index_times() -> dict:
    return _require_json_type(
        INDEX_TIMES_FILE, read_json(INDEX_TIMES_FILE, {}), dict, "index times"
    )


# ── working-tree scan ────────────────────────────────────────────────────────

def working_tree_paths(root=".", index=None, force=False, patterns=None) -> set:
    """Return non-ignored paths, failing if any directory cannot be scanned."""
    ignore = patterns if patterns is not None else load_ignore()
    # Directories that contain tracked files must not be skipped wholesale.
    tracked_dirs: set = set()
    if index:
        for _p in index:
            _parts = _p.split("/")
            for _i in range(1, len(_parts)):
                tracked_dirs.add("/".join(_parts[:_i]))
    paths: set = set()

    def _walk_error(error):
        failed_path = getattr(error, "filename", None) or root
        _die(f"could not scan working tree at '{failed_path}': {error}")

    for dirpath, dirs, filenames in os.walk(root, onerror=_walk_error):
        def _drel(d):
            return os.path.relpath(os.path.join(dirpath, d), ".").replace("\\", "/")
        # Keep ignored directories traversable because a later negated rule can
        # re-include a descendant.  The metadata directory is always pruned.
        dirs[:] = sorted(d for d in dirs if d != VCS_DIR)
        for name in sorted(filenames):
            full = os.path.join(dirpath, name)
            rel  = os.path.relpath(full, ".").replace("\\", "/")
            if rel == VCS_DIR or rel.startswith(VCS_DIR + "/"):
                continue
            if not force and is_ignored(rel, ignore) and (index is None or rel not in index):
                continue
            if os.path.islink(full) and (index is None or rel not in index):
                # Trees carry no file modes, so a link cannot be recorded
                # faithfully; skip it instead of failing the whole scan.  A
                # tracked path replaced by a link still fails loudly below so
                # it is never silently dropped from the index.
                if rel not in _WARNED_SYMLINKS:
                    _WARNED_SYMLINKS.add(rel)
                    print(f"warning: skipping symbolic link '{rel}' "
                          "(notgit does not track symbolic links)", file=sys.stderr)
                continue
            paths.add(rel)
    return paths

def _scan_working_tree(root=".", index=None, *, include_data=False, force=False) -> dict:
    """Read and hash work-tree paths, aborting on every file-system error."""
    files: dict = {}
    for rel in working_tree_paths(root, index=index, force=force):
        try:
            if include_data:
                source, initial_stat = _open_worktree_file(rel)
                with source:
                    data = source.read(initial_stat.st_size + 1)
                    final_stat = os.fstat(source.fileno())
                if (len(data) != initial_stat.st_size
                        or final_stat.st_size != initial_stat.st_size
                        or final_stat.st_mtime_ns != initial_stat.st_mtime_ns):
                    raise OSError(errno.EIO, "file changed while reading", rel)
                oid = hash_blob(data)
            else:
                oid = hash_blob_file(rel)
        except OSError as e:
            _die(f"could not read working-tree file '{rel}': {e}")
        files[rel] = (oid, data) if include_data else oid
    return files

def working_tree_files(root=".", index=None, force=False) -> dict:
    """Return ``{rel_path: (oid, raw_bytes)}`` for every non-ignored file."""
    return _scan_working_tree(root, index, include_data=True, force=force)

def working_tree_oids(root=".", index=None, force=False) -> dict:
    """Return ``{rel_path: oid}`` without holding file bytes in memory."""
    return _scan_working_tree(root, index, include_data=False, force=force)


# ── tree objects ─────────────────────────────────────────────────────────────

def build_tree(file_map: dict) -> str:
    """Build nested tree objects from {rel_path: blob_oid} and return root OID."""
    _validate_blob_map(file_map, "tree")

    def _build(mapping: dict) -> str:
        entries, subdirs = [], {}
        for path, oid in sorted(mapping.items()):
            parts = path.split("/", 1)
            if len(parts) == 1:
                entries.append({"name": parts[0], "type": "blob", "oid": oid})
            else:
                subdirs.setdefault(parts[0], {})[parts[1]] = oid
        for dname, sub in sorted(subdirs.items()):
            entries.append({"name": dname, "type": "tree", "oid": _build(sub)})
        raw = json.dumps({"type": "tree", "entries": entries}, sort_keys=True).encode()
        return store_object("tree", raw)
    return _build(file_map)

def read_tree_entries(oid: str) -> list:
    """Return the validated top-level entries of tree *oid*."""
    obj_type, content = read_object(oid)
    if obj_type != "tree":
        _die(f"expected tree object, got {obj_type}")
    try:
        tree = json.loads(content)
    except json.JSONDecodeError as e:
        _die(f"object corrupt: {oid} (invalid tree JSON: {e})")
    if not isinstance(tree, dict) or not isinstance(tree.get("entries"), list):
        _die(f"object corrupt: {oid} (invalid tree structure)")
    for e in tree["entries"]:
        if not isinstance(e, dict):
            _die(f"object corrupt: {oid} (invalid tree entry)")
        name = e.get("name")
        entry_type = e.get("type")
        entry_oid = e.get("oid")
        if not isinstance(name, str) or not _safe_path_component(name):
            _die(f"object corrupt: {oid} (unsafe tree entry name)")
        if not isinstance(entry_oid, str):
            _die(f"object corrupt: {oid} (invalid tree entry oid)")
        if entry_type not in ("blob", "tree"):
            _die(f"object corrupt: {oid} (invalid tree entry type)")
    return tree["entries"]


def read_tree(oid: str, base="") -> dict:
    """Return {rel_path: blob_oid} for every file in the tree."""
    files = {}
    for e in read_tree_entries(oid):
        path = (base + "/" + e["name"]).lstrip("/")
        if e["type"] == "blob":
            files[path] = e["oid"]
        else:
            files.update(read_tree(e["oid"], path))
    return files


# ── commit objects ───────────────────────────────────────────────────────────

def create_commit(tree_oid: str, message: str, parents: list, author=None,
                  timestamp=None) -> str:
    if author is None:
        name, email = get_author()
        author = f"{name} <{email}>"
    commit = {
        "type":      "commit",
        "tree":      tree_oid,
        "parents":   [p for p in (parents or []) if p],
        "author":    author,
        "message":   message,
        "timestamp": time.time() if timestamp is None else timestamp,
    }
    return store_object("commit", json.dumps(commit, sort_keys=True).encode())

def read_commit(oid: str) -> dict:
    obj_type, content = read_object(oid)
    if obj_type != "commit":
        _die(f"expected commit object, got {obj_type}")
    try:
        data = json.loads(content)
    except json.JSONDecodeError as e:
        _die(f"object corrupt: {oid} (invalid commit JSON: {e})")
    if not isinstance(data, dict) or not isinstance(data.get("tree"), str):
        _die(f"object corrupt: {oid} (invalid commit structure)")
    tree_type, _ = read_object(data["tree"])
    if tree_type != "tree":
        _die(f"object corrupt: {oid} (commit tree is a {tree_type} object)")
    # migrate legacy single-parent field
    if "parent" in data and "parents" not in data:
        data["parents"] = [data["parent"]] if data["parent"] else []
    data.setdefault("parents", [])
    required = {
        "parents": list,
        "author": str,
        "message": str,
        "timestamp": (int, float),
    }
    for key, expected in required.items():
        if not isinstance(data.get(key), expected):
            _die(f"object corrupt: {oid} (invalid commit {key})")
    for parent in data["parents"]:
        if not isinstance(parent, str) or not re.fullmatch(r"[0-9a-f]{40}", parent):
            _die(f"object corrupt: {oid} (invalid parent oid)")
    return data


# ── restore helpers ──────────────────────────────────────────────────────────

def _copy_stream(source, destination):
    while True:
        chunk = source.read(IO_CHUNK_SIZE)
        if not chunk:
            return
        destination.write(chunk)


def _write_transaction_source(source, destination):
    if isinstance(source, bytes):
        destination.write(source)
        return
    if (isinstance(source, tuple) and len(source) == 2
            and source[0] == "blob"):
        _stream_blob_object(source[1], destination)
        return
    _die("invalid repository transaction source")


def _default_worktree_mode() -> int:
    current = os.umask(0)
    os.umask(current)
    return 0o666 & ~current


def _copy_regular_path(path: str, destination):
    flags = os.O_RDONLY | getattr(os, "O_BINARY", 0)
    flags |= getattr(os, "O_CLOEXEC", 0) | getattr(os, "O_NOFOLLOW", 0)
    fd = os.open(path, flags)
    try:
        opened = os.fstat(fd)
        if not stat.S_ISREG(opened.st_mode):
            raise OSError(errno.EINVAL, "not a regular file", path)
        with os.fdopen(fd, "rb") as source:
            fd = None
            _copy_stream(source, destination)
    finally:
        if fd is not None:
            os.close(fd)


def _install_transaction_file(source_path: str, target_path: str, mode: int):
    parent = os.path.dirname(target_path) or "."
    os.makedirs(parent, exist_ok=True)
    _contained_worktree_path(parent)
    fd, tmp = tempfile.mkstemp(prefix=".notgit-install-", dir=parent)
    stream = None
    try:
        stream = os.fdopen(fd, "wb")
        fd = None
        with stream as destination:
            stream = None
            with open(source_path, "rb") as source:
                _copy_stream(source, destination)
            destination.flush()
            os.fsync(destination.fileno())
        os.chmod(tmp, mode)
        _contained_worktree_path(parent)
        os.replace(tmp, target_path)
        tmp = None
        _fsync_directory(parent)
    finally:
        if stream is not None:
            stream.close()
        if fd is not None:
            os.close(fd)
        if tmp is not None:
            try:
                os.unlink(tmp)
            except OSError:
                pass


def _remove_transaction_path(path: str):
    if not os.path.lexists(path):
        return
    node = os.lstat(path)
    if stat.S_ISDIR(node.st_mode):
        os.rmdir(path)
    else:
        os.unlink(path)
    _fsync_directory(os.path.dirname(path) or ".")


def _transaction_record(record=None):
    if record is None:
        record = read_json(TRANSACTION_FILE, None)
    if not isinstance(record, dict) or record.get("version") != 1:
        _die(f"invalid repository transaction in {TRANSACTION_FILE}")
    txn_dir = record.get("directory")
    entries = record.get("entries")
    changes = record.get("changes")
    if (not isinstance(txn_dir, str) or not isinstance(entries, list)
            or not isinstance(changes, list)):
        _die(f"invalid repository transaction in {TRANSACTION_FILE}")
    vcs_real = os.path.realpath(VCS_DIR)
    txn_real = os.path.realpath(txn_dir)
    if (os.path.commonpath([vcs_real, txn_real]) != vcs_real
            or not os.path.basename(txn_real).startswith(".transaction-")):
        _die(f"invalid repository transaction directory in {TRANSACTION_FILE}")
    for item in entries + changes:
        if not isinstance(item, dict) or not isinstance(item.get("path"), str):
            _die(f"invalid repository transaction entry in {TRANSACTION_FILE}")
        ensure_repo_relative_path(item["path"])
    return record


def _prepare_repository_transaction(changes: dict, metadata_paths) -> dict:
    if os.path.exists(TRANSACTION_FILE):
        _die("an unfinished repository transaction requires recovery")
    os.makedirs(VCS_DIR, exist_ok=True)
    txn_dir = tempfile.mkdtemp(prefix=".transaction-", dir=VCS_DIR)
    protected = sorted(set(changes) | set(metadata_paths))
    entries = []
    staged_changes = []
    try:
        for number, path in enumerate(protected):
            ensure_repo_relative_path(path)
            full = _contained_worktree_path(path)
            item = {"path": path, "exists": os.path.lexists(full)}
            if item["exists"]:
                node = os.lstat(full)
                if (stat.S_ISDIR(node.st_mode) and changes.get(path) is not None
                        and _directory_emptied_by(path, changes)):
                    # A tracked directory replaced by a file: its contents are
                    # backed up as their own deletions, and rollback recreates
                    # the directory when it reinstalls them.
                    item["exists"] = False
                    entries.append(item)
                    continue
                if not stat.S_ISREG(node.st_mode):
                    action = "remove" if changes.get(path, object()) is None else "write"
                    raise OSError(
                        errno.EINVAL,
                        f"could not {action} '{path}': target is not a regular file",
                    )
                backup = f"backup-{number}"
                backup_path = os.path.join(txn_dir, backup)
                with open(backup_path, "wb") as destination:
                    _copy_regular_path(full, destination)
                    destination.flush()
                    os.fsync(destination.fileno())
                item.update(backup=backup, mode=stat.S_IMODE(node.st_mode))
            entries.append(item)

        for number, (path, source) in enumerate(sorted(changes.items())):
            item = {"path": path, "delete": source is None}
            if source is not None:
                stage = f"desired-{number}"
                stage_path = os.path.join(txn_dir, stage)
                with open(stage_path, "wb") as destination:
                    _write_transaction_source(source, destination)
                    destination.flush()
                    os.fsync(destination.fileno())
                original = next(e for e in entries if e["path"] == path)
                item.update(
                    stage=stage,
                    mode=(original.get("mode") if original["exists"]
                          else _default_worktree_mode()),
                )
            staged_changes.append(item)

        _fsync_directory(txn_dir)
        record = {
            "version": 1,
            "directory": txn_dir,
            "entries": entries,
            "changes": staged_changes,
        }
        write_json(TRANSACTION_FILE, record)
        return record
    except BaseException:
        shutil.rmtree(txn_dir, ignore_errors=True)
        raise


def _directory_emptied_by(path: str, changes: dict) -> bool:
    """True when every file below directory *path* is scheduled for removal."""
    for dirpath, _dirs, filenames in os.walk(path):
        for name in filenames:
            rel = os.path.relpath(os.path.join(dirpath, name), ".").replace("\\", "/")
            if rel not in changes or changes[rel] is not None:
                return False
    return True


def _prune_empty_parents(path: str):
    """Remove directories left empty by deleting *path*, up to the work tree."""
    parent = os.path.dirname(path)
    while parent and parent not in (".", VCS_DIR):
        try:
            os.rmdir(parent)
        except OSError:
            return
        _fsync_directory(os.path.dirname(parent) or ".")
        parent = os.path.dirname(parent)


def _apply_repository_transaction(record: dict):
    record = _transaction_record(record)
    for item in sorted(record["changes"],
                       key=lambda value: value["path"].count("/"), reverse=True):
        if item["delete"]:
            _remove_transaction_path(item["path"])
            _prune_empty_parents(item["path"])
    for item in sorted(record["changes"],
                       key=lambda value: value["path"].count("/")):
        if item["delete"]:
            continue
        source = os.path.join(record["directory"], item["stage"])
        _install_transaction_file(source, item["path"], item["mode"])


def _discard_repository_transaction(record: dict, *, missing_ok=False):
    _durable_unlink(TRANSACTION_FILE, missing_ok=missing_ok)
    shutil.rmtree(record["directory"], ignore_errors=True)


def _rollback_repository_transaction(record: dict):
    record = _transaction_record(record)
    for item in sorted(record["entries"],
                       key=lambda value: value["path"].count("/"), reverse=True):
        _remove_transaction_path(item["path"])
    for item in sorted(record["entries"],
                       key=lambda value: value["path"].count("/")):
        if not item["exists"]:
            continue
        backup = os.path.join(record["directory"], item["backup"])
        if not os.path.isfile(backup):
            _die(f"repository transaction backup is missing for '{item['path']}'")
        _install_transaction_file(backup, item["path"], item["mode"])
    _discard_repository_transaction(record, missing_ok=True)


def _recover_repository_transaction(root: str):
    journal = os.path.join(root, TRANSACTION_FILE)
    if not os.path.exists(journal):
        return
    previous_cwd = os.getcwd()
    previous_root = globals().get("_WORKTREE_ROOT")
    try:
        os.chdir(root)
        globals()["_WORKTREE_ROOT"] = root
        record = _transaction_record()
        _rollback_repository_transaction(record)
    finally:
        globals()["_WORKTREE_ROOT"] = previous_root
        os.chdir(previous_cwd)
    print("warning: recovered an interrupted repository transaction", file=sys.stderr)


@contextlib.contextmanager
def _repository_transaction(changes=None, metadata_paths=()):
    changes = dict(changes or {})
    if not changes and not metadata_paths:
        yield
        return
    try:
        record = _prepare_repository_transaction(changes, metadata_paths)
    except OSError as e:
        _die(f"could not prepare repository transaction: {e}")
    try:
        _apply_repository_transaction(record)
        yield
    except BaseException as operation_error:
        try:
            _rollback_repository_transaction(record)
        except BaseException as rollback_error:
            _err(f"repository transaction rollback failed: {rollback_error}")
            raise
        if isinstance(operation_error, OSError):
            _die(f"repository transaction failed: {operation_error}")
        raise operation_error
    else:
        try:
            _discard_repository_transaction(record)
        except BaseException:
            _rollback_repository_transaction(record)
            raise


def _remove_path_and_empty_parents(path: str):
    try:
        os.remove(path)
    except FileNotFoundError:
        return
    except OSError as e:
        _die(f"could not remove '{path}': {e}")
    parent = os.path.dirname(path)
    while parent and parent != ".":
        try:
            os.rmdir(parent)
            parent = os.path.dirname(parent)
        except OSError:
            break

def _write_worktree_file(path: str, data: bytes):
    ensure_repo_relative_path(path)
    try:
        with _repository_transaction({path: data}):
            pass
    except OSError as e:
        _die(f"could not write '{path}': {e}")


def _tree_worktree_changes(tree_oid: str, tracked_before=None) -> tuple[dict, dict]:
    target = read_tree(tree_oid)
    tracked_before = set(read_index() if tracked_before is None else tracked_before)
    tracked_now = tracked_before | set(target)
    current = working_tree_oids(index={path: None for path in tracked_now})
    changes = {}
    for path in sorted(tracked_before - set(target)):
        ensure_repo_relative_path(path)
        if os.path.lexists(path):
            changes[path] = None
    for path, blob_oid in target.items():
        ensure_repo_relative_path(path)
        if read_object_type(blob_oid) != "blob":
            _die(f"expected blob object, got {read_object_type(blob_oid)}")
        if current.get(path) != blob_oid:
            changes[path] = ("blob", blob_oid)
    return target, changes

def restore_tree_to_workdir(tree_oid: str, tracked_before=None):
    """Update tracked worktree files to match a tree object."""
    _target, changes = _tree_worktree_changes(tree_oid, tracked_before)
    with _repository_transaction(changes):
        pass

def _apply_tree_and_index(tree_oid: str, tracked_before=None, *,
                          metadata_paths=(), finalize=None):
    target, changes = _tree_worktree_changes(tree_oid, tracked_before)
    protected = [INDEX_FILE, *metadata_paths]
    with _repository_transaction(changes, protected):
        write_index(target)
        if finalize is not None:
            finalize()


def apply_commit(commit_oid: str, *, metadata_paths=(), finalize=None):
    """Restore working tree and index to the state of a commit."""
    tracked_before = set(read_index())
    commit = read_commit(commit_oid)
    _apply_tree_and_index(
        commit["tree"], tracked_before=tracked_before,
        metadata_paths=metadata_paths, finalize=finalize,
    )

def _switch_commit(from_tree: dict, to_tree: dict, *, metadata_paths=(), finalize=None):
    """Move index and work tree from *from_tree* to *to_tree* like Git's
    branch switch: only paths that differ between the two trees are touched,
    so unrelated staged and unstaged changes are carried over intact.
    Callers must run _guard_tree_transition first."""
    index = read_index()
    new_index = dict(index)
    changes = {}
    for path in sorted(set(from_tree) | set(to_tree)):
        if from_tree.get(path) == to_tree.get(path):
            continue
        ensure_repo_relative_path(path)
        if path in to_tree:
            blob_oid = to_tree[path]
            if read_object_type(blob_oid) != "blob":
                _die(f"expected blob object, got {read_object_type(blob_oid)}")
            changes[path] = ("blob", blob_oid)
            new_index[path] = blob_oid
        else:
            if os.path.lexists(path):
                changes[path] = None
            new_index.pop(path, None)
    with _repository_transaction(changes, [INDEX_FILE, *metadata_paths]):
        write_index(new_index)
        if finalize is not None:
            finalize()

def _worktree_is_dirty() -> bool:
    index = read_index()
    head = get_head_commit()
    committed = read_tree(read_commit(head)["tree"]) if head else {}
    wt = working_tree_oids(index=index)

    if index != committed:
        return True
    for path, oid in wt.items():
        if path in index and index[path] != oid:
            return True
    for path in index:
        if path not in wt:
            return True
    return False

def _ensure_clean_worktree(action: str):
    if _worktree_is_dirty():
        _die(f"cannot {action}: you have uncommitted changes")

def _validate_ref_name(name: str, kind: str):
    if not _safe_ref_name(name):
        _die(f"invalid {kind} name '{name}'")

def _guard_tree_transition(from_tree: dict, to_tree: dict, action: str,
                           advice: str, affected_paths=None):
    index = read_index()
    wt = working_tree_oids(index=index)
    affected = set(affected_paths) if affected_paths is not None else set(from_tree) | set(to_tree)
    tracked_conflicts = []
    untracked_conflicts = []

    for path in sorted(affected):
        from_blob = from_tree.get(path)
        to_blob = to_tree.get(path)
        if from_blob == to_blob:
            continue
        idx_oid = index.get(path)
        wt_oid = wt.get(path)
        if (idx_oid is None and to_blob is not None and os.path.isdir(path)
                and not os.path.islink(path)):
            # A directory where the target has a file: only untracked
            # content inside it would be lost; tracked files are checked
            # as their own paths.
            untracked_conflicts.extend(
                p for p in sorted(wt) if p.startswith(path + "/") and p not in index
            )
        elif idx_oid is None and os.path.lexists(path):
            untracked_conflicts.append(path)
        elif wt_oid != idx_oid or idx_oid != from_blob:
            tracked_conflicts.append(path)

    if tracked_conflicts or untracked_conflicts:
        for path in tracked_conflicts:
            _err(f"Your local changes to '{path}' would be overwritten by {action}.")
        for path in untracked_conflicts:
            _err(f"Your untracked file '{path}' would be overwritten by {action}.")
        print(advice, file=sys.stderr)
        sys.exit(1)


# ── diff helpers ─────────────────────────────────────────────────────────────

def _split_revs_and_paths(raw_args: list, command: str = "diff") -> tuple:
    """Split positional diff args into (rev_list, path_list).

    Greedily resolves up to 2 leading tokens as revisions; any token that
    doesn't resolve to a known commit (or exceeds the 2-rev limit) and
    everything after it are treated as path specs.
    """
    revs, rest = [], list(raw_args)
    while rest and len(revs) < 2:
        candidate = rest[0]
        if resolve_commit(candidate) is not None:
            _die_if_rev_path_ambiguous(candidate, command)
            revs.append(rest.pop(0))
        else:
            break
    return revs, rest


# ── diff printing ─────────────────────────────────────────────────────────────

def print_diff(path: str, a_lines: list | None, b_lines: list | None,
               a_label="a", b_label="b"):
    """Print a unified diff; ``None`` means that side does not exist, while
    ``[]`` is an existing empty file."""
    # When labels are the defaults we use the standard a/<path> b/<path> form;
    # for --no-index the caller passes the actual file paths as labels.
    no_index = (a_label != "a" or b_label != "b")
    a_missing, b_missing = a_lines is None, b_lines is None
    a_lines, b_lines = a_lines or [], b_lines or []
    if no_index:
        print(f"diff --notgit {a_label} {b_label}")
    else:
        print(f"diff --notgit a/{path} b/{path}")
    if a_missing:
        print("new file mode 100644")
    elif b_missing:
        print("deleted file mode 100644")
    if no_index:
        a_name = "/dev/null" if a_missing else a_label
        b_name = "/dev/null" if b_missing else b_label
    else:
        a_name = "/dev/null" if a_missing else f"a/{path}"
        b_name = "/dev/null" if b_missing else f"b/{path}"
    # The first two lines are the ---/+++ headers; content such as "++i"
    # renders as "+++i" and must still be coloured as an insertion.
    for number, line in enumerate(difflib.unified_diff(
            a_lines, b_lines, fromfile=a_name, tofile=b_name, n=3)):
        if number < 2:
            sys.stdout.write(line)
        elif line.startswith("+"):
            sys.stdout.write(green(line))
        elif line.startswith("-"):
            sys.stdout.write(red(line))
        elif line.startswith("@@"):
            sys.stdout.write(cyan(line))
        else:
            sys.stdout.write(line)
        if not line.endswith("\n"):
            print()
            print("\\ No newline at end of file")

def blob_lines(oid: str | None) -> list:
    if not oid:
        return []
    _, data = read_object(oid)
    return data.decode(errors="replace").splitlines(True)

def map_blob_lines(file_map: dict, path: str) -> list | None:
    return blob_lines(file_map[path]) if path in file_map else None

def _count_ins_dels(a_lines: list, b_lines: list) -> tuple[int, int]:
    """Count inserted / deleted lines via unified_diff (O(n))."""
    ins = dels = 0
    # Skip the two header lines positionally: content lines such as "++i;"
    # render as "+++i;" and must not be mistaken for a "+++" header.
    for line in list(difflib.unified_diff(a_lines, b_lines, n=0))[2:]:
        if line.startswith("@@"):
            continue
        if line.startswith("+"):
            ins += 1
        elif line.startswith("-"):
            dels += 1
    return ins, dels


# ══════════════════════════════════════════════════════════════════════════════
# Commands
# ══════════════════════════════════════════════════════════════════════════════

def cmd_init(args):
    repo_root = _find_repo_root(os.getcwd())
    reinitializing = repo_root is not None
    repo_root = repo_root or os.path.abspath(os.getcwd())
    os.chdir(repo_root)
    global _WORKTREE_ROOT
    _WORKTREE_ROOT = repo_root
    initial_branch = getattr(args, "initial_branch", None) or "main"
    _validate_ref_name(initial_branch, "branch")
    os.makedirs(OBJECTS_DIR, exist_ok=True)
    os.makedirs(HEADS_DIR,   exist_ok=True)
    os.makedirs(TAGS_DIR,    exist_ok=True)
    if not os.path.isfile(INDEX_FILE) or os.path.getsize(INDEX_FILE) == 0:
        write_index({})
    if not os.path.isfile(HEAD_FILE) or os.path.getsize(HEAD_FILE) == 0:
        init_head(initial_branch)
    if not os.path.isfile(CONFIG_FILE) or os.path.getsize(CONFIG_FILE) == 0:
        write_config({"core": {"repositoryformatversion": 0}})
    if not os.path.exists(IGNORE_FILE):
        _atomic_write_text(
            IGNORE_FILE,
            "# notgit ignore file  (same syntax as .gitignore)\n"
            "__pycache__/\n*.pyc\n.DS_Store\n",
        )
    action = "Reinitialized existing" if reinitializing else "Initialized empty"
    print(f"{action} notgit repository in {os.path.abspath(VCS_DIR)}/")


# ── clone ────────────────────────────────────────────────────────────────────

@contextlib.contextmanager
def _temporary_destination(dest: str):
    """Build a new destination privately and publish it only on success."""
    if os.path.lexists(dest):
        _die(f"destination path '{os.path.basename(dest)}' already exists")
    parent = os.path.dirname(dest) or "."
    os.makedirs(parent, exist_ok=True)
    temporary = tempfile.mkdtemp(
        prefix=f".{os.path.basename(dest)}.notgit-build-", dir=parent
    )
    previous_cwd = os.getcwd()
    previous_root = globals().get("_WORKTREE_ROOT")
    try:
        yield temporary
    except BaseException:
        try:
            if os.path.commonpath([os.path.realpath(os.getcwd()),
                                   os.path.realpath(temporary)]) == os.path.realpath(temporary):
                os.chdir(previous_cwd)
        finally:
            globals()["_WORKTREE_ROOT"] = previous_root
            shutil.rmtree(temporary, ignore_errors=True)
        raise
    else:
        if os.path.commonpath([os.path.realpath(os.getcwd()),
                               os.path.realpath(temporary)]) == os.path.realpath(temporary):
            os.chdir(previous_cwd)
        os.replace(temporary, dest)
        _fsync_directory(parent)
        globals()["_WORKTREE_ROOT"] = dest


def cmd_clone(args):
    src = os.path.abspath(args.source)
    dest = (os.path.abspath(args.dest)
            if args.dest
            else os.path.join(_INVOCATION_CWD,
                              os.path.basename(src.rstrip(os.sep))))
    branch = getattr(args, "branch", None)
    no_checkout = getattr(args, "no_checkout", False)
    single_branch = getattr(args, "single_branch", False)
    no_tags = getattr(args, "no_tags", False)

    src_vcs = os.path.join(src, VCS_DIR)
    if not os.path.isdir(src_vcs):
        _die(f"'{args.source}' does not appear to be a notgit repository")

    if os.path.lexists(dest):
        _die(f"destination path '{os.path.basename(dest)}' already exists")

    if branch:
        _validate_ref_name(branch, "branch")
        src_branch = os.path.join(src_vcs, "refs", "heads", branch)
        src_tag = os.path.join(src_vcs, "refs", "tags", branch)
        if not os.path.isfile(src_branch) and not os.path.isfile(src_tag):
            _die(f"Remote branch {branch} not found in upstream origin")

    print(f"Cloning into '{os.path.basename(dest)}'...")
    with _repository_lock_at(src):
        _recover_repository_transaction(src)
        with _temporary_destination(dest) as build_dest:
            dest_vcs = os.path.join(build_dest, VCS_DIR)
            dest_heads = os.path.join(dest_vcs, "refs", "heads")
            dest_tags = os.path.join(dest_vcs, "refs", "tags")
            os.makedirs(dest_heads, exist_ok=True)
            os.makedirs(dest_tags, exist_ok=True)

            src_objects = os.path.join(src_vcs, "objects")
            dest_objects = os.path.join(dest_vcs, "objects")
            if os.path.isdir(src_objects):
                shutil.copytree(src_objects, dest_objects)
            else:
                os.makedirs(dest_objects)

            try:
                with open(os.path.join(src_vcs, "HEAD"), encoding="utf-8") as f:
                    source_head = f.read().strip()
            except OSError as e:
                _die(f"could not read source HEAD: {e}")
            source_head_branch = None
            if source_head.startswith("ref: refs/heads/"):
                source_head_branch = source_head[len("ref: refs/heads/"):]

            src_heads = os.path.join(src_vcs, "refs", "heads")
            selected_branch = branch if branch and os.path.isfile(
                os.path.join(src_heads, branch)
            ) else source_head_branch
            if os.path.isdir(src_heads):
                for fname in _list_ref_names(src_heads):
                    if single_branch and fname != selected_branch:
                        continue
                    dp = os.path.join(dest_heads, fname)
                    os.makedirs(os.path.dirname(dp), exist_ok=True)
                    shutil.copy2(os.path.join(src_heads, fname), dp)

            src_tags = os.path.join(src_vcs, "refs", "tags")
            if os.path.isdir(src_tags):
                for fname in _list_ref_names(src_tags):
                    if no_tags and fname != branch:
                        continue
                    dp = os.path.join(dest_tags, fname)
                    os.makedirs(os.path.dirname(dp), exist_ok=True)
                    shutil.copy2(os.path.join(src_tags, fname), dp)

            shutil.copy2(os.path.join(src_vcs, "HEAD"), os.path.join(dest_vcs, "HEAD"))
            source_config_path = os.path.join(src_vcs, "config")
            src_cfg = _require_json_type(
                source_config_path, read_json(source_config_path, {}), dict,
                "source config",
            )
            cfg = {key: value for key, value in src_cfg.items() if key != "user"}
            cfg.setdefault("remote", {})["origin"] = src
            write_json(os.path.join(dest_vcs, "config"), cfg)
            write_json(os.path.join(dest_vcs, "index"), {})

            os.chdir(build_dest)
            global _WORKTREE_ROOT
            _WORKTREE_ROOT = build_dest
            if branch:
                branch_commit = get_branch_commit(branch)
                if branch_commit:
                    set_head_ref(branch)
                    head_commit = branch_commit
                else:
                    head_commit = get_tag_commit(branch)
                    if not head_commit:
                        _die(f"Remote branch {branch} not found in upstream origin")
                    if read_object_type(head_commit) != "commit":
                        _die(f"reference '{branch}' does not point to a commit")
                    _atomic_write_text(HEAD_FILE, head_commit)
                    if no_tags:
                        _durable_unlink(os.path.join(TAGS_DIR, branch))
            else:
                head_commit = get_head_commit()
            if head_commit and not no_checkout:
                apply_commit(head_commit)
            elif not head_commit:
                print("warning: You appear to have cloned an empty repository.")

    print("done.")


# ── import-git (convert a real .git repository into .notgit) ───────────────────

def _resolve_git_dir(src: str) -> str:
    src = os.path.abspath(src)
    candidate = os.path.join(src, ".git")
    if os.path.isdir(candidate):
        return candidate
    if os.path.isfile(candidate):
        with open(candidate) as f:
            data = f.read().strip()
        if data.startswith("gitdir:"):
            gitdir = data.split(":", 1)[1].strip()
            return gitdir if os.path.isabs(gitdir) else os.path.normpath(os.path.join(src, gitdir))
    if (os.path.isdir(os.path.join(src, "objects"))
            and os.path.isdir(os.path.join(src, "refs"))
            and os.path.isfile(os.path.join(src, "HEAD"))):
        return src   # bare repository
    _die(f"'{src}' does not appear to be a git repository")

def _safe_path_component(name: str) -> bool:
    """A single git tree-entry filename: must not contain a path separator."""
    return bool(name) and name not in (".", "..") and "/" not in name and "\\" not in name and "\0" not in name

def _safe_ref_name(name: str) -> bool:
    """Accept Git-like hierarchical refs while excluding unsafe spellings."""
    if (not name or name.startswith("/") or name.endswith("/")
            or "\\" in name or "\0" in name or ".." in name
            or "@{" in name or name.endswith(".")
            or any(ord(c) < 32 or c in " ~^:?*[" for c in name)):
        return False
    return all(part not in ("", ".", "..") and not part.endswith(".lock")
               for part in name.split("/"))


def _apply_git_delta(base: bytes, delta: bytes) -> bytes:
    """Reconstruct an object's content from a git OFS_DELTA/REF_DELTA payload."""
    def read_varint(buf, i):
        result = shift = 0
        while True:
            if i >= len(buf) or shift > 63:
                _die("corrupt git delta: truncated size")
            b = buf[i]; i += 1
            result |= (b & 0x7f) << shift
            shift += 7
            if not (b & 0x80):
                return result, i

    i = 0
    src_size, i = read_varint(delta, i)
    tgt_size, i = read_varint(delta, i)
    if src_size != len(base):
        _die("corrupt git delta: base size mismatch")
    if tgt_size > MAX_GIT_OBJECT_BYTES:
        _die(f"git object exceeds {MAX_GIT_OBJECT_BYTES} byte import limit")
    out = bytearray()
    n = len(delta)
    while i < n:
        op = delta[i]; i += 1
        if op & 0x80:
            cp_off = cp_size = 0
            for bit, shift in ((0x01, 0), (0x02, 8), (0x04, 16), (0x08, 24)):
                if op & bit:
                    if i >= n:
                        _die("corrupt git delta: truncated copy offset")
                    cp_off |= delta[i] << shift
                    i += 1
            for bit, shift in ((0x10, 0), (0x20, 8), (0x40, 16)):
                if op & bit:
                    if i >= n:
                        _die("corrupt git delta: truncated copy size")
                    cp_size |= delta[i] << shift
                    i += 1
            if cp_size == 0:
                cp_size = 0x10000
            if cp_off + cp_size > len(base):
                _die("corrupt git delta: copy exceeds base object")
            out += base[cp_off:cp_off + cp_size]
        elif op:
            if i + op > n:
                _die("corrupt git delta: truncated literal")
            out += delta[i:i + op]
            i += op
        else:
            _die("corrupt git delta: invalid opcode 0")
        if len(out) > tgt_size:
            _die("corrupt git delta: target size exceeded")
    if len(out) != tgt_size:
        _die("corrupt git delta: target size mismatch")
    return bytes(out)


class _GitObjectStore:
    """Read-only reader for a .git object database (loose objects + packs)."""

    _TYPE_NAMES = {1: "commit", 2: "tree", 3: "blob", 4: "tag"}

    def __init__(self, git_dir: str):
        self.git_dir = git_dir
        self._pack_index = {}    # sha hex -> (pack_path, offset)
        self._pack_files = {}    # pack_path -> open file handle
        self._delta_base_cache = OrderedDict()   # (pack_path, offset) -> (type, content)
        self._delta_base_cache_bytes = 0
        pack_dir = os.path.join(git_dir, "objects", "pack")
        if os.path.isdir(pack_dir):
            try:
                pack_names = sorted(os.listdir(pack_dir))
            except OSError as e:
                _die(f"could not list git pack directory {pack_dir}: {e}")
            for fname in pack_names:
                if fname.endswith(".idx"):
                    pack_path = os.path.join(pack_dir, fname[:-4] + ".pack")
                    if os.path.isfile(pack_path):
                        self._load_idx(os.path.join(pack_dir, fname), pack_path)

    def _load_idx(self, idx_path: str, pack_path: str):
        try:
            with open(idx_path, "rb") as f:
                data = f.read()
        except OSError as e:
            _die(f"could not read git pack index {idx_path}: {e}")
        if data[:4] != b"\xfftOc":
            _die(f"unsupported pack index format (v1) in {idx_path}; "
                 f"run 'git repack -ad' in the source repo to upgrade it")
        if len(data) < 8 + 256 * 4 + 40:
            _die(f"corrupt git pack index {idx_path}: truncated header")
        version = struct.unpack(">I", data[4:8])[0]
        if version != 2:
            _die(f"unsupported pack index version {version} in {idx_path}")
        fanout = struct.unpack(">256I", data[8:8 + 256 * 4])
        if any(a > b for a, b in zip(fanout, fanout[1:])):
            _die(f"corrupt git pack index {idx_path}: invalid fanout table")
        count = fanout[255]
        off = 8 + 256 * 4
        fixed_end = off + count * 20 + count * 4 + count * 4
        if fixed_end + 40 > len(data):
            _die(f"corrupt git pack index {idx_path}: truncated object tables")
        sha_table = data[off:off + count * 20]
        off += count * 20
        off += count * 4    # skip CRC32 table
        offset_table = data[off:off + count * 4]
        off += count * 4
        large_indexes = [
            struct.unpack_from(">I", offset_table, i * 4)[0] & 0x7fffffff
            for i in range(count)
            if struct.unpack_from(">I", offset_table, i * 4)[0] & 0x80000000
        ]
        large_count = max(large_indexes, default=-1) + 1
        expected_length = off + large_count * 8 + 40
        if len(data) != expected_length:
            _die(f"corrupt git pack index {idx_path}: invalid table length")
        if hashlib.sha1(data[:-20]).digest() != data[-20:]:
            _die(f"corrupt git pack index {idx_path}: checksum mismatch")
        large_table = data[off:off + large_count * 8]
        for i in range(count):
            sha = sha_table[i * 20:(i + 1) * 20].hex()
            o32 = struct.unpack_from(">I", offset_table, i * 4)[0]
            if o32 & 0x80000000:
                large_index = o32 & 0x7fffffff
                if large_index >= large_count:
                    _die(f"corrupt git pack index {idx_path}: invalid large offset")
                offset = struct.unpack_from(">Q", large_table, large_index * 8)[0]
            else:
                offset = o32
            self._pack_index[sha] = (pack_path, offset)

    def _pack_file(self, pack_path: str):
        f = self._pack_files.get(pack_path)
        if f is None:
            f = open(pack_path, "rb")
            self._pack_files[pack_path] = f
        return f

    def close(self):
        for f in self._pack_files.values():
            f.close()
        self._pack_files.clear()

    @staticmethod
    def _inflate(f, expected_size: int) -> bytes:
        if expected_size > MAX_GIT_OBJECT_BYTES:
            _die(f"git object exceeds {MAX_GIT_OBJECT_BYTES} byte import limit")
        d = zlib.decompressobj()
        out = bytearray()
        compressed = 0
        pending = b""
        while not d.eof:
            chunk = pending or f.read(4096)
            if not chunk:
                _die("corrupt git pack: truncated compressed object")
            if not pending:
                compressed += len(chunk)
                if compressed > expected_size + IO_CHUNK_SIZE:
                    _die("corrupt git pack: compressed object is unreasonably large")
            out += d.decompress(chunk, expected_size - len(out) + 1)
            pending = d.unconsumed_tail
            if len(out) > expected_size:
                _die("corrupt git pack: inflated size exceeds header")
        if len(out) != expected_size:
            _die("corrupt git pack: inflated size mismatch")
        return bytes(out)

    def _read_loose_object(self, sha_hex: str, loose_path: str):
        try:
            d = zlib.decompressobj()
            raw = bytearray()
            compressed = 0
            with open(loose_path, "rb") as f:
                while True:
                    chunk = f.read(IO_CHUNK_SIZE)
                    if not chunk:
                        break
                    compressed += len(chunk)
                    if compressed > MAX_GIT_OBJECT_BYTES + IO_CHUNK_SIZE:
                        _die("compressed git object exceeds import limit")
                    raw += d.decompress(chunk, MAX_GIT_OBJECT_BYTES + 1 - len(raw))
                    if len(raw) > MAX_GIT_OBJECT_BYTES:
                        _die(f"git object exceeds {MAX_GIT_OBJECT_BYTES} byte import limit")
            raw += d.flush(MAX_GIT_OBJECT_BYTES + 1 - len(raw))
        except (OSError, zlib.error) as e:
            _die(f"could not read git object {sha_hex}: {e}")
        if not d.eof or d.unused_data:
            _die(f"corrupt git object {sha_hex}: incomplete or trailing compressed data")
        raw = bytes(raw)
        if hashlib.sha1(raw).hexdigest() != sha_hex:
            _die(f"corrupt git object {sha_hex}: hash mismatch")
        try:
            header, content = raw.split(b"\0", 1)
            obj_type_raw, size_raw = header.split(b" ", 1)
            obj_type = obj_type_raw.decode("ascii")
            declared_size = int(size_raw.decode("ascii"))
        except (ValueError, UnicodeDecodeError):
            _die(f"corrupt git object {sha_hex}: invalid header")
        if obj_type not in self._TYPE_NAMES.values() or declared_size != len(content):
            _die(f"corrupt git object {sha_hex}: invalid type or size")
        return obj_type, content

    def read(self, sha_hex: str):
        """Return (type, content_bytes) for a git object, resolving deltas."""
        if not isinstance(sha_hex, str) or not re.fullmatch(r"[0-9a-f]{40}", sha_hex):
            _die(f"invalid git object id: {sha_hex}")
        loose_path = os.path.join(self.git_dir, "objects", sha_hex[:2], sha_hex[2:])
        if os.path.isfile(loose_path):
            return self._read_loose_object(sha_hex, loose_path)
        entry = self._pack_index.get(sha_hex)
        if entry is None:
            _die(f"git object not found: {sha_hex}")
        try:
            obj_type, content = self._read_pack_object(entry[0], entry[1])
        except (OSError, IndexError, KeyError, struct.error, zlib.error, ValueError) as e:
            _die(f"corrupt git pack object {sha_hex}: {e}")
        raw = f"{obj_type} {len(content)}\0".encode() + content
        if hashlib.sha1(raw).hexdigest() != sha_hex:
            _die(f"corrupt git pack object {sha_hex}: hash mismatch")
        return obj_type, content

    def _cache_delta_base(self, key, obj_type: str, content: bytes):
        if len(content) > MAX_DELTA_BASE_CACHE_BYTES:
            return
        previous = self._delta_base_cache.pop(key, None)
        if previous is not None:
            self._delta_base_cache_bytes -= len(previous[1])
        self._delta_base_cache[key] = (obj_type, content)
        self._delta_base_cache_bytes += len(content)
        while self._delta_base_cache_bytes > MAX_DELTA_BASE_CACHE_BYTES:
            _key, (_type, evicted) = self._delta_base_cache.popitem(last=False)
            self._delta_base_cache_bytes -= len(evicted)

    def _read_pack_entry(self, pack_path: str, offset: int):
        """Read one pack entry: ("base", type, content), ("ofs", base_offset,
        delta) or ("ref", base_sha, delta)."""
        f = self._pack_file(pack_path)
        f.seek(offset)
        first_raw = f.read(1)
        if not first_raw:
            _die("corrupt ngit pack: object offset is beyond EOF")
        first = first_raw[0]
        obj_type_id = (first >> 4) & 0x7
        size = first & 0xf
        shift = 4
        b = first
        while b & 0x80:
            raw = f.read(1)
            if not raw or shift > 63:
                _die("corrupt ngit pack: truncated object header")
            b = raw[0]
            size |= (b & 0x7f) << shift
            shift += 7

        if obj_type_id == 6:      # OBJ_OFS_DELTA
            raw = f.read(1)
            if not raw:
                _die("corrupt ngit pack: truncated delta offset")
            b = raw[0]
            rel_offset = b & 0x7f
            while b & 0x80:
                raw = f.read(1)
                if not raw:
                    _die("corrupt ngit pack: truncated delta offset")
                b = raw[0]
                rel_offset = ((rel_offset + 1) << 7) | (b & 0x7f)
            if rel_offset <= 0 or rel_offset >= offset:
                _die("corrupt ngit pack: invalid delta base offset")
            return "ofs", offset - rel_offset, self._inflate(f, size)
        if obj_type_id == 7:      # OBJ_REF_DELTA
            base_raw = f.read(20)
            if len(base_raw) != 20:
                _die("corrupt ngit pack: truncated delta base id")
            return "ref", base_raw.hex(), self._inflate(f, size)
        if obj_type_id not in self._TYPE_NAMES:
            _die(f"corrupt ngit pack: invalid object type {obj_type_id}")
        return "base", self._TYPE_NAMES[obj_type_id], self._inflate(f, size)

    def _read_pack_object(self, pack_path: str, offset: int):
        """Resolve a packed object, walking its delta chain iteratively.

        Each resolved object is kept in a bounded cache, so objects sharing
        a chain do not re-inflate every base, and chains deeper than the
        interpreter's recursion limit still resolve."""
        pending = []    # (cache key, delta) from the requested object down
        while True:
            key = (pack_path, offset)
            cached = self._delta_base_cache.get(key)
            if cached is not None:
                self._delta_base_cache.move_to_end(key)
                obj_type, content = cached
                break
            kind, locator, payload = self._read_pack_entry(pack_path, offset)
            if kind == "base":
                obj_type, content = locator, payload
                self._cache_delta_base(key, obj_type, content)
                break
            pending.append((key, payload))
            if len(pending) > MAX_GIT_DELTA_CHAIN:
                _die("corrupt ngit pack: delta chain is too long or cyclic")
            if kind == "ofs":
                offset = locator
                continue
            entry = self._pack_index.get(locator)
            if entry is None:
                obj_type, content = self.read(locator)   # loose base object
                break
            pack_path, offset = entry
        for key, delta in reversed(pending):
            content = _apply_git_delta(content, delta)
            self._cache_delta_base(key, obj_type, content)
        return obj_type, content


def _parse_git_tree_entries(content: bytes) -> list:
    entries = []
    i, n = 0, len(content)
    while i < n:
        try:
            sp = content.index(b" ", i)
            mode = content[i:sp].decode("ascii")
            nul = content.index(b"\0", sp + 1)
        except (ValueError, UnicodeDecodeError):
            _die("corrupt git tree: invalid entry header")
        if nul + 21 > n:
            _die("corrupt git tree: truncated object id")
        name = content[sp + 1:nul].decode("utf-8", "surrogateescape")
        sha = content[nul + 1:nul + 21].hex()
        entries.append((mode, name, sha))
        i = nul + 21
    return entries

_GIT_IDENTITY_RE = re.compile(r"^(.*) <([^>]*)> (\d+) ([+-]\d{4})$")

def _parse_git_identity(line: str) -> tuple:
    m = _GIT_IDENTITY_RE.match(line)
    if not m:
        return line.strip(), "", time.time()
    name, email, ts, _tz = m.groups()
    return name, email, float(ts)

def _parse_git_commit_text(content: bytes) -> tuple:
    lines = content.decode("utf-8", "surrogateescape").split("\n")
    tree, parents, author_line = None, [], None
    i = 0
    while i < len(lines) and lines[i] != "":
        line = lines[i]
        if line.startswith("tree "):
            tree = line[5:].strip()
        elif line.startswith("parent "):
            parents.append(line[7:].strip())
        elif line.startswith("author "):
            author_line = line[7:]
        i += 1
    message = "\n".join(lines[i + 1:]) if i < len(lines) else ""
    name, email, ts = _parse_git_identity(author_line or "")
    return tree, parents, name, email, ts, message

def _parse_git_tag_text(content: bytes) -> tuple:
    lines = content.decode("utf-8", "surrogateescape").split("\n")
    obj, tagger_line = None, None
    i = 0
    while i < len(lines) and lines[i] != "":
        line = lines[i]
        if line.startswith("object "):
            obj = line[7:].strip()
        elif line.startswith("tagger "):
            tagger_line = line[7:]
        i += 1
    message = "\n".join(lines[i + 1:]) if i < len(lines) else ""
    if tagger_line:
        name, email, ts = _parse_git_identity(tagger_line)
    else:
        name, email, ts = "Unknown", "unknown@import", time.time()
    return obj, name, email, ts, message


def _read_git_refs(git_dir: str) -> tuple:
    branches, tags = {}, {}
    for kind, dest in (("heads", branches), ("tags", tags)):
        refs_dir = os.path.join(git_dir, "refs", kind)
        if not os.path.isdir(refs_dir):
            continue
        for dirpath, _dirs, filenames in os.walk(refs_dir):
            for fname in filenames:
                full = os.path.join(dirpath, fname)
                name = os.path.relpath(full, refs_dir).replace(os.sep, "/")
                try:
                    with open(full, encoding="utf-8") as f:
                        oid = f.read().strip()
                except OSError as e:
                    _die(f"could not read git ref {full}: {e}")
                if not re.fullmatch(r"[0-9a-f]{40}", oid):
                    _die(f"corrupt git ref {full}: invalid object id")
                dest[name] = oid
    packed = os.path.join(git_dir, "packed-refs")
    if os.path.isfile(packed):
        try:
            with open(packed, encoding="utf-8") as f:
                packed_lines = list(f)
        except OSError as e:
            _die(f"could not read packed git refs {packed}: {e}")
        for line in packed_lines:
            line = line.strip()
            if not line or line.startswith("#") or line.startswith("^"):
                continue
            try:
                sha, ref = line.split(" ", 1)
            except ValueError:
                _die(f"corrupt packed git refs {packed}: malformed line")
            if not re.fullmatch(r"[0-9a-f]{40}", sha):
                _die(f"corrupt packed git refs {packed}: invalid object id")
            if ref.startswith("refs/heads/"):
                branches.setdefault(ref[len("refs/heads/"):], sha)
            elif ref.startswith("refs/tags/"):
                tags.setdefault(ref[len("refs/tags/"):], sha)
    return branches, tags

def _read_git_head(git_dir: str) -> tuple:
    head_path = os.path.join(git_dir, "HEAD")
    if not os.path.isfile(head_path):
        return ("detached", None)
    try:
        with open(head_path, encoding="utf-8") as f:
            data = f.read().strip()
    except OSError as e:
        _die(f"could not read git HEAD {head_path}: {e}")
    if data.startswith("ref:"):
        ref = data.split(" ", 1)[1].strip()
        if ref.startswith("refs/heads/"):
            return ("branch", ref[len("refs/heads/"):])
        return ("detached", None)
    if data and not re.fullmatch(r"[0-9a-f]{40}", data):
        _die(f"corrupt git HEAD {head_path}: invalid object id")
    return ("detached", data)


def _git_commit_order(tip_shas: list, store: "_GitObjectStore") -> list:
    """Return commit shas reachable from *tip_shas* in parents-first order."""
    visited = set()
    order = []
    stack = [(sha, False) for sha in tip_shas if sha]
    while stack:
        sha, processed = stack.pop()
        if processed:
            order.append(sha)
            continue
        if sha in visited:
            continue
        visited.add(sha)
        obj_type, content = store.read(sha)
        if obj_type != "commit":
            continue
        _, parents, _, _, _, _ = _parse_git_commit_text(content)
        stack.append((sha, True))
        for p in parents:
            stack.append((p, False))
    return order

def _import_git_tree(git_tree_sha: str, store: "_GitObjectStore",
                      tree_cache: dict, blob_cache: dict, warnings: list) -> str:
    if git_tree_sha in tree_cache:
        return tree_cache[git_tree_sha]
    obj_type, content = store.read(git_tree_sha)
    if obj_type != "tree":
        warnings.append(f"expected tree object {git_tree_sha}, got {obj_type}")
        tree_cache[git_tree_sha] = store_object(
            "tree", json.dumps({"type": "tree", "entries": []}, sort_keys=True).encode())
        return tree_cache[git_tree_sha]

    entries = []
    for mode, name, sha in _parse_git_tree_entries(content):
        if not _safe_path_component(name):
            warnings.append(f"skipped unsafe tree entry name {name!r}")
            continue
        if mode == "160000":
            warnings.append(f"skipped submodule '{name}' (gitlink {sha})")
            continue
        if mode in ("40000", "040000"):
            sub_oid = _import_git_tree(sha, store, tree_cache, blob_cache, warnings)
            entries.append({"name": name, "type": "tree", "oid": sub_oid})
        else:
            oid = blob_cache.get(sha)
            if oid is None:
                btype, bcontent = store.read(sha)
                if btype != "blob":
                    warnings.append(f"skipped non-blob tree entry '{name}' ({sha})")
                    continue
                oid = store_object("blob", bcontent)
                blob_cache[sha] = oid
            entries.append({"name": name, "type": "blob", "oid": oid})

    raw = json.dumps({"type": "tree", "entries": entries}, sort_keys=True).encode()
    oid = store_object("tree", raw)
    tree_cache[git_tree_sha] = oid
    return oid


def cmd_import_git(args):
    git_dir = _resolve_git_dir(args.source)
    store = _GitObjectStore(git_dir)

    dest = (os.path.abspath(args.dest) if args.dest
            else os.path.join(_INVOCATION_CWD,
                              os.path.basename(os.path.abspath(args.source).rstrip(os.sep))))
    if os.path.lexists(dest):
        _die(f"destination path '{os.path.basename(dest)}' already exists")

    branches, tags = _read_git_refs(git_dir)
    head_kind, head_value = _read_git_head(git_dir)

    warnings = []
    tip_shas = list(branches.values())
    tag_targets = {}    # name -> {"kind", "target_sha", ["tagger", "message", "timestamp"]}

    def peel_tag(sha):
        seen = 0
        while True:
            obj_type, content = store.read(sha)
            if obj_type != "tag" or seen > 10:
                return obj_type, sha
            obj, *_rest = _parse_git_tag_text(content)
            if not obj:
                return obj_type, sha
            sha = obj
            seen += 1

    for tagname, sha in tags.items():
        if not _safe_ref_name(tagname):
            warnings.append(f"skipped tag with unsafe name {tagname!r}")
            continue
        obj_type, content = store.read(sha)
        if obj_type == "tag":
            tobj, tname, temail, tts, tmessage = _parse_git_tag_text(content)
            target_type, target_sha = peel_tag(tobj) if tobj else (None, None)
            if target_type != "commit" or not target_sha:
                warnings.append(f"skipped tag '{tagname}': does not point to a commit")
                continue
            tag_targets[tagname] = dict(kind="annotated", target_sha=target_sha,
                                         tagger=f"{tname} <{temail}>",
                                         message=tmessage, timestamp=tts)
            tip_shas.append(target_sha)
        elif obj_type == "commit":
            tag_targets[tagname] = dict(kind="light", target_sha=sha)
            tip_shas.append(sha)
        else:
            warnings.append(f"skipped tag '{tagname}': points to a {obj_type}, not a commit")

    if head_kind == "detached" and head_value:
        tip_shas.append(head_value)

    order = _git_commit_order(tip_shas, store)

    print(f"Importing '{git_dir}' into '{os.path.basename(dest)}'...")
    commit_map = {}
    try:
        with _temporary_destination(dest) as build_dest:
            dest_vcs = os.path.join(build_dest, VCS_DIR)
            os.makedirs(os.path.join(dest_vcs, "refs", "heads"), exist_ok=True)
            os.makedirs(os.path.join(dest_vcs, "refs", "tags"), exist_ok=True)
            os.makedirs(os.path.join(dest_vcs, "objects"), exist_ok=True)
            write_json(os.path.join(dest_vcs, "index"), {})
            _atomic_write_text(os.path.join(dest_vcs, "HEAD"), "ref: refs/heads/main")
            write_json(os.path.join(dest_vcs, "config"),
                       {"core": {"repositoryformatversion": 0},
                        "remote": {"origin": git_dir}})

            os.chdir(build_dest)
            global _WORKTREE_ROOT
            _WORKTREE_ROOT = build_dest

            tree_cache, blob_cache = {}, {}
            for sha in order:
                obj_type, content = store.read(sha)
                if obj_type != "commit":
                    _die(f"git history entry {sha} is a {obj_type}, not a commit")
                tree_sha, parents, name, email, ts, message = _parse_git_commit_text(content)
                if not tree_sha:
                    _die(f"corrupt git commit {sha}: missing tree")
                notgit_tree = _import_git_tree(
                    tree_sha, store, tree_cache, blob_cache, warnings
                )
                missing_parents = [parent for parent in parents if parent not in commit_map]
                if missing_parents:
                    _die(f"corrupt git history at {sha}: parent was not imported")
                commit_map[sha] = create_commit(
                    notgit_tree, message, [commit_map[parent] for parent in parents],
                    author=f"{name} <{email}>", timestamp=ts,
                )

            for name, sha in branches.items():
                if not _safe_ref_name(name):
                    warnings.append(f"skipped branch with unsafe name {name!r}")
                elif sha in commit_map:
                    set_branch_commit(name, commit_map[sha])
                else:
                    warnings.append(f"skipped branch '{name}': target commit not found")

            for name, info in tag_targets.items():
                target_oid = commit_map.get(info["target_sha"])
                if target_oid is None:
                    warnings.append(f"skipped tag '{name}': target commit not found")
                    continue
                if info["kind"] == "annotated":
                    tag_data = {
                        "type": "tag", "object": target_oid, "tag": name,
                        "tagger": info["tagger"], "message": info["message"],
                        "timestamp": info["timestamp"],
                    }
                    oid = store_object(
                        "tag", json.dumps(tag_data, sort_keys=True).encode()
                    )
                else:
                    oid = target_oid
                _atomic_write_text(os.path.join(TAGS_DIR, name), oid)

            if head_kind == "branch" and head_value:
                set_head_ref(head_value)
            elif head_kind == "detached" and head_value in commit_map:
                _atomic_write_text(HEAD_FILE, commit_map[head_value])
            elif branches:
                set_head_ref(sorted(branches)[0])

            head_commit = get_head_commit()
            if head_commit:
                apply_commit(head_commit)
            else:
                print("warning: the source repository has no commits; nothing to check out.")
    finally:
        store.close()
    print(f"Converted {len(commit_map)} commit(s), {len(branches)} branch(es), "
          f"{len(tag_targets)} tag(s).")
    for w in warnings:
        print(f"warning: {w}", file=sys.stderr)
    print("done.")


# ── add ───────────────────────────────────────────────────────────────────────

def cmd_add(args):
    ensure_repo()
    index   = read_index()
    ignore  = load_ignore()
    verbose = getattr(args, 'verbose', False)
    update  = getattr(args, 'update', False)   # -u: only update tracked files
    add_all = getattr(args, 'all', False)
    patch_mode = getattr(args, 'patch', False)
    dry_run = getattr(args, 'dry_run', False)
    force   = getattr(args, 'force', False)
    targets = list(args.files or [])
    if add_all and not targets:
        targets = ["."]
    if not targets:
        _die("Nothing specified, nothing added.")

    to_stage  = []   # rel paths whose content should be stored + indexed
    to_delete = []   # rel paths to remove from index (deleted from disk)
    add_errors = False

    for target in targets:
        if target in (".", "./"):
            root = normalize_pathspec(target)
            wt = (working_tree_paths(root, index=index, force=force, patterns=ignore)
                  if root != "." else
                  working_tree_paths(index=index, force=force, patterns=ignore))
            for rel in wt:
                if not update or rel in index:
                    to_stage.append(rel)
            # stage removals of tracked files that have vanished from disk
            for rel in index:
                if (root == "." or rel == root or rel.startswith(root + "/")) and rel not in wt:
                    to_delete.append(rel)

        elif os.path.isdir(normalize_pathspec(target)):
            target_rel = normalize_pathspec(target)
            dir_prefix = target_rel
            dir_prefix = "" if dir_prefix in (".", "") else dir_prefix + "/"
            wt = working_tree_paths(
                target_rel, index=index, force=force, patterns=ignore
            )
            for rel in wt:
                if not update or rel in index:
                    to_stage.append(rel)
            for rel in index:
                if (not dir_prefix or rel.startswith(dir_prefix)) and rel not in wt:
                    to_delete.append(rel)

        elif os.path.isfile(normalize_pathspec(target)):
            rel = normalize_pathspec(target)
            if is_ignored(rel, ignore) and rel not in index and not force:
                print(f"The following paths are ignored by your {IGNORE_FILE}: {rel}")
            else:
                to_stage.append(rel)

        else:
            rel = normalize_pathspec(target)
            # tracked file deleted from disk → stage the removal
            if rel in index:
                to_delete.append(rel)
                continue
            # try glob
            pattern = target if os.path.isabs(target) else os.path.join(_INVOCATION_CWD, target)
            matched = glob.glob(pattern, recursive=True)
            if not matched:
                _err(f"pathspec '{target}' did not match any files")
                add_errors = True
                continue
            for m in matched:
                mrel = normalize_pathspec(m)
                if (force or not is_ignored(mrel, ignore) or mrel in index) and os.path.isfile(m):
                    to_stage.append(mrel)

    if add_errors:
        sys.exit(1)

    if patch_mode:
        selected_stage, selected_delete = [], []
        old_tree = read_index()
        for path in sorted(set(to_stage)):
            old_lines = map_blob_lines(old_tree, path)
            try:
                with open(path, "rb") as fh:
                    new_lines = fh.read().decode(errors="replace").splitlines(True)
            except OSError:
                new_lines = None
            if old_lines == new_lines:
                continue
            print_diff(path, old_lines, new_lines)
            ans = input(f"stage this change to '{path}' [y,n]? ").strip().lower()
            if ans.startswith("y"):
                selected_stage.append(path)
        for path in sorted(set(to_delete)):
            print_diff(path, map_blob_lines(old_tree, path), None)
            ans = input(f"stage deletion of '{path}' [y,n]? ").strip().lower()
            if ans.startswith("y"):
                selected_delete.append(path)
        to_stage, to_delete = selected_stage, selected_delete

    if dry_run:
        for path in sorted(set(to_stage)):
            print(f"add '{path}'")
        for path in sorted(set(to_delete)):
            print(f"remove '{path}'")
        return

    had_error = False
    verbose_paths = []
    times = read_index_times()
    now = time.time()
    for path in sorted(set(to_stage)):
        try:
            oid = store_blob_file(path)
            index[path] = oid
            times[path] = now
            if verbose:
                verbose_paths.append(f"add '{path}'")
        except OSError as e:
            _err(f"could not stage '{path}': {e}")
            had_error = True
    if had_error:
        sys.exit(1)
    for path in sorted(set(to_delete)):
        if path in index:
            del index[path]
            times.pop(path, None)
            if verbose:
                verbose_paths.append(f"remove '{path}'")

    write_index(index)
    write_json(INDEX_TIMES_FILE, times)
    _mark_conflicts_resolved(set(to_stage) | set(to_delete))
    for message in verbose_paths:
        print(message)


# ── rm ────────────────────────────────────────────────────────────────────────

def cmd_rm(args):
    ensure_repo()
    index = read_index()
    head = get_head_commit()
    committed = read_tree(read_commit(head)["tree"]) if head else {}
    force = getattr(args, "force", False)
    dry_run = getattr(args, "dry_run", False)
    quiet = getattr(args, "quiet", False)
    ignore_unmatch = getattr(args, "ignore_unmatch", False)
    planned = []
    had_error = False

    # Validate every path before mutating either the index or the worktree.
    for target in args.files:
        rel = normalize_pathspec(target)
        if rel not in index:
            if not ignore_unmatch:
                _err(f"pathspec '{target}' did not match any files known to notgit")
                had_error = True
            continue

        disk_oid = None
        if os.path.isfile(rel):
            try:
                disk_oid = hash_blob_file(rel)
            except OSError as e:
                _err(f"could not inspect '{rel}': {e}")
                had_error = True
                continue

        # Let the removal phase report the underlying I/O error for a tracked
        # path that has been replaced by a directory or other non-file node.
        # Such a node can never pass the content safety check or be removed by
        # os.remove(), and retaining this path preserves the index entry.
        if os.path.exists(rel) and not os.path.isfile(rel):
            planned.append(rel)
            continue

        if not force:
            if args.cached:
                safe = index[rel] in (committed.get(rel), disk_oid)
            else:
                safe = (disk_oid is not None
                        and index[rel] == committed.get(rel) == disk_oid)
            if not safe:
                _err(f"the following file has staged or unstaged changes: '{rel}'")
                _err("use --force to remove it")
                had_error = True
                continue
        planned.append(rel)

    if had_error:
        sys.exit(1)

    if dry_run:
        if not quiet:
            for rel in planned:
                print(f"rm '{rel}'")
        return

    times = read_index_times()
    for rel in planned:
        if not args.cached:
            try:
                os.remove(rel)
            except OSError as e:
                _err(f"could not remove '{rel}': {e}")
                had_error = True
                continue
            _prune_empty_parents(rel)
        del index[rel]
        times.pop(rel, None)
        if not quiet:
            print(f"rm '{rel}'")
    write_index(index)
    write_json(INDEX_TIMES_FILE, times)
    _mark_conflicts_resolved(planned)
    if had_error:
        sys.exit(1)


# ── mv ────────────────────────────────────────────────────────────────────────

def _tracked_paths_for_source(index: dict, src: str) -> list:
    if src in index:
        return [src]
    prefix = src.rstrip("/") + "/"
    return sorted(path for path in index if path.startswith(prefix))

def _mv_target_for_source(src: str, dest: str, dest_is_dir: bool, src_paths: list) -> str:
    if dest_is_dir:
        base = os.path.basename(src.rstrip("/"))
        return f"{dest.rstrip('/')}/{base}" if dest.rstrip("/") else base
    if len(src_paths) > 1:
        return dest.rstrip("/")
    return dest

def cmd_mv(args):
    ensure_repo()
    sources = args.paths[:-1]
    dest_arg = args.paths[-1]
    if not sources:
        _die("missing source")

    index = read_index()
    times = read_index_times()
    dest = normalize_pathspec(dest_arg)
    dest_exists = os.path.exists(dest)
    dest_is_dir = dest_exists and os.path.isdir(dest)

    if len(sources) > 1 and not dest_is_dir:
        _die(f"destination '{dest_arg}' is not a directory")

    moves = []
    planned_dests = set()
    had_error = False

    for src_arg in sources:
        src = normalize_pathspec(src_arg)
        tracked = _tracked_paths_for_source(index, src)
        if not tracked:
            _err(f"source '{src_arg}' is not under version control")
            had_error = True
            continue
        if not os.path.exists(src):
            _err(f"bad source, source='{src_arg}', destination='{dest_arg}'")
            had_error = True
            continue

        actual_dest = _mv_target_for_source(src, dest, dest_is_dir, tracked)
        if actual_dest == ".":
            actual_dest = os.path.basename(src.rstrip("/"))
        ensure_repo_relative_path(actual_dest)

        src_prefix = src.rstrip("/") + "/"
        dest_prefix = actual_dest.rstrip("/") + "/"
        if actual_dest == src or dest_prefix.startswith(src_prefix):
            _err(f"can not move directory into itself, source={src_arg}, destination={dest_arg}")
            had_error = True
            continue
        if os.path.isdir(src) and os.path.lexists(actual_dest):
            # shutil.move would nest the source inside the existing directory
            # and leave the index pointing at paths that do not exist.
            _err(f"destination already exists, source={src_arg}, destination={actual_dest}")
            had_error = True
            continue

        rewritten = []
        if len(tracked) == 1 and tracked[0] == src:
            rewritten.append((src, actual_dest))
        else:
            prefix = src.rstrip("/") + "/"
            for old_path in tracked:
                suffix = old_path[len(prefix):]
                rewritten.append((old_path, actual_dest.rstrip("/") + "/" + suffix))

        for old_path, new_path in rewritten:
            if new_path in planned_dests:
                _err(f"destination '{new_path}' specified more than once")
                had_error = True
                break
            if new_path in index and new_path not in tracked and not args.force:
                _err(f"destination '{new_path}' already exists in index")
                had_error = True
                break
            if os.path.exists(new_path) and new_path not in tracked and not args.force:
                _err(f"destination '{new_path}' already exists")
                had_error = True
                break
            planned_dests.add(new_path)
        else:
            moves.append((src, actual_dest, tracked, rewritten))

    if had_error:
        sys.exit(1)

    if getattr(args, "dry_run", False):
        for _src, _dest, _tracked, rewritten in moves:
            for old_path, new_path in rewritten:
                print(f"rename '{old_path}' -> '{new_path}'")
        return

    for src, actual_dest, tracked, rewritten in moves:
        os.makedirs(os.path.dirname(actual_dest) or ".", exist_ok=True)
        try:
            if args.force and os.path.exists(actual_dest) and not os.path.isdir(src):
                if os.path.isdir(actual_dest):
                    _err(f"destination '{actual_dest}' is a directory")
                    had_error = True
                    continue
                os.replace(src, actual_dest)
            else:
                shutil.move(src, actual_dest)
        except OSError as e:
            _err(f"could not move '{src}' to '{actual_dest}': {e}")
            had_error = True
            continue

        for old_path, new_path in rewritten:
            index[new_path] = index.pop(old_path)
            if old_path in times:
                times[new_path] = times.pop(old_path)
            print(f"rename '{old_path}' -> '{new_path}'")

    write_index(index)
    write_json(INDEX_TIMES_FILE, times)
    if had_error:
        sys.exit(1)


# ── commit ────────────────────────────────────────────────────────────────────

def _commit_message_from_args(args):
    message = getattr(args, "message", None)
    message_file = getattr(args, "message_file", None)
    if message_file is not None:
        if message is not None:
            _die("options '-m' and '-F' cannot be used together")
        try:
            if message_file == "-":
                if sys.stdin is None:
                    _die("could not read commit message from standard input")
                raw = sys.stdin.buffer.read()
            else:
                # Relative paths are relative to where notgit was invoked,
                # not the repo root that ensure_repo() chdir'd into.
                with open(os.path.join(_INVOCATION_CWD, message_file), "rb") as f:
                    raw = f.read()
        except OSError as e:
            _die(f"could not read commit message file '{message_file}': {e}")
        message = _cleanup_message(raw.decode("utf-8", errors="replace"))
    return message


def _cleanup_message(text: str) -> str:
    """Git's 'whitespace' cleanup: strip trailing whitespace on each line,
    collapse runs of blank lines, and drop leading/trailing blank lines."""
    out = []
    for line in text.replace("\r\n", "\n").split("\n"):
        line = line.rstrip()
        if not line and (not out or not out[-1]):
            continue
        out.append(line)
    while out and not out[-1]:
        out.pop()
    return "\n".join(out)


def _append_signoff(message: str) -> str:
    name, email = get_author()
    trailer = f"Signed-off-by: {name} <{email}>"
    if trailer in message.splitlines():
        return message
    return message.rstrip("\n") + "\n\n" + trailer


def _print_commit_dry_run(index: dict, committed: dict):
    changed = sorted(set(index) | set(committed))
    changed = [p for p in changed if index.get(p) != committed.get(p)]
    if not changed:
        print("nothing to commit, working tree clean")
        return False
    print("Changes to be committed:")
    for path in changed:
        if path not in committed:
            status = "new file"
        elif path not in index:
            status = "deleted"
        else:
            status = "modified"
        print(f"\t{status}:   {path}")
    return True


def cmd_commit(args):
    ensure_repo()
    index     = read_index()
    head      = get_head_commit()
    amend     = getattr(args, "amend", False)
    dry_run   = getattr(args, "dry_run", False)
    supplied_message = _commit_message_from_args(args)

    # Stage all tracked modified files when -a is given
    if getattr(args, "all", False):
        wt = working_tree_oids(index=index)
        for path, oid in wt.items():
            if path in index and index[path] != oid:
                index[path] = oid if dry_run else store_blob_file(path)
        # also remove deleted tracked files from index
        for path in list(index):
            if path not in wt:
                del index[path]

    committed = read_tree(read_commit(head)["tree"]) if head else {}
    if dry_run:
        # Like git, a dry run with nothing to commit exits 1.
        if not _print_commit_dry_run(index, committed):
            sys.exit(1)
        return

    if amend:
        if not head:
            _die("You have nothing to amend – no commits yet")
        if os.path.isfile(MERGE_HEAD_FILE) or os.path.isfile(REVERT_HEAD_FILE):
            _die("cannot amend while a merge or revert is in progress")
        old_commit = read_commit(head)
        message = (old_commit["message"] if getattr(args, "no_edit", False)
                   else (supplied_message
                         if supplied_message is not None else old_commit["message"]))
        if getattr(args, "signoff", False):
            message = _append_signoff(message)
        if not message and not getattr(args, "allow_empty_message", False):
            _die("empty commit message not allowed")
        parents    = old_commit.get("parents", [])
        tree_oid   = build_tree(index)
        author     = getattr(args, "author", None) or old_commit.get("author")
        timestamp  = parse_timestamp(args.date) if getattr(args, "date", None) else old_commit.get("timestamp")
        commit_oid = create_commit(tree_oid, message, parents,
                                   author=author, timestamp=timestamp)
        protected = [_head_update_path()]
        if getattr(args, "all", False):
            protected.append(INDEX_FILE)
        if os.path.isfile(REVERT_HEAD_FILE):
            protected.extend(_revert_state_paths())
        with _repository_transaction(metadata_paths=protected):
            if getattr(args, "all", False):
                write_index(index)
            update_head(commit_oid)
            if os.path.isfile(REVERT_HEAD_FILE):
                _clear_revert_state()
        if not getattr(args, "quiet", False):
            branch = current_branch()
            label  = branch if branch else "detached HEAD"
            print(f"[{label} {commit_oid[:7]}] {_pretty_subject(message)}")
        return

    merge_head, merge_msg = _read_merge_state()
    if _pending_conflicts(MERGE_CONFLICTS_FILE) or _pending_conflicts(REVERT_CONFLICTS_FILE):
        _die("cannot commit: unmerged paths remain")

    if (index == committed and not merge_head
            and not getattr(args, "allow_empty", False)):
        branch = current_branch() or "HEAD"
        wt = working_tree_oids(index=index)
        untracked = sorted(p for p in wt if p not in index)
        if untracked:
            print(f"On branch {branch}\n"
                  "nothing to commit but untracked files present "
                  '(use "notgit add" to track)')
        else:
            print(f"On branch {branch}\nnothing to commit, working tree clean")
        sys.exit(1)

    message = supplied_message if supplied_message is not None else (merge_msg if merge_head else None)
    if message is None:
        _die("no commit message given (use -m <message>)")
    if not message and not getattr(args, "allow_empty_message", False):
        _die("empty commit message not allowed")
    if getattr(args, "signoff", False):
        message = _append_signoff(message)

    parents = [head] if head else []
    if merge_head and merge_head != head:
        parents.append(merge_head)

    tree_oid   = build_tree(index)          # ← commit from INDEX, not from disk
    commit_oid = create_commit(
        tree_oid, message, parents,
        author=getattr(args, "author", None),
        timestamp=(parse_timestamp(args.date) if getattr(args, "date", None) else None),
    )
    protected = [_head_update_path(), *_merge_state_paths()]
    if getattr(args, "all", False):
        protected.append(INDEX_FILE)
    if os.path.isfile(REVERT_HEAD_FILE):
        protected.extend(_revert_state_paths())
    with _repository_transaction(metadata_paths=protected):
        if getattr(args, "all", False):
            write_index(index)
        update_head(commit_oid)
        _clear_merge_state()
        if os.path.isfile(REVERT_HEAD_FILE):
            _clear_revert_state()

    if getattr(args, "quiet", False):
        return
    branch = current_branch()
    label  = branch if branch else "detached HEAD"
    print(f"[{label} {commit_oid[:7]}] {_pretty_subject(message)}")

    # summary stats
    all_paths = set(committed) | set(index)
    new_f  = sorted(p for p in all_paths if p in index and p not in committed)
    del_f  = sorted(p for p in all_paths if p not in index and p in committed)
    mod_f  = sorted(p for p in all_paths
                    if p in index and p in committed and index[p] != committed[p])
    total  = len(new_f) + len(del_f) + len(mod_f)
    ins = dels = 0
    for p in new_f + del_f + mod_f:
        p_ins, p_dels = _count_ins_dels(blob_lines(committed.get(p)),
                                        blob_lines(index.get(p)))
        ins  += p_ins
        dels += p_dels
    parts = [f"{total} file{'s' if total != 1 else ''} changed"]
    if ins:  parts.append(f"{ins} insertion{'s' if ins!=1 else ''}(+)")
    if dels: parts.append(f"{dels} deletion{'s' if dels!=1 else ''}(-)")
    print(" " + ", ".join(parts))
    for p in new_f: print(f" create mode 100644 {p}")
    for p in del_f: print(f" delete mode 100644 {p}")


# ── log ───────────────────────────────────────────────────────────────────────

def _pretty_subject(message: str) -> str:
    return ((message or "").splitlines() or [""])[0]


def _indent_message(message: str) -> str:
    return "\n".join(("    " + l) if l else "" for l in (message or "").split("\n"))


def _format_log_pretty(fmt: str, oid: str, commit: dict) -> str:
    if fmt.startswith("format:"):
        fmt = fmt[len("format:"):]
    percent_token = "\0PERCENT\0"
    fmt = fmt.replace("%%", percent_token)
    author = commit.get("author", "Unknown")
    author_name = author.split("<", 1)[0].strip() or author
    replacements = {
        "%H": oid,
        "%h": oid[:7],
        "%s": _pretty_subject(commit.get("message", "")),
        "%an": author_name,
    }
    out = fmt
    for key in sorted(replacements, key=len, reverse=True):
        out = out.replace(key, replacements[key])
    return out.replace(percent_token, "%")


def _commit_diff_pairs(oid: str, commit=None):
    commit = commit or read_commit(oid)
    parents = commit.get("parents", [])
    parent_files = read_tree(read_commit(parents[0])["tree"]) if parents else {}
    cur_files = read_tree(commit["tree"])
    return [
        (path, map_blob_lines(parent_files, path), map_blob_lines(cur_files, path))
        for path in sorted(set(parent_files) | set(cur_files))
        if parent_files.get(path) != cur_files.get(path)
    ]


def _print_history_diff_options(args, oid: str, commit: dict, *, default_patch=False):
    stat = getattr(args, "stat", False)
    name_only = getattr(args, "name_only", False)
    name_status = getattr(args, "name_status", False)
    patch = getattr(args, "patch", False)
    no_patch = getattr(args, "no_patch", False)
    if not (stat or name_only or name_status or patch or default_patch):
        return
    if no_patch and not (stat or name_only or name_status):
        return
    pairs = _commit_diff_pairs(oid, commit)
    if name_only:
        for path, _a, _b in pairs:
            print(path)
    elif name_status:
        _print_name_status(pairs)
    elif stat:
        _print_stat(pairs)
    elif patch or default_patch:
        for path, a_lines, b_lines in pairs:
            print_diff(path, a_lines, b_lines, "a", "b")


def cmd_log(args):
    ensure_repo()
    head = get_head_commit()
    if not head:
        b = current_branch() or "HEAD"
        print(f"fatal: your current branch '{b}' does not have any commits yet",
              file=sys.stderr)
        sys.exit(1)

    # build decoration map  oid → [label, …]
    decorations: dict[str, list] = {}
    cur = current_branch()
    for b in list_branches():
        bc = get_branch_commit(b)
        if bc:
            label = green(f"HEAD -> {b}") if b == cur else green(b)
            decorations.setdefault(bc, []).append(label)
    # detached HEAD: annotate the head commit with "HEAD"
    if cur is None:
        decorations.setdefault(head, []).insert(0, cyan("HEAD"))
    for t in list_tags():
        tc = get_tag_commit(t)
        if tc:
            decorations.setdefault(tc, []).append(yellow(f"tag: {t}"))

    pretty     = getattr(args, "pretty", None)
    oneline    = getattr(args, "oneline", False)
    reverse    = getattr(args, "reverse", False)
    max_count  = getattr(args, "n", None)
    skip_count = max(0, getattr(args, "skip", 0) or 0)
    path_filter = normalize_pathspec(args.path) if getattr(args, "path", None) else None
    if path_filter == ".":
        path_filter = None
    count, matched_count = 0, 0
    starts = [head]
    if getattr(args, "all", False):
        starts = [oid for oid in (
            [get_branch_commit(b) for b in list_branches()] +
            [get_tag_commit(t) for t in list_tags()]
        ) if oid]
    first_parent = getattr(args, "first_parent", False)
    reachable = {}
    pending_children = {}
    stack = list(starts)
    while stack:
        oid = stack.pop()
        if not oid or oid in reachable:
            continue
        commit = read_commit(oid)
        reachable[oid] = commit
        parents = commit.get("parents", [])[:1] if first_parent else commit.get("parents", [])
        for parent in parents:
            pending_children[parent] = pending_children.get(parent, 0) + 1
            stack.append(parent)
    for oid in reachable:
        pending_children.setdefault(oid, 0)
    ready = [
        (-reachable[oid].get("timestamp", 0), oid)
        for oid, children in pending_children.items()
        if children == 0 and oid in reachable
    ]
    heapq.heapify(ready)
    ordered = []
    while ready:
        _neg_timestamp, oid = heapq.heappop(ready)
        ordered.append(oid)
        parents = reachable[oid].get("parents", [])
        if first_parent:
            parents = parents[:1]
        for parent in parents:
            pending_children[parent] -= 1
            if pending_children[parent] == 0:
                heapq.heappush(
                    ready, (-reachable[parent].get("timestamp", 0), parent)
                )

    commits = []
    author_filter = getattr(args, "author", None)
    grep_filter = getattr(args, "grep", None)
    since = parse_timestamp(args.since) if getattr(args, "since", None) else None
    until = parse_timestamp(args.until) if getattr(args, "until", None) else None

    for oid in ordered:
        commit = reachable[oid]
        parents = commit.get("parents", [])

        # path filter: skip commits that didn't touch the given path
        if path_filter:
            # Compare the object at the path, so a directory matches when
            # anything beneath it changed, without flattening whole trees.
            cur_blob  = _tree_path_oid(commit["tree"], path_filter)
            par_blobs = (
                {_tree_path_oid(read_commit(p)["tree"], path_filter) for p in parents}
                if parents else {None}
            )
            if par_blobs == {cur_blob}:
                continue

        matches_filters = True
        if author_filter and author_filter.lower() not in commit.get("author", "").lower():
            matches_filters = False
        if grep_filter and grep_filter.lower() not in commit.get("message", "").lower():
            matches_filters = False
        if since is not None and commit["timestamp"] < since:
            matches_filters = False
        if until is not None and commit["timestamp"] > until:
            matches_filters = False
        if getattr(args, "merges", False) and len(parents) < 2:
            matches_filters = False
        if getattr(args, "no_merges", False) and len(parents) > 1:
            matches_filters = False

        if matches_filters:
            if matched_count < skip_count:
                matched_count += 1
            else:
                if max_count is not None and count >= max_count:
                    break
                matched_count += 1
                count += 1
                commits.append((oid, commit, parents))

    if reverse:
        commits.reverse()

    for oid, commit, parents in commits:
        ts = time.strftime("%a %b %d %H:%M:%S %Y",
                           time.localtime(commit["timestamp"]))
        deco = decorations.get(oid, [])
        deco_str = f" ({', '.join(deco)})" if deco else ""

        prefix = "* " if getattr(args, "graph", False) else ""
        if pretty:
            print(prefix + _format_log_pretty(pretty, oid, commit))
        elif oneline:
            subject = _pretty_subject(commit.get("message", ""))
            print(f"{prefix}{yellow(oid[:7])}{deco_str} {subject}")
        else:
            print(prefix + yellow(f"commit {oid}") + deco_str)
            if len(parents) > 1:
                print(f"Merge: {' '.join(p[:7] for p in parents)}")
            print(f"Author: {commit.get('author', 'Unknown')}")
            print(f"Date:   {ts}")
            print("\n" + _indent_message(commit["message"]) + "\n")
        _print_history_diff_options(args, oid, commit)


# ── status ────────────────────────────────────────────────────────────────────

def cmd_status(args):
    ensure_repo()
    index     = read_index()
    head      = get_head_commit()
    committed = read_tree(read_commit(head)["tree"]) if head else {}
    wt        = working_tree_oids(index=index)

    # staged vs committed
    s_new  = sorted(p for p in index if p not in committed)
    s_del  = sorted(p for p in committed if p not in index)
    s_mod  = sorted(p for p in index if p in committed and index[p] != committed[p])

    # worktree vs index
    wt_mod = sorted(p for p, oid in wt.items() if p in index and index[p] != oid)
    wt_del = sorted(p for p in index if p not in wt)

    # untracked / ignored
    untracked = sorted(p for p in wt if p not in index)
    untracked_mode = getattr(args, "untracked_files", None)
    if untracked_mode == "no":
        untracked = []
    ignored = []
    if getattr(args, "ignored", None) not in (None, False, "no"):
        visible = set(working_tree_paths(index=index))
        all_paths = set(working_tree_paths(index=index, force=True))
        ignored = sorted(all_paths - visible - set(index))

    has_staged   = bool(s_new or s_del or s_mod)
    has_unstaged = bool(wt_mod or wt_del)

    porcelain = getattr(args, "porcelain", None)
    null_terminated = getattr(args, "null", False)
    def status_path(path):
        if null_terminated or not any(ord(c) < 32 or c in '\\"' for c in path):
            return path
        return json.dumps(path, ensure_ascii=False)

    def file_mode(oid):
        return "100644" if oid else "000000"

    if getattr(args, "short", False) or porcelain or null_terminated:
        lines = []
        if getattr(args, "branch", False):
            branch = current_branch()
            if str(porcelain) == "2":
                lines.append(f"# branch.oid {head or '(initial)'}")
                lines.append(f"# branch.head {branch or '(detached)'}")
            else:
                if branch:
                    lines.append(f"## {branch}" if head else f"## No commits yet on {branch}")
                else:
                    lines.append("## HEAD (no branch)")

        staged_status = {}
        staged_status.update((p, "A") for p in s_new)
        staged_status.update((p, "M") for p in s_mod)
        staged_status.update((p, "D") for p in s_del)

        worktree_status = {}
        worktree_status.update((p, "M") for p in wt_mod)
        worktree_status.update((p, "D") for p in wt_del)

        # Porcelain v2 marks an unchanged side with "." so fields stay
        # space-separated; v1/short use a blank.
        unchanged = "." if str(porcelain) == "2" else " "
        for p in sorted(set(staged_status) | set(worktree_status)):
            xy = f"{staged_status.get(p, unchanged)}{worktree_status.get(p, unchanged)}"
            shown_path = status_path(p)
            if str(porcelain) == "2":
                zero = "0" * 40
                lines.append(
                    f"1 {xy} N... {file_mode(committed.get(p))} "
                    f"{file_mode(index.get(p))} {file_mode(wt.get(p))} "
                    f"{committed.get(p, zero)} {index.get(p, zero)} {shown_path}"
                )
            else:
                lines.append(f"{xy} {shown_path}")
        for p in untracked:
            shown_path = status_path(p)
            lines.append(f"? {shown_path}" if str(porcelain) == "2" else f"?? {shown_path}")
        for p in ignored:
            shown_path = status_path(p)
            lines.append(f"! {shown_path}" if str(porcelain) == "2" else f"!! {shown_path}")
        terminator = "\0" if null_terminated else "\n"
        if lines:
            sys.stdout.write(terminator.join(lines) + terminator)
        return

    branch = current_branch()
    if branch:
        print(f"On branch {branch}")
    else:
        short = head[:7] if head else "???"
        print(f"HEAD detached at {short}")

    if not head:
        print("\nNo commits yet\n")

    if has_staged:
        print('\nChanges to be committed:')
        print(f'  (use "notgit reset HEAD <file>..." to unstage)\n')
        for p in s_new: print(f"\t{green('new file:   ' + p)}")
        for p in s_mod: print(f"\t{green('modified:   ' + p)}")
        for p in s_del: print(f"\t{green('deleted:    ' + p)}")

    if has_unstaged:
        print('\nChanges not staged for commit:')
        print(f'  (use "notgit add <file>..." to update what will be committed)')
        print(f'  (use "notgit restore <file>..." to discard changes)\n')
        for p in wt_mod: print(f"\t{red('modified:   ' + p)}")
        for p in wt_del: print(f"\t{red('deleted:    ' + p)}")

    if untracked:
        print('\nUntracked files:')
        print(f'  (use "notgit add <file>..." to include in what will be committed)\n')
        for p in untracked:
            print(f"\t{red(p)}")

    if ignored:
        print("\nIgnored files:")
        for p in ignored:
            print(f"\t{red(p)}")

    if getattr(args, "show_stash", False):
        stash_count = len(_stash_load())
        if stash_count:
            print(f"\nYour stash currently has {stash_count} entr{'y' if stash_count == 1 else 'ies'}")

    if not has_staged and not has_unstaged and not untracked:
        print("nothing to commit, working tree clean")
    elif not has_staged:
        print('\nno changes added to commit '
              '(use "notgit add" and/or "notgit commit -a")')


# ── diff ──────────────────────────────────────────────────────────────────────

def _diff_pairs(args):
    """Return list of (path, a_lines, b_lines) for the requested diff."""
    staged  = getattr(args, "staged", False)
    raw     = list(getattr(args, "commits", []) or [])
    pairs   = []

    # Split on explicit -- separator: everything after it is a forced path spec,
    # bypassing revision detection in _split_revs_and_paths.
    if "--" in raw:
        sep = raw.index("--")
        forced_paths = raw[sep + 1:]
        raw = raw[:sep]
    else:
        forced_paths = []

    if staged:
        # --staged compares the requested commit (HEAD by default) vs index.
        staged_revs, path_specs_from_raw = _split_revs_and_paths(raw)
        path_specs = path_specs_from_raw + forced_paths
        base_oid = (resolve_commit(staged_revs[0])
                    if staged_revs else get_head_commit())
        a_map = read_tree(read_commit(base_oid)["tree"]) if base_oid else {}
        b_map = read_index()
        for path in sorted(set(a_map) | set(b_map)):
            if a_map.get(path) != b_map.get(path):
                pairs.append((path, map_blob_lines(a_map, path),
                              map_blob_lines(b_map, path)))
    else:
        commits, remaining_paths = _split_revs_and_paths(raw)
        path_specs = remaining_paths + forced_paths

        if len(commits) >= 2:
            a_oid = resolve_commit(commits[0])
            b_oid = resolve_commit(commits[1])
            if not a_oid or not b_oid:
                _die("bad revision")
            a_map = read_tree(read_commit(a_oid)["tree"])
            b_map = read_tree(read_commit(b_oid)["tree"])
            for path in sorted(set(a_map) | set(b_map)):
                if a_map.get(path) != b_map.get(path):
                    pairs.append((path, map_blob_lines(a_map, path),
                                  map_blob_lines(b_map, path)))
        elif len(commits) == 1:
            c_oid = resolve_commit(commits[0])
            if not c_oid:
                _die(f"bad revision '{commits[0]}'")
            c_map = read_tree(read_commit(c_oid)["tree"])
            current_index = read_index()
            wt = working_tree_oids(index=current_index)
            tracked = set(c_map) | set(current_index)
            for path in sorted(tracked):
                # Compare object ids: decoded text cannot tell apart binary
                # contents whose invalid bytes all decode to U+FFFD.
                if c_map.get(path) != wt.get(path):
                    a_lines = map_blob_lines(c_map, path)
                    b_lines = _read_file_lines(path) if path in wt else None
                    pairs.append((path, a_lines, b_lines))
        else:
            index = read_index()
            wt = working_tree_oids(index=index)
            for path in sorted(index):
                idx_oid = index.get(path)
                wt_oid = wt.get(path)
                if idx_oid != wt_oid:
                    a_lines = map_blob_lines(index, path)
                    b_lines = _read_file_lines(path) if path in wt else None
                    pairs.append((path, a_lines, b_lines))

    if path_specs:
        norm = [normalize_pathspec(p) for p in path_specs]
        # A bare "." pathspec means "everything" — no filtering needed.
        if "." not in norm:
            pairs = [
                (fp, a, b) for fp, a, b in pairs
                if any(fp == n or fp.startswith(n + "/") for n in norm)
            ]

    return pairs


def _print_stat(pairs):
    """Print a git-style --stat summary for a list of (path, a_lines, b_lines)."""
    rows = []
    tot_ins = tot_dels = 0
    for path, a_lines, b_lines in pairs:
        ins, dels = _count_ins_dels(a_lines or [], b_lines or [])
        rows.append((path, ins, dels))
        tot_ins  += ins
        tot_dels += dels

    if not rows:
        return
    max_path  = max(len(r[0]) for r in rows)
    max_total = max(r[1] + r[2] for r in rows) or 1
    bar_width = 40
    for path, ins, dels in rows:
        total = ins + dels
        bar   = (
            green("+" * round(ins  / max_total * bar_width)) +
            red(  "-" * round(dels / max_total * bar_width))
        )
        print(f" {path:<{max_path}} | {total:>4} {bar}")

    n = len(rows)
    parts = [f"{n} file{'s' if n != 1 else ''} changed"]
    if tot_ins:  parts.append(f"{tot_ins} insertion{'s' if tot_ins!=1 else ''}(+)")
    if tot_dels: parts.append(f"{tot_dels} deletion{'s' if tot_dels!=1 else ''}(-)")
    print(" " + ", ".join(parts))

def _print_name_status(pairs):
    for path, a_lines, b_lines in pairs:
        a_exists = a_lines is not None
        b_exists = b_lines is not None
        a_lines = a_lines or []
        b_lines = b_lines or []
        if not a_exists and b_exists:
            code = "A"
        elif a_exists and not b_exists:
            code = "D"
        else:
            code = "M"
        print(f"{code}\t{path}")

def _print_word_diff(path, a_lines, b_lines):
    print(f"diff --notgit a/{path} b/{path}")
    old = "".join(a_lines or []).split()
    new = "".join(b_lines or []).split()
    chunks = []
    for part in difflib.ndiff(old, new):
        if part.startswith("- "):
            chunks.append("[-" + part[2:] + "-]")
        elif part.startswith("+ "):
            chunks.append("{+" + part[2:] + "+}")
        elif part.startswith("  "):
            chunks.append(part[2:])
    print(" ".join(chunks))

def _diff_check(pairs) -> int:
    errors = 0
    for path, _a_lines, b_lines in pairs:
        b_lines = b_lines or []
        for group in difflib.SequenceMatcher(a=_a_lines or [], b=b_lines).get_opcodes():
            tag, _i1, _i2, j1, j2 = group
            if tag == "equal":
                continue
            for offset, line in enumerate(b_lines[j1:j2], j1 + 1):
                stripped = line.rstrip("\n")
                if stripped.endswith(" ") or stripped.endswith("\t"):
                    print(f"{path}:{offset}: trailing whitespace.")
                    errors += 1
    return errors


def _read_file_lines(path: str) -> list:
    """Read a file from disk and return its lines, or [] if it does not exist."""
    try:
        with open(path, "rb") as fh:
            return fh.read().decode(errors="replace").splitlines(True)
    except FileNotFoundError:
        return []


def cmd_diff(args):
    if getattr(args, "no_index", False):
        commits = list(getattr(args, "commits", []) or [])
        # strip a leading "--" that callers may pass
        if commits and commits[0] == "--":
            commits = commits[1:]
        if len(commits) != 2:
            _die("--no-index requires exactly two file paths")
        file_a, file_b = commits
        contents = []
        for path in (file_a, file_b):
            if not os.path.exists(path):
                _die(f"path '{path}' does not exist")
            if not os.path.isfile(path):
                _die(f"--no-index only compares regular files: '{path}'")
            try:
                with open(path, "rb") as fh:
                    contents.append(fh.read())
            except OSError as e:
                _die(f"could not read '{path}': {e}")
        same = contents[0] == contents[1]
        a_lines, b_lines = (data.decode(errors="replace").splitlines(True)
                            for data in contents)
        stat = getattr(args, "stat", False)
        label = os.path.basename(file_a) if file_a == file_b else file_a
        pairs = [] if same else [(label, a_lines, b_lines)]
        quiet = getattr(args, "quiet", False)
        if quiet:
            sys.exit(1 if pairs else 0)
        if getattr(args, "check", False):
            sys.exit(1 if _diff_check(pairs) else 0)
        if getattr(args, "name_only", False):
            for path, _a, _b in pairs:
                print(path)
        elif getattr(args, "name_status", False):
            _print_name_status(pairs)
        elif stat:
            _print_stat([(label, a_lines or [], b_lines or [])])
        elif getattr(args, "word_diff", False):
            for path, old, new in pairs:
                _print_word_diff(path, old, new)
        else:
            print_diff(label, a_lines, b_lines,
                       a_label=file_a, b_label=file_b)
        if getattr(args, "exit_code", False):
            sys.exit(1 if pairs else 0)
        # Git's --no-index form implies --exit-code.
        sys.exit(0 if same else 1)

    ensure_repo()
    staged  = getattr(args, "staged", False)
    commits = getattr(args, "commits", []) or []

    stat = getattr(args, "stat", False)
    pairs = _diff_pairs(args)
    if getattr(args, "quiet", False):
        sys.exit(1 if pairs else 0)
    printable_pairs = [(p, a or [], b or []) for p, a, b in pairs]
    if getattr(args, "check", False):
        sys.exit(1 if _diff_check(pairs) else 0)
    if getattr(args, "name_only", False):
        for path, _a, _b in pairs:
            print(path)
    elif getattr(args, "name_status", False):
        _print_name_status(pairs)
    elif stat:
        _print_stat(printable_pairs)
    elif getattr(args, "word_diff", False):
        for path, a_lines, b_lines in pairs:
            _print_word_diff(path, a_lines, b_lines)
    else:
        for path, a_lines, b_lines in pairs:
            print_diff(path, a_lines, b_lines, "a", "b")
    if getattr(args, "exit_code", False):
        sys.exit(1 if pairs else 0)


# ── show ──────────────────────────────────────────────────────────────────────

def _show_blob(oid: str):
    """Write a blob's raw content to stdout (decoded when captured for the pager)."""
    stream = getattr(sys.stdout, "buffer", None)
    if stream is None:
        sys.stdout.write(read_object(oid)[1].decode("utf-8", errors="replace"))
        return
    sys.stdout.flush()
    _stream_blob_object(oid, stream)
    stream.flush()


def cmd_show(args):
    ensure_repo()
    rev = getattr(args, "commit", None) or "HEAD"
    stat = getattr(args, "stat", False)
    oneline = getattr(args, "oneline", False)
    pretty = getattr(args, "pretty", None)
    # Only <rev>:<path> may name a blob or tree; a bare hash must be a commit.
    oid = resolve_rev(rev) if ":" in rev else resolve_commit(rev)
    if not oid:
        _die(f"bad revision '{rev}'")
    obj_type = read_object_type(oid)
    if obj_type == "blob":
        _show_blob(oid)
        return
    if obj_type == "tree":
        print(yellow(f"tree {rev}") + "\n")
        for e in read_tree_entries(oid):
            print(e["name"] + ("/" if e["type"] == "tree" else ""))
        return

    commit  = read_commit(oid)
    ts      = time.strftime("%a %b %d %H:%M:%S %Y",
                            time.localtime(commit["timestamp"]))
    parents = commit.get("parents", [])

    if pretty:
        print(_format_log_pretty(pretty, oid, commit))
    elif oneline:
        subject = _pretty_subject(commit.get("message", ""))
        print(f"{yellow(oid[:7])} {subject}")
    else:
        print(yellow(f"commit {oid}"))
        if len(parents) > 1:
            print(f"Merge: {' '.join(p[:7] for p in parents)}")
        print(f"Author: {commit.get('author', 'Unknown')}")
        print(f"Date:   {ts}")
        print("\n" + _indent_message(commit["message"]) + "\n")

    _print_history_diff_options(args, oid, commit, default_patch=True)


# ── rev-parse ────────────────────────────────────────────────────────────────

def _rev_parse_one(rev: str) -> str | None:
    base, peel = _peel_rev_suffix(rev)
    oid = resolve_rev(base)
    if not oid:
        return None
    if peel == "commit":
        obj_type, _ = read_object(oid)
        if obj_type != "commit":
            return None
    return oid

def _abbrev_ref_name(rev: str) -> str | None:
    base, peel = _peel_rev_suffix(rev)
    if peel:
        return None
    if base == "HEAD":
        return current_branch() or "HEAD"
    if get_branch_commit(base) is not None or get_tag_commit(base) is not None:
        return base
    return None


def _symbolic_full_name(rev: str) -> str | None:
    base, peel = _peel_rev_suffix(rev)
    if peel:
        return None
    if base == "HEAD":
        branch = current_branch()
        return f"refs/heads/{branch}" if branch else None
    if get_branch_commit(base) is not None:
        return f"refs/heads/{base}"
    if get_tag_commit(base) is not None:
        return f"refs/tags/{base}"
    return None

def cmd_rev_parse(args):
    ensure_repo()

    printed = False
    if getattr(args, "show_toplevel", False):
        print(os.path.abspath("."))
        printed = True
    if getattr(args, "git_dir", False):
        print(os.path.abspath(VCS_DIR))
        printed = True
    if getattr(args, "absolute_git_dir", False):
        print(os.path.abspath(VCS_DIR))
        printed = True
    if getattr(args, "is_inside_git_dir", False):
        git_dir = os.path.abspath(VCS_DIR)
        invocation = os.path.abspath(_INVOCATION_CWD)
        print("true" if os.path.commonpath([git_dir, invocation]) == git_dir else "false")
        printed = True
    if getattr(args, "is_inside_work_tree", False):
        root = os.path.abspath(".")
        invocation = os.path.abspath(_INVOCATION_CWD)
        git_dir = os.path.abspath(VCS_DIR)
        inside_root = os.path.commonpath([root, invocation]) == root
        inside_git_dir = os.path.commonpath([git_dir, invocation]) == git_dir
        print("true" if inside_root and not inside_git_dir else "false")
        printed = True
    if getattr(args, "is_bare_repository", False):
        print("false")
        printed = True
    if getattr(args, "show_object_format", None):
        print("sha1")
        printed = True
    if getattr(args, "show_prefix", False):
        rel = os.path.relpath(_INVOCATION_CWD, os.path.abspath("."))
        print("" if rel == "." else rel.replace("\\", "/") + "/")
        printed = True
    if getattr(args, "show_cdup", False):
        rel = os.path.relpath(os.path.abspath("."), _INVOCATION_CWD)
        print("" if rel == "." else rel.replace("\\", "/") + "/")
        printed = True

    branch_pattern = getattr(args, "branches", None)
    if branch_pattern:
        pattern = branch_pattern if branch_pattern != "*" else "*"
        for name in list_branches():
            if fnmatch.fnmatch(name, pattern):
                oid = get_branch_commit(name)
                if oid:
                    print(oid)
        printed = True
    tag_pattern = getattr(args, "tags", None)
    if tag_pattern:
        pattern = tag_pattern if tag_pattern != "*" else "*"
        for name in list_tags():
            if fnmatch.fnmatch(name, pattern):
                oid = get_tag_commit(name)
                if oid:
                    print(oid)
        printed = True

    revs = [r for r in getattr(args, "revs", []) if r != "--"]
    if not revs:
        if not printed:
            _die("no revisions or options given")
        return

    short_len = getattr(args, "short", None)
    if short_len is not None:
        try:
            short_len = int(short_len)
        except ValueError:
            _die(f"option --short expects a number, got '{short_len}'")
        if short_len < 4:
            _die("option --short expects a value of at least 4")

    verify = getattr(args, "verify", False)
    abbrev_ref = getattr(args, "abbrev_ref", False)
    symbolic_full = getattr(args, "symbolic_full_name", False)
    quiet = getattr(args, "quiet", False)

    if verify and len(revs) != 1:
        if not quiet:
            _die("Needed a single revision")
        sys.exit(1)

    had_error = False
    for rev in revs:
        if symbolic_full:
            name = _symbolic_full_name(rev)
            if name is not None:
                print(name)
            continue
        if abbrev_ref:
            name = _abbrev_ref_name(rev)
            if name is not None:
                print(name)
                continue

        oid = _rev_parse_one(rev)
        if not oid:
            had_error = True
            if not quiet:
                _err(f"bad revision '{rev}'")
            continue
        print(oid[:short_len] if short_len is not None else oid)

    if had_error:
        sys.exit(1)


# ── branch ────────────────────────────────────────────────────────────────────

def _format_ref_output(fmt: str, kind: str, name: str, oid: str, current=False) -> str:
    commit = read_commit(oid)
    replacements = {
        "%(refname)": f"refs/{kind}/{name}",
        "%(refname:short)": name,
        "%(objectname)": oid,
        "%(objectname:short)": oid[:7],
        "%(HEAD)": "*" if current else " ",
        "%(subject)": _pretty_subject(commit.get("message", "")),
    }
    out = fmt
    for token, value in replacements.items():
        out = out.replace(token, value)
    return out


def _sort_refs(items: list[tuple[str, str]], sort_key: str | None):
    reverse = bool(sort_key and sort_key.startswith("-"))
    key = sort_key[1:] if reverse else sort_key
    if key in ("committerdate", "authordate"):
        value = lambda item: (read_commit(item[1]).get("timestamp", 0), item[0])
    else:
        value = lambda item: item[0].lower()
    return sorted(items, key=value, reverse=reverse)


def cmd_branch(args):
    ensure_repo()

    rename = getattr(args, "move", None) or getattr(args, "force_move", None)
    if rename:
        if len(rename) == 1:
            old = current_branch()
            new = rename[0]
        elif len(rename) == 2:
            old, new = rename
        else:
            _die("branch rename expects one or two branch names")
        if not old:
            _die("cannot rename detached HEAD")
        _validate_ref_name(old, "branch")
        _validate_ref_name(new, "branch")
        old_path = os.path.join(HEADS_DIR, old)
        new_path = os.path.join(HEADS_DIR, new)
        if not os.path.isfile(old_path):
            _die(f"branch '{old}' not found.")
        if old != new and os.path.exists(new_path):
            if not getattr(args, "force_move", None):
                _die(f"A branch named '{new}' already exists.")
            if new == current_branch():
                _die(f"cannot force update the current branch '{new}'")
        if old != new and not os.path.isfile(new_path):
            _ensure_ref_creatable(HEADS_DIR, new, "branch")
        rename_current = current_branch() == old
        protected = [old_path, new_path]
        if rename_current:
            protected.append(HEAD_FILE)
        with _repository_transaction(metadata_paths=protected):
            os.makedirs(os.path.dirname(new_path), exist_ok=True)
            os.replace(old_path, new_path)
            _fsync_directory(os.path.dirname(old_path))
            if os.path.dirname(new_path) != os.path.dirname(old_path):
                _fsync_directory(os.path.dirname(new_path))
            if rename_current:
                set_head_ref(new)
        return

    # delete
    to_delete = getattr(args, "delete", None) or getattr(args, "force_delete", None)
    if to_delete:
        had_error = False
        force_delete = bool(getattr(args, "force_delete", None))
        head_ancestors = _ancestors(get_head_commit()) if get_head_commit() else set()
        for name in to_delete:
            _validate_ref_name(name, "branch")
            p = os.path.join(HEADS_DIR, name)
            if not os.path.isfile(p):
                _err(f"branch '{name}' not found.")
                had_error = True
                continue
            if name == current_branch():
                _err(f"Cannot delete the branch '{name}' which you are on.")
                had_error = True
                continue
            branch_oid = get_branch_commit(name)
            if not force_delete and branch_oid not in head_ancestors:
                _err(f"The branch '{name}' is not fully merged. Use -D to delete it.")
                had_error = True
                continue
            with open(p) as f:
                bc = f.read().strip()[:7]
            os.remove(p)
            parent = os.path.dirname(p)
            while parent != HEADS_DIR:
                try:
                    os.rmdir(parent)
                except OSError:
                    break
                parent = os.path.dirname(parent)
            print(f"Deleted branch {name} (was {bc}).")
        if had_error:
            sys.exit(1)
        return

    if getattr(args, "show_current", False):
        branch = current_branch()
        if branch:
            print(branch)
        return

    # create
    name = getattr(args, "name", None)
    list_mode = bool(
        getattr(args, "list", False)
        or getattr(args, "contains", None)
        or getattr(args, "points_at", None)
        or getattr(args, "merged", False)
        or getattr(args, "no_merged", False)
        or getattr(args, "format", None)
        or getattr(args, "sort", None)
        or name is None
    )
    if name and not list_mode:
        _validate_ref_name(name, "branch")
        start_arg = getattr(args, "start_point", None) or "HEAD"
        start = resolve_commit(start_arg)
        if not start:
            _die(f"Not a valid object name: '{start_arg}'")
        p = os.path.join(HEADS_DIR, name)
        if os.path.exists(p) and not getattr(args, "force", False):
            _err(f"A branch named '{name}' already exists.")
            sys.exit(1)
        if os.path.isfile(p) and name == current_branch():
            # Moving the checked-out branch would leave index and work tree
            # describing the old commit.
            _die(f"cannot force update the current branch '{name}'")
        if not os.path.isfile(p):
            _ensure_ref_creatable(HEADS_DIR, name, "branch")
        set_branch_commit(name, start)
        print(f"Branch '{name}' created at {start[:7]}.")
        return

    # list
    cur = current_branch()
    merged_filter = getattr(args, "merged", False)
    no_merged_filter = getattr(args, "no_merged", False)
    head = get_head_commit()
    head_ancestors = _ancestors(head) if head and (merged_filter or no_merged_filter) else set()
    contains_oid = resolve_commit(args.contains) if getattr(args, "contains", None) else None
    if getattr(args, "contains", None) and not contains_oid:
        _die(f"malformed object name {args.contains}")
    points_oid = resolve_commit(args.points_at) if getattr(args, "points_at", None) else None
    if getattr(args, "points_at", None) and not points_oid:
        _die(f"malformed object name {args.points_at}")
    items = [(b, get_branch_commit(b) or "") for b in list_branches()]
    if getattr(args, "list", False) and name:
        items = [item for item in items if fnmatch.fnmatch(item[0], name)]
    items = _sort_refs(items, getattr(args, "sort", None))
    for b, bc in items:
        if merged_filter and bc not in head_ancestors:
            continue
        if no_merged_filter and bc in head_ancestors:
            continue
        if contains_oid and contains_oid not in _ancestors(bc):
            continue
        if points_oid and bc != points_oid:
            continue
        fmt = getattr(args, "format", None)
        if fmt:
            print(_format_ref_output(fmt, "heads", b, bc, b == cur))
            continue
        if b == cur:
            print(green(f"* {b}"))
        else:
            print(f"  {b}")



def _commit_tree_map(oid: str | None) -> dict:
    return read_tree(read_commit(oid)["tree"]) if oid else {}

def _guard_dirty_checkout(from_tree: dict, to_tree: dict):
    """Refuse checkout if uncommitted local changes would be overwritten."""
    _guard_tree_transition(
        from_tree, to_tree, "checkout",
        "Please commit your changes or stash them before you switch branches."
    )

def _checkout_commit(oid: str, force: bool, finalize):
    """Move HEAD's commit to *oid*: carry local changes over unless forced."""
    current_head = get_head_commit()
    if force:
        apply_commit(oid, metadata_paths=[HEAD_FILE], finalize=finalize)
        return
    from_tree, to_tree = _commit_tree_map(current_head), _commit_tree_map(oid)
    _guard_dirty_checkout(from_tree, to_tree)
    _switch_commit(from_tree, to_tree, metadata_paths=[HEAD_FILE], finalize=finalize)

def _checkout_paths(pathspecs: list, source_rev: str | None):
    """checkout [<rev>] -- <path>...: restore paths from the index, or from
    <rev> into both the index and the work tree."""
    index = read_index()
    if source_rev is not None:
        source_oid = resolve_commit(source_rev)
        if not source_oid:
            _die(f"invalid reference: {source_rev}")
        source = _commit_tree_map(source_oid)
    else:
        source = index
    new_index = dict(index)
    changes = {}
    for spec in pathspecs:
        norm = normalize_pathspec(spec)
        matched = [rel for rel in sorted(source)
                   if norm == "." or rel == norm or rel.startswith(norm + "/")]
        if not matched:
            _die(f"pathspec '{spec}' did not match any file(s) known to notgit")
        for rel in matched:
            blob_oid = source[rel]
            if read_object_type(blob_oid) != "blob":
                _die(f"expected blob object, got {read_object_type(blob_oid)}")
            new_index[rel] = blob_oid
            # Rewriting unchanged files only costs I/O and bumps mtimes.
            try:
                current = (hash_blob_file(rel)
                           if os.path.isfile(rel) and not os.path.islink(rel) else None)
            except OSError:
                current = None
            if current != blob_oid:
                changes[rel] = ("blob", blob_oid)
    protected = [INDEX_FILE] if source_rev is not None else []
    with _repository_transaction(changes, protected):
        if source_rev is not None:
            write_index(new_index)

def cmd_checkout(args):
    ensure_repo()
    target     = args.target
    pathspecs  = getattr(args, "pathspecs", None) or []
    create_new = getattr(args, "b", False)
    force_new  = getattr(args, "B", False)
    force      = getattr(args, "force", False)
    detach     = getattr(args, "detach", False)
    orphan     = getattr(args, "orphan", False)

    if pathspecs:
        if create_new or force_new or detach or orphan:
            _die("paths cannot be used with switching branches")
        _checkout_paths(pathspecs, target)
        return
    if not target:
        _die("you must specify a branch, commit, or path to checkout")

    if orphan:
        _validate_ref_name(target, "branch")
        if os.path.exists(os.path.join(HEADS_DIR, target)):
            _die(f"A branch named '{target}' already exists.")
        _ensure_ref_creatable(HEADS_DIR, target, "branch")
        if not force:
            _ensure_clean_worktree("create orphan branch")
        set_head_ref(target)
        print(f"Switched to a new branch '{target}'")
        return

    if create_new or force_new:
        head = get_head_commit()
        if not head:
            _die("Not a valid object name: 'HEAD'")
        _validate_ref_name(target, "branch")
        p = os.path.join(HEADS_DIR, target)
        if os.path.exists(p) and not force_new:
            _die(f"A branch named '{target}' already exists.")
        if not os.path.isfile(p):
            _ensure_ref_creatable(HEADS_DIR, target, "branch")
        branch_path = os.path.join(HEADS_DIR, target)
        with _repository_transaction(metadata_paths=[branch_path, HEAD_FILE]):
            set_branch_commit(target, head)
            set_head_ref(target)
        print(f"Switched to a new branch '{target}'")
        return

    # switch to existing branch  (must be a file, not a directory like ".")
    p = os.path.join(HEADS_DIR, target)
    if _safe_ref_name(target) and os.path.isfile(p) and not detach:
        if target == current_branch() and not force:
            print(f"Already on '{target}'")
            return
        bc = get_branch_commit(target)
        current_head = get_head_commit()
        if bc and (bc != current_head or force):
            _checkout_commit(bc, force, lambda: set_head_ref(target))
        else:
            set_head_ref(target)
        print(f"Switched to branch '{target}'")
        return

    # detach at commit
    oid = resolve_rev(target)
    if oid and read_object_type(oid) != "commit" and ":" not in target:
        # A file whose name happens to prefix a blob or tree id is a path.
        norm = normalize_pathspec(target)
        if any(rel == norm or rel.startswith(norm + "/") for rel in read_index()):
            oid = None
    if oid:
        obj_type, _ = read_object(oid)
        if obj_type != "commit":
            _die(f"'{target}' is not a commit")
        _die_if_rev_path_ambiguous(target, "checkout")
        current_head = get_head_commit()
        if oid != current_head or force:
            _checkout_commit(oid, force, lambda: _atomic_write_text(HEAD_FILE, oid))
        else:
            _atomic_write_text(HEAD_FILE, oid)
        msg = read_commit(oid)["message"]
        print(f"Note: switching to '{target}'.")
        print(f"HEAD is now at {oid[:7]} {msg}")
        return

    # Path restore: checkout . / checkout src/foo.py
    # Restores working-tree files from the index (same as "restore <path>").
    # Paths no longer in the index are untracked and must be left alone —
    # deleting them here would destroy data after "notgit rm --cached".
    norm = normalize_pathspec(target)
    if not any(norm == "." or rel == norm or rel.startswith(norm + "/")
               for rel in read_index()):
        _die(f"pathspec '{target}' did not match any known branch, commit, or tracked file")
    _checkout_paths([target], None)


# ── reset ─────────────────────────────────────────────────────────────────────

def cmd_reset(args):
    ensure_repo()
    mode     = getattr(args, "mode", None) or "mixed"
    positional = list(getattr(args, "positional", []) or [])
    patch_mode = getattr(args, "patch", False)

    # split positional into optional-commit + files
    # Strategy: if first token resolves to a commit, it's the commit; rest are files.
    commit_arg = "HEAD"
    file_args  = []
    pathspecs  = getattr(args, "pathspecs", None) or []

    if pathspecs:
        # reset [<commit>] -- <file>...: nothing after "--" is a revision.
        if len(positional) > 1:
            _die(f"ambiguous argument '{positional[1]}': unknown revision")
        commit_arg = positional[0] if positional else "HEAD"
        file_args = pathspecs
    elif positional:
        first = positional[0]
        if (first == "HEAD"
                or get_branch_commit(first)
                or resolve_commit(first)):
            # "reset cafe" must not move HEAD when "cafe" is also a file.
            _die_if_rev_path_ambiguous(first, "reset")
            commit_arg = first
            file_args  = [f for f in positional[1:] if f != "--"]
        else:
            # treat everything as files
            file_args = positional

    target_oid = resolve_commit(commit_arg)
    if not target_oid:
        _die(f"ambiguous argument '{commit_arg}': unknown revision")

    if file_args:
        # unstage specific files
        index     = read_index()
        committed = read_tree(read_commit(target_oid)["tree"])
        had_error = False
        for fpath in file_args:
            rel = normalize_pathspec(fpath)
            if rel in committed:
                index[rel] = committed[rel]
                print(f"Unstaged changes after reset:\nM\t{rel}")
            elif rel in index:
                del index[rel]
            else:
                _err(f"pathspec '{fpath}' did not match any files")
                had_error = True
        write_index(index)
        if had_error:
            sys.exit(1)
        return

    if patch_mode:
        index = read_index()
        committed = read_tree(read_commit(target_oid)["tree"])
        for path in sorted(set(index) | set(committed)):
            if index.get(path) == committed.get(path):
                continue
            print_diff(path, map_blob_lines(committed, path), map_blob_lines(index, path))
            ans = input(f"unstage this change to '{path}' [y,n]? ").strip().lower()
            if ans.startswith("y"):
                if path in committed:
                    index[path] = committed[path]
                else:
                    index.pop(path, None)
        write_index(index)
        return

    # full HEAD reset — also aborts any in-progress merge, like git
    commit_data = read_commit(target_oid)
    def finish_reset():
        update_head(target_oid)
        _clear_merge_state()
    if mode == "soft":
        with _repository_transaction(
                metadata_paths=[_head_update_path(), *_merge_state_paths()]):
            finish_reset()
    elif mode == "mixed":
        with _repository_transaction(
                metadata_paths=[INDEX_FILE, _head_update_path(), *_merge_state_paths()]):
            write_index(read_tree(commit_data["tree"]))
            finish_reset()
        print(f"HEAD is now at {target_oid[:7]} {commit_data['message']}")
    elif mode == "hard":
        apply_commit(
            target_oid,
            metadata_paths=[_head_update_path(), *_merge_state_paths()],
            finalize=finish_reset,
        )
        print(f"HEAD is now at {target_oid[:7]} {commit_data['message']}")
    elif mode == "merge":
        target_tree = read_tree(commit_data["tree"])
        index = read_index()
        wt = working_tree_oids(index=index)
        changed = {
            path for path in set(index) | set(target_tree)
            if index.get(path) != target_tree.get(path)
        }
        conflicts = [path for path in changed if wt.get(path) != index.get(path)]
        if conflicts:
            for path in conflicts:
                _err(f"Entry '{path}' not uptodate. Cannot merge.")
            sys.exit(1)
        changes = {
            path: (("blob", target_tree[path]) if path in target_tree else None)
            for path in changed
        }
        with _repository_transaction(
                changes,
                [INDEX_FILE, _head_update_path(), *_merge_state_paths()]):
            write_index(target_tree)
            finish_reset()
        print(f"HEAD is now at {target_oid[:7]} {commit_data['message']}")
    elif mode == "keep":
        old_head = get_head_commit()
        old_tree = read_tree(read_commit(old_head)["tree"]) if old_head else {}
        new_tree = read_tree(commit_data["tree"])
        _guard_tree_transition(
            old_tree, new_tree, "reset",
            "Cannot do a keep reset while local changes would be overwritten."
        )
        changed = {
            path for path in set(old_tree) | set(new_tree)
            if old_tree.get(path) != new_tree.get(path)
        }
        changes = {
            path: (("blob", new_tree[path]) if path in new_tree else None)
            for path in changed
        }
        with _repository_transaction(
                changes,
                [INDEX_FILE, _head_update_path(), *_merge_state_paths()]):
            write_index(new_tree)
            finish_reset()
        print(f"HEAD is now at {target_oid[:7]} {commit_data['message']}")


# ── restore ───────────────────────────────────────────────────────────────────

def cmd_restore(args):
    ensure_repo()
    staged = getattr(args, "staged", False)
    worktree = getattr(args, "worktree", False)
    source = getattr(args, "source", None)
    original_index = read_index()
    if source:
        src_oid = resolve_commit(source)
        if not src_oid:
            _die(f"bad revision '{source}'")
        source_tree = read_tree(read_commit(src_oid)["tree"])
    else:
        source_tree = None

    if getattr(args, "patch", False):
        if source_tree is not None:
            desired = source_tree
        elif staged:
            head = get_head_commit()
            desired = read_tree(read_commit(head)["tree"]) if head else {}
        else:
            desired = original_index
        candidates = set()
        current_paths = set(original_index) | set(desired)
        for target in args.files:
            rel = normalize_pathspec(target)
            candidates.update(
                p for p in current_paths
                if rel == "." or p == rel or p.startswith(rel + "/")
            )
        selected = []
        for path in sorted(candidates):
            old_lines = (map_blob_lines(original_index, path) if staged and not worktree
                         else (_read_file_lines(path) if os.path.lexists(path) else None))
            new_lines = map_blob_lines(desired, path)
            if old_lines == new_lines:
                continue
            print_diff(path, old_lines, new_lines)
            answer = input(f"restore this change to '{path}' [y,n]? ").strip().lower()
            if answer.startswith("y"):
                selected.append(path)
        if not selected:
            return
        args.files = selected

    new_index = dict(original_index)
    had_error = False
    if staged:
        head = get_head_commit()
        committed = source_tree if source_tree is not None else (
            read_tree(read_commit(head)["tree"]) if head else {}
        )
        for target in args.files:
            rel = normalize_pathspec(target)
            scope = {
                p for p in set(new_index) | set(committed)
                if rel == "." or p == rel or p.startswith(rel + "/")
            }
            if not scope:
                _err(f"pathspec '{target}' did not match any file(s)")
                had_error = True
                continue
            for path in scope:
                if path in committed:
                    new_index[path] = committed[path]
                else:
                    new_index.pop(path, None)

    changes = {}
    if (not staged) or worktree:
        desired = source_tree if source_tree is not None else new_index
        for target in args.files:
            rel = normalize_pathspec(target)
            matches = [
                path for path in desired
                if rel == "." or path == rel or path.startswith(rel + "/")
            ]
            removals = []
            if source_tree is not None:
                removals = [
                    path for path in original_index
                    if (rel == "." or path == rel or path.startswith(rel + "/"))
                    and path not in source_tree
                ]
            if not matches and not removals:
                _err(f"pathspec '{target}' did not match any file(s) known to notgit")
                had_error = True
                continue
            for path in removals:
                if os.path.lexists(path):
                    changes[path] = None
            for path in matches:
                if read_object_type(desired[path]) != "blob":
                    _die(f"expected blob object, got {read_object_type(desired[path])}")
                changes[path] = ("blob", desired[path])

    if had_error:
        sys.exit(1)
    protected = [INDEX_FILE] if staged else []
    with _repository_transaction(changes, protected):
        if staged:
            write_index(new_index)


def _read_merge_state() -> tuple[str | None, str | None]:
    """Return (merge_head_oid, merge_msg) for an in-progress merge, if any."""
    if not os.path.isfile(MERGE_HEAD_FILE):
        return None, None
    try:
        with open(MERGE_HEAD_FILE, encoding="utf-8") as f:
            merge_head = f.read().strip() or None
        merge_msg = None
        if os.path.isfile(MERGE_MSG_FILE):
            with open(MERGE_MSG_FILE, encoding="utf-8") as f:
                merge_msg = f.read().strip() or None
    except OSError as e:
        _die(f"could not read merge state: {e}")
    if merge_head:
        if not re.fullmatch(r"[0-9a-f]{40}", merge_head):
            _die(f"invalid merge state in {MERGE_HEAD_FILE}")
        if read_object_type(merge_head) != "commit":
            _die(f"invalid merge state: {merge_head} is not a commit")
    return merge_head, merge_msg

def _clear_merge_state():
    for path in _merge_state_paths():
        try:
            _durable_unlink(path)
        except FileNotFoundError:
            pass
        except OSError as e:
            _die(f"could not clear merge state: {e}")


def _read_revert_state() -> tuple[str | None, str | None]:
    if not os.path.isfile(REVERT_HEAD_FILE):
        return None, None
    try:
        with open(REVERT_HEAD_FILE, encoding="utf-8") as f:
            revert_head = f.read().strip() or None
        message = None
        if os.path.isfile(REVERT_MSG_FILE):
            with open(REVERT_MSG_FILE, encoding="utf-8") as f:
                message = f.read().strip() or None
        return revert_head, message
    except OSError as e:
        _die(f"could not read revert state: {e}")


def _clear_revert_state():
    for path in _revert_state_paths():
        try:
            _durable_unlink(path)
        except FileNotFoundError:
            pass
        except OSError as e:
            _die(f"could not clear revert state: {e}")


def _pending_conflicts(path: str) -> list:
    conflicts = read_json(path, [])
    return _require_json_type(path, conflicts, list, "conflict path list")


def _mark_conflicts_resolved(paths):
    resolved = set(paths)
    if not resolved:
        return
    for state_file in (MERGE_CONFLICTS_FILE, REVERT_CONFLICTS_FILE):
        if not os.path.exists(state_file):
            continue
        remaining = [p for p in _pending_conflicts(state_file) if p not in resolved]
        write_json(state_file, remaining)


def _commit_index_with_parents(message: str, parents: list[str]):
    index = read_index()
    tree_oid = build_tree(index)
    commit_oid = create_commit(tree_oid, message, parents)
    # Like "commit", record the index without touching the work tree, so
    # edits made after the conflict that are not staged survive.
    with _repository_transaction(
            metadata_paths=[_head_update_path(), *_revert_state_paths()]):
        update_head(commit_oid)
        if os.path.isfile(REVERT_HEAD_FILE):
            _clear_revert_state()
    branch = current_branch()
    label = branch if branch else "detached HEAD"
    print(f"[{label} {commit_oid[:7]}] {message}")
    return commit_oid


def _index_has_conflict_markers(conflicts_file: str) -> bool:
    index = read_index()
    paths = read_json(conflicts_file, None)
    if paths is None:
        paths = list(index)
    _require_json_type(conflicts_file, paths, list, "conflict path list")
    for path in paths:
        oid = index.get(path)
        if not oid:
            continue
        obj_type, data = read_object(oid)
        if obj_type == "blob" and all(
            marker in data for marker in (b"<<<<<<< ", b"=======", b">>>>>>> ")
        ):
            return True
    return False


# ── revert ────────────────────────────────────────────────────────────────────

def cmd_revert(args):
    """Create a new commit that undoes the changes introduced by a given commit."""
    ensure_repo()
    head = get_head_commit()
    if not head:
        _die("nothing to revert – no commits yet")

    if getattr(args, "abort", False) or getattr(args, "skip", False):
        revert_head, _message = _read_revert_state()
        if not revert_head:
            _die("no revert in progress")
        apply_commit(
            head, metadata_paths=_revert_state_paths(),
            finalize=_clear_revert_state,
        )
        return
    if getattr(args, "quit", False):
        revert_head, _message = _read_revert_state()
        if not revert_head:
            _die("no revert in progress")
        with _repository_transaction(metadata_paths=_revert_state_paths()):
            _clear_revert_state()
        return
    if getattr(args, "continue_", False):
        revert_head, message = _read_revert_state()
        if not revert_head:
            _die("no revert in progress")
        if _pending_conflicts(REVERT_CONFLICTS_FILE):
            _die("cannot continue: unresolved conflicts remain")
        _commit_index_with_parents(message or f"Revert {revert_head[:7]}", [head])
        return

    rev = getattr(args, "commit", None) or "HEAD"
    target_oid = resolve_commit(rev)
    if not target_oid:
        _die(f"bad revision '{rev}'")

    target_commit = read_commit(target_oid)
    target_parents = target_commit.get("parents", [])
    mainline = getattr(args, "mainline", None)
    if len(target_parents) > 1 and mainline is None:
        _die(f"commit {target_oid[:7]} is a merge but no -m option was given")
    if mainline is not None:
        if len(target_parents) < 2:
            _die("mainline was specified but the commit is not a merge")
        if mainline < 1 or mainline > len(target_parents):
            _die(f"commit {target_oid[:7]} does not have parent {mainline}")
        parent_oid = target_parents[mainline - 1]
    else:
        parent_oid = target_parents[0] if target_parents else None
    _ensure_clean_worktree("revert")

    # Revert = three-way merge where:
    #   base   = the commit being reverted (target)
    #   ours   = current HEAD
    #   theirs = target's parent  (the "before" state)
    cur_branch = current_branch() or "HEAD"
    tree_oid, conflicts = _three_way_merge(
        target_oid, head, parent_oid,
        cur_branch, f"parent of {target_oid[:7]}"
    )

    msg = getattr(args, "message", None) or f"Revert \"{target_commit['message']}\""

    if conflicts:
        def record_revert():
            _atomic_write_text(REVERT_HEAD_FILE, target_oid)
            _atomic_write_text(REVERT_MSG_FILE, msg)
            write_json(REVERT_CONFLICTS_FILE, conflicts)
        _apply_tree_and_index(
            tree_oid, metadata_paths=_revert_state_paths(),
            finalize=record_revert,
        )
        for c in conflicts:
            print(f"CONFLICT (content): Merge conflict in {c}")
        print("Automatic revert failed; fix conflicts and then commit the result.")
        sys.exit(1)

    if getattr(args, "no_commit", False):
        _apply_tree_and_index(tree_oid)
        return
    commit_oid = create_commit(tree_oid, msg, [head])
    apply_commit(
        commit_oid, metadata_paths=[_head_update_path()],
        finalize=lambda: update_head(commit_oid),
    )
    branch = current_branch()
    label  = branch if branch else "detached HEAD"
    print(f"[{label} {commit_oid[:7]}] {msg}")


# ── merge ─────────────────────────────────────────────────────────────────────

def _ancestors(oid: str) -> set:
    seen, q = set(), deque([oid])
    while q:
        cur = q.popleft()
        if cur and cur not in seen:
            seen.add(cur)
            q.extend(read_commit(cur).get("parents", []))
    return seen

def _find_merge_base(a: str, b: str) -> str | None:
    """Return a best common ancestor: one not reachable from any other
    common ancestor (the nearest one found by a BFS can be older)."""
    a_anc = _ancestors(a)
    common = {c for c in _ancestors(b) if c in a_anc}
    redundant = set()
    q = deque(p for c in common for p in read_commit(c).get("parents", []))
    while q:
        cur = q.popleft()
        if cur and cur not in redundant:
            redundant.add(cur)
            q.extend(read_commit(cur).get("parents", []))
    best = common - redundant
    if not best:
        return None
    return max(best, key=lambda c: (read_commit(c)["timestamp"], c))


def _blob_bytes(oid: str | None) -> bytes:
    if not oid:
        return b""
    obj_type, data = read_object(oid)
    if obj_type != "blob":
        _die(f"expected blob object, got {obj_type}")
    return data


def _line_edits(base: list[str], side: list[str]) -> list:
    return [
        (i1, i2, side[j1:j2])
        for tag, i1, i2, j1, j2
        in difflib.SequenceMatcher(a=base, b=side).get_opcodes()
        if tag != "equal"
    ]


def _edits_overlap(a, b) -> bool:
    a1, a2, _ = a
    b1, b2, _ = b
    if a1 == a2 and b1 == b2:
        return a1 == b1
    if a1 == a2:
        return b1 <= a1 < b2
    if b1 == b2:
        return a1 <= b1 < a2
    return max(a1, b1) < min(a2, b2)


def _merge_blob_oids(base_oid, ours_oid, theirs_oid,
                     our_name: str, their_name: str):
    base_bytes = _blob_bytes(base_oid)
    ours_bytes = _blob_bytes(ours_oid)
    theirs_bytes = _blob_bytes(theirs_oid)
    if any(b"\0" in data for data in (base_bytes, ours_bytes, theirs_bytes)):
        return ours_oid or theirs_oid, True
    try:
        base = base_bytes.decode("utf-8").splitlines(True)
        ours = ours_bytes.decode("utf-8").splitlines(True)
        theirs = theirs_bytes.decode("utf-8").splitlines(True)
    except UnicodeDecodeError:
        # Preserve our bytes exactly; conflict state carries the unresolved path.
        return ours_oid or theirs_oid, True

    ours_edits = _line_edits(base, ours)
    theirs_edits = _line_edits(base, theirs)
    # The same change made on both sides is not a conflict; apply it once.
    ours_keys = {(start, end, tuple(lines)) for start, end, lines in ours_edits}
    theirs_edits = [edit for edit in theirs_edits
                    if (edit[0], edit[1], tuple(edit[2])) not in ours_keys]
    if not any(_edits_overlap(a, b) for a in ours_edits for b in theirs_edits):
        merged = list(base)
        for start, end, replacement in sorted(
                ours_edits + theirs_edits, key=lambda edit: edit[0], reverse=True):
            merged[start:end] = replacement
        return store_object("blob", "".join(merged).encode()), False

    merged = (
        [f"<<<<<<< HEAD ({our_name})\n"] + ours
        + ["||||||| merged common ancestors\n"] + base
        + ["=======\n"] + theirs
        + [f">>>>>>> {their_name}\n"]
    )
    return store_object("blob", "".join(merged).encode()), True


def _three_way_merge_maps(base: dict, ours: dict, theirs: dict,
                          our_name: str, their_name: str):
    result, conflicts = {}, []
    for path in sorted(set(base) | set(ours) | set(theirs)):
        b, o, t = base.get(path), ours.get(path), theirs.get(path)
        if o == t:
            if o:
                result[path] = o
        elif b == o:
            if t:
                result[path] = t
        elif b == t:
            if o:
                result[path] = o
        else:
            merged_oid, conflict = _merge_blob_oids(b, o, t, our_name, their_name)
            if merged_oid:
                result[path] = merged_oid
            if conflict:
                conflicts.append(path)
    return result, conflicts

def _three_way_merge(base_oid, ours_oid, theirs_oid,
                     our_name: str, their_name: str):
    base  = read_tree(read_commit(base_oid)["tree"])  if base_oid  else {}
    ours  = read_tree(read_commit(ours_oid)["tree"])
    theirs= read_tree(read_commit(theirs_oid)["tree"]) if theirs_oid else {}
    result, conflicts = _three_way_merge_maps(
        base, ours, theirs, our_name, their_name
    )
    return build_tree(result), conflicts

def cmd_merge(args):
    ensure_repo()
    head = get_head_commit()
    if not head:
        _die("You have no commits yet – nothing to merge into")

    merge_head, merge_msg = _read_merge_state()
    if getattr(args, "abort", False):
        if not merge_head:
            _die("There is no merge to abort (MERGE_HEAD missing).")
        apply_commit(
            head, metadata_paths=_merge_state_paths(),
            finalize=_clear_merge_state,
        )
        return
    if getattr(args, "quit", False):
        if not merge_head:
            _die("There is no merge to quit (MERGE_HEAD missing).")
        with _repository_transaction(metadata_paths=_merge_state_paths()):
            _clear_merge_state()
        return
    if getattr(args, "continue_", False):
        if not merge_head:
            _die("There is no merge in progress (MERGE_HEAD missing).")
        if _pending_conflicts(MERGE_CONFLICTS_FILE):
            _die("cannot continue: unresolved conflicts remain")
        continue_args = argparse.Namespace(
            amend=False, all=False, dry_run=False, message=None,
            message_file=None, no_edit=False, author=None, date=None,
            signoff=False, allow_empty=False, allow_empty_message=False,
        )
        cmd_commit(continue_args)
        return

    branch = args.branch
    if not branch:
        _die("No commit specified and merge.defaultToUpstream is not configured.")
    other  = resolve_commit(branch)
    if not other:
        _die(f"'{branch}' is not a valid branch or commit")
    if head == other:
        print("Already up to date.")
        return
    _ensure_clean_worktree("merge")

    base = _find_merge_base(head, other)
    if base is None and not getattr(args, "allow_unrelated_histories", False):
        _die("refusing to merge unrelated histories")
    if base == other:
        print("Already up to date.")
        return
    if base == head and getattr(args, "squash", False):
        target_tree = read_tree(read_commit(other)["tree"])
        _guard_tree_transition(
            read_tree(read_commit(head)["tree"]), target_tree, "merge",
            "Please commit your changes, stash them, or remove conflicting files before you merge."
        )
        _apply_tree_and_index(read_commit(other)["tree"])
        print("Squash commit -- not updating HEAD")
        return
    if base == head and not getattr(args, "no_ff", False):
        _guard_tree_transition(
            read_tree(read_commit(head)["tree"]),
            read_tree(read_commit(other)["tree"]),
            "merge",
            "Please commit your changes, stash them, or remove conflicting files before you merge."
        )
        apply_commit(
            other, metadata_paths=[_head_update_path()],
            finalize=lambda: update_head(other),
        )
        print(f"Updating {head[:7]}..{other[:7]}")
        print("Fast-forward")
        return
    if getattr(args, "ff_only", False):
        _die("Not possible to fast-forward, aborting.")

    cur_name = current_branch() or "HEAD"
    tree_oid, conflicts = _three_way_merge(base, head, other, cur_name, branch)
    _guard_tree_transition(
        read_tree(read_commit(head)["tree"]),
        read_tree(tree_oid),
        "merge",
        "Please commit your changes, stash them, or remove conflicting files before you merge."
    )

    if conflicts:
        # Write conflict-marked files to disk and index, but do NOT create a
        # commit – the user must resolve conflicts and commit manually.
        # MERGE_HEAD records the second parent so that commit can finish the
        # merge instead of silently producing a single-parent commit.
        def record_merge_conflict():
            if not getattr(args, "squash", False):
                _atomic_write_text(MERGE_HEAD_FILE, other)
                _atomic_write_text(
                    MERGE_MSG_FILE,
                    getattr(args, "message", None) or f"Merge branch '{branch}'"
                )
            # Squash merges record conflicts too, so "commit" refuses to
            # record conflict markers until the paths are re-added.
            write_json(MERGE_CONFLICTS_FILE, conflicts)
        merge_metadata = ((MERGE_CONFLICTS_FILE,) if getattr(args, "squash", False)
                          else _merge_state_paths())
        _apply_tree_and_index(
            tree_oid, metadata_paths=merge_metadata,
            finalize=record_merge_conflict,
        )
        for c in conflicts:
            print(f"CONFLICT (content): Merge conflict in {c}")
        print("Automatic merge failed; fix conflicts and then commit the result.")
        sys.exit(1)
    else:
        if getattr(args, "squash", False):
            _apply_tree_and_index(tree_oid)
            print("Squash commit -- not updating HEAD")
        elif getattr(args, "no_commit", False):
            def record_merge():
                _atomic_write_text(MERGE_HEAD_FILE, other)
                _atomic_write_text(
                    MERGE_MSG_FILE,
                    getattr(args, "message", None) or f"Merge branch '{branch}'"
                )
            _apply_tree_and_index(
                tree_oid, metadata_paths=_merge_state_paths(),
                finalize=record_merge,
            )
            print("Automatic merge went well; stopped before committing as requested")
        else:
            commit_oid = create_commit(
                tree_oid,
                getattr(args, "message", None) or f"Merge branch '{branch}'",
                [head, other]
            )
            apply_commit(
                commit_oid, metadata_paths=[_head_update_path()],
                finalize=lambda: update_head(commit_oid),
            )
            print(f"Merge made by the 'ort' strategy.")


# ── tag ───────────────────────────────────────────────────────────────────────

def cmd_tag(args):
    ensure_repo()
    os.makedirs(TAGS_DIR, exist_ok=True)

    name = getattr(args, "name", None)
    list_mode = bool(
        not name
        or getattr(args, "list", False)
        or getattr(args, "contains", None)
        or getattr(args, "points_at", None)
        or getattr(args, "merged", None)
        or getattr(args, "sort", None)
        or getattr(args, "format", None)
    )
    if list_mode and not getattr(args, "delete", False):
        contains_oid = resolve_commit(args.contains) if getattr(args, "contains", None) else None
        if getattr(args, "contains", None) and not contains_oid:
            _die(f"malformed object name {args.contains}")
        points_oid = resolve_commit(args.points_at) if getattr(args, "points_at", None) else None
        if getattr(args, "points_at", None) and not points_oid:
            _die(f"malformed object name {args.points_at}")
        merged_arg = getattr(args, "merged", None)
        merged_oid = resolve_commit(merged_arg or "HEAD") if merged_arg is not None else None
        merged_ancestors = _ancestors(merged_oid) if merged_oid else set()
        items = [(tag, get_tag_commit(tag) or "") for tag in list_tags()]
        if name:
            items = [item for item in items if fnmatch.fnmatch(item[0], name)]
        for tag, oid in _sort_refs(items, getattr(args, "sort", None)):
            if contains_oid and contains_oid not in _ancestors(oid):
                continue
            if points_oid and oid != points_oid:
                continue
            if merged_oid and oid not in merged_ancestors:
                continue
            fmt = getattr(args, "format", None)
            print(_format_ref_output(fmt, "tags", tag, oid) if fmt else tag)
        return

    if getattr(args, "delete", False):
        _validate_ref_name(name, "tag")
        p = os.path.join(TAGS_DIR, name)
        if not os.path.isfile(p):
            _die(f"tag '{name}' not found.")
        os.remove(p)
        print(f"Deleted tag '{name}'")
        return

    _validate_ref_name(name, "tag")
    p = os.path.join(TAGS_DIR, name)
    if os.path.exists(p) and not getattr(args, "force", False):
        _die(f"tag '{name}' already exists")
    if not os.path.isfile(p):
        _ensure_ref_creatable(TAGS_DIR, name, "tag")

    rev = getattr(args, "commit", None) or "HEAD"
    oid = resolve_commit(rev)
    if not oid:
        _die(f"bad revision '{rev}'")
    if getattr(args, "annotate", False) or getattr(args, "message", None) is not None:
        message = getattr(args, "message", None)
        if not message:
            _die("annotated tag requires -m <message>")
        _tag_name, _tag_email = get_author()
        tag_data = {
            "type": "tag",
            "object": oid,
            "tag": name,
            "tagger": f"{_tag_name} <{_tag_email}>",
            "message": message,
            "timestamp": time.time(),
        }
        oid = store_object("tag", json.dumps(tag_data, sort_keys=True).encode())
    _atomic_write_text(p, oid)
    print(f"Tag '{name}' created at {get_tag_commit(name)[:7]}.")


# ── config ────────────────────────────────────────────────────────────────────

def cmd_config(args):
    ensure_repo()
    cfg = read_config()
    if getattr(args, "list", False):
        for section in sorted(cfg):
            values = cfg[section]
            if not isinstance(values, dict):
                continue
            for subkey in sorted(values):
                print(f"{section}.{subkey}={values[subkey]}")
        return

    key = args.key
    if not key:
        _die("no config key supplied", code=1)
    if "." not in key:
        _err(f"key does not contain a section: {key}")
        sys.exit(1)
    section, subkey = key.split(".", 1)
    if getattr(args, "unset", False):
        if section not in cfg or subkey not in cfg[section]:
            sys.exit(5)
        del cfg[section][subkey]
        if not cfg[section]:
            del cfg[section]
        write_config(cfg)
        return

    if args.value is None or getattr(args, "get", False):
        val = cfg.get(section, {}).get(subkey)
        if val is None:
            default = getattr(args, "default", None)
            if default is not None:
                print(default)
                return
            sys.exit(1)
        print(val)
    else:
        cfg.setdefault(section, {})[subkey] = args.value
        write_config(cfg)


# ── stash ─────────────────────────────────────────────────────────────────────

def _stash_load():
    entries = _require_json_type(STASH_FILE, read_json(STASH_FILE, []), list, "stash")
    for i, entry in enumerate(entries):
        if not isinstance(entry, dict):
            _die(f"invalid stash entry {i} in {STASH_FILE}")
        for key in ("index", "worktree", "untracked"):
            value = entry.get(key, {})
            if not isinstance(value, dict):
                _die(f"invalid stash entry {i} {key} in {STASH_FILE}")
            _validate_blob_map(value, f"stash entry {i} {key}")
        if not isinstance(entry.get("message"), str):
            _die(f"invalid stash entry {i} message in {STASH_FILE}")
        if not isinstance(entry.get("timestamp"), (int, float)):
            _die(f"invalid stash entry {i} timestamp in {STASH_FILE}")
        head = entry.get("head")
        if head is not None and (not isinstance(head, str)
                                 or not re.fullmatch(r"[0-9a-f]{40}", head)):
            _die(f"invalid stash entry {i} head in {STASH_FILE}")
        paths = entry.get("paths")
        if paths is not None and (not isinstance(paths, list)
                                  or not all(isinstance(p, str) for p in paths)):
            _die(f"invalid stash entry {i} paths in {STASH_FILE}")
    return entries

def _stash_save(lst):
    write_json(STASH_FILE, lst)

def _stash_index(ref: str | None, count: int) -> int:
    if ref is None:
        return 0
    m = re.fullmatch(r"stash@\{(\d+)\}", ref)
    if not m:
        _die(f"invalid stash reference '{ref}'")
    idx = int(m.group(1))
    if idx < 0 or idx >= count:
        _die(f"stash entry '{ref}' not found")
    return idx

def cmd_stash(args):
    ensure_repo()
    sub = getattr(args, "stash_cmd", None) or "push"

    if sub in ("push", "save"):
        head  = get_head_commit()
        index = read_index()
        all_files = getattr(args, "all_files", False)
        wt = working_tree_oids(index=index, force=all_files)
        committed = read_tree(read_commit(head)["tree"]) if head else {}
        tracked_paths = set(index) | set(committed)
        include_untracked = getattr(args, "include_untracked", False) or all_files
        wt_oids = {p: oid for p, oid in wt.items() if p in tracked_paths}
        untracked = {p: oid for p, oid in wt.items() if p not in tracked_paths}
        staged_only = getattr(args, "staged", False)
        staged_paths = {
            p for p in set(index) | set(committed)
            if index.get(p) != committed.get(p)
        }
        tracked_changes = {
            p for p in tracked_paths
            if index.get(p) != committed.get(p) or wt_oids.get(p) != index.get(p)
        }
        selected_paths = set(staged_paths if staged_only else tracked_changes)
        if include_untracked and not staged_only:
            selected_paths.update(untracked)

        if getattr(args, "patch", False):
            chosen = set()
            for path in sorted(selected_paths):
                old_lines = map_blob_lines(committed, path)
                new_lines = (_read_file_lines(path) if path in wt
                             else map_blob_lines(index, path))
                print_diff(path, old_lines, new_lines)
                answer = input(f"stash this change to '{path}' [y,n]? ").strip().lower()
                if answer.startswith("y"):
                    chosen.add(path)
            selected_paths = chosen

        if not selected_paths:
            print("No local changes to save")
            return
        if staged_only:
            # Only the index version is saved, and the work tree is reset to
            # HEAD below, so unstaged edits on top would be lost for good.
            layered = sorted(p for p in selected_paths if wt_oids.get(p) != index.get(p))
            if layered:
                _die(f"cannot stash --staged: '{layered[0]}' also has unstaged changes; "
                     "add or stash them first")
            wt_snapshot = {p: oid for p, oid in index.items() if p in selected_paths}
        else:
            wt_snapshot = {
                p: store_blob_file(p)
                for p in wt
                if p in tracked_paths and p in selected_paths
            }
        untracked_snapshot = {
            p: store_blob_file(p)
            for p in wt
            if include_untracked and p not in tracked_paths and p in selected_paths
        }
        msg = (getattr(args, "message", None)
               or f"WIP on {current_branch() or 'HEAD'}")
        entry = {
            "message":   msg,
            "head":      head,
            "index":     index,
            "worktree":  wt_snapshot,
            "untracked": untracked_snapshot,
            "paths":     sorted(selected_paths),
            "timestamp": time.time(),
        }
        lst = _stash_load()
        lst.insert(0, entry)
        keep_index = getattr(args, "keep_index", False) or getattr(args, "patch", False)
        clean_paths = set(selected_paths)
        if keep_index:
            clean_paths -= staged_paths
        cleaned_index = dict(index)
        changes = {}
        for path in sorted(clean_paths & tracked_paths):
            if path in committed:
                if read_object_type(committed[path]) != "blob":
                    _die(f"expected blob object, got {read_object_type(committed[path])}")
                changes[path] = ("blob", committed[path])
                cleaned_index[path] = committed[path]
            else:
                if os.path.lexists(path):
                    changes[path] = None
                cleaned_index.pop(path, None)
        for path in sorted((selected_paths & set(untracked_snapshot))):
            if os.path.lexists(path):
                changes[path] = None
        if keep_index:
            for path in staged_paths:
                if path in index:
                    if read_object_type(index[path]) != "blob":
                        _die(f"expected blob object, got {read_object_type(index[path])}")
                    changes[path] = ("blob", index[path])
                elif os.path.lexists(path):
                    changes[path] = None
        with _repository_transaction(changes, [STASH_FILE, INDEX_FILE]):
            _stash_save(lst)
            write_index(cleaned_index)
        print(f"Saved working directory and index state: {msg}")

    elif sub == "list":
        for i, e in enumerate(_stash_load()):
            ts = time.strftime("%Y-%m-%d", time.localtime(e["timestamp"]))
            print(f"stash@{{{i}}}: {e['message']} ({ts})")

    elif sub in ("pop", "apply"):
        lst = _stash_load()
        if not lst:
            _die("No stash entries found.")
        idx = _stash_index(getattr(args, "stash_ref", None), len(lst))
        _ensure_clean_worktree(f"{sub} stash")
        e = lst[idx]
        tracked_snapshot = set(e["index"])
        if e["head"]:
            tracked_snapshot |= set(read_tree(read_commit(e["head"])["tree"]))
        _cur_head = get_head_commit()
        current_tree = read_tree(read_commit(_cur_head)["tree"]) if _cur_head else {}
        base_tree = (read_tree(read_commit(e["head"])["tree"])
                     if e["head"] else {})
        affected = set(e.get("paths") or (
            tracked_snapshot | set(e["worktree"]) | set(e.get("untracked", {}))
        ))
        for path in e.get("untracked", {}):
            if path in affected and os.path.exists(path):
                _die(f"untracked file '{path}' already exists")

        stash_tree = dict(base_tree)
        tracked_affected = affected & tracked_snapshot
        for path in tracked_affected:
            if path in e["worktree"]:
                stash_tree[path] = e["worktree"][path]
            else:
                stash_tree.pop(path, None)
        merged_tree, conflicts = _three_way_merge_maps(
            base_tree, current_tree, stash_tree,
            current_branch() or "HEAD", f"stash@{{{idx}}}"
        )
        conflicts = [path for path in conflicts if path in tracked_affected]
        if conflicts:
            _die("stash application resulted in conflicts", code=1)

        merged_index = None
        if getattr(args, "index", False):
            stash_index_tree = dict(base_tree)
            for path in tracked_affected:
                if path in e["index"]:
                    stash_index_tree[path] = e["index"][path]
                else:
                    stash_index_tree.pop(path, None)
            merged_index, index_conflicts = _three_way_merge_maps(
                base_tree, current_tree, stash_index_tree,
                current_branch() or "HEAD", f"stash@{{{idx}}} index"
            )
            if any(path in tracked_affected for path in index_conflicts):
                _die("stash index application resulted in conflicts", code=1)

        changes = {
            path: None
            for path in tracked_affected - set(merged_tree)
            if os.path.lexists(path)
        }
        restored = {
            **{p: merged_tree[p] for p in tracked_affected if p in merged_tree},
            **e.get("untracked", {}),
        }
        for path, oid in restored.items():
            if path not in affected:
                continue
            if read_object_type(oid) != "blob":
                _die(f"expected blob object, got {read_object_type(oid)}")
            changes[path] = ("blob", oid)
        protected = []
        current_index = None
        if getattr(args, "index", False):
            protected.append(INDEX_FILE)
            current_index = read_index()
            for path in affected:
                if merged_index is not None and path in merged_index:
                    current_index[path] = merged_index[path]
                else:
                    current_index.pop(path, None)
        if sub == "pop":
            protected.append(STASH_FILE)
        with _repository_transaction(changes, protected):
            if current_index is not None:
                write_index(current_index)
            if sub == "pop":
                lst.pop(idx)
                _stash_save(lst)
        print(f"Applied stash@{{{idx}}}: {e['message']}")

    elif sub == "drop":
        lst = _stash_load()
        if not lst:
            _die("No stash entries found.")
        idx = _stash_index(getattr(args, "stash_ref", None), len(lst))
        e = lst.pop(idx)
        _stash_save(lst)
        print(f"Dropped stash@{{{idx}}}: {e['message']}")

    elif sub == "show":
        lst = _stash_load()
        if not lst:
            _die("No stash entries found.")
        idx = _stash_index(getattr(args, "stash_ref", None), len(lst))
        e = lst[idx]
        paths = set(e.get("paths") or (
            set(e.get("index", {})) | set(e.get("worktree", {}))
        )) - set(e.get("untracked", {}))
        if getattr(args, "include_untracked", False):
            paths |= set(e.get("untracked", {}))
        if getattr(args, "only_untracked", False):
            paths = set(e.get("untracked", {}))
        for path in sorted(paths):
            print(path)

    elif sub == "clear":
        _stash_save([])
        print("Stash cleared.")

    else:
        _die(f"unknown stash subcommand '{sub}'")


# ── ls ────────────────────────────────────────────────────────────────────────

def _ls_path_matches(path: str, spec: str) -> bool:
    if spec == ".":
        return True
    if glob.has_magic(spec):
        return fnmatch.fnmatch(path, spec)
    return path == spec or path.startswith(spec + "/")


def cmd_ls(args):
    ensure_repo()
    index = read_index()

    if not index:
        print("No files tracked.")
        return

    tracked_paths = sorted(index)
    pathspecs = list(getattr(args, "pathspecs", []) or [])
    if pathspecs:
        specs = [normalize_pathspec(p) for p in pathspecs]
        tracked_paths = [
            path for path in tracked_paths
            if any(_ls_path_matches(path, spec) for spec in specs)
        ]
        if not tracked_paths:
            print("No files matched.")
            return

    # Walk commit history (BFS, newest-first) to find the most recent commit
    # that changed each tracked file.
    last_commit: dict[str, tuple[float, str]] = {}  # path -> (ts, short_oid)
    tracked_path_set = set(tracked_paths)
    head = get_head_commit()
    if head:
        seen: set[str] = set()
        queue: deque[str] = deque([head])
        while queue:
            oid = queue.popleft()
            if not oid or oid in seen:
                continue
            seen.add(oid)
            commit = read_commit(oid)
            parents = commit.get("parents", [])
            cur_tree = read_tree(commit["tree"])
            par_tree = read_tree(read_commit(parents[0])["tree"]) if parents else {}
            ts = commit["timestamp"]
            for path in cur_tree:
                if (path in tracked_path_set and path not in last_commit
                        and cur_tree.get(path) != par_tree.get(path)):
                    last_commit[path] = (ts, oid[:7])
            for p in parents:
                queue.append(p)

    times = read_index_times()

    def _fmt(ts: float | None) -> str:
        if ts is None:
            return "-"
        return time.strftime("%Y-%m-%d %H:%M", time.localtime(ts))

    rows = []
    for path in tracked_paths:
        add_ts   = times.get(path)
        add_str  = _fmt(add_ts)

        if path in last_commit:
            c_ts, c_short = last_commit[path]
            commit_str = f"{_fmt(c_ts)} ({c_short})"
        else:
            commit_str = "-"

        rows.append((path, add_str, commit_str))

    max_path   = max(len(r[0]) for r in rows)
    max_add    = max(len(r[1]) for r in rows)
    col_path   = max(max_path, 4)
    col_add    = max(max_add,  8)

    header = f"{'FILE':<{col_path}}  {'LAST ADD':<{col_add}}  LAST COMMIT"
    sep    = "-" * len(header)
    print(header)
    print(sep)
    for path, add_str, commit_str in rows:
        print(f"{path:<{col_path}}  {add_str:<{col_add}}  {commit_str}")


def cmd_versions(args):
    ensure_repo()
    rel = normalize_pathspec(args.file)
    head = get_head_commit()
    if not head:
        _die("no commits yet")

    starts = [oid for oid in (
        [head] +
        [get_branch_commit(b) for b in list_branches()] +
        [get_tag_commit(t) for t in list_tags()]
    ) if oid]
    seen_commits: set[str] = set()
    queue: deque[str] = deque(starts)
    commits = []

    while queue:
        oid = queue.popleft()
        if not oid or oid in seen_commits:
            continue
        seen_commits.add(oid)
        commit = read_commit(oid)
        commits.append((oid, commit))
        for parent in commit.get("parents", []):
            queue.append(parent)

    commits.sort(key=lambda item: (item[1].get("timestamp", 0), item[0]))

    seen_blobs: set[str] = set()
    planned = []
    stem, ext = os.path.splitext(rel)
    for oid, commit in commits:
        tree = read_tree(commit["tree"])
        blob_oid = tree.get(rel)
        if not blob_oid or blob_oid in seen_blobs:
            continue
        seen_blobs.add(blob_oid)
        order_id = len(planned) + 1
        commit_date = time.strftime("%Y%m%d_%H%M", time.localtime(commit["timestamp"]))
        out_path = f"{stem}_{oid[:7]}_{commit_date}_{order_id}{ext}"
        ensure_repo_relative_path(out_path)
        if os.path.lexists(out_path):
            _die(f"refusing to overwrite existing output '{out_path}'")
        if read_object_type(blob_oid) != "blob":
            _die(f"expected blob object, got {read_object_type(blob_oid)}")
        planned.append((out_path, blob_oid))

    if not planned:
        _die(f"pathspec '{args.file}' did not match any committed file")
    with _repository_transaction({
            path: ("blob", oid) for path, oid in planned
    }):
        pass
    for path, _oid in planned:
        print(path)


def cmd_grep(args):
    no_index = getattr(args, "no_index", False)
    if no_index:
        if getattr(args, "cached", False):
            _die("grep: --cached and --no-index are incompatible", code=129)
    else:
        ensure_repo()

    if args.e_pattern is not None:
        # With -e, the first positional is a rev or path, not the pattern.
        if args.pattern is not None:
            args.rev_or_paths = [args.pattern, *args.rev_or_paths]
        args.pattern = args.e_pattern
    if args.pattern is None:
        _die("grep: no pattern given (use positional or -e <pattern>)", code=129)
    if args.name_only and args.files_without_match:
        _die("grep: -l/--name-only and -L/--files-without-match are mutually exclusive", code=129)

    # Split rev_or_paths: if the first element resolves to a commit, treat it
    # as the revision; everything else (or all elements) are pathspecs.
    positional = list(args.rev_or_paths)
    forced_paths = list(getattr(args, "pathspecs_after_dashdash", None) or [])
    args.rev = None
    args.pathspecs = []
    if forced_paths:
        # grep <pattern> [<rev>] -- <path>...: everything before "--" is a rev.
        if len(positional) > 1 or (positional and (args.cached or no_index)):
            _die(f"ambiguous argument '{positional[-1]}': unknown revision")
        if positional:
            args.rev = positional[0]
        args.pathspecs = forced_paths
    elif positional and not args.cached and not no_index:
        candidate = positional[0]
        if resolve_commit(candidate) is not None:
            _die_if_rev_path_ambiguous(candidate, "grep")
            args.rev = candidate
            args.pathspecs = positional[1:]
        else:
            args.pathspecs = positional
    else:
        args.pathspecs = positional

    # Build the regex.
    pattern = args.pattern
    flags = re.IGNORECASE if args.ignore_case else 0
    if args.fixed_strings:
        pattern = re.escape(pattern)
    if args.word_regexp:
        pattern = r"\b" + pattern + r"\b"
    try:
        regex = re.compile(pattern, flags)
    except re.error as exc:
        _die(f"grep: invalid pattern: {exc}")

    # Determine the file set and how to read each file.
    # --cached          → read staged blobs from the index.
    # a rev             → read blobs from that commit's tree.
    # default           → read working-tree files (tracked only).
    if args.cached or args.rev:
        if args.cached:
            tree = read_index()  # {path: blob_oid} — staged content, not HEAD
        else:
            commit_oid = resolve_commit(args.rev)
            if not commit_oid:
                _die(f"ambiguous argument '{args.rev}': unknown revision")
            tree = read_tree(read_commit(commit_oid)["tree"])

        def get_content(path):
            oid = tree.get(path)
            if oid is None:
                return None
            _, content = read_object(oid)
            return content

        all_paths = sorted(tree.keys())
    elif no_index:
        roots = args.pathspecs or ["."]
        all_paths = []
        for root in roots:
            if os.path.isfile(root):
                all_paths.append(root)
                continue
            for dirpath, dirs, names in os.walk(root):
                dirs[:] = [d for d in dirs if d not in (VCS_DIR, ".git")]
                for name in names:
                    all_paths.append(os.path.join(dirpath, name))
        all_paths = sorted(set(os.path.relpath(p, ".").replace("\\", "/") for p in all_paths))

        def get_content(path):
            try:
                with open(path, "rb") as fh:
                    return fh.read()
            except OSError:
                return None

        args.pathspecs = []
    else:
        index = read_index()

        def get_content(path):
            try:
                with open(path, "rb") as fh:
                    return fh.read()
            except OSError:
                return None

        if getattr(args, "untracked", False):
            all_paths = sorted(working_tree_paths(index=index))
        else:
            all_paths = sorted(index.keys())

    # Apply pathspec filters.
    if args.pathspecs:
        specs = [normalize_pathspec(p) for p in args.pathspecs]
        all_paths = [
            p for p in all_paths
            if any(p == s or p.startswith(s + "/") for s in specs)
        ]

    matched_files = []
    unmatched_files = []
    found_any = False
    quiet = getattr(args, "quiet", False)
    invert = getattr(args, "invert_match", False)
    count_mode = getattr(args, "count", False)
    only_matching = getattr(args, "only_matching", False)
    max_count = getattr(args, "max_count", None)
    before = getattr(args, "before_context", 0) or 0
    after = getattr(args, "after_context", 0) or 0
    context = getattr(args, "context", None)
    if context is not None:
        before = after = context

    for path in all_paths:
        raw = get_content(path)
        if raw is None:
            continue
        try:
            text = raw.decode("utf-8")
        except UnicodeDecodeError:
            continue  # skip binary files

        lines = text.splitlines()
        hits = []
        search_lines = [] if max_count == 0 else lines
        for lineno, line in enumerate(search_lines, 1):
            match = regex.search(line)
            if bool(match) != invert:
                hits.append((lineno, line, match))
                if max_count is not None and len(hits) >= max_count:
                    break

        if hits:
            matched_files.append(path)
            found_any = True
            if quiet:
                return
            if count_mode:
                print(f"{path}:{len(hits)}")
            elif not args.files_without_match and not args.name_only:
                hit_map = {lineno: (line, match) for lineno, line, match in hits}
                display_lines = set(hit_map)
                for lineno in hit_map:
                    display_lines.update(range(
                        max(1, lineno - before), min(len(lines), lineno + after) + 1
                    ))
                for lineno in sorted(display_lines):
                    line = lines[lineno - 1]
                    if lineno not in hit_map:
                        print(f"{path}-{lineno}-{line}" if args.line_number else f"{path}-{line}")
                        continue
                    match = hit_map[lineno][1]
                    prefix = f"{path}:{lineno}:" if args.line_number else f"{path}:"
                    if only_matching and match is not None:
                        for found in regex.finditer(line):
                            print(prefix + found.group(0))
                    else:
                        print(prefix + line)
        else:
            unmatched_files.append(path)
            if count_mode:
                print(f"{path}:0")

    if quiet:
        sys.exit(1)
    if args.name_only:
        for path in matched_files:
            print(path)
    elif args.files_without_match:
        for path in unmatched_files:
            print(path)

    if args.files_without_match:
        if not unmatched_files:
            sys.exit(1)
    elif not found_any:
        sys.exit(1)


# ══════════════════════════════════════════════════════════════════════════════
# Argument parser
# ══════════════════════════════════════════════════════════════════════════════

_HELP_GROUPS = [
    ("start a working area", ["init", "clone", "import-git"]),
    ("work on the current change", ["add", "rm", "mv", "restore", "reset"]),
    ("examine the history and state",
     ["status", "log", "show", "diff", "grep", "ls", "versions", "rev-parse"]),
    ("grow, mark and tweak your history",
     ["commit", "branch", "checkout", "merge", "revert", "tag", "stash"]),
    ("settings", ["config"]),
]

_HELP_EPILOG_NOTES = """\
notes:
  <rev> is HEAD, a branch or tag name, or a full or abbreviated object id,
  optionally followed by ancestry suffixes: ~<n> (n-th first-parent
  ancestor), ^<n> (n-th parent of a merge), e.g. HEAD~2, main^, HEAD^2~1.
  <rev>:<path> names the file or directory at <path> in that commit
  (root-relative unless it starts with ./ or ../); :<path> is the staged file.
  Paths are relative to the directory notgit is run from.  Run
  'notgit <command> -h' for the full description of a command's options.

environment:
  NOTGIT_AUTHOR_NAME, NOTGIT_AUTHOR_EMAIL
                    commit author when user.name / user.email are not set
  GIT_PAGER, PAGER  pager for diff output (default: less)
"""


def _command_synopsis(sp: argparse.ArgumentParser, width: int) -> str:
    """One command's usage, wrapped without splitting any [...] group."""
    usage = " ".join(sp.format_usage().split())
    usage = re.sub(r"^usage: notgit ", "", usage).replace(" [-h]", "", 1)
    words, depth, cur = [], 0, ""
    for ch in usage:
        if ch == " " and depth == 0:
            words.append(cur)
            cur = ""
            continue
        depth += (ch in "[(") - (ch in "])")
        cur += ch
    words.append(cur)
    lines, line = [], "  " + words[0]
    for word in words[1:]:
        if len(line) + 1 + len(word) > width:
            lines.append(line)
            line = "      " + word
        else:
            line += " " + word
    lines.append(line)
    return "\n".join(lines)


def _build_help_epilog(commands: dict) -> str:
    width = max(60, min(shutil.get_terminal_size().columns, 100) - 2)
    parts = []
    for title, names in _HELP_GROUPS:
        parts.append(f"{title}:")
        for name in names:
            sp = commands[name]
            parts.append(_command_synopsis(sp, width))
            for stash_sp in getattr(sp, "_notgit_subcommands", {}).values():
                parts.append(_command_synopsis(stash_sp, width))
        parts.append("")
    return "\n".join(parts) + "\n" + _HELP_EPILOG_NOTES


def build_parser():
    p = argparse.ArgumentParser(
        prog="notgit",
        description="A local git clone – supports all everyday local commands.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    sub = p.add_subparsers(dest="command", metavar="<command>",
                           title="commands")
    commands = {}

    def command(name, help, description=None):
        sp = sub.add_parser(name, help=help, description=description or help)
        commands[name] = sp
        return sp

    # init
    ini = command("init", "Initialize a repository",
                  "Create an empty .notgit repository in the current directory.")
    ini.add_argument("-b", "--initial-branch", dest="initial_branch",
                     metavar="<name>",
                     help="Use the specified initial branch name (default: main)")
    ini.add_argument("-q", "--quiet", action="store_true",
                     help="Only print error messages")

    # clone
    cl = command("clone", "Clone a repository into a new directory",
                 "Copy a local .notgit repository into a new directory and "
                 "check out its HEAD (or the branch given with -b).")
    cl.add_argument("-b", "--branch", dest="branch", metavar="<name>",
                    help="Checkout the named branch or tag instead of HEAD")
    cl.add_argument("-n", "--no-checkout", action="store_true",
                    help="Do not populate the working tree")
    cl.add_argument("--single-branch", action="store_true",
                    help="Copy only the selected branch ref")
    cl.add_argument("--no-tags", action="store_true",
                    help="Do not copy tag refs")
    cl.add_argument("-q", "--quiet", action="store_true",
                    help="Only print error messages")
    cl.add_argument("source", metavar="<source>", help="Source repository path")
    cl.add_argument("dest", nargs="?", metavar="<dest>",
                    help="Destination directory (default: source basename)")

    # import-git
    ig = command("import-git",
                 "Convert a .git repository into a new .notgit repository",
                 "Read the history of a git repository (working copy, bare "
                 "repository, or .git directory) and write it as a new .notgit "
                 "repository.")
    ig.add_argument("source", metavar="<git-repo>",
                    help="Path to a git working copy, bare repo, or .git directory")
    ig.add_argument("dest", nargs="?", metavar="<dest>",
                    help="Destination directory (default: source basename)")

    # add
    a = command("add", "Stage files (use '.' for everything)",
                "Add file contents to the index.  With no paths and -A or -u, "
                "operate on the whole working tree.")
    a.add_argument("files", nargs="*", metavar="<path>",
                   help="Files, directories, or wildcard patterns to stage")
    a.add_argument("-v", "--verbose", action="store_true",
                   help="Print each path as it is staged")
    a.add_argument("-u", "--update",  action="store_true",
                   help="Only update already-tracked files")
    a.add_argument("-A", "--all", action="store_true",
                   help="Stage new, modified, and deleted files")
    a.add_argument("-p", "--patch", action="store_true",
                   help="Interactively choose file-level changes to stage")
    a.add_argument("-f", "--force", action="store_true",
                   help="Allow adding otherwise ignored files")
    a.add_argument("-n", "--dry-run", action="store_true",
                   help="Show paths that would be staged without changing the index")

    # rm
    r = command("rm", "Remove files from index and/or disk")
    r.add_argument("files", nargs="+", metavar="<path>",
                   help="Tracked files or directories to remove")
    r.add_argument("--cached", action="store_true",
                   help="Remove only from index, keep on disk")
    r.add_argument("-f", "--force", action="store_true",
                   help="Override staged and unstaged change checks")
    r.add_argument("-n", "--dry-run", action="store_true",
                   help="Show what would be removed without removing anything")
    r.add_argument("--ignore-unmatch", action="store_true",
                   help="Exit successfully even if no files matched")
    r.add_argument("-q", "--quiet", action="store_true",
                   help="Do not list removed files")

    # mv
    mv = command("mv", "Move or rename tracked files",
                 "Move or rename a file or directory; with several sources the "
                 "destination must be an existing directory.")
    mv.usage = "notgit mv [-h] [-f] [-n] [-v] <source>... <dest>"
    mv.add_argument("-f", "--force", action="store_true",
                    help="Overwrite an existing destination")
    mv.add_argument("-n", "--dry-run", action="store_true",
                    help="Show what would be moved without moving anything")
    mv.add_argument("-v", "--verbose", action="store_true",
                    help="Report each file as it is moved")
    mv.add_argument("paths", nargs="+", metavar="<path>",
                    help="Source path(s) followed by destination")

    # commit
    c = command("commit", "Record staged changes",
                "Create a new commit from the index.  Exits 1 when there is "
                "nothing to commit.")
    c.add_argument("-m", "--message", default=None, metavar="<msg>",
                   help="Commit message (required unless --amend, -F, or a merge)")
    c.add_argument("-F", "--file", dest="message_file", metavar="<file>",
                   help="Read the commit message from <file> ('-' reads stdin)")
    c.add_argument("-a", "--all", action="store_true",
                   help="Stage all tracked modified files before committing")
    c.add_argument("--amend", action="store_true",
                   help="Replace the most recent commit")
    c.add_argument("--no-edit", action="store_true",
                   help="Reuse the existing message when amending")
    c.add_argument("--author", metavar="<author>",
                   help="Override commit author ('Name <email>')")
    c.add_argument("--date", metavar="<date>",
                   help="Override commit date")
    c.add_argument("--dry-run", action="store_true",
                   help="Show what would be committed")
    c.add_argument("--allow-empty", action="store_true",
                   help="Allow a commit that changes nothing")
    c.add_argument("--allow-empty-message", action="store_true",
                   help="Allow a commit with an empty message")
    c.add_argument("-s", "--signoff", action="store_true",
                   help="Add a Signed-off-by trailer")
    c.add_argument("-q", "--quiet", action="store_true",
                   help="Suppress the commit summary")

    # log
    lg = command("log", "Show commit history",
                 "Show commits reachable from HEAD (or all refs with --all), "
                 "newest first.  '-<n>' is shorthand for '-n <n>'.")
    lg.add_argument("--oneline", action="store_true",
                    help="Show each commit as an abbreviated hash and subject")
    lg.add_argument("--pretty", "--format", dest="pretty", metavar="<format>",
                    help="Format each commit with placeholders %%H %%h %%s %%an %%%% "
                         "(optional 'format:' prefix)")
    lg.add_argument("--reverse", "-r", action="store_true",
                    help="Show commits in reverse order")
    lg.add_argument("-n", "--max-count", dest="n", type=int, metavar="<n>",
                    help="Limit to <n> most recent commits")
    lg.add_argument("--skip", type=int, default=0, metavar="<n>",
                    help="Skip <n> commits before starting to show output")
    lg.add_argument("--graph", action="store_true",
                    help="Prefix each commit with a graph marker")
    lg.add_argument("--decorate", action="store_true",
                    help="Show branch and tag names next to commits")
    lg.add_argument("--all", action="store_true",
                    help="Show commits reachable from every branch and tag")
    lg.add_argument("--author", metavar="<pattern>",
                    help="Only commits whose author matches <pattern>")
    lg.add_argument("--grep", metavar="<pattern>",
                    help="Only commits whose message matches <pattern>")
    lg.add_argument("--since", metavar="<date>",
                    help="Only commits newer than <date>")
    lg.add_argument("--until", metavar="<date>",
                    help="Only commits older than <date>")
    lg.add_argument("--after", dest="since", metavar="<date>",
                    help="Same as --since")
    lg.add_argument("--before", dest="until", metavar="<date>",
                    help="Same as --until")
    lg.add_argument("--first-parent", action="store_true",
                    help="Follow only the first parent of merge commits")
    merge_filter = lg.add_mutually_exclusive_group()
    merge_filter.add_argument("--merges", action="store_true",
                              help="Only show merge commits")
    merge_filter.add_argument("--no-merges", action="store_true",
                              help="Do not show merge commits")
    lg.add_argument("--stat", action="store_true",
                    help="Show a diffstat for each commit")
    log_names = lg.add_mutually_exclusive_group()
    log_names.add_argument("--name-only", action="store_true",
                           help="Show names of changed files")
    log_names.add_argument("--name-status", action="store_true",
                           help="Show names and status letters of changed files")
    lg.add_argument("--patch", action="store_true",
                    help="Show the patch for each commit")
    lg.add_argument("--no-patch", action="store_true",
                    help="Suppress patch output")
    lg.add_argument("path", nargs="?", metavar="<path>",
                    help="Limit to commits that touched this path")

    # status
    st = command("status", "Show working-tree status")
    st.add_argument("-s", "--short", action="store_true",
                    help="Give the output in short format")
    st.add_argument("--porcelain", nargs="?", const="1", choices=("1", "2"),
                    metavar="<version>",
                    help="Give stable script-friendly output (version 1 or 2)")
    st.add_argument("-b", "--branch", action="store_true",
                    help="Show branch information in short output")
    st.add_argument("-z", "--null", action="store_true",
                    help="Terminate entries with NUL")
    st.add_argument("-u", "--untracked-files", nargs="?", const="all",
                    choices=("no", "normal", "all"), metavar="<mode>",
                    help="Show untracked files: no, normal, or all (default: all)")
    st.add_argument("--ignored", nargs="?", const="traditional",
                    choices=("traditional", "matching", "no"), metavar="<mode>",
                    help="Show ignored files: traditional, matching, or no")
    st.add_argument("--show-stash", action="store_true",
                    help="Show the number of stash entries")

    # diff
    d = command("diff", "Show changes between commits / index / tree",
                "With no <rev>, show working tree vs index; with --staged, "
                "index vs HEAD; with one <rev>, working tree vs <rev>; with two, "
                "<rev> vs <rev>.  Paths may follow, optionally after '--'.  "
                "Output is paged through $GIT_PAGER / $PAGER.")
    d.usage = ("notgit diff [-h] [--staged] [--stat] [--no-index] [--name-only] "
               "[--name-status] [--check] [--word-diff] [--exit-code] [--quiet] "
               "[<rev> [<rev>]] [[--] <path>...]")
    d.add_argument("--staged", "--cached", dest="staged", action="store_true",
                   help="Show staged changes (index vs HEAD)")
    d.add_argument("--stat", action="store_true",
                   help="Show diffstat summary instead of full patch")
    d.add_argument("--no-index", dest="no_index", action="store_true",
                   help="Compare two files outside any repository")
    d.add_argument("--name-only", action="store_true",
                   help="Show only changed file names")
    d.add_argument("--name-status", action="store_true",
                   help="Show changed file names and status letters")
    d.add_argument("--check", action="store_true",
                   help="Warn on whitespace errors")
    d.add_argument("--word-diff", action="store_true",
                   help="Show word-level changes")
    d.add_argument("--exit-code", action="store_true",
                   help="Exit 1 if there are differences, 0 otherwise")
    d.add_argument("--quiet", action="store_true",
                   help="Print nothing; implies --exit-code")
    d.add_argument("commits", nargs=argparse.REMAINDER,
                   metavar="<rev>|<path>",
                   help="Zero, one, or two revisions optionally followed by "
                        "path specs to limit the diff")

    # show
    sh = command("show", "Show a commit and its changes")
    sh.add_argument("--stat", action="store_true",
                    help="Show diffstat summary instead of full patch")
    sh.add_argument("--oneline", action="store_true",
                    help="Show the commit as an abbreviated hash and subject")
    sh.add_argument("--pretty", "--format", dest="pretty", metavar="<format>",
                    help="Format the commit header (see 'log --pretty')")
    sh.add_argument("--name-only", action="store_true",
                    help="Show names of changed files")
    sh.add_argument("--name-status", action="store_true",
                    help="Show names and status letters of changed files")
    sh.add_argument("--patch", action="store_true",
                    help="Show the patch (default)")
    sh.add_argument("--no-patch", action="store_true",
                    help="Suppress patch output")
    sh.add_argument("commit", nargs="?", default="HEAD", metavar="<rev>",
                    help="Commit, or <rev>:<path> file or directory, to show "
                         "(default: HEAD)")

    # rev-parse
    rp = command("rev-parse", "Parse revisions or show repository paths",
                 "Print the object id of each <rev>, or answer questions about "
                 "the repository.  '--short=<n>' shortens ids to <n> characters.")
    rp.add_argument("--show-toplevel", action="store_true",
                    help="Show the absolute path to the worktree root")
    rp.add_argument("--git-dir", action="store_true",
                    help="Show the path to the .notgit directory")
    rp.add_argument("--absolute-git-dir", action="store_true",
                    help="Show the absolute path to the .notgit directory")
    rp.add_argument("--is-inside-git-dir", action="store_true",
                    help="Print true when inside the .notgit directory")
    rp.add_argument("--is-inside-work-tree", action="store_true",
                    help="Print true when inside a worktree")
    rp.add_argument("--is-bare-repository", action="store_true",
                    help="Print whether the repository is bare (always false)")
    rp.add_argument("--show-object-format", nargs="?", const="storage",
                    choices=("storage", "input", "output"), metavar="<which>",
                    help="Show the object hash algorithm (sha1)")
    rp.add_argument("--show-prefix", action="store_true",
                    help="Show the invocation path relative to the worktree root")
    rp.add_argument("--show-cdup", action="store_true",
                    help="Show the path from the invocation directory back to root")
    rp.add_argument("--abbrev-ref", action="store_true",
                    help="Show a symbolic branch or tag name when possible")
    rp.add_argument("--symbolic-full-name", action="store_true",
                    help="Show the full ref name (e.g. refs/heads/main)")
    rp.add_argument("--branches", nargs="?", const="*", metavar="<pattern>",
                    help="Show ids of all branches (optionally matching <pattern>)")
    rp.add_argument("--tags", nargs="?", const="*", metavar="<pattern>",
                    help="Show ids of all tags (optionally matching <pattern>)")
    rp.add_argument("--verify", action="store_true",
                    help="Require exactly one valid revision")
    rp.add_argument("-q", "--quiet", action="store_true",
                    help="Suppress errors for invalid revisions")
    rp.add_argument("--short", action="store_const", const="7",
                    help="Shorten object names to 7 characters "
                         "(--short=<n> for <n>)")
    rp.add_argument("--short-value", dest="short", help=argparse.SUPPRESS)
    rp.add_argument("revs", nargs="*", metavar="<rev>",
                    help="Revisions to resolve")

    # branch
    br = command("branch", "List, create, or delete branches",
                 "With no arguments, list branches.  With <name>, create a "
                 "branch at <start-point>.")
    br.add_argument("name", nargs="?", metavar="<name>",
                    help="New branch name (or pattern with --list)")
    br.add_argument("start_point", nargs="?", metavar="<start-point>",
                    help="Start point (default: HEAD)")
    br.add_argument("-d", "--delete",       nargs="+", metavar="<branch>",
                    help="Delete fully merged branch(es)")
    br.add_argument("-D", "--force-delete", nargs="+", metavar="<branch>",
                    dest="force_delete",
                    help="Delete branch(es) even if unmerged")
    br.add_argument("-f", "--force", action="store_true",
                    help="Reset <name> to <start-point> if it already exists")
    br.add_argument("-m", "--move", nargs="+", metavar="<branch>",
                    help="Rename a branch ([<old>] <new>)")
    br.add_argument("-M", "--force-move", nargs="+", metavar="<branch>",
                    dest="force_move",
                    help="Rename a branch, overwriting the destination")
    br.add_argument("--merged", action="store_true",
                    help="List only branches merged into HEAD")
    br.add_argument("--no-merged", action="store_true",
                    help="List only branches not merged into HEAD")
    br.add_argument("-l", "--list", action="store_true",
                    help="List branches (matching <name> as a pattern)")
    br.add_argument("--show-current", action="store_true",
                    help="Print the current branch name")
    br.add_argument("--contains", metavar="<rev>",
                    help="List only branches that contain <rev>")
    br.add_argument("--points-at", metavar="<rev>",
                    help="List only branches that point at <rev>")
    br.add_argument("--sort", metavar="<key>",
                    help="Sort by refname, committerdate, or authordate "
                         "(prefix '-' to reverse)")
    br.add_argument("--format", metavar="<format>",
                    help="Format each branch with %%(refname), %%(refname:short), "
                         "%%(objectname), %%(objectname:short), %%(HEAD), %%(subject)")
    br.add_argument("-q", "--quiet", action="store_true",
                    help="Suppress messages when creating/deleting/renaming")

    # checkout
    co = command("checkout", "Switch branches or detach HEAD",
                 "Switch to a branch or commit, or restore files from the index "
                 "when <target> is a path.  'checkout [<rev>] -- <path>...' "
                 "always treats the arguments after -- as paths, restoring "
                 "them from the index, or from <rev> into the index and the "
                 "working tree.")
    co.add_argument("-b", action="store_true",
                    help="Create and switch to new branch <target>")
    co.add_argument("-B", action="store_true",
                    help="Create/reset and switch to branch <target>")
    co.add_argument("-d", "--detach", action="store_true",
                    help="Detach HEAD at <target>")
    co.add_argument("-f", "--force", action="store_true",
                    help="Discard local changes when switching")
    co.add_argument("--orphan", action="store_true",
                    help="Start a new branch <target> with no history")
    co.add_argument("-q", "--quiet", action="store_true",
                    help="Suppress feedback messages")
    co.add_argument("target", metavar="<target>", nargs="?",
                    help="Branch, commit, or path (or the source <rev> before --)")
    co.add_argument("--pathspec", dest="pathspecs", action="append",
                    help=argparse.SUPPRESS)

    # reset
    rs = command("reset", "Reset HEAD or unstage files",
                 "Move the current branch to <commit> (default: HEAD), or with "
                 "paths, unstage those paths.")
    rs.add_argument("--soft",  dest="mode", action="store_const", const="soft",
                    help="Move HEAD only; keep index and working tree")
    rs.add_argument("--mixed", dest="mode", action="store_const", const="mixed",
                    help="Move HEAD and reset the index (default)")
    rs.add_argument("--hard",  dest="mode", action="store_const", const="hard",
                    help="Move HEAD and reset index and working tree")
    rs.add_argument("--merge", dest="mode", action="store_const", const="merge",
                    help="Like --hard, but keep unstaged local changes")
    rs.add_argument("--keep",  dest="mode", action="store_const", const="keep",
                    help="Like --hard, but abort if local changes would be lost")
    rs.add_argument("-p", "--patch", action="store_true",
                    help="Interactively choose file-level staged changes to unstage")
    rs.add_argument("-q", "--quiet", action="store_true",
                    help="Only report errors")
    rs.add_argument("positional", nargs="*",
                    metavar="<commit-or-file>",
                    help="Optional commit then optional file list")
    rs.add_argument("--pathspec", dest="pathspecs", action="append",
                    help=argparse.SUPPRESS)

    # restore  (rst: don't shadow the `re` module)
    rst = command("restore", "Restore working-tree or index files",
                  "Restore paths in the working tree (default) and/or index "
                  "from the index or --source.")
    rst.add_argument("--staged", "-S", action="store_true",
                     help="Restore the index (unstage)")
    rst.add_argument("--worktree", "-W", action="store_true",
                     help="Restore the working tree")
    rst.add_argument("--source", "-s", metavar="<rev>",
                     help="Restore from the given revision")
    rst.add_argument("-p", "--patch", action="store_true",
                     help="Interactively choose files to restore")
    rst.add_argument("-q", "--quiet", action="store_true",
                     help="Suppress feedback messages")
    rst.add_argument("files", nargs="+", metavar="<path>",
                     help="Paths to restore")

    # revert
    rv = command("revert", "Revert a commit by creating an inverse commit")
    rv.add_argument("commit", nargs="?", metavar="<commit>",
                    help="Commit to revert (default: HEAD)")
    rv.add_argument("-m", "--mainline", type=int, metavar="<parent>",
                    help="Select the mainline parent when reverting a merge")
    rv.add_argument("--message", default=None, metavar="<msg>",
                    help="Override the auto-generated revert message (notgit extension)")
    rv.add_argument("-n", "--no-commit", action="store_true",
                    help="Apply the inverse changes without committing")
    rv.add_argument("--continue", dest="continue_", action="store_true",
                    help="Continue after resolving conflicts")
    rv.add_argument("--abort", action="store_true",
                    help="Cancel the revert and restore the previous state")
    rv.add_argument("--skip", action="store_true",
                    help="Skip the current commit")
    rv.add_argument("--quit", action="store_true",
                    help="Forget the in-progress revert, keeping changes")

    # merge
    mg = command("merge", "Join development histories",
                 "Merge <branch> into the current branch.  On conflicts, fix "
                 "the files, 'notgit add' them, then 'notgit merge --continue'.")
    mg.add_argument("branch", nargs="?", metavar="<branch>",
                    help="Branch or commit to merge")
    mg.add_argument("--abort", action="store_true",
                    help="Abort the merge and restore the pre-merge state")
    mg.add_argument("--continue", dest="continue_", action="store_true",
                    help="Commit the merge after resolving conflicts")
    mg.add_argument("--quit", action="store_true",
                    help="Forget the in-progress merge, keeping changes")
    mg.add_argument("--no-commit", action="store_true",
                    help="Merge but stop before creating the merge commit")
    mg.add_argument("--squash", action="store_true",
                    help="Stage the merged changes without recording a merge")
    ff = mg.add_mutually_exclusive_group()
    ff.add_argument("--ff-only", action="store_true",
                    help="Refuse to merge unless it can fast-forward")
    ff.add_argument("--no-ff", action="store_true",
                    help="Always create a merge commit")
    mg.add_argument("-m", "--message", metavar="<msg>",
                    help="Merge commit message")
    mg.add_argument("--allow-unrelated-histories", action="store_true",
                    help="Allow merging histories with no common ancestor")
    mg.add_argument("-q", "--quiet", action="store_true",
                    help="Suppress feedback messages")

    # tag
    tg = command("tag", "Create, list, or delete tags",
                 "With no arguments, list tags.  With <name>, create a tag at "
                 "<commit>.")
    tg.add_argument("name", nargs="?", metavar="<name>",
                    help="Tag name (or pattern with --list)")
    tg.add_argument("commit", nargs="?", metavar="<commit>",
                    help="Commit to tag (default: HEAD)")
    tg.add_argument("-d", "--delete", action="store_true",
                    help="Delete tag <name>")
    tg.add_argument("-f", "--force",  action="store_true",
                    help="Replace an existing tag")
    tg.add_argument("-a", "--annotate", action="store_true",
                    help="Create an annotated tag")
    tg.add_argument("-m", "--message", metavar="<msg>",
                    help="Annotated tag message (implies -a)")
    tg.add_argument("-l", "--list", action="store_true",
                    help="List tags (matching <name> as a pattern)")
    tg.add_argument("--contains", metavar="<rev>",
                    help="List only tags that contain <rev>")
    tg.add_argument("--points-at", metavar="<rev>",
                    help="List only tags that point at <rev>")
    tg.add_argument("--merged", nargs="?", const="HEAD", metavar="<rev>",
                    help="List only tags reachable from <rev> (default: HEAD)")
    tg.add_argument("--sort", metavar="<key>",
                    help="Sort by refname, committerdate, or authordate "
                         "(prefix '-' to reverse)")
    tg.add_argument("--format", metavar="<format>",
                    help="Format each tag (see 'branch --format')")

    # config
    cf = command("config", "Get/set repository config values",
                 "Read or write values in .notgit/config.  With <key> alone, "
                 "print its value; with <key> <value>, set it.")
    cf.add_argument("key", nargs="?", metavar="<key>",
                    help="section.key  e.g. user.name")
    cf.add_argument("value", nargs="?", metavar="<value>",
                    help="New value for <key>")
    cf.add_argument("--get", action="store_true",
                    help="Print the value of <key>")
    cf.add_argument("-l", "--list", action="store_true",
                    help="List all config values")
    cf.add_argument("--unset", action="store_true",
                    help="Remove <key>")
    cf.add_argument("--default", metavar="<value>",
                    help="Value to print with --get when <key> is not set")
    cf.add_argument("--local", action="store_true",
                    help="Use the repository config (the only scope)")

    # ls
    ls = command("ls", "List tracked files with last-add and last-commit dates")
    ls.add_argument("pathspecs", nargs="*", metavar="<path>",
                    help="Optional tracked paths or wildcard patterns")

    # versions
    vs = command("versions", "Write every committed version of a file",
                 "Write each distinct committed version of <file> next to it as "
                 "<stem>_<commit>_<YYYYmmdd_HHMM>_<n><ext>, oldest first.")
    vs.add_argument("file", metavar="<file>",
                    help="File whose committed versions should be written")

    # grep
    gp = command("grep", "Search tracked files for a pattern",
                 "Search tracked files in the working tree, the index "
                 "(--cached), or a <rev> for a regular expression.")
    gp.add_argument("pattern", nargs="?", default=None, metavar="<pattern>",
                    help="Pattern to search for (may be supplied via -e instead)")
    gp.add_argument("rev_or_paths", nargs="*", metavar="<rev>|<path>",
                    help="Optional revision followed by optional pathspecs")
    gp.add_argument("--pathspec", dest="pathspecs_after_dashdash", action="append",
                    help=argparse.SUPPRESS)
    gp.add_argument("-e", dest="e_pattern", metavar="<pattern>",
                    help="Use this pattern (overrides positional)")
    gp.add_argument("-n", "--line-number", action="store_true",
                    help="Prefix each matching line with its line number")
    gp.add_argument("-i", "--ignore-case", action="store_true",
                    help="Case-insensitive matching")
    gp.add_argument("-l", "--name-only", "--files-with-matches",
                    action="store_true",
                    help="Print only the names of files with matches")
    gp.add_argument("-L", "--files-without-match", action="store_true",
                    help="Print only the names of files without matches")
    gp.add_argument("-w", "--word-regexp", action="store_true",
                    help="Match whole words only")
    gp.add_argument("-F", "--fixed-strings", action="store_true",
                    help="Treat pattern as a fixed string, not a regex")
    gp.add_argument("--cached", action="store_true",
                    help="Search staged blobs (the index) instead of the working tree")
    gp.add_argument("--no-index", action="store_true",
                    help="Search files in the current directory, not in a repository")
    gp.add_argument("--untracked", action="store_true",
                    help="Also search untracked files")
    gp.add_argument("-v", "--invert-match", action="store_true",
                    help="Select non-matching lines")
    gp.add_argument("-c", "--count", action="store_true",
                    help="Print the number of matching lines per file")
    gp.add_argument("-q", "--quiet", action="store_true",
                    help="Print nothing; exit 0 if anything matched")
    gp.add_argument("-o", "--only-matching", action="store_true",
                    help="Print only the matched part of each line")
    gp.add_argument("-m", "--max-count", type=int, metavar="<n>",
                    help="Stop after <n> matching lines per file")
    gp.add_argument("-C", "--context", type=int, metavar="<n>",
                    help="Show <n> lines of context around matches")
    gp.add_argument("-A", "--after-context", type=int, default=0, metavar="<n>",
                    help="Show <n> lines after each match")
    gp.add_argument("-B", "--before-context", type=int, default=0, metavar="<n>",
                    help="Show <n> lines before each match")

    # stash  (sta: `st` is already the status parser above)
    sta = command("stash", "Save and restore dirty working state",
                  "Save local changes and revert to a clean working tree.  With "
                  "no subcommand, 'push' is assumed.  <stash> is stash@{<n>} or "
                  "<n> (default: the latest).")
    # Separate dest: a subparser's defaults would clobber a shared "quiet".
    sta.add_argument("-q", "--quiet", dest="stash_quiet", action="store_true",
                     help="Suppress feedback messages")
    st_sub = sta.add_subparsers(dest="stash_cmd", metavar="<subcommand>",
                                title="subcommands")
    stash_commands = {}

    def stash_command(name, help):
        sp = st_sub.add_parser(name, help=help, description=help,
                               prog=f"notgit stash {name}")
        stash_commands[name] = sp
        return sp

    def stash_save_options(sp):
        sp.add_argument("-u", "--include-untracked", action="store_true",
                        help="Also stash untracked files")
        sp.add_argument("-a", "--all", dest="all_files", action="store_true",
                        help="Also stash untracked and ignored files")
        sp.add_argument("-k", "--keep-index", action="store_true",
                        help="Keep staged changes in the index and working tree")
        sp.add_argument("-S", "--staged", action="store_true",
                        help="Stash only staged changes")
        sp.add_argument("-p", "--patch", action="store_true",
                        help="Interactively choose files to stash")
        sp.add_argument("-q", "--quiet", action="store_true",
                        help="Suppress feedback messages")

    st_push = stash_command("push", "Save local changes to a new stash entry")
    st_push.add_argument("-m", "--message", dest="message", nargs="?",
                         metavar="<msg>", help="Description of the stash entry")
    stash_save_options(st_push)
    st_save = stash_command("save", "Like push, with the message as an argument")
    st_save.add_argument("message", nargs="?", metavar="<msg>",
                         help="Description of the stash entry")
    stash_save_options(st_save)
    stash_command("list", "List stash entries")
    for name, help in (("pop", "Apply a stash entry and remove it"),
                       ("apply", "Apply a stash entry, keeping it")):
        sp = stash_command(name, help)
        sp.add_argument("stash_ref", nargs="?", metavar="<stash>",
                        help="Entry to apply (default: stash@{0})")
        sp.add_argument("--index", action="store_true",
                        help="Also restore the staged state")
        sp.add_argument("-q", "--quiet", action="store_true",
                        help="Suppress feedback messages")
    st_drop = stash_command("drop", "Remove a stash entry")
    st_drop.add_argument("stash_ref", nargs="?", metavar="<stash>",
                         help="Entry to drop (default: stash@{0})")
    st_drop.add_argument("-q", "--quiet", action="store_true",
                         help="Suppress feedback messages")
    st_show = stash_command("show", "Show the changes recorded in a stash entry")
    st_show.add_argument("stash_ref", nargs="?", metavar="<stash>",
                         help="Entry to show (default: stash@{0})")
    st_show.add_argument("-u", "--include-untracked", action="store_true",
                         help="Also show untracked files in the entry")
    st_show.add_argument("--only-untracked", action="store_true",
                         help="Show only untracked files in the entry")
    stash_command("clear", "Remove all stash entries")
    sta._notgit_subcommands = stash_commands

    p.epilog = _build_help_epilog(commands)
    return p


_DIFF_FLAGS = {"--staged", "--cached", "--stat", "--no-index", "--name-only",
               "--name-status", "--check", "--word-diff", "--exit-code", "--quiet"}

def _normalize_argv(argv: list[str]) -> list[str]:
    """Handle Git-style options argparse cannot express directly."""
    if not argv:
        return argv
    if argv[0] == "rev-parse":
        normalized = []
        for arg in argv:
            if arg.startswith("--short="):
                normalized.extend(["--short-value", arg.split("=", 1)[1]])
            else:
                normalized.append(arg)
        return normalized
    if argv[0] == "diff":
        # argparse.REMAINDER swallows options that follow a positional
        # ("diff foo --stat"), so hoist known flags in front of the
        # rev/path arguments. Tokens after "--" stay untouched.
        rest = argv[1:]
        sep = rest.index("--") if "--" in rest else len(rest)
        pre, post = rest[:sep], rest[sep:]
        flags = [a for a in pre if a in _DIFF_FLAGS]
        positionals = [a for a in pre if a not in _DIFF_FLAGS]
        return ["diff"] + flags + positionals + post
    if argv[0] == "grep":
        # argparse rejects "-e -dash"; the attached form "-e-dash" is the
        # same option, and searching for such patterns is what -e is for.
        attached, i = [], 0
        while i < len(argv):
            if argv[i] == "-e" and i + 1 < len(argv) and argv[i + 1] != "--":
                attached.append("-e" + argv[i + 1])
                i += 2
            else:
                attached.append(argv[i])
                i += 1
        argv = attached
    if argv[0] in ("checkout", "reset", "grep") and "--" in argv:
        # argparse drops "--", so carry the paths that follow it explicitly;
        # they must never be reinterpreted as revisions.
        sep = argv.index("--")
        normalized = list(argv[:sep])
        for path in argv[sep + 1:]:
            normalized.append(f"--pathspec={path}")
        return normalized
    if argv[0] == "log":
        normalized = ["log"]
        for arg in argv[1:]:
            m = re.fullmatch(r"-(\d+)", arg)
            if m:
                normalized.extend(["-n", m.group(1)])
            else:
                normalized.append(arg)
        return normalized
    return argv


# Commands whose -q/--quiet just silences informational stdout. (commit
# handles -q itself; rm/diff/grep/rev-parse give --quiet other meanings.)
_QUIET_STDOUT_COMMANDS = {"init", "clone", "branch", "checkout", "reset",
                          "restore", "merge", "stash"}


def _quiet_stdout(args) -> bool:
    if args.command not in _QUIET_STDOUT_COMMANDS:
        return False
    if not (getattr(args, "quiet", False) or getattr(args, "stash_quiet", False)):
        return False
    if args.command == "branch":
        # Like git, -q never hides a branch listing.
        mutating = (args.delete or args.force_delete or args.move
                    or args.force_move or args.name)
        return bool(mutating) and not (args.list or args.show_current)
    if args.command == "stash":
        return getattr(args, "stash_cmd", None) not in ("list", "show")
    return True


def main():
    parser = build_parser()
    args   = parser.parse_args(_normalize_argv(sys.argv[1:]))

    dispatch = {
        "init":     cmd_init,
        "clone":    cmd_clone,
        "import-git": cmd_import_git,
        "add":      cmd_add,
        "rm":       cmd_rm,
        "mv":       cmd_mv,
        "commit":   cmd_commit,
        "log":      cmd_log,
        "status":   cmd_status,
        "diff":     cmd_diff,
        "show":     cmd_show,
        "rev-parse": cmd_rev_parse,
        "branch":   cmd_branch,
        "checkout": cmd_checkout,
        "reset":    cmd_reset,
        "restore":  cmd_restore,
        "revert":   cmd_revert,
        "merge":    cmd_merge,
        "tag":      cmd_tag,
        "config":   cmd_config,
        "stash":    cmd_stash,
        "ls":       cmd_ls,
        "versions": cmd_versions,
        "grep":     cmd_grep,
    }

    if not args.command:
        parser.print_help()
        return

    fn = dispatch.get(args.command)
    if fn:
        mutating = {
            "init", "add", "rm", "mv", "commit", "branch", "checkout", "reset",
            "restore", "revert", "merge", "tag", "config", "stash",
            "versions",
        }
        lock = _repo_lock() if args.command in mutating else contextlib.nullcontext()
        quiet = (open(os.devnull, "w") if _quiet_stdout(args)
                 else contextlib.nullcontext())
        with lock, quiet as sink:
            if sink is not None:
                with contextlib.redirect_stdout(sink):
                    fn(args)
            elif args.command == "diff":
                _run_with_pager(fn, args)
            else:
                fn(args)
    else:
        print(f"notgit: '{args.command}' is not a notgit command. See 'notgit --help'.")
        sys.exit(1)


if __name__ == "__main__":
    main()
