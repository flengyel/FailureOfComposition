#!/usr/bin/env python3
"""Maintain and verify an isolated, persistent Linux mirror of FailureOfComposition.

Only selected source/configuration files are synchronized. Dependency checkouts,
build products, logs, and verification results are never copied from the source.
"""

import argparse
from datetime import datetime, timezone
import fcntl
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import signal
import stat
import subprocess
import sys
import tempfile


MARKER = ".syncfailcomp.json"
LOCK = ".syncfailcomp.lock"
OWNER = "FailureOfComposition"
PIN = "Audit/failure-composition-v36/evidence/evaluator-source-pins.json"


class SyncError(Exception):
    """Refuse an unsafe or inconsistent synchronization."""


class Interrupted(Exception):
    def __init__(self, number):
        self.number = number


def interrupt(number, _frame):
    raise Interrupted(number)


def no_symlinks(path):
    """Check every existing component, including dangling symbolic links."""
    path = Path(path).absolute()
    for component in reversed((path, *path.parents)):
        if component.is_symlink():
            raise SyncError(f"symbolic-link path component is not allowed: {component}")


def overlaps(left, right):
    return left == right or left in right.parents or right in left.parents


def validate_destination(source, destination, protected):
    """Validate paths without creating directories or changing source files."""
    source = Path(source).resolve(strict=True)
    destination = Path(destination)
    if not destination.is_absolute():
        raise SyncError(f"FAILCOMP_DST must be absolute: {destination}")
    no_symlinks(destination)
    destination = destination.resolve()
    if re.match(r"^/mnt/[a-zA-Z](?:/|$)", str(destination)):
        raise SyncError("FAILCOMP_DST must use Linux storage, not /mnt/<drive>")
    home = Path.home().resolve()
    if destination == Path("/") or destination == home or destination in home.parents:
        raise SyncError("destination must not be the root, home, or an ancestor of home")
    for other in (source, *(Path(item).resolve() for item in protected)):
        if overlaps(destination, other):
            raise SyncError(f"destination overlaps source or protected workspace: {other}")
    if destination.exists() and not destination.is_dir():
        raise SyncError(f"destination is not a directory: {destination}")
    if destination.exists() and any(destination.iterdir()) and not (destination / MARKER).exists():
        raise SyncError(f"refusing nonempty unowned destination: {destination}")
    return destination


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def selected_path(relative):
    """The exact ownership boundary; reject forged inventory deletion targets."""
    path = Path(relative)
    if path.is_absolute() or ".." in path.parts or any(part.startswith(".") for part in path.parts):
        return False
    if relative == PIN or relative in {
        "Lean/FailureOfComposition.lean", "Lean/CategoricalRiceShapiro.lean",
        "Lean/lakefile.toml", "Lean/lake-manifest.json", "Lean/lean-toolchain",
    }:
        return True
    if len(path.parts) < 3 or path.parts[0] != "Lean":
        return False
    if path.parts[1] == "FailureOfComposition":
        if path.parts[2:3] == ("Palomar",) and path.suffix in {".json", ".yaml"}:
            return True
        return path.suffix in {".lean", ".py", ".sh", ".md"}
    return path.parts[1] == "CategoricalRiceShapiro" and path.suffix == ".lean"


def source_inventory(source):
    """Inventory only maintained sources and the single evaluator provenance pin."""
    source = Path(source)
    paths = [source / relative for relative in (
        "Lean/FailureOfComposition.lean", "Lean/CategoricalRiceShapiro.lean",
        "Lean/lakefile.toml", "Lean/lake-manifest.json", "Lean/lean-toolchain", PIN,
    )]
    for name in ("FailureOfComposition", "CategoricalRiceShapiro"):
        directory = source / "Lean" / name
        no_symlinks(directory)
        if not directory.is_dir():
            raise SyncError(f"required source directory is missing: {directory}")
        for parent, dirs, files in os.walk(directory, followlinks=False):
            for name in list(dirs):
                child = Path(parent) / name
                if child.is_symlink():
                    raise SyncError(f"symbolic-link source directory is not allowed: {child}")
                if name.startswith(".") or name == "__pycache__":
                    dirs.remove(name)
            for name in files:
                path = Path(parent) / name
                if selected_path(path.relative_to(source).as_posix()):
                    paths.append(path)
    result = {}
    for path in sorted(paths):
        no_symlinks(path)
        if not path.is_file():
            raise SyncError(f"required source is not a regular file: {path}")
        result[path.relative_to(source).as_posix()] = {
            "sha256": digest(path), "mode": stat.S_IMODE(path.stat().st_mode),
        }
    for relative in ("Lean/FailureOfComposition/verify.sh",
                     "Lean/FailureOfComposition/prepare_packages.py"):
        if relative not in result:
            raise SyncError(f"required verifier source is missing: {relative}")
    return result


def load_marker(destination, source):
    path = destination / MARKER
    no_symlinks(path)
    if not path.exists():
        return {"format": 1, "owner": OWNER, "source_root": str(source), "files": {}}
    try:
        value = json.loads(path.read_text())
    except (OSError, ValueError) as error:
        raise SyncError(f"cannot read ownership marker: {error}") from error
    if not isinstance(value, dict) or value.get("format") != 1 or value.get("owner") != OWNER:
        raise SyncError("destination has an unrecognized ownership marker")
    if value.get("source_root") != str(source):
        raise SyncError("destination belongs to a different source repository")
    fields = ("files", "pending") if "pending" in value else ("files",)
    for field in fields:
        if not isinstance(value.get(field), dict):
            raise SyncError("invalid managed-file inventory")
        for relative, record in value[field].items():
            if not selected_path(relative) or not isinstance(record, dict):
                raise SyncError(f"invalid managed-file inventory entry: {relative}")
            if not re.fullmatch(r"[0-9a-f]{64}", str(record.get("sha256", ""))):
                raise SyncError(f"invalid managed-file digest: {relative}")
            if not isinstance(record.get("mode"), int) or not 0 <= record["mode"] <= 0o7777:
                raise SyncError(f"invalid managed-file mode: {relative}")
    return value


def recover_marker(destination, marker):
    """Recognize only old/new journaled contents after an interrupted atomic copy.

    No source file is changed here. The next synchronization can resume even if
    the source has since changed again; intervening local edits are rejected.
    """
    if "pending" not in marker:
        return marker
    old, new, actual = marker["files"], marker["pending"], {}
    for relative in old.keys() | new.keys():
        target = destination / relative
        no_symlinks(target)
        if not target.exists():
            if relative in old and relative in new:
                raise SyncError(f"managed file removed during interrupted sync: {target}")
            continue  # A not-yet-created new file or an already-pruned old file.
        if not target.is_file():
            raise SyncError(f"managed path changed type during interrupted sync: {target}")
        record = {"sha256": digest(target), "mode": stat.S_IMODE(target.stat().st_mode)}
        if record not in (old.get(relative), new.get(relative)):
            raise SyncError(f"local edit conflicts with interrupted synchronization: {target}")
        actual[relative] = record
    return {"format": 1, "owner": OWNER, "source_root": marker["source_root"], "files": actual}


def check_managed(destination, previous, inventory):
    """Reject all local edits and collisions before changing any managed file."""
    for relative, record in previous.items():
        target = destination / relative
        no_symlinks(target)
        if not target.is_file() or digest(target) != record["sha256"]:
            raise SyncError(f"managed file was changed or removed locally: {target}")
        if stat.S_IMODE(target.stat().st_mode) != record["mode"]:
            raise SyncError(f"managed file mode was changed locally: {target}")
    for relative in inventory:
        target = destination / relative
        no_symlinks(target)
        if target.exists() and relative not in previous:
            raise SyncError(f"refusing to overwrite an unowned file: {target}")


def check_mirror_shape(destination):
    """Generated artifacts must also remain in the isolated workspace."""
    allowed = {MARKER, LOCK, "Lean", "Audit", "logs", "tmp"}
    if any(path.name not in allowed and not (
            path.is_file() and path.name.startswith(".syncfailcomp-"))
           for path in destination.iterdir()):
        raise SyncError("destination contains unrelated top-level files or directories")
    lean = destination / "Lean"
    no_symlinks(lean)
    if lean.is_dir():
        allowed_lean = {"FailureOfComposition", "CategoricalRiceShapiro", ".lake",
                        "FailureOfComposition.lean", "CategoricalRiceShapiro.lean",
                        "lakefile.toml", "lake-manifest.json", "lean-toolchain"}
        if any(path.name not in allowed_lean and not (
                path.is_file() and path.name.startswith(".syncfailcomp-"))
               for path in lean.iterdir()):
            raise SyncError("mirror Lean directory contains unrelated files or libraries")
    for parent, directories, files in os.walk(destination, followlinks=False):
        for name in (*directories, *files):
            path = Path(parent) / name
            if path.is_symlink():
                raise SyncError(f"symbolic links are not allowed in the mirror: {path}")


def atomic_write(path, data, mode=0o600):
    no_symlinks(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    handle, temporary = tempfile.mkstemp(prefix=".syncfailcomp-", dir=path.parent)
    try:
        with os.fdopen(handle, "wb") as stream:
            stream.write(data)
        os.chmod(temporary, mode)
        os.replace(temporary, path)
    finally:
        if os.path.exists(temporary):
            os.unlink(temporary)


def save_marker(destination, marker):
    atomic_write(destination / MARKER, (json.dumps(marker, indent=2) + "\n").encode())


def synchronize(source, destination, inventory):
    """Caller holds the mirror flock; prune only unchanged previously owned files."""
    marker = recover_marker(destination, load_marker(destination, source))
    previous = marker["files"]
    check_managed(destination, previous, inventory)
    # Record both sides before replacing any file. Each replacement is atomic,
    # so recovery accepts precisely a known old or intended new file state.
    marker["pending"] = inventory
    save_marker(destination, marker)
    copied = removed = 0
    for relative, record in inventory.items():
        if previous.get(relative) == record:
            continue
        data = (source / relative).read_bytes()
        if hashlib.sha256(data).hexdigest() != record["sha256"]:
            raise SyncError(f"source changed during synchronization: {relative}")
        atomic_write(destination / relative, data, record["mode"])
        copied += 1
    for relative in previous.keys() - inventory.keys():
        target = destination / relative
        no_symlinks(target)
        if digest(target) != previous[relative]["sha256"]:
            raise SyncError(f"managed file changed before pruning: {target}")
        target.unlink()
        removed += 1
    marker["files"] = inventory
    marker.pop("pending", None)
    save_marker(destination, marker)
    return copied, removed


def protected_directories(source):
    """Obtain checked dependency locations using the existing read-only preflight."""
    path = source / "Lean/FailureOfComposition/prepare_packages.py"
    spec = importlib.util.spec_from_file_location("syncfailcomp_packages", path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    supplied = os.environ.get("CRS_LAKE_PACKAGES") or None
    packages = module.canonical_packages(source / "Lean", supplied)
    pcats = Path(os.environ.get("PCATS_DST") or Path.home() / "src/PCats").resolve()
    return [pcats, *(Path(entry["dir"]) for entry in packages["packages"])]


def run_logged(command, cwd, environment, log, lock_fd):
    """Tee output without a shell pipeline; return the original child exit code."""
    process = subprocess.Popen(command, cwd=cwd, env=environment, stdout=subprocess.PIPE,
                               stderr=subprocess.STDOUT, start_new_session=True,
                               pass_fds=(lock_fd,))
    try:
        while True:
            data = process.stdout.read1(65536)
            if not data:
                break
            log.buffer.write(data)
            log.flush()
            sys.stdout.buffer.write(data)
            sys.stdout.flush()
        code = process.wait()
    except BaseException:
        try:
            os.killpg(process.pid, signal.SIGTERM)
        except ProcessLookupError:
            pass
        try:
            process.wait(timeout=2)
        except subprocess.TimeoutExpired:
            pass
        # The immediate shell may exit before its descendants do. Stop the
        # whole remaining group before releasing the parent's lock descriptor.
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        process.wait()
        raise
    finally:
        process.stdout.close()
    return code if code >= 0 else 128 - code


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument("--check-environment", action="store_true",
                       help="synchronize, then check the mirrored environment without running Lake")
    modes.add_argument("--sync-only", action="store_true",
                       help="check the source environment and synchronize without building")
    args = parser.parse_args()
    if sys.version_info < (3, 9):
        raise SyncError("Python 3.9 or later is required")
    source = Path(__file__).resolve().parent.parent
    for name in ("PCATS_DST", "CRS_LAKE_PACKAGES"):
        if os.environ.get(name):
            os.environ[name] = str(Path(os.environ[name]).absolute())
    destination = Path(os.environ.get("FAILCOMP_DST") or Path.home() / "src/FailureOfComposition")
    # Reject an unsafe destination even before inspecting dependency checkouts.
    destination = validate_destination(source, destination, [
        Path(os.environ.get("PCATS_DST") or Path.home() / "src/PCats")])
    inventory = source_inventory(source)
    destination = validate_destination(source, destination, protected_directories(source))
    destination.mkdir(parents=True, exist_ok=True)
    no_symlinks(destination / LOCK)
    descriptor = os.open(destination / LOCK, os.O_CREAT | os.O_RDWR | os.O_NOFOLLOW, 0o600)
    with os.fdopen(descriptor, "w") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        # Recheck after waiting: another invocation may have initialized the mirror.
        check_mirror_shape(destination)
        marker = recover_marker(destination, load_marker(destination, source))
        if not (destination / MARKER).exists() and any(
                path.name != LOCK for path in destination.iterdir()):
            raise SyncError("destination became nonempty before ownership was established")
        check_managed(destination, marker["files"], inventory)
        if not (destination / MARKER).exists():
            save_marker(destination, marker)
        for relative in ("tmp", "logs"):
            no_symlinks(destination / relative)
            (destination / relative).mkdir(exist_ok=True)
        timestamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
        logfile = destination / "logs" / f"verify-{timestamp}-{os.getpid()}.log"
        environment = os.environ.copy()
        environment["TMPDIR"] = str(destination / "tmp")
        environment["PYTHONDONTWRITEBYTECODE"] = "1"
        with logfile.open("x") as log:
            def note(message):
                line = "syncfailcomp: " + message
                print(line, flush=True)
                print(line, file=log, flush=True)

            note(f"source      {source}")
            note(f"destination {destination}")
            note(f"log         {logfile}")
            note("checking source environment before copying managed files")
            code = run_logged(["bash", str(source / "Lean/FailureOfComposition/verify.sh"),
                               "--check-environment"], source, environment, log, lock.fileno())
            if code:
                note(f"source environment check failed (exit {code}); log retained")
                return code
            copied, removed = synchronize(source, destination, inventory)
            note(f"synchronized {len(inventory)} managed files: {copied} copied, {removed} pruned")
            if args.sync_only:
                note("PASS synchronization; verification was not requested")
                return 0
            command = ["bash", str(destination / "Lean/FailureOfComposition/verify.sh")]
            if args.check_environment:
                command.append("--check-environment")
            code = run_logged(command, destination, environment, log, lock.fileno())
            note(f"{'PASS' if code == 0 else 'FAIL'} mirrored verification (exit {code}); log retained")
            return code


if __name__ == "__main__":
    sys.dont_write_bytecode = True
    signal.signal(signal.SIGTERM, interrupt)
    signal.signal(signal.SIGHUP, interrupt)
    try:
        raise SystemExit(main())
    except (SyncError, OSError, ValueError) as error:
        print(f"syncfailcomp: {error}", file=sys.stderr)
        raise SystemExit(1)
    except KeyboardInterrupt:
        print("syncfailcomp: interrupted; existing logs and mirror retained", file=sys.stderr)
        raise SystemExit(130)
    except Interrupted as error:
        print("syncfailcomp: interrupted; existing logs and mirror retained", file=sys.stderr)
        raise SystemExit(128 + error.number)
