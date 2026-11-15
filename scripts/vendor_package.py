#!/usr/bin/env python3
"""Authenticate canonical vendor payloads and package them without live-tree writes."""
from contextlib import contextmanager, redirect_stderr, redirect_stdout
from datetime import datetime, timezone
import argparse
import hashlib
import io
import json
import os
from pathlib import Path, PurePosixPath
import shutil
import signal
import stat
import subprocess
import sys
import tarfile
import tempfile

import gen_vendor_manifest as gen
import vendor_manifest_format

try:
    from compression.zstd import ZstdError
    CODEC_ERRORS = (ZstdError,)
except ImportError:
    CODEC_ERRORS = ()

ANSWERS_PINNED_INPUTS = True
ROOT = Path(__file__).resolve().parent.parent
FIELDS = ("cargo_lock_sha256", "summary", "crates")


class Refused(ValueError):
    pass


class RecoveryRequired(Refused):
    pass


def digest(stream):
    value = hashlib.sha256()
    for block in iter(lambda: stream.read(64 * 1024), b""):
        value.update(block)
    return value.hexdigest()


def file_hash(path):
    with path.open("rb") as stream:
        return digest(stream)


def entries(tree, embedded=False):
    if tree.is_symlink() or not tree.is_dir():
        raise Refused("TREE: vendor root must be a regular directory")
    result = {}
    for directory, dirs, files in os.walk(tree, followlinks=False):
        for name in dirs + files:
            path = Path(directory) / name
            relative = path.relative_to(tree).as_posix()
            mode = path.lstat().st_mode
            if not (stat.S_ISDIR(mode) or stat.S_ISREG(mode)):
                raise Refused("TYPE: links and special files are forbidden: " + relative)
            if embedded and relative == ".vendor_manifest.json" and stat.S_ISREG(mode):
                continue
            result[relative] = ("dir" if stat.S_ISDIR(mode) else "file", path)
    return result


def compare_tree(actual, canonical):
    got, expected = entries(actual, embedded=True), entries(canonical)
    if set(got) != set(expected):
        raise Refused("PATH_SET: vendor paths differ from canonical archives")
    for name, (kind, source) in expected.items():
        actual_kind, target = got[name]
        if kind != actual_kind:
            raise Refused("TYPE: vendor entry differs: " + name)
        if kind == "file" and file_hash(target) != file_hash(source):
            raise Refused("PAYLOAD: vendor bytes differ from canonical archive: " + name)


def bookend(root, lock, manifest):
    current = (root / "data/vendor_manifest.json")
    now = current.read_bytes() if current.exists() else None
    if (root / "Cargo.lock").read_bytes() != lock or now != manifest:
        raise Refused("INPUT_CHANGED: trusted lock or manifest changed during the operation")


def check_metadata(raw, expected, scratch, lock, label):
    target = scratch / (label + ".json")
    target.write_bytes(raw)
    errors, output = io.StringIO(), io.StringIO()
    with redirect_stderr(errors), redirect_stdout(output):
        status = gen.check_committed(str(target), str(lock))
    if status:
        raise Refused("MANIFEST: " + errors.getvalue().strip())
    actual = vendor_manifest_format.read_manifest(target)
    if any(actual.get(field) != expected[field] for field in FIELDS):
        raise Refused("MANIFEST: metadata differs from canonical archives")


def canonical_inventory(lock, caches):
    expected = {}
    def add(path, kind, checksum=None):
        value = (kind, checksum)
        if path in expected and expected[path] != value:
            raise Refused("CANONICAL_TYPE: conflicting path " + path)
        expected[path] = value
    for name, version, checksum in gen.third_party_packages(gen.parse_cargo_lock(str(lock))):
        prefix = name + "-" + version
        add(prefix, "dir")
        data = gen.fetch_crate(name, version, checksum, caches, download=False)
        seen, payload = set(), {}
        with tarfile.open(fileobj=io.BytesIO(data), mode="r:gz") as source:
            for member in source:
                path = PurePosixPath(member.name)
                if path.is_absolute() or ".." in path.parts or not path.parts or path.parts[0] != prefix:
                    raise Refused("CANONICAL_PATH: " + member.name)
                if path in seen:
                    raise Refused("CANONICAL_DUPLICATE: " + member.name)
                seen.add(path)
                if not (member.isdir() or member.type in (tarfile.REGTYPE, tarfile.AREGTYPE)):
                    raise Refused("CANONICAL_TYPE: links and special members are forbidden")
                relative = PurePosixPath(*path.parts[1:])
                if relative.as_posix() == ".cargo-checksum.json":
                    raise Refused("CANONICAL_RESERVED: archive contains generated checksum record")
                if path.name == ".cargo-ok" or not gen.vendor_includes(relative):
                    continue
                if member.isdir():
                    add(path.as_posix(), "dir")
                else:
                    if relative.as_posix() == ".":
                        raise Refused("CANONICAL_TYPE: crate root must be a directory")
                    value = digest(source.extractfile(member))
                    payload[relative.as_posix()] = value
                    add(path.as_posix(), "file", value)
                parent = path.parent
                while parent.as_posix() != ".":
                    add(parent.as_posix(), "dir")
                    parent = parent.parent
        record = {"$comment": gen.CARGO_CHECKSUM_COMMENT, "files": payload, "package": checksum}
        raw = json.dumps(record, separators=(",", ":"), sort_keys=True).encode()
        add(prefix + "/.cargo-checksum.json", "file", hashlib.sha256(raw).hexdigest())
    return expected


def prepare(root, scratch, require_manifest, caches=None):
    lock = (root / "Cargo.lock").read_bytes()
    reference = root / "data/vendor_manifest.json"
    manifest = reference.read_bytes() if reference.exists() else None
    if require_manifest and manifest is None:
        raise Refused("MANIFEST: committed data/vendor_manifest.json is required")
    snapshot_lock = scratch / "Cargo.lock"
    snapshot_lock.write_bytes(lock)
    canonical = scratch / "vendor"
    caches = gen.cargo_registry_cache_dirs() if caches is None else caches
    inventory = canonical_inventory(snapshot_lock, caches)
    gen.stage_third_party(canonical, str(snapshot_lock), caches, download=False)
    staged = entries(canonical)
    if set(staged) != set(inventory):
        raise Refused("CANONICAL_PATH_SET: staging changed archive paths on this filesystem")
    for path, (kind, checksum) in inventory.items():
        actual_kind, actual = staged[path]
        if kind != actual_kind or (kind == "file" and file_hash(actual) != checksum):
            raise Refused("CANONICAL_PAYLOAD: staged bytes differ from authenticated archive")
    generated = scratch / "generated.json"
    # Keep the public producer as the metadata owner; this operation never mints live metadata.
    result = subprocess.run([sys.executable, "scripts/gen_vendor_manifest.py", str(canonical), str(generated)],
                            cwd=root, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    if result.returncode:
        raise Refused("GENERATOR: " + (result.stderr or result.stdout).strip())
    bookend(root, lock, manifest)
    expected = vendor_manifest_format.read_manifest(generated)
    if manifest is not None:
        check_metadata(manifest, expected, scratch, snapshot_lock, "reference")
    return canonical, expected, lock, manifest


@contextmanager
def scratch_space():
    parent = Path(tempfile.gettempdir()) / ".ubd"
    parent.mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="clean-vendor-auth-", dir=parent) as name:
        yield Path(name)


def stop(process):
    try:
        os.killpg(process.pid, signal.SIGTERM)
    except ProcessLookupError:
        pass
    try:
        process.wait(timeout=5)
    except subprocess.TimeoutExpired:
        pass
    finally:
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        process.wait()


@contextmanager
def archive_reader(path, scratch):
    if "zst" in tarfile.TarFile.OPEN_METH:
        with tarfile.open(path, "r:zst", ignore_zeros=True) as archive:
            yield archive
        return
    codec = shutil.which("zstd")
    if codec is None:
        raise Refused("CODEC: Python zstd support or the zstd executable is required")
    with (scratch / "zstd-read.log").open("xb") as errors:
        process = subprocess.Popen([codec, "-d", "--stdout", "--", str(path)],
                                   stdout=subprocess.PIPE, stderr=errors, start_new_session=True)
        try:
            with tarfile.open(fileobj=process.stdout, mode="r|", ignore_zeros=True) as archive:
                yield archive
            process.stdout.close()
            if process.wait(timeout=600):
                raise Refused("CODEC: archive decompression failed")
        except BaseException:
            stop(process)
            raise


def write_archive(tree, destination, scratch):
    if "zst" in tarfile.TarFile.OPEN_METH:
        with tarfile.open(destination, "w:zst", dereference=True) as archive:
            archive.add(tree, arcname="vendor")
        return
    codec = shutil.which("zstd")
    if codec is None:
        raise Refused("CODEC: Python zstd support or the zstd executable is required")
    with destination.open("xb") as output, (scratch / "zstd-write.log").open("xb") as errors:
        process = subprocess.Popen([codec, "-q", "-c"], stdin=subprocess.PIPE,
                                   stdout=output, stderr=errors, start_new_session=True)
        try:
            with tarfile.open(fileobj=process.stdin, mode="w|", dereference=True) as archive:
                archive.add(tree, arcname="vendor")
            process.stdin.close()
            if process.wait(timeout=600):
                raise Refused("CODEC: archive compression failed")
        except BaseException:
            stop(process)
            raise


def verify_archive(path, canonical, expected, scratch, manifest_present):
    wanted = entries(canonical, embedded=True)
    seen, files, dirs = set(), set(), set()
    embedded = False
    limit = max(1024 * 1024, len(json.dumps(expected).encode()) * 4)
    with archive_reader(path, scratch) as archive:
        for member in archive:
            name = PurePosixPath(member.name)
            if name.is_absolute() or ".." in name.parts or not name.parts or name.parts[0] != "vendor":
                raise Refused("ARCHIVE_PATH: member is outside vendor: " + member.name)
            relative = PurePosixPath(*name.parts[1:]).as_posix()
            if relative == ".":
                relative = ""
            if relative in seen:
                raise Refused("ARCHIVE_DUPLICATE: " + relative)
            seen.add(relative)
            if not (member.isdir() or member.type in (tarfile.REGTYPE, tarfile.AREGTYPE)):
                raise Refused("ARCHIVE_TYPE: links and special members are forbidden")
            if member.mode & 0o7000:
                raise Refused("ARCHIVE_MODE: special permission bits are forbidden")
            if not relative:
                if not member.isdir():
                    raise Refused("ARCHIVE_TYPE: vendor root must be a directory")
                continue
            if relative == ".vendor_manifest.json":
                if not member.isfile() or member.size > limit:
                    raise Refused("MANIFEST: invalid or oversized embedded manifest")
                source = archive.extractfile(member)
                raw = source.read(limit + 1)
                if len(raw) != member.size:
                    raise Refused("MANIFEST: truncated embedded manifest")
                check_metadata(raw, expected, scratch, scratch / "Cargo.lock", "embedded")
                embedded = True
                continue
            if relative not in wanted:
                raise Refused("ARCHIVE_EXTRA: " + relative)
            kind, original = wanted[relative]
            if member.isdir():
                if kind != "dir":
                    raise Refused("ARCHIVE_TYPE: directory replaces a file")
                dirs.add(relative)
            else:
                if kind != "file" or member.size != original.stat().st_size:
                    raise Refused("ARCHIVE_SIZE: " + relative)
                source = archive.extractfile(member)
                if source is None or digest(source) != file_hash(original):
                    raise Refused("ARCHIVE_PAYLOAD: bytes differ: " + relative)
                files.add(relative)
            parent = PurePosixPath(relative).parent
            while parent.as_posix() != ".":
                dirs.add(parent.as_posix())
                parent = parent.parent
    if files != {p for p, (kind, _) in wanted.items() if kind == "file"} or dirs != {p for p, (kind, _) in wanted.items() if kind == "dir"}:
        raise Refused("ARCHIVE_MISSING: canonical payload paths are absent")
    if not manifest_present and not embedded:
        raise Refused("MANIFEST: committed or validated embedded manifest is required")


def authenticate(root, tree, caches=None):
    with scratch_space() as scratch:
        canonical, _, lock, manifest = prepare(root, scratch, True, caches)
        compare_tree(tree, canonical)
        bookend(root, lock, manifest)
    print("VENDOR_AUTH=ok: complete paths and bytes match lock-authenticated archives")


def publish_pair(archive, sidecar, output):
    pairs = [(archive, output / archive.name), (sidecar, output / sidecar.name)]
    prior = []
    try:
        for index, (_, destination) in enumerate(pairs):
            if destination.is_symlink() or (destination.exists() and not destination.is_file()):
                raise Refused("OUTPUT: destination is not a regular file")
            backup = archive.parent / ("prior-" + str(index)) if destination.exists() else None
            if backup is not None:
                shutil.copy2(destination, backup)
            prior.append(backup)
    except BaseException as error:
        error.vendor_rollback_complete = True  # no destination has been touched
        raise
    try:
        for source, destination in pairs:
            os.replace(source, destination)
    except BaseException as error:
        errors = []
        for (_, destination), backup in zip(pairs, prior):
            try:
                if backup is None:
                    destination.unlink(missing_ok=True)
                else:
                    os.replace(backup, destination)
            except BaseException as restore_error:
                errors.append(str(restore_error))
        if errors:
            raise RecoveryRequired("OUTPUT: restore incomplete; recovery state retained at " + str(archive.parent))
        error.vendor_rollback_complete = True
        raise


def package(root, version, output, caches=None):
    if not version or any(c in version for c in ("/", "\\", "\n", "\r")):
        raise Refused("VERSION: version must be a nonempty filename component")
    live = (root / "vendor").resolve()
    resolved_output = output.resolve()
    if resolved_output == live or live in resolved_output.parents:
        raise Refused("OUTPUT: archive output must be outside the live vendor tree")
    with scratch_space() as scratch:
        canonical, expected, lock, manifest = prepare(root, scratch, True, caches)
        compare_tree(root / "vendor", canonical)
        (canonical / ".vendor_manifest.json").write_bytes(manifest)
        output.mkdir(parents=True, exist_ok=True)
        name = "vendor-sources-v" + version + ".tar.zst"
        # Publish only complete private output; authentication failures never overwrite prior artifacts.
        pending = Path(tempfile.mkdtemp(prefix=".vendor-package-", dir=output))
        keep = False
        try:
            archive = pending / name
            write_archive(canonical, archive, scratch)
            verify_archive(archive, canonical, expected, scratch, True)
            checksum = file_hash(archive)
            sidecar = pending / (name + ".sha256")
            sidecar.write_text(checksum + "  " + name + "\n")
            bookend(root, lock, manifest)
            # Until installation or rollback positively completes, cancellation
            # must retain preimages rather than delete them in outer cleanup.
            keep = True
            try:
                publish_pair(archive, sidecar, output)
            except BaseException as error:
                keep = not getattr(error, "vendor_rollback_complete", False)
                raise
            else:
                keep = False
        except RecoveryRequired:
            keep = True
            raise
        finally:
            if not keep:
                shutil.rmtree(pending)
    print("packaged: " + str(output / name))
    print("sha256: " + checksum)


def verify(root, path, caches=None):
    if not path.is_file():
        raise Refused("ARCHIVE: file not found")
    before = file_hash(path)
    sidecar = Path(str(path) + ".sha256")
    if sidecar.exists():
        fields = sidecar.read_text().split()
        if not fields or fields[0] != before:
            raise Refused("SIDECAR: archive sha256 mismatch")
    else:
        print("warn: no archive sidecar; canonical source authentication remains required", file=sys.stderr)
    with scratch_space() as scratch:
        # Authenticate exactly the bytes copied here, never a later reopen of
        # the caller's mutable path between two matching bookend digests.
        snapshot = scratch / "archive.tar.zst"
        copied = hashlib.sha256()
        with path.open("rb") as source, snapshot.open("xb") as target:
            for block in iter(lambda: source.read(64 * 1024), b""):
                copied.update(block)
                target.write(block)
        if copied.hexdigest() != before:
            raise Refused("INPUT_CHANGED: archive changed while taking its snapshot")
        canonical, expected, lock, manifest = prepare(root, scratch, False, caches)
        verify_archive(snapshot, canonical, expected, scratch, manifest is not None)
        bookend(root, lock, manifest)
        if file_hash(path) != before:
            raise Refused("INPUT_CHANGED: archive changed during verification")
    print("verify OK: " + str(path))


def self_test():
    with scratch_space() as scratch:
        root = scratch / "fixture"
        (root / "scripts").mkdir(parents=True)
        (root / "data").mkdir()
        for name in ("gen_vendor_manifest.py", "vendor_manifest_format.py", "script_import_inputs.py"):
            shutil.copyfile(ROOT / "scripts" / name, root / "scripts" / name)
        cache = scratch / "cache"
        cache.mkdir()
        def crate(payload):
            return gen._synthetic_crate("demo", "1.0.0", [("demo-1.0.0/src/lib.rs", payload)])
        good, bad = crate(b"pub fn n()->u8{1}"), crate(b"pub fn n()->u8{2}")
        checksum = hashlib.sha256(good).hexdigest()
        archive = cache / "demo-1.0.0.crate"
        archive.write_bytes(good)
        (root / "Cargo.lock").write_text('[[package]]\nname = "demo"\nversion = "1.0.0"\nsource = "' + gen.CRATES_IO_SOURCE + '"\nchecksum = "' + checksum + '"\n')
        gen.stage_third_party(root / "vendor", str(root / "Cargo.lock"), [cache])
        subprocess.run([sys.executable, "scripts/gen_vendor_manifest.py", "vendor"], cwd=root, check=True, stdout=subprocess.DEVNULL)
        authenticate(root, root / "vendor", [cache])
        package(root, "selftest", root / "dist", [cache])
        verify(root, root / "dist/vendor-sources-vselftest.tar.zst", [cache])
        failures = []
        def refused(label, call):
            try:
                call()
            except (Refused, gen.StageRefused):
                print("VENDOR_AUTH_SELFTEST arm ok: " + label)
            else:
                failures.append(label)
                print("VENDOR_AUTH_SELFTEST arm FAILED: " + label)
        payload = root / "vendor/demo-1.0.0/src/lib.rs"
        payload.write_bytes(b"pub fn n()->u8{2}")
        refused("changed tree payload", lambda: authenticate(root, root / "vendor", [cache]))
        hostile = scratch / "hostile.tar.zst"
        write_archive(root / "vendor", hostile, scratch)
        refused("changed archive payload", lambda: verify(root, hostile, [cache]))
        archive.write_bytes(bad)
        shutil.rmtree(root / "vendor")
        files = gen.unpack_crate(bad, "demo", "1.0.0", root / "vendor")
        record = {"$comment": gen.CARGO_CHECKSUM_COMMENT, "files": files, "package": checksum}
        (root / "vendor/demo-1.0.0/.cargo-checksum.json").write_text(json.dumps(record, separators=(",", ":"), sort_keys=True))
        refused("changed archive authority", lambda: authenticate(root, root / "vendor", [cache]))
        if failures:
            return 1
    print("VENDOR_AUTH_SELFTEST=ok")
    return 0


def main():
    if sys.argv[1:] == ["--pinned-inputs"]:
        from script_import_inputs import first_party_imports
        paths = set(first_party_imports(Path(__file__)))
        paths.update(("scripts/package_vendor.sh", "scripts/build_offline.sh"))
        print("\n".join(sorted(paths)))
        return 0
    if sys.argv[1:] == ["--self-test"]:
        return self_test()
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    p = sub.add_parser("package")
    p.add_argument("version", nargs="?", default=datetime.now(timezone.utc).strftime('%Y.%m.%d'))
    p.add_argument("output", nargs="?", type=Path, default=Path("dist"))
    p = sub.add_parser("verify")
    p.add_argument("archive", type=Path)
    p = sub.add_parser("authenticate")
    p.add_argument("tree", type=Path)
    args = parser.parse_args()
    if args.command == "package":
        package(ROOT, args.version, args.output)
    elif args.command == "verify":
        verify(ROOT, args.archive)
    else:
        authenticate(ROOT, args.tree)
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (Refused, gen.StageRefused, OSError, ValueError, RecursionError, EOFError, tarfile.TarError, subprocess.SubprocessError) + CODEC_ERRORS as error:
        print("VENDOR_PACKAGE=refused: " + str(error), file=sys.stderr)
        raise SystemExit(1)
