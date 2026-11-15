#!/usr/bin/env python3
"""Independent public CLI regressions for authenticated vendor publication.

All cache archives, lock files, manifests, trees and outputs live in private
fixtures. No Rust invocation, network fetch or full dependency graph is needed.
"""
from __future__ import annotations

from contextlib import contextmanager, redirect_stdout
import gzip
import hashlib
import io
import json
import os
from pathlib import Path
import shlex
import shutil
import stat
import subprocess
import sys
import tarfile
import tempfile
import unittest
from unittest.mock import patch

try:
    import compression.zstd as zstd
except ImportError:  # Python 3.11-3.13 can use the production external backend.
    zstd = None

ROOT = Path(__file__).resolve().parent.parent
if str(ROOT / "scripts") not in sys.path:
    sys.path.insert(0, str(ROOT / "scripts"))
SOURCE = "registry+https://github.com/rust-lang/crates.io-index"
PREFIX = "vendor/demo-1.2.3/"


def snapshot(path: Path) -> dict:
    """Record types, modes, bytes and link literals without following links."""
    if not path.exists() and not path.is_symlink():
        return {}
    result = {}
    paths = [path] if not path.is_dir() or path.is_symlink() else [path, *sorted(path.rglob("*"))]
    for item in paths:
        info = item.lstat()
        relative = "." if item == path else item.relative_to(path).as_posix()
        mode = stat.S_IMODE(info.st_mode)
        if stat.S_ISLNK(info.st_mode):
            result[relative] = ("link", mode, os.readlink(item))
        elif stat.S_ISREG(info.st_mode):
            result[relative] = ("file", mode, item.read_bytes())
        elif stat.S_ISDIR(info.st_mode):
            result[relative] = ("directory", mode)
        else:
            result[relative] = ("special", info.st_mode)
    return result


class VendorPackageTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory(prefix="vendor-package-tests-")
        self.addCleanup(self.temporary.cleanup)
        self.home = Path(self.temporary.name)
        self.repo = self.home / "fixture repo"
        scripts = self.repo / "scripts"
        scripts.mkdir(parents=True)
        runtime = {"scripts/build_offline.sh", ".cargo/config.offline.toml",
                   "scripts/package_vendor.sh", "scripts/gen_vendor_manifest.py",
                   "scripts/vendor_manifest_format.py", "scripts/script_import_inputs.py"}
        if (ROOT / "scripts/vendor_package.py").is_file():
            from script_import_inputs import first_party_imports
            runtime.add("scripts/vendor_package.py")
            runtime.update(first_party_imports(ROOT / "scripts/vendor_package.py"))
        for relative in runtime:
            destination = self.repo / relative
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(ROOT / relative, destination)
        self.cache_home = self.home / "cargo-home"
        self.cache_dir = self.cache_home / "registry/cache/index.crates.io-fixture"
        self.cache_dir.mkdir(parents=True)
        self.cache = self.cache_dir / "demo-1.2.3.crate"
        self.tmp = self.home / "tmp"
        self.tmp.mkdir()
        (self.tmp / ".ubd").mkdir()
        self.env = {**os.environ, "CLEAN_GATE_PYTHON": sys.executable,
                    "CARGO_HOME": str(self.cache_home), "TMPDIR": str(self.tmp),
                    "PYTHONDONTWRITEBYTECODE": "1",
                    "PATH": str(Path(sys.executable).parent) + os.pathsep + os.environ.get("PATH", "")}
        self.env.pop("PYTHONPATH", None)
        self.env.pop("PYTHONHOME", None)
        self.payloads = {
            "Cargo.toml": b'[package]\nname = "demo"\nversion = "1.2.3"\n',
            "src/lib.rs": b"pub fn value() -> u8 { 1 }\n",
            "docs/" + "long-name-" * 14 + ".txt": b"A canonical long path.\n",
        }
        self.cache.write_bytes(self.crate_bytes())
        self.lock = self.repo / "Cargo.lock"
        self.write_lock(hashlib.sha256(self.cache.read_bytes()).hexdigest())
        self.vendor = self.repo / "vendor"
        self.manifest = self.repo / "data/vendor_manifest.json"
        self.manifest.parent.mkdir()
        for args in (("--stage-third-party", str(self.vendor)),
                     (str(self.vendor), str(self.manifest))):
            result = self.generator(*args)
            self.assertEqual(result.returncode, 0, result.stdout)
        self.canonical = {p.relative_to(self.vendor).as_posix(): p.read_bytes()
                          for p in self.vendor.rglob("*") if p.is_file()}
        self.out = self.home / "out dir"
        self.sequence = 0

    def crate_bytes(self, entries=None) -> bytes:
        entries = entries if entries is not None else [
            ("demo-1.2.3/" + name, payload, tarfile.REGTYPE, "", {})
            for name, payload in self.payloads.items()]
        return gzip.compress(self.tar_bytes(entries), mtime=0)

    @staticmethod
    def tar_bytes(entries, archive_format=tarfile.PAX_FORMAT) -> bytes:
        output = io.BytesIO()
        with tarfile.open(fileobj=output, mode="w", format=archive_format) as archive:
            for name, payload, kind, target, headers in entries:
                member = tarfile.TarInfo(name)
                member.type, member.linkname = kind, target
                member.mode = 0o755 if kind == tarfile.DIRTYPE else 0o644
                member.mtime = 0
                member.pax_headers = dict(headers)
                member.size = len(payload) if kind == tarfile.REGTYPE else 0
                archive.addfile(member, io.BytesIO(payload) if kind == tarfile.REGTYPE else None)
        return output.getvalue()

    def compress(self, data: bytes) -> bytes:
        if zstd is not None:
            return zstd.compress(data)
        executable = shutil.which("zstd")
        self.assertIsNotNone(executable, "need Python 3.14 zstd or the supported external zstd backend")
        result = subprocess.run([executable, "-q", "--stdout"], input=data,
                                capture_output=True, timeout=10)
        self.assertEqual(result.returncode, 0, result.stderr)
        return result.stdout

    def decompress(self, data: bytes) -> bytes:
        if zstd is not None:
            return zstd.decompress(data)
        executable = shutil.which("zstd")
        self.assertIsNotNone(executable)
        result = subprocess.run([executable, "-d", "--stdout"], input=data,
                                capture_output=True, timeout=10)
        self.assertEqual(result.returncode, 0, result.stderr)
        return result.stdout

    def write_lock(self, checksum: str) -> None:
        self.lock.write_text('[[package]]\nname = "demo"\nversion = "1.2.3"\n'
                             f'source = "{SOURCE}"\nchecksum = "{checksum}"\n')

    def generator(self, *args):
        return subprocess.run([sys.executable, str(self.repo / "scripts/gen_vendor_manifest.py"), *args],
                              cwd=self.repo, env=self.env, text=True, stdout=subprocess.PIPE,
                              stderr=subprocess.STDOUT, timeout=15)

    def restore_vendor(self) -> None:
        shutil.rmtree(self.vendor)
        self.vendor.mkdir()
        for name, data in self.canonical.items():
            destination = self.vendor / name
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_bytes(data)

    def protected(self, extra=()) -> dict:
        paths = [self.lock, self.manifest, self.vendor, self.cache_home, *extra]
        return {str(path): snapshot(path) for path in paths}

    def cli(self, *args, accepted: bool, extra=(), reason=None):
        before = self.protected(extra)
        tmp_before, out_before = snapshot(self.tmp), snapshot(self.out)
        result = subprocess.run(["bash", str(self.repo / "scripts/package_vendor.sh"), *map(str, args)],
                                cwd=self.home, env=self.env, text=True, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, timeout=20)
        self.assertEqual(self.protected(extra), before, result.stdout)
        self.assertEqual(snapshot(self.tmp), tmp_before, result.stdout)
        self.assertNotIn("Traceback", result.stdout)
        if accepted:
            self.assertEqual(result.returncode, 0, result.stdout)
        else:
            self.assertNotEqual(result.returncode, 0, result.stdout)
            out_after = snapshot(self.out)
            # Creating an empty output directory publishes no artifact.
            if not out_before and set(out_after) == {"."}:
                out_after = {}
            self.assertEqual(out_after, out_before, result.stdout)
            for marker in ("verify OK:", "packaged:", "VENDOR_PACKAGE=ok", "VENDOR_AUTH=ok", "VENDOR_VERIFY=ok"):
                self.assertNotIn(marker, result.stdout)
            if reason:
                self.assertRegex(result.stdout.lower(), reason)
        return result

    def entries(self, embedded=True):
        entries = [("vendor", b"", tarfile.DIRTYPE, "", {})]
        for path in sorted(self.vendor.rglob("*")):
            name = "vendor/" + path.relative_to(self.vendor).as_posix()
            if path.is_symlink():
                entries.append((name, b"", tarfile.SYMTYPE, os.readlink(path), {}))
            elif path.is_dir():
                entries.append((name, b"", tarfile.DIRTYPE, "", {}))
            else:
                entries.append((name, path.read_bytes(), tarfile.REGTYPE, "", {}))
        if embedded:
            entries.append(("vendor/.vendor_manifest.json", self.manifest.read_bytes(),
                            tarfile.REGTYPE, "", {}))
        return entries

    def archive(self, entries=None, *, archive_format=tarfile.PAX_FORMAT, embedded=True):
        self.sequence += 1
        target = self.home / ("input-" + str(self.sequence) + ".tar.zst")
        target.write_bytes(self.compress(self.tar_bytes(
            entries if entries is not None else self.entries(embedded), archive_format)))
        self.sidecar(target)
        return target

    @staticmethod
    def sidecar(archive: Path) -> Path:
        result = Path(str(archive) + ".sha256")
        result.write_text(hashlib.sha256(archive.read_bytes()).hexdigest() + "  " + archive.name + "\n")
        return result

    def verify(self, archive: Path, accepted: bool, reason=None):
        return self.cli("verify", archive, accepted=accepted,
                        extra=(archive, Path(str(archive) + ".sha256")), reason=reason)

    @contextmanager
    def engine_context(self):
        import vendor_package
        with patch.dict(os.environ, self.env, clear=True), \
                patch.object(tempfile, "tempdir", str(self.tmp)):
            yield vendor_package

    def test_second_publication_replace_failure_restores_both_preimages(self):
        self.out.mkdir()
        archive = self.out / "vendor-sources-vfault.tar.zst"
        sidecar = Path(str(archive) + ".sha256")
        for post_effect in (False, True):
            with self.subTest(post_effect=post_effect):
                archive.write_bytes(b"original archive")
                sidecar.write_bytes(b"original sidecar")
                before, output_before, temp_before = self.protected(), snapshot(self.out), snapshot(self.tmp)
                stdout = io.StringIO()
                with self.engine_context() as engine:
                    real_replace = engine.os.replace
                    target = sidecar.resolve()
                    observed = []
                    def fail_second(source, destination, *args, **kwargs):
                        if Path(destination).resolve() == target and not observed:
                            self.assertNotEqual(archive.read_bytes(), b"original archive")
                            observed.append(True)
                            if post_effect:
                                real_replace(source, destination, *args, **kwargs)
                                self.assertNotEqual(sidecar.read_bytes(), b"original sidecar")
                            raise OSError("injected second publication replacement failure")
                        return real_replace(source, destination, *args, **kwargs)
                    with patch.object(engine.os, "replace", fail_second), redirect_stdout(stdout):
                        with self.assertRaises(OSError):
                            engine.package(self.repo, "fault", self.out, caches=[self.cache_dir])
                    self.assertEqual(observed, [True])
                self.assertEqual(self.protected(), before)
                self.assertEqual(snapshot(self.out), output_before)
                self.assertEqual(snapshot(self.tmp), temp_before)
                self.assertNotIn("packaged:", stdout.getvalue())

    def test_reader_reopen_aba_cannot_authenticate_different_archive_bytes(self):
        pristine = self.archive()
        target = self.vendor / "demo-1.2.3/src/lib.rs"
        target.write_bytes(target.read_bytes().replace(b"{ 1 }", b"{ 2 }"))
        changed = self.archive()
        self.restore_vendor()
        bad_bytes, good_bytes = changed.read_bytes(), pristine.read_bytes()
        self.assertNotEqual(bad_bytes, good_bytes)
        before = self.protected((changed, Path(str(changed) + ".sha256")))
        stdout = io.StringIO()
        observed = []
        with self.engine_context() as engine:
            with self.assertRaises(engine.Refused):
                engine.verify(self.repo, changed, caches=[self.cache_dir])
            real_reader = engine.archive_reader
            @contextmanager
            def swap_only_original(path, scratch):
                observed.append(Path(path).resolve())
                # An attacker changes only the caller-owned path, never a
                # verifier-private snapshot, then restores the original bytes.
                changed.write_bytes(good_bytes)
                try:
                    with real_reader(path, scratch) as reader:
                        yield reader
                finally:
                    changed.write_bytes(bad_bytes)
            with patch.object(engine, "archive_reader", swap_only_original), redirect_stdout(stdout):
                with self.assertRaises(engine.Refused):
                    engine.verify(self.repo, changed, caches=[self.cache_dir])
        self.assertTrue(observed)
        self.assertEqual(changed.read_bytes(), bad_bytes)
        self.assertEqual(self.protected((changed, Path(str(changed) + ".sha256"))), before)
        self.assertNotIn("verify OK:", stdout.getvalue())

    def test_interrupted_restore_retains_needed_old_output_preimage(self):
        self.out.mkdir()
        archive = self.out / "vendor-sources-vrestore.tar.zst"
        sidecar = Path(str(archive) + ".sha256")
        archive.write_bytes(b"original archive needed for recovery")
        sidecar.write_bytes(b"original sidecar")
        before, temp_before = self.protected(), snapshot(self.tmp)
        old_files = {p.resolve() for p in self.out.rglob("*") if p.is_file()}
        observed = []
        stdout = io.StringIO()
        with self.engine_context() as engine:
            real_replace = engine.os.replace
            def interrupt_restore(source, destination, *args, **kwargs):
                source_path, destination_path = Path(source), Path(destination).resolve()
                if destination_path == sidecar.resolve() and not observed:
                    observed.append("second install failed")
                    raise OSError("injected install failure")
                if (observed == ["second install failed"]
                        and destination_path == archive.resolve()
                        and source_path.read_bytes() == b"original archive needed for recovery"):
                    observed.append("restore interrupted")
                    raise KeyboardInterrupt("injected restore interruption")
                return real_replace(source, destination, *args, **kwargs)
            with patch.object(engine.os, "replace", interrupt_restore), redirect_stdout(stdout):
                with self.assertRaises(BaseException) as caught:
                    engine.package(self.repo, "restore", self.out, caches=[self.cache_dir])
            self.assertIsInstance(caught.exception, (engine.RecoveryRequired, KeyboardInterrupt))
        self.assertEqual(observed, ["second install failed", "restore interrupted"])
        self.assertEqual(sidecar.read_bytes(), b"original sidecar")
        if archive.read_bytes() != b"original archive needed for recovery":
            recovery = [p for p in self.out.rglob("*") if p.is_file() and p.resolve() not in old_files]
            self.assertTrue(any(p.read_bytes() == b"original archive needed for recovery" for p in recovery),
                            "failed restoration must retain the needed original archive preimage")
        self.assertEqual(self.protected(), before)
        self.assertEqual(snapshot(self.tmp), temp_before)
        self.assertNotIn("packaged:", stdout.getvalue())

    def test_compression_failure_preserves_prior_output_pair(self):
        self.out.mkdir()
        archive = self.out / "vendor-sources-vcompression.tar.zst"
        archive.write_bytes(b"old archive")
        Path(str(archive) + ".sha256").write_bytes(b"old sidecar")
        before, output_before, temp_before = self.protected(), snapshot(self.out), snapshot(self.tmp)
        stdout = io.StringIO()
        observed = []
        def fail_compression(tree, destination, scratch):
            self.assertEqual((tree / "demo-1.2.3/src/lib.rs").read_bytes(), self.payloads["src/lib.rs"])
            destination.write_bytes(b"partial compressed output")
            observed.append(True)
            raise OSError("injected compressor write failure")
        with self.engine_context() as engine, \
                patch.object(engine, "write_archive", fail_compression), redirect_stdout(stdout):
            with self.assertRaises(OSError):
                engine.package(self.repo, "compression", self.out, caches=[self.cache_dir])
        self.assertEqual(observed, [True])
        self.assertEqual(self.protected(), before)
        self.assertEqual(snapshot(self.out), output_before)
        self.assertEqual(snapshot(self.tmp), temp_before)
        self.assertNotIn("packaged:", stdout.getvalue())

    def test_output_inside_vendor_and_its_alias_refuse(self):
        alias = self.home / "vendor-alias"
        alias.symlink_to(self.vendor, target_is_directory=True)
        for output in (self.vendor, self.vendor / "dist", alias / "dist"):
            with self.subTest(output=output):
                self.cli("package", "inside", output, accepted=False,
                         extra=(alias,), reason="output|outside|vendor")

    def test_real_external_zstd_writer_and_reader(self):
        self.assertIsNotNone(shutil.which("zstd"), "external backend qualification needs real zstd")
        before, temp_before = self.protected(), snapshot(self.tmp)
        calls = []
        with self.engine_context() as engine:
            native_modes = {k: v for k, v in engine.tarfile.TarFile.OPEN_METH.items() if k != "zst"}
            real_popen = engine.subprocess.Popen
            def track_popen(argv, *args, **kwargs):
                if isinstance(argv, (list, tuple)) and Path(argv[0]).name == "zstd":
                    calls.append(list(map(str, argv)))
                return real_popen(argv, *args, **kwargs)
            with patch.dict(engine.tarfile.TarFile.OPEN_METH, native_modes, clear=True), \
                    patch.object(engine.subprocess, "Popen", track_popen):
                engine.package(self.repo, "external", self.out, caches=[self.cache_dir])
                archive = self.out / "vendor-sources-vexternal.tar.zst"
                engine.verify(self.repo, archive, caches=[self.cache_dir])
        self.assertTrue(any("-c" in argv for argv in calls), calls)
        self.assertTrue(any("-d" in argv for argv in calls), calls)
        self.assertEqual(self.protected(), before)
        self.assertEqual(snapshot(self.tmp), temp_before)
        self.verify(archive, True)

    def test_reserved_and_duplicate_authenticated_cache_members_refuse(self):
        original_cache, original_lock = self.cache.read_bytes(), self.lock.read_bytes()
        original_manifest = self.manifest.read_bytes()
        ordinary = [("demo-1.2.3/" + name, data, tarfile.REGTYPE, "", {})
                    for name, data in self.payloads.items()]
        lib = next(item for item in ordinary if item[0] == "demo-1.2.3/src/lib.rs")
        extras = [
            ("demo-1.2.3/.cargo-checksum.json", b"{}", tarfile.REGTYPE, "", {}),
            lib,
            ("demo-1.2.3/src/./lib.rs", lib[1], tarfile.REGTYPE, "", {}),
            ("demo-1.2.3//src/lib.rs", lib[1], tarfile.REGTYPE, "", {}),
        ]
        for extra in extras:
            with self.subTest(extra=extra[0]):
                self.restore_vendor()
                malicious = self.crate_bytes(ordinary + [extra])
                self.cache.write_bytes(malicious)
                checksum = hashlib.sha256(malicious).hexdigest()
                self.write_lock(checksum)
                metadata = json.loads(original_manifest)
                metadata["cargo_lock_sha256"] = hashlib.sha256(self.lock.read_bytes()).hexdigest()
                metadata["crates"][0]["checksum"] = checksum
                self.manifest.write_text(json.dumps(metadata))
                # Without the duplicate guard, last-wins extraction would otherwise
                # produce this exact candidate: keep its generated package pin fresh.
                checks = self.vendor / "demo-1.2.3/.cargo-checksum.json"
                record = json.loads(checks.read_text())
                record["package"] = checksum
                checks.write_text(json.dumps(record, sort_keys=True, separators=(",", ":")))
                valid = self.generator("--check", str(self.manifest), str(self.lock))
                self.assertEqual(valid.returncode, 0, valid.stdout)
                self.cli("authenticate", self.vendor, accepted=False, reason="canonical.*reserved|canonical.*duplicate")
                self.cli("package", "invalid-cache", self.out, accepted=False)
        self.cache.write_bytes(original_cache)
        self.lock.write_bytes(original_lock)
        self.manifest.write_bytes(original_manifest)
        self.restore_vendor()
        self.cli("authenticate", self.vendor, accepted=True)

    def offline_stub(self):
        directory = self.home / "protocol bin"
        directory.mkdir()
        receipt = self.home / "targo-protocol.jsonl"
        driver = directory / "protocol.py"
        driver.write_text(
            "import hashlib, json, os, pathlib, sys\n"
            "argv = sys.argv[1:]\n"
            "config = pathlib.Path(argv[argv.index('--config') + 1]) if '--config' in argv else None\n"
            "row = {'marker': 'CLEAN_OFFLINE_TARGO_STUB_V1', 'argv': argv,\n"
            "       'cwd': str(pathlib.Path.cwd().resolve()),\n"
            "       'config_sha256': hashlib.sha256(config.read_bytes()).hexdigest() if config and config.is_file() else None}\n"
            "with open(os.environ['CLEAN_OFFLINE_STUB_RECEIPT'], 'a') as stream: stream.write(json.dumps(row) + '\\n')\n"
            "print('CLEAN_OFFLINE_TARGO_STUB=hit')\n")
        stub = directory / "targo"
        stub.write_text("#!/bin/sh\nexec " + shlex.quote(sys.executable) + " "
                        + shlex.quote(str(driver)) + ' "$@"\n')
        stub.chmod(0o755)
        env = {**self.env, "TARGO": str(stub),
               "PATH": str(directory) + os.pathsep + self.env["PATH"],
               "CLEAN_OFFLINE_STUB_RECEIPT": str(receipt)}
        self.assertEqual(Path(shutil.which("targo", path=env["PATH"])).resolve(), stub.resolve())
        return env, receipt, (stub, driver)

    def offline_call(self, args, env, protected, accepted):
        before = self.protected(protected)
        tmp_before = snapshot(self.tmp)
        result = subprocess.run(["/bin/bash", str(self.repo / "scripts/build_offline.sh"), *args],
                                cwd=self.home, env=env, text=True, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, timeout=20)
        self.assertEqual(self.protected(protected), before, result.stdout)
        self.assertEqual(snapshot(self.tmp), tmp_before, result.stdout)
        self.assertNotIn("Traceback", result.stdout)
        self.assertEqual(result.returncode, 0 if accepted else 1, result.stdout)
        return result

    def test_offline_wrapper_routes_locked_build_and_check_after_authentication(self):
        env, receipt, stub_inputs = self.offline_stub()
        config = self.repo / ".cargo/config.offline.toml"
        protected = (*stub_inputs, config, self.repo / "scripts/build_offline.sh")
        for args, verb in ((("--locked",), "build"), (("check", "--locked", "-p", "demo"), "check")):
            with self.subTest(verb=verb):
                receipt.unlink(missing_ok=True)
                result = self.offline_call(args, env, protected, True)
                rows = [json.loads(line) for line in receipt.read_text().splitlines()]
                self.assertEqual(len(rows), 1)
                self.assertEqual(rows[0]["marker"], "CLEAN_OFFLINE_TARGO_STUB_V1")
                self.assertEqual(rows[0]["cwd"], str(self.repo.resolve()))
                tail = list(args) if verb == "build" else list(args[1:])
                self.assertEqual(rows[0]["argv"], ["--unverified", verb, "--config",
                                 ".cargo/config.offline.toml", "--offline", *tail])
                self.assertEqual(rows[0]["config_sha256"], hashlib.sha256(config.read_bytes()).hexdigest())
                self.assertIn("CLEAN_OFFLINE_TARGO_STUB=hit", result.stdout)

    def test_offline_wrapper_refuses_untrusted_payload_or_cache_before_targo(self):
        env, receipt, stub_inputs = self.offline_stub()
        config = self.repo / ".cargo/config.offline.toml"
        protected = (*stub_inputs, config, self.repo / "scripts/build_offline.sh")
        cache = self.cache.read_bytes()
        for mutation in ("forged payload map", "missing cache", "corrupt cache"):
            with self.subTest(mutation=mutation):
                self.restore_vendor()
                self.cache.write_bytes(cache)
                receipt.unlink(missing_ok=True)
                if mutation == "forged payload map":
                    target = self.vendor / "demo-1.2.3/src/lib.rs"
                    target.write_bytes(target.read_bytes().replace(b"{ 1 }", b"{ 2 }"))
                    checks = self.vendor / "demo-1.2.3/.cargo-checksum.json"
                    record = json.loads(checks.read_text())
                    record["files"]["src/lib.rs"] = hashlib.sha256(target.read_bytes()).hexdigest()
                    checks.write_text(json.dumps(record, sort_keys=True, separators=(",", ":")))
                elif mutation == "missing cache":
                    self.cache.unlink()
                else:
                    self.cache.write_bytes(cache[:-1] + bytes([cache[-1] ^ 1]))
                result = self.offline_call(("check", "--locked"), env, protected, False)
                self.assertFalse(receipt.exists(), result.stdout)
                self.assertNotIn("CLEAN_OFFLINE_TARGO_STUB=hit", result.stdout)

    def test_pristine_authenticate_package_and_verify(self):
        self.cli("authenticate", self.vendor, accepted=True)
        self.cli("package", "public-test", self.out, accepted=True)
        archive = self.out / "vendor-sources-vpublic-test.tar.zst"
        sidecar = Path(str(archive) + ".sha256")
        self.assertTrue(archive.is_file())
        self.assertEqual(sidecar.read_text().split(),
                         [hashlib.sha256(archive.read_bytes()).hexdigest(), archive.name])
        self.assertEqual({p.name for p in self.out.iterdir()}, {archive.name, sidecar.name})
        with tarfile.open(fileobj=io.BytesIO(self.decompress(archive.read_bytes())), mode="r:") as reader:
            files = {m.name.removeprefix("./"): reader.extractfile(m).read()
                     for m in reader if m.isfile()}
        for name, data in self.canonical.items():
            self.assertEqual(files["vendor/" + name], data)
        embedded = json.loads(files["vendor/.vendor_manifest.json"])
        reference = json.loads(self.manifest.read_text())
        for field in ("cargo_lock_sha256", "summary", "crates"):
            self.assertEqual(embedded[field], reference[field])
        self.verify(archive, True)

    def test_existing_live_embedded_manifest_is_preserved(self):
        embedded = self.vendor / ".vendor_manifest.json"
        embedded.write_bytes(self.manifest.read_bytes())
        self.cli("package", "embedded", self.out, accepted=True)
        self.assertEqual(embedded.read_bytes(), self.manifest.read_bytes())

    def test_pristine_package_can_replace_existing_output_pair(self):
        self.out.mkdir()
        archive = self.out / "vendor-sources-vreplace.tar.zst"
        archive.write_bytes(b"old archive")
        Path(str(archive) + ".sha256").write_bytes(b"old sidecar")
        self.cli("package", "replace", self.out, accepted=True)
        self.verify(archive, True)

    def test_payload_changes_refuse_all_public_paths(self):
        for mutation in ("same-length", "forged-map", "missing", "extra"):
            with self.subTest(mutation=mutation):
                self.restore_vendor()
                path = self.vendor / "demo-1.2.3/src/lib.rs"
                if mutation in ("same-length", "forged-map"):
                    original = path.read_bytes()
                    changed = original.replace(b"{ 1 }", b"{ 2 }")
                    self.assertNotEqual(original, changed)
                    self.assertEqual(len(original), len(changed))
                    path.write_bytes(changed)
                    if mutation == "forged-map":
                        checks = self.vendor / "demo-1.2.3/.cargo-checksum.json"
                        data = json.loads(checks.read_text())
                        data["files"]["src/lib.rs"] = hashlib.sha256(changed).hexdigest()
                        checks.write_text(json.dumps(data, sort_keys=True, separators=(",", ":")))
                elif mutation == "missing":
                    path.unlink()
                else:
                    (path.parent / ".hidden-extra").write_bytes(b"unlisted payload")
                self.cli("authenticate", self.vendor, accepted=False)
                self.cli("package", "mutated", self.out, accepted=False)
                self.verify(self.archive(), False)

    def test_tree_symbolic_link_is_not_a_regular_payload(self):
        target = self.vendor / "demo-1.2.3/src/lib.rs"
        outside = self.home / "same-bytes.rs"
        outside.write_bytes(target.read_bytes())
        target.unlink()
        target.symlink_to(outside)
        self.cli("authenticate", self.vendor, accepted=False, extra=(outside,))
        self.cli("package", "linked", self.out, accepted=False, extra=(outside,))

    def test_metadata_check_remains_metadata_only(self):
        (self.vendor / "demo-1.2.3/src/lib.rs").write_bytes(b"untrusted changed payload\n")
        result = self.generator("--check", str(self.manifest), str(self.lock))
        self.assertEqual(result.returncode, 0, result.stdout)
        self.cli("authenticate", self.vendor, accepted=False)

    def test_missing_and_corrupt_cache_fail_closed_without_replacement(self):
        archive = self.archive()
        canonical = self.cache.read_bytes()
        for corruption in (None, canonical[:-1] + bytes([canonical[-1] ^ 1])):
            with self.subTest(missing=corruption is None):
                if self.cache.exists():
                    self.cache.unlink()
                if corruption is not None:
                    self.cache.write_bytes(corruption)
                self.cli("authenticate", self.vendor, accepted=False, reason="cache|checksum")
                self.cli("package", "cache", self.out, accepted=False, reason="cache|checksum")
                self.verify(archive, False, reason="cache|checksum")
        self.cache.write_bytes(canonical)
        self.cli("authenticate", self.vendor, accepted=True)

    def test_authentication_failure_preserves_prior_archive_and_sidecar(self):
        self.out.mkdir()
        archive = self.out / "vendor-sources-vprior.tar.zst"
        archive.write_bytes(b"prior archive retained")
        Path(str(archive) + ".sha256").write_bytes(b"prior sidecar retained")
        self.cache.unlink()
        self.cli("package", "prior", self.out, accepted=False, reason="cache")

    def test_trusted_lock_is_required(self):
        archive = self.archive()
        self.lock.unlink()
        self.cli("authenticate", self.vendor, accepted=False, reason="lock")
        self.cli("package", "lockless", self.out, accepted=False, reason="lock")
        self.verify(archive, False, reason="lock")

    def test_package_requires_committed_manifest(self):
        self.manifest.unlink()
        self.cli("package", "no-metadata", self.out, accepted=False, reason="manifest")

    def test_verify_without_embedded_manifest_uses_committed_metadata(self):
        self.verify(self.archive(embedded=False), True)

    def test_verify_can_check_embedded_metadata_against_canonical_bytes(self):
        archive = self.archive()
        self.manifest.unlink()
        self.verify(archive, True)

    def test_embedded_claims_cannot_override_canonical_source(self):
        entries = self.entries()
        metadata = json.loads(self.manifest.read_text())
        metadata["crates"][0]["checksum"] = "0" * 64
        entries[-1] = ("vendor/.vendor_manifest.json", json.dumps(metadata).encode(),
                       tarfile.REGTYPE, "", {})
        archive = self.archive(entries)
        self.manifest.unlink()
        self.verify(archive, False)

    def test_missing_all_metadata_refuses(self):
        archive = self.archive(embedded=False)
        self.manifest.unlink()
        self.verify(archive, False)

    def test_archive_sidecar_mismatch_refuses(self):
        archive = self.archive()
        Path(str(archive) + ".sha256").write_text("0" * 64 + "  " + archive.name + "\n")
        self.verify(archive, False, reason="sha256|checksum|sidecar")

    def test_authentic_archive_without_optional_sidecar_still_verifies(self):
        archive = self.archive()
        Path(str(archive) + ".sha256").unlink()
        self.verify(archive, True)

    def test_malformed_compressed_archive_refuses_cleanly(self):
        archive = self.archive()
        archive.write_bytes(b"not a zstd archive")
        self.sidecar(archive)
        self.verify(archive, False)

    def test_pax_and_gnu_long_name_archives_are_accepted(self):
        for archive_format in (tarfile.PAX_FORMAT, tarfile.GNU_FORMAT):
            with self.subTest(format=archive_format):
                self.verify(self.archive(archive_format=archive_format), True)

    def test_uniform_dot_prefix_archive_is_accepted(self):
        entries = [("./" + name, payload, kind, target, headers)
                   for name, payload, kind, target, headers in self.entries()]
        self.verify(self.archive(entries), True)

    def test_unsafe_archive_paths_never_write_outside(self):
        sentinel = self.tmp / "outside-sentinel"
        sentinel.write_bytes(b"outside sentinel retained")
        absolute = self.home / "absolute-sentinel"
        absolute.write_bytes(b"absolute sentinel retained")
        for name in ("../outside-sentinel", str(absolute),
                     PREFIX + "../../../outside-sentinel"):
            with self.subTest(name=name):
                entries = self.entries() + [(name, b"overwritten", tarfile.REGTYPE, "", {})]
                archive = self.archive(entries)
                self.cli("verify", archive, accepted=False,
                         extra=(archive, Path(str(archive) + ".sha256"), sentinel, absolute))

    def test_links_and_special_archive_entries_refuse(self):
        outside = self.home / "link-sentinel"
        outside.write_bytes(self.payloads["src/lib.rs"])
        cases = [
            (tarfile.SYMTYPE, PREFIX + "src/lib.rs", str(outside)),
            (tarfile.LNKTYPE, PREFIX + "src/lib.rs", str(outside)),
            (tarfile.FIFOTYPE, PREFIX + "src/lib.rs", ""),
            (tarfile.CHRTYPE, PREFIX + "src/lib.rs", ""),
            (tarfile.BLKTYPE, PREFIX + "src/lib.rs", ""),
        ]
        for kind, name, target in cases:
            with self.subTest(kind=kind):
                base = [entry for entry in self.entries() if entry[0] != PREFIX + "src/lib.rs"]
                archive = self.archive(base + [(name, b"", kind, target, {})])
                self.cli("verify", archive, accepted=False,
                         extra=(archive, Path(str(archive) + ".sha256"), outside))
        entries = [entry for entry in self.entries() if not entry[0].startswith(PREFIX + "src")]
        entries.extend([(PREFIX + "src", b"", tarfile.SYMTYPE, str(self.home), {}),
                        (PREFIX + "src/link-sentinel", b"bad", tarfile.REGTYPE, "", {})])
        archive = self.archive(entries)
        self.cli("verify", archive, accepted=False,
                 extra=(archive, Path(str(archive) + ".sha256"), outside))

    def test_duplicate_effective_archive_paths_refuse(self):
        original = next(entry for entry in self.entries() if entry[0] == PREFIX + "src/lib.rs")
        variants = [original,
                    (original[0], b"different bytes", tarfile.REGTYPE, "", {}),
                    (PREFIX + "src/./lib.rs", original[1], tarfile.REGTYPE, "", {}),
                    ("vendor//demo-1.2.3/src/lib.rs", original[1], tarfile.REGTYPE, "", {}),
                    ("placeholder", original[1], tarfile.REGTYPE, "", {"path": original[0]})]
        for entry in variants:
            with self.subTest(duplicate=entry[0], headers=entry[4]):
                self.verify(self.archive(self.entries() + [entry]), False)

    def test_pax_effective_path_traversal_refuses(self):
        sentinel = self.tmp / "outside-sentinel"
        sentinel.write_bytes(b"PAX sentinel retained")
        entry = (PREFIX + "src/lib.rs", self.payloads["src/lib.rs"], tarfile.REGTYPE, "",
                 {"path": "../outside-sentinel"})
        base = [item for item in self.entries() if item[0] != PREFIX + "src/lib.rs"]
        archive = self.archive(base + [entry])
        self.cli("verify", archive, accepted=False,
                 extra=(archive, Path(str(archive) + ".sha256"), sentinel))

    def test_wrong_archive_roots_and_extra_top_level_entries_refuse(self):
        cases = [
            [("other", b"", tarfile.DIRTYPE, "", {})],
            [("vendor", b"root file", tarfile.REGTYPE, "", {})],
            self.entries() + [(".hidden-top", b"untrusted", tarfile.REGTYPE, "", {})],
            self.entries() + [("vendor/.hidden-extra", b"untrusted", tarfile.REGTYPE, "", {})],
        ]
        for index, entries in enumerate(cases):
            with self.subTest(case=index):
                self.verify(self.archive(entries), False)

    def test_authenticated_cache_archive_rejects_traversal_and_links(self):
        original_cache = self.cache.read_bytes()
        original_lock, original_manifest = self.lock.read_bytes(), self.manifest.read_bytes()
        cases = [("malformed gzip", b"not a gzip or tar archive")]
        for kind, name, target in ((tarfile.REGTYPE, "demo-1.2.3/../../escape", ""),
                                   (tarfile.SYMTYPE, "demo-1.2.3/link", str(self.home)),
                                   (tarfile.LNKTYPE, "demo-1.2.3/link", "demo-1.2.3/src/lib.rs")):
            cases.append((str(kind), self.crate_bytes([(name, b"bad", kind, target, {})])))
        for label, malicious in cases:
            with self.subTest(case=label):
                self.cache.write_bytes(malicious)
                checksum = hashlib.sha256(malicious).hexdigest()
                self.write_lock(checksum)
                metadata = json.loads(original_manifest)
                metadata["cargo_lock_sha256"] = hashlib.sha256(self.lock.read_bytes()).hexdigest()
                metadata["crates"][0]["checksum"] = checksum
                self.manifest.write_text(json.dumps(metadata))
                valid_metadata = self.generator("--check", str(self.manifest), str(self.lock))
                self.assertEqual(valid_metadata.returncode, 0, valid_metadata.stdout)
                self.cli("authenticate", self.vendor, accepted=False)
                self.cli("package", "unsafe-cache", self.out, accepted=False)
        self.cache.write_bytes(original_cache)
        self.lock.write_bytes(original_lock)
        self.manifest.write_bytes(original_manifest)
        self.cli("authenticate", self.vendor, accepted=True)


if __name__ == "__main__":
    unittest.main()
