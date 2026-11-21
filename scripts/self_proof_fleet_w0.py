# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Validate and run the pinned native W0 reader."""

from dataclasses import dataclass
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

if __package__:
    from .kcheck_coverage_export import Refused, no_number, once
else:
    from kcheck_coverage_export import Refused, no_number, once

BOARD = Path("data/self_proof_scoreboard.json")
COVERAGE = Path("data/kcheck_coverage.json")
BUILD_SCHEMA = "clean.w0_planning_build.v1"
OBJECT_ID = re.compile(r"[0-9a-f]{40}")


class W0BuildError(ValueError):
    """The receipt, executable or native response failed custody checks."""


def saved_board_refusal(root, canonical):
    """Read the Fleet warning by comparing the recorded text with canonical W0."""
    try:
        recorded = (root / BOARD).read_text(encoding="utf-8")
    except OSError:
        return f"{BOARD} does not exist"
    if recorded != canonical:
        writer = Path("scripts") / "self_proof_scoreboard.py"
        return f"the record differs from a re-derivation; run {writer.as_posix()} --write"
    return None


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def executable_digest(path):
    result = hashlib.sha256()
    with path.open("rb") as binary:
        for chunk in iter(lambda: binary.read(1024 * 1024), b""):
            result.update(chunk)
    return result.hexdigest()


@dataclass(frozen=True)
class PinnedBuild:
    executable: Path
    receipt_path: Path
    raw_receipt: bytes
    receipt: dict

    def require_inputs(self, inputs):
        if self.receipt != {"schema": BUILD_SCHEMA, "version": self.receipt["version"], **inputs}:
            raise W0BuildError("native W0 build receipt does not match the executable and pinned inputs")

    def receipt_unchanged(self):
        return self.receipt_path.read_bytes() == self.raw_receipt

    def require_version(self, cwd, runner):
        wanted = (self.receipt["version"] + "\n").encode("utf-8")
        require_output(runner([str(self.executable), "--version"], cwd), "version", wanted)


def read_pinned_build(build, *, expected_commit=None):
    executable_path, receipt_path, receipt_sha256 = build
    executable = Path(executable_path).resolve(strict=True)
    receipt_path = Path(receipt_path)
    if not executable.is_file() or not receipt_path.is_file():
        raise W0BuildError("native W0 executable and build receipt must be regular files")
    raw = receipt_path.read_bytes()
    if digest(raw) != receipt_sha256:
        raise W0BuildError("native W0 build receipt differs from its supplied SHA-256")
    try:
        receipt = json.loads(raw, object_pairs_hook=once, parse_constant=no_number)
    except (ValueError, Refused) as err:
        raise W0BuildError(f"invalid native W0 build receipt ({err})") from err
    commit = expected_commit
    if commit is None and isinstance(receipt, dict):
        commit = receipt.get("source_commit")
    version = receipt.get("version") if isinstance(receipt, dict) else None
    if (not isinstance(commit, str) or not OBJECT_ID.fullmatch(commit)
            or not isinstance(version, str) or not re.fullmatch(rf"clean [^\s+]+\+g{commit}", version)):
        raise W0BuildError("native W0 build receipt version must name the exact Clean commit")
    return PinnedBuild(executable, receipt_path, raw, receipt)


def run_candidate(argv, cwd):
    try:
        return subprocess.run(argv, cwd=cwd, stdin=subprocess.DEVNULL, capture_output=True, timeout=60)
    except subprocess.TimeoutExpired as err:
        raise W0BuildError("native W0 comparison timed out") from err


def require_output(actual, label, expected=None):
    if actual.returncode or actual.stderr or not actual.stdout or (expected is not None and actual.stdout != expected):
        diagnostic = actual.stderr.decode("utf-8", errors="replace").strip()
        raise W0BuildError(f"native W0 {label} did not match (exit {actual.returncode}, stderr {diagnostic!r})")
    return actual.stdout


def _read_git(root, *args):
    env = {key: value for key, value in os.environ.items() if not key.upper().startswith("GIT_")}
    env.update(GIT_NO_LAZY_FETCH="1", GIT_ALLOW_PROTOCOL="", GIT_TERMINAL_PROMPT="0", GIT_OPTIONAL_LOCKS="0")
    try:
        git = subprocess.run(
            ["git", "--no-replace-objects", *args], cwd=root, env=env,
            stdin=subprocess.DEVNULL, capture_output=True, timeout=15,
        )
    except subprocess.TimeoutExpired as err:
        raise W0BuildError("native W0 build source lookup timed out") from err
    if git.returncode or git.stderr:
        diagnostic = git.stderr.decode("utf-8", errors="replace").strip()
        raise W0BuildError(f"native W0 build source lookup failed ({diagnostic or git.returncode})")
    return git.stdout


def _git_source_inputs(root, commit):
    if _read_git(root, "rev-parse", "--is-inside-work-tree", "--show-prefix") != b"true\n\n":
        raise W0BuildError("native W0 build source must be read from the Git checkout root")
    if _read_git(root, "cat-file", "-t", commit) != b"commit\n":
        raise W0BuildError("native W0 build source is not a Git commit")
    tree = _read_git(root, "rev-parse", "--verify", f"{commit}^{{tree}}")
    if not re.fullmatch(rb"[0-9a-f]{40}\n", tree):
        raise W0BuildError("native W0 build commit has no resolved tree")
    return {
        "source_commit": commit,
        "source_tree": tree[:-1].decode("ascii"),
        "board_sha256": digest(_read_git(root, "cat-file", "blob", f"{commit}:{BOARD}")),
        "coverage_sha256": digest(_read_git(root, "cat-file", "blob", f"{commit}:{COVERAGE}")),
    }


def _git_inputs(root, commit, executable):
    return {**_git_source_inputs(root, commit), "executable_sha256": executable_digest(executable)}


def _executable_stat(executable):
    info = executable.stat()
    return (info.st_dev, info.st_ino, info.st_size, info.st_mtime_ns, info.st_ctime_ns)


def _clean_w0_source(root, commit):
    head = _read_git(root, "rev-parse", "--verify", "HEAD^{commit}")
    if head != (commit + "\n").encode("ascii"):
        raise W0BuildError("W0 handoff source HEAD changed")
    flags = _read_git(root, "ls-files", "-v", "-z").split(b"\0")
    if any(entry[:1].islower() or entry.startswith(b"S ") for entry in flags):
        raise W0BuildError("W0 handoff requires checked-out tracked files without index shortcuts")
    if _read_git(root, "-c", "core.fsmonitor=false", "-c", "core.trustctime=true",
                 "status", "--porcelain=v1", "--untracked-files=no", "--ignore-submodules=none"):
        raise W0BuildError("W0 handoff source has dirty tracked files")
    inputs = _git_source_inputs(root, commit)
    for path, kind in ((BOARD, "board_sha256"), (COVERAGE, "coverage_sha256")):
        saved = root / path
        if saved.is_symlink() or not saved.is_file() or digest(saved.read_bytes()) != inputs[kind]:
            raise W0BuildError(f"W0 handoff {path} differs from its committed bytes")
    return inputs


def _handoff_inputs(root, commit, executable):
    return {**_clean_w0_source(root, commit), "executable_sha256": executable_digest(executable)}


def export_w0_build(source_checkout, executable, executable_sha256, output_parent, *,
                    expected_inputs=None, expected_version=None):
    """Retain an independently pinned qualified executable and the native Fleet receipt."""
    if not re.fullmatch(r"[0-9a-f]{64}", executable_sha256):
        raise W0BuildError("W0 handoff requires an independently recorded executable SHA-256")
    root = Path(source_checkout).resolve(strict=True)
    executable = Path(executable).resolve(strict=True)
    parent = Path(output_parent).resolve(strict=True)
    if not executable.is_file() or not os.access(executable, os.X_OK):
        raise W0BuildError("W0 handoff input must be an executable regular file")
    commit = _read_git(root, "rev-parse", "--verify", "HEAD^{commit}").decode("ascii").strip()
    if not OBJECT_ID.fullmatch(commit):
        raise W0BuildError("W0 handoff source must name a full Clean commit")
    identity = _executable_stat(executable)
    inputs = _handoff_inputs(root, commit, executable)
    if expected_inputs is not None and inputs != expected_inputs:
        raise W0BuildError("W0 gate result producing source or executable has changed")
    if inputs["executable_sha256"] != executable_sha256 or _executable_stat(executable) != identity:
        raise W0BuildError("W0 handoff executable differs from its supplied SHA-256")

    directory = Path(tempfile.mkdtemp(prefix="w0-build-", dir=parent))
    try:
        copy = directory / "clean"
        shutil.copyfile(executable, copy)
        copy.chmod(0o700)
        copy_identity = _executable_stat(copy)
        if executable_digest(copy) != executable_sha256:
            raise W0BuildError("W0 handoff executable changed during copying")
        version = require_output(run_candidate([str(copy), "--version"], root), "handoff version").decode("utf-8")
        if not re.fullmatch(rf"clean [^\s+]+\+g{commit}\n", version):
            raise W0BuildError("W0 handoff version must name the exact Clean commit")
        if expected_version is not None and version != expected_version + "\n":
            raise W0BuildError("W0 gate result executable version differs from the record")
        if copy.is_symlink() or _executable_stat(copy) != copy_identity:
            raise W0BuildError("W0 handoff copy changed during the version check")
        command = [str(copy), "evidence", "status", "--scoreboard", "--check", "--repo-root", str(root)]
        require_output(run_candidate(command, root), "handoff saved-board check",
                       b"SELF_PROOF_SCOREBOARD=ok the record matches its sources\n")
        if (_handoff_inputs(root, commit, executable) != inputs or _executable_stat(executable) != identity
                or copy.is_symlink() or _executable_stat(copy) != copy_identity
                or executable_digest(copy) != executable_sha256):
            raise W0BuildError("W0 handoff inputs changed during verification")
        raw = (json.dumps({"schema": BUILD_SCHEMA, "version": version[:-1], **inputs},
                          indent=2, sort_keys=True) + "\n").encode("utf-8")
        pin = digest(raw)
        (directory / "build-receipt.sha256").write_text(pin + "\n", encoding="ascii")
        staged = directory / ".receipt"
        staged.write_bytes(raw)
        receipt = directory / "build-receipt.json"
        os.link(staged, receipt)
        staged.unlink()
    except BaseException:
        shutil.rmtree(directory)
        raise
    return {"executable": str(copy), "receipt": str(receipt), "receipt_sha256": pin}


def run_pinned_w0_json(build, *, git_root, data_root) -> bytes:
    """Read W0 from the data root using the receipt's independently pinned build."""
    pinned = read_pinned_build(build)
    git_root = Path(git_root).resolve(strict=True)
    data_root = Path(data_root).resolve(strict=True)
    commit = pinned.receipt["source_commit"]
    executable_stat = _executable_stat(pinned.executable)
    inputs = _git_inputs(git_root, commit, pinned.executable)
    pinned.require_inputs(inputs)
    if _executable_stat(pinned.executable) != executable_stat or not pinned.receipt_unchanged():
        raise W0BuildError("native W0 build inputs changed before the version check")
    pinned.require_version(data_root, run_candidate)
    if _executable_stat(pinned.executable) != executable_stat or not pinned.receipt_unchanged():
        raise W0BuildError("native W0 build inputs changed during the version check")
    argv = [str(pinned.executable), "evidence", "status", "--scoreboard", "--json",
            "--repo-root", str(data_root)]
    stdout = require_output(run_candidate(argv, data_root), "JSON render")
    if (_executable_stat(pinned.executable) != executable_stat or not pinned.receipt_unchanged()
            or _git_inputs(git_root, commit, pinned.executable) != inputs):
        raise W0BuildError("native W0 build inputs changed during the comparison")
    return stdout



def _record_gate_build(runner, root, commit, scratch, version=None):
    root, scratch = Path(root), Path(scratch)
    path = root / os.environ["CLEAN_W0_GATE_RESULT"]
    path = path.parent.resolve(strict=True) / path.name
    source = {"source_checkout": str(root), **_clean_w0_source(root, commit)}
    inputs = scratch / "gate-source.json"
    helper = Path(__file__).resolve()
    scripts = Path("scripts")
    script_inputs = {
        "run_w0_scoreboard_gate.sh": Path(runner),
        helper.name: helper,
        "kcheck_coverage_export.py": helper.with_name("kcheck_coverage_export.py"),
        "cargo_test_nonvacuous.sh": root / scripts / "cargo_test_nonvacuous.sh",
    }
    qualification = {(scripts / name).as_posix(): executable_digest(file) for name, file in script_inputs.items()}
    preflight = {"destination": str(path), "source": source, "qualification_sha256": qualification}
    if version is None:
        if path.exists() or path.is_symlink():
            raise W0BuildError("W0 gate result destination already exists")
        inputs.write_text(json.dumps(preflight), encoding="utf-8")
        return

    if preflight != json.loads(inputs.read_bytes()):
        raise W0BuildError("W0 gate result inputs or destination changed during qualification")
    artifact = json.loads((scratch / "gate-artifact.json").read_bytes())
    executable = Path(artifact["executable"])
    image_sha = artifact["cargo_artifact"]["trust_executable_sha256"]
    if executable_digest(executable) != image_sha:
        raise W0BuildError("W0 gate result executable changed after qualification")
    record = {"schema": "clean.w0_gate_result.v1", **source, **artifact, "version": version,
              "executable_sha256": image_sha, "qualification_sha256": qualification,
              "cargo_log_sha256": executable_digest(scratch / "cargo.log")}
    with tempfile.NamedTemporaryFile(dir=path.parent, prefix=".w0-result-") as staged:
        staged.write((json.dumps(record, indent=2, sort_keys=True) + "\n").encode("utf-8"))
        staged.flush()
        os.fsync(staged.fileno())
        os.link(staged.name, path)


if __name__ == "__main__":
    try:
        _record_gate_build(*sys.argv[1:])
    except (OSError, ValueError, KeyError, TypeError) as error:
        sys.exit(f"W0_GATE_RESULT=invalid {error}")
