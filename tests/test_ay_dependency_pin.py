# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0

from __future__ import annotations

import importlib.util
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "check_ay_updates.py"
SPEC = importlib.util.spec_from_file_location("clean_check_ay_updates", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
checker = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = checker
SPEC.loader.exec_module(checker)

TEST_REV = "0123456789abcdef0123456789abcdef01234567"
OTHER_REV = "89abcdef0123456789abcdef0123456789abcdef"


def write_fixture(
    root: Path,
    *,
    manifest_revisions: list[str] | None = None,
    lock_query_revision: str = TEST_REV,
    lock_resolved_revision: str = TEST_REV,
    lock_sources: int = checker.AY_LOCK_SOURCE_COUNT,
    lock_packages: list[str] | None = None,
) -> None:
    root.mkdir(parents=True, exist_ok=True)
    revisions = manifest_revisions or [TEST_REV] * len(checker.AY_MANIFEST_KEYS)
    manifest_lines = ["[workspace]", 'members = []', "", "[workspace.dependencies]"]
    for key, revision in zip(checker.AY_MANIFEST_KEYS, revisions, strict=True):
        manifest_lines.append(
            f'{key} = {{ package = "{key}", git = "{checker.AY_REPO_URL}", '
            f'rev = "{revision}" }}'
        )
    (root / "Cargo.toml").write_text("\n".join(manifest_lines) + "\n")

    lock_lines = ["version = 4", ""]
    packages = (lock_packages or list(checker.AY_LOCK_PACKAGE_NAMES))[:lock_sources]
    for name in packages:
        lock_lines.extend(
            [
                "[[package]]",
                f'name = "{name}"',
                'version = "0.0.0"',
                (
                    f'source = "git+{checker.AY_REPO_URL}'
                    f"?rev={lock_query_revision}#{lock_resolved_revision}\""
                ),
                "",
            ]
        )
    (root / "Cargo.lock").write_text("\n".join(lock_lines))


def test_reads_complete_committed_ay_graph_without_a_sibling(tmp_path: Path) -> None:
    repo_root = tmp_path / "clean"
    write_fixture(repo_root)

    evidence = checker.read_pin_evidence(repo_root)

    assert evidence.ay_dependency_rev == TEST_REV
    assert evidence.ay_lockfile_rev == TEST_REV
    assert evidence.ay_lockfile_commit == TEST_REV
    assert evidence.ay_manifest_pin_count == 7
    assert evidence.ay_lock_source_count == checker.AY_LOCK_SOURCE_COUNT
    assert not (tmp_path / "ay").exists()


def test_rejects_split_manifest_revisions(tmp_path: Path) -> None:
    revisions = [TEST_REV] * len(checker.AY_MANIFEST_KEYS)
    revisions[-1] = OTHER_REV
    write_fixture(tmp_path, manifest_revisions=revisions)

    with pytest.raises(checker.PinEvidenceError, match="do not share one revision"):
        checker.read_pin_evidence(tmp_path)


def test_rejects_non_ay_key_aliasing_an_ay_package(
    tmp_path: Path,
) -> None:
    write_fixture(tmp_path)
    manifest_path = tmp_path / "Cargo.toml"
    manifest_path.write_text(
        manifest_path.read_text()
        + 'legacy-solver = { package = "ay-sat", '
        'git = "https://example.invalid/solver.git", '
        f'rev = "{TEST_REV}" }}\n'
    )

    with pytest.raises(checker.PinEvidenceError, match="exactly the seven expected"):
        checker.read_pin_evidence(tmp_path)


def test_rejects_incomplete_lock_inventory(tmp_path: Path) -> None:
    write_fixture(tmp_path, lock_sources=checker.AY_LOCK_SOURCE_COUNT - 1)

    with pytest.raises(
        checker.PinEvidenceError,
        match=rf"exactly {checker.AY_LOCK_SOURCE_COUNT} AY Git sources",
    ):
        checker.read_pin_evidence(tmp_path)


def test_rejects_same_size_but_substituted_lock_inventory(tmp_path: Path) -> None:
    packages = list(checker.AY_LOCK_PACKAGE_NAMES)
    packages[-1] = "ay-unexpected"
    write_fixture(tmp_path, lock_packages=packages)

    with pytest.raises(checker.PinEvidenceError, match="must exactly match"):
        checker.read_pin_evidence(tmp_path)


def test_rejects_resolved_fragment_drift(tmp_path: Path) -> None:
    write_fixture(tmp_path, lock_resolved_revision=OTHER_REV)

    with pytest.raises(checker.PinEvidenceError, match="resolved revision"):
        checker.read_pin_evidence(tmp_path)


def test_remote_check_queries_only_authoritative_main(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    observed: dict[str, object] = {}

    def fake_run(command: list[str], **kwargs: object) -> object:
        observed["command"] = command
        observed["env"] = kwargs.get("env")
        return checker.subprocess.CompletedProcess(
            command,
            0,
            stdout=f"{TEST_REV}\t{checker.AY_MAIN_REF}\n",
            stderr="",
        )

    monkeypatch.setattr(checker.subprocess, "run", fake_run)

    assert (
        checker._get_remote_revision(checker.AY_REPO_URL, checker.AY_MAIN_REF)
        == TEST_REV
    )
    assert observed["command"] == [
        "git",
        "ls-remote",
        checker.AY_REPO_URL,
        checker.AY_MAIN_REF,
    ]
    assert isinstance(observed["env"], dict)
    assert observed["env"]["GIT_TERMINAL_PROMPT"] == "0"
