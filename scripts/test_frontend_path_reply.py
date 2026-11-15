#!/usr/bin/env python3
"""The frontend's newline frames a pathname; its whitespace belongs to the file.

These controls execute shell stubs through the real selectors. They make no
compiler, resource-authority, kernel-control or proof claim.
"""
from __future__ import annotations

import contextlib
import io
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest import mock

import check_gate_registry as registry
import check_lint_coverage as coverage
import check_workspace_dependency_boundary as boundary
import dev_ir_aliases as aliases
import patched_kernel_control as control

ROOT = Path(__file__).resolve().parents[1]
SCRATCH = Path(tempfile.gettempdir()) / ".ubd"
SCRATCH.mkdir(exist_ok=True)
_STATE = tempfile.TemporaryDirectory(prefix="frontend-reply-state-", dir=SCRATCH)
with mock.patch.dict(os.environ, {
    "VERIFY_RUNNER_STATE_DIR": str(Path(_STATE.name) / "state"),
    "VERIFY_RUNNER_TARGET_DIR": str(Path(_STATE.name) / "target"),
    "VERIFY_RUNNER_JOURNAL_DIR": str(Path(_STATE.name) / "journal"),
}):
    import verify_runner as runner


class FrontendPathReply(unittest.TestCase):
    def exercise(self, reader, suffix="", refusal=None, managed=False):
        with tempfile.TemporaryDirectory(prefix="frontend-reply-", dir=SCRATCH) as td:
            root = Path(td).resolve()
            frontend = root / "scripts/rust_frontend.sh"
            frontend.parent.mkdir()
            frontend.write_bytes((ROOT / "scripts/rust_frontend.sh").read_bytes())
            if refusal == "blank":
                frontend.write_text("#!/bin/sh\nprintf ' \\t\\n'\n")
            elif refusal == "error":
                frontend.write_text('#!/bin/sh\nprintf \'%s\\n\' "$TARGO"\nexit 19\n')
            frontend.chmod(0o700)
            selected = root / ("targo" + suffix)
            neighbor = root / "targo"
            if managed:
                selected = root / "toolchain\rpart/bin/targo"
                neighbor = root / "toolchain\npart/bin/targo"
            for path in {selected, neighbor}:
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(
                    '#!/bin/sh\nprintf \'%s\\n\' "$0" >> "$CLEAN_TEST_EXEC_LOG"\n'
                    'printf \'%s\\n\' \'{"packages":[]}\'\n'
                )
                path.chmod(0o700)
            log = root / "executed"
            shims = root / "shims"
            shims.mkdir()
            env = {
                "PATH": os.defpath,
                "TARGO": str(selected),
                "CLEAN_TEST_EXEC_LOG": str(log),
            }
            if managed:
                managed_bin = root / "managed-bin"
                managed_bin.mkdir()
                trustc = managed_bin / "trustc"
                trustc.write_text('#!/bin/sh\nprintf \'%s\\n\' "$SYSROOT"\n')
                trustc.chmod(0o700)
                env.pop("TARGO")
                env.update(ATPKG_BIN=str(managed_bin), SYSROOT=str(selected.parent.parent))
            with contextlib.ExitStack() as stack:
                stack.enter_context(mock.patch.dict(os.environ, env, clear=True))
                for module in (registry, coverage, boundary, control):
                    stack.enter_context(mock.patch.object(module, "ROOT", root))
                stack.enter_context(mock.patch.object(boundary, "FRONTEND", frontend))
                stack.enter_context(mock.patch.object(registry, "_TARGO_CACHE", []))
                stack.enter_context(mock.patch.object(runner, "REPO_ROOT", root))
                stack.enter_context(mock.patch("tempfile.gettempdir", return_value=str(shims)))
                stack.enter_context(mock.patch.object(aliases, "declared_aliases", return_value=True))
                stack.enter_context(mock.patch.object(aliases, "excluded_packages", return_value=set()))
                stack.enter_context(contextlib.redirect_stdout(io.StringIO()))
                stack.enter_context(contextlib.redirect_stderr(io.StringIO()))

                def invoke():
                    if reader == "boundary":
                        return boundary.resolve_targo()
                    if reader == "coverage":
                        return coverage.resolve_targo()
                    if reader == "control":
                        return control.resolve_targo()
                    if reader == "registry":
                        return registry._canonical_targo()
                    if reader == "aliases":
                        aliases.production_locks(root, {}, {"Cargo.lock": ""})
                        return None
                    runner._canonical_targo_first_on_path()
                    return None

                if refusal:
                    if reader in ("registry", "runner"):
                        self.assertIsNone(invoke())
                        self.assertEqual(os.environ["PATH"], env["PATH"])
                    else:
                        error = {
                            "boundary": boundary.BoundaryViolation,
                            "coverage": coverage.CoverageFailure,
                            "control": SystemExit,
                            "aliases": aliases.DevAliasError,
                        }[reader]
                        with self.assertRaises(error):
                            invoke()
                    self.assertFalse(log.exists(), "a refused selection executed a file")
                else:
                    path = invoke()
                    if reader not in ("aliases", "runner"):
                        subprocess.run([path, "--version"], check=True, capture_output=True)
                    elif reader == "runner":
                        subprocess.run(["targo", "--version"], check=True, capture_output=True)
                    # Only the shell framing LF separates trace records; Unicode
                    # line separators are valid filename bytes.
                    self.assertEqual(log.read_bytes(), os.fsencode(str(selected)) + b"\n")

    def check_reader(self, reader):
        for suffix in ("", " ", "\t", "\u00a0", "\u0085", "\u2028", "\u2029"):
            with self.subTest(reader=reader, suffix=repr(suffix)):
                self.exercise(reader, suffix)
        with self.subTest(reader=reader, managed_carriage_return=True):
            self.exercise(reader, managed=True)
        for refusal in ("blank", "error"):
            with self.subTest(reader=reader, refusal=refusal):
                self.exercise(reader, refusal=refusal)

    def test_boundary(self):
        self.check_reader("boundary")

    def test_coverage(self):
        self.check_reader("coverage")

    def test_control_launcher(self):
        self.check_reader("control")

    def test_registry(self):
        self.check_reader("registry")

    def test_dev_aliases(self):
        self.check_reader("aliases")

    def test_runner(self):
        self.check_reader("runner")


if __name__ == "__main__":
    unittest.main()
