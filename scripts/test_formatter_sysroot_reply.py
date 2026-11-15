#!/usr/bin/env python3
"""Exercise formatter selection with real shell pathname replies, without Rust."""
from __future__ import annotations

import contextlib
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest import mock

import check_fmt_changed as fmt


class FormatterSysrootReply(unittest.TestCase):
    def exercise(self, suffix="", reply="path"):
        scratch = Path(tempfile.gettempdir()) / ".ubd"
        scratch.mkdir(exist_ok=True)
        with tempfile.TemporaryDirectory(prefix="formatter-reply-", dir=scratch) as td:
            root = Path(td).resolve()
            selected = root / ("toolchain" + suffix)
            neighbor = root / "toolchain"
            log = root / "executed"
            for sysroot in {selected, neighbor, root}:
                bindir = sysroot / "bin"
                bindir.mkdir(parents=True, exist_ok=True)
                tool = bindir / "trustfmt"
                tool.write_text('#!/bin/sh\nprintf \'%s\\n\' "$0" >> "$EXEC_LOG"\n')
                tool.chmod(0o700)
            tools = root / "tools"
            tools.mkdir()
            trustc = tools / "trustc"
            trustc.write_text(
                '#!/bin/sh\n[ "$1" = --print ] && [ "$2" = sysroot ] || exit 21\n'
                'case "$REPLY" in\n'
                'blank) printf \'\\n\';;\n'
                'error) printf \'%s\\n\' "$SYSROOT"; exit 19;;\n'
                'missing) printf \'%s\\n\' "$SYSROOT/missing";;\n'
                '*) printf \'%s\\n\' "$SYSROOT";;\nesac\n'
            )
            trustc.chmod(0o700)
            env = {"PATH": str(tools) + os.pathsep + os.defpath,
                   "SYSROOT": str(selected), "EXEC_LOG": str(log), "REPLY": reply}
            with mock.patch.dict(os.environ, env, clear=True), contextlib.chdir(root):
                if reply != "path":
                    with self.assertRaises(fmt.Refuse):
                        fmt.resolve_rustfmt()
                    self.assertFalse(log.exists())
                else:
                    tool = fmt.resolve_rustfmt()
                    subprocess.run([str(tool), "--version"], check=True)
                    self.assertEqual(log.read_bytes(), os.fsencode(str(selected / "bin/trustfmt")) + b"\n")

    def test_pathname_bytes(self):
        for suffix in ("", " ", "\t", "\u00a0", "\u0085", "\u2028", "\u2029", "\r", "\n"):
            with self.subTest(suffix=repr(suffix)):
                self.exercise(suffix)

    def test_blank_reply_cannot_select_cwd(self):
        self.exercise(reply="blank")

    def test_failed_lookup_or_missing_formatter_refuses(self):
        for reply in ("error", "missing"):
            with self.subTest(reply=reply):
                self.exercise(reply=reply)


if __name__ == "__main__":
    unittest.main()
