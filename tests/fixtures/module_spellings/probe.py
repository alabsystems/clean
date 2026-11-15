#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""Regenerate the module-system spelling verdicts from real Lean.

Plan item `formats-module-spelling-refusals`
(`docs/plans/LEAN4_UPSTREAM_DELTA_2026-10-16.md`). Every row of
`verdicts.tsv` and `modifier_matrix.tsv` is a whole `.lean` file that each
toolchain named on the command line elaborates on its own (`lean <file>`, no
Lake, no imports beyond the implicit `Init`). A row's verdict and messages are
what Lean printed; the script refuses to write a table when two toolchains
disagree on any row, so a committed row holds for every toolchain it names.

Usage (from the repository root):

    python3 -I tests/fixtures/module_spellings/probe.py            # rewrite both TSVs
    python3 -I tests/fixtures/module_spellings/probe.py --check    # compare, exit 1 on drift

`--toolchain DIR` (repeatable) replaces the default pair, the pinned
v4.30.0-rc2 and v4.33.1 under `~/.elan/toolchains`. Under aterm, `lean` on PATH
is Clean, so the script runs each toolchain's own `bin/lean` by absolute path,
with that `bin` first on PATH and `ATERM_NO_REROUTE=1`.
"""

from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
ELAN = Path.home() / ".elan" / "toolchains"
DEFAULT_TOOLCHAINS = [
    ELAN / "leanprover--lean4---v4.30.0-rc2",
    ELAN / "leanprover--lean4---v4.33.1",
]

# (id, module header?, spelling, body). The source is "module\n\n" + body when
# the header is present, else body.
CORE_ROWS = [
    ("public_import", False, "public import", "public import Init\n\ndef x : Nat := 1\n"),
    ("public_import", True, "public import", "public import Init\n\ndef x : Nat := 1\n"),
    ("meta_import", False, "meta import", "meta import Init\n\ndef x : Nat := 1\n"),
    ("meta_import", True, "meta import", "meta import Init\n\ndef x : Nat := 1\n"),
    ("import_all", False, "import all", "import all Init\n\ndef x : Nat := 1\n"),
    ("import_all", True, "import all", "import all Init\n\ndef x : Nat := 1\n"),
    ("public_meta_import", False, "public meta import", "public meta import Init\n\ndef x : Nat := 1\n"),
    ("public_meta_import", True, "public meta import", "public meta import Init\n\ndef x : Nat := 1\n"),
    ("public_import_all", True, "public import all", "public import all Init\n\ndef x : Nat := 1\n"),
    ("private_import", False, "private import", "private import Init\n\ndef x : Nat := 1\n"),
    ("private_import", True, "private import", "private import Init\n\ndef x : Nat := 1\n"),
    ("private_section", False, "private section", "private section\ndef x : Nat := 1\nend\n"),
    ("private_section", True, "private section", "private section\ndef x : Nat := 1\nend\n"),
    ("public_variable", False, "public variable", "public variable (n : Nat)\ndef x : Nat := n\n"),
    ("public_variable", True, "public variable", "public variable (n : Nat)\ndef x : Nat := n\n"),
    ("private_variable", False, "private variable", "private variable (n : Nat)\ndef x : Nat := n\n"),
    ("private_variable", True, "private variable", "private variable (n : Nat)\ndef x : Nat := n\n"),
    ("public_section", False, "public section", "public section\ndef x : Nat := 1\nend\n"),
    ("expose_public_section", False, "@[expose] public section", "@[expose] public section\ndef x : Nat := 1\nend\n"),
    ("public_def", False, "public def", "public def x : Nat := 1\n"),
    ("meta_def", False, "meta def", "meta def x : Nat := 1\n"),
]

# Rows written whole: a comment before or inside the header. Pinned Lean's
# whitespace skips `--` and `/- ... -/` but not `/-- ... -/` (a declaration doc
# comment) or `/-! ... -/` (a module doc, itself a command), so either one ends
# the header. The `module` column says whether Lean reads a `module` header.
WHOLE_ROWS = [
    ("moddoc_public_import", True, "/-! doc -/ before public import",
     "module\n\n/-! doc -/\n\npublic import Init\n\ndef x : Nat := 1\n"),
    ("moddoc_meta_import", True, "/-! doc -/ before meta import",
     "module\n\npublic import Init\n/-! doc -/\nmeta import Init\n"),
    ("moddoc_module", False, "/-! doc -/ before module",
     "/-! doc -/\nmodule\n\npublic import Init\n"),
    ("doc_public_import", True, "/-- doc -/ before public import",
     "module\n\n/-- d -/\npublic import Init\n"),
    ("doc_module", False, "/-- doc -/ before module",
     "/-- d -/\nmodule\n\npublic import Init\n"),
    ("doc_import", True, "/-- doc -/ before import", "module\n\n/-- d -/\nimport Init\n"),
    ("doc_import", False, "/-- doc -/ before import", "/-- d -/\nimport Init\n"),
    ("imports_then_moddoc", True, "/-! doc -/ after the imports",
     "module\n\npublic import Init\n\n/-! doc -/\n\ndef x : Nat := 1\n"),
    ("comments_in_header", True, "-- and /- -/ in the header",
     "/- c -/\nmodule\n/- c -/\npublic import Init\n-- c\nmeta import Init\n\ndef x : Nat := 1\n"),
    ("doc_def", True, "/-- doc -/ before public def",
     "module\n\npublic import Init\n\n/-- d -/\npublic def x : Nat := 1\n"),
]

# Every modifier prefix probed in front of the three commands the module
# system's spellings decide. Each source is "def y : Nat := 1\n<prefix> <command>\n",
# so the prefix stands in command position after a command, outside the header.
MATRIX_PREFIXES = [
    "private", "public", "protected", "meta", "noncomputable", "unsafe", "partial",
    "@[simp]", "@[expose]", "@[expose] public", "@[expose] private", "@[simp] private",
    "@[simp] public", "public noncomputable", "public meta", "private noncomputable",
    "private protected", "public protected", "protected noncomputable",
    "noncomputable unsafe", "unsafe partial", "@[expose] noncomputable",
    "@[expose] public noncomputable meta", "private unsafe", "public unsafe",
    "private partial", "scoped", "local", "@[simp] scoped", "private scoped",
    "@[simp] local", "noncomputable scoped", "scoped noncomputable",
    "noncomputable private", "meta public", "unsafe private", "@[expose] @[simp]",
    "@[simp] @[expose]", "@[expose, simp]", "private meta",
    "public protected noncomputable unsafe partial", "meta noncomputable",
    "protected protected",
    # A declaration doc comment is the first slot of `declModifiers`, and of
    # the `syntax`-family, simproc and doc-only command parsers; `sectionHeader`
    # has none.
    "/-- d -/", "/-- d -/ private", "/-- d -/ public", "/-- d -/ protected",
    "/-- d -/ noncomputable", "/-- d -/ unsafe", "/-- d -/ @[simp]", "/-- d -/ @[expose]",
    "/-- d -/ @[expose] public", "/-- d -/ scoped", "/-- d -/ local",
    "/-- d -/ @[simp] scoped", "/-- d -/ private scoped",
]
MATRIX_COMMANDS = [
    ("import", "import Init"),
    ("section", "section\nend"),
    ("variable", "variable (n : Nat)"),
]

CORE_HEADER = "id\tmodule\tspelling\tsource\tlean_verdict\tlean_messages\tlean_toolchains"
MATRIX_HEADER = "id\tprefix\tcommand\tsource\tlean_verdict\tlean_messages\tlean_toolchains"


def core_sources():
    for ident, module, spelling, body in CORE_ROWS:
        row_id = f"{ident}_{'mod' if module else 'nomod'}"
        source = ("module\n\n" + body) if module else body
        yield row_id, ("yes" if module else "no"), spelling, source
    for ident, module, spelling, source in WHOLE_ROWS:
        row_id = f"{ident}_{'mod' if module else 'nomod'}"
        yield row_id, ("yes" if module else "no"), spelling, source


def matrix_sources():
    n = 0
    for prefix in MATRIX_PREFIXES:
        for command, body in MATRIX_COMMANDS:
            n += 1
            yield f"m{n:03d}", prefix, command, f"def y : Nat := 1\n{prefix} {body}\n"


def escape(source: str) -> str:
    if "\t" in source or "\\" in source:
        raise ValueError(f"source holds a tab or backslash: {source!r}")
    return source.replace("\n", "\\n")


def run_lean(toolchain: Path, workdir: Path, row_id: str, source: str):
    """Lean's verdict and its messages, each `line:col: error: text`."""
    path = workdir / f"{row_id}.lean"
    path.write_text(source, encoding="utf-8")
    env = dict(os.environ)
    env["PATH"] = f"{toolchain / 'bin'}{os.pathsep}{env.get('PATH', '')}"
    env["ATERM_NO_REROUTE"] = "1"
    proc = subprocess.run(
        [str(toolchain / "bin" / "lean"), path.name],
        cwd=workdir,
        env=env,
        capture_output=True,
        text=True,
        check=False,
    )
    out = (proc.stdout + proc.stderr).splitlines()
    prefix = f"{row_id}.lean:"
    messages = []
    for line in out:
        if not line.startswith(prefix):
            raise RuntimeError(f"{toolchain.name} {row_id}: unexpected output line {line!r}")
        messages.append(line[len(prefix):])
    if any(" | " in m for m in messages):
        raise RuntimeError(f"{row_id}: a message holds the field separator")
    if proc.returncode == 0 and not messages:
        return "accept", []
    if proc.returncode == 1 and messages and all(re.match(r"\d+:\d+: error: ", m) for m in messages):
        return "refuse", messages
    raise RuntimeError(f"{toolchain.name} {row_id}: exit {proc.returncode} with {messages!r}")


def version_line(toolchain: Path) -> str:
    env = dict(os.environ)
    env["ATERM_NO_REROUTE"] = "1"
    proc = subprocess.run(
        [str(toolchain / "bin" / "lean"), "--version"],
        env=env, capture_output=True, text=True, check=True,
    )
    return proc.stdout.strip()


def release_of(version: str) -> str:
    """`v4.30.0-rc2` from `Lean (version 4.30.0-rc2, arm64-..., commit ..., Release)`."""
    match = re.match(r"Lean \(version ([^,\s]+),", version)
    if not match:
        raise RuntimeError(f"unrecognised `lean --version` line {version!r}")
    return "v" + match.group(1)


def measure(toolchains, releases, rows):
    """rows: iterable of (row_id, fields..., source). Returns TSV body lines;
    the last column names every toolchain that printed the row."""
    lines = []
    with tempfile.TemporaryDirectory(prefix="module_spellings_") as tmp:
        workdir = Path(tmp)
        for row in rows:
            row_id, *fields, source = row
            verdicts = {tc.name: run_lean(tc, workdir, row_id, source) for tc in toolchains}
            distinct = {(v, tuple(m)) for v, m in verdicts.values()}
            if len(distinct) != 1:
                raise RuntimeError(f"{row_id}: toolchains disagree: {verdicts!r}")
            verdict, messages = next(iter(verdicts.values()))
            lines.append(
                "\t".join(
                    [row_id, *fields, escape(source), verdict, " | ".join(messages), ",".join(releases)]
                )
            )
    return lines


def render(header: str, versions, body) -> str:
    comment = [
        "# Generated by tests/fixtures/module_spellings/probe.py; never edit by hand.",
        "# Plan item formats-module-spelling-refusals. Every toolchain below printed exactly",
        "# these verdicts and messages (message: line:col: error: text, ' | '-joined);",
        "# lean_toolchains names them on each row.",
    ]
    comment += [f"# {v}" for v in versions]
    return "\n".join(comment + [header] + body) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--toolchain", action="append", type=Path)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    toolchains = args.toolchain or DEFAULT_TOOLCHAINS
    for tc in toolchains:
        if not (tc / "bin" / "lean").is_file():
            print(f"probe: no lean under {tc}", file=sys.stderr)
            return 2
    versions = [version_line(tc) for tc in toolchains]
    releases = [release_of(v) for v in versions]
    outputs = {
        HERE / "verdicts.tsv": render(
            CORE_HEADER, versions, measure(toolchains, releases, core_sources())
        ),
        HERE / "modifier_matrix.tsv": render(
            MATRIX_HEADER, versions, measure(toolchains, releases, matrix_sources())
        ),
    }
    drift = False
    for path, text in outputs.items():
        if args.check:
            if not path.is_file() or path.read_text(encoding="utf-8") != text:
                print(f"probe: {path.name} differs from what Lean prints", file=sys.stderr)
                drift = True
        else:
            path.write_text(text, encoding="utf-8")
            print(f"probe: wrote {path.name} ({text.count(chr(10)) - 5 - len(versions)} rows)")
    return 1 if drift else 0


if __name__ == "__main__":
    sys.exit(main())
