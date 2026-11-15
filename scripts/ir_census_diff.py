#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""Differential check: Clean's compiled-IR census against the pinned Lean's.

Two producers print the same line format for the same import closure:

* Clean:  ``clean olean ir-census --closure <roots> --search-path <p>... [--print-decl N]...
  [--print-module M]... [--print-attrs]``  (``crates/clean-olean/src/lean_ir/census.rs``)
* Lean:   ``lean IRCensusOracle.lean`` with ``IR_CENSUS_ROOTS`` / ``IR_CENSUS_PRINT`` /
  ``IR_CENSUS_PRINT_MODULES`` / ``IR_CENSUS_ATTRS``
  (``crates/clean-olean/tests/fixtures/lean/v4.30.0-rc2/oracle/IRCensusOracle.lean``)

Lines: ``MOD <module> k=v ...`` (one per module), ``TOTAL modules=N k=v ...``,
``DECL <module> <olean|ir> <name>`` ... ``ENDDECL`` blocks, and ``ATTR`` / ``DECLEXT`` /
``DECLSORRY`` lines.

FAIL-CLOSED. Exit 0 only when: both sides parse completely (an unknown line is an error), both
carry at least one ``MOD`` row and exactly one ``TOTAL``, the module sets are equal, every row is
equal, the ``TOTAL`` rows are equal, the ``DECL`` block headers are equal in order and every body
is equal modulo whitespace, every ``ATTR``/``DECLEXT``/``DECLSORRY`` line is equal in order, and
every ``--expect-decl`` name has at least one ``DECL`` block on the Lean side (so a spot check
cannot pass by printing nothing). Any other outcome exits 1 (a diff) or 2 (unusable input).

Modes::

    ir_census_diff.py diff CLEAN_OUT LEAN_OUT [--expect-decl NAME]...
    ir_census_diff.py run --clean-bin CLEAN --roots A,B --search-path P [--search-path P]...
                          [--print-decl N]... [--print-decl-file F] [--print-module M]...
                          [--print-all] [--attrs]
                          --out-dir DIR
    ir_census_diff.py selftest

``run`` executes both producers SEQUENTIALLY (each loads the whole closure), so wrap it in
``scripts/heavy_gate.sh run <weight> <label> -- python3 scripts/ir_census_diff.py run ...``.
The Lean side gets ``LEAN_PATH`` = the search paths (the toolchain's own ``lib/lean`` is found
through the binary's sysroot); the Clean side gets the same search paths followed by the pinned
toolchain's ``lib/lean``.
"""

from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
import tempfile
from dataclasses import dataclass, field
from pathlib import Path

if sys.version_info < (3, 11):  # pragma: no cover - interpreter guard
    sys.stderr.write("ir_census_diff.py needs Python >= 3.11\n")
    sys.exit(2)

REPO = Path(__file__).resolve().parent.parent
ORACLE = REPO / "crates/clean-olean/tests/fixtures/lean/v4.30.0-rc2/oracle/IRCensusOracle.lean"
PINNED_TOOLCHAIN = Path.home() / ".elan/toolchains/leanprover--lean4---v4.30.0-rc2"

ROW_KEYS = (
    "fdecl_olean",
    "extern_olean",
    "fdecl_ir",
    "extern_ir",
    "extern_attr",
    "implemented_by",
    "regular_init",
    "regular_init_ir",
    "builtin_init",
)
ROW_RE = re.compile(r"^MOD (\S+) " + " ".join(rf"{k}=(\d+)" for k in ROW_KEYS) + r"$")
TOTAL_RE = re.compile(r"^TOTAL modules=(\d+) " + " ".join(rf"{k}=(\d+)" for k in ROW_KEYS) + r"$")
DECL_RE = re.compile(r"^DECL (\S+) (olean|ir) (.+)$")
ATTR_PREFIXES = ("ATTR ", "DECLEXT ", "DECLSORRY ")


class InputError(Exception):
    """The output of one producer cannot be parsed: never a pass."""


@dataclass
class Census:
    rows: dict[str, tuple[int, ...]] = field(default_factory=dict)
    total: tuple[int, ...] | None = None
    decls: list[tuple[str, str]] = field(default_factory=list)  # (header, body)
    attrs: list[str] = field(default_factory=list)


def parse(text: str, side: str) -> Census:
    census = Census()
    lines = text.split("\n")
    if lines and lines[-1] == "":
        lines.pop()
    i = 0
    while i < len(lines):
        line = lines[i]
        if m := ROW_RE.match(line):
            if m.group(1) in census.rows:
                raise InputError(f"{side}: module {m.group(1)} has two MOD rows")
            if census.total is not None:
                raise InputError(f"{side}: MOD row after TOTAL: {line!r}")
            census.rows[m.group(1)] = tuple(int(g) for g in m.groups()[1:])
        elif m := TOTAL_RE.match(line):
            if census.total is not None:
                raise InputError(f"{side}: two TOTAL rows")
            census.total = tuple(int(g) for g in m.groups())
        elif DECL_RE.match(line):
            body = []
            i += 1
            while i < len(lines) and lines[i] != "ENDDECL":
                body.append(lines[i])
                i += 1
            if i == len(lines):
                raise InputError(f"{side}: unterminated block {line!r}")
            census.decls.append((line, "\n".join(body)))
        elif line.startswith(ATTR_PREFIXES):
            census.attrs.append(line)
        else:
            raise InputError(f"{side}: unrecognized line {i + 1}: {line!r}")
        i += 1
    if not census.rows:
        raise InputError(f"{side}: no MOD rows")
    if census.total is None:
        raise InputError(f"{side}: no TOTAL row (a refused census prints none)")
    if census.total[0] != len(census.rows):
        raise InputError(f"{side}: TOTAL says {census.total[0]} modules, {len(census.rows)} rows")
    return census


def squash(text: str) -> str:
    return " ".join(text.split())


def compare(clean: Census, lean: Census, expect_decls: list[str]) -> list[str]:
    diffs: list[str] = []
    only_clean = sorted(set(clean.rows) - set(lean.rows))
    only_lean = sorted(set(lean.rows) - set(clean.rows))
    for m in only_clean:
        diffs.append(f"module only in Clean: {m}")
    for m in only_lean:
        diffs.append(f"module only in Lean: {m}")
    for m in sorted(set(clean.rows) & set(lean.rows)):
        if clean.rows[m] != lean.rows[m]:
            fields = [
                f"{k}: clean {a} lean {b}"
                for k, a, b in zip(ROW_KEYS, clean.rows[m], lean.rows[m])
                if a != b
            ]
            diffs.append(f"row {m}: " + "; ".join(fields))
    if clean.total != lean.total:
        diffs.append(f"TOTAL: clean {clean.total} lean {lean.total}")
    clean_heads = [h for h, _ in clean.decls]
    lean_heads = [h for h, _ in lean.decls]
    if clean_heads != lean_heads:
        missing = sorted(set(lean_heads) - set(clean_heads))
        extra = sorted(set(clean_heads) - set(lean_heads))
        diffs.append(
            f"DECL headers differ ({len(clean_heads)} vs {len(lean_heads)}); "
            f"missing in Clean {missing[:5]}, extra in Clean {extra[:5]}"
        )
    else:
        for (head, cb), (_, lb) in zip(clean.decls, lean.decls):
            if squash(cb) != squash(lb):
                diffs.append(f"{head}: body differs\n--- clean ---\n{cb}\n--- lean ---\n{lb}")
    if clean.attrs != lean.attrs:
        cs, ls = set(clean.attrs), set(lean.attrs)
        diffs.append(
            f"ATTR/DECLEXT/DECLSORRY lines differ ({len(clean.attrs)} vs {len(lean.attrs)}); "
            f"only Clean {sorted(cs - ls)[:5]}, only Lean {sorted(ls - cs)[:5]}"
        )
    for name in expect_decls:
        if not any(h.split(" ", 3)[3] == name for h in lean_heads):
            diffs.append(f"--expect-decl {name}: the Lean side printed no DECL block for it")
    return diffs


def diff_files(clean_path: Path, lean_path: Path, expect_decls: list[str]) -> int:
    try:
        clean = parse(clean_path.read_text(encoding="utf-8"), "clean")
        lean = parse(lean_path.read_text(encoding="utf-8"), "lean")
    except (OSError, UnicodeDecodeError, InputError) as error:
        print(f"ir_census_diff: UNUSABLE INPUT: {error}", file=sys.stderr)
        return 2
    diffs = compare(clean, lean, expect_decls)
    exact = sum(1 for (_, a), (_, b) in zip(clean.decls, lean.decls) if a == b)
    print(
        f"ir_census_diff: {len(lean.rows)} module(s), {len(lean.decls)} DECL block(s) "
        f"({exact} byte-exact), {len(lean.attrs)} ATTR/DECLEXT/DECLSORRY line(s), "
        f"{len(diffs)} diff(s)"
    )
    for d in diffs[:50]:
        print(f"  DIFF {d}")
    if len(diffs) > 50:
        print(f"  ... {len(diffs) - 50} more")
    return 1 if diffs else 0


def run_both(args: argparse.Namespace) -> int:
    out = Path(args.out_dir)
    out.mkdir(parents=True, exist_ok=True)
    if args.print_all:
        args.print_module = [*args.print_module, "*"]
    if args.print_decl_file is not None:
        names = [n.strip() for n in args.print_decl_file.read_text(encoding="utf-8").splitlines()]
        args.print_decl = [*args.print_decl, *(n for n in names if n)]
    roots = [r for r in args.roots.split(",") if r]
    if not roots:
        print("ir_census_diff: --roots is empty", file=sys.stderr)
        return 2
    lean_bin = Path(args.lean) if args.lean else PINNED_TOOLCHAIN / "bin/lean"
    stdlib = lean_bin.parent.parent / "lib/lean"
    if not lean_bin.is_file() or not stdlib.is_dir():
        print(f"ir_census_diff: pinned Lean not found at {lean_bin}", file=sys.stderr)
        return 2
    template = ORACLE.read_text(encoding="utf-8")
    imports = "".join(f"\nimport {r}" for r in roots)
    if "import Lean\n" not in template:
        print("ir_census_diff: oracle template lost its `import Lean` line", file=sys.stderr)
        return 2
    with tempfile.TemporaryDirectory() as tmp:
        script = Path(tmp) / "IRCensusOracle.lean"
        script.write_text(template.replace("import Lean\n", f"import Lean{imports}\n", 1))
        env = dict(os.environ)
        env["LEAN_PATH"] = os.pathsep.join(args.search_path)
        env["IR_CENSUS_ROOTS"] = ",".join(roots)
        env["IR_CENSUS_PRINT"] = ",".join(args.print_decl)
        env["IR_CENSUS_PRINT_MODULES"] = ",".join(args.print_module)
        env["IR_CENSUS_ATTRS"] = "1" if args.attrs else ""
        # A file, not stdout: `#eval` buffers captured stdout and the buffer
        # grows by copying, which a full-closure rendering never survives.
        lean_out = out / "lean.out"
        lean_out.unlink(missing_ok=True)
        env["IR_CENSUS_OUT"] = str(lean_out)
        lean = subprocess.run([str(lean_bin), str(script)], env=env, capture_output=True, check=False)
    (out / "lean.stdout").write_bytes(lean.stdout)
    (out / "lean.err").write_bytes(lean.stderr)
    if lean.stdout.strip():
        print(f"ir_census_diff: Lean oracle printed to stdout; see {out / 'lean.stdout'}", file=sys.stderr)
        return 2
    if lean.returncode != 0 or not lean_out.is_file():
        print(f"ir_census_diff: Lean oracle exited {lean.returncode}; see {out / 'lean.err'}", file=sys.stderr)
        return 2
    cmd = [args.clean_bin, "olean", "ir-census", "--closure", *roots]
    for p in [*args.search_path, str(stdlib)]:
        cmd += ["--search-path", p]
    for n in args.print_decl:
        cmd += ["--print-decl", n]
    for m in args.print_module:
        cmd += ["--print-module", m]
    if args.attrs:
        cmd.append("--print-attrs")
    cmd += ["--jobs", str(args.jobs)]
    with open(out / "clean.out", "wb") as stdout, open(out / "clean.err", "wb") as stderr:
        clean = subprocess.run(cmd, stdout=stdout, stderr=stderr, check=False)
    if clean.returncode != 0:
        print(f"ir_census_diff: clean exited {clean.returncode}; see {out / 'clean.err'}", file=sys.stderr)
        return 2
    return diff_files(out / "clean.out", out / "lean.out", args.print_decl)


def selftest() -> int:
    row = "MOD A.B fdecl_olean=1 extern_olean=2 fdecl_ir=3 extern_ir=0 extern_attr=0 implemented_by=0 regular_init=0 regular_init_ir=0 builtin_init=0"
    total = "TOTAL modules=1 fdecl_olean=1 extern_olean=2 fdecl_ir=3 extern_ir=0 extern_attr=0 implemented_by=0 regular_init=0 regular_init_ir=0 builtin_init=0"
    block = "DECL A.B ir f\ndef f : obj :=\n  ret x_1\nENDDECL"
    base = f"{row}\n{total}\n{block}\nATTR A.B extern f opaque\n"
    cases = [
        ("identical", base, base, [], 0),
        ("whitespace-only DECL difference", base.replace("  ret", "    ret"), base, [], 0),
        ("count differs", base.replace("fdecl_ir=3", "fdecl_ir=4", 1), base, [], 1),
        ("body differs", base.replace("ret x_1", "ret x_2"), base, [], 1),
        ("attr differs", base.replace("opaque", "adhoc all"), base, [], 1),
        ("expect-decl present", base, base, ["f"], 0),
        ("expect-decl absent", base, base, ["g"], 1),
        ("missing TOTAL", base.replace(total + "\n", ""), base, [], 2),
        ("no rows", "", base, [], 2),
        ("unknown line", base + "garbage\n", base, [], 2),
        ("unterminated DECL", f"{row}\n{total}\nDECL A.B ir f\ndef f\n", base, [], 2),
        (
            "extra module",
            base.replace(row, row + "\n" + row.replace("A.B", "A.C")).replace("modules=1", "modules=2"),
            base,
            [],
            1,
        ),
    ]
    failed = 0
    with tempfile.TemporaryDirectory() as tmp:
        for name, clean_text, lean_text, expect, want in cases:
            c, l = Path(tmp) / "c", Path(tmp) / "l"
            c.write_text(clean_text)
            l.write_text(lean_text)
            got = diff_files(c, l, expect)
            status = "ok" if got == want else "FAIL"
            failed += got != want
            print(f"selftest {status}: {name} -> exit {got} (want {want})")
    print(f"selftest: {len(cases) - failed}/{len(cases)} passed")
    return 1 if failed else 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = parser.add_subparsers(dest="mode", required=True)
    d = sub.add_parser("diff")
    d.add_argument("clean_out", type=Path)
    d.add_argument("lean_out", type=Path)
    d.add_argument("--expect-decl", action="append", default=[])
    r = sub.add_parser("run")
    r.add_argument("--clean-bin", required=True)
    r.add_argument("--lean", default=None)
    r.add_argument("--roots", required=True)
    r.add_argument("--search-path", action="append", required=True)
    r.add_argument("--print-decl", action="append", default=[])
    r.add_argument(
        "--print-decl-file",
        type=Path,
        default=None,
        help="file with one declaration name per line (added to --print-decl)",
    )
    r.add_argument("--print-module", action="append", default=[])
    r.add_argument(
        "--print-all",
        action="store_true",
        help="render every declaration of the closure (--print-module '*' on both sides)",
    )
    r.add_argument("--attrs", action="store_true")
    r.add_argument("--jobs", type=int, default=4)
    r.add_argument("--out-dir", required=True)
    sub.add_parser("selftest")
    args = parser.parse_args()
    if args.mode == "diff":
        return diff_files(args.clean_out, args.lean_out, args.expect_decl)
    if args.mode == "run":
        return run_both(args)
    return selftest()


if __name__ == "__main__":
    sys.exit(main())
