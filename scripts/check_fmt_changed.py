#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0

"""Refuse a push that carries an unformatted Rust file THE PUSH ITSELF touched.

WHY THIS EXISTS
---------------
`gate::fmt` (`cargo fmt --all --check`, suite row) went RED, was fixed, and went
RED again -- three times. Every instance was found HOURS later by whichever lane
swept the suite next, and the fixer was never the author. The most recent one is
the shape of all of them: 45b313095 landed
`crates/clean-elab/tests/r5_measure_spelling_routing_e2e.rs` with one
two-line-instead-of-one-line `expect_err`, merged as f21d6336b, and the suite
row caught it a day later.

Nothing ran fmt at landing time, and nothing could: `fmt --all --check` is 26.4 s
warm on this machine (measured 2026-08-25 at f21d6336b, four other lanes in
flight), and the pre-push hook's entire budget is about 6 s. So the hook did the
only thing available to it -- nothing -- and the suite row became the first
reader of every fmt mistake.

This leg closes that. It checks the files THE PUSH TOUCHES, not the workspace:
measured 0.073 s for the 11 .rs files of 503ef4d76, 0.204 s for the 4 of the
commit that actually broke the gate, and 0.70 s for the 20 largest .rs files in
the tree (8.2 MB) taken together. That is a gate that fits in a hook.

WHY `--skip-children` IS LOAD-BEARING, NOT A TUNING FLAG
--------------------------------------------------------
rustfmt follows `mod` declarations. Handed `spec/core_spec/mod.rs` it formats
every module below it, so the same 11-file commit costs 5.70 s instead of 0.073 s
-- and, far worse, it reports diffs in files the push never touched, which is
precisely the blame the recurrence is about. `--skip-children` (an unstable
option, hence `--unstable-features`) confines each check to the file named.

THE FALSE-POSITIVE CLASS, MEASURED AND ELIMINATED BY MECHANISM
--------------------------------------------------------------
A changed-files rustfmt check is NOT the same predicate as `cargo fmt --all
--check`, and the difference is not small. Measured 2026-08-25 over all 6,940
tracked .rs files: rustfmt-per-file reports 21 dirty files; `cargo fmt --all
--check` on the same tree reports ZERO. All 21 are files cargo fmt structurally
cannot reach, in exactly two mechanical classes:

  * 13 live outside `crates/` -- `crown-proofs/` (5), `scripts/` (6),
    `realtelem-harness/` (1), top-level `tests/` (1). Not workspace members, so
    `--all` never selects them.
  * 8 live inside `crates/` but are spliced in with `include!("...")`, which
    rustfmt has never followed: three `boolean_analysis_*_consts.rs` under
    clean-kernel, four `graduate/tests/*.rs` and one
    `lean4/olean/axiom_profile_tests.rs` under clean-mathverse.

So this leg filters by those two mechanisms -- under `crates/`, and not an
`include!()` target -- rather than by a hand-written skip list that would rot.
Verified: the filter removes exactly those 21 and nothing else, leaving the
leg's verdict on the current tree equal to `cargo fmt --all --check`'s.

The 21 are a real pre-existing blind spot and this leg does not pretend to fix
it; reformatting them would be pure whitespace churn across two crates that
several lanes are actively editing. They are named in `--report-blindspot`.

WHAT THIS IS NOT
----------------
It is not a replacement for `gate::fmt`. It cannot see a file the push did not
touch, so a tree that was already dirty stays dirty until `--all` runs. It is a
LANDING-TIME check whose only claim is that what YOU push is formatted.

Usage:
    python3 scripts/check_fmt_changed.py                 # check (fail-closed)
    python3 scripts/check_fmt_changed.py --range A..B    # explicit range
    python3 scripts/check_fmt_changed.py --selftest      # mutation arms
    python3 scripts/check_fmt_changed.py --report-blindspot
"""

from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
ZERO = "0" * 40
INCLUDE_RE = re.compile(r'include!\s*\(\s*"([^"]+)"\s*\)')


class Refuse(Exception):
    """The leg cannot run, or the tree does not satisfy it."""


def _git(*args: str, cwd: Path | None = None) -> str:
    proc = subprocess.run(
        ["git", *args],
        cwd=str(cwd or ROOT),
        capture_output=True,
        text=True,
        check=False,
    )
    if proc.returncode != 0:
        raise Refuse(f"git {' '.join(args)} failed: {proc.stderr.strip()}")
    return proc.stdout


def _git_ok(*args: str, cwd: Path | None = None) -> bool:
    return (
        subprocess.run(
            ["git", *args],
            cwd=str(cwd or ROOT),
            capture_output=True,
            text=True,
            check=False,
        ).returncode
        == 0
    )


def resolve_rustfmt() -> Path:
    """The formatter belonging to the toolchain that is PINNED.

    Same reasoning as scripts/rust_frontend.sh: `rust-toolchain.toml` pins the
    `trust` channel, whose stage2 ships `trustfmt` rather than `rustfmt`, and a
    symlinked sysroot is refused by the Trust frontends -- so the path is
    resolved through `rustc --print sysroot` and canonicalised.

    Fail closed if no formatter is found. A leg that shrugs when its tool is
    missing is the `gate::srcelab` failure ("skipped:no-binary" recorded GREEN),
    and this repo has that mistake on the books already.
    """
    proc = subprocess.run(
        ["rustc", "--print", "sysroot"], capture_output=True, text=True, check=False
    )
    if proc.returncode != 0:
        raise Refuse(
            "`rustc --print sysroot` failed, so the pinned formatter cannot be located.\n"
            "  A format gate that cannot find its formatter must not report a pass."
        )
    bindir = Path(os.path.realpath(proc.stdout.strip())) / "bin"
    for name in ("rustfmt", "trustfmt"):
        cand = bindir / name
        if cand.is_file() and os.access(cand, os.X_OK):
            return cand
    raise Refuse(
        f"no rustfmt/trustfmt in {bindir}.\n"
        "  Install the component (`rustup component add rustfmt`) or fix the pin."
    )


def supports_skip_children(fmt: Path) -> bool:
    """Probe once; `--skip-children` is unstable and a stock stable rustfmt refuses it."""
    with tempfile.NamedTemporaryFile("w", suffix=".rs", delete=False) as fh:
        fh.write("fn a() {}\n")
        probe = fh.name
    try:
        rc = subprocess.run(
            [
                str(fmt),
                "--check",
                "--edition",
                "2021",
                "--unstable-features",
                "--skip-children",
                probe,
            ],
            capture_output=True,
            text=True,
            check=False,
        )
        return rc.returncode == 0 and "Unstable option" not in (rc.stdout + rc.stderr)
    finally:
        os.unlink(probe)


def push_ranges() -> list[tuple[str, str]]:
    """(base, tip) pairs for this push, from the hook, or the branch's own range."""
    raw = os.environ.get("CLEAN_PUSH_RANGES", "").strip()
    out: list[tuple[str, str]] = []
    if raw:
        for line in raw.splitlines():
            parts = line.split()
            if len(parts) != 2:
                continue
            remote_sha, local_sha = parts
            if local_sha == ZERO:
                continue  # a deletion has nothing to format
            out.append((base_for(remote_sha, local_sha), local_sha))
        return out
    return [(base_for(ZERO, "HEAD"), "HEAD")]


def base_for(remote_sha: str, local_sha: str) -> str:
    """What to diff against: the remote tip if we have it, else the origin fork point."""
    if remote_sha != ZERO and _git_ok("cat-file", "-e", f"{remote_sha}^{{commit}}"):
        return remote_sha
    for ref in ("origin/main", "main"):
        if _git_ok("rev-parse", "--verify", "--quiet", ref):
            try:
                return _git("merge-base", ref, local_sha).strip()
            except Refuse:
                continue
    raise Refuse(
        "cannot determine what this push adds: no reachable remote sha and no\n"
        "  origin/main to fork from. Fetch first (`git fetch origin`) -- a format\n"
        "  gate with no baseline would be checking nothing and calling it a pass."
    )


def changed_rs(ranges: list[tuple[str, str]], include_worktree: bool) -> list[str]:
    files: set[str] = set()
    for base, tip in ranges:
        out = _git("diff", "--name-only", "--diff-filter=d", base, tip, "--", "*.rs")
        files.update(p for p in out.splitlines() if p.strip())
    if include_worktree:
        for args in (
            ("diff", "--name-only", "--diff-filter=d", "--", "*.rs"),
            ("diff", "--name-only", "--diff-filter=d", "--cached", "--", "*.rs"),
        ):
            files.update(p for p in _git(*args).splitlines() if p.strip())
    return sorted(files)


def include_targets() -> set[str]:
    """Basenames rustfmt will never reach because something `include!()`s them."""
    proc = subprocess.run(
        ["git", "grep", "-h", "-o", "-E", r'include!\s*\(\s*"[^"]+"\s*\)', "--", "*.rs"],
        cwd=str(ROOT),
        capture_output=True,
        text=True,
        check=False,
    )
    if proc.returncode not in (0, 1):  # 1 == no matches, which is fine
        raise Refuse(f"scanning for include!() targets failed: {proc.stderr.strip()}")
    return {
        Path(m.group(1)).name
        for m in (INCLUDE_RE.search(ln) for ln in proc.stdout.splitlines())
        if m
    }


def reachable(paths: list[str], includes: set[str]) -> tuple[list[str], list[str]]:
    """Split into (files cargo fmt --all would format, files it structurally cannot)."""
    keep, skip = [], []
    for p in paths:
        if not p.startswith("crates/") or Path(p).name in includes:
            skip.append(p)
        else:
            keep.append(p)
    return keep, skip


def run_fmt(fmt: Path, files: list[str], skip_children: bool, cwd: Path) -> tuple[int, str]:
    if not files:
        return 0, ""
    cmd = [str(fmt), "--check", "--edition", "2021"]
    if skip_children:
        cmd += ["--unstable-features", "--skip-children"]
    proc = subprocess.run(
        cmd + files, cwd=str(cwd), capture_output=True, text=True, check=False
    )
    return proc.returncode, proc.stdout + proc.stderr


def check(range_arg: str | None, include_worktree: bool) -> int:
    fmt = resolve_rustfmt()
    if range_arg:
        base, _, tip = range_arg.partition("..")
        ranges = [(base, tip or "HEAD")]
    else:
        ranges = push_ranges()

    files = changed_rs(ranges, include_worktree)
    if not files:
        print("  fmt-changed: no .rs files in this push")
        return 0

    keep, skip = reachable(files, include_targets())
    if not keep:
        print(f"  fmt-changed: {len(files)} .rs changed, none reachable by cargo fmt")
        return 0

    rc, out = run_fmt(fmt, keep, supports_skip_children(fmt), ROOT)
    if rc == 0:
        note = f" ({len(skip)} unreachable skipped)" if skip else ""
        print(f"  fmt-changed: {len(keep)} changed .rs file(s) formatted{note}")
        return 0

    dirty = sorted({
        ln.split("Diff in ", 1)[1].rsplit(":", 2)[0]
        for ln in out.splitlines()
        if ln.startswith("Diff in ")
    })
    print("RUSTFMT: this push carries unformatted Rust.", file=sys.stderr)
    for d in dirty:
        try:
            rel = Path(d).resolve().relative_to(ROOT)
        except ValueError:
            rel = Path(d)
        print(f"  {rel}", file=sys.stderr)
    print(
        "\nThese are files THIS push touches, so they are yours to format:\n"
        "    cargo fmt --all      (or: just fmt)\n"
        "then commit the result. Left alone this reddens the gate::fmt suite row\n"
        "hours from now, for whichever lane sweeps next.",
        file=sys.stderr,
    )
    return 1


def report_blindspot() -> int:
    """Name the files `cargo fmt --all --check` structurally cannot reach."""
    tracked = [p for p in _git("ls-files", "*.rs").splitlines() if p.strip()]
    _, skip = reachable(tracked, include_targets())
    print(f"{len(skip)} tracked .rs file(s) are outside `cargo fmt --all`'s reach:")
    for p in skip:
        why = "include!()-spliced" if p.startswith("crates/") else "outside crates/"
        print(f"  {p}  [{why}]")
    return 0


# --------------------------------------------------------------------- selftest
def _run(cmd: list[str], cwd: Path) -> subprocess.CompletedProcess:
    return subprocess.run(cmd, cwd=str(cwd), capture_output=True, text=True, check=False)


def selftest() -> int:
    """Mutation arms on a synthetic repo. A ratchet that cannot fail proves nothing."""
    fmt = resolve_rustfmt()
    skipc = supports_skip_children(fmt)
    arms: list[tuple[str, bool]] = []

    def arm(name: str, ok: bool) -> None:
        arms.append((name, ok))

    with tempfile.TemporaryDirectory() as td:
        repo = Path(td) / "repo"
        (repo / "crates/demo/src").mkdir(parents=True)
        (repo / "other").mkdir(parents=True)
        _run(["git", "init", "-q", "-b", "main", "."], repo)
        _run(["git", "config", "user.email", "t@t"], repo)
        _run(["git", "config", "user.name", "t"], repo)
        clean = "fn a() -> u32 {\n    1\n}\n"
        (repo / "crates/demo/src/lib.rs").write_text(clean)
        _run(["git", "add", "-A"], repo)
        _run(["git", "commit", "-qm", "base"], repo)
        base = _run(["git", "rev-parse", "HEAD"], repo).stdout.strip()

        dirty = "fn a() -> u32 {\n        1\n}\n"

        # ARM 1 — an unformatted file inside crates/ must be CAUGHT.
        (repo / "crates/demo/src/lib.rs").write_text(dirty)
        _run(["git", "add", "-A"], repo)
        _run(["git", "commit", "-qm", "dirty"], repo)
        tip = _run(["git", "rev-parse", "HEAD"], repo).stdout.strip()
        rc, _ = run_fmt(fmt, ["crates/demo/src/lib.rs"], skipc, repo)
        arm("unformatted file in crates/ is caught", rc != 0)

        # ARM 2 — the same content formatted must PASS.
        (repo / "crates/demo/src/lib.rs").write_text(clean)
        rc, _ = run_fmt(fmt, ["crates/demo/src/lib.rs"], skipc, repo)
        arm("formatted file passes", rc == 0)

        # ARM 3 — the range really selects the changed file.
        out = _run(
            ["git", "diff", "--name-only", "--diff-filter=d", base, tip, "--", "*.rs"],
            repo,
        ).stdout.split()
        arm("range selects the changed .rs", out == ["crates/demo/src/lib.rs"])

        # ARM 4 — a file outside crates/ is filtered out (cargo fmt --all cannot see it).
        keep, skip = reachable(["other/loose.rs"], set())
        arm("file outside crates/ is skipped", keep == [] and skip == ["other/loose.rs"])

        # ARM 5 — an include!()-spliced file inside crates/ is filtered out.
        keep, skip = reachable(["crates/demo/src/gen_consts.rs"], {"gen_consts.rs"})
        arm("include!()-spliced file is skipped", keep == [] and len(skip) == 1)

        # ARM 6 — a normal file inside crates/ is NOT filtered out. Without this
        # arm, a filter that skipped everything would pass arms 4 and 5 and
        # silently gate nothing at all.
        keep, skip = reachable(["crates/demo/src/lib.rs"], {"gen_consts.rs"})
        arm("ordinary crates/ file survives the filter", keep == ["crates/demo/src/lib.rs"])

        # ARM 7 — include!() targets are actually harvested from source.
        (repo / "crates/demo/src/host.rs").write_text('include!("gen_consts.rs");\n')
        _run(["git", "add", "-A"], repo)
        _run(["git", "commit", "-qm", "inc"], repo)
        got = _run(
            ["git", "grep", "-h", "-o", "-E", r'include!\s*\(\s*"[^"]+"\s*\)', "--", "*.rs"],
            repo,
        ).stdout
        names = {Path(m.group(1)).name for m in INCLUDE_RE.finditer(got)}
        arm("include!() targets are harvested", names == {"gen_consts.rs"})

        # ARM 8 — --skip-children keeps a dirty CHILD from failing its clean parent.
        if skipc:
            (repo / "crates/demo/src/child.rs").write_text(dirty)
            (repo / "crates/demo/src/parent.rs").write_text("mod child;\n")
            rc, _ = run_fmt(fmt, ["crates/demo/src/parent.rs"], True, repo)
            arm("--skip-children does not blame an untouched child", rc == 0)
            rc, _ = run_fmt(fmt, ["crates/demo/src/parent.rs"], False, repo)
            arm("...and without it, the child WOULD be blamed", rc != 0)

    width = max(len(n) for n, _ in arms)
    for name, ok in arms:
        print(f"  {'ok  ' if ok else 'FAIL'} {name.ljust(width)}")
    bad = [n for n, ok in arms if not ok]
    if bad:
        print(f"\ncheck_fmt_changed selftest: {len(bad)} arm(s) failed", file=sys.stderr)
        return 1
    print(f"  check_fmt_changed selftest: {len(arms)}/{len(arms)} arms")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--range", help="explicit BASE..TIP instead of the push range")
    ap.add_argument(
        "--worktree",
        action="store_true",
        help="also check uncommitted .rs changes (for local_gate, not the hook)",
    )
    ap.add_argument("--selftest", action="store_true")
    ap.add_argument("--report-blindspot", action="store_true")
    args = ap.parse_args()
    try:
        if args.selftest:
            return selftest()
        if args.report_blindspot:
            return report_blindspot()
        return check(args.range, args.worktree)
    except Refuse as exc:
        print(f"check_fmt_changed: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
