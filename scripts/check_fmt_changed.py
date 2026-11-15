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

CURRENT REACHABILITY — 2026-11-13
--------------------------------
Changed-file mode keeps the crates/ scope and checks each selected file with
--skip-children, so untouched children are not blamed. Included files are not
exempt: the pinned Trust formatter now follows literal module-item includes,
and a basename exemption also hid unrelated ordinary modules of the same name.

--all delegates workspace/module traversal to the native Trust formatter,
using the targo beside the selected trustfmt and explicitly selecting that
formatter. Native warnings remain visible. --report-blindspot names paths
outside changed-file mode's crates/ scope; it is not a native coverage census.

Usage:
    python3 scripts/check_fmt_changed.py                 # check (fail-closed)
    python3 scripts/check_fmt_changed.py --range A..B    # explicit range
    python3 scripts/check_fmt_changed.py --selftest      # mutation arms
    python3 scripts/check_fmt_changed.py --report-blindspot
"""

from __future__ import annotations

import argparse
import os
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
ZERO = "0" * 40


class Refuse(Exception):
    """The leg cannot run, or the tree does not satisfy it."""


_GIT_LOCATION_VARS = frozenset({
    "GIT_DIR", "GIT_WORK_TREE", "GIT_INDEX_FILE", "GIT_COMMON_DIR",
    "GIT_OBJECT_DIRECTORY", "GIT_ALTERNATE_OBJECT_DIRECTORIES", "GIT_PREFIX",
})


def _bound_git_env(root: Path) -> dict[str, str]:
    """Ignore caller repository/index overrides and verify the worktree root."""
    env = {k: v for k, v in os.environ.items() if k not in _GIT_LOCATION_VARS}
    probe = subprocess.run(
        ["git", "rev-parse", "--show-toplevel"], cwd=str(root), env=env,
        capture_output=True, check=False,
    )
    if probe.returncode != 0:
        raise Refuse(f"cannot bind Git to {root}: {os.fsdecode(probe.stderr).strip()}")
    if not probe.stdout.endswith(b"\n") or not probe.stdout[:-1]:
        raise Refuse("Git did not report a framed worktree root")
    actual = Path(os.fsdecode(probe.stdout[:-1])).resolve()
    try:
        same_root = actual.samefile(root)
    except OSError as exc:
        raise Refuse(f"cannot compare Git worktree root {actual} with {root}: {exc}") from exc
    if not same_root:
        raise Refuse(f"Git worktree root {actual} differs from the required root {root}")
    return env


def _git(*args: str, cwd: Path | None = None) -> str:
    proc = subprocess.run(
        ["git", *args],
        cwd=str(cwd or ROOT),
        env=_bound_git_env(cwd or ROOT),
        capture_output=True,
        text=True,
        check=False,
    )
    if proc.returncode != 0:
        raise Refuse(f"git {' '.join(args)} failed: {proc.stderr.strip()}")
    return proc.stdout


def _git_paths(*args: str) -> list[str]:
    """Read literal Git paths without display quoting or newline translation."""
    proc = subprocess.run(
        ["git", args[0], "-z", *args[1:]], cwd=str(ROOT),
        env=_bound_git_env(ROOT), capture_output=True, check=False,
    )
    if proc.returncode != 0:
        raise Refuse(f"git {' '.join(args)} failed: {os.fsdecode(proc.stderr).strip()}")
    if proc.stdout and not proc.stdout.endswith(b"\0"):
        raise Refuse("Git path output is not NUL-terminated")
    return [os.fsdecode(p) for p in proc.stdout.split(b"\0")[:-1]]


def _git_ok(*args: str, cwd: Path | None = None) -> bool:
    return (
        subprocess.run(
            ["git", *args],
            cwd=str(cwd or ROOT),
            env=_bound_git_env(cwd or ROOT),
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
    resolved through `trustc --print sysroot` and canonicalised.

    Fail closed if no formatter is found. A leg that shrugs when its tool is
    missing is the `gate::srcelab` failure ("skipped:no-binary" recorded GREEN),
    and this repo has that mistake on the books already.
    """
    proc = subprocess.run(
        ["trustc", "--print", "sysroot"], capture_output=True, check=False
    )
    if proc.returncode != 0:
        raise Refuse(
            "`trustc --print sysroot` failed, so the pinned formatter cannot be located.\n"
            "  A format gate that cannot find its formatter must not report a pass."
        )
    # Preserve pathname bytes, including CR and Unicode line separators. Only
    # the final LF frames the sysroot reply; an empty path must not select cwd.
    sysroot = os.fsdecode(proc.stdout).removesuffix("\n")
    if not sysroot:
        raise Refuse("`trustc --print sysroot` returned no path")
    bindir = Path(os.path.realpath(sysroot)) / "bin"
    # Trust's formatter only: a stock `rustfmt` found here would be a different
    # formatter under the same gate name (owner directive 2026-09-28).
    cand = bindir / "trustfmt"
    if cand.is_file() and os.access(cand, os.X_OK):
        return cand
    raise Refuse(
        f"no trustfmt in {bindir}.\n"
        "  The Trust sysroot `trustc --print sysroot` names ships none; fix the toolchain."
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
        out = _git_paths("diff", "--name-only", "--diff-filter=d", base, tip, "--", "*.rs")
        files.update(out)
    if include_worktree:
        for args in (
            ("diff", "--name-only", "--diff-filter=d", "--", "*.rs"),
            ("diff", "--name-only", "--diff-filter=d", "--cached", "--", "*.rs"),
        ):
            files.update(_git_paths(*args))
    return sorted(files)


def reachable(paths: list[str]) -> tuple[list[str], list[str]]:
    """Split changed paths into the crates/ scope and paths outside it."""
    keep, skip = [], []
    for p in paths:
        if not p.startswith("crates/"):
            skip.append(p)
        else:
            keep.append(p)
    return keep, skip


def unparseable(out: str) -> list[str]:
    """Files rustfmt could not PARSE, as distinct from files it would reformat.

    `crates/clean-kernel/src/model_islands.rs` declares Trust's out-of-line
    island units, `#[path = "...clean"] clean mod <unit>;`. Whether that parses
    depends on WHICH formatter the pin resolves to, and both answers are live:
    a stock `rustfmt` does not implement the form and answers `expected one of
    `!` or `::`, found keyword `mod``, which is how this leg went RED on
    2026-09-14 for a push that had nothing unformatted in it -- with an EMPTY
    file list, because no `Diff in` line was ever emitted; whereas Trust's own
    `trustfmt`, which is what `resolve_rustfmt` returns on a box whose stage2
    ships no `rustfmt`, parses it and both the unit file and model_islands.rs
    come back rc=0 (measured 2026-09-15 at trustfmt 1.9.0-trust 58f0804260).
    So this function must keep working on a formatter that never sees the
    island form, and its selftest arm must not be keyed on that dialect --
    see ARM 3b. Asking a formatter to format a dialect it does not parse is
    not a formatting verdict, and reporting it as one is the defect. Same
    family as the `include!()`-spliced files above: a file this tool
    structurally cannot judge is skipped and NAMED, never silently counted
    either way.
    """
    hits = set()
    for ln in out.splitlines():
        stripped = ln.strip()
        if stripped.startswith("--> ") and ".rs:" in stripped:
            hits.add(stripped[4:].rsplit(":", 2)[0])
        marker = "cannot parse "
        if marker in ln:
            hits.add(ln.split(marker, 1)[1].strip())
    return sorted(hits)


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


def check_all() -> int:
    """Use the pinned formatter's own workspace and include traversal."""
    fmt = resolve_rustfmt()
    tracked = _git_paths("ls-files", "--", "*.rs")
    keep, _ = reachable(tracked)
    if not keep:
        print("RUSTFMT: no tracked .rs file is in the crates/ scope.", file=sys.stderr)
        return 1
    targo = fmt.parent / "targo"
    if targo.is_symlink() or not targo.is_file() or not os.access(targo, os.X_OK):
        raise Refuse(f"no executable regular targo beside the pinned formatter: {targo}")
    result = subprocess.run(
        [str(targo), "fmt", "--all", "--check"], cwd=str(ROOT),
        env={**_bound_git_env(ROOT), "RUSTFMT": str(fmt)}, capture_output=True, text=True, check=False,
    )
    if result.stdout:
        print(result.stdout, end="")
    if result.stderr:
        print(result.stderr, end="", file=sys.stderr)
    if result.returncode == 0:
        print("  fmt-all: native Trust workspace format check passed")
    return result.returncode


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

    keep, skip = reachable(files)
    if not keep:
        print(f"  fmt-changed: {len(files)} .rs changed, none in the crates/ scope")
        return 0

    return _judge(fmt, keep, skip, "fmt-changed")


def _judge(fmt: Path, keep: list[str], skip: list[str], label: str) -> int:
    """Judge changed files without following untouched children.

    Parse failures are named; an unexplained nonzero exit is a refusal.
    Whole-workspace mode delegates traversal to the native Trust command.
    """
    sc = supports_skip_children(fmt)
    rc, out = run_fmt(fmt, keep, sc, ROOT)

    # A file rustfmt cannot PARSE yields no `Diff in` line, so a naive read of a
    # non-zero exit reports "unformatted Rust" and names nothing. Drop those,
    # name them, and judge the rest -- refusing outright if that leaves nothing
    # to judge, because a leg that cannot run its tool must not report a pass.
    unparsed: list[str] = []
    if rc != 0 and not any(ln.startswith("Diff in ") for ln in out.splitlines()):
        bad = {os.path.realpath(f) for f in unparseable(out)}
        if bad:
            unparsed = sorted(
                str(Path(f).resolve().relative_to(ROOT)) if str(f).startswith(str(ROOT)) else str(f)
                for f in bad
            )
            keep = [f for f in keep if os.path.realpath(os.path.join(ROOT, f)) not in bad]
            if not keep:
                print(
                    "RUSTFMT: every .rs file in scope is one rustfmt cannot "
                    "parse:\n  " + "\n  ".join(unparsed),
                    file=sys.stderr,
                )
                return 1
            rc, out = run_fmt(fmt, keep, sc, ROOT)

    if rc == 0:
        bits = []
        if skip:
            bits.append(f"{len(skip)} outside crates/")
        if unparsed:
            bits.append(f"{len(unparsed)} unparseable by rustfmt ({', '.join(unparsed)})")
        note = f" ({'; '.join(bits)} skipped)" if bits else ""
        print(f"  {label}: {len(keep)} .rs file(s) formatted{note}")
        return 0

    dirty = sorted({
        ln.split("Diff in ", 1)[1].rsplit(":", 2)[0]
        for ln in out.splitlines()
        if ln.startswith("Diff in ")
    })
    if not dirty:
        print(
            "RUSTFMT: the formatter exited non-zero but reported no `Diff in` line and no "
            "file it could not parse, so this leg cannot say what is wrong. Refusing rather "
            "than guessing. Raw output follows.\n" + out.strip(),
            file=sys.stderr,
        )
        return 1
    print("RUSTFMT: this push carries unformatted Rust.", file=sys.stderr)
    for d in dirty:
        try:
            rel = Path(d).resolve().relative_to(ROOT)
        except ValueError:
            rel = Path(d)
        print(f"  {rel}", file=sys.stderr)
    print(
        "\nThese are files THIS push touches, so they are yours to format:\n"
        "    targo fmt --all      (or: just fmt)\n"
        "then commit the result. Left alone this reddens the gate::fmt suite row\n"
        "hours from now, for whichever lane sweeps next.",
        file=sys.stderr,
    )
    return 1


def report_blindspot() -> int:
    """Name tracked paths outside changed-file mode, not native --all coverage."""
    tracked = _git_paths("ls-files", "--", "*.rs")
    _, skip = reachable(tracked)
    print(f"{len(skip)} tracked .rs file(s) are outside changed-file mode's crates/ scope:")
    for p in skip:
        why = "outside crates/"
        print(f"  {p}  [{why}]")
    return 0


# --------------------------------------------------------------------- selftest
def _run(cmd: list[str], cwd: Path) -> subprocess.CompletedProcess:
    # A synthetic Git command must never follow the caller's repository,
    # index, templates or global hooks/configuration outside its scratch tree.
    env = {k: v for k, v in os.environ.items() if not k.startswith("GIT_")}
    env.update(GIT_CONFIG_GLOBAL=os.devnull, GIT_CONFIG_NOSYSTEM="1")
    return subprocess.run(cmd, cwd=str(cwd), env=env,
                          capture_output=True, text=True, check=False)


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

        # ARM 3b — a file rustfmt cannot PARSE is told apart from an unformatted
        # one. Both halves matter: the run must fail, and it must fail with NO
        # `Diff in` line, which is exactly what made the real red name zero
        # files.
        #
        # The input is a mismatched delimiter and NOT the island form that
        # motivated the rule, and that substitution is the point of this
        # comment. Whether a formatter can parse `clean mod unit;` is a property
        # of the DIALECT it implements, not of the code under test here.
        # Measured 2026-09-15 against the formatter this box actually resolves —
        # `trustfmt 1.9.0-trust (58f0804260 2026-08-28)`, the pinned stage2's —
        # the synthetic island file AND the real
        # crates/clean-kernel/src/model_islands.rs both come back rc=0 with
        # empty output: Trust's own rustfmt implements Trust's own front end. So
        # an arm keyed on the island form asserts `rc != 0` and measures ZERO,
        # which is how both halves of this arm arrived RED on a box where the
        # leg they guard is entirely correct. `fn a() { ( }` is refused by every
        # rustfmt-family parser, so the arm now measures unparseable() and the
        # no-`Diff in` property — which is what it was written to measure.
        (repo / "crates/demo/src/unparseable.rs").write_text("fn a() { ( }\n")
        rc, out = run_fmt(fmt, ["crates/demo/src/unparseable.rs"], skipc, repo)
        named = unparseable(out)
        arm(
            "a file rustfmt cannot parse fails with no `Diff in` line",
            rc != 0 and not any(ln.startswith("Diff in ") for ln in out.splitlines()),
        )
        arm(
            "...and `unparseable` names it, so the report is never an empty accusation",
            any(n.endswith("unparseable.rs") for n in named),
        )
        (repo / "crates/demo/src/unparseable.rs").unlink()

        # ARM 3c — the other direction, without which 3b is passed by an
        # `unparseable()` that names every file it is shown and by a leg that
        # calls every failure a parse error: an unformatted but PARSEABLE file
        # must produce a `Diff in` line and must be named by nobody.
        (repo / "crates/demo/src/lib.rs").write_text(dirty)
        rc, out = run_fmt(fmt, ["crates/demo/src/lib.rs"], skipc, repo)
        arm(
            "an unformatted-but-parseable file is a `Diff in`, never an unparseable",
            rc != 0
            and any(ln.startswith("Diff in ") for ln in out.splitlines())
            and unparseable(out) == [],
        )
        (repo / "crates/demo/src/lib.rs").write_text(clean)

        # ARM 4 — changed-file mode stays inside the crates/ scope.
        keep, skip = reachable(["other/loose.rs"])
        arm("file outside crates/ is skipped", keep == [] and skip == ["other/loose.rs"])

        # ARM 5 — an include!()-spliced file inside crates/ must still be checked.
        keep, skip = reachable(["crates/demo/src/gen_consts.rs"])
        arm("include!()-spliced file remains in scope", keep == ["crates/demo/src/gen_consts.rs"] and not skip)

        # ARM 6 — ordinary files stay selected alongside included fragments.
        keep, skip = reachable(["crates/demo/src/lib.rs"])
        arm("ordinary crates/ file survives the filter", keep == ["crates/demo/src/lib.rs"])

        # Establish a clean tracked baseline before changed-path controls.
        _run(["git", "add", "-A"], repo)
        _run(["git", "commit", "-qm", "fixture baseline"], repo)

        # ARM 8 — --skip-children keeps a dirty CHILD from failing its clean parent.
        if skipc:
            (repo / "crates/demo/src/child.rs").write_text(dirty)
            (repo / "crates/demo/src/parent.rs").write_text("mod child;\n")
            rc, _ = run_fmt(fmt, ["crates/demo/src/parent.rs"], True, repo)
            arm("--skip-children does not blame an untouched child", rc == 0)
            rc, _ = run_fmt(fmt, ["crates/demo/src/parent.rs"], False, repo)
            arm("...and without it, the child WOULD be blamed", rc != 0)

        # Git display quoting must not turn a reachable path into a skipped alias.
        from unittest.mock import patch
        names = [f"crates/demo/src/{name}.rs" for name in
                 ["space name", "λ", 'quote"name', "tab\tname", "line\nname", "cr\rname", "back\\name"]]
        for name in names:
            (repo / name).write_text(dirty)
        _run(["git", "add", "--", *names], repo)
        with patch.dict(globals(), ROOT=repo):
            selected = changed_rs([], True)
            arm("staged unusual paths retain their literal identity", selected == sorted(names))
            keep, skip = reachable(selected)
            arm("unusual paths inside crates stay reachable", keep == sorted(names) and not skip)
            _run(["git", "commit", "-qm", "unusual paths"], repo)
            unusual_tip = _git("rev-parse", "HEAD").strip()
            selected = changed_rs([(tip, unusual_tip)], False)
            arm("committed unusual paths survive Git quoting", set(names) <= set(selected))
            for name in names:
                (repo / name).write_text(clean)
            selected = changed_rs([], True)
            arm("unstaged unusual paths retain their literal identity", selected == sorted(names))
            arm("tracked unusual paths retain their literal identity",
                set(names) <= set(_git_paths("ls-files", "--", "*.rs")))
            rc, _ = run_fmt(fmt, names, skipc, repo)
            arm("formatted unusual paths pass the real formatter", rc == 0)
            for name in names:
                (repo / name).write_text(dirty)
            rc, _ = run_fmt(fmt, names, skipc, repo)
            arm("dirty unusual paths fail the real formatter", rc != 0)

        # The native formatter owns traversal, including literal item includes.
        collision = Path(td) / "collision"
        source = collision / "crates/demo/src"
        (source / "live").mkdir(parents=True)
        (source / "generated").mkdir()
        (collision / "Cargo.toml").write_text('[workspace]\nmembers = ["crates/demo"]\nresolver = "2"\n')
        (source.parent / "Cargo.toml").write_text(
            '[package]\nname = "fmt_collision"\nversion = "0.1.0"\nedition = "2021"\n')
        for rel, body in {
            "lib.rs": "mod host;\nmod live;\n",
            "host.rs": 'include!("generated/shared.rs");\n',
            "live.rs": '#[path = "live/shared.rs"]\nmod shared;\n',
            "live/shared.rs": dirty,
            "generated/shared.rs": clean,
        }.items():
            (source / rel).write_text(body)
        _run(["git", "init", "-q", "-b", "main", "."], collision)
        _run(["git", "add", "-f", "--", "Cargo.toml", "crates"], collision)
        with patch.dict(globals(), ROOT=collision):
            rc, _ = run_fmt(fmt, ["crates/demo/src/lib.rs"], False, collision)
            arm("formatter reaches the dirty ordinary same-basename module", rc != 0)
            arm("include exclusion cannot hide that ordinary module", check_all() == 1)
            (source / "live/shared.rs").write_text(clean)
            (source / "generated/shared.rs").write_text(dirty)
            rc, _ = run_fmt(fmt, ["crates/demo/src/lib.rs"], False, collision)
            arm("formatter reaches the actual included fragment", rc != 0)
            arm("gate catches the dirty included fragment", check_all() == 1)
            (source / "generated/shared.rs").write_text(clean)
            rc, _ = run_fmt(fmt, ["crates/demo/src/lib.rs"], False, collision)
            arm("formatter passes the clean include/module tree", rc == 0)
            arm("native all mode passes the clean workspace", check_all() == 0)

            alias = collision.with_name("COLLISION")
            if alias.exists() and alias.samefile(collision):
                accepted = False
                try:
                    _bound_git_env(alias)
                    accepted = True
                except Refuse:
                    pass
                arm("a case alias of the same worktree root is accepted", accepted)
            else:
                print("  skip case-alias control: filesystem distinguishes case")

            # Caller Git context must not hide staged content or redirect fixtures.
            _run(["git", "config", "user.name", "fixture"], collision)
            _run(["git", "config", "user.email", "fixture@example.invalid"], collision)
            _run(["git", "add", "-A"], collision)
            _run(["git", "-c", "core.hooksPath=/dev/null", "-c", "commit.gpgsign=false",
                  "commit", "-qm", "clean baseline"], collision)
            own_head = _git("rev-parse", "HEAD").strip()
            (source / "live/shared.rs").write_text(dirty)
            rel = "crates/demo/src/live/shared.rs"
            _run(["git", "add", "--", rel], collision)
            blank = Path(td) / "foreign-index"
            setup_env = {k: v for k, v in os.environ.items() if not k.startswith("GIT_")}
            subprocess.run(["git", "read-tree", "--empty"], cwd=collision,
                           env={**setup_env, "GIT_INDEX_FILE": str(blank)}, check=True)
            with patch.dict(os.environ, GIT_INDEX_FILE=str(blank)):
                arm("foreign index cannot hide staged paths", changed_rs([], True) == [rel])
                arm("foreign index cannot make dirty worktree checking green",
                    check("HEAD..HEAD", True) == 1)
            decoy = Path(td) / "decoy"
            decoy.mkdir()
            _run(["git", "init", "-q", "-b", "main"], decoy)
            with patch.dict(os.environ, GIT_DIR=str(decoy / ".git"), GIT_WORK_TREE=str(decoy)):
                arm("object probes stay in the explicit repository",
                    _git_ok("cat-file", "-e", own_head + "^{commit}"))
                _run(["git", "config", "--local", "format.fixture", "actual"], collision)
            arm("fixture writes stay in their explicit cwd",
                _run(["git", "config", "--local", "--get", "format.fixture"], collision).stdout.strip() == "actual"
                and _run(["git", "config", "--local", "--get", "format.fixture"], decoy).returncode == 1)
            _run(["git", "config", "--local", "core.worktree", str(decoy)], collision)
            try:
                refused = False
                try:
                    _git("rev-parse", "--show-toplevel")
                except Refuse:
                    refused = True
                arm("a foreign configured worktree root is refused", refused)
            finally:
                _run(["git", "config", "--local", "--unset", "core.worktree"], collision)

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
    ap.add_argument(
        "--all",
        action="store_true",
        help="run the native Trust workspace formatter with --all --check",
    )
    args = ap.parse_args()
    try:
        if args.selftest:
            return selftest()
        if args.report_blindspot:
            return report_blindspot()
        if args.all:
            return check_all()
        return check(args.range, args.worktree)
    except Refuse as exc:
        print(f"check_fmt_changed: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
