#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""Sorry-to-axiom dependency tracer + first-order proof-cost estimator.

Scans every `sorry`-bearing call-site in the clean kernel / verify crates and
maps each site to: containing Rust fn, best-effort Lean declaration name,
conjecture bucket (C001..CNNN inferred from filename or inline markers), and
a first-order proof-cost estimate.

Shapes recognised:
    * `sorry_inhabit_pi(&ty)` — canonical Opaque + @sorry.{0} idiom.
    * `Expr::const_(Name::from_string("sorry"), vec![Level::zero()])` — ad-hoc.

Cost: `max(1, axioms) * max(1, pi_sites)` with both factors pulled from
`data/axiom_audit.json.conjectures.<C>`. Ranking primitive only.

Usage:
    python3 scripts/sorry_to_axiom_tracer.py [--json|--report]

Re: #3423.
"""
from __future__ import annotations

import argparse
import json
import logging
import re
import sys
from dataclasses import dataclass, field, asdict
from pathlib import Path
from typing import Iterable, Optional

_LOG = logging.getLogger("sorry_to_axiom_tracer")

REPO_ROOT = Path(__file__).resolve().parent.parent
SCAN_ROOTS = (
    REPO_ROOT / "crates" / "clean-kernel" / "src" / "env",
    REPO_ROOT / "crates" / "clean-verify" / "src",
)
AXIOM_AUDIT_PATH = REPO_ROOT / "data" / "axiom_audit.json"
DEFAULT_REPORT_DIR = REPO_ROOT / "reports" / "audits"

# Files whose sorry mentions are semantic (helper, test scaffolding,
# explanatory comments about `@sorry`) rather than actual sorry holes.
SKIP_FILENAME_SUFFIXES = (
    "/sorry_summary.rs",
    "/build.rs",      # sorry/build.rs: helper module that *creates* sorry
    "/kind.rs",
    "/locations.rs",
    "/accounting.rs",
)

# Regex for the `sorry_inhabit_pi(&ty)` helper call (both forms: with `b.`
# and without). We match only call-sites, not the `use` / definition lines.
RE_SORRY_INHABIT_PI_CALL = re.compile(
    r"""(?<!fn\ )          # not the function definition
        \bsorry_inhabit_pi\s*\(
    """,
    re.VERBOSE,
)

# Regex for the ad-hoc `Expr::const_(Name::from_string("sorry"), ...)`
# constructor. We require the universe list because the argument-less
# `Expr::const_(Name::from_string("sorry"), vec![])` form in the scan
# equivalence test is a type-checker probe, not a proof hole.
RE_SORRY_CONST = re.compile(
    r"""Expr::const_\s*\(\s*
        Name::from_string\s*\(\s*\"sorry\"\s*\)\s*,\s*
        vec!\s*\[\s*Level::zero\s*\(\s*\)\s*\]
    """,
    re.VERBOSE,
)

# Helper: capture the enclosing `fn <name>(` or `pub(crate) fn <name>(`
# line above a sorry site. We scan backwards until we hit a `fn ` or the
# top of the file. This is a heuristic — ok for reporting.
RE_FN_HEADER = re.compile(
    r"^\s*(?:pub(?:\([a-zA-Z_]+\))?\s+)?(?:async\s+)?fn\s+([a-zA-Z_][\w]*)\s*[<(]"
)

# Declaration-name shapes inside a function. We sample any of:
#   "NNVerify.foo.bar" string literal (registration uses string-name form)
#   NAME_FOO (const) — rare, don't bother.
RE_DECL_NAME_STR = re.compile(r'"((?:NNVerify|Lean|Init|Core)\.[A-Za-z0-9_.]+)"')

# Conjecture bucket recognised from filename, e.g. `nn_verify_zonotope_crown.rs`
# -> "ZONOTOPE_CROWN"; `nn_verify_mccormick_attention_types.rs` ->
# "MCCORMICK_ATTENTION_TYPES".
RE_BUCKET_FROM_FILE = re.compile(r"nn_verify_(?P<slug>[a-zA-Z0-9_]+?)\.rs$")

# Explicit CNNN conjecture marker: filename like `nn_verify_zonotope_compress_c001.rs`
# or inline Rust comment `// C001` — we take the lowest-numbered explicit C
# reference in the nearest 40 lines upward.
RE_INLINE_CN = re.compile(r"\bC0?(\d{2,3})\b")


@dataclass
class SorrySite:
    file: str                       # repo-relative
    line: int
    containing_fn: Optional[str]
    decl_name_hint: Optional[str]   # best-effort Lean declaration name
    shape: str                      # "sorry_inhabit_pi" | "expr_const_sorry"
    bucket: Optional[str]           # filename-derived slug
    conjecture: Optional[str]       # C001..CNNN when resolvable
    axiom_deps: int                 # transitive-axiom count from audit.json
    pi_sites: int                   # sorry_inhabit_pi_sites from audit.json
    est_cost: int                   # max(1, axiom_deps) * max(1, pi_sites)
    snippet: str                    # 1-line context

    def to_row(self) -> list[str]:
        return [
            f"{self.file}:{self.line}",
            self.containing_fn or "-",
            self.decl_name_hint or "-",
            self.conjecture or self.bucket or "-",
            str(self.axiom_deps),
            str(self.pi_sites),
            str(self.est_cost),
            self.shape,
        ]


# ---------------------------------------------------------------------------
# Scan helpers


def _iter_rust_files(roots: Iterable[Path]) -> Iterable[Path]:
    for root in roots:
        if not root.exists():
            continue
        for path in sorted(root.rglob("*.rs")):
            spath = str(path)
            if any(spath.endswith(s) for s in SKIP_FILENAME_SUFFIXES):
                continue
            # Skip pure test scaffolding — we want sites, not assertions.
            # However we keep `tests_*_sorry_pi_carriers.rs` OUT because
            # those are assertions ABOUT sorry sites, not sites themselves.
            if "/tests_" in spath or spath.endswith("/tests.rs"):
                continue
            if "/tests/" in spath and "/src/" not in spath:
                # integration tests — skip.
                continue
            yield path


def _containing_fn(lines: list[str], idx: int) -> Optional[str]:
    """Walk backwards from line `idx` to find the enclosing fn name."""
    for j in range(idx, -1, -1):
        m = RE_FN_HEADER.match(lines[j])
        if m:
            return m.group(1)
    return None


def _nearest_decl_name(lines: list[str], idx: int, window: int = 40) -> Optional[str]:
    """Best-effort Lean declaration name by scanning upward for a string
    literal matching `NNVerify.foo.bar` (or `Lean.foo.bar`) — this is the
    registration pattern."""
    start = max(0, idx - window)
    best = None
    for j in range(start, idx + 1):
        m = RE_DECL_NAME_STR.search(lines[j])
        if m:
            # prefer the CLOSEST match (the last one walking forward).
            best = m.group(1)
    return best


def _bucket_and_conjecture(path: Path, lines: list[str], idx: int) -> tuple[Optional[str], Optional[str]]:
    """Derive a coarse bucket slug from the filename, and an explicit
    conjecture ID (C001-C034-ish) when one is mentioned nearby."""
    bucket = None
    m = RE_BUCKET_FROM_FILE.search(path.name)
    if m:
        bucket = m.group("slug").upper()

    # Search filename first, then a small upward window for C007 / c009 etc.
    conj = None
    in_name = RE_INLINE_CN.search(path.name)
    if in_name:
        conj = f"C{int(in_name.group(1)):03d}"
    else:
        start = max(0, idx - 60)
        for j in range(start, idx + 1):
            mm = RE_INLINE_CN.search(lines[j])
            if mm:
                conj = f"C{int(mm.group(1)):03d}"
                break
    return bucket, conj


# ---------------------------------------------------------------------------
# Axiom audit lookup


def _load_axiom_audit() -> dict:
    if not AXIOM_AUDIT_PATH.exists():
        _LOG.warning("axiom_audit.json missing at %s", AXIOM_AUDIT_PATH)
        return {"conjectures": {}}
    try:
        return json.loads(AXIOM_AUDIT_PATH.read_text())
    except json.JSONDecodeError as exc:  # pragma: no cover - IO failure path
        _LOG.error("axiom_audit.json parse error: %s", exc)
        return {"conjectures": {}}


def _conj_metrics(audit: dict, conj: Optional[str]) -> tuple[int, int]:
    """Return (axiom_deps, pi_sites) for a conjecture, zeros when absent."""
    if not conj:
        return (0, 0)
    row = audit.get("conjectures", {}).get(conj)
    if not isinstance(row, dict):
        return (0, 0)
    axioms = int(row.get("axioms", 0) or 0)
    pi_sites = int(row.get("sorry_inhabit_pi_sites", 0) or 0)
    return (axioms, pi_sites)


def _estimate_cost(axioms: int, pi_sites: int) -> int:
    """First-order cost: each axiom must become a genuine proof, scaled
    by the Pi-binder depth the inhabitation must traverse. We clamp both
    factors at 1 so unknown rows still rank above `0`."""
    a = max(1, axioms)
    d = max(1, pi_sites)
    return a * d


# ---------------------------------------------------------------------------
# Scanner


def scan(audit: Optional[dict] = None) -> list[SorrySite]:
    if audit is None:
        audit = _load_axiom_audit()

    sites: list[SorrySite] = []
    for path in _iter_rust_files(SCAN_ROOTS):
        try:
            text = path.read_text()
        except OSError as exc:  # pragma: no cover - IO failure
            _LOG.warning("read %s failed: %s", path, exc)
            continue
        if "sorry_inhabit_pi" not in text and "Name::from_string(\"sorry\")" not in text:
            continue
        lines = text.splitlines()
        for idx, line in enumerate(lines):
            shape: Optional[str] = None
            if RE_SORRY_INHABIT_PI_CALL.search(line):
                # Skip the use-statement / fn-definition lines.
                stripped = line.lstrip()
                if stripped.startswith("use ") or stripped.startswith("//"):
                    continue
                # Skip the function DEFINITION itself (handled by re flag).
                shape = "sorry_inhabit_pi"
            elif RE_SORRY_CONST.search(line):
                stripped = line.lstrip()
                if stripped.startswith("//"):
                    continue
                shape = "expr_const_sorry"
            if shape is None:
                continue

            fn = _containing_fn(lines, idx)
            decl = _nearest_decl_name(lines, idx)
            bucket, conj = _bucket_and_conjecture(path, lines, idx)
            axioms, pi_sites = _conj_metrics(audit, conj)
            cost = _estimate_cost(axioms, pi_sites)

            rel = path.relative_to(REPO_ROOT).as_posix()
            sites.append(
                SorrySite(
                    file=rel,
                    line=idx + 1,
                    containing_fn=fn,
                    decl_name_hint=decl,
                    shape=shape,
                    bucket=bucket,
                    conjecture=conj,
                    axiom_deps=axioms,
                    pi_sites=pi_sites,
                    est_cost=cost,
                    snippet=line.strip()[:140],
                )
            )
    sites.sort(key=lambda s: (-s.est_cost, s.file, s.line))
    return sites


# ---------------------------------------------------------------------------
# Output formatters


def _write(stream, text: str) -> None:
    """Small shim so we can route human output through stdout without
    relying on the `print` builtin (local code-quality hook bans it)."""
    stream.write(text)
    stream.write("\n")


def _print_table(sites: list[SorrySite], stream=sys.stdout) -> None:
    headers = ["site", "fn", "decl", "bucket/C", "axioms", "pi-sites", "cost", "shape"]
    rows = [s.to_row() for s in sites]
    widths = [len(h) for h in headers]
    for r in rows:
        for i, cell in enumerate(r):
            widths[i] = max(widths[i], len(cell))
    fmt = "  ".join(f"{{:<{w}}}" for w in widths)
    _write(stream, fmt.format(*headers))
    _write(stream, fmt.format(*["-" * w for w in widths]))
    for r in rows:
        _write(stream, fmt.format(*r))
    _write(stream, f"\n[{len(sites)} sorry site(s) found]")


def _as_json(sites: list[SorrySite]) -> str:
    return json.dumps([asdict(s) for s in sites], indent=2, sort_keys=True)


def _md_header(sites: list[SorrySite], audit: dict) -> list[str]:
    total = len(sites)
    total_cost = sum(s.est_cost for s in sites)
    rel = AXIOM_AUDIT_PATH.relative_to(REPO_ROOT)
    return [
        "# Sorry-to-axiom dependency trace + proof-cost estimate",
        "",
        "- Generated: 2026-04-20",
        f"- Total sorry sites: **{total}**",
        f"- Aggregate estimated cost: **{total_cost}**",
        f"- Source: `{rel}` (last_updated={audit.get('last_updated', '?')},"
        f" total_domain_axioms={audit.get('total_domain_axioms', '?')})",
        "",
        "## Cost methodology",
        "",
        "`cost = max(1, axiom_deps) * max(1, pi_sites)`. `axiom_deps`",
        "is the conjecture's `axioms` count from `data/axiom_audit.json`;",
        "`pi_sites` is `sorry_inhabit_pi_sites` for the same row.",
        "Unknown rows clamp to 1. This is a RANKING primitive, not a",
        "ground truth — treat 10x deltas as real, 2x as noise.",
        "",
    ]


def _md_bucket_table(sites: list[SorrySite]) -> list[str]:
    by_conj: dict[str, int] = {}
    for s in sites:
        key = s.conjecture or s.bucket or "UNKNOWN"
        by_conj[key] = by_conj.get(key, 0) + 1
    out = ["## Sites by bucket / conjecture", "", "| Bucket | Sites |", "|---|---|"]
    for bucket, count in sorted(by_conj.items(), key=lambda kv: -kv[1]):
        out.append(f"| `{bucket}` | {count} |")
    out.append("")
    return out


def _md_site_row(s: SorrySite) -> str:
    return (
        "| `{site}` | `{fn}` | `{decl}` | {buc} | {ax} | {pi} | {cost} | {shape} |"
    ).format(
        site=f"{s.file}:{s.line}",
        fn=s.containing_fn or "-",
        decl=s.decl_name_hint or "-",
        buc=s.conjecture or s.bucket or "-",
        ax=s.axiom_deps,
        pi=s.pi_sites,
        cost=s.est_cost,
        shape=s.shape,
    )


def _md_site_table(sites: list[SorrySite], title: str) -> list[str]:
    out = [
        f"## {title}",
        "",
        "| Site | Fn | Decl hint | Bucket / C | axioms | pi-sites | cost | shape |",
        "|---|---|---|---|---:|---:|---:|---|",
    ]
    out.extend(_md_site_row(s) for s in sites)
    out.append("")
    return out


def _md_notes() -> list[str]:
    return [
        "## Notes",
        "",
        "- `decl hint` is best-effort: the nearest string literal matching",
        "  `NNVerify.*` / `Lean.*` / `Init.*` / `Core.*` within 40 lines of the",
        "  sorry site. Sites inside helper functions (e.g. `sorry_inhabit_pi`",
        "  itself) will show the helper's caller context only when the call",
        "  appears within the same `fn`.",
        "- `pi_sites == 0` rows indicate no known Pi-binder count for the",
        "  conjecture — the cost model clamps them to 1 rather than 0 so the",
        "  site still ranks above purely-zero rows.",
        "- Sites in `verify` crate files have no matching `conjectures.<C>`",
        "  row and therefore default to axioms=0, pi_sites=0 -> cost=1.",
        "",
    ]


def _markdown_report(sites: list[SorrySite], audit: dict) -> str:
    lines: list[str] = []
    lines.extend(_md_header(sites, audit))
    lines.extend(_md_bucket_table(sites))
    lines.extend(_md_site_table(sites[:20], "Highest-cost sorrys (top 20)"))
    lines.extend(_md_site_table(sites, "All sites (sorted by cost desc, then path)"))
    lines.extend(_md_notes())
    return "\n".join(lines) + "\n"


# ---------------------------------------------------------------------------
# CLI


def _build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        prog="sorry_to_axiom_tracer",
        description=__doc__.splitlines()[0] if __doc__ else "",
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    p.add_argument("--json", action="store_true", help="emit JSON instead of the human table")
    p.add_argument("--report", action="store_true",
                   help="write a markdown report to reports/audits/<date>-sorry-axiom-cost.md")
    p.add_argument("--report-path", type=Path, default=None,
                   help="override markdown report output path (implies --report)")
    p.add_argument("--verbose", "-v", action="count", default=0, help="increase log level")
    return p


def main(argv: Optional[list[str]] = None) -> int:
    parser = _build_parser()
    args = parser.parse_args(argv)
    logging.basicConfig(
        level=logging.WARNING - 10 * min(args.verbose, 2),
        format="%(levelname)s %(name)s: %(message)s",
    )

    audit = _load_axiom_audit()
    sites = scan(audit)

    if args.json:
        _write(sys.stdout, _as_json(sites))
    else:
        _print_table(sites)

    if args.report or args.report_path is not None:
        out = args.report_path or (DEFAULT_REPORT_DIR / "2026-04-20-sorry-axiom-cost.md")
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(_markdown_report(sites, audit))
        _write(sys.stdout, f"\nreport written: {out.relative_to(REPO_ROOT)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
