#!/usr/bin/env python3
"""Fail-fast gate on stale upstream-Lean ledger entries.

Port of trust/scripts/check_ledger_expirations.py, kept table-driven so a new
clean-side ledger is one `LEDGERS` row rather than new code. Same contract:
every ACTIVE entry must carry an `expires_on`; once that date passes the entry
must be re-reviewed and either renewed with a fresh expiry or retired.

Ported unchanged in substance:
  * the (path, list_key, id_field) LEDGERS table;
  * EXEMPT_LEDGERS, and the check that an exempt file has NOT grown an
    `expires_on` — silence is indistinguishable from coverage, so the exemption
    is stated and then verified;
  * `--max-same-day`, the expiry-cliff guard. A cluster of rows all expiring on
    one date blocks every push at once, and a reviewer facing that on a deadline
    renews the batch unexamined. That is exactly how 71 rows in the Rust ledger
    came to waive a defect that had already been fixed;
  * the tomllib re-exec, because bare `python3` on this box is 3.9.

Usage:
    tests/upstream-lean/check_ledger_expirations.py
    tests/upstream-lean/check_ledger_expirations.py --warn-days 14
    tests/upstream-lean/check_ledger_expirations.py --as-of 2027-01-01
    tests/upstream-lean/check_ledger_expirations.py --json
    tests/upstream-lean/check_ledger_expirations.py --self-test

Exit codes:
    0   all active entries valid
    1   one or more entries expired, missing an expiry, or clustered
    2   warnings only, and only with --strict-warn

Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
"""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass, field
from datetime import date, datetime, timezone
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parents[2]

# (path, top-level list key, field that names an entry in diagnostics)
LEDGERS: tuple[tuple[Path, str, str], ...] = (
    (REPO_ROOT / "tests" / "upstream-lean" / "exceptions.toml", "exceptions", "id"),
)

# Ledger-SHAPED files this gate deliberately does not walk, each with a reason,
# and each then CHECKED: an exempt file that grows an `expires_on` has become an
# expiring ledger and its exemption is no longer true, which fails.
EXEMPT_LEDGERS: tuple[tuple[Path, str], ...] = (
    (
        REPO_ROOT / "tests" / "upstream-lean" / "baseline.toml",
        "the adopted-upstream alignment record, not an exception ledger: its "
        "entries carry a status classification of a surface, not the "
        "active/retired lifecycle this gate reads. Its `[seeding] unseeded_until` "
        "IS a deadline, but it is enforced by run_upstream_lean.py, which is the "
        "only thing that can tell a seeded corpus from an unseeded one",
    ),
    (
        REPO_ROOT / "tests" / "upstream-lean" / "corpus.toml",
        "the pinned probe set: rows are (file, decl, expected) measurements with "
        "no lifecycle and no expiry. A probe is retired by deleting it, and "
        "run_upstream_lean.py fails on an exception row whose probe is gone",
    ),
)


def _reexec_under_a_toml_capable_python() -> None:
    import importlib.util
    import os
    import shutil

    if importlib.util.find_spec("tomllib") or importlib.util.find_spec("tomli"):
        return
    if os.environ.get("CLEAN_LEDGER_PY_REEXEC"):
        return
    for candidate in ("python3.14", "python3.13", "python3.12", "python3.11"):
        found = shutil.which(candidate)
        if not found:
            continue
        os.environ["CLEAN_LEDGER_PY_REEXEC"] = "1"
        os.execv(found, [found, os.path.abspath(__file__), *sys.argv[1:]])


_reexec_under_a_toml_capable_python()

TOML_PARSER_ERROR = (
    "error: no TOML parser available for ledger checks; use Python 3.11+ for "
    "stdlib tomllib, or install tomli for this Python environment"
)


@dataclass
class EntryStatus:
    ledger: Path
    entry_id: str
    expires_on: date | None
    status: str  # "expired" | "expiring_soon" | "ok" | "no_expiry"
    days_remaining: int | None = None
    note: str = ""
    owner: str = ""
    issue: str = ""
    reviewed_on: str = ""
    reason: str = ""


@dataclass
class Report:
    expired: list[EntryStatus] = field(default_factory=list)
    expiring_soon: list[EntryStatus] = field(default_factory=list)
    ok: list[EntryStatus] = field(default_factory=list)
    no_expiry: list[EntryStatus] = field(default_factory=list)

    def as_dict(self) -> dict[str, Any]:
        def serialize(es: EntryStatus) -> dict[str, Any]:
            return {
                "ledger": str(es.ledger.relative_to(REPO_ROOT)),
                "entry_id": es.entry_id,
                "expires_on": es.expires_on.isoformat() if es.expires_on else None,
                "status": es.status,
                "days_remaining": es.days_remaining,
                "note": es.note,
                "owner": es.owner,
                "issue": es.issue,
                "reviewed_on": es.reviewed_on,
                "reason": es.reason,
            }

        return {
            "summary": {
                "expired": len(self.expired),
                "expiring_soon": len(self.expiring_soon),
                "ok": len(self.ok),
                "no_expiry": len(self.no_expiry),
            },
            "expired": [serialize(e) for e in self.expired],
            "expiring_soon": [serialize(e) for e in self.expiring_soon],
            "no_expiry": [serialize(e) for e in self.no_expiry],
        }


def load_toml(path: Path) -> dict[str, Any]:
    try:
        import tomllib
    except ModuleNotFoundError:
        try:
            import tomli as tomllib  # type: ignore[no-redef]
        except ModuleNotFoundError as exc:
            raise RuntimeError(TOML_PARSER_ERROR) from exc
    return tomllib.loads(path.read_text(encoding="utf-8"))


def parse_date(value: Any) -> date | None:
    if value is None:
        return None
    if isinstance(value, datetime):
        return value.date()
    if isinstance(value, date):
        return value
    if isinstance(value, str):
        try:
            return date.fromisoformat(value)
        except ValueError:
            return None
    return None


def entry_is_active(entry: dict[str, Any]) -> bool:
    """Only `status = "active"` entries gate.

    A missing `status` is treated as ACTIVE — better to surface a missing-field
    problem than to skip a row silently.
    """
    status = entry.get("status")
    if status is None:
        return True
    return str(status).lower() == "active"


def render_value(value: Any) -> str:
    if isinstance(value, (date, datetime)):
        return value.isoformat()
    if value is None:
        return ""
    return str(value)


def classify(expires_on: date | None, as_of: date, warn_days: int) -> tuple[str, int | None]:
    if expires_on is None:
        return ("no_expiry", None)
    delta = (expires_on - as_of).days
    if delta < 0:
        return ("expired", delta)
    if delta <= warn_days:
        return ("expiring_soon", delta)
    return ("ok", delta)


def walk_ledger(
    path: Path, list_key: str, id_field: str, as_of: date, warn_days: int
) -> list[EntryStatus]:
    if not path.exists():
        return []
    data = load_toml(path)
    out: list[EntryStatus] = []
    for raw in data.get(list_key) or []:
        if not isinstance(raw, dict) or not entry_is_active(raw):
            continue
        entry_id = str(raw.get(id_field, raw.get("id", "<unknown>")))
        expires_on = parse_date(raw.get("expires_on"))
        status, days = classify(expires_on, as_of, warn_days)
        note = ""
        if status == "no_expiry":
            note = "active entry has no `expires_on` — every ledger entry must carry an expiration"
        out.append(
            EntryStatus(
                ledger=path,
                entry_id=entry_id,
                expires_on=expires_on,
                status=status,
                days_remaining=days,
                note=note,
                owner=render_value(raw.get("owner")),
                issue=render_value(raw.get("issue")),
                reviewed_on=render_value(raw.get("reviewed_on")),
                reason=render_value(raw.get("reason")),
            )
        )
    return out


def check_exemptions() -> list[str]:
    problems: list[str] = []
    for path, reason in EXEMPT_LEDGERS:
        if not path.exists():
            problems.append(f"{path.relative_to(REPO_ROOT)}: exempt file is missing")
            continue
        if "expires_on" in path.read_text(encoding="utf-8"):
            problems.append(
                f"{path.relative_to(REPO_ROOT)} carries `expires_on` but is exempt from "
                f"this gate ({reason}). Either drop the expiry or move the file into "
                f"LEDGERS; an expiring row nobody checks is worse than no row."
            )
    return problems


def same_day_clusters(report: Report, limit: int) -> list[tuple[date, int]]:
    if limit <= 0:
        return []
    counts: dict[date, int] = {}
    for es in [*report.ok, *report.expiring_soon]:
        if es.expires_on is None:
            continue
        counts[es.expires_on] = counts.get(es.expires_on, 0) + 1
    return sorted(((d, n) for d, n in counts.items() if n > limit), key=lambda t: t[0])


def build_report(as_of: date, warn_days: int) -> Report:
    report = Report()
    for path, list_key, id_field in LEDGERS:
        for es in walk_ledger(path, list_key, id_field, as_of, warn_days):
            {
                "expired": report.expired,
                "expiring_soon": report.expiring_soon,
                "ok": report.ok,
                "no_expiry": report.no_expiry,
            }[es.status].append(es)
    return report


def render_text(report: Report, as_of: date, warn_days: int) -> str:
    total = len(report.expired) + len(report.expiring_soon) + len(report.ok) + len(report.no_expiry)
    lines = [
        f"upstream-lean ledger expiration check  as_of={as_of.isoformat()}  warn_days={warn_days}",
        "",
        f"  active entries reviewed: {total}",
        f"  expired:        {len(report.expired)}",
        f"  expiring soon:  {len(report.expiring_soon)}",
        f"  no expiry set:  {len(report.no_expiry)}",
        f"  ok:             {len(report.ok)}",
        "",
        f"  ledgers walked: {len(LEDGERS)}",
        f"  exempt:         {len(EXEMPT_LEDGERS)} "
        f"({', '.join(str(p.relative_to(REPO_ROOT)) for p, _ in EXEMPT_LEDGERS)})",
    ]

    def context(es: EntryStatus) -> None:
        lines.append(
            f"    owner={es.owner or '<missing>'}  issue={es.issue or '<missing>'}  "
            f"reviewed_on={es.reviewed_on or '<missing>'}"
        )
        if es.reason:
            lines.append(f"    reason={es.reason}")

    if report.expired:
        lines += ["", "EXPIRED — gate FAIL:"]
        for es in report.expired:
            lines.append(
                f"  • {es.ledger.relative_to(REPO_ROOT)}  {es.entry_id}  "
                f"expired={es.expires_on}  ({-(es.days_remaining or 0)} days ago)"
            )
            context(es)
        lines.append(
            "Remediation: re-review each expired entry, then retire it if the "
            "divergence is fixed or renew `expires_on` with current owner/issue context."
        )
    if report.expiring_soon:
        lines += ["", f"EXPIRING within {warn_days} days — review required:"]
        for es in report.expiring_soon:
            lines.append(
                f"  • {es.ledger.relative_to(REPO_ROOT)}  {es.entry_id}  "
                f"expires={es.expires_on}  ({es.days_remaining} days remaining)"
            )
            context(es)
    if report.no_expiry:
        lines += ["", "NO EXPIRY SET — schema violation (active entries must expire):"]
        for es in report.no_expiry:
            lines.append(f"  • {es.ledger.relative_to(REPO_ROOT)}  {es.entry_id}")
            context(es)
    return "\n".join(lines) + "\n"


def self_test() -> int:
    """Exercise classify/active/exemption logic without touching the tree."""
    failures: list[str] = []
    as_of = date(2026, 9, 1)

    cases = [
        (date(2026, 8, 31), "expired"),
        (date(2026, 9, 1), "expiring_soon"),
        (date(2026, 9, 10), "expiring_soon"),
        (date(2026, 10, 1), "ok"),
        (None, "no_expiry"),
    ]
    for expires, want in cases:
        got, _ = classify(expires, as_of, 14)
        if got != want:
            failures.append(f"classify({expires}) -> {got}, want {want}")

    if not entry_is_active({}):
        failures.append("a row with no `status` must be treated as active")
    if not entry_is_active({"status": "active"}):
        failures.append("status=active must gate")
    if entry_is_active({"status": "resolved"}):
        failures.append("status=resolved must not gate")

    report = Report(
        ok=[
            EntryStatus(LEDGERS[0][0], f"e{i}", date(2026, 12, 1), "ok", 91)
            for i in range(4)
        ]
    )
    if not same_day_clusters(report, 3):
        failures.append("4 rows on one date must trip a --max-same-day 3 cliff")
    if same_day_clusters(report, 4):
        failures.append("4 rows must not trip a --max-same-day 4 cliff")
    if same_day_clusters(report, 0):
        failures.append("--max-same-day 0 must disable the cliff check")

    problems = check_exemptions()
    if problems:
        failures.append(f"live exemption check is unhappy: {problems}")

    if failures:
        print("expiry-gate self-test FAILED:", file=sys.stderr)
        for failure in failures:
            print(f"  {failure}", file=sys.stderr)
        return 1
    print(f"expiry-gate self-test passed ({len(cases) + 6} assertions).")
    return 0


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--warn-days", type=int, default=14)
    p.add_argument("--as-of", default=None, help="Override today's date (ISO YYYY-MM-DD).")
    p.add_argument("--json", action="store_true")
    p.add_argument("--strict-warn", action="store_true")
    p.add_argument(
        "--max-same-day",
        type=int,
        default=0,
        help="Fail when more than N active entries share one `expires_on` (0 = off).",
    )
    p.add_argument("--self-test", action="store_true")
    return p.parse_args()


def main() -> int:
    args = parse_args()
    if args.self_test:
        return self_test()
    as_of = parse_date(args.as_of) if args.as_of else datetime.now(timezone.utc).date()
    if as_of is None:
        print(f"error: invalid --as-of value: {args.as_of!r}", file=sys.stderr)
        return 1
    try:
        report = build_report(as_of, args.warn_days)
    except RuntimeError as exc:
        print(exc, file=sys.stderr)
        return 1
    problems = check_exemptions()
    if args.json:
        json.dump(report.as_dict(), sys.stdout, indent=2, default=str)
        sys.stdout.write("\n")
    else:
        sys.stdout.write(render_text(report, as_of, args.warn_days))
    if problems:
        print("EXEMPT LEDGER NO LONGER EXEMPT:", file=sys.stderr)
        for problem in problems:
            print(f"  {problem}", file=sys.stderr)
        return 1
    clusters = same_day_clusters(report, args.max_same_day)
    for when, count in clusters:
        print(
            f"EXPIRY CLIFF {when.isoformat()}: {count} entries (limit "
            f"{args.max_same_day}). On that date every push blocks until all "
            f"{count} are reviewed, which is how a batch gets renewed unexamined.",
            file=sys.stderr,
        )
    if report.expired or report.no_expiry or clusters:
        return 1
    if args.strict_warn and report.expiring_soon:
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
