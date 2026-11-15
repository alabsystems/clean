#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0

"""Fail closed unless the pre-push hook still covers the fast gate.

The pre-push hook (`scripts/githooks/pre-push`) does not run `local_gate.sh --fast`
verbatim -- three of that gate's legs are cargo builds and two more cost 20+ s,
so a hook built from all of them is a hook nobody keeps installed. It runs a
curated subset instead.

A hand-curated subset rots. Somebody adds a fail-closed leg to the fast gate,
nothing adds it to the hook, and six weeks later the hook is a green stamp on
half a gate -- which is exactly the failure the hook was installed to end, one
level up. So the curation is data (`scripts/githooks/gate-legs.txt`), and this
checker refuses the push unless three independent things still agree:

  1. the `# GATE-LEG:` ids reachable in local_gate.sh's FAST path,
  2. the ids `scripts/githooks/pre-push` declares in its HOOK-LEGS block,
  3. the rows of `scripts/githooks/gate-legs.txt`.

Set equality on (1)==(3) and (2)=={IN_HOOK, WAIVED} gives an actionable
diagnostic.

THREE-WAY, NOT TWO-WAY. Until 2026-08-25 a row carried one status that was read
as two different claims at once -- "the hook does not run it" AND "local_gate.sh
runs it only in full mode" -- and nothing checked the second. Five of the six
COST rows said "Full gate only" while their legs sat outside every
`GATE-FULL-ONLY` region and ran in `--fast` as well, `trust-verify-soundness`
among them: a Trust-side red that refused every Clean-side run of the command
CLAUDE.md tells lanes to use before pushing. So the axes are now separate
columns. STATUS is about the HOOK (IN_HOOK / COST / WAIVED). MODE is about
local_gate.sh (`both` = the fast path reaches it, `full` = only the full path
does), it is DERIVED here from where the leg's `# GATE-LEG:` marker sits, and a
row that disagrees with the code refuses the push. A leg the hook runs must be
reachable in fast mode, so IN_HOOK/WAIVED implies `both`.

The marker placement rule that makes MODE derivable: a leg's `# GATE-LEG:`
marker belongs inside the region that actually RUNS it. A marker parked above an
`if [[ $FAST -eq 1 ]]` that skips the leg describes nothing.

None of this is the whole guard, because a marker-based parse only sees
what somebody remembered to mark. The backstop is a digest: the entire fast
region of local_gate.sh, comments and blank lines stripped, is pinned in
`data/hook_gate_pin.json`, and so is the hook's own leg-definition region. Any
edit to any fast leg -- a new one, a changed flag, a deleted one, or a leg body
quietly gutted while its id stays put -- moves a digest and refuses the push
until a human re-classifies and refreshes the pin. That is deliberately noisy in
exactly the place noise is worth paying for.

Usage:
    python3 scripts/check_hook_coverage.py            # check (fail-closed)
    python3 scripts/check_hook_coverage.py --update   # re-pin after a review
"""

from __future__ import annotations

import hashlib
import json
import re
import sys
from datetime import date
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
GATE = ROOT / "scripts/local_gate.sh"
HOOK = ROOT / "scripts/githooks/pre-push"
POLICY = ROOT / "scripts/githooks/gate-legs.txt"
PIN = ROOT / "data/hook_gate_pin.json"

FULL_ONLY_BEGIN = "# GATE-FULL-ONLY BEGIN"
FULL_ONLY_END = "# GATE-FULL-ONLY END"
MARKER = re.compile(r"^\s*#\s*GATE-LEG:\s*(\S+)\s*$")
VALID_STATUS = ("IN_HOOK", "COST", "WAIVED")
MODE_BOTH = "both"
MODE_FULL = "full"
VALID_MODE = (MODE_BOTH, MODE_FULL)
ISO = re.compile(r"^\d{4}-\d{2}-\d{2}$")

# A WAIVED row means "the leg RUNS and PRINTS and does not block". The hook
# implements that itself; `local_gate.sh` implements it by reporting through
# `fail_waivable <leg-id> "<msg>"` instead of `fail "<msg>"`, and a leg that
# still calls plain `fail` exits the whole gate on the spot whatever the table
# says. Measured 2026-09-14: `no-ignored-tests` was waived, the hook honoured
# it, and `scripts/local_gate.sh` — the command CLAUDE.md tells every lane to
# run before pushing — exited 1 at leg 8 of 56 with FORTY-EIGHT legs never
# reached, the soundness certificate and the workspace lint among them. So the
# two tables have to agree on this too, not only on which ids exist.
# `|| fail_waivable <id> "..."` is the idiomatic form for a leg whose command is
# a pipeline, and `fail_waivable <id> "..."` inside an if-block is the other.
# Anchoring on the bare call alone missed the first spelling and reported a
# WAIVED row as having no call site (measured 2026-09-14, on the very next
# waiver added after this rule landed).
WAIVABLE_CALL = re.compile(r"^\s*(?:\|\||&&)?\s*fail_waivable\s+(\S+)\s")

# A ratchet whose baseline carries its own owned, expiring, CAPPED debt is
# never WAIVED: a waiver passes whatever its leg measures, so every growth in
# every crate lands while it runs (verifier land-clean-r1 P6, 2026-09-29: with
# paragon-ratchet waived for the kernel/cert batch's +1/+9/+8, an unwrap
# appended to clean-elab printed NOT BLOCKING). The debt admits exactly what
# was measured and no more. Leg id -> where its debt lives.
DEBT_RATCHETS = {"paragon-ratchet": "data/paragon_ratchet.json's `debt`"}


class Drift(Exception):
    """A disagreement between the gate, the hook and the policy table."""


def _read(path: Path) -> str:
    try:
        return path.read_text()
    except OSError as exc:
        raise Drift(f"{path.relative_to(ROOT)} is unreadable: {exc}") from exc


class Regions:
    """local_gate.sh split into the part `--fast` runs and the part it does not.

    Both halves are kept, and both are pinned. Pinning only the fast half was a
    hole with teeth: moving a leg into a `GATE-FULL-ONLY` region would have
    dropped its body out of digest coverage entirely, so the one edit that
    changes a leg's mode was also the one edit that stopped watching it.
    """

    def __init__(self, fast_lines, fast_ids, full_lines, full_ids):
        self.fast_lines = fast_lines
        self.fast_ids = fast_ids
        self.full_lines = full_lines
        self.full_ids = full_ids

    @property
    def ids(self) -> list[str]:
        return self.fast_ids + self.full_ids

    def derived_mode(self, leg: str) -> str | None:
        if leg in self.fast_ids:
            return MODE_BOTH
        if leg in self.full_ids:
            return MODE_FULL
        return None


def split_regions(text: str) -> Regions:
    """Split local_gate.sh at its `GATE-FULL-ONLY` markers.

    A `# GATE-LEG:` id lands in the fast set or the full set purely by where its
    marker sits, which is what makes the MODE column checkable instead of
    aspirational.
    """
    fast_lines: list[str] = []
    fast_ids: list[str] = []
    full_lines: list[str] = []
    full_ids: list[str] = []
    depth = 0
    for raw in text.splitlines():
        stripped = raw.strip()
        if stripped == FULL_ONLY_BEGIN:
            depth += 1
            continue
        if stripped == FULL_ONLY_END:
            depth -= 1
            if depth < 0:
                raise Drift(
                    f"{FULL_ONLY_END} without a matching {FULL_ONLY_BEGIN} in local_gate.sh"
                )
            continue
        hit = MARKER.match(raw)
        if depth:
            if hit:
                full_ids.append(hit.group(1))
            full_lines.append(raw)
            continue
        if hit:
            fast_ids.append(hit.group(1))
        fast_lines.append(raw)
    if depth:
        raise Drift(f"{FULL_ONLY_BEGIN} was never closed in local_gate.sh")
    return Regions(fast_lines, fast_ids, full_lines, full_ids)


def normalized_digest(lines: list[str]) -> str:
    """sha256 of the fast region with comments and blank lines removed.

    Comments are stripped so that documenting a leg -- which the legs in this
    tree do at length -- never costs a re-pin, while changing what a leg RUNS
    always does.
    """
    body = [
        ln.strip()
        for ln in lines
        if ln.strip() and not ln.strip().startswith("#")
    ]
    return hashlib.sha256("\n".join(body).encode()).hexdigest()


def hook_legs(text: str) -> list[str]:
    begin = "# HOOK-LEGS BEGIN"
    end = "# HOOK-LEGS END"
    try:
        block = text.split(begin, 1)[1].split(end, 1)[0]
    except IndexError as exc:
        raise Drift(
            "scripts/githooks/pre-push no longer has its HOOK-LEGS BEGIN/END block, "
            "so the hook can no longer state which legs it runs"
        ) from exc
    out = []
    for ln in block.splitlines():
        tok = ln.strip().strip('"')
        if not tok or tok.startswith("#") or tok.startswith("HOOK_LEGS="):
            continue
        out.append(tok)
    return out


def hook_functions(text: str) -> set[str]:
    return set(re.findall(r"^(leg_[a-z0-9_]+)\s*\(\)", text, flags=re.M))


def hook_body_digest(text: str) -> str:
    """sha256 of the hook's leg DEFINITIONS, comments and blanks stripped.

    Name equality is not coverage. A mutation that left every id in place and
    gutted `leg_add_decl_ratchet()` -- dropping the `--selftest` arm, so the
    ratchet's own falsifiability check stops running -- passed every set
    comparison above and sailed. Measured, in a throwaway clone, 2026-08-23.

    So the bodies are pinned too — and AUDIT r10 M10-3 measured that the region
    this docstring described was not the region the code took. `start` was
    anchored on the literal `leg_dep_boundary()`, the FIFTH leg definition, so
    `leg_gate_registry`, `leg_cargo_test_selectors`, `leg_doc_claims` and
    `leg_suite_journal` sat outside every digest; `end` stopped at
    `# HOOK-LEGS END`, leaving the driver, the waiver read, the BLOCKING
    aggregation and the exit unpinned. 117 of 448 lines were covered. Measured
    consequences, both with a byte-identical digest and rc=0: replacing
    `leg_gate_registry()`'s body (the leg that runs the 141-row registry check)
    with `true`, and turning the final `if [ -z "$BLOCKING" ] ...` into
    `if true`, i.e. a hook that always exits 0.

    AUDIT r11 M11-2 finished the job. Widening the region to "first `leg_*()`
    to EOF" still left the 45 executable lines ABOVE the first leg unpinned,
    and that prefix is not prose: it carries `set -uo pipefail`, the
    `PUSHED_REFS` drain, `pick_python()`/`PY=` that every leg runs under, the
    exported `CLEAN_PUSH_RANGES` that fmt-changed judges, and a
    **deletion-only shortcut that `exit 0`s**. Measured: changing ONE token
    there (`0000…0) ;;` -> `0000…0|*) ;;`) made the hook print "deletion-only
    push, nothing to gate." and exit 0 with ZERO of its 30 legs run — while
    this checker reported the same digest, byte for byte, at rc 0.

    So the digest now covers the WHOLE FILE with comments and blank lines
    stripped, the way `split_regions` already treats `local_gate.sh` (which has
    both halves pinned and never had this hole). Stripping keeps the property
    the old boundary was reaching for -- re-pinning is not triggered by editing
    a comment -- without excluding code.
    """
    import re as _re
    stripped = "\n".join(
        ln for ln in text.split("\n")
        if ln.strip() and not ln.lstrip().startswith("#")
    )
    if not _re.search(r"^leg_[A-Za-z0-9_]+\(\)", text, _re.M):
        raise Drift(
            "scripts/githooks/pre-push no longer has a recognisable leg-definition "
            "region (no `leg_*()` definition found), so what the hook actually runs "
            "cannot be pinned"
        )
    text = stripped
    start = 0
    end = len(text)
    body = [
        ln.strip()
        for ln in text[start:end].splitlines()
        if ln.strip() and not ln.strip().startswith("#")
    ]
    return hashlib.sha256("\n".join(body).encode()).hexdigest()


def policy_rows() -> list[dict[str, str]]:
    rows = []
    for lineno, raw in enumerate(_read(POLICY).splitlines(), 1):
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        parts = [p.strip() for p in raw.split("|")]
        if len(parts) < 6:
            raise Drift(
                f"{POLICY.name}:{lineno}: need 6 `|` fields "
                "(<status> | <mode> | <leg-id> | <owner> | <expires> | <reason>), "
                f"got {len(parts)}"
            )
        row = dict(
            zip(
                ("status", "mode", "leg", "owner", "expires", "reason"),
                parts[:5] + ["|".join(parts[5:]).strip()],
            )
        )
        row["lineno"] = str(lineno)
        if row["status"] not in VALID_STATUS:
            raise Drift(
                f"{POLICY.name}:{lineno}: status {row['status']!r} is not one of {VALID_STATUS}"
            )
        if row["mode"] not in VALID_MODE:
            raise Drift(
                f"{POLICY.name}:{lineno}: mode {row['mode']!r} is not one of {VALID_MODE} "
                "-- `both` means local_gate.sh --fast reaches the leg, `full` means only "
                "the full gate does"
            )
        if row["status"] in ("IN_HOOK", "WAIVED") and row["mode"] != MODE_BOTH:
            raise Drift(
                f"{POLICY.name}:{lineno}: {row['leg']} is {row['status']} but mode="
                f"{row['mode']!r}. The hook is the fast path's subset; it cannot run a leg "
                "the fast path never reaches."
            )
        if not row["reason"]:
            raise Drift(f"{POLICY.name}:{lineno}: {row['leg']} has no reason")
        if row["status"] == "WAIVED":
            if row["owner"] in ("", "-"):
                raise Drift(
                    f"{POLICY.name}:{lineno}: a WAIVED row needs a real owner, not {row['owner']!r} "
                    "-- an unowned waiver is how a red leg becomes permanent"
                )
            # audit r10 M10-4: shape alone let a far-future date retire a leg
            # permanently; same 180-day horizon as the registry and the
            # source-elab exception.
            if ISO.match(row["expires"]):
                import datetime as _dt
                _h = (_dt.date.today() + _dt.timedelta(days=180)).isoformat()
                if row["expires"] > _h:
                    raise Drift(
                        f"{POLICY.name}:{lineno}: waiver expires={row['expires']} is beyond "
                        f"the 180-day horizon ({_h}) -- a waiver that outlives review is a "
                        f"permanent bypass wearing a date")
            if not ISO.match(row["expires"]):
                raise Drift(
                    f"{POLICY.name}:{lineno}: a WAIVED row needs an expiry as YYYY-MM-DD, "
                    f"got {row['expires']!r}"
                )
        else:
            if row["owner"] != "-" or row["expires"] != "-":
                raise Drift(
                    f"{POLICY.name}:{lineno}: {row['status']} rows carry no owner/expiry; use `-`"
                )
        if row["status"] == "COST" and not re.search(r"\d|cargo ", row["reason"]):
            raise Drift(
                f"{POLICY.name}:{lineno}: a COST exclusion must name the measured cost or the "
                "build it runs -- an unmeasured cost claim is not reviewable"
            )
        rows.append(row)
    return rows


def main(argv: list[str]) -> int:
    update = "--update" in argv[1:]

    gate_text = _read(GATE)
    regions = split_regions(gate_text)
    gate_ids = regions.ids
    digest = normalized_digest(regions.fast_lines)
    full_digest = normalized_digest(regions.full_lines)

    hook_text = _read(HOOK)
    declared = hook_legs(hook_text)
    fns = hook_functions(hook_text)
    hook_digest = hook_body_digest(hook_text)

    rows = policy_rows()
    policy_ids = [r["leg"] for r in rows]
    runnable = [r["leg"] for r in rows if r["status"] in ("IN_HOOK", "WAIVED")]

    problems: list[str] = []

    dupes = {x for x in policy_ids if policy_ids.count(x) > 1}
    if dupes:
        problems.append(f"gate-legs.txt lists {sorted(dupes)} more than once")
    dupes = {x for x in declared if declared.count(x) > 1}
    if dupes:
        problems.append(f"the hook declares {sorted(dupes)} more than once")

    missing = sorted(set(gate_ids) - set(policy_ids))
    if missing:
        problems.append(
            "local_gate.sh reaches legs that gate-legs.txt does not classify: "
            f"{missing}\n    Add an IN_HOOK / COST / WAIVED row for each, with its mode. "
            "A leg nobody classified is a leg the hook silently does not run."
        )
    extra = sorted(set(policy_ids) - set(gate_ids))
    if extra:
        problems.append(
            f"gate-legs.txt classifies legs local_gate.sh no longer has: {extra}\n"
            "    Delete the rows, or restore the `# GATE-LEG:` marker in local_gate.sh."
        )

    # The MODE column, re-derived rather than read back. This is the check that
    # would have caught five COST rows claiming "Full gate only" for legs that
    # ran in `--fast` -- including a leg reaching a Trust toolchain outside this
    # repo, which made the documented pre-push command red for reasons no Clean
    # pusher caused.
    for row in rows:
        derived = regions.derived_mode(row["leg"])
        if derived is None:
            continue  # already reported as an unclassified/extra id above
        if derived != row["mode"]:
            where = (
                "inside a GATE-FULL-ONLY region"
                if derived == MODE_FULL
                else "outside every GATE-FULL-ONLY region"
            )
            problems.append(
                f"gate-legs.txt:{row['lineno']}: {row['leg']} declares mode={row['mode']!r} "
                f"but its `# GATE-LEG:` marker sits {where} in local_gate.sh, i.e. "
                f"mode={derived!r}.\n    Either move the leg, or correct the row. A row that "
                "says 'full gate only' about a leg the fast gate runs is how a red nobody "
                "caused reaches every push."
            )

    missing = sorted(set(runnable) - set(declared))
    if missing:
        problems.append(
            f"gate-legs.txt says the hook runs {missing}, and the hook does not declare them"
        )
    extra = sorted(set(declared) - set(runnable))
    if extra:
        problems.append(
            f"the hook declares {extra}, which gate-legs.txt does not mark IN_HOOK or WAIVED"
        )

    for leg in declared:
        fn = "leg_" + leg.replace("-", "_")
        if fn not in fns:
            problems.append(f"the hook declares {leg} but defines no {fn}()")

    for row in rows:
        if row["status"] == "WAIVED" and row["leg"] in DEBT_RATCHETS:
            problems.append(
                f"gate-legs.txt:{row['lineno']}: {row['leg']} is WAIVED, but a waiver passes "
                "whatever its leg measures -- any growth in any crate lands under it. Record the "
                f"growth as an owned, expiring debt capped at what was measured in "
                f"{DEBT_RATCHETS[row['leg']]}, and mark the row IN_HOOK."
            )

    today = date.today().isoformat()
    for row in rows:
        if row["status"] == "WAIVED" and row["expires"] < today:
            problems.append(
                f"gate-legs.txt:{row['lineno']}: the waiver for {row['leg']} expired on "
                f"{row['expires']} (owner {row['owner']}). Fix the leg or re-own the row."
            )

    # A waiver that local_gate.sh cannot act on is a waiver that does not apply
    # there: the leg still takes the whole gate down at its own line number.
    waivable_sites = {m.group(1) for m in
                      (WAIVABLE_CALL.match(line) for line in gate_text.splitlines())
                      if m is not None}
    waived_ids = {r["leg"] for r in rows if r["status"] == "WAIVED"}
    for leg in sorted(waived_ids - waivable_sites):
        problems.append(
            f"gate-legs.txt marks {leg} WAIVED, but local_gate.sh has no "
            f"`fail_waivable {leg} \"...\"` call site — so the leg still exits the whole "
            "gate on the spot and every later leg never runs. Convert its `fail` call."
        )
    for leg in sorted(waivable_sites - waived_ids):
        problems.append(
            f"local_gate.sh calls `fail_waivable {leg}` but gate-legs.txt has no WAIVED "
            f"row for {leg} — the call site outlived its waiver. It currently falls back "
            "to a hard `fail`, which is safe; restore the plain `fail` call so the code "
            "says what it does."
        )

    if update:
        if problems:
            print("REFUSING to re-pin while the tables disagree:", file=sys.stderr)
            for p in problems:
                print(f"  x {p}", file=sys.stderr)
            return 1
        PIN.write_text(
            json.dumps(
                {
                    "_comment": (
                        "Digests of scripts/local_gate.sh, split at its GATE-FULL-ONLY "
                        "markers (comments and blank lines stripped). BOTH halves are "
                        "pinned: pinning only the fast half meant the single edit that "
                        "changes a leg's mode -- moving it into a full-only region -- was "
                        "also the edit that stopped watching its body. Refreshed only by "
                        "`python3 scripts/check_hook_coverage.py --update`, and only when the "
                        "leg tables already agree. A moved digest means a leg changed and "
                        "its classification needs a human."
                    ),
                    "fast_region_sha256": digest,
                    "full_region_sha256": full_digest,
                    "hook_body_sha256": hook_digest,
                    "fast_leg_ids": regions.fast_ids,
                    "full_leg_ids": regions.full_ids,
                    "hook_leg_ids": declared,
                    "updated_utc_date": today,
                },
                indent=2,
            )
            + "\n"
        )
        print(f"hook coverage: re-pinned {PIN.relative_to(ROOT)} at {digest[:16]}...")
        return 0

    try:
        pinned = json.loads(_read(PIN))
    except (ValueError, Drift):
        problems.append(
            f"{PIN.relative_to(ROOT)} is missing or unparseable -- nothing pins the fast "
            "gate, so a new leg could land unclassified. Re-pin with "
            "`python3 scripts/check_hook_coverage.py --update`."
        )
        pinned = {}
    else:
        if pinned.get("hook_body_sha256") != hook_digest:
            problems.append(
                "the hook's leg DEFINITIONS moved (pinned "
                f"{str(pinned.get('hook_body_sha256'))[:16]}..., now {hook_digest[:16]}...).\n"
                "    Some leg now runs something different from what was reviewed -- the "
                "ids alone cannot see that.\n"
                "    Re-read the diff, then "
                "`python3 scripts/check_hook_coverage.py --update`."
            )
        if pinned.get("fast_region_sha256") != digest:
            problems.append(
                "local_gate.sh's FAST region moved (pinned "
                f"{str(pinned.get('fast_region_sha256'))[:16]}..., now {digest[:16]}...).\n"
                "    Some leg was added, changed or removed. Classify it in "
                "scripts/githooks/gate-legs.txt, teach the hook to run it if it is cheap, then\n"
                "    `python3 scripts/check_hook_coverage.py --update`."
            )
        if pinned.get("full_region_sha256") != full_digest:
            problems.append(
                "local_gate.sh's FULL-ONLY region moved (pinned "
                f"{str(pinned.get('full_region_sha256'))[:16]}..., now {full_digest[:16]}...).\n"
                "    A full-mode leg was added, changed or removed. It is not in the hook, "
                "but it is still a fail-closed gate leg;\n    re-read the diff, then "
                "`python3 scripts/check_hook_coverage.py --update`."
            )

    if problems:
        print("HOOK COVERAGE: FAIL — the pre-push hook no longer provably covers the gate.", file=sys.stderr)
        for p in problems:
            print(f"  x {p}", file=sys.stderr)
        return 1

    n_hook = len(declared)
    n_cost = sum(1 for r in rows if r["status"] == "COST")
    n_waived = sum(1 for r in rows if r["status"] == "WAIVED")
    print(
        f"  hook coverage: {n_hook} legs in the hook, {n_cost} excluded on cost, "
        f"{n_waived} waived; gate pinned at {digest[:12]}, hook bodies at {hook_digest[:12]}"
    )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main(sys.argv))
    except Drift as exc:
        print(f"HOOK COVERAGE: FAIL — {exc}", file=sys.stderr)
        raise SystemExit(1) from exc
