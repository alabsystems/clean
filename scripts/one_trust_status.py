#!/usr/bin/env python3
"""O1 v0 — the fused One Trust status page generator.

Renders docs/STATUS_ONE_TRUST.md ENTIRELY from machine-readable sources.
Every number on the page is read at generation time; the fixed prose carries
framing, the authority hierarchy, the claim-owning-command states (probed from
the filesystem), the JUNE-label retirement map (verbatim from the One Trust §2
CHANGE ledger), and pointers to the governing docs — never a number of its own.

Program doc: designs/2026-08-22-one-trust-backward-design.md §1 Layer O (O1)
and §2 ledger ("the fused status page (O1)"). Status authority, stated once:
G-SCORE's scoreboard and the committed probes are the number sources;
docs/CRYSTAL_STATUS.md remains the kernel-workstream page feeding them; this
fused page AGGREGATES — it never hand-carries a number.

A missing source is never silence: the section renders as UNKNOWN with a
reason and the generator still succeeds (R10 — a coverage number is only as
good as its producer; absence is reported, not invented).

Usage:
  one_trust_status.py             generate + write docs/STATUS_ONE_TRUST.md
  one_trust_status.py --check     exit 1 if the committed page differs from a
                                  fresh render (staleness detector; the
                                  generated-at line is masked, content is not)
  one_trust_status.py --self-test missing-source + staleness arms, exit 1 on
                                  any failure
"""

from __future__ import annotations

import argparse
import datetime as _dt
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
PAGE_REL = "docs/STATUS_ONE_TRUST.md"
UNKNOWN = "UNKNOWN"
GENERATED_PREFIX = "**Generated:**"

SOURCES = {
    "scoreboard": "data/spine_scoreboard.json",
    "env_bypass": "data/env_bypass_census.json",
    "unchecked_decl": "data/unchecked_decl_ratchet.json",
    "axiom_ratchet": "data/clean_verify_axiom_ratchet.json",
    "spine_set": "data/spine_set.json",
    "spine_set_pending": "data/spine_set.PENDING.md",
    "gate_legs": "scripts/githooks/gate-legs.txt",
    "program_one_trust": "designs/2026-08-22-one-trust-backward-design.md",
    "program_spine_lattice": "designs/2026-08-22-spine-and-lattice-program.md",
}

# The three claim-owning commands (One Trust §1 Layer E / D1 / D2 and Spine &
# Lattice S5). State is PROBED from scripts/ at generation time, never asserted.
COMMAND_PROBES = [
    ("supersession gate (D1)",
     ["scripts/supersession_gate.sh", "scripts/supersession_gate.py"]),
    ("revolution gate (D2)",
     ["scripts/revolution_gate.sh", "scripts/revolution_gate.py"]),
    ("spine_gate (S&L S5)",
     ["scripts/spine_gate.sh", "scripts/spine_gate.py"]),
]

# Verbatim from designs/2026-08-22-one-trust-backward-design.md §2 CHANGE:
JUNE_LEDGER_SENTENCE = (
    "June labels retired into live successors with the JUNE: prefix "
    "(JUNE:M-C1b→B3, JUNE:M-C7→B4, JUNE:M-NV→B6, JUNE:M-RATCHET→D2), "
    "tracked only on the fused page (O1)"
)
JUNE_MAP = [
    ("JUNE:M-C1b", "B3"),
    ("JUNE:M-C7", "B4"),
    ("JUNE:M-NV", "B6"),
    ("JUNE:M-RATCHET", "D2"),
]

GOVERNING_DOCS = [
    ("designs/2026-08-22-one-trust-backward-design.md",
     "One Trust — the ideal state, derived backward (ADOPTED design)"),
    ("designs/2026-08-22-spine-and-lattice-program.md",
     "Spine & Lattice — the kernel workstream, incorporated by reference"),
    ("docs/analysis/spine-lattice-recon-2026-08-22.md",
     "anchor provenance, clean side"),
    ("docs/analysis/one-trust-anchors-2026-08-22.md",
     "anchor provenance, trust side"),
]


def _load_json(path: Path):
    """Parsed JSON, or None if the file is absent/unreadable (fail-closed)."""
    try:
        with path.open(encoding="utf-8") as fh:
            return json.load(fh)
    except (OSError, json.JSONDecodeError):
        return None


def _git_head(repo_root: Path) -> str:
    try:
        out = subprocess.run(
            ["git", "-C", str(repo_root), "rev-parse", "--short", "HEAD"],
            capture_output=True, text=True, timeout=30, check=False)
        return out.stdout.strip() or UNKNOWN
    except OSError:
        return UNKNOWN


def _md_escape(value) -> str:
    return str(value).replace("|", "\\|").replace("\n", " ")


def _unknown_section(title: str, source_rel: str, reason: str) -> list[str]:
    return [
        f"## {title}",
        "",
        f"Source: `{source_rel}`",
        "",
        f"**{UNKNOWN}** — {reason}",
        "",
    ]


# ---------------------------------------------------------------- sections


def section_scoreboard(repo_root: Path) -> list[str]:
    """G-SCORE scoreboard — ALL rows, UNKNOWNs first-class with reasons."""
    title = "Scoreboard (G-SCORE) — the number source"
    src = SOURCES["scoreboard"]
    doc = _load_json(repo_root / src)
    if not isinstance(doc, dict) or not isinstance(doc.get("rows"), list):
        return _unknown_section(
            title, src,
            f"{src} absent or its 'rows' list is unreadable; regenerate with "
            "`scripts/spine_scoreboard.py` (the generator does not invent "
            "rows)")
    rows = [r for r in doc["rows"] if isinstance(r, dict)]
    unknown_count = sum(1 for r in rows if r.get("value") == UNKNOWN)
    lines = [
        f"## {title}",
        "",
        f"Source: `{src}` (generator `{doc.get('generator', UNKNOWN)}`, "
        f"scoreboard generated_at_utc `{doc.get('generated_at_utc', UNKNOWN)}`)",
        "",
        f"Rows: **{len(rows)}** ({unknown_count} UNKNOWN — first-class, "
        "never rounded to 0).",
        "",
        "| Row | Value | Direction | Reason (when UNKNOWN) |",
        "|---|---|---|---|",
    ]
    for r in rows:
        reason = r.get("reason", "") if r.get("value") == UNKNOWN else ""
        lines.append(
            f"| `{_md_escape(r.get('id', '?'))}` "
            f"| {_md_escape(r.get('value', UNKNOWN))} "
            f"| {_md_escape(r.get('direction', '?'))} "
            f"| {_md_escape(reason)} |")
    lines.append("")
    return lines


def section_env_bypass(repo_root: Path) -> list[str]:
    title = "Environment-bypass census (G-SCAN)"
    src = SOURCES["env_bypass"]
    doc = _load_json(repo_root / src)
    if not isinstance(doc, dict) or not isinstance(doc.get("rows"), list):
        return _unknown_section(
            title, src,
            f"{src} absent or its 'rows' list is unreadable — the bypass "
            "watch cannot be summarized from nothing")
    rows = [r for r in doc["rows"] if isinstance(r, dict)]
    site_records = sum(
        len(r["sites"]) for r in rows if isinstance(r.get("sites"), list))
    classes: dict[str, int] = {}
    for r in rows:
        key = str(r.get("classification", "unclassified"))
        classes[key] = classes.get(key, 0) + 1
    class_str = ", ".join(f"{k}: {v}" for k, v in sorted(classes.items()))
    lines = [
        f"## {title}",
        "",
        f"Source: `{src}` (scanner `{doc.get('scanner', UNKNOWN)}`, "
        f"last_updated `{doc.get('last_updated', UNKNOWN)}`)",
        "",
        f"- Census rows (watched method/site-classes): **{len(rows)}**",
        f"- Accounted production site records: **{site_records}**",
        f"- Classification breakdown: {class_str}",
        "",
    ]
    return lines


def section_unchecked_decl(repo_root: Path) -> list[str]:
    title = "Unchecked-declaration ratchet"
    src = SOURCES["unchecked_decl"]
    doc = _load_json(repo_root / src)
    if not isinstance(doc, dict):
        return _unknown_section(
            title, src, f"{src} absent or unreadable — bypass counts have no "
            "producer")
    ec = doc.get("extend_constants")
    ec = ec if isinstance(ec, dict) else {}

    def _count(value):
        return value if isinstance(value, int) else UNKNOWN

    lines = [
        f"## {title}",
        "",
        f"Source: `{src}` (last_updated `{doc.get('last_updated', UNKNOWN)}`; "
        "counts only go down)",
        "",
        f"- `add_decl_structural` production sites: "
        f"**{_count(doc.get('add_decl_structural_count'))}**",
        f"- `add_decl_unchecked` production sites: "
        f"**{_count(doc.get('add_decl_unchecked_count'))}**",
        f"- `extend_constants_unchecked` production sites: "
        f"**{_count(ec.get('unchecked_production_count'))}**",
        f"- `extend_constants_structural` production sites: "
        f"**{_count(ec.get('structural_production_count'))}**",
        "",
    ]
    return lines


def section_axiom_census(repo_root: Path) -> list[str]:
    title = "clean-verify axiom census"
    src = SOURCES["axiom_ratchet"]
    doc = _load_json(repo_root / src)
    if not isinstance(doc, dict):
        return _unknown_section(
            title, src, f"{src} absent or unreadable — the census has no "
            "producer (census stays a standing rule, not a rendered number)")
    tb = doc.get("_trust_breakdown")
    tb = tb if isinstance(tb, dict) else {}

    def _len_or_unknown(value):
        return len(value) if isinstance(value, list) else UNKNOWN

    origin = doc.get("origin_counts")
    origin_str = (", ".join(f"{k}: {v}" for k, v in origin.items())
                  if isinstance(origin, dict) else UNKNOWN)
    lines = [
        f"## {title}",
        "",
        f"Source: `{src}` (schema `{doc.get('_schema', UNKNOWN)}`, "
        f"last_updated `{doc.get('_last_updated', UNKNOWN)}`)",
        "",
        f"- Conservative census (every opaque env constant): "
        f"**{doc.get('count', UNKNOWN)}**",
        f"- Genuine foundational axioms: "
        f"**{tb.get('genuine_foundational_axiom_count', UNKNOWN)}**",
        f"- Quotient primitives (CIC type-formers, not axioms): "
        f"**{_len_or_unknown(tb.get('quotient_primitives_not_axioms'))}**",
        f"- Honesty tripwires (anti-trust markers): "
        f"**{_len_or_unknown(tb.get('honesty_tripwires_anti_trust'))}**",
        f"- Origin counts: {origin_str}",
        "",
    ]
    return lines


def section_spine_set(repo_root: Path) -> list[str]:
    title = "Spine set (Claim S quantifier domain)"
    src = SOURCES["spine_set"]
    pending_rel = SOURCES["spine_set_pending"]
    minted = _load_json(repo_root / src)
    pending_exists = (repo_root / pending_rel).exists()
    lines = [
        f"## {title}",
        "",
        f"Source: `{src}` (minted artifact) / `{pending_rel}` "
        "(recorded absence)",
        "",
    ]
    if isinstance(minted, (dict, list)):
        members = (minted.get("members")
                   if isinstance(minted, dict) else minted)
        size = len(members) if isinstance(members, list) else UNKNOWN
        lines += [f"State: **MINTED** — `{src}` present, members: **{size}**.",
                  ""]
        if pending_exists:
            lines += [f"Note: `{pending_rel}` still present alongside the "
                      "minted artifact — the pending marker owes a deletion.",
                      ""]
    elif pending_exists:
        lines += [
            f"State: **PENDING** — `{src}` is not yet minted; the recorded "
            f"state (not silence) is `{pending_rel}`: the post-a5aae3bde "
            "whole-crate dump is owed from the trust host, and the "
            "derivation fails closed rather than emit a partial spine set.",
            "",
        ]
    else:
        lines += [
            f"State: **{UNKNOWN}** — neither `{src}` nor `{pending_rel}` "
            "exists; the absence itself is unrecorded, which is a gap "
            "(recorded state, not silence, is the rule).",
            "",
        ]
    return lines


def section_gate_legs(repo_root: Path) -> list[str]:
    title = "Pre-push hook leg policy"
    src = SOURCES["gate_legs"]
    path = repo_root / src
    try:
        text = path.read_text(encoding="utf-8")
    except OSError:
        return _unknown_section(
            title, src, f"{src} absent or unreadable — the leg policy table "
            "has no producer")
    counts = {"IN_HOOK": 0, "COST": 0, "WAIVED": 0}
    other = 0
    for line in text.splitlines():
        stripped = line.strip()
        if not stripped or stripped.startswith("#"):
            continue
        status = stripped.split("|", 1)[0].strip()
        if status in counts:
            counts[status] += 1
        else:
            other += 1
    total = sum(counts.values()) + other
    lines = [
        f"## {title}",
        "",
        f"Source: `{src}` (rows counted from the table body, never from its "
        "header comments)",
        "",
        f"- Legs total: **{total}**",
        f"- IN_HOOK (run + block): **{counts['IN_HOOK']}**",
        f"- COST (excluded from the HOOK, measured cost recorded; the row's "
        f"MODE column says whether local_gate.sh --fast still runs it): "
        f"**{counts['COST']}**",
        f"- WAIVED (run, printed, non-blocking, owned + dated): "
        f"**{counts['WAIVED']}**",
    ]
    if other:
        lines.append(f"- Unrecognized status rows: **{other}** (a fourth "
                     "status does not exist — this is a parse alarm)")
    lines.append("")
    return lines


def section_program_docs(repo_root: Path) -> list[str]:
    title = "Program docs"
    entries = [
        ("One Trust backward design", SOURCES["program_one_trust"]),
        ("Spine & Lattice program", SOURCES["program_spine_lattice"]),
    ]
    lines = [
        f"## {title}",
        "",
        "Source: filesystem existence of the two program docs, probed at "
        "generation time",
        "",
    ]
    for name, rel in entries:
        state = "present" if (repo_root / rel).exists() else (
            f"{UNKNOWN} — ABSENT (the program doc is missing from the tree)")
        lines.append(f"- {name}: `{rel}` — **{state}**")
    lines.append("")
    return lines


def section_commands(repo_root: Path) -> list[str]:
    lines = [
        "## Claim-owning commands",
        "",
        "Source: filesystem probe of `scripts/` at generation time — a claim "
        "is owned by a command, never by a sentence (One Trust §1 Layer E, "
        "per R7). A command probed ABSENT owns nothing yet; its claim is "
        "therefore unmade.",
        "",
        "| Command | Probed paths | State |",
        "|---|---|---|",
    ]
    for name, candidates in COMMAND_PROBES:
        hits = [c for c in candidates if (repo_root / c).exists()]
        state = (f"**built** (`{hits[0]}`)" if hits
                 else "**not yet built** (absent)")
        probed = ", ".join(f"`{c}`" for c in candidates)
        lines.append(f"| {name} | {probed} | {state} |")
    lines.append("")
    return lines


def section_june_map() -> list[str]:
    lines = [
        "## JUNE-label retirement map",
        "",
        "Verbatim from the One Trust §2 CHANGE ledger "
        "(designs/2026-08-22-one-trust-backward-design.md): "
        f"\u201c{JUNE_LEDGER_SENTENCE}\u201d. This page is that tracking.",
        "",
        "| Retired June label | Live successor |",
        "|---|---|",
    ]
    for old, new in JUNE_MAP:
        lines.append(f"| `{old}` | {new} |")
    lines.append("")
    return lines


def section_governing_docs(repo_root: Path) -> list[str]:
    lines = [
        "## Governing docs",
        "",
    ]
    for rel, role in GOVERNING_DOCS:
        state = "" if (repo_root / rel).exists() else " — **ABSENT**"
        lines.append(f"- [`{rel}`]({Path('..') / rel}) — {role}{state}")
    lines.append("")
    return lines


# ------------------------------------------------------------------ render


def render(repo_root: Path) -> str:
    now = _dt.datetime.now(_dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    head = _git_head(repo_root)
    lines = [
        "# One Trust — fused status (O1, v0)",
        "",
        "> GENERATED FILE — do not hand-edit. Every number below was read "
        "from a machine-readable source at generation time; edits belong in "
        "the sources or in `scripts/one_trust_status.py`.",
        "",
        f"{GENERATED_PREFIX} {now} at `{head}`",
        "",
        "**Regenerate:** `/opt/homebrew/bin/python3.14 "
        "scripts/one_trust_status.py` · **Staleness check:** "
        "`/opt/homebrew/bin/python3.14 scripts/one_trust_status.py --check`",
        "",
        "## Authority hierarchy",
        "",
        "Status authority, stated once (One Trust §1 Layer O, O1): "
        "**G-SCORE's scoreboard (`data/spine_scoreboard.json`) and the "
        "committed probes are the number sources; `docs/CRYSTAL_STATUS.md` "
        "remains the kernel-workstream page feeding them; this fused page "
        "AGGREGATES — it never hand-carries a number.** A value this page "
        "cannot read from a source renders as UNKNOWN with its reason, "
        "never as a guess; UNKNOWN is first-class and is never rounded up.",
        "",
    ]
    lines += section_commands(repo_root)
    lines += section_scoreboard(repo_root)
    lines += section_spine_set(repo_root)
    lines += section_env_bypass(repo_root)
    lines += section_unchecked_decl(repo_root)
    lines += section_axiom_census(repo_root)
    lines += section_gate_legs(repo_root)
    lines += section_program_docs(repo_root)
    lines += section_june_map()
    lines += section_governing_docs(repo_root)
    lines += [
        "---",
        "",
        "Footer: `--check` (staleness detector) is deliberately NOT wired "
        "into any gate yet — wiring: follow-up.",
        "",
    ]
    return "\n".join(lines)


def _mask_generated_line(text: str) -> str:
    """Mask the volatile generated-at line so --check compares content."""
    return re.sub(
        rf"^{re.escape(GENERATED_PREFIX)}.*$", f"{GENERATED_PREFIX} <masked>",
        text, count=1, flags=re.MULTILINE)


def check_stale(repo_root: Path) -> int:
    page = repo_root / PAGE_REL
    try:
        committed = page.read_text(encoding="utf-8")
    except OSError:
        print(f"one_trust_status --check: STALE — {PAGE_REL} does not exist; "
              "generate it")
        return 1
    fresh = render(repo_root)
    if _mask_generated_line(committed) == _mask_generated_line(fresh):
        print(f"one_trust_status --check: OK — {PAGE_REL} matches a fresh "
              "render (generated-at line masked)")
        return 0
    committed_lines = _mask_generated_line(committed).splitlines()
    fresh_lines = _mask_generated_line(fresh).splitlines()
    first_diff = next(
        (i for i, (a, b) in enumerate(zip(committed_lines, fresh_lines))
         if a != b),
        min(len(committed_lines), len(fresh_lines)))
    print(f"one_trust_status --check: STALE — {PAGE_REL} differs from a "
          f"fresh render (first difference at line {first_diff + 1}); "
          "regenerate with scripts/one_trust_status.py")
    return 1


# ---------------------------------------------------------------- self-test


def self_test() -> int:
    failures = []

    def expect(name, cond, detail=""):
        status = "ok" if cond else "FAIL"
        print(f"self-test: {name}: {status}{(' — ' + detail) if detail else ''}")
        if not cond:
            failures.append(name)

    # Arm 1: every source absent — every section renders UNKNOWN/absent with
    # a reason, and the generator still succeeds.
    with tempfile.TemporaryDirectory() as tmp:
        empty = Path(tmp)
        try:
            text = render(empty)
            rendered = True
        except Exception as exc:  # noqa: BLE001 — the arm asserts no raise
            rendered = False
            text = f"render raised: {exc!r}"
        expect("missing_sources_generator_succeeds", rendered, text[:120])
        if rendered:
            expect("missing_scoreboard_unknown",
                   "data/spine_scoreboard.json absent" in text)
            expect("missing_env_bypass_unknown",
                   "data/env_bypass_census.json absent" in text)
            expect("missing_unchecked_decl_unknown",
                   "data/unchecked_decl_ratchet.json absent" in text)
            expect("missing_axiom_census_unknown",
                   "data/clean_verify_axiom_ratchet.json absent" in text)
            expect("missing_gate_legs_unknown",
                   "scripts/githooks/gate-legs.txt absent" in text)
            expect("missing_spine_set_reported_unknown",
                   "the absence itself is unrecorded" in text)
            expect("missing_program_docs_absent",
                   "ABSENT (the program doc is missing" in text)
            expect("commands_probe_absent_when_no_scripts",
                   text.count("**not yet built** (absent)") == len(COMMAND_PROBES))
            expect("unknown_sections_carry_reasons",
                   f"**{UNKNOWN}** — " in text)

    # Arm 2: spine_set PENDING marker alone -> PENDING state, with a reason.
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        (root / "data").mkdir()
        (root / "data" / "spine_set.PENDING.md").write_text(
            "# pending\n", encoding="utf-8")
        text = "\n".join(section_spine_set(root))
        expect("spine_set_pending_state", "State: **PENDING**" in text)

    # Arm 3: spine_set minted -> MINTED with member count read from the file.
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        (root / "data").mkdir()
        (root / "data" / "spine_set.json").write_text(
            json.dumps({"members": [{"body": "a"}, {"body": "b"}]}),
            encoding="utf-8")
        text = "\n".join(section_spine_set(root))
        expect("spine_set_minted_counts_members",
               "State: **MINTED**" in text and "members: **2**" in text)

    # Arm 4: --check staleness detection, in a scratch repo layout.
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        (root / "docs").mkdir()
        page = root / PAGE_REL
        # 4a: no committed page -> stale.
        expect("check_missing_page_is_stale", check_stale(root) == 1)
        # 4b: fresh page -> OK.
        page.write_text(render(root), encoding="utf-8")
        expect("check_fresh_page_ok", check_stale(root) == 0)
        # 4c: timestamp-only difference stays OK (the volatile line is masked).
        aged = re.sub(
            rf"^{re.escape(GENERATED_PREFIX)}.*$",
            f"{GENERATED_PREFIX} 1970-01-01T00:00:00Z at `0000000`",
            page.read_text(encoding="utf-8"), count=1, flags=re.MULTILINE)
        page.write_text(aged, encoding="utf-8")
        expect("check_timestamp_only_diff_ok", check_stale(root) == 0)
        # 4d: a content edit -> stale.
        page.write_text(
            page.read_text(encoding="utf-8").replace(
                "## Authority hierarchy", "## Authority hierarchy (edited)"),
            encoding="utf-8")
        expect("check_content_edit_is_stale", check_stale(root) == 1)
        # 4e: a source moving under a committed page -> stale.
        page.write_text(render(root), encoding="utf-8")
        (root / "data").mkdir()
        (root / "data" / "spine_set.PENDING.md").write_text(
            "# pending\n", encoding="utf-8")
        expect("check_source_move_is_stale", check_stale(root) == 1)

    if failures:
        print(f"self-test: FAIL ({len(failures)} arm(s)): "
              f"{', '.join(failures)}")
        return 1
    print("self-test: PASS (all arms)")
    return 0


# --------------------------------------------------------------------- main


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--check", action="store_true",
                        help="exit 1 if the committed page differs from a "
                             "fresh render")
    parser.add_argument("--self-test", action="store_true",
                        help="run the missing-source and staleness arms")
    args = parser.parse_args(argv)

    if args.self_test:
        return self_test()
    if args.check:
        return check_stale(REPO_ROOT)

    out_path = REPO_ROOT / PAGE_REL
    text = render(REPO_ROOT)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(text, encoding="utf-8")
    unknown_sections = text.count(f"**{UNKNOWN}** — ")
    print(f"one_trust_status: generated -> {PAGE_REL} "
          f"({unknown_sections} section(s) UNKNOWN, first-class)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
