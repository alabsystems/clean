#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Read the self-proof evidence and show the fleet which gates and proof obligations are open."""

import argparse
from datetime import date
import gzip
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

from self_proof_fleet_evidence import (
    PR29_REPORT, census_progress, displayed_events, event_units, execution_receipts, read_const_trial, read_export_evidence,
    native_matcher_text, read_soundness_quorum, read_soundness_quorum_history, read_source_qualification, source_event,
)
from self_proof_fleet_w0 import saved_board_refusal

ROOT = Path(__file__).resolve().parents[1]
PLAN = "docs/plans/SELF_PROOF_EXECUTION_PLAN_2026-11-12.md"
CATALOG = "data/self_proof_fleet_obligations.json"
TIMELINE = "data/self_proof_fleet_timeline.json"
REPORT = "reports/self-proof-root-export-2026-11-17/source-fidelity"
C3 = "reports/c3-complete-sound-2026-11-15/current-main-qualification/qualification.json"
C3_RECEIPT_REVISION = "14e413fd9ead0a0ca0aa131cb0b9d65310320036"
# Published bytes of the frozen two-kernel run. A later run gets its own evidence.
C3_FILES = {
    "qualification.json": "feca37ec6237a6d6f99c4d5cb482e47f172c8e9271df60c080ebff7534fa1603",
    "canonical.log.gz": "41022105eec6b5c3acdd8706d3f2f730fbb4f6d44f340ffb4be4f79206fc8d79",
    "executed-binary.json": "cc74046f58f2bcffdcd46f00663d0cb9d63b1454f2a92ba11c03a655c9aeaaa0",
    "executed-kcheck-labelled.bin.gz": "f691d252f91973e685538af3eb87792db20c9008b5490ec5e3b69250aef3d8b4",
    "qualified-inputs.json": "bc495837b4a702dd0661802562c69c7d8a937de71a5e4497884ed7e13d694864",
}
SCHEMA = "clean-self-proof-fleet-v1"


def read_json(path):
    if path.suffix == ".gz":
        try:
            with gzip.open(path, "rt", encoding="utf-8") as f:
                return json.load(f)
        except EOFError as e:
            raise ValueError(f"truncated gzip archive: {path}") from e
    return json.loads(path.read_text(encoding="utf-8"))


def timeline(document, unit=None):
    if document.get("schema") != "clean.self_proof_fleet_timeline.v1":
        raise ValueError("unsupported timeline schema")
    last_date = ""
    selected = []
    for event in document["events"]:
        when = event["date"]
        if date.fromisoformat(when).isoformat() != when or when < last_date:
            raise ValueError(f"invalid or unordered timeline date {when}")
        last_date = when
        if event["kind"] not in {"decision", "proof", "wiring", "measurement", "blocker"}:
            raise ValueError(f"unknown timeline category {event['kind']}")
        if "input_sha256" in event and not (
            isinstance(event["input_sha256"], str) and re.fullmatch(r"[0-9a-f]{64}", event["input_sha256"])
        ):
            raise ValueError(f"invalid timeline input SHA-256 on {when}")
        if "qualification_sha256" in event and not (isinstance(event["qualification_sha256"], str)
                and re.fullmatch(r"[0-9a-f]{64}", event["qualification_sha256"])):
            raise ValueError(f"invalid timeline qualification SHA-256 on {when}")
        source = Path(event["source"].split("#", 1)[0])
        if source.is_absolute() or ".." in source.parts or not source.parts:
            raise ValueError(f"expected a repository source for the {when} event")
        if not event["unit"] or not event["summary"].strip():
            raise ValueError(f"incomplete timeline event on {when}")
        units = event_units(event)
        if unit is None or unit in units:
            selected.append(event)
    return selected


def recorded_events(root, unit=None):
    try:
        return timeline(read_json(root / TIMELINE), unit)
    except FileNotFoundError:
        return []


def followup_results(root, events):
    from self_proof_fleet_evidence import (read_console_replay, read_followup,
                                          read_native_init_slice, read_native_matcher, read_w3_digest_library)
    results = {}
    library = [event for event in events if event["unit"] == "W3" and event["kind"] == "measurement"
               and event.get("measurement") == "digest-library"]
    if len(library) == 1:
        reading = read_w3_digest_library(root, library[0])
        if reading:
            results["W3-digest-library"] = reading
    for key in ("PR-30", "PR-31"):
        rows = [event for event in events if event["unit"] == key and event["kind"] == "measurement"]
        if len(rows) == 1:
            result = read_followup(root, rows[0])
            if result:
                results[key] = result
    console = [event for event in events if event["unit"] == "W6" and event["kind"] == "measurement"
               and "PR-32" in event.get("related_obligations", [])]
    if len(console) == 1:
        result = read_console_replay(root, console[0])
        if result:
            results["PR-32"] = result
    for key, reader in (("PR-49", read_native_init_slice), ("PR-67", read_native_matcher)):
        matches = [event for event in events if event["unit"] == key and event["kind"] == "measurement"]
        if len(matches) == 1:
            result = reader(root, matches[0])
            if result:
                results[key] = result
    return results


def unit_history(unit=None):
    events = recorded_events(ROOT, unit)
    adoption = source_event(events)
    current = read_source_qualification(ROOT / PR29_REPORT, adoption) if adoption else None
    return displayed_events(events, current, followup_results(ROOT, events),
                            read_soundness_quorum_history(ROOT, events, current), receipts=execution_receipts(ROOT, events))


def render_events(events):
    for event in events:
        source = event["source"]
        if "source_revision" in event:
            revision = event["source_revision"]
            if isinstance(revision, str) and re.fullmatch(r"[0-9a-f]{40}", revision):
                source += f" (Clean {revision})"
            else:
                source += " (invalid source revision)"
        print(f"{event['date']}  {event['kind']}  {event['unit']}\n  {event['summary']}\n  {source}")


def catalog(rows):
    """Refuse ambiguous identifiers, unknown units and cyclic dependencies."""
    by_id = {}
    for row in rows:
        key = row["id"]
        if not isinstance(key, str) or not key or key in by_id:
            raise ValueError(f"invalid or duplicate unit {key!r}")
        if row["kind"] not in {"proof", "wiring", "evidence", "external"}:
            raise ValueError(f"{key} has an unknown work kind")
        for field in ("goal", "closes_with", "source"):
            if not isinstance(row[field], str) or not row[field].strip():
                raise ValueError(f"{key} needs {field}")
        deps = row["prerequisites"]
        if not isinstance(deps, list) or len(set(deps)) != len(deps):
            raise ValueError(f"{key} has malformed prerequisites")
        by_id[key] = row
    visited = set()

    def visit(key, active):
        if key in active:
            raise ValueError(f"dependency cycle at {key}")
        if key not in by_id:
            raise ValueError(f"unknown prerequisite {key}")
        if key in visited:
            return
        for dep in by_id[key]["prerequisites"]:
            visit(dep, active | {key})
        visited.add(key)

    for key in by_id:
        visit(key, set())
    return by_id


def plan_claims(text):
    """Read the current Claims table. Historical narrative below it is outside the table."""
    heading = "| Units | Claimed by | Since |"
    start = text.index(heading, text.index("## 9. Claims"))
    result = []
    for line in text[start:].splitlines()[2:]:
        if not line.startswith("|"):
            break
        cols = line.strip().strip("|").split("|")
        if len(cols) != 3:
            raise ValueError("malformed row in Claims table")
        task, owner, since = (c.strip() for c in cols)
        # A release at the start of the owner cell closes the whole claim.
        # Later prose can describe releasing just one part of an active task.
        if re.search(r"claim released|^complete\b|^released(?: by [\w-]+)?(?:\.(?=\s|$)|$)", owner, re.I):
            continue
        result.append({"task": task, "owner": owner, "since": since})
    return result


def claims_for(units, claims):
    if not units:
        return []
    # Match the task label at the start of the cell, including compound W1/E4/X2
    # and labels such as "Lane A A1.1". Mentions later in prose are not claims.
    if isinstance(units, str):
        units = [units]
    token = re.compile(r"(?<![\w.])(?:" + "|".join(map(re.escape, units)) + r")(?![\w.])")
    found = []
    for claim in claims:
        label = re.match(r"^(?:Lane\s+[A-Z]\s+)?[A-Za-z0-9.]+(?:[/,–-][A-Za-z0-9.]+)*", claim["task"])
        if label and token.search(label[0]):
            found.append(claim)
    return found


def c3_snapshot(root):
    folder = (root / C3).parent
    try:
        files = {name: (folder / name).read_bytes() for name in C3_FILES}
        if all(hashlib.sha256(files[name]).hexdigest() == digest for name, digest in C3_FILES.items()):
            row = json.loads(files["qualification.json"])
            executed = json.loads(files["executed-binary.json"])
            inputs = json.loads(files["qualified-inputs.json"])
            if (row["qualified_source"] == executed["executed_source"] == inputs["head"]
                    and row["input_files"] == len(inputs["inputs"]) and row["exit_code"] == 0):
                return {"state": "qualified_snapshot", "revision": row["qualified_source"],
                        "receipt_revision": C3_RECEIPT_REVISION, "source": C3}
    except (OSError, ValueError, TypeError, KeyError):
        pass
    return {"state": "unverified", "source": C3}


def minimal_metrics(board):
    head, route = board["headline"], board["route"]
    counted = route["accepted_by_kcheck_no_site"]
    return {
        "production": head["decided_by_compiled_kcheck"],
        "fragment": {k: v for k, v in counted.items() if k != "accepted_declarations"},
        "planted_false_clean": head["planted_false_mints_clean"],
        "planted_false_trust": head["planted_false_mints_trust"],
        "islands": route["island_gaps"],
        "rule_families": route["lean_kernel_rule_families"],
    }


def verify_w0_shadow(root, executable, board):
    from self_proof_scoreboard import serialize

    result = subprocess.run(
        [str(executable.resolve()), "evidence", "status", "--scoreboard", "--json",
         "--repo-root", str(root.resolve())],
        cwd=root, stdin=subprocess.DEVNULL, capture_output=True, timeout=60,
    )
    if result.returncode or result.stderr:
        diagnostic = result.stderr.decode("utf-8", errors="replace").strip()
        raise ValueError(f"native W0 shadow failed with exit {result.returncode}\n{diagnostic}")
    if result.stdout != serialize(board).encode("utf-8"):
        raise ValueError("native W0 shadow stdout differs from the canonical Python board")


def decode_native_w0(raw):
    """Accept only a canonical W0 board with the rows and counts the fleet reads."""
    try:
        board = json.loads(raw.decode("utf-8"))
        canonical = json.dumps(board, indent=2, sort_keys=True, allow_nan=False) + "\n"
    except (ValueError, RecursionError) as error:
        raise ValueError(f"invalid native W0 JSON ({error})") from error
    if raw != canonical.encode("utf-8"):
        raise ValueError("native W0 stdout is not canonical JSON")
    if (not isinstance(board, dict) or set(board) != {"schema", "what_this_is", "headline", "route"}
            or board["schema"] != "clean.self_proof_scoreboard.v1"
            or not isinstance(board["what_this_is"], str)):
        raise ValueError("native W0 stdout has an invalid scoreboard envelope")
    counts = {
        "headline": {
            "decided_by_compiled_kcheck": ("real_declarations_decided",),
            "planted_false_mints_clean": ("minted_under_mutant", "sites"),
            "planted_false_mints_trust": ("minted_under_mutant", "sites"),
        },
        "route": {
            "accepted_by_kcheck_no_site": ("accepted", "inside_fragment", "ordinary_declarations"),
            "checker_soundness": (),
            "clean_elaborates_theories": ("elaborated", "modules"),
            "island_gaps": ("open", "rows"),
            "lean_kernel_rule_families": ("specified", "partial", "unspecified", "families"),
        },
    }
    for section, fields in counts.items():
        rows = board[section]
        if not isinstance(rows, dict) or rows.keys() != fields.keys():
            raise ValueError(f"native W0 stdout has invalid {section} rows")
        for name, numbers in fields.items():
            row = rows[name]
            if isinstance(row, dict) and row:
                if "absent" in row:
                    if row.keys() == {"absent"} and isinstance(row["absent"], str) and row["absent"]:
                        continue
                elif all(type(row.get(key)) is int and row[key] >= 0 for key in numbers):
                    continue
            raise ValueError(f"native W0 stdout has an invalid {name} row")
    return board


def read_w0(root, *, shadow_w0=None, native_w0=None):
    if native_w0 is not None:
        if shadow_w0 is not None:
            raise ValueError("select one W0 mode")
        from self_proof_fleet_w0 import run_pinned_w0_json

        raw = run_pinned_w0_json(native_w0, git_root=ROOT, data_root=root)
        board = decode_native_w0(raw)
        canonical = raw.decode("utf-8")
    else:
        from self_proof_scoreboard import derive, serialize

        board = derive(root)
        if shadow_w0 is not None:
            verify_w0_shadow(root, shadow_w0, board)
        canonical = serialize(board)
    return board, saved_board_refusal(root, canonical)


def snapshot(root=ROOT, report_dir=None, *, shadow_w0=None, native_w0=None, defer_native_w0=False):
    rows = catalog(read_json(root / CATALOG))
    claims = plan_claims((root / PLAN).read_text(encoding="utf-8"))
    try:
        board, warning = read_w0(root, shadow_w0=shadow_w0, native_w0=native_w0)
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        if native_w0 is None or not defer_native_w0:
            raise
        board, warning = None, str(error)
    export = read_export_evidence(report_dir or root / REPORT)
    events = recorded_events(root)
    trial_events = [row for row in events if row["unit"] == "PR-28"]
    adoption = source_event(events)
    current = read_source_qualification(root / PR29_REPORT, adoption) if adoption else None
    trial = (read_const_trial(root / "reports/self-proof-const-branch-trial", trial_events[-1], export)
             if trial_events else None)
    seed = c3_snapshot(root)
    metrics = minimal_metrics(board) if board is not None else {}
    state = {key: "needs_gate_evidence" for key in rows}
    if "C3" in state:
        state["C3"] = seed["state"]
    fragment = metrics.get("fragment", {})
    if (not warning and type(fragment.get("accepted")) is int and fragment["accepted"] > 0
            and type(fragment.get("inside_fragment")) is int
            and fragment["accepted"] <= fragment["inside_fragment"]):
        state["C4-C5"] = "bounded_evidence"
    if export["state"] == "measured":
        state["Q1"] = "qualified_snapshot"
        state["self-admission-prefix"] = "qualified_snapshot"
        state["self-admission"] = "measured_refusal" if export.get("first_refusal") else "needs_gate_evidence"
    else:
        for key in ("Q1", "self-admission-prefix", "self-admission"):
            state[key] = "unverified"
    units = []
    for key, row in rows.items():
        deps = row["prerequisites"]
        units.append({**row, "status": state[key],
                      "waiting_on": [d for d in deps if state[d] != "qualified_snapshot"],
                      "recorded_claims": claims_for(row.get("claim_unit"), claims)})
    followups = followup_results(root, events)
    quorum_history = read_soundness_quorum_history(root, events, current)
    return {"schema": SCHEMA, "scoreboard_warning": warning, "metrics": metrics,
            "c3": seed, "literal_export": export, "const_helper_trial": trial, "source_qualification": current,
            "followups": followups, "console_replay": followups.get("PR-32"), "units": units,
            "soundness_root_quorum": quorum_history[-1] if quorum_history else None,
            "soundness_root_quorum_history": quorum_history,
            "execution_receipts": execution_receipts(root, events)}


def ready_units(rows):
    """Select open Clean work whose prerequisites have a qualifying result."""
    return [row for row in rows if row["kind"] != "external"
            and not row["waiting_on"] and row["status"] != "qualified_snapshot"]


def metric_observation(key, row):
    if "absent" in row:
        return "unverified (" + str(row["absent"]) + ")"
    fields = {
        "production": ("real_declarations_decided",),
        "fragment": ("accepted", "inside_fragment", "ordinary_declarations"),
        "planted_false_clean": ("minted_under_mutant", "sites"),
        "planted_false_trust": ("minted_under_mutant", "sites"),
        "islands": ("open", "rows"),
        "rule_families": ("specified", "partial", "unspecified", "families"),
    }
    return ", ".join(f"{name}={row.get(name, 'unverified')}" for name in fields[key])


def change_summary(old, now):
    if not isinstance(old, dict) or old.get("schema") != SCHEMA:
        raise ValueError("previous snapshot uses a different schema")
    changes = []
    for key, value in now["metrics"].items():
        previous = old["metrics"].get(key)
        if previous != value:
            before_value = metric_observation(key, previous or {})
            after_value = metric_observation(key, value)
            if before_value == after_value:
                changes.append(f"{key}: evidence or provenance changed, counts unchanged ({after_value})")
            else:
                changes.append(f"{key}: {before_value} -> {after_value}")
    before, after = old["literal_export"], now["literal_export"]
    if before.get("state") != after.get("state") and "unverified" in (before.get("state"), after.get("state")):
        changes.append(f"literal replay evidence: {before.get('state')} -> {after.get('state')}; no comparable prefix counts")
    elif (before.get("sha256") != after.get("sha256") or
            before.get("root") != after.get("root")):
        changes.append("literal export changed; prefix counts have different input bytes")
    elif (before.get("prefix_accepted"), before.get("first_refusal"), before.get("state")) != (
            after.get("prefix_accepted"), after.get("first_refusal"), after.get("state")):
        changes.append(f"literal replay on the same bytes: {before.get('prefix_accepted', 'unverified')} -> "
                       f"{after.get('prefix_accepted', 'unverified')} consecutive admissions; first refusal {after.get('first_refusal')}")
    trial = now.get("const_helper_trial") or {}
    prior_trial = old.get("const_helper_trial") or {}
    # Earlier snapshots of the same PR-28 exit did not expose the original stock counts.
    trial_keys = ("state", "reason", "result_sha256", "input_sha256", "baseline_input_sha256",
                  "stock_admitted", "named", "root", "root_accepted")
    if any(trial.get(key) != prior_trial.get(key) for key in trial_keys):
        if trial.get("state") == "recorded":
            changes.append(f"PR-28 experimental stock ck0 vote on candidate {trial['input_sha256']}: "
                           f"{trial['stock_admitted']} of {trial['named']} names admitted, including {trial['root']}. "
                           f"Baseline {trial['baseline_input_sha256']}. Receipt {trial['result_sha256']}.")
        else:
            reason = trial.get("reason", "no candidate receipt in the snapshot")
            changes.append(f"PR-28 experimental stock ck0 vote unavailable ({reason}).")
    if old.get("source_qualification") != now.get("source_qualification"):
        current = now.get("source_qualification") or {}
        if current.get("state") == "qualified":
            changes.append(_qualification_text(current))
        else:
            changes.append(f"PR-29 source qualification unavailable ({current.get('reason', 'no qualified snapshot')}).")
    previous_quorum = old.get("soundness_root_quorum") or {}
    quorum = now.get("soundness_root_quorum") or {}
    if quorum.get("source_revision") != previous_quorum.get("source_revision"):
        changes.append(_quorum_text(quorum) if quorum else
                       "The frozen Q4 soundness-root receipt is unavailable in this snapshot.")
    previous_followups = old.get("followups", {})
    for key, reading in now.get("followups", {}).items():
        if previous_followups.get(key) == reading:
            continue
        if key == "PR-30":
            for subject in ("current", "historical"):
                result = reading[subject]
                changes.append(f"PR-30 {subject} export {result['input_sha256']} admitted "
                               f"{result['accepted_records']} of {result['declaration_records']} records "
                               f"and stopped at {result['first_refusal']} on line {result['line']}.")
        elif key == "PR-31":
            changes.append(f"PR-31 checked {reading['edges_checked']} constant references from the "
                           f"unchanged statement to {', '.join(reading['targets'])}.")
        elif key == "PR-32":
            changes.append(f"PR-32 executed the genuine Init println module {reading['module_digest']} and "
                           f"matched {reading['stdout_bytes']} bytes from Lean. Two-action sequencing stopped at "
                           f"{reading['pair_refusal']}.")
        elif key == "PR-49":
            changes.append(f"PR-49 admitted {reading['accepted']} of {reading['target_declarations']} "
                           "original named Init declarations using native advice and the interim checker.")
        elif key == "PR-67":
            changes.append(native_matcher_text(reading))
    for key in sorted(previous_followups.keys() - now.get("followups", {}).keys()):
        changes.append(f"{key} qualification is unavailable in this snapshot.")
    if old.get("c3") != now.get("c3"):
        old_c3, new_c3 = old.get("c3", {}), now.get("c3", {})
        changes.append(f"C3 qualification: {old_c3.get('revision', 'unverified')} -> {new_c3.get('revision', 'unverified')}")
    previous_units = {r["id"]: r for r in old["units"]}
    for row in now["units"]:
        prior = previous_units.get(row["id"], {})
        if prior.get("status") != row["status"] or prior.get("waiting_on") != row["waiting_on"]:
            changes.append(f"{row['id']}: {prior.get('status', 'new')} -> {row['status']}; open prerequisites {row['waiting_on']}")
        if prior.get("recorded_claims", []) != row["recorded_claims"]:
            changes.append(f"{row['id']}: recorded claims changed")
    for removed in sorted(previous_units.keys() - {r["id"] for r in now["units"]}):
        changes.append(f"{removed}: removed from the catalog")
    return changes


def _qualification_text(current):
    return (f"PR-29 qualified Clean source {current['qualified_revision']}: pinned Lean, fenced Clean and stock ck0 "
            f"each admitted {current['stock_admitted']} of {current['declarations']} names including {current['root']}. "
            f"Resident comparison matched {current['resident_equal']} of {current['declarations']}. "
            f"The adopted checker admitted {current['prefix_accepted']} consecutive records out of {current['records']}, "
            f"then refused {current['first_refusal']['name']} at line {current['first_refusal']['line']}. "
            f"PR-29 recorded no qualified Lean4Lean vote. Input SHA-256 {current['input_sha256']}. "
            f"Qualification SHA-256 {current['qualification_sha256']}.")


def _quorum_text(quorum):
    when = f" on {quorum['date']}" if quorum.get("date") else ""
    return (f"Q4{when} recorded 4/4 independent acceptances, including qualified Lean4Lean, "
            f"for the {quorum['declarations']}-name soundness export at frozen Clean source {quorum['epoch']}. "
            f"Input SHA-256 {quorum['input_sha256']}.")


def render(report, rows, focused):
    metrics = report["metrics"]
    print("Clean self-proof fleet")
    if report["scoreboard_warning"]:
        print(f"Scoreboard receipt needs refresh: {report['scoreboard_warning']}")
    print("Production decisions by compiled kcheck:", metrics["production"].get("real_declarations_decided", "unverified"))
    current = report.get("source_qualification")
    if current and current["state"] == "qualified":
        print(_qualification_text(current))
        quorum = report.get("soundness_root_quorum")
        if quorum:
            print(_quorum_text(quorum))
        matcher = report.get("followups", {}).get("PR-67")
        if matcher and matcher["input_sha256"] == current["input_sha256"]:
            print(native_matcher_text(matcher))
        print("Historical original export")
    elif current:
        print("PR-29 source qualification unavailable:", current["reason"])
    raw = report["literal_export"]
    if raw["state"] == "measured":
        first = raw.get("first_refusal")
        print(f"Literal replay admitted {raw['prefix_accepted']} consecutive records out of {raw['records']}.")
        if first:
            print(f"First refusal at {first['name']} (line {first['line']}): {first['reason']}")
        if raw.get("public_source_commit"):
            print(f"Writer source: {raw['public_source_commit']}")
        print(f"Full input: {raw['declarations']} named declarations, SHA-256 {raw['sha256']}")
        print(f"The input contains {raw['inductive_blocks']} inductive blocks and {raw['quotient_records']} quotient records. "
              f"{raw['outside_named_seed_types']} family names are outside Eq, PUnit and Nat.")
    else:
        print("Literal replay evidence unavailable:", raw.get("reason", "unverified"))
    trial = report.get("const_helper_trial")
    if trial and trial["state"] == "recorded":
        if "baseline_stock_admitted" in trial:
            print(f"Stock ck0 admitted {trial['baseline_stock_admitted']} of {trial['baseline_named']} original names and refused the root.")
        print(f"PR-28 experimental proof: stock ck0 admitted {trial['stock_admitted']} of {trial['named']} names, including {trial['root']}.")
        print("Candidate input SHA-256:", trial["input_sha256"])
    elif trial:
        print("PR-28 receipt unavailable:", trial["reason"])
    fragment = metrics["fragment"]
    if "accepted" in fragment:
        print(f"Interim checker: {fragment['accepted']} of {fragment['inside_fragment']} in scope, {fragment['ordinary_declarations']} ordinary declarations in fixture.")
    named = report.get("followups", {}).get("PR-49")
    if named:
        print(f"Named Init slice: {named['accepted']} of {named['target_declarations']} original declarations "
              f"admitted with native advice, plus {named['recognised_families']} recognised base families.")
    if not rows:
        print("No catalog units match these filters. Use --unit ID on its own to see that unit and its outstanding prerequisites.")
    for r in rows:
        waiting = ", ".join(r["waiting_on"])
        print(f"\n{r['id']}  {r['kind']}  {r['status']}  {r['goal']}")
        if waiting:
            print(f"  Open prerequisites: {waiting}")
        print(f"  Completion evidence: {r['closes_with']}")
        if r["id"] == "C4-C5" and named:
            print("  Next integration check: replay the retained named-slice bytes through the checker "
                  "built by Trust, identify its loader and consuming site, and retain the forged, "
                  "structure-eta and level-only comparisons.")
            print("  Comparison command: python3 scripts/self_proof_fleet.py --replay-checker /path/to/checker --json")
        for claim in r["recorded_claims"]:
            print(f"  Recorded claim ({claim['since']}): {claim['owner']} — {claim['task'].split(':', 1)[0][:110]}")
        if focused:
            print(f"  Source: {r['source']}")
            if r.get("history"):
                print("  Dated history")
                render_events(r["history"])
    if "changes" in report:
        print("\nChanges since the supplied snapshot:")
        print("\n".join(report["changes"]) or "No measured changes.")


def clean_revision():
    return subprocess.run(["git", "-C", str(ROOT), "rev-parse", "HEAD"], check=True,
                          capture_output=True, text=True).stdout.strip()


def planning_view(action, publication_root, *, w0_shadow=None, w0_native=None):
    if w0_native is not None and (action not in ("design", "preview") or w0_shadow is not None):
        raise ValueError("native W0 requires Product Planning design or preview and a single W0 mode")
    from self_proof_fleet_product import product_plan, product_status, sync_product

    if action == "status":
        return product_status(publication_root)
    if action == "design":
        report = snapshot(native_w0=w0_native)
        return product_plan(report, clean_revision(), events=recorded_events(ROOT))
    if w0_native is not None:
        commit = clean_revision()
        report = snapshot(root=ROOT, native_w0=w0_native, defer_native_w0=True)
        return sync_product(report, commit, publication_root, clean_root=ROOT, w0_native=w0_native)
    return sync_product(snapshot(), clean_revision(), publication_root, clean_root=ROOT,
                        publish=action == "publish", w0_shadow=w0_shadow)


def render_planning(view):
    print(f"Fleet goal {view['goal']} · {view.get('name', 'Clean proves itself')}")
    if "state" in view:
        print("Operation:", view["state"])
    caps = view.get("capabilities", {})
    if caps:
        print("Native aterm Product Planning:", "available" if caps["native_table"] else "unavailable")
        if caps.get("native_reason"):
            print("Native probe:", caps["native_reason"])
        print("Evidence backend:", view.get("backend", "publication tracker" if view["state"] != "unavailable" else "unavailable"))
    if shadow := view.get("w0_native_shadow"):
        print(f"Native W0 comparison {shadow['state']}")
    if native := view.get("w0_native"):
        print(f"Native W0 validation {native['state']}")
    if view.get("publication_commit"):
        print("Publication snapshot:", view["publication_commit"], "(locally fetched origin/main)")
    elif view.get("publication_source") == "offline-working-copy":
        print("Publication snapshot: offline working copy")
    for gate in view.get("external_prerequisites", []):
        print(f"  External prerequisite {gate['id']}  {gate['status']}  {gate['goal']}")
    for pkg in view.get("packages", []):
        if "key" in pkg:
            waits = ", ".join(pkg["waiting_on"]) or "none"
            print(f"  {pkg['key']}  {pkg['status']}  {pkg['title']} (open prerequisites: {waits})")
        else:
            owner = pkg.get("claimed_by") or pkg.get("claim") or ""
            print(f"  {pkg.get('id', pkg.get('pk', '?'))}  {pkg.get('state', 'unverified')}  {pkg.get('title', '')}"
                  + (f" · {owner}" if owner else ""))
    for row in view.get("measurements", []):
        print(f"  {row['metric']} = {row['value']} {row.get('unit', '')}  {row.get('state', row.get('date', ''))}")
    if view.get("reason"):
        print(view["reason"])
    for why in view.get("deferred", []):
        print("Deferred:", why)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true", help="emit a snapshot for machines or subsequent comparison")
    parser.add_argument("--timeline", action="store_true", help="show dated proof, wiring, measurement and blocker events with their sources")
    parser.add_argument("--unit", help="show the completion gate, recorded claims and dated history for one unit")
    parser.add_argument("--ready", action="store_true", help="show open units with all catalog prerequisites qualified; retain recorded ownership")
    parser.add_argument("--proofs", action="store_true", help="show proof obligations only")
    parser.add_argument("--root-report", type=Path, help="read another digest-bound literal export receipt directory")
    parser.add_argument("--census-progress", metavar="FILE", type=Path,
                        help="read progress and the adopted checker output from a running or complete E4 census")
    focus = parser.add_mutually_exclusive_group()
    focus.add_argument("--entry-only", action="store_true",
                       help="with --census-progress, show just the local library imports of the actual checker entry")
    focus.add_argument("--proof-source-only", action="store_true",
                       help="with --census-progress, show the CompleteSound source module and its local imports")
    parser.add_argument("--replay-checker", metavar="EXECUTABLE", type=Path,
                        help="compare a supplied checker with retained Prelude, named Init, universe-level and eta process results")
    parser.add_argument("--measure-prefix", metavar="EXPORT", type=Path,
                        help="run the adopted checker from its base on a raw or gzip declaration export")
    parser.add_argument("--limit", type=int, metavar="RECORDS",
                        help="stop --measure-prefix after at most this many declaration records")
    parser.add_argument("--previous", type=Path, help="compare with a saved JSON snapshot")
    w0 = parser.add_mutually_exclusive_group()
    w0.add_argument("--shadow-w0", metavar="EXECUTABLE", type=Path,
                    help="compare native and Python W0 bytes before rendering an ordinary fleet report")
    w0.add_argument("--native-w0", nargs=3, metavar=("EXECUTABLE", "BUILD_RECEIPT", "SHA256"),
                    help="derive W0 for a fleet report, presentation or Planning design with a pinned Clean build")
    w0.add_argument("--export-w0-build", nargs=4, metavar=("SOURCE_CHECKOUT", "EXECUTABLE", "SHA256", "OUTPUT_PARENT"),
                    help="retain an independently pinned qualified W0 build and its receipt")
    w0.add_argument("--export-w0-gate-result", nargs=3, metavar=("RESULT", "RESULT_SHA256", "OUTPUT_PARENT"),
                    help="retain the qualified W0 build named by an independently pinned gate result")
    parser.add_argument("--planning", choices=("status", "design", "preview", "publish"),
                        help="read fleet goal E1, export its obligation catalog, or preview/publish qualified readings")
    planning_w0 = parser.add_mutually_exclusive_group()
    planning_w0.add_argument("--planning-shadow-w0", nargs=3, metavar=("EXECUTABLE", "BUILD_RECEIPT", "SHA256"),
                             help="compare a pinned native W0 build in a Product Planning preview")
    planning_w0.add_argument("--planning-native-w0", nargs=3, metavar=("EXECUTABLE", "BUILD_RECEIPT", "SHA256"),
                             help="derive and check W0 with a pinned Clean build in a Product Planning preview")
    parser.add_argument("--publication-root", type=Path, default=Path.home() / "publication",
                        help="checkout containing the fleet's goals/data and goals/tools/goals.py")
    parser.add_argument("--presentation", metavar="FILE", type=Path,
                        help="generate a standalone presentation of the timeline, current evidence and next gates")
    args = parser.parse_args()
    if (args.export_w0_build is not None or args.export_w0_gate_result is not None) and any((
            args.planning, args.planning_shadow_w0, args.planning_native_w0, args.presentation,
            args.ready, args.proofs, args.unit, args.previous, args.root_report, args.timeline, args.census_progress,
            args.measure_prefix, args.replay_checker, args.limit is not None, args.entry_only, args.proof_source_only)):
        option = "--export-w0-build" if args.export_w0_build is not None else "--export-w0-gate-result"
        parser.error(f"{option} runs independently of the other Fleet views")
    if args.planning_shadow_w0 is not None and args.planning != "preview":
        parser.error("--planning-shadow-w0 requires --planning preview")
    if args.planning_native_w0 is not None and args.planning != "preview":
        parser.error("--planning-native-w0 requires --planning preview")
    independent_view = any((args.timeline, args.census_progress, args.measure_prefix, args.replay_checker))
    if args.shadow_w0 is not None and (args.planning or args.presentation is not None or independent_view):
        parser.error("--shadow-w0 requires an ordinary fleet report")
    if args.native_w0 is not None and (independent_view or args.planning not in (None, "design")):
        parser.error("--native-w0 requires a fleet report, presentation or Planning design")
    native_w0 = None if args.native_w0 is None else tuple(args.native_w0)
    if (args.entry_only or args.proof_source_only) and not args.census_progress:
        parser.error("source import views require --census-progress")
    if args.replay_checker is not None:
        if any((args.planning, args.presentation, args.ready, args.proofs, args.unit, args.previous,
                args.root_report, args.timeline, args.census_progress, args.measure_prefix, args.limit is not None)):
            parser.error("--replay-checker runs independently of the other fleet views")
        from self_proof_checker_replay import replay
        try:
            result = replay(ROOT, args.replay_checker)
        except (ValueError, OSError, KeyError, TypeError, subprocess.SubprocessError) as exc:
            print(f"Candidate checker replay failed: {exc}", file=sys.stderr)
            return 1
        if args.json:
            print(json.dumps(result, indent=2))
        else:
            print(f"{result['matched']} of {result['qualified_cases']} process results matched "
                  f"for checker SHA-256 {result['checker_sha256']}.")
            for case in result["cases"]:
                if not case["matched"]:
                    print(f"  {case['case']} differed (expected exit {case['expected_exit']}, observed {case['exit']}).")
                    for channel in ("stdout", "stderr"):
                        difference = case.get(channel + "_first_difference")
                        if difference:
                            print(f"    {channel} line {difference['line']} expected {difference['expected']!r}, "
                                  f"observed {difference['observed']!r}")
            print("Compiler provenance requires a build receipt. Production decisions credited: 0.")
        return 0 if result["all_matched"] else 1
    if args.limit is not None and args.measure_prefix is None:
        parser.error("--limit requires --measure-prefix")
    if args.census_progress and any((args.planning, args.presentation, args.ready, args.proofs, args.unit,
                                     args.previous, args.root_report, args.timeline, args.measure_prefix)):
        parser.error("--census-progress accepts a checkpoint file and --json")
    if args.measure_prefix is not None:
        if any((args.planning, args.presentation, args.ready, args.proofs, args.unit,
                args.previous, args.root_report, args.timeline)):
            parser.error("--measure-prefix accepts --limit and --json")
        from self_proof_prefix import main as prefix_main
        options = [str(args.measure_prefix)]
        if args.limit is not None:
            options.extend(["--limit", str(args.limit)])
        if args.json:
            options.append("--json")
        return prefix_main(options)
    try:
        if args.export_w0_build is not None:
            from self_proof_fleet_w0 import export_w0_build

            print(json.dumps(export_w0_build(*args.export_w0_build), indent=2, sort_keys=True))
            return 0
        if args.export_w0_gate_result is not None:
            from self_proof_fleet_w0_result import export_w0_gate_result

            print(json.dumps(export_w0_gate_result(*args.export_w0_gate_result), indent=2, sort_keys=True))
            return 0
        if args.census_progress:
            import time
            # The registered E4 runner rewrites its JSON after each completed module.
            for attempt in range(3):
                try:
                    progress = census_progress(ROOT, read_json(args.census_progress), entry_only=args.entry_only,
                                               proof_source_only=args.proof_source_only)
                    break
                except json.JSONDecodeError:
                    if attempt == 2:
                        raise ValueError("E4 checkpoint is incomplete or invalid")
                    time.sleep(0.08)
            if args.json:
                print(json.dumps(progress, indent=2))
            else:
                print("E4 census at", progress["source_revision"])
                if args.entry_only or args.proof_source_only:
                    graph = progress["entry_imports" if args.entry_only else "proof_source_imports"]
                    print(f'{graph["entry"]} imports {len(graph["modules"]) - 1} local modules transitively '
                          f'({graph["staged_sources"]} sources staged, {progress["census_modules_expected"]} in E4).')
                    outside = [path for path, node in graph["modules"].items()
                               if path != graph["entry"] and not node["in_census"]]
                    if outside:
                        print("Local imports outside E4:", ", ".join(outside))
                if args.proof_source_only:
                    root = progress["proof_source"]
                    print("Soundness source module:", root["status"], root.get("first_error", ""))
                print(f'{progress["modules_recorded"]} of {progress["modules_expected"]} module rows recorded',
                      "(complete census)" if progress["complete"] else "(partial census)")
                print(", ".join(f"{count} {status}" for status, count in progress["module_counts"].items()))
                for package, rows in progress["packages"].items():
                    print(f'  {package}  {rows["recorded"]}/{rows["expected"]} recorded, '
                          f'{rows["elaborated"]} elaborated, {rows["refused"]} refused, {rows["timed_out"]} timed out')
                for group in progress["first_refusals"][:5]:
                    print(f'{group["rows"]} module rows first name {group["declaration"]} '
                          f'(first seen in {group["first_module"]})')
                if progress["unnamed_refusals"]:
                    print(f'{progress["unnamed_refusals"]} refusals did not identify a declaration in the first diagnostic')
                entry = progress["adopted_main"]
                print(f'Adopted checker main {entry["status"]}. Stdout {entry["stdout_bytes"]} of {entry["expected_bytes"]} expected bytes.')
                if entry["first_error"]:
                    print(entry["first_error"])
            return 0
        if args.planning or args.presentation:
            if any((args.ready, args.proofs, args.unit, args.previous, args.root_report, args.timeline)):
                parser.error("planning and presentation use the full canonical evidence set")
            if args.planning and args.presentation:
                parser.error("select a planning operation or a presentation")
            if args.presentation:
                from self_proof_fleet_slides import render_slides
                if args.json:
                    parser.error("--presentation writes HTML; use --json for a fleet snapshot")
                view = planning_view("status", args.publication_root)
                report = snapshot(native_w0=native_w0)
                events = displayed_events(recorded_events(ROOT), report.get("source_qualification"), report.get("followups"),
                                          report.get("soundness_root_quorum_history", ()), receipts=report.get("execution_receipts"))
                deck = render_slides(report, events, view, revision=clean_revision())
                args.presentation.write_text(deck, encoding="utf-8")
                print(args.presentation)
            else:
                planning_native = native_w0 if args.planning_native_w0 is None else tuple(args.planning_native_w0)
                if planning_native is not None:
                    view = planning_view(args.planning, args.publication_root, w0_native=planning_native)
                else:
                    view = planning_view(args.planning, args.publication_root, w0_shadow=args.planning_shadow_w0)
                if args.json:
                    print(json.dumps(view, indent=2, sort_keys=True))
                else:
                    render_planning(view)
                if args.planning_shadow_w0 is not None and view["w0_native_shadow"]["state"] != "matched":
                    return 1
                if args.planning_native_w0 is not None and view["w0_native"]["state"] != "matched":
                    return 1
                if args.planning == "publish" and view["state"] in {"unavailable", "deferred", "partial"}:
                    return 1
            return 0
        if args.timeline:
            if args.ready or args.proofs or args.previous or args.root_report:
                parser.error("--timeline accepts --unit and --json")
            events = unit_history(args.unit)
            if args.unit and not events:
                raise ValueError(f"no timeline events for {args.unit}")
            if args.json:
                print(json.dumps({"schema": "clean.self_proof_fleet_timeline.v1", "events": events}, indent=2))
            else:
                render_events(events)
            return 0
        report = snapshot(report_dir=args.root_report, shadow_w0=args.shadow_w0, native_w0=native_w0)
        rows = report["units"]
        if args.unit:
            rows = [r for r in rows if r["id"] == args.unit]
            if not rows:
                raise ValueError(f"unknown unit {args.unit}")
        if args.proofs:
            rows = [r for r in rows if r["kind"] == "proof"]
        if args.ready:
            rows = ready_units(rows)
        if args.previous:
            report["changes"] = change_summary(read_json(args.previous), report)
        if args.unit and rows:
            events = displayed_events(recorded_events(ROOT, args.unit), report.get("source_qualification"), report.get("followups"),
                                      report.get("soundness_root_quorum_history", ()), receipts=report.get("execution_receipts"))
            if events:
                rows[0]["history"] = events
        if args.json:
            if args.unit or args.proofs or args.ready:
                report["selected_units"] = [r["id"] for r in rows]
            print(json.dumps(report, indent=2, sort_keys=True))
        else:
            render(report, rows, bool(args.unit))
        return 0
    except (OSError, KeyError, TypeError, ValueError, subprocess.SubprocessError) as error:
        print(f"self_proof_fleet: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
