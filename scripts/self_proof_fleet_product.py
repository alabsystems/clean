# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Project E1 planning and evidence through native aterm Product Planning or its publication bridge."""

import csv
import io
import json
import os
from pathlib import Path
import re
import subprocess
import sys

if __package__:
    from .self_proof_fleet_evidence import (
        PR29_COMMAND, PR29_REPORT, displayed_events, event_units, read_const_trial,
        read_export_evidence, read_source_qualification, source_event, source_qualification_command,
    )
    from .self_proof_fleet_w0 import (
        BOARD, COVERAGE, W0BuildError, _executable_stat, digest as _digest, executable_digest,
        read_pinned_build, require_output, run_candidate,
    )
else:
    from self_proof_fleet_evidence import (
        PR29_COMMAND, PR29_REPORT, displayed_events, event_units, read_const_trial,
        read_export_evidence, read_source_qualification, source_event, source_qualification_command,
    )
    from self_proof_fleet_w0 import (
        BOARD, COVERAGE, W0BuildError, _executable_stat, digest as _digest, executable_digest,
        read_pinned_build, require_output, run_candidate,
    )

ROOT = Path(__file__).resolve().parents[1]
REPORT = Path("reports/self-proof-root-export-2026-11-17/source-fidelity")
TRIAL_REPORT = Path("reports/self-proof-const-branch-trial")
PROJECT = "clean/self-proof"
GOAL = "E1"
SCHEMA = "clean-self-proof-fleet-v1"
FAMILY_ABSENT = "aterm db table: no typed table of that name in this build (see `aterm db table ls`)"
LEGACY_GOALS = "aterm: unknown command 'goals' (try --help)"
E1_METRICS = {f"{GOAL}.{name}" for name in (
    "soundness_root_resident_equal", "adopted_kcheck_first_prefix_accepted", "compiled_kcheck_decisions",
    "stock_ck0_soundness_root_admitted", "stock_ck0_const_helper_candidate_admitted",
)}


class ProductUnavailable(ValueError):
    """The tracker or the measurement cannot presently support an operation."""


class NativeTableAbsent(ProductUnavailable):
    """The table scan reported the installed build's specific missing-table diagnostic."""


def _run(argv, cwd):
    env = os.environ.copy()
    env.pop("ALAB_GOALS_DATA", None)  # The owned publication checkout supplies its own tables.
    if argv[:3] == ["aterm", "goals", "show"]:
        env["ATERM_GOALS_PUBLICATION"] = str(cwd)
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    try:
        return subprocess.run(argv, cwd=cwd, env=env, text=True, capture_output=True, check=False)
    except OSError as err:
        return subprocess.CompletedProcess(argv, 127, "", str(err))


def _output(result):
    if result.returncode:
        raise ProductUnavailable((result.stderr or result.stdout).strip() or
                                 f"{Path(result.args[0]).name} exited {result.returncode}")
    return result.stdout


def _checked(argv, cwd, runner):
    return _output(runner(argv, cwd))


def _rows(text, fields):
    reader = csv.DictReader(io.StringIO(text), delimiter="\t")
    if not reader.fieldnames or not fields <= set(reader.fieldnames):
        raise ProductUnavailable("publication tracker table lacks its required columns")
    rows = list(reader)
    if any(None in row or None in row.values() for row in rows):
        raise ProductUnavailable("publication tracker table has a malformed row")
    return rows


def _publication_origin(root, runner):
    remote = _checked(["git", "remote", "get-url", "origin"], root, runner).strip()
    if not re.fullmatch(r"(?:https://github\.com/|ssh://git@github\.com/|git@github\.com:)alabsystems/publication(?:\.git)?/?", remote):
        raise ProductUnavailable("publication checkout has a different origin")


def _publication_revision(root, runner):
    top = runner(["git", "rev-parse", "--show-toplevel"], root)
    if top.returncode:
        if "not a git repository" in top.stderr and not (root / ".git").exists():
            return None
        raise ProductUnavailable(top.stderr.strip() or "publication checkout is unreadable")
    if Path(top.stdout.strip()).resolve() != root:
        raise ProductUnavailable("publication directory must be the root of its own checkout")
    _publication_origin(root, runner)
    # Resolve once. A fetch in a sibling worktree must not split these three tables across revisions.
    revision = _checked(["git", "rev-parse", "--verify", "refs/remotes/origin/main^{commit}"], root, runner).strip()
    if not re.fullmatch(r"[0-9a-f]{40}", revision):
        raise ProductUnavailable("publication origin/main has no resolved commit")
    return revision


def _table(root, revision, table, fields, runner):
    path = f"goals/data/{table}.tsv"
    contents = (_checked(["git", "show", f"{revision}:{path}"], root, runner) if revision
                else (root / path).read_text(encoding="utf-8"))
    return _rows(contents, fields)


def _native_scan(collection, scope, runner, cwd):
    command = ["aterm", "db", "table", "scan", "lab/tracker", collection, "--where", scope, "--json"]
    scan = runner(command, cwd)
    if scan.returncode == 1 and not scan.stdout.strip() and scan.stderr.strip() == FAMILY_ABSENT:
        raise NativeTableAbsent(FAMILY_ABSENT)
    result = json.loads(_output(scan))
    malformed = result.get("malformed", 0 if collection == "measure" else None) if isinstance(result, dict) else None
    if (not isinstance(result, dict) or result.get("collection") != collection
            or type(malformed) is not int or malformed != 0 or not isinstance(result.get("rows"), list)
            or any(not isinstance(row, dict) for row in result["rows"])):
        raise ProductUnavailable(f"unusable lab/tracker {collection} scan")
    return result["rows"]


def _native_measures(metric, runner, clean):
    rows = []
    for entry in _native_scan("measure", f"metric={metric}", runner, clean):
        # Typed cell scans are flat. A signed log entry may expose its record under row.
        row = entry.get("row", entry)
        if (not isinstance(row, dict) or row.get("metric") != metric or not isinstance(row.get("value"), str)
                or not re.fullmatch(r"-?(?:0|[1-9][0-9]*)(?:\.[0-9]+)?", row["value"])
                or "source" not in row or "commit" not in row
                or (row["source"] is not None and not isinstance(row["source"], str))
                or (row["commit"] is not None and not isinstance(row["commit"], str))):
            raise ProductUnavailable(f"unusable or unscoped typed measure row for {metric}")
        rows.append({**row, "unit": "declarations"})
    return rows


def _agoals_json(argv, cwd, runner):
    def unique_fields(pairs):
        fields = dict(pairs)
        if len(fields) != len(pairs):
            raise ProductUnavailable("duplicate field in aGoals response")
        return fields

    def invalid_number(token):
        raise ProductUnavailable(f"invalid JSON number in aGoals response: {token}")

    reply = runner(argv, cwd)
    raw = _output(reply)
    if reply.stderr.strip():
        raise ProductUnavailable(reply.stderr.strip())
    result = json.loads(raw, object_pairs_hook=unique_fields, parse_constant=invalid_number)
    if not isinstance(result, dict):
        raise ProductUnavailable("aGoals returned a non-object response")
    return result


def _publication_capabilities(clean, runner):
    fields = _agoals_json(["aterm", "goals", "capabilities", "--json"], clean, runner)
    expected = {"schema": 1, "product": "aGoals", "backend": "publication", "family_registered": False}
    if fields != expected or type(fields["schema"]) is not int or fields["family_registered"] is not False:
        raise ProductUnavailable("aGoals capabilities do not identify an unregistered publication backend")
    return fields


def _native_status(clean, runner, caps, packages):
    help_result = runner(["aterm", "goals", "measure", "--help"], clean)
    has_measure = help_result.returncode == 0 and "measure" in help_result.stdout and "--source" in help_result.stdout
    try:
        scoped = _native_scan("package", "goal=E1", runner, clean)
    except NativeTableAbsent as err:
        legacy = (help_result.returncode == 2 and not help_result.stdout.strip()
                  and help_result.stderr.strip() == LEGACY_GOALS)
        if has_measure and not help_result.stderr.strip():
            caps["agoals"] = _publication_capabilities(clean, runner)
        elif not legacy:
            raise ProductUnavailable(help_result.stderr.strip() or "unrecognized aGoals measurement command") from err
        caps["native_reason"] = str(err)
        return None
    except ProductUnavailable as err:
        missing = str(FileNotFoundError(2, os.strerror(2), "aterm"))
        if help_result.returncode == 127 and help_result.stderr.strip() == missing and str(err) == missing:
            caps["native_reason"] = missing
            return None
        raise
    caps["native_table"] = True
    if any(row.get("goal") != GOAL for row in scoped):
        raise ProductUnavailable("native package scan returned a row outside E1")
    packages.extend(scoped)
    if not has_measure:
        raise ProductUnavailable("native package table is present but aterm goals measure --source is unavailable")
    metrics = _native_scan("metric", "goal=E1", runner, clean)
    for row in metrics:
        metric = row.get("id", row.get("pk"))
        if (isinstance(metric, str) and metric in E1_METRICS and row.get("row") == "live"
                and row.get("goal") == GOAL and row.get("unit") == "declarations"):
            caps["native_metric_ids"].append(metric)
    caps["native_metric_ids"].sort()
    if len(set(caps["native_metric_ids"])) != len(caps["native_metric_ids"]):
        raise ProductUnavailable("native E1 metric registration is ambiguous")
    if not caps["native_metric_ids"]:
        raise ProductUnavailable("native tracker has no live, declarations-unit Clean E1 metrics")
    measures = [row for metric in caps["native_metric_ids"] for row in _native_measures(metric, runner, clean)]
    caps["native_measure"] = True
    return {"project": PROJECT, "goal": GOAL, "state": "available", "backend": "aterm",
            "capabilities": caps, "goal_row": None, "packages": packages, "measurements": measures,
            "native_packages": packages}


def _show_records(view, name, revision, tablename, strings):
    rows = view.get(name)
    if not isinstance(rows, list):
        raise ProductUnavailable(f"aGoals did not return its {name} list")
    previous_line = 1
    identities = set()
    prefix = f"{revision}:goals/data/{tablename}.tsv:"
    for row in rows:
        if not isinstance(row, dict) or any(not isinstance(row.get(k), str) for k in strings):
            raise ProductUnavailable(f"malformed aGoals {name} record")
        ref = row.get("publication_ref")
        line = ref[len(prefix):] if isinstance(ref, str) and ref.startswith(prefix) else ""
        if not re.fullmatch(r"[1-9][0-9]*", line) or int(line) <= previous_line:
            raise ProductUnavailable(f"ambiguous or unbound aGoals {name} record")
        identity = row["id"] if "id" in strings else ref
        if not identity or identity in identities or row.get("pk") != identity:
            raise ProductUnavailable(f"ambiguous aGoals {name} identity")
        previous_line = int(line)
        identities.add(identity)
    return rows


def _source_packages(root, revision, runner):
    # show expands depends into IDs and loses its original punctuation. Preserve
    # that field for existing publication callers and bind it to the physical row.
    path = "goals/data/packages.tsv"
    raw = _checked(["git", "show", f"{revision}:{path}"], root, runner)
    reader = csv.DictReader(io.StringIO(raw), delimiter="\t", quoting=csv.QUOTE_NONE)
    head = reader.fieldnames or []
    if not {"id", "goal", "depends"} <= set(head) or len(head) != len(set(head)):
        raise ProductUnavailable("invalid publication package header")
    packages = {}
    for row in reader:
        if None in row or None in row.values():
            raise ProductUnavailable("invalid publication package row")
        if row["goal"] == GOAL:
            packages[f"{revision}:{path}:{reader.line_num}"] = row
    return packages


def _observation_rows(view, revision):
    observations = _show_records(view, "measures", revision, "metrics",
                                 ("goal", "metric", "date", "at", "machine", "value", "unit", "source", "note"))
    units = {}
    for row in observations:
        name = row["metric"].removeprefix(f"{GOAL}.")
        if (row["goal"] != GOAL or not name or row["metric"] != f"{GOAL}.{name}"
                or row["at"] != row["date"]):
            raise ProductUnavailable("unscoped or inconsistent aGoals observation")
        units.setdefault(row["metric"], set()).add(row["unit"])
        row["metric_id"], row["metric"] = row["metric"], name
    definitions = view.get("metrics")
    if not isinstance(definitions, list) or len(definitions) != len(units):
        raise ProductUnavailable("aGoals metric definitions disagree with its observations")
    for definition in definitions:
        if not isinstance(definition, dict) or not isinstance(definition.get("id"), str):
            raise ProductUnavailable("malformed aGoals metric definition")
        key = definition["id"]
        observed = sorted(units.pop(key, set()))
        if (not observed or definition.get("pk") != key or definition.get("goal") != GOAL
                or definition.get("name") != key.removeprefix(f"{GOAL}.") or definition.get("units") != observed
                or "unit" not in definition or definition["unit"] != (observed[0] if len(observed) == 1 else None)):
            raise ProductUnavailable("ambiguous or inconsistent aGoals metric definition")
    return observations


def _publication_show(root, revision, runner):
    if revision is None:
        raise ProductUnavailable("aGoals publication requires a pinned origin/main")
    view = _agoals_json(["aterm", "goals", "show", GOAL, "--json"], root, runner)
    if view.get("source") != f"Publication at {revision}":
        raise ProductUnavailable("aGoals returned a different publication source")
    goals = _show_records(view, "goals", revision, "goals", ("id", "title", "target", "state", "baseline"))
    if len(goals) != 1 or goals[0]["id"] != GOAL:
        raise ProductUnavailable("aGoals did not return exactly one E1 goal")
    packages = _show_records(view, "packages", revision, "packages",
                             ("id", "title", "goal", "lane", "state", "claimed_by", "claim",
                              "exit_command", "exit_expect", "evidence"))
    stored_packages = _source_packages(root, revision, runner)
    if list(stored_packages) != [row["publication_ref"] for row in packages]:
        raise ProductUnavailable("aGoals E1 packages disagree with the pinned package rows")
    for row in packages:
        stored = stored_packages[row["publication_ref"]]
        original = stored["depends"]
        ids = [d.strip() for d in re.split("[,; ]", original) if d.strip()]
        if (row["goal"] != GOAL or row.get("depends") != ids
                or any(row.get(k) != v for k, v in stored.items() if k != "depends")
                or row["claimed_by"] != row["claim"]
                or row.get("exit") != {"command": row["exit_command"], "expect": row["exit_expect"]}):
            raise ProductUnavailable("unscoped or inconsistent aGoals package")
        for key in ("dispatchable", "dependencies_readable"):
            if key in row and type(row[key]) is not bool:
                raise ProductUnavailable(f"unusable aGoals package {key}")
        for key in ("blocking_dependencies", "unknown_dependencies"):
            if key in row and (not isinstance(row[key], list) or any(i not in ids for i in row[key])
                               or len(row[key]) != len(set(row[key]))):
                raise ProductUnavailable(f"unusable aGoals package {key}")
        if row.get("dispatchable") is True and (
                row["state"] != "ready" or row["claim"] or row.get("blocking_dependencies")
                or row.get("dependencies_readable") is False or row.get("blocked_on")):
            raise ProductUnavailable("aGoals marked a held or blocked package dispatchable")
        row["depends_ids"], row["depends"] = ids, original
    lanes = _show_records(view, "lanes", revision, "lanes", ("id", "name"))
    package_lanes = {r["lane"] for r in packages}
    for row in lanes:
        memberships = row.get("goals")
        if (not isinstance(memberships, list) or any(not isinstance(g, str) for g in memberships)
                or (row["id"] not in package_lanes and GOAL not in memberships)):
            raise ProductUnavailable("aGoals returned an unscoped lane")
    lane_ids = {row["id"] for row in lanes}
    if not package_lanes <= lane_ids:
        raise ProductUnavailable("aGoals omitted a package lane")
    decisions = _show_records(view, "decisions", revision, "decisions", ("id", "lane", "decision", "reason"))
    if any(row["lane"] not in lane_ids for row in decisions):
        raise ProductUnavailable("aGoals returned an unscoped decision")
    findings = view.get("findings")
    if not isinstance(findings, list) or any(not isinstance(f, str) for f in findings):
        raise ProductUnavailable("malformed aGoals findings")
    return {"goal_row": goals[0], "packages": packages, "measurements": _observation_rows(view, revision),
            "lanes": lanes, "decisions": decisions, "metrics": view["metrics"], "findings": findings}


def product_status(publication_root, *, clean_root=ROOT, runner=_run):
    """Read scoped native Product Planning. Use the publication bridge when the native family is absent."""
    root = Path(publication_root).resolve()
    clean = Path(clean_root).resolve()
    native_packages = []
    caps = {"native_table": False, "native_measure": False, "native_metric_ids": []}
    try:
        native = _native_status(clean, runner, caps, native_packages)
        if native is not None:
            return native
    except (OSError, ValueError) as err:
        caps["native_reason"] = str(err)
        return {"project": PROJECT, "goal": GOAL, "state": "unavailable", "backend": "aterm",
                "capabilities": caps, "reason": str(err), "packages": native_packages,
                "measurements": [], "native_packages": native_packages}
    try:
        revision = _publication_revision(root, runner)
        envelope = {"project": PROJECT, "goal": GOAL, "state": "available", "capabilities": caps,
                    "backend": "publication", "publication_commit": revision,
                    "publication_source": "refs/remotes/origin/main" if revision else "offline-working-copy",
                    "native_packages": []}
        if "agoals" in caps:
            return {**envelope, **_publication_show(root, revision, runner)}
        goals = [row for row in _table(root, revision, "goals", {"id", "title", "target"}, runner) if row["id"] == GOAL]
        if len(goals) != 1:
            raise ProductUnavailable("publication does not hold exactly one E1 goal")
        packages = [row for row in _table(root, revision, "packages", {"id", "goal", "depends", "state", "claimed_by",
                                                                       "exit_expect", "evidence"}, runner) if row["goal"] == GOAL]
        measures = [row for row in _table(root, revision, "metrics", {"goal", "metric", "value", "source", "unit"}, runner)
                    if row["goal"] == GOAL]
        if revision is None and not (root / "goals/tools/goals.py").is_file():
            raise ProductUnavailable("publication goals/tools/goals.py is missing")
        return {**envelope, "goal_row": goals[0], "packages": packages, "measurements": measures}
    except (OSError, ValueError, csv.Error) as err:
        return {"project": PROJECT, "goal": GOAL, "state": "unavailable", "capabilities": caps,
                "backend": "publication", "reason": str(err), "native_packages": []}


def _validate_snapshot(snapshot, clean_commit):
    if not isinstance(clean_commit, str) or not re.fullmatch(r"[0-9a-f]{40}", clean_commit):
        raise ProductUnavailable("Clean provenance requires a full Git commit")
    if not isinstance(snapshot, dict) or snapshot.get("schema") != SCHEMA:
        raise ProductUnavailable("unsupported Clean self-proof snapshot")


def product_plan(snapshot, clean_commit, *, events=()):
    """Render E1 design packages with repository evidence and dependencies, without changing tracker rows."""
    _validate_snapshot(snapshot, clean_commit)
    history = {}
    for event in displayed_events(events, snapshot.get("source_qualification"), snapshot.get("followups"),
                                  snapshot.get("soundness_root_quorum_history", []), receipts=snapshot.get("execution_receipts")):
        for unit in event_units(event):
            history.setdefault(unit, []).append(event)
    packages = []
    external = []
    for row in snapshot["units"]:
        if row["kind"] == "external":
            item = {key: row[key] for key in ("id", "goal", "status", "closes_with", "source")}
            external.append(item)
        else:
            item = {"key": row["id"], "repo": "clean", "goal": GOAL, "kind": row["kind"], "title": row["goal"],
                    "depends_on": list(row["prerequisites"]), "exit_expect": row["closes_with"],
                    "source": row["source"], "status": row["status"], "waiting_on": list(row["waiting_on"]),
                    "recorded_claims": list(row["recorded_claims"])}
            packages.append(item)
        if row["id"] in history:
            item["history"] = history[row["id"]]
    return {"name": "Clean proves itself", "project": PROJECT, "goal": GOAL, "clean_commit": clean_commit,
            "source": "data/self_proof_fleet_obligations.json", "packages": packages,
            "external_prerequisites": external}


def _canonical(root, commit, path, runner):
    path = str(path)
    current = (root / path).read_bytes()
    stored = _checked(["git", "show", f"{commit}:{path}"], root, runner)
    if current != stored.encode("utf-8"):
        raise ProductUnavailable(f"{path} differs from clean@{commit}")
    return current


def _export_readings(snapshot, root, commit, runner):
    manifest = _canonical(root, commit, REPORT / "receipt-set.json", runner)
    _checked(["git", "diff", "--quiet", commit, "--", "scripts/self_proof_fleet_evidence.py"], root, runner)
    actual = read_export_evidence(root / REPORT)
    if actual.get("state") != "measured":
        raise ProductUnavailable("canonical export unverified: " + str(actual.get("reason", "no measured receipts")))
    if json.dumps(actual, sort_keys=True) != json.dumps(snapshot.get("literal_export"), sort_keys=True):
        raise ProductUnavailable("root export does not match the canonical hash-bound receipts")
    source = (f"python3 scripts/self_proof_fleet.py --json # {REPORT}/receipt-set.json "
              f"sha256={_digest(manifest)} export_sha256={actual['sha256']}")
    note = (f"Retained at clean@{commit}. Writer {actual['public_source_commit']}. "
            f"Lean modules {actual['lean_module_source']}. Root {actual['root']}.")
    count = actual["declarations"]
    prefix = actual.get("first_refusal")
    observation = f" First refusal {prefix['name']} at line {prefix['line']}." if prefix else ""
    return [
        {"metric": "soundness_root_resident_equal", "value": actual["resident_equal"], "unit": "declarations",
         "source": source, "note": f"{note} Pinned Lean compared all {count} declarations."},
        {"metric": "adopted_kcheck_first_prefix_accepted", "value": actual["prefix_accepted"], "unit": "declarations",
         "source": source, "note": f"{note} Prefix ends at the first declaration.{observation}"},
    ]


def _qualification_paths(clean):
    manifest = PR29_REPORT / "qualification.json"
    artifacts = json.loads((clean / manifest).read_bytes())["artifacts"]
    replay = json.loads((clean / PR29_REPORT / "replay.json").read_bytes())
    subject = os.path.normpath(PR29_REPORT / replay["retained_export"])
    return sorted({str(manifest), *(str(PR29_REPORT / name) for name in artifacts), subject})


def _root_readings(snapshot, root, commit, runner):
    observed = snapshot.get("source_qualification")
    if observed is None:
        return _export_readings(snapshot, root, commit, runner)
    manifest = _canonical(root, commit, PR29_REPORT / "qualification.json", runner)
    history = json.loads(_canonical(root, commit, "data/self_proof_fleet_timeline.json", runner))
    event = source_event(history["events"])
    if event is None or event.get("qualification_sha256") != _digest(manifest):
        raise ProductUnavailable("PR-29 has no matching committed qualification observation")
    _checked(["git", "diff", "--quiet", commit, "--", "scripts/self_proof_fleet_evidence.py"], root, runner)
    actual = read_source_qualification(root / PR29_REPORT, event)
    if actual.get("state") != "qualified" or observed != actual:
        raise ProductUnavailable("PR-29 source qualification is unavailable or differs from the measured snapshot")
    _checked(["git", "merge-base", "--is-ancestor", actual["qualified_revision"], commit], root, runner)
    paths = _qualification_paths(root)
    tracked = _checked(["git", "ls-tree", "-r", "--name-only", commit, "--", *paths], root, runner).splitlines()
    if set(tracked) != set(paths):
        raise ProductUnavailable("PR-29 evidence files are missing from the publishing Clean commit")
    _checked(["git", "diff", "--quiet", commit, "--", *paths], root, runner)
    source = source_qualification_command(actual)
    root_note = f"PR-29 at clean@{actual['qualified_revision']}. Root {actual['root']}."
    count = actual["declarations"]
    notes = (
        ("stock_ck0_soundness_root_admitted", actual["stock_admitted"],
         f"Independent stock ck0 admitted {actual['stock_admitted']} of {count} named declarations including the root."),
        ("soundness_root_resident_equal", actual["resident_equal"],
         f"Pinned Lean's resident declarations matched {actual['resident_equal']} of {count} names."),
        ("adopted_kcheck_first_prefix_accepted", actual["prefix_accepted"],
         f"The adopted checker admitted {actual['prefix_accepted']} consecutive declaration records out of "
         f"{actual['records']}. First refusal {actual['first_refusal']['name']} at line {actual['first_refusal']['line']}."),
    )
    return [{"metric": key, "value": value, "unit": "declarations", "source": source,
             "note": root_note + " " + note} for key, value, note in notes]


def _const_trial_readings(snapshot, root, commit, runner):
    observed = snapshot.get("const_helper_trial")
    if observed is None:
        return []
    directory = TRIAL_REPORT
    path = directory / "result.json"
    manifest = _canonical(root, commit, path, runner)
    history = json.loads(_canonical(root, commit, "data/self_proof_fleet_timeline.json", runner))
    event = next((row for row in reversed(history["events"]) if row.get("unit") == "PR-28"), None)
    if event is None or event.get("result_sha256") != _digest(manifest):
        raise ProductUnavailable("the const-helper trial has no matching committed observation")
    _checked(["git", "diff", "--quiet", commit, "--", "scripts/self_proof_fleet_evidence.py"], root, runner)
    actual = read_const_trial(root / directory, event, snapshot["literal_export"])
    if actual.get("state") != "recorded" or observed != actual:
        raise ProductUnavailable("the archived const-helper trial differs from the observed result")
    source = (f"python3 {directory}/verify.py # receipt_sha256={actual['result_sha256']} "
              f"candidate_sha256={actual['input_sha256']} baseline_sha256={actual['baseline_input_sha256']}")
    note = (f"Retained at clean@{commit}. Independent stock ck0 admitted all {actual['named']} candidate "
            f"declarations including {actual['root']}. The adopted checker and production have separate readings.")
    return [{"metric": "stock_ck0_const_helper_candidate_admitted", "value": actual["stock_admitted"],
             "unit": "declarations", "source": source, "note": note}]


def _production_reading(snapshot, root, commit, runner, *, check_python=True):
    if not check_python and snapshot["scoreboard_warning"] is not None:
        raise ProductUnavailable(snapshot["scoreboard_warning"])
    board = _canonical(root, commit, BOARD, runner)
    coverage = _canonical(root, commit, COVERAGE, runner)
    producer = json.loads(board)["headline"]["decided_by_compiled_kcheck"]
    if not isinstance(producer, dict):
        raise ProductUnavailable("qualified production scoreboard entry is missing")
    value = producer.get("real_declarations_decided")
    if (type(value) is not int or value < 0 or producer.get("source") != str(COVERAGE)
            or snapshot["scoreboard_warning"] is not None
            or json.dumps(snapshot["metrics"]["production"], sort_keys=True) != json.dumps(producer, sort_keys=True)):
        raise ProductUnavailable("compiled decisions have no matching qualified scoreboard count")
    if check_python:
        check = [sys.executable, "-B", str(root / "scripts/self_proof_scoreboard.py")]
        _checked(["git", "diff", "--quiet", commit, "--", "scripts/self_proof_scoreboard.py",
                  "scripts/kcheck_coverage.py", "scripts/kcheck_coverage_readers.py",
                  "scripts/kcheck_coverage_export.py", "scripts/kcheck_fragment_census.py"], root, runner)
        if not _checked([*check, "--check"], root, runner).startswith("SELF_PROOF_SCOREBOARD=ok "):
            raise ProductUnavailable("scoreboard checker did not report a matching re-derivation")
    return {"metric": "compiled_kcheck_decisions", "value": value, "unit": "declarations",
            "source": (f"python3 scripts/self_proof_scoreboard.py --check # {BOARD} "
                       f"sha256={_digest(board)} coverage_sha256={_digest(coverage)}"),
            "note": f"Validated at clean@{commit}. Real declarations decided at a production site by compiled kcheck."}


def _w0_build_inputs(root, commit, executable, runner):
    if _checked(["git", "rev-parse", "HEAD"], root, runner).strip() != commit:
        raise ProductUnavailable("native W0 build source differs from the current Clean checkout")
    if runner(["git", "diff", "--quiet", "--no-ext-diff", commit, "--"], root).returncode:
        raise ProductUnavailable("tracked Clean inputs differ from the native W0 build commit")
    tree = _checked(["git", "rev-parse", f"{commit}^{{tree}}"], root, runner).strip()
    if not re.fullmatch(r"[0-9a-f]{40}", tree):
        raise ProductUnavailable("native W0 build commit has no resolved tree")
    return {"source_commit": commit, "source_tree": tree, "executable_sha256": executable_digest(executable),
            "board_sha256": _digest(_canonical(root, commit, BOARD, runner)),
            "coverage_sha256": _digest(_canonical(root, commit, COVERAGE, runner))}


def _run_w0_candidate(argv, cwd):
    try:
        return run_candidate(argv, cwd)
    except W0BuildError as err:
        raise ProductUnavailable(str(err)) from err


def _preview_w0_candidate(root, commit, runner, build, *, guard_identity=False):
    try:
        pinned = read_pinned_build(build, expected_commit=commit)
        identity = _executable_stat(pinned.executable) if guard_identity else None
        inputs = _w0_build_inputs(root, commit, pinned.executable, runner)
        pinned.require_inputs(inputs)
        if identity is not None and (_executable_stat(pinned.executable) != identity or not pinned.receipt_unchanged()):
            raise ProductUnavailable("native W0 build inputs changed before the version check")
        pinned.require_version(root, _run_w0_candidate)
        if identity is not None and (_executable_stat(pinned.executable) != identity or not pinned.receipt_unchanged()):
            raise ProductUnavailable("native W0 build inputs changed during the version check")
        argv = [str(pinned.executable), "evidence", "status", "--scoreboard", "--check", "--repo-root", str(root)]
        require_output(_run_w0_candidate(argv, root), "saved-board check",
                       b"SELF_PROOF_SCOREBOARD=ok the record matches its sources\n")
        if ((identity is not None and _executable_stat(pinned.executable) != identity)
                or not pinned.receipt_unchanged()
                or _w0_build_inputs(root, commit, pinned.executable, runner) != inputs):
            raise ProductUnavailable("native W0 build inputs changed during the comparison")
    except W0BuildError as err:
        raise ProductUnavailable(str(err)) from err
    return {"state": "matched", "receipt_sha256": build[2], **pinned.receipt}


def _identity(row):
    return tuple(str(row[field]) for field in ("metric", "value", "unit", "source"))


def _publication_check(root, runner):
    # The bridge's --push publishes everything its checkout has ahead of origin/main.
    # Use a clean checkout with no unpublished commits to keep its transaction scoped.
    dirty = _checked(["git", "status", "--porcelain", "--untracked-files=no"], root, runner)
    if dirty.strip():
        raise ProductUnavailable("publication checkout contains tracked work outside this measurement")
    _publication_origin(root, runner)
    _checked(["git", "fetch", "--quiet", "origin", "refs/heads/main:refs/remotes/origin/main"], root, runner)
    if runner(["git", "merge-base", "--is-ancestor", "HEAD", "refs/remotes/origin/main"], root).returncode:
        raise ProductUnavailable("publication checkout has unpublished commits or its ancestry is unavailable")


def _published_rows(root, runner):
    raw = _checked(["git", "show", "refs/remotes/origin/main:goals/data/metrics.tsv"], root, runner)
    return [r for r in _rows(raw, {"goal", "metric", "value", "unit", "source"}) if r["goal"] == GOAL]


def _resident_sample(samples, item, commit, runner, clean, *, just_written=False):
    metric = f"{GOAL}.{item['metric']}"
    matched = False
    for sample in samples:
        if sample["metric"] != metric or sample["source"] != item["source"]:
            continue
        # The typed log stores exact decimals as strings, including a possible fractional zero.
        if sample["value"].partition(".")[0] != str(item["value"]) or sample["value"].partition(".")[2].strip("0"):
            raise ProductUnavailable(f"native {metric} has a conflicting value for the same evidence")
        recorded = sample["commit"]
        if not isinstance(recorded, str) or not re.fullmatch(r"[0-9a-f]{7,40}", recorded):
            raise ProductUnavailable(f"native {metric} has no qualified Clean commit for this evidence")
        if len(recorded) < 40:
            recorded = _checked(["git", "rev-parse", "--verify", recorded + "^{commit}"], clean, runner).strip()
        if recorded == commit:
            matched = True
            continue
        if just_written:
            raise ProductUnavailable(f"native {metric} did not record the publishing Clean commit")
        # Reuse an older sample with identical retained evidence only when that very
        # evidence also belongs to its recorded Clean revision in this main history.
        paths = [str(REPORT / "receipt-set.json")]
        if item["metric"] == "compiled_kcheck_decisions":
            paths = [str(BOARD), str(COVERAGE)]
        elif item["source"].startswith(PR29_COMMAND + " # "):
            manifest = PR29_REPORT / "qualification.json"
            paths = _qualification_paths(clean)
            input_sha = json.loads((clean / manifest).read_bytes())["input_sha256"]
            history = json.loads(_checked(["git", "show", f"{recorded}:data/self_proof_fleet_timeline.json"], clean, runner))
            earlier = source_event(history["events"])
            certified = _digest((clean / manifest).read_bytes())
            if not earlier or earlier.get("qualification_sha256") != certified or earlier.get("input_sha256") != input_sha:
                raise ProductUnavailable(f"native {metric} has no matching PR-29 observation at its recorded revision")
        elif item["metric"] == "stock_ck0_const_helper_candidate_admitted":
            manifest = TRIAL_REPORT / "result.json"
            artifacts = json.loads((clean / manifest).read_bytes())["artifacts"]
            paths += [str(manifest), *(str(TRIAL_REPORT / name) for name in artifacts)]
        if (runner(["git", "merge-base", "--is-ancestor", recorded, commit], clean).returncode
                or runner(["git", "diff", "--quiet", recorded, commit, "--", *paths], clean).returncode):
            raise ProductUnavailable(f"native {metric} receipt cannot be bound to the same Clean evidence")
        matched = True
    return matched


def _sync_native(row, status, commit, publish, runner, clean):
    metric = f"{GOAL}.{row['metric']}"
    if metric not in status["capabilities"]["native_metric_ids"]:
        raise ProductUnavailable(f"native {metric} has no live E1 registration in declarations")
    command = ["aterm", "goals", "measure", metric, str(row["value"]), "--source", row["source"]]
    row["native_candidate"] = command
    samples = _native_measures(metric, runner, clean) if publish else status["measurements"]
    if _resident_sample(samples, row, commit, runner, clean):
        row["state"] = "present"
    elif publish:
        row["state"] = "unconfirmed"
        _checked(command, clean, runner)
        if not _resident_sample(_native_measures(metric, runner, clean), row, commit, runner, clean, just_written=True):
            raise ProductUnavailable(f"native {metric} append was not confirmed by the local typed log")
        row["state"] = "published"
    if row["state"] in ("present", "published"):
        row["confirmation"] = "local typed measure log"


def sync_product(snapshot, clean_commit, publication_root, *, clean_root=ROOT, publish=False, runner=_run,
                 w0_shadow=None, w0_native=None):
    """Preview or publish measured E1 evidence. The caller supplies its own publication checkout."""
    if w0_native is not None:
        if publish:
            raise ProductUnavailable("native W0 reading requires Product Planning preview")
        if w0_shadow is not None:
            raise ProductUnavailable("native W0 reading cannot be combined with the W0 shadow")
    if w0_shadow is not None and publish:
        raise ProductUnavailable("native W0 comparison requires Product Planning preview")
    root = Path(publication_root).resolve()
    clean = Path(clean_root).resolve()
    status = product_status(root, clean_root=clean, runner=runner)
    native = status["backend"] == "aterm"
    result = {"project": PROJECT, "goal": GOAL, "state": "preview", "backend": status["backend"],
              "capabilities": status["capabilities"],
              "measurements": [], "deferred": []}
    w0_build = w0_native if w0_native is not None else w0_shadow
    w0_result_key = "w0_native" if w0_native is not None else "w0_native_shadow"
    if w0_build is not None:
        result[w0_result_key] = {"state": "deferred"}
    if w0_native is not None:
        result[w0_result_key]["method"] = "clean evidence status --scoreboard --check"
    if not native and not publish and status["state"] == "available":
        result.update(publication_commit=status["publication_commit"], publication_source=status["publication_source"])
    try:
        _validate_snapshot(snapshot, clean_commit)
        if status["state"] != "available":
            raise ProductUnavailable(status["reason"])
        if publish:
            head = _checked(["git", "rev-parse", "HEAD"], clean, runner).strip()
            if head != clean_commit:
                raise ProductUnavailable("requested Clean commit differs from the current checkout")
            if runner(["git", "merge-base", "--is-ancestor", clean_commit, "refs/remotes/origin/main"], clean).returncode:
                raise ProductUnavailable("Clean source commit is outside known origin/main history")
            if not native:
                if status["publication_commit"] is None:
                    raise ProductUnavailable("an offline tracker working copy cannot publish measurements")
                _publication_check(root, runner)
        # An unpublished bridge row cannot satisfy a retry. Native samples are checked in Clean's cwd.
        existing = [] if native else (_published_rows(root, runner) if publish else status["measurements"])
        readings = []
        for producer in (_root_readings, _production_reading, _const_trial_readings):
            compare_w0 = w0_build is not None and producer is _production_reading
            try:
                if compare_w0 and w0_native is not None:
                    produced = producer(snapshot, clean, clean_commit, runner, check_python=False)
                else:
                    produced = producer(snapshot, clean, clean_commit, runner)
                if compare_w0:
                    result[w0_result_key].update(_preview_w0_candidate(
                        clean, clean_commit, runner, w0_build, guard_identity=w0_native is not None))
                readings.extend(produced if isinstance(produced, list) else [produced])
            except (OSError, ValueError, KeyError, TypeError) as err:
                if compare_w0:
                    result[w0_result_key]["reason"] = str(err)
                result["deferred"].append(str(err))
        keys = {_identity(row) for row in existing}
        for row in readings:
            item = {**row, "state": "present" if _identity(row) in keys else "candidate"}
            result["measurements"].append(item)
            if native:
                try:
                    _sync_native(item, status, clean_commit, publish, runner, clean)
                except (OSError, ValueError) as err:
                    if item["state"] == "unconfirmed":
                        # The append may have happened. A retry reads its receipt first.
                        raise
                    item["state"] = "deferred"
                    result["deferred"].append(str(err))
                continue
            if not publish or item["state"] == "present":
                continue
            command = [sys.executable, "-B", str(root / "goals/tools/goals.py"), "measure", GOAL,
                       "--metric", row["metric"], "--value", str(row["value"]), "--unit", row["unit"],
                       "--source", row["source"], "--note", row["note"], "--push"]
            try:
                _checked(command, root, runner)
                keys = {_identity(record) for record in _published_rows(root, runner)}
                if _identity(row) not in keys:
                    raise ProductUnavailable(f"published tracker row could not be confirmed for {row['metric']}")
            except (OSError, ValueError) as err:
                item["state"] = "unconfirmed"
                raise ProductUnavailable(str(err)) from err
            item["state"] = "published"
        if publish:
            result["state"] = "published" if any(r["state"] == "published" for r in result["measurements"]) else "unchanged"
    except (OSError, ValueError, KeyError, TypeError) as err:
        if w0_native is not None and result[w0_result_key]["state"] == "deferred":
            result[w0_result_key].setdefault("reason", str(err))
        result["deferred"].append(str(err))
    if result["deferred"]:
        result["state"] = "partial" if any(r["state"] in ("present", "published", "candidate")
                                           for r in result["measurements"]) else "deferred"
    return result
