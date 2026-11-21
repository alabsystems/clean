# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Read the retained soundness-root measurements at their recorded source revisions."""

from __future__ import annotations

from datetime import date
import gzip
import hashlib
import io
import json
from pathlib import Path
import re
import subprocess
import zlib

if __package__:
    from .kcheck_coverage_readers import derive as derive_coverage
    from .kcheck_coverage_export import Refused, nat, no_number, once, sha
else:
    from kcheck_coverage_readers import derive as derive_coverage
    from kcheck_coverage_export import Refused, nat, no_number, once, sha

_ROOT = "KCheck.CompleteSound.kcheck_sound"
_MODULE = "KCheck.CompleteSound"
_AXIOMS = {"propext", "Quot.sound"}
_STREAM = "clean-kcheck-sound.ndjson.gz"
_FILES = {_STREAM, "writer.json", "provenance.json", "corrected-resident.json",
          "corrected-upstream.json", "fenced-clean.json", "prefix-comparison.json",
          "missing-axiom.txt"}
_ORDINARY = {"def", "thm", "opaque", "quot", "axiom"}
_ROUND_TRIP = "read back by Clean's reader and written again, byte-identical"
_READER = "lean4export Export.parseStream"
_Q4_REPORT = "reports/self-proof-q4-corrected-reference-2026-11-18"
_Q4_ROOT_REPLAYS = {_Q4_REPORT + "/root/replay.json", _Q4_REPORT + "/main-362fac/root/replay.json"}


def _require(condition, reason):
    if not condition:
        raise Refused(reason)


def _object(value):
    _require(isinstance(value, dict), "expected a JSON object")
    return value


def _json(raw):
    return _object(json.loads(raw, object_pairs_hook=once, parse_constant=no_number))


def _counts(obj, expected):
    for field, value in expected.items():
        _require(nat(obj[field]) == value, f"receipt count {field} disagrees with the export")


def _axioms(value):
    _require(isinstance(value, list) and len(value) == len(_AXIOMS) and set(value) == _AXIOMS,
             "permitted or observed axioms differ from the exact soundness-root basis")


def _names_of_record(kind, body):
    if kind in _ORDINARY:
        return [body["name"]]
    _require(kind == "inductive" and set(body) == {"types", "ctors", "recs"},
             "unknown declaration record")
    _require(all(isinstance(body[key], list) for key in body) and body["types"],
             "an inductive block has no types or invalid member lists")
    return [member["name"] for key in ("types", "ctors", "recs") for member in body[key]]


def _scan(compressed, *, declaration_names=None, required_theorems=()):
    # Retain structured names to distinguish separate components from a quoted dot.
    # Count expressions in stream order without materializing the whole proof DAG.
    names = [()]
    declared = set()
    missing_theorems = set(required_theorems)
    axioms = set()
    exprs = levels = records = total = 0
    blocks = quotients = outside_seed = 0
    digest = hashlib.sha256()
    nonheader = hashlib.sha256()
    prefix = None
    terminal = None
    with gzip.GzipFile(fileobj=io.BytesIO(compressed)) as stream:
        for line, raw in enumerate(stream, 1):
            _require(raw.endswith(b"\n"), "an export row lacks its terminating newline")
            digest.update(raw)
            total += len(raw)
            row = _json(raw)
            terminal = None
            if line == 1:
                _require(set(row) == {"meta"}, "first export row lacks an exclusive metadata header")
                meta = _object(row["meta"])
                header = raw
                continue
            if prefix is None:
                nonheader.update(raw)
            indices = set(row) & {"ie", "il", "in"}
            if indices:
                _require(len(indices) == 1 and len(row) == 2, "ambiguous export table record")
                index = indices.pop()
                number = nat(row[index])
                if index == "ie":
                    _require(number == exprs, "expression table has an index gap")
                    exprs += 1
                elif index == "il":
                    _require(number == levels + 1, "level table has an index gap")
                    levels += 1
                else:
                    _require(number == len(names), "name table has an index gap")
                    kind = next(key for key in row if key != "in")
                    _require(kind in ("str", "num"), "unknown name component")
                    part = _object(row[kind])
                    parent = names[nat(part["pre"])]
                    component = part["str"] if kind == "str" else nat(part["i"])
                    _require(kind != "str" or isinstance(component, str), "invalid string name")
                    names.append(parent + (component,))
                continue
            _require(len(row) == 1, "ambiguous declaration record")
            kind, body = next(iter(row.items()))
            members = [names[nat(index)] for index in _names_of_record(kind, _object(body))]
            _require(all(members) and len(set(members)) == len(members)
                     and declared.isdisjoint(members), "duplicate or anonymous declaration")
            declared.update(members)
            if kind == "thm":
                missing_theorems.discard(members[0])
            if declaration_names is not None:
                declaration_names.extend(members)
            records += 1
            if kind == "inductive":
                blocks += 1
                outside_seed += sum(names[type_row["name"]] not in {("Eq",), ("PUnit",), ("Nat",)}
                                    for type_row in body["types"])
            elif kind == "quot":
                quotients += 1
            if kind == "axiom":
                axioms.add(members[0])
            if prefix is None:
                prefix_kind = kind
                first = ".".join(map(str, members[0]))
                prefix = {"first": first, "lines": line, "bytes": total,
                          "prefix_sha256": digest.hexdigest(), "header_sha256": sha(header),
                          "terminal_record_sha256": sha(raw), "all_non_header_bytes": total - len(header),
                          "all_non_header_sha256": nonheader.hexdigest()}
            terminal = (kind, members[0], body)
    _require(not missing_theorems, "PR-29 export omits the named caller or helper theorem")
    _require(terminal is not None and terminal[:2] == ("thm", tuple(_ROOT.split("."))),
             "last export record is not the qualified root theorem")
    _require(nat(terminal[2]["value"]) < exprs and nat(terminal[2]["type"]) < exprs,
             "root theorem does not refer to a stored proof and statement")
    _require(axioms == {tuple(name.split(".")) for name in _AXIOMS}, "export axiom basis differs")
    counts = {"records": records, "declarations": len(declared), "bytes": total,
              "exprs": exprs, "names": len(names) - 1, "levels": levels, "lines": line}
    workload = {"inductive_blocks": blocks, "quotient_records": quotients,
                "outside_named_seed_types": outside_seed}
    return digest.hexdigest(), counts, meta, prefix, prefix_kind, workload


def _check_prefix(comparison, digest, prefix, kind):
    """Qualify one declaration-terminated prefix. Any longer run needs its own receipt profile."""
    _require(comparison["source_stream_sha256"] == digest, "prefix probe identifies other export bytes")
    probe = comparison["cone-final"]
    for field, actual in prefix.items():
        saved = probe[field]
        _require(type(saved) is type(actual) and saved == actual,
                 f"prefix {field} differs from the bytes up through the first declaration")
    _require(probe["label"] == "cone-final" and probe["checker_stderr"] == "",
             "prefix checker reported a loader or invocation problem")
    name, line = prefix["first"], prefix["lines"]
    _require(name and not any(char in name for char in "\r\n"), "ambiguous prefix transcript name")
    output = probe["checker_stdout"]
    _require(isinstance(output, str), "prefix checker stdout is not text")
    if kind == "inductive":
        diagnostic, separator, output = output.partition("\n")
        traced = re.fullmatch(
            rf"line={line} name={re.escape(name)} knownFamily=(true|false) "
            r"recognisedRows=(true|false) unitTemplate=(?:true|false)", diagnostic)
        _require(separator and traced and traced.groups() != ("true", "false"),
                 "prefix trace differs from the first export record or signals a loader refusal")
    exit_code = nat(probe["checker_exit"])
    if exit_code == 0 and output == f"accepted receipt={name}\n":
        return 1, None
    refused = re.fullmatch(rf"refused name={re.escape(name)} reason=(KCheck\.Refusal\.\w+(?: [^\r\n]+)?)\n",
                           output)
    _require(exit_code == 1 and refused, "prefix checker lacks a matching explicit verdict and exit")
    return 0, {"name": name, "line": line, "reason": refused[1]}


def _commit(value):
    _require(isinstance(value, str) and re.fullmatch(r"[0-9a-f]{40}", value),
             "missing or malformed historical source revision")
    return value


def _read(directory):
    manifest = _json((directory / "receipt-set.json").read_bytes())
    _require(manifest["schema"] == "clean-self-proof-root-receipts-v1" and manifest["root"] == _ROOT,
             "receipt set does not identify the qualified root and schema")
    files = _object(manifest["files"])
    _require(set(files) == _FILES, "receipt set does not bind exactly the required files")
    receipts = {}
    for filename in sorted(_FILES):
        data = (directory / filename).read_bytes()
        _require(sha(data) == files[filename], f"receipt hash mismatch for {filename}")
        receipts[filename] = _json(data) if filename.endswith(".json") else data

    digest, counts, meta, prefix, prefix_kind, workload = _scan(receipts[_STREAM])
    writer = receipts["writer.json"]
    provenance = receipts["provenance.json"]
    _require(digest == manifest["input_sha256"] == writer["written"]["sha256"] == provenance["export_sha256"],
             "export digest differs across stream, manifest, writer or provenance")
    _counts(writer["written"], counts)
    _axioms(writer["written"]["axioms"])
    _require(nat(writer["targets"]) == 1 and writer["modules"] == [_MODULE]
             and writer["round_trip"] == _ROUND_TRIP, "writer lacks the single-root round-trip result")
    _require(provenance["tracked_inputs_clean"] is True and nat(provenance["export_bytes"]) == counts["bytes"],
             "unclean or inconsistent export provenance")
    public_commit = _commit(provenance["public_source_commit"])
    lean_commit = _commit(provenance["lean_module_source"])
    _require(provenance["theory_libs_revision"] == lean_commit, "Lean module source differs within provenance")
    command = provenance["writer_command"]
    _require(isinstance(command, list) and command.count("--target") == 1
             and command[command.index("--target") + 1] == _ROOT, "writer command selects a different root")
    resident = receipts["corrected-resident.json"]
    upstream = receipts["corrected-upstream.json"]
    fenced = receipts["fenced-clean.json"]
    lean = meta["lean"]
    _require(lean == {"version": "4.30.0-rc2", "githash": "3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc"}
             and meta["format"] == {"version": "3.1.0"} and meta["exporter"]["name"] == "clean-export"
             and provenance["sdk_githash"] == lean["githash"], "different SDK or format in proof provenance")
    for receipt in (writer, resident, upstream, fenced["meta"]):
        _require(receipt["lean_version"] == lean["version"] and receipt["lean_githash"] == lean["githash"],
                 "replay or comparison used a different Lean SDK")
    count = counts["declarations"]
    _counts(resident, {"compared": count, "equal": count, "differing_count": 0})
    _require(resident["modules"] == [_MODULE] and resident["reader"] == _READER
             and resident["against"] == "Lean's environment (importModules)" and resident["verdict"] == "equal"
             and resident["absent"] == [] and resident["differing"] == [] and resident["differing_by_field"] == {},
             "resident comparison lacks complete field equality")
    _counts(upstream, {"declarations": count, "order": count})
    _axioms(upstream["axioms"])
    _axioms(upstream["permitted"])
    _require(upstream["verdict"] == "accepted" and upstream["reader"] == _READER
             and upstream["kernel"] == "Lean.Environment.replay", "upstream did not accept the complete export")
    _counts(fenced, {"declarations": count, "admitted": count})
    _axioms(fenced["axioms"])
    _require(fenced["accepted"] is True and fenced["reader_error"] is None and fenced["refusals"] == []
             and fenced["unpermitted_axioms"] == [] and fenced["meta"]["rule_set"] == "lean-v4-30-rc2"
             and fenced["meta"]["exporter_name"] == meta["exporter"]["name"]
             and fenced["meta"]["exporter_version"] == meta["exporter"]["version"]
             and fenced["meta"]["format_version"] == meta["format"]["version"],
             "fenced checker did not admit the complete export")
    permits = provenance["fenced_command"]
    _require(isinstance(permits, list) and "--reference" in permits, "missing fenced reference command")
    _axioms([permits[i + 1] for i, arg in enumerate(permits) if arg == "--permit"])
    _require(receipts["missing-axiom.txt"].splitlines() == [
        b"exit 1", b"lean_export_replay: REJECTED: axioms outside the permitted set: #[Quot.sound]"],
        "missing-axiom negative control does not record the expected refusal")
    prefix_accepted, refusal = _check_prefix(receipts["prefix-comparison.json"], digest, prefix, prefix_kind)
    return {"state": "measured", "sha256": digest, "root": _ROOT, "declarations": count,
            "records": counts["records"], "resident_equal": resident["equal"], "fenced_admitted": fenced["admitted"],
            "upstream_admitted": upstream["order"], "prefix_accepted": prefix_accepted, "first_refusal": refusal,
            "public_source_commit": public_commit, "lean_module_source": lean_commit, **workload}


def read_export_evidence(report_dir: Path) -> dict:
    """Return hash-bound historical measurements or the reason the receipts are unavailable."""
    try:
        return _read(report_dir)
    except (OSError, EOFError, zlib.error, ValueError, TypeError, KeyError, IndexError, RecursionError, Refused) as exc:
        return {"state": "unverified", "reason": str(exc) or type(exc).__name__}


def read_const_trial(directory: Path, event: dict, baseline: dict) -> dict:
    """Read the independent exit receipt pinned by the dated PR-28 observation."""
    try:
        raw = (directory / "result.json").read_bytes()
        _require(sha(raw) == event["result_sha256"], "PR-28 exit receipt digest differs")
        result = _json(raw)
        _require(result["schema"] == "clean.q4.const-branch-trial.v1" and result["root"] == _ROOT,
                 "PR-28 receipt is for another proof")
        _require(baseline.get("state") == "measured" and
                 result["baseline_input_sha256"] == baseline.get("sha256") == event["baseline_input_sha256"],
                 "PR-28 baseline differs from the measured export")
        candidate = result["input_sha256"]
        _require(isinstance(candidate, str) and re.fullmatch(r"[0-9a-f]{64}", candidate)
                 and candidate == event["input_sha256"] and candidate != result["baseline_input_sha256"],
                 "PR-28 candidate identity differs")
        parts = _object(result["artifacts"])
        _require({"candidate.ndjson.gz", "candidate-ck0-verdicts.ndjson.gz", "adopted-prefix.json",
                  "candidate-lean.json", "candidate-fenced.json"} <= parts.keys(), "incomplete PR-28 archive")
        for name, pin in parts.items():
            _require(name not in (".", "..") and Path(name).name == name, "invalid PR-28 artifact path")
            data = (directory / name).read_bytes()
            _require(nat(pin["bytes"]) == len(data) and sha(data) == pin["sha256"],
                     f"PR-28 artifact differs: {name}")
        vote = result["stock_outcomes"]["candidate"]
        accepted, named = nat(vote["accepted"]), nat(vote["named"])
        _require(named > 0 and accepted == named and vote["root_accepted"] is True,
                 "PR-28 receipt lacks the full candidate root vote")
        original = result["stock_outcomes"].get("baseline")
        prior = {}
        if original is not None:
            previous = nat(original["named"])
            admitted = nat(original["accepted"])
            _require(previous == baseline.get("declarations") and admitted < previous
                     and nat(original["refused"]) == previous - admitted and original["root_accepted"] is False,
                     "PR-28 original stock vote disagrees with its baseline")
            prior = {"baseline_stock_admitted": admitted, "baseline_named": previous}
        return {**prior, "state": "recorded", "result_sha256": sha(raw), "input_sha256": candidate,
                "baseline_input_sha256": result["baseline_input_sha256"],
                "stock_admitted": accepted, "named": named, "root": _ROOT, "root_accepted": True}
    except (OSError, ValueError, TypeError, KeyError, Refused) as exc:
        return {"state": "unverified", "reason": str(exc) or type(exc).__name__}


_PR29_CALLER = "KCheck.conv_sound_step"
_PR29_HELPER = _PR29_CALLER + "._proof_1_10"
PR29_REPORT = Path("reports/self-proof-const-helper-adoption")
PR29_COMMAND = f"python3 {PR29_REPORT}/verify.py"
_PR29_LOGS = {"outputs.json.gz", "per-name.ndjson.gz", "stock-verdicts.ndjson.gz"}
_PR29_REQUIRED = _PR29_LOGS | {"replay.json", "census.json", "labelled/result.json", "exit.json",
    "record_qualification.py", "verify.py", "replay.py", "labelled.py", "verify_census.py",
    "aggregate.stdout.gz", "aggregate.stderr.gz",
    "e7-baseline.log.gz", "e7-mint.log.gz", "e7-comparison.log.gz",
    "labelled/initial.json", "labelled/initial.log.gz", "labelled/final.json", "labelled/final.log.gz"}
_SHARED_SUBJECT = "../self-proof-const-branch-trial/candidate.ndjson.gz"


def event_units(event):
    """Return the event's subject and the distinct obligations it informs."""
    units = [event["unit"]]
    if "obligation" in event:
        units.append(event["obligation"])
    related = event.get("related_obligations", [])
    if not isinstance(related, list):
        raise ValueError("expected a list of related timeline obligations")
    units.extend(related)
    if (any(not isinstance(unit, str) or not unit.strip() or unit != unit.strip() for unit in units)
            or len(set(units)) != len(units)):
        raise ValueError("invalid or duplicate timeline obligation")
    return units


def displayed_events(events, qualification, followups=None, quorum_history=(), *, receipts=None):
    current = qualification or {}
    verified = followups or {}
    visible = []
    for event in events:
        pinned = receipts is not None and "source_sha256" in event
        if (pinned or _has_replay_pin(event)) and not execution_matches(event, receipts or {}):
            continue
        unit = event.get("unit")
        if event.get("kind") == "measurement":
            if unit == "Q4" and event.get("source") in _Q4_ROOT_REPLAYS:
                if not any(row["source"] == event["source"] and row["source_revision"] == event.get("source_revision")
                           and row["source_sha256"] == event.get("source_sha256")
                           and row["input_sha256"] == event.get("input_sha256", row["input_sha256"])
                           and row["input_sha256"] == current.get("input_sha256") for row in quorum_history):
                    continue
            if unit == "PR-29" and not (current.get("state") == "qualified" and event.get("obligation") == "Q4"
                    and event.get("qualification_sha256") == current["qualification_sha256"]
                    and event.get("input_sha256") == current["input_sha256"]):
                continue
            if unit == "W6" and "PR-32" in event.get("related_obligations", []):
                observed = verified.get("PR-32")
                if not observed or not all(observed.get(key) and observed[key] == event.get(key)
                        for key in ("receipt_sha256", "module_digest", "source_revision")):
                    continue
            if unit == "W3" and event.get("measurement") == "digest-library":
                library = verified.get("W3-digest-library")
                if not library or event.get("source") != W3_DIGEST_RECEIPT or (
                        event.get("source_revision"), event.get("source_sha256")) != (
                        library.get("source_revision"), library.get("qualification_sha256")):
                    continue
            if unit in {"PR-49", "PR-67"}:
                reading = verified.get(unit)
                if (not reading or reading.get("qualification_sha256") != event.get("source_sha256")
                        or reading.get("source_revision") != event.get("source_revision")):
                    continue
            if unit == "PR-67" and (verified[unit].get("input_sha256") != event.get("input_sha256")
                    or verified[unit].get("qualification_sha256") != event.get("qualification_sha256")):
                continue
            if unit in _FOLLOWUP_REPORTS:
                observed = verified.get(unit)
                if not observed or not all(observed.get(key) and observed[key] == event.get(key)
                        for key in ("input_sha256", "qualification_sha256", "source_revision")):
                    continue
        visible.append(event)
    return visible


def source_event(events):
    return next((row for row in reversed(events) if row.get("unit") == "PR-29"
                 and row.get("obligation") == "Q4" and row.get("kind") == "measurement"), None)


def source_qualification_command(current):
    return (f"{PR29_COMMAND} # qualified_revision={current['qualified_revision']} "
            f"qualification_sha256={current['qualification_sha256']} export_sha256={current['input_sha256']}")


def _check_source_stock(directory, replay, run, declaration_names):
    total = len(declaration_names)
    stock = gzip.decompress((directory / "stock-verdicts.ndjson.gz").read_bytes())
    ledger = gzip.decompress((directory / "per-name.ndjson.gz").read_bytes())
    _require(sha(stock) == replay["stock_stdout_sha256"] == run["stdout_sha256"]
             and sha(ledger) == replay["per_name_sha256"], "PR-29 named verdict transcripts differ")
    stock_rows, ledger_rows = stock.splitlines(), ledger.splitlines()
    _require(len(stock_rows) == total + 1 and len(ledger_rows) == total, "PR-29 per-name verdict count differs")
    coverage = _json(stock_rows.pop())
    stock_axioms = [[{"str": part} for part in name.split(".")] for name in sorted(_AXIOMS)]
    _require(coverage["kind"] == "coverage" and nat(coverage["total"]) == nat(coverage["accepted"]) == total
             and coverage["refused"] == {} and len(coverage["axioms"]) == len(stock_axioms)
             and all(name in coverage["axioms"] for name in stock_axioms), "PR-29 stock summary disagrees")
    for name, stock_line, ledger_line in zip(declaration_names, stock_rows, ledger_rows):
        vote, row = _json(stock_line), _json(ledger_line)
        components = [{"str": part} if isinstance(part, str) else {"num": str(part)} for part in name]
        _require(vote["kind"] == "declaration" and vote["name"] == row["name"] == components and vote["accepted"] is row["stock"] is True
                 and row["lean"] == row["fenced"] == "admitted", "PR-29 named verdict row disagrees")


def _check_source_labelled(directory, labelled):
    _require(labelled == _json((directory / "labelled/result.json").read_bytes())
             and labelled["target"] == "kcheck_labelled" and labelled["helper"] == _PR29_HELPER
             and nat(labelled["passed"]) == 2 and nat(labelled["failed"]) == nat(labelled["filtered"]) == 0,
             "PR-29 aggregate does not contain its successful labelled subcheck")
    for old, new in (("preserved_closure_rows", "closure_rows"), ("preserved_statement_or_body_pins", "statement_or_body_pins")):
        _require(nat(labelled[old]) > 0 and nat(labelled[new]) == nat(labelled[old]) + 1,
                 "PR-29 labelled subcheck does not record a single helper addition")
    for phase, expected_exit, tally in (("initial", 101, "FAILED. 1 passed; 1 failed"),
                                        ("final", 0, "ok. 2 passed; 0 failed")):
        run = _json((directory / "labelled" / f"{phase}.json").read_bytes())
        log = gzip.decompress((directory / "labelled" / f"{phase}.log.gz").read_bytes())
        summary = labelled[f"{phase}_run"]
        _require(summary["source"] == _commit(run["source_commit"])
                 and nat(summary["exit"]) == nat(run["exit"]) == expected_exit
                 and summary["transcript"] == f"{phase}.log.gz"
                 and summary["stdout_stderr_sha256"] == run["stdout_stderr_sha256"] == sha(log)
                 and f"test result: {tally}; 0 ignored; 0 measured; 0 filtered out;".encode() in log,
                 f"PR-29 labelled {phase} run disagrees with its retained result")
        if phase == "initial":
            _require(b"observed axiom closures differ from theories/kcheck_labelled/axiom_closures.json" in log,
                     "PR-29 initial labelled run failed for a different reason")
        else:
            controls = labelled["controls"]
            starts = ("labelled full index:", "kcheck_labelled subjects ", "partial C3:")
            _require(isinstance(controls, list) and len(controls) == len(starts)
                     and all(isinstance(line, str) and line.startswith(prefix) and line.encode() in log.splitlines()
                             for line, prefix in zip(controls, starts)), "PR-29 labelled controls disagree")


def _check_source_census(directory, labelled, e7):
    census = _json((directory / "census.json").read_bytes())
    helper = census["helper"]
    _require(census["schema"] == "clean.pr29.census.v1" and helper["declaration"] == _PR29_HELPER
             and helper["kind"] == "theorem" and helper["module"] == "KCheck.ConvSound"
             and helper["package"] == "kcheck_labelled" and labelled["helper_statement_pin"] == census["helper_statement_pin"]
             and labelled["helper_closure"] == census["helper_labelled_closure"], "PR-29 E7 helper disagrees with labelled")
    _axioms(helper["axiom_closure"])
    _require(re.fullmatch(r"[0-9a-f]{64}", labelled["helper_statement_pin"]) and
             labelled["helper_closure"] == sorted(_AXIOMS | {"Quot", "Quot.ind", "Quot.lift", "Quot.mk"}),
             "PR-29 labelled helper has an invalid statement pin or quotient inventory")
    counts = {}
    for phase in ("baseline", "mint", "comparison"):
        run = census["runs"][phase]
        log = gzip.decompress((directory / f"e7-{phase}.log.gz").read_bytes())
        verdict = b"LEAN_AXIOM_CENSUS=ok minted" if phase == "mint" else b"LEAN_AXIOM_CENSUS=ok"
        _require(nat(run["exit"]) == 0 and sha(log) == run["log_sha256"] and verdict in log.splitlines(),
                 f"PR-29 E7 {phase} result disagrees with its transcript")
        rows = re.findall(rb"^([a-z0-9_]+): declarations=([0-9]+) ", log, re.MULTILINE)
        counts[phase] = {name: int(value) for name, value in rows}
        _require(rows and len(rows) == len(counts[phase]), f"PR-29 E7 {phase} package counts are missing or repeated")
    before, after = counts["baseline"], counts["comparison"]
    _require(before.keys() == after.keys() and counts["mint"] == after and
             all(after[name] == value + (name == b"kcheck_labelled") for name, value in before.items())
             and b"kcheck_labelled" in before, "PR-29 E7 package counts disagree")
    _require(e7 == {"added": _PR29_HELPER, "packages": len(after),
                    "before": sum(before.values()), "after": sum(after.values()),
                    "qualified_source": _commit(census["qualified_revision"])},
             "PR-29 aggregate does not contain its registered E7 subcheck")


def _source_subchecks(directory, stdout):
    # verify.py writes exactly three JSON objects in execution order.
    decoder = json.JSONDecoder(object_pairs_hook=once, parse_constant=no_number)
    rest = stdout.decode().strip()
    observations = []
    for _ in range(3):
        value, end = decoder.raw_decode(rest)
        observations.append(_object(value))
        rest = rest[end:].lstrip()
    _require(not rest, "unexpected output after the PR-29 registered exit")
    labelled, e7, exit_row = observations
    _check_source_labelled(directory, labelled)
    _check_source_census(directory, labelled, e7)
    return exit_row


def read_source_qualification(directory: Path, event: dict) -> dict:
    """Read the measured PR-29 package exit and its named, byte-bound replay on the joined source."""
    try:
        raw = (directory / "qualification.json").read_bytes()
        receipt = _json(raw)
        _require(event == source_event([event]) and date.fromisoformat(event["date"]).isoformat() == event["date"]
                 and sha(raw) == event["qualification_sha256"],
                 "PR-29 observation does not bind this qualification")
        revision = _commit(receipt["qualified_revision"])
        _require(receipt["schema"] == "clean.pr29.source-qualification.v1" and nat(receipt["exit"]) == 0
                 and receipt["exit_command"] == PR29_COMMAND, "PR-29 full package exit is unavailable")
        files = _object(receipt["artifacts"])
        _require(_PR29_REQUIRED <= files.keys(), "incomplete PR-29 evidence archive")
        for name, pin in files.items():
            path = Path(name)
            _require(path.parts and not path.is_absolute() and ".." not in path.parts and str(path) == name
                     and (directory / path).resolve().is_relative_to(directory.resolve()), "invalid PR-29 evidence path")
            _require(sha((directory / path).read_bytes()) == pin, f"PR-29 evidence differs: {name}")
        manifest = _json((directory / "replay.json").read_bytes())
        replay = _object(manifest["replay"])
        _require(nat(manifest["schema"]) == 1 and replay["root"] == _ROOT, "PR-29 replay is for another proof")
        subject = manifest["retained_export"]
        _require((subject == _SHARED_SUBJECT and replay["trial_input_identical"] is True)
                 or (subject == "current.ndjson.gz" and replay["trial_input_identical"] is False and subject in files),
                 "PR-29 replay has an unsupported or unbound subject")
        replay_files = _object(manifest["files"])
        expected_files = _PR29_LOGS if subject == _SHARED_SUBJECT else _PR29_LOGS | {subject}
        _require(set(replay_files) == expected_files and all(files[name] == pin for name, pin in replay_files.items()),
                 "PR-29 replay archive bindings differ")
        declaration_names = []
        _require(replay["helper"] == _PR29_HELPER, "PR-29 replay identifies a different helper")
        digest, counts, _, prefix, kind, _ = _scan(
            (directory / subject).read_bytes(), declaration_names=declaration_names,
            required_theorems=[tuple(name.split(".")) for name in (_PR29_CALLER, _PR29_HELPER)])
        _require(digest == replay["input_sha256"] == receipt["input_sha256"] == event["input_sha256"],
                 "PR-29 observation or replay identifies other export bytes")
        _counts(replay, {key: counts[key] for key in ("records", "declarations", "bytes")})
        names = counts["declarations"]
        _require(nat(replay["resident_equal"]) == names, "PR-29 resident comparison is incomplete")
        for member in ("lean", "fenced", "stock"):
            vote = replay["members"][member]
            _require(nat(vote["named"]) == nat(vote["accepted"]) == names
                     and all(vote[field] is True for field in ("root_accepted", "helper_accepted", "caller_accepted")),
                     f"incomplete PR-29 {member} vote")
        outputs = _json(gzip.decompress((directory / "outputs.json.gz").read_bytes()))
        runs = manifest["identities"]["runs"]
        for member in ("lean", "fenced", "stock", "resident"):
            _require(runs[member]["input_sha256"] == digest and nat(runs[member]["exit"]) == 0,
                     f"PR-29 {member} used different bytes or failed")
        for member in ("lean", "fenced", "resident", "adopted-prefix"):
            for channel in ("stdout", "stderr"):
                _require(sha(outputs[f"{member}.{channel}"].encode()) == runs[member][f"{channel}_sha256"],
                         f"PR-29 {member} {channel} disagrees with its run receipt")
        resident = _json(outputs["resident.stdout"])
        _require(resident["verdict"] == "equal" and nat(resident["compared"]) == nat(resident["equal"]) == names
                 and resident["absent"] == resident["differing"] == [] and nat(resident["differing_count"]) == 0,
                 "PR-29 resident transcript disagrees")
        lean = _json(outputs["lean.stdout"])
        fenced = _json(outputs["fenced.stdout"])
        _axioms(lean["permitted"])
        _axioms(lean["axioms"])
        _axioms(fenced["axioms"])
        _require(lean["verdict"] == "accepted" and nat(lean["order"]) == nat(lean["declarations"]) == names
                 and fenced["accepted"] is True and nat(fenced["admitted"]) == nat(fenced["declarations"]) == names
                 and fenced["refusals"] == fenced["unpermitted_axioms"] == [], "PR-29 member transcripts disagree")
        _check_source_stock(directory, replay, runs["stock"], declaration_names)
        probe = runs["adopted-prefix"]
        _require(probe["input_sha256"] == replay["adopted_prefix_sha256"] == prefix["prefix_sha256"],
                 "PR-29 adopted checker probed different prefix bytes")
        within, refusal = _check_prefix({"source_stream_sha256": digest, "cone-final": {
            **prefix, "label": "cone-final", "checker_exit": probe["exit"], "checker_stdout": outputs["adopted-prefix.stdout"],
            "checker_stderr": outputs["adopted-prefix.stderr"]}}, digest, prefix, kind)
        _require(refusal and refusal["name"] == replay["adopted_first_refusal"]
                 and within == nat(replay["adopted_admissions_before_first_refusal"]), "PR-29 adopted prefix disagrees")
        exit_bytes = (directory / "exit.json").read_bytes()
        stdout = gzip.decompress((directory / "aggregate.stdout.gz").read_bytes())
        _require(stdout == exit_bytes or stdout.endswith(b"\n" + exit_bytes),
                 "PR-29 verdict differs from the final output of the registered command")
        exit_row = _source_subchecks(directory, stdout)
        _require(exit_row == _json(exit_bytes) and exit_row["scope"] == "PR-29 package exit" and exit_row["input_sha256"] == digest
                 and nat(exit_row["names"]) == names and exit_row["root"] == _ROOT
                 and exit_row["lean_fenced_stock_all_admitted"] is True
                 and exit_row["adopted_first_refusal"] == refusal["name"]
                 and replay["fourth_member"]["qualified"] is False and exit_row["external_member_qualified"] is False,
                 "PR-29 aggregate exit disagrees with member receipts")
        return {"state": "qualified", "qualified_revision": revision, "qualification_sha256": sha(raw),
                "input_sha256": digest, "root": _ROOT, "declarations": names, "records": counts["records"],
                "resident_equal": replay["resident_equal"], "stock_admitted": replay["members"]["stock"]["accepted"],
                "upstream_admitted": replay["members"]["lean"]["accepted"], "fenced_admitted": replay["members"]["fenced"]["accepted"],
                "fourth_member_qualified": False, "prefix_accepted": within, "first_refusal": refusal}
    except (OSError, EOFError, zlib.error, ValueError, TypeError, KeyError, IndexError, RecursionError, Refused) as exc:
        return {"state": "unverified", "reason": str(exc) or type(exc).__name__}


# A new measurement needs its own dated observation and independent package exit.
_FOLLOWUP_REPORTS = {
    "PR-30": ("self-proof-prefix-measurement", "qualification.json",
              "434c489988450bba3ba4fc2bebb13872e47bd315", "7aa075a504b3bcdc57e96f54cd8f2eca7e08f451ec9d3b41ad2d7abe1e37c1f1"),
    "PR-31": ("self-proof-statement-dependencies", "verification.json",
              "19397daa48131bc0aa5845af4b6bb3c47cb95add", "bfee94013a582c92258274c8fa036efd436297119e43b54e695f8e7ec681a6a9"),
}


def _pin(value):
    _require(isinstance(value, str) and re.fullmatch(r"[0-9a-f]{64}", value), "invalid SHA-256")
    return value


def _pinned_file(path, pin):
    data = path.read_bytes()
    _require(sha(data) == _pin(pin), f"local receipt differs: {path.name}")
    return data


def _historical_blob(root, revision, path):
    return subprocess.check_output(["git", "--no-replace-objects", "cat-file", "blob", f"{revision}:{path}"],
                                   cwd=root, stderr=subprocess.DEVNULL)


W3_DIGEST_RECEIPT = "reports/w3-digest-library-2026-11-17/qualification.json"


def read_w3_digest_library(root, event):
    """Qualify the dated library extraction only, using its preserved gate and main intake."""
    revision = "d1fcb93841ee1c00f8657feacea37cc5c4e32c74"
    digest = "ea54b3ac0976ef7b75e6eb697ece9f79f46b0f6303cb83b743650ad865ef679e"
    if (event.get("source"), event.get("source_revision"), event.get("source_sha256")) != (
            W3_DIGEST_RECEIPT, revision, digest):
        return None
    try:
        raw = _historical_blob(root, revision, W3_DIGEST_RECEIPT)
        intake_raw = _historical_blob(root, revision, W3_DIGEST_RECEIPT.replace("qualification.json", "main-intake.json"))
        if sha(raw) != digest or sha(intake_raw) != "3fe78b9ab32e1a866b82dcb59dc1be37e4cf37ef0df6cf15e580d364857aa85e":
            return None
        gate, intake = _json(raw), _json(intake_raw)
        if (gate["head"] != intake["qualified_source_commit"] or not gate["complete"]
                or not gate["source_inputs_unchanged"] or intake["changed_qualification_inputs"]
                or any(command["exit"] != 0 for command in gate["commands"])):
            return None
        return {"source_revision": revision, "qualification_sha256": digest, "checked_revision": gate["head"],
                "commands_passed": len(gate["commands"]), "unchanged_source_inputs": gate["input_count"],
                "unchanged_pin_files": intake["pin_files_byte_exact"]}
    except (OSError, KeyError, ValueError, Refused, subprocess.CalledProcessError):
        return None


def _has_replay_pin(event):
    return bool({"replay_source", "replay_sha256", "replay_revision"}.intersection(event))


def _execution_pins(event):
    """Resolve the primary citation and any declared replay at their respective revisions."""
    try:
        revision = _commit(event["source_revision"])
        source = event["source"]
        _require(isinstance(source, str), "missing execution source")
        pins = [(revision, source.split("#", 1)[0], _pin(event["source_sha256"]))]
        if _has_replay_pin(event):
            pins.append((_commit(event.get("replay_revision", revision)),
                         event["replay_source"], _pin(event["replay_sha256"])))
        for _, path, _ in pins:
            _require(isinstance(path, str) and path and "\x00" not in path
                     and not Path(path).is_absolute() and ".." not in Path(path).parts,
                     "invalid execution artifact path")
        return pins
    except (KeyError, Refused):
        return []


def execution_matches(event, receipts):
    pins = _execution_pins(event)
    return bool(pins) and all(receipts.get(f"{rev}:{path}") == digest for rev, path, digest in pins)


def execution_receipts(root, events):
    """Retain a dated observation only after all its cited Git blobs match."""
    receipts = {}
    for event in events:
        pins = _execution_pins(event)
        try:
            if any(sha(_historical_blob(root, rev, path)) != digest for rev, path, digest in pins):
                continue
        except (OSError, subprocess.CalledProcessError):
            continue
        receipts.update((f"{rev}:{path}", digest) for rev, path, digest in pins)
    return receipts


def read_soundness_quorum_history(root, events, adoption):
    """Read frozen four-member replays of the adopted proof bytes in timeline order."""
    replays = []
    members = {"lean", "clean-reference", "ck0-stock", "lean4lean"}
    for event in events:
        path = event.get("source")
        if not adoption or event.get("unit") != "Q4" or event.get("kind") != "measurement" or path not in _Q4_ROOT_REPLAYS:
            continue
        try:
            revision = _commit(event["source_revision"])
            raw = _historical_blob(root, revision, path)
            _require(sha(raw) == _pin(event["source_sha256"]), "wrong quorum receipt digest")
            record = _json(raw)
            _require(record["schema"] == "clean.kstar-recheck.v1" and record["success"] is True
                     and record["qualified_lean4lean"] is True and nat(record["lean4lean_qualification_exit"]) == 0,
                     "unqualified quorum replay")
            subject, = record["subjects"]
            _require(subject["sha256"] == adoption["input_sha256"] and subject["accepted"] is True
                     and event.get("input_sha256", subject["sha256"]) == subject["sha256"]
                     and nat(subject["declarations"]) == adoption["declarations"]
                     and sorted(subject["input_axioms"]) == ["Quot.sound", "propext"], "different proof input")
            votes = subject["members"]
            _require(set(votes) == members and all(v["accepted"] is True and v["verdict"] == "accepted"
                     and nat(v["exit_code"]) == 0 for v in votes.values()), "missing accepted member")
            controls = record["controls"]
            _require(set(controls) == {"extra-axiom", "ill-typed-body", "forged-recursor"}
                     and all(c["accepted"] is False and c["panicked"] == [] and c["all_refused_for_reason"] is True
                             and set(c["refused_for_reason"]) == members
                             and all(value is True for value in c["refused_for_reason"].values())
                             for c in controls.values()),
                     "missing quorum refusal control")
            replays.append({"date": event["date"], "source": path, "source_revision": revision,
                            "source_sha256": event["source_sha256"], "epoch": _commit(record["source_commit"]),
                            "input_sha256": subject["sha256"], "members": sorted(members),
                            "declarations": subject["declarations"]})
        except (OSError, KeyError, TypeError, ValueError, Refused, subprocess.CalledProcessError):
            continue
    return replays


def read_soundness_quorum(root, events, adoption):
    history = read_soundness_quorum_history(root, events, adoption)
    return history[-1] if history else None


def native_matcher_text(reading):
    """Describe the interim measurement only when the partition and its targeted control agree."""
    try:
        positive, control = reading["positive"], reading["control"]
        accepted = nat(positive["accepted"])
        recognised = nat(positive["recognised_families"])
        outside = nat(positive["outside_fragment"])
        records = nat(positive["declaration_records"])
        name = reading["matcher"]["name"]
        _require(name == control["name"] and isinstance(name, str) and name, "unidentified control")
        _require(records == accepted + recognised + outside and nat(positive["refused_inside"]) == 0,
                 "incomplete positive partition")
        _require(nat(control["accepted"]) == accepted - 1 and nat(control["refused_inside"]) == 1
                 and nat(control["declaration_records"]) == records and nat(control["outside_fragment"]) == outside
                 and nat(control["recognised_families"]) == recognised
                 and nat(control["changed_frame_records"]) == 1 and nat(control["unchanged_prior_rows"]) == records - 1,
                 "different control scope")
    except (KeyError, TypeError, ValueError, Refused):
        return ""
    return (f"With native advice, the interim checker admitted {accepted} ordinary declarations "
            f"in the first {records} soundness-export records, recognised {recognised} base families "
            f"and skipped {outside} outside its fragment. Clearing the frame for {name} made it refuse.")


def read_native_matcher(root, event):
    """Bind locally re-derived interim verdicts to the enrolled proof-stream receipt."""
    if __package__:
        from .self_proof_native_matcher import verify
    else:
        from self_proof_native_matcher import verify
    source = "reports/self-proof-native-proof-prefix/matcher/qualification.json"
    try:
        _require(event["source"] == source, "wrong matcher archive")
        revision = _commit(event["source_revision"])
        raw = _historical_blob(root, revision, source)
        digest = _pin(event["source_sha256"])
        _require(sha(raw) == digest == event["qualification_sha256"], "matcher receipt changed")
        receipt = _json(raw)
        _require(receipt["source_sha256"] == _pin(event["input_sha256"]), "different proof stream")
        _require(verify(root) == receipt, "the checker verdicts differ from the enrolled receipt")
        return {"state": "measured", "input_sha256": receipt["source_sha256"], "source_revision": revision,
                "qualification_sha256": digest, "positive": receipt["positive"], "control": receipt["control"],
                "matcher": receipt["matcher"]}
    except (OSError, ValueError, TypeError, KeyError, EOFError, zlib.error, subprocess.CalledProcessError, Refused):
        return None


def read_native_init_slice(root, event):
    """Recover the named-slice count from the export, native frames and checker output at its pin."""
    directory = Path("reports/self-proof-native-init-slice")
    path = directory / "qualification.json"
    try:
        revision = _commit(event["source_revision"])
        _require(event["source"] == path.as_posix(), "wrong Init slice receipt")
        raw = _historical_blob(root, revision, path)
        _require(sha(raw) == _pin(event["source_sha256"]), "wrong Init slice digest")
        receipt = _json(raw)
        _require(receipt["schema"] == "clean.native-init-slice/1" and receipt["loader_proved"] is False
                 and nat(receipt["production_decisions_credited"]) == 0, "wrong measurement scope")
        export = gzip.decompress(_historical_blob(root, revision, directory / "roots.ndjson.gz"))
        wire = _historical_blob(root, revision, directory / "advice.bin")
        transcript = _historical_blob(root, revision, directory / "checker.txt")
        _require([sha(export), sha(wire), sha(transcript)] == [
            receipt["export_sha256"], receipt["advice_sha256"], receipt["transcript_sha256"]],
            "Init slice inputs differ from the receipt")
        replay = derive_coverage(export, wire, transcript.decode())
        contract = _json(_historical_blob(root, revision, "data/c5_init_slice.json"))
        targets = {row["name"] for row in contract["accepted_both"]} - set(contract["base_families"])
        # This contract's names consist entirely of string components.
        expected = {"[" + " ".join(f"s{len(part.encode())}:{part}" for part in name.split(".")) + "]"
                    for name in targets}
        observed = {row["name"] for row in replay["accepted_declarations"]}
        _require(replay == receipt["replay"] and observed == expected
                 and replay["accepted"] == len(targets) == 39 and replay["recognised_families"] == 3,
                 "native admissions and the named C5 slice disagree")
        return {"accepted": replay["accepted"], "target_declarations": len(targets),
                "recognised_families": replay["recognised_families"], "records": replay["declaration_records"],
                "source_revision": revision, "qualification_sha256": event["source_sha256"],
                "export_sha256": receipt["export_sha256"]}
    except (OSError, ValueError, TypeError, KeyError, EOFError, zlib.error, subprocess.CalledProcessError, Refused):
        return None


def _first_refused_declaration(error):
    # Source-import diagnostics can prefix the same named error with nested module labels.
    line = error.splitlines()[0] if error else ""
    named = re.match(r"^(?:\[[^\]\n]+\] )*([^\s:\[\]]+): elaboration error at line \d+:", line)
    if named:
        return named[1]
    imported = re.match(r"^Error: refusing to compile [^:]+: declaration `([^`]+)` failed to elaborate:", line)
    return imported[1] if imported else None


def census_progress(root, report, entry_only=False, proof_source_only=False):
    """Count observed E4 rows against the ordered source inventory at the run's revision."""
    if __package__:
        from . import self_proof_elab_probe as e4
        from .self_proof_entry_imports import ENTRY, SOUNDNESS, entry_imports
    else:
        import self_proof_elab_probe as e4
        from self_proof_entry_imports import ENTRY, SOUNDNESS, entry_imports

    try:
        revision = _commit(report["commit"])
        _require(report["schema"] == "self-proof-elab-v2" and type(report["complete"]) is bool
                 and report["source_snapshot_commit"] == revision and revision in report["version"],
                 "checkpoint source or schema differs")
        _require(_pin(report["runner_sha256"]) == sha(_historical_blob(root, revision, "scripts/self_proof_elab_probe.py")),
                 "runner differs from its source revision")
        e4.validate_binary_profile(report["build_profile"], report["binary_profile"])
        binary = _pin(report["binary_sha256"])
        inventory = []
        for package in e4.PACKAGES:
            order = _historical_blob(root, revision, f"theories/{package}/ORDER")
            for line in order.decode().splitlines():
                module = line.partition("#")[0].strip()
                if module:
                    inventory.append([package, module])
        modules = report["modules"]
        names = [[row["package"], row["module"]] for row in modules]
        _require(report["expected_modules"] == inventory and names == inventory[:len(names)],
                 "module rows differ from the pinned ORDER prefix")
        _require(not report["complete"] or len(names) == len(inventory), "complete checkpoint has missing modules")
        _require(not (entry_only and proof_source_only), "choose one source to trace")
        graph = None
        if entry_only or proof_source_only:
            graph = entry_imports(root, revision, SOUNDNESS if proof_source_only else ENTRY)
        subjects = {(p, m): None for p, m in inventory}
        if graph:
            subjects = {(node["package"], path[:-5]): node["sha256"]
                        for path, node in graph["modules"].items() if node["in_census"]}
            _require(subjects.keys() <= {tuple(row) for row in inventory}, "entry import missing from ORDER")
        counts = {"elaborated": 0, "refused": 0, "timed_out": 0}
        by_package = {p: {"expected": 0, "recorded": 0, **counts} for p in e4.PACKAGES}
        for package, _ in subjects:
            by_package[package]["expected"] += 1
        first_refusals = {}
        unnamed_refusals = 0
        proof_source = {"status": "pending"}
        for row in modules:
            _require(row["command"][1:] == ["check", row["module"] + ".lean", "--json"],
                     "module command differs from its row")
            status, error = e4.classify(row)
            _require((status, error) == (row["status"], row["first_error"]), "module verdict differs from its transcript")
            key = (row["package"], row["module"])
            if key not in subjects:
                continue
            if graph:
                _require(row["source_sha256"] == subjects[key], "entry module source differs from its Git input")
                if proof_source_only and row["module"] + ".lean" == graph["entry"]:
                    proof_source = {"status": status, "first_error": error}
            counts[status] += 1
            package = row["package"]
            by_package[package]["recorded"] += 1
            by_package[package][status] += 1
            if status == "refused":
                decl = _first_refused_declaration(error)
                if decl:
                    group = first_refusals.setdefault(decl, {"declaration": decl, "rows": 0,
                                                             "first_module": f"{package}/{row['module']}"})
                    group["rows"] += 1
                else:
                    unnamed_refusals += 1
        probes = report["probes"]
        _require([row["name"] for row in probes] == e4.EXPECTED_PROBES == report["expected_probes"],
                 "checkpoint has incomplete or reordered probes")
        adopted = next(row for row in probes if row["name"] == "KCheckLabelledMain")
        _require(adopted["command"][1:] == ["run", "KCheckLabelledMain.lean", "--decl", "main"],
                 "wrong adopted checker command")
        expected = _historical_blob(root, revision, "theories/kcheck_labelled/expected_output.txt")
        output = adopted["stdout"].encode()
        if adopted["exit"] == 0 and not adopted["timed_out"]:
            _require(output == expected, "adopted checker printed different verdict bytes")
            status, error = "executed", ""
        else:
            status, error = e4.classify(adopted)
        _require((adopted["status"], adopted["first_error"]) == (status, error),
                 "adopted checker verdict differs from its transcript")
    except (Refused, TypeError, KeyError, StopIteration) as error:
        raise ValueError(f"invalid E4 checkpoint: {error}") from error
    return {"source_revision": revision, "binary_sha256": binary, "complete": report["complete"],
            "modules_recorded": sum(counts.values()), "modules_expected": len(subjects), "module_counts": counts,
            **({"census_modules_expected": len(inventory)} if graph else {}),
            **({"entry_imports": graph} if entry_only else {}),
            **({"proof_source_imports": graph, "proof_source": proof_source} if proof_source_only else {}),
            "packages": by_package,
            "first_refusals": sorted(first_refusals.values(), key=lambda g: (-g["rows"], g["declaration"])),
            "unnamed_refusals": unnamed_refusals,
            "adopted_main": {"status": status, "first_error": error, "stdout_bytes": len(output),
                             "expected_bytes": len(expected), "matches_expected": output == expected}}


def _prefix_reading(row, archive, refusal, groups):
    _require(row["schema"] == "clean.self-proof-prefix.v1" and row["limit"] is None and row["census_unreadable"] is None
             and row["stop"] == "checker_refused", "measurement has a different advice, bound or stopping condition")
    receipts = row["accepted"]
    _require(isinstance(receipts, list) and len(receipts) == len(groups), "incorrect receipt sequence")
    _counts(row, {"accepted_records": len(receipts), "accepted_named_declarations": sum(map(len, groups))})
    for i, (entry, names) in enumerate(zip(receipts, groups), 1):
        _require(nat(entry["ordinal"]) == i and entry["kind"] == "inductive" and entry["receipt"] == entry["name"] == names[0]
                 and entry["names"] == names and entry["name_components"] == [name.split(".") for name in names]
                 and entry["receipt_components"] == names[0].split(".") and entry["recognised_rows"] is True,
                 "recorded checker receipt or grouped names disagree")
    terminal = row["terminal"]
    _require(terminal["name"] == refusal and terminal["kind"] == "inductive"
             and terminal["reason"] == "KCheck.Refusal.inductiveBlock `" + refusal
             and terminal["known_family"] is False and terminal["unit_template"] is False
             and nat(terminal["line"]) == nat(row["prefix_lines"]) and nat(terminal["ordinal"]) == len(receipts) + 1,
             "recorded first refusal disagrees with its prefix")

    # Bind the displayed result to the actual local input and the ends of its
    # reached prefixes. The registered package exit already replayed the checker.
    digest = hashlib.sha256()
    size = lines = 0
    with gzip.open(archive, "rb") as stream:
        for boundary in [*receipts, {**terminal, "prefix_bytes": row["prefix_bytes"], "prefix_sha256": row["prefix_sha256"]}]:
            delta = nat(boundary["prefix_bytes"]) - size
            _require(0 < delta <= nat(row["input_bytes"]), "prefix boundary is out of order")
            chunk = stream.read(delta)
            digest.update(chunk)
            size += len(chunk)
            lines += chunk.count(b"\n")
            _require(len(chunk) == delta and chunk.endswith(b"\n") and lines == nat(boundary["line"])
                     and digest.hexdigest() == boundary["prefix_sha256"], "prefix bytes disagree")
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
            size += len(block)
            lines += block.count(b"\n")
    _counts(row, {"input_lines": lines, "input_bytes": size})
    _require(digest.hexdigest() == row["input_sha256"], "local export differs from the observed subject")
    return {**{key: row[key] for key in ("input_sha256", "accepted_records", "declaration_records",
                                        "accepted_named_declarations", "named_declarations")},
            "first_refusal": terminal["name"], "line": terminal["line"]}


def _followup_prefix(root, directory, manifest, adoption):
    files = _object(manifest["evidence"])
    _require(manifest["schema"] == "clean.self-proof-prefix-exit.v1"
             and files.keys() == {"clean-current.json", "upstream-historical.json", "controls.json"}, "incomplete receipt roster")
    docs = {name: _json(_pinned_file(directory / name, pin)) for name, pin in files.items()}
    clean, historical, controls = docs["clean-current.json"], docs["upstream-historical.json"], docs["controls.json"]
    checker = clean["identity"]
    _require(checker == historical["identity"] == controls["identity"] and checker["entry"] == "KCheck.kcheckBytes"
             and checker["initial_environment"] == "KCheck.base" and checker["advice"] == "ByteArray.empty"
             and checker["lean_githash"] == adoption["identities"]["sdk_hash"]
             and checker["lean_sha256"] == adoption["identities"]["lean_sha256"], "checker identities disagree")
    run = adoption["replay"]
    _require(clean["input_sha256"] == run["input_sha256"]
             and adoption["retained_export"] == "../self-proof-const-branch-trial/candidate.ndjson.gz", "wrong current export")
    _counts(clean, {"declaration_records": nat(run["records"]), "named_declarations": nat(run["declarations"])})
    _counts(historical, {"declaration_records": 4402, "named_declarations": 4912})
    archive = (root / PR29_REPORT / adoption["retained_export"]).resolve()
    current = _prefix_reading(clean, archive, "Iff", [])
    prior = _prefix_reading(historical, root / "reports/self-proof-root-export-2026-11-17/kcheck_sound.ndjson.gz", "List",
                            [["Nat", "Nat.zero", "Nat.succ", "Nat.rec"]])
    _counts(manifest, {"current_records_admitted": current["accepted_records"], "historical_records_admitted": prior["accepted_records"],
                       "historical_names_covered": prior["accepted_named_declarations"], "control_cases": len(controls["observations"]),
                       "historical_probe_crosschecks": 2 + len(controls["historical_probe"])})
    return {"current": current, "historical": prior}


def _followup_paths(directory, receipt, adoption):
    witnesses = _json(_pinned_file(directory / "paths.json", receipt["wire_witnesses_sha256"]))
    _pinned_file(directory / "Resident.lean", receipt["probe_sha256"])
    targets = ["Iff", "List", "Quot"]
    run, identities = adoption["replay"], adoption["identities"]
    _require(witnesses["root"] == run["root"] == _ROOT and witnesses["input_sha256"] == run["input_sha256"] == receipt["input_sha256"]
             and witnesses["statement_sha256"] == receipt["statement_sha256"] == run["subjects"][_ROOT]["statement_sha256"]
             and receipt["archived_clean_revision"] == identities["source_revision"]
             and receipt["resident_module_sha256"] == identities["modules"]["CompleteSound"]
             and receipt["lean_revision"] == identities["sdk_hash"] and receipt["lean_executable_sha256"] == identities["lean_sha256"]
             and receipt["root_proof_body_used"] is False and receipt["targets"] == targets
             and set(witnesses["paths"]) == set(targets), "statement scope, targets or resident identity disagree")
    edges = set()
    for target, path in witnesses["paths"].items():
        _require(isinstance(path, list) and path and path[0]["field"] == "type", "path does not start at the statement")
        source = _ROOT
        for i, edge in enumerate(path):
            field = edge["field"]
            _require(edge["source"] == source and (i == 0 or source != _ROOT) and field in {"type", "value"},
                     "dependency path is disconnected or reenters the root")
            source = edge["target"]
            edges.add((field, edge["source"], source))
        _require(source == target, "dependency path misses its target")
    _require(len(edges) == nat(receipt["edges_checked"]) == 13 and nat(receipt["wrong_edge_exit"]) == 1
             and receipt["wrong_edge"] == f"type|{_ROOT}|Quot" and ("type", _ROOT, "Quot") not in edges,
             "distinct edge count or rejected control disagrees")
    return {"targets": targets, "root_proof_body_used": False, "edges_checked": len(edges),
            "statement_sha256": witnesses["statement_sha256"]}


def read_followup(root: Path, event: dict) -> dict | None:
    """Read the enrolled historical exit and its local subordinate evidence, or suppress the observation."""
    try:
        unit = event["unit"]
        name, manifest, revision, qualified = _FOLLOWUP_REPORTS[unit]
        report = Path("reports") / name
        source = report / "README.md"
        _require(_commit(event["source_revision"]) == revision and _pin(event["qualification_sha256"]) == qualified
                 and event["source"] == source.as_posix(), "wrong historical source or manifest")
        for path, pin in ((source, event["source_sha256"]), (report / manifest, qualified)):
            data = _pinned_file(root / path, pin)
            _require(data == _historical_blob(root, revision, path), "local artifact differs from its original revision")
        receipt = _json(data)
        adoption = _json(_historical_blob(root, revision, PR29_REPORT / "replay.json"))
        _require(_pin(event["input_sha256"]) == adoption["replay"]["input_sha256"], "wrong qualified input")
        result = (_followup_prefix(root, root / report, receipt, adoption) if unit == "PR-30"
                  else _followup_paths(root / report, receipt, adoption))
        return {**result, "input_sha256": event["input_sha256"], "qualification_sha256": qualified, "source_revision": revision}
    except (OSError, EOFError, zlib.error, ValueError, TypeError, KeyError, IndexError, AttributeError,
            RecursionError, subprocess.CalledProcessError, Refused):
        return None

def read_console_replay(root, event):
    """Read the dated executable observation at its original module and report revision."""
    report = Path("reports/self-proof-w6-console-2026-11-17")
    try:
        revision = _commit(event["source_revision"])
        readme = report / "README.md"
        receipt = report / "run-link.json"
        _require(event["source"].split("#", 1)[0] == readme.as_posix()
                 and sha(_historical_blob(root, revision, readme)) == event["source_sha256"], "wrong W6 report")
        raw = _pinned_file(root / receipt, event["receipt_sha256"])
        _require(raw == _historical_blob(root, revision, receipt), "W6 receipt differs at its reported revision")
        result = _json(raw)
        _require(result["sha256"]["clean"] == _pin(event["clean_binary_sha256"])
                 and result["clean_version"].endswith("+g" + _commit(event["clean_binary_revision"]))
                 and re.fullmatch(r"sha256:[0-9a-f]{64}", event["module_digest"]),
                 "W6 compiler or module identity mismatch")
        printed, pair = result["subjects"]["Print"], result["subjects"]["Pair"]
        current, previous = printed["receipt"], printed["earlier_clean"]["receipt"]
        _require(current["module_digest"] == previous["module_digest"] == event["module_digest"]
                 and previous["step"] == "link-demand" and printed["earlier_clean"]["cli"]["exit"] == 1,
                 "unmatched earlier W6 refusal")
        expected = {"exit": 0, "stdout": "clean-println\n", "stderr": ""}
        _require(printed["lean"] == printed["program"] == expected and current["stage"] == "built"
                 and current["lowered"] == "clean-compiler-unvalidated" and current["runtime"] == "C via cc"
                 and nat(current["kernel_tv_certified"]) == 0, "wrong W6 executable result or authority scope")
        _require(pair["trustcg_cli"]["exit"] == pair["c_cli"]["exit"] == 1
                 and "native-eager-io" in pair["receipt"]["cause"], "missing W6 sequencing refusal")
        return {"source_revision": revision, "receipt_sha256": event["receipt_sha256"],
                "module_digest": current["module_digest"], "stdout_bytes": len(printed["program"]["stdout"].encode()),
                "runtime": current["runtime"], "lowered": current["lowered"], "pair_refusal": "native-eager-io"}
    except (OSError, ValueError, TypeError, KeyError, subprocess.CalledProcessError, Refused):
        return None
