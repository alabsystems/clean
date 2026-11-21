#!/usr/bin/env python3
# Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0
"""Render an offline, printable presentation from the fleet's evidence snapshot."""

from datetime import date
from html import escape
from pathlib import PurePosixPath
import re
from urllib.parse import quote

if __package__:
    from .self_proof_fleet_evidence import PR29_COMMAND, execution_matches, native_matcher_text, source_qualification_command
else:
    from self_proof_fleet_evidence import PR29_COMMAND, execution_matches, native_matcher_text, source_qualification_command


PLAN = "docs/plans/SELF_PROOF_EXECUTION_PLAN_2026-11-12.md"
CATALOG = "data/self_proof_fleet_obligations.json"
TIMELINE = "data/self_proof_fleet_timeline.json"
ROOT_REPORT = "reports/self-proof-root-export-2026-11-17/source-fidelity/README.md"
BOARD = "data/self_proof_scoreboard.json"
QUORUM = "reports/self-proof-q4-ck0-2026-11-16/README.md"
LATER_QUORUM = "reports/self-proof-q4-corrected-reference-2026-11-18/README.md"


def _map(item):
    return item if isinstance(item, dict) else {}


def _list(item):
    return item if isinstance(item, list) else []


def _safe(value):
    return escape(str(value), quote=True)


def _revision(value):
    return isinstance(value, str) and re.fullmatch(r"[0-9a-f]{40}", value)


def _source(label, path, revision):
    text = _safe(label)
    if not _revision(revision) or not isinstance(path, str):
        return text
    file, _, anchor = path.partition("#")
    if (not file or file.startswith("/") or "\\" in file
            or any(part in (".", "..", "") for part in file.split("/"))
            or ":" in file or PurePosixPath(file).is_absolute()):
        return text
    url = "https://github.com/alabsystems/clean/blob/" + revision + "/" + quote(file, safe="/")
    if anchor:
        url += "#" + quote(anchor, safe="-")
    return '<a href="' + _safe(url) + '">' + text + '</a>'


def _event_source(label, event, revision):
    if not event:
        return ""
    return _source(label, event.get("source"), event.get("source_revision", revision))


def _observation(value):
    row = _map(value)
    return {} if "absent" in row else row


def _number(value):
    return f"{value:,}" if type(value) is int and value >= 0 else "Unverified"


def _ratio(done, total):
    if any(type(n) is not int or n < 0 for n in (done, total)) or done > total:
        return "Unverified"
    return f"{done:,} / {total:,}"


def _metric(label, value, description):
    return (f'<div class="metric"><dt>{_safe(label)}</dt><dd>{_safe(value)}</dd>'
            f'<dd class="annotation">{_safe(description)}</dd></div>')


def _slide(anchor, title, content, sources):
    links = " · ".join(dict.fromkeys(link for link in sources if link))
    foot = f'<footer>{links}</footer>' if links else ""
    return (f'<section class="slide" id="{anchor}" aria-labelledby="{anchor}-title" tabindex="-1">'
            f'<h2 id="{anchor}-title">{_safe(title)}</h2>{content}{foot}</section>')


def _milestones(events, revision, trial=None, adoption=None, quorum=None):
    # Historical results use the event's own subject and date. In particular
    # the restricted Init ck0 measurements and the proof-export counts differ.
    selected = [
        ("2026-10-15", "authority", "decision"),
        ("2026-11-12", "authority", "decision"),
        ("2026-11-14", "C3", "proof"),
        ("2026-11-15", "C4-C5", "measurement"),
        ("2026-11-15", "C3", "measurement"),
        ("2026-11-16", "Q4", "measurement"),
    ]
    by_key = {(r.get("date"), r.get("unit"), r.get("kind")): r
              for r in events if isinstance(r, dict)
              and all(isinstance(r.get(key), str) for key in ("date", "unit", "kind"))}
    rows = [by_key[k] for k in selected if k in by_key]
    later = [r for r in events if isinstance(r, dict) and r.get("unit") == "self-admission-prefix"]
    if later and not trial:
        rows.append(later[-1])
    source_export = by_key.get(("2026-11-17", "CL-03", "wiring"))
    if source_export:
        rows.append(source_export)
    if trial:
        rows.append(trial)
    if adoption:
        rows.append(adoption)
    if quorum:
        vote = next((row for row in reversed(events) if isinstance(row, dict)
                     and row.get("unit") == "Q4" and row.get("kind") == "measurement"
                     and all(row.get(key) == quorum.get(key) and quorum.get(key)
                             for key in ("date", "source", "source_revision", "source_sha256"))), None)
        if vote:
            rows.append(vote)
    if len(rows) > 6:
        # On a full week keep the strongest selected receipt on each date.
        # Multiple experiments on one day should not displace the route's adoption.
        by_day = {row["date"]: row for row in rows}
        rows = [by_day[day] for day in sorted(by_day)[-6:]]
    if not rows:
        return '<p class="lead">No sourced milestones were supplied.</p>'
    items = []
    for row in rows:
        date = row.get("date", "")
        items.append('<li><time>' + _event_source(date, row, revision) + '</time>'
                     '<p>' + _safe(row.get("summary", "Unverified")) + '</p></li>')
    return '<ol class="timeline">' + "".join(items) + '</ol>'


def _matched_event(events, digest, kind, stock_result=None, *, unit="Q4", field="input_sha256"):
    if not isinstance(digest, str) or not re.fullmatch(r"[0-9a-f]{64}", digest):
        return {}
    for row in reversed(events):
        if (not isinstance(row, dict) or row.get("unit") != unit or row.get("kind") != kind
                or row.get(field) != digest):
            continue
        if stock_result is not None and row.get("stock_result_sha256") != stock_result:
            continue
        when = row.get("date")
        try:
            dated = isinstance(when, str) and date.fromisoformat(when).isoformat() == when
        except ValueError:
            dated = False
        if dated and all(isinstance(row.get(k), str) and row[k].strip() for k in ("summary", "source")):
            return row
    return {}


def _console_event(events, observed):
    row = _map(observed)
    event = _matched_event(events, row.get("receipt_sha256"), "measurement", unit="W6", field="receipt_sha256")
    module = row.get("module_digest")
    if (not event or event.get("obligation") != "X3-X5"
            or event.get("source") != "reports/self-proof-w6-console-2026-11-17/README.md"
            or not _revision(row.get("source_revision")) or event.get("source_revision") != row["source_revision"]
            or not isinstance(module, str) or not re.fullmatch(r"sha256:[0-9a-f]{64}", module)
            or event.get("module_digest") != module or type(row.get("stdout_bytes")) is not int or row["stdout_bytes"] <= 0
            or row.get("runtime") != "C via cc" or row.get("lowered") != "clean-compiler-unvalidated"
            or row.get("pair_refusal") != "native-eager-io"):
        return {}
    return event


def _quorum_result(events, digest):
    measured = _matched_event(events, digest, "measurement")
    if measured:
        return measured, "Stock verdict on this export"
    earlier = next((row for row in events if isinstance(row, dict) and "input_sha256" not in row
                    and (row.get("date"), row.get("unit"), row.get("kind"))
                    == ("2026-11-17", "Q4", "blocker")), {})
    return earlier, "Earlier quorum check"


def _brief_text(row):
    brief = row.get("brief")
    return _safe(brief if isinstance(brief, str) and brief.strip() else row.get("summary", ""))


def _publication_line(item, planning, table):
    ref = re.fullmatch(rf"([0-9a-f]{{40}}):goals/data/{table}\.tsv:([1-9][0-9]*)",
                       str(item.get("publication_ref", "")))
    if ref and ref[1] == planning.get("publication_commit") and planning.get("backend") == "publication":
        return ref[2]
    return None


def _publication_label(label, item, planning, table):
    line = _publication_line(item, planning, table)
    if line:
        url = f'https://github.com/alabsystems/publication/blob/{planning["publication_commit"]}/goals/data/{table}.tsv#L{line}'
        return f'<a href="{url}">{_safe(label)}</a>'
    return _safe(label)


def _original_source_history(planning, name, label, unit_pattern, outcome):
    metric_id = "E1." + name
    definitions = [row for row in _list(planning.get("metrics")) if isinstance(row, dict) and row.get("id") == metric_id]
    if len(definitions) != 1:
        return ""
    definition = definitions[0]
    unit = definition.get("unit")
    bound = re.fullmatch(unit_pattern, unit) if isinstance(unit, str) else None
    if (not bound or definition.get("units") != [unit] or definition.get("goal") != "E1"
            or definition.get("pk") != metric_id or definition.get("name") != name):
        return ""
    readings = []
    seen_lines = set()
    for row in _list(planning.get("measurements")):
        if not isinstance(row, dict) or (row.get("metric") != name and row.get("metric_id") != metric_id):
            continue
        line = _publication_line(row, planning, "metrics")
        value, day = row.get("value"), row.get("date")
        if (not line or line in seen_lines or row.get("pk") != row.get("publication_ref")
                or row.get("goal") != "E1" or row.get("metric") != name or row.get("metric_id") != metric_id
                or row.get("unit") != unit or not isinstance(value, str) or not re.fullmatch(r"0|[1-9][0-9]*", value)
                or not isinstance(day, str) or row.get("at") != day):
            return ""
        try:
            if int(value) > int(bound[1]) or date.fromisoformat(day).isoformat() != day:
                return ""
            readings.append((day, int(line), _publication_label(value, row, planning, "metrics")))
        except ValueError:
            return ""
        seen_lines.add(line)
    if not readings:
        return ""
    values = " → ".join(link for _, _, link in sorted(readings))
    return f'<li><strong>{label}</strong> · {values} {_safe(unit)} {outcome}</li>'


def _original_source_histories(planning):
    data = _map(planning)
    if (data.get("state") != "available" or data.get("goal") != "E1"
            or data.get("publication_source") != "refs/remotes/origin/main"
            or _map(data.get("capabilities")).get("agoals") != {
                "schema": 1, "product": "aGoals", "backend": "publication", "family_registered": False}):
        return ""
    histories = [
        _original_source_history(data, "w1_original_token_declarations_elaborated", "Original Token",
                                 r"of ([1-9][0-9]*) original declarations", "elaborated"),
        _original_source_history(data, "w1_psigma_syntax_named_declarations", "Original PSigma",
                                 r"of ([1-9][0-9]*) original named declarations", "elaborated"),
        _original_source_history(data, "w3_advice_start_canonical_digest_matches", "Advice.start identity",
                                 r"of (1) original checker definition", "matched its upstream digest"),
        _original_source_history(data, "w3_advice_exhausted_resident_body_checked", "Advice.exhausted",
                                 r"of (1) original cursor predicate body", "checked by pinned Lean"),
    ]
    if not any(histories):
        return ""
    return '<ul class="compact" aria-label="Original source measurements">' + "".join(histories) + '</ul>'


def _package_label(item, planning):
    label = " · ".join(str(item[field]) for field in ("id", "title") if item.get(field))
    return _publication_label(label, item, planning, "packages")


def _planning(planning, current):
    if not planning:
        return ('<p class="lead">The planning backend has no observation in this snapshot.</p>'
                '<p>Use the fleet guide to check the work queue. Record an E1 planning result '
                'before treating a task as synchronized.</p>'
                '<p><code>python3 scripts/self_proof_fleet.py --ready</code></p>')
    data = _map(planning)
    status = data.get("state")
    content = '<dl class="facts">'
    for title, key in (("Tracker", "backend"), ("State", "state"), ("Goal", "goal")):
        value = data.get(key)
        if isinstance(value, (str, int)) and not isinstance(value, bool) and str(value):
            content += f'<dt>{_safe(title)}</dt><dd>{_safe(value)}</dd>'
    if not isinstance(status, str) or not status:
        content += '<dt>Verified state</dt><dd>Unavailable</dd>'
    content += '</dl>'
    caps = _map(data.get("capabilities"))
    if status == "available" and data.get("backend") == "publication" and caps.get("native_table") is False:
        agoals = _map(caps.get("agoals"))
        if (agoals.get("product") == "aGoals" and agoals.get("backend") == "publication"
                and agoals.get("family_registered") is False):
            content += '<p>aGoals reads E1 from publication. Its native database tables await registration.</p>'
        else:
            content += '<p>This machine reads E1 through the publication tracker. The native aterm Product Planning table is unavailable.</p>'
    elif caps:
        features = []
        for key, label in (("native_table", "Read planning tables"), ("native_measure", "Write a native measurement")):
            if type(caps.get(key)) is bool:
                features.append(label + (" available" if caps[key] else " unavailable in the probe"))
        if type(caps.get("native_metric_ids")) is list:
            features.append(f"{len(caps['native_metric_ids'])} native metric IDs observed")
        if features:
            content += '<p>' + _safe(". ".join(features)) + '.</p>'
    if status == "available" and isinstance(data.get("packages"), list):
        packages = [item for item in data["packages"] if isinstance(item, dict)]
        held = [item for item in packages if item.get("state") == "running"
                and (item.get("claimed_by") or item.get("claim"))]
        counts = [f'{len(packages)} package' + ('' if len(packages) == 1 else 's'),
                  f'{len(held)} active claim' + ('' if len(held) == 1 else 's')]
        eligible = []
        if packages and all(type(item.get("dispatchable")) is bool for item in packages):
            eligible = [item for item in packages if item["dispatchable"]]
            counts.append(f'{len(eligible)} ready to dispatch')
        content += '<p>E1 has ' + ', '.join(counts) + '.</p>'
        done = [item for item in packages if item.get("state") == "done" and item.get("evidence")
                and isinstance(item.get("done_on"), str) and item.get("done_on")]
        if eligible:
            labels = ", ".join(_package_label(item, data) for item in eligible[:3])
            content += f'<p>Ready to dispatch · {labels}</p>'
            if len(eligible) > 3:
                content += f'<p class="annotation">Showing three of {len(eligible)} eligible packages.</p>'
        named_claims = [item for item in held if item.get("id")]
        if named_claims:
            labels = ", ".join(f'{_package_label(item, data)} ({_safe(item.get("claimed_by") or item["claim"])})'
                               for item in named_claims[:3])
            content += f'<p>In progress · {labels}</p>'
            if len(named_claims) > 3:
                content += f'<p class="annotation">Showing three of {len(named_claims)} named claims.</p>'
        if done:
            day = max(item["done_on"] for item in done)
            completions = [item for item in done if item["done_on"] == day]
            example = _package_label(completions[-1], data)
            if len(completions) == 1:
                content += f'<p>Completed on {_safe(day)} · {example}</p>'
            else:
                content += f'<p>{len(completions)} packages completed on {_safe(day)}, including {example}.</p>'
    source = source_qualification_command(current) if current else None
    measures = [item for item in _list(data.get("measurements")) if isinstance(item, dict)
                and (not str(item.get("source", "")).startswith(PR29_COMMAND)
                     or item.get("source") == source)]
    if measures:
        content += '<h3>Planning measurements</h3><ul class="compact">'
        for item in measures[-5:]:
            metric = item.get("metric", item.get("name", "Unnamed measurement"))
            value = item.get("value")
            if value is None or isinstance(value, (list, dict, bool)):
                value = "unverified"
            labels = {"w1_adopted_main_stdout_bytes": "Checker output from Clean source (5,110 bytes expected)",
                      "w1_adopted_main_diagnostic_stdout_bytes": "Full checker output in the 600-second diagnostic",
                      "w2_level_island_open_gaps": "Open gaps on the Trust universe-level build",
                      "prelude_native_advice_admitted": "Prelude admissions with native advice (22 in fragment)",
                      "level_only_with_specified_advice": "Universe-level divergences accepted with specified advice (zero with native advice)",
                      "named_init_slice_native_admitted": "Native admissions on the 39 named Prelude and Core declarations",
                      "w1_rawsets_original_declarations_elaborated": "Original RawSets declarations admitted by the source compiler",
                      "w1_quotient_syntax_type_prefix_elaborated": "Original declarations through QuotientSyntax.type_closed",
                      "w1_original_token_declarations_elaborated": "Original Token declarations accepted by Clean",
                      "w1_quotient_respect_prefix_elaborated": "Original declarations through QuotientSyntax.mapLevels_respectExpr",
                      "w1_psigma_syntax_named_declarations": "Original PSigma syntax declarations accepted by Clean",
                      "w1_psigma_original_module_checks_passed": "Unchanged PSigma source files checked including section commands",
                      "w3_advice_start_canonical_digest_matches": "Advice.start canonical digest matching the upstream resident",
                      "w3_advice_exhausted_resident_body_checked": "Advice.exhausted bodies checked by the pinned Lean kernel",
                      "w3_advice_exhausted_canonical_digest_matches": "Advice.exhausted canonical digest matching the upstream resident",
                      "w3_advice_read_exact_end_contracts_checked": "Exact-end theorem for every successful advice read",
                      "w2_cursor_boundary_trustcg_outputs_matching": "TrustCG-linked cursor examples matching the expected output",
                      "w3_advice_start_kernel_defeq_fields": "Advice.start fields definitionally equal to the upstream resident",
                      "w1_grouped_rewrite_expected_outcomes": "Grouped rewrite cases matching the required source outcome",
                      "w1_quotient_packet_prefix_elaborated": "Original declarations through QuotientSyntax.Packet",
                      "w1_census_subjects_recorded": "Checker-source modules measured (440 in the frozen census)",
                      "w1_entry_local_imports": "Local library modules imported by the original checker entry",
                      "soundness_source_local_imports": "Local library modules imported by the soundness theorem source",
                      "w1_entry_source_modules_elaborated": "Original executable imports elaborated by the measured Clean compiler",
                      "soundness_source_modules_elaborated": "Original soundness-source modules elaborated by frozen Clean",
                      "w4_soundness_prefix87_native_accepted": "Ordinary admissions within the first 87 soundness-export records",
                      "w4_soundness_prefix24_native_accepted": "Ordinary admissions within the first 24 soundness-export records",
                      "qualified_soundness_root_recheckers": "Independent recheckers accepting the soundness proof",
                      "w6_byte_equality_uncovered_instructions": "Machine instructions awaiting proof in the byte-equality object",
                      "soundness_root_resident_equal": "Declarations matching resident Lean",
                      "adopted_kcheck_first_prefix_accepted": "Consecutive first-prefix admissions",
                      "compiled_kcheck_decisions": "Compiled-checker production decisions",
                      "stock_ck0_soundness_root_admitted": "Soundness-root declarations admitted by stock ck0",
                      "stock_ck0_const_helper_candidate_admitted": "Stock ck0 admissions on the const-helper candidate"}
            label = f"{labels.get(metric.removeprefix('E1.'), metric) if isinstance(metric, str) else 'Unknown metric'} — {value}"
            if source and item.get("source") == source:
                label = "PR-29 qualified source · " + label
            for key in ("unit", "state"):
                if isinstance(item.get(key), str) and item[key]:
                    label += " · " + item[key]
            content += '<li>' + _publication_label(label, item, data, "metrics") + '</li>'
        content += '</ul>'
        if len(measures) > 5:
            content += f'<p class="annotation">Showing the last five of {len(measures)} supplied rows.</p>'
    deferred = [item for item in _list(data.get("deferred")) if isinstance(item, str) and item]
    if isinstance(data.get("reason"), str) and data["reason"]:
        deferred.insert(0, data["reason"])
    if deferred:
        content += '<h3>Deferred work</h3><ul class="compact">'
        content += "".join('<li>' + _safe(entry) + '</li>' for entry in deferred[:3]) + '</ul>'
        if len(deferred) > 3:
            content += f'<p class="annotation">{len(deferred) - 3} additional items in the planning report.</p>'
    return content


def _qualified_quorum_table(original, current, trial):
    def prefix_result(subject):
        value = _ratio(subject.get("prefix_accepted"), subject.get("records"))
        first = _map(subject.get("first_refusal"))
        if isinstance(first.get("name"), str) and type(first.get("line")) is int:
            value += f' · {first["name"]}, line {first["line"]}'
        return value

    names = original.get("declarations")
    original_stock = "Unverified"
    if (trial.get("baseline_input_sha256") == original.get("sha256") and type(names) is int
            and type(trial.get("baseline_named")) is int and trial["baseline_named"] == names
            and type(trial.get("baseline_stock_admitted")) is int and 0 <= trial["baseline_stock_admitted"] < names):
        original_stock = _ratio(trial["baseline_stock_admitted"], names) + " · root refused"
    rows = [("Export size", f'{_number(names)} names · {_number(original.get("records"))} records',
             f'{_number(current["declarations"])} names · {_number(current["records"])} records')]
    for label, key in (("Resident Lean terms matched", "resident_equal"), ("Pinned Lean admitted", "upstream_admitted"),
                       ("Fenced Clean admitted", "fenced_admitted")):
        rows.append((label, _ratio(original.get(key), names), _ratio(current[key], current["declarations"])))
    rows.extend((("Stock ck0 admitted", original_stock,
                  _ratio(current["stock_admitted"], current["declarations"]) + " · root admitted"),
                 ("Adopted checker prefix", prefix_result(original), prefix_result(current))))
    header = ('<table><thead><tr><th scope="col">Check</th><th scope="col">Original Clean export</th>'
              '<th scope="col">PR-29 qualified source</th></tr></thead><tbody>')
    return header + "".join(f'<tr><th scope="row">{label}</th><td>{_safe(before)}</td><td>{_safe(after)}</td></tr>'
                            for label, before, after in rows) + "</tbody></table>"


def _followup(followups, events, adopted, unit):
    receipt = _map(followups.get(unit))
    event = _matched_event(events, adopted.get("input_sha256"), "measurement", unit=unit)
    digest = receipt.get("qualification_sha256")
    if (receipt.get("state", "qualified") not in ("qualified", "measured") or not event
            or not isinstance(digest, str) or not re.fullmatch(r"[0-9a-f]{64}", digest)
            or digest != event.get("qualification_sha256") or receipt.get("input_sha256") != event["input_sha256"]
            or not _revision(receipt.get("source_revision")) or receipt["source_revision"] != event.get("source_revision")):
        return {}, {}
    return receipt, event


def _prefix_comparison(receipt, adopted):
    current, historical = _map(receipt.get("current")), _map(receipt.get("historical"))
    if (not current or not historical or current.get("input_sha256") != receipt.get("input_sha256")
            or historical.get("input_sha256") == current.get("input_sha256")
            or current.get("declaration_records") != adopted.get("records")
            or current.get("named_declarations") != adopted.get("declarations")
            or current.get("accepted_records") != adopted.get("prefix_accepted")
            or current.get("first_refusal") != adopted["first_refusal"]["name"]
            or current.get("line") != adopted["first_refusal"]["line"]):
        return ""
    rows = []
    for label, item in (("Current Clean", current), ("Historical upstream Lean", historical)):
        digest, refusal, line = item.get("input_sha256"), item.get("first_refusal"), item.get("line")
        counts = [item.get(field) for field in ("accepted_records", "declaration_records",
                                                 "accepted_named_declarations", "named_declarations")]
        if (not isinstance(digest, str) or not re.fullmatch(r"[0-9a-f]{64}", digest)
                or not isinstance(refusal, str) or not refusal.strip() or type(line) is not int or line < 2
                or not all(type(count) is int for count in counts)):
            return ""
        accepted, records, covered, names = counts
        if not (0 <= accepted < records <= names and accepted <= covered < names and (accepted == 0) == (covered == 0)):
            return ""
        rows.append(f'<tr><th scope="row">{label}<br><code title="{digest}">{digest[:12]}</code></th>'
                    f'<td>{_ratio(accepted, records)}</td><td>{_ratio(covered, names)}</td>'
                    f'<td>{_safe(refusal)}, line {line}</td></tr>')
    return ('<p>PR-30 replayed two exports of the same soundness theorem, in order, with empty advice. '
            'Each accepted declaration record earns one receipt and can cover several names.</p>'
            '<table><thead><tr><th>Export · SHA-256</th><th>Records admitted</th><th>Names covered</th>'
            '<th>First refusal</th></tr></thead><tbody>' + "".join(rows) + '</tbody></table>')


def _statement_finding(receipt):
    targets, checked, statement = receipt.get("targets"), receipt.get("edges_checked"), receipt.get("statement_sha256")
    if (not isinstance(targets, list) or not all(isinstance(name, str) for name in targets) or "Iff" not in targets
            or receipt.get("root_proof_body_used") is not False or type(checked) is not int or checked < len(targets)
            or not isinstance(statement, str) or not re.fullmatch(r"[0-9a-f]{64}", statement)):
        return ""
    return (f'<p class="callout"><strong>Changing only the final proof body leaves <code>Iff</code> in the input.</strong> '
            f'PR-31 traced the fixed statement <code title="{statement}">{statement[:12]}</code> through the set model’s '
            'membership definition to <code>Iff</code>. The path starts in the theorem’s type.</p>')


def render_slides(snapshot, events, planning=None, *, revision=""):
    """Return standalone HTML. Only full Clean Git revisions become evidence links."""
    report = _map(snapshot)
    events = _list(events.get("events")) if isinstance(events, dict) else _list(events)
    metrics = _map(report.get("metrics"))
    export = _map(report.get("literal_export"))
    measured = export.get("state") == "measured"
    evidence = export if measured else {}
    first = _map(evidence.get("first_refusal"))
    c3 = _map(report.get("c3"))
    qualified = c3.get("state") == "qualified_snapshot" and bool(_revision(c3.get("revision")))
    production = _observation(metrics.get("production"))
    fragment = _observation(metrics.get("fragment"))
    units = {r["id"]: r for r in _list(report.get("units"))
             if isinstance(r, dict) and isinstance(r.get("id"), str)}
    n = evidence.get("declarations")
    prefix = evidence.get("prefix_accepted")
    root = evidence.get("root")
    snap_warning = report.get("scoreboard_warning")

    def src(label, path, rev=revision):
        return _source(label, path, rev)

    adopted = _map(report.get("source_qualification"))
    adoption = _matched_event(events, adopted.get("input_sha256"), "measurement", unit="PR-29")
    own = _map(adopted.get("first_refusal"))
    named = adopted.get("declarations")
    records = adopted.get("records")
    if (type(named) is not int or named <= 0 or type(records) is not int or not 0 < records <= named
            or any(type(adopted.get(key)) is not int or adopted[key] != named
                   for key in ("stock_admitted", "resident_equal", "upstream_admitted", "fenced_admitted"))
            or type(adopted.get("prefix_accepted")) is not int or adopted["prefix_accepted"] != 0
            or adopted.get("fourth_member_qualified") is not False
            or not isinstance(own.get("name"), str) or not own["name"] or type(own.get("line")) is not int or own["line"] < 2
            or not isinstance(adopted.get("root"), str) or not adopted["root"]
            or adopted.get("state") != "qualified" or adoption.get("obligation") != "Q4"
            or not _revision(adopted.get("qualified_revision"))
            or not isinstance(adopted.get("qualification_sha256"), str)
            or not re.fullmatch(r"[0-9a-f]{64}", adopted["qualification_sha256"])
            or adoption.get("qualification_sha256") != adopted["qualification_sha256"]):
        adopted, adoption = {}, {}
    leading_first = _map(adopted.get("first_refusal", first))
    later_vote = _map(report.get("soundness_root_quorum"))
    quorum_note = ""
    quorum_source = src("Later Q4 rechecking", LATER_QUORUM)
    if (adoption and later_vote.get("input_sha256") == adopted.get("input_sha256")
            and later_vote.get("declarations") == named and _revision(later_vote.get("epoch"))
            and later_vote.get("members") == ["ck0-stock", "clean-reference", "lean", "lean4lean"]):
        quorum_note = (f'At frozen source <code>{_safe(later_vote["epoch"][:12])}</code>, all four independent recheckers '
                       f'accepted the unchanged {_number(named)}-name proof export, including qualified Lean4Lean.')
        if later_vote.get("source") and _revision(later_vote.get("source_revision")):
            quorum_source = _event_source("Q4 root replay", later_vote, revision)
    slides = []
    if (adopted or measured) and leading_first.get("name"):
        answer = f"No. The adopted checker refused {_safe(leading_first['name'])} before it reached its own soundness theorem."
    elif measured:
        answer = "A prefix was replayed. A complete run admitting the soundness theorem still needs its own evidence."
    else:
        answer = "The snapshot supplies no verified full-root replay evidence for the adopted checker."
    theorem = (f'Two kernels rechecked the per-bound semantic theorem at '
               f'<code>{_safe(c3["revision"][:10])}</code>. The fenced Rust kernel still holds authority.'
               if qualified else 'A two-kernel semantic proof receipt is unverified in this snapshot.')
    intro = f'<p class="lead">{answer}</p><p>{theorem}</p><dl class="metrics">'
    intro += _metric("Full proof export", _number(adopted.get("declarations", n)), "Named declarations in the retained stream.")
    intro += _metric("Adopted checker", _number(adopted.get("prefix_accepted", prefix)), "Consecutive records admitted in the measured prefix.")
    intro += _metric("Production", _number(production.get("real_declarations_decided")), "Real declarations decided by compiled kcheck at a site.")
    intro += '</dl>'
    if quorum_note:
        intro += '<p>' + quorum_note + '</p>'
    elif adoption:
        intro += (f'<p>On qualified Clean source <code>{_safe(adopted["qualified_revision"][:12])}</code>, '
                  f'pinned Lean, fenced Clean and stock ck0 each admitted {_safe(_ratio(adopted.get("stock_admitted"), adopted.get("declarations")))} '
                  f'names, including the root. That PR-29 receipt recorded no qualified Lean4Lean vote.</p>')
    if qualified and measured and first.get("name") and production.get("real_declarations_decided") == 0:
        intro += ('<p>Recent work established checker soundness for the supported fragment and made the full proof input reproducible. '
                  'The adopted checker still owes a receipt for its soundness theorem and its first production decision.</p>')
    if snap_warning:
        intro += '<p class="notice">Scoreboard record needs attention. ' + _safe(snap_warning) + '</p>'
    slides.append(_slide("answer", "Can Clean prove itself?", intro,
                         [src("Soundness proof receipt", c3.get("source"), c3.get("receipt_revision", revision)),
                          src("Full export and prefix", ROOT_REPORT), _event_source("PR-29 source qualification", adoption, revision),
                          quorum_source,
                          src("Scoreboard", BOARD)]))
    trial = _matched_event(events, evidence.get("sha256"), "measurement",
                                  unit="PR-28", field="baseline_input_sha256")
    recorded = _map(report.get("const_helper_trial"))
    if (recorded.get("state") != "recorded" or recorded.get("result_sha256") != trial.get("result_sha256")
            or recorded.get("input_sha256") != trial.get("input_sha256")):
        trial = {}
    slides.append(_slide("history", "What changed over time", _milestones(events, revision, trial, adoption, later_vote if quorum_note else None),
                         [src("Complete dated timeline", TIMELINE)]))

    quorum, quorum_label = _quorum_result(events, evidence.get("sha256"))
    diagnosis = {}
    stock_result = quorum.get("stock_result_sha256")
    if quorum.get("kind") == "measurement" and isinstance(stock_result, str) and re.fullmatch(r"[0-9a-f]{64}", stock_result):
        diagnosis = _matched_event(events, evidence.get("sha256"), "blocker", stock_result)
    if adoption:
        table = _qualified_quorum_table(evidence, adopted, recorded if trial else {})
        historical = "The PR-29 receipt recorded no qualified Lean4Lean vote; later Q4 rechecking is recorded separately."
        content = f'<p>Soundness root · <code>{_safe(adopted["root"])}</code>. {quorum_note or historical}</p>' + table
        if quorum.get("kind") == "measurement":
            quorum_label = "Original stock verdict"
        if diagnosis:
            content += f'<p><strong>Original stock refusal.</strong> {_brief_text(diagnosis)}</p>'
        if trial and trial.get("input_sha256") == adopted["input_sha256"]:
            content += '<p>PR-28 independently measured the candidate. PR-29 reproduced those same proof bytes from the qualified source.</p>'
        elif trial:
            content += f'<p><strong>PR-28 experiment.</strong> {_brief_text(trial)}</p>'
    else:
        table = '<table><thead><tr><th scope="col">Check</th><th scope="col">Result on this export</th></tr></thead><tbody>'
        for label, key in (("Source terms equal the resident declarations", "resident_equal"),
                           ("Pinned upstream Lean admitted", "upstream_admitted"),
                           ("Clean’s fenced Rust reference kernel admitted", "fenced_admitted")):
            table += f'<tr><th scope="row">{label}</th><td>{_safe(_ratio(evidence.get(key), n))}</td></tr>'
        table += '</tbody></table>'

        if measured and first:
            summary = f'At line {_safe(first.get("line", "unknown"))}, the adopted checker refused <code>{_safe(first.get("name", "unknown"))}</code>.'
        elif measured:
            summary = "The measured prefix records no refusal."
        else:
            summary = "The first adopted-checker verdict is unverified."
        proof_description = (f'<p>One root, <code>{_safe(root)}</code>, brings in '
                             f'{_number(evidence.get("records"))} declaration records.</p>' if root
                             else '<p>The receipt for the one-root proof input is unavailable.</p>')
        quorum_note = (f'<p><time>{_safe(quorum["date"])}</time> · {_brief_text(quorum)}</p>' if quorum else "")
        if diagnosis:
            quorum_note += f'<p>{_brief_text(diagnosis)}</p>'
        if trial:
            quorum_note += f'<p><strong>Experimental proof.</strong> {_brief_text(trial)}</p>'
        content = proof_description + table + f'<p class="callout">{summary}</p>' + quorum_note
    scope = ('<p>The theorem starts with the Eq, PUnit and Nat families and entries for the PSigma former and constructor. '
             'It applies per universe bound. Each generation relies on its stated base assumptions and retains independent rechecking.</p>')
    slides.append(_slide("boundary", "Who actually checked the proof?", content + scope,
                         [src("Source fidelity and direct replay", ROOT_REPORT),
                          quorum_source,
                          _event_source(quorum_label, quorum, revision) if quorum.get("source") else "",
                          _event_source("Resource diagnosis", diagnosis, revision),
                          _event_source("Const-helper experiment", trial, revision),
                          _event_source("PR-29 source qualification", adoption, revision),
                          src("Semantic scope", c3.get("source"), c3.get("receipt_revision", revision))]))
    names = {"W1": "Run KCheckLabelledMain.lean from Clean source and match expected_output.txt byte for byte.", "W2": "Build the same modules inside Trust.",
             "W3": "Check proof pins, bodies and axioms in that build.", "W4": "Replay real Init declarations with emitted advice.",
             "W5": "Require a sealed verdict at the first production site."}
    states = {"needs_gate_evidence": "Gate evidence needed", "qualified_snapshot": "Qualified snapshot",
              "measured_refusal": "Measured refusal", "unverified": "Unverified"}
    wiring = '<ol class="steps">'
    for name, label in names.items():
        state = units.get(name, {}).get("status")
        status_label = states.get(state, "Unverified") if isinstance(state, str) else "Unverified"
        wiring += (f'<li><b>{name}</b><span>{label}</span>'
                   f'<small>{_safe(status_label)}</small></li>')
    families = units.get("S2-S3", {})
    family_gate = "The first production site comes before new family support."
    if leading_first.get("name") == "Iff" and "W5" in _list(families.get("prerequisites")):
        family_gate = ("After W5, S2–S3 must justify the two-field Iff constructor and its recursor, "
                       "refuse forged input, and replay the same prefix through the next declaration.")
    wiring += ('</ol><p class="callout">' + family_gate
               + ' The quorum must independently agree on the complete proof bytes.</p>')
    if measured and type(evidence.get("outside_named_seed_types")) is int:
        wiring += (f'<p>The input contains {_number(evidence.get("inductive_blocks"))} inductive blocks and {_number(evidence.get("quotient_records"))} '
                   f'quotient records. It includes {_number(evidence.get("outside_named_seed_types"))} family names outside the three '
                   'preregistered types. One general family certificate may cover many. An ETA needs measured progress on these gates.</p>')
    wiring_sources = [src("Adopted wiring order", PLAN), src("Dependency catalog", CATALOG), src("Dated quorum run", QUORUM)]
    console = _map(report.get("console_replay"))
    observed = _console_event(events, console)
    if observed:
        wiring += (f'<p><time>{_safe(observed["date"])}</time> · W6. Pinned Lean and the TrustCG-linked executable printed '
                   f'the same {console["stdout_bytes"]} bytes for genuine Init’s <code>IO.println</code> '
                   'with a C runtime and unvalidated lowering on the compiled side, while Clean still refused '
                   'to sequence two actions (<code>native-eager-io</code>).</p>')
        wiring_sources.append(_event_source("W6 console replay", observed, revision))
    slides.append(_slide("wiring", "What must happen next", wiring, wiring_sources))
    progress = '<dl class="metrics">'
    progress += _metric("Supported Prelude fragment", _ratio(fragment.get("accepted"), fragment.get("inside_fragment")), "Bounded run with the recorded advice and loader.")
    for key, label in (("planted_false_clean", "Clean mutation sites"), ("planted_false_trust", "Trust mutation sites")):
        observation = _observation(metrics.get(key))
        progress += _metric(label, _ratio(observation.get("minted_under_mutant"), observation.get("sites")), "Measured sites issuing a row for the planted false proof.")
    followups = _map(report.get("followups"))
    prefix_receipt, prefix_event = _followup(followups, events, adopted, "PR-30")
    statement_receipt, statement_event = _followup(followups, events, adopted, "PR-31")
    comparison = _prefix_comparison(prefix_receipt, adopted)
    finding = _statement_finding(statement_receipt)
    if comparison or finding:
        sources = [src("Measured figures", BOARD)]
        if comparison:
            sources.append(_event_source("PR-30 prefix replay", prefix_event, revision))
        if finding:
            sources.append(_event_source("PR-31 statement dependencies", statement_event, revision))
        matcher, matcher_event = _followup(followups, events, adopted, "PR-67")
        native = native_matcher_text(matcher) if matcher else ""
        if native:
            sources.append(_event_source("Native proof-stream replay", matcher_event, revision))
            finding += f'<p>{_safe(native)}</p>'
        progress = comparison + finding + progress + '</dl>'
        slides.append(_slide("progress", "Where self-admission stops", progress, sources))
    else:
        progress += ('</dl><p class="lead">Track the first refusal moving forward, then a complete self-admission receipt and real production decisions.</p>'
                     '<p>These mutation counts record exposures to a false proof. A deciding site improves when it refuses that proof. For shipped authority, every deciding site must use the proved compiled checker. The build must license its emitted bodies, '
                     'bind the term, IR and binary, and identify trusted runtime and shell assumptions. The executing Rust model needs proved alignment.</p>'
                     '<p>A smaller proof of the same pinned statement could shorten the replay. Compare its axiom closure, give the new bytes their own series, and retain independent rechecking.</p>')
        slides.append(_slide("progress", "How progress is measured", progress,
                             [src("Measured figures", BOARD), src("Six conditions for authority", PLAN)]))
    planning_content = _planning(planning, adopted)
    pending = next((k for k in names if units.get(k, {}).get("status") != "qualified_snapshot"), None)
    if pending:
        planning_content += f'<p class="callout">Next wiring result · {pending}. {_safe(names[pending])}</p>'
        claims = _list(units.get(pending, {}).get("recorded_claims"))
        if claims and isinstance(claims[0], dict) and isinstance(claims[0].get("owner"), str):
            owner = claims[0]["owner"].split(";", 1)[0].replace("`", "")
            quorum_next = ("Recheck any changed proof export with all four readers." if quorum_note
                           else "Full-root quorum rechecking can proceed in parallel.")
            planning_content += f'<p>Clean records {_safe(owner)} on {pending}. {quorum_next}</p>'
    else:
        planning_content += '<p class="callout">Review independent full-root quorum evidence and the remaining shipped-authority conditions.</p>'
    receipts = _map(report.get("execution_receipts"))
    recent = [row for row in events if isinstance(row, dict) and isinstance(row.get("brief"), str)
              and execution_matches(row, receipts)]
    if recent:
        entries = []
        for row in recent[-5:]:
            label = f"{row.get('unit', '')} · {row.get('kind', '')}"
            entries.append('<li><span><time>' + _safe(row.get("date", "")) + '</time><br>'
                           + _event_source(label, row, revision) + '</span><p>'
                           + _safe(row["brief"]) + '</p></li>')
        slides.append(_slide("execution", "What the latest runs showed",
                             '<ol class="timeline">' + "".join(entries) + '</ol>' + _original_source_histories(planning),
                             [src("Full dated evidence timeline", TIMELINE)]))
    slides.append(_slide("planning", "E1 planning and the next result", planning_content,
                         [src("Work orders and claims", PLAN), src("Gate requirements", CATALOG)]))
    rev_label = revision[:10] if _revision(revision) else "unverified revision"
    return _document(slides, rev_label)


def _document(slides, revision):
    return """<!doctype html>
<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1">
<title>Clean self-proof · Fleet briefing</title><style>""" + _CSS + """</style></head>
<body><a class="skip" href="#answer">Skip to presentation</a><header class="mast">
<h1>Clean self-proof</h1><span>Fleet briefing · """ + _safe(revision) + """</span></header>
<main>""" + "".join(slides) + """</main><nav aria-label="Slide controls" class="navigation" hidden>
<button id="previous" type="button" aria-label="Previous slide">← Previous</button>
<span id="position" aria-live="polite" aria-atomic="true"></span>
<button id="next" type="button" aria-label="Next slide">Next →</button>
<button id="print" type="button">Print or save PDF</button></nav><script>""" + _JS + """</script></body></html>"""


_CSS = """
:root{color-scheme:light;--paper:#f7f4ec;--ink:#182922;--muted:#4c6257;--line:#c2cbbf;--accent:#176149;--wash:#e2ece1}
*{box-sizing:border-box}body{margin:0;background:var(--paper);color:var(--ink);font-family:Inter,"Helvetica Neue",Arial,sans-serif;font-size:clamp(16px,1.3vw,21px);line-height:1.48}
.mast,main,.navigation{width:min(96%,1080px);margin:auto}.mast{border-bottom:1px solid var(--line);padding:1.2rem 1rem;display:flex;justify-content:space-between;align-items:baseline;gap:1rem}
h1,.mast span,footer,.navigation,small,dt{font-size:.83rem}.mast h1{font-size:1rem;margin:0}.mast span,footer,.annotation,small{color:var(--muted)}
.slide{padding:clamp(1.3rem,4vw,3.2rem) clamp(1rem,3vw,2.7rem);min-height:65vh;border-bottom:1px solid var(--line)}
h2{font-family:"Instrument Serif","Iowan Old Style",Baskerville,Georgia,serif;font-weight:500;line-height:1.08;letter-spacing:-.035em;font-size:clamp(2.1rem,5.5vw,4rem);margin:0 0 1.1rem}
h3{font-size:1rem;margin:.9rem 0 .3rem}p{margin:.75rem 0}.lead{font-size:clamp(1.22rem,2.5vw,2.05rem);line-height:1.27;max-width:40em}
a{color:var(--accent);text-underline-offset:.19em;text-decoration-thickness:1px}.skip{position:absolute;left:.5rem;top:-5rem;background:white;padding:.5rem}.skip:focus{top:.25rem}
a:focus-visible,button:focus-visible{outline:3px solid #ad631c;outline-offset:3px}.slide:focus{outline:0}
.metrics{display:grid;grid-template-columns:repeat(3,minmax(0,1fr));gap:1.3rem;margin:1.5rem 0 1rem}.metric{border-top:3px solid var(--accent);padding:.65rem 0}.metric dt{font-weight:650}.metric dd{margin:.3rem 0;font-family:Georgia,serif;font-size:clamp(1.8rem,4vw,3.1rem);line-height:1.1}.metric dd.annotation{font:normal .9rem/1.45 Inter,Arial,sans-serif}
footer{margin-top:1.6rem}.callout,.notice{background:var(--wash);border-left:4px solid var(--accent);padding:.8rem 1rem;margin:1.15rem 0}.notice{background:#f0e6cc;border-color:#815413}
.timeline,.steps{list-style:none;margin:1rem 0;padding:0}.timeline li,.steps li{border-top:1px solid var(--line);padding:.55rem 0;display:grid;gap:1rem}
.timeline li{grid-template-columns:6.5rem 1fr}.timeline p{margin:0;font-size:.99rem}.timeline time{font-size:.85rem;font-weight:650;white-space:nowrap}.steps li{grid-template-columns:2.5rem 1fr auto;align-items:baseline}.steps b{color:var(--accent)}.steps small{font-size:.78rem}
table{width:100%;border-collapse:collapse;margin:1.3rem 0}th,td{text-align:left;padding:.65rem .25rem;border-bottom:1px solid var(--line)}thead{font-size:.78rem;color:var(--muted)}tbody th{font-weight:500}td{font-weight:650;font-variant-numeric:tabular-nums}.facts{display:grid;grid-template-columns:minmax(6rem,12%) 1fr;align-items:baseline;column-gap:1rem}.facts dt,.facts dd{padding:.3rem 0;margin:0}.facts dt{color:var(--muted)}.compact{margin:.3rem 0;padding-left:1.2rem;font-size:.95rem}
code{font-family:"IBM Plex Mono",Menlo,monospace;font-size:.87em;overflow-wrap:anywhere}.navigation{display:flex;align-items:center;gap:.5rem;padding:.9rem 1rem;background:var(--paper);position:sticky;bottom:0;border-top:1px solid var(--line)}[hidden]{display:none}.navigation span{margin-right:auto;color:var(--muted)}button{background:var(--ink);color:white;border:1px solid var(--ink);border-radius:.35rem;padding:.48rem .8rem;font:inherit;cursor:pointer}button:disabled{background:transparent;color:var(--muted);border-color:var(--line);cursor:default}
@media(min-width:641px){#execution .timeline li{grid-template-columns:11rem 1fr}#execution .timeline span{font-size:.89rem}}
@media(max-width:640px){.mast,main,.navigation{width:100%}.metrics{grid-template-columns:1fr;gap:.3rem}.metric{display:grid;grid-template-columns:1fr auto;align-items:baseline;gap:.2rem .7rem}.metric .annotation{grid-column:1/-1}.timeline li{grid-template-columns:1fr;gap:.1rem}.steps li{grid-template-columns:2rem 1fr;gap:.4rem}.steps small{grid-column:2}.navigation{flex-wrap:wrap}.navigation button{padding:.5rem}.mast{flex-wrap:wrap}.slide{min-height:0}}
@media print{@page{size:landscape;margin:14mm}body{background:white;font-size:12pt}.mast,.navigation,.skip{display:none!important}main{width:100%}.slide,.slide[hidden]{display:block!important;min-height:0;padding:0;border:0;break-after:page}.slide:last-child{break-after:auto}h2{font-size:30pt}.lead{font-size:17pt}.metrics{grid-template-columns:repeat(3,1fr)}footer{font-size:9pt}.timeline li{grid-template-columns:6.5rem 1fr}.callout,.metric{break-inside:avoid}}
"""

_JS = """
(function () {
  const sections = Array.from(document.querySelectorAll('main .slide'));
  const previous = document.getElementById('previous'), next = document.getElementById('next');
  const position = document.getElementById('position');
  let current = 0;
  function fromHash() { return Math.max(0, sections.findIndex(s => '#' + s.id === location.hash)); }
  function show(index, focus) {
    current = Math.max(0, Math.min(sections.length - 1, index));
    sections.forEach((section, i) => { section.hidden = i !== current; });
    previous.disabled = current === 0; next.disabled = current === sections.length - 1;
    position.textContent = (current + 1) + ' of ' + sections.length;
    if (focus) { sections[current].focus(); window.scrollTo(0, 0); }
  }
  function go(index) {
    if (index < 0 || index >= sections.length || index === current) return;
    location.hash = sections[index].id;
  }
  previous.addEventListener('click', () => go(current - 1));
  next.addEventListener('click', () => go(current + 1));
  document.getElementById('print').addEventListener('click', () => window.print());
  window.addEventListener('hashchange', () => show(fromHash(), true));
  document.addEventListener('keydown', event => {
    if (event.altKey || event.metaKey || event.ctrlKey || event.shiftKey) return;
    if (event.target.closest('input,textarea,select,[contenteditable="true"]')) return;
    const keys = {ArrowRight: current + 1, PageDown: current + 1, ArrowLeft: current - 1, PageUp: current - 1, Home: 0, End: sections.length - 1};
    if (Object.prototype.hasOwnProperty.call(keys, event.key)) { event.preventDefault(); go(keys[event.key]); }
  });
  show(fromHash(), false);
  document.querySelector('.navigation').hidden = false;
})();
"""
