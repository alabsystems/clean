#!/usr/bin/env python3
# Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0
"""The presentation keeps proof subjects, dates and source revisions distinct."""

from html.parser import HTMLParser
import json
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
from self_proof_fleet_slides import _event_source, render_slides


SOURCE = "1" * 40
MEASURED_AT = "2" * 40


class Document(HTMLParser):
    def __init__(self, html):
        super().__init__()
        self.tags = []
        self.text = []
        self.feed(html)

    def handle_starttag(self, tag, attrs):
        self.tags.append((tag, dict(attrs)))

    def handle_data(self, data):
        self.text.append(data)

    def all(self, tag):
        return [attrs for element, attrs in self.tags if element == tag]


class PresentationTests(unittest.TestCase):
    def test_measured_subjects_and_revision(self):
        report = {
            "c3": {"state": "qualified_snapshot", "revision": MEASURED_AT, "source": "reports/proof.json"},
            "literal_export": {"state": "measured", "root": "KCheck.CompleteSound.kcheck_sound",
                               "declarations": 4912, "records": 4402, "prefix_accepted": 0,
                               "resident_equal": 4912, "upstream_admitted": 4912, "fenced_admitted": 4912,
                               "first_refusal": {"line": 55, "name": "Iff"}},
            "metrics": {"production": {"real_declarations_decided": 0}},
        }
        timeline = {"events": [
            {"kind": "measurement", "date": "2026-11-15", "unit": "C4-C5",
             "source": "reports/advice.md", "summary": "Advice improved 9 to 22 on Prelude."},
            {"kind": "measurement", "date": "2026-11-16", "unit": "Q4",
             "source": "reports/quorum.md", "summary": "ck0 accepted 57,418 on restricted Init."},
            {"kind": "blocker", "date": "2026-11-17", "unit": "Q4",
             "source": "reports/other.md", "summary": "ck0 admitted 4,906 on each original proof stream."},
            {"kind": "wiring", "date": "2026-11-17", "unit": "CL-03",
             "source": "docs/DECISIONS.md", "summary": "Fresh fenced-kernel replay admitted all 10 fixture declarations."},
        ]}
        doc = Document(render_slides(report, timeline, revision=SOURCE))
        text = " ".join(doc.text)
        self.assertIn("4,912 / 4,912", text)
        self.assertIn("Iff", text)
        self.assertIn("9 to 22 on Prelude", text)
        self.assertIn("57,418 on restricted Init", text)
        self.assertIn("4,906 on each original proof stream", text)
        self.assertIn("10 fixture declarations", text)
        self.assertIn(MEASURED_AT[:10], text)
        sources = [a["href"] for a in doc.all("a") if a["href"] != "#answer"]
        self.assertIn(f"https://github.com/alabsystems/clean/blob/{SOURCE}/reports/proof.json", sources)
        self.assertTrue(all(f"/blob/{SOURCE}/" in url for url in sources))
        self.assertEqual(len(doc.all("section")), 6)
        self.assertTrue(all("aria-labelledby" in section and "hidden" not in section for section in doc.all("section")))
        self.assertEqual([b["id"] for b in doc.all("button")], ["previous", "next", "print"])

    def test_weekly_history_retains_adoption_and_the_qualified_fourth_vote(self):
        from self_proof_fleet_slides import _milestones
        selected = [("10-15", "authority", "decision"), ("11-12", "authority", "decision"),
                    ("11-14", "C3", "proof"), ("11-15", "C3", "measurement"),
                    ("11-15", "C4-C5", "measurement"), ("11-16", "Q4", "measurement"),
                    ("11-17", "CL-03", "wiring"), ("11-18", "Q4", "measurement")]
        events = [{"date": "2026-" + day, "unit": unit, "kind": kind, "summary": day + " " + unit,
                   "source": unit + ".md", "source_revision": SOURCE, "source_sha256": "b" * 64}
                  for day, unit, kind in selected]
        def days(qualified):
            return [value for value in Document(_milestones(events, SOURCE, quorum=qualified)).text
                    if value.startswith("2026-")]
        self.assertEqual(days(events[-1]), ["2026-11-" + d for d in ("12", "14", "15", "16", "17", "18")])
        self.assertNotIn("2026-11-18", days({**events[-1], "source_sha256": "c" * 64}))

    def test_dated_links_use_the_recorded_source_revision(self):
        timeline = Path(__file__).resolve().parents[1] / "data/self_proof_fleet_timeline.json"
        events = json.loads(timeline.read_text())["events"]
        pins = {"c72b68371186c66ab0debdd8e2714877d3bab6c7": "W1",
                "c08933d6cd27e219f820c4bb797dea0af5de7fde": "W1",
                "550b430cc9db12d8c40ff85ca4fcc62dfad34a13": "W6"}
        for revision, unit in pins.items():
            event = next(row for row in events if row.get("source_revision") == revision and row["unit"] == unit)
            expected = f"https://github.com/alabsystems/clean/blob/{revision}/{event['source']}"
            self.assertEqual(Document(_event_source(event["date"], event, SOURCE)).all("a"), [{"href": expected}])

        def slide_links(revision):
            # Both the dated milestone and the quorum footer use the same source.
            event = {"unit": "Q4", "kind": "measurement", "date": "2026-11-16",
                     "source": "reports/quorum.md", "summary": "Observed.", "source_revision": revision,
                     "input_sha256": "a1" * 32}
            report = {"literal_export": {"state": "measured", "sha256": event["input_sha256"]}}
            return [row["href"] for row in Document(render_slides(report, [event], revision=SOURCE)).all("a")
                    if row["href"].endswith("/reports/quorum.md")]

        self.assertEqual(slide_links(MEASURED_AT),
                         [f"https://github.com/alabsystems/clean/blob/{MEASURED_AT}/reports/quorum.md"] * 2)
        self.assertEqual(slide_links("main"), [])

    def test_quorum_measurement_binds_the_measured_export_bytes(self):
        digest = "a7" * 32
        evidence = {"state": "measured", "sha256": digest}
        old = {"unit": "Q4", "kind": "blocker", "date": "2026-11-17", "source": "reports/old.md",
               "summary": "On the original stream ck0 stopped."}
        measured = {"unit": "Q4", "kind": "measurement", "date": "2026-11-18", "source": "reports/same.md",
                    "input_sha256": digest, "summary": "Stock ck0 checked the corrected stream."}

        def boundary(literal_export, rows):
            html = render_slides({"literal_export": literal_export}, rows, revision=SOURCE)
            return Document(html.split('id="boundary"', 1)[1].split("</section>", 1)[0])

        matched = boundary(evidence, [old, measured, {**measured, "input_sha256": "b" * 64,
                                                     "summary": "Different proof bytes"}])
        words = " ".join(matched.text)
        self.assertIn(measured["summary"], words)
        self.assertIn(measured["date"], words)
        self.assertNotIn(old["summary"], words)
        self.assertNotIn("Different proof bytes", words)
        sources = [attrs["href"] for attrs in matched.all("a")]
        self.assertIn(f"https://github.com/alabsystems/clean/blob/{SOURCE}/reports/same.md", sources)

        for snapshot_change, event_change in [
            ({"state": "unverified"}, {}), ({"sha256": None}, {}), ({"sha256": "b" * 64}, {}),
            ({"sha256": "malformed"}, {"input_sha256": "malformed"}), ({}, {"input_sha256": None}),
            ({}, {"unit": "Q1"}), ({}, {"kind": "blocker"}), ({}, {"date": ""}), ({}, {"date": "2026-13-01"}),
        ]:
            with self.subTest(snapshot_change=snapshot_change, event_change=event_change):
                doc = boundary({**evidence, **snapshot_change}, [old, {**measured, **event_change}])
                self.assertIn(old["summary"], " ".join(doc.text))
                self.assertNotIn(measured["summary"], " ".join(doc.text))
        unbound = dict(measured)
        del unbound["input_sha256"]
        orphan = boundary({"state": "measured"}, [unbound])
        self.assertNotIn(measured["summary"], " ".join(orphan.text))

    def test_diagnostic_attaches_only_to_the_named_stock_receipt_and_input(self):
        digest, stock_digest = "a7" * 32, "b3" * 32
        measured = {"unit": "Q4", "kind": "measurement", "date": "2026-11-17",
                    "summary": "Full stock history.", "brief": "Stock admitted 4,906 names.",
                    "source": "reports/stock.md", "input_sha256": digest, "stock_result_sha256": stock_digest}
        diagnosis = {**measured, "kind": "blocker", "summary": "Full diagnostic history.",
                     "brief": "The observer recorded 2,096,959 proof-body steps.", "source": "reports/observer.md"}

        def boundary(stock, blocker):
            snapshot = {"literal_export": {"state": "measured", "sha256": digest}}
            html = render_slides(snapshot, [stock, blocker], revision=SOURCE)
            return Document(html.split('id="boundary"', 1)[1].split("</section>", 1)[0])

        section = boundary(measured, diagnosis)
        self.assertIn(measured["brief"], " ".join(section.text))
        self.assertIn(diagnosis["brief"], " ".join(section.text))
        self.assertIn(f"https://github.com/alabsystems/clean/blob/{SOURCE}/reports/observer.md",
                      [a["href"] for a in section.all("a")])
        for stock_change, blocker_change in [
            ({}, {"stock_result_sha256": "1" * 64}), ({}, {"input_sha256": "2" * 64}),
            ({"stock_result_sha256": None}, {"stock_result_sha256": None}),
            ({"stock_result_sha256": "invalid"}, {"stock_result_sha256": "invalid"}),
            ({}, {"date": "invalid"}), ({}, {"unit": "W1"}), ({}, {"kind": "proof"}),
        ]:
            with self.subTest(stock_change=stock_change, blocker_change=blocker_change):
                section = boundary({**measured, **stock_change}, {**diagnosis, **blocker_change})
                self.assertIn(measured["brief"], " ".join(section.text))
                self.assertNotIn(diagnosis["brief"], " ".join(section.text))
        section = boundary(measured, {**diagnosis, "brief": []})
        self.assertIn(diagnosis["summary"], " ".join(section.text))

    def test_qualified_joined_source_requires_its_own_dated_receipt(self):
        current = {"state": "qualified", "qualified_revision": SOURCE, "input_sha256": "c" * 64,
                   "qualification_sha256": "d" * 64, "declarations": 5, "stock_admitted": 5, "resident_equal": 5,
                   "upstream_admitted": 5, "fenced_admitted": 5, "fourth_member_qualified": False,
                   "root": "KCheck.root", "records": 4, "prefix_accepted": 0, "first_refusal": {"name": "Packet", "line": 12}}
        original = {"state": "measured", "declarations": 3, "records": 2, "sha256": "e" * 64, "resident_equal": 3}
        report = {"literal_export": original, "source_qualification": current}
        event = {"date": "2026-11-17", "unit": "PR-29", "obligation": "Q4", "kind": "measurement",
                 "source": "reports/adoption/README.md", "summary": "Adopted proof source qualified.",
                 "input_sha256": "c" * 64, "qualification_sha256": "d" * 64}
        def content(snapshot, rows):
            return " ".join(Document(render_slides(snapshot, rows, revision=SOURCE)).text)
        live = content(report, [event])
        claimed = {**report, "units": [{"id": "W1", "recorded_claims": [{"owner": "source team"}]}]}
        vote = {"input_sha256": current["input_sha256"], "declarations": 5, "epoch": SOURCE,
                "members": ["ck0-stock", "clean-reference", "lean", "lean4lean"]}
        self.assertIn("Full-root quorum rechecking can proceed in parallel.", content(claimed, [event]))
        self.assertIn("Recheck any changed proof export with all four readers.",
                      content({**claimed, "soundness_root_quorum": vote}, [event]))
        self.assertNotIn("Recheck any changed proof export with all four readers.",
                         content({**claimed, "soundness_root_quorum": {**vote, "input_sha256": "a" * 64}}, [event]))
        for text in ("PR-29 qualified source", "5 / 5", "0 / 4", "Packet", "Original Clean export", "3 / 3"):
            self.assertIn(text, live)
        # Both exports need their own denominators and full-root result in one comparison.
        original = {**original, "prefix_accepted": 0, "first_refusal": {"name": "Packet", "line": 10}}
        trial_receipt = {"state": "recorded", "result_sha256": "f" * 64, "input_sha256": current["input_sha256"],
                         "baseline_input_sha256": original["sha256"], "baseline_named": 3, "baseline_stock_admitted": 2}
        prior = {**event, "unit": "PR-28", "baseline_input_sha256": original["sha256"], "result_sha256": "f" * 64,
                 "source": "reports/trial.md", "summary": "Experimental proof vote."}
        original_vote = {**event, "unit": "Q4", "input_sha256": original["sha256"], "stock_result_sha256": "a" * 64,
                         "source": "reports/original-stock.md", "summary": "Original stock vote."}
        diagnosis = {**original_vote, "kind": "blocker", "source": "reports/diagnosis.md", "summary": "Measured original cost."}
        samples = [prior, original_vote, diagnosis, event]
        complete = {**report, "literal_export": original, "const_helper_trial": trial_receipt}
        html = render_slides(complete, samples, revision=SOURCE)
        section = html.split('id="boundary"', 1)[1].split("</section>", 1)[0]
        words = " ".join(Document(section).text)
        for text in ("Export size 3 names · 2 records 5 names · 4 records",
                     "Stock ck0 admitted 2 / 3 · root refused 5 / 5 · root admitted",
                     "0 / 2 · Packet, line 10 0 / 4 · Packet, line 12", "The PR-29 receipt recorded no qualified Lean4Lean vote",
                     "Measured original cost.", "PR-29 reproduced those same proof bytes"):
            self.assertIn(text, words)
        links = [tag.get("href", "") for tag in Document(section).all("a")]
        for source in (prior["source"], original_vote["source"], diagnosis["source"], event["source"]):
            self.assertTrue(any(link.endswith("/" + source) for link in links), source)
        unbound = {**complete, "const_helper_trial": {**trial_receipt, "baseline_named": 7}}
        self.assertNotIn("2 / 3 · root refused", content(unbound, samples))
        self.assertIn("Stock ck0 admitted Unverified 5 / 5 · root admitted", content(unbound, samples))
        for rows in ([], [{**event, "qualification_sha256": "0" * 64}], [{**event, "input_sha256": "0" * 64}],
                     [{**event, "obligation": "W1"}]):
            self.assertNotIn("PR-29 qualified source", content(report, rows))
        source = ("python3 reports/self-proof-const-helper-adoption/verify.py # qualified_revision=" + SOURCE
                  + " qualification_sha256=" + "d" * 64 + " export_sha256=" + "c" * 64)
        planning = {"state": "available", "measurements": [
            {"metric": "E1.stock_ck0_soundness_root_admitted", "source": source, "value": 5, "unit": "declarations"}]}
        self.assertIn("PR-29 qualified source · Soundness-root declarations admitted by stock ck0 — 5",
                      " ".join(Document(render_slides(report, [event], planning)).text))
        self.assertNotIn("stock ck0 — 5", " ".join(Document(render_slides(report, [], planning)).text))
        self.assertNotIn("PR-29 qualified source", content({"literal_export": original}, [event]))
        for partial in ({**current, "first_refusal": {}}, {**current, "stock_admitted": 0}, {**current, "records": None}):
            self.assertNotIn("PR-29 qualified source", content({**report, "source_qualification": partial}, [event]))
        self.assertNotIn("PR-29 qualified source", content({**report, "source_qualification": {"state": "unverified"}}, [event]))

    def test_prefix_subjects_and_statement_path_require_their_own_dated_receipts(self):
        subject = "c" * 64
        adoption = {"state": "qualified", "qualified_revision": SOURCE, "qualification_sha256": "d" * 64,
                    "input_sha256": subject, "declarations": 4913, "stock_admitted": 4913, "resident_equal": 4913,
                    "upstream_admitted": 4913, "fenced_admitted": 4913, "fourth_member_qualified": False,
                    "root": "KCheck.CompleteSound.kcheck_sound", "records": 4403, "prefix_accepted": 0,
                    "first_refusal": {"name": "Iff", "line": 55}}
        def event(unit, pin):
            return {"date": "2026-11-17", "kind": "measurement", "unit": unit, "input_sha256": subject,
                    "qualification_sha256": pin * 64, "source_revision": MEASURED_AT,
                    "source": f"reports/{unit}.md", "summary": "Qualified."}
        pr29, pr30, pr31 = event("PR-29", "d"), event("PR-30", "a"), event("PR-31", "b")
        pr29["obligation"] = "Q4"
        current = {"input_sha256": subject, "accepted_records": 0, "declaration_records": 4403,
                   "accepted_named_declarations": 0, "named_declarations": 4913, "first_refusal": "Iff", "line": 55}
        prior = {"input_sha256": "e" * 64, "accepted_records": 1, "declaration_records": 4402,
                 "accepted_named_declarations": 4, "named_declarations": 4912, "first_refusal": "List", "line": 116}
        prefix = {**pr30, "current": current, "historical": prior}
        statement = {**pr31, "targets": ["Iff", "Quot", "List"], "root_proof_body_used": False,
                     "statement_sha256": "f" * 64, "edges_checked": 13}
        def page(replay=prefix, paths=statement, rows=(pr29, pr30, pr31), baseline=adoption):
            snap = {"source_qualification": baseline, "followups": {"PR-30": replay, "PR-31": paths}}
            deck = render_slides(snap, list(rows), revision=SOURCE)
            return Document(deck.split('id="progress"', 1)[1].split("</section>", 1)[0])

        result = page()
        text = " ".join(result.text)
        self.assertIn("Current Clean " + subject[:12] + " 0 / 4,403 0 / 4,913 Iff, line 55", text)
        self.assertIn("Historical upstream Lean " + prior["input_sha256"][:12] + " 1 / 4,402 4 / 4,912 List, line 116", text)
        self.assertIn("Changing only the final proof body leaves", text)
        links = [r["href"] for r in result.all("a")]
        for unit in ("PR-30", "PR-31"):
            self.assertIn(f"https://github.com/alabsystems/clean/blob/{MEASURED_AT}/reports/{unit}.md", links)
        for replay in ({}, {**prefix, "input_sha256": "1" * 64}, {**prefix, "state": "unverified"},
                       {**prefix, "source_revision": SOURCE}, {**prefix, "qualification_sha256": "0" * 64},
                       {**prefix, "historical": {**prior, "input_sha256": subject}},
                       {**prefix, "historical": {**prior, "accepted_named_declarations": None}},
                       {**prefix, "current": {**current, "line": 56}}):
            words = " ".join(page(replay=replay).text)
            self.assertNotIn("Historical upstream Lean", words)
            self.assertIn("Changing only the final proof body leaves", words)
        for changes in ({"root_proof_body_used": True}, {"targets": ["Quot", "List"]}, {"edges_checked": 0},
                        {"statement_sha256": "invalid"}, {"input_sha256": "1" * 64}, {"qualification_sha256": "1" * 64}):
            words = " ".join(page(paths={**statement, **changes}).text)
            self.assertNotIn("Changing only the final proof body leaves", words)
            self.assertIn("Historical upstream Lean", words)
        for old in (page(rows=(pr29,)), page(baseline={"state": "unverified"})):
            self.assertNotIn("Where self-admission stops", " ".join(old.text))
            self.assertIn("How progress is measured", " ".join(old.text))

    def test_wiring_shows_both_console_outcomes_only_on_the_bound_replay(self):
        receipt = {"source_revision": MEASURED_AT, "receipt_sha256": "a" * 64, "module_digest": "sha256:" + "b" * 64,
                   "runtime": "C via cc", "lowered": "clean-compiler-unvalidated",
                   "pair_refusal": "native-eager-io", "stdout_bytes": 14}
        event = {"unit": "W6", "obligation": "X3-X5", "kind": "measurement", "date": "2026-11-17",
                 "source": "reports/self-proof-w6-console-2026-11-17/README.md", "summary": "Console replay.",
                 **{k: receipt[k] for k in ("source_revision", "receipt_sha256", "module_digest")}}
        def wiring(observed, events):
            html = render_slides({"console_replay": observed}, events, revision=SOURCE)
            return Document(html.split('id="wiring"', 1)[1].split("</section>", 1)[0])
        page = wiring(receipt, [event])
        words = " ".join(page.text)
        for expected in (event["date"], "same 14 bytes", "IO.println", "C runtime and unvalidated lowering",
                         "refused to sequence two actions", "native-eager-io"):
            self.assertIn(expected, words)
        self.assertIn(f"https://github.com/alabsystems/clean/blob/{MEASURED_AT}/{event['source']}",
                      [r["href"] for r in page.all("a")])
        bad_events = [[], [{**event, "kind": "blocker"}], [{**event, "receipt_sha256": "c" * 64}],
                      [{**event, "source_revision": SOURCE}], [{**event, "source": "reports/other.md"}],
                      [{**event, "module_digest": "sha256:" + "c" * 64}], [{**event, "obligation": "W1"}]]
        for events in bad_events:
            self.assertNotIn("TrustCG-linked executable", " ".join(wiring(receipt, events).text))
        for invalid in (None, {}, {**receipt, "stdout_bytes": True}, {**receipt, "runtime": "unknown"},
                        {**receipt, "lowered": "validated"}, {**receipt, "pair_refusal": None}):
            self.assertNotIn("TrustCG-linked executable", " ".join(wiring(invalid, [event]).text))

    def test_execution_slide_only_uses_the_receipt_at_the_cited_revision(self):
        receipt = "reports/run/result.json"
        digest = "a" * 64
        row = {"date": "2026-11-17", "kind": "blocker", "unit": "W1", "source": receipt,
               "source_revision": SOURCE, "source_sha256": digest, "brief": "Stopped at the first import."}
        report = {"execution_receipts": {SOURCE + ":" + receipt: digest}}
        self.assertIn("Stopped at the first import.", render_slides(report, [row]))
        for changed in ({"source_sha256": "b" * 64}, {"source_revision": "c" * 40},
                        {"source": "reports/other.json"}):
            self.assertNotIn('id="execution"', render_slides(report, [{**row, **changed}]))

    def test_execution_slide_uses_the_separately_pinned_replay(self):
        row = {"unit": "W1", "source": "reports/run", "source_revision": SOURCE,
               "source_sha256": "a" * 64, "brief": "Compared both entries.",
               "replay_revision": "c" * 40, "replay_source": "reports/other", "replay_sha256": "b" * 64}
        primary = {SOURCE + ":reports/run": row["source_sha256"]}
        self.assertNotIn(row["brief"], render_slides({"execution_receipts": primary}, [row]))
        receipts = {**primary, row["replay_revision"] + ":reports/other": row["replay_sha256"]}
        self.assertIn(row["brief"], render_slides({"execution_receipts": receipts}, [row]))
        self.assertNotIn(row["brief"], render_slides({"execution_receipts": receipts},
                                                    [{**row, "replay_revision": SOURCE}]))

    def test_execution_keeps_typed_source_histories_and_their_publication_rows(self):
        token, psigma = "w1_original_token_declarations_elaborated", "w1_psigma_syntax_named_declarations"
        identity = "w3_advice_start_canonical_digest_matches"
        cursor = "w3_advice_exhausted_resident_body_checked"
        units = {token: "of 11 original declarations", psigma: "of 9 original named declarations",
                 identity: "of 1 original checker definition", cursor: "of 1 original cursor predicate body"}
        definitions = [{"id": "E1." + name, "pk": "E1." + name, "name": name, "goal": "E1",
                        "unit": unit, "units": [unit]} for name, unit in units.items()]

        def reading(name, line, day, value):
            ref = f"{MEASURED_AT}:goals/data/metrics.tsv:{line}"
            return {"metric_id": "E1." + name, "metric": name, "goal": "E1", "date": day, "at": day,
                    "pk": ref, "publication_ref": ref, "value": value, "unit": units[name]}

        first = reading(token, 304, "2026-11-16", "6")
        second = reading(token, 98, "2026-11-18", "2")
        last = reading(token, 105, "2026-11-18", "11")
        other = reading(psigma, 109, "2026-11-18", "4")
        newer = [{"metric": "unrelated", "value": "40"}] * 6
        mismatch = reading(identity, 110, "2026-11-18", "0")
        match = reading(identity, 112, "2026-11-18", "1")
        cursor_refusal = reading(cursor, 114, "2026-11-18", "0")
        rows = [last, other, first, second, match, mismatch, cursor_refusal, *newer]
        plan = {"state": "available", "backend": "publication", "publication_commit": MEASURED_AT, "goal": "E1",
                "publication_source": "refs/remotes/origin/main", "metrics": definitions, "measurements": rows,
                "capabilities": {"agoals": {"product": "aGoals", "schema": 1, "backend": "publication",
                                             "family_registered": False}}}
        events = [{"source_revision": SOURCE, "source": f"reports/{i}.json", "source_sha256": "a" * 64,
                   "brief": f"Recent run {i}."} for i in range(7)]
        report = {"execution_receipts": {SOURCE + ":" + e["source"]: e["source_sha256"] for e in events}}

        def execution(**updates):
            html = render_slides(report, events, {**plan, **updates}, revision=SOURCE)
            return Document(html.split('id="execution"', 1)[1].split("</section>", 1)[0])

        doc = execution()
        words = "".join(doc.text)
        self.assertIn("Original Token · 6 → 2 → 11 of 11 original declarations elaborated", words)
        self.assertIn("Original PSigma · 4 of 9 original named declarations elaborated", words)
        self.assertIn("Advice.start identity · 0 → 1 of 1 original checker definition matched its upstream digest", words)
        self.assertIn("Advice.exhausted · 0 of 1 original cursor predicate body checked by pinned Lean", words)
        self.assertNotIn("Advice.exhausted · 1", words)
        accepted = reading(cursor, 115, "2026-11-18", "1")
        updated = execution(measurements=[accepted, *rows])
        self.assertIn("Advice.exhausted · 0 → 1 of 1 original cursor predicate body checked by pinned Lean",
                      "".join(updated.text))
        self.assertIn(f"https://github.com/alabsystems/publication/blob/{MEASURED_AT}/goals/data/metrics.tsv#L115",
                      [r["href"] for r in updated.all("a")])
        wrong = "of 2 original checker definition"
        altered = [{**d, "unit": wrong, "units": [wrong]} if d["name"] == identity else d for d in definitions]
        self.assertNotIn("Advice.start identity", "".join(execution(
            metrics=altered, measurements=[{**match, "unit": wrong}]).text))
        self.assertIn("Recent run 6.", words)
        hrefs = [a["href"] for a in doc.all("a") if "/publication/" in a["href"]]
        self.assertEqual(hrefs, [f"https://github.com/alabsystems/publication/blob/{MEASURED_AT}/goals/data/metrics.tsv#L{n}"
                                 for n in (304, 98, 105, 109, 110, 112, 114)])
        self.assertNotIn("Original Token", "".join(execution(measurements=[other]).text))
        self.assertIn("6 → 11", "".join(execution(measurements=[first, last]).text))
        for invalid in ({"unit": units[psigma]}, {"value": "12"}, {"goal": "C1"}, {"metric_id": "C1." + token},
                        {"publication_ref": first["publication_ref"].replace(MEASURED_AT, SOURCE)},
                        {"pk": "foreign"}, {"date": "2026-02-30", "at": "2026-02-30"}):
            with self.subTest(invalid=invalid):
                words = "".join(execution(measurements=[{**first, **invalid}, second, other]).text)
                self.assertNotIn("Original Token", words)
                self.assertIn("Original PSigma", words)
        self.assertNotIn("Original Token", "".join(execution(metrics=definitions[1:]).text))
        self.assertNotIn("Original Token", "".join(execution(measurements=[first, first]).text))
        self.assertNotIn("Original Token", "".join(execution(publication_source="offline-working-copy").text))

    def test_planning_names_the_stock_ck0_soundness_root_measurement(self):
        for metric in ("stock_ck0_soundness_root_admitted", "E1.stock_ck0_soundness_root_admitted"):
            planning = {"state": "available", "measurements": [{"metric": metric, "value": "42",
                                                                 "unit": "declarations"}]}
            text = " ".join(Document(render_slides({}, [], planning)).text)
            self.assertIn("Soundness-root declarations admitted by stock ck0 — 42 · declarations", text)

    def test_completed_package_keeps_its_receipt_and_releases_its_active_claim(self):
        row = {"id": "CL-03", "title": "Source export", "state": "done", "claimed_by": "original owner",
               "done_on": "2026-11-17", "evidence": "Release fixture passed", "dispatchable": False,
               "publication_ref": f"{MEASURED_AT}:goals/data/packages.tsv:331"}
        plan = {"state": "available", "backend": "publication", "publication_commit": MEASURED_AT,
                "capabilities": {"native_table": False, "agoals": {"product": "aGoals", "backend": "publication",
                                                                   "family_registered": False}},
                "packages": [row, {"state": "running", "claim": "current owner", "dispatchable": False},
                             {"state": "ready", "dispatchable": False}]}
        doc = Document(render_slides({}, [], plan, revision=SOURCE))
        text = " ".join(doc.text)
        self.assertIn("aGoals reads E1 from publication", text)
        self.assertIn("3 packages, 1 active claim, 0 ready to dispatch", text)
        self.assertIn("Source export", text)
        url = f"https://github.com/alabsystems/publication/blob/{MEASURED_AT}/goals/data/packages.tsv#L331"
        self.assertIn(url, [a["href"] for a in doc.all("a")])
        row["publication_ref"] = f"{SOURCE}:goals/data/packages.tsv:331"
        del row["dispatchable"]
        other = Document(render_slides({}, [], plan, revision=SOURCE))
        self.assertNotIn("ready to dispatch", " ".join(other.text))
        self.assertFalse(any("publication/blob" in a["href"] for a in other.all("a")))
        plan["state"] = "unavailable"
        self.assertNotIn("Source export", " ".join(Document(render_slides({}, [], plan, revision=SOURCE)).text))

    def test_planning_links_the_eligible_package_on_its_publication_revision(self):
        ready = {"id": "PR-28", "title": "Check the const helper", "state": "ready", "dispatchable": True,
                 "publication_ref": f"{MEASURED_AT}:goals/data/packages.tsv:427"}
        blocked = {"id": "PR-03", "title": "Waiting package", "state": "ready", "dispatchable": False}
        plan = {"state": "available", "backend": "publication", "publication_commit": MEASURED_AT,
                "packages": [ready, blocked]}
        doc = Document(render_slides({}, [], plan, revision=SOURCE))
        words = " ".join(doc.text)
        url = f"https://github.com/alabsystems/publication/blob/{MEASURED_AT}/goals/data/packages.tsv#L427"
        self.assertIn("2 packages, 0 active claims, 1 ready to dispatch", words)
        self.assertIn("PR-28 · Check the const helper", words)
        self.assertNotIn("Waiting package", words)
        self.assertIn(url, [a["href"] for a in doc.all("a")])
        ready["publication_ref"] = f"{SOURCE}:goals/data/packages.tsv:427"
        other = Document(render_slides({}, [], plan, revision=SOURCE))
        self.assertFalse(any("publication/blob" in a["href"] for a in other.all("a")))
        del blocked["dispatchable"]
        uncertain = Document(render_slides({}, [], plan, revision=SOURCE))
        self.assertNotIn("PR-28", " ".join(uncertain.text))

    def test_same_day_completions_have_no_invented_order(self):
        packages = [{"id": name, "state": "done", "evidence": "Retained check", "done_on": day}
                    for name, day in [("PR-9", "2026-11-17"), ("PR-10", "2026-11-17"), ("PR-8", "2026-11-16")]]
        text = " ".join(Document(render_slides({}, [], {"state": "available", "packages": packages})).text)
        self.assertIn("2 packages completed on 2026-11-17, including PR-10", text)
        self.assertNotIn("Latest recorded completion", text)

    def test_reading_links_to_its_pinned_measurement_row(self):
        reading = {"metric": "w6_byte_equality_uncovered_instructions", "value": "22",
                   "publication_ref": f"{MEASURED_AT}:goals/data/metrics.tsv:422"}
        plan = {"state": "available", "backend": "publication", "publication_commit": MEASURED_AT,
                "measurements": [reading]}
        render = lambda: Document(render_slides({}, [], plan))
        url = f"https://github.com/alabsystems/publication/blob/{MEASURED_AT}/goals/data/metrics.tsv#L422"
        self.assertIn(url, [a["href"] for a in render().all("a")])
        self.assertIn("Machine instructions awaiting proof in the byte-equality object", " ".join(render().text))
        for bad_ref in [f"{SOURCE}:goals/data/metrics.tsv:422", f"{MEASURED_AT}:goals/data/packages.tsv:422"]:
            reading["publication_ref"] = bad_ref
            self.assertNotIn(url, [a["href"] for a in render().all("a")])

    def test_planning_shows_a_recorded_result_alongside_the_owned_and_available_work(self):
        packages = [
            {"id": "CL-03", "title": "Source export", "state": "done", "claimed_by": "export-session-retained-in-history",
             "evidence": "Release fixture passed", "done_on": "2026-11-17", "dispatchable": False},
            {"id": "PR-28", "title": "Const helper", "state": "running", "claim": "session <45>",
             "publication_ref": f"{MEASURED_AT}:goals/data/packages.tsv:428", "dispatchable": False},
            {"id": "PR-30", "title": "Replay the candidate", "state": "ready", "dispatchable": True},
        ]
        plan = {"state": "available", "backend": "publication", "publication_commit": MEASURED_AT,
                "packages": packages}
        doc = Document(render_slides({}, [], plan, revision=SOURCE))
        words = " ".join(doc.text)
        self.assertIn("3 packages, 1 active claim, 1 ready to dispatch", words)
        self.assertIn("PR-28 · Const helper", words)
        self.assertIn("(session <45>)", words)
        self.assertIn("CL-03 · Source export", words)
        self.assertIn("PR-30 · Replay the candidate", words)
        self.assertNotIn("export-session-retained-in-history", words)
        url = f"https://github.com/alabsystems/publication/blob/{MEASURED_AT}/goals/data/packages.tsv#L428"
        self.assertIn(url, [a["href"] for a in doc.all("a")])

    def test_candidate_result_keeps_its_own_stream_and_requires_the_displayed_baseline(self):
        baseline = "a" * 64
        candidate = "b" * 64
        report = {"literal_export": {"state": "measured", "sha256": baseline},
                  "const_helper_trial": {"state": "recorded", "result_sha256": "c" * 64, "input_sha256": candidate}}
        event = {"date": "2026-11-17", "unit": "PR-28", "kind": "measurement",
                 "result_sha256": "c" * 64, "input_sha256": candidate, "baseline_input_sha256": baseline,
                 "summary": "Separately checked proof bytes", "brief": "The experimental member accepted.",
                 "source": "reports/trial/README.md"}
        doc = Document(render_slides(report, [event], revision=SOURCE))
        self.assertIn("The experimental member accepted.", " ".join(doc.text))
        self.assertIn("Separately checked proof bytes", " ".join(doc.text))
        for replacement in ({"baseline_input_sha256": candidate}, {"input_sha256": baseline},
                            {"input_sha256": "unknown"}, {"result_sha256": "d" * 64}):
            other = Document(render_slides(report, [{**event, **replacement}], revision=SOURCE))
            self.assertNotIn("The experimental member accepted.", " ".join(other.text))
            self.assertNotIn("Separately checked proof bytes", " ".join(other.text))

    def test_missing_evidence_and_revision(self):
        report = {"c3": {"state": "qualified_snapshot", "revision": "short"},
                  "literal_export": {"state": "unverified", "declarations": 999999, "first_refusal": {"name": "unearned"}},
                  "metrics": {"production": {"absent": "stale", "real_declarations_decided": 777777},
                              "fragment": {"accepted": 100, "inside_fragment": 5}},
                  "units": [{"id": {}}, {"id": "W1", "status": []}]}
        doc = Document(render_slides(report, [{"kind": {}, "unit": "Q4"}], revision="latest"))
        text = " ".join(doc.text)
        for claim in ("unearned", "999,999", "777,777", "100 / 5", "Two independent kernels rechecked"):
            self.assertNotIn(claim, text)
        self.assertIn("Unverified", text)
        self.assertIn("no observation", text)
        self.assertEqual([a["href"] for a in doc.all("a")], ["#answer"])

    def test_unsafe_inputs_stay_text(self):
        payload = '</script><img src="x" onerror="fail()">'
        events = [{"date": "2026-11-15", "unit": "C3", "kind": "measurement",
                   "summary": payload, "source": "https://outside.example/escape"}]
        plan = {"state": "preview", "goal": "E1", "project": "Clean", "deferred": [payload],
                "measurements": [{"metric": payload, "value": "0", "unit": "records", "state": "retained"}],
                "capabilities": {"native_table": False, "native_measure": True, "native_metric_ids": []}}
        doc = Document(render_slides({"scoreboard_warning": payload}, events, plan, revision=SOURCE))
        self.assertEqual(len(doc.all("script")), 1)
        self.assertEqual(doc.all("img"), [])
        self.assertIn(payload, " ".join(doc.text))
        self.assertIn("preview", doc.text)
        self.assertIn("unavailable in the probe", " ".join(doc.text))
        self.assertTrue(all("outside.example" not in a["href"] for a in doc.all("a")))


if __name__ == "__main__":
    unittest.main()
