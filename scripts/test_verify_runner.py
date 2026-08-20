#!/usr/bin/env python3
"""Tests for the honesty-critical logic in scripts/verify_runner.py.

The whole value of `data/suite_state/` is that a row cannot claim more than was
measured. Every test here pins one way that could silently break: a stored
GREEN outliving its inputs, a killed run reading as a pass, an externally
reported result being promoted without evidence.

Run: python3 scripts/test_verify_runner.py
"""

from __future__ import annotations

import os
import sys
import tempfile
import subprocess
import threading
import unittest
from unittest import mock
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

# Redirect both writable locations BEFORE importing the module: it resolves
# them once at import. Without this, an end-to-end test would deposit synthetic
# records into the real data/suite_state/, where nothing downstream could tell
# them from measured ones.
_SANDBOX = tempfile.mkdtemp(prefix="verify_runner_test_")
os.environ["VERIFY_RUNNER_STATE_DIR"] = os.path.join(_SANDBOX, "state")
os.environ["VERIFY_RUNNER_TARGET_DIR"] = os.path.join(_SANDBOX, "target")

import verify_runner as vr  # noqa: E402

ENTRY = {"id": "pkg::test::t", "package": "pkg", "kind": "test", "argv": ["cargo", "test"]}
DIGEST = "sha256:aaaa"
OTHER = "sha256:bbbb"


def record(**overrides):
    base = {
        "target": "pkg::test::t",
        "status": vr.STATUS_GREEN,
        "input_digest": DIGEST,
        "source": "measured",
        "commit": "0123456789abcdef",
        "final_line": "test result: ok. 3 passed; 0 failed",
    }
    base.update(overrides)
    return base


class TestDeriveBucket(unittest.TestCase):
    def test_derive_no_record_returns_unknown(self):
        row = vr.derive(ENTRY, None, DIGEST)
        self.assertEqual(row["bucket"], vr.BUCKET_UNKNOWN)
        self.assertIn("never run", row["reason"])

    def test_derive_green_at_matching_digest_returns_green(self):
        row = vr.derive(ENTRY, record(), DIGEST)
        self.assertEqual(row["bucket"], vr.BUCKET_GREEN)

    def test_derive_green_at_moved_digest_returns_unknown(self):
        row = vr.derive(ENTRY, record(), OTHER)
        self.assertEqual(row["bucket"], vr.BUCKET_UNKNOWN)
        self.assertIn("stale", row["reason"])

    def test_derive_red_at_matching_digest_returns_red(self):
        row = vr.derive(ENTRY, record(status=vr.STATUS_RED), DIGEST)
        self.assertEqual(row["bucket"], vr.BUCKET_RED)

    def test_derive_stale_red_keeps_last_known_visible(self):
        """A red that goes stale must not vanish silently into UNKNOWN."""
        row = vr.derive(ENTRY, record(status=vr.STATUS_RED), OTHER)
        self.assertEqual(row["bucket"], vr.BUCKET_UNKNOWN)
        self.assertIn("RED@", row["last_known"])

    def test_derive_seeded_record_returns_unknown_not_green(self):
        row = vr.derive(ENTRY, record(source="seeded", seed_note="reported by lane"), DIGEST)
        self.assertEqual(row["bucket"], vr.BUCKET_UNKNOWN)
        self.assertIn("seeded", row["reason"])

    def test_derive_running_with_dead_pid_returns_unknown(self):
        row = vr.derive(ENTRY, record(status=vr.STATUS_RUNNING, pid=999999999), DIGEST)
        self.assertEqual(row["bucket"], vr.BUCKET_UNKNOWN)
        self.assertIn("abandoned", row["reason"])

    def test_derive_running_with_live_pid_returns_running(self):
        import os

        row = vr.derive(ENTRY, record(status=vr.STATUS_RUNNING, pid=os.getpid()), DIGEST)
        self.assertEqual(row["bucket"], vr.BUCKET_RUNNING)

    def test_derive_error_status_returns_unknown(self):
        """A runner timeout is an absence of information, not a pass or a fail."""
        row = vr.derive(ENTRY, record(status=vr.STATUS_ERROR, notes="KILLED after timeout"), DIGEST)
        self.assertEqual(row["bucket"], vr.BUCKET_UNKNOWN)

    def test_derive_unknown_status_string_returns_unknown(self):
        """Anything unrecognised must fall through to UNKNOWN, never to GREEN."""
        row = vr.derive(ENTRY, record(status="probably fine"), DIGEST)
        self.assertEqual(row["bucket"], vr.BUCKET_UNKNOWN)

    def test_derive_seeded_record_with_matching_digest_still_unknown(self):
        """A seeded record must not be launderable by any digest coincidence."""
        row = vr.derive(ENTRY, record(source="seeded", seed_note="n", status=vr.STATUS_GREEN), DIGEST)
        self.assertEqual(row["bucket"], vr.BUCKET_UNKNOWN)


class TestSummarizeOutput(unittest.TestCase):
    def test_summarize_picks_last_test_result_line_verbatim(self):
        text = "running 3 tests\ntest a ... ok\ntest result: ok. 3 passed; 0 failed; 0 ignored\n"
        final, counts = vr.summarize_output(text, 0)
        self.assertEqual(final, "test result: ok. 3 passed; 0 failed; 0 ignored")
        self.assertEqual(counts["passed"], 3)
        self.assertEqual(counts["failed"], 0)

    def test_summarize_sums_counts_across_multiple_result_lines(self):
        text = (
            "test result: ok. 3 passed; 0 failed; 0 ignored\n"
            "test result: FAILED. 1 passed; 2 failed; 0 ignored\n"
        )
        _final, counts = vr.summarize_output(text, 101)
        self.assertEqual(counts["passed"], 4)
        self.assertEqual(counts["failed"], 2)
        self.assertEqual(counts["result_lines"], 2)

    def test_summarize_empty_output_reports_absence_not_success(self):
        final, counts = vr.summarize_output("", 1)
        self.assertIn("no output", final)
        self.assertEqual(counts["passed"], 0)

    def test_summarize_falls_back_to_last_line_when_no_result_line(self):
        final, _counts = vr.summarize_output("error: could not compile `clean-verify`\n", 101)
        self.assertEqual(final, "error: could not compile `clean-verify`")


class TestInputDigest(unittest.TestCase):
    def test_digest_changes_when_argv_changes(self):
        """argv is part of the key: a green for one command is not a green for another."""
        a = dict(ENTRY, _dirs=[vr.REPO_ROOT / "scripts"])
        b = dict(ENTRY, _dirs=[vr.REPO_ROOT / "scripts"], argv=["cargo", "test", "--release"])
        self.assertNotEqual(vr.input_digest(a), vr.input_digest(b))

    def test_digest_is_stable_for_identical_inputs(self):
        a = dict(ENTRY, _dirs=[vr.REPO_ROOT / "scripts"])
        self.assertEqual(vr.input_digest(a), vr.input_digest(dict(a)))

    def test_digest_scope_excludes_the_state_directory(self):
        """Writing a record must never invalidate other records."""
        self.assertFalse(str(vr.STATE_DIR).startswith(str(vr.REPO_ROOT / "crates")))


class TestRunOneClassification(unittest.TestCase):
    """End-to-end through run_one with synthetic commands: no cargo, real records."""

    @staticmethod
    def _entry(name: str, argv: list[str]) -> dict:
        return {"id": name, "package": "synthetic", "kind": "test", "argv": argv,
                "_dirs": [vr.REPO_ROOT / "scripts"]}

    def test_run_one_zero_exit_records_green(self):
        entry = self._entry("synthetic::ok", ["/bin/sh", "-c", "echo 'test result: ok. 1 passed; 0 failed'"])
        rec = vr.run_one(entry, timeout=60)
        self.assertEqual(rec["status"], vr.STATUS_GREEN)
        self.assertEqual(rec["exit_code"], 0)
        self.assertEqual(rec["final_line"], "test result: ok. 1 passed; 0 failed")
        self.assertEqual(rec["counts"]["passed"], 1)

    def test_run_one_nonzero_exit_records_red_with_verbatim_line(self):
        entry = self._entry(
            "synthetic::fail",
            ["/bin/sh", "-c", "echo 'test result: FAILED. 0 passed; 2 failed; 0 ignored'; exit 101"],
        )
        rec = vr.run_one(entry, timeout=60)
        self.assertEqual(rec["status"], vr.STATUS_RED)
        self.assertEqual(rec["exit_code"], 101)
        self.assertEqual(rec["final_line"], "test result: FAILED. 0 passed; 2 failed; 0 ignored")
        self.assertEqual(rec["counts"]["failed"], 2)

    def test_run_one_timeout_records_error_not_green_or_red(self):
        entry = self._entry("synthetic::hang", ["/bin/sh", "-c", "sleep 30"])
        rec = vr.run_one(entry, timeout=2)
        self.assertEqual(rec["status"], vr.STATUS_ERROR)
        self.assertNotIn(rec["status"], (vr.STATUS_GREEN, vr.STATUS_RED))
        self.assertIn("NOT a pass", rec["notes"])

    def test_run_one_records_command_and_digest_provenance(self):
        entry = self._entry("synthetic::prov", ["/bin/sh", "-c", "true"])
        rec = vr.run_one(entry, timeout=60)
        self.assertEqual(rec["command"], "/bin/sh -c true")
        self.assertTrue(rec["input_digest"].startswith("sha256:"))
        self.assertEqual(rec["source"], "measured")
        self.assertIsNotNone(rec["commit"])
        self.assertIn("inputs_moved_during_run", rec)


class TestTimeoutPolicy(unittest.TestCase):
    """The per-target budget must be derived, explainable, and always finite.

    The failure this pins: on 2026-08-12 a flat 25s budget killed
    `clean-verify::test::whnf_lemma_wrapper_defs` at "running 2 tests" and
    recorded ERROR. The artifact was right to refuse to call that a pass or a
    fail; the budget was simply wrong for a target whose spec build alone runs
    into the thousands of seconds.
    """

    TEST_ENTRY = {"id": "pkg::test::t", "package": "pkg", "kind": "test", "argv": ["cargo"]}
    GATE_ENTRY = {"id": "gate::fmt", "package": "__workspace__", "kind": "gate", "argv": ["cargo"]}
    LIB_ENTRY = {"id": "pkg::lib", "package": "pkg", "kind": "lib", "argv": ["cargo"]}

    def test_never_run_target_gets_its_kind_floor(self):
        budget, basis = vr.timeout_for(self.TEST_ENTRY, None)
        self.assertEqual(budget, vr.TIMEOUT_FLOOR_BY_KIND["test"])
        self.assertIn("never completed here", basis)

    def test_spec_building_target_floor_is_realistic_not_seconds(self):
        """The concrete regression: a spec-building target must never get 25s."""
        budget, _ = vr.timeout_for(self.TEST_ENTRY, None)
        self.assertGreaterEqual(budget, 2500, "spec builds alone routinely take 2000-2500s")

    def test_kinds_get_different_floors(self):
        self.assertNotEqual(
            vr.timeout_for(self.GATE_ENTRY, None)[0], vr.timeout_for(self.LIB_ENTRY, None)[0]
        )

    def test_measured_duration_scales_the_budget(self):
        rec = record(status=vr.STATUS_GREEN, duration_s=5000.0, source="measured")
        budget, basis = vr.timeout_for(self.TEST_ENTRY, rec)
        self.assertEqual(budget, int(5000.0 * vr.TIMEOUT_HEADROOM) + 1)
        self.assertIn("5000.0s", basis)

    def test_short_measured_duration_does_not_shrink_below_the_floor(self):
        rec = record(status=vr.STATUS_GREEN, duration_s=3.0, source="measured")
        budget, _ = vr.timeout_for(self.TEST_ENTRY, rec)
        self.assertEqual(budget, vr.TIMEOUT_FLOOR_BY_KIND["test"])

    def test_a_killed_run_doubles_the_next_budget(self):
        """A kill is evidence the budget was too small -- it must escalate."""
        rec = record(status=vr.STATUS_ERROR, timed_out=True, timeout_s=20000, source="measured")
        budget, basis = vr.timeout_for(self.TEST_ENTRY, rec)
        self.assertEqual(budget, 40000)
        self.assertIn("KILLED", basis)

    def test_legacy_killed_record_without_the_flag_is_still_recognised(self):
        """Records written before `timed_out` existed must not read as completed."""
        rec = record(
            status=vr.STATUS_ERROR,
            timeout_s=25,
            duration_s=25.2,
            final_line="<timed out after 25s; last line: running 2 tests>",
            source="measured",
        )
        rec.pop("timed_out", None)
        self.assertTrue(vr._record_was_killed(rec))
        budget, _ = vr.timeout_for(self.TEST_ENTRY, rec)
        self.assertGreaterEqual(budget, vr.TIMEOUT_FLOOR_BY_KIND["test"])

    def test_a_killed_run_duration_is_never_used_to_size_the_next_one(self):
        """25.2s of a killed run is not evidence the target needs 100s."""
        rec = record(
            status=vr.STATUS_ERROR, timed_out=True, timeout_s=25, duration_s=25.2, source="measured"
        )
        budget, _ = vr.timeout_for(self.TEST_ENTRY, rec)
        self.assertGreater(budget, int(25.2 * vr.TIMEOUT_HEADROOM))

    def test_budget_is_always_finite_and_clamped(self):
        rec = record(status=vr.STATUS_GREEN, duration_s=10**9, source="measured")
        budget, _ = vr.timeout_for(self.TEST_ENTRY, rec)
        self.assertEqual(budget, vr.TIMEOUT_HARD_CEILING)

    def test_no_policy_path_yields_a_disabled_timeout(self):
        """There must be no input that turns the timeout off."""
        for rec in (
            None,
            record(status=vr.STATUS_GREEN, duration_s=0, source="measured"),
            record(status=vr.STATUS_ERROR, timed_out=True, timeout_s=10**9, source="measured"),
            record(status="weird", source="measured"),
        ):
            for entry in (self.TEST_ENTRY, self.GATE_ENTRY, self.LIB_ENTRY):
                budget, _ = vr.timeout_for(entry, rec)
                self.assertGreater(budget, 0)
                self.assertLessEqual(budget, vr.TIMEOUT_HARD_CEILING)

    def test_explicit_override_still_wins_and_says_so(self):
        budget, basis = vr.timeout_for(self.TEST_ENTRY, None, override=90)
        self.assertEqual(budget, 90)
        self.assertIn("override", basis)

    def test_seeded_record_does_not_size_a_budget(self):
        """A result this runner did not measure is not evidence of cost either."""
        rec = record(status=vr.STATUS_GREEN, duration_s=9.0, source="seeded", seed_note="lane")
        budget, basis = vr.timeout_for(self.TEST_ENTRY, rec)
        self.assertEqual(budget, vr.TIMEOUT_FLOOR_BY_KIND["test"])
        self.assertIn("never completed here", basis)

    def test_timeout_record_carries_its_basis_and_the_killed_flag(self):
        entry = {"id": "synthetic::hang2", "package": "synthetic", "kind": "test",
                 "argv": ["/bin/sh", "-c", "sleep 30"], "_dirs": [vr.REPO_ROOT / "scripts"]}
        rec = vr.run_one(entry, timeout=2, timeout_basis="unit test")
        self.assertIs(rec["timed_out"], True)
        self.assertEqual(rec["timeout_basis"], "unit test")
        self.assertIn("NOT a pass", rec["notes"])

    def test_completed_record_marks_itself_not_timed_out(self):
        entry = {"id": "synthetic::quick", "package": "synthetic", "kind": "test",
                 "argv": ["/bin/sh", "-c", "true"], "_dirs": [vr.REPO_ROOT / "scripts"]}
        rec = vr.run_one(entry, timeout=60, timeout_basis="unit test")
        self.assertIs(rec["timed_out"], False)


class TestGateExitCode(unittest.TestCase):
    def test_gate_all_green_exits_zero(self):
        self.assertEqual(vr.gate_exit_code({"GREEN": 5, "RED": 0, "UNKNOWN": 0, "RUNNING": 0}), 0)

    def test_gate_any_red_exits_one(self):
        self.assertEqual(vr.gate_exit_code({"GREEN": 4, "RED": 1, "UNKNOWN": 0, "RUNNING": 0}), 1)

    def test_gate_any_unknown_exits_two(self):
        """An absence of information must not pass a gate."""
        self.assertEqual(vr.gate_exit_code({"GREEN": 4, "RED": 0, "UNKNOWN": 1, "RUNNING": 0}), 2)

    def test_gate_running_counts_as_not_green(self):
        self.assertEqual(vr.gate_exit_code({"GREEN": 4, "RED": 0, "UNKNOWN": 0, "RUNNING": 1}), 2)

    def test_gate_red_outranks_unknown(self):
        self.assertEqual(vr.gate_exit_code({"GREEN": 0, "RED": 1, "UNKNOWN": 9, "RUNNING": 0}), 1)


SAMPLE_NAMES = [
    "sat_verify::cdcl::tests::a",
    "sat_verify::cdcl::tests::b",
    "sat_verify::frontier::tests::c",
    "spec::core_spec::par_reduction::par_reduction_tests::d",
    "spec::core_spec::par_reduction::par_reduction_tests::e",
    "spec::core_spec::impl_infer::tests::f",
    "spec::tests::g",
    "eval_ir::tests::h",
    # A test sitting DIRECTLY in a module that will be split: its key is that
    # module, which is a strict prefix of its siblings' keys.
    "spec::core_spec::loose_test",
    # A test at the crate root, with no module path at all.
    "bare_root_test",
]


class TestShardKey(unittest.TestCase):
    """The key is what makes the shards a partition, so it must be a function."""

    def test_key_is_total_every_name_gets_exactly_one(self):
        splits = {"spec", "spec::core_spec"}
        keys = [vr.shard_key(n, splits) for n in SAMPLE_NAMES]
        self.assertEqual(len(keys), len(SAMPLE_NAMES))
        self.assertTrue(all(isinstance(k, str) and k for k in keys))

    def test_key_is_deterministic(self):
        splits = {"spec", "spec::core_spec"}
        self.assertEqual(
            [vr.shard_key(n, splits) for n in SAMPLE_NAMES],
            [vr.shard_key(n, splits) for n in reversed(SAMPLE_NAMES)][::-1],
        )

    def test_key_never_consumes_the_test_function_name(self):
        """`a::b::t` under split `a::b` must key on `a::b`, not on the test `t`."""
        self.assertEqual(vr.shard_key("spec::core_spec::loose_test", {"spec", "spec::core_spec"}),
                         "spec::core_spec")

    def test_key_of_a_root_test_is_itself(self):
        self.assertEqual(vr.shard_key("bare_root_test", set()), "bare_root_test")

    def test_unsplit_names_key_on_the_top_level_module(self):
        self.assertEqual(vr.shard_key("sat_verify::cdcl::tests::a", set()), "sat_verify")

    def test_classes_of_the_key_partition_the_names(self):
        """Sum of class sizes == population, and no name in two classes."""
        splits = vr.derive_splits(SAMPLE_NAMES, max_tests=2)
        buckets = {}
        for name in SAMPLE_NAMES:
            buckets.setdefault(vr.shard_key(name, splits), []).append(name)
        self.assertEqual(sum(len(v) for v in buckets.values()), len(SAMPLE_NAMES))
        flat = [n for v in buckets.values() for n in v]
        self.assertEqual(sorted(flat), sorted(SAMPLE_NAMES))
        self.assertEqual(len(flat), len(set(flat)))


class TestDeriveSplits(unittest.TestCase):
    def test_splits_reach_a_fixpoint_under_the_cap(self):
        splits = vr.derive_splits(SAMPLE_NAMES, max_tests=1)
        counts = {}
        for name in SAMPLE_NAMES:
            key = vr.shard_key(name, splits)
            counts[key] = counts.get(key, 0) + 1
        for key, count in counts.items():
            if count > 1:
                # Only an indivisible key may exceed the cap: every member must
                # already be at the module depth of the key.
                members = [n for n in SAMPLE_NAMES if vr.shard_key(n, splits) == key]
                self.assertTrue(
                    all(len(m.split("::")) - 1 <= len(key.split("::")) for m in members),
                    f"{key} exceeded the cap but was still divisible",
                )

    def test_a_cap_above_the_population_splits_nothing(self):
        self.assertEqual(vr.derive_splits(SAMPLE_NAMES, max_tests=1000), set())


class TestShardFilters(unittest.TestCase):
    def test_a_prefix_key_skips_its_sibling_keys(self):
        keys = ["spec::core_spec", "spec::core_spec::impl_infer", "spec::core_spec::par_reduction"]
        filters, skips = vr.shard_filters("spec::core_spec", keys)
        self.assertEqual(filters, ["spec::core_spec::"])
        self.assertEqual(skips, ["spec::core_spec::impl_infer::", "spec::core_spec::par_reduction::"])

    def test_a_leaf_key_needs_no_skips(self):
        keys = ["spec::core_spec", "spec::core_spec::impl_infer"]
        _filters, skips = vr.shard_filters("spec::core_spec::impl_infer", keys)
        self.assertEqual(skips, [])


class TestShardRealisation(unittest.TestCase):
    """libtest matches substrings with no anchor, so a prefix is not always safe."""

    def test_an_unambiguous_prefix_is_used_as_is(self):
        declared = ["a::x::t1", "a::x::t2", "b::y::t3"]
        mode, filters, skips = vr.shard_realisation("a", ["a", "b"], {"a::x::t1", "a::x::t2"}, declared)
        self.assertEqual(mode, "prefix")
        self.assertEqual(filters, ["a::"])
        self.assertEqual(skips, [])

    def test_an_overreaching_prefix_falls_back_to_exact_names(self):
        """The measured case: `tests::` selects 3501 of 6900 tests, not 5."""
        declared = ["tests::t1", "tests::t2", "sat::cdcl::tests::t3"]
        mode, filters, _skips = vr.shard_realisation(
            "tests", ["tests", "sat"], {"tests::t1", "tests::t2"}, declared
        )
        self.assertEqual(mode, "exact")
        self.assertEqual(filters, ["tests::t1", "tests::t2"])

    def test_exact_mode_names_every_member_and_nothing_else(self):
        declared = ["proofs::tests::a", "nn::crown_proofs::tests::b"]
        intended = {"proofs::tests::a"}
        mode, filters, _ = vr.shard_realisation("proofs", ["proofs", "nn"], intended, declared)
        self.assertEqual(mode, "exact")
        self.assertEqual(set(filters), intended)

    def test_binary_args_pass_exact_flag_only_in_exact_mode(self):
        self.assertEqual(
            vr.shard_binary_args({"mode": "exact", "filters": ["a::t"], "skip": []}),
            ["--exact", "a::t"],
        )
        self.assertEqual(
            vr.shard_binary_args({"mode": "prefix", "filters": ["a::"], "skip": ["a::b::"]}),
            ["a::", "--skip", "a::b::"],
        )


class TestShardRecordPaths(unittest.TestCase):
    def test_shard_records_live_under_their_parent(self):
        path = vr.record_path("clean-verify::lib::shard::spec::core_spec")
        self.assertIn("shards", path.parts)
        self.assertIn(vr.safe_name("clean-verify::lib"), path.parts)

    def test_plain_records_stay_at_the_top_level(self):
        self.assertEqual(vr.record_path("clean-verify::lib").parent, vr.STATE_DIR)


def _shard_entry(key, count):
    parent = "pkg::lib"
    return {
        "id": vr.shard_target_id(parent, key),
        "package": "pkg",
        "kind": vr.KIND_SHARD,
        "argv": ["cargo"],
        "_parent": parent,
        "_shard": {"key": key, "id": vr.shard_target_id(parent, key), "test_count": count},
    }


class TestShardCountGuard(unittest.TestCase):
    """A shard whose filter matches nothing exits 0. That must not read GREEN."""

    def test_shard_running_its_planned_count_is_green(self):
        entry = _shard_entry("a", 5)
        rec = record(counts={"passed": 5, "failed": 0, "ignored": 0, "result_lines": 1})
        self.assertEqual(vr.derive(entry, rec, DIGEST)["bucket"], vr.BUCKET_GREEN)

    def test_shard_that_ran_nothing_is_unknown_not_green(self):
        entry = _shard_entry("a", 5)
        rec = record(counts={"passed": 0, "failed": 0, "ignored": 0, "result_lines": 1})
        row = vr.derive(entry, rec, DIGEST)
        self.assertEqual(row["bucket"], vr.BUCKET_UNKNOWN)
        self.assertIn("ran 0 tests", row["reason"])

    def test_shard_that_ran_too_few_is_unknown(self):
        entry = _shard_entry("a", 5)
        rec = record(counts={"passed": 4, "failed": 0, "ignored": 1, "result_lines": 1})
        self.assertEqual(vr.derive(entry, rec, DIGEST)["bucket"], vr.BUCKET_GREEN)
        rec = record(counts={"passed": 3, "failed": 0, "ignored": 0, "result_lines": 1})
        self.assertEqual(vr.derive(entry, rec, DIGEST)["bucket"], vr.BUCKET_UNKNOWN)


class TestRollup(unittest.TestCase):
    """The roll-up is GREEN only on a complete, proved, fresh set of shards."""

    PARENT = "pkg::lib"

    def _plan(self, shard_counts, verified=True, digest=DIGEST):
        return {
            "schema": vr.PLAN_SCHEMA,
            "parent": self.PARENT,
            "package": "pkg",
            "base_argv": ["cargo", "test"],
            "commit": "0" * 40,
            "generated_at": "2026-08-13T00:00:00Z",
            "input_digest": digest,
            "max_tests_per_shard": 100,
            "split_prefixes": [],
            "partition_proof": {"verified": verified, "declared_total": sum(shard_counts.values())},
            "shards": [
                {"key": k, "id": vr.shard_target_id(self.PARENT, k), "filters": [f"{k}::"],
                 "skip": [], "test_count": c}
                for k, c in sorted(shard_counts.items())
            ],
        }

    def setUp(self):
        # A roll-up derives any shard row the caller did not supply, which means
        # computing that shard's digest. These synthetic shards have no sources,
        # so the digest is pinned instead of measured.
        self._real_digest = vr.input_digest
        vr.input_digest = lambda entry, fresh=False: DIGEST

    def tearDown(self):
        vr.input_digest = self._real_digest

    def _entry(self, plan):
        return {"id": self.PARENT, "package": "pkg", "kind": vr.KIND_ROLLUP,
                "argv": ["cargo"], "_plan": plan, "_dirs": [vr.REPO_ROOT / "scripts"]}

    @staticmethod
    def _rows(plan, buckets):
        return [{"target": s["id"], "bucket": b, "kind": vr.KIND_SHARD}
                for s, b in zip(plan["shards"], buckets)]

    def _write_shard_records(self, plan, ran):
        for shard, count in zip(plan["shards"], ran):
            vr.write_record({
                "target": shard["id"], "status": vr.STATUS_GREEN, "source": "measured",
                "input_digest": DIGEST,
                "counts": {"passed": count, "failed": 0, "ignored": 0, "result_lines": 1},
            })

    def test_no_plan_is_unknown(self):
        entry = {"id": "pkg::unplanned", "package": "pkg", "kind": vr.KIND_ROLLUP, "argv": ["c"]}
        row = vr.derive(entry, None, DIGEST, [])
        self.assertEqual(row["bucket"], vr.BUCKET_UNKNOWN)
        self.assertIn("no shard plan", row["reason"])

    def test_unproved_partition_is_unknown_even_if_every_shard_is_green(self):
        plan = self._plan({"a": 2, "b": 3}, verified=False)
        self._write_shard_records(plan, [2, 3])
        row = vr.derive(self._entry(plan), None, DIGEST,
                        self._rows(plan, [vr.BUCKET_GREEN, vr.BUCKET_GREEN]))
        self.assertEqual(row["bucket"], vr.BUCKET_UNKNOWN)
        self.assertIn("partition proof", row["reason"])

    def test_stale_plan_is_unknown(self):
        plan = self._plan({"a": 2}, digest=OTHER)
        row = vr.derive(self._entry(plan), None, DIGEST, self._rows(plan, [vr.BUCKET_GREEN]))
        self.assertEqual(row["bucket"], vr.BUCKET_UNKNOWN)
        self.assertIn("stale", row["reason"])

    def test_one_unknown_shard_makes_the_parent_unknown_never_green(self):
        plan = self._plan({"a": 2, "b": 3})
        self._write_shard_records(plan, [2, 3])
        row = vr.derive(self._entry(plan), None, DIGEST,
                        self._rows(plan, [vr.BUCKET_GREEN, vr.BUCKET_UNKNOWN]))
        self.assertEqual(row["bucket"], vr.BUCKET_UNKNOWN)

    def test_one_running_shard_makes_the_parent_unknown(self):
        plan = self._plan({"a": 2, "b": 3})
        self._write_shard_records(plan, [2, 3])
        row = vr.derive(self._entry(plan), None, DIGEST,
                        self._rows(plan, [vr.BUCKET_GREEN, vr.BUCKET_RUNNING]))
        self.assertEqual(row["bucket"], vr.BUCKET_UNKNOWN)

    def test_one_red_shard_makes_the_parent_red(self):
        plan = self._plan({"a": 2, "b": 3})
        self._write_shard_records(plan, [2, 3])
        row = vr.derive(self._entry(plan), None, DIGEST,
                        self._rows(plan, [vr.BUCKET_GREEN, vr.BUCKET_RED]))
        self.assertEqual(row["bucket"], vr.BUCKET_RED)

    def test_an_unenumerated_shard_is_derived_from_the_plan_not_assumed(self):
        """`--only <parent>` enumerates no shards; the plan still decides."""
        plan = self._plan({"a": 2, "b": 3})
        self._write_shard_records(plan, [2, 3])
        row = vr.derive(self._entry(plan), None, DIGEST, [])
        self.assertEqual(row["bucket"], vr.BUCKET_GREEN)

    def test_a_shard_with_no_record_at_all_makes_the_parent_unknown(self):
        """An incomplete measurement must never roll up to GREEN."""
        plan = self._plan({"a": 2, "b": 3})
        # Only the first shard has ever run.
        vr.write_record({
            "target": plan["shards"][0]["id"], "status": vr.STATUS_GREEN, "source": "measured",
            "input_digest": DIGEST,
            "counts": {"passed": 2, "failed": 0, "ignored": 0, "result_lines": 1},
        })
        path = vr.record_path(plan["shards"][1]["id"])
        if path.exists():
            path.unlink()
        row = vr.derive(self._entry(plan), None, DIGEST, [])
        self.assertEqual(row["bucket"], vr.BUCKET_UNKNOWN)
        self.assertIn("1 UNKNOWN", row["reason"])

    def test_all_green_and_counts_close_is_green(self):
        plan = self._plan({"a": 2, "b": 3})
        self._write_shard_records(plan, [2, 3])
        row = vr.derive(self._entry(plan), None, DIGEST,
                        self._rows(plan, [vr.BUCKET_GREEN, vr.BUCKET_GREEN]))
        self.assertEqual(row["bucket"], vr.BUCKET_GREEN)
        self.assertIn("5 tests ran", row["reason"])

    def test_all_green_but_fewer_tests_ran_than_declared_is_unknown(self):
        """The run-time half of the partition proof: the pieces must re-sum."""
        plan = self._plan({"a": 2, "b": 3})
        self._write_shard_records(plan, [2, 2])
        row = vr.derive(self._entry(plan), None, DIGEST,
                        self._rows(plan, [vr.BUCKET_GREEN, vr.BUCKET_GREEN]))
        self.assertEqual(row["bucket"], vr.BUCKET_UNKNOWN)
        self.assertIn("does not close", row["reason"])


class TestPartitionVerification(unittest.TestCase):
    """`verify_partition` must fail loudly on drops, duplicates and strays."""

    @staticmethod
    def _fake_lister(mapping):
        def lister(_binary, args=None):
            return sorted(mapping[tuple(args or [])])
        return lister

    def _run(self, shards, declared, mapping):
        original = vr.list_tests
        vr.list_tests = self._fake_lister(mapping)
        try:
            return vr.verify_partition(Path("fake"), shards, declared)
        finally:
            vr.list_tests = original

    def test_clean_partition_verifies(self):
        shards = [
            {"id": "s::a", "filters": ["a::"], "skip": [], "test_count": 2, "_intended": ["a::x", "a::y"]},
            {"id": "s::b", "filters": ["b::"], "skip": [], "test_count": 1, "_intended": ["b::z"]},
        ]
        proof = self._run(shards, ["a::x", "a::y", "b::z"],
                          {("a::",): ["a::x", "a::y"], ("b::",): ["b::z"]})
        self.assertTrue(proof["verified"])
        self.assertEqual(proof["sum_of_shard_counts"], 3)
        self.assertEqual(proof["union_size"], 3)

    def test_a_dropped_test_fails_the_proof(self):
        shards = [
            {"id": "s::a", "filters": ["a::"], "skip": [], "test_count": 2, "_intended": ["a::x", "a::y"]},
        ]
        proof = self._run(shards, ["a::x", "a::y", "b::z"], {("a::",): ["a::x", "a::y"]})
        self.assertFalse(proof["verified"])
        self.assertEqual(proof["dropped_count"], 1)

    def test_a_double_counted_test_fails_the_proof(self):
        shards = [
            {"id": "s::a", "filters": ["a::"], "skip": [], "test_count": 1, "_intended": ["a::x"]},
            {"id": "s::b", "filters": ["x"], "skip": [], "test_count": 1, "_intended": ["a::x"]},
        ]
        proof = self._run(shards, ["a::x"], {("a::",): ["a::x"], ("x",): ["a::x"]})
        self.assertFalse(proof["verified"])
        self.assertEqual(proof["duplicated_count"], 1)

    def test_substring_overreach_is_caught_as_a_shard_mismatch(self):
        """The concrete hazard: `eval_ir::` also matches `spec::eval_ir::`."""
        declared = ["eval_ir::tests::a", "spec::eval_ir::tests::b"]
        shards = [
            {"id": "s::eval_ir", "filters": ["eval_ir::"], "skip": [], "test_count": 1,
             "_intended": ["eval_ir::tests::a"]},
            {"id": "s::spec", "filters": ["spec::"], "skip": [], "test_count": 1,
             "_intended": ["spec::eval_ir::tests::b"]},
        ]
        proof = self._run(shards, declared,
                          {("eval_ir::",): declared, ("spec::",): ["spec::eval_ir::tests::b"]})
        self.assertFalse(proof["verified"])
        self.assertGreaterEqual(proof["duplicated_count"], 1)
        self.assertGreaterEqual(proof["mismatched_shard_count"], 1)


class TestSpecPayingScan(unittest.TestCase):
    """The cost hint. Wrong answers cost time; they can never cost correctness."""

    def _src(self, files):
        tmp = tempfile.mkdtemp()
        root = Path(tmp) / "src"
        for rel, text in files.items():
            path = root / rel
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
        return root

    def test_a_directory_module_reports_its_top_level_name(self):
        root = self._src({
            "spec/core_spec/par.rs": "fn t() { let s = build_spec_with_stack(); }",
            "nn_verify/crown.rs": "fn t() { assert!(true); }",
        })
        roots, evidence = vr.spec_paying_roots(root)
        self.assertEqual(roots, {"spec"})
        self.assertEqual(evidence, ["spec/core_spec/par.rs"])

    def test_lib_rs_maps_to_the_crate_root_tests_key(self):
        root = self._src({"lib.rs": "mod tests { fn t() { build_spec_with_stack(); } }"})
        roots, _ = vr.spec_paying_roots(root)
        self.assertEqual(roots, {"tests"})

    def test_a_top_level_file_module_drops_its_rs_suffix(self):
        root = self._src({"eval_ir.rs": "fn t() { build_eval_ir_spec_with_stack(); }"})
        roots, _ = vr.spec_paying_roots(root)
        self.assertEqual(roots, {"eval_ir"})

    def test_a_missing_source_tree_is_not_an_error(self):
        self.assertEqual(vr.spec_paying_roots(Path("/no/such/dir")), (set(), []))


class TestPackGrouping(unittest.TestCase):
    def test_a_spec_paying_root_always_lands_in_the_shared_bin(self):
        self.assertEqual(vr.pack_group_of("spec::core_spec", {"spec": 3}, {"spec"}, 100), "spec_paying")

    def test_a_big_non_spec_root_gets_its_own_group(self):
        self.assertEqual(vr.pack_group_of("sat_verify::cdcl", {"sat_verify": 2764}, set(), 100),
                         "sat_verify")

    def test_a_small_non_spec_root_is_swept_into_misc(self):
        self.assertEqual(vr.pack_group_of("ffi", {"ffi": 9}, set(), 100), "misc")


class TestPackBins(unittest.TestCase):
    def _buckets(self, sizes):
        return {key: [f"{key}::t{i}" for i in range(n)] for key, n in sizes.items()}

    def test_every_key_lands_in_exactly_one_bin(self):
        buckets = self._buckets({"a": 400, "b": 400, "c": 400, "d": 5})
        groups = {"a": "g", "b": "g", "c": "g", "d": "misc"}
        bins = vr.pack_bins(buckets, groups, 900)
        placed = [key for item in bins for key in item["keys"]]
        self.assertEqual(sorted(placed), sorted(buckets))
        self.assertEqual(len(placed), len(set(placed)))

    def test_a_bin_never_mixes_groups(self):
        buckets = self._buckets({"a": 10, "b": 10})
        bins = vr.pack_bins(buckets, {"a": "one", "b": "two"}, 1000)
        self.assertEqual(len(bins), 2)

    def test_the_cap_is_respected_except_for_an_indivisible_key(self):
        buckets = self._buckets({"a": 600, "b": 600, "huge": 5000})
        groups = dict.fromkeys(buckets, "g")
        bins = vr.pack_bins(buckets, groups, 1000)
        sizes = [sum(len(buckets[k]) for k in item["keys"]) for item in bins]
        self.assertIn(5000, sizes)  # its own bin, over the cap, undivided
        self.assertTrue(all(size <= 1000 for size in sizes if size != 5000))

    def test_a_single_bin_group_keeps_the_bare_group_name(self):
        bins = vr.pack_bins(self._buckets({"a": 3}), {"a": "solo"}, 1000)
        self.assertEqual(bins[0]["key"], "solo")

    def test_a_split_group_numbers_its_bins(self):
        bins = vr.pack_bins(self._buckets({"a": 600, "b": 600}), {"a": "g", "b": "g"}, 700)
        self.assertEqual([item["key"] for item in bins], ["g_01", "g_02"])


class TestLibtestSelect(unittest.TestCase):
    """Our mirror of libtest's own filtering. A skip beats an include."""

    def test_substring_matching_is_unanchored(self):
        declared = ["a::t", "z::a::t"]
        self.assertEqual(vr.libtest_select(declared, ["a::"], []), {"a::t", "z::a::t"})

    def test_a_skip_removes_a_test_an_include_matched(self):
        declared = ["a::t", "a::b::t"]
        self.assertEqual(vr.libtest_select(declared, ["a::"], ["a::b::"]), {"a::t"})

    def test_exact_mode_matches_whole_names_only(self):
        declared = ["a::t", "a::t2"]
        self.assertEqual(vr.libtest_select(declared, ["a::t"], [], exact=True), {"a::t"})


class TestBinRealisation(unittest.TestCase):
    def test_packing_two_keys_uses_both_prefixes(self):
        declared = ["a::x::t", "b::y::t", "c::z::t"]
        mode, filters, skips = vr.bin_realisation(
            ["a", "b"], ["a", "b", "c"], {"a::x::t", "b::y::t"}, declared
        )
        self.assertEqual((mode, filters, skips), ("prefix", ["a::", "b::"], []))

    def test_a_fence_comes_down_when_the_sibling_joins_the_bin(self):
        """`a`'s skip of `a::b::` exists to fence off `a::b`. Packed together it must go."""
        declared = ["a::t", "a::b::t"]
        keys = ["a", "a::b"]
        mode, filters, skips = vr.bin_realisation(keys, keys, {"a::t", "a::b::t"}, declared)
        self.assertEqual(mode, "prefix")
        self.assertEqual(skips, [])
        self.assertEqual(vr.libtest_select(declared, filters, skips), {"a::t", "a::b::t"})

    def test_a_fence_stays_up_when_the_sibling_is_in_another_bin(self):
        declared = ["a::t", "a::b::t"]
        keys = ["a", "a::b"]
        mode, filters, skips = vr.bin_realisation(["a"], keys, {"a::t"}, declared)
        self.assertEqual((mode, filters, skips), ("prefix", ["a::"], ["a::b::"]))

    def test_an_overreaching_prefix_in_the_bin_forces_exact(self):
        declared = ["tests::t1", "spec::t2", "sat::cdcl::tests::t3"]
        intended = {"tests::t1", "spec::t2"}
        mode, filters, _ = vr.bin_realisation(
            ["tests", "spec"], ["tests", "spec", "sat"], intended, declared
        )
        self.assertEqual(mode, "exact")
        self.assertEqual(set(filters), intended)

    def test_a_bin_too_big_to_name_exactly_is_refused_not_truncated(self):
        long = "x" * 400
        declared = [f"tests::{long}{i}" for i in range(1000)] + ["sat::tests::other"]
        intended = set(declared[:-1])
        self.assertIsNone(
            vr.bin_realisation(["tests"], ["tests", "sat"], intended, declared)
        )


class TestPackedShardBudgets(unittest.TestCase):
    """The floors must be what the measured cost model says, not round numbers."""

    def test_the_spec_shard_floor_covers_four_flavour_builds_plus_marginal(self):
        derived = vr.SPEC_FLAVOURS * vr.ONE_FLAVOUR_BUILD_S + vr.DECLARED_TESTS * vr.MARGINAL_PER_TEST_S
        floor = vr.TIMEOUT_FLOOR_BY_KIND[vr.KIND_SHARD_SPEC]
        self.assertGreaterEqual(floor, derived)
        self.assertLess(floor, derived * 1.15, "a floor well above its derivation is slack, not a derivation")

    def test_the_cheap_shard_floor_covers_the_population_plus_one_build(self):
        derived = 4.0 * vr.CHEAP_POPULATION_S + vr.ONE_FLAVOUR_BUILD_S
        floor = vr.TIMEOUT_FLOOR_BY_KIND[vr.KIND_SHARD]
        self.assertGreaterEqual(floor, derived)
        self.assertLess(floor, derived * 1.15)

    def test_a_spec_shard_gets_the_spec_floor_and_a_cheap_one_does_not(self):
        spec, _ = vr.timeout_for({"kind": vr.KIND_SHARD_SPEC}, None)
        cheap, _ = vr.timeout_for({"kind": vr.KIND_SHARD}, None)
        self.assertEqual(spec, vr.TIMEOUT_FLOOR_BY_KIND[vr.KIND_SHARD_SPEC])
        self.assertEqual(cheap, vr.TIMEOUT_FLOOR_BY_KIND[vr.KIND_SHARD])
        self.assertGreater(spec, cheap)

    def test_shard_entries_carry_the_kind_the_plan_assigned(self):
        plan = {
            "parent": "pkg::lib", "package": "pkg",
            "base_argv": ["cargo", "test"],
            "shards": [
                {"id": "pkg::lib::shard::spec_paying", "key": "spec_paying",
                 "kind": vr.KIND_SHARD_SPEC, "mode": "prefix", "filters": ["spec::"],
                 "skip": [], "test_count": 3},
                {"id": "pkg::lib::shard::misc", "key": "misc", "mode": "prefix",
                 "filters": ["misc::"], "skip": [], "test_count": 1},
            ],
        }
        kinds = {e["id"]: e["kind"] for e in vr.shard_entries(plan)}
        self.assertEqual(kinds["pkg::lib::shard::spec_paying"], vr.KIND_SHARD_SPEC)
        # A plan written before packing has no `kind`; it must still be a shard.
        self.assertEqual(kinds["pkg::lib::shard::misc"], vr.KIND_SHARD)


class TestCommandRendering(unittest.TestCase):
    def test_a_short_command_is_stored_verbatim(self):
        argv = ["cargo", "test", "--lib"]
        self.assertEqual(vr.render_command(argv), "cargo test --lib")

    def test_a_huge_exact_argv_is_marked_not_silently_cut(self):
        argv = ["cargo", "test", "--"] + [f"name_{i:06d}" * 4 for i in range(2000)]
        rendered = vr.render_command(argv)
        self.assertIn("<<TRUNCATED:", rendered)
        self.assertIn("NOT runnable", rendered)
        self.assertLess(len(rendered), 2_500)


class TestInventory(unittest.TestCase):
    def test_gates_match_the_documented_prepush_commands(self):
        by_id = {g["id"]: g["argv"] for g in vr.WORKSPACE_GATES}
        self.assertIn("--workspace", by_id["gate::check"])
        self.assertIn("--all-targets", by_id["gate::check"])
        self.assertIn("--workspace", by_id["gate::clippy"])
        self.assertIn("--all-targets", by_id["gate::clippy"])
        self.assertIn("--all", by_id["gate::fmt"])

    def test_the_paragon_ratchet_is_a_gate_row(self):
        """It was not, and that is how `files_over_500` grew 1410 -> 1416.

        `scripts/paragon_ratchet.sh` is a leg of `scripts/local_gate.sh` in both
        modes, and `scripts/hooks/pre-push` runs `local_gate.sh --fast` -- but
        that hook only exists once `just install-hooks` points `core.hooksPath`
        at it, and on the box that produced the 2026-08-16 suite pass it did
        not. This runner is what ran; the ratchet has to be one of its rows or
        nothing routine measures it.
        """
        by_id = {g["id"]: g for g in vr.WORKSPACE_GATES}
        self.assertIn("gate::paragon", by_id)
        self.assertEqual(by_id["gate::paragon"]["argv"], ["scripts/paragon_ratchet.sh"])
        self.assertEqual(by_id["gate::paragon"]["kind"], "gate")

    def test_the_paragon_row_declares_the_inputs_no_crate_dir_covers(self):
        """The ratchet MEASURES crates/ but DECIDES against files outside it.

        A row digested over the crate dirs alone would stay fresh across an edit
        to the baseline it compares against, or to the heuristics that produce
        the numbers -- a stale green in the one place the whole artifact exists
        to prevent.
        """
        entry = next(g for g in vr.WORKSPACE_GATES if g["id"] == "gate::paragon")
        extra = list(entry["_extra_paths"])
        self.assertEqual(
            extra, ["data/paragon_ratchet.json", "scripts/paragon_ratchet.sh"]
        )
        for rel in extra:
            self.assertFalse(
                rel.startswith("crates/"),
                f"{rel} is under crates/ and needs no declaration; the point of "
                f"_extra_paths is inputs the workspace dirs do NOT reach",
            )
            self.assertTrue(
                (vr.REPO_ROOT / rel).exists(),
                f"{rel} is declared as a digest input but is not in the tree",
            )

    def test_a_declared_file_path_really_widens_the_digest(self):
        """`_dirs` holding a FILE must be hashed, not silently ignored.

        The widening rests entirely on `git ls-files -- <path>` accepting a file
        pathspec the same way it accepts a directory. If that ever stopped being
        true the scope would narrow in silence, which is exactly the failure the
        declaration is there to prevent -- so it is measured rather than
        assumed.
        """
        narrow = {
            "id": "probe",
            "package": "__workspace__",
            "kind": "gate",
            "argv": ["scripts/paragon_ratchet.sh"],
            "_dirs": [vr.REPO_ROOT / "crates" / "clean-verify"],
        }
        wide = dict(narrow)
        wide["_dirs"] = narrow["_dirs"] + [vr.REPO_ROOT / "data" / "paragon_ratchet.json"]
        self.assertNotEqual(
            vr.input_digest(narrow, fresh=True), vr.input_digest(wide, fresh=True)
        )




class MemoryAdmissionTests(unittest.TestCase):
    """The runner's concurrency unit is memory, and it learns its own weights.

    Regression cover for reports/kernel-panic-rca-2026-08-19.md: `--jobs N`
    used to mean N targets regardless of whether each was 50 MB or 8.8 GB.
    """

    def test_unmeasured_target_gets_the_conservative_default(self):
        with mock.patch.object(vr, "load_record", return_value=None):
            self.assertEqual(vr._gate_weight_gb("t"), vr.DEFAULT_TARGET_GB)

    def test_default_exceeds_the_measured_spec_binary(self):
        # 8.8 GB RSS was measured for a clean-verify spec binary. A default
        # below that would under-admit the very shape that caused the panic.
        self.assertGreater(vr.DEFAULT_TARGET_GB, 8.8)

    def test_a_measured_target_admits_at_its_own_cost_plus_headroom(self):
        with mock.patch.object(vr, "load_record", return_value={"peak_rss_gb": 8.8}):
            self.assertEqual(vr._gate_weight_gb("t"), 14)   # ceil(8.8 * 1.5)

    def test_a_tiny_target_never_admits_at_zero(self):
        with mock.patch.object(vr, "load_record", return_value={"peak_rss_gb": 0.05}):
            self.assertEqual(vr._gate_weight_gb("t"), vr.MIN_TARGET_GB)

    def test_a_junk_measurement_falls_back_to_the_default(self):
        for bad in ({"peak_rss_gb": 0}, {"peak_rss_gb": -3}, {"peak_rss_gb": "big"}, {}):
            with mock.patch.object(vr, "load_record", return_value=bad):
                self.assertEqual(vr._gate_weight_gb("t"), vr.DEFAULT_TARGET_GB)

    def test_a_missing_gate_never_blocks_the_suite(self):
        # The gate is a safety device, not a dependency: if it is absent the
        # suite must still run, just without admission control.
        with mock.patch.object(vr, "HEAVY_GATE", vr.REPO_ROOT / "no" / "such"):
            self.assertIsNone(vr._gate_acquire(4, "t"))
            vr._gate_release(None)          # must not raise

    def test_peak_rss_measures_a_real_process_group(self):
        proc = subprocess.Popen(
            [sys.executable, "-c", "x=bytearray(300*1024*1024); import time; time.sleep(2)"],
            start_new_session=True,
        )
        stop = threading.Event()
        out: list[float] = []
        t = threading.Thread(target=lambda: out.append(vr._peak_rss_gb(proc.pid, stop)))
        t.start()
        proc.wait()
        stop.set()
        t.join(timeout=10)
        self.assertGreater(out[0], 0.2)      # saw the ~300 MB allocation
        self.assertLess(out[0], 4.0)         # and did not invent a number



class WeightIsReadBeforeTheRecordIsOverwritten(unittest.TestCase):
    """The learning loop must not read its own blank.

    Live for one commit: the RUNNING template (peak_rss_gb=None) was written
    BEFORE the weight was computed, so `_gate_weight_gb` always read None and
    every target admitted at the default forever -- the measurement was taken
    and then ignored. Ordering is the whole fix, so it is pinned here.
    """

    def test_weight_is_computed_before_the_running_template(self):
        src = (vr.REPO_ROOT / "scripts" / "verify_runner.py").read_text()
        weight_at = src.index("gate_weight = _gate_weight_gb(")
        template_at = src.index('"status": STATUS_RUNNING')
        self.assertLess(
            weight_at, template_at,
            "the gate weight must be read before the RUNNING record overwrites "
            "peak_rss_gb, or the runner never learns",
        )

if __name__ == "__main__":
    unittest.main(verbosity=2)
