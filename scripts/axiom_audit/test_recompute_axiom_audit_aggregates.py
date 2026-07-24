# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""Tests for scripts.axiom_audit.aggregates (#3613, #3641).

Covers the behavioral requirements:

  * Unit: `compute_aggregates` sums `.conjectures[*].axioms` and
    `.conjectures[*].theorems` correctly, counts `constructive:true`
    theorems, and includes `.non_conjecture_axioms.per_prefix.*.count`
    in `total_all_axioms` (#3641).
  * Write / idempotence: `write_aggregates` updates the four aggregate
    fields on first run and is a no-op on the second run. Key order is
    preserved.
  * Fail-loud: `verify_aggregates` raises `AggregateMismatch` on null,
    missing, non-integer, or stale aggregates. The CLI returns exit 1
    in `--check` mode for each of those cases.
  * Fail-loud (verify_axiom_audit): the companion schema gate in
    `verify_axiom_audit.load_audit` rejects null aggregates (#3613 anchor)
    and rejects malformed `total_all_axioms` values (#3641 anchor).
  * Non-conjecture block (#3641): `compute_non_conjecture_axiom_total`
    sums `per_prefix.*.count` and rejects malformed shapes.
"""
from __future__ import annotations

import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

from scripts.axiom_audit.aggregates import (
    AGGREGATE_KEYS,
    AggregateMismatch,
    Aggregates,
    compute_aggregates,
    compute_non_conjecture_axiom_total,
    main,
    verify_aggregates,
    write_aggregates,
)
from scripts.axiom_audit.verify import load_audit as verify_load_audit


# ---------------------------------------------------------------------------
# Fixtures
# ---------------------------------------------------------------------------

# Minimal synthetic audit: three conjectures, mixed scalar-int and legacy
# list-shaped `axioms`/`theorems` fields, with one marked `constructive`.
# Expected aggregates:
#   total_domain_axioms  = 2 + 0 + 3 = 5
#   total_theorems       = 10 + 7 + 4 = 21
#   constructive_theorems = 7 (only C002 is constructive:true)
SYNTHETIC_AUDIT: dict = {
    "last_updated": "2026-04-20",
    "total_domain_axioms": None,  # explicit null — must be rewritten
    "total_theorems": 999,  # stale value — must be corrected
    "conjectures": {
        "C001": {
            "axioms": 2,
            "theorems": 10,
            "constructive": False,
            "proof_mechanism": "masquerade_demoted",
        },
        "C002": {
            "axioms": 0,
            "theorems": 7,
            "constructive": True,
            "proof_mechanism": "constructive",
        },
        "C003": {
            # legacy list-shaped counts
            "axioms": ["ax.foo", "ax.bar", "ax.baz"],
            "theorems": ["T.a", "T.b", "T.c", "T.d"],
            "constructive": False,
            "proof_mechanism": "sorry_inhabited",
        },
    },
    "proof_mechanism_legend": {
        "constructive": "stub legend",
        "sorry_inhabited": "stub",
        "masquerade_demoted": "stub",
    },
}


def _write_fixture(tmpdir: Path, name: str = "audit.json") -> Path:
    path = tmpdir / name
    path.write_text(
        json.dumps(SYNTHETIC_AUDIT, indent=2, ensure_ascii=True) + "\n",
        encoding="utf-8",
    )
    return path


# ---------------------------------------------------------------------------
# Tests
# ---------------------------------------------------------------------------


class ComputeAggregatesTests(unittest.TestCase):
    def test_sums_scalar_and_list_fields(self) -> None:
        agg = compute_aggregates(SYNTHETIC_AUDIT)
        self.assertEqual(agg.total_domain_axioms, 5)  # 2 + 0 + 3
        self.assertEqual(agg.total_theorems, 21)  # 10 + 7 + 4
        self.assertEqual(agg.constructive_theorems, 7)  # only C002

    def test_empty_conjectures_gives_zero_aggregates(self) -> None:
        audit = {"conjectures": {}}
        agg = compute_aggregates(audit)
        self.assertEqual(agg, Aggregates(0, 0, 0, 0))

    def test_total_all_axioms_matches_domain_when_no_block(self) -> None:
        """#3641: with no `non_conjecture_axioms` block, total_all_axioms == total_domain_axioms."""
        agg = compute_aggregates(SYNTHETIC_AUDIT)
        self.assertEqual(agg.total_all_axioms, agg.total_domain_axioms)
        self.assertEqual(agg.total_all_axioms, 5)

    def test_total_all_axioms_includes_non_conjecture_block(self) -> None:
        """#3641: when `non_conjecture_axioms.per_prefix.*.count` is set,
        those counts roll up into `total_all_axioms` but NOT into
        `total_domain_axioms` (the ratchet stays scoped to conjectures)."""
        audit = dict(SYNTHETIC_AUDIT)
        audit["non_conjecture_axioms"] = {
            "per_prefix": {
                "Nat.": {"count": 127, "source": "#3641"},
                "Int.": {"count": 90, "source": "#3641"},
                "Rat.": {"count": 18, "source": "#3572"},
            },
        }
        agg = compute_aggregates(audit)
        # Per-conjecture ratchet field unchanged.
        self.assertEqual(agg.total_domain_axioms, 5)
        # Non-conjecture axioms roll up only into total_all_axioms.
        self.assertEqual(agg.total_all_axioms, 5 + 127 + 90 + 18)

    def test_missing_conjectures_raises(self) -> None:
        with self.assertRaises(ValueError):
            compute_aggregates({"not_conjectures": {}})

    def test_rejects_bool_count(self) -> None:
        audit = {"conjectures": {"C001": {"axioms": True, "theorems": 0}}}
        with self.assertRaises(ValueError):
            compute_aggregates(audit)

    def test_rejects_negative_count(self) -> None:
        audit = {"conjectures": {"C001": {"axioms": -1, "theorems": 0}}}
        with self.assertRaises(ValueError):
            compute_aggregates(audit)


class WriteAggregatesTests(unittest.TestCase):
    def test_write_is_idempotent(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            path = _write_fixture(Path(tmp))
            agg1, changed1 = write_aggregates(path)
            self.assertTrue(changed1, "first run should mutate the file")
            agg2, changed2 = write_aggregates(path)
            self.assertFalse(changed2, "second run must be a no-op")
            self.assertEqual(agg1, agg2)
            # Stored values now match recomputed values.
            stored = json.loads(path.read_text(encoding="utf-8"))
            self.assertEqual(stored["total_domain_axioms"], 5)
            self.assertEqual(stored["total_theorems"], 21)
            self.assertEqual(stored["constructive_theorems"], 7)
            # #3641: total_all_axioms is materialized on the first write
            # and equals total_domain_axioms when no non_conjecture_axioms
            # block is present in the fixture.
            self.assertEqual(stored["total_all_axioms"], 5)

    def test_preserves_trailing_newline_and_indent(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            path = _write_fixture(Path(tmp))
            write_aggregates(path)
            text = path.read_text(encoding="utf-8")
            self.assertTrue(text.endswith("\n"), "must end with trailing \\n")
            # 2-space indent: the second line should start with two spaces.
            self.assertTrue(text.splitlines()[1].startswith("  "))

    def test_preserves_key_order_of_existing_aggregates(self) -> None:
        """If aggregate keys already exist, write should not reorder them."""
        with tempfile.TemporaryDirectory() as tmp:
            path = _write_fixture(Path(tmp))
            write_aggregates(path)
            stored = json.loads(path.read_text(encoding="utf-8"))
            keys = list(stored.keys())
            # The two originally-present aggregates retain their slot
            # (immediately after `last_updated`), and the previously-
            # missing constructive_theorems + total_all_axioms (#3641)
            # sit immediately after them in canonical AGGREGATE_KEYS order.
            i_last = keys.index("last_updated")
            self.assertEqual(keys[i_last + 1], "total_domain_axioms")
            self.assertEqual(keys[i_last + 2], "total_theorems")
            self.assertEqual(keys[i_last + 3], "constructive_theorems")
            self.assertEqual(keys[i_last + 4], "total_all_axioms")

    def test_does_not_mutate_conjectures(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            path = _write_fixture(Path(tmp))
            write_aggregates(path)
            stored = json.loads(path.read_text(encoding="utf-8"))
            # Per-conjecture data is verbatim (including legacy list form).
            self.assertEqual(stored["conjectures"]["C001"]["axioms"], 2)
            self.assertEqual(
                stored["conjectures"]["C003"]["axioms"],
                ["ax.foo", "ax.bar", "ax.baz"],
            )
            # Free-form top-level fields untouched.
            self.assertEqual(stored["last_updated"], "2026-04-20")


class VerifyAggregatesTests(unittest.TestCase):
    def test_passes_on_fresh_recompute(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            path = _write_fixture(Path(tmp))
            write_aggregates(path)
            agg = verify_aggregates(path)
            # #3641: 4-tuple now. total_all_axioms = total_domain_axioms
            # when fixture carries no non_conjecture_axioms block.
            self.assertEqual(agg, Aggregates(5, 21, 7, 5))

    def test_fails_on_null_aggregate(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            path = _write_fixture(Path(tmp))
            # Fixture has null total_domain_axioms out of the box.
            with self.assertRaises(AggregateMismatch) as cm:
                verify_aggregates(path)
            self.assertIn("null", str(cm.exception))
            self.assertIn("total_domain_axioms", str(cm.exception))

    def test_fails_on_stale_aggregate(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            path = _write_fixture(Path(tmp))
            write_aggregates(path)
            # Corrupt one stored value.
            stored = json.loads(path.read_text(encoding="utf-8"))
            stored["total_domain_axioms"] = 999
            path.write_text(json.dumps(stored, indent=2) + "\n", encoding="utf-8")
            with self.assertRaises(AggregateMismatch) as cm:
                verify_aggregates(path)
            self.assertIn("stored 999", str(cm.exception))
            self.assertIn("recomputed 5", str(cm.exception))

    def test_fails_on_missing_aggregate(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            path = _write_fixture(Path(tmp))
            stored = json.loads(path.read_text(encoding="utf-8"))
            stored.pop("total_domain_axioms", None)
            stored.pop("total_theorems", None)
            path.write_text(json.dumps(stored, indent=2) + "\n", encoding="utf-8")
            with self.assertRaises(AggregateMismatch) as cm:
                verify_aggregates(path)
            self.assertIn("missing", str(cm.exception))

    def test_fails_on_non_integer_aggregate(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            path = _write_fixture(Path(tmp))
            write_aggregates(path)
            stored = json.loads(path.read_text(encoding="utf-8"))
            stored["total_domain_axioms"] = "five"
            path.write_text(json.dumps(stored, indent=2) + "\n", encoding="utf-8")
            with self.assertRaises(AggregateMismatch) as cm:
                verify_aggregates(path)
            self.assertIn("non-integer", str(cm.exception))


class CLITests(unittest.TestCase):
    def test_write_then_check_via_main(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            path = _write_fixture(Path(tmp))
            rc = main(["--audit", str(path)])
            self.assertEqual(rc, 0)
            rc = main(["--audit", str(path), "--check"])
            self.assertEqual(rc, 0)

    def test_check_without_recompute_fails_fast(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            path = _write_fixture(Path(tmp))
            # Do not call --write first: the fixture has null aggregate.
            rc = main(["--audit", str(path), "--check"])
            self.assertEqual(rc, 1)

    def test_missing_file_returns_2(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "nope.json"
            rc = main(["--audit", str(path), "--check"])
            self.assertEqual(rc, 2)

    def test_subprocess_invocation_via_module(self) -> None:
        """End-to-end: invoke the module the same way the pre-commit hook does."""
        with tempfile.TemporaryDirectory() as tmp:
            path = _write_fixture(Path(tmp))
            # Write first, then check — should PASS.
            proc = subprocess.run(
                [
                    sys.executable,
                    "-m",
                    "scripts.axiom_audit.aggregates",
                    "--audit",
                    str(path),
                ],
                capture_output=True,
                text=True,
            )
            self.assertEqual(proc.returncode, 0, proc.stderr)
            proc = subprocess.run(
                [
                    sys.executable,
                    "-m",
                    "scripts.axiom_audit.aggregates",
                    "--audit",
                    str(path),
                    "--check",
                ],
                capture_output=True,
                text=True,
            )
            self.assertEqual(proc.returncode, 0, proc.stderr)


class VerifyAxiomAuditNullAggregateTests(unittest.TestCase):
    """The #3613 fail-loud anchor in `verify_axiom_audit.load_audit`.

    A null `total_domain_axioms` must raise ValueError even before the
    downstream kernel invocation runs — this is the gate that guarantees
    the ratchet invariant is non-vacuous.
    """

    def _make_audit(self, tmp: Path, **overrides) -> Path:
        # Minimal audit accepted by verify_axiom_audit schema (needs
        # proof_mechanism on every conjecture).
        audit = {
            "last_updated": "2026-04-20",
            "total_domain_axioms": 2,
            "total_theorems": 5,
            "conjectures": {
                "C001": {
                    "axioms": 2,
                    "theorems": 5,
                    "constructive": False,
                    "proof_mechanism": "masquerade_demoted",
                }
            },
        }
        audit.update(overrides)
        path = tmp / "audit.json"
        path.write_text(json.dumps(audit, indent=2) + "\n", encoding="utf-8")
        return path

    def test_null_aggregate_raises(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            path = self._make_audit(Path(tmp), total_domain_axioms=None)
            with self.assertRaises(ValueError) as cm:
                verify_load_audit(path)
            self.assertIn("null", str(cm.exception))
            self.assertIn("ratchet", str(cm.exception))

    def test_missing_aggregate_raises(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            # Build an audit without total_domain_axioms at all.
            audit = {
                "conjectures": {
                    "C001": {
                        "axioms": 0,
                        "theorems": 0,
                        "proof_mechanism": "masquerade_demoted",
                    }
                }
            }
            path = Path(tmp) / "audit.json"
            path.write_text(json.dumps(audit) + "\n", encoding="utf-8")
            with self.assertRaises(ValueError) as cm:
                verify_load_audit(path)
            self.assertIn("missing", str(cm.exception))

    def test_happy_path(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            path = self._make_audit(Path(tmp))
            # Must NOT raise.
            d = verify_load_audit(path)
            self.assertEqual(d["total_domain_axioms"], 2)


class NonConjectureAxiomsTests(unittest.TestCase):
    """#3641 Option B: `non_conjecture_axioms.per_prefix.*.count` rollup.

    Validates:
      * Absent block yields 0.
      * Empty block yields 0.
      * Well-formed per_prefix counts are summed.
      * Unknown keys inside entries (`source`, `example_names`) are ignored.
      * Malformed shapes (non-object block, non-object entry, non-int count,
        negative count, bool count) raise ValueError.
    """

    def test_absent_block_returns_zero(self) -> None:
        self.assertEqual(compute_non_conjecture_axiom_total({}), 0)

    def test_empty_block_returns_zero(self) -> None:
        self.assertEqual(
            compute_non_conjecture_axiom_total({"non_conjecture_axioms": {}}), 0
        )

    def test_empty_per_prefix_returns_zero(self) -> None:
        audit = {"non_conjecture_axioms": {"per_prefix": {}}}
        self.assertEqual(compute_non_conjecture_axiom_total(audit), 0)

    def test_sums_counts_across_prefixes(self) -> None:
        audit = {
            "non_conjecture_axioms": {
                "per_prefix": {
                    "Nat.": {"count": 127},
                    "Int.": {"count": 90},
                    "Rat.": {"count": 18},
                },
            }
        }
        self.assertEqual(compute_non_conjecture_axiom_total(audit), 235)

    def test_ignores_unknown_entry_keys(self) -> None:
        audit = {
            "non_conjecture_axioms": {
                "per_prefix": {
                    "Nat.": {
                        "count": 3,
                        "source": "#3641",
                        "example_names": ["Nat.le_refl", "Nat.zero_lt_succ"],
                    },
                },
            }
        }
        self.assertEqual(compute_non_conjecture_axiom_total(audit), 3)

    def test_rejects_non_object_block(self) -> None:
        with self.assertRaises(ValueError):
            compute_non_conjecture_axiom_total({"non_conjecture_axioms": 42})

    def test_rejects_non_object_per_prefix(self) -> None:
        with self.assertRaises(ValueError):
            compute_non_conjecture_axiom_total(
                {"non_conjecture_axioms": {"per_prefix": "not-an-object"}}
            )

    def test_rejects_non_object_entry(self) -> None:
        with self.assertRaises(ValueError):
            compute_non_conjecture_axiom_total(
                {"non_conjecture_axioms": {"per_prefix": {"Nat.": 7}}}
            )

    def test_rejects_non_int_count(self) -> None:
        with self.assertRaises(ValueError):
            compute_non_conjecture_axiom_total(
                {"non_conjecture_axioms": {"per_prefix": {"Nat.": {"count": "nine"}}}}
            )

    def test_rejects_bool_count(self) -> None:
        with self.assertRaises(ValueError):
            compute_non_conjecture_axiom_total(
                {"non_conjecture_axioms": {"per_prefix": {"Nat.": {"count": True}}}}
            )

    def test_rejects_negative_count(self) -> None:
        with self.assertRaises(ValueError):
            compute_non_conjecture_axiom_total(
                {"non_conjecture_axioms": {"per_prefix": {"Nat.": {"count": -1}}}}
            )

    def test_compute_aggregates_surfaces_block_errors(self) -> None:
        """A malformed block must propagate out of compute_aggregates."""
        audit = {
            "conjectures": {},
            "non_conjecture_axioms": {"per_prefix": {"Nat.": {"count": -1}}},
        }
        with self.assertRaises(ValueError):
            compute_aggregates(audit)


class VerifyAxiomAuditTotalAllAxiomsTests(unittest.TestCase):
    """The #3641 fail-loud anchor in `verify_axiom_audit.load_audit`.

    `total_all_axioms` is optional (pre-#3641 files omit it), but when
    present it must be a non-negative int and must be >= total_domain_axioms.
    """

    def _make_audit(self, tmp: Path, **overrides) -> Path:
        audit = {
            "last_updated": "2026-04-20",
            "total_domain_axioms": 2,
            "total_theorems": 5,
            "total_all_axioms": 10,
            "conjectures": {
                "C001": {
                    "axioms": 2,
                    "theorems": 5,
                    "constructive": False,
                    "proof_mechanism": "masquerade_demoted",
                }
            },
        }
        audit.update(overrides)
        path = tmp / "audit.json"
        path.write_text(json.dumps(audit, indent=2) + "\n", encoding="utf-8")
        return path

    def test_absent_total_all_axioms_allowed(self) -> None:
        """Pre-#3641 files without total_all_axioms must still load."""
        with tempfile.TemporaryDirectory() as tmp:
            # Build audit WITHOUT total_all_axioms at all.
            audit = {
                "last_updated": "2026-04-20",
                "total_domain_axioms": 2,
                "total_theorems": 5,
                "conjectures": {
                    "C001": {
                        "axioms": 2,
                        "theorems": 5,
                        "constructive": False,
                        "proof_mechanism": "masquerade_demoted",
                    }
                },
            }
            path = Path(tmp) / "audit.json"
            path.write_text(json.dumps(audit, indent=2) + "\n", encoding="utf-8")
            # Must NOT raise.
            d = verify_load_audit(path)
            self.assertNotIn("total_all_axioms", d)

    def test_valid_non_conjecture_block_without_total_all_axioms_loads(self) -> None:
        """A well-formed non-conjecture block is still allowed without the companion total."""
        with tempfile.TemporaryDirectory() as tmp:
            audit = {
                "last_updated": "2026-04-20",
                "total_domain_axioms": 2,
                "total_theorems": 5,
                "conjectures": {
                    "C001": {
                        "axioms": 2,
                        "theorems": 5,
                        "constructive": False,
                        "proof_mechanism": "masquerade_demoted",
                    }
                },
                "non_conjecture_axioms": {
                    "per_prefix": {
                        "Nat.": {"count": 3, "source": "#3641"},
                    }
                },
            }
            path = Path(tmp) / "audit.json"
            path.write_text(json.dumps(audit, indent=2) + "\n", encoding="utf-8")
            d = verify_load_audit(path)
            self.assertEqual(d["non_conjecture_axioms"]["per_prefix"]["Nat."]["count"], 3)

    def test_malformed_non_conjecture_block_raises_without_total_all_axioms(self) -> None:
        """Malformed non-conjecture counts must fail loud even if total_all_axioms is omitted."""
        with tempfile.TemporaryDirectory() as tmp:
            audit = {
                "last_updated": "2026-04-20",
                "total_domain_axioms": 2,
                "total_theorems": 5,
                "conjectures": {
                    "C001": {
                        "axioms": 2,
                        "theorems": 5,
                        "constructive": False,
                        "proof_mechanism": "masquerade_demoted",
                    }
                },
                "non_conjecture_axioms": {
                    "per_prefix": {
                        "Nat.": {"count": "three", "source": "#3641"},
                    }
                },
            }
            path = Path(tmp) / "audit.json"
            path.write_text(json.dumps(audit, indent=2) + "\n", encoding="utf-8")
            with self.assertRaises(ValueError) as cm:
                verify_load_audit(path)
            self.assertIn("non_conjecture_axioms.per_prefix.Nat.count", str(cm.exception))
            self.assertIn("non-integer", str(cm.exception))

    def test_null_total_all_axioms_raises(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            path = self._make_audit(Path(tmp), total_all_axioms=None)
            with self.assertRaises(ValueError) as cm:
                verify_load_audit(path)
            self.assertIn("total_all_axioms", str(cm.exception))
            self.assertIn("null", str(cm.exception))

    def test_non_integer_total_all_axioms_raises(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            path = self._make_audit(Path(tmp), total_all_axioms="ten")
            with self.assertRaises(ValueError) as cm:
                verify_load_audit(path)
            self.assertIn("total_all_axioms", str(cm.exception))
            self.assertIn("non-integer", str(cm.exception))

    def test_negative_total_all_axioms_raises(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            path = self._make_audit(Path(tmp), total_all_axioms=-1)
            with self.assertRaises(ValueError) as cm:
                verify_load_audit(path)
            self.assertIn("total_all_axioms", str(cm.exception))
            self.assertIn("negative", str(cm.exception))

    def test_total_all_axioms_less_than_domain_raises(self) -> None:
        """Non-conjecture delta must be non-negative (#3641)."""
        with tempfile.TemporaryDirectory() as tmp:
            # total_domain_axioms=2, total_all_axioms=1 would mean the
            # non-conjecture block contributed -1 — impossible by construction.
            path = self._make_audit(Path(tmp), total_all_axioms=1)
            with self.assertRaises(ValueError) as cm:
                verify_load_axiom_audit_helper(path)
            self.assertIn("total_all_axioms", str(cm.exception))
            self.assertIn("less than", str(cm.exception))

    def test_total_all_axioms_happy_path(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            # A positive delta is accepted when the non-conjecture breakdown
            # is present and sums to the delta (#3641 fail-loud rule).
            path = self._make_audit(
                Path(tmp),
                total_all_axioms=10,
                non_conjecture_axioms={
                    "per_prefix": {
                        "Nat.": {"count": 8},
                    }
                },
            )
            d = verify_load_audit(path)
            self.assertEqual(d["total_all_axioms"], 10)


# Alias for clarity in the `less_than_domain` test — uses the same gate.
verify_load_axiom_audit_helper = verify_load_audit


if __name__ == "__main__":
    unittest.main()
