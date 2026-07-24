# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0

"""Tests for cleanVerifier."""

import pytest
from unittest.mock import Mock, patch

from clean_fate import cleanVerifier
from clean_fate.structs import cleanVerifyResult


class TestFateCodeParsing:
    """Test FATE Lean file format parsing."""

    def test_simple_theorem(self):
        """Parse simple theorem with no args."""
        code = """
theorem simple : 1 + 1 = 2 := by rfl
"""
        verifier = cleanVerifier.__new__(cleanVerifier)
        goal, proof = verifier._parse_fate_code(code)
        assert "1 + 1 = 2" in goal
        assert proof == "rfl"

    def test_theorem_with_args(self):
        """Parse theorem with arguments."""
        code = """
theorem foo (n : Nat) : n + 0 = n := by
  rfl
"""
        verifier = cleanVerifier.__new__(cleanVerifier)
        goal, proof = verifier._parse_fate_code(code)
        assert "n + 0 = n" in goal
        assert "rfl" in proof

    def test_theorem_with_complex_args(self):
        """Parse theorem with multiple complex arguments."""
        code = """
theorem complex [Ring R] (x y : R) : x + y = y + x := by
  ring
"""
        verifier = cleanVerifier.__new__(cleanVerifier)
        goal, proof = verifier._parse_fate_code(code)
        assert "x + y = y + x" in goal
        assert "ring" in proof

    def test_lemma_keyword(self):
        """Parse lemma instead of theorem."""
        code = """
lemma my_lemma : True := by trivial
"""
        verifier = cleanVerifier.__new__(cleanVerifier)
        goal, proof = verifier._parse_fate_code(code)
        assert "True" in goal
        assert "trivial" in proof

    def test_fate_format_with_imports(self):
        """Parse full FATE file with imports."""
        code = """
import Mathlib.Algebra.Ring.Basic

open scoped Polynomial

theorem fate_001
  (n : Nat)
  (hn : n > 0) :
  n + 1 > 1 := by
  sorry
"""
        verifier = cleanVerifier.__new__(cleanVerifier)
        goal, proof = verifier._parse_fate_code(code)
        assert "n + 1 > 1" in goal
        assert "sorry" in proof

    def test_multiline_proof(self):
        """Parse theorem with multiline proof."""
        code = """
theorem multi : 1 + 1 = 2 := by
  have h := rfl
  exact h
"""
        verifier = cleanVerifier.__new__(cleanVerifier)
        goal, proof = verifier._parse_fate_code(code)
        assert "1 + 1 = 2" in goal
        assert "have h := rfl" in proof
        assert "exact h" in proof

    def test_nested_parentheses_in_args(self):
        """Parse theorem with nested parentheses in arguments (#789)."""
        code = """
theorem foo (h : (A → B) → C) : D := by sorry
"""
        verifier = cleanVerifier.__new__(cleanVerifier)
        goal, proof = verifier._parse_fate_code(code)
        # Args should include the full nested type
        assert "(h : (A → B) → C)" in goal
        assert "D" in goal
        assert proof == "sorry"

    def test_deeply_nested_parentheses(self):
        """Parse theorem with deeply nested parentheses (#789)."""
        code = """
theorem bar (f : ((A → B) → C) → D) (g : E) : F := by
  exact sorry
"""
        verifier = cleanVerifier.__new__(cleanVerifier)
        goal, proof = verifier._parse_fate_code(code)
        assert "(f : ((A → B) → C) → D)" in goal
        assert "(g : E)" in goal
        assert "F" in goal
        assert "exact sorry" in proof

    def test_mixed_brackets_nested(self):
        """Parse theorem with mixed bracket types and nesting (#789)."""
        code = """
theorem mixed [Inst : Class (A → B)] (h : {x : T // P x} → Q) : R := by rfl
"""
        verifier = cleanVerifier.__new__(cleanVerifier)
        goal, proof = verifier._parse_fate_code(code)
        assert "[Inst : Class (A → B)]" in goal
        assert "(h : {x : T // P x} → Q)" in goal
        assert "R" in goal
        assert "rfl" in proof

    def test_by_word_boundary(self):
        """Ensure 'by' matching respects word boundaries (audit #789)."""
        # Type contains 'by' as substring (e.g., 'nearby')
        code = """
theorem nearby_thm (n : Nat) : nearby n := by exact sorry
"""
        verifier = cleanVerifier.__new__(cleanVerifier)
        goal, proof = verifier._parse_fate_code(code)
        # Should extract 'nearby n' as goal type, not stop at 'near'
        assert "nearby n" in goal
        assert "exact sorry" in proof


class TestVerifierResultConversion:
    """Test conversion of clean responses to FATE-Eval format."""

    def test_successful_verification(self):
        """Convert successful verification result."""
        verifier = cleanVerifier.__new__(cleanVerifier)
        verifier.client = Mock()

        result = verifier._convert_result(
            code="theorem t : True := by trivial",
            result={"verified": True, "time_ns": 1000},
            timeout=30,
            elapsed=0.001,
            extra_info={"test": True},
        )

        assert result.pass_ is True
        assert result.complete is True
        assert result.is_timeout is False
        assert result.lean_toolchain == "clean"
        assert result.extra_info == {"test": True}

    def test_failed_verification(self):
        """Convert failed verification result."""
        verifier = cleanVerifier.__new__(cleanVerifier)
        verifier.client = Mock()

        result = verifier._convert_result(
            code="theorem t : False := by sorry",
            result={
                "verified": False,
                "error": {"message": "type mismatch"},
                "time_ns": 500,
            },
            timeout=30,
            elapsed=0.001,
            extra_info={},
        )

        assert result.pass_ is False
        assert result.complete is False
        assert len(result.sorted_messages.errors) == 1
        assert "type mismatch" in result.sorted_messages.errors[0].data

    def test_sorry_detection(self):
        """Detect sorry in incomplete proof."""
        verifier = cleanVerifier.__new__(cleanVerifier)
        verifier.client = Mock()

        result = verifier._convert_result(
            code="theorem t : True := by sorry",
            result={"verified": False, "time_ns": 100},
            timeout=30,
            elapsed=0.001,
            extra_info={},
        )

        assert result.complete is False
        assert len(result.sorted_messages.sorries) == 1

    def test_timing_breakdown_extraction(self):
        """Extract timing breakdown from response."""
        verifier = cleanVerifier.__new__(cleanVerifier)
        verifier.client = Mock()

        result = verifier._convert_result(
            code="theorem t : True := by trivial",
            result={
                "verified": True,
                "time_ns": 450,
                "timing": {
                    "parse_ns": 50,
                    "elaborate_ns": 200,
                    "verify_ns": 150,
                    "total_ns": 400,
                },
            },
            timeout=30,
            elapsed=0.001,
            extra_info={},
        )

        assert result.timing is not None
        assert result.timing.parse_ns == 50
        assert result.timing.elaborate_ns == 200
        assert result.timing.verify_ns == 150
        assert result.timing.total_ns == 400


class TestVerifierAPI:
    """Test verifier API calls (mocked)."""

    def test_verify_single(self):
        """Test single verification call."""
        mock_response = Mock()
        mock_response.json.return_value = {
            "jsonrpc": "2.0",
            "result": {"verified": True, "time_ns": 1000},
            "id": 1,
        }
        mock_response.raise_for_status = Mock()

        with patch("httpx.Client") as mock_client:
            mock_client.return_value.post.return_value = mock_response

            verifier = cleanVerifier(endpoint="http://test:8000")
            result = verifier.verify("theorem t : True := by trivial", timeout=30)

            assert result.complete is True
            mock_client.return_value.post.assert_called_once()

    def test_batch_fallback(self):
        """Test batch verify falls back to sequential on 404."""
        mock_404 = Mock()
        mock_404.raise_for_status.side_effect = Exception("404")

        mock_single = Mock()
        mock_single.json.return_value = {
            "jsonrpc": "2.0",
            "result": {"verified": True, "time_ns": 1000},
            "id": 1,
        }
        mock_single.raise_for_status = Mock()

        with patch("httpx.Client") as mock_client:
            # First call (batch) fails, subsequent calls (single) succeed
            mock_client.return_value.post.side_effect = [mock_404, mock_single, mock_single]

            verifier = cleanVerifier(endpoint="http://test:8000")
            results = verifier.batch_verify(
                ["theorem t1 : True := by trivial", "theorem t2 : True := by trivial"],
                timeout=30,
            )

            assert len(results) == 2


class TestDeltaMeasurement:
    """Test δ measurement harness."""

    def test_delta_calculation(self):
        """Calculate δ from trial results."""
        from clean_fate import DeltaMeasurement
        from clean_fate.delta import StageResult, TrialResult

        verifier = Mock()
        dm = DeltaMeasurement(verifier)

        # Simulate 4 trials: 2 successes, 2 failures
        dm.results = [
            TrialResult("p1", 0, [], True, 100),
            TrialResult("p1", 1, [], True, 100),
            TrialResult("p1", 2, [], False, 100),
            TrialResult("p1", 3, [], False, 100),
        ]

        delta = dm.calculate_delta()
        assert delta == 0.5  # 2/4

    def test_expected_iterations(self):
        """Calculate E[n] ≤ 4/δ."""
        from clean_fate import DeltaMeasurement
        from clean_fate.delta import TrialResult

        verifier = Mock()
        dm = DeltaMeasurement(verifier)

        # δ = 0.25 → E[n] ≤ 16
        dm.results = [
            TrialResult("p1", i, [], i == 0, 100) for i in range(4)
        ]  # 1 success, 3 failures

        expected_n = dm.calculate_expected_iterations()
        assert expected_n == 16.0  # 4 / 0.25

    def test_stage_delta(self):
        """Calculate per-stage δ."""
        from clean_fate import DeltaMeasurement
        from clean_fate.delta import StageResult, TrialResult

        verifier = Mock()
        dm = DeltaMeasurement(verifier)

        # Parse always succeeds, elaborate 50%, verify 25%
        dm.results = [
            TrialResult(
                "p1",
                0,
                [
                    StageResult("parse", True, 10, None),
                    StageResult("elaborate", True, 20, None),
                    StageResult("verify", True, 30, None),
                ],
                True,
                60,
            ),
            TrialResult(
                "p1",
                1,
                [
                    StageResult("parse", True, 10, None),
                    StageResult("elaborate", True, 20, None),
                    StageResult("verify", False, 0, "failed"),
                ],
                False,
                30,
            ),
            TrialResult(
                "p1",
                2,
                [
                    StageResult("parse", True, 10, None),
                    StageResult("elaborate", False, 0, "type error"),
                    StageResult("verify", False, 0, None),
                ],
                False,
                10,
            ),
            TrialResult(
                "p1",
                3,
                [
                    StageResult("parse", True, 10, None),
                    StageResult("elaborate", False, 0, "type error"),
                    StageResult("verify", False, 0, None),
                ],
                False,
                10,
            ),
        ]

        assert dm.calculate_delta("parse") == 1.0  # 4/4
        assert dm.calculate_delta("elaborate") == 0.5  # 2/4
        assert dm.calculate_delta("verify") == 0.25  # 1/4

    def test_report_generation(self):
        """Generate complete measurement report."""
        from clean_fate import DeltaMeasurement
        from clean_fate.delta import StageResult, TrialResult

        verifier = Mock()
        dm = DeltaMeasurement(verifier)

        dm.results = [
            TrialResult(
                "problem_1",
                0,
                [StageResult("parse", True, 10, None)],
                True,
                100,
            ),
            TrialResult(
                "problem_1",
                1,
                [StageResult("parse", True, 10, None)],
                False,
                200,
            ),
        ]

        report = dm.report()

        assert report["total_trials"] == 2
        assert report["overall_delta"] == 0.5
        assert report["expected_iterations_4_over_delta"] == 8.0
        assert "stage_deltas" in report
        assert "timing_stats" in report
        assert "per_benchmark" in report
        assert "problem_1" in report["per_benchmark"]
