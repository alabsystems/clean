# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0

"""
cleanVerifier: Drop-in replacement for FATE-Eval's Verifier class.

Uses clean-server JSON-RPC API instead of subprocess Lean calls.
Provides 100-1000x speedup for proof verification.

Usage:
    verifier = cleanVerifier(endpoint="http://localhost:8000")
    result = verifier.verify(code, timeout=30)
    results = verifier.batch_verify(codes, timeout=30, max_workers=8)
"""

import re
import time
from datetime import datetime, timezone
from typing import Optional

import httpx

from clean_fate.structs import (
    ExtractedTheorem,
    cleanVerifyResult,
    Message,
    SorryLocation,
    SortedMessages,
    TimingBreakdown,
    VerifyFileResult,
)


class cleanVerifier:
    """
    clean-backed verifier for FATE-Eval.

    Implements the same interface as FATE-Eval's Verifier class but uses
    clean-server's JSON-RPC API for verification.

    Args:
        endpoint: clean-server JSON-RPC endpoint (default: http://localhost:8000)
        lean_workspace: Ignored, for API compatibility with FATE-Eval
        lake_path: Ignored, for API compatibility with FATE-Eval
    """

    def __init__(
        self,
        endpoint: str = "http://localhost:8000",
        lean_workspace: Optional[str] = None,
        lake_path: Optional[str] = None,
    ):
        self.endpoint = endpoint
        # lean_workspace and lake_path ignored - kept for FATE-Eval API compat
        self.client = httpx.Client(timeout=600.0)  # 10 min max
        self._request_id = 0

    def verify(
        self,
        code: str,
        timeout: int = 300,
        extra_info: Optional[dict] = None,
    ) -> cleanVerifyResult:
        """
        Verify single Lean code sample via clean.

        Args:
            code: Complete Lean file content (FATE format)
            timeout: Verification timeout in seconds
            extra_info: Additional metadata to include in result

        Returns:
            cleanVerifyResult compatible with FATE-Eval's VerifyResult
        """
        extra_info = extra_info or {}

        # Extract goal and proof from FATE format
        goal, proof = self._parse_fate_code(code)

        start = time.time()

        self._request_id += 1
        request = {
            "jsonrpc": "2.0",
            "method": "verifyProof",  # Note: llm/ prefix pending #94
            "params": {
                "goal": goal,
                "proof": proof,
                "timeout_ms": timeout * 1000,
            },
            "id": self._request_id,
        }

        try:
            response = self.client.post(self.endpoint, json=request)
            response.raise_for_status()
            result = response.json().get("result", {})
        except Exception as e:
            return self._error_result(code, timeout, str(e), extra_info)

        elapsed = time.time() - start

        return self._convert_result(code, result, timeout, elapsed, extra_info)

    def batch_verify(
        self,
        codes: list[str],
        timeout: int = 300,
        max_workers: Optional[int] = None,
        extra_infos: Optional[list[dict]] = None,
    ) -> list[cleanVerifyResult]:
        """
        Batch verify via llm/verifyProofBatch.

        Falls back to sequential verification if batch endpoint unavailable.

        Args:
            codes: List of complete Lean files (FATE format)
            timeout: Verification timeout in seconds (total for batch)
            max_workers: Ignored - clean handles parallelism internally
            extra_infos: Additional metadata per code sample

        Returns:
            List of cleanVerifyResult in same order as codes
        """
        extra_infos = extra_infos or [{} for _ in codes]

        # Build batch request
        proofs = []
        for i, code in enumerate(codes):
            goal, proof = self._parse_fate_code(code)
            proofs.append({"id": f"p{i}", "goal": goal, "proof": proof})

        self._request_id += 1
        request = {
            "jsonrpc": "2.0",
            "method": "verifyProofBatch",  # Note: llm/ prefix pending #94
            "params": {
                "proofs": proofs,
                "timeout_ms": timeout * 1000,
            },
            "id": self._request_id,
        }

        start = time.time()

        try:
            response = self.client.post(self.endpoint, json=request)
            response.raise_for_status()
            batch_result = response.json().get("result", {})
        except httpx.HTTPStatusError as e:
            if e.response.status_code == 404:
                # Batch endpoint not available, fall back to sequential
                return self._sequential_verify(codes, timeout, extra_infos)
            raise
        except Exception:
            # Network error or other issue, fall back to sequential
            return self._sequential_verify(codes, timeout, extra_infos)

        elapsed = time.time() - start

        # Convert batch results
        results = []
        batch_items = batch_result.get("results", [])

        for i, (code, extra_info) in enumerate(zip(codes, extra_infos)):
            if i < len(batch_items):
                item_result = batch_items[i]
                # Use per-item time if available, else estimate from total
                item_time_ns = item_result.get("time_ns", 0)
                item_elapsed = item_time_ns / 1e9 if item_time_ns else elapsed / len(codes)
            else:
                item_result = {}
                item_elapsed = elapsed / len(codes)

            results.append(
                self._convert_result(code, item_result, timeout, item_elapsed, extra_info)
            )

        return results

    def verify_file(
        self,
        file_path: str,
        timeout: int = 300,
        extra_info: Optional[dict] = None,
    ) -> cleanVerifyResult:
        """
        Verify a Lean file by path using verify() endpoint.

        Args:
            file_path: Path to .lean file
            timeout: Verification timeout in seconds
            extra_info: Additional metadata

        Returns:
            cleanVerifyResult
        """
        with open(file_path) as f:
            code = f.read()
        return self.verify(code, timeout, extra_info or {"file": file_path})

    def verify_file_content(
        self,
        content: str,
        proof: Optional[str] = None,
        timeout: int = 300,
    ) -> VerifyFileResult:
        """
        Verify a complete Lean file using the verifyFile endpoint.

        This endpoint parses FATE-style files to extract theorem information
        and optionally verifies a replacement proof.

        Args:
            content: Complete Lean file content
            proof: Optional replacement proof (tactic script)
            timeout: Verification timeout in seconds

        Returns:
            VerifyFileResult with extracted theorem info and verification result
        """
        self._request_id += 1

        params: dict = {
            "content": content,
            "timeout_ms": timeout * 1000,
        }
        if proof is not None:
            params["proof"] = proof

        request = {
            "jsonrpc": "2.0",
            "method": "verifyFile",
            "params": params,
            "id": self._request_id,
        }

        try:
            response = self.client.post(self.endpoint, json=request)
            response.raise_for_status()
            result = response.json().get("result", {})
        except Exception as e:
            # Return error result
            return VerifyFileResult(
                verified=False,
                theorem=None,
                sorries=[],
                time_ns=0,
                timing=None,
                error={"message": str(e)},
            )

        # Parse result into structured types
        theorem = None
        if result.get("theorem"):
            t = result["theorem"]
            theorem = ExtractedTheorem(
                name=t.get("name", ""),
                goal=t.get("goal", ""),
                line=t.get("line", 0),
                original_proof=t.get("original_proof", t.get("originalProof", "")),
            )

        sorries = [
            SorryLocation(
                line=s.get("line", 0),
                col=s.get("col", 0),
                context=s.get("context"),
            )
            for s in result.get("sorries", [])
        ]

        timing = None
        if result.get("timing"):
            t = result["timing"]
            timing = TimingBreakdown(
                parse_ns=t.get("parse_ns", t.get("parseNs", 0)),
                elaborate_ns=t.get("elaborate_ns", t.get("elaborateNs", 0)),
                verify_ns=t.get("verify_ns", t.get("verifyNs", 0)),
                total_ns=t.get("total_ns", t.get("totalNs", 0)),
            )

        return VerifyFileResult(
            verified=result.get("verified", False),
            theorem=theorem,
            sorries=sorries,
            time_ns=result.get("time_ns", result.get("timeNs", 0)),
            timing=timing,
            error=result.get("error"),
        )

    def _parse_fate_code(self, code: str) -> tuple[str, str]:
        """
        Parse FATE Lean file format into goal + proof.

        FATE format example:
        ```lean
        import Mathlib...
        open Nat...

        theorem foo (h: P) : Q := by
          sorry
        ```

        We extract:
        - goal: The theorem's type (e.g., "Q" or full signature "P → Q")
        - proof: The tactic proof (e.g., "sorry")

        For clean's llm/verifyProof, we need the type to check against.

        Supports nested parentheses in args (fixed in #789).
        e.g., `(h : (A → B) → C)` parses correctly.
        """
        # Find theorem/lemma declaration
        decl_match = re.search(r"(?:theorem|lemma)\s+(\w+)", code)
        if not decl_match:
            return code, ""

        # Start after the theorem name
        pos = decl_match.end()

        # Skip whitespace
        while pos < len(code) and code[pos].isspace():
            pos += 1

        # Collect arguments with balanced brackets
        args_list = []
        while pos < len(code):
            if code[pos] == "(":
                arg, end = self._match_balanced(code, pos, "(", ")")
                if arg:
                    args_list.append(arg)
                    pos = end
                else:
                    break
            elif code[pos] == "[":
                arg, end = self._match_balanced(code, pos, "[", "]")
                if arg:
                    args_list.append(arg)
                    pos = end
                else:
                    break
            elif code[pos] == "{":
                arg, end = self._match_balanced(code, pos, "{", "}")
                if arg:
                    args_list.append(arg)
                    pos = end
                else:
                    break
            elif code[pos].isspace():
                pos += 1
            elif code[pos] == ":":
                break
            else:
                break

        # Now pos should be at the colon before the type
        if pos >= len(code) or code[pos] != ":":
            # Try simpler fallback pattern
            simple_pattern = r"(?:theorem|lemma)\s+\w+\s*:\s*(.*?)\s*:=\s*by\s*([\s\S]*)"
            match = re.search(simple_pattern, code, re.MULTILINE)
            if match:
                return match.group(1).strip(), match.group(2).strip()
            return code, ""

        # Skip the colon and whitespace
        pos += 1
        while pos < len(code) and code[pos].isspace():
            pos += 1

        # Find := by to get the type
        type_end = code.find(":=", pos)
        if type_end == -1:
            return code, ""

        goal_type = code[pos:type_end].strip()

        # Find 'by' keyword after ':=' (must be word boundary)
        by_match = re.search(r"\bby\b", code[type_end + 2:])
        if by_match is None:
            return code, ""
        by_pos = type_end + 2 + by_match.start()

        # Everything after 'by' is the proof
        proof = code[by_pos + 2:].strip()

        # Construct goal with args
        if args_list:
            args = " ".join(args_list)
            goal = f"{args} : {goal_type}"
        else:
            goal = goal_type

        return goal, proof

    def _match_balanced(
        self, text: str, start: int, open_char: str, _close_char: str
    ) -> tuple[Optional[str], int]:
        """
        Match a balanced bracket expression starting at position `start`.

        Args:
            text: The source text to parse
            start: Position where bracket starts
            open_char: The opening bracket character to match
            _close_char: Unused, kept for API clarity (uses bracket_pairs dict)

        Returns (matched_string, end_position) or (None, start) on failure.
        Handles nested brackets of all types: (), [], {}.

        Note: Does not handle brackets inside string literals.
        """
        if start >= len(text) or text[start] != open_char:
            return None, start

        pos = start
        bracket_pairs = {"(": ")", "[": "]", "{": "}"}
        close_chars = set(bracket_pairs.values())
        stack: list[str] = []

        while pos < len(text):
            char = text[pos]

            if char in bracket_pairs:
                stack.append(bracket_pairs[char])
            elif char in close_chars:
                if stack and stack[-1] == char:
                    stack.pop()
                    if not stack:  # depth == 0
                        return text[start : pos + 1], pos + 1
                else:
                    # Mismatched bracket
                    return None, start

            pos += 1

        # Unclosed bracket
        return None, start

    def _convert_result(
        self,
        code: str,
        result: dict,
        timeout: int,
        elapsed: float,
        extra_info: dict,
    ) -> cleanVerifyResult:
        """Convert clean JSON-RPC response to FATE-Eval format."""
        verified = result.get("verified", False)
        error = result.get("error", {})
        time_ns = result.get("time_ns", 0)
        timing_data = result.get("timing", {})

        # Build sorted_messages from clean error
        messages = SortedMessages()

        if error.get("message"):
            messages.errors.append(
                Message(
                    severity="error",
                    data=error.get("message", ""),
                    pos=None,
                    end_pos=None,
                    keep_full_range=False,
                    caption="",
                )
            )

        # Check for sorry in proof (incomplete)
        has_sorry = "sorry" in code.lower() and not verified
        if has_sorry:
            messages.sorries.append(
                Message(
                    severity="sorry",
                    data="incomplete proof",
                    pos=None,
                    end_pos=None,
                    keep_full_range=False,
                    caption="",
                )
            )

        # Build timing breakdown if available
        timing = None
        if timing_data:
            timing = TimingBreakdown(
                parse_ns=timing_data.get("parse_ns", 0),
                elaborate_ns=timing_data.get("elaborate_ns", 0),
                verify_ns=timing_data.get("verify_ns", 0),
                total_ns=timing_data.get("total_ns", time_ns),
            )

        return cleanVerifyResult(
            sorted_messages=messages,
            verified_code=code,
            verified_timeout=timeout,
            pass_=not bool(messages.errors),
            complete=verified and not has_sorry,
            is_timeout=False,
            verify_time=time_ns / 1e9 if time_ns else elapsed,
            complete_timestamp=datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
            system_errors=None,
            extra_info=extra_info,
            lean_toolchain="clean",
            timing=timing,
            certificate=result.get("certificate"),
        )

    def _error_result(
        self,
        code: str,
        timeout: int,
        error: str,
        extra_info: dict,
    ) -> cleanVerifyResult:
        """Create error/timeout result."""
        return cleanVerifyResult(
            sorted_messages=SortedMessages(),
            verified_code=code,
            verified_timeout=timeout,
            pass_=False,
            complete=False,
            is_timeout="timeout" in error.lower(),
            verify_time=float(timeout),
            complete_timestamp=datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
            system_errors=error,
            extra_info=extra_info,
            lean_toolchain="clean",
        )

    def _sequential_verify(
        self,
        codes: list[str],
        timeout: int,
        extra_infos: list[dict],
    ) -> list[cleanVerifyResult]:
        """Fallback: verify codes sequentially when batch not available."""
        return [
            self.verify(code, timeout, extra_info)
            for code, extra_info in zip(codes, extra_infos)
        ]

    def close(self) -> None:
        """Close the HTTP client."""
        self.client.close()

    def __enter__(self) -> "cleanVerifier":
        return self

    def __exit__(self, *args: object) -> None:
        self.close()
