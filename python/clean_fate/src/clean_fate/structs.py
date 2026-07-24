# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0

"""
Data structures for clean-fate integration.

These types are compatible with FATE-Eval's structs.py, using Pydantic BaseModel
for JSON serialization and camelCase alias support.
"""

from typing import Literal, Optional

from pydantic import BaseModel, ConfigDict
from pydantic.alias_generators import to_camel


class Pos(BaseModel):
    """Position in source code."""
    model_config = ConfigDict(alias_generator=to_camel, populate_by_name=True)

    line: int
    column: int


Severity = Literal["error", "warning", "information", "sorry"]


class Message(BaseModel):
    """Verification message from clean."""
    model_config = ConfigDict(alias_generator=to_camel, populate_by_name=True)

    severity: Severity
    pos: Optional[Pos] = None
    end_pos: Optional[Pos] = None
    keep_full_range: bool = False
    data: str
    caption: str = ""


class SortedMessages(BaseModel):
    """Messages sorted by severity, compatible with FATE-Eval."""
    model_config = ConfigDict(alias_generator=to_camel, populate_by_name=True)

    errors: list[Message] = []
    sorries: list[Message] = []
    warnings: list[Message] = []
    informations: list[Message] = []


class TimingBreakdown(BaseModel):
    """
    Per-stage timing from clean verification.

    Required for δ measurement per the 4/δ bound theorem (arXiv:2512.02080).
    Maps to verification pipeline stages:
    - parse: CodeGen stage
    - elaborate: InvariantSynth stage
    - verify: SMTSolving stage
    """
    model_config = ConfigDict(alias_generator=to_camel, populate_by_name=True)

    parse_ns: int = 0
    elaborate_ns: int = 0
    verify_ns: int = 0
    total_ns: int = 0


class cleanVerifyResult(BaseModel):
    """
    Verification result from clean, compatible with FATE-Eval's VerifyResult.

    This is a drop-in replacement that includes additional clean-specific
    fields like timing breakdown.
    """
    model_config = ConfigDict(alias_generator=to_camel, populate_by_name=True)

    # FATE-Eval compatible fields
    sorted_messages: SortedMessages
    system_errors: Optional[str] = None
    verified_code: str
    verified_timeout: int
    pass_: bool  # No errors encountered
    complete: bool  # Proof complete (no sorries)
    is_timeout: bool
    verify_time: float  # Seconds
    complete_timestamp: str
    extra_info: dict = {}
    lean_toolchain: str = "clean"

    # clean-specific extensions
    timing: Optional[TimingBreakdown] = None
    certificate: Optional[str] = None  # Proof certificate from clean


class ExtractedTheorem(BaseModel):
    """Theorem extracted from a Lean file by verifyFile endpoint."""
    model_config = ConfigDict(alias_generator=to_camel, populate_by_name=True)

    name: str  # Theorem name (e.g., "fate_x_001")
    goal: str  # Full type/goal signature
    line: int  # Line number where theorem starts
    original_proof: str  # Original proof text


class SorryLocation(BaseModel):
    """Location of a sorry in a Lean file."""
    model_config = ConfigDict(alias_generator=to_camel, populate_by_name=True)

    line: int  # Line number (1-indexed)
    col: int  # Column number (1-indexed)
    context: Optional[str] = None  # Enclosing theorem name


class VerifyFileResult(BaseModel):
    """
    Result from clean's verifyFile endpoint.

    Used for FATE benchmark file verification - extracts theorem info
    and optionally verifies a replacement proof.
    """
    model_config = ConfigDict(alias_generator=to_camel, populate_by_name=True)

    verified: bool
    theorem: Optional[ExtractedTheorem] = None
    sorries: list[SorryLocation] = []
    time_ns: int
    timing: Optional[TimingBreakdown] = None
    error: Optional[dict] = None  # VerifyProofError from clean
