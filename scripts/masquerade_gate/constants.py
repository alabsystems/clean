# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0
"""Shared constants, regexes, and carrier tables for the MASQUERADE gate.

See `designs/2026-04-19-demasquerade-cxxx-pattern.md` for the methodology.
"""
from __future__ import annotations

import re

# Glob prefix for the "NN-verify registration" surface. The gate is
# intentionally scoped here because these are the files the demasquerade
# sweep (wave 6-9) had to repair.
NN_VERIFY_GLOB_PREFIX = "crates/clean-kernel/src/env/nn_verify_"

# Trivial proof-term combinators.
TRIVIAL_PROOFS: tuple[str, ...] = (
    "Eq.refl",
    "Rat.le_refl",
    "Nat.le_refl",
    "True.intro",
    "rfl",
)

# Carrier names identified by prior demasquerade waves as confirmed
# argument-discarding reducible Definitions.
KNOWN_MASQUERADE_CARRIERS: tuple[str, ...] = (
    "NNVerify.Block.compose",
    "NNVerify.Block.monolithic_crown",
    "NNVerify.Block.ibp_transfer",
    "NNVerify.IBP.forward_layernorm",
    "NNVerify.CROWN.backward_layernorm",
    "NNVerify.LayerNorm.generators_after_ln",
    "NNVerify.axiomProfile",
    "NNVerify.composePair",
)

# Mapping carrier constant name -> list of helper identifiers that
# typically construct that constant in the Rust source.
CARRIER_HELPER_HINTS: tuple[tuple[str, tuple[str, ...]], ...] = (
    (
        "NNVerify.Block.compose",
        ("block_compose", "Block.compose", "build_block_compose"),
    ),
    (
        "NNVerify.Block.monolithic_crown",
        (
            "monolithic_crown",
            "Block.monolithic_crown",
            "build_monolithic_crown",
        ),
    ),
    (
        "NNVerify.Block.ibp_transfer",
        ("ibp_transfer", "Block.ibp_transfer", "build_ibp_transfer"),
    ),
    (
        "NNVerify.IBP.forward_layernorm",
        (
            "forward_layernorm",
            "IBP.forward_layernorm",
            "build_ibp_forward_layernorm",
        ),
    ),
    (
        "NNVerify.CROWN.backward_layernorm",
        (
            "backward_layernorm",
            "CROWN.backward_layernorm",
            "build_crown_backward_layernorm",
        ),
    ),
    (
        "NNVerify.LayerNorm.generators_after_ln",
        ("generators_after_ln", "LayerNorm.generators_after_ln"),
    ),
    (
        "NNVerify.axiomProfile",
        ("axiom_profile", "axiomProfile", "build_axiom_profile_app"),
    ),
    (
        "NNVerify.composePair",
        ("compose_pair", "composePair", "build_compose_pair_app"),
    ),
)

DECL_THEOREM_HEADER = re.compile(r"Declaration::Theorem\s*\{", re.MULTILINE)
DECL_DEFINITION_HEADER = re.compile(
    r"Declaration::Definition\s*\{", re.MULTILINE
)
NAME_FROM_STRING = re.compile(
    r'Name::from_string\(\s*"([^"]+)"\s*,?\s*\)'
)
IS_REDUCIBLE_TRUE = re.compile(r"is_reducible\s*:\s*true")
ARG_DISCARDING_HELPERS = re.compile(
    r"\b(?:"
    r"zero_ib|"
    r"identity_on_bounds|"
    r"build_[a-z_0-9]+_zero(?:_[a-z_0-9]+)?|"
    r"forward_layernorm_identity|"
    r"constant_bound|"
    r"placeholder_carrier|"
    r"tail_norm_sum_zero|"
    r"identity_carrier"
    r")\b"
)
ALLOW_MARKER = re.compile(r"//\s*MASQUERADE-ALLOW:\s*(.+)$", re.MULTILINE)
