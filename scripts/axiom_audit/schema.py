#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""Schema helpers for `data/axiom_audit.json`."""

from __future__ import annotations

__all__ = ["KNOWN_MECHANISMS", "load_audit"]

import json
from pathlib import Path
from typing import Any

KNOWN_MECHANISMS = {
    "constructive",
    "sorry_inhabited",
    "axiom_wrapper",
    "unchecked",
    "mixed",
    "masquerade_demoted",
    "hypothesis_wrapped",
    "hypothesis_wrapped_local_evidence",
}


def _validate_conjectures(conjectures: dict[str, Any]) -> list[str]:
    errs: list[str] = []
    for cid, entry in conjectures.items():
        mech = entry.get("proof_mechanism")
        if mech is None:
            errs.append(f"{cid}: missing 'proof_mechanism'")
        elif mech not in KNOWN_MECHANISMS:
            errs.append(
                f"{cid}: unknown proof_mechanism '{mech}' "
                f"(expected one of {sorted(KNOWN_MECHANISMS)})"
            )
    return errs


def _validate_required_aggregate(raw: dict[str, Any], key: str) -> list[str]:
    if key not in raw:
        return [f"top-level {key!r}: missing"]
    val = raw[key]
    if val is None:
        return [
            f"top-level {key!r}: null — violates ratchet invariant "
            f"(#3613). Run `python3 -m scripts.axiom_audit.aggregates`."
        ]
    if isinstance(val, bool) or not isinstance(val, int):
        return [f"top-level {key!r}: non-integer {val!r} (want int)"]
    if val < 0:
        return [f"top-level {key!r}: negative {val}"]
    return []


def _validate_total_all_axioms(raw: dict[str, Any]) -> list[str]:
    if "total_all_axioms" not in raw:
        return []
    val = raw["total_all_axioms"]
    if val is None:
        return [
            "top-level 'total_all_axioms': null — violates ratchet "
            "invariant (#3641). Run `python3 -m scripts.axiom_audit.aggregates`."
        ]
    if isinstance(val, bool) or not isinstance(val, int):
        return [f"top-level 'total_all_axioms': non-integer {val!r} (want int)"]
    if val < 0:
        return [f"top-level 'total_all_axioms': negative {val}"]
    total_domain_axioms = raw.get("total_domain_axioms")
    if (
        isinstance(total_domain_axioms, int)
        and not isinstance(total_domain_axioms, bool)
        and val < total_domain_axioms
    ):
        return [
            f"top-level 'total_all_axioms' ({val}) is less than "
            f"'total_domain_axioms' ({total_domain_axioms}); non-conjecture "
            "delta must be non-negative (#3641)."
        ]
    return []


def _validate_non_conjecture_per_prefix(
    block: dict[str, Any],
) -> tuple[dict[str, Any] | None, int, list[str]]:
    per_prefix = block.get("per_prefix")
    if not isinstance(per_prefix, dict):
        return (
            None,
            0,
            [
                f"top-level 'non_conjecture_axioms.per_prefix': expected object, got {type(per_prefix).__name__}"
            ],
        )

    errs: list[str] = []
    per_prefix_sum = 0
    for prefix, entry in per_prefix.items():
        prefix_path = prefix.rstrip(".")
        if not isinstance(entry, dict):
            errs.append(
                f"top-level 'non_conjecture_axioms.per_prefix.{prefix_path}': "
                f"expected object, got {type(entry).__name__}"
            )
            continue
        count = entry.get("count")
        if isinstance(count, bool) or not isinstance(count, int):
            errs.append(
                f"top-level 'non_conjecture_axioms.per_prefix.{prefix_path}.count': "
                f"non-integer {count!r} (want int)"
            )
            continue
        if count < 0:
            errs.append(
                f"top-level 'non_conjecture_axioms.per_prefix.{prefix_path}.count': negative {count}"
            )
            continue
        per_prefix_sum += count

    return per_prefix, per_prefix_sum, errs


def _validate_non_conjecture_delta(
    raw: dict[str, Any], per_prefix: dict[str, Any], per_prefix_sum: int
) -> list[str]:
    total_all = raw.get("total_all_axioms")
    total_domain = raw.get("total_domain_axioms")
    if not isinstance(total_all, int) or isinstance(total_all, bool):
        return []
    if not isinstance(total_domain, int) or isinstance(total_domain, bool):
        return []
    delta = total_all - total_domain

    if delta == 0:
        if per_prefix_sum == 0:
            return []
        return [
            f"'non_conjecture_axioms.per_prefix' sum={per_prefix_sum} "
            "but total_all_axioms - total_domain_axioms = 0 (#3641)."
        ]

    if per_prefix and per_prefix_sum == delta:
        return []

    if not per_prefix:
        return [
            f"'total_all_axioms' exceeds 'total_domain_axioms' by {delta}, "
            "but 'non_conjecture_axioms.per_prefix' is empty. #3641 requires "
            "the per-prefix breakdown to accompany any non-zero delta. "
            "Run `python3 -m scripts.axiom_audit.aggregates` after populating "
            "data/axiom_audit.json.non_conjecture_axioms."
        ]
    return [
        f"'non_conjecture_axioms.per_prefix' sum={per_prefix_sum} "
        f"does not match total_all_axioms - total_domain_axioms = {delta} (#3641)."
    ]


def _validate_non_conjecture_block(raw: dict[str, Any]) -> list[str]:
    block = raw.get("non_conjecture_axioms")
    if block is None:
        return []
    if not isinstance(block, dict):
        return [
            f"top-level 'non_conjecture_axioms': expected object, got {type(block).__name__}"
        ]

    per_prefix, per_prefix_sum, errs = _validate_non_conjecture_per_prefix(block)
    if errs:
        return errs
    assert per_prefix is not None
    return _validate_non_conjecture_delta(raw, per_prefix, per_prefix_sum)


def load_audit(path: Path) -> dict[str, Any]:
    """Load and structurally validate `data/axiom_audit.json`."""
    if not path.exists():
        raise FileNotFoundError(f"axiom audit file not found: {path}")
    raw = json.loads(path.read_text(encoding="utf-8"))
    conjectures = raw.get("conjectures")
    if not isinstance(conjectures, dict):
        raise ValueError(f"{path}: missing or non-object 'conjectures' field")

    errs: list[str] = []
    errs.extend(_validate_conjectures(conjectures))
    for agg_key in ("total_domain_axioms", "total_theorems"):
        errs.extend(_validate_required_aggregate(raw, agg_key))
    errs.extend(_validate_total_all_axioms(raw))
    errs.extend(_validate_non_conjecture_block(raw))

    if errs:
        raise ValueError("axiom_audit.json schema errors:\n" + "\n".join(errs))
    return raw
