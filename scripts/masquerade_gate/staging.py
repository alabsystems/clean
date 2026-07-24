# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0
"""Staged-file discovery for the MASQUERADE gate."""
from __future__ import annotations

import logging
import subprocess
from pathlib import Path

from scripts.masquerade_gate.constants import NN_VERIFY_GLOB_PREFIX

logger = logging.getLogger(__name__)


def staged_nn_verify_files(repo_root: Path) -> list[Path]:
    """Return staged (A/C/M) paths matching the NN-verify glob."""
    try:
        out = subprocess.check_output(
            ["git", "diff", "--cached", "--name-only", "--diff-filter=ACM"],
            cwd=repo_root,
            text=True,
        )
    except (OSError, subprocess.CalledProcessError) as exc:
        logger.warning(
            "[masquerade-gate] ERROR: git diff --cached failed: %s", exc
        )
        return []
    hits: list[Path] = []
    for line in out.splitlines():
        line = line.strip()
        if not line or not line.startswith(NN_VERIFY_GLOB_PREFIX):
            continue
        if not line.endswith(".rs"):
            continue
        if Path(line).name.startswith("tests_"):
            continue
        hits.append(repo_root / line)
    return hits


def repo_root() -> Path:
    try:
        out = subprocess.check_output(
            ["git", "rev-parse", "--show-toplevel"], text=True
        )
        return Path(out.strip())
    except (OSError, subprocess.CalledProcessError):
        return Path(__file__).resolve().parents[2]
