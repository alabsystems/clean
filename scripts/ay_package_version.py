# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Stable AY version spelling, without source or compatibility authority."""
import re


def stable_version(raw):
    if not isinstance(raw, str) or re.fullmatch(
            r"(?:0|[1-9][0-9]*)\.(?:0|[1-9][0-9]*)\.(?:0|[1-9][0-9]*)", raw) is None:
        return None
    try:
        return tuple(map(int, raw.split(".")))
    except ValueError:
        return None


def is_ay_028_patch(raw):
    version = stable_version(raw)
    return version is not None and version[:2] == (0, 28)
