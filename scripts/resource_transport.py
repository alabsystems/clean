# Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
"""Numeric descriptor transport only; native owners authenticate authority.

Keep the same field/parser contract as Trust's maintained launcher. This helper
creates no pool, credits, SDK lease or CPU claim and changes no advertisements.
"""
from __future__ import annotations

import os
import re
from typing import Dict, Set, Tuple


def resource_fds(env: Dict[str, str]) -> Tuple[int, ...]:
    """Preserve only advertised live transport descriptions, never grant authority.

    The native owners still authenticate GNU/SDK/CPU custody. A Python launch
    must not silently close its caller's actual descriptions or pass unrelated
    descriptors. Malformed or closed locators refuse before running a row.
    """
    descriptors: Set[int] = set()

    def add(word: str, name: str) -> None:
        if not re.fullmatch(r"[1-9][0-9]{0,9}", word) or int(word) < 3:
            raise RuntimeError(f"row custody: malformed {name} descriptor")
        descriptor = int(word)
        try:
            os.fstat(descriptor)
        except (OSError, OverflowError) as error:
            raise RuntimeError(f"row custody: {name} descriptor is not live") from error
        descriptors.add(descriptor)

    for name in ("ATERM_SDK_LEASE_V3", "ATERM_WORKLOAD_HOST_STORE_FD_V1",
                 "TRUST_CPU_IMPLICIT_FD"):
        if name in env:
            add(env[name], name)
    for name in ("ATERM_WORKLOAD_CPU_FDS_V1", "BUILD_SLOT_FENCE_FDS",
                 "ATERM_WORKLOAD_HOST_CONTROL_FDS_V1"):
        if name in env:
            words = env[name].split(",")
            if not 1 <= len(words) <= 128 or len(set(words)) != len(words):
                raise RuntimeError(f"row custody: malformed {name} descriptor set")
            for word in words:
                add(word, name)
    # Match vendor/jobserver's environment and find_jobserver_auth precedence:
    # first PRESENT variable, last auth substring, otherwise last legacy fds;
    # the value stops at a literal space (not shell/general whitespace).
    # Never inspect or resurrect obsolete/lower-priority pipe advertisements.
    for name in ("CARGO_MAKEFLAGS", "MAKEFLAGS", "MFLAGS"):
        if name not in env:
            continue
        flags = env[name]
        try:
            flags.encode("utf-8")
        except UnicodeError as error:
            raise RuntimeError(f"row custody: malformed {name} jobserver flags") from error
        value = None
        for option in ("--jobserver-auth=", "--jobserver-fds="):
            if option in flags:
                value = flags.rsplit(option, 1)[1].split(" ", 1)[0]
                break
        if value is None:
            break
        # Named FIFO and native handoff authentication stay with the native
        # importer. A path/advertisement never becomes numeric FD authority.
        if value.startswith("fifo:") and value != "fifo:":
            break
        pair = re.fullmatch(r"([+-]?[0-9]+),([+-]?[0-9]+)", value)
        if pair is None:
            raise RuntimeError(f"row custody: malformed {name} jobserver descriptor pair")
        numbers = []
        for word in pair.groups():
            # Rust parses signed i32 values, including + and leading zeroes.
            # Bound normalized digits before int(), including enormous inputs.
            digits = word.lstrip("+-").lstrip("0") or "0"
            if len(digits) > 10:
                raise RuntimeError(f"row custody: malformed {name} jobserver descriptor")
            number = int(digits) * (-1 if word.startswith("-") else 1)
            if not -(1 << 31) <= number < (1 << 31):
                raise RuntimeError(f"row custody: malformed {name} jobserver descriptor")
            numbers.append(number)
        # Negative descriptors disable numeric transport; native import policy
        # still decides whether that advertisement is allowed for its context.
        if all(number >= 0 for number in numbers):
            for number in numbers:
                add(str(number), name)
        break
    return tuple(sorted(descriptors))
