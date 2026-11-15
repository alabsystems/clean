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
        except OSError as error:
            raise RuntimeError(f"row custody: {name} descriptor is not live") from error
        descriptors.add(descriptor)

    for name in ("ATERM_SDK_LEASE_V3", "ATERM_WORKLOAD_HOST_STORE_FD_V1",
                 "TRUST_CPU_IMPLICIT_FD"):
        if name in env:
            add(env[name], name)
    for name in ("ATERM_WORKLOAD_CPU_FDS_V1", "BUILD_SLOT_FENCE_FDS"):
        if name in env:
            words = env[name].split(",")
            if not 1 <= len(words) <= 128 or len(set(words)) != len(words):
                raise RuntimeError(f"row custody: malformed {name} descriptor set")
            for word in words:
                add(word, name)
    # FIFO/path and native handoff advertisements are deliberately left intact
    # for the maintained GNU importer. Only its numeric pipe transport needs
    # descriptor inheritance at this Python boundary.
    for name in ("CARGO_MAKEFLAGS", "MAKEFLAGS", "MFLAGS"):
        for pair in re.finditer(r"(?:^|\s)--jobserver-(?:auth|fds)=([0-9]+),([0-9]+)(?=\s|$)",
                                env.get(name, "")):
            add(pair[1], name)
            add(pair[2], name)
    return tuple(sorted(descriptors))
