#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""Deterministic level-pair enumeration for the pinned-Lean verdict fixture.

Writes `a<TAB>b` lines in `KernelLevelVerdicts.lean`'s encoding
(`Z`, `S(x)`, `M(a,b)`, `I(a,b)`, `P(n)`): every SEMANTICALLY EQUAL,
structurally distinct ordered pair of raw levels to depth 2 over the atoms
`0, 1, u, v, u+1, v+1`, a seeded sample of the depth-3 pairs built from them,
and the named shapes of `reports/level-normalizer-probe-2026-10-17/` (t1-t9).

Ground truth is evaluation only (u, v, w in 0..3); no port of either kernel's
level algebra is involved, so the file pins inputs, and pinned Lean decides
every verdict (`KernelLevelVerdicts.lean`). Usage:

    python3 gen_level_pairs.py <out.tsv>
"""

import random
import sys
from collections import defaultdict

SEED = 20261017
DEPTH3_SAMPLE = 1480

Z = ("Z",)


def S(level):
    return ("S", level)


def M(a, b):
    return ("M", a, b)


def I(a, b):
    return ("I", a, b)


def P(name):
    return ("P", name)


def ev(level, assignment):
    tag = level[0]
    if tag == "Z":
        return 0
    if tag == "S":
        return ev(level[1], assignment) + 1
    if tag == "P":
        return assignment[level[1]]
    if tag == "M":
        return max(ev(level[1], assignment), ev(level[2], assignment))
    right = ev(level[2], assignment)
    return 0 if right == 0 else max(ev(level[1], assignment), right)


def enc(level):
    tag = level[0]
    if tag == "Z":
        return "Z"
    if tag == "S":
        return f"S({enc(level[1])})"
    if tag == "P":
        return f"P({level[1]})"
    return f"{tag}({enc(level[1])},{enc(level[2])})"


def main() -> int:
    if len(sys.argv) != 2:
        print(__doc__, file=sys.stderr)
        return 2
    u, v, w, one = P("u"), P("v"), P("w"), S(Z)
    atoms = [Z, one, u, v, S(u), S(v)]
    depth2 = list(atoms)
    for a in atoms:
        for b in atoms:
            depth2 += [M(a, b), I(a, b)]
    depth2 = list(dict.fromkeys(depth2))
    uv = [{"u": x, "v": y, "w": 0} for x in range(4) for y in range(4)]
    sig2 = {lvl: tuple(ev(lvl, s) for s in uv) for lvl in depth2}
    rows = [(a, b) for a in depth2 for b in depth2 if a != b and sig2[a] == sig2[b]]

    depth3 = list(depth2)
    for x in depth2:
        if x[0] in ("M", "I"):
            for a in atoms:
                depth3 += [M(x, a), M(a, x), I(x, a), I(a, x)]
    depth3 = list(dict.fromkeys(depth3))
    known = set(depth2)
    classes = defaultdict(list)
    for lvl in depth3:
        classes[tuple(ev(lvl, s) for s in uv)].append(lvl)
    deep = [
        (a, b)
        for members in classes.values()
        for a in members
        for b in members
        if a != b and (a not in known or b not in known)
    ]
    rng = random.Random(SEED)
    rows += rng.sample(deep, DEPTH3_SAMPLE)

    # The named shapes (design §1). t5 and t10 are constructions, not pairs:
    # the kernel and replay tests pin them.
    uvw = [{"u": x, "v": y, "w": z} for x in range(4) for y in range(4) for z in range(4)]
    named = [
        (M(one, I(u, v)), M(M(one, v), I(u, v))),  # t1
        (M(S(u), w), M(S(u), M(M(one, w), I(S(u), I(S(u), w))))),  # t2
        (I(M(v, u), S(w)), M(u, M(v, S(w)))),  # t3
        (I(u, S(w)), M(u, S(w))),  # t3b
        (M(u, v), M(M(u, v), I(u, v))),  # t4
        (S(M(u, v)), M(S(u), S(v))),  # t6
        (M(one, M(u, v)), M(M(v, one), u)),  # t7
        (I(u, u), u),  # t8
        (M(u, I(v, u)), I(v, u)),  # t9
    ]
    for a, b in named:
        if [ev(a, s) for s in uvw] != [ev(b, s) for s in uvw]:
            print(f"named shape is not an equality: {enc(a)} {enc(b)}", file=sys.stderr)
            return 1
    rows += named
    with open(sys.argv[1], "w", encoding="utf-8") as out:
        for a, b in rows:
            out.write(f"{enc(a)}\t{enc(b)}\n")
    print(f"depth-2 {len(rows) - DEPTH3_SAMPLE - len(named)} depth-3 sample "
          f"{DEPTH3_SAMPLE} named {len(named)} total {len(rows)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
