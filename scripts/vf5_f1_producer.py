#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""VF5's certificate producer over SemR (docs/DECISIONS.md R169, R170, R206, R213, R215).

Writes the generated modules of the fixture family
`crates/clean-olean/tests/fixtures/lean/v4.30.0-rc2/vf5_f1/`:

* `VF5Rows.lean`: one "proved (calculus)" theorem per VF3-census F1 row named
  in `blobs/rows.tsv` — `RowProved blob A fid sym` by `row_of checks rfl`, where
  `checks : checkBlob blob A certs = true := rfl` makes the kernel decode the
  stage-2 compiler's trust-ir blob with SemR's decoder, evaluate F1's `vc`
  under the precondition annotation `A`, and run VF4's `chk_LIA_cases` on
  every obligation with its certificate, and `rfl` decides the row's shape
  (`rowShape`: function `fid` carries the symbol `sym`, the module's roots carry
  no precondition, every annotated function is reachable from a root) — plus a
  satisfiability witness for every precondition the annotation states;
* `VF5MutantRows.lean`: for each mutant calculus, the certificates of every
  obligation it emits for its counterexample blob and the bad run SemR
  evaluates (`mutSign` and, per signed comparison, `mutSignAt`, each on its own
  compiled witness); for the twins, F1's own rows; and the entry premise's
  controls (an annotation on a root, satisfiable or vacuous, certifies the
  reproducer's obligations but no row's shape);
* `VF7Rows.lean` (R206) and `VF5AtermRows.lean`: the spec harnesses' rows
  (`blobs/vf7/`, `blobs/aterm_spec/`), one artifact per row, each with its
  false-clause control (`spec_rows`), and VF7's mutants and twins.
* `VF5D2bRows1.lean` … `VF5D2bRows10.lean`: the D-2(b) rows (R213, R215), aterm's "PM-1-free,
  F1+D2b" and "behind PM-1, F1+D2b" functions' spec harnesses over `blobs/d2b_rows/`, each `RowProvedB3`, with a
  false-clause control per row and B3 against rustc's own reading (`b3probe.rs`).
* `VF5PM1Rows1.lean` … `VF5PM1Rows6.lean`: aterm's "behind PM-1, F1" functions' spec
  harnesses over `blobs/pm1_rows/`, each `RowProved`, with a false-clause control per row.

This producer is UNTRUSTED. It runs the calculus itself (Lean `#eval` of
`VF5.vcC` over the family's own modules, compiled here by the pinned `lean`)
to learn the obligations, searches the annotation R1-style (a function whose
obligations are not all refutable gets, as candidate precondition, the
negation of one constraint of a failing obligation over its parameter
variables; a candidate is kept when its function then certifies and the
module's failing obligations strictly decrease, so a vacuous candidate that
moves the failures to the callers is rejected), and finds a Farkas
certificate per obligation by exact rational simplex. A wrong annotation or
certificate makes the kernel refuse the theorem.

    python3 scripts/vf5_f1_producer.py            # regenerate
    python3 scripts/vf5_f1_producer.py --check    # exit 1 on drift
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
from fractions import Fraction
from math import gcd
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
FAMILY = ROOT / "crates/clean-olean/tests/fixtures/lean/v4.30.0-rc2/vf5_f1"
BLOBS = FAMILY / "blobs"
THEORY = ROOT / "theories/chk_lia"
BUILD = ROOT / "target/vf5-producer"
GENERATED = {"VF5Rows", "VF5MutantRows", "VF7Rows", "VF5AtermRows"}
VF7 = BLOBS / "vf7"
ATERM_SPEC = BLOBS / "aterm_spec"
D2B_ROWS = BLOBS / "d2b_rows"
# Bytes of artifact literals per D-2(b) module (`VF7Rows` holds about 45 KB).
D2B_CHUNK = 46000
PIN = "v4.30.0-rc2"


def lean_bin() -> Path:
    pin = (ROOT / "lean-toolchain").read_text().strip()
    assert pin == f"leanprover/lean4:{PIN}", pin
    return Path.home() / f".elan/toolchains/leanprover--lean4---{PIN}/bin/lean"


def order_stems(path: Path) -> list[str]:
    out = []
    for line in path.read_text().splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        out.append(line)
    return out


def build() -> Path:
    """Compile the theory and the family's hand-written modules into BUILD."""
    lean = lean_bin()
    if BUILD.exists():
        shutil.rmtree(BUILD)
    BUILD.mkdir(parents=True)
    stems = []
    for step in order_stems(FAMILY / "ORDER"):
        if step.startswith("theory "):
            name = step.split()[1]
            assert name == "chk_lia", step
            for s in order_stems(THEORY / "ORDER"):
                shutil.copy(THEORY / f"{s}.lean", BUILD / f"{s}.lean")
                stems.append(s)
        elif step.startswith("from "):
            # A sibling family's source (`from semr SemR`: Clean's one SemR copy).
            family, stem = step.split()[1:]
            shutil.copy(FAMILY.parent / family / f"{stem}.lean", BUILD / f"{stem}.lean")
            stems.append(stem)
        elif step in GENERATED or step.startswith(("VF5D2bRows", "VF5PM1Rows")):
            break
        else:
            shutil.copy(FAMILY / f"{step}.lean", BUILD / f"{step}.lean")
            stems.append(step)
    for s in stems:
        out = subprocess.run([str(lean), "--root", ".", "-o", f"{s}.olean", f"{s}.lean"],
                             cwd=BUILD, capture_output=True, text=True,
                             env=dict(os.environ, LEAN_PATH=str(BUILD)))
        if out.returncode != 0:
            sys.exit(f"lean {s}.lean failed:\n{out.stdout}{out.stderr}")
    return BUILD


# --------------------------------------------------------------------------
# Lean spellings.
# --------------------------------------------------------------------------

def lean_cons(c) -> str:
    co, b = c
    return "⟨[%s], %d⟩" % (", ".join(str(x) for x in co), b)


def lean_annot(pre: dict) -> str:
    items = ["(%d, [%s])" % (fid, ", ".join(lean_cons(c) for c in cs)) for fid, cs in sorted(pre.items())]
    return "annot [%s]" % ", ".join(items)


def lean_cert(lam) -> str:
    if isinstance(lam, dict):
        # A cutting-plane certificate (VF7): Chvátal–Gomory steps, then a Farkas step.
        return "[%s]" % ", ".join("⟨[%s], %d⟩" % (", ".join(str(x) for x in ms), d)
                                  for ms, d in lam["steps"])
    return "[⟨[%s], 0⟩]" % ", ".join(str(x) for x in lam)


def lean_certs(certs: dict) -> str:
    return "[%s]" % ",\n   ".join(
        "(%d, [%s])" % (fid, ", ".join(lean_cert(l) for l in certs[fid])) for fid in sorted(certs))


def lean_bytes(blob) -> str:
    return "[%s]" % ", ".join(str(b) for b in blob)


# --------------------------------------------------------------------------
# The calculus, evaluated by Lean.
# --------------------------------------------------------------------------

def dump(blob, pre, calc="stdCalc"):
    """`VF5.vcC calc` of every function of the decoded blob: {fid: (params, [obligation])}."""
    src = "\n".join([
        "import VF5Mutants",
        "open SemR VF5",
        "set_option maxRecDepth 100000",
        "def blob : List Nat := " + lean_bytes(blob),
        "def A : Nat → List Cons := " + lean_annot(pre),
        'def jc (c : ChkLIA.Cons) : String := s!"[{c.coeffs},{c.bound}]"',
        'def jp (p : List ChkLIA.Cons) : String := "[" ++ ",".intercalate (p.map jc) ++ "]"',
        "def jt : Ty → String",
        '  | .int t => s!"\\"i{t.code}\\"" | .bool => "\\"b\\"" | _ => "\\"o\\""',
        "#eval match decode blob with",
        '  | .ok m => "{\\"fns\\":[" ++ ",".intercalate (m.functions.map fun (g : Func) =>',
        '      s!"[{g.id},[" ++ ",".intercalate ((match nth? m.funcTys g.ty with',
        '        | some (t : FuncTy) => t.params | none => []).map jt) ++ "],[" ++',
        '      ",".intercalate ((vcC ' + calc + ' m A g.id).map jp) ++ "]]") ++ "]}"',
        '  | .error _ => "{\\"error\\":true}"',
        ""])
    path = BUILD / "Dump.lean"
    path.write_text(src)
    out = subprocess.run([str(lean_bin()), "Dump.lean"], cwd=BUILD, capture_output=True, text=True,
                         env=dict(os.environ, LEAN_PATH=str(BUILD)))
    if out.returncode != 0:
        sys.exit("lean Dump.lean failed:\n" + out.stdout + out.stderr)
    text = out.stdout.strip()
    data = json.loads(json.loads(text))
    if "error" in data:
        sys.exit("SemR does not decode the blob")
    return {fid: (params, [[(co, b) for co, b in p] for p in obs]) for fid, params, obs in data["fns"]}


def meta(blob, pre):
    """What the row's shape reads, evaluated by Lean: each function's symbol
    (bytes), the module's roots, and `entriesOK` under `pre`."""
    src = "\n".join([
        "import VF5Mutants",
        "open SemR VF5",
        "set_option maxRecDepth 100000",
        "def blob : List Nat := " + lean_bytes(blob),
        "def A : Nat → List Cons := " + lean_annot(pre),
        "#eval match decode blob with",
        '  | .ok m => "{\\"names\\":[" ++ ",".intercalate (m.functions.map fun (g : Func) =>',
        '      s!"[{g.id},{g.name}]") ++ s!"],\\"roots\\":{roots m},\\"entries\\":{entriesOK m A}}"',
        '  | .error _ => "{\\"error\\":true}"',
        ""])
    path = BUILD / "Meta.lean"
    path.write_text(src)
    out = subprocess.run([str(lean_bin()), "Meta.lean"], cwd=BUILD, capture_output=True, text=True,
                         env=dict(os.environ, LEAN_PATH=str(BUILD)))
    if out.returncode != 0:
        sys.exit("lean Meta.lean failed:\n" + out.stdout + out.stderr)
    data = json.loads(json.loads(out.stdout.strip()))
    if "error" in data:
        sys.exit("SemR does not decode the blob")
    return {fid: bytes(name) for fid, name in data["names"]}, data["roots"], data["entries"]


def lean_sym(name: str, sym: bytes) -> str:
    return (f"/-- `{sym.decode()}` -/\n"
            f"def sym_{name} : List Nat := {lean_bytes(list(sym))}\n")


# --------------------------------------------------------------------------
# Farkas certificates.
# --------------------------------------------------------------------------

def farkas(cons):
    """Nonnegative integer multipliers λ with Σ λ_j·a_j = 0 and Σ λ_j·b_j < 0,
    or None: exact phase-1 simplex over the rationals, Bland's rule."""
    m = len(cons)
    if m == 0:
        return None
    n = max(len(co) for co, _ in cons)
    rows = [[Fraction(co[i] if i < len(co) else 0) for co, _ in cons] + [Fraction(0)] for i in range(n)]
    rows.append([Fraction(b) for _, b in cons] + [Fraction(-1)])
    for r in rows:
        if r[-1] < 0:
            r[:] = [-x for x in r]
    R = len(rows)
    tab = [r[:-1] + [Fraction(1 if k == i else 0) for k in range(R)] + [r[-1]] for i, r in enumerate(rows)]
    basis = [m + i for i in range(R)]
    ncols = m + R
    z = [Fraction(0)] * (ncols + 1)
    for i in range(R):
        for k in range(ncols + 1):
            z[k] -= tab[i][k]
    for i in range(R):
        z[m + i] += 1
    while True:
        enter = next((k for k in range(ncols) if z[k] < 0), None)
        if enter is None:
            break
        best = None
        for i in range(R):
            if tab[i][enter] > 0:
                ratio = tab[i][-1] / tab[i][enter]
                if best is None or ratio < best[0] or (ratio == best[0] and basis[i] < basis[best[1]]):
                    best = (ratio, i)
        if best is None:
            return None
        i = best[1]
        piv = tab[i][enter]
        tab[i] = [x / piv for x in tab[i]]
        for r in range(R):
            if r != i and tab[r][enter] != 0:
                f = tab[r][enter]
                tab[r] = [a - f * b for a, b in zip(tab[r], tab[i])]
        f = z[enter]
        z = [a - f * b for a, b in zip(z, tab[i])]
        basis[i] = enter
    if z[-1] != 0:
        return None
    lam = [Fraction(0)] * m
    for i, bv in enumerate(basis):
        if bv < m:
            lam[bv] = tab[i][-1]
    den = 1
    for x in lam:
        den = den * x.denominator // gcd(den, x.denominator)
    ints = [int(x * den) for x in lam]
    for i in range(n):
        assert sum(ints[j] * (cons[j][0][i] if i < len(cons[j][0]) else 0) for j in range(m)) == 0
    assert sum(ints[j] * cons[j][1] for j in range(m)) < 0 and all(x >= 0 for x in ints)
    return ints


def cg_cert(cons):
    """VF7: when the rational relaxation is satisfiable, one round of
    Chvátal–Gomory rounding of single constraints (a constraint whose
    coefficients share a divisor `g ≥ 2` its bound does not have: divide and
    round the bound down; a bit read through a sign or a repeated sign bit is the
    usual case), then a Farkas certificate over the cuts and the problem. The
    steps are `chk_LIA`'s: unit multipliers over the known constraints, newest
    first, and the divisor."""
    m = len(cons)
    derived, steps = [], []
    for j, (co, b) in enumerate(cons):
        g = 0
        for x in co:
            g = gcd(g, abs(x))
        if g >= 2 and b % g != 0:
            mults = [0] * (len(derived) + m)
            mults[len(derived) + j] = 1
            steps.append((mults, g))
            derived.insert(0, ([x // g for x in co], b // g))
    if not steps:
        return None
    lam = farkas(derived + list(cons))
    if lam is None:
        return None
    steps.append((lam, 0))
    return {"steps": steps}


def cg_combo_cert(cons):
    """When single-constraint rounding is not enough: one round of Chvátal–Gomory cuts of
    a constraint, or of a constraint plus one other that cancels a word variable (a
    value's definition by its bits, `x = Σ 2^i·bᵢ`), COMBINED with unit bounds of its
    variables. For each such base and each divisor `g` (2..=16 and every power of two up
    to 2^64), every coefficient not divisible by `g` is made so by adding copies of a unit
    bound of that variable among the constraints (`x ≤ u` adds `+1`, `-x ≤ -l` adds `-1`;
    the cheaper in bound is taken); when the combined bound is not divisible by `g`, the
    rounding tightens it. The parity of a sum whose low bit the path fixed (`y = x + 1`
    read bit by bit, `x` even) and a narrow range's high bits (`l ≤ 14` read bit by bit)
    are the usual cases. Then a Farkas certificate over the cuts and the problem, and the
    cuts it does not use dropped. Tried only where `farkas` and `cg_cert` find none, so
    every certificate they find is unchanged."""
    m = len(cons)
    upper, lower = {}, {}
    for j, (co, b) in enumerate(cons):
        nz = [(i, x) for i, x in enumerate(co) if x != 0]
        if len(nz) == 1 and nz[0][1] in (1, -1):
            i, x = nz[0]
            side = upper if x == 1 else lower
            if i not in side or b < cons[side[i]][1]:
                side[i] = j
    bit = {i for i in upper if i in lower and cons[upper[i]][1] <= 1 and cons[lower[i]][1] >= 0}
    n = max(len(co) for co, _ in cons)

    def vec(co):
        return [co[i] if i < len(co) else 0 for i in range(n)]

    bases = [((j,), vec(co), b) for j, (co, b) in enumerate(cons)]
    for j, (co, b) in enumerate(cons):
        for k, (ck, bk) in enumerate(cons):
            if k == j:
                continue
            a, c = vec(co), vec(ck)
            if any(a[i] != 0 and a[i] == -c[i] and i not in bit for i in range(n)):
                bases.append(((j, k), [x + y for x, y in zip(a, c)], b + bk))
    divisors = sorted(set(range(2, 17)) | {1 << e for e in range(1, 65)})
    cands, seen = [], set()
    for base, acc0, b0 in bases:
        for g in divisors:
            mult = [0] * m
            for j in base:
                mult[j] += 1
            acc, bound = list(acc0), b0
            okc = True
            for i, a in enumerate(acc0):
                r = a % g
                if r == 0:
                    continue
                opts = []
                if i in upper:
                    opts.append(((g - r) * cons[upper[i]][1], upper[i], g - r, 1))
                if i in lower:
                    opts.append((r * cons[lower[i]][1], lower[i], r, -1))
                if not opts:
                    okc = False
                    break
                cost, jb, k, sgn = min(opts)
                mult[jb] += k
                acc[i] += sgn * k
                bound += cost
            if not okc or not any(acc) or bound % g == 0:
                continue
            cut = (tuple(x // g for x in acc), bound // g)
            if cut in seen:
                continue
            seen.add(cut)
            cands.append((mult, g, (list(cut[0]), cut[1])))
    if not cands:
        return None

    def attempt(cs):
        derived, steps = [], []
        for mult, g, cut in cs:
            steps.append(([0] * len(derived) + mult, g))
            derived.insert(0, cut)
        return derived, steps, farkas(derived + list(cons))

    derived, steps, lam = attempt(cands)
    if lam is None:
        return None
    # `derived` is newest first: cut `t` of `cands` is `derived[len(cands) - 1 - t]`.
    used = [c for t, c in enumerate(cands) if lam[len(cands) - 1 - t] != 0]
    derived, steps, lam = attempt(used)
    assert lam is not None
    steps.append((lam, 0))
    return {"steps": steps}


def certify(fns):
    certs, failing = {}, []
    for fid, (_, obs) in fns.items():
        certs[fid] = []
        for i, p in enumerate(obs):
            lam = farkas(p)
            if lam is None:
                lam = cg_cert(p)
            if lam is None:
                lam = cg_combo_cert(p)
            if lam is None:
                failing.append((fid, i))
            certs[fid].append(lam)
    return certs, failing


def search(blob):
    """R1-style annotation search (see the module docstring)."""
    pre = {}
    fns = dump(blob, pre)
    certs, failing = certify(fns)
    for _ in range(8):
        if not failing:
            return pre, fns, certs
        best = None
        for fid, i in failing:
            if fid in pre:
                continue
            nparams = len(fns[fid][0])
            for co, b in fns[fid][1][i]:
                if len(co) <= nparams and any(co):
                    trial = dict(pre)
                    trial[fid] = [([-x for x in co], -b - 1)]
                    tf = dump(blob, trial)
                    tc, tfail = certify(tf)
                    if any(f == fid for f, _ in tfail):
                        continue
                    if len(tfail) < len(failing) and (best is None or len(tfail) < len(best[2])):
                        best = (trial, tf, tfail, tc)
        if best is None:
            return pre, fns, None
        pre, fns, failing, certs = best
    return pre, fns, None


def witness(params, pre):
    """Arguments meeting `pre`: each parameter tried at 0, 1, 2 (enough for
    the single-constraint preconditions the search proposes)."""
    import itertools
    for vals in itertools.product([0, 1, 2], repeat=len(params)):
        if all(sum(c * vals[i] for i, c in enumerate(co) if i < len(vals)) <= b for co, b in pre):
            args = []
            for t, v in zip(params, vals):
                if t == "b":
                    if v > 1:
                        break
                    args.append(".bool %s" % ("true" if v else "false"))
                else:
                    args.append(".int %s %d" % (INT_TY[int(t[1:])], v))
            else:
                return "[%s]" % ", ".join(args)
    return None


# `SemR.IntTy.code` order.
INT_TY = [".i8", ".i16", ".i32", ".i64", ".i128", ".isize", ".u8", ".u16", ".u32", ".u64", ".u128", ".usize"]


HEADER = """/-
  {name} — GENERATED by `scripts/vf5_f1_producer.py` from `blobs/`; a hand edit is
  drift (`--check`).

{body}
-/
import {imp}

set_option maxRecDepth 100000

namespace {name}

open SemR VF5
"""


def valid_cert(cons, lam) -> bool:
    n = max(len(co) for co, _ in cons)
    if any(x < 0 for x in lam):
        return False
    if any(sum(lam[j] * (cons[j][0][i] if i < len(cons[j][0]) else 0) for j in range(len(cons))) != 0
           for i in range(n)):
        return False
    return sum(lam[j] * cons[j][1] for j in range(len(cons))) < 0


def mutate_certs(fns, certs):
    """The certificates with one multiplier of one obligation's certificate
    changed so that the combination no longer closes."""
    for fid in sorted(certs):
        for i, lam in enumerate(certs[fid]):
            if not isinstance(lam, list):
                continue
            cons = fns[fid][1][i]
            for j in range(len(lam)):
                for delta in (1, -1):
                    lam2 = list(lam)
                    lam2[j] += delta
                    if lam2[j] >= 0 and not valid_cert(cons, lam2):
                        out = {f: list(v) for f, v in certs.items()}
                        out[fid] = list(out[fid])
                        out[fid][i] = lam2
                        return out, (fid, i, j, lam[j], lam2[j])
    raise SystemExit("no certificate mutation breaks a certificate")


def divisor_offset(blob) -> int:
    """The byte of the call site's divisor: `const u32 5` (`Inst` tag 25, `Ty`
    tag 7, `Constant` tag 0, then the 16-byte little-endian literal)."""
    pat = [25, 7, 0, 5] + [0] * 15
    hits = [i for i in range(len(blob) - len(pat)) if blob[i:i + len(pat)] == pat]
    assert len(hits) == 1, hits
    return hits[0] + 3


def rows_module():
    rows = []
    for line in (BLOBS / "rows.tsv").read_text().splitlines():
        if line.startswith("#") or not line.strip():
            continue
        rows.append(line.split("\t"))
    out = [HEADER.format(name="VF5Rows", imp="VF5Enum", body=(
        "  Each `blob_*` is the trust-ir crate module the stage-2 compiler wrote for one\n"
        "  VF3-census test (`-Ztrust-dump=ir:`), byte for byte (`blobs/`). `checks_*` is\n"
        "  the kernel evaluating `checkBlob`: SemR decodes the blob, F1's `vc` runs\n"
        "  under the annotation `A_*` (untrusted, searched by the producer), and VF4's\n"
        "  `chk_LIA_cases` checks every certificate. Each `row_*` is a \"proved\n"
        "  (calculus)\" row, `RowProved blob A fid sym`: the function is the artifact's\n"
        "  `sym_*` (its own symbol), the module's roots carry no precondition and every\n"
        "  annotated function is reachable from one (`rowShape`, decided by `rfl`). Each\n"
        "  `pre_*` is a kernel-checked witness that a precondition the annotation states\n"
        "  is satisfiable; there is one per annotated function."))]
    report = []
    for key in sorted({r[0] for r in rows}):
        mine = [r for r in rows if r[0] == key]
        blob = list((BLOBS / mine[0][1]).read_bytes())
        pre, fns, certs = search(blob)
        if certs is None:
            report.append(f"{key}\tno-certificate\t{json.dumps(pre)}")
            continue
        names, roots, entries = meta(blob, pre)
        assert entries, f"{key}: the entry premise fails under {pre} (roots {roots})"
        out.append(f"\n/-- `blobs/{mine[0][1]}`, {len(blob)} bytes. -/\n"
                   f"def blob_{key} : List Nat :=\n  {lean_bytes(blob)}\n")
        out.append(f"def A_{key} : Nat → List Cons := {lean_annot(pre)}\n")
        out.append(f"def certs_{key} : List (Nat × List (List ChkLIA.Step)) :=\n  {lean_certs(certs)}\n")
        nob = sum(len(v) for v in certs.values())
        out.append(f"/-- Every obligation of every function ({nob}) is refuted. -/\n"
                   f"theorem checks_{key} : checkBlob blob_{key} A_{key} certs_{key} = true := rfl\n")
        mcerts, (mf, mi, mj, was, now) = mutate_certs(fns, certs)
        out.append(f"/-- The certificates with multiplier {mj} of function {mf}'s obligation {mi} changed\n"
                   f"    from {was} to {now}: the combination no longer closes. -/\n"
                   f"def certs_mut_{key} : List (Nat × List (List ChkLIA.Step)) :=\n  {lean_certs(mcerts)}\n"
                   f"theorem refused_cert_{key} : checkBlob blob_{key} A_{key} certs_mut_{key} = false := rfl\n")
        off = divisor_offset(blob)
        out.append(f"/-- The artifact with byte {off} (the call site's divisor `5`) set to `0`: the call\n"
                   f"    misses the callee's precondition, so the same certificates no longer check. -/\n"
                   f"theorem refused_zero_divisor_{key} :\n"
                   f"    checkBlob (setNth blob_{key} {off} 0) A_{key} certs_{key} = false := rfl\n")
        for fid in sorted(pre):
            w = witness(fns[fid][0], pre[fid])
            assert w is not None, (key, fid)
            out.append(f"/-- Function {fid}'s precondition is satisfiable. -/\n"
                       f"theorem pre_{key}_{fid} : preWitness blob_{key} A_{key} {fid} {w} = true := rfl\n")
        for r in mine:
            name, fid, what = r[2], int(r[3]), r[4]
            out.append(lean_sym(name, names[fid]))
            out.append(f"/-- {what} -/\ntheorem row_{name} : RowProved blob_{key} A_{key} {fid} sym_{name} :=\n"
                       f"  row_of checks_{key} rfl\n")
            premise = premise_of(pre, fid, roots, names)
            report.append(f"{key}\t{name}\t{fid}\t{names[fid].decode()}\tproved (calculus)\t"
                          f"{json.dumps({str(k): v for k, v in pre.items()})}\t{premise}\t{nob}")
    d2b_text, d2b_report = d2b_rows()
    out.append(d2b_text)
    report.append("# D-2(b): fieldless enums (not VF3-census rows) and B3's positional check")
    report.extend(d2b_report)
    aterm_text, aterm_report = aterm_rows()
    out.append(aterm_text)
    report.append("# aterm's PM-1-free F1 rows (aterm docs/PLAN-tests-to-specs-2026-10-15.md), from a mirror")
    report.extend(aterm_report)
    out.append("\nend VF5Rows\n")
    return "".join(out), report


def premise_of(pre, fid, roots, names) -> str:
    """The row's precondition column: none, or the closed-world premise the
    kernel cannot check (every root carries none and every annotated function
    is reachable from one: that much it checks)."""
    if not pre:
        return "pre=none"
    annotated = ",".join(names[f].decode() for f in sorted(pre))
    rs = ",".join(names[r].decode() for r in roots)
    mine = "annotated" if fid in pre else "unannotated"
    return (f"pre=closed-world (this function {mine}; annotated: {annotated}; roots, unannotated: {rs}; "
            f"premise: no caller outside the module enters an annotated function)")


# rustc's `usize` discriminant type is `u64` in the artifact's enum record (SemR's κ is 64-bit,
# read from the target record; the compiler writes a `repr(usize)` tag as `repr(u64)`), so B3
# reads rustc's `usize` as `u64`.
REPR = {"u8": "(some .u8)", "u16": "(some .u16)", "u32": "(some .u32)", "u64": "(some .u64)",
        "usize": "(some .u64)",
        "i8": "(some .i8)", "i16": "(some .i16)", "i32": "(some .i32)", "i64": "(some .i64)",
        "isize": "none"}
# The D-2(b) module is larger (18 functions, 2.4 KB): its decided statements are checked by
# the kernel's evaluation directly (`decide +kernel`: `of_decide_eq_true (Eq.refl true)`, no
# elaborator unfolding, no `Lean.ofReduceBool`).
KDEC = "by decide +kernel"


def lean_pos(ds) -> str:
    return "[%s]" % ", ".join("(%d, %d)" % (i, d) for i, d in enumerate(ds))


def find_once(blob, pat) -> int:
    hits = [i for i in range(len(blob) - len(pat) + 1) if blob[i:i + len(pat)] == pat]
    assert len(hits) == 1, (pat[:4], hits)
    return hits[0]


def disc_entries(ds):
    """The wire image of explicit discriminants: count, then `1, i128 LE` each."""
    out = [len(ds)]
    for d in ds:
        out += [1] + list((d % (1 << 128)).to_bytes(16, "little"))
    return out


def d2b_rows():
    """D-2(b): the fieldless-enum artifact's rows, and B3 against rustc's reader."""
    d2b = BLOBS / "d2b"
    rows = [l.split("\t") for l in (BLOBS / "d2b.tsv").read_text().splitlines()
            if l.strip() and not l.startswith("#")]
    blob = list((BLOBS / rows[0][1]).read_bytes())
    pre, fns, certs = search(blob)
    if certs is None or pre:
        sys.exit(f"d2b: expected every obligation certified with no annotation, got {pre}")
    nob = sum(len(v) for v in certs.values())
    out = [f"\n/-! ## D-2(b): fieldless enums by value (`blobs/d2b/`) -/\n",
           f"\n/-- `blobs/{rows[0][1]}`, {len(blob)} bytes. -/\ndef blob_fieldless : List Nat :=\n  {lean_bytes(blob)}\n",
           f"def certs_fieldless : List (Nat × List (List ChkLIA.Step)) :=\n  {lean_certs(certs)}\n",
           f"/-- Every obligation of every function ({nob}) is refuted; the entry forks every enum\n"
           f"    parameter per variant (Rust's validity invariant). -/\n"
           f"theorem checks_fieldless : checkBlob blob_fieldless (annot []) certs_fieldless = true :=\n  {KDEC}\n"]
    report = []
    names, roots, entries = meta(blob, pre)
    assert entries, "d2b: the entry premise fails"
    ids = {l.split("\t")[0]: int(l.split("\t")[1]) for l in (d2b / "b3_ids.tsv").read_text().splitlines()
           if l.strip() and not l.startswith("#")}
    rustc = {}
    for l in (d2b / "b3_rustc.tsv").read_text().splitlines():
        name, ty, ds = l.split("\t")
        rustc[name] = (ty, [int(x) for x in ds.strip("[]").split(",")])
    table = ",\n   ".join(f"({ids[n]}, {lean_pos(rustc[n][1])}, {REPR[rustc[n][0]]})"
                          for n in sorted(ids, key=ids.get))
    out.append("/-- B3's table: per enum of the artifact, rustc's positional discriminants and\n"
               "    explicit `repr` (`blobs/d2b/b3_rustc.tsv`, by the ids of `b3_ids.tsv`). -/\n"
               f"def b3_table : List B3Entry :=\n  [{table}]\n"
               "/-- B3 holds for every enum of the artifact: each D-2(b) row carries it. -/\n"
               f"theorem b3all_fieldless : checkB3All blob_fieldless b3_table = true :=\n  {KDEC}\n")
    for r in rows:
        name, fid, what = r[2], int(r[3]), r[4]
        out.append(lean_sym(name, names[fid]))
        out.append(f"/-- {what} -/\ntheorem row_{name} : RowProvedB3 blob_fieldless (annot []) {fid} sym_{name} b3_table :=\n"
                   f"  rowB3_of checks_fieldless ({KDEC}) b3all_fieldless\n")
        report.append(f"fieldless\t{name}\t{fid}\t{names[fid].decode()}\tproved (calculus) + B3\t{{}}\t"
                      f"{premise_of(pre, fid, roots, names)}\t{nob}")
    out.append("/-- The validity premise is load-bearing: `headroom` on a `ContainmentMode` whose tag is\n"
               "    255 (no variant's) overflows `255 + 1` and panics. `Valid_R` and `ClosedSafe`\n"
               "    quantify over valid values only, as Rust guarantees them. -/\n"
               f"theorem d2b_invalid_tag_panics : runBad blob_fieldless 4 [.enum 0 [.int .u8 255]] = true :=\n"
               f"  {KDEC}\n")
    out.append("\n/-! ### B3: the artifact's positional discriminants are rustc's (P1–P5) -/\n")
    for name in sorted(ids, key=ids.get):
        ty, ds = rustc[name]
        out.append(f"/-- P5: `{name}` (rustc: `{ty}`, {ds}). -/\n"
                   f"theorem b3_{name} : checkB3 blob_fieldless {ids[name]} {lean_pos(ds)} {REPR[ty]} = true :=\n  {KDEC}\n")
        report.append(f"fieldless\tb3_{name}\t{ids[name]}\tB3 positional = rustc\t{ty}\t{ds}")
    # P4: each refused (stated `= false`; the test flips each and requires a refusal).
    cm, o3, sp = rustc["ContainmentMode"][1], rustc["Ordering3"][1], rustc["Sparse"][1]
    neg = [
        ("swap_safety_user", ids["ContainmentMode"], [cm[0], cm[2], cm[1]], "(some .u8)", "blob_fieldless",
         "`ContainmentMode` with `Safety`/`User` swapped"),
        ("swap_less_greater", ids["Ordering3"], [o3[2], o3[1], o3[0]], "(some .i8)", "blob_fieldless",
         "`Ordering3` (`cmp::Ordering`'s -1, 0, 1) with `Less`/`Greater` swapped"),
        ("index_not_disc", ids["Sparse"], [0, 1], "none", "blob_fieldless",
         "`Sparse { A = 5, B = 9 }` read as variant indices (the t216 shape)"),
        ("repr_mismatch", ids["ContainmentMode"], cm, "(some .i8)", "blob_fieldless",
         "`repr(u8)` read as `i8`"),
    ]
    # The producer mutants: the artifact itself rewritten.
    # the discriminant entries, then the repr byte (`1` = u8 for `ContainmentMode`, `0` = none)
    off = find_once(blob, disc_entries(cm) + [1]) + 1
    # each entry is a tag byte then 16 value bytes: entry j's low value byte is off + 17 j + 1
    o1, o2 = off + 18, off + 35
    swapped = f"(setNth (setNth blob_fieldless {o1} {cm[2] % 256}) {o2} {cm[1] % 256})"
    neg.append(("artifact_swap", ids["ContainmentMode"], cm, "(some .u8)", swapped,
                f"an artifact whose `ContainmentMode` writes `Safety = 2`, `User = 1` (bytes {o1}, {o2}): "
                f"a swap the code could use consistently, refused positionally"))
    offs = find_once(blob, disc_entries(sp) + [0]) + 1
    s1, s2 = offs + 1, offs + 18
    indexed = f"(setNth (setNth blob_fieldless {s1} 0) {s2} 1)"
    neg.append(("artifact_index_tags", ids["Sparse"], sp, "none", indexed,
                f"an artifact whose producer wrote `Sparse`'s variant indices for its discriminants "
                f"(bytes {s1}, {s2})"))
    for tag, eid, ds, repr, bs, what in neg:
        out.append(f"/-- P4, refused: {what}. -/\n"
                   f"theorem b3_refused_{tag} : checkB3 {bs} {eid} {lean_pos(ds)} {repr} = false :=\n  {KDEC}\n")
        report.append(f"fieldless\tb3_refused_{tag}\t{eid}\tB3 refuses\t{what}")
    # The mutated artifacts still decode, to the mutated assignment: the refusals above
    # are B3's, not the decoder's.
    out.append(f"/-- The swapped artifact decodes, to `Safety = 2`, `User = 1`. -/\n"
               f"theorem b3_reads_artifact_swap : checkB3 {swapped} {ids['ContainmentMode']} "
               f"{lean_pos([cm[0], cm[2], cm[1]])} (some .u8) = true :=\n  {KDEC}\n")
    out.append(f"/-- The index-tagged artifact decodes, to `A = 0`, `B = 1`. -/\n"
               f"theorem b3_reads_artifact_index_tags : checkB3 {indexed} {ids['Sparse']} "
               f"{lean_pos([0, 1])} none = true :=\n  {KDEC}\n")
    # The D-2(b) rows carry B3: the swapped artifact's obligations are certified by the
    # same certificates (the code uses the swapped tags consistently), but no row of it
    # is minted, because B3 over the whole artifact refuses it.
    out.append(f"/-- The swapped artifact's obligations check with the honest certificates: the\n"
               f"    calculus alone cannot tell the swap. -/\n"
               f"theorem checks_artifact_swap : checkBlob {swapped} (annot []) certs_fieldless = true :=\n"
               f"  {KDEC}\n")
    for tag, bs in [("artifact_swap", swapped), ("artifact_index_tags", indexed)]:
        out.append(f"/-- B3 over the whole artifact refuses it, so no D-2(b) row of it exists. -/\n"
                   f"theorem b3all_refused_{tag} : checkB3All {bs} b3_table = false :=\n  {KDEC}\n")
        report.append(f"fieldless\tb3all_refused_{tag}\t-\tB3 (whole artifact) refuses\t{tag}")
    return "".join(out), report


def aterm_rows():
    """aterm's "PM-1-free, F1" rows: the stage-1 compiler's artifact of a mirror crate whose
    bodies are the aterm functions' verbatim (`blobs/aterm/f1_rows.rs`). Every function is a
    root, so every row is proved with no annotation (`pre=none`)."""
    rows = [l.split("\t") for l in (BLOBS / "aterm.tsv").read_text().splitlines()
            if l.strip() and not l.startswith("#")]
    blob = list((BLOBS / rows[0][1]).read_bytes())
    pre, fns, certs = search(blob)
    if certs is None or pre:
        sys.exit(f"aterm: expected every obligation certified with no annotation, got {pre}")
    nob = sum(len(v) for v in certs.values())
    names, roots, entries = meta(blob, pre)
    assert entries, "aterm: the entry premise fails"
    out = [f"\n/-! ## aterm's PM-1-free F1 rows (`blobs/aterm/`) -/\n",
           f"\n/-- `blobs/{rows[0][1]}`, {len(blob)} bytes. -/\ndef blob_aterm : List Nat :=\n  {lean_bytes(blob)}\n",
           f"def certs_aterm : List (Nat × List (List ChkLIA.Step)) :=\n  {lean_certs(certs)}\n",
           f"/-- Every obligation of every function ({nob}) is refuted, with no annotation (the\n"
           f"    artifact is large, so by the kernel's evaluation directly, as D-2(b)'s). -/\n"
           f"theorem checks_aterm : checkBlob blob_aterm (annot []) certs_aterm = true :=\n  {KDEC}\n"]
    mcerts, (mf, mi, mj, was, now) = mutate_certs(fns, certs)
    out.append(f"/-- The certificates with multiplier {mj} of function {mf}'s obligation {mi} changed\n"
               f"    from {was} to {now}: the combination no longer closes. -/\n"
               f"def certs_mut_aterm : List (Nat × List (List ChkLIA.Step)) :=\n  {lean_certs(mcerts)}\n"
               f"theorem refused_cert_aterm : checkBlob blob_aterm (annot []) certs_mut_aterm = false :=\n  {KDEC}\n")
    report = []
    for r in rows:
        name, fid, what = r[2], int(r[3]), r[4]
        out.append(lean_sym(name, names[fid]))
        out.append(f"/-- {what} -/\ntheorem row_{name} : RowProved blob_aterm (annot []) {fid} sym_{name} :=\n"
                   f"  row_of checks_aterm ({KDEC})\n")
        report.append(f"aterm\t{name}\t{fid}\t{names[fid].decode()}\tproved (calculus)\t{{}}\t"
                      f"{premise_of(pre, fid, roots, names)}\t{nob}")
    return "".join(out), report


# (blob, theorem prefix, the calculus, function, arguments, the bad run). `mutSign` reads all
# four signed comparisons unsigned; each `mutSignAt` reads one, and has its own witness, compiled
# so that the one comparison guards the overflowing `x - 100`.
MUTANTS = [
    ("mut_wrap", "mutWrap", "mutWrap", 0, "[.int .u8 200, .int .u8 100]",
     "`add_u8(200, 100)` panics: attempt to add with overflow"),
    ("mut_sign", "mutSign", "mutSign", 0, "[.int .i8 227]",
     "`below(-29)` panics: attempt to subtract with overflow (`-29 - 100 < -128`)"),
    ("mut_sign", "mutSignAt_slt", "(mutSignAt .slt)", 0, "[.int .i8 227]",
     "`below(-29)` (`x < 0` guards `x - 100`) panics: attempt to subtract with overflow"),
    ("mut_sign_le", "mutSignAt_sle", "(mutSignAt .sle)", 0, "[.int .i8 227]",
     "`below_le(-29)` (`x <= 0` guards `x - 100`) panics: attempt to subtract with overflow"),
    ("mut_sign_gt", "mutSignAt_sgt", "(mutSignAt .sgt)", 0, "[.int .i8 227]",
     "`below_gt(-29)` (`x > 0` false runs `x - 100`) panics: attempt to subtract with overflow"),
    ("mut_sign_ge", "mutSignAt_sge", "(mutSignAt .sge)", 0, "[.int .i8 227]",
     "`below_ge(-29)` (`x >= 1` false runs `x - 100`) panics: attempt to subtract with overflow"),
]
TWINS = ("twins", [(0, "add_twin"), (1, "below_twin")])
# The entry premise's controls: an annotation on the reproducer's root (`add_u8` and `below`,
# which nothing in their modules calls). Satisfiable (`a ≤ 100 ∧ b ≤ 100`) or vacuous
# (`0 ≤ -1`), it certifies every obligation, yet `rowShape` refuses the row: a root carries no
# precondition.
PROBES = [
    ("wrap", "mut_wrap", 0, {0: [([1, 0], 100), ([0, 1], 100)]}, "[.int .u8 0, .int .u8 0]",
     "`a ≤ 100 ∧ b ≤ 100` on `add_u8` (satisfiable), the soundness review's probe"),
    ("sign_vacuous", "mut_sign", 0, {0: [([0], -1)]}, None,
     "`0 ≤ -1` on `below` (vacuous)"),
]


def mutants_module():
    out = [HEADER.format(name="VF5MutantRows", imp="VF5Mutants", body=(
        "  Each mutant calculus is refuted on a compiled blob: the kernel accepts a\n"
        "  certificate for every obligation the mutant emits (the mutant would call the\n"
        "  program safe) and evaluates SemR's run to a panic. The same run shows the\n"
        "  program unsafe, so F1's sound calculus must leave an obligation of it\n"
        "  unrefuted. `mutSignAt o` reads only the signed comparison `o` unsigned; each\n"
        "  has its own witness. The twins are the corrected programs, proved by F1's\n"
        "  calculus. The probes: an annotation on a reproducer's root certifies its\n"
        "  obligations, and `rowShape` refuses the row."))]
    report = []
    blobs_done = set()
    for blob_name, tname, calc, fid, argv, why in MUTANTS:
        blob = list((BLOBS / f"{blob_name}.bin").read_bytes())
        certs, failing = certify(dump(blob, {}, calc=calc))
        if failing:
            sys.exit(f"{blob_name}: the mutant {calc} leaves obligations unrefuted: {failing}")
        _, std_failing = certify(dump(blob, {}))
        assert std_failing, f"{blob_name}: F1's calculus certifies an unsafe program"
        n = sum(len(v) for v in certs.values())
        if blob_name not in blobs_done:
            blobs_done.add(blob_name)
            out.append(f"\n/-- `blobs/{blob_name}.bin`, {len(blob)} bytes. -/\n"
                       f"def blob_{blob_name} : List Nat :=\n  {lean_bytes(blob)}\n")
            out.append(f"/-- The reproducer is unsafe; F1's calculus leaves {len(std_failing)} obligation(s) of it\n"
                       f"    with no certificate. -/\n"
                       f"theorem {blob_name}_unsafe : ∀ m, decode blob_{blob_name} = .ok m → ¬ ClosedSafe m (annot []) :=\n"
                       f"  unsafeBlob (fid := {fid}) (args := {argv}) (fuel := 1000) (depth := 64) rfl\n")
        out.append(f"/-- The mutant `{calc}` refutes every obligation it emits ({n}). -/\n"
                   f"theorem {tname}_checks : checkBlobC {calc} blob_{blob_name} (annot []) {lean_certs(certs)} = true := rfl\n")
        out.append(f"/-- {why}. -/\ntheorem {tname}_bad : badRunBlob blob_{blob_name} (annot []) {fid} {argv} 1000 64 = true := rfl\n")
        out.append(f"/-- **`{calc}` is unsound.** -/\ntheorem {tname}_refuted : ¬ CalcSound {calc} :=\n"
                   f"  refuteBlob {tname}_checks {tname}_bad\n")
        report.append(f"{blob_name}\t{tname}\trefuted\t{n} mutant obligation(s) certified\t{len(std_failing)} unrefuted by F1")
    for tag, blob_name, fid, pre, w, why in PROBES:
        blob = list((BLOBS / f"{blob_name}.bin").read_bytes())
        fns = dump(blob, pre)
        certs, failing = certify(fns)
        assert not failing, (tag, failing)
        names, roots, entries = meta(blob, pre)
        assert fid in roots and not entries, (tag, roots, entries)
        out.append(f"\n/-! ### Probe `{tag}`: {why} -/\n"
                   f"def A_probe_{tag} : Nat → List Cons := {lean_annot(pre)}\n"
                   + lean_sym(f"probe_{tag}", names[fid]) +
                   f"/-- Every obligation checks under the root's annotation: the old row's evidence. -/\n"
                   f"theorem probe_{tag}_checks : checkBlob blob_{blob_name} A_probe_{tag} "
                   f"{lean_certs(certs)} = true := rfl\n")
        if w is not None:
            out.append(f"/-- The annotation is satisfiable. -/\n"
                       f"theorem probe_{tag}_pre : preWitness blob_{blob_name} A_probe_{tag} {fid} {w} = true := rfl\n")
        out.append(f"/-- **Refused**: the function is a root of its module, so no row carries an annotation\n"
                   f"    on it. -/\n"
                   f"theorem refused_row_probe_{tag} : rowShape blob_{blob_name} A_probe_{tag} {fid} sym_probe_{tag} = false := rfl\n")
        report.append(f"{blob_name}\tprobe_{tag}\trow refused (a root carries a precondition)\t{why}")
    blob_name, named = TWINS
    blob = list((BLOBS / f"{blob_name}.bin").read_bytes())
    certs, failing = certify(dump(blob, {}))
    assert not failing, failing
    names, roots, entries = meta(blob, {})
    assert entries
    out.append(f"\n/-- `blobs/{blob_name}.bin`, {len(blob)} bytes: the reproducers' corrected twins. -/\n"
               f"def blob_{blob_name} : List Nat :=\n  {lean_bytes(blob)}\n")
    out.append(f"theorem checks_{blob_name} : checkBlob blob_{blob_name} (annot []) {lean_certs(certs)} = true := rfl\n")
    for fid, name in named:
        out.append(lean_sym(name, names[fid]))
        out.append(f"theorem row_{name} : RowProved blob_{blob_name} (annot []) {fid} sym_{name} :=\n"
                   f"  row_of checks_{blob_name} rfl\n")
        report.append(f"{blob_name}\t{name}\t{names[fid].decode()}\tproved (calculus)")
    out.append("\nend VF5MutantRows\n")
    return "".join(out), report


# VF7 (docs/DECISIONS.md R206): the aterm spec harnesses' rows, the three mutant calculi
# refuted on their compiled witnesses, and the witnesses' corrected twins.
VF7_MUTANTS = [
    ("mut_ashr", "mutAshr", "ashr_div", "[.int .i32 4294967295]",
     "`ashr_div(-1)` panics: attempt to divide by zero (`-1 >> 31` is `-1`, `+ 1` is `0`)"),
    ("mut_xor", "mutXor", "xor_div", "[.int .u8 1]",
     "`xor_div(1)` panics: attempt to divide by zero (`1 ^ 1` is `0`)"),
    ("mut_trunc", "mutTrunc", "trunc_div", "[.int .u32 256]",
     "`trunc_div(256)` panics: attempt to divide by zero (`256 as u8` is `0`)"),
]


# The harness form is not vacuous: per row with a harness, a FALSE clause's harness
# (`blobs/vf7/<stem>.rs`; the first two share `aterm_bv_wrong.rs`), its counterexample, and why.
VF7_WRONG = [
    ("aterm_bv_wrong", "exited_zero_wrong", "[.int .i32 128]",
     "`exited_zero_wrong(128)` panics: the clause read with `% 256` is false at 128"),
    ("aterm_bv_wrong", "does_token_fit_wrong", "[.int .u8 240]",
     "`does_token_fit_wrong(0xF0)` panics: the clause read with `< 16` is false at 0xF0"),
    ("wrong_h6_of_hash", "h6_of_hash_wrong", "[.int .u64 18446744073709551615]",
     "`h6_of_hash_wrong(u64::MAX)` panics: the clause with the bound `<= 16777214` is false "
     "at `u64::MAX`"),
    ("wrong_level_bit", "level_bit_wrong", "[.int .u16 32]",
     "`level_bit_wrong(32)` panics: the clause's power-of-two branch reaching `depth < 33` is "
     "false at 32"),
    ("wrong_dir_safe_for_private_write", "dir_safe_for_private_write_wrong",
     "[.int .u32 0, .int .u32 0, .int .u32 2]",
     "`dir_safe_for_private_write_wrong(0, 0, 2)` panics: the clause reading the other-write "
     "bit as `/ 4` is false at mode 2"),
    ("wrong_safe_mode", "safe_mode_wrong", "[.int .u32 64, .bool false]",
     "`safe_mode_wrong(64, false)` panics: the clause without the owner execute bit `0o100` "
     "is false at mode 64"),
    ("wrong_creation_flags", "creation_flags_wrong", "[CF_QUIET, .int .u32 0, .bool false]",
     "`creation_flags_wrong(Quiet, 0, false)` panics: the clause with k(Quiet, false) = "
     "DETACHED_PROCESS is false there (and `creation_flags` has no certificate to change)"),
]
# Every row of `blobs/vf7/rows.tsv` has a false-clause control above.
VF7_WRONG_ROWS = {"exited_zero", "does_token_fit", "h6_of_hash", "level_bit",
                  "dir_safe_for_private_write", "safe_mode", "creation_flags"}


def bad_run(blob, fid: int, argv: str) -> bool:
    """`badRunBlob blob (annot []) fid argv 1000 64`, evaluated by Lean: the producer
    checks the counterexample before it writes the theorem the kernel decides."""
    src = "\n".join([
        "import VF5Mutants",
        "open SemR VF5",
        "set_option maxRecDepth 100000",
        "def blob : List Nat := " + lean_bytes(blob),
        f"#eval badRunBlob blob (annot []) {fid} {argv} 1000 64",
        ""])
    path = BUILD / "BadRun.lean"
    path.write_text(src)
    out = subprocess.run([str(lean_bin()), "BadRun.lean"], cwd=BUILD, capture_output=True, text=True,
                         env=dict(os.environ, LEAN_PATH=str(BUILD)))
    if out.returncode != 0:
        sys.exit("lean BadRun.lean failed:\n" + out.stdout + out.stderr)
    return out.stdout.strip() == "true"


def fid_of(names, fn: str) -> int:
    """The function whose v0 symbol ends in `fn`'s identifier."""
    tag = f"{len(fn)}{fn}".encode()
    hits = [f for f, n in names.items() if n.endswith(tag)]
    assert len(hits) == 1, (fn, hits)
    return hits[0]


def spec_rows(d: Path, rel: str, rows, wrong, lit_of):
    """The spec harnesses' rows over `blobs/<rel>/` (VF7's and aterm's): per row of
    `rows` (key, harness function, aterm source, clause), `checks_<key>` over
    `bv_<key>.bin`, `refused_cert_<key>`, `sym_<key>` and `row_<key>`; per entry of
    `wrong` (stem, function, row key, counterexample, why), `<fn>_unsafe` over
    `<stem>.bin` and `<key>_spec_runs_at_cex`."""
    out, report = [], []
    # One artifact per row (`bv_<key>.rs`: the function and its harness), so each check
    # stays within the reference entry's per-declaration heartbeat budget.
    rowinfo = {}
    for key, fn, src, spec in rows:
        blob = list((d / f"bv_{key}.bin").read_bytes())
        fns = dump(blob, {})
        certs, failing = certify(fns)
        if failing:
            sys.exit(f"{rel} {key}: obligations with no certificate: {failing}")
        names, roots, entries = meta(blob, {})
        assert entries
        nob = sum(len(v) for v in certs.values())
        ncg = sum(1 for v in certs.values() for c in v if isinstance(c, dict))
        out.append(f"\n/-- `blobs/{rel}/bv_{key}.bin`, {len(blob)} bytes. -/\n"
                   f"def blob_{key} : List Nat :=\n  {lean_bytes(blob)}\n")
        out.append(f"def certs_{key} : List (Nat × List (List ChkLIA.Step)) :=\n  {lean_certs(certs)}\n")
        out.append(f"/-- Every obligation of every function ({nob}; {ncg} by a cutting plane) is refuted. -/\n"
                   f"theorem checks_{key} : checkBlob blob_{key} (annot []) certs_{key} = true :=\n  {KDEC}\n")
        if nob:
            mcerts, (mf, mi, mj, was, now) = mutate_certs(fns, certs)
            out.append(f"/-- The certificates with multiplier {mj} of function {mf}'s obligation {mi} changed\n"
                       f"    from {was} to {now}: the combination no longer closes. -/\n"
                       f"def certs_mut_{key} : List (Nat × List (List ChkLIA.Step)) :=\n  {lean_certs(mcerts)}\n"
                       f"theorem refused_cert_{key} : checkBlob blob_{key} (annot []) certs_mut_{key} = false :=\n"
                       f"  {KDEC}\n")
        else:
            # No obligation is left: the calculus decides every path syntactically (every
            # comparison's other cases contradict the path outright). Its control: the
            # checks with one certificate too many are refused (the lengths must agree).
            out.append(f"/-- The checks with one (empty) certificate too many are refused. -/\n"
                       f"theorem refused_cert_{key} : checkBlob blob_{key} (annot []) "
                       f"(certs_{key}.map fun p => (p.1, [] :: p.2)) = false :=\n  {KDEC}\n")
        fid = fid_of(names, fn)
        rowinfo[key] = (blob, fid)
        out.append(lean_sym(key, names[fid]))
        out.append(f"/-- {spec} (`{src}`). -/\n"
                   f"theorem row_{key} : RowProved blob_{key} (annot []) {fid} sym_{key} :=\n"
                   f"  row_of checks_{key} ({KDEC})\n")
        report.append(f"bv_{key}\t{key}\t{fid}\t{names[fid].decode()}\tproved (calculus)\t{{}}\tpre=none\t{nob}\t{src}")
    # The harness form is not vacuous: a FALSE clause's harness panics at its
    # counterexample, and F1's calculus leaves an obligation of it unrefuted.
    assert sorted(r[0] for r in rows) == sorted(w[2] for w in wrong), \
        f"{rel}: every row has one false-clause control"
    seen = {}
    for stem, fn, key, argv, why in wrong:
        lit = lit_of(stem)
        if stem not in seen:
            wb = list((d / f"{stem}.bin").read_bytes())
            wnames, _, _ = meta(wb, {})
            seen[stem] = (wb, wnames, dump(wb, {}))
            out.append(f"\n/-- `blobs/{rel}/{stem}.bin`, {len(wb)} bytes: harnesses whose clause is "
                       f"false. -/\ndef {lit} : List Nat :=\n  {lean_bytes(wb)}\n")
        wb, wnames, wfns = seen[stem]
        fid = fid_of(wnames, fn)
        _, wfail = certify({fid: wfns[fid]})
        assert wfail, f"{fn}: F1's calculus certifies a false clause"
        argv = argv.replace("CF_QUIET", ".enum 0 [.int .u8 0]")
        assert bad_run(wb, fid, argv), f"{fn}: SemR's run at {argv} is not bad"
        out.append(f"/-- {why}; F1's calculus leaves {len(wfail)} obligation(s) of it with no certificate. -/\n"
                   f"theorem {fn}_unsafe : ∀ m, decode {lit} = .ok m → ¬ ClosedSafe m (annot []) :=\n"
                   f"  unsafeBlob (fid := {fid}) (args := {argv}) (fuel := 1000) (depth := 64) ({KDEC})\n")
        report.append(f"{stem}\t{fn}\tunsafe\t{why}\t{len(wfail)} unrefuted by F1")
        # The control's control: the row's own harness runs clean at the same input, so the
        # panic above is the false clause's, not the copied body's.
        rb, rfid = rowinfo[key]
        assert not bad_run(rb, rfid, argv), f"{key}: the true harness panics at {argv}"
        out.append(f"/-- The row's own harness does not panic at the same input. -/\n"
                   f"theorem {key}_spec_runs_at_cex : badRunBlob blob_{key} (annot []) {rfid} {argv} 1000 64 "
                   f"= false :=\n  {KDEC}\n")
    return out, report


def vf7_module():
    out = [HEADER.format(name="VF7Rows", imp="VF5MutantRows", body=(
        "  VF7, first slice (docs/DECISIONS.md R206): F1's calculus reads integer `&`, `|`,\n"
        "  `^`, shifts by a known or an unknown amount, narrowing casts and unsigned\n"
        "  division or remainder by `2^j` exactly, bit by bit. Each `blob_<row>` is the\n"
        "  stage-2 compiler's artifact of `blobs/vf7/bv_<row>.rs`: an aterm function copied\n"
        "  verbatim with its SPEC HARNESS (the body, then the crate's SPECS.md clause written apart\n"
        "  from it; `ok as u8 - 1` underflows exactly when the clause is false). A harness's\n"
        "  row is \"proved (calculus)\": its function never panics, so the clause holds for\n"
        "  every input. Then the three VF7 mutant calculi, each refuted on its compiled\n"
        "  witness, and the witnesses' corrected twins."))]
    report = ["# VF7: bitwise operations, shifts, casts (R206)"]
    rows = [l.split("\t") for l in (VF7 / "rows.tsv").read_text().splitlines()
            if l.strip() and not l.startswith("#")]
    keys = {r[0] for r in rows}
    assert keys == VF7_WRONG_ROWS, f"rows.tsv {sorted(keys)} and VF7_WRONG_ROWS differ"
    wrong = [(stem, fn, fn.removesuffix("_wrong"), argv, why) for stem, fn, argv, why in VF7_WRONG]
    rows_out, rows_report = spec_rows(VF7, "vf7", [r[:4] for r in rows], wrong,
                                      lambda stem: "blob_bv_wrong" if stem == "aterm_bv_wrong" else f"blob_{stem}")
    out.extend(rows_out)
    report.extend(rows_report)
    # Trust's CAST-SIGNED-CLAMP-UB-1 (VF7's accept line): proved not-Valid by SemR's run; its
    # twin is among the twins below.
    cb = list((VF7 / "cast_clamp.bin").read_bytes())
    cnames, _, _ = meta(cb, {})
    cfid = fid_of(cnames, "c2_add")
    _, cfail = certify(dump(cb, {}))
    assert cfail, "c2_add: F1's calculus certifies CAST-SIGNED-CLAMP-UB-1"
    out.append(f"\n/-- `blobs/vf7/cast_clamp.bin`, {len(cb)} bytes: Trust's CAST-SIGNED-CLAMP-UB-1. -/\n"
               f"def blob_cast_clamp : List Nat :=\n  {lean_bytes(cb)}\n"
               f"/-- **CAST-SIGNED-CLAMP-UB-1 is not valid**: `c2_add(-1)` panics (`-1 as u32` is\n"
               f"    `4294967295`; adding `4294967200` overflows); F1's calculus leaves {len(cfail)} obligation(s)\n"
               f"    of it with no certificate. -/\n"
               f"theorem c2_add_unsafe : ∀ m, decode blob_cast_clamp = .ok m → ¬ ClosedSafe m (annot []) :=\n"
               f"  unsafeBlob (fid := {cfid}) (args := [.int .i32 4294967295]) (fuel := 1000) (depth := 64) ({KDEC})\n")
    report.append(f"cast_clamp\tc2_add\tunsafe\tCAST-SIGNED-CLAMP-UB-1: c2_add(-1) panics\t{len(cfail)} unrefuted by F1")
    for blob_name, calc, fn, argv, why in VF7_MUTANTS:
        mb = list((VF7 / f"{blob_name}.bin").read_bytes())
        mnames, _, _ = meta(mb, {})
        fid = fid_of(mnames, fn)
        mc, mfail = certify(dump(mb, {}, calc=calc))
        if mfail:
            sys.exit(f"{blob_name}: the mutant {calc} leaves obligations unrefuted: {mfail}")
        _, std_failing = certify(dump(mb, {}))
        assert std_failing, f"{blob_name}: F1's calculus certifies an unsafe program"
        n = sum(len(v) for v in mc.values())
        out.append(f"\n/-- `blobs/vf7/{blob_name}.bin`, {len(mb)} bytes. -/\n"
                   f"def blob_{blob_name} : List Nat :=\n  {lean_bytes(mb)}\n")
        out.append(f"/-- The witness is unsafe; F1's calculus leaves {len(std_failing)} obligation(s) of it\n"
                   f"    with no certificate. -/\n"
                   f"theorem {blob_name}_unsafe : ∀ m, decode blob_{blob_name} = .ok m → ¬ ClosedSafe m (annot []) :=\n"
                   f"  unsafeBlob (fid := {fid}) (args := {argv}) (fuel := 1000) (depth := 64) ({KDEC})\n")
        out.append(f"/-- The mutant `{calc}` refutes every obligation it emits ({n}). -/\n"
                   f"theorem {calc}_checks : checkBlobC {calc} blob_{blob_name} (annot []) {lean_certs(mc)} = true :=\n"
                   f"  {KDEC}\n")
        out.append(f"/-- {why}. -/\ntheorem {calc}_bad : badRunBlob blob_{blob_name} (annot []) {fid} {argv} 1000 64 = true :=\n"
                   f"  {KDEC}\n")
        out.append(f"/-- **`{calc}` is unsound.** -/\ntheorem {calc}_refuted : ¬ CalcSound {calc} :=\n"
                   f"  refuteBlob {calc}_checks {calc}_bad\n")
        report.append(f"{blob_name}\t{calc}\trefuted\t{n} mutant obligation(s) certified\t{len(std_failing)} unrefuted by F1")
    tb = list((VF7 / "twins_bv.bin").read_bytes())
    tc, tfail = certify(dump(tb, {}))
    assert not tfail, tfail
    tnames, _, tentries = meta(tb, {})
    assert tentries
    out.append(f"\n/-- `blobs/vf7/twins_bv.bin`, {len(tb)} bytes: the witnesses' corrected twins. -/\n"
               f"def blob_twins_bv : List Nat :=\n  {lean_bytes(tb)}\n")
    out.append(f"theorem checks_twins_bv : checkBlob blob_twins_bv (annot []) {lean_certs(tc)} = true :=\n  {KDEC}\n")
    for fn in ("ashr_div_twin", "xor_div_twin", "trunc_div_twin", "c2_add_twin"):
        fid = fid_of(tnames, fn)
        out.append(lean_sym(fn, tnames[fid]))
        out.append(f"theorem row_{fn} : RowProved blob_twins_bv (annot []) {fid} sym_{fn} :=\n"
                   f"  row_of checks_twins_bv ({KDEC})\n")
        report.append(f"twins_bv\t{fn}\t{tnames[fid].decode()}\tproved (calculus)")
    out.append("\nend VF7Rows\n")
    return "".join(out), report


# aterm's "PM-1-free, F1" rows (aterm docs/PLAN-tests-to-specs-2026-10-15.md) beyond R206's and
# R208's: per row, its false-clause control `blobs/aterm_spec/wrong_<key>.rs` (function
# `<key>_wrong`), the counterexample, and why it panics there.
ATERM_WRONG = [
    ("least_greater_odd", "[.int .u8 1]",
     "`least_greater_odd_wrong(1)` panics: the clause with the least bound `result - level <= 1` "
     "is false at 1 (the result is 3)"),
    ("least_greater_even", "[.int .u8 254]",
     "`least_greater_even_wrong(254)` panics: the clause saturating from 255 is false at 254 "
     "(the result is 255, odd)"),
    ("canonical_bracket", "[.int .u32 9002]",
     "`canonical_bracket_wrong(0x232A)` panics: the clause mapping 0x232A to 0x3008 is false there"),
    ("json_utf8_len", "[.int .u8 224]",
     "`json_utf8_len_wrong(0xE0)` panics: the clause with 2 for the E nibble is false there"),
    ("is_word", "[.int .u8 95]",
     "`is_word_wrong(0x5F)` panics: the clause without `_` is false there"),
    ("lex_utf8_len", "[.int .u8 192]",
     "`lex_utf8_len_wrong(0xC0)` panics: the clause reading a two-byte lead as `>> 6 == 2` is "
     "false there"),
    ("devtool_answer_age_ms", "[.int .i64 18446744073709551615, .int .i64 9223372036854775807]",
     "`devtool_answer_age_ms_wrong(-1, i64::MAX)` panics: the clause without the saturation is "
     "false there (the difference is 2^63)"),
    ("compact_pet_witness_frame", "[.int .usize 1, .int .usize 4]",
     "`compact_pet_witness_frame_wrong(1, 4)` panics: the clause with `c - n <= 2` is false there"),
    ("resting_pet_min_width", "[.int .usize 0]",
     "`resting_pet_min_width_wrong(0)` panics: the clause as 2w is false at 0"),
    ("token_from_literal", "[.int .usize 1]",
     "`token_from_literal_wrong(1)` panics: the clause as 8·l is false at 1"),
    ("mask_trns_key", "[.int .u16 256, .int .u32 16]",
     "`mask_trns_key_wrong(256, 16)` panics: the clause masking at depth 16 too is false there"),
    ("shaping_min_run", "[.bool true]",
     "`shaping_min_run_wrong(true)` panics: the clause with 2 for user features is false there"),
    ("ink_skip_applies_to_width", "[.int .usize 1]",
     "`ink_skip_applies_to_width_wrong(1)` panics: the clause as cols = 0 is false at 1"),
    ("undercurl_supported", "[.int .usize 256, .int .usize 1]",
     "`undercurl_supported_wrong(256, 1)` panics: the clause with the width cap 255 is false there"),
    ("band_icon_width", "[.int .usize 1, .bool true]",
     "`band_icon_width_wrong(1, true)` panics: the clause as 2cw when spilled is false there"),
    # `selection_contains_linear`, in seven parts (see `bv_selection_contains_linear_*.rs`).
    ("selection_contains_linear_one_row_below",
     "[.int .i32 4294967295, .int .usize 0, .int .i32 0, .int .usize 0, .int .i32 0, .int .usize 0]",
     "`selection_contains_linear_one_row_below_wrong` panics at (-1, 0) of the one-cell selection (0, 0): "
     "the clause as `before_end` alone is false there"),
    ("selection_contains_linear_one_row_at",
     "[.int .i32 0, .int .usize 0, .int .i32 0, .int .usize 0, .int .i32 0, .int .usize 0]",
     "`selection_contains_linear_one_row_at_wrong` panics at (0, 0) of the one-cell selection (0, 0): "
     "the clause with a strict end column is false there"),
    ("selection_contains_linear_one_row_above",
     "[.int .i32 1, .int .usize 0, .int .i32 0, .int .usize 0, .int .i32 0, .int .usize 0]",
     "`selection_contains_linear_one_row_above_wrong` panics at (1, 0) of the one-cell selection (0, 0): "
     "the clause as `after_start` alone is false there"),
    ("selection_contains_linear_many_outside",
     "[.int .i32 2, .int .usize 0, .int .i32 0, .int .usize 0, .int .i32 1, .int .usize 0]",
     "`selection_contains_linear_many_outside_wrong` panics at (2, 0) of the selection (0, 0) to (1, 0): "
     "the clause as `after_start` alone is false there"),
    ("selection_contains_linear_many_inside",
     "[.int .i32 1, .int .usize 5, .int .i32 0, .int .usize 0, .int .i32 2, .int .usize 0]",
     "`selection_contains_linear_many_inside_wrong` panics at (1, 5) of the selection (0, 0) to (2, 0): "
     "the clause bounding an inner row's column by `end_col` is false there"),
    ("selection_contains_linear_many_start",
     "[.int .i32 0, .int .usize 0, .int .i32 0, .int .usize 0, .int .i32 1, .int .usize 0]",
     "`selection_contains_linear_many_start_wrong` panics at (0, 0) of the selection (0, 0) to (1, 0): "
     "the clause with a strict start column is false there"),
    ("selection_contains_linear_many_end",
     "[.int .i32 1, .int .usize 0, .int .i32 0, .int .usize 0, .int .i32 1, .int .usize 0]",
     "`selection_contains_linear_many_end_wrong` panics at (1, 0) of the selection (0, 0) to (1, 0): "
     "the clause with a strict end column is false there"),
]


def aterm_module():
    out = [HEADER.format(name="VF5AtermRows", imp="VF7Rows", body=(
        "  aterm's \"PM-1-free, F1\" rows (aterm docs/PLAN-tests-to-specs-2026-10-15.md,\n"
        "  \"F1-ready specs\") beyond R206's (`VF7Rows`) and R208's (`VF5Rows`' mirror), in\n"
        "  VF7's form. Each `blob_<row>` is the stage-2 compiler's artifact of\n"
        "  `blobs/aterm_spec/bv_<row>.rs`: an aterm function with its SPEC HARNESS (the body,\n"
        "  then the crate's SPECS.md clause written apart from it; `ok as u8 - 1` underflows\n"
        "  exactly when the clause is false; a clause's `requires` is the harness's early\n"
        "  return). Where the body is not F1 as written, the harness copies it rewritten, and\n"
        "  `blobs/aterm_spec/rows.tsv` and the source say how. A row is \"proved (calculus)\":\n"
        "  its harness never panics, so the clause holds for every input it admits. Each row\n"
        "  has a false-clause control, `<row>_wrong_unsafe`, and `<row>_spec_runs_at_cex`.\n"
        "  Every definition is `noncomputable`: they are data the kernel evaluates, and\n"
        "  compiled they gave Lean's compiler 115,935 declarations, past the 100,000 rows\n"
        "  `clean-olean` reads from one extension of one module."))]
    report = ["# aterm's PM-1-free F1 rows beyond R206/R208 (blobs/aterm_spec)"]
    rows = [l.split("\t") for l in (ATERM_SPEC / "rows.tsv").read_text().splitlines()
            if l.strip() and not l.startswith("#")]
    wrong = [(f"wrong_{key}", f"{key}_wrong", key, argv, why) for key, argv, why in ATERM_WRONG]
    rows_out, rows_report = spec_rows(ATERM_SPEC, "aterm_spec", [r[:4] for r in rows], wrong,
                                      lambda stem: f"blob_{stem}")
    out.extend(re.sub(r"(?m)^def ", "noncomputable def ", part) for part in rows_out)
    report.extend(rows_report)
    out.append("\nend VF5AtermRows\n")
    return "".join(out), report


# D-2(b) rows (docs/DECISIONS.md R213, R215): aterm's "PM-1-free, F1+D2b" and "behind PM-1,
# F1+D2b" functions (aterm
# docs/PLAN-tests-to-specs-2026-10-15.md), each copied verbatim with its SPEC HARNESS into
# `blobs/d2b_rows/<stem>.rs`, one artifact per row or per enum's rows, so each check stays
# within the reference entry's per-declaration heartbeat budget.
def tsv_rows(path: Path) -> list[list[str]]:
    return [l.split("\t") for l in path.read_text().splitlines() if l.strip() and not l.startswith("#")]


def b3_table_of(ids: list[tuple[str, int]], rustc: dict) -> str:
    """`List B3Entry` for one artifact: (enum id, rustc's positional list, rustc's repr)."""
    items = sorted((eid, name) for name, eid in ids)
    return "[%s]" % ",\n   ".join(f"({eid}, {lean_pos(rustc[name][1])}, {REPR[rustc[name][0]]})"
                                  for eid, name in items)


def fid_of_path(names, fn: str) -> int:
    """`fid_of` for `Type::method`: the symbol ends in the method's identifier and names the
    type's identifier too (an inherent impl's self type)."""
    *ty, last = fn.split("::")
    tag = f"{len(last)}{last}".encode()
    hits = [f for f, n in names.items() if n.endswith(tag) and all(f"{len(t)}{t}".encode() in n for t in ty)]
    assert len(hits) == 1, (fn, hits)
    return hits[0]


def d2b_rows_module():
    """The D-2(b) rows' modules: [(module name, text)]. The artifacts are split over several
    modules (`D2B_CHUNK` bytes of artifact literals each, about `VF7Rows`'s): a module's `.olean`
    grows with its literals, and one holding them all (250 MB) outgrows the reader's bound on a
    typed extension array."""
    head = "".join(["/-\n  VF5D2bRows — GENERATED by `scripts/vf5_f1_producer.py` from `blobs/d2b_rows/`; a hand\n"
           "  edit is drift (`--check`).\n\n"
           "  D-2(b) rows (docs/DECISIONS.md R213, R215): aterm's \"PM-1-free, F1+D2b\" functions and\n"
           "  (`pm1_<stem>`) its \"behind PM-1, F1+D2b\" functions over mirrors of their bodies (aterm\n"
           "  docs/PLAN-tests-to-specs-2026-10-15.md), fieldless enums by value. Each `blob_<stem>` is the\n"
           "  stage-2 compiler's artifact of `blobs/d2b_rows/<stem>.rs`: aterm functions copied verbatim\n"
           "  with their SPEC HARNESSES (the body, then the crate's SPECS.md clause written apart from\n"
           "  it; `ok as u8 - 1` underflows exactly when the clause is false). A row is\n"
           "  `RowProvedB3`: its harness never panics on any valid input, so the clause holds for every\n"
           "  input, and B3 binds every enum of the artifact to rustc's own discriminants\n"
           "  (`b3probe.rs`, `b3_rustc.tsv`). Per artifact: the certificates perturbed (`refused_cert_*`)\n"
           "  and B3 over a swapped table refused (`b3all_refused_*`); per row: a FALSE clause's harness\n"
           "  unsafe at a named counterexample (`*_wrong_unsafe`), the row's own harness valid at that\n"
           "  input (`*_cex_valid`) and clean there (`*_spec_runs_at_cex`). Then VF7's `creation_flags`\n"
           "  row carried over to `RowProvedB3`.\n-/\n"
           "import VF7Rows\nimport VF5Enum\n\nset_option maxRecDepth 100000\n\nnamespace VF5D2bRows\n\nopen SemR VF5\n"])
    pieces: dict[str, list[str]] = {}
    sizes: dict[str, int] = {}
    report = ["# D-2(b) rows: aterm's PM-1-free (R213) and behind-PM-1 (R215, pm1_*) F1+D2b functions"]
    rows = tsv_rows(D2B_ROWS / "rows.tsv")
    wrong = tsv_rows(D2B_ROWS / "wrong.tsv")
    ids: dict[str, list[tuple[str, int]]] = {}
    for stem, name, eid in tsv_rows(D2B_ROWS / "b3_ids.tsv"):
        ids.setdefault(stem, []).append((name, int(eid)))
    rustc: dict[str, dict] = {}
    for stem, name, ty, ds in tsv_rows(D2B_ROWS / "b3_rustc.tsv"):
        rustc.setdefault(stem, {})[name] = (ty, [int(x) for x in ds.strip("[]").split(",")])
    rowinfo = {}
    for stem in sorted({r[0] for r in rows}, key=lambda k: [r[0] for r in rows].index(k)):
        mine = [r for r in rows if r[0] == stem]
        blob = list((D2B_ROWS / f"{stem}.bin").read_bytes())
        fns = dump(blob, {})
        certs, failing = certify(fns)
        if failing:
            sys.exit(f"d2b_rows {stem}: obligations with no certificate: {failing}")
        names, roots, entries = meta(blob, {})
        assert entries, stem
        nob = sum(len(v) for v in certs.values())
        ncg = sum(1 for v in certs.values() for c in v if isinstance(c, dict))
        assert set(rustc[stem]) == {n for n, _ in ids[stem]}, f"{stem}: b3_ids.tsv and b3_rustc.tsv"
        pieces.setdefault(stem, []).append(f"\n/-! ## `{stem}` -/\n\n/-- `blobs/d2b_rows/{stem}.bin`, {len(blob)} bytes. -/\n"
                   f"def blob_{stem} : List Nat :=\n  {lean_bytes(blob)}\n"
                   f"def certs_{stem} : List (Nat × List (List ChkLIA.Step)) :=\n  {lean_certs(certs)}\n"
                   f"/-- Every obligation of every function ({nob}; {ncg} by a cutting plane) is refuted; the\n"
                   f"    entry forks every enum parameter per variant. -/\n"
                   f"theorem checks_{stem} : checkBlob blob_{stem} (annot []) certs_{stem} = true :=\n  {KDEC}\n")
        if nob:
            mcerts, (mf, mi, mj, was, now) = mutate_certs(fns, certs)
            pieces.setdefault(stem, []).append(f"/-- The certificates with multiplier {mj} of function {mf}'s obligation {mi} changed\n"
                       f"    from {was} to {now}: the combination no longer closes. -/\n"
                       f"def certs_mut_{stem} : List (Nat × List (List ChkLIA.Step)) :=\n  {lean_certs(mcerts)}\n"
                       f"theorem refused_cert_{stem} : checkBlob blob_{stem} (annot []) certs_mut_{stem} = false :=\n"
                       f"  {KDEC}\n")
        else:
            pieces.setdefault(stem, []).append(f"/-- No obligation is left (every path is decided syntactically); the checks with one\n"
                       f"    (empty) certificate too many are refused. -/\n"
                       f"theorem refused_cert_{stem} : checkBlob blob_{stem} (annot []) "
                       f"(certs_{stem}.map fun p => (p.1, [] :: p.2)) = false :=\n  {KDEC}\n")
        table = b3_table_of(ids[stem], rustc[stem])
        pieces.setdefault(stem, []).append(f"/-- B3's table: per enum of the artifact, rustc's positional discriminants and repr\n"
                   f"    (`b3_rustc.tsv`, by the ids of `b3_ids.tsv`). -/\n"
                   f"def b3_{stem} : List B3Entry :=\n  {table}\n"
                   f"theorem b3all_{stem} : checkB3All blob_{stem} b3_{stem} = true :=\n  {KDEC}\n")
        # B3's control on this artifact: its first enum's first two discriminants swapped.
        name0, eid0 = min(ids[stem], key=lambda x: x[1])
        ty0, ds0 = rustc[stem][name0]
        if len(ds0) >= 2:
            sw = [ds0[1], ds0[0]] + ds0[2:]
            swapped = table.replace(f"({eid0}, {lean_pos(ds0)},", f"({eid0}, {lean_pos(sw)},", 1)
            assert swapped != table
            pieces.setdefault(stem, []).append(f"/-- B3 refuses `{name0}` read with its first two discriminants swapped. -/\n"
                       f"theorem b3all_refused_{stem} : checkB3All blob_{stem}\n  {swapped} = false :=\n  {KDEC}\n")
        for r in mine:
            _, fn, row, plan, src, clause = r
            fid = fid_of_path(names, fn)
            rowinfo[row] = (stem, blob, fid)
            pieces.setdefault(stem, []).append(lean_sym(row, names[fid]))
            pieces.setdefault(stem, []).append(f"/-- aterm plan row {plan}: {clause} (`{src}`). -/\n"
                       f"theorem row_{row} : RowProvedB3 blob_{stem} (annot []) {fid} sym_{row} b3_{stem} :=\n"
                       f"  rowB3_of checks_{stem} ({KDEC}) b3all_{stem}\n")
            report.append(f"{stem}\t{row}\t{fid}\t{names[fid].decode()}\tproved (calculus) + B3\t{{}}\tpre=none\t"
                          f"{nob}\tplan row {plan}\t{src}")
    # The harness form is not vacuous: per row, a FALSE clause's harness panics at its
    # counterexample, F1's calculus leaves an obligation of it unrefuted, and the row's own
    # harness is valid and runs clean at the same input.
    assert sorted(w[2] for w in wrong) == sorted(rowinfo), "wrong.tsv names each row once"
    seen = {}
    for stem, fn, row, argv, rargv, why in wrong:
        if stem not in seen:
            wb = list((D2B_ROWS / f"wrong_{stem}.bin").read_bytes())
            wnames, _, _ = meta(wb, {})
            seen[stem] = (wb, wnames, dump(wb, {}))
            pieces.setdefault(stem, []).append(f"\n/-- `blobs/d2b_rows/wrong_{stem}.bin`, {len(wb)} bytes: harnesses whose clause is "
                       f"false. -/\ndef blob_wrong_{stem} : List Nat :=\n  {lean_bytes(wb)}\n")
        wb, wnames, wfns = seen[stem]
        wfid = fid_of_path(wnames, fn)
        _, wfail = certify({wfid: wfns[wfid]})
        assert wfail, f"{fn}: F1's calculus certifies a false clause"
        assert bad_run(wb, wfid, argv), f"{fn}: SemR's run at {argv} is not bad"
        pieces.setdefault(stem, []).append(f"/-- {why}; F1's calculus leaves {len(wfail)} obligation(s) of it with no certificate. -/\n"
                   f"theorem {row}_wrong_unsafe : ∀ m, decode blob_wrong_{stem} = .ok m → ¬ ClosedSafe m (annot []) :=\n"
                   f"  unsafeBlob (fid := {wfid}) (args := {argv}) (fuel := 1000) (depth := 64) ({KDEC})\n")
        rstem, rb, rfid = rowinfo[row]
        assert rstem == stem, (row, stem)
        assert not bad_run(rb, rfid, rargv), f"{row}: the true harness panics at {rargv}"
        pieces.setdefault(stem, []).append(f"/-- The counterexample is a valid input of the row's own harness. -/\n"
                   f"theorem {row}_cex_valid : preWitness blob_{stem} (annot []) {rfid} {rargv} = true :=\n  {KDEC}\n"
                   f"/-- The row's own harness does not panic at the same input. -/\n"
                   f"theorem {row}_spec_runs_at_cex : badRunBlob blob_{stem} (annot []) {rfid} {rargv} 1000 64 "
                   f"= false :=\n  {KDEC}\n")
        report.append(f"wrong_{stem}\t{fn}\tunsafe\t{why}\t{len(wfail)} unrefuted by F1")
    stem = ""
    # VF7's creation_flags row (aterm plan row 67) carried over to D-2(b): B3 over its artifact.
    cb = list((VF7 / "bv_creation_flags.bin").read_bytes())
    cnames, _, _ = meta(cb, {})
    cfid = fid_of(cnames, "creation_flags_spec")
    ctable = b3_table_of(ids["bv_creation_flags"], rustc["bv_creation_flags"])
    pieces.setdefault(stem, []).append(f"\n/-! ## aterm plan row 67: VF7's `creation_flags` row with B3 -/\n\n"
               f"def b3_creation_flags : List B3Entry :=\n  {ctable}\n"
               f"theorem b3all_creation_flags : checkB3All VF7Rows.blob_creation_flags b3_creation_flags = true :=\n"
               f"  {KDEC}\n"
               f"/-- aterm plan row 67: aterm-uds SPECS.md creation-flags-rule (VF7's row), now with B3 over\n"
               f"    `Console`. -/\n"
               f"theorem row_creation_flags_b3 : RowProvedB3 VF7Rows.blob_creation_flags (annot []) {cfid}\n"
               f"    VF7Rows.sym_creation_flags b3_creation_flags :=\n"
               f"  rowB3_of VF7Rows.checks_creation_flags ({KDEC}) b3all_creation_flags\n")
    report.append(f"bv_creation_flags\tcreation_flags_b3\t{cfid}\t{cnames[cfid].decode()}\tproved (calculus) + B3\t"
                  f"{{}}\tpre=none\t-\tplan row 67\taterm-uds src/spawn.rs creation_flags")
    for st in pieces:
        sizes[st] = sum((D2B_ROWS / f).stat().st_size for f in (f"{st}.bin", f"wrong_{st}.bin")) if st else 0
    chunks: list[list[str]] = [[]]
    used = 0
    for st in pieces:
        if chunks[-1] and used + sizes[st] > D2B_CHUNK:
            chunks.append([])
            used = 0
        chunks[-1].append(st)
        used += sizes[st]
    mods = []
    for i, sts in enumerate(chunks, 1):
        name = f"VF5D2bRows{i}"
        text = (head.replace("VF5D2bRows —", f"{name} —", 1)
                + f"\n/-! Artifacts: {', '.join('`' + (x or 'creation_flags (VF7)') + '`' for x in sts)}. -/\n"
                + "".join("".join(pieces[x]) for x in sts) + "\nend VF5D2bRows\n")
        mods.append((name, text))
    order = order_stems(FAMILY / "ORDER")
    listed = [x for x in order if x.startswith("VF5D2bRows")]
    assert listed == [n for n, _ in mods], f"ORDER lists {listed}, the producer writes {[n for n, _ in mods]}"
    return mods, report


# The "behind PM-1, F1" rows: aterm's functions (aterm docs/PLAN-tests-to-specs-2026-10-15.md)
# whose crates PM-1 keeps from being credited through Trust; the mirror proof does not depend
# on PM-1. Per row `blobs/pm1_rows/bv_<key>.rs` (the function and its SPEC HARNESS) and its
# false-clause control `wrong_<key>.rs`, one artifact each, split over modules as D-2(b)'s.
PM1_ROWS = BLOBS / "pm1_rows"
# Bytes of artifact literals per module (`VF7Rows` holds about 45 KB).
PM1_CHUNK = 46000


def pm1_rows_module():
    """The behind-PM-1 rows' modules: [(module name, text)], and the report lines."""
    head = ("/-\n  VF5PM1Rows — GENERATED by `scripts/vf5_f1_producer.py` from `blobs/pm1_rows/`; a hand\n"
            "  edit is drift (`--check`).\n\n"
            "  aterm's \"behind PM-1, F1\" rows (aterm docs/PLAN-tests-to-specs-2026-10-15.md, \"F1-ready\n"
            "  specs\"): PM-1 keeps their crates from being credited through Trust, and the mirror proof\n"
            "  does not depend on it. Each `blob_<row>` is the stage-2 compiler's artifact of\n"
            "  `blobs/pm1_rows/bv_<row>.rs`: the aterm function copied (verbatim but for visibility and\n"
            "  its cfg, or, where it needs a `requires`, in a comment) with its SPEC HARNESS (the body,\n"
            "  then the crate's SPECS.md clause written apart from it; `ok as u8 - 1` underflows exactly\n"
            "  when the clause is false; a clause's `requires` is the harness's early return). Where\n"
            "  the body is not F1 as written, the harness copies it rewritten, as\n"
            "  `blobs/pm1_rows/rows.tsv`'s last column and the source say. A row is \"proved\n"
            "  (calculus)\": its harness never panics, so the clause holds for every input it admits.\n"
            "  Per row: `checks_*`, `refused_cert_*`, `sym_*`, `row_*`, and the false-clause control\n"
            "  `*_wrong_unsafe` (`wrong_<row>.rs`, at the counterexample `wrong.tsv` names), with\n"
            "  `*_cex_valid` and `*_spec_runs_at_cex` (the row's own harness valid and clean there).\n"
            "  Every definition is `noncomputable`: data the kernel evaluates (`VF5AtermRows`' reason).\n-/\n"
            "import VF7Rows\n\nset_option maxRecDepth 100000\n\nnamespace VF5PM1Rows\n\nopen SemR VF5\n")
    pieces: dict[str, list[str]] = {}
    report = ["# aterm's behind-PM-1 F1 rows (blobs/pm1_rows)"]
    rows = tsv_rows(PM1_ROWS / "rows.tsv")
    wrong = {w[0]: w for w in tsv_rows(PM1_ROWS / "wrong.tsv")}
    assert sorted(wrong) == sorted(r[0] for r in rows), "wrong.tsv names each row once"
    pinned = [p[0] for p in tsv_rows(PM1_ROWS / "aterm_pin.tsv")]
    assert pinned == [r[0] for r in rows], "aterm_pin.tsv pins each row's clause once (--aterm DIR --pin)"
    for key, fn, plan, src, clause, _ in rows:
        out = pieces.setdefault(key, [])
        blob = list((PM1_ROWS / f"bv_{key}.bin").read_bytes())
        fns = dump(blob, {})
        certs, failing = certify(fns)
        if failing:
            sys.exit(f"pm1_rows {key}: obligations with no certificate: {failing}")
        names, roots, entries = meta(blob, {})
        assert entries, key
        nob = sum(len(v) for v in certs.values())
        ncg = sum(1 for v in certs.values() for c in v if isinstance(c, dict))
        out.append(f"\n/-! ## aterm plan row {plan}: `{key}` -/\n\n"
                   f"/-- `blobs/pm1_rows/bv_{key}.bin`, {len(blob)} bytes. -/\n"
                   f"def blob_{key} : List Nat :=\n  {lean_bytes(blob)}\n"
                   f"def certs_{key} : List (Nat × List (List ChkLIA.Step)) :=\n  {lean_certs(certs)}\n"
                   f"/-- Every obligation of every function ({nob}; {ncg} by a cutting plane) is refuted. -/\n"
                   f"theorem checks_{key} : checkBlob blob_{key} (annot []) certs_{key} = true :=\n  {KDEC}\n")
        if nob:
            mcerts, (mf, mi, mj, was, now) = mutate_certs(fns, certs)
            out.append(f"/-- The certificates with multiplier {mj} of function {mf}'s obligation {mi} changed\n"
                       f"    from {was} to {now}: the combination no longer closes. -/\n"
                       f"def certs_mut_{key} : List (Nat × List (List ChkLIA.Step)) :=\n  {lean_certs(mcerts)}\n"
                       f"theorem refused_cert_{key} : checkBlob blob_{key} (annot []) certs_mut_{key} = false :=\n"
                       f"  {KDEC}\n")
        else:
            out.append(f"/-- No obligation is left (every path is decided syntactically); the checks with one\n"
                       f"    (empty) certificate too many are refused. -/\n"
                       f"theorem refused_cert_{key} : checkBlob blob_{key} (annot []) "
                       f"(certs_{key}.map fun p => (p.1, [] :: p.2)) = false :=\n  {KDEC}\n")
        fid = fid_of_path(names, fn)
        out.append(lean_sym(key, names[fid]))
        out.append(f"/-- aterm plan row {plan}: {clause} (`{src}`). -/\n"
                   f"theorem row_{key} : RowProved blob_{key} (annot []) {fid} sym_{key} :=\n"
                   f"  row_of checks_{key} ({KDEC})\n")
        report.append(f"bv_{key}\t{key}\t{fid}\t{names[fid].decode()}\tproved (calculus)\t{{}}\tpre=none\t"
                      f"{nob}\tplan row {plan}\t{src}")
        # The harness form is not vacuous: a FALSE clause's harness panics at its
        # counterexample, F1's calculus leaves an obligation of it unrefuted, and the row's
        # own harness is valid and runs clean at the same input.
        _, wfn, argv, why = wrong[key]
        wb = list((PM1_ROWS / f"wrong_{key}.bin").read_bytes())
        wnames, _, _ = meta(wb, {})
        wfns = dump(wb, {})
        wfid = fid_of_path(wnames, wfn)
        _, wfail = certify({wfid: wfns[wfid]})
        assert wfail, f"{wfn}: F1's calculus certifies a false clause"
        assert bad_run(wb, wfid, argv), f"{wfn}: SemR's run at {argv} is not bad"
        assert not bad_run(blob, fid, argv), f"{key}: the true harness panics at {argv}"
        out.append(f"\n/-- `blobs/pm1_rows/wrong_{key}.bin`, {len(wb)} bytes: the harness whose clause is "
                   f"false. -/\ndef blob_wrong_{key} : List Nat :=\n  {lean_bytes(wb)}\n"
                   f"/-- {why}; F1's calculus leaves {len(wfail)} obligation(s) of it with no certificate. -/\n"
                   f"theorem {key}_wrong_unsafe : ∀ m, decode blob_wrong_{key} = .ok m → ¬ ClosedSafe m (annot []) :=\n"
                   f"  unsafeBlob (fid := {wfid}) (args := {argv}) (fuel := 1000) (depth := 64) ({KDEC})\n"
                   f"/-- The counterexample is a valid input of the row's own harness. -/\n"
                   f"theorem {key}_cex_valid : preWitness blob_{key} (annot []) {fid} {argv} = true :=\n  {KDEC}\n"
                   f"/-- The row's own harness does not panic at the same input. -/\n"
                   f"theorem {key}_spec_runs_at_cex : badRunBlob blob_{key} (annot []) {fid} {argv} 1000 64 "
                   f"= false :=\n  {KDEC}\n")
        report.append(f"wrong_{key}\t{wfn}\tunsafe\t{why}\t{len(wfail)} unrefuted by F1")
    sizes = {k: sum((PM1_ROWS / f).stat().st_size for f in (f"bv_{k}.bin", f"wrong_{k}.bin")) for k in pieces}
    chunks: list[list[str]] = [[]]
    used = 0
    for k in pieces:
        if chunks[-1] and used + sizes[k] > PM1_CHUNK:
            chunks.append([])
            used = 0
        chunks[-1].append(k)
        used += sizes[k]
    mods = []
    for i, ks in enumerate(chunks, 1):
        name = f"VF5PM1Rows{i}"
        body = "".join("".join(pieces[x]) for x in ks)
        body = re.sub(r"(?m)^def ", "noncomputable def ", body)
        text = (head.replace("VF5PM1Rows —", f"{name} —", 1)
                + f"\n/-! Rows: {', '.join('`' + x + '`' for x in ks)}. -/\n"
                + body + "\nend VF5PM1Rows\n")
        mods.append((name, text))
    order = order_stems(FAMILY / "ORDER")
    listed = [x for x in order if x.startswith("VF5PM1Rows")]
    assert listed == [n for n, _ in mods], f"ORDER lists {listed}, the producer writes {[n for n, _ in mods]}"
    return mods, report


# aterm drift (the behind-PM-1 rows' copies and clauses against an aterm checkout)


def _strip(text: str) -> str:
    text = re.sub(r"//[^\n]*", "", text)
    text = re.sub(r"#!?\[[^\]]*\]", "", text)
    text = re.sub(r"\bpub(?:\([^)]*\))?\s+", "", text)
    text = re.sub(r"\s+", "", text)
    return re.sub(r",(?=[)}\]])", "", text)


def _items(text: str, name: str) -> dict[str, str]:
    """Every fn or const named `name` (`NAME_*` a prefix) in `text`: {name: normalized item}."""
    pat = re.escape(name[:-1]) + r"\w*" if name.endswith("*") else re.escape(name)
    found: dict[str, str] = {}
    for m in re.finditer(r"(?m)^[ \t]*(?:pub(?:\([^)]*\))?\s+)?const\s+(" + pat + r")\s*:", text):
        end = text.index(";", m.end())
        found.setdefault(m.group(1), _strip(text[m.start():end + 1]))
    for m in re.finditer(r"(?m)^[ \t]*(?:pub(?:\([^)]*\))?\s+)?(?:const\s+)?fn\s+(" + pat + r")\s*[(<]", text):
        i, depth = m.end() - 1, 0
        while True:
            c = text[i]
            depth += c == "("
            depth -= c == ")"
            if c == "{" and depth == 0:
                break
            i += 1
        j, depth = i, 0
        while True:
            depth += text[j] == "{"
            depth -= text[j] == "}"
            j += 1
            if depth == 0:
                break
        found.setdefault(m.group(1), _strip(text[m.start():j]))
    return found


def _specs_clause(aterm: Path, crate: str, row: str) -> str | None:
    for line in (aterm / "crates" / crate / "SPECS.md").read_text().splitlines():
        cells = line.split("\t")
        if cells[0] == row and len(cells) > 3:
            return cells[3]
    return None


def pm1_aterm_drift(aterm: Path, rows_dir: Path = PM1_ROWS) -> list[str]:
    """What differs between the behind-PM-1 harnesses and an aterm checkout: every item a
    `// aterm: <file> `names`` line names (a fn or const, `NAME_*` a prefix) is compared with the
    same-named item of that file, comments, attributes, visibility, whitespace and trailing
    commas aside (a copy in a comment, where the function needs a `requires`, counts); and
    each row's SPECS.md clause cell against the sha256 `aterm_pin.tsv` holds for it. Nothing
    in the proof reads aterm, so this is the one place a stale copy or clause shows."""
    problems = []
    for src in sorted(rows_dir.glob("bv_*.rs")):
        text = src.read_text()
        decommented = "\n".join(re.sub(r"^\s*// ?", "", l) for l in text.splitlines() if l.lstrip().startswith("//"))
        named = []
        for m in re.finditer(r"(?m)^// aterm: (.*)$", text):
            file = None
            for tok in re.finditer(r"((?:crates|apps)/\S+)|`([^`]+)`|\.\s", m.group(1) + " "):
                if tok.group(0).startswith("."):
                    break
                if tok.group(1):
                    file = tok.group(1)
                elif file:
                    named.append((file, tok.group(2)))
        if not named:
            problems.append(f"{src.name}: no `// aterm:` line names a file and an item")
        for file, name in named:
            theirs = (aterm / file).read_text()
            name = name.split("::")[-1]
            mine = _items(text, name) or _items(decommented, name)
            if not mine:
                problems.append(f"{src.name}: names `{name}` but holds no copy of it")
            for k, v in mine.items():
                t = _items(theirs, k).get(k)
                if t is None:
                    problems.append(f"{src.name}: `{k}` is not in aterm {file}")
                elif t != v:
                    problems.append(f"{src.name}: `{k}` differs from aterm {file}")
    for line in (rows_dir / "aterm_pin.tsv").read_text().splitlines():
        if line.startswith("#"):
            continue
        key, crate, row, digest = line.split("\t")
        clause = _specs_clause(aterm, crate, row)
        if clause is None:
            problems.append(f"{key}: aterm crates/{crate}/SPECS.md has no row {row}")
        elif hashlib.sha256(clause.encode()).hexdigest() != digest:
            problems.append(f"{key}: the clause of crates/{crate}/SPECS.md {row} changed since the pin")
    return problems


def pm1_aterm_pin(aterm: Path, rows_dir: Path = PM1_ROWS) -> str:
    """`aterm_pin.tsv` for the checkout `aterm`: each row's crate, SPECS.md row and the sha256
    of its clause cell (written with `--aterm DIR --pin` once the clauses there are read)."""
    lines = ["# GENERATED by `scripts/vf5_f1_producer.py --aterm DIR --pin` once each row's clause in that",
             "# checkout was read against its harness; `--aterm DIR` reports a clause changed since.",
             "# key\tcrate\tSPECS.md row\tsha256 of the row's clause cell"]
    for key, _, _, _, clause, _ in tsv_rows(rows_dir / "rows.tsv"):
        crate, specs, row = clause.split(" ", 3)[:3]
        assert specs == "SPECS.md", key
        row = row.rstrip(":")
        cell = _specs_clause(aterm, crate, row)
        assert cell is not None, f"{key}: crates/{crate}/SPECS.md has no row {row}"
        lines.append("\t".join([key, crate, row, hashlib.sha256(cell.encode()).hexdigest()]))
    return "\n".join(lines) + "\n"


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--aterm", type=Path, help="an aterm checkout: report the behind-PM-1 rows' drift from it, and stop")
    ap.add_argument("--pin", action="store_true", help="with --aterm: rewrite blobs/pm1_rows/aterm_pin.tsv from it")
    args = ap.parse_args()
    if args.aterm:
        if args.pin:
            (PM1_ROWS / "aterm_pin.tsv").write_text(pm1_aterm_pin(args.aterm))
        problems = pm1_aterm_drift(args.aterm)
        print("\n".join(problems) or f"blobs/pm1_rows matches aterm at {args.aterm}")
        return 1 if problems else 0
    build()
    rows_text, rows_report = rows_module()
    mut_text, mut_report = mutants_module()
    vf7_text, vf7_report = vf7_module()
    aterm_text, aterm_report = aterm_module()
    d2b_mods, d2b_report = d2b_rows_module()
    pm1_mods, pm1_report = pm1_rows_module()
    report = ("# GENERATED by scripts/vf5_f1_producer.py; a hand edit is drift (--check).\n"
              "# blob\trow\tfid\tsymbol\tgrade\tannotation (fid: [[coeffs, bound]])\tprecondition premise\tobligations\n"
              + "\n".join(rows_report) + "\n# mutants and twins\n" + "\n".join(mut_report) + "\n"
              + "\n".join(vf7_report) + "\n" + "\n".join(aterm_report) + "\n"
              + "\n".join(d2b_report) + "\n" + "\n".join(pm1_report) + "\n")
    targets = {FAMILY / "VF5Rows.lean": rows_text, FAMILY / "VF5MutantRows.lean": mut_text,
               FAMILY / "VF7Rows.lean": vf7_text, FAMILY / "VF5AtermRows.lean": aterm_text,
               FAMILY / "rows.out.tsv": report}
    targets.update({FAMILY / f"{n}.lean": t for n, t in d2b_mods})
    targets.update({FAMILY / f"{n}.lean": t for n, t in pm1_mods})
    if args.check:
        stale = [p.name for p, t in targets.items() if not p.exists() or p.read_text() != t]
        if stale:
            print("stale: " + ", ".join(stale) + " (regenerate)", file=sys.stderr)
            return 1
        print("VF5Rows.lean, VF5MutantRows.lean, VF7Rows.lean, VF5AtermRows.lean, VF5D2bRows*.lean, VF5PM1Rows*.lean and rows.out.tsv "
              "regenerate byte for byte")
        return 0
    for p, t in targets.items():
        p.write_text(t)
    print(report, end="")
    return 0


if __name__ == "__main__":
    sys.exit(main())
