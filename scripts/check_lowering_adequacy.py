#!/usr/bin/env python3
"""The LOWERING-ADEQUACY channel.

WHY THIS EXISTS, BEFORE THE THING IT WILL JUDGE
-----------------------------------------------
Closing A0's *bodyful reachable closure* requires a SECOND lowering into
trust-ir: MIR -> trust_ir, for cross-crate instances rustc will not hand THIR
for (`thir_body` takes a `LocalDefId`; `trust-mir-extract` early-returns on
`!def_id.is_local()`; the assembled module carries 0 core bodies of 13,906).
Design: `designs/2026-08-26-cross-crate-lowering-for-a0.md`.

Two lowerings into one IR means the module can contain functions produced by
different rules. If they disagree, every theorem over that module is about a
chimera. This script is the differential that says whether they agree — built
FIRST, deliberately, while the answer is still known and a demonstration is
still cheap. Once a second lowering exists there is something to blame, and a
channel nobody has seen fail is worth nothing.

WHAT IT DOES
------------
Compares two trust-ir text artifacts function-by-function and reports the
agreement fraction over the shared set.

THREE PROPERTIES, EACH A LESSON THIS TREE ALREADY PAID FOR
----------------------------------------------------------
1. FAIL-CLOSED. Any disagreement exits non-zero. A caller must treat a refusal
   as "do not splice", never as "splice anyway" -- the 2026-08-24 kernel panic
   came from a refusal path that was fail-OPEN.
2. NON-VACUOUS. A channel comparing two EMPTY sequences passes and means
   nothing: ~96% of `markers_exact` rows once did exactly that. So bodies with
   no instructions are counted and reported SEPARATELY, and an agreement
   computed only over empty bodies is refused outright.
3. REPORTED, NOT ASSERTED. The fractions are printed so anyone can re-derive
   them, and `--selftest` mutates real input to prove each verdict can fire.
"""
from __future__ import annotations
import argparse, hashlib, re, sys
from pathlib import Path

FN_RE = re.compile(r"^rustcc fn @(?P<name>.+?)\((?P<sig>[^)]*)\)\s*\{\s*$")


def split_functions(text: str) -> dict[str, list[str]]:
    """name -> body lines. Braces are column-0 anchored in this format."""
    out: dict[str, list[str]] = {}
    cur: str | None = None
    buf: list[str] = []
    for line in text.splitlines():
        m = FN_RE.match(line)
        if m:
            if cur is not None:
                out[cur] = buf
            cur, buf = m.group("name"), []
            continue
        if cur is not None:
            if line == "}":
                out[cur] = buf
                cur, buf = None, None if False else []
                cur = None
                continue
            buf.append(line)
    if cur is not None:
        out[cur] = buf
    return out


def canon(lines: list[str], *, keep_loc: bool) -> str:
    """Canonical form of one body.

    `#loc:` is DROPPED by default and the reason is not cosmetic: the two
    lowerings read the same spans but need not attribute them to the same
    instruction, and a location difference is not a semantic difference. It is
    kept under --with-loc so a caller who does care can ask.
    """
    out = []
    for ln in lines:
        s = ln.strip()
        if not s or s.startswith(";"):
            continue
        if not keep_loc:
            s = s.split("  ; #loc:")[0].split("; #loc:")[0].rstrip()
        out.append(s)
    return "\n".join(out)


def instr_count(lines: list[str]) -> int:
    return sum(1 for ln in lines if ln.strip() and not ln.strip().startswith((";", "bb")))


def compare(a_text: str, b_text: str, *, keep_loc: bool) -> dict:
    A, B = split_functions(a_text), split_functions(b_text)
    shared = sorted(set(A) & set(B))
    agree, differ, empty_both = [], [], []
    fwd, rev = {}, {}   # the SHARED global id bijection
    for n in shared:
        ia, ib = instr_count(A[n]), instr_count(B[n])
        if ia == 0 and ib == 0:
            empty_both.append(n)
            continue
        ca, cb = canon(A[n], keep_loc=keep_loc), canon(B[n], keep_loc=keep_loc)
        (agree if bodies_agree(ca, cb, fwd, rev) else differ).append(n)
    return {
        "a_functions": len(A), "b_functions": len(B),
        "shared": len(shared), "only_a": sorted(set(A) - set(B))[:20],
        "only_b": sorted(set(B) - set(A))[:20],
        "n_only_a": len(set(A) - set(B)), "n_only_b": len(set(B) - set(A)),
        "agree": len(agree), "differ": len(differ), "empty_both": len(empty_both),
        "differ_names": differ[:25],
    }


def report(r: dict) -> int:
    """Print, then decide. Returns the exit code."""
    nonvac = r["agree"] + r["differ"]
    print(f"  A functions {r['a_functions']}  B functions {r['b_functions']}  shared {r['shared']}")
    print(f"  only-in-A {r['n_only_a']}  only-in-B {r['n_only_b']}")
    print(f"  NON-VACUOUS compared: {nonvac}   (both-empty, not counted: {r['empty_both']})")
    if nonvac == 0:
        print("LOWERING_ADEQUACY=red  every shared body was EMPTY on both sides; an agreement "
              "computed over empty sequences is exactly the vacuity this channel exists to refuse")
        return 3
    frac = r["agree"] / nonvac
    print(f"  agree {r['agree']}  differ {r['differ']}   agreement {frac:.6f}")
    if r["differ"]:
        print("  first disagreements:")
        for n in r["differ_names"]:
            print(f"    {n[:110]}")
        print(f"LOWERING_ADEQUACY=red  {r['differ']} body(ies) disagree; a caller MUST NOT splice "
              "a body this channel refuses")
        return 1
    if r["n_only_b"]:
        print(f"LOWERING_ADEQUACY=ok  {r['agree']}/{nonvac} agree; B additionally carries "
              f"{r['n_only_b']} body(ies) A does not -- that is the cross-crate gain, and it is "
              "NOT evidence of agreement, only of coverage")
        return 0
    print(f"LOWERING_ADEQUACY=ok  {r['agree']}/{nonvac} agree (1.000000)")
    return 0


FIXTURE = Path(__file__).resolve().parent.parent / (
    "tests/fixtures/lowering_adequacy/real_excerpt.trust-ir.txt"
)


ID_RE = re.compile(r"\b(func|struct|enum|functy|global|closure_ty)\.(\d+)\b")


def id_bijection(a_lines, b_lines, fwd, rev):
    """Extend a SHARED global id map with this body's pairs; False on conflict.

    Trust (2026-08-27): the map is GLOBAL across the artifact pair, not per body.
    A per-body map is too weak, and this file's own selftest caught it: a body
    containing a single `global.N` would accept ANY replacement, because one id
    mapping to one other id is a consistent bijection when nothing else
    constrains it. Held globally, `func.6463 -> func.6464` in one body conflicts
    with `func.6463 -> func.6463` everywhere else, and the change is caught.

    This is what keeps the normaliser from being an erasure: renumbering is
    absorbed because it is consistent EVERYWHERE; a changed call target is not.
    """
    for la, lb in zip(a_lines, b_lines):
        ia = [(m.group(1), m.group(2)) for m in ID_RE.finditer(la)]
        ib = [(m.group(1), m.group(2)) for m in ID_RE.finditer(lb)]
        if len(ia) != len(ib) or ID_RE.sub(r"\1.#", la) != ID_RE.sub(r"\1.#", lb):
            return False
        for (ka, va), (kb, vb) in zip(ia, ib):
            if ka != kb:
                return False
            ea, eb = f"{ka}.{va}", f"{kb}.{vb}"
            if fwd.setdefault(ea, eb) != eb or rev.setdefault(eb, ea) != ea:
                return False
    return True


def bodies_agree(a_canon, b_canon, fwd, rev):
    """Equal outright, or equal under the SHARED global-id bijection."""
    # NO early return for identical bodies. An identical body still has to
    # REGISTER its ids as identity pairs, or it does not constrain the shared
    # map -- and this file's own selftest caught exactly that: body 1 mapping
    # `global.0 -> global.1` went unchallenged because body 2, which uses
    # `global.1 -> global.1`, short-circuited on equality and never recorded it.
    a_lines, b_lines = a_canon.splitlines(), b_canon.splitlines()
    if len(a_lines) != len(b_lines):
        return False
    return id_bijection(a_lines, b_lines, fwd, rev)


def selftest() -> int:
    """Every verdict must be reachable, and the arms mutate REAL producer text.

    The fixture is five bodies lifted verbatim out of a whole-crate clean-kernel
    dump (`clean_kernel.trust-ir.txt`, sha256:50ecdde3..., lane m-subj/dump_O3)
    -- four instruction-bearing and one genuinely empty, so even the vacuity arm
    runs on a real body rather than a hand-written imitation of one. An earlier
    revision of this selftest used a synthetic snippet while its own docstring
    claimed "REAL text"; checking the excerpt in is what makes the claim true and
    lets anyone replay the demonstration.

    Replayed at full scale on the source artifact (7,025 functions, 6,097
    non-vacuous): identity agrees 1.000000, and ONE mutated instruction inside
    ONE body reddens the channel and names that body. Fail-closed is exercised
    here rather than asserted.
    """
    if not FIXTURE.is_file():
        print(f"    [RED] fixture missing: {FIXTURE}")
        return 1
    base = FIXTURE.read_text()
    bodies = base.split("rustcc fn ")
    empties = ["rustcc fn " + b for b in bodies[1:] if "bb0" not in b]
    if not empties:
        print("    [RED] fixture carries no empty body; the vacuity arm cannot run")
        return 1
    if "const u64 5" not in base or "; #loc: 0 49 26" not in base:
        print("    [RED] fixture lost the anchors the arms mutate")
        return 1
    arms, ok = [], True

    def arm(name, a, b, want, keep_loc=False):
        nonlocal ok
        got = report(compare(a, b, keep_loc=keep_loc))
        good = got == want
        ok = ok and good
        arms.append((name, want, got, good))
        print(f"    [{'ok ' if good else 'RED'}] {name}: want {want}, got {got}\n")

    print("  arm: identical REAL input must AGREE")
    arm("identity", base, base, 0)
    print("  arm: ONE mutated instruction must DISAGREE")
    arm("mutated-instr", base, base.replace("const u64 5", "const u64 999999", 1), 1)
    print("  arm: a #loc-only difference must AGREE by default...")
    arm("loc-only-default", base, base.replace("; #loc: 0 49 26", "; #loc: 9 9 9"), 0)
    print("  arm: ...and DISAGREE under --with-loc")
    arm("loc-only-strict", base, base.replace("; #loc: 0 49 26", "; #loc: 9 9 9"), 1, keep_loc=True)
    print("  arm: CONSISTENT global renumbering must AGREE (the 2026-08-27 repair)")
    import re as _re
    def _shift(txt, delta):
        return _re.sub(r"\b(func|struct|enum|functy|global)\.(\d+)\b",
                       lambda m: f"{m.group(1)}.{int(m.group(2)) + delta}", txt)
    arm("renumber-consistent", base, _shift(base, 7), 0)
    print("  arm: ...but a changed CALL TARGET must still DISAGREE")
    one = base.replace("ptr_from_parts", "ptr_from_parts", 1)
    tgt = _re.sub(r"global_addr @global\.(\d+)",
                  lambda m: f"global_addr @global.{int(m.group(1)) + 1}", base, count=1)
    arm("target-change-caught", base, tgt, 1)
    print("  arm: an all-empty shared set must be REFUSED as vacuous")
    arm("vacuous", empties[0], empties[0], 3)
    print(f"  lowering-adequacy selftest: {sum(1 for *_, g in arms if g)}/{len(arms)} arms behave")
    return 0 if ok else 1


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("a", nargs="?", help="baseline trust-ir .txt artifact")
    p.add_argument("b", nargs="?", help="candidate trust-ir .txt artifact")
    p.add_argument("--with-loc", action="store_true", help="treat #loc differences as disagreement")
    p.add_argument("--selftest", action="store_true")
    args = p.parse_args()
    if args.selftest or not (args.a and args.b):
        print("lowering-adequacy selftest:")
        rc = selftest()
        if not (args.a and args.b):
            return rc
        if rc:
            return rc
    for f in (args.a, args.b):
        if not Path(f).is_file():
            print(f"LOWERING_ADEQUACY=red  no such artifact: {f}")
            return 2
    at, bt = Path(args.a).read_text(), Path(args.b).read_text()
    print(f"lowering adequacy:\n  A {args.a} sha256:{hashlib.sha256(at.encode()).hexdigest()[:16]}"
          f"\n  B {args.b} sha256:{hashlib.sha256(bt.encode()).hexdigest()[:16]}")
    return report(compare(at, bt, keep_loc=args.with_loc))


if __name__ == "__main__":
    sys.exit(main())
