#!/usr/bin/env python3
"""Re-derive the crystal FRONTIER TABLE from a whole-crate trust-ir dump.

    scripts/crystal_frontier_census.py <dump_O3> <dump_O0> <O3.flip.txt> <O0.flip.txt> \
        <out.json> [KEY=VALUE ...]
    scripts/crystal_frontier_census.py --self-test | --pinned-inputs

Trailing `KEY=VALUE` pairs are recorded VERBATIM under `provenance`. They are
the only fields this script cannot derive -- which driver seal produced the
dumps, what `guard` said, which revisions the two repos were at -- and a run
that omits them writes an artifact that cannot be attributed. Supply them.

WHY THIS EXISTS.  `data/crystal_frontier_census_2026-08-16.json` recorded
`call` and `gep` at ZERO chained flips, and that table was quoted for four days
after five producer waves (GS, CP, DR, W3, W3b) had moved it.  The table was
re-derived by hand each time, which is why it went stale silently.  This script
is the derivation, committed, so the numbers can be re-taken rather than
trusted.

WHAT IT READS, AND NOTHING ELSE.  Four files produced by ONE sealed-driver
whole-crate compile of `clean-kernel`:

  * `<dump>/clean_kernel.coverage.json` — one row per body: `def_index`,
    `func_id`, `lineage`, the derived-MIR `verdict` and `markers_exact`.
  * `<dump>/clean_kernel.trust-ir.txt`  — the emitted module, from which the
    per-body INSTRUCTION census and the call graph are parsed.
  * the two `RUSTC_LOG=rustc_mir_transform::trust_ir_flip=info` logs — the flip
    events, joined to coverage rows by `def_index` WITHIN the compile.

  `def_index` is NOT stable across HEADs.  Joining across two compiles is a
  defect; this script never does it.

THE TWO INDEX FACTS IT DEPENDS ON, both re-checked on every run:

  1. The `rustcc fn @…` entries in the text are a BODY PREFIX followed by
     body-less DECLARATIONS, and the ordinal of a body equals its coverage
     `func_id` — so `@func.N` for N inside the prefix resolves to that body.
     Measured on the 2026-08-20 tip dump: 7,494 entries = 6,392 bodies + 1,102
     empty declarations, `totals.spliced` = 6,392, and 8,151 of the 14,591 call
     sites name a callee inside the prefix, which is exactly
     `totals.calls.resolved`.  `verify_prefix` asserts the split; a run whose
     dump violates it FAILS rather than reporting a number.
  2. Therefore `bodyful_reachable_closure` is decidable from the text alone: a
     body's closure is bodyful iff every transitively reachable `@func.N` is
     inside the body prefix.  A callee at or above the prefix is a DECLARATION
     with no body — `ir_call_exec` would go stuck on it — and the closure fails.
"""

import collections
import json
import os
import re
import sys
import tempfile

if os.path.dirname(os.path.abspath(__file__)) not in sys.path:
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
# The ONE reader of trust-ir's definition-site symbols (M2, 2026-09-27): trust-ir WS4.3 prints a
# non-bare name QUOTED; the reader decodes it, refuses what the printer cannot write, and holds
# the module to one grammar, so a body's name is compared with its coverage `def_path` as a NAME.
import crystal_trust_ir_symbols as tir_symbols  # noqa: E402

# Read by check_gate_registry.py (PINNED_INPUTS_MARKER): `--pinned-inputs` prints the first-party
# modules this script executes besides itself (derived from its imports).
ANSWERS_PINNED_INPUTS = True
CALL = re.compile(r"call @func\.(\d+)")
ASSIGN = re.compile(r"^\s+%\d+ = ([a-z_]+)")
BARE = re.compile(r"^\s+([a-z_]+)")
BLOCK = re.compile(r"^bb\d+")
DID = re.compile(r"did=DefId\(0:(\d+) ~")
LINEAGE = re.compile(r"lineage=(sha256:[0-9a-f]+)")

# The constructs the frontier table tracks. `gep` and `call` are the two the
# 2026-08-16 census recorded at zero and the reason this script exists; the rest
# are carried so the table is a census and not a two-row claim.
CONSTRUCTS = (
    "gep",
    "call",
    "load",
    "store",
    "insertfield",
    "extractfield",
    "switch",
    "icmp",
)


def parse_ir(path):
    """Every `fn @…` entry in emission order: opcode census and callee set."""
    funcs, cur = [], None
    syms = tir_symbols.ModuleSymbols(tir_symbols.RUSTCC_PREFIX)
    for ln_no, ln in enumerate(open(path, encoding="utf-8", errors="replace"), 1):
        s = ln.rstrip("\n")
        try:
            fh = syms.fn_header(s, f"line {ln_no}")
        except tir_symbols.SymbolRefusal as exc:
            raise SystemExit(f"trust-ir text {path} line {ln_no}: {exc}")
        if fh is not None:
            cur = {"name": fh[0], "ops": collections.Counter(), "callees": set()}
            funcs.append(cur)
            continue
        if cur is None:
            continue
        if s.startswith("}"):
            cur = None
            continue
        body = s.strip()
        if body and not body.startswith(";") and not BLOCK.match(body):
            m = ASSIGN.match(s) or BARE.match(s)
            if m:
                cur["ops"][m.group(1)] += 1
        for c in CALL.finditer(s):
            cur["callees"].add(int(c.group(1)))
    return funcs


def verify_prefix(funcs, cov):
    """Fail closed on the two index facts the whole census rests on."""
    n = sum(1 for f in funcs if sum(f["ops"].values()) > 0)
    for i, f in enumerate(funcs):
        if (sum(f["ops"].values()) > 0) != (i < n):
            raise SystemExit(
                f"index fact 1 violated: entry {i} ({f['name']}) breaks the "
                "body-prefix / declaration-suffix split"
            )
    if n != cov["totals"]["spliced"]:
        raise SystemExit(
            f"index fact 1 violated: {n} bodies in the text, "
            f"{cov['totals']['spliced']} spliced in coverage"
        )
    for b in cov["bodies"]:
        fid = b["func_id"]
        if fid is None:
            continue
        # The text decorates an initializer body's name with the kind of
        # initializer it is (`::{const-init}` / `::{static-init}`); coverage
        # carries the undecorated path. Strip the suffix, do not fuzzy-match.
        name = re.sub(r"::\{(?:const|static)-init\}$", "", funcs[fid]["name"]) if fid < n else ""
        if fid >= n or name != b["def_path"]:
            raise SystemExit(
                f"index fact 1 violated: coverage func_id {fid} is "
                f"{b['def_path']}, the text's ordinal {fid} is "
                f"{funcs[fid]['name'] if fid < len(funcs) else '<out of range>'}"
            )
    # Index fact 2: every `@func.N` names an entry of THIS table -- there is no
    # callee id outside it -- and at least one resolves inside the body prefix.
    # Without the range check a stray id would be silently read as "declaration,
    # closure not bodyful", which is the fail-closed direction but for the wrong
    # reason; with it, a producer that changed the id space FAILS here.
    ids = [c for f in funcs for c in f["callees"]]
    if ids and max(ids) >= len(funcs):
        raise SystemExit(
            f"index fact 2 violated: callee id {max(ids)} is outside the "
            f"{len(funcs)}-entry function table"
        )
    if not any(c < n for c in ids):
        raise SystemExit("index fact 2 violated: no call resolves inside the body prefix")
    return n


def parse_flips(path):
    """-> (codegen, ctfe, fallback), each `def_index` -> lineage / raw line."""
    cod, ctfe, fb = {}, {}, {}
    for ln in open(path, encoding="utf-8", errors="replace"):
        if "trust-ir-flip:" not in ln:
            continue
        m = DID.search(ln)
        if not m:
            continue
        di = int(m.group(1))
        lm = LINEAGE.search(ln)
        lin = lm.group(1) if lm else None
        if "CTFE compiled from trust" in ln:
            ctfe[di] = lin
        elif "compiled from trust" in ln:
            cod[di] = lin
        elif "FALLBACK to built MIR" in ln:
            fb[di] = ln.strip()
    return cod, ctfe, fb


def self_test():
    """M2 (2026-09-27): `parse_ir` reads a module however trust-ir printed its symbols.

    A WS4.3 module (non-bare names QUOTED) parses to the SAME decoded names, opcodes and callees as
    its legacy twin -- the `fn @(.*)` regex this replaced kept the quotes in the name, so every
    body missed its coverage `def_path` -- and what no trust-ir printer writes is REFUSED."""
    legacy = ("rustcc fn @k::a<'_>(functy.0) {\nbb0:\n    %0 = call @func.1()\n    ret\n}\n"
              "rustcc fn @<k::S as k::T>::b(functy.1) {\n}\n")
    quoted = tir_symbols.respell_ws43(legacy)
    arms = []
    with tempfile.TemporaryDirectory() as d:
        def parse(text):
            path = os.path.join(d, "m.trust-ir.txt")
            with open(path, "w", encoding="utf-8") as fh:
                fh.write(text)
            return [(f["name"], dict(f["ops"]), sorted(f["callees"])) for f in parse_ir(path)]

        want = [("k::a<'_>", {"call": 1, "ret": 1}, [1]), ("<k::S as k::T>::b", {}, [])]
        got = parse(legacy)
        arms.append(("a legacy module parses", got == want, got))
        got = parse(quoted)
        arms.append(("a WS4.3 quoted module parses to the SAME names, opcodes and callees",
                     '@"k::a<\'_>"' in quoted and got == want, got))
        for tag, text, needle in (
                ("a module mixing quoted and raw symbols is REFUSED",
                 quoted.replace('@"<k::S as k::T>::b"', "@<k::S as k::T>::b"), "mixes a QUOTED"),
                ("an escape the printer cannot write is REFUSED",
                 quoted.replace('"k::a<\'_>"', '"k::a\\q"'), "is not one the trust-ir printer emits")):
            try:
                got = parse(text)
            except SystemExit as exc:
                arms.append((tag, needle in str(exc), f"refused by the wrong guard: {exc}"))
            else:
                arms.append((tag, False, f"parsed {got} instead of refusing"))
    bad = [(tag, why) for tag, ok, why in arms if not ok]
    for tag, why in bad:
        print(f"  [RED] self-test arm {tag}: {why}")
    print(f"crystal_frontier_census self-test: {len(arms) - len(bad)}/{len(arms)} arms behave")
    return 0 if not bad else 1


def main(argv):
    if len(argv) == 2 and argv[1] in ("--self-test", "--selftest"):
        raise SystemExit(self_test())
    if len(argv) == 2 and argv[1] == "--pinned-inputs":
        from pathlib import Path  # noqa: PLC0415 -- this flag's only use
        print("\n".join(tir_symbols.first_party_imports(Path(__file__))))
        return
    if len(argv) < 6:
        raise SystemExit(__doc__)
    d3, d0, f3, f0, out = argv[1:6]
    provenance = {}
    for kv in argv[6:]:
        if "=" not in kv:
            raise SystemExit(f"provenance argument {kv!r} is not KEY=VALUE")
        k, v = kv.split("=", 1)
        provenance[k] = v
    cov = json.load(open(d3 + "/clean_kernel.coverage.json", encoding="utf-8"))
    funcs = parse_ir(d3 + "/clean_kernel.trust-ir.txt")
    nb = verify_prefix(funcs, cov)
    cod3, ctfe3, fb3 = parse_flips(f3)
    cod0, ctfe0, fb0 = parse_flips(f0)

    rows = []
    for b in cov["bodies"]:
        fid = b["func_id"]
        f = funcs[fid] if fid is not None else None
        dm = b["differentials"].get("derived_mir", {})
        rows.append(
            {
                "def_path": b["def_path"],
                "def_index": b["def_index"],
                "func_id": fid,
                "lineage": b.get("lineage"),
                "instr": b.get("instr_count", 0),
                "verdict": dm.get("verdict"),
                "markers_exact": bool(dm.get("markers_exact")),
                "markers_detail": dm.get("markers_detail", ""),
                "ops": f["ops"] if f else collections.Counter(),
                "callees": f["callees"] if f else set(),
            }
        )

    closures = {}

    def closure(r):
        fid = r["func_id"]
        if fid in closures:
            return closures[fid]
        seen, stack, ok = set(), list(r["callees"]), True
        while stack:
            c = stack.pop()
            if c in seen:
                continue
            seen.add(c)
            if c >= nb:
                ok = False
                continue
            stack.extend(funcs[c]["callees"])
        closures[fid] = (ok, seen)
        return closures[fid]

    constructs = {}
    for con in CONSTRUCTS:
        carry = [r for r in rows if r["ops"].get(con, 0) > 0]
        ag = [r for r in carry if r["verdict"] == "agreed"]
        constructs[con] = {
            "carry": len(carry),
            "agreed": len(ag),
            "markers_exact": sum(1 for r in ag if r["markers_exact"]),
            "bodyful_closure": sum(1 for r in carry if closure(r)[0]),
            "agreed_and_bodyful": sum(1 for r in ag if closure(r)[0]),
            "flip_O3": sum(1 for r in carry if r["def_index"] in cod3),
            "flip_O0": sum(1 for r in carry if r["def_index"] in cod0),
            "ctfe_O3": sum(1 for r in carry if r["def_index"] in ctfe3),
            "ctfe_O0": sum(1 for r in carry if r["def_index"] in ctfe0),
            "flip_O3_bodies": sorted(
                r["def_path"] for r in carry if r["def_index"] in cod3
            ),
        }

    def chainable(flips):
        return [
            r
            for r in rows
            if r["def_index"] in flips
            and r["markers_exact"]
            and r["verdict"] == "agreed"
            and closure(r)[0]
        ]

    ch3, ch0 = chainable(cod3), chainable(cod0)
    census3 = collections.Counter()
    for r in ch3:
        census3.update(r["ops"])

    result = {
        "schema": "clean.crystal.frontier_census/2",
        "provenance": provenance,
        "inputs": {"dump_O3": d3, "dump_O0": d0, "flip_O3": f3, "flip_O0": f0},
        "index_facts": {
            "text_entries": len(funcs),
            "bodies": nb,
            "declarations": len(funcs) - nb,
            "coverage_spliced": cov["totals"]["spliced"],
            "coverage_declarations": cov["totals"]["declarations"],
        },
        "totals": {
            "bodies": cov["totals"]["bodies"],
            "instr": cov["totals"]["instr_count"],
            "derived_mir_agreed": sum(1 for r in rows if r["verdict"] == "agreed"),
            "markers_exact": sum(
                1 for r in rows if r["verdict"] == "agreed" and r["markers_exact"]
            ),
            "markers_exact_nonvacuous": sum(
                1
                for r in rows
                if r["verdict"] == "agreed"
                and r["markers_exact"]
                and not r["markers_detail"].startswith("0 marker line(s)")
            ),
            "codegen_flips_O3": len(cod3),
            "codegen_flips_O0": len(cod0),
            "ctfe_flips_O3": len(ctfe3),
            "ctfe_flips_O0": len(ctfe0),
            "loud_fallbacks_O3": len(fb3),
            "loud_fallbacks_O0": len(fb0),
        },
        "constructs": constructs,
        "chainable_O3": {
            "count": len(ch3),
            "instruction_census": dict(census3.most_common()),
            "bare_ret_only": sum(
                1 for r in ch3 if sum(r["ops"].values()) == r["ops"].get("ret", 0)
            ),
            "carrying_gep_or_call": sorted(
                (
                    {
                        "def_path": r["def_path"],
                        "def_index": r["def_index"],
                        "func_id": r["func_id"],
                        "instr": r["instr"],
                        "lineage": r["lineage"],
                        "markers_detail": r["markers_detail"],
                        "ops": dict(r["ops"]),
                    }
                    for r in ch3
                    if r["ops"].get("gep") or r["ops"].get("call")
                ),
                key=lambda x: x["def_index"],
            ),
        },
        "chainable_O0_count": len(ch0),
        "call_bodies_with_a_bodyful_closure": sorted(
            (
                {
                    "def_path": r["def_path"],
                    "def_index": r["def_index"],
                    "verdict": r["verdict"],
                    "markers_exact": r["markers_exact"],
                    "flip_O3": r["def_index"] in cod3,
                    "flip_O0": r["def_index"] in cod0,
                    "reachable": len(closure(r)[1]),
                }
                for r in rows
                if r["ops"].get("call") and closure(r)[0]
            ),
            key=lambda x: x["def_index"],
        ),
    }
    json.dump(result, open(out, "w", encoding="utf-8"), indent=1)

    print(f"index: {len(funcs)} entries = {nb} bodies + {len(funcs) - nb} declarations")
    print(
        f"codegen flips  O3={len(cod3)}  O0={len(cod0)}   "
        f"ctfe O3={len(ctfe3)} O0={len(ctfe0)}   "
        f"loud fallbacks O3={len(fb3)} O0={len(fb0)}"
    )
    hdr = (
        f"{'construct':<13}{'carry':>7}{'agreed':>8}{'mk_exact':>10}"
        f"{'bodyful':>9}{'ag+bf':>7}{'flipO3':>8}{'flipO0':>8}"
    )
    print(hdr)
    for con in CONSTRUCTS:
        c = constructs[con]
        print(
            f"{con:<13}{c['carry']:>7}{c['agreed']:>8}{c['markers_exact']:>10}"
            f"{c['bodyful_closure']:>9}{c['agreed_and_bodyful']:>7}"
            f"{c['flip_O3']:>8}{c['flip_O0']:>8}"
        )
    print(
        f"chainable at -O3: {len(ch3)}  (bare-ret-only "
        f"{result['chainable_O3']['bare_ret_only']})"
    )
    print(f"chainable instruction census: {result['chainable_O3']['instruction_census']}")
    for r in result["chainable_O3"]["carrying_gep_or_call"]:
        print(f"  gep/call chainable: {r['def_path']} di={r['def_index']} ops={r['ops']}")
    print(f"wrote {out}")


if __name__ == "__main__":
    main(sys.argv)
