#!/usr/bin/env python3
"""Does the DERIVED callee bundle close a target body's reachable call graph?

    scripts/crystal_sidecar_closure.py <dump_dir> <target-def-path> <out.json> [KEY=VALUE ...]
    scripts/crystal_sidecar_closure.py --self-test | --pinned-inputs

WHY THIS EXISTS.  A0's fifth criterion is a *bodyful reachable closure*: every
callee a body can transitively reach must itself have a body, so that a proof
about the body is a proof about a program and not about a promise.  For
`level::Level::is_zero` that criterion has been the crystal's open cell, and
`scripts/crystal_a0_census.py:139` states exactly why it stays open: the walk
requires every reachable callee to sit in the module's own spliced
instruction-bearing prefix, and no producer lowers a cross-crate monomorphic
instance into it.

The callee SIDECAR (`-Ztrust-ir-callee-sidecar=<filter>`, trust) changes the
input, not the criterion.  It publishes a SECOND artifact beside the crate
module -- the foreign callees' bodies, derived from their own monomorphized
upstream MIR -- with a manifest that joins each crate-module DECLARATION to the
sidecar member that carries its body.  So the question this script answers is
narrow and mechanical:

    walking the target's call graph in the crate module, which reached callees
    have no body there; of those, which does the sidecar manifest derive; and
    what is left over?

WHAT IT DOES NOT CLAIM.  Two artifacts are not one module.  A0's criterion AS
WRITTEN reads one spliced prefix, and this script does not rewrite it: a row
here says the closure is bodyful ACROSS the pair, naming the artifact each body
came from.  Teaching the census itself to read a sidecar is a separate act with
its own record.  Nor does a body being derived make it *correct*: that is links
3-5, per chain, elsewhere.

FAIL-CLOSED.  A `call_indirect` in the closure has no static target, so the
closure is not statically known and `closed` is False whatever else holds -- the
same disposition `crystal_a0_census.py` takes.  A declaration the manifest does
not join is left over and named.  A sidecar whose own manifest says
`closed: false` (an escaping edge, a refused member) cannot close anything, and
the verdict says so rather than counting its members.

Provenance KEY=VALUE pairs are recorded verbatim, the same contract
`crystal_a0_census.py` and `crystal_frontier_census.py` use.
"""

import json
import re
import sys
from pathlib import Path

if str(Path(__file__).resolve().parent) not in sys.path:
    sys.path.insert(0, str(Path(__file__).resolve().parent))
# The ONE reader of trust-ir's definition-site symbols (M2, 2026-09-27): trust-ir WS4.3 prints a
# non-bare name QUOTED; the reader decodes it, refuses what the printer cannot write, and holds
# the module to one grammar, so a target is found by its NAME whichever printer wrote the dump.
import crystal_trust_ir_symbols as tir_symbols  # noqa: E402

# Read by check_gate_registry.py (PINNED_INPUTS_MARKER): `--pinned-inputs` prints the first-party
# modules this script executes besides itself (derived from its imports).
ANSWERS_PINNED_INPUTS = True
CALL = re.compile(r"call @func\.(\d+)")
FNDEF = re.compile(r"fndef<func\.(\d+)>")
INDIRECT = re.compile(r"\bcall_indirect\b")


def parse_module(text):
    """Return (names, bodies) indexed by the dense FuncId the text addresses.

    Every `fn @NAME(functy.N) {` row takes the next id, defined bodies and
    bodyless declarations alike -- that is the numbering `call @func.N` uses,
    and it is the numbering `crystal_a0_census.py` walks.
    """
    names, bodies, cur = [], [], None
    syms = tir_symbols.ModuleSymbols(tir_symbols.RUSTCC_PREFIX)
    for ln_no, line in enumerate(text.splitlines(), 1):
        try:
            fh = syms.fn_header(line, f"line {ln_no}")
        except tir_symbols.SymbolRefusal as exc:
            raise SystemExit(f"trust-ir text line {ln_no}: {exc}")
        if fh is not None:
            names.append(fh[0])
            bodies.append([])
            cur = len(names) - 1
            continue
        if cur is not None:
            if line == "}":
                cur = None
            else:
                bodies[cur].append(line)
    return names, bodies


def instruction_bearing(body):
    """True when the row carries executable content rather than being a declaration.

    A declaration's block is empty or comment-only; a body has at least one line
    that is neither a comment (`;`) nor a block label (`bbN...`).
    """
    for line in body:
        stripped = line.strip()
        if not stripped or stripped.startswith(";") or stripped.startswith("bb"):
            continue
        return True
    return False


def walk(names, bodies, roots):
    """Transitive closure over call / fndef edges, recording indirect calls."""
    seen, stack, indirect = set(), list(roots), []
    while stack:
        i = stack.pop()
        if i in seen:
            continue
        seen.add(i)
        for line in bodies[i]:
            if INDIRECT.search(line):
                indirect.append({"in": names[i], "line": line.strip()})
            for pattern in (CALL, FNDEF):
                for m in pattern.finditer(line):
                    j = int(m.group(1))
                    if j < len(names) and j not in seen:
                        stack.append(j)
    return seen, indirect


def declaration_kind(name, local_def_paths):
    """LOCAL-UNLOWERED or FOREIGN, decided by the crate's own coverage rows.

    A bodyless row is named either by a plain def-path or, when that name collides,
    by `!trust_bodyless_instance::<def-path>::<definition>-<hex(key)>`
    (crate_module.rs `declaration_name`).  Recovering the def-path and asking whether
    the crate's coverage lists it as one of THIS crate's bodies separates two gaps that
    look identical in the text and are not the same problem:

      * LOCAL-UNLOWERED -- a body of this very crate that the producer declined to lower.
        No sidecar can help: the fix is in the producer's local lane.
      * FOREIGN -- a callee of another crate, which is exactly what the sidecar derives.

    A `!trust_bodyless_instance::` row whose recovered path is not in coverage is read as
    FOREIGN; that is the fail-open direction for this classification alone, and it is
    reported rather than hidden (`ambiguous_instance_rows`).
    """
    path = name
    ambiguous = False
    if path.startswith("!trust_bodyless_instance::"):
        path = path[len("!trust_bodyless_instance::") :]
        path = path.rsplit("::", 1)[0]
        ambiguous = True
    if path in local_def_paths:
        return "local-unlowered", path, False
    return "foreign", path, ambiguous


def census(dump, out, provenance):
    """Whole-crate: how many bodies have a bodyful closure, and what blocks the rest."""
    crate_text = next(iter(sorted(dump.glob("*.trust-ir.txt"))), None)
    if crate_text is None:
        print(f"no <crate>.trust-ir.txt in {dump}")
        return 1
    crate_name = crate_text.name[: -len(".trust-ir.txt")]
    coverage_path = dump / f"{crate_name}.coverage.json"
    if not coverage_path.exists():
        print(f"no coverage at {coverage_path} -- the census needs it to separate local-unlowered from foreign")
        return 1
    names, bodies = parse_module(crate_text.read_text())
    has_body = [instruction_bearing(b) for b in bodies]
    local_def_paths = {row["def_path"] for row in json.loads(coverage_path.read_text())["bodies"]}

    blocked, blockers, indirect_bodies = {}, {}, []
    for i, present in enumerate(has_body):
        if not present:
            continue
        reached, indirect = walk(names, bodies, [i])
        if indirect:
            indirect_bodies.append(names[i])
            continue
        decls = [j for j in reached if not has_body[j]]
        if decls:
            blocked[i] = decls
            for j in decls:
                blockers[j] = blockers.get(j, 0) + 1

    total = sum(1 for x in has_body if x)
    complete = total - len(blocked) - len(indirect_bodies)
    kinds, ambiguous = {}, 0
    for j in blockers:
        kind, _path, amb = declaration_kind(names[j], local_def_paths)
        kinds[kind] = kinds.get(kind, 0) + 1
        ambiguous += 1 if amb else 0
    only_foreign = only_local = mixed = 0
    for decls in blocked.values():
        ks = {declaration_kind(names[j], local_def_paths)[0] for j in decls}
        if ks == {"foreign"}:
            only_foreign += 1
        elif ks == {"local-unlowered"}:
            only_local += 1
        else:
            mixed += 1
    foreign_order = sorted(
        (j for j in blockers if declaration_kind(names[j], local_def_paths)[0] == "foreign"),
        key=lambda j: -blockers[j],
    )
    reach = []
    for k in (1, 5, 20, 100, len(foreign_order)):
        top = set(foreign_order[:k])
        gained = sum(1 for decls in blocked.values() if set(decls) <= top)
        reach.append({"top_foreign_declarations": k, "bodies_gained": gained, "closure_complete": complete + gained})

    def rows(predicate, limit):
        out_rows = []
        for j in sorted(blockers, key=lambda j: -blockers[j]):
            kind, path, _amb = declaration_kind(names[j], local_def_paths)
            if not predicate(kind):
                continue
            out_rows.append({"bodies_blocked": blockers[j], "kind": kind, "path": path})
            if len(out_rows) >= limit:
                break
        return out_rows

    report = {
        "schema": "crystal-sidecar-width-census-v1",
        "crate_module": {"path": str(crate_text), "functions": len(names), "instruction_bearing": total},
        "closure_complete_in_the_module_alone": complete,
        "blocked_by_declarations": len(blocked),
        "bodies_with_an_indirect_call": len(indirect_bodies),
        "distinct_blocking_declarations": len(blockers),
        "blocking_declarations_by_kind": kinds,
        "ambiguous_instance_rows": ambiguous,
        "blocked_only_by_foreign": only_foreign,
        "blocked_only_by_local_unlowered": only_local,
        "blocked_mixed": mixed,
        "top_foreign_blockers": rows(lambda k: k == "foreign", 20),
        "top_local_unlowered_blockers": rows(lambda k: k == "local-unlowered", 10),
        "reach_of_deriving_the_top_foreign_declarations": reach,
        "meaning": (
            "FOREIGN declarations are what the callee sidecar derives; LOCAL-UNLOWERED ones are "
            "bodies of this crate the producer declined to lower and no sidecar can reach them. "
            "A row here is closure ELIGIBILITY only -- it says nothing about whether a body is "
            "correct, which is links 3-5 and is per chain."
        ),
        "provenance": provenance,
    }
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(report, indent=2) + "\n")
    print(f"{total} instruction-bearing bodies; {complete} closure-complete in the module alone; "
          f"{len(blocked)} blocked; {len(indirect_bodies)} with an indirect call")
    print(f"  blockers: {len(blockers)} distinct {kinds}")
    print(f"  blocked only by FOREIGN declarations (sidecar-addressable): {only_foreign}; "
          f"only by LOCAL-UNLOWERED: {only_local}; mixed: {mixed}")
    for row in reach:
        print(f"  deriving the top {row['top_foreign_declarations']} foreign declarations -> "
              f"{row['closure_complete']} of {total} closure-complete")
    print(f"wrote {out}")
    return 0


def self_test():
    """M2 (2026-09-27): `parse_module` reads a module however trust-ir printed its symbols.

    A WS4.3 module (non-bare names QUOTED) gives the SAME dense names and bodies as its legacy
    twin -- the `fn @(.*)` regex this replaced kept the quotes, so a target named by its def path
    was never found -- and what no trust-ir printer writes is REFUSED."""
    legacy = ("rustcc fn @k::a<'_>(functy.0) {\nbb0:\n    %0 = call @func.1()\n    ret\n}\n"
              "fn @<k::S as k::T>::b(functy.1) {\n}\n")
    quoted = tir_symbols.respell_ws43(legacy)
    arms = []
    want = (["k::a<'_>", "<k::S as k::T>::b"], [["bb0:", "    %0 = call @func.1()", "    ret"], []])
    got = parse_module(legacy)
    arms.append(("a legacy module parses", got == want, got))
    got = parse_module(quoted)
    arms.append(("a WS4.3 quoted module parses to the SAME names and bodies",
                 '@"k::a<\'_>"' in quoted and got == want, got))
    walked = walk(*parse_module(quoted), [0])[0]
    arms.append(("the walk over the quoted module reaches the callee", walked == {0, 1}, walked))
    for tag, text, needle in (
            ("a module mixing quoted and raw symbols is REFUSED",
             quoted.replace('@"<k::S as k::T>::b"', "@<k::S as k::T>::b"), "mixes a QUOTED"),
            ("an escape the printer cannot write is REFUSED",
             quoted.replace('"k::a<\'_>"', '"k::a\\q"'), "is not one the trust-ir printer emits")):
        try:
            got = parse_module(text)
        except SystemExit as exc:
            arms.append((tag, needle in str(exc), f"refused by the wrong guard: {exc}"))
        else:
            arms.append((tag, False, f"parsed {got} instead of refusing"))
    bad = [(tag, why) for tag, ok, why in arms if not ok]
    for tag, why in bad:
        print(f"  [RED] self-test arm {tag}: {why}")
    print(f"crystal_sidecar_closure self-test: {len(arms) - len(bad)}/{len(arms)} arms behave")
    return 0 if not bad else 1


def main(argv):
    if len(argv) == 2 and argv[1] in ("--self-test", "--selftest"):
        return self_test()
    if len(argv) == 2 and argv[1] == "--pinned-inputs":
        print("\n".join(tir_symbols.first_party_imports(Path(__file__))))
        return 0
    if len(argv) >= 3 and argv[1] == "--census":
        prov = {}
        for pair in argv[4:]:
            key, _, value = pair.partition("=")
            prov[key] = value
        return census(Path(argv[2]), Path(argv[3]), prov)
    if len(argv) < 4:
        print(__doc__.strip().splitlines()[2].strip())
        return 2
    dump = Path(argv[1])
    target = argv[2]
    out = Path(argv[3])
    provenance = {}
    for pair in argv[4:]:
        if "=" not in pair:
            print(f"provenance argument {pair!r} is not KEY=VALUE")
            return 2
        key, value = pair.split("=", 1)
        provenance[key] = value

    crate_text = None
    for candidate in sorted(dump.glob("*.trust-ir.txt")):
        crate_text = candidate
        break
    if crate_text is None:
        print(f"no <crate>.trust-ir.txt in {dump}")
        return 1
    crate_name = crate_text.name[: -len(".trust-ir.txt")]
    manifest_path = dump / "callees" / f"{crate_name}.callees.manifest.json"
    if not manifest_path.exists():
        print(f"no sidecar manifest at {manifest_path} -- run the producer with -Ztrust-ir-callee-sidecar")
        return 1

    names, bodies = parse_module(crate_text.read_text())
    roots = [i for i, n in enumerate(names) if n == target]
    if len(roots) != 1:
        print(f"target {target!r} names {len(roots)} rows in {crate_text} -- expected exactly 1")
        return 1

    reached, indirect = walk(names, bodies, roots)
    declarations = sorted(i for i in reached if not instruction_bearing(bodies[i]))

    manifest = json.loads(manifest_path.read_text())
    derived = {}
    for root in manifest.get("roots", []):
        for func_id in root.get("crate_decl_func_ids", []):
            derived[func_id] = {
                "callee_def_path": root.get("callee_def_path"),
                "resolved": root.get("resolved"),
                "sidecar_func_id": root.get("sidecar_func_id"),
                "outcome": root.get("outcome"),
            }

    covered, left_over = [], []
    for i in declarations:
        row = {"crate_func_id": i, "name": names[i]}
        if i in derived and derived[i]["sidecar_func_id"] is not None:
            row.update(derived[i])
            covered.append(row)
        else:
            left_over.append(row)

    sidecar_closed = bool(manifest.get("closed"))
    closed = (
        not indirect
        and not left_over
        and sidecar_closed
        and manifest.get("lowering") == "ok"
    )
    report = {
        "schema": "crystal-sidecar-closure-v1",
        "target": target,
        "crate_module": {
            "path": str(crate_text),
            "functions": len(names),
            "instruction_bearing": sum(1 for b in bodies if instruction_bearing(b)),
        },
        "sidecar_manifest": {
            "path": str(manifest_path),
            "closed": sidecar_closed,
            "lowering": manifest.get("lowering"),
            "members": [m.get("name") for m in manifest.get("members", [])],
            "panic_terminals": manifest.get("panic_terminals", []),
            "escaping": manifest.get("escaping", []),
        },
        "closure": {
            "size": len(reached),
            "members": sorted(names[i] for i in reached),
            "declarations": len(declarations),
            "indirect_calls": indirect,
        },
        "derived_by_sidecar": covered,
        "left_over": left_over,
        "closed_across_the_pair": closed,
        "closed_meaning": (
            "every callee the target transitively reaches has a body -- in the crate module or, "
            "for a declaration the manifest joins by concrete key, in the sidecar -- with no "
            "indirect call anywhere in the walk, the sidecar's own bundle closed, and its lowering "
            "ok. It does NOT say A0's criterion 5 is met AS WRITTEN (that reads one spliced "
            "prefix), and it says nothing about whether a derived body is correct."
        ),
        "residual_panic_terminals": manifest.get("panic_terminals", []),
        "residual_meaning": (
            "a diverging panic/abort terminal is lowered `assert false; unreachable` with no call "
            "and needs no body; its unreachability is a separate proof obligation on the caller "
            "(for is_zero: ir_lzb_panic_path_is_unreachable)."
        ),
        "provenance": provenance,
    }
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(report, indent=2) + "\n")

    print(f"target {target}")
    print(f"  closure {len(reached)} function(s); {len(declarations)} without a body in the crate module")
    for row in covered:
        print(f"  DERIVED  func.{row['crate_func_id']} -> sidecar member {row['sidecar_func_id']}  {row['resolved']}")
    for row in left_over:
        print(f"  LEFT OVER func.{row['crate_func_id']}  {row['name'][:110]}")
    for row in indirect:
        print(f"  INDIRECT in {row['in']}: {row['line'][:100]}")
    print(f"  sidecar closed={sidecar_closed} lowering={manifest.get('lowering')} terminals={manifest.get('panic_terminals')}")
    print(f"CLOSED ACROSS THE PAIR: {closed}")
    print(f"wrote {out}")
    return 0 if closed else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv))
