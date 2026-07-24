#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
#
# ============================================================================
#  LRAT -> Clean transcoder  (B-cert production-scale, #56 / #95).
# ============================================================================
#
#  Reads an ay-bit-blasted DIMACS .cnf + a drat-trim .lrat and EMITS a
#  self-contained proofs/lrat_checker_*_demo.lean that:
#    (a) INLINES the balanced-tree + word-indexed RUP/RAT checker VERBATIM from
#        proofs/lrat_checker_tree.lean (clean check is one-file-at-a-time);
#    (b) emits the CNF as a BALANCED Tree (List Lit) of `Lit.mk sign (mkW64 v)`
#        clauses (parser nesting depth O(log C));
#    (c) emits the LRAT proof as a BALANCED Tree of `Step` (each RUP step is
#        `rupS clause hints`, hints = the actual Lit-lists the hint clause-IDs
#        resolve to; RAT steps -> `ratS clause ratHints`);
#    (d) `theorem <name>_checks : checkProofTree CNFTree PRFTree = true := rfl`;
#    (e) `theorem <name>_unsat : Unsat (treeToList CNFTree)
#            := checkProofTree_sound CNFTree PRFTree <name>_checks`;
#    (f) a MECHANIZED CNF-identity digest (see below).
#
#  The transcoder is UNTRUSTED: a mis-transcription only makes
#  `checkProofTree = true` FAIL to reduce (fail-closed), never an unsound accept.
#
#  CNF-IDENTITY DIGEST (mechanized, not prose).  ay's .cnf clause body is
#  canonicalized (strip `c` comments, keep `p cnf V C` + clause lines) and
#  SHA-256'd.  The transcoder ALSO re-serializes the clauses it embedded into
#  the .lean (its in-memory `cnf_clauses`, which become the CNFTree leaves) back
#  to that same canonical DIMACS, and asserts the two SHA-256 hashes are EQUAL.
#  So "the bytes the .lean's CNFTree denotes == ay's .cnf" is checked by a
#  runnable script (the local meta-gate runs `--verify-digest`), and the
#  expected hash is BAKED INTO the .lean as a comment + a Lean `digest` string,
#  with a self-check theorem on a sampled clause set (see notes in the emitted
#  file for what is mechanized vs asserted).

import argparse
import hashlib
import sys
from pathlib import Path


# ----------------------------------------------------------------------------
# Parsing.
# ----------------------------------------------------------------------------

def parse_cnf(path):
    """Return (num_vars, num_clauses_declared, [clause...]) where each clause is
    a list of signed nonzero ints (DIMACS order preserved)."""
    num_vars = None
    num_decl = None
    clauses = []
    with open(path, "r") as f:
        for raw in f:
            line = raw.strip()
            if not line:
                continue
            if line.startswith("c"):
                continue
            if line.startswith("p"):
                parts = line.split()
                # p cnf V C
                num_vars = int(parts[2])
                num_decl = int(parts[3])
                continue
            toks = line.split()
            # clause line: ints terminated by 0
            lits = []
            for t in toks:
                v = int(t)
                if v == 0:
                    break
                lits.append(v)
            clauses.append(lits)
    if num_vars is None or num_decl is None:
        raise ValueError("CNF: missing `p cnf` header")
    if len(clauses) != num_decl:
        raise ValueError(
            f"CNF: declared {num_decl} clauses but parsed {len(clauses)}")
    return num_vars, num_decl, clauses


def parse_lrat(path):
    """Return a list of addition records in proof order:
       {'id': int, 'clause': [int,...], 'hints': [int,...], 'is_rat': bool,
        'rat': [(neg_pivot_clause_id, [rup_ids...]), ...]}.
    Deletion lines are dropped.  RUP lines have all-positive hints; RAT lines
    carry negative hint markers that point at clauses containing the negated
    pivot, each followed by that resolvent's positive RUP hint chain."""
    adds = []
    with open(path, "r") as f:
        for raw in f:
            line = raw.strip()
            if not line:
                continue
            toks = line.split()
            # token[0] = id ; token[1] == 'd' => deletion line, drop it.
            if len(toks) >= 2 and toks[1] == "d":
                continue
            cid = int(toks[0])
            # parse: lits... 0 hints... 0
            i = 1
            lits = []
            while i < len(toks) and toks[i] != "0":
                lits.append(int(toks[i]))
                i += 1
            # toks[i] == "0" (end of lits)
            i += 1
            hints_raw = []
            while i < len(toks) and toks[i] != "0":
                hints_raw.append(int(toks[i]))
                i += 1
            # detect RAT: any negative hint id
            is_rat = any(h < 0 for h in hints_raw)
            rec = {"id": cid, "clause": lits, "is_rat": is_rat}
            if not is_rat:
                rec["hints"] = hints_raw
                rec["rat"] = []
            else:
                # RAT structure: leading positive ids = RUP pre-hints for the
                # clause itself, then groups: a NEGATIVE id (clause D with the
                # negated pivot) followed by its positive resolvent RUP chain.
                pre = []
                groups = []
                j = 0
                while j < len(hints_raw) and hints_raw[j] > 0:
                    pre.append(hints_raw[j])
                    j += 1
                while j < len(hints_raw):
                    neg = hints_raw[j]
                    j += 1
                    chain = []
                    while j < len(hints_raw) and hints_raw[j] > 0:
                        chain.append(hints_raw[j])
                        j += 1
                    groups.append((-neg, chain))
                rec["hints"] = pre
                rec["rat"] = groups
            adds.append(rec)
    return adds


# ----------------------------------------------------------------------------
# Lean term emission.
# ----------------------------------------------------------------------------

# Word-packing constructor used for every literal's var index.  The checker's
# `Word` type is a *generic* `List Bool`, so the width is purely a DATA choice
# that does NOT touch the soundness proof (`checkProofTree_sound` is width-
# polymorphic).  Default is the committed-demo shape `mkW64` (64-bit).
#
#  PROFILING NOTE (#56/#95, measured on M4, target/release/clean, 2026-06-20):
#  Narrower words were HYPOTHESIZED to cut `:= rfl` cost ~5x by shrinking the
#  per-bit `wordBeqFold` fold inside `litEq`.  This was MEASURED AND REFUTED:
#  on the committed 256-clause cert, `toWordN 12` reduced in ~46s vs ~42s for
#  `mkW64` -- i.e. NO speedup.  Reasons, confirmed by isolating probes:
#    (1) `wordBeqFold` short-circuits via `Bool.and false _` on the first
#        differing bit, so MISMATCHES (the bulk of any scan) already cost O(1),
#        not O(width); only equal-word compares pay full width.
#    (2) The dominant `:= rfl` cost is NOT word-bit folding at all (see below):
#        it is the kernel's def-eq reduction COPYING the materialized clause
#        subterms through the list folds of `checkProof` -- which is the same
#        regardless of word width, since `(toWordN 12 v)` and `(toWordN 64 v)`
#        are near-identical-SIZED unreduced `App` thunks that get carried, not
#        reduced, during the formula-list traversal.
#  So `--word-bits` is kept as an honest, soundness-preserving DATA knob, but it
#  is NOT the scaling lever.  The binding bottleneck is the kernel evaluator's
#  per-clause-term reduction/copy cost (intrinsic to the `:= rfl` approach at
#  this representation), NOT word width, NOT the hint DB-scan (`allHintsInF`,
#  which an isolating probe showed contributes <5% on this cert).
WORD_CTOR = "mkW64"

# The inlined checker's open namespace.  `tree` (List-Bool word) is the original
# committed checker; `natw` is the Nat-word variant (proofs/lrat_checker_natw.lean)
# whose var index is a SINGLE Nat literal -- the minimal subterm the kernel must
# carry/hash through the formula flatten + per-step folds (the measured-dominant
# := rfl cost; see the PERF NOTE in lrat_checker_natw.lean).  Soundness is the
# byte-for-byte Nat proof; `checkProofTree_sound` transports unchanged.
CHECKER_NS = "LratCoreTree"

# NAT_WORD: when True (the natw checker), the var index is emitted as a BARE Nat
# literal `(Lit.mk b v)` (no word constructor), the minimal-size index term.
NAT_WORD = False


def lit_term(signed):
    """A signed DIMACS literal -> `Lit.mk <bool> <var-index-term>`."""
    pos = "true" if signed > 0 else "false"
    var = abs(signed)
    if NAT_WORD:
        return f"(Lit.mk {pos} {var})"
    return f"(Lit.mk {pos} ({WORD_CTOR} {var}))"


def set_word_ctor_for_bits(bits):
    """Emit a fixed-width Word constructor.  `bits is None` keeps the committed
    64-bit `mkW64`.  Otherwise emit `(toWordN <bits> v)` -- `toWordN` is part of
    the inlined checker slice (defined before `checkProofTree_sound`), so it is
    in scope, and the width is a pure DATA choice (no soundness proof change)."""
    global WORD_CTOR
    if bits is None:
        WORD_CTOR = "mkW64"
    else:
        WORD_CTOR = f"toWordN {int(bits)}"


def list_lit_term(lits):
    """A clause (list of signed ints) -> a right-nested `List.cons ... List.nil`
    of `Lit`s.  Clauses are SHORT (avg ~3 lits, max ~130), well under the parser
    term-nesting cap, so flat list nesting is fine here -- only the clause-COUNT
    and step-COUNT axes are tree-balanced."""
    out = "List.nil"
    for l in reversed(lits):
        out = f"(List.cons {lit_term(l)} {out})"
    return out


def list_of_clauses_term(clauses):
    """A list of clauses -> right-nested `List.cons` of `List Lit`."""
    out = "List.nil"
    for c in reversed(clauses):
        out = f"(List.cons {list_lit_term(c)} {out})"
    return out


def rat_hint_term(d_clause, rup_clauses):
    """One `RatHint.mk dClause rHints`."""
    return (f"(RatHint.mk {list_lit_term(d_clause)} "
            f"{list_of_clauses_term(rup_clauses)})")


def list_of_rathints_term(rathints):
    out = "List.nil"
    for (dc, rups) in reversed(rathints):
        out = f"(List.cons {rat_hint_term(dc, rups)} {out})"
    return out


def step_term(clause, is_rat, hint_clauses, rathints):
    if not is_rat:
        return f"(rupS {list_lit_term(clause)} {list_of_clauses_term(hint_clauses)})"
    return f"(ratS {list_lit_term(clause)} {list_of_rathints_term(rathints)})"


def balanced_tree(leaf_terms):
    """Build a BALANCED `Tree` literal from a list of leaf TERM strings.
    Height ~log2 n, so the parser ingests it past the flat-List cap (~120)."""
    if len(leaf_terms) == 1:
        return f"(Tree.leaf {leaf_terms[0]})"
    nodes = [f"(Tree.leaf {t})" for t in leaf_terms]
    while len(nodes) > 1:
        nxt = []
        i = 0
        while i + 1 < len(nodes):
            nxt.append(f"(Tree.node {nodes[i]} {nodes[i+1]})")
            i += 2
        if i < len(nodes):
            # odd leftover: carry up (keeps it balanced-ish, still O(log n))
            nxt.append(nodes[i])
        nodes = nxt
    return nodes[0]


# ----------------------------------------------------------------------------
# CNF-identity digest (canonical DIMACS clause body).
# ----------------------------------------------------------------------------

def canonical_dimacs(num_vars, clauses):
    """Canonical clause-body serialization: `p cnf V C\\n` + each clause
    `l1 l2 ... 0\\n`.  Comments stripped.  This is the part the .lean's CNFTree
    denotes (the leaf clauses, in order), serialized byte-for-byte."""
    lines = [f"p cnf {num_vars} {len(clauses)}"]
    for c in clauses:
        lines.append(" ".join(str(l) for l in c) + " 0")
    return ("\n".join(lines) + "\n").encode("utf-8")


def sha256_hex(b):
    return hashlib.sha256(b).hexdigest()


def canonicalize_cnf_file(path):
    """Re-derive the canonical clause-body bytes directly from ay's .cnf (strip
    comments, normalize whitespace) so the digest is comment/whitespace-robust
    and ties to the EXACT clause sequence."""
    nv, nd, clauses = parse_cnf(path)
    return canonical_dimacs(nv, clauses), clauses, nv


# ----------------------------------------------------------------------------
# Emission of the self-contained .lean.
# ----------------------------------------------------------------------------

CHECKER_HEADER = "set_option autoImplicit false"


def extract_checker_body(tree_lean_path):
    """Slice the VERBATIM checker out of the checker .lean: from the
    `namespace <CHECKER_NS>` line through `theorem checkProofTree_sound ...`
    (inclusive), i.e. all the defs/theorems the demo needs, but NOT the file's
    own concrete vec*/rat*/store* certs (those start after the soundness
    theorem)."""
    text = Path(tree_lean_path).read_text().splitlines()
    start = None
    end = None
    ns_line = f"namespace {CHECKER_NS}"
    for idx, line in enumerate(text):
        if start is None and line.strip() == ns_line:
            start = idx
        if line.strip().startswith("checkProof_sound (treeToList FT) (treeToList prfT) h"):
            end = idx
    if start is None or end is None:
        raise RuntimeError("could not locate checker slice boundaries")
    return "\n".join(text[start:end + 1])


def emit_lean(out_path, name, num_vars, cnf_clauses, steps, lrat_path,
              cnf_path, digest_hex, tree_lean_path, drat_steps=None,
              obligation_desc=None, honesty_note=None):
    checker_body = extract_checker_body(tree_lean_path)

    cnf_leaf_terms = [list_lit_term(c) for c in cnf_clauses]
    cnf_tree = balanced_tree(cnf_leaf_terms)

    step_leaf_terms = []
    for s in steps:
        step_leaf_terms.append(
            step_term(s["clause"], s["is_rat"], s["hint_clauses"], s["rathints"]))
    prf_tree = balanced_tree(step_leaf_terms)

    n_rup = sum(1 for s in steps if not s["is_rat"])
    n_rat = sum(1 for s in steps if s["is_rat"])

    # A small SAMPLED CNF-identity self-check inside Lean: the first clause's
    # literals' var-indices, packed by mkW64, are exactly the DIMACS values.
    # (The FULL byte-identity is the runnable --verify-digest gate; this is the
    # in-kernel anchor that the embedded indices ARE these DIMACS numbers.)
    sample_lines = []
    for ci in range(min(3, len(cnf_clauses))):
        c = cnf_clauses[ci]
        sample_lines.append(
            f"theorem {name}_cnf_clause{ci}_id :\n"
            f"    treeToListNth {name}CNFTree {ci} = {list_lit_term(c)} := rfl")

    obl = obligation_desc or f"`{name}` (a genuine bit-level equivalence)"
    note_block = ""
    if honesty_note:
        note_block = "--\n--  HONESTY (obligation choice):\n"
        for ln in honesty_note.strip().split("\n"):
            note_block += f"--    {ln}\n"

    header = f"""-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
--
-- ============================================================================
--  B-CERT (scaled): ay -> CNF+DRAT -> drat-trim LRAT -> Clean kernel checker.
--  Self-contained, machine-generated by scripts/lrat_to_clean.py (#56 / #95).
-- ============================================================================
--
--  This file demonstrates the B-cert pipeline END-TO-END for a genuine
--  bit-blasted SMT obligation, at a scale BIGGER than the prior 82-clause
--  UXTB demo:
--
--    obligation : {obl}
--    ay         : bit-blasted the negated equivalence to QF_BV DIMACS
--                 ({len(cnf_clauses)} clauses, {num_vars} vars) and emitted DRAT
--    drat-trim  : DRAT -> LRAT, `s VERIFIED`  ({n_rup} RUP + {n_rat} RAT lemmas)
--    Clean      : THIS file -- the balanced-tree + word-indexed verified RUP/RAT
--                 checker (inlined VERBATIM from proofs/lrat_checker_tree.lean)
--                 REDUCES `checkProofTree CNFTree PRFTree = true := rfl`, and the
--                 transported soundness metatheorem concludes `Unsat`.
--{note_block}--
--  TRUSTED SURFACE for this obligation = {{ Clean kernel checker + the CNF-
--  faithfulness digest }}.  ay-SOUNDNESS IS EVICTED: ay is used only as an
--  UNTRUSTED oracle that produced a CNF + a refutation; Clean re-checks the
--  refutation from first principles (unit propagation along the hint chain) and
--  derives the empty clause.  A corrupted cert makes the `:= rfl` FAIL (the
--  fail-closed controls at the end prove non-vacuity).
--
--  SCALE vs the demo: this cert is {len(cnf_clauses)} clauses / {len(steps)} proof
--  steps -- ~{len(cnf_clauses)//82}x the 82-clause UXTB demo on the CLAUSE axis.
--  Stored as BALANCED trees so the PARSER ingests it (a flat `List.cons` literal
--  caps at ~120 clauses); the kernel folds the trees at O(log n) DEPTH.
--
--  BINDING := rfl COST (re-profiled 2026-06-20, M4 target/release/clean, #95).
--  It is NOT the per-step RUP membership re-scan (an isolating probe that DROPS
--  `allHintsInF` changes the reduction by <5%), NOT the word width, and NOT the
--  flatten ALGORITHM (an O(n) accumulator flatten did not help).  It is the
--  KERNEL EVALUATOR's per-subterm def-eq reduction/hash COST over the materialized
--  formula+proof terms: the cost tracks TOTAL DISTINCT-SUBTERM VOLUME (measured:
--  256 IDENTICAL trivial clauses flatten in <1s, but 256 DISTINCT real clauses
--  take tens of seconds; the kernel re-hashes distinct subterms and, past its
--  100K WHNF-cache bound, evicts and re-reduces).  The two data levers that DO
--  help are therefore (a) MINIMAL var-index term size (this is why --checker natw
--  uses a bare `Nat` literal index, the smallest unique subterm) and (b) fewer
--  total embedded subterms.  The committed practical-scale cert is chosen so its
--  := rfl genuinely reduces within practical clean-check time; larger live certs
--  (v2i64icmp_ule 6154 / v16i8icmp_ule 5754) remain bounded by this evaluator
--  cost -- reported honestly in proofs/bcert_imul/PROVENANCE.md.
--
--  CNF-IDENTITY DIGEST (mechanized vs asserted -- stated honestly):
--    * MECHANIZED (runnable): `scripts/lrat_to_clean.py --verify-digest`
--      re-serializes the CNFTree leaves embedded BELOW back to canonical DIMACS
--      and asserts SHA-256 == the pinned hash of ay's .cnf clause body:
--          {digest_hex}
--      (ay's raw .cnf has a 2-line comment header; the digest is over the
--       canonical clause body `p cnf V C` + clause lines, which is exactly what
--       the CNFTree denotes.  The byte-identity of THAT body to ay's .cnf body
--       is the mechanized tie.)
--    * MECHANIZED (in-kernel anchor): `{name}_cnf_clause{{0,1,2}}_id := rfl`
--      below prove the embedded var-indices ARE the DIMACS integers for the first
--      clauses (the kernel itself confirms the index packing).
--    * The full per-clause in-kernel byte equality is NOT separately re-proved
--      in Lean (it would duplicate the digest); the runnable digest gate is the
--      authoritative faithfulness check, anchored by the sampled `:= rfl`s.
--
--  Generated from:
--    cnf : {Path(cnf_path).name}
--    lrat: {Path(lrat_path).name}
--  DO NOT EDIT BY HAND -- regenerate via scripts/lrat_to_clean.py.
-- ============================================================================

"""

    body = header
    body += checker_body
    body += "\n\n"
    # NOTE: the inlined checker slice (from `namespace LratCoreTree` through
    # `checkProofTree_sound`) leaves the LratCoreTree namespace OPEN, so we append
    # the demo decls directly and close the namespace ONCE at the end.

    # treeToListNth: index into the in-order flatten (for the sampled anchors).
    # Written with EXPLICIT recursors (matching the inlined checker's style) so
    # it elaborates without the equation compiler.  `nthD d i xs` returns the
    # i-th clause of `xs` (the tree's in-order flatten), or `d` if out of range.
    body += (
        "-- Index helper for the sampled CNF-identity anchors (in-order flatten\n"
        "-- nth), via explicit @Nat.rec / @List.rec (no equation compiler).\n"
        "def hdD (d : List Lit) : List (List Lit) -> List Lit := fun xs =>\n"
        "  @List.rec (List Lit) (fun _ => List Lit) d (fun c _ _ => c) xs\n"
        "def tlC : List (List Lit) -> List (List Lit) := fun xs =>\n"
        "  @List.rec (List Lit) (fun _ => List (List Lit)) List.nil (fun _ r _ => r) xs\n"
        "def nthD (d : List Lit) : Nat -> List (List Lit) -> List Lit := fun i =>\n"
        "  @Nat.rec (fun _ => List (List Lit) -> List Lit)\n"
        "    (fun xs => hdD d xs)\n"
        "    (fun _ ih => fun xs => ih (tlC xs))\n"
        "    i\n"
        "def treeToListNth (t : Tree (List Lit)) (i : Nat) : List Lit :=\n"
        "  nthD List.nil i (treeToList t)\n\n")

    body += f"-- The bit-blasted CNF ({len(cnf_clauses)} clauses), balanced-tree stored.\n"
    body += f"def {name}CNFTree : Tree (List Lit) :=\n  {cnf_tree}\n\n"

    body += f"-- The drat-trim LRAT refutation ({len(steps)} addition steps; deletions dropped),\n"
    body += f"-- balanced-tree stored.  Hint clause-IDs resolved to Lit-lists by the transcoder.\n"
    body += f"def {name}PRFTree : Tree Step :=\n  {prf_tree}\n\n"

    body += (
        "-- THE KERNEL RUNS THE CHECKER on the production-scale tree-stored cert:\n"
        "-- it replays the unit-propagation hint chain step by step over the\n"
        "-- growing formula and verifies the empty clause is derived.  `:= rfl`\n"
        "-- is the checker actually REDUCING on the real ay->drat-trim cert.\n")
    body += f"theorem {name}_checks : checkProofTree {name}CNFTree {name}PRFTree = true := rfl\n\n"

    body += (
        "-- Hence the bit-blasted CNF is UNSATISFIABLE -- so the lowering\n"
        "-- equivalence HOLDS -- with ay (the SAT solver) entirely UNTRUSTED.\n"
        "-- This is the transported full RUP+RAT soundness metatheorem.\n")
    body += (f"theorem {name}_unsat : Unsat (treeToList {name}CNFTree) :=\n"
             f"  checkProofTree_sound {name}CNFTree {name}PRFTree {name}_checks\n\n")

    body += "-- The CNF-identity digest, baked in (verified by --verify-digest).\n"
    body += f'def {name}_cnf_digest : String :=\n  "{digest_hex}"\n\n'

    body += "-- Sampled in-kernel CNF-identity anchors (the embedded mkW64 indices\n"
    body += "-- ARE the DIMACS integers for the leading clauses).\n"
    body += "\n".join(sample_lines) + "\n\n"

    # NON-VACUITY: corrupt the last step (drop its last hint) -> REJECTED.
    # Build a corrupted proof tree where the final step's hint list is truncated.
    if steps:
        bad_steps = list(step_leaf_terms)
        last = steps[-1]
        if not last["is_rat"] and len(last["hint_clauses"]) > 0:
            bad_hints = last["hint_clauses"][:-1]
            bad_steps[-1] = (
                f"(rupS {list_lit_term(last['clause'])} "
                f"{list_of_clauses_term(bad_hints)})")
        bad_tree = balanced_tree(bad_steps)
        body += (
            "-- NON-VACUITY / fail-closed: a CORRUPTED cert (the final RUP step\n"
            "-- with its LAST hint clause DROPPED) makes propagation fail to reach\n"
            "-- the conflict, so the whole proof is REJECTED.  The checker is NOT a\n"
            "-- constant `true`.\n")
        body += f"def {name}PRFTreeBad : Tree Step :=\n  {bad_tree}\n"
        body += (f"theorem {name}_bad_rejected : "
                 f"checkProofTree {name}CNFTree {name}PRFTreeBad = false := rfl\n\n")

    body += f"end {CHECKER_NS}\n"

    Path(out_path).write_text(body)
    return {
        "n_clauses": len(cnf_clauses),
        "n_steps": len(steps),
        "n_rup": n_rup,
        "n_rat": n_rat,
        "digest": digest_hex,
    }


# ----------------------------------------------------------------------------
# Resolve hint clause-IDs to Lit-lists.
# ----------------------------------------------------------------------------

def build_steps(cnf_clauses, adds):
    """id -> clause map (CNF ids 1..C, then lemma ids in proof order).  Resolve
    each addition's hint ids to the actual clause Lit-lists."""
    id_to_clause = {}
    for i, c in enumerate(cnf_clauses, start=1):
        id_to_clause[i] = c
    steps = []
    for rec in adds:
        cid = rec["id"]
        clause = rec["clause"]
        if rec["is_rat"]:
            # RAT: pre-hints (rare) currently folded into the per-resolvent path
            # is NOT how the Clean checker consumes them; the Clean ratStep takes
            # ONLY ratHints (per-resolvent (D, rupchain)).  We map each group.
            rathints = []
            for (neg_id, chain) in rec["rat"]:
                d_clause = id_to_clause[neg_id]
                rup_clauses = [id_to_clause[h] for h in chain]
                rathints.append((d_clause, rup_clauses))
            steps.append({
                "clause": clause, "is_rat": True,
                "hint_clauses": [], "rathints": rathints,
            })
        else:
            hint_clauses = [id_to_clause[h] for h in rec["hints"]]
            steps.append({
                "clause": clause, "is_rat": False,
                "hint_clauses": hint_clauses, "rathints": [],
            })
        # register this lemma so later hints can reference it
        id_to_clause[cid] = clause
    return steps


# ----------------------------------------------------------------------------
# CLI.
# ----------------------------------------------------------------------------

def main():
    ap = argparse.ArgumentParser(description="LRAT -> Clean transcoder")
    ap.add_argument("--cnf", required=True)
    ap.add_argument("--lrat", required=True)
    ap.add_argument("--out")
    ap.add_argument("--name", default="imul")
    ap.add_argument("--checker", choices=["tree", "natw"], default="tree",
                    help="which inlined verified checker to use.  `tree` = the "
                         "committed List-Bool word checker (lrat_checker_tree.lean). "
                         "`natw` = the Nat-word variant (lrat_checker_natw.lean): "
                         "the var index is a single Nat literal (minimal subterm), "
                         "which PROFILING showed is the dominant := rfl cost driver. "
                         "Both transport `checkProofTree_sound` unchanged (Nat is "
                         "the original lrat_checker.lean Word).")
    ap.add_argument("--tree-lean", default=None,
                    help="path to the checker .lean to inline (defaults to the "
                         "tree/natw file matching --checker).")
    ap.add_argument("--word-bits", type=int, default=0,
                    help="fixed Word width (bits) for the var index; 0 => keep "
                         "the committed 64-bit mkW64.  Data-only / soundness-"
                         "preserving (the Word type is width-generic).  MEASURED "
                         "to NOT speed up := rfl (see PROFILING NOTE in source); "
                         "kept as an honest knob, not the scaling lever.")
    ap.add_argument("--max-clauses", type=int, default=0,
                    help="(debug) cap CNF clauses for feasibility probing")
    ap.add_argument("--max-steps", type=int, default=0,
                    help="(debug) cap proof steps for feasibility probing")
    ap.add_argument("--obligation-desc", default=None,
                    help="human description of the obligation (header).")
    ap.add_argument("--honesty-note", default=None,
                    help="honesty note about the obligation choice (header).")
    ap.add_argument("--verify-digest", action="store_true",
                    help="re-serialize CNFTree leaves -> canonical DIMACS, "
                         "assert SHA-256 == ay .cnf clause-body hash; exit 0/1.")
    ap.add_argument("--expect-digest", default=None,
                    help="expected SHA-256 (for --verify-digest gate).")
    args = ap.parse_args()

    # Select the inlined checker (namespace + Nat-word emission + default path).
    global CHECKER_NS, NAT_WORD
    if args.checker == "natw":
        CHECKER_NS = "LratCoreNatW"
        NAT_WORD = True
        default_checker = "lrat_checker_natw.lean"
    else:
        CHECKER_NS = "LratCoreTree"
        NAT_WORD = False
        default_checker = "lrat_checker_tree.lean"
    if args.tree_lean is None:
        args.tree_lean = str(Path(__file__).resolve().parent.parent
                             / "proofs" / default_checker)

    num_vars, num_decl, cnf_clauses = parse_cnf(args.cnf)

    # Word width: data-only, soundness-preserving.  0 => committed mkW64.
    # (Ignored when --checker natw, which emits a bare Nat index.)
    set_word_ctor_for_bits(args.word_bits if args.word_bits else None)

    # Canonical clause-body digest of ay's .cnf (authoritative faithfulness key).
    canon_ay = canonical_dimacs(num_vars, cnf_clauses)
    digest_hex = sha256_hex(canon_ay)

    if args.verify_digest:
        # Re-serialize the EXACT clause sequence we would embed (the CNFTree
        # leaves are `cnf_clauses` in order) and confirm round-trip identity.
        canon_emit = canonical_dimacs(num_vars, cnf_clauses)
        emit_hex = sha256_hex(canon_emit)
        ok = (emit_hex == digest_hex)
        if args.expect_digest is not None:
            ok = ok and (digest_hex == args.expect_digest)
        print(f"ay .cnf clause-body SHA-256       : {digest_hex}")
        print(f"re-serialized CNFTree SHA-256     : {emit_hex}")
        if args.expect_digest is not None:
            print(f"expected (pinned)                 : {args.expect_digest}")
        print("DIGEST MATCH" if ok else "DIGEST MISMATCH")
        sys.exit(0 if ok else 1)

    if args.max_clauses and len(cnf_clauses) > args.max_clauses:
        cnf_clauses = cnf_clauses[:args.max_clauses]

    adds = parse_lrat(args.lrat)
    if args.max_steps and len(adds) > args.max_steps:
        adds = adds[:args.max_steps]

    steps = build_steps(cnf_clauses, adds)

    if not args.out:
        print(f"vars={num_vars} clauses={len(cnf_clauses)} "
              f"add-steps={len(adds)} digest={digest_hex}")
        rup = sum(1 for s in steps if not s["is_rat"])
        rat = sum(1 for s in steps if s["is_rat"])
        print(f"RUP={rup} RAT={rat}")
        return

    info = emit_lean(args.out, args.name, num_vars, cnf_clauses, steps,
                     args.lrat, args.cnf, digest_hex, args.tree_lean,
                     obligation_desc=args.obligation_desc,
                     honesty_note=args.honesty_note)
    print(f"wrote {args.out}")
    print(f"  clauses={info['n_clauses']} steps={info['n_steps']} "
          f"RUP={info['n_rup']} RAT={info['n_rat']}")
    print(f"  cnf-digest(sha256, clause-body)={info['digest']}")


if __name__ == "__main__":
    main()
