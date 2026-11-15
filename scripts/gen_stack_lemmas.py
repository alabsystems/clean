#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""Mint `eval_ir_stack_minted.rs` -- TWO lemma families from ONE source-derived skeleton
over `ir_exec`: the `ir_stk_*` FRAME-STACKING family (build-order steps 3-7 of
`eval_ir_stack.rs`'s module doc) and its `ir_mext_*` MODULE-EXTENSION twin (the
lemma plan_risks.txt risk 9 names as the binding one for infer_type).

WHAT IT MINTS, in registration order:

  ir_stk  C. head-only read pins      ir_getd_stack, ir_mach_mem_stack, ir_resolve_stack
          D. writer lemmas            ir_bind_stack .. ir_push_stack (Eq.refl at a cons
                                      head) and ir_ret_to_stack, the ONE writer that
                                      consumes the running premise
          E. branching helpers        one lemma per machine helper that eliminates on
                                      a scrutinee (Bool / IROption / IRScalar / IRTy)
          F. per-constructor lemmas  ir_stk_arm_<ctor>, one per IRInst constructor,
                                      each ONE application of a D/E lemma
          G. the main term            ir_stk_step (S1 of plan_lemma_statement)
  ir_mext E'. module-reading helpers  ir_mext_jump, ir_mext_condbr_b, ir_mext_condbr_exec,
                                      ir_mext_switch_n, ir_mext_switch_exec,
                                      ir_mext_call_exec, ir_mext_callind_exec,
                                      ir_mext_globaladdr
          F'. per-constructor lemmas ir_mext_arm_<ctor>
          G'. the main terms          ir_mext_step, then ir_mext_steps by Nat.rec
                                      exactly as the hand-authored ir_stk_steps (S3)

S2-S5 of the design (ir_stk_running_back, ir_stk_steps, ir_stk_ret_step,
ir_stk_activation) are hand-authored elsewhere and are NOT emitted here.

EVERY TABLE IS READ FROM SOURCE, NEVER HARD-CODED. The IRInst / IRScalar / IRTy /
IRStepResult constructor lists (order, arity, field types, which fields are
recursive) come from the `inductive` declarations in `eval_ir_syntax.rs` and
`eval_ir_state.rs`; the field NAMES and the helper chain of every `ir_exec` arm
come from `ir_exec`'s own `match` in `eval_ir_machine.rs`; the binder lists of
the helper lemmas come from the machine helpers' own `def` signatures with
`(s : IRMachine)` expanded to the frame block and `(m : IRModule)` to the module
block; the abstracted helper bodies the neutral-major motives quote are held
against the machine's own bodies by `--self-test`. So the design note that said
"IRTy has 16 constructors" was wrong by two (the declaration has 18) and the
generator did not have to know: `--self-test` prints the counts it read.

THE PROOF SHAPES, ONCE.
  * S0 := (IRMachine.mk (IRList.cons IRFrame f t) mem na)             -- standalone
    S1 := (IRMachine.mk (IRList.cons IRFrame f (ir_frames_app t rest)) mem na)
    Every ir_stk equation is `Eq IRConfig (H S1 ..) (ir_config_stack (H S0 ..) rest)`.
  * M0 := (IRModule.mk fs0 gs0), M := (IRModule.mk fs gs). Every ir_mext equation
    is `Eq IRConfig (H M0 S0 ..) (H M S0 ..)` under a RUNNING premise on the M0
    side and the EXTENSION premises hf / hg: whatever ir_func_find / ir_global_find
    answers with `some` in M0, it answers identically in M (`forall k g, find fs0 k
    = some g -> find fs k = some g`). A lookup that MISSES in M0 halts the M0 step
    (stuck no_func / type_error no_global), which the running premise refutes; a
    lookup that HITS is transported to M by the premise. So an extension may add
    functions and globals freely, and the lemma says nothing about a step that
    already failed in M0 -- exactly the shape a callee closure registered
    incrementally needs. The premise SET is per arm, read off the exec table:
    Module-independent arms read no module (Eq.refl, no premise); `load` reads ir_mod_encs which is
    the empty table on BOTH `IRModule.mk` sides by iota (Eq.refl, no premise),
    br / condbr / switch / call / callindirect read functions (hf), globaladdr reads
    globals (hg). Modules of the `mkv` form are covered by the TWIN family below.
  * THE mkv TWIN (crystal link 4 M0 W3, appended last): `ir_mextv_*` over
    M0 := (IRModule.mkv fs0 gs0 es0), M := (IRModule.mkv fs gs es), minted by running
    every ir_mext builder under the swapped module spelling. Its `load` arm reads the
    two DERIVED encodings tables, so it takes the ENCODINGS premise -- `henc`: every row
    lookup answers alike in both tables, a hit AND a miss (a miss is not a fault but
    the identity view, so an inclusion premise in the hf / hg shape would be unsound
    here); `hlen`: the tables have one length, which is the view's fuel -- and closes by
    `ir_enc_agree_load_view` (three minted lemmas: the row image, the view at every
    fuel, the load view). `ir_mextv_step` / `ir_mextv_steps` thread henc / hlen to it, and
    `ir_mextv_run` is ir_mext_run's term over the mkv modules. The outcome-keyed twin
    and `ir_mextvo_run` are minted by scripts/gen_stack_axes.py (they need ir_mext_ok).
    --self-test holds every twin to its mk term by undoing the module re-spelling.
  * A writer re-conses the tail verbatim, so both sides whnf to the same
    `running (mk (cons <new head> (ir_frames_app t rest)) mem na)` -- Eq.refl.
  * A helper that eliminates on a VARIABLE scrutinee gets a recursor with a
    goal-abstracting motive over that variable; minor arity is fields-then-IHs.
  * A helper that eliminates on a NEUTRAL scrutinee (`ir_case_find cases n`,
    `ir_func_find (ir_mod_funcs m) fid`, `ir_as_int (ir_frame_get f i)`, and the
    three fetch lookups of the main terms) is spelled per `--form`:
      --form direct  (default) applies the recursor to the neutral term directly
                     -- the motive applied to the major is the goal after delta,
                     the check the tree's `ir_load_view_agg` already passes;
      --form convoy  emits the equation-convoy form
                     `X.rec (fun o => Eq T scrut o -> GOAL) .. scrut (Eq.refl T scrut)`
                     with an Eq.subst along Eq.symm in each minor, the
                     `ir_mem_lookup_update_skip` precedent.
    The FOUR lookups the extension premises close (the function fetch of
    ir_mext_step, ir_mext_jump, ir_mext_call_exec, ir_mext_globaladdr) are ALWAYS
    convoy whatever `--form` says: their `some` minor needs the equation
    `find fs0 k = some g` as a term to feed hf / hg, and the direct form has no
    such term. That is a difference in what is PROVED, not in elaboration.
  * An argument list is resolved from the head frame only, but `ir_resolve` is
    stuck at an abstract list, so the ir_stk jump / call / gep / ret arms rewrite it
    through `ir_resolve_stack` with ONE Eq.subst + Eq.symm (the
    eval_ir_activation.rs idiom). Nothing here uses the foundation's Eq.cong:
    IRList IRScalar is an App type and the congruence goes through ir_eq_cong.
  * The running premise `hrun` is consumed in the ir_stk family in exactly two
    leaves -- the empty frame list in ir_stk_step and the empty caller list in
    ir_ret_to_stack -- via ir_bool_false_ne_true; in every ir_stk arm lemma except ret
    it is bound and unused. In the ir_mext family it is consumed at every module
    lookup that misses (the fetch, jump, call and globaladdr none-minors).

WHAT --check SAYS. That `eval_ir_stack_minted.rs` is BYTE-FOR-BYTE what this
script emits today -- consts, their order, STACK_MINTED_NAMES, DECLS, the tests
and the doc. A hand-added const, a reordered row or an edited term is a refusal.
NOT that the terms are true: the kernel says that, in the EvalIr bundle build, and
each declaration fails BY NAME there (that is why the arms are separate declarations
and not anonymous minors of two terms).

WHAT --self-test SAYS. Structural: the counts read from source agree with each
other (one ir_exec arm per IRInst constructor, arities match), every emitted
term is ASCII with balanced parens and no leftover machine variable `s`, module
variable `m` or `{S}` / `{M}` placeholder, every helper lemma's binders are its
helper's own binders with `s` / `m` expanded, every abstracted helper body a
motive quotes IS the machine's own body, and every `*_stack` / `ir_stk_*` /
`ir_mext_*` name a term references is registered EARLIER in DECLS. Then the
MUTATION test: the freshly rendered file passes the --check logic, and three
hand edits of it -- one character inside a term, a hand-added const, and a
reordered registration row -- are each REFUSED by that same logic, so the
census is demonstrated to fail rather than assumed to. Then the digest pins:
the sha256 of every term against PINNED_DIGESTS, so a refactor of this
generator that moves a shape fails here in a second rather than in a 40-second
bundle build.

PROVENANCE OF THE PINS. Re-pinned 2026-09-25, at the merge of origin/main into
the crystal lane, AFTER the merged spec accepted every one of the 153 terms (63
ir_stk_* + 42 ir_mext_* + 48 node-keyed): in ONE spec_suite process,
`tests/eval_ir_stack_census.rs` passed all six of its tests (the EvalIr bundle
censuses of both minted families, the split, the axes, and the Full-spec axes
witnesses), beside the ctr / its / acceptance_cdp_in censuses, axiom_ratchet,
vacuity_firewall, proof_status_invariants, premise_witness_gate and
spec_axiom_closure_honesty: 34 passed, 0 failed, 1762.45 s. Every checked root has
an EMPTY axiom closure. Retained log:
target-quality/crystal-m0-merge/spec-suite.log. Against origin/main's pins the merge
moved NONE and added the lane's 48; against the lane's it added the three
atomic_fetch_add_relaxed_usize_seq arms and moved the six terms that enumerate
IRInst (ir_stk_step, ir_mext_step, ir_stkn_step, ir_inst_is_ret,
ir_stk_botret_false_of_running) or read the fat-kind IRTy cases
(ir_overflow_exec_stack). The previous checkpoints (105 terms 2026-09-25 on main,
150 on the lane, 101 on 2026-09-20) predate those constructors.
The digests are therefore of KERNEL-CHECKED terms; a `--self-test` red now means
a shape moved away from what the kernel accepted, and the remedy is a bundle
build, never a re-pin.

WIRING (three edits, none of them in the minted file, none of them made here):
  crates/clean-verify/src/spec/core_spec/mod.rs
      mod eval_ir_stack_minted;
      pub use eval_ir_stack_minted::STACK_MINTED_NAMES;
  crates/clean-verify/src/spec/core_spec/bundles.rs
      Specification::add_eval_ir_stack_minted   -- immediately AFTER
      add_eval_ir_stack in BOTH the Full STAGES list and EVAL_IR_STAGE_APPLY.

USAGE
    python3 scripts/gen_stack_lemmas.py --emit        # (re)write the Rust file
    python3 scripts/gen_stack_lemmas.py --check       # byte-compare with the tree
    python3 scripts/gen_stack_lemmas.py --self-test   # structure + mutation + digest pins
    python3 scripts/gen_stack_lemmas.py --print ir_mext_arm_call
    python3 scripts/gen_stack_lemmas.py --list        # names, in DECLS order
    python3 scripts/gen_stack_lemmas.py --tables      # what was read from source
    python3 scripts/gen_stack_lemmas.py --form convoy --emit
    python3 scripts/gen_stack_lemmas.py --digests | --pin
"""

from __future__ import annotations

import argparse
import contextlib
import hashlib
import re
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
CORE = REPO / "crates/clean-verify/src/spec/core_spec"
SYNTAX_RS = CORE / "eval_ir_syntax.rs"
STATE_RS = CORE / "eval_ir_state.rs"
MACHINE_RS = CORE / "eval_ir_machine.rs"
STACK_RS = CORE / "eval_ir_stack.rs"
MINTED_RS = CORE / "eval_ir_stack_minted.rs"

# How a recursor on a NEUTRAL scrutinee is spelled: "direct" applies the
# recursor to the neutral term with a goal-abstracting motive; "convoy" is the
# equation-convoy fallback (see the module doc). Overridable with --form so a
# build failure on the direct form is a one-flag re-emit. The four lookups the
# extension premises close are convoy in EITHER form (see ext_lookup).
FORM = "direct"

# --------------------------------------------------------------------------
# Reading the source
# --------------------------------------------------------------------------


def _lit(src: str, i: int) -> tuple[str, int]:
    """Parse one Rust string literal starting at src[i]; return (text, end)."""
    if src.startswith('r#"', i):
        raise SystemExit("gen_stack_lemmas: r#\" literals are not handled")
    if src.startswith('r"', i):
        j = src.index('"', i + 2)
        return src[i + 2 : j], j + 1
    if src[i] != '"':
        raise ValueError(f"not a string literal at {i}: {src[i:i + 30]!r}")
    out: list[str] = []
    j = i + 1
    while True:
        c = src[j]
        if c == "\\":
            nxt = src[j + 1]
            if nxt == "n":
                out.append("\n")
                j += 2
            elif nxt == "\n":
                j += 2
                while src[j] in " \t":
                    j += 1
            else:
                out.append(nxt)
                j += 2
        elif c == '"':
            return "".join(out), j + 1
        else:
            out.append(c)
            j += 1


def first_arg_sources(path: Path) -> list[str]:
    """The FIRST argument of every add_recursive_def / add_inductive call whose
    first argument is a string literal or a concat! of them."""
    src = path.read_text()
    out: list[str] = []
    for m in re.finditer(r"\.add_(?:recursive_def|inductive)\(\s*", src):
        i = m.end()
        if src.startswith("concat!(", i):
            i += len("concat!(")
            parts: list[str] = []
            while True:
                while src[i] in " \t\n,":
                    i += 1
                if src[i] == ")":
                    break
                s, i = _lit(src, i)
                parts.append(s)
            out.append("".join(parts))
        elif src.startswith('"', i) or src.startswith('r"', i):
            s, _ = _lit(src, i)
            out.append(s)
    return out


ARROW = re.compile(r"\s*(?:→|->)\s*")


def inductives() -> dict[str, list[tuple[str, list[str]]]]:
    """family -> [(ctor, [field types])], in declaration order."""
    fams: dict[str, list[tuple[str, list[str]]]] = {}
    for path in (SYNTAX_RS, STATE_RS):
        for s in first_arg_sources(path):
            if not s.startswith("inductive "):
                continue
            head, *lines = s.split("\n")
            m = re.match(r"inductive (\w+)(?: \((\w+) : Type\))? : Type$", head)
            if not m:
                # A dependent family (MemExt-style) or a probe: not one of ours.
                continue
            fam = m.group(1)
            ctors: list[tuple[str, list[str]]] = []
            for ln in lines:
                cm = re.match(r"\| (\w+) : (.*)$", ln.strip())
                if not cm:
                    raise SystemExit(f"gen_stack_lemmas: unparsed constructor line {ln!r} in {fam}")
                parts = [p for p in ARROW.split(cm.group(2)) if p]
                ctors.append((cm.group(1), parts[:-1]))
            fams[fam] = ctors
    return fams


INDUCTIVES = inductives()


def ctors(fam: str) -> list[tuple[str, list[str]]]:
    if fam not in INDUCTIVES:
        raise SystemExit(f"gen_stack_lemmas: inductive {fam} not found in the source")
    return INDUCTIVES[fam]


def _binders(s: str, i: int) -> tuple[list[tuple[str, str]], int]:
    out: list[tuple[str, str]] = []
    while True:
        while s[i] == " ":
            i += 1
        if s[i] != "(":
            return out, i
        depth, j = 0, i
        while True:
            if s[j] == "(":
                depth += 1
            elif s[j] == ")":
                depth -= 1
                if depth == 0:
                    break
            j += 1
        name, _, ty = s[i + 1 : j].partition(" : ")
        out.append((name, ty))
        i = j + 1


class Def:
    def __init__(self, name: str, binders: list[tuple[str, str]], ty: str, body: str):
        self.name, self.binders, self.ty, self.body = name, binders, ty, body

    @property
    def names(self) -> list[str]:
        return [n for n, _ in self.binders]


def machine_defs() -> dict[str, Def]:
    out: dict[str, Def] = {}
    for s in first_arg_sources(MACHINE_RS):
        if not s.startswith("def "):
            continue
        m = re.match(r"def (\w+)", s)
        name = m.group(1)
        binders, i = _binders(s, m.end())
        assert s[i:].startswith(": "), (name, s[i : i + 20])
        rest = s[i + 2 :]
        ty, _, body = rest.partition(" := ")
        out[name] = Def(name, binders, ty.strip(), body.strip())
    return out


MACHINE = machine_defs()


def machine(name: str) -> Def:
    if name not in MACHINE:
        raise SystemExit(f"gen_stack_lemmas: machine helper {name} not found in {MACHINE_RS.name}")
    return MACHINE[name]


def match_arms(defname: str, fam: str) -> list[tuple[str, list[str], str]]:
    """[(ctor, [field names], rhs)] of a `match` definition, in source order."""
    body = machine(defname).body
    arms: list[tuple[str, list[str], str]] = []
    for ln in body.split("\n")[1:]:
        m = re.match(rf"\| {fam}\.(\w+)((?: \w+)*) => (.*)$", ln.strip())
        if m:
            arms.append((m.group(1), m.group(2).split(), m.group(3).strip()))
    if [c for c, _, _ in arms] != [c for c, _ in ctors(fam)]:
        raise SystemExit(f"gen_stack_lemmas: {defname}'s arms do not enumerate {fam} in declaration order")
    for (c, names, _), (_, types) in zip(arms, ctors(fam)):
        assert len(names) == len(types), (defname, c, names, types)
    return arms


# Field names per constructor, read off a match in the machine whose arms bind
# every field: ir_exec for IRInst, ir_store_exec for IRScalar, ir_ty_shape for IRTy.
EXEC_ARMS = match_arms("ir_exec", "IRInst")
SCALAR_NAMES = {c: n for c, n, _ in match_arms("ir_store_exec", "IRScalar")}
TY_NAMES = {c: n for c, n, _ in match_arms("ir_ty_shape", "IRTy")}

# --------------------------------------------------------------------------
# Vocabulary
# --------------------------------------------------------------------------

BLOCK = "(f : IRFrame) (t : IRList IRFrame) (rest : IRList IRFrame) (mem : IRList IRMemSlot) (na : Nat)"
BARGS = "f t rest mem na"
APP = "(ir_frames_app t rest)"
S0 = "(IRMachine.mk (IRList.cons IRFrame f t) mem na)"
S1 = f"(IRMachine.mk (IRList.cons IRFrame f {APP}) mem na)"
VS = "(IRList IRScalar)"

# The module-extension block: two `IRModule.mk` modules and the two extension
# premises. `kf`/`gf`/`kg`/`gg` are the premises' OWN bound names and collide
# with nothing a lemma binds (the found item at a use site is `gf` / `gg` too,
# bound by the recursor minor, and `fn` where the main term needs it by name).
MBLOCK = "(fs0 : IRList IRFunc) (gs0 : IRList IRGlobal) (fs : IRList IRFunc) (gs : IRList IRGlobal)"
MARGS = "fs0 gs0 fs gs"
M0 = "(IRModule.mk fs0 gs0)"
M1 = "(IRModule.mk fs gs)"
FBLOCK = "(f : IRFrame) (t : IRList IRFrame) (mem : IRList IRMemSlot) (na : Nat)"
FARGS = "f t mem na"
HF_TY = ("forall (kf : Nat) (gf : IRFunc), Eq (IROption IRFunc) (ir_func_find fs0 kf) (IROption.some IRFunc gf) -> "
         "Eq (IROption IRFunc) (ir_func_find fs kf) (IROption.some IRFunc gf)")
HG_TY = ("forall (kg : Nat) (gg : IRGlobal), Eq (IROption IRGlobal) (ir_global_find gs0 kg) (IROption.some IRGlobal gg) -> "
         "Eq (IROption IRGlobal) (ir_global_find gs kg) (IROption.some IRGlobal gg)")
PREMISE = {"hf": f"(hf : {HF_TY})", "hg": f"(hg : {HG_TY})"}

# The ENCODINGS premise of the mkv module axis (crystal link 4 M0 W3): the two
# tables answer every row lookup identically (a hit AND a miss) and have the same
# length, which is the view's fuel. Only the `load` arm reads it.
HE_TY = "forall (te : IRTy), Eq (IROption IREnc) (ir_enc_find es0 te) (ir_enc_find es te)"
HL_TY = "Eq Nat (ir_enc_len es0) (ir_enc_len es)"
PREMISE["he"] = f"(henc : {HE_TY})"
PREMISE["hl"] = f"(hlen : {HL_TY})"
# Set only inside `_module_variant(True)`: the builders below read it to thread
# the encodings premise into the load arm and the two main terms.
_MKV = False

# Names a lemma's own binders may never collide with. A helper parameter or a
# constructor field that is one of these is renamed (RENAMES) before use.
RESERVED = {"m", "f", "t", "rest", "mem", "na", "rs", "hrun", "vs", "s",
            "fs0", "gs0", "fs", "gs", "hf", "hg", "es0", "es", "henc", "hlen"}
RENAMES = {"t": "ty", "f": "g"}


def rn(name: str) -> str:
    return RENAMES.get(name, name)


def at(tpl: str, S: str) -> str:
    return tpl.replace("{S}", S)


def atm(tpl: str, M: str) -> str:
    return tpl.replace("{M}", M)


def stk_goal(tpl: str) -> str:
    """`Eq IRConfig (H S1 ..) (ir_config_stack (H S0 ..) rest)` for a template over {S}."""
    return f"Eq IRConfig {at(tpl, S1)} (ir_config_stack {at(tpl, S0)} rest)"


def mext_goal(tpl: str) -> str:
    """`Eq IRConfig (H M0 ..) (H M ..)` for a template over {M} (the machine is S0)."""
    return f"Eq IRConfig {atm(tpl, M0)} {atm(tpl, M1)}"


def mext_prem(tpl: str) -> str:
    """The running premise on the M0 side."""
    return f"Eq Bool (ir_stk_running {atm(tpl, M0)}) Bool.true"


def mext_stmt(tpl: str) -> str:
    """Premise-passing statement: the shape every ir_mext motive has."""
    return f"{mext_prem(tpl)} -> {mext_goal(tpl)}"


def running(frames: str, mem: str = "mem", na: str = "na") -> str:
    return f"(IRConfig.running (IRMachine.mk {frames} {mem} {na}))"


def cons(x: str, xs: str) -> str:
    return f"(IRList.cons IRFrame {x} {xs})"


def halted(o: str) -> str:
    return f"(IRConfig.halted {o})"


def stuck(fault: str) -> str:
    return halted(f"(IROutcome.stuck IRFault.{fault})")


def tyerr(fault: str) -> str:
    return halted(f"(IROutcome.type_error IRFault.{fault})")


def ub(fault: str) -> str:
    return halted(f"(IROutcome.ub IRFault.{fault})")


def refl(ty: str, x: str) -> str:
    return f"Eq.refl {ty} {x}"


def defn(name: str, binders: str, ty: str, body: str) -> str:
    if not binders:
        return f"def {name} : {ty} := {body}"
    return f"def {name} {binders} : {ty} := {body}"


def top_tokens(s: str) -> list[str]:
    """Split on spaces at paren depth 0."""
    toks, depth, cur = [], 0, []
    for ch in s:
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
        if ch == " " and depth == 0:
            if cur:
                toks.append("".join(cur))
                cur = []
        else:
            cur.append(ch)
    if cur:
        toks.append("".join(cur))
    return toks


def ctor_app(fam: str, ctor: str, fields: list[str]) -> str:
    return f"({fam}.{ctor} {' '.join(fields)})" if fields else f"{fam}.{ctor}"


def uses(name: str, term: str) -> bool:
    return re.search(rf"\b{name}\b", term) is not None


# --------------------------------------------------------------------------
# Recursor emitters
# --------------------------------------------------------------------------


def bool_rec(var: str, motive, false_case: str, true_case: str, major: str) -> str:
    return f"Bool.rec (fun ({var} : Bool) => {motive(var)}) ({false_case}) ({true_case}) {major}"


def opt_rec(param: str, var: str, motive, none_case: str, some_binder: tuple[str, str],
            some_case: str, major: str) -> str:
    sb, sty = some_binder
    return (f"IROption.rec {param} (fun ({var} : IROption {param}) => {motive(var)}) "
            f"({none_case}) (fun ({sb} : {sty}) => {some_case}) {major}")


def neutral_opt_rec(param: str, var: str, motive, none_case: str, some_binder: tuple[str, str],
                    some_case: str, scrut: str, goal: str) -> str:
    """IROption.rec on a NEUTRAL scrutinee, spelled per FORM. `goal` is the
    statement at the scrutinee (the motive applied to it); the direct form never
    mentions it, the convoy form makes it the motive's conclusion."""
    if FORM == "direct":
        return opt_rec(param, var, motive, none_case, some_binder, some_case, scrut)
    if FORM != "convoy":
        raise SystemExit(f"gen_stack_lemmas: unknown --form {FORM!r}")
    T = f"(IROption {param})"
    sb, sty = some_binder
    none = f"(IROption.none {param})"
    some = f"(IROption.some {param} {sb})"

    def transport(known: str, term: str) -> str:
        return (f"Eq.subst {T} (fun ({var}1 : IROption {param}) => {motive(var + '1')}) {known} {scrut} "
                f"(Eq.symm {T} {scrut} {known} h{var}) ({term})")

    return (f"IROption.rec {param} (fun ({var} : IROption {param}) => Eq {T} {scrut} {var} -> {goal}) "
            f"(fun (h{var} : Eq {T} {scrut} {none}) => {transport(none, none_case)}) "
            f"(fun ({sb} : {sty}) (h{var} : Eq {T} {scrut} {some}) => {transport(some, some_case)}) "
            f"{scrut} (Eq.refl {T} {scrut})")


def fam_rec(fam: str, var: str, motive, arms: dict, default, major: str, names: dict[str, list[str]],
            tag: str, hyp=None) -> str:
    """`fam.rec` with one minor per constructor in declaration order. Minor
    binders are the constructor's fields (named from `names`, suffixed with
    `_tag` so nested sites and lemma binders never collide) followed by one IH
    per recursive field. `arms[ctor](fields, ihs)` gives a minor's body;
    `default(fields, ihs)` every other. With `hyp`, the motive is
    premise-passing and every minor takes one more binder, the premise at the
    applied constructor (`hyp(ctor_app)`), named `h` where the body uses it."""
    minors = []
    for ctor, ftypes in ctors(fam):
        fnames = [f"{n}_{tag}" for n in names[ctor]]
        assert len(fnames) == len(ftypes), (fam, ctor, fnames, ftypes)
        ihs = [(f"ih_{n}", n) for n, ty in zip(fnames, ftypes) if ty == fam]
        binders = [f"({n} : {ty})" for n, ty in zip(fnames, ftypes)]
        binders += [f"({ih} : {motive(n)})" for ih, n in ihs]
        body = arms.get(ctor, default)(fnames, [ih for ih, _ in ihs])
        if hyp is not None:
            binders.append(f"({'h' if uses('h', body) else '_'} : {hyp(ctor_app(fam, ctor, fnames))})")
        minors.append(f"(fun {' '.join(binders)} => {body})" if binders else f"({body})")
    return f"{fam}.rec (fun ({var} : {fam}) => {motive(var)}) {' '.join(minors)} {major}"


def ext_lookup(T: str, find: str, l0: str, l1: str, hyp: str, key: str, body0, body1,
               found: str, some_term: str) -> str:
    """The convoy on a module lookup that an EXTENSION premise closes.

    `body0(o)` / `body1(o)` are the M0 / M sides with the looked-up option
    abstracted; the term produced has type
        PREM(body0 (find l0 key)) -> Eq IRConfig (body0 (find l0 key)) (body1 (find l1 key)).
    The none minor refutes from the premise (the M0 side halted). The some
    minor binds the found item as `found` and the equation as `he`, feeds them
    to `hyp` for the M-side equation, and transports `some_term` -- a proof of
    `Eq IRConfig (body0 (some found)) (body1 (some found))`, which may use the
    running premise `h` at `some` -- along its symmetric. ALWAYS the convoy
    form: the direct form has no `he` to hand to the premise."""
    OT = f"(IROption {T})"
    scrut, other = f"({find} {l0} {key})", f"({find} {l1} {key})"
    none = f"(IROption.none {T})"
    some = f"(IROption.some {T} {found})"
    prem = lambda o: f"Eq Bool (ir_stk_running {body0(o)}) Bool.true"
    goal = lambda o: f"Eq IRConfig {body0(o)} {body1(other)}"
    none_minor = (f"(fun (_ : Eq {OT} {scrut} {none}) (h : {prem(none)}) => "
                  f"ir_bool_false_ne_true ({goal(none)}) h)")
    hname = "h" if uses("h", some_term) else "_"
    some_minor = (f"(fun ({found} : {T}) (he : Eq {OT} {scrut} {some}) ({hname} : {prem(some)}) => "
                  f"Eq.subst {OT} (fun (o2 : IROption {T}) => Eq IRConfig {body0(some)} {body1('o2')}) {some} {other} "
                  f"(Eq.symm {OT} {other} {some} ({hyp} {key} {found} he)) ({some_term}))")
    return (f"IROption.rec {T} (fun (o : IROption {T}) => Eq {OT} {scrut} o -> {prem('o')} -> {goal('o')}) "
            f"{none_minor} {some_minor} {scrut} (Eq.refl {OT} {scrut})")


# --------------------------------------------------------------------------
# Signatures derived from the machine helpers
# --------------------------------------------------------------------------


def sig(helper: str, m_first: bool = False) -> tuple[str, list[str], str]:
    """(binders, args, template) of `<helper>_stack`: the helper's own binders
    with `(s : IRMachine)` expanded to the stacking block, and the LHS template
    `(<helper> <args with s -> {S}>)`."""
    d = machine(helper)
    binders, args = [], []
    for n, ty in d.binders:
        if n == "s":
            assert ty == "IRMachine", (helper, n, ty)
            binders.append(BLOCK)
            args.append("{S}")
        else:
            nn = rn(n)
            # `m`, `rs` and `vs` are the helper's own pass-through parameters
            # (module, result ids, resolved values) and keep their names; only
            # the block's five, the machine `s` and the premise name are off
            # limits. (`vs` is the Eq.subst binder in resolve_subst, and no
            # lemma that transports through it also takes a `vs` parameter --
            # structural() checks every term for a leftover, and the kernel
            # would refuse a capture.)
            assert nn not in RESERVED - {"m", "rs", "vs"}, (helper, n)
            binders.append(f"({nn} : {ty})")
            args.append(nn)
    assert "{S}" in args, f"{helper} takes no machine"
    if m_first:
        assert binders[0] == "(m : IRModule)", helper
    return " ".join(binders), args, f"({helper} {' '.join(args)})"


def msig(helper: str, prem: str) -> tuple[str, str, str]:
    """(binders, args, template) of `ir_mext_<helper>`: the helper's own binders
    with `(m : IRModule)` expanded to the module block plus the premise `prem`
    and `(s : IRMachine)` to the frame block; the template is `(<helper> {M} S0 ..)`.
    The running premise is appended by the caller, LAST."""
    d = machine(helper)
    assert d.names[:2] == ["m", "s"], (helper, d.names)
    binders, call_args, tpl_args = [], [], []
    for n, ty in d.binders:
        if n == "m":
            binders += [MBLOCK, PREMISE[prem]]
            call_args += [MARGS, prem]
            tpl_args.append("{M}")
        elif n == "s":
            binders.append(FBLOCK)
            call_args.append(FARGS)
            tpl_args.append(S0)
        else:
            nn = rn(n)
            # `rs` (the node's result ids) is the one pass-through name kept.
            assert nn not in RESERVED - {"rs"}, (helper, n)
            binders.append(f"({nn} : {ty})")
            call_args.append(nn)
            tpl_args.append(nn)
    return " ".join(binders), " ".join(call_args), f"({helper} {' '.join(tpl_args)})"


def stackify(rhs: str) -> tuple[str, list[str]]:
    """Rewrite a machine-helper application over `s` into the application of
    its `_stack` lemma over the block: `(ir_getd s x)` becomes the head-only
    read `(ir_frame_get f x)`, `(ir_mach_mem s)` becomes `mem`, `ir_load_eval s`
    becomes `ir_load_at mem`, `(ir_resolve s x)` becomes `(ir_resolve S0 x)` and
    is reported so the caller can transport it. Refuses if any `s` survives."""
    r = re.sub(r"\(ir_getd s (\w+)\)", r"(ir_frame_get f \1)", rhs)
    r = r.replace("(ir_mach_mem s)", "mem").replace("(ir_load_eval s ", "(ir_load_at mem ")
    resolves = re.findall(r"\(ir_resolve s (\w+)\)", r)
    r = re.sub(r"\(ir_resolve s (\w+)\)", lambda m: f"(ir_resolve {S0} {m.group(1)})", r)
    head, *args = top_tokens(r)
    assert head.startswith("ir_") and "s" in args, rhs
    out = f"{head}_stack {' '.join(BARGS if a == 's' else a for a in args)}"
    assert not re.search(r"\bs\b", out), out
    return out, resolves


def resolve_subst(x: str, motive_body, inner: str) -> str:
    """Transport `inner`, stated at `(ir_resolve S0 x)`, to `(ir_resolve S1 x)`.
    `motive_body(vs)` is the statement with the resolved list abstracted."""
    r0, r1 = f"(ir_resolve {S0} {x})", f"(ir_resolve {S1} {x})"
    return (f"Eq.subst {VS} (fun (vs : IRList IRScalar) => {motive_body('vs')}) {r0} {r1} "
            f"(Eq.symm {VS} {r1} {r0} (ir_resolve_stack {BARGS} {x})) ({inner})")


# The abstracted helper bodies the neutral-major motives quote. Each is the
# machine's own body with the module, the machine and the MAJOR abstracted;
# `--self-test` holds them against the source (see body_checks).


def switch_n_body(m: str, S: str, o: str) -> str:
    return (f"(IROption.rec IRSwitchCase (fun (_ : IROption IRSwitchCase) => IRConfig) "
            f"(ir_jump {m} {S} dflt dargs) "
            f"(fun (c : IRSwitchCase) => ir_jump {m} {S} (ir_case_target c) (ir_case_args c)) {o})")


def call_exec_body(S: str, o: str) -> str:
    # The callee binder is renamed g: the source's `f` would capture the frame.
    return (f"(IROption.rec IRFunc (fun (_ : IROption IRFunc) => IRConfig) "
            f"(IRConfig.halted (IROutcome.stuck IRFault.no_func)) "
            f"(fun (g : IRFunc) => ir_push {S} rs g (ir_resolve {S} args)) {o})")


def alloca_exec_body(S: str, o: str) -> str:
    return (f"(IROption.rec Nat (fun (_ : IROption Nat) => IRConfig) "
            f"(IRConfig.halted (IROutcome.type_error IRFault.not_int)) "
            f"(fun (k : Nat) => ir_alloca_k {S} rs k) {o})")


def globaladdr_body(o: str) -> str:
    return (f"(IROption.rec IRGlobal (fun (_ : IROption IRGlobal) => IRStepResult) "
            f"(IRStepResult.fault (IROutcome.type_error IRFault.no_global)) "
            f"(fun (_ : IRGlobal) => IRStepResult.value (IRScalar.ptr_ g)) {o})")


def body_checks() -> list[str]:
    """Each abstracted body, re-instantiated at the source's own names and major,
    must BE the source body after its explicit recursor-head `@`."""
    bad = []
    cases = [
        ("ir_switch_n", switch_n_body("m", "s", "(ir_case_find cases n)")),
        ("ir_call_exec", call_exec_body("s", "(ir_func_find (ir_mod_funcs m) fid)").replace("(g : IRFunc) => ir_push s rs g", "(f : IRFunc) => ir_push s rs f")),
        ("ir_alloca_exec", alloca_exec_body("s", "(ir_alloca_count s c)")),
        ("ir_globaladdr_eval", globaladdr_body("(ir_global_find (ir_mod_globals m) g)")),
    ]
    for helper, quoted in cases:
        if "@" + quoted[1:-1] != machine(helper).body:
            bad.append(f"{helper}: the abstracted body the motives quote is not the machine's own body")
    return bad


# ==========================================================================
# THE ir_stk FAMILY (frame stacking)
# ==========================================================================

# --------------------------------------------------------------------------
# C. head-only read pins
# --------------------------------------------------------------------------


def c_getd() -> str:
    binders, _, tpl = sig("ir_getd")
    return defn("ir_getd_stack", binders, f"Eq IRScalar {at(tpl, S1)} {at(tpl, S0)}",
                refl("IRScalar", "(ir_frame_get f k)"))


def c_mach_mem() -> str:
    binders, _, tpl = sig("ir_mach_mem")
    return defn("ir_mach_mem_stack", binders, f"Eq (IRList IRMemSlot) {at(tpl, S1)} {at(tpl, S0)}",
                refl("(IRList IRMemSlot)", "mem"))


def c_resolve() -> str:
    binders, _, _ = sig("ir_resolve")
    mot = lambda v: f"Eq {VS} (ir_resolve {S1} {v}) (ir_resolve {S0} {v})"
    body = (f"IRList.rec Nat (fun (ids0 : IRList Nat) => {mot('ids0')}) "
            f"({refl(VS, '(IRList.nil IRScalar)')}) "
            f"(fun (i : Nat) (ids2 : IRList Nat) (ih : {mot('ids2')}) => "
            f"ir_eq_cong {VS} {VS} (fun (vs : IRList IRScalar) => IRList.cons IRScalar (ir_frame_get f i) vs) "
            f"(ir_resolve {S1} ids2) (ir_resolve {S0} ids2) ih) ids")
    return defn("ir_resolve_stack", binders, mot("ids"), body)


# --------------------------------------------------------------------------
# D. writer lemmas
# --------------------------------------------------------------------------


def _refl_writer(helper: str, normal_form: str, name: str | None = None) -> str:
    binders, _, tpl = sig(helper)
    return defn(name or f"{helper}_stack", binders, stk_goal(tpl), refl("IRConfig", normal_form))


def d_bind() -> str:
    return _refl_writer("ir_bind", running(cons("(ir_frame_bind f rs v)", APP)))


def d_bind_result() -> str:
    binders, _, _ = sig("ir_bind_result")
    mot = lambda r: stk_goal(f"(ir_bind_result {{S}} rs {r})")
    body = (f"IRStepResult.rec (fun (r0 : IRStepResult) => {mot('r0')}) "
            f"(fun (v : IRScalar) => ir_bind_stack {BARGS} rs v) "
            f"(fun (o : IROutcome) => {refl('IRConfig', halted('o'))}) r")
    assert [c for c, _ in ctors("IRStepResult")] == ["value", "fault"]
    return defn("ir_bind_result_stack", binders, mot("r"), body)


def d_bind2() -> str:
    return _refl_writer("ir_bind2", running(cons("(ir_frame_bind2 f rs v u)", APP)))


def d_advance() -> str:
    return _refl_writer("ir_advance", running(cons("(ir_frame_advance f)", APP)))


def d_advance_set_mem() -> str:
    tpl = "(ir_advance (ir_set_mem {S} m2))"
    return defn("ir_advance_set_mem_stack", f"{BLOCK} (m2 : IRList IRMemSlot)", stk_goal(tpl),
                refl("IRConfig", running(cons("(ir_frame_advance f)", APP), mem="m2")))


def d_alloca_k() -> str:
    return _refl_writer(
        "ir_alloca_k",
        running(cons("(ir_frame_bind f rs (IRScalar.ptr_ na))", APP), mem="(ir_alloc_cells na k mem)",
                na="(Nat.add na k)"),
    )


def d_goto() -> str:
    return _refl_writer(
        "ir_goto", running(cons("(ir_frame_goto f tgt (ir_bind_params ps vs (ir_frame_locals f)))", APP)))


def d_push() -> str:
    callee = ("(IRFrame.mk (ir_func_id g) (ir_func_entry g) Nat.zero "
              "(ir_bind_params (ir_func_params g) vs (IRList.nil IRBinding)) rs)")
    return _refl_writer("ir_push", running(cons(callee, cons("(ir_frame_advance f)", APP))))


def d_ret_to() -> str:
    d = machine("ir_ret_to")
    assert d.names == ["dests", "rest", "mem", "na", "vs"], d.names
    def mot(v: str) -> str:
        return (f"Eq Bool (ir_stk_running (ir_ret_to ds {v} mem na vs)) Bool.true -> "
                f"Eq IRConfig (ir_ret_to ds (ir_frames_app {v} rest) mem na vs) "
                f"(ir_config_stack (ir_ret_to ds {v} mem na vs) rest)")
    nil = "(IRList.nil IRFrame)"
    nil_goal = (f"Eq IRConfig (ir_ret_to ds (ir_frames_app {nil} rest) mem na vs) "
                f"(ir_config_stack (ir_ret_to ds {nil} mem na vs) rest)")
    nil_minor = (f"(fun (h0 : Eq Bool (ir_stk_running (ir_ret_to ds {nil} mem na vs)) Bool.true) => "
                 f"ir_bool_false_ne_true ({nil_goal}) h0)")
    cons_minor = (f"(fun (g : IRFrame) (t2 : IRList IRFrame) (_ih : {mot('t2')}) "
                  f"(h0 : Eq Bool (ir_stk_running (ir_ret_to ds (IRList.cons IRFrame g t2) mem na vs)) Bool.true) => "
                  f"{refl('IRConfig', running(cons('(ir_frame_set_many g ds vs)', '(ir_frames_app t2 rest)')))})")
    body = f"IRList.rec IRFrame (fun (t0 : IRList IRFrame) => {mot('t0')}) {nil_minor} {cons_minor} t h"
    binders = ("(ds : IRList Nat) (rest : IRList IRFrame) (mem : IRList IRMemSlot) (na : Nat) "
               "(vs : IRList IRScalar) (t : IRList IRFrame) "
               "(h : Eq Bool (ir_stk_running (ir_ret_to ds t mem na vs)) Bool.true)")
    ty = (f"Eq IRConfig (ir_ret_to ds (ir_frames_app t rest) mem na vs) "
          f"(ir_config_stack (ir_ret_to ds t mem na vs) rest)")
    return defn("ir_ret_to_stack", binders, ty, body)


# --------------------------------------------------------------------------
# E. branching helpers
# --------------------------------------------------------------------------


def _scalar_default(fault: str):
    return lambda fs, ihs: refl("IRConfig", tyerr(fault))


def e_store_live() -> str:
    binders, _, _ = sig("ir_store_live")
    mot = lambda b: stk_goal(f"(ir_store_live {{S}} a v {b})")
    body = bool_rec("b0", mot, refl("IRConfig", ub("bad_addr")),
                    f"ir_advance_set_mem_stack {BARGS} (ir_mem_update mem a v)", "live")
    return defn("ir_store_live_stack", binders, mot("live"), body)


def e_store_checked() -> str:
    binders, _, _ = sig("ir_store_checked")
    mot = lambda o: stk_goal(f"(ir_store_checked {{S}} a v {o})")
    body = opt_rec("IRMemSlot", "o0", mot, refl("IRConfig", ub("bad_addr")), ("c", "IRMemSlot"),
                   f"ir_store_live_stack {BARGS} a v (ir_slot_live c)", "o")
    return defn("ir_store_checked_stack", binders, mot("o"), body)


def e_store_exec() -> str:
    binders, _, _ = sig("ir_store_exec")
    mot = lambda p: stk_goal(f"(ir_store_exec {{S}} {p} v)")
    through = lambda fs, ihs: f"ir_store_checked_stack {BARGS} {fs[0]} v (ir_mem_lookup mem {fs[0]})"
    arms = {"ptr_": through, "fat_": through,
            "nullptr_": lambda fs, ihs: refl("IRConfig", ub("null_deref"))}
    body = fam_rec("IRScalar", "p0", mot, arms, _scalar_default("not_ptr"), "p", SCALAR_NAMES, "p")
    return defn("ir_store_exec_stack", binders, mot("p"), body)


def e_jump_block() -> str:
    binders, _, _ = sig("ir_jump_block")
    mot = lambda ob: stk_goal(f"(ir_jump_block {{S}} tgt vs {ob})")
    body = opt_rec("IRBlock", "o0", mot, refl("IRConfig", stuck("no_block")), ("b", "IRBlock"),
                   f"ir_goto_stack {BARGS} tgt (ir_block_params b) vs", "ob")
    return defn("ir_jump_block_stack", binders, mot("ob"), body)


def e_jump_func() -> str:
    binders, _, _ = sig("ir_jump_func")
    mot = lambda of: stk_goal(f"(ir_jump_func {{S}} tgt vs {of})")
    body = opt_rec("IRFunc", "o0", mot, refl("IRConfig", stuck("no_func")), ("g", "IRFunc"),
                   f"ir_jump_block_stack {BARGS} tgt vs (ir_block_find (ir_func_blocks g) tgt)", "of")
    return defn("ir_jump_func_stack", binders, mot("of"), body)


def e_jump() -> str:
    binders, _, tpl = sig("ir_jump", m_first=True)
    cur = f"(ir_cur_func m {S0})"
    mot = lambda vs: f"Eq IRConfig (ir_jump_func {S1} tgt {vs} {cur}) (ir_config_stack {at(tpl, S0)} rest)"
    body = resolve_subst("args", mot, f"ir_jump_func_stack {BARGS} tgt (ir_resolve {S0} args) {cur}")
    return defn("ir_jump_stack", binders, stk_goal(tpl), body)


def e_condbr_b() -> str:
    binders, _, _ = sig("ir_condbr_b", m_first=True)
    mot = lambda b: stk_goal(f"(ir_condbr_b m {{S}} tt targs et eargs {b})")
    body = bool_rec("b0", mot, f"ir_jump_stack m {BARGS} et eargs", f"ir_jump_stack m {BARGS} tt targs", "b")
    return defn("ir_condbr_b_stack", binders, mot("b"), body)


def e_condbr_exec() -> str:
    binders, _, _ = sig("ir_condbr_exec", m_first=True)
    mot = lambda c: stk_goal(f"(ir_condbr_exec m {{S}} {c} tt targs et eargs)")
    arms = {"bool_": lambda fs, ihs: f"ir_condbr_b_stack m {BARGS} tt targs et eargs {fs[0]}"}
    body = fam_rec("IRScalar", "c0", mot, arms, _scalar_default("not_bool"), "c", SCALAR_NAMES, "c")
    return defn("ir_condbr_exec_stack", binders, mot("c"), body)


def e_switch_n() -> str:
    binders, _, tpl = sig("ir_switch_n", m_first=True)
    mot = lambda o: f"Eq IRConfig {switch_n_body('m', S1, o)} (ir_config_stack {switch_n_body('m', S0, o)} rest)"
    body = neutral_opt_rec("IRSwitchCase", "o0", mot, f"ir_jump_stack m {BARGS} dflt dargs",
                           ("c", "IRSwitchCase"),
                           f"ir_jump_stack m {BARGS} (ir_case_target c) (ir_case_args c)",
                           "(ir_case_find cases n)", stk_goal(tpl))
    return defn("ir_switch_n_stack", binders, stk_goal(tpl), body)


def e_switch_exec() -> str:
    binders, _, _ = sig("ir_switch_exec", m_first=True)
    mot = lambda v: stk_goal(f"(ir_switch_exec m {{S}} {v} dflt dargs cases)")
    arms = {"int_": lambda fs, ihs: f"ir_switch_n_stack m {BARGS} dflt dargs cases {fs[0]}"}
    body = fam_rec("IRScalar", "v0", mot, arms, _scalar_default("not_int"), "v", SCALAR_NAMES, "v")
    return defn("ir_switch_exec_stack", binders, mot("v"), body)


def e_call_exec() -> str:
    binders, _, tpl = sig("ir_call_exec", m_first=True)
    mot = lambda o: f"Eq IRConfig {call_exec_body(S1, o)} (ir_config_stack {call_exec_body(S0, o)} rest)"
    some_mot = lambda vs: (f"Eq IRConfig (ir_push {S1} rs g {vs}) "
                           f"(ir_config_stack (ir_push {S0} rs g (ir_resolve {S0} args)) rest)")
    some_case = resolve_subst("args", some_mot, f"ir_push_stack {BARGS} rs g (ir_resolve {S0} args)")
    body = neutral_opt_rec("IRFunc", "o0", mot, refl("IRConfig", stuck("no_func")), ("g", "IRFunc"),
                           some_case, "(ir_func_find (ir_mod_funcs m) fid)", stk_goal(tpl))
    return defn("ir_call_exec_stack", binders, stk_goal(tpl), body)


def e_callind_exec() -> str:
    binders, _, _ = sig("ir_callind_exec", m_first=True)
    mot = lambda cv: stk_goal(f"(ir_callind_exec m {{S}} rs {cv} args)")
    arms = {"fnptr_": lambda fs, ihs: f"ir_call_exec_stack m {BARGS} rs {fs[0]} args",
            "nullptr_": lambda fs, ihs: refl("IRConfig", ub("null_deref"))}
    body = fam_rec("IRScalar", "cv0", mot, arms, _scalar_default("not_fnptr"), "cv", SCALAR_NAMES, "cv")
    return defn("ir_callind_exec_stack", binders, mot("cv"), body)


def e_assert_b() -> str:
    binders, _, _ = sig("ir_assert_b")
    mot = lambda b: stk_goal(f"(ir_assert_b {{S}} {b})")
    body = bool_rec("b0", mot, refl("IRConfig", ub("assert_failed")), f"ir_advance_stack {BARGS}", "b")
    return defn("ir_assert_b_stack", binders, mot("b"), body)


def e_assert_exec() -> str:
    binders, _, _ = sig("ir_assert_exec")
    mot = lambda c: stk_goal(f"(ir_assert_exec {{S}} {c})")
    arms = {"bool_": lambda fs, ihs: f"ir_assert_b_stack {BARGS} {fs[0]}"}
    body = fam_rec("IRScalar", "c0", mot, arms, _scalar_default("not_bool"), "c", SCALAR_NAMES, "c")
    return defn("ir_assert_exec_stack", binders, mot("c"), body)


def e_alloca_exec() -> str:
    binders, _, _ = sig("ir_alloca_exec")
    mot = lambda c: stk_goal(f"(ir_alloca_exec {{S}} rs {c})")
    inner_mot = lambda o: f"Eq IRConfig {alloca_exec_body(S1, o)} (ir_config_stack {alloca_exec_body(S0, o)} rest)"
    inner = neutral_opt_rec("Nat", "o1", inner_mot, refl("IRConfig", tyerr("not_int")), ("k", "Nat"),
                            f"ir_alloca_k_stack {BARGS} rs k", "(ir_as_int (ir_frame_get f i))",
                            mot("(IROption.some Nat i)"))
    body = opt_rec("Nat", "c0", mot, f"ir_alloca_k_stack {BARGS} rs (Nat.succ Nat.zero)", ("i", "Nat"),
                   inner, "c")
    return defn("ir_alloca_exec_stack", binders, mot("c"), body)


def e_overflow_ints() -> str:
    binders, _, tpl = sig("ir_overflow_ints")
    proof, resolves = stackify(machine("ir_overflow_ints").body)
    assert not resolves and proof.startswith("ir_bind2_stack ")
    return defn("ir_overflow_ints_stack", binders, stk_goal(tpl), proof)


def e_overflow_vals() -> str:
    binders, _, _ = sig("ir_overflow_vals")
    mot_a = lambda a: stk_goal(f"(ir_overflow_vals {{S}} rs op sgn w {a} b)")
    dflt = _scalar_default("not_int")

    def int_arm(fs, ihs):
        x = fs[0]
        mot_b = lambda b: stk_goal(f"(ir_overflow_vals {{S}} rs op sgn w (IRScalar.int_ {x}) {b})")
        arms_b = {"int_": lambda fs2, ihs2: f"ir_overflow_ints_stack {BARGS} rs op sgn w {x} {fs2[0]}"}
        return fam_rec("IRScalar", "b0", mot_b, arms_b, dflt, "b", SCALAR_NAMES, "b")

    body = fam_rec("IRScalar", "a0", mot_a, {"int_": int_arm}, dflt, "a", SCALAR_NAMES, "a")
    return defn("ir_overflow_vals_stack", binders, mot_a("a"), body)


def e_overflow_exec() -> str:
    binders, _, _ = sig("ir_overflow_exec")
    mot = lambda ty: stk_goal(f"(ir_overflow_exec {{S}} rs op {ty} a b)")
    arms = {"int_": lambda fs, ihs: f"ir_overflow_vals_stack {BARGS} rs op Bool.true {fs[0]} a b",
            "uint_": lambda fs, ihs: f"ir_overflow_vals_stack {BARGS} rs op Bool.false {fs[0]} a b"}
    body = fam_rec("IRTy", "ty0", mot, arms, lambda fs, ihs: refl("IRConfig", tyerr("not_int")), "ty",
                   TY_NAMES, "ty")
    return defn("ir_overflow_exec_stack", binders, mot("ty"), body)


# --------------------------------------------------------------------------
# F. the per-constructor arm lemmas, from ir_exec's own match
# --------------------------------------------------------------------------


def arm_fields() -> list[tuple[str, list[str], list[str], str]]:
    """[(ctor, renamed field names, field types, renamed rhs)] in IRInst order."""
    out = []
    for (ctor, names, rhs), (_, types) in zip(EXEC_ARMS, ctors("IRInst")):
        renamed = [rn(n) for n in names]
        assert not (set(renamed) & RESERVED), (ctor, renamed)
        for old, new in zip(names, renamed):
            if old != new:
                rhs = re.sub(rf"\b{old}\b", new, rhs)
        out.append((ctor, renamed, types, rhs))
    return out


ARMS = arm_fields()


def inst_app(ctor: str, names: list[str]) -> str:
    return f"(IRInst.{ctor} {' '.join(names)})" if names else f"IRInst.{ctor}"


def arm_proof(ctor: str, names: list[str], rhs: str, tpl: str,
              ret_lemma: str = "ir_ret_to_stack", ret_prem: str = "hrun") -> str:
    """The proof of one arm. `ret_lemma` / `ret_prem` name the writer lemma the
    ret arm closes through and the premise it hands it: the running-keyed family
    passes `ir_ret_to_stack ... hrun`, the node-keyed twin `ir_stkn_ret_to ... ht`.
    Every other arm's proof mentions no premise at all."""
    if rhs.startswith("IRConfig.halted "):
        return refl("IRConfig", f"({rhs})")
    if rhs.startswith("ir_return_exec s "):
        (ids,) = rhs.split()[2:]
        mot = lambda vs: (f"Eq IRConfig (ir_ret_to (ir_frame_dests f) (ir_frames_app t rest) mem na {vs}) "
                          f"(ir_config_stack {at(tpl, S0)} rest)")
        return resolve_subst(ids, mot, f"{ret_lemma} (ir_frame_dests f) rest mem na (ir_resolve {S0} {ids}) t {ret_prem}")
    term, resolves = stackify(rhs)
    if not resolves:
        return term
    (x,) = resolves
    assert term.startswith(f"ir_bind_result_stack {BARGS} rs "), (ctor, term)
    evaluator = term[len(f"ir_bind_result_stack {BARGS} rs "):]
    mot = lambda vs: (f"Eq IRConfig (ir_bind_result {S1} rs {evaluator.replace(f'(ir_resolve {S0} {x})', vs)}) "
                      f"(ir_config_stack {at(tpl, S0)} rest)")
    return resolve_subst(x, mot, term)


def arm_lemma(ctor: str, names: list[str], types: list[str], rhs: str) -> str:
    tpl = f"(ir_exec m {inst_app(ctor, names)} rs {{S}})"
    fields = " ".join(f"({n} : {ty})" for n, ty in zip(names, types))
    binders = f"(m : IRModule) {BLOCK} (rs : IRList Nat) {fields + ' ' if fields else ''}(hrun : Eq Bool (ir_stk_running {at(tpl, S0)}) Bool.true)"
    return defn(f"ir_stk_arm_{ctor}", binders, stk_goal(tpl), arm_proof(ctor, names, rhs, tpl))


def arm_builder(ctor: str, names: list[str], types: list[str], rhs: str):
    return lambda: arm_lemma(ctor, names, types, rhs)


# --------------------------------------------------------------------------
# G. the main term
# --------------------------------------------------------------------------


def g_stk_step() -> str:
    mk = lambda fs: f"(IRMachine.mk {fs} mem na)"
    mot_s = lambda s0: (f"Eq Bool (ir_stk_running (ir_step m {s0})) Bool.true -> "
                        f"Eq IRConfig (ir_step m (ir_mach_stack {s0} rest)) (ir_config_stack (ir_step m {s0}) rest)")
    mot_fs = lambda fs0: mot_s(mk(fs0))
    bl, pc = "(ir_frame_block f)", "(ir_frame_pc f)"

    def layer(step):
        return lambda o: (f"Eq Bool (ir_stk_running {step(S0, o)}) Bool.true -> "
                          f"Eq IRConfig {step(S1, o)} (ir_config_stack {step(S0, o)} rest)")

    step_f = lambda S, o: f"(ir_step_f m {S} {bl} {pc} {o})"
    step_b = lambda S, o: f"(ir_step_b m {S} {pc} {o})"
    step_n = lambda S, o: f"(ir_step_n m {S} {o})"
    exec_node = lambda S, n0: f"(ir_exec_node m {n0} {S})"
    exec_i = lambda S, i0: f"(ir_exec m {i0} rs {S})"
    mot_f, mot_b, mot_n = layer(step_f), layer(step_b), layer(step_n)
    mot_nd, mot_i = layer(exec_node), layer(exec_i)

    def none_minor(step, param: str, fault: str) -> str:
        none = f"(IROption.none {param})"
        return (f"fun (_ : Eq Bool (ir_stk_running {step(S0, none)}) Bool.true) => "
                f"{refl('IRConfig', stuck(fault))}")

    inst_minors = []
    for ctor, names, types, _ in ARMS:
        call = f"ir_stk_arm_{ctor} m {BARGS} rs {' '.join(names)}".rstrip()
        if names:
            fields = " ".join(f"({n} : {ty})" for n, ty in zip(names, types))
            inst_minors.append(f"(fun {fields} => {call})")
        else:
            inst_minors.append(f"({call})")
    inst_rec = f"IRInst.rec (fun (i0 : IRInst) => {mot_i('i0')}) {' '.join(inst_minors)} i"
    assert [c for c, _ in ctors("IRNode")] == ["mk"] and ctors("IRNode")[0][1] == ["IRInst", "IRList Nat"]
    node_rec = f"IRNode.rec (fun (n0 : IRNode) => {mot_nd('n0')}) (fun (i : IRInst) (rs : IRList Nat) => {inst_rec}) nd"
    n_scrut = f"(ir_nodes_get (ir_block_nodes bk) {pc})"
    n_rec = neutral_opt_rec("IRNode", "on", mot_n, none_minor(step_n, "IRNode", "fetch_past_end"),
                            ("nd", "IRNode"), node_rec, n_scrut, mot_n(n_scrut))
    b_scrut = f"(ir_block_find (ir_func_blocks fn) {bl})"
    b_rec = neutral_opt_rec("IRBlock", "ob", mot_b, none_minor(step_b, "IRBlock", "no_block"),
                            ("bk", "IRBlock"), n_rec, b_scrut, mot_b(b_scrut))
    f_scrut = "(ir_func_find (ir_mod_funcs m) (ir_frame_func f))"
    f_rec = neutral_opt_rec("IRFunc", "o", mot_f, none_minor(step_f, "IRFunc", "no_func"),
                            ("fn", "IRFunc"), b_rec, f_scrut, mot_f(f_scrut))
    nil = "(IRList.nil IRFrame)"
    nil_minor = (f"(fun (h : Eq Bool (ir_stk_running (ir_step m {mk(nil)})) Bool.true) => "
                 f"ir_bool_false_ne_true (Eq IRConfig (ir_step m (ir_mach_stack {mk(nil)} rest)) "
                 f"(ir_config_stack (ir_step m {mk(nil)}) rest)) h)")
    cons_minor = f"(fun (f : IRFrame) (t : IRList IRFrame) (_ih : {mot_fs('t')}) => {f_rec})"
    list_rec = f"IRList.rec IRFrame (fun (fs0 : IRList IRFrame) => {mot_fs('fs0')}) {nil_minor} {cons_minor} fs"
    assert ctors("IRMachine")[0][1] == ["IRList IRFrame", "IRList IRMemSlot", "Nat"]
    body = (f"IRMachine.rec (fun (s0 : IRMachine) => {mot_s('s0')}) "
            f"(fun (fs : IRList IRFrame) (mem : IRList IRMemSlot) (na : Nat) => {list_rec}) s hrun")
    binders = ("(m : IRModule) (s : IRMachine) (rest : IRList IRFrame) "
               "(hrun : Eq Bool (ir_stk_running (ir_step m s)) Bool.true)")
    return defn("ir_stk_step", binders, "Eq IRConfig (ir_step m (ir_mach_stack s rest)) (ir_config_stack (ir_step m s) rest)", body)


# ==========================================================================
# THE ir_mext FAMILY (module extension) -- the same skeleton, the other axis
# ==========================================================================

# --------------------------------------------------------------------------
# E'. module-reading helpers
# --------------------------------------------------------------------------


def _hrun(tpl: str) -> str:
    return f"(hrun : {mext_prem(tpl)})"


def x_jump() -> str:
    binders, _, tpl = msig("ir_jump", "hf")
    body = lambda o: f"(ir_jump_func {S0} tgt (ir_resolve {S0} args) {o})"
    term = ext_lookup("IRFunc", "ir_func_find", "fs0", "fs", "hf", "(ir_frame_func f)", body, body, "gf",
                      refl("IRConfig", body("(IROption.some IRFunc gf)")))
    return defn("ir_mext_jump", f"{binders} {_hrun(tpl)}", mext_goal(tpl), f"{term} hrun")


def x_condbr_b() -> str:
    binders, _, _ = msig("ir_condbr_b", "hf")
    tpl = lambda b: f"(ir_condbr_b {{M}} {S0} tt targs et eargs {b})"
    mot = lambda b: mext_stmt(tpl(b))
    false_case = f"fun (h : {mext_prem(tpl('Bool.false'))}) => ir_mext_jump {MARGS} hf {FARGS} et eargs h"
    true_case = f"fun (h : {mext_prem(tpl('Bool.true'))}) => ir_mext_jump {MARGS} hf {FARGS} tt targs h"
    body = bool_rec("b0", mot, false_case, true_case, "b")
    return defn("ir_mext_condbr_b", f"{binders} {_hrun(tpl('b'))}", mext_goal(tpl("b")), f"{body} hrun")


def x_condbr_exec() -> str:
    binders, _, _ = msig("ir_condbr_exec", "hf")
    tpl = lambda c: f"(ir_condbr_exec {{M}} {S0} {c} tt targs et eargs)"
    mot = lambda c: mext_stmt(tpl(c))
    hyp = lambda capp: mext_prem(tpl(capp))
    arms = {"bool_": lambda fs, ihs: f"ir_mext_condbr_b {MARGS} hf {FARGS} tt targs et eargs {fs[0]} h"}
    body = fam_rec("IRScalar", "c0", mot, arms, _scalar_default("not_bool"), "c", SCALAR_NAMES, "c", hyp=hyp)
    return defn("ir_mext_condbr_exec", f"{binders} {_hrun(tpl('c'))}", mext_goal(tpl("c")), f"{body} hrun")


def x_switch_n() -> str:
    binders, _, tpl = msig("ir_switch_n", "hf")
    body_o = lambda M, o: switch_n_body(M, S0, o)
    mot = lambda o: (f"Eq Bool (ir_stk_running {body_o(M0, o)}) Bool.true -> "
                     f"Eq IRConfig {body_o(M0, o)} {body_o(M1, o)}")
    none = "(IROption.none IRSwitchCase)"
    some = "(IROption.some IRSwitchCase c)"
    none_case = (f"fun (h : Eq Bool (ir_stk_running {body_o(M0, none)}) Bool.true) => "
                 f"ir_mext_jump {MARGS} hf {FARGS} dflt dargs h")
    some_case = (f"fun (h : Eq Bool (ir_stk_running {body_o(M0, some)}) Bool.true) => "
                 f"ir_mext_jump {MARGS} hf {FARGS} (ir_case_target c) (ir_case_args c) h")
    scrut = "(ir_case_find cases n)"
    body = neutral_opt_rec("IRSwitchCase", "o0", mot, none_case, ("c", "IRSwitchCase"), some_case, scrut, mot(scrut))
    return defn("ir_mext_switch_n", f"{binders} {_hrun(tpl)}", mext_goal(tpl), f"{body} hrun")


def x_switch_exec() -> str:
    binders, _, _ = msig("ir_switch_exec", "hf")
    tpl = lambda v: f"(ir_switch_exec {{M}} {S0} {v} dflt dargs cases)"
    mot = lambda v: mext_stmt(tpl(v))
    hyp = lambda vapp: mext_prem(tpl(vapp))
    arms = {"int_": lambda fs, ihs: f"ir_mext_switch_n {MARGS} hf {FARGS} dflt dargs cases {fs[0]} h"}
    body = fam_rec("IRScalar", "v0", mot, arms, _scalar_default("not_int"), "v", SCALAR_NAMES, "v", hyp=hyp)
    return defn("ir_mext_switch_exec", f"{binders} {_hrun(tpl('v'))}", mext_goal(tpl("v")), f"{body} hrun")


def x_call_exec() -> str:
    binders, _, tpl = msig("ir_call_exec", "hf")
    body = lambda o: call_exec_body(S0, o)
    term = ext_lookup("IRFunc", "ir_func_find", "fs0", "fs", "hf", "fid", body, body, "gf",
                      refl("IRConfig", body("(IROption.some IRFunc gf)")))
    return defn("ir_mext_call_exec", f"{binders} {_hrun(tpl)}", mext_goal(tpl), f"{term} hrun")


def x_callind_exec() -> str:
    binders, _, _ = msig("ir_callind_exec", "hf")
    tpl = lambda cv: f"(ir_callind_exec {{M}} {S0} rs {cv} args)"
    mot = lambda cv: mext_stmt(tpl(cv))
    hyp = lambda cvapp: mext_prem(tpl(cvapp))
    arms = {"fnptr_": lambda fs, ihs: f"ir_mext_call_exec {MARGS} hf {FARGS} rs {fs[0]} args h",
            "nullptr_": lambda fs, ihs: refl("IRConfig", ub("null_deref"))}
    body = fam_rec("IRScalar", "cv0", mot, arms, _scalar_default("not_fnptr"), "cv", SCALAR_NAMES, "cv", hyp=hyp)
    return defn("ir_mext_callind_exec", f"{binders} {_hrun(tpl('cv'))}", mext_goal(tpl("cv")), f"{body} hrun")


def x_globaladdr() -> str:
    binders = f"{MBLOCK} {PREMISE['hg']} {FBLOCK} (rs : IRList Nat) (g : Nat)"
    tpl = f"(ir_bind_result {S0} rs (ir_globaladdr_eval {{M}} g))"
    body = lambda o: f"(ir_bind_result {S0} rs {globaladdr_body(o)})"
    term = ext_lookup("IRGlobal", "ir_global_find", "gs0", "gs", "hg", "g", body, body, "gg",
                      refl("IRConfig", body("(IROption.some IRGlobal gg)")))
    return defn("ir_mext_globaladdr", f"{binders} {_hrun(tpl)}", mext_goal(tpl), f"{term} hrun")


# --------------------------------------------------------------------------
# F'. the per-constructor arm lemmas, premise set read off the arm's module reads
# --------------------------------------------------------------------------


def mext_arm_prem(rhs: str) -> str | None:
    """Which extension premise an arm needs: `hg` if it evaluates a global
    address, `hf` if it hands the module to a helper (every such helper reaches
    ir_func_find), none if the module is unread or read only through
    ir_mod_encs, which is the empty table on both `IRModule.mk` sides."""
    if "ir_globaladdr_eval" in rhs:
        return "hg"
    if _MKV and "(ir_mod_encs m)" in rhs:
        return "enc"
    if uses("m", rhs.replace("(ir_mod_encs m)", "")):
        return "hf"
    return None


def _prem_binders(prem: str | None) -> str:
    """An arm's premise binders, then a trailing space (none: empty)."""
    if prem is None:
        return ""
    if prem == "enc":
        return f"{PREMISE['he']} {PREMISE['hl']} "
    return PREMISE[prem] + " "


def _prem_args(prem: str | None) -> str:
    """The premise arguments an arm lemma is applied to, with a leading space."""
    return "" if prem is None else " henc hlen" if prem == "enc" else " " + prem


def _enc_binders() -> str:
    return f" {PREMISE['he']} {PREMISE['hl']}" if _MKV else ""


def _enc_args() -> str:
    return " henc hlen" if _MKV else ""


def mext_arm_proof(ctor: str, names: list[str], rhs: str, prem: str | None) -> str:
    if prem is None:
        witness = re.sub(r"\bs\b", S0, rhs)
        witness = re.sub(r"\bm\b", M0, witness)
        return refl("IRConfig", f"({witness})")
    if prem == "enc":
        # The mkv `load`: both sides bind ir_load_view at their OWN table, so the
        # equation is ir_eq_cong of ir_bind_result over the view agreement the
        # encodings premise gives (ir_enc_agree_load_view).
        m = re.fullmatch(r"ir_bind_result s rs \(ir_load_view \(ir_mod_encs m\) (\w+) (.+)\)", rhs)
        assert m, (ctor, rhs)
        ty, r = m.group(1), re.sub(r"\bs\b", S0, m.group(2))
        return (f"ir_eq_cong IRStepResult IRConfig (fun (r1 : IRStepResult) => ir_bind_result {S0} rs r1) "
                f"(ir_load_view es0 {ty} {r}) (ir_load_view es {ty} {r}) "
                f"(ir_enc_agree_load_view es0 es henc hlen {ty} {r})")
    if prem == "hg":
        m = re.fullmatch(r"ir_bind_result s rs \(ir_globaladdr_eval m (\w+)\)", rhs)
        assert m, (ctor, rhs)
        return f"ir_mext_globaladdr {MARGS} hg {FARGS} rs {m.group(1)} hrun"
    head, *args = top_tokens(re.sub(r"\(ir_getd s (\w+)\)", r"(ir_frame_get f \1)", rhs))
    assert head.startswith("ir_") and args[:2] == ["m", "s"], (ctor, rhs)
    out = [f"ir_mext_{head[3:]}", MARGS, "hf", FARGS] + args[2:] + ["hrun"]
    term = " ".join(out)
    assert not uses("s", term) and not uses("m", term), term
    return term


def mext_arm_lemma(ctor: str, names: list[str], types: list[str], rhs: str) -> str:
    prem = mext_arm_prem(rhs)
    tpl = f"(ir_exec {{M}} {inst_app(ctor, names)} rs {S0})"
    fields = " ".join(f"({n} : {ty})" for n, ty in zip(names, types))
    binders = (f"{MBLOCK} {_prem_binders(prem)}{FBLOCK} (rs : IRList Nat) "
               f"{fields + ' ' if fields else ''}{_hrun(tpl)}")
    return defn(f"ir_mext_arm_{ctor}", binders, mext_goal(tpl), mext_arm_proof(ctor, names, rhs, prem))


def mext_arm_builder(ctor: str, names: list[str], types: list[str], rhs: str):
    return lambda: mext_arm_lemma(ctor, names, types, rhs)


# --------------------------------------------------------------------------
# G'. the main terms
# --------------------------------------------------------------------------


def g_mext_step() -> str:
    mk = lambda fr: f"(IRMachine.mk {fr} mem na)"
    mot_s = lambda s0: (f"Eq Bool (ir_stk_running (ir_step {M0} {s0})) Bool.true -> "
                        f"Eq IRConfig (ir_step {M0} {s0}) (ir_step {M1} {s0})")
    mot_fr = lambda fr0: mot_s(mk(fr0))
    bl, pc = "(ir_frame_block f)", "(ir_frame_pc f)"

    def layer(step):
        return lambda o: (f"Eq Bool (ir_stk_running {step(M0, o)}) Bool.true -> "
                          f"Eq IRConfig {step(M0, o)} {step(M1, o)}")

    step_f = lambda M, o: f"(ir_step_f {M} {S0} {bl} {pc} {o})"
    step_b = lambda M, o: f"(ir_step_b {M} {S0} {pc} {o})"
    step_n = lambda M, o: f"(ir_step_n {M} {S0} {o})"
    exec_node = lambda M, n0: f"(ir_exec_node {M} {n0} {S0})"
    exec_i = lambda M, i0: f"(ir_exec {M} {i0} rs {S0})"
    mot_b, mot_n, mot_nd, mot_i = layer(step_b), layer(step_n), layer(exec_node), layer(exec_i)

    def none_minor(step, param: str, fault: str) -> str:
        none = f"(IROption.none {param})"
        return (f"fun (_ : Eq Bool (ir_stk_running {step(M0, none)}) Bool.true) => "
                f"{refl('IRConfig', stuck(fault))}")

    inst_minors = []
    for ctor, names, types, rhs in ARMS:
        prem = mext_arm_prem(rhs)
        call = f"ir_mext_arm_{ctor} {MARGS}{_prem_args(prem)} {FARGS} rs {' '.join(names)}".rstrip()
        if names:
            fields = " ".join(f"({n} : {ty})" for n, ty in zip(names, types))
            inst_minors.append(f"(fun {fields} => {call})")
        else:
            inst_minors.append(f"({call})")
    inst_rec = f"IRInst.rec (fun (i0 : IRInst) => {mot_i('i0')}) {' '.join(inst_minors)} i"
    node_rec = f"IRNode.rec (fun (n0 : IRNode) => {mot_nd('n0')}) (fun (i : IRInst) (rs : IRList Nat) => {inst_rec}) nd"
    n_scrut = f"(ir_nodes_get (ir_block_nodes bk) {pc})"
    n_rec = neutral_opt_rec("IRNode", "on", mot_n, none_minor(step_n, "IRNode", "fetch_past_end"),
                            ("nd", "IRNode"), node_rec, n_scrut, mot_n(n_scrut))
    b_scrut = f"(ir_block_find (ir_func_blocks fn) {bl})"
    b_rec = neutral_opt_rec("IRBlock", "ob", mot_b, none_minor(step_b, "IRBlock", "no_block"),
                            ("bk", "IRBlock"), n_rec, b_scrut, mot_b(b_scrut))
    # The function fetch is the ONE lookup of the fetch chain the extension
    # premise closes: always the convoy, `some_term` is the block recursor
    # applied to the running premise at `some fn`.
    f_conv = ext_lookup("IRFunc", "ir_func_find", "fs0", "fs", "hf", "(ir_frame_func f)",
                        lambda o: step_f(M0, o), lambda o: step_f(M1, o), "fn", f"{b_rec} h")
    nil = "(IRList.nil IRFrame)"
    nil_minor = (f"(fun (_ : Eq Bool (ir_stk_running (ir_step {M0} {mk(nil)})) Bool.true) => "
                 f"{refl('IRConfig', stuck('no_frame'))})")
    cons_minor = f"(fun (f : IRFrame) (t : IRList IRFrame) (_ih : {mot_fr('t')}) => {f_conv})"
    list_rec = f"IRList.rec IRFrame (fun (fr0 : IRList IRFrame) => {mot_fr('fr0')}) {nil_minor} {cons_minor} fr"
    body = (f"IRMachine.rec (fun (s0 : IRMachine) => {mot_s('s0')}) "
            f"(fun (fr : IRList IRFrame) (mem : IRList IRMemSlot) (na : Nat) => {list_rec}) s hrun")
    binders = (f"{MBLOCK} {PREMISE['hf']} {PREMISE['hg']}{_enc_binders()} (s : IRMachine) "
               f"(hrun : Eq Bool (ir_stk_running (ir_step {M0} s)) Bool.true)")
    return defn("ir_mext_step", binders, f"Eq IRConfig (ir_step {M0} s) (ir_step {M1} s)", body)


def g_mext_steps() -> str:
    stmt = lambda k: (f"forall (c : IRConfig), Eq Bool (ir_stk_running (ir_steps {k} {M0} c)) Bool.true -> "
                      f"Eq IRConfig (ir_steps {k} {M0} c) (ir_steps {k} {M1} c)")
    mot_c = lambda c0: (f"Eq Bool (ir_stk_running (ir_steps (Nat.succ k) {M0} {c0})) Bool.true -> "
                        f"Eq IRConfig (ir_steps (Nat.succ k) {M0} {c0}) (ir_steps (Nat.succ k) {M1} {c0})")
    a = f"(ir_steps k {M0} (ir_step {M0} s))"
    b = f"(ir_steps k {M1} (ir_step {M0} s))"
    c = f"(ir_steps k {M1} (ir_step {M1} s))"
    running_minor = (
        f"(fun (s : IRMachine) (hrun : Eq Bool (ir_stk_running (ir_steps (Nat.succ k) {M0} (IRConfig.running s))) Bool.true) => "
        f"Eq.trans IRConfig {a} {b} {c} (ih (ir_step {M0} s) hrun) "
        f"(ir_eq_cong IRConfig IRConfig (fun (c1 : IRConfig) => ir_steps k {M1} c1) (ir_step {M0} s) (ir_step {M1} s) "
        f"(ir_mext_step {MARGS} hf hg{_enc_args()} s (ir_stk_running_back {M0} k (ir_step {M0} s) hrun))))")
    halted_minor = (f"(fun (o : IROutcome) (_ : Eq Bool (ir_stk_running (ir_steps (Nat.succ k) {M0} (IRConfig.halted o))) Bool.true) => "
                    f"{refl('IRConfig', halted('o'))})")
    zero = (f"(fun (c : IRConfig) (_ : Eq Bool (ir_stk_running (ir_steps Nat.zero {M0} c)) Bool.true) => "
            f"{refl('IRConfig', 'c')})")
    succ = (f"(fun (k : Nat) (ih : {stmt('k')}) => fun (c : IRConfig) => "
            f"IRConfig.rec (fun (c0 : IRConfig) => {mot_c('c0')}) {running_minor} {halted_minor} c)")
    body = f"Nat.rec (fun (k : Nat) => {stmt('k')}) {zero} {succ} n"
    binders = f"{MBLOCK} {PREMISE['hf']} {PREMISE['hg']}{_enc_binders()} (n : Nat)"
    return defn("ir_mext_steps", binders, stmt("n"), body)


# ==========================================================================
# THE ir_stkn FAMILY -- the FETCHED-NODE classifier and the node-keyed twin
# ==========================================================================
#
# The running-keyed ir_stk family consumes its premise in exactly two leaves:
# the empty frame list (ir_stk_step) and the empty caller list at a ret
# (ir_ret_to_stack). Both are facts about the FETCHED NODE and the frame list,
# never about the step's outcome. So the premise is replaced here by a Bool
# classifier on the machine -- `ir_stk_botret`, true exactly at a single frame
# whose fetch is a `ret` -- plus an explicit nonempty-frames premise, because
# the classifier is false on the empty list and the empty list does NOT commute
# (ir_step halts stuck no_frame there while the stacked machine steps `rest`).
#
# With no outcome premise, a step that FAULTS commutes too: the stacked step
# halts with the same fault. That is the case the running-keyed family cannot
# state, and the reason the split (eval_ir_stack_split.rs) needs this twin.
#
# Reused unchanged: the 30 `*_stack` writer/branching helpers (none takes a
# premise). Twinned: the per-constructor arms (premise-free except ret), the one
# writer that reads the tail (ir_ret_to), and the main term.

FALSE_K = "(fun (_ : IRFrame) (_ : IRList IRFrame) (_ : Bool) => Bool.false)"
NIL_F = "(IRList.nil IRFrame)"


def frames_case(nil_val: str, t: str) -> str:
    """`IRList.rec IRFrame (fun _ => Bool) nil_val (fun _ _ _ => Bool.false) t`:
    the Bool that is `nil_val` on an empty list and false on a cons. With
    nil_val = Bool.true it IS ir_frames_is_nil's body, which is how the classifier
    premise at a ret node becomes the arm's `t is not nil` premise by iota."""
    return f"(IRList.rec IRFrame (fun (_ : IRList IRFrame) => Bool) {nil_val} {FALSE_K} {t})"


def node_prem(cls: str) -> str:
    """The classifier premise at a cons machine `f :: t`, with the fetch layer's
    Bool abstracted: false iff t is a cons, or t is empty and the fetch is not ret."""
    return f"Eq Bool {frames_case(cls, 't')} Bool.false"


def k_frames_is_nil() -> str:
    return defn("ir_frames_is_nil", "(fs : IRList IRFrame)", "Bool",
                frames_case("Bool.true", "fs")[1:-1])


def k_inst_is_ret() -> str:
    names = {c: [f"{n}" for n in ns] for c, ns, _, _ in ARMS}
    body = fam_rec("IRInst", "i0", lambda _v: "Bool", {"ret": lambda fs, ihs: "Bool.true"},
                   lambda fs, ihs: "Bool.false", "i", names, "r")
    return defn("ir_inst_is_ret", "(i : IRInst)", "Bool", body)


def k_node_is_ret() -> str:
    assert [c for c, _ in ctors("IRNode")] == ["mk"]
    return defn("ir_node_is_ret", "(n : IRNode)", "Bool",
                "IRNode.rec (fun (_ : IRNode) => Bool) (fun (i : IRInst) (_ : IRList Nat) => ir_inst_is_ret i) n")


def k_fetch_n_ret() -> str:
    return defn("ir_fetch_n_ret", "(on : IROption IRNode)", "Bool",
                "IROption.rec IRNode (fun (_ : IROption IRNode) => Bool) Bool.false "
                "(fun (n : IRNode) => ir_node_is_ret n) on")


def k_fetch_b_ret() -> str:
    return defn("ir_fetch_b_ret", "(pc : Nat) (ob : IROption IRBlock)", "Bool",
                "IROption.rec IRBlock (fun (_ : IROption IRBlock) => Bool) Bool.false "
                "(fun (b : IRBlock) => ir_fetch_n_ret (ir_nodes_get (ir_block_nodes b) pc)) ob")


def k_fetch_f_ret() -> str:
    return defn("ir_fetch_f_ret", "(bl : Nat) (pc : Nat) (of : IROption IRFunc)", "Bool",
                "IROption.rec IRFunc (fun (_ : IROption IRFunc) => Bool) Bool.false "
                "(fun (fn : IRFunc) => ir_fetch_b_ret pc (ir_block_find (ir_func_blocks fn) bl)) of")


def cls_f_at(fr: str, m: str = "m") -> str:
    """The function-layer classifier at frame `fr`, spelled exactly as ir_step fetches."""
    return (f"(ir_fetch_f_ret (ir_frame_block {fr}) (ir_frame_pc {fr}) "
            f"(ir_func_find (ir_mod_funcs {m}) (ir_frame_func {fr})))")


def k_botret() -> str:
    body = ("IRMachine.rec (fun (_ : IRMachine) => Bool) "
            "(fun (fs : IRList IRFrame) (_ : IRList IRMemSlot) (_ : Nat) => "
            "IRList.rec IRFrame (fun (_ : IRList IRFrame) => Bool) Bool.false "
            f"(fun (f : IRFrame) (t : IRList IRFrame) (_ : Bool) => {frames_case(cls_f_at('f'), 't')[1:-1]}) fs) s")
    return defn("ir_stk_botret", "(m : IRModule) (s : IRMachine)", "Bool", body)


def k_pin(name: str, binders: str, lhs: str, rhs: str) -> str:
    return defn(name, binders, f"Eq Bool {lhs} {rhs}", refl("Bool", rhs))


def k_pins() -> list[tuple[str, str, object, str]]:
    """Vacuity pins: an undeclared id in a TYPE becomes a silent free variable,
    so every classifier layer is pinned at a constructor, by computation, in both
    polarities where it has two."""
    mk = lambda fs: f"(IRMachine.mk {fs} mem na)"
    blk = "(m : IRModule) (mem : IRList IRMemSlot) (na : Nat)"
    rows = [
        ("ir_frames_is_nil_nil", "", f"(ir_frames_is_nil {NIL_F})", "Bool.true",
         "the empty frame list IS nil"),
        ("ir_frames_is_nil_cons", "(f : IRFrame) (t : IRList IRFrame)",
         "(ir_frames_is_nil (IRList.cons IRFrame f t))", "Bool.false", "a cons is not nil, whatever its tail"),
        ("ir_inst_is_ret_ret", "(ids : IRList Nat)", "(ir_inst_is_ret (IRInst.ret ids))", "Bool.true",
         "the ret constructor is classified ret, at every operand list"),
        ("ir_inst_is_ret_call", "(fid : Nat) (args : IRList Nat)", "(ir_inst_is_ret (IRInst.call fid args))",
         "Bool.false", "a call is not a ret -- the negative polarity, at the constructor ir_call_push is about"),
        ("ir_stk_botret_nil", blk, f"(ir_stk_botret m {mk(NIL_F)})", "Bool.false",
         "the classifier is FALSE on the empty frame list -- which is why every theorem over it also takes "
         "the nonempty premise: the empty list is outside the commuting class but not a bottom ret"),
        ("ir_stk_botret_two", f"{blk} (f : IRFrame) (g : IRFrame) (t : IRList IRFrame)",
         f"(ir_stk_botret m {mk('(IRList.cons IRFrame f (IRList.cons IRFrame g t))')})", "Bool.false",
         "the classifier is FALSE on two or more frames, whatever the head fetches: a ret there pops into a "
         "caller that is part of the standalone run, so it commutes"),
    ]
    out = []
    for name, binders, lhs, rhs, why in rows:
        out.append((f"SRC_{name[3:].upper()}", name,
                    (lambda n=name, b=binders, l=lhs, r=rhs: k_pin(n, b, l, r)),
                    f"{name}: vacuity pin -- {why}. Eq.refl, so the classifier's definition is held to this spelling. {D}"))
    return out


def d_stkn_ret_to() -> str:
    def mot(v: str) -> str:
        return (f"Eq Bool (ir_frames_is_nil {v}) Bool.false -> "
                f"Eq IRConfig (ir_ret_to ds (ir_frames_app {v} rest) mem na vs) "
                f"(ir_config_stack (ir_ret_to ds {v} mem na vs) rest)")
    nil_goal = (f"Eq IRConfig (ir_ret_to ds (ir_frames_app {NIL_F} rest) mem na vs) "
                f"(ir_config_stack (ir_ret_to ds {NIL_F} mem na vs) rest)")
    nil_minor = (f"(fun (h0 : Eq Bool (ir_frames_is_nil {NIL_F}) Bool.false) => "
                 f"ir_bool_false_ne_true ({nil_goal}) (Eq.symm Bool (ir_frames_is_nil {NIL_F}) Bool.false h0))")
    cons_minor = (f"(fun (g : IRFrame) (t2 : IRList IRFrame) (_ih : {mot('t2')}) "
                  f"(_ : Eq Bool (ir_frames_is_nil (IRList.cons IRFrame g t2)) Bool.false) => "
                  f"{refl('IRConfig', running(cons('(ir_frame_set_many g ds vs)', '(ir_frames_app t2 rest)')))})")
    body = f"IRList.rec IRFrame (fun (t0 : IRList IRFrame) => {mot('t0')}) {nil_minor} {cons_minor} t h"
    binders = ("(ds : IRList Nat) (rest : IRList IRFrame) (mem : IRList IRMemSlot) (na : Nat) "
               "(vs : IRList IRScalar) (t : IRList IRFrame) "
               "(h : Eq Bool (ir_frames_is_nil t) Bool.false)")
    ty = (f"Eq IRConfig (ir_ret_to ds (ir_frames_app t rest) mem na vs) "
          f"(ir_config_stack (ir_ret_to ds t mem na vs) rest)")
    return defn("ir_stkn_ret_to", binders, ty, body)


def is_ret_rhs(rhs: str) -> bool:
    return rhs.startswith("ir_return_exec s ")


def stkn_arm_lemma(ctor: str, names: list[str], types: list[str], rhs: str) -> str:
    tpl = f"(ir_exec m {inst_app(ctor, names)} rs {{S}})"
    parts = ["(m : IRModule)", BLOCK, "(rs : IRList Nat)"]
    parts += [f"({n} : {ty})" for n, ty in zip(names, types)]
    if is_ret_rhs(rhs):
        parts.append("(ht : Eq Bool (ir_frames_is_nil t) Bool.false)")
    return defn(f"ir_stkn_arm_{ctor}", " ".join(parts), stk_goal(tpl),
                arm_proof(ctor, names, rhs, tpl, ret_lemma="ir_stkn_ret_to", ret_prem="ht"))


def stkn_arm_builder(ctor: str, names: list[str], types: list[str], rhs: str):
    return lambda: stkn_arm_lemma(ctor, names, types, rhs)


def _fetch_layers():
    bl, pc = "(ir_frame_block f)", "(ir_frame_pc f)"
    step_f = lambda S, o: f"(ir_step_f m {S} {bl} {pc} {o})"
    step_b = lambda S, o: f"(ir_step_b m {S} {pc} {o})"
    step_n = lambda S, o: f"(ir_step_n m {S} {o})"
    exec_node = lambda S, n0: f"(ir_exec_node m {n0} {S})"
    exec_i = lambda S, i0: f"(ir_exec m {i0} rs {S})"
    cls_f = lambda o: f"(ir_fetch_f_ret {bl} {pc} {o})"
    cls_b = lambda o: f"(ir_fetch_b_ret {pc} {o})"
    cls_n = lambda o: f"(ir_fetch_n_ret {o})"
    cls_nd = lambda n0: f"(ir_node_is_ret {n0})"
    cls_i = lambda i0: f"(ir_inst_is_ret {i0})"
    return bl, pc, (step_f, cls_f), (step_b, cls_b), (step_n, cls_n), (exec_node, cls_nd), (exec_i, cls_i)


def g_stkn_step() -> str:
    mk = lambda fs: f"(IRMachine.mk {fs} mem na)"
    goal_s = lambda s0: (f"Eq IRConfig (ir_step m (ir_mach_stack {s0} rest)) "
                         f"(ir_config_stack (ir_step m {s0}) rest)")
    hc_s = lambda s0: f"Eq Bool (ir_stk_botret m {s0}) Bool.false"
    mot_s = lambda s0: (f"Eq Bool (ir_frames_is_nil (ir_mach_frames {s0})) Bool.false -> "
                        f"{hc_s(s0)} -> {goal_s(s0)}")
    mot_fs = lambda fs0: f"Eq Bool (ir_frames_is_nil {fs0}) Bool.false -> {hc_s(mk(fs0))} -> {goal_s(mk(fs0))}"
    bl, pc, F, B, N, ND, I = _fetch_layers()

    def layer(step, cls):
        return lambda o: (f"{node_prem(cls(o))} -> "
                          f"Eq IRConfig {step(S1, o)} (ir_config_stack {step(S0, o)} rest)")

    mot_f, mot_b, mot_n = layer(*F), layer(*B), layer(*N)
    mot_nd, mot_i = layer(*ND), layer(*I)

    def none_minor(cls, param: str, fault: str) -> str:
        none = "(IROption.none " + param + ")"
        return f"fun (_ : {node_prem(cls(none))}) => {refl('IRConfig', stuck(fault))}"

    inst_minors = []
    for ctor, names, types, rhs in ARMS:
        call = f"ir_stkn_arm_{ctor} m {BARGS} rs {' '.join(names)}".rstrip()
        fields = " ".join(f"({n} : {ty})" for n, ty in zip(names, types))
        prem = node_prem(I[1](inst_app(ctor, names)))
        if is_ret_rhs(rhs):
            inst_minors.append(f"(fun {fields} (hp : {prem}) => {call} hp)")
        else:
            inst_minors.append(f"(fun {fields + ' ' if fields else ''}(_ : {prem}) => {call})")
    inst_rec = f"IRInst.rec (fun (i0 : IRInst) => {mot_i('i0')}) {' '.join(inst_minors)} i"
    node_rec = f"IRNode.rec (fun (n0 : IRNode) => {mot_nd('n0')}) (fun (i : IRInst) (rs : IRList Nat) => {inst_rec}) nd"
    n_scrut = f"(ir_nodes_get (ir_block_nodes bk) {pc})"
    n_rec = neutral_opt_rec("IRNode", "on", mot_n, none_minor(N[1], "IRNode", "fetch_past_end"),
                            ("nd", "IRNode"), node_rec, n_scrut, mot_n(n_scrut))
    b_scrut = f"(ir_block_find (ir_func_blocks fn) {bl})"
    b_rec = neutral_opt_rec("IRBlock", "ob", mot_b, none_minor(B[1], "IRBlock", "no_block"),
                            ("bk", "IRBlock"), n_rec, b_scrut, mot_b(b_scrut))
    f_scrut = "(ir_func_find (ir_mod_funcs m) (ir_frame_func f))"
    f_rec = neutral_opt_rec("IRFunc", "o", mot_f, none_minor(F[1], "IRFunc", "no_func"),
                            ("fn", "IRFunc"), b_rec, f_scrut, mot_f(f_scrut))
    nil_minor = (f"(fun (h : Eq Bool (ir_frames_is_nil {NIL_F}) Bool.false) (_ : {hc_s(mk(NIL_F))}) => "
                 f"ir_bool_false_ne_true ({goal_s(mk(NIL_F))}) (Eq.symm Bool (ir_frames_is_nil {NIL_F}) Bool.false h))")
    cons_minor = (f"(fun (f : IRFrame) (t : IRList IRFrame) (_ih : {mot_fs('t')}) "
                  f"(_ : Eq Bool (ir_frames_is_nil (IRList.cons IRFrame f t)) Bool.false) => {f_rec})")
    list_rec = f"IRList.rec IRFrame (fun (fs0 : IRList IRFrame) => {mot_fs('fs0')}) {nil_minor} {cons_minor} fs"
    body = (f"IRMachine.rec (fun (s0 : IRMachine) => {mot_s('s0')}) "
            f"(fun (fs : IRList IRFrame) (mem : IRList IRMemSlot) (na : Nat) => {list_rec}) s hne hc")
    binders = ("(m : IRModule) (s : IRMachine) (rest : IRList IRFrame) "
               "(hne : Eq Bool (ir_frames_is_nil (ir_mach_frames s)) Bool.false) "
               "(hc : Eq Bool (ir_stk_botret m s) Bool.false)")
    return defn("ir_stkn_step", binders, goal_s("s"), body)


def g_botret_false_of_running() -> str:
    mk = lambda fs: f"(IRMachine.mk {fs} mem na)"
    run = lambda c: f"Eq Bool (ir_stk_running {c}) Bool.true"
    mot_s = lambda s0: f"{run('(ir_step m ' + s0 + ')')} -> Eq Bool (ir_stk_botret m {s0}) Bool.false"
    mot_fs = lambda fs0: mot_s(mk(fs0))
    S0n = mk(cons("f", NIL_F))
    bl, pc, F, B, N, ND, I = _fetch_layers()

    def layer(step, cls):
        return lambda o: f"{run(step(S0n, o))} -> Eq Bool {cls(o)} Bool.false"

    mot_f, mot_b, mot_n = layer(*F), layer(*B), layer(*N)
    mot_nd, mot_i = layer(*ND), layer(*I)

    def none_minor(step, cls, param: str) -> str:
        none = f"(IROption.none {param})"
        return (f"fun (h : {run(step(S0n, none))}) => "
                f"ir_bool_false_ne_true (Eq Bool {cls(none)} Bool.false) h")

    inst_minors = []
    for ctor, names, types, rhs in ARMS:
        fields = " ".join(f"({n} : {ty})" for n, ty in zip(names, types))
        prem = run(I[0](S0n, inst_app(ctor, names)))
        concl = f"Eq Bool {I[1](inst_app(ctor, names))} Bool.false"
        lead = f"fun {fields + ' ' if fields else ''}"
        if is_ret_rhs(rhs):
            inst_minors.append(f"({lead}(h : {prem}) => ir_bool_false_ne_true ({concl}) h)")
        else:
            inst_minors.append(f"({lead}(_ : {prem}) => {refl('Bool', 'Bool.false')})")
    inst_rec = f"IRInst.rec (fun (i0 : IRInst) => {mot_i('i0')}) {' '.join(inst_minors)} i"
    node_rec = f"IRNode.rec (fun (n0 : IRNode) => {mot_nd('n0')}) (fun (i : IRInst) (rs : IRList Nat) => {inst_rec}) nd"
    n_scrut = f"(ir_nodes_get (ir_block_nodes bk) {pc})"
    n_rec = neutral_opt_rec("IRNode", "on", mot_n, none_minor(N[0], N[1], "IRNode"),
                            ("nd", "IRNode"), node_rec, n_scrut, mot_n(n_scrut))
    b_scrut = f"(ir_block_find (ir_func_blocks fn) {bl})"
    b_rec = neutral_opt_rec("IRBlock", "ob", mot_b, none_minor(B[0], B[1], "IRBlock"),
                            ("bk", "IRBlock"), n_rec, b_scrut, mot_b(b_scrut))
    f_scrut = "(ir_func_find (ir_mod_funcs m) (ir_frame_func f))"
    f_rec = neutral_opt_rec("IRFunc", "o", mot_f, none_minor(F[0], F[1], "IRFunc"),
                            ("fn", "IRFunc"), b_rec, f_scrut, mot_f(f_scrut))
    def t_mot(t0: str) -> str:
        step = "(ir_step m " + mk(cons("f", t0)) + ")"
        return f"{run(step)} -> Eq Bool {frames_case(cls_f_at('f'), t0)} Bool.false"

    step_two = "(ir_step m " + mk(cons("f", cons("g", "t2"))) + ")"
    t_cons = (f"(fun (g : IRFrame) (t2 : IRList IRFrame) (_ih : {t_mot('t2')}) "
              f"(_ : {run(step_two)}) => {refl('Bool', 'Bool.false')})")
    t_rec = f"IRList.rec IRFrame (fun (t0 : IRList IRFrame) => {t_mot('t0')}) ({f_rec}) {t_cons} t"
    step_nil = "(ir_step m " + mk(NIL_F) + ")"
    nil_minor = f"(fun (_ : {run(step_nil)}) => {refl('Bool', 'Bool.false')})"
    cons_minor = f"(fun (f : IRFrame) (t : IRList IRFrame) (_ih : {mot_fs('t')}) => {t_rec})"
    list_rec = f"IRList.rec IRFrame (fun (fs0 : IRList IRFrame) => {mot_fs('fs0')}) {nil_minor} {cons_minor} fs"
    body = (f"IRMachine.rec (fun (s0 : IRMachine) => {mot_s('s0')}) "
            f"(fun (fs : IRList IRFrame) (mem : IRList IRMemSlot) (na : Nat) => {list_rec}) s hrun")
    binders = f"(m : IRModule) (s : IRMachine) (hrun : {run('(ir_step m s)')})"
    return defn("ir_stk_botret_false_of_running", binders, "Eq Bool (ir_stk_botret m s) Bool.false", body)


# --------------------------------------------------------------------------
# The registry: (CONST, name, builder, description), in REGISTRATION order.
# --------------------------------------------------------------------------

D = "DerivedProved, zero axiom_deps."


def _arm_desc(ctor: str, rhs: str) -> str:
    if rhs.startswith("IRConfig.halted "):
        how = "both sides halt identically and ir_config_stack is the identity on a halted configuration, so Eq.refl closes it"
    elif rhs.startswith("ir_return_exec s "):
        how = ("the ONE arm that reads the tail: ir_return_exec is ir_ret_to at the head frame's dests over the caller list, "
               "so the resolved ids are transported through ir_resolve_stack and ir_ret_to_stack consumes the running premise")
    else:
        head = top_tokens(rhs)[0]
        how = f"one application of {head}_stack at the arm's operands read from the head frame"
        if "(ir_resolve s " in rhs:
            how += ", after one Eq.subst through ir_resolve_stack for the resolved id list"
    used = "consumed" if ctor == "ret" else "bound and unused"
    refusal = ("This is an explicit legacy refusal, not successful execution coverage. "
               if rhs.startswith("IRConfig.halted (IROutcome.unmodelled ") else "")
    return (f"ir_stk_arm_{ctor}: the `{ctor}` arm of ir_exec is tail-independent while it stays running -- {how}. "
            f"The defeq between `ir_exec m (IRInst.{ctor} ..) rs S` and the helper it dispatches to is checked when THIS "
            f"declaration registers, so a failure names the arm; the running premise is {used}. {refusal}{D}")


def _mext_arm_desc(ctor: str, rhs: str) -> str:
    prem = mext_arm_prem(rhs)
    if prem is None and "(ir_mod_encs m)" in rhs:
        how = ("the arm reads the module ONLY through ir_mod_encs, which is the empty encodings table on both "
               "IRModule.mk sides by iota, so the two steps are the same term after delta and Eq.refl closes it with no premise")
    elif prem is None:
        how = ("the arm reads no module at all (it is stated at both modules only to be dispatched from the same skeleton), "
               "so the two steps unfold to the same term and Eq.refl closes it with no premise")
    elif prem == "hg":
        how = ("the arm reads the globals through ir_globaladdr_eval, so it is one application of ir_mext_globaladdr "
               "under hg; a global absent from M0 halts the M0 step and is refuted from the running premise")
    else:
        head = top_tokens(rhs)[0]
        how = (f"the arm hands the module to {head}, which reaches ir_func_find, so it is one application of "
               f"ir_mext_{head[3:]} under hf; a function absent from M0 halts the M0 step and is refuted from the running premise")
    refusal = ("This is an explicit legacy refusal, not successful execution coverage. "
               if rhs.startswith("IRConfig.halted (IROutcome.unmodelled ") else "")
    return (f"ir_mext_arm_{ctor}: the `{ctor}` arm of ir_exec steps identically in an extended module while it stays running "
            f"in the original -- {how}. The defeq between `ir_exec (IRModule.mk ..) (IRInst.{ctor} ..) rs S` and its unfolding "
            f"is checked when THIS declaration registers, so a failure names the arm. {refusal}{D}")


TERMS: list[tuple[str, str, object, str]] = [
    ("SRC_GETD_STACK", "ir_getd_stack", c_getd,
     f"ir_getd_stack: an SSA read is HEAD-ONLY. The machine with `rest` beneath its frames reads the same value as the machine without it -- Eq.refl at `ir_frame_get f k`, because ir_frames_get discards the tail. The operand defeq every per-arm lemma relies on, pinned; the risk-4 fallback would rewrite through it explicitly. {D}"),
    ("SRC_MACH_MEM_STACK", "ir_mach_mem_stack", c_mach_mem,
     f"ir_mach_mem_stack: the heap projection does not see the frame stack -- Eq.refl at `mem`. The pin behind the load, store and borrow arms, whose evaluators read `ir_mach_mem s`. {D}"),
    ("SRC_RESOLVE_STACK", "ir_resolve_stack", c_resolve,
     f"ir_resolve_stack: resolving an argument list reads the head frame only, at EVERY id list -- IRList.rec on the ids, cons minor by ir_eq_cong over IRList.cons of the head read. NOT Eq.refl: ir_resolve is stuck on an abstract list, so this is the one head-only fact that needs induction, and it is what the jump, call, gep and ret arms transport through. {D}"),
    ("SRC_BIND_STACK", "ir_bind_stack", d_bind,
     f"ir_bind_stack: binding a result re-conses the tail verbatim, so stacking `rest` beneath commutes with the bind -- Eq.refl at the running machine whose head is the bound frame over `ir_frames_app t rest` (one IRMachine.rec iota, one IRList.rec iota, one ir_frames_app iota on each side). {D}"),
    ("SRC_BIND_RESULT_STACK", "ir_bind_result_stack", d_bind_result,
     f"ir_bind_result_stack: the same over a step result -- IRStepResult.rec, the first proof-level use of it in the tree: a value routes to ir_bind_stack, a fault halts identically on both sides because ir_config_stack is the identity on a halted configuration. The ir_bind_result dispatch arms go through this lemma. {D}"),
    ("SRC_BIND2_STACK", "ir_bind2_stack", d_bind2,
     f"ir_bind2_stack: the two-result bind that overflow uses commutes with stacking -- Eq.refl, ir_bind_stack's shape with ir_frame_bind2 in place of ir_frame_bind. {D}"),
    ("SRC_ADVANCE_STACK", "ir_advance_stack", d_advance,
     f"ir_advance_stack: advancing past a value-less instruction commutes with stacking -- Eq.refl at the advanced head frame over `ir_frames_app t rest`. The assert path and the store path both end here. {D}"),
    ("SRC_ADVANCE_SET_MEM_STACK", "ir_advance_set_mem_stack", d_advance_set_mem,
     f"ir_advance_set_mem_stack: an advance after a heap replacement commutes with stacking, at EVERY replacement heap m2 -- Eq.refl; ir_set_mem keeps the frames and ir_advance re-conses the tail. This is the store's commit path, stated once for ir_store_live_stack. {D}"),
    ("SRC_ALLOCA_K_STACK", "ir_alloca_k_stack", d_alloca_k,
     f"ir_alloca_k_stack: allocation commutes with stacking -- Eq.refl at the fresh cells consed on the heap, the bumped counter and the head frame bound to `ptr_ na`; the tail is re-consed verbatim. Heap and counter are the SAME on both sides, which is what makes the lemma family compose with the callee's own heap contract later. {D}"),
    ("SRC_GOTO_STACK", "ir_goto_stack", d_goto,
     f"ir_goto_stack: an intra-function jump rebuilds the head frame at the target block with the branch arguments bound and re-conses the tail -- Eq.refl. Shared by br, condbr and switch through ir_jump_stack. {D}"),
    ("SRC_PUSH_STACK", "ir_push_stack", d_push,
     f"ir_push_stack: pushing a callee frame commutes with stacking -- Eq.refl at `callee :: ir_frame_advance f :: ir_frames_app t rest`, two ir_frames_app iotas on the standalone side. The machine only ever LENGTHENS the tail; nothing on the step path inspects it until ret. {D}"),
    ("SRC_RET_TO_STACK", "ir_ret_to_stack", d_ret_to,
     f"ir_ret_to_stack: THE ONE WRITER THAT NEEDS THE PREMISE. ir_ret_to eliminates on the caller list itself: at a non-empty list it pops into that list and re-conses the rest, so stacking commutes (Eq.refl); at the EMPTY list it halts with IROutcome.ret where the stacked run would continue into `rest`, and that leaf is refuted from the running hypothesis by ir_bool_false_ne_true -- the hypothesis reduces to Eq Bool Bool.false Bool.true. IRList.rec on the caller list, hypothesis-passing motive. {D}"),
    ("SRC_STORE_LIVE_STACK", "ir_store_live_stack", e_store_live,
     f"ir_store_live_stack: Bool.rec on the liveness bit, minor order (false, true) -- a dead cell halts identically with bad_addr (Eq.refl), a live cell commits through ir_advance_set_mem_stack at the updated heap; `ir_mach_mem S` on both sides is `mem` by computation. {D}"),
    ("SRC_STORE_CHECKED_STACK", "ir_store_checked_stack", e_store_checked,
     f"ir_store_checked_stack: IROption.rec on the looked-up cell -- an absent cell halts identically with bad_addr, a present one routes to ir_store_live_stack at the cell's own liveness bit. {D}"),
    ("SRC_STORE_EXEC_STACK", "ir_store_exec_stack", e_store_exec,
     f"ir_store_exec_stack: IRScalar.rec on the pointer operand, one minor per constructor read off the family declaration -- ptr_ and fat_ route to ir_store_checked_stack at the head-only heap lookup, nullptr_ halts identically with null_deref, the other nine with not_ptr. Minor arity is fields-then-IHs (aggv one field one IH, vcons two and two). {D}"),
    ("SRC_JUMP_BLOCK_STACK", "ir_jump_block_stack", e_jump_block,
     f"ir_jump_block_stack: IROption.rec on the resolved block -- no_block halts identically, a block routes to ir_goto_stack at its own parameter list. {D}"),
    ("SRC_JUMP_FUNC_STACK", "ir_jump_func_stack", e_jump_func,
     f"ir_jump_func_stack: IROption.rec on the resolved function -- no_func halts identically, a function routes to ir_jump_block_stack at its block lookup, which is the same term on both sides. {D}"),
    ("SRC_JUMP_STACK", "ir_jump_stack", e_jump,
     f"ir_jump_stack: br, and the shared target of condbr and switch. ir_cur_func is head-only, so the function lookup is the same term on both sides by computation; the branch ARGUMENTS are stuck on an abstract id list and are transported through ir_resolve_stack by one Eq.subst plus Eq.symm before ir_jump_func_stack closes. {D}"),
    ("SRC_CONDBR_B_STACK", "ir_condbr_b_stack", e_condbr_b,
     f"ir_condbr_b_stack: Bool.rec on the decided condition, minor order (false, true) -- each edge is ir_jump_stack at its own target and arguments. {D}"),
    ("SRC_CONDBR_EXEC_STACK", "ir_condbr_exec_stack", e_condbr_exec,
     f"ir_condbr_exec_stack: IRScalar.rec on the condition operand -- bool_ routes to ir_condbr_b_stack, the other eleven halt identically with not_bool because ir_as_bool is none on them by iota. {D}"),
    ("SRC_SWITCH_N_STACK", "ir_switch_n_stack", e_switch_n,
     f"ir_switch_n_stack: IROption.rec on the NEUTRAL scrutinee `ir_case_find cases n` with a goal-abstracting motive whose body is ir_switch_n's own -- the ir_view_opt_agg / ir_load_view_agg precedent, applied at the lookup. Default and matched arms are both ir_jump_stack. {D}"),
    ("SRC_SWITCH_EXEC_STACK", "ir_switch_exec_stack", e_switch_exec,
     f"ir_switch_exec_stack: IRScalar.rec on the selector -- int_ routes to ir_switch_n_stack at the decided integer, the other eleven halt identically with not_int. {D}"),
    ("SRC_CALL_EXEC_STACK", "ir_call_exec_stack", e_call_exec,
     f"ir_call_exec_stack: IROption.rec on the NEUTRAL callee lookup `ir_func_find (ir_mod_funcs m) fid` -- no_func halts identically; a callee is ir_push_stack after one Eq.subst through ir_resolve_stack for the arguments. The module axis is untouched: the lookup is the same term on both sides, which is why this lemma says nothing about a callee the module lacks. {D}"),
    ("SRC_CALLIND_EXEC_STACK", "ir_callind_exec_stack", e_callind_exec,
     f"ir_callind_exec_stack: IRScalar.rec on the callee value -- fnptr_ routes to ir_call_exec_stack at the function id, nullptr_ halts identically with null_deref, the other ten with not_fnptr. {D}"),
    ("SRC_ASSERT_B_STACK", "ir_assert_b_stack", e_assert_b,
     f"ir_assert_b_stack: Bool.rec on the decided condition, minor order (false, true) -- a failed assertion halts identically with assert_failed, a passed one is ir_advance_stack. {D}"),
    ("SRC_ASSERT_EXEC_STACK", "ir_assert_exec_stack", e_assert_exec,
     f"ir_assert_exec_stack: IRScalar.rec on the condition operand -- bool_ routes to ir_assert_b_stack, the other eleven halt identically with not_bool. {D}"),
    ("SRC_ALLOCA_EXEC_STACK", "ir_alloca_exec_stack", e_alloca_exec,
     f"ir_alloca_exec_stack: IROption.rec on the instruction's count field -- absent allocates one cell (ir_alloca_k_stack at `Nat.succ Nat.zero`, ir_alloca_count computing); present eliminates again on the NEUTRAL head-only read `ir_as_int (ir_frame_get f i)` with a goal-abstracting motive whose body is ir_alloca_exec's own: none halts identically with not_int, some k is ir_alloca_k_stack. {D}"),
    ("SRC_OVERFLOW_INTS_STACK", "ir_overflow_ints_stack", e_overflow_ints,
     f"ir_overflow_ints_stack: the decided-integer case is one ir_bind2_stack at the wrapped value and the flag -- the arguments are ir_overflow_ints's own body with the machine replaced by the stacking block, read from the source by the generator rather than retyped. {D}"),
    ("SRC_OVERFLOW_VALS_STACK", "ir_overflow_vals_stack", e_overflow_vals,
     f"ir_overflow_vals_stack: IRScalar.rec on the first operand, then IRScalar.rec on the second inside the int_ minor -- the int_/int_ cell routes to ir_overflow_ints_stack, every other cell halts identically with not_int because ir_as_int is none on it by iota. {D}"),
    ("SRC_OVERFLOW_EXEC_STACK", "ir_overflow_exec_stack", e_overflow_exec,
     f"ir_overflow_exec_stack: IRTy.rec on the declared type, one minor per constructor read off the family declaration -- int_ (signed) and uint_ (unsigned) route to ir_overflow_vals_stack at their width, every other constructor halts identically with not_int. The six pointer-like constructors and array_ are recursive and carry one IH each, fields first. {D}"),
]
TERMS += [
    (f"SRC_STK_ARM_{ctor.upper()}", f"ir_stk_arm_{ctor}", arm_builder(ctor, names, types, rhs), _arm_desc(ctor, rhs))
    for ctor, names, types, rhs in ARMS
]
TERMS.append((
    "SRC_STK_STEP", "ir_stk_step", g_stk_step,
    f"ir_stk_step (S1): *** ONE STEP IS TAIL-INDEPENDENT WHILE IT STAYS RUNNING. *** IRMachine.rec, then IRList.rec on the frames -- the nil minor is refuted from the premise (standalone is stuck no_frame, stacked would run the caller) -- then the three fetch recursors on their NEUTRAL majors (function, block, node; every none minor is Eq.refl because both sides halt identically), IRNode.rec, and IRInst.rec with one minor per constructor in declaration order, each ONE application of its ir_stk_arm_ lemma. The premise is consumed in exactly two leaves: the empty frame list here and the empty caller list in ir_ret_to_stack. {D}",
))
TERMS += [
    ("SRC_MEXT_JUMP", "ir_mext_jump", x_jump,
     f"ir_mext_jump: br, and the shared target of condbr and switch, across a module EXTENSION. ir_cur_func at a cons-headed machine IS ir_func_find at the head frame's function id, so this is the equation convoy on that lookup in M0: a miss halts the M0 step with stuck no_func and is refuted from the running premise by ir_bool_false_ne_true; a hit `some gf` is carried to M by hf and the M-side lookup is rewritten to it by one Eq.subst along Eq.symm, after which ir_jump_func is the same term on both sides (it never reads the module) and Eq.refl closes. Always the convoy form: the direct form has no equation to hand to hf. {D}"),
    ("SRC_MEXT_CONDBR_B", "ir_mext_condbr_b", x_condbr_b,
     f"ir_mext_condbr_b: Bool.rec on the decided condition with a premise-passing motive, minor order (false, true) -- each edge is ir_mext_jump at its own target and arguments, fed the running premise at that edge (the hypothesis reduces by iota to the edge's own). {D}"),
    ("SRC_MEXT_CONDBR_EXEC", "ir_mext_condbr_exec", x_condbr_exec,
     f"ir_mext_condbr_exec: IRScalar.rec on the condition operand with a premise-passing motive -- bool_ routes to ir_mext_condbr_b, the other eleven halt identically with not_bool on both modules because ir_as_bool is none on them by iota (Eq.refl, premise unused). Minor arity is fields-then-IHs, then the premise. {D}"),
    ("SRC_MEXT_SWITCH_N", "ir_mext_switch_n", x_switch_n,
     f"ir_mext_switch_n: IROption.rec on the NEUTRAL scrutinee `ir_case_find cases n` with a premise-passing motive whose body is ir_switch_n's own at each module -- the case table is on the instruction, not the module, so the scrutinee is the same term on both sides; default and matched arms are both ir_mext_jump fed the premise at that arm. Spelled per --form. {D}"),
    ("SRC_MEXT_SWITCH_EXEC", "ir_mext_switch_exec", x_switch_exec,
     f"ir_mext_switch_exec: IRScalar.rec on the selector with a premise-passing motive -- int_ routes to ir_mext_switch_n at the decided integer, the other eleven halt identically with not_int on both modules (Eq.refl, premise unused). {D}"),
    ("SRC_MEXT_CALL_EXEC", "ir_mext_call_exec", x_call_exec,
     f"ir_mext_call_exec: THE CALL ACROSS AN EXTENSION. The equation convoy on `ir_func_find fs0 fid`: a callee absent from M0 is stuck no_func there and is refuted from the running premise; a callee present in M0 is present in M by hf, the M-side lookup is rewritten to it, and ir_push is the same term on both sides (it reads the callee, not the module). This is the lemma that lets a closure be registered incrementally: a step that already resolved its callee in the smaller module resolves it identically in every extension. {D}"),
    ("SRC_MEXT_CALLIND_EXEC", "ir_mext_callind_exec", x_callind_exec,
     f"ir_mext_callind_exec: IRScalar.rec on the callee value with a premise-passing motive -- fnptr_ routes to ir_mext_call_exec at the function id, nullptr_ halts identically with null_deref, the other ten with not_fnptr (Eq.refl, premise unused). {D}"),
    ("SRC_MEXT_GLOBALADDR", "ir_mext_globaladdr", x_globaladdr,
     f"ir_mext_globaladdr: the one arm that reads the globals. ir_globaladdr_eval is IROption.rec on `ir_global_find (ir_mod_globals m) g`, so this is the equation convoy on that lookup in M0 under ir_bind_result: a global absent from M0 faults with type_error no_global, which ir_bind_result turns into a halt, refuted from the running premise; a global present in M0 is present in M by hg and both sides bind `ptr_ g`. Always the convoy form. {D}"),
]
TERMS += [
    (f"SRC_MEXT_ARM_{ctor.upper()}", f"ir_mext_arm_{ctor}", mext_arm_builder(ctor, names, types, rhs), _mext_arm_desc(ctor, rhs))
    for ctor, names, types, rhs in ARMS
]
TERMS += [
    ("SRC_MEXT_STEP", "ir_mext_step", g_mext_step,
     f"ir_mext_step: *** ONE STEP IS MODULE-EXTENSION-INVARIANT WHILE IT STAYS RUNNING. *** For M0 = IRModule.mk fs0 gs0 and M = IRModule.mk fs gs with hf / hg (every function / global M0 resolves, M resolves identically), a step of any machine in M0 that stays running is the same configuration as the step in M. The SAME skeleton as ir_stk_step: IRMachine.rec, IRList.rec on the frames (the nil minor is Eq.refl here -- both modules are stuck no_frame on an empty stack), then the function fetch as the equation convoy hf closes (a fetch that misses in M0 is refuted from the premise), the block and node fetches on their neutral majors (same terms on both sides once the function is identified), IRNode.rec, and IRInst.rec with one minor per constructor, each ONE application of its ir_mext_arm_ lemma with exactly the premises that arm reads. {D}"),
    ("SRC_MEXT_STEPS", "ir_mext_steps", g_mext_steps,
     f"ir_mext_steps: n steps, running-to-running, same n in both modules -- Nat.rec on n generalised over the configuration, exactly the shape of the hand-authored ir_stk_steps (S3): the zero case is Eq.refl, the succ case is IRConfig.rec on the configuration whose running minor chains the induction hypothesis at the M0 step (Eq.trans) with ir_eq_cong of ir_steps over ir_mext_step at the running premise recovered by ir_stk_running_back, and whose halted minor is Eq.refl because a halted configuration stays halted in either module. ir_steps_add-free because the succ case is definitional. {D}"),
]

# ---- the ir_stkn family: classifier, pins, the node-keyed twin (appended LAST,
#      so every earlier registration keeps its position and its pinned digest)
TERMS += [
    ("SRC_FRAMES_IS_NIL", "ir_frames_is_nil", k_frames_is_nil,
     f"ir_frames_is_nil: Bool test for the EMPTY frame list, by IRList.rec. Written with the exact motive and cons minor the classifier's inner case uses, so that at a ret node the classifier premise IS `ir_frames_is_nil t = false` by iota -- the premise the node-keyed ret arm takes. It is also the explicit nonempty premise of every theorem over the classifier: the empty list is outside the commuting class (ir_step halts stuck no_frame there, the stacked machine would step `rest`). {D}"),
    ("SRC_INST_IS_RET", "ir_inst_is_ret", k_inst_is_ret,
     f"ir_inst_is_ret: Bool test for the `ret` constructor -- IRInst.rec with one minor per constructor read off the inductive declaration, true only at ret. Minted rather than typed so a new IRInst constructor re-mints it instead of leaving a hand-written classifier that silently ignores the new arm. {D}"),
    ("SRC_NODE_IS_RET", "ir_node_is_ret", k_node_is_ret,
     f"ir_node_is_ret: ir_inst_is_ret on a node's instruction, by IRNode.rec -- the classifier layer at ir_exec_node, so the node-keyed step's IRNode.rec carries the premise through by iota. {D}"),
    ("SRC_FETCH_N_RET", "ir_fetch_n_ret", k_fetch_n_ret,
     f"ir_fetch_n_ret: the classifier layer at the NODE fetch -- IROption.rec on the looked-up node, false on a miss (fetch_past_end is not a ret). It mirrors ir_step_n exactly, which is what lets one neutral-major recursor abstract the lookup in the premise and in the step at once. {D}"),
    ("SRC_FETCH_B_RET", "ir_fetch_b_ret", k_fetch_b_ret,
     f"ir_fetch_b_ret: the classifier layer at the BLOCK fetch -- mirrors ir_step_b: a missing block is not a ret, a found block defers to ir_fetch_n_ret at the frame's pc. {D}"),
    ("SRC_FETCH_F_RET", "ir_fetch_f_ret", k_fetch_f_ret,
     f"ir_fetch_f_ret: the classifier layer at the FUNCTION fetch -- mirrors ir_step_f: a missing function is not a ret, a found function defers to ir_fetch_b_ret at the frame's block. {D}"),
    ("SRC_STK_BOTRET", "ir_stk_botret", k_botret,
     f"ir_stk_botret: *** THE FETCHED-NODE CLASSIFIER. *** True exactly when the frame list is a SINGLE frame [f] and fetching f's function, block and pc in the module yields an IRInst.ret node -- a bottom ret, the one step whose standalone result (halt with IROutcome.ret) differs from its stacked result (pop into `rest`). False on the empty list, on two or more frames, and on a fetch that misses or yields any other node. It reads only the fetched node, never the step's OUTCOME: the 18 ir_bind_result arms make a fault outcome abstract, so an outcome-keyed test could not be decided (eval_ir_stack.rs, ir_stk_ret_step). {D}"),
]
TERMS += k_pins()
TERMS.append((
    "SRC_STKN_RET_TO", "ir_stkn_ret_to", d_stkn_ret_to,
    f"ir_stkn_ret_to: the node-keyed twin of ir_ret_to_stack -- the one writer that reads the tail, keyed on the tail being a CONS (`ir_frames_is_nil t = false`) instead of on the step staying running. IRList.rec on the caller list: the nil leaf is refuted from the premise (it reduces to Eq Bool Bool.true Bool.false), the cons leaf is Eq.refl because ir_ret_to pops into the caller and re-conses `rest` verbatim. {D}"),
)
TERMS += [
    (f"SRC_STKN_ARM_{ctor.upper()}", f"ir_stkn_arm_{ctor}", stkn_arm_builder(ctor, names, types, rhs),
     (f"ir_stkn_arm_{ctor}: the node-keyed twin of ir_stk_arm_{ctor} -- "
      + ("the ONE arm that takes a premise, `ir_frames_is_nil t = false`, which is what the classifier premise reduces to at a ret node; the resolved ids are transported through ir_resolve_stack and ir_stkn_ret_to consumes the premise. "
         if is_ret_rhs(rhs) else
         "the same proof term with NO premise at all: the running premise of the old arm was bound and never used, so dropping it changes nothing the kernel checks except the statement. ")
      + f"Checked by name when it registers. {D}"))
    for ctor, names, types, rhs in ARMS
]
TERMS += [
    ("SRC_STKN_STEP", "ir_stkn_step", g_stkn_step,
     f"ir_stkn_step: *** ONE STEP IS TAIL-INDEPENDENT ON THE COMMUTING CLASS -- WHATEVER ITS OUTCOME. *** For a machine whose frame list is nonempty and whose fetched node is not a bottom ret (ir_stk_botret false), stacking `rest` beneath commutes with the step, INCLUDING a step that halts with a fault: the stacked step halts with the same outcome, because ir_config_stack is the identity on a halted configuration. The running-keyed ir_stk_step cannot state that. Same skeleton as ir_stk_step: IRMachine.rec, IRList.rec on the frames (the nil leaf refuted from the nonempty premise), the three fetch recursors on their NEUTRAL majors with the classifier premise abstracted alongside the step, IRNode.rec, IRInst.rec with one minor per constructor -- each ir_stkn_arm_ lemma, the ret minor handing it the premise that has reduced to `ir_frames_is_nil t = false`. {D}"),
    ("SRC_STK_BOTRET_FALSE_OF_RUNNING", "ir_stk_botret_false_of_running", g_botret_false_of_running,
     f"ir_stk_botret_false_of_running: a machine whose step stays RUNNING is never a bottom ret -- so the old running premise implies the new classifier premise, and the running-keyed family is the special case. IRMachine.rec, IRList.rec on the frames, then on the tail: two or more frames is Eq.refl (the classifier is false there by computation); a single frame goes through the three fetch recursors and IRInst.rec, where every non-ret constructor is Eq.refl and the ret minor is refuted -- a single-frame ret halts with IROutcome.ret, so the running hypothesis reduces to Eq Bool Bool.false Bool.true. A fetch that misses is refuted the same way. {D}"),
]

# ==========================================================================
# THE mkv MODULE AXIS (crystal link 4, M0 work item W3, 2026-09-30) -- appended
# LAST, so every earlier registration keeps its position and its pinned digest.
# ==========================================================================
#
# A derived module is `IRModule.mkv fs gs es`: its loads read the DERIVED
# encodings table `es` through `ir_load_view`, so the mk family (whose load arm
# is Eq.refl because both `IRModule.mk` tables are empty by iota) says nothing
# about it. The mkv twin is the SAME skeleton over M0 := IRModule.mkv fs0 gs0 es0
# and M := IRModule.mkv fs gs es: every builder above runs unchanged under the
# swapped module spelling (`_module_variant`), and the ONE arm that reads the
# table, `load`, takes the encodings premise -- `henc`: the two tables answer every
# row lookup identically, a hit AND a miss; `hlen`: they have the same length, which
# is the view's fuel. One-directional inclusion (the function/global premises'
# shape) is NOT enough here: a lookup that MISSES in M0 is not a fault but the
# identity view, and a row M adds for that type would image the same word
# differently. `--self-test` holds the twin to the mk term: undoing the module
# re-spelling gives back the mk term byte for byte, for every term but the load
# arm and the two main terms, which differ by exactly the threaded premise.

MVBLOCK = ("(fs0 : IRList IRFunc) (gs0 : IRList IRGlobal) (es0 : IRList IREnc) "
           "(fs : IRList IRFunc) (gs : IRList IRGlobal) (es : IRList IREnc)")
MVARGS = "fs0 gs0 es0 fs gs es"
MV0 = "(IRModule.mkv fs0 gs0 es0)"
MV1 = "(IRModule.mkv fs gs es)"
ENC_TBL = "(es0 : IRList IREnc) (es : IRList IREnc)"
VIEW_FN = "IRTy -> IRScalar -> IRScalar"


@contextlib.contextmanager
def _module_variant(mkv: bool):
    g = globals()
    saved = {k: g[k] for k in ("M0", "M1", "MBLOCK", "MARGS", "_MKV")}
    if mkv:
        g.update(M0=MV0, M1=MV1, MBLOCK=MVBLOCK, MARGS=MVARGS, _MKV=True)
    try:
        yield
    finally:
        g.update(saved)


def to_mkv_name(name: str) -> str:
    return re.sub(r"\bir_mext_", "ir_mextv_", name)


def _mkv(fn):
    def build() -> str:
        with _module_variant(True):
            term = fn()
        return to_mkv_name(term)
    return build


def from_mkv(term: str) -> str:
    """The mk term an mkv twin re-spells (the inverse of `_mkv`, by text)."""
    t = re.sub(r"\bir_mextv_", "ir_mext_", term)
    for new, old in ((MVBLOCK, MBLOCK), (MV0, M0), (MV1, M1), (MVARGS, MARGS)):
        t = t.replace(new, old)
    return t


def _ir_opt_rec(param: str, res: str, none: str, some: str, major: str, motive: str | None = None) -> str:
    mot = motive or f"(fun (_ : IROption {param}) => {res})"
    return f"(IROption.rec {param} {mot} {none} {some} {major})"


def v_view_word() -> str:
    """ir_view_word respects a pointwise-equal payload view (one IREnc.rec)."""
    goal = lambda e: f"Eq IRScalar (ir_view_word r0 {e} v) (ir_view_word r1 {e} v)"
    cong = lambda img, args: (f"ir_eq_cong IRScalar IRScalar (fun (x : IRScalar) => {img} x {args} v) "
                              f"(r0 p v) (r1 p v) (h p v)")
    body = (f"IREnc.rec (fun (e0 : IREnc) => {goal('e0')}) "
            f"(fun (k : Nat) (no : Nat) (so : Nat) (p : IRTy) => {cong('ir_niche_image', 'no so')}) "
            f"(fun (k : Nat) (i : Nat) (c : Nat) (p : IRTy) => {cong('ir_wrap_image', 'i c')}) e")
    binders = (f"(r0 : {VIEW_FN}) (r1 : {VIEW_FN}) "
               f"(h : forall (p : IRTy) (v : IRScalar), Eq IRScalar (r0 p v) (r1 p v)) (e : IREnc) (v : IRScalar)")
    return defn("ir_enc_agree_view_word", binders, goal("e"), body)


def v_view_ty() -> str:
    """The view at every fuel agrees when the two tables find every row alike."""
    stmt = lambda n: (f"forall (t : IRTy) (v : IRScalar), "
                      f"Eq IRScalar (ir_view_ty es0 {n} t v) (ir_view_ty es {n} t v)")
    word = lambda tbl: f"(fun (e : IREnc) => ir_view_word (ir_view_ty {tbl} k) e v)"
    opt = lambda word_tbl, major: _ir_opt_rec("IREnc", "IRScalar", "v", word(word_tbl), major)
    mid = opt("es0", "(ir_enc_find es t)")
    cong1 = (f"ir_eq_cong (IROption IREnc) IRScalar (fun (o : IROption IREnc) => {opt('es0', 'o')}) "
             f"(ir_enc_find es0 t) (ir_enc_find es t) (henc t)")
    rec2 = _ir_opt_rec(
        "IREnc", "", "(Eq.refl IRScalar v)",
        f"(fun (e : IREnc) => ir_enc_agree_view_word (ir_view_ty es0 k) (ir_view_ty es k) ih e v)",
        "(ir_enc_find es t)",
        motive=f"(fun (o : IROption IREnc) => Eq IRScalar {opt('es0', 'o')} {opt('es', 'o')})")
    succ = (f"(fun (k : Nat) (ih : {stmt('k')}) => fun (t : IRTy) (v : IRScalar) => "
            f"Eq.trans IRScalar (ir_view_ty es0 (Nat.succ k) t v) {mid} (ir_view_ty es (Nat.succ k) t v) "
            f"({cong1}) ({rec2}))")
    body = (f"Nat.rec (fun (n0 : Nat) => {stmt('n0')}) "
            f"(fun (t : IRTy) (v : IRScalar) => Eq.refl IRScalar v) {succ} n")
    return defn("ir_enc_agree_view_ty", f"{ENC_TBL} {PREMISE['he']} (n : Nat)", stmt("n"), body)


def v_load_view() -> str:
    """THE view agreement the mkv load arm consumes: henc (rows found alike) and hlen (same fuel)."""
    res = lambda tbl: f"(fun (e : IREnc) => ir_view_result {tbl} e r)"
    opt = lambda tbl, major: _ir_opt_rec("IREnc", "IRStepResult", "r", res(tbl), major)
    mid = opt("es0", "(ir_enc_find es t)")
    cong1 = (f"ir_eq_cong (IROption IREnc) IRStepResult (fun (o : IROption IREnc) => {opt('es0', 'o')}) "
             f"(ir_enc_find es0 t) (ir_enc_find es t) (henc t)")
    a = "(ir_view_word (ir_view_ty es0 (ir_enc_len es0)) e v)"
    b = "(ir_view_word (ir_view_ty es0 (ir_enc_len es)) e v)"
    c = "(ir_view_word (ir_view_ty es (ir_enc_len es)) e v)"
    w1 = (f"ir_eq_cong Nat IRScalar (fun (n1 : Nat) => ir_view_word (ir_view_ty es0 n1) e v) "
          f"(ir_enc_len es0) (ir_enc_len es) hlen")
    w2 = (f"ir_enc_agree_view_word (ir_view_ty es0 (ir_enc_len es)) (ir_view_ty es (ir_enc_len es)) "
          f"(ir_enc_agree_view_ty es0 es henc (ir_enc_len es)) e v")
    word = f"Eq.trans IRScalar {a} {b} {c} ({w1}) ({w2})"
    result_e = (f"IRStepResult.rec (fun (r0 : IRStepResult) => "
                f"Eq IRStepResult (ir_view_result es0 e r0) (ir_view_result es e r0)) "
                f"(fun (v : IRScalar) => ir_eq_cong IRScalar IRStepResult (fun (x : IRScalar) => IRStepResult.value x) "
                f"{a} {c} ({word})) "
                f"(fun (o : IROutcome) => Eq.refl IRStepResult (IRStepResult.fault o)) r")
    rec2 = _ir_opt_rec(
        "IREnc", "", "(Eq.refl IRStepResult r)", f"(fun (e : IREnc) => {result_e})", "(ir_enc_find es t)",
        motive=f"(fun (o : IROption IREnc) => Eq IRStepResult {opt('es0', 'o')} {opt('es', 'o')})")
    body = (f"Eq.trans IRStepResult (ir_load_view es0 t r) {mid} (ir_load_view es t r) "
            f"({cong1}) ({rec2})")
    binders = f"{ENC_TBL} {PREMISE['he']} {PREMISE['hl']} (t : IRTy) (r : IRStepResult)"
    return defn("ir_enc_agree_load_view", binders, "Eq IRStepResult (ir_load_view es0 t r) (ir_load_view es t r)", body)


def v_mext_run() -> str:
    """ir_mext_run's mkv form: a run reaching a RUNNING configuration in M0 reaches it in M."""
    s0 = f"(ir_steps k {MV0} c)"
    s1 = f"(ir_steps k {MV1} c)"
    run2 = "(IRConfig.running s2)"
    back = (f"Eq.subst IRConfig (fun (c1 : IRConfig) => Eq Bool (ir_stk_running c1) Bool.true) {run2} {s0} "
            f"(Eq.symm IRConfig {s0} {run2} hrun) (Eq.refl Bool Bool.true)")
    body = (f"Eq.trans IRConfig {s1} {s0} {run2} "
            f"(Eq.symm IRConfig {s0} {s1} (ir_mextv_steps {MVARGS} hf hg henc hlen k c ({back}))) hrun")
    binders = (f"{MVBLOCK} {PREMISE['hf']} {PREMISE['hg']} {PREMISE['he']} {PREMISE['hl']} "
               f"(k : Nat) (c : IRConfig) (s2 : IRMachine) (hrun : Eq IRConfig {s0} {run2})")
    return defn("ir_mextv_run", binders, f"Eq IRConfig {s1} {run2}", body)


MKV_D = ("The mkv twin (M0 := IRModule.mkv fs0 gs0 es0, M := IRModule.mkv fs gs es) of the mk term, minted by "
         "running its builder under the swapped module spelling; --self-test undoes the re-spelling to the mk term. ")
TERMS += [
    ("SRC_ENC_AGREE_VIEW_WORD", "ir_enc_agree_view_word", v_view_word,
     f"ir_enc_agree_view_word: ir_view_word respects a pointwise-equal payload view -- one IREnc.rec, each minor ONE ir_eq_cong of the row's image (ir_niche_image / ir_wrap_image) over the hypothesis at the row's payload type. {D}"),
    ("SRC_ENC_AGREE_VIEW_TY", "ir_enc_agree_view_ty", v_view_ty,
     f"ir_enc_agree_view_ty: at EVERY fuel, the view over table es0 is the view over es when the two find every row alike (henc). Nat.rec on the fuel: zero is the identity on both sides; at succ, ir_eq_cong rewrites es0's lookup into es's, then IROption.rec on that lookup closes the none minor by Eq.refl and the some minor by ir_enc_agree_view_word at the induction hypothesis. {D}"),
    ("SRC_ENC_AGREE_LOAD_VIEW", "ir_enc_agree_load_view", v_load_view,
     f"ir_enc_agree_load_view: *** THE ENCODINGS PREMISE, CONSUMED. *** ir_load_view at es0 and at es agree on every type and result when the tables find every row alike (henc) and have the same length (hlen -- the payload view's fuel is the table's own length). The lookup is rewritten by ir_eq_cong along henc; on a row, IRStepResult.rec: a fault is unchanged, a value's image moves its fuel along hlen and then its payload view by ir_enc_agree_view_ty. {D}"),
]
TERMS += [
    (const.replace("SRC_MEXT_", "SRC_MEXTV_", 1), to_mkv_name(name), _mkv(fn),
     f"{to_mkv_name(name)}: {MKV_D}"
     + ("THE ONE ARM THAT READS THE TABLE: it takes henc and hlen and closes by ir_eq_cong of ir_bind_result over ir_enc_agree_load_view. "
        if name == "ir_mext_arm_load" else
        "It threads henc / hlen to the load arm. " if name in ("ir_mext_step", "ir_mext_steps") else "")
     + D)
    for const, name, fn, _ in list(TERMS) if name.startswith("ir_mext_")
]
TERMS.append((
    "SRC_MEXTV_RUN", "ir_mextv_run", v_mext_run,
    f"ir_mextv_run: *** THE MODULE AXIS FOR DERIVED (mkv) MODULES. *** A run reaching a running configuration in IRModule.mkv fs0 gs0 es0 reaches it in every IRModule.mkv fs gs es whose function/global lookups extend M0's on each hit (hf / hg) and whose encodings table finds every row as M0's does and has its length (henc / hlen). ir_mextv_steps under the running premise read off the conclusion -- ir_mext_run's term with the module re-spelled and the encodings premise threaded. {D}",
))

NAMES = [name for _, name, _, _ in TERMS]
CONSTS = [const for const, _, _, _ in TERMS]
N_ARMS = len(ARMS)
LAST_ARM = ARMS[-1][0]
# The terms that bind a machine of their own rather than expanding a helper's.
MAIN_TERMS = {"ir_stk_step", "ir_mext_step", "ir_mext_steps", "ir_stkn_step", "ir_stk_botret_false_of_running",
              "ir_mextv_step", "ir_mextv_steps"}


def minted() -> dict[str, str]:
    return {const: fn() for const, _, fn, _ in TERMS}


def by_name(name: str) -> str:
    for const, n, fn, _ in TERMS:
        if n == name or const == name:
            return fn()
    raise SystemExit(f"gen_stack_lemmas: no term named {name}")


# --------------------------------------------------------------------------
# The Rust file
# --------------------------------------------------------------------------


def rust_escape(s: str) -> str:
    return s.replace("\\", "\\\\").replace('"', '\\"')


HEADER = """\
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **`ir_stk` / `ir_mext` -- the MINTED half of the frame-stacking family and
//! its module-extension twin**: build-order steps 3-7 of `eval_ir_stack.rs`'s
//! module doc, and the lemma the design's risk 9 names as the binding one.
//!
//! GENERATED by `scripts/gen_stack_lemmas.py --emit`. DO NOT HAND-EDIT: every
//! constant, the registration order, [`STACK_MINTED_NAMES`], the tests and this
//! doc are re-derived by the script, and `python3 scripts/gen_stack_lemmas.py
//! --check` refuses the file byte-for-byte if any of them differ (the script's
//! `--self-test` demonstrates the refusal on three hand edits). The definitions
//! the terms rest on (`ir_frames_app`, `ir_mach_stack`, `ir_config_stack`,
//! `ir_stk_running`), their `Eq.refl` pins, the measurement `ir_step_cons_fetch`
//! and the hand-authored theorems S2/S4 live in `eval_ir_stack.rs`; this stage
//! MUST register after it (and after `add_eval_ir_lzd_fresh`, for
//! `ir_bool_false_ne_true`).
//!
//! What is here, in registration order, with S0 the standalone machine
//! `IRMachine.mk (IRList.cons IRFrame f t) mem na`, S1 the same machine with
//! `rest` appended beneath (`ir_frames_app t rest`), and M0 / M the modules
//! `IRModule.mk fs0 gs0` / `IRModule.mk fs gs`:
//!
//! - **C. head-only reads** -- `ir_getd_stack`, `ir_mach_mem_stack` (pins) and
//!   `ir_resolve_stack` (induction on the id list).
//! - **D. writers** -- every frame-list writer on the step path re-conses the
//!   tail verbatim, so `Eq IRConfig (W S1 ..) (ir_config_stack (W S0 ..) rest)`
//!   is `Eq.refl`; `ir_ret_to_stack` is the ONE writer that eliminates on the
//!   tail and consumes the running premise at the empty caller list.
//! - **E. branching helpers** -- one lemma per machine helper that eliminates
//!   on a scrutinee, each a recursor on that scrutinee with a goal-abstracting
//!   motive; the NEUTRAL scrutinees (`ir_case_find`, `ir_func_find`,
//!   `ir_as_int (ir_frame_get f i)`, the three fetch lookups) are spelled per
//!   the script's `--form` (direct, the `ir_load_view_agg` precedent, by
//!   default; the equation convoy on request).
//! - **F. per-constructor arm lemmas** `ir_stk_arm_<ctor>`, one per `IRInst`
//!   constructor in declaration order, each ONE application of a D/E lemma at
//!   the arm's operands. Separate declarations on purpose: the defeq
//!   `ir_exec m (IRInst.<ctor> ..) rs S == <helper> S ..` is checked when THAT
//!   lemma registers and fails by name.
//! - **G. `ir_stk_step`** (S1 of the design) -- pure plumbing over the arms.
//! - **E'. module-reading helpers** `ir_mext_jump` .. `ir_mext_globaladdr` --
//!   the step in M0 equals the step in M under a RUNNING premise on the M0 side
//!   and the EXTENSION premises `hf` / `hg`: whatever `ir_func_find` /
//!   `ir_global_find` answers with `some` in M0, it answers identically in M. A
//!   lookup that misses in M0 halts the M0 step and is refuted from the running
//!   premise; a lookup that hits is transported by the premise. Those lookups
//!   are ALWAYS the equation convoy (the `some` minor needs the equation as a
//!   term); everything else follows `--form`.
//! - **F'. per-constructor arm lemmas** `ir_mext_arm_<ctor>` with the premise SET
//!   read off the arm's module reads: module-independent arms are `Eq.refl`
//!   with no premise; `load` reads `ir_mod_encs`, the empty table on both
//!   `IRModule.mk` sides, and is `Eq.refl` with no premise; `br` / `condbr` /
//!   `switch` / `call` / `callindirect` take `hf`; `globaladdr` takes `hg`.
//!   Modules of the `mkv` form are out of the statement.
//!   An explicit `unmodelled` arm proves only equality of refusals, never
//!   successful execution or atomic semantics.
//! - **G'. `ir_mext_step`**, the same skeleton, and **`ir_mext_steps`** by
//!   `Nat.rec` exactly as the hand-authored `ir_stk_steps` (S3).
//! - **H. the FETCHED-NODE classifier** `ir_stk_botret` (true exactly at a
//!   single frame whose fetch is a `ret`; false on the empty list, which is
//!   excluded separately by `ir_frames_is_nil`), its Bool layers and vacuity
//!   pins; then the **node-keyed twin** of the ir_stk family: `ir_stkn_ret_to`,
//!   `ir_stkn_arm_<ctor>` (premise-free except `ret`, which takes `t` not nil)
//!   and `ir_stkn_step`, whose premises are the nonempty frame list and the
//!   classifier being false -- never the step's outcome, so a step that FAULTS
//!   commutes with stacking too. Last, `ir_stk_botret_false_of_running`: the old
//!   running premise implies the new one. Appended after `ir_mext_steps` so
//!   every earlier registration keeps its position and pinned digest.
//!
//! Constructor tables were READ from `eval_ir_syntax.rs` / `eval_ir_state.rs`
//! and the arm chains from `ir_exec`'s own match in `eval_ir_machine.rs`; no
//! arity is typed anywhere. Every term is ASCII, names only Eq/Nat/Bool and
//! `IR*`/`ir_*` (both elaboration environments carry them), and every
//! congruence into an App type goes through `ir_eq_cong`, never `Eq.cong`.
//!
//! Wiring, none of it in this file: `mod eval_ir_stack_minted;` and
//! `pub use eval_ir_stack_minted::STACK_MINTED_NAMES;` in `mod.rs`, and a
//! `Specification::add_eval_ir_stack_minted` entry immediately after
//! `add_eval_ir_stack` in BOTH stage lists of `bundles.rs`.

use crate::spec::error::SpecError;
use crate::spec::Specification;

"""


def render_rust(terms: dict[str, str]) -> str:
    out = [HEADER]
    for const in CONSTS:
        out.append(f'const {const}: &str = "{rust_escape(terms[const])}";\n')
    out.append("\n")
    out.append(
        "/// Every declaration this stage registers, in registration order. `pub`\n"
        "/// so the census test can hold its copy against THIS list rather than a\n"
        "/// name prefix, and so `scripts/gen_stack_lemmas.py --check` has one\n"
        "/// authority for the order.\n"
        "pub const STACK_MINTED_NAMES: &[&str] = &[\n"
    )
    for name in NAMES:
        out.append(f'    "{name}",\n')
    out.append("];\n\n")
    out.append("/// `(source, description)`, positionally paired with [`STACK_MINTED_NAMES`].\n")
    out.append("const DECLS: &[(&str, &str)] = &[\n")
    for const, _, _, desc in TERMS:
        assert '"' not in desc and "\\" not in desc, desc
        assert len(desc) > 100, f"description too short to be rustfmt-stable on one row: {desc}"
        out.append(f'    ({const}, "{desc}"),\n')
    out.append("];\n\n")
    out.append(
        "impl Specification {\n"
        "    /// Register the minted half of the frame-stacking family and its\n"
        "    /// module-extension twin. MUST follow `add_eval_ir_stack` (definitions,\n"
        "    /// pins, `ir_stk_running_back`) and `add_eval_ir_lzd_fresh`\n"
        "    /// (`ir_bool_false_ne_true`).\n"
        "    ///\n"
        "    /// # Errors\n"
        "    /// Returns `SpecError` if any declaration fails to elaborate or\n"
        "    /// kernel-check -- by name, one declaration per arm.\n"
        "    pub(super) fn add_eval_ir_stack_minted(&mut self) -> Result<(), SpecError> {\n"
        "        for (source, description) in DECLS {\n"
        "            self.add_recursive_def(source, description)?;\n"
        "        }\n"
        "        Ok(())\n"
        "    }\n"
        "}\n"
        "\n"
        "#[cfg(test)]\n"
        "mod tests {\n"
        "    use super::*;\n"
        "\n"
        "    /// The sources stay ASCII and balanced -- the same cheap structural check\n"
        "    /// the sibling stages run.\n"
        "    #[test]\n"
        "    fn test_sources_balanced_ascii() {\n"
        "        for src in all_sources() {\n"
        '            assert!(src.is_ascii(), "spec sources stay ASCII");\n'
        "            assert_eq!(\n"
        "                src.matches('(').count(),\n"
        "                src.matches(')').count(),\n"
        '                "unbalanced parens in: {}",\n'
        "                &src[..60.min(src.len())]\n"
        "            );\n"
        "        }\n"
        "    }\n"
        "\n"
        "    /// Each source declares the name the list claims it declares, and the\n"
        "    /// two lists stay the same length.\n"
        "    #[test]\n"
        "    fn test_every_source_declares_its_listed_name() {\n"
        "        assert_eq!(all_sources().len(), STACK_MINTED_NAMES.len());\n"
        "        for (src, name) in all_sources().iter().zip(STACK_MINTED_NAMES) {\n"
        "            assert!(\n"
        '                src.starts_with(&format!("def {name} ")),\n'
        '                "{name} is not what {} declares",\n'
        "                &src[..40.min(src.len())]\n"
        "            );\n"
        "        }\n"
        "    }\n"
        "\n"
        "    /// One arm lemma per `IRInst` constructor in EACH family, each main\n"
        "    /// term after its arms, and the fuel induction last. The count is the\n"
        "    /// one the generator read off the inductive declaration, not a number\n"
        "    /// typed here.\n"
        "    #[test]\n"
        "    fn test_one_arm_lemma_per_irinst_constructor_per_family() {\n"
        f'        assert_eq!(count_prefixed("ir_stk_arm_"), {N_ARMS});\n'
        f'        assert_eq!(count_prefixed("ir_mext_arm_"), {N_ARMS});\n'
        f'        assert_eq!(count_prefixed("ir_stkn_arm_"), {N_ARMS});\n'
        f'        assert_eq!(count_prefixed("ir_mextv_arm_"), {N_ARMS});\n'
        f'        let last_stk_arm = "ir_stk_arm_{LAST_ARM}";\n'
        f'        let last_mext_arm = "ir_mext_arm_{LAST_ARM}";\n'
        '        assert!(position_of("ir_stk_step") > position_of(last_stk_arm));\n'
        '        assert!(position_of("ir_mext_step") > position_of(last_mext_arm));\n'
        '        assert!(position_of("ir_mext_step") > position_of("ir_stk_step"));\n'
        f'        let last_stkn_arm = "ir_stkn_arm_{LAST_ARM}";\n'
        '        assert!(position_of("ir_stkn_step") > position_of(last_stkn_arm));\n'
        '        assert!(position_of("ir_stkn_arm_ret") > position_of("ir_stkn_ret_to"));\n'
        '        assert!(position_of("ir_stkn_ret_to") > position_of("ir_stk_botret"));\n'
        '        assert!(position_of("ir_stk_botret") > position_of("ir_mext_steps"));\n'
        f'        let last_mextv_arm = "ir_mextv_arm_{LAST_ARM}";\n'
        '        assert!(position_of("ir_mextv_step") > position_of(last_mextv_arm));\n'
        '        assert!(position_of("ir_mextv_arm_load") > position_of("ir_enc_agree_load_view"));\n'
        '        assert!(\n'
        '            position_of("ir_enc_agree_view_word") > position_of("ir_stk_botret_false_of_running")\n'
        '        );\n'
        '        assert_eq!(STACK_MINTED_NAMES.last(), Some(&"ir_mextv_run"));\n'
        "    }\n"
        "\n"
        "    fn count_prefixed(prefix: &str) -> usize {\n"
        "        STACK_MINTED_NAMES\n"
        "            .iter()\n"
        "            .filter(|n| n.starts_with(prefix))\n"
        "            .count()\n"
        "    }\n"
        "\n"
        "    fn position_of(name: &str) -> usize {\n"
        "        STACK_MINTED_NAMES\n"
        "            .iter()\n"
        "            .position(|n| *n == name)\n"
        '            .expect("every name this test asks for is listed")\n'
        "    }\n"
        "\n"
        "    /// The stage's own table, projected. Nothing is re-listed here: a source\n"
        "    /// that is not registered cannot be tested, and a registration that is not\n"
        "    /// listed cannot exist.\n"
        "    fn all_sources() -> Vec<&'static str> {\n"
        "        DECLS.iter().map(|(src, _doc)| *src).collect()\n"
        "    }\n"
        "}\n"
    )
    return "".join(out)


# --------------------------------------------------------------------------
# Checks
# --------------------------------------------------------------------------

# sha256 of every term as emitted (in the default --form direct). See the
# module doc for what these pins are (and are not) evidence of.
PINNED_DIGESTS: dict = {
    "SRC_ADVANCE_SET_MEM_STACK": "594f96f42fac87ad7a1abfb1626687b9f3f9b5a6f415e26730f0db3bd74aa0a2",
    "SRC_ADVANCE_STACK": "8fe86ef541c9abebacb5f76fa4a8fcd444dc3eea9a34960ab27de15d14bfd30e",
    "SRC_ALLOCA_EXEC_STACK": "6f3219b7d3eee252591f2d9ba2f557340e993e2a2f0ab31589ee5c214eeb71b6",
    "SRC_ALLOCA_K_STACK": "2f1b30dd797a4acc9fc3fd7aedffa192cff26ea9f554e4e6c9c4abfa525fee50",
    "SRC_ASSERT_B_STACK": "0111f708b964fc512a23e0d460883641467d72656576ea835db38e92b50cc54e",
    "SRC_ASSERT_EXEC_STACK": "d91d880a6224f1c5e41eb292debcf471d25c0312bf2f3153ddf6860e64a7f9fb",
    "SRC_BIND2_STACK": "b6aef4e11feb8658b2bded7794d7243e3f6e13727c4440a64847d78ebdb8f058",
    "SRC_BIND_RESULT_STACK": "15c8b58ad35054c0a9edb79147997300894a0cd8a97bccae11c9f22f680d5d62",
    "SRC_BIND_STACK": "bea5865245fe92c45c948c85de8209ad3d485910ccdf3aa6dd1cd4490b63c7ad",
    "SRC_CALLIND_EXEC_STACK": "c98fbdce6f5b75478334b8c4ef78674bd5375184d7212a0cc2ae322344c9b951",
    "SRC_CALL_EXEC_STACK": "ae038cc02c2478616973d13205e9c1e8a8f7768b7fddda1e0222e6540ed961fa",
    "SRC_CONDBR_B_STACK": "2d380eb72fcc528d2a1b61a83fd2cf8d023841fa7e98540547d9911647fc519a",
    "SRC_CONDBR_EXEC_STACK": "1c1eb1b295768c5cdb8bea0dac053519cd86b420515e43a06b2f2aa94c0d9b6f",
    "SRC_ENC_AGREE_LOAD_VIEW": "88ff661bdc29d43ce4b4732ca0a2b492d20cb44df4e4a62bcace66a91bdd8380",
    "SRC_ENC_AGREE_VIEW_TY": "35807a6897804e51445fbd06d7a7c7a956f59f731c25992d552b042602327682",
    "SRC_ENC_AGREE_VIEW_WORD": "c26111c8ade5cb97206adf44c6632daef73ffb342a9262532f818e28eaf5b188",
    "SRC_FETCH_B_RET": "88173a5c25bdd0356d8009224916e526c185fe334142233b006724b77870a4c1",
    "SRC_FETCH_F_RET": "04ac79cfdacf8ff2c6d65f90210832377b1f94cd881ea5d22344af093c1b9891",
    "SRC_FETCH_N_RET": "c089b460a1ed8fcc3aae9340cfcd482e1d68c830ac1d6294fe635ea5d9492af6",
    "SRC_FRAMES_IS_NIL": "c92ea5adcd7d846dbd4dd17bebb9669571a79c2b14bc3381882d4167d356ef4a",
    "SRC_FRAMES_IS_NIL_CONS": "5306f187512309acae5f4267028aef33f675768c5196491ad3fa047994ada165",
    "SRC_FRAMES_IS_NIL_NIL": "fa7464d12e1c5da0f03ae6fe1e873a2797fb66675ecedc6b409a52ce1df5a9e5",
    "SRC_GETD_STACK": "5704fffc5cc309c82de5b290b40430e370600070f61c2a9d7f914111d9b114c0",
    "SRC_GOTO_STACK": "6f699cd2d89bfdaefcb076a049124c143a6d3587703c778bc7c60478ee872af5",
    "SRC_INST_IS_RET": "2597b0ecae3ed09715c30e89f4477a7c46eb8e8b68b005009e4fba2d7fe015d2",
    "SRC_INST_IS_RET_CALL": "5f1c838493b70b77d2d86d18cd6fb7cbc8fd6248ca9e9d90ba3532f840d87f59",
    "SRC_INST_IS_RET_RET": "043d0256de933709e597bf9e45e8b4f451fc8141306b8365bf93b59b659f4fcd",
    "SRC_JUMP_BLOCK_STACK": "c5601b06a57eb205a7f2533cb0d732533cf57fe04a1f17ca4ffc15487b7e8997",
    "SRC_JUMP_FUNC_STACK": "3f3c0a686dc817e1a81675d3a3d135aa1cac5eb7860e1ff28e75d504a72cd172",
    "SRC_JUMP_STACK": "94b28113d07e9f660aaaba9836056b361d324084f0e4ed72edac2fe6731f8ad4",
    "SRC_MACH_MEM_STACK": "1119e707652101b4dac9aa32775c8d419eef9e07868ab7832ba36577c7097b8a",
    "SRC_MEXTV_ARM_ALLOCA": "6a498918ad2d6eddb6452c87311e61e5d501b0988bc4099063bdd9b6be5f48ac",
    "SRC_MEXTV_ARM_ASSERT": "3b59e63d051ae942c365b745c37255348ce6d28ada6f30a14b7425915da9c80b",
    "SRC_MEXTV_ARM_ATOMIC_FETCH_ADD_RELAXED_U64_SEQ": "f95326670f9971c44a66124a12a3f1bb5d44d336d3f0176a6560124fbeb8bfec",
    "SRC_MEXTV_ARM_ATOMIC_FETCH_ADD_RELAXED_USIZE_SEQ": "c4719835b84814819e439d35244c833b12ab063a0c3a1d9e0eb67636c451e1a8",
    "SRC_MEXTV_ARM_BINOP": "6d8af8dee028f20b409e28edfb9f8a9177b07580cdcee56e61f27348135dfe57",
    "SRC_MEXTV_ARM_BORROW": "f888a674fd354e0c36bd2da9bb3693c52954667bf10fc91149699d023dc48b1a",
    "SRC_MEXTV_ARM_BR": "ea11cd04a5f6c99d5a104182f97f75e5214369d8a9eab00ce0609e169d9156bd",
    "SRC_MEXTV_ARM_CALL": "4fd55c16dfaad0eaa8721a63974f3d0cbc46883173ad31612ec0771207e78671",
    "SRC_MEXTV_ARM_CALLINDIRECT": "84c2917c407e6a094f96b4d1850dee39cc60d9e1bd0139f9db6ad35bfc3f7aa6",
    "SRC_MEXTV_ARM_CAST": "4b52bedcae75962bd1b05938ce1a42dbc56fd608d03add06bb34eae24b9f416d",
    "SRC_MEXTV_ARM_CONDBR": "8dd252c3e323a41674beb1dc25f389cccd586073d01b922afd5cd12f9febadd3",
    "SRC_MEXTV_ARM_CONST_": "6f965d042bed8da17cf17005711059346a74d7fb18fb2e739e464b726468e7f8",
    "SRC_MEXTV_ARM_COPY": "21b2286ded0212643225a94d7a715cabb893286550e8b3c84c0bc999cbb3f988",
    "SRC_MEXTV_ARM_EXTRACTELEMENT": "ab51ae0aa0c0dc72733ad663dcf781e8aabc884db9b600eedb17ecfab3b82d75",
    "SRC_MEXTV_ARM_EXTRACTFIELD": "ecc981de686868bf7ab0c039416ed2f627f985f4d9769d7fc3f5fcfd162b6304",
    "SRC_MEXTV_ARM_FCMP": "f060b8eec0b984b4a9bdeac6e05b2219c536fefffa1f1cc5fc100406f184ef9c",
    "SRC_MEXTV_ARM_GEP": "288690ec69c8bd49f559840cd4181c75059e024cf009ec0f12ef1fcc24a9dab7",
    "SRC_MEXTV_ARM_GLOBALADDR": "675ccd7ccb0eaf73d8fa04b0630ed374dd86a717d89f0a90cb4df1f9fbd4fca8",
    "SRC_MEXTV_ARM_ICMP": "0f26b19ee61d5322424c79e6f550f029cc0e54b1b3fe19b7281fafd2f92d7ee0",
    "SRC_MEXTV_ARM_INSERTFIELD": "2061ff6b1dae6e3f7ac34d3dd4ffe1a2ec62e8b6487fc92b81db3be0b4aa14b4",
    "SRC_MEXTV_ARM_LOAD": "532243788780e690543fe1f9c4e18ad4ea24d3ddc21f7718892efd6c0338e730",
    "SRC_MEXTV_ARM_OVERFLOW": "755c10e7c52804a99115123a4a5ca0e45775c9c93f04f4561c9db338c5aa9d27",
    "SRC_MEXTV_ARM_PTRDATA": "0a5653da8c2c87eb914eceb77beae1bcc8a60d3915e280cdc6a585463085ad3d",
    "SRC_MEXTV_ARM_PTRFROMPARTS": "7ca1ac230badaa1fb4aaac49bca97ed2c53808c18cb4538643abc1ce6fd9c6dc",
    "SRC_MEXTV_ARM_PTRMETADATA": "e0a7dc2dd47a78656484f727fabe0c46b010970b2457ab7535198ea056117033",
    "SRC_MEXTV_ARM_RELEASE": "428e6b35a0501b49a8db65ff3e7b7c3940944839d88d66ae6f09245950068e3b",
    "SRC_MEXTV_ARM_RET": "26cd402b196460addca8d089c63f1eeb6ef96f5013f1ea4e0d90f6e2ac6db810",
    "SRC_MEXTV_ARM_SELECT": "081b64af8dd77eb71803c368077daf049fe466b5f33c7ea6284419e17588003f",
    "SRC_MEXTV_ARM_STORE": "424131221b0c0a216077247652b8fc448ddde4fe1dcbbe05acd2d8b825ede87f",
    "SRC_MEXTV_ARM_SWITCH": "d4679eeec91d471590bcd3b2d68bdb060f0ab33358916d34e98c765d41bd7c4c",
    "SRC_MEXTV_ARM_UNDEF": "17fec3783fb68d1e548bc994f07b058fcf5055a561a75e4827ac66ac4d3e4204",
    "SRC_MEXTV_ARM_UNOP": "a9c5430a2b2bf2767b147f303e21e0ba9a90e676a6b4920b46990d55afe32ca2",
    "SRC_MEXTV_ARM_UNREACHABLE": "d75bf57fd618f3cae7b814ebdb1144e4d188b6f78cb4edf4f2eef4ee7ae43612",
    "SRC_MEXTV_CALLIND_EXEC": "2d07bc5a30e382e9cb8109062cac63ada5f8f72c6bceed95d61dcaeeb2611da8",
    "SRC_MEXTV_CALL_EXEC": "91847fa8982f7724a37ca0972a2452689e3bd3b3943c4c1e25dc2b1b05d28ba4",
    "SRC_MEXTV_CONDBR_B": "38f69b33777b529418bccc92a97d92e139d87b9eac8f6d323ea496deaae6ba63",
    "SRC_MEXTV_CONDBR_EXEC": "c9d3a32f9ef0dc78c0d7b24d01f24a14fa9a9ce5e664d47335d579273338c792",
    "SRC_MEXTV_GLOBALADDR": "220c8211ee6354e642396d0421939d5ec9ae5de37bdf436a5c7feeb9fde2e179",
    "SRC_MEXTV_JUMP": "4e51e9e89fda230362007f21a94195ecbe868e569d031a4bd5ef548368dbd222",
    "SRC_MEXTV_RUN": "b208a09b6c42ccefefabb74799d01f4a4b6e5d7e4c87141b3d8dead4a59f76e8",
    "SRC_MEXTV_STEP": "c9100ab3bfac484f23abec360ad301bee1a96b0fe9c7f6febff301c5f1c4452a",
    "SRC_MEXTV_STEPS": "e2777ddf1953381d4c93382a5bd5935e9daec27c6a0a2c3a6147f522c3489bec",
    "SRC_MEXTV_SWITCH_EXEC": "32d5cbb07877a1c6a79f98eeeb8477e3df3204a77fd8f5efe01939a0853c8663",
    "SRC_MEXTV_SWITCH_N": "620e42de47c7377365ae309c60913d59127c8e76a6ccf324ffe299d9821dad49",
    "SRC_MEXT_ARM_ALLOCA": "c5a2e9d1657712927e30c98b8fb35849fa982b7cf334ca66b3d541630ca4eba4",
    "SRC_MEXT_ARM_ASSERT": "f83ec5c0b30b028356c0b7f765777ada9e9ff4e72c784b321c72c522aec639bf",
    "SRC_MEXT_ARM_ATOMIC_FETCH_ADD_RELAXED_U64_SEQ": "3b45bdec85abdf491e16d9fb534881760bdaf4f15e662f9403eb863e129a8d7f",
    "SRC_MEXT_ARM_ATOMIC_FETCH_ADD_RELAXED_USIZE_SEQ": "828c8ae24345a26c6700d329d830d5ab4557a495518ffd7d9fe9cf7c3478ab64",
    "SRC_MEXT_ARM_BINOP": "5c58960468b7bea890558f8a8bee22a6088988788863588788dc47d7176a4df9",
    "SRC_MEXT_ARM_BORROW": "a29658b0a8428457922953b288d95613857ecf3605c26fba322cfaff14f6b6a4",
    "SRC_MEXT_ARM_BR": "600a3a551b9d8b3ee565d0562e05e2f3ef10db7d90c6830a8395d72bcf8d15e8",
    "SRC_MEXT_ARM_CALL": "f7850a4b2c25df4936cc2c7d836417e7fca836111330fb6250c7dd213c81313e",
    "SRC_MEXT_ARM_CALLINDIRECT": "8249146b1adc9f53eadc67a036c1c9a5b35e814f571e1ae3a0c32447f515eb48",
    "SRC_MEXT_ARM_CAST": "5a955caec34f2b66c8a63708615aa3a3b8f359a2ff5cb150221f8b147764186d",
    "SRC_MEXT_ARM_CONDBR": "8b06b405ebae120f92ac1d25c7d94e04d906c18d3816ec7a6e0316a9a4f4ed31",
    "SRC_MEXT_ARM_CONST_": "08776b3df1efefbe03a17b003285012466070871cbc4b37d6f5c9fc3a774e5eb",
    "SRC_MEXT_ARM_COPY": "3fbddc14c3a4730306f3e048683472440c2da68190aa2560f2de5ae2063df3f6",
    "SRC_MEXT_ARM_EXTRACTELEMENT": "6492d9882ccf93a21dccf3a69acd0851f8c4a5f5c9e17713cf00dd3b62cc998b",
    "SRC_MEXT_ARM_EXTRACTFIELD": "5ee139bec55e4cab704a2256fb6d8c065b1fac08bc38082a5951b0d19fe7098b",
    "SRC_MEXT_ARM_FCMP": "9241cc0086121590f349377bf30c28504f82c6544c0d442653624249e00e132a",
    "SRC_MEXT_ARM_GEP": "3021c32269b664a5fd4a28a103ff3f0a99a0aa4cfb993bf74ee60bfdffc64113",
    "SRC_MEXT_ARM_GLOBALADDR": "33936aca862759c58873a8481d763bf4a4621e83a67d494ad9c5b58854c44379",
    "SRC_MEXT_ARM_ICMP": "ccacd85019a441ba1d0e466586d73550f2a33a7d4adb0b5d32755b5aae9731c3",
    "SRC_MEXT_ARM_INSERTFIELD": "bd9504a04c77f30c10ac48b8ea02800c0bc655be88897b7fe7128ac4d24ea9af",
    "SRC_MEXT_ARM_LOAD": "d6f9a9e4ad40620e2c76bb73c2b7376a5015f2d7044f8941b98bf7bfe1c5cc7b",
    "SRC_MEXT_ARM_OVERFLOW": "b848e244e36ba450216da14544aadf63bd83192c20562d032d44523fde0fdcee",
    "SRC_MEXT_ARM_PTRDATA": "4405c6732df5da75e82eaac9cd3e93faad7c7fb72c45aab725e834ba77a6a6e5",
    "SRC_MEXT_ARM_PTRFROMPARTS": "607673215fb792cb69d2f7634cec1cdf23bdef82b9a5e80e875228aeb06d32ac",
    "SRC_MEXT_ARM_PTRMETADATA": "b52ffeb2f124e070fcd212b7161e02fc0f1f8516eab74b45e14350038fab90d6",
    "SRC_MEXT_ARM_RELEASE": "fec5559a280b1df79eb4932e4c3e9e22870f54c88760c32431f9a2975514aff7",
    "SRC_MEXT_ARM_RET": "93d0fa7ba945820209afdf53e81155ba0570316398064c1fe59c5b4d30f91302",
    "SRC_MEXT_ARM_SELECT": "d340f9fac023d6969ba61418ea066306fd26c00ebee0907611fa0ebd1f9770a7",
    "SRC_MEXT_ARM_STORE": "5245464bf87d751e5361f2c6ddc696862675f4ac3c4bcf0db0005cd96879231c",
    "SRC_MEXT_ARM_SWITCH": "4a3795fd4e1591ac17cddab2acd229f21ba67983ff4c42a60dc76b662ab4b17f",
    "SRC_MEXT_ARM_UNDEF": "182b8e35a46755159f3ad3718e97a3d34d66fd9214633fc4a6a2a58e91a31df4",
    "SRC_MEXT_ARM_UNOP": "c70777d00d1319eb01c55a93f2b54fcf64129c301bf68898af2d43359b334475",
    "SRC_MEXT_ARM_UNREACHABLE": "2080c7a4b5263a0fd6b17f89293df833c67a9350f559afdf8b6d99bc330492cd",
    "SRC_MEXT_CALLIND_EXEC": "2bf5bf240a7ff5f1cda2b75364a79acf59d658630c8361bd1be3f1aeed84d473",
    "SRC_MEXT_CALL_EXEC": "d753da455b9e6ae9300dfa853cd213508547cc37e03082007a1762f3c83548b8",
    "SRC_MEXT_CONDBR_B": "e6a72b1c57abe2ba59f6c3d7b74693753312eed6febebe257ca903f525279edd",
    "SRC_MEXT_CONDBR_EXEC": "0f6c361717361db0e5cf1609df81589c7f065d828cc0447bcb6c92f0923b30fc",
    "SRC_MEXT_GLOBALADDR": "f0f704868a6996e7ac866a4a94afe859b1f71401367e5781e0c7cf4a520a13b7",
    "SRC_MEXT_JUMP": "22023b879684aef4f25b1c93fc1d7ce918fd421ad0fb9d29f013d737f8f1411b",
    "SRC_MEXT_STEP": "df913d9e81c4c31dc722318915ed8cd089ad300c16e9af647a99d2188d40bf45",
    "SRC_MEXT_STEPS": "011cbf80f78c58c2860ff2d374594479d30452572d0326f62867b6ee2e657fa2",
    "SRC_MEXT_SWITCH_EXEC": "15123fdf945675fb1688766bdf2603862fe362b17847c40214cf55c2e9556015",
    "SRC_MEXT_SWITCH_N": "b4e2b3097ce9c7b3d0bd5957ca3577d641a6d13c7aa77cd722851f81c5e2f366",
    "SRC_NODE_IS_RET": "aa686a6daa74ad69f44d3d81230e34f266d38ff23313f7e7d23656852bbc8637",
    "SRC_OVERFLOW_EXEC_STACK": "8128611d51f03cdf79d5a45a86675f32e0dac014a2c5ca2e5aaa2fda3fedf5c2",
    "SRC_OVERFLOW_INTS_STACK": "ef364b2fc81f18d2712770db05b31741f200f87706655ac0d341620fb1a12813",
    "SRC_OVERFLOW_VALS_STACK": "b31c463d7527f8bc8ebe6dfa4dc706f2d731eeb91b9af4d140326ee08021fff4",
    "SRC_PUSH_STACK": "8cbcf2f0b15f5ea88a1167e63656c1b696559544d472b5cd565732ac6a9beb42",
    "SRC_RESOLVE_STACK": "8095a89bdea969b0ec8bec095269b28ec89d5da091ebc084222d6d1ac7363ac9",
    "SRC_RET_TO_STACK": "381b584ade8778160836661efe7c33e084288f715675524035596e61e0cf14b3",
    "SRC_STKN_ARM_ALLOCA": "d101e7d66d3a04456d2143698d0689073d00787a3f80edad92addd80b3586580",
    "SRC_STKN_ARM_ASSERT": "a9305414b4c626ec0ea59693ce38bf9e13a6a88f2db51a9d9b83e31f961d4340",
    "SRC_STKN_ARM_ATOMIC_FETCH_ADD_RELAXED_U64_SEQ": "ed8e7e5d327d57b1efeef81114ddaf6da0fed84d1db7b4fa41884577db3a241b",
    "SRC_STKN_ARM_ATOMIC_FETCH_ADD_RELAXED_USIZE_SEQ": "34b9d912f91f2f21adaf1d3a4731fbcb80327e184d41ef5d9698172684843a2e",
    "SRC_STKN_ARM_BINOP": "ed84fec54ba5f3fc5334bf3bed68b947f976b6eef0cee44af07486b73dc65ae8",
    "SRC_STKN_ARM_BORROW": "09e363a0b9ed9fb80dc07f2d2f988b5a16b0e3470299d515d02497966a117d02",
    "SRC_STKN_ARM_BR": "a485c858d259298ce687c970bf5c38fd6d51b01f501ae386ab10e2117e8c4466",
    "SRC_STKN_ARM_CALL": "7301300bc28ef8c6c9a345835f12b5fd591338a0299da2d0b2f2f739b4f785a0",
    "SRC_STKN_ARM_CALLINDIRECT": "631e6cdba0346467415d1c6d3d65ec7dc85d6a515d93b38c87dfecee2b579e27",
    "SRC_STKN_ARM_CAST": "35c2e96979f3899c77414be5f66726ec2c63fcc52dc3998670c0f02fb49fa6b2",
    "SRC_STKN_ARM_CONDBR": "5eeef8bb920dd307f1a0f42fdc3166e7cc0465f845735275595cd2d7cb148fbb",
    "SRC_STKN_ARM_CONST_": "d2fbf8ab2ea4eeea0db45789201f9cc120339a3a25004dd208126fc6c0654b89",
    "SRC_STKN_ARM_COPY": "baafd7fb6fd489d4f096078f6622e1c7a0ad1cf2aa0341f3f09c53a4f874c919",
    "SRC_STKN_ARM_EXTRACTELEMENT": "d5036dcb9da45e4d09d6bec22a0231512cf0335eee708494aba33d779d24690b",
    "SRC_STKN_ARM_EXTRACTFIELD": "49320e97a6ac00e574712b776cb52baff85a548cf21ef6b6634bc2794be72fb1",
    "SRC_STKN_ARM_FCMP": "fa6577445c3f98b6ab85c1650cb16fd9860c152b1aa05e5bf57c5c2a0ea41043",
    "SRC_STKN_ARM_GEP": "d34d33ff09459a33dfa0935524a20ed3a6d202ff4e1f0ad853608d3cdd850583",
    "SRC_STKN_ARM_GLOBALADDR": "f90e01df070332f16f2cae93695cccac0e30d1f22fbad456bb755fab9f2bb936",
    "SRC_STKN_ARM_ICMP": "03219efc4f279a3c983a6dd830b5eebc6002d75003c8a58a78bbfd9cede686ca",
    "SRC_STKN_ARM_INSERTFIELD": "1a9e125fb00e8492e278f328ae79e24c6bccf90bf075de533044959385c2c330",
    "SRC_STKN_ARM_LOAD": "c52e884d511e746f696c48f0a66048111cfa4a5585d22901ece8fd89db59d692",
    "SRC_STKN_ARM_OVERFLOW": "154f8a80b24495345417b90f7a5abafdd2e2f38a91e9bd9df39eee70c7c4c7a4",
    "SRC_STKN_ARM_PTRDATA": "88768d1e4e1b4388c1e0b14ece32c7156e5a6a56c76dfbe94dea720546513a91",
    "SRC_STKN_ARM_PTRFROMPARTS": "20fa1c27b051cc1db093f8e597bde91049cbae0d3dba41c956bb3ba6cef7b649",
    "SRC_STKN_ARM_PTRMETADATA": "5f5e25634ca8c38a1ea44b71be55f76d6597a140b7617c6049d62162aaaedb1c",
    "SRC_STKN_ARM_RELEASE": "f56848661457ccf06a648c9892aa087bfb019ad1ae0ae45162065e5c27292234",
    "SRC_STKN_ARM_RET": "09db9565b3a67036faa3c6d76c3142cb5a706e87db054ae3f5b27794a8920d06",
    "SRC_STKN_ARM_SELECT": "4983f4fdcb3fd514c7f35303d2a1a8049eb8dc3232b0bd328122e195a82bf18a",
    "SRC_STKN_ARM_STORE": "2d8cd5bc696096af13330c9c2d825fea3067cef7a613657885f7e6159c7db87e",
    "SRC_STKN_ARM_SWITCH": "d6ad717efa1f0ab7e770be304c7e0a3db3aaf0a3acb1cacd6151bae9ad4e051a",
    "SRC_STKN_ARM_UNDEF": "9036e328426f8c04ff7da5b2ee38286c2bf45bf03e5cf5e9ea7e9f10b0188692",
    "SRC_STKN_ARM_UNOP": "d5b32112d8e411fc02d96963807e67abdeac8a92407263fb5ed0afe124a9e309",
    "SRC_STKN_ARM_UNREACHABLE": "b661032fc223b127467f53c95d2359a548379a3694306ec4ca3f194e68e27a39",
    "SRC_STKN_RET_TO": "6db4a93a32d31f88e8fa5a34791f6f56c75a0cedc575062b778c09725ec93e02",
    "SRC_STKN_STEP": "524f2a37611daa86230d172216cbb8d9d55ef8b7a8939143d5872e859a776972",
    "SRC_STK_ARM_ALLOCA": "60835b0dad029e80ad790525247932caaab0f72e97917762fcf674990630248a",
    "SRC_STK_ARM_ASSERT": "2497c5764a0238ebc38d6dea8d71719aaf0eee92449814520d53970269229cb4",
    "SRC_STK_ARM_ATOMIC_FETCH_ADD_RELAXED_U64_SEQ": "55881eb16f92f1ad3968aaa5418f7ed7b1c98a9080f7c6aa99ac5f97b3ab1c6f",
    "SRC_STK_ARM_ATOMIC_FETCH_ADD_RELAXED_USIZE_SEQ": "b7bd9da25d7c44707532ab23062c6822de58a894ef533237b3e325cc3deb3d8d",
    "SRC_STK_ARM_BINOP": "397b0691189554e8fd5c4bca736e2cbf85e1b5257ff31a1af36008321eab310d",
    "SRC_STK_ARM_BORROW": "6f7faafab4c00ec9e29162787453bc4dfd948b1f96880d3c0323ae7c69f4a036",
    "SRC_STK_ARM_BR": "e9c88c35f302451520eadfd33e42f9c76543a0a33c1f5c861dbbc3dfecad2a76",
    "SRC_STK_ARM_CALL": "2bf6a3f409dd07e3fc2d4e61340aeea05ceb91eda46922b21321e0fe8a476ddb",
    "SRC_STK_ARM_CALLINDIRECT": "4dd712b32fb5a40daba105970aff7ae1def0f7ab39d54bdc96bb2e185d2a235d",
    "SRC_STK_ARM_CAST": "3ae5f85ed1e6be71655fc54803f8b0db1cd008ead00e42705eff306aed2d40ec",
    "SRC_STK_ARM_CONDBR": "cf07f425657eb11793803747b09bc6b3fd8221eb7d37aaa7e6a443aa9330a372",
    "SRC_STK_ARM_CONST_": "8cb3669f4ec85676aa6de1c0cfbdfa6041ddf2e6f9070f6dbda6284c86e76d8e",
    "SRC_STK_ARM_COPY": "96727c41b5a11387ea6de8f3d930954cd078f308892c168c508c8c1b1653d038",
    "SRC_STK_ARM_EXTRACTELEMENT": "4265b9312c9fa21fe8358f2da554a7b06ae4537c1ed470da7e96471d9007b22e",
    "SRC_STK_ARM_EXTRACTFIELD": "32282102737caa8ba0286221cb2216c3adb13563159632a50948df3066433462",
    "SRC_STK_ARM_FCMP": "93ef88c3fb9ee0abb5180a34b230baee1ff538db8430030a316b7c167774be91",
    "SRC_STK_ARM_GEP": "088e34b683a320b96d6c4b4f52985d4cc6cae730ca04dd17dd63c77266a4c5dc",
    "SRC_STK_ARM_GLOBALADDR": "d0d3ab94f30ff556313d6acfebe0b925b37665c27a6587b87e2ac82c0cf1ed75",
    "SRC_STK_ARM_ICMP": "30756831efdd1b8c53bce880a1781a5409f810d77e915f2b285263b2284a0484",
    "SRC_STK_ARM_INSERTFIELD": "2c084b6fb0e96e79e8a87e28b7315ce2f37ae11f4081b99f0a240c60d03a2f9f",
    "SRC_STK_ARM_LOAD": "3b598bef70fc364d8adaafdb42de091b6403dbc621c123d7a495c8fbbc9267a3",
    "SRC_STK_ARM_OVERFLOW": "b597a49eb954ec5451e245ae811e7622616d729bd19bd2bbf13e45c040451a97",
    "SRC_STK_ARM_PTRDATA": "9e872183d8fdf4ee5941afe1f59361474adb629ccf4504d8aef15fb3a1bc0724",
    "SRC_STK_ARM_PTRFROMPARTS": "2197f5c5e473c448e9046f5fd37e420256e29a16e06a62d5a9c3cf724b80de01",
    "SRC_STK_ARM_PTRMETADATA": "ddfb31f7aa6b5a9298ee641298a215960d7c6f4c69cb9026f4e5d2a7aeaf4ac7",
    "SRC_STK_ARM_RELEASE": "0a84816b8564c3ad7728f9e97b19766c6db0c296cae8f574de1756515950d090",
    "SRC_STK_ARM_RET": "71b66f8f575805ecc8528b045a2a9bac88602dc82c97a8f2d7bcc5b2aa7df758",
    "SRC_STK_ARM_SELECT": "5d921ebd0d2497889d471afc07256d7dd00ce5d9d004344afbb7cfd548e7d403",
    "SRC_STK_ARM_STORE": "e01c62b5edbac4fef6e633e4f340e883a0a285ace60491c8c2e67e620bca7012",
    "SRC_STK_ARM_SWITCH": "48d5d877d32720bdde8119c3f516f622556556a5f69f3521618f8dfd2b07e86a",
    "SRC_STK_ARM_UNDEF": "fd3c01d02d6fb87c95bc4c84712e04997d526bcbf2513c019561bb25e1b41f91",
    "SRC_STK_ARM_UNOP": "8e1cbedf42633990bd8df9f7ca38397e0e45b82f3d8295b93964152467355ccc",
    "SRC_STK_ARM_UNREACHABLE": "596a4615ed7b7e5b66b3e326f90c4676a75a3b81d0ba90dd96c9b6c5277a910d",
    "SRC_STK_BOTRET": "8a3535d972cd5cf0e6bf4085e18b78f16d47179358666eceb924edd051392092",
    "SRC_STK_BOTRET_FALSE_OF_RUNNING": "e5b2fa9046c0b759a70ecd41208d1094cd8d5329f05a0250a0bc6d20b76a4efd",
    "SRC_STK_BOTRET_NIL": "57f25ba2d508c87f21b867a38d2e01239636d9283d37de2e47eb51fd8bcbc1a2",
    "SRC_STK_BOTRET_TWO": "33e01ca62ac259a1fb1723b512073c32630b117281b6b41c287dadef3d213627",
    "SRC_STK_STEP": "5b1153165336bf880ab7350a5fc9b64a34fa3ea8215ce2fc52d526fad5ec5d6b",
    "SRC_STORE_CHECKED_STACK": "a571c586fcb96594fa024f1c3e08cfa9cf7a4d7c11c8ec51cdc765b67d27dc1b",
    "SRC_STORE_EXEC_STACK": "f2409e03f929590da9dff273676e50f9f574fe39ae107fd0b770f839baed32c9",
    "SRC_STORE_LIVE_STACK": "8c31c21e91f3c5832411443caa459d6a4c91ad43cd359b853734f3728d6e7aa2",
    "SRC_SWITCH_EXEC_STACK": "b4600edf24ebef7789865fbb4ef54a3a024d716e013998dc55b64dd6c495102b",
    "SRC_SWITCH_N_STACK": "5fa726f7ab7bf9c115efc1abd698c4fa8de3678aaeaa4288e8796082311e79f6",
}


def digests(terms: dict[str, str]) -> dict[str, str]:
    return {k: hashlib.sha256(v.encode()).hexdigest() for k, v in terms.items()}


def structural(terms: dict[str, str]) -> list[str]:
    """Refusals, or an empty list."""
    bad: list[str] = []
    n_inst = len(ctors("IRInst"))
    if len(EXEC_ARMS) != n_inst:
        bad.append(f"ir_exec has {len(EXEC_ARMS)} arms for {n_inst} IRInst constructors")
    if len(ARMS) != n_inst:
        bad.append(f"{len(ARMS)} arm lemmas for {n_inst} constructors")
    bad += body_checks()
    # Registered before this stage: every `def` the hand-authored eval_ir_stack.rs
    # declares (ir_frames_app, ir_mach_stack, ir_config_stack, ir_stk_running,
    # the pins, S2/S4). Read from that file so a rename there is noticed here.
    seen: set[str] = set(re.findall(r'"def (ir_\w+) ', STACK_RS.read_text()))
    if not {"ir_mach_stack", "ir_config_stack", "ir_stk_running", "ir_stk_running_back"} <= seen:
        bad.append(f"eval_ir_stack.rs no longer declares the definitions this stage rests on: {sorted(seen)}")
    prem_set = {ctor: mext_arm_prem(rhs) for ctor, _, _, rhs in ARMS}
    want_hf = {ctor for ctor, _, _, rhs in ARMS if top_tokens(rhs)[0] in
               {"ir_jump", "ir_condbr_exec", "ir_switch_exec", "ir_call_exec", "ir_callind_exec"}}
    if {c for c, p in prem_set.items() if p == "hf"} != want_hf:
        bad.append(f"the hf arms are not the five module-dispatching helpers: {sorted(c for c, p in prem_set.items() if p == 'hf')}")
    if {c for c, p in prem_set.items() if p == "hg"} != {"globaladdr"}:
        bad.append(f"the hg arms are not exactly globaladdr: {sorted(c for c, p in prem_set.items() if p == 'hg')}")
    for const, name, _, _ in TERMS:
        src = terms[const]
        if not src.isascii():
            bad.append(f"{name}: non-ASCII")
        if src.count("(") != src.count(")"):
            bad.append(f"{name}: unbalanced parens")
        if "{S}" in src or "{M}" in src or '"' in src or "\\" in src:
            bad.append(f"{name}: leftover placeholder or quote")
        if not src.startswith(f"def {name} "):
            bad.append(f"{name}: source declares something else: {src[:50]}")
        body = src.split(" := ", 1)[1]
        if name.startswith("ir_mext_") and uses("m", body):
            bad.append(f"{name}: a bare module variable survives in the body")
        if name.startswith("ir_mext_") and name not in MAIN_TERMS and uses("s", body):
            bad.append(f"{name}: a bare machine variable survives in the body")
        for ref in set(re.findall(r"\b(ir_\w+_stack|ir_stk_arm_\w+|ir_stk_step|ir_mext_\w+|ir_mextv_\w+|ir_enc_agree_\w+|ir_stkn_\w+|ir_stk_botret\w*"
                                  r"|ir_frames_is_nil|ir_inst_is_ret|ir_node_is_ret|ir_fetch_[fbn]_ret)\b", body)):
            if ref not in seen:
                bad.append(f"{name}: references {ref}, which is not registered earlier")
        seen.add(name)
    # The mkv twin (crystal link 4 M0 W3) re-spells the mk term: undoing the module
    # re-spelling gives back the mk term byte for byte, except where the encodings
    # premise is THREADED (the load arm, the two main terms), which is checked by name.
    threaded = {"ir_mext_arm_load", "ir_mext_step", "ir_mext_steps"}
    for name in [n for n in NAMES if n.startswith("ir_mext_")]:
        twin = to_mkv_name(name)
        if twin not in NAMES:
            bad.append(f"{name}: no mkv twin {twin}")
            continue
        t = terms[CONSTS[NAMES.index(twin)]]
        mk = terms[CONSTS[NAMES.index(name)]]
        if name not in threaded:
            if from_mkv(t) != mk:
                bad.append(f"{twin}: undoing the mkv re-spelling does not give back {name}")
        else:
            stripped = from_mkv(t).replace(f" {PREMISE['he']} {PREMISE['hl']}", "").replace(" henc hlen", "")
            if name == "ir_mext_arm_load":
                if "ir_enc_agree_load_view es0 es henc hlen" not in t or "Eq.refl" in t.split(" := ", 1)[1]:
                    bad.append(f"{twin}: the load arm is not closed by the encodings premise")
                if stripped.split(" := ", 1)[0] != mk.split(" := ", 1)[0]:
                    bad.append(f"{twin}: the load arm's statement is not the mk statement plus henc / hlen")
            elif stripped != mk:
                bad.append(f"{twin}: removing the threaded henc / hlen does not give back {name}")
        if uses("m", t.split(" := ", 1)[1]):
            bad.append(f"{twin}: a bare module variable survives in the body")
        # NAME CAPTURE (found by the kernel on the first build, 2026-09-30): the convoy in
        # ext_lookup binds its lookup equation as `he`, so an encodings premise spelled `he`
        # was SHADOWED inside every convoy and the load arm received the equation. The
        # premises are `henc` / `hlen`; no term may bind either name a second time.
        for prem_name in (re.match(r"\((\w+) :", PREMISE[k]).group(1) for k in ("he", "hl")):
            if t.count(f"({prem_name} :") > 1:
                bad.append(f"{twin}: `{prem_name}` is bound more than once (a premise would be shadowed)")
    # Every D/E lemma's binders are its helper's own with `s` expanded; every E'
    # lemma's are its helper's own with `m` and `s` expanded and hrun last.
    for const, name, _, _ in TERMS:
        got = [n for n, _ in _binders(terms[const], len(f"def {name}"))[0]]
        if name.endswith("_stack") and name[: -len("_stack")] in MACHINE and name != "ir_ret_to_stack":
            want = []
            for n in MACHINE[name[: -len("_stack")]].names:
                want += ["f", "t", "rest", "mem", "na"] if n == "s" else [rn(n)]
        elif name.startswith("ir_mext_") and name not in MAIN_TERMS and "ir_" + name[len("ir_mext_"):] in MACHINE:
            want = []
            for n in MACHINE["ir_" + name[len("ir_mext_"):]].names:
                want += (["fs0", "gs0", "fs", "gs", "hf"] if n == "m" else ["f", "t", "mem", "na"] if n == "s" else [rn(n)])
            want.append("hrun")
        else:
            continue
        if got != want:
            bad.append(f"{name}: binders {got} are not the helper's {want}")
    return bad


CONST_RE = re.compile(r'^const (SRC_[A-Z0-9_]+): &str = "(.*?)";$', re.M)
NAMES_RE = re.compile(r"pub const STACK_MINTED_NAMES: &\[&str\] = &\[(.*?)\];", re.S)
DECLS_RE = re.compile(r"const DECLS: &\[\(&str, &str\)\] = &\[(.*?)\n\];", re.S)
ROW_RE = re.compile(r"^\s*\((SRC_[A-Z0-9_]+),", re.M)


def check_text(have: str, want: str) -> list[str]:
    """Why `have` is not the file this script emits -- an empty list iff it is.
    Byte equality is the verdict; the rest is the diagnosis."""
    if have == want:
        return []
    bad: list[str] = []
    have_consts = dict(CONST_RE.findall(have))
    for const, body in CONST_RE.findall(want):
        if const not in have_consts:
            bad.append(f"MISSING {const}")
        elif have_consts[const] != body:
            i = next((j for j, (x, y) in enumerate(zip(have_consts[const], body)) if x != y),
                     min(len(body), len(have_consts[const])))
            bad.append(f"DIFFERS {const}: committed {len(have_consts[const])} chars, minted {len(body)} chars; "
                       f"first difference at {i}: committed ...{have_consts[const][max(0, i - 60):i + 60]}... "
                       f"minted ...{body[max(0, i - 60):i + 60]}...")
    extra = sorted(set(have_consts) - set(CONSTS))
    if extra:
        bad.append(f"UNDECLARED consts: {extra} -- the census refuses hand-added terms")
    names = NAMES_RE.search(have)
    if not names:
        bad.append("MISSING: `pub const STACK_MINTED_NAMES` no longer parses")
    elif re.findall(r'"([^"]+)"', names.group(1)) != NAMES:
        bad.append("STACK_MINTED_NAMES is not the minted list (order, a hand-added or a missing name)")
    table = DECLS_RE.search(have)
    if not table:
        bad.append("MISSING: `const DECLS` no longer parses")
    elif ROW_RE.findall(table.group(1)) != CONSTS:
        bad.append("DECLS rows are not the minted registration order")
    if not bad:
        bad.append("the file differs outside the consts and tables (doc, tests, or whitespace)")
    return bad


def check() -> int:
    if not MINTED_RS.exists():
        print(f"MISSING: {MINTED_RS} does not exist; run --emit")
        return 1
    bad = check_text(MINTED_RS.read_text(), render_rust(minted()))
    for line in bad:
        print(line)
    if bad:
        print(f"gen_stack_lemmas: {MINTED_RS.name} is not what --emit produces ({len(bad)} finding(s))")
        return 1
    print(f"gen_stack_lemmas: {len(TERMS)} terms, STACK_MINTED_NAMES and DECLS match {MINTED_RS.name}")
    return 0


def mutation_test(want: str) -> list[str]:
    """The census must REFUSE a hand edit, demonstrated rather than assumed:
    the rendered file passes, and three edits of it each fail."""
    bad: list[str] = []
    if check_text(want, want):
        bad.append("MUTATION: the freshly rendered file does not pass its own check")
    # 1. one character inside a term
    const, body = CONST_RE.findall(want)[len(CONSTS) // 2]
    i = body.index("Bool.true")
    edited = want.replace(f'const {const}: &str = "{body}";', f'const {const}: &str = "{body[:i]}Bool.false{body[i + len("Bool.true"):]}";', 1)
    if edited == want or not any(f"DIFFERS {const}" in b for b in check_text(edited, want)):
        bad.append(f"MUTATION: a hand-edited term inside {const} was not refused")
    # 2. a hand-added const, registered and listed
    last = CONSTS[-1]
    hand = ('const SRC_HAND_ADDED: &str = "def ir_stk_hand_added (x : Nat) : Nat := x";\n')
    added = want.replace(f"const {last}: &str = ", hand + f"const {last}: &str = ", 1)
    added = added.replace(f'    "{NAMES[-1]}",\n', f'    "{NAMES[-1]}",\n    "ir_stk_hand_added",\n', 1)
    added = added.replace("\n];\n\nimpl Specification", '\n    (SRC_HAND_ADDED, "hand-added row"),\n];\n\nimpl Specification', 1)
    found = check_text(added, want)
    if added == want or not any("UNDECLARED" in b for b in found) or not any("STACK_MINTED_NAMES" in b for b in found) \
            or not any("DECLS rows" in b for b in found):
        bad.append(f"MUTATION: a hand-added const was not refused on all three surfaces: {found}")
    # 3. a reordered registration row (the const stays, its position moves)
    rows = ROW_RE.findall(DECLS_RE.search(want).group(1))
    a, b = rows[0], rows[1]
    lines = want.split("\n")
    ia = next(i for i, ln in enumerate(lines) if ln.startswith(f"    ({a}, "))
    ib = next(i for i, ln in enumerate(lines) if ln.startswith(f"    ({b}, "))
    lines[ia], lines[ib] = lines[ib], lines[ia]
    swapped = "\n".join(lines)
    if swapped == want or not any("DECLS rows" in b for b in check_text(swapped, want)):
        bad.append("MUTATION: a reordered DECLS row was not refused")
    return bad


def self_test() -> int:
    terms = minted()
    bad = structural(terms)
    want = render_rust(terms)
    bad += mutation_test(want)
    have = digests(terms)
    for k in sorted(set(CONSTS) - set(PINNED_DIGESTS)):
        bad.append(f"UNPINNED: {k} is minted but has no pinned digest (run --pin after a kernel build accepts it)")
    for k in sorted(set(PINNED_DIGESTS) - set(CONSTS)):
        bad.append(f"ORPHAN DIGEST: {k} is pinned but no emitter produces it")
    if FORM == "direct":
        for k, v in PINNED_DIGESTS.items():
            if k in have and have[k] != v:
                bad.append(f"DIGEST MOVED: {k}")
    else:
        print(f"(digest pins are of the direct form; --form {FORM} is not held against them)")
    for line in bad:
        print(line)
    n_mext_helpers = sum(1 for n in NAMES if n.startswith("ir_mext_") and not n.startswith("ir_mext_arm_")) - 2
    n_mkv = len(NAMES) - NAMES.index("ir_enc_agree_view_word")
    n_node = NAMES.index("ir_enc_agree_view_word") - NAMES.index("ir_mext_steps") - 1
    n_node_arms = sum(1 for n in NAMES if n.startswith("ir_stkn_arm_"))
    print(f"tables read from source: IRInst {len(ctors('IRInst'))}, IRScalar {len(ctors('IRScalar'))}, "
          f"IRTy {len(ctors('IRTy'))}, IRStepResult {len(ctors('IRStepResult'))}; "
          f"{len(EXEC_ARMS)} ir_exec arms; {len(TERMS)} terms "
          f"({len(TERMS) - n_node - n_mkv - 2 * N_ARMS - n_mext_helpers - 3} ir_stk helpers + {N_ARMS} ir_stk arms + ir_stk_step, "
          f"{n_mext_helpers} ir_mext helpers + {N_ARMS} ir_mext arms + ir_mext_step + ir_mext_steps, "
          f"{n_node - n_node_arms - 3} node-keyed classifier defs/pins + ir_stkn_ret_to + {n_node_arms} ir_stkn arms "
          f"+ ir_stkn_step + ir_stk_botret_false_of_running, {n_mkv} mkv: 3 encodings-agreement lemmas + "
          f"{n_mkv - 4} ir_mextv twins + ir_mextv_run), "
          f"{sum(len(v) for v in terms.values())} chars; mutation test: 3 hand edits refused")
    print("gen_stack_lemmas --self-test: " + ("OK" if not bad else f"FAILED ({len(bad)})"))
    return 0 if not bad else 1


def tables() -> None:
    for fam in ("IRInst", "IRScalar", "IRTy", "IRStepResult", "IROption", "IRList", "IRNode", "IRMachine", "IRConfig"):
        print(f"{fam} ({len(ctors(fam))}):")
        for c, tys in ctors(fam):
            rec = [i for i, ty in enumerate(tys) if ty == fam]
            print(f"  {c}: {tys}" + (f"  recursive fields at {rec}" if rec else ""))
    print("ir_exec arms (ctor, fields, rhs, ir_mext premise):")
    for ctor, names, types, rhs in ARMS:
        print(f"  {ctor} {names} -> {rhs}   [mext: {mext_arm_prem(rhs) or 'none, Eq.refl'}]")


def main(argv=None) -> int:
    global FORM
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--emit", action="store_true", help="(re)write the Rust file")
    ap.add_argument("--check", action="store_true", help="byte-compare with the tree")
    ap.add_argument("--self-test", action="store_true", help="structure + mutation + digest pins")
    ap.add_argument("--print", dest="show", help="print one term by name or const")
    ap.add_argument("--list", action="store_true", help="names in registration order")
    ap.add_argument("--tables", action="store_true", help="what was read from source")
    ap.add_argument("--digests", action="store_true")
    ap.add_argument("--pin", action="store_true", help="rewrite PINNED_DIGESTS from the current (direct) emission")
    ap.add_argument("--form", choices=["direct", "convoy"], default=FORM,
                    help="how a recursor on a NEUTRAL major is spelled (default direct)")
    args = ap.parse_args(argv)
    FORM = args.form
    if args.tables:
        tables()
        return 0
    if args.list:
        for n in NAMES:
            print(n)
        return 0
    if args.show:
        print(by_name(args.show))
        return 0
    if args.digests:
        for k, v in sorted(digests(minted()).items()):
            print(f'    "{k}": "{v}",')
        return 0
    if args.pin:
        if FORM != "direct":
            print("gen_stack_lemmas: pins are of the direct form; re-run without --form convoy")
            return 1
        body = "PINNED_DIGESTS: dict = {\n" + "".join(
            f'    "{k}": "{v}",\n' for k, v in sorted(digests(minted()).items())) + "}"
        src = Path(__file__).read_text()
        src = re.sub(r"PINNED_DIGESTS: dict = \{.*?\n\}", body, src, count=1, flags=re.S)
        Path(__file__).write_text(src)
        print(f"pinned {len(TERMS)} digests")
        return 0
    if args.self_test:
        return self_test()
    if args.emit:
        bad = structural(minted())
        if bad:
            for line in bad:
                print(line)
            return 1
        MINTED_RS.write_text(render_rust(minted()))
        print(f"gen_stack_lemmas: emitted {len(TERMS)} terms into {MINTED_RS} (--form {FORM})")
        return 0
    return check()


if __name__ == "__main__":
    sys.exit(main())
