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
S0 = "(IRMachine.mk (@IRList.cons IRFrame f t) mem na)"
S1 = f"(IRMachine.mk (@IRList.cons IRFrame f {APP}) mem na)"
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
HF_TY = ("forall (kf : Nat) (gf : IRFunc), @Eq (IROption IRFunc) (ir_func_find fs0 kf) (@IROption.some IRFunc gf) -> "
         "@Eq (IROption IRFunc) (ir_func_find fs kf) (@IROption.some IRFunc gf)")
HG_TY = ("forall (kg : Nat) (gg : IRGlobal), @Eq (IROption IRGlobal) (ir_global_find gs0 kg) (@IROption.some IRGlobal gg) -> "
         "@Eq (IROption IRGlobal) (ir_global_find gs kg) (@IROption.some IRGlobal gg)")
PREMISE = {"hf": f"(hf : {HF_TY})", "hg": f"(hg : {HG_TY})"}

# The ENCODINGS premise of the mkv module axis (crystal link 4 M0 W3): the two
# tables answer every row lookup identically (a hit AND a miss) and have the same
# length, which is the view's fuel. Only the `load` arm reads it.
HE_TY = "forall (te : IRTy), @Eq (IROption IREnc) (ir_enc_find es0 te) (ir_enc_find es te)"
HL_TY = "@Eq Nat (ir_enc_len es0) (ir_enc_len es)"
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
    return f"@Eq IRConfig {at(tpl, S1)} (ir_config_stack {at(tpl, S0)} rest)"


def mext_goal(tpl: str) -> str:
    """`Eq IRConfig (H M0 ..) (H M ..)` for a template over {M} (the machine is S0)."""
    return f"@Eq IRConfig {atm(tpl, M0)} {atm(tpl, M1)}"


def mext_prem(tpl: str) -> str:
    """The running premise on the M0 side."""
    return f"@Eq Bool (ir_stk_running {atm(tpl, M0)}) Bool.true"


def mext_stmt(tpl: str) -> str:
    """Premise-passing statement: the shape every ir_mext motive has."""
    return f"{mext_prem(tpl)} -> {mext_goal(tpl)}"


def running(frames: str, mem: str = "mem", na: str = "na") -> str:
    return f"(IRConfig.running (IRMachine.mk {frames} {mem} {na}))"


def cons(x: str, xs: str) -> str:
    return f"(@IRList.cons IRFrame {x} {xs})"


def halted(o: str) -> str:
    return f"(IRConfig.halted {o})"


def stuck(fault: str) -> str:
    return halted(f"(IROutcome.stuck IRFault.{fault})")


def tyerr(fault: str) -> str:
    return halted(f"(IROutcome.type_error IRFault.{fault})")


def ub(fault: str) -> str:
    return halted(f"(IROutcome.ub IRFault.{fault})")


def refl(ty: str, x: str) -> str:
    return f"@Eq.refl {ty} {x}"


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
    return f"@Bool.rec (fun ({var} : Bool) => {motive(var)}) ({false_case}) ({true_case}) {major}"


def opt_rec(param: str, var: str, motive, none_case: str, some_binder: tuple[str, str],
            some_case: str, major: str) -> str:
    sb, sty = some_binder
    return (f"@IROption.rec {param} (fun ({var} : IROption {param}) => {motive(var)}) "
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
    none = f"(@IROption.none {param})"
    some = f"(@IROption.some {param} {sb})"

    def transport(known: str, term: str) -> str:
        return (f"@Eq.subst {T} (fun ({var}1 : IROption {param}) => {motive(var + '1')}) {known} {scrut} "
                f"(@Eq.symm {T} {scrut} {known} h{var}) ({term})")

    return (f"@IROption.rec {param} (fun ({var} : IROption {param}) => @Eq {T} {scrut} {var} -> {goal}) "
            f"(fun (h{var} : @Eq {T} {scrut} {none}) => {transport(none, none_case)}) "
            f"(fun ({sb} : {sty}) (h{var} : @Eq {T} {scrut} {some}) => {transport(some, some_case)}) "
            f"{scrut} (@Eq.refl {T} {scrut})")


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
    return f"@{fam}.rec (fun ({var} : {fam}) => {motive(var)}) {' '.join(minors)} {major}"


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
    none = f"(@IROption.none {T})"
    some = f"(@IROption.some {T} {found})"
    prem = lambda o: f"@Eq Bool (ir_stk_running {body0(o)}) Bool.true"
    goal = lambda o: f"@Eq IRConfig {body0(o)} {body1(other)}"
    none_minor = (f"(fun (_ : @Eq {OT} {scrut} {none}) (h : {prem(none)}) => "
                  f"ir_bool_false_ne_true ({goal(none)}) h)")
    hname = "h" if uses("h", some_term) else "_"
    some_minor = (f"(fun ({found} : {T}) (he : @Eq {OT} {scrut} {some}) ({hname} : {prem(some)}) => "
                  f"@Eq.subst {OT} (fun (o2 : IROption {T}) => @Eq IRConfig {body0(some)} {body1('o2')}) {some} {other} "
                  f"(@Eq.symm {OT} {other} {some} ({hyp} {key} {found} he)) ({some_term}))")
    return (f"@IROption.rec {T} (fun (o : IROption {T}) => @Eq {OT} {scrut} o -> {prem('o')} -> {goal('o')}) "
            f"{none_minor} {some_minor} {scrut} (@Eq.refl {OT} {scrut})")


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
    return (f"@Eq.subst {VS} (fun (vs : IRList IRScalar) => {motive_body('vs')}) {r0} {r1} "
            f"(@Eq.symm {VS} {r1} {r0} (ir_resolve_stack {BARGS} {x})) ({inner})")


# The abstracted helper bodies the neutral-major motives quote. Each is the
# machine's own body with the module, the machine and the MAJOR abstracted;
# `--self-test` holds them against the source (see body_checks).


def switch_n_body(m: str, S: str, o: str) -> str:
    return (f"(@IROption.rec IRSwitchCase (fun (_ : IROption IRSwitchCase) => IRConfig) "
            f"(ir_jump {m} {S} dflt dargs) "
            f"(fun (c : IRSwitchCase) => ir_jump {m} {S} (ir_case_target c) (ir_case_args c)) {o})")


def call_exec_body(S: str, o: str) -> str:
    # The callee binder is renamed g: the source's `f` would capture the frame.
    return (f"(@IROption.rec IRFunc (fun (_ : IROption IRFunc) => IRConfig) "
            f"(IRConfig.halted (IROutcome.stuck IRFault.no_func)) "
            f"(fun (g : IRFunc) => ir_push {S} rs g (ir_resolve {S} args)) {o})")


def alloca_exec_body(S: str, o: str) -> str:
    return (f"(@IROption.rec Nat (fun (_ : IROption Nat) => IRConfig) "
            f"(IRConfig.halted (IROutcome.type_error IRFault.not_int)) "
            f"(fun (k : Nat) => ir_alloca_k {S} rs k) {o})")


def globaladdr_body(o: str) -> str:
    return (f"(@IROption.rec IRGlobal (fun (_ : IROption IRGlobal) => IRStepResult) "
            f"(IRStepResult.fault (IROutcome.type_error IRFault.no_global)) "
            f"(fun (_ : IRGlobal) => IRStepResult.value (IRScalar.ptr_ g)) {o})")


def body_checks() -> list[str]:
    """Each abstracted body, re-instantiated at the source's own names and major,
    must BE the source body after removing only the wrapping parentheses."""
    bad = []
    cases = [
        ("ir_switch_n", switch_n_body("m", "s", "(ir_case_find cases n)")),
        ("ir_call_exec", call_exec_body("s", "(ir_func_find (ir_mod_funcs m) fid)").replace("(g : IRFunc) => ir_push s rs g", "(f : IRFunc) => ir_push s rs f")),
        ("ir_alloca_exec", alloca_exec_body("s", "(ir_alloca_count s c)")),
        ("ir_globaladdr_eval", globaladdr_body("(ir_global_find (ir_mod_globals m) g)")),
    ]
    for helper, quoted in cases:
        if quoted[1:-1] != machine(helper).body:
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
    return defn("ir_getd_stack", binders, f"@Eq IRScalar {at(tpl, S1)} {at(tpl, S0)}",
                refl("IRScalar", "(ir_frame_get f k)"))


def c_mach_mem() -> str:
    binders, _, tpl = sig("ir_mach_mem")
    return defn("ir_mach_mem_stack", binders, f"@Eq (IRList IRMemSlot) {at(tpl, S1)} {at(tpl, S0)}",
                refl("(IRList IRMemSlot)", "mem"))


def c_resolve() -> str:
    binders, _, _ = sig("ir_resolve")
    mot = lambda v: f"@Eq {VS} (ir_resolve {S1} {v}) (ir_resolve {S0} {v})"
    body = (f"@IRList.rec Nat (fun (ids0 : IRList Nat) => {mot('ids0')}) "
            f"({refl(VS, '(@IRList.nil IRScalar)')}) "
            f"(fun (i : Nat) (ids2 : IRList Nat) (ih : {mot('ids2')}) => "
            f"ir_eq_cong {VS} {VS} (fun (vs : IRList IRScalar) => @IRList.cons IRScalar (ir_frame_get f i) vs) "
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
    body = (f"@IRStepResult.rec (fun (r0 : IRStepResult) => {mot('r0')}) "
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
              "(ir_bind_params (ir_func_params g) vs (@IRList.nil IRBinding)) rs)")
    return _refl_writer("ir_push", running(cons(callee, cons("(ir_frame_advance f)", APP))))


def d_ret_to() -> str:
    d = machine("ir_ret_to")
    assert d.names == ["dests", "rest", "mem", "na", "vs"], d.names
    def mot(v: str) -> str:
        return (f"@Eq Bool (ir_stk_running (ir_ret_to ds {v} mem na vs)) Bool.true -> "
                f"@Eq IRConfig (ir_ret_to ds (ir_frames_app {v} rest) mem na vs) "
                f"(ir_config_stack (ir_ret_to ds {v} mem na vs) rest)")
    nil = "(@IRList.nil IRFrame)"
    nil_goal = (f"@Eq IRConfig (ir_ret_to ds (ir_frames_app {nil} rest) mem na vs) "
                f"(ir_config_stack (ir_ret_to ds {nil} mem na vs) rest)")
    nil_minor = (f"(fun (h0 : @Eq Bool (ir_stk_running (ir_ret_to ds {nil} mem na vs)) Bool.true) => "
                 f"ir_bool_false_ne_true ({nil_goal}) h0)")
    cons_minor = (f"(fun (g : IRFrame) (t2 : IRList IRFrame) (_ih : {mot('t2')}) "
                  f"(h0 : @Eq Bool (ir_stk_running (ir_ret_to ds (@IRList.cons IRFrame g t2) mem na vs)) Bool.true) => "
                  f"{refl('IRConfig', running(cons('(ir_frame_set_many g ds vs)', '(ir_frames_app t2 rest)')))})")
    body = f"@IRList.rec IRFrame (fun (t0 : IRList IRFrame) => {mot('t0')}) {nil_minor} {cons_minor} t h"
    binders = ("(ds : IRList Nat) (rest : IRList IRFrame) (mem : IRList IRMemSlot) (na : Nat) "
               "(vs : IRList IRScalar) (t : IRList IRFrame) "
               "(h : @Eq Bool (ir_stk_running (ir_ret_to ds t mem na vs)) Bool.true)")
    ty = (f"@Eq IRConfig (ir_ret_to ds (ir_frames_app t rest) mem na vs) "
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
    mot = lambda vs: f"@Eq IRConfig (ir_jump_func {S1} tgt {vs} {cur}) (ir_config_stack {at(tpl, S0)} rest)"
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
    mot = lambda o: f"@Eq IRConfig {switch_n_body('m', S1, o)} (ir_config_stack {switch_n_body('m', S0, o)} rest)"
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
    mot = lambda o: f"@Eq IRConfig {call_exec_body(S1, o)} (ir_config_stack {call_exec_body(S0, o)} rest)"
    some_mot = lambda vs: (f"@Eq IRConfig (ir_push {S1} rs g {vs}) "
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
    inner_mot = lambda o: f"@Eq IRConfig {alloca_exec_body(S1, o)} (ir_config_stack {alloca_exec_body(S0, o)} rest)"
    inner = neutral_opt_rec("Nat", "o1", inner_mot, refl("IRConfig", tyerr("not_int")), ("k", "Nat"),
                            f"ir_alloca_k_stack {BARGS} rs k", "(ir_as_int (ir_frame_get f i))",
                            mot("(@IROption.some Nat i)"))
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
        mot = lambda vs: (f"@Eq IRConfig (ir_ret_to (ir_frame_dests f) (ir_frames_app t rest) mem na {vs}) "
                          f"(ir_config_stack {at(tpl, S0)} rest)")
        return resolve_subst(ids, mot, f"{ret_lemma} (ir_frame_dests f) rest mem na (ir_resolve {S0} {ids}) t {ret_prem}")
    term, resolves = stackify(rhs)
    if not resolves:
        return term
    (x,) = resolves
    assert term.startswith(f"ir_bind_result_stack {BARGS} rs "), (ctor, term)
    evaluator = term[len(f"ir_bind_result_stack {BARGS} rs "):]
    mot = lambda vs: (f"@Eq IRConfig (ir_bind_result {S1} rs {evaluator.replace(f'(ir_resolve {S0} {x})', vs)}) "
                      f"(ir_config_stack {at(tpl, S0)} rest)")
    return resolve_subst(x, mot, term)


def arm_lemma(ctor: str, names: list[str], types: list[str], rhs: str) -> str:
    tpl = f"(ir_exec m {inst_app(ctor, names)} rs {{S}})"
    fields = " ".join(f"({n} : {ty})" for n, ty in zip(names, types))
    binders = f"(m : IRModule) {BLOCK} (rs : IRList Nat) {fields + ' ' if fields else ''}(hrun : @Eq Bool (ir_stk_running {at(tpl, S0)}) Bool.true)"
    return defn(f"ir_stk_arm_{ctor}", binders, stk_goal(tpl), arm_proof(ctor, names, rhs, tpl))


def arm_builder(ctor: str, names: list[str], types: list[str], rhs: str):
    return lambda: arm_lemma(ctor, names, types, rhs)


# --------------------------------------------------------------------------
# G. the main term
# --------------------------------------------------------------------------


def g_stk_step() -> str:
    mk = lambda fs: f"(IRMachine.mk {fs} mem na)"
    mot_s = lambda s0: (f"@Eq Bool (ir_stk_running (ir_step m {s0})) Bool.true -> "
                        f"@Eq IRConfig (ir_step m (ir_mach_stack {s0} rest)) (ir_config_stack (ir_step m {s0}) rest)")
    mot_fs = lambda fs0: mot_s(mk(fs0))
    bl, pc = "(ir_frame_block f)", "(ir_frame_pc f)"

    def layer(step):
        return lambda o: (f"@Eq Bool (ir_stk_running {step(S0, o)}) Bool.true -> "
                          f"@Eq IRConfig {step(S1, o)} (ir_config_stack {step(S0, o)} rest)")

    step_f = lambda S, o: f"(ir_step_f m {S} {bl} {pc} {o})"
    step_b = lambda S, o: f"(ir_step_b m {S} {pc} {o})"
    step_n = lambda S, o: f"(ir_step_n m {S} {o})"
    exec_node = lambda S, n0: f"(ir_exec_node m {n0} {S})"
    exec_i = lambda S, i0: f"(ir_exec m {i0} rs {S})"
    mot_f, mot_b, mot_n = layer(step_f), layer(step_b), layer(step_n)
    mot_nd, mot_i = layer(exec_node), layer(exec_i)

    def none_minor(step, param: str, fault: str) -> str:
        none = f"(@IROption.none {param})"
        return (f"fun (_ : @Eq Bool (ir_stk_running {step(S0, none)}) Bool.true) => "
                f"{refl('IRConfig', stuck(fault))}")

    inst_minors = []
    for ctor, names, types, _ in ARMS:
        call = f"ir_stk_arm_{ctor} m {BARGS} rs {' '.join(names)}".rstrip()
        if names:
            fields = " ".join(f"({n} : {ty})" for n, ty in zip(names, types))
            inst_minors.append(f"(fun {fields} => {call})")
        else:
            inst_minors.append(f"({call})")
    inst_rec = f"@IRInst.rec (fun (i0 : IRInst) => {mot_i('i0')}) {' '.join(inst_minors)} i"
    assert [c for c, _ in ctors("IRNode")] == ["mk"] and ctors("IRNode")[0][1] == ["IRInst", "IRList Nat"]
    node_rec = f"@IRNode.rec (fun (n0 : IRNode) => {mot_nd('n0')}) (fun (i : IRInst) (rs : IRList Nat) => {inst_rec}) nd"
    n_scrut = f"(ir_nodes_get (ir_block_nodes bk) {pc})"
    n_rec = neutral_opt_rec("IRNode", "on", mot_n, none_minor(step_n, "IRNode", "fetch_past_end"),
                            ("nd", "IRNode"), node_rec, n_scrut, mot_n(n_scrut))
    b_scrut = f"(ir_block_find (ir_func_blocks fn) {bl})"
    b_rec = neutral_opt_rec("IRBlock", "ob", mot_b, none_minor(step_b, "IRBlock", "no_block"),
                            ("bk", "IRBlock"), n_rec, b_scrut, mot_b(b_scrut))
    f_scrut = "(ir_func_find (ir_mod_funcs m) (ir_frame_func f))"
    f_rec = neutral_opt_rec("IRFunc", "o", mot_f, none_minor(step_f, "IRFunc", "no_func"),
                            ("fn", "IRFunc"), b_rec, f_scrut, mot_f(f_scrut))
    nil = "(@IRList.nil IRFrame)"
    nil_minor = (f"(fun (h : @Eq Bool (ir_stk_running (ir_step m {mk(nil)})) Bool.true) => "
                 f"ir_bool_false_ne_true (@Eq IRConfig (ir_step m (ir_mach_stack {mk(nil)} rest)) "
                 f"(ir_config_stack (ir_step m {mk(nil)}) rest)) h)")
    cons_minor = f"(fun (f : IRFrame) (t : IRList IRFrame) (_ih : {mot_fs('t')}) => {f_rec})"
    list_rec = f"@IRList.rec IRFrame (fun (fs0 : IRList IRFrame) => {mot_fs('fs0')}) {nil_minor} {cons_minor} fs"
    assert ctors("IRMachine")[0][1] == ["IRList IRFrame", "IRList IRMemSlot", "Nat"]
    body = (f"@IRMachine.rec (fun (s0 : IRMachine) => {mot_s('s0')}) "
            f"(fun (fs : IRList IRFrame) (mem : IRList IRMemSlot) (na : Nat) => {list_rec}) s hrun")
    binders = ("(m : IRModule) (s : IRMachine) (rest : IRList IRFrame) "
               "(hrun : @Eq Bool (ir_stk_running (ir_step m s)) Bool.true)")
    return defn("ir_stk_step", binders, "@Eq IRConfig (ir_step m (ir_mach_stack s rest)) (ir_config_stack (ir_step m s) rest)", body)


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
                      refl("IRConfig", body("(@IROption.some IRFunc gf)")))
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
    mot = lambda o: (f"@Eq Bool (ir_stk_running {body_o(M0, o)}) Bool.true -> "
                     f"@Eq IRConfig {body_o(M0, o)} {body_o(M1, o)}")
    none = "(@IROption.none IRSwitchCase)"
    some = "(@IROption.some IRSwitchCase c)"
    none_case = (f"fun (h : @Eq Bool (ir_stk_running {body_o(M0, none)}) Bool.true) => "
                 f"ir_mext_jump {MARGS} hf {FARGS} dflt dargs h")
    some_case = (f"fun (h : @Eq Bool (ir_stk_running {body_o(M0, some)}) Bool.true) => "
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
                      refl("IRConfig", body("(@IROption.some IRFunc gf)")))
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
                      refl("IRConfig", body("(@IROption.some IRGlobal gg)")))
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
    mot_s = lambda s0: (f"@Eq Bool (ir_stk_running (ir_step {M0} {s0})) Bool.true -> "
                        f"@Eq IRConfig (ir_step {M0} {s0}) (ir_step {M1} {s0})")
    mot_fr = lambda fr0: mot_s(mk(fr0))
    bl, pc = "(ir_frame_block f)", "(ir_frame_pc f)"

    def layer(step):
        return lambda o: (f"@Eq Bool (ir_stk_running {step(M0, o)}) Bool.true -> "
                          f"@Eq IRConfig {step(M0, o)} {step(M1, o)}")

    step_f = lambda M, o: f"(ir_step_f {M} {S0} {bl} {pc} {o})"
    step_b = lambda M, o: f"(ir_step_b {M} {S0} {pc} {o})"
    step_n = lambda M, o: f"(ir_step_n {M} {S0} {o})"
    exec_node = lambda M, n0: f"(ir_exec_node {M} {n0} {S0})"
    exec_i = lambda M, i0: f"(ir_exec {M} {i0} rs {S0})"
    mot_b, mot_n, mot_nd, mot_i = layer(step_b), layer(step_n), layer(exec_node), layer(exec_i)

    def none_minor(step, param: str, fault: str) -> str:
        none = f"(@IROption.none {param})"
        return (f"fun (_ : @Eq Bool (ir_stk_running {step(M0, none)}) Bool.true) => "
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
    inst_rec = f"@IRInst.rec (fun (i0 : IRInst) => {mot_i('i0')}) {' '.join(inst_minors)} i"
    node_rec = f"@IRNode.rec (fun (n0 : IRNode) => {mot_nd('n0')}) (fun (i : IRInst) (rs : IRList Nat) => {inst_rec}) nd"
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
    nil = "(@IRList.nil IRFrame)"
    nil_minor = (f"(fun (_ : @Eq Bool (ir_stk_running (ir_step {M0} {mk(nil)})) Bool.true) => "
                 f"{refl('IRConfig', stuck('no_frame'))})")
    cons_minor = f"(fun (f : IRFrame) (t : IRList IRFrame) (_ih : {mot_fr('t')}) => {f_conv})"
    list_rec = f"@IRList.rec IRFrame (fun (fr0 : IRList IRFrame) => {mot_fr('fr0')}) {nil_minor} {cons_minor} fr"
    body = (f"@IRMachine.rec (fun (s0 : IRMachine) => {mot_s('s0')}) "
            f"(fun (fr : IRList IRFrame) (mem : IRList IRMemSlot) (na : Nat) => {list_rec}) s hrun")
    binders = (f"{MBLOCK} {PREMISE['hf']} {PREMISE['hg']}{_enc_binders()} (s : IRMachine) "
               f"(hrun : @Eq Bool (ir_stk_running (ir_step {M0} s)) Bool.true)")
    return defn("ir_mext_step", binders, f"@Eq IRConfig (ir_step {M0} s) (ir_step {M1} s)", body)


def g_mext_steps() -> str:
    stmt = lambda k: (f"forall (c : IRConfig), @Eq Bool (ir_stk_running (ir_steps {k} {M0} c)) Bool.true -> "
                      f"@Eq IRConfig (ir_steps {k} {M0} c) (ir_steps {k} {M1} c)")
    mot_c = lambda c0: (f"@Eq Bool (ir_stk_running (ir_steps (Nat.succ k) {M0} {c0})) Bool.true -> "
                        f"@Eq IRConfig (ir_steps (Nat.succ k) {M0} {c0}) (ir_steps (Nat.succ k) {M1} {c0})")
    a = f"(ir_steps k {M0} (ir_step {M0} s))"
    b = f"(ir_steps k {M1} (ir_step {M0} s))"
    c = f"(ir_steps k {M1} (ir_step {M1} s))"
    running_minor = (
        f"(fun (s : IRMachine) (hrun : @Eq Bool (ir_stk_running (ir_steps (Nat.succ k) {M0} (IRConfig.running s))) Bool.true) => "
        f"@Eq.trans IRConfig {a} {b} {c} (ih (ir_step {M0} s) hrun) "
        f"(ir_eq_cong IRConfig IRConfig (fun (c1 : IRConfig) => ir_steps k {M1} c1) (ir_step {M0} s) (ir_step {M1} s) "
        f"(ir_mext_step {MARGS} hf hg{_enc_args()} s (ir_stk_running_back {M0} k (ir_step {M0} s) hrun))))")
    halted_minor = (f"(fun (o : IROutcome) (_ : @Eq Bool (ir_stk_running (ir_steps (Nat.succ k) {M0} (IRConfig.halted o))) Bool.true) => "
                    f"{refl('IRConfig', halted('o'))})")
    zero = (f"(fun (c : IRConfig) (_ : @Eq Bool (ir_stk_running (ir_steps Nat.zero {M0} c)) Bool.true) => "
            f"{refl('IRConfig', 'c')})")
    succ = (f"(fun (k : Nat) (ih : {stmt('k')}) => fun (c : IRConfig) => "
            f"@IRConfig.rec (fun (c0 : IRConfig) => {mot_c('c0')}) {running_minor} {halted_minor} c)")
    body = f"@Nat.rec (fun (k : Nat) => {stmt('k')}) {zero} {succ} n"
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
NIL_F = "(@IRList.nil IRFrame)"


def frames_case(nil_val: str, t: str) -> str:
    """`IRList.rec IRFrame (fun _ => Bool) nil_val (fun _ _ _ => Bool.false) t`:
    the Bool that is `nil_val` on an empty list and false on a cons. With
    nil_val = Bool.true it IS ir_frames_is_nil's body, which is how the classifier
    premise at a ret node becomes the arm's `t is not nil` premise by iota."""
    return f"(@IRList.rec IRFrame (fun (_ : IRList IRFrame) => Bool) {nil_val} {FALSE_K} {t})"


def node_prem(cls: str) -> str:
    """The classifier premise at a cons machine `f :: t`, with the fetch layer's
    Bool abstracted: false iff t is a cons, or t is empty and the fetch is not ret."""
    return f"@Eq Bool {frames_case(cls, 't')} Bool.false"


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
                "@IRNode.rec (fun (_ : IRNode) => Bool) (fun (i : IRInst) (_ : IRList Nat) => ir_inst_is_ret i) n")


def k_fetch_n_ret() -> str:
    return defn("ir_fetch_n_ret", "(on : IROption IRNode)", "Bool",
                "@IROption.rec IRNode (fun (_ : IROption IRNode) => Bool) Bool.false "
                "(fun (n : IRNode) => ir_node_is_ret n) on")


def k_fetch_b_ret() -> str:
    return defn("ir_fetch_b_ret", "(pc : Nat) (ob : IROption IRBlock)", "Bool",
                "@IROption.rec IRBlock (fun (_ : IROption IRBlock) => Bool) Bool.false "
                "(fun (b : IRBlock) => ir_fetch_n_ret (ir_nodes_get (ir_block_nodes b) pc)) ob")


def k_fetch_f_ret() -> str:
    return defn("ir_fetch_f_ret", "(bl : Nat) (pc : Nat) (of : IROption IRFunc)", "Bool",
                "@IROption.rec IRFunc (fun (_ : IROption IRFunc) => Bool) Bool.false "
                "(fun (fn : IRFunc) => ir_fetch_b_ret pc (ir_block_find (ir_func_blocks fn) bl)) of")


def cls_f_at(fr: str, m: str = "m") -> str:
    """The function-layer classifier at frame `fr`, spelled exactly as ir_step fetches."""
    return (f"(ir_fetch_f_ret (ir_frame_block {fr}) (ir_frame_pc {fr}) "
            f"(ir_func_find (ir_mod_funcs {m}) (ir_frame_func {fr})))")


def k_botret() -> str:
    body = ("@IRMachine.rec (fun (_ : IRMachine) => Bool) "
            "(fun (fs : IRList IRFrame) (_ : IRList IRMemSlot) (_ : Nat) => "
            "@IRList.rec IRFrame (fun (_ : IRList IRFrame) => Bool) Bool.false "
            f"(fun (f : IRFrame) (t : IRList IRFrame) (_ : Bool) => {frames_case(cls_f_at('f'), 't')[1:-1]}) fs) s")
    return defn("ir_stk_botret", "(m : IRModule) (s : IRMachine)", "Bool", body)


def k_pin(name: str, binders: str, lhs: str, rhs: str) -> str:
    return defn(name, binders, f"@Eq Bool {lhs} {rhs}", refl("Bool", rhs))


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
         "(ir_frames_is_nil (@IRList.cons IRFrame f t))", "Bool.false", "a cons is not nil, whatever its tail"),
        ("ir_inst_is_ret_ret", "(ids : IRList Nat)", "(ir_inst_is_ret (IRInst.ret ids))", "Bool.true",
         "the ret constructor is classified ret, at every operand list"),
        ("ir_inst_is_ret_call", "(fid : Nat) (args : IRList Nat)", "(ir_inst_is_ret (IRInst.call fid args))",
         "Bool.false", "a call is not a ret -- the negative polarity, at the constructor ir_call_push is about"),
        ("ir_stk_botret_nil", blk, f"(ir_stk_botret m {mk(NIL_F)})", "Bool.false",
         "the classifier is FALSE on the empty frame list -- which is why every theorem over it also takes "
         "the nonempty premise: the empty list is outside the commuting class but not a bottom ret"),
        ("ir_stk_botret_two", f"{blk} (f : IRFrame) (g : IRFrame) (t : IRList IRFrame)",
         f"(ir_stk_botret m {mk('(@IRList.cons IRFrame f (@IRList.cons IRFrame g t))')})", "Bool.false",
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
        return (f"@Eq Bool (ir_frames_is_nil {v}) Bool.false -> "
                f"@Eq IRConfig (ir_ret_to ds (ir_frames_app {v} rest) mem na vs) "
                f"(ir_config_stack (ir_ret_to ds {v} mem na vs) rest)")
    nil_goal = (f"@Eq IRConfig (ir_ret_to ds (ir_frames_app {NIL_F} rest) mem na vs) "
                f"(ir_config_stack (ir_ret_to ds {NIL_F} mem na vs) rest)")
    nil_minor = (f"(fun (h0 : @Eq Bool (ir_frames_is_nil {NIL_F}) Bool.false) => "
                 f"ir_bool_false_ne_true ({nil_goal}) (@Eq.symm Bool (ir_frames_is_nil {NIL_F}) Bool.false h0))")
    cons_minor = (f"(fun (g : IRFrame) (t2 : IRList IRFrame) (_ih : {mot('t2')}) "
                  f"(_ : @Eq Bool (ir_frames_is_nil (@IRList.cons IRFrame g t2)) Bool.false) => "
                  f"{refl('IRConfig', running(cons('(ir_frame_set_many g ds vs)', '(ir_frames_app t2 rest)')))})")
    body = f"@IRList.rec IRFrame (fun (t0 : IRList IRFrame) => {mot('t0')}) {nil_minor} {cons_minor} t h"
    binders = ("(ds : IRList Nat) (rest : IRList IRFrame) (mem : IRList IRMemSlot) (na : Nat) "
               "(vs : IRList IRScalar) (t : IRList IRFrame) "
               "(h : @Eq Bool (ir_frames_is_nil t) Bool.false)")
    ty = (f"@Eq IRConfig (ir_ret_to ds (ir_frames_app t rest) mem na vs) "
          f"(ir_config_stack (ir_ret_to ds t mem na vs) rest)")
    return defn("ir_stkn_ret_to", binders, ty, body)


def is_ret_rhs(rhs: str) -> bool:
    return rhs.startswith("ir_return_exec s ")


def stkn_arm_lemma(ctor: str, names: list[str], types: list[str], rhs: str) -> str:
    tpl = f"(ir_exec m {inst_app(ctor, names)} rs {{S}})"
    parts = ["(m : IRModule)", BLOCK, "(rs : IRList Nat)"]
    parts += [f"({n} : {ty})" for n, ty in zip(names, types)]
    if is_ret_rhs(rhs):
        parts.append("(ht : @Eq Bool (ir_frames_is_nil t) Bool.false)")
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
    goal_s = lambda s0: (f"@Eq IRConfig (ir_step m (ir_mach_stack {s0} rest)) "
                         f"(ir_config_stack (ir_step m {s0}) rest)")
    hc_s = lambda s0: f"@Eq Bool (ir_stk_botret m {s0}) Bool.false"
    mot_s = lambda s0: (f"@Eq Bool (ir_frames_is_nil (ir_mach_frames {s0})) Bool.false -> "
                        f"{hc_s(s0)} -> {goal_s(s0)}")
    mot_fs = lambda fs0: f"@Eq Bool (ir_frames_is_nil {fs0}) Bool.false -> {hc_s(mk(fs0))} -> {goal_s(mk(fs0))}"
    bl, pc, F, B, N, ND, I = _fetch_layers()

    def layer(step, cls):
        return lambda o: (f"{node_prem(cls(o))} -> "
                          f"@Eq IRConfig {step(S1, o)} (ir_config_stack {step(S0, o)} rest)")

    mot_f, mot_b, mot_n = layer(*F), layer(*B), layer(*N)
    mot_nd, mot_i = layer(*ND), layer(*I)

    def none_minor(cls, param: str, fault: str) -> str:
        none = "(@IROption.none " + param + ")"
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
    inst_rec = f"@IRInst.rec (fun (i0 : IRInst) => {mot_i('i0')}) {' '.join(inst_minors)} i"
    node_rec = f"@IRNode.rec (fun (n0 : IRNode) => {mot_nd('n0')}) (fun (i : IRInst) (rs : IRList Nat) => {inst_rec}) nd"
    n_scrut = f"(ir_nodes_get (ir_block_nodes bk) {pc})"
    n_rec = neutral_opt_rec("IRNode", "on", mot_n, none_minor(N[1], "IRNode", "fetch_past_end"),
                            ("nd", "IRNode"), node_rec, n_scrut, mot_n(n_scrut))
    b_scrut = f"(ir_block_find (ir_func_blocks fn) {bl})"
    b_rec = neutral_opt_rec("IRBlock", "ob", mot_b, none_minor(B[1], "IRBlock", "no_block"),
                            ("bk", "IRBlock"), n_rec, b_scrut, mot_b(b_scrut))
    f_scrut = "(ir_func_find (ir_mod_funcs m) (ir_frame_func f))"
    f_rec = neutral_opt_rec("IRFunc", "o", mot_f, none_minor(F[1], "IRFunc", "no_func"),
                            ("fn", "IRFunc"), b_rec, f_scrut, mot_f(f_scrut))
    nil_minor = (f"(fun (h : @Eq Bool (ir_frames_is_nil {NIL_F}) Bool.false) (_ : {hc_s(mk(NIL_F))}) => "
                 f"ir_bool_false_ne_true ({goal_s(mk(NIL_F))}) (@Eq.symm Bool (ir_frames_is_nil {NIL_F}) Bool.false h))")
    cons_minor = (f"(fun (f : IRFrame) (t : IRList IRFrame) (_ih : {mot_fs('t')}) "
                  f"(_ : @Eq Bool (ir_frames_is_nil (@IRList.cons IRFrame f t)) Bool.false) => {f_rec})")
    list_rec = f"@IRList.rec IRFrame (fun (fs0 : IRList IRFrame) => {mot_fs('fs0')}) {nil_minor} {cons_minor} fs"
    body = (f"@IRMachine.rec (fun (s0 : IRMachine) => {mot_s('s0')}) "
            f"(fun (fs : IRList IRFrame) (mem : IRList IRMemSlot) (na : Nat) => {list_rec}) s hne hc")
    binders = ("(m : IRModule) (s : IRMachine) (rest : IRList IRFrame) "
               "(hne : @Eq Bool (ir_frames_is_nil (ir_mach_frames s)) Bool.false) "
               "(hc : @Eq Bool (ir_stk_botret m s) Bool.false)")
    return defn("ir_stkn_step", binders, goal_s("s"), body)


def g_botret_false_of_running() -> str:
    mk = lambda fs: f"(IRMachine.mk {fs} mem na)"
    run = lambda c: f"@Eq Bool (ir_stk_running {c}) Bool.true"
    mot_s = lambda s0: f"{run('(ir_step m ' + s0 + ')')} -> @Eq Bool (ir_stk_botret m {s0}) Bool.false"
    mot_fs = lambda fs0: mot_s(mk(fs0))
    S0n = mk(cons("f", NIL_F))
    bl, pc, F, B, N, ND, I = _fetch_layers()

    def layer(step, cls):
        return lambda o: f"{run(step(S0n, o))} -> @Eq Bool {cls(o)} Bool.false"

    mot_f, mot_b, mot_n = layer(*F), layer(*B), layer(*N)
    mot_nd, mot_i = layer(*ND), layer(*I)

    def none_minor(step, cls, param: str) -> str:
        none = f"(@IROption.none {param})"
        return (f"fun (h : {run(step(S0n, none))}) => "
                f"ir_bool_false_ne_true (@Eq Bool {cls(none)} Bool.false) h")

    inst_minors = []
    for ctor, names, types, rhs in ARMS:
        fields = " ".join(f"({n} : {ty})" for n, ty in zip(names, types))
        prem = run(I[0](S0n, inst_app(ctor, names)))
        concl = f"@Eq Bool {I[1](inst_app(ctor, names))} Bool.false"
        lead = f"fun {fields + ' ' if fields else ''}"
        if is_ret_rhs(rhs):
            inst_minors.append(f"({lead}(h : {prem}) => ir_bool_false_ne_true ({concl}) h)")
        else:
            inst_minors.append(f"({lead}(_ : {prem}) => {refl('Bool', 'Bool.false')})")
    inst_rec = f"@IRInst.rec (fun (i0 : IRInst) => {mot_i('i0')}) {' '.join(inst_minors)} i"
    node_rec = f"@IRNode.rec (fun (n0 : IRNode) => {mot_nd('n0')}) (fun (i : IRInst) (rs : IRList Nat) => {inst_rec}) nd"
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
        return f"{run(step)} -> @Eq Bool {frames_case(cls_f_at('f'), t0)} Bool.false"

    step_two = "(ir_step m " + mk(cons("f", cons("g", "t2"))) + ")"
    t_cons = (f"(fun (g : IRFrame) (t2 : IRList IRFrame) (_ih : {t_mot('t2')}) "
              f"(_ : {run(step_two)}) => {refl('Bool', 'Bool.false')})")
    t_rec = f"@IRList.rec IRFrame (fun (t0 : IRList IRFrame) => {t_mot('t0')}) ({f_rec}) {t_cons} t"
    step_nil = "(ir_step m " + mk(NIL_F) + ")"
    nil_minor = f"(fun (_ : {run(step_nil)}) => {refl('Bool', 'Bool.false')})"
    cons_minor = f"(fun (f : IRFrame) (t : IRList IRFrame) (_ih : {mot_fs('t')}) => {t_rec})"
    list_rec = f"@IRList.rec IRFrame (fun (fs0 : IRList IRFrame) => {mot_fs('fs0')}) {nil_minor} {cons_minor} fs"
    body = (f"@IRMachine.rec (fun (s0 : IRMachine) => {mot_s('s0')}) "
            f"(fun (fs : IRList IRFrame) (mem : IRList IRMemSlot) (na : Nat) => {list_rec}) s hrun")
    binders = f"(m : IRModule) (s : IRMachine) (hrun : {run('(ir_step m s)')})"
    return defn("ir_stk_botret_false_of_running", binders, "@Eq Bool (ir_stk_botret m s) Bool.false", body)


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
    return f"(@IROption.rec {param} {mot} {none} {some} {major})"


def v_view_word() -> str:
    """ir_view_word respects a pointwise-equal payload view (one IREnc.rec)."""
    goal = lambda e: f"@Eq IRScalar (ir_view_word r0 {e} v) (ir_view_word r1 {e} v)"
    cong = lambda img, args: (f"ir_eq_cong IRScalar IRScalar (fun (x : IRScalar) => {img} x {args} v) "
                              f"(r0 p v) (r1 p v) (h p v)")
    body = (f"@IREnc.rec (fun (e0 : IREnc) => {goal('e0')}) "
            f"(fun (k : Nat) (no : Nat) (so : Nat) (p : IRTy) => {cong('ir_niche_image', 'no so')}) "
            f"(fun (k : Nat) (i : Nat) (c : Nat) (p : IRTy) => {cong('ir_wrap_image', 'i c')}) e")
    binders = (f"(r0 : {VIEW_FN}) (r1 : {VIEW_FN}) "
               f"(h : forall (p : IRTy) (v : IRScalar), @Eq IRScalar (r0 p v) (r1 p v)) (e : IREnc) (v : IRScalar)")
    return defn("ir_enc_agree_view_word", binders, goal("e"), body)


def v_view_ty() -> str:
    """The view at every fuel agrees when the two tables find every row alike."""
    stmt = lambda n: (f"forall (t : IRTy) (v : IRScalar), "
                      f"@Eq IRScalar (ir_view_ty es0 {n} t v) (ir_view_ty es {n} t v)")
    word = lambda tbl: f"(fun (e : IREnc) => ir_view_word (ir_view_ty {tbl} k) e v)"
    opt = lambda word_tbl, major: _ir_opt_rec("IREnc", "IRScalar", "v", word(word_tbl), major)
    mid = opt("es0", "(ir_enc_find es t)")
    cong1 = (f"ir_eq_cong (IROption IREnc) IRScalar (fun (o : IROption IREnc) => {opt('es0', 'o')}) "
             f"(ir_enc_find es0 t) (ir_enc_find es t) (henc t)")
    rec2 = _ir_opt_rec(
        "IREnc", "", "(@Eq.refl IRScalar v)",
        f"(fun (e : IREnc) => ir_enc_agree_view_word (ir_view_ty es0 k) (ir_view_ty es k) ih e v)",
        "(ir_enc_find es t)",
        motive=f"(fun (o : IROption IREnc) => @Eq IRScalar {opt('es0', 'o')} {opt('es', 'o')})")
    succ = (f"(fun (k : Nat) (ih : {stmt('k')}) => fun (t : IRTy) (v : IRScalar) => "
            f"@Eq.trans IRScalar (ir_view_ty es0 (Nat.succ k) t v) {mid} (ir_view_ty es (Nat.succ k) t v) "
            f"({cong1}) ({rec2}))")
    body = (f"@Nat.rec (fun (n0 : Nat) => {stmt('n0')}) "
            f"(fun (t : IRTy) (v : IRScalar) => @Eq.refl IRScalar v) {succ} n")
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
    word = f"@Eq.trans IRScalar {a} {b} {c} ({w1}) ({w2})"
    result_e = (f"@IRStepResult.rec (fun (r0 : IRStepResult) => "
                f"@Eq IRStepResult (ir_view_result es0 e r0) (ir_view_result es e r0)) "
                f"(fun (v : IRScalar) => ir_eq_cong IRScalar IRStepResult (fun (x : IRScalar) => IRStepResult.value x) "
                f"{a} {c} ({word})) "
                f"(fun (o : IROutcome) => @Eq.refl IRStepResult (IRStepResult.fault o)) r")
    rec2 = _ir_opt_rec(
        "IREnc", "", "(@Eq.refl IRStepResult r)", f"(fun (e : IREnc) => {result_e})", "(ir_enc_find es t)",
        motive=f"(fun (o : IROption IREnc) => @Eq IRStepResult {opt('es0', 'o')} {opt('es', 'o')})")
    body = (f"@Eq.trans IRStepResult (ir_load_view es0 t r) {mid} (ir_load_view es t r) "
            f"({cong1}) ({rec2})")
    binders = f"{ENC_TBL} {PREMISE['he']} {PREMISE['hl']} (t : IRTy) (r : IRStepResult)"
    return defn("ir_enc_agree_load_view", binders, "@Eq IRStepResult (ir_load_view es0 t r) (ir_load_view es t r)", body)


def v_mext_run() -> str:
    """ir_mext_run's mkv form: a run reaching a RUNNING configuration in M0 reaches it in M."""
    s0 = f"(ir_steps k {MV0} c)"
    s1 = f"(ir_steps k {MV1} c)"
    run2 = "(IRConfig.running s2)"
    back = (f"@Eq.subst IRConfig (fun (c1 : IRConfig) => @Eq Bool (ir_stk_running c1) Bool.true) {run2} {s0} "
            f"(@Eq.symm IRConfig {s0} {run2} hrun) (@Eq.refl Bool Bool.true)")
    body = (f"@Eq.trans IRConfig {s1} {s0} {run2} "
            f"(@Eq.symm IRConfig {s0} {s1} (ir_mextv_steps {MVARGS} hf hg henc hlen k c ({back}))) hrun")
    binders = (f"{MVBLOCK} {PREMISE['hf']} {PREMISE['hg']} {PREMISE['he']} {PREMISE['hl']} "
               f"(k : Nat) (c : IRConfig) (s2 : IRMachine) (hrun : @Eq IRConfig {s0} {run2})")
    return defn("ir_mextv_run", binders, f"@Eq IRConfig {s1} {run2}", body)


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
    "SRC_ADVANCE_SET_MEM_STACK": "2816beb45bc2d30174960c764772c7e6d3e26926c7bc3d46ed306be6ab911dfe",
    "SRC_ADVANCE_STACK": "18fe77c79d1d0dc3bc62f7c6c3945e89c548f5116e6242c0b83ecdf6fe35d9d1",
    "SRC_ALLOCA_EXEC_STACK": "2a835dfebffe6d091d66d8b12ac0d31083b0fd1ed6084d19041fcdec4673017a",
    "SRC_ALLOCA_K_STACK": "6784b8577fcc13662b0f355ab621344eb3cea6af8315198adbeea805c40073ca",
    "SRC_ASSERT_B_STACK": "37dd7847a2920d40912ba02f50b5cca9372bd08e6e81f1b11e1287d073e75d0c",
    "SRC_ASSERT_EXEC_STACK": "788d46435c6f299ab55681b70a7f0f066c6032627d7e2ba0f93395345aafa158",
    "SRC_BIND2_STACK": "d3d6a67a6cf76c33be86a55e76f5e2cd4f180f70123a7baed52d633d89bbf0b2",
    "SRC_BIND_RESULT_STACK": "0f5fee56555c301721721579b43255265e9277e29a26cb3957bdaa19942867c4",
    "SRC_BIND_STACK": "ab8c6ee7483cf4bdf2c1c00d99ebfeddf756531498b5ac308728aa03d55c5f0b",
    "SRC_CALLIND_EXEC_STACK": "864be03e15a73b0e9c499b7d38e6363b42c5aafdf3a7ce20e4fa590e611f652e",
    "SRC_CALL_EXEC_STACK": "0fbb342c0a17404d203d9d618b399f0661cd777bc418249628233e47b14fa5df",
    "SRC_CONDBR_B_STACK": "3c9c1a790327ce86e151e0d02a082d056757657d5ddf4d261b3122a12b06f0b3",
    "SRC_CONDBR_EXEC_STACK": "40ca638fac84d901feef7f699d275aca29d88df59f37019be104c8b7ced1d9d0",
    "SRC_ENC_AGREE_LOAD_VIEW": "a03f656ea70fa5b4ab0451fd698a1c0cd8651725f4671170ea53223ad457630b",
    "SRC_ENC_AGREE_VIEW_TY": "c14ad29de326c7ecf046f29602c2af772684b8606aba2bbb621a9a11521d70c5",
    "SRC_ENC_AGREE_VIEW_WORD": "32a9a3d442653ec38dc416fbaab01b41d7c8db585d53c5c7f5679e53e026d77d",
    "SRC_FETCH_B_RET": "fbd13e072a41e6dcd378f20850e5f870c860eec1d0735471cb76dc7880679bd1",
    "SRC_FETCH_F_RET": "2cf2b643b331a98ec23ebde683e7eccd0fade64a0263776097753188333f4da5",
    "SRC_FETCH_N_RET": "a85c7b1aa5784d437b7ff68e7f9b8aa7eb30dcacb9ef6774b74c56079fc4988d",
    "SRC_FRAMES_IS_NIL": "c1d7471d679a474052d2fdb017fb37daa043ac17bfbc47e0d057fc88f0017e78",
    "SRC_FRAMES_IS_NIL_CONS": "779d8f6cba8f2bcb17bbffd0a4075ce6417dfa02e41d30f533ae21dd823ca50f",
    "SRC_FRAMES_IS_NIL_NIL": "c3acd8a8b6e6130189d40a47fc9bd9305261714ff1327d392a93ee4a10bfe87e",
    "SRC_GETD_STACK": "cc47a72eb17d4d6f729ce0dda6014fe4943b73ce0297bb6fd8a044437ac3a671",
    "SRC_GOTO_STACK": "9c36a3a64d25c9aadfd8346f4302a528ebb8ef15617891b15fff6f61e40947dd",
    "SRC_INST_IS_RET": "b842502d3046c67d6576320002ea64a57ff26098fd0514c9693d263ffa605896",
    "SRC_INST_IS_RET_CALL": "eff8746447361bed7a0c3b4acf570d88235d2d806538b3106d714fd4a934fab5",
    "SRC_INST_IS_RET_RET": "78b39c537e236b4c82965b0dd18ed1e5e8a2d1c78541c7220401c5742d9c4a5c",
    "SRC_JUMP_BLOCK_STACK": "b0390503225b64f72f9c9c95c704ac9c6b71b80bf3965aa1b6268d3120b08264",
    "SRC_JUMP_FUNC_STACK": "47515c352a75f6290b8636c7ac79e9e561a01edf4c541af8f574f86feed175de",
    "SRC_JUMP_STACK": "e195d38ed2d76580b233da242ac35207d0f91f182eec7d61f4df8f2a77a3949a",
    "SRC_MACH_MEM_STACK": "b5a462d154349d1fd801bcc545d8f187d545808205e10361ee835a285f9e2b01",
    "SRC_MEXTV_ARM_ALLOCA": "11a161328f29ce8d2855c0ab60f62f2bd55450a37d1a6d320566a5afef736a8e",
    "SRC_MEXTV_ARM_ASSERT": "8f7ac3d3733dc0ce7b30c4e19f7033908b74e641a2932282fa246768cc2bd950",
    "SRC_MEXTV_ARM_ATOMIC_FETCH_ADD_RELAXED_U64_SEQ": "5c3ecde5eff6b799991d8daf5f4e81d60a0b90ca006c433ed2291eb979572e31",
    "SRC_MEXTV_ARM_ATOMIC_FETCH_ADD_RELAXED_USIZE_SEQ": "56d72ecd7da30bf6ca173a6d0d5d702a1e8e4876413d4037cc62870c6121fedb",
    "SRC_MEXTV_ARM_BINOP": "1660ac86ac9bea5685e0ce62cdae79b21d6576bbc01d7507a28e2a33b018d1f6",
    "SRC_MEXTV_ARM_BORROW": "f546ebfc8063c577b558afca46cd5f55f6ded14d09825ab1ce129e05bb783755",
    "SRC_MEXTV_ARM_BR": "46a6959aa571fadefd42af84d133ada9d5dfa54aa5b15d7b8abbd0ae96d492e4",
    "SRC_MEXTV_ARM_CALL": "6b30938623e2b25f9be26ac97bca5539951f4ad1d17ee4aaf19a8336df3c9b37",
    "SRC_MEXTV_ARM_CALLINDIRECT": "2db9fdc521711acd1eac5213cf4a339a1036dc95b61401b6ac59efde36e894d8",
    "SRC_MEXTV_ARM_CAST": "c93af6f4b9aefed78c51fdf8869baa462e50d6adbbe1135d97a52ad23bc7952a",
    "SRC_MEXTV_ARM_CONDBR": "7ecc8279d41a6ab0a64f378f97520479b2753b568a715dd1ad1aa4092ba409e3",
    "SRC_MEXTV_ARM_CONST_": "455c6845872048e66a9b1e10b6a150cbc912ff5964de8fbefbdd1f63b37ab27e",
    "SRC_MEXTV_ARM_COPY": "dd92b5e5866342eaba1b936abb1799ab0b704d541a6ad52f55c064fe976b9988",
    "SRC_MEXTV_ARM_EXTRACTELEMENT": "dea33e9f19b5501eef8aac52dd41dcf41d01fe0e07b0fd352d96d5b85687ec1b",
    "SRC_MEXTV_ARM_EXTRACTFIELD": "b581b96126fca31019789fc24d31921ec8b0e9ddbdb30463083ff320c3f0b772",
    "SRC_MEXTV_ARM_FCMP": "8a8a18b04273d5d1c20d2d0fff2f3dd3d2f9309a00ac0e1da5f1975a06286774",
    "SRC_MEXTV_ARM_GEP": "c35623c48a2b126690381cef9a6468581c31824802a8dbd0d151eef17cf637b6",
    "SRC_MEXTV_ARM_GLOBALADDR": "16c508b903bc20db42546faece72da152e806778ff97e3f58562f9ea6dad339d",
    "SRC_MEXTV_ARM_ICMP": "4bca29cbb12717396355beb27d551e114ed8d6f56a01b7653a922cde830b3ae4",
    "SRC_MEXTV_ARM_INSERTFIELD": "8757becb210f354b1436aa8caa74c9379a4b47c97899e4e987a58d39a2ea1161",
    "SRC_MEXTV_ARM_LOAD": "69b704e9ea58c0f8bd05ed540d45eca71e456b0da67d33f67242e3140b890476",
    "SRC_MEXTV_ARM_OVERFLOW": "c059c849c881efbbc336bb0aaa067446a63e05d4f428a861d99888b4375545e1",
    "SRC_MEXTV_ARM_PTRDATA": "cbb75bdce8fe367b51e555cc8772301e6d5687387bd756828e24851860156164",
    "SRC_MEXTV_ARM_PTRFROMPARTS": "e1c2154c06a9b033b07dc8dba25f24e5a0c66ec974362c5fd703d892abf716a1",
    "SRC_MEXTV_ARM_PTRMETADATA": "79f8578ad3f5e5648664e3a488769ad94161067a72a9db0eb85028728b187076",
    "SRC_MEXTV_ARM_RELEASE": "26893bf78c142c5cce9216084a263a653b7d52f2c5b24376b0447acf5acc5768",
    "SRC_MEXTV_ARM_RET": "89c2f72c2b84194f21cf7ba2f216820b1ce61a112af4a54bbb7b9c14a398b0b2",
    "SRC_MEXTV_ARM_SELECT": "2ea10d029303f3306bbfc9ac42bf6a82696f49f314c798cbe6e9fa5050edbeb9",
    "SRC_MEXTV_ARM_STORE": "a3bb716d774bfd38c9728e166f67d646acd701b283368a269a8d71b36cca0214",
    "SRC_MEXTV_ARM_SWITCH": "d7008ee1d16c3a0a7e0dfb95ea33976e0c3b1cd853431c43fd47342c31d14404",
    "SRC_MEXTV_ARM_UNDEF": "99e76f631bcc4d27b4bdc39fbd8e68d703484ce967de2c8645fb139985a6b2e5",
    "SRC_MEXTV_ARM_UNOP": "7468e753303b69f85175b7438bf8b24503aa7a8a2eb5c1d3b6048a5d9140d01d",
    "SRC_MEXTV_ARM_UNREACHABLE": "cd30d014a9656a242009166838a8ff7356bcfe5153c50003d4714b3672f6c380",
    "SRC_MEXTV_CALLIND_EXEC": "c459c1e929289d9db3bb9945c958df235bf56e9ce1186557f23677126e2ab0f6",
    "SRC_MEXTV_CALL_EXEC": "739f8f9d147494cb17f19702333c769a8021aa21a5d7df4680495a39dd116bdc",
    "SRC_MEXTV_CONDBR_B": "f22f7f36bcabd730eea1e6c451d6b495937fe87e834c27b5f21a928728ee1cec",
    "SRC_MEXTV_CONDBR_EXEC": "d325f6273744db01924672bf5387ba5bb27e9bb8fdb5de6e129ec2c34ca600bd",
    "SRC_MEXTV_GLOBALADDR": "d2afde4389939fb0072099bd4c5ceda17ec179eba55496416961f94bd459db33",
    "SRC_MEXTV_JUMP": "37739e72badcd1bdeaf0f6c53fae3e8b9756adb14efe4d097db72fb1384f422c",
    "SRC_MEXTV_RUN": "74bd5c54fa1b1071185797a1c2d3540f7ae94aacf4b0a67d073d725e22e386f0",
    "SRC_MEXTV_STEP": "2a820104b76e9a872eb0d3f839ed785deb637968a7aa03ad0d95cf09bc0b87c0",
    "SRC_MEXTV_STEPS": "f248cee1641e66d715869b46d8f26645e442b5c5b7cb9ee07a4c1a43fea854e3",
    "SRC_MEXTV_SWITCH_EXEC": "bf3172d6147fc6db6319aab4b70e83c5feff96b0d057b1eebc44a4eb655da74c",
    "SRC_MEXTV_SWITCH_N": "2f4e495b185f4f3a2d5fdb04314200a9ea69fb097dbb12a8565b7d4bedc04a35",
    "SRC_MEXT_ARM_ALLOCA": "6d46a29f277cd3f6bf4e7eb77de8c95bda3c8d0078386756c06e2ba197209769",
    "SRC_MEXT_ARM_ASSERT": "077d71dab110c62451b5f176e895542d88f74b07475eb934930ef47dbb3aae29",
    "SRC_MEXT_ARM_ATOMIC_FETCH_ADD_RELAXED_U64_SEQ": "22a06158ae3e6fd554847347b347be234948e69e7b63911aaa0d1e0bea80f868",
    "SRC_MEXT_ARM_ATOMIC_FETCH_ADD_RELAXED_USIZE_SEQ": "ceee576937da3ff851a3539ef5360148e868982c084acdfb631374a79563c36d",
    "SRC_MEXT_ARM_BINOP": "1a1241d80f643b136b5aa009261196cce688ad1f3142441dffbc46bd572e0678",
    "SRC_MEXT_ARM_BORROW": "4aa661bf303510493eb98096024e54e475e855158c6e3d500f85a896c6df89c9",
    "SRC_MEXT_ARM_BR": "1093ba3ee841a4a6fec69214e54beb9dddb4d6080242d9077b6c34989d89c031",
    "SRC_MEXT_ARM_CALL": "0a6b18940fe80f2d551e1e6380e3b16d61470eeed4a77fdb7dc11b37d03c3ae2",
    "SRC_MEXT_ARM_CALLINDIRECT": "1677564faa9d02951f086bcfa5fe904fd2ff5d287cacb33f1ff6501220534fa8",
    "SRC_MEXT_ARM_CAST": "bd503e8d064e76c4fa66a24a2db17dc2165f5ef7aa5ea3967cff4cf8dcbd1b1b",
    "SRC_MEXT_ARM_CONDBR": "91a439f9effe5630d5e76de9af75a4ff7502c053927ffc4e83c317973685de74",
    "SRC_MEXT_ARM_CONST_": "05948f6a070a4ae05c458d337143420737bb5fbf777896416e61d8a21c772048",
    "SRC_MEXT_ARM_COPY": "eb21ebecb8cfed15313f242756b3f52423560f6e16f36c6c7d59befaf0626796",
    "SRC_MEXT_ARM_EXTRACTELEMENT": "996c7fe346fa8fbee8dd4ad41e4916011837afaf0138191573c1f6eb002c30ae",
    "SRC_MEXT_ARM_EXTRACTFIELD": "fa2632d44e1a83d365329f8adee6cf65ffd76966a7742b5a14f56ad53b91cff6",
    "SRC_MEXT_ARM_FCMP": "2b47bc70a0c0cdb3522d3cffc558278a947d0d62920604b9c3be6f5d1f554c5a",
    "SRC_MEXT_ARM_GEP": "f16aca0f81c2101c32fee989476caf59e2d79eee6e023c2e7aafcf25ceeab6e5",
    "SRC_MEXT_ARM_GLOBALADDR": "d24a39bdf95fd503d4fbe5ad0e7420fed784dbfb72c088e4150ad9b5515a4eec",
    "SRC_MEXT_ARM_ICMP": "49c1b612169b77ed3ac5711a4bef21918c35ae07eafa2992fe4f97391a5f4ebd",
    "SRC_MEXT_ARM_INSERTFIELD": "e9e5df18f519040b854b408e2997f35e19768c0f29344663a998cd3e75f7b81b",
    "SRC_MEXT_ARM_LOAD": "867bdb650bea5c6a79d9bd57ab0767b4542a63a5f883e15b51ff83428b9b9219",
    "SRC_MEXT_ARM_OVERFLOW": "6b9ce801f802dc1bd3f3f371ee06644027a311b0a868c4e55d8223f6edc88bcd",
    "SRC_MEXT_ARM_PTRDATA": "51d84eb446c26a93998c716264af08622704dfdc0a18c85280b726ea60de5c58",
    "SRC_MEXT_ARM_PTRFROMPARTS": "c00897414702de0b2a2b1c5b34212cd8177056cd7e8681c2b739bc0d45e261c2",
    "SRC_MEXT_ARM_PTRMETADATA": "ac7f37c57d03f7ec41788710b4eb856a690f83c34503102bb17b25434fbed015",
    "SRC_MEXT_ARM_RELEASE": "49bb23e4d18d8478357474030ede7b5fd665e64a3d8a7204a9d224627a0d35fb",
    "SRC_MEXT_ARM_RET": "b82c50024475e7bffa24be00d6ab89aec09ae300df78c396ba254c544976f47b",
    "SRC_MEXT_ARM_SELECT": "61e3f789773971430a21bc1b20f68e96195516db47842456bda7cf47692fedb8",
    "SRC_MEXT_ARM_STORE": "94f4981cac2f581952fedff6dc648840dcac5ada222b291bf4508636bbe6c2b4",
    "SRC_MEXT_ARM_SWITCH": "6e2b37ea523400312e1edc373cbc82171e9d3b5b01e212a0a4b8c2e3bf96e9a0",
    "SRC_MEXT_ARM_UNDEF": "2e87b1d704c24d17b77be4f4b374ff5b2362b0bd30a3f7048d38c424709d6423",
    "SRC_MEXT_ARM_UNOP": "51b823c77193ae023f760eb55e2538387908e9324f686a5508bdc51ddd2ef714",
    "SRC_MEXT_ARM_UNREACHABLE": "04eea04ebc6bed073f32d55a8c125c775d7be6c6d5f8b870c8b43e7f4c616a2b",
    "SRC_MEXT_CALLIND_EXEC": "96ce2c2e5d41fbab54775b0b4722cf7167a994e4f7a94691b27d5182fc50f09c",
    "SRC_MEXT_CALL_EXEC": "64118be620d12ac81b4dc5ec52d5e241bc7ec3e5b99f1774d75c305735848fed",
    "SRC_MEXT_CONDBR_B": "ae7f5c4c8cb55297776993d5b46b62c9b5253286684fc51f610614c4bc596ef3",
    "SRC_MEXT_CONDBR_EXEC": "4f4062ed67fb585dc8ebe720c19995ebadb85897e3c552569fe563d677a29c8b",
    "SRC_MEXT_GLOBALADDR": "e8c95895698588022c4ec75a8e4c7bb7de4edddbfdcd207c536818813eea3f09",
    "SRC_MEXT_JUMP": "e234bebb7d6678c7f80f7bf7faa89b7f9fc905d9526df60f8be1e753b1d89486",
    "SRC_MEXT_STEP": "8dcdc64732c0a7cde8086179a34f0e116edc6421113a7c289a68bc34ea5a5dba",
    "SRC_MEXT_STEPS": "64eb6c5ba3be660567055ade99a4ce93cb8415e3d3bf76d10b49689d89656dd9",
    "SRC_MEXT_SWITCH_EXEC": "b5a943c8f3a72bfdb2a66556172f30750f0307cfb4f0a10627d76547c601eda2",
    "SRC_MEXT_SWITCH_N": "eddc12eb63cb6ca78dfade0d4ebe9d726e0afb7e5b392c8a30dd841354d3237f",
    "SRC_NODE_IS_RET": "6ac47e6b66dc0f6be46b2eed0ca42dbd5d3a31bfc6cad4cd6e29148aa84c3d75",
    "SRC_OVERFLOW_EXEC_STACK": "a57c72c977e72013c46724103165e2ae80546a27417de76185fa17f9b6a473da",
    "SRC_OVERFLOW_INTS_STACK": "0d131e528fdf851998ec7f02b11c4070e030b91238487672887e0c286e7e8dd2",
    "SRC_OVERFLOW_VALS_STACK": "adfd72415ffbfd4a325b293ff0a5ab89f3ffc28e47b08fd321b79fee936250f1",
    "SRC_PUSH_STACK": "283851d73f2aaffc290bd67ecd8658337a8ad1982c35f5bd738f405fe42adf01",
    "SRC_RESOLVE_STACK": "daf922bc1cc7c583b912cdc6d26d791d2c38fe416aa48a666a67c1c70f338d59",
    "SRC_RET_TO_STACK": "07795400639f958d203769ffbf0f7f03a85b0ef61f99cc0a4359edbb41de0eb6",
    "SRC_STKN_ARM_ALLOCA": "29443e5b63eaf889faa7afd7a92352f390db5f3e58373bb3204e110150f8d99a",
    "SRC_STKN_ARM_ASSERT": "fc9fa31160e0a8d6056b9e6adc721e3be0d3a07bc0ea5a9d78dee2b45cad0abc",
    "SRC_STKN_ARM_ATOMIC_FETCH_ADD_RELAXED_U64_SEQ": "c338e2e6e1b4b6e4188fca451d566b1ea519f3e6e690d8d0295b1bf8bc89fb5a",
    "SRC_STKN_ARM_ATOMIC_FETCH_ADD_RELAXED_USIZE_SEQ": "e43c6e00e03fee6cd18ea8eb9081cfbea0cf1004082c81fd7d1a76ed186ded12",
    "SRC_STKN_ARM_BINOP": "bfc160093213a2e4ee8346e10c419937bdbd76151d0a583eabc57d02864aecac",
    "SRC_STKN_ARM_BORROW": "0f336562abb23d8846e63479abf6d8c48da1d6bca08ab209657577d80e36defd",
    "SRC_STKN_ARM_BR": "146a3969df2b615f88f4c6de4f79e148412fa378e59b5467b6a72ea8b2c15c2d",
    "SRC_STKN_ARM_CALL": "a7b047c3eaae826f51b6a7654867c7910c3008069f3e05572b5273a3a24d9834",
    "SRC_STKN_ARM_CALLINDIRECT": "7640000f6e505ec236adc9e21502b1e00706edbdd6a931f52b272f2d883c4388",
    "SRC_STKN_ARM_CAST": "8e1bbec472e699d986b2d6b75fe428cb3baed697f879f18760631847485f0fa2",
    "SRC_STKN_ARM_CONDBR": "9eb75e42906d4f161b1323dbbdd507b50b8ad339e343d30494704e27e01a125c",
    "SRC_STKN_ARM_CONST_": "f173cfaa3406b379b0c478a93ce81d4daa8f55c18f42625132247b2199808bf9",
    "SRC_STKN_ARM_COPY": "9f31e9d47c78dbbef7fbc24071fec423882ac84320e02956ca0d4954d486d029",
    "SRC_STKN_ARM_EXTRACTELEMENT": "1ffca1b190496cf738c0084afd08f0616e0169be119ccfa88fbde7bc57b6a22f",
    "SRC_STKN_ARM_EXTRACTFIELD": "973c9a66a95911963719db4da84eede8e4c0227fbe4c67a79119b4613af3b010",
    "SRC_STKN_ARM_FCMP": "2c215ce20631145b8f9aa144396c1946967c553f5f8d5cf9fb9b64fd4ba24bed",
    "SRC_STKN_ARM_GEP": "c345d56821632e26eca7c59d88dc57cabf86e12c17376fb9e8bfb6779ac01e25",
    "SRC_STKN_ARM_GLOBALADDR": "af5adfedef744c499fe917785b80013f532e4fbb709c86592e950b9713292f02",
    "SRC_STKN_ARM_ICMP": "5d1d7401a60544ca35c92959902ef03762f48ae850855d83ca1a07fee28ad568",
    "SRC_STKN_ARM_INSERTFIELD": "3f591f09bbda76eaf68a0f99f8009cc9caff5ac5abcea2fb3c87cd07f84254d7",
    "SRC_STKN_ARM_LOAD": "747b0c42589b1a0243211329db32eddc310cfdcc40feb8b4c5a3f7a47f93b853",
    "SRC_STKN_ARM_OVERFLOW": "593b402b516218a50f13fe272d5e1f4a8d972809ca5ae8cc1c8f81304136776f",
    "SRC_STKN_ARM_PTRDATA": "a92e132649f4ef6506aa147ba2b358ef8fbaa352786099096066753631ec08cd",
    "SRC_STKN_ARM_PTRFROMPARTS": "533e679fde6a9348416677d37584948d4cd1a11a5b643088a1b49d6a0892270f",
    "SRC_STKN_ARM_PTRMETADATA": "4b336101f5bc5f0c4b1c93a3035eaf9178ac6a59ebcad2e3976650e8a6028161",
    "SRC_STKN_ARM_RELEASE": "5f52b6dd52264bf466d90921903dda700ce8448e9056d01aadc2f579b4557687",
    "SRC_STKN_ARM_RET": "9b5ec8b4c1c90ce4f57cc834c4aeec40b289cb3c2b3b8856ebc759cfb7579383",
    "SRC_STKN_ARM_SELECT": "5a9cb9ca968acede06ee3d2cb1fad0c71a0cbd510711490120e18779359c26de",
    "SRC_STKN_ARM_STORE": "994371593e090bb3e0c1d1b569f76724db318654b29d08b3716de6e377aaceb6",
    "SRC_STKN_ARM_SWITCH": "c91aa990b8e1fe52b4817f989fdf1b6b2a54b4c09961a2d6e93a8f10529cf678",
    "SRC_STKN_ARM_UNDEF": "78033ec8deeea05d04f36748e27160c82d1960935cd573f931b6a57d836d748f",
    "SRC_STKN_ARM_UNOP": "0063da1b555c028d7788f73dbabc3f29cd8cefa4ffeb49e596288a07c629090a",
    "SRC_STKN_ARM_UNREACHABLE": "a52b1aa15155fff6bce45eadfb5c10b794b9982962727c091fa89431b97d81e1",
    "SRC_STKN_RET_TO": "67f4543a11340b2e363ba6d1e08f7b5227aee289ddb5c91a69123708706b55e7",
    "SRC_STKN_STEP": "ca3ca591af80ef2e5d2ce10e7ab4d3be0bc6c6f640981737106ed6bee1b93ba5",
    "SRC_STK_ARM_ALLOCA": "82c2668881fb6215b767be852960f047a58807a548933c153cb5752dbf0d8b55",
    "SRC_STK_ARM_ASSERT": "19cd21084ffe35ac1c29d241cb74c417bbb688c639550304db282dfc8965282a",
    "SRC_STK_ARM_ATOMIC_FETCH_ADD_RELAXED_U64_SEQ": "84f7dbbe6ef08a00bff684b7e6d442f74090b679b3a261635de12806e9b7a29e",
    "SRC_STK_ARM_ATOMIC_FETCH_ADD_RELAXED_USIZE_SEQ": "45022bcef6feb5dd6d63902c576540b6c806fad6011c172dec78ab0357ab1ebc",
    "SRC_STK_ARM_BINOP": "62ebe6cfb7c68d85b064634f2f9f811d28dcc2c09309e834cf460dc9d2756035",
    "SRC_STK_ARM_BORROW": "b7c02ea24bac83d268387ec40a2573b14439cd32fd0a8359ed0e0500adb75127",
    "SRC_STK_ARM_BR": "d12fa02a46678ccde7f3c15b562f24cb3fc63edc8d2335a159b99d21e7cecadb",
    "SRC_STK_ARM_CALL": "e205c1493dedce22a9a2601ff19632783512d7a42b27daf4c81ec35c1afcfdb1",
    "SRC_STK_ARM_CALLINDIRECT": "1e41bc1a54209218184311651b53a9a1712e11bd5f70c369ad4c30c1f852a9df",
    "SRC_STK_ARM_CAST": "2022cc53e4e131ef98fd2227fb92bf1ab0e16460fad969226ac82d00244b4546",
    "SRC_STK_ARM_CONDBR": "31a4ce4ba6695805f36c679c84d7810fd8d723468b2ed128418b7e03f0460da9",
    "SRC_STK_ARM_CONST_": "34d5ea21c1584c0fcc4205b49e5dd821febb56c39683f122ddee71cdd0757cac",
    "SRC_STK_ARM_COPY": "566e9b83354fd77b8876037a9eb4099ba1ea7c7b68dae0ce8dd94bec72b1bf69",
    "SRC_STK_ARM_EXTRACTELEMENT": "6372e47827e9679b65931831ec5a881ad2f1cf55b9251a7b5591a8b427bb155a",
    "SRC_STK_ARM_EXTRACTFIELD": "8aac0272e2da78a353d0f7e135ed986a76cd0298146970b28ce75471a0b4c9e7",
    "SRC_STK_ARM_FCMP": "33ea2f606a9010398eda83be1390af8de3bc5bbc3b9b4971e538f66e20b52657",
    "SRC_STK_ARM_GEP": "41792ca2dd9fdc8af4fb25b974b6d001bbad5f3edfccbefc1a88adf21981d997",
    "SRC_STK_ARM_GLOBALADDR": "c684573ed60a5b023915911b07eb7212435294c085839ba7bdc9a2d63d5566d5",
    "SRC_STK_ARM_ICMP": "8e659be35a827691015eec5ccb3fc812cfd9dc2c5e4bc0bc06271f16845bad6f",
    "SRC_STK_ARM_INSERTFIELD": "c2e6443858cb05049055d1648e878e7d2c41d7f45371c37be97eeb3b2d5e9776",
    "SRC_STK_ARM_LOAD": "b5a81c930931d3cbca409221614cf5d4d28341b9a7f7be11af4af064dd74c080",
    "SRC_STK_ARM_OVERFLOW": "6ae8a8c8243af5aca3d873b294186ccd2451ff2f7add3a1fbab81525fd1fa407",
    "SRC_STK_ARM_PTRDATA": "9b61c3a909e63714fe17569a84e8c51225e84685a8be67bf026878e323168ecd",
    "SRC_STK_ARM_PTRFROMPARTS": "00ca63f5effb36821ca187c7676318180f664522c2ccb4ef0c57e6772e95739a",
    "SRC_STK_ARM_PTRMETADATA": "5c02bc7d2cfd139400bc6bad9c4685a3b0c53d98b0d9649ed51dac4bef7dcfbe",
    "SRC_STK_ARM_RELEASE": "a03cfb2417c0618c4bc55c518b60f15ceb5061d054cbcb0d16da0ef5f0d26e56",
    "SRC_STK_ARM_RET": "ea624d56d53e397f7e104854a3895b78c23a86cfba01c2e3b37ac01ebcf547ae",
    "SRC_STK_ARM_SELECT": "b45e668ccf82f80bdb4023dd823491f9c5433d1e177ce0256cd5af192fa1d9b1",
    "SRC_STK_ARM_STORE": "6bbbdc01bb80bafb8badc218fd0638ddd8f3e3c5d653079370f520995cde31a9",
    "SRC_STK_ARM_SWITCH": "f114134bd9dd99f63768796e2fbcb32825420c8ad396fcd0478985313cc23ef3",
    "SRC_STK_ARM_UNDEF": "9d1b6a201570e428824d55dc4b20b51fa2d35f8e5eec8774b6f9f8a70bd8f1f6",
    "SRC_STK_ARM_UNOP": "1e74473f23b4bc6dc8058d57a05acbce83d50dd666c59d1c84749ee68b5bcb72",
    "SRC_STK_ARM_UNREACHABLE": "244bc3d232145b4ff86e0945f8ff7813d39353ee92ab90472d2c7d0b285555ad",
    "SRC_STK_BOTRET": "65493b6472d59eea395919597ef4c26d45beccdf2d684b097ec1f39913071947",
    "SRC_STK_BOTRET_FALSE_OF_RUNNING": "5c4b318b5b50e63a87bf2dadb9a41f955596619255164e84e2747d1e9750c450",
    "SRC_STK_BOTRET_NIL": "29abe260799ccf7eeb55f5f36a1568eee72f520125e8946e82bcf20b2ba0ca92",
    "SRC_STK_BOTRET_TWO": "4cc11a589e1eba179174f046934a748fd24537a05345728dbb1e317097ad9a2d",
    "SRC_STK_STEP": "585d7572e5ba37e003b4e1a392af909858de6b87039089bf4846fa8d33cbd21f",
    "SRC_STORE_CHECKED_STACK": "62dc1538bc3b8acf36c06f1080b86703c693e20b43cc7671eabf8a4c7e10d9eb",
    "SRC_STORE_EXEC_STACK": "edd01fba8aa14f565ecaeec4b492b1b243fb143ed1a1f01b6aec292209ed8d38",
    "SRC_STORE_LIVE_STACK": "686210fa05358afb89ca35fedaee8e70959c1986d988ad76c3b9acead46f4b0c",
    "SRC_SWITCH_EXEC_STACK": "f2dce6751d86276e261ec34315c9606182b0ed686920a9072b6b442e15be1d5f",
    "SRC_SWITCH_N_STACK": "a3fbd7de5a87500e016bd3352a4c62f0fa1fbd68433ff0b6a07eff554f1560d0",
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
