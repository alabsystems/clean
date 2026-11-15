// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **`ir_it` — THE DESIGNATED TARGET. `TypeChecker::infer_type` itself, minted
//! from the compiler's artifact, and the kernel running it.**
//!
//! Every chain before this one is a body NEAR the target. This is the target:
//! function index 0 of the callee sidecar's partial bundle for
//! `<impl tc::TypeChecker<'env>>::infer_type`, six blocks, 36 nodes, projected by
//! reader A and replayed here line for line.
//!
//! ```text
//!   bb0  %2 = alloca struct.2      ; the Result slot
//!        %3 = call @func.19(%0)    ; tick_heartbeat
//!   bb1  switch on the heartbeat's tag -> bb5 (ok) / bb4 (err) / bb2
//!   bb5  %29 = call @func.2(%0,%1) ; infer_type_fast, stored and joined
//!   bb4  the error path, built out of `undef`s
//!   bb3  %5 = load struct.2 ; ret %5
//! ```
//!
//! # What is proved here, and it is a REFUSAL
//!
//! The module defines ONE function and CALLS two it does not define —
//! `tick_heartbeat` at canonical 1 and `infer_type_fast` at canonical 2.
//! `ir_call_exec` resolves a callee through `ir_func_find`, which matches on a
//! candidate's OWN id, so the first call halts the machine at
//! `IROutcome.stuck IRFault.no_func`: fail-closed, never a misroute.
//!
//! So `ir_it_halts_at_the_heartbeat` is what the kernel computes, and **A4 is
//! NOT claimed over `ir_it_module`**. This is exactly the posture
//! [`super::eval_ir_level_minted`] takes for `ir_lz`, whose A4 sentence is
//! kernel-checked FALSE, and it is the honest state of the target: the body is in
//! the spec, it executes, and it stops at its first callee.
//!
//! # Why that is worth registering rather than waiting
//!
//! Because the alternative is a sentence. Before this file, every statement about
//! `infer_type`'s reachability was made over the trust-ir artifact by probes;
//! nothing in the spec had the body at all, so "the closure is 396 functions and
//! the cut set has size one" could not be *executed* anywhere. Now the first cut
//! is not an argument about a call graph — it is the machine stopping, by
//! computation, at the one callee the 2026-09-16 measurement named.
//!
//! # Why `ir_it_b4` could not run even if the machine reached it
//!
//! `ir_undef_then_insertfield_faults` below pins the mechanism, and tracing it to
//! the bottom gives a sharper answer than "add an arity":
//!
//! ```text
//!   inductive IRModule
//!   | mk  : IRList IRFunc -> IRList IRGlobal -> IRModule
//!   | mkv : IRList IRFunc -> IRList IRGlobal -> IRList IREnc -> IRModule
//! ```
//!
//! **The reflected module has no struct/enum FIELD TABLE.** It carries functions,
//! globals, and (in `mkv`) an encodings table whose two row kinds — `nicheptr`
//! and `ptrwrap` — describe byte DECODING, not arity. So `IRTy.struct_ k` is an
//! opaque id and the machine cannot know the type has N fields.
//!
//! That splits the gap in two, and only one half is small:
//!
//! * `undef (tuple_ k)` CAN materialize a spine — there is no tuple table to
//!   index, so `k` can only be the arity;
//! * `undef (struct_ k)` / `undef (enum_ k)` CANNOT, at any cost inside the
//!   current object language. Closing it means widening `IRModule`, and its own
//!   registration says why that is not a small act: `mk` "is retained rather than
//!   widened so the eighteen chains minted before Phase B keep their exact
//!   terms", and the module is the unit the artifact digest is taken over.
//!
//! `ir_it_b4` uses the struct form — `undef struct.18`, `undef struct.19`,
//! `undef struct.2` — so `infer_type`'s error path is on the far side of that
//! decision, not the near side.
//!
//! ## The blocker was RE-MEASURED, and it held — with a sharper reason
//!
//! "Needs a field table" is the kind of claim this lane has had to retract
//! repeatedly, so it was tested rather than trusted. The producer's idiom is
//! SEQUENTIAL (`undef T; insertfield 0; insertfield 1; …`), which suggests a
//! spine that simply grows as it goes and needs no arity at all. It does not
//! work, and the reason is exact:
//!
//! ```text
//!   ir_ef_at        undef_ k    =  value undef_        <- the READ accepts undef
//!   ir_insert_field undef_ k v  =  fault not_agg       <- the WRITE refuses it
//!   ir_if_at        sp k v      =  fault bad_field  when k >= ir_vals_len sp
//! ```
//!
//! Padding `undef_` to a `k+1` spine on first write is not enough, because
//! `ir_it_b4` writes fields **0 then 2**: after the first insert the spine has
//! length one and the second is out of range. And `bad_field` is LOAD-BEARING —
//! it catches a genuine out-of-range field write — so extending on out-of-range
//! would weaken a real check to accommodate an idiom. The arity is therefore
//! genuinely required, and step 0 below stands.
//!
//! ### An asymmetry worth an owner's eye, independent of all this
//!
//! `ir_ef_at` reads `undef_` as an all-undef aggregate and returns `undef_`;
//! `ir_insert_field` refuses the same value as `not_agg`. Those are two different
//! answers to "is an undef an aggregate?", in one file, and only the read side's
//! is written down as a decision. Whichever is right, they disagree.
//!
//! ## There is no body left in the closure that needs none of this
//!
//! Measured 2026-09-16 over the whole bundle, so the stopping point is a fact
//! rather than a judgement: of the 2,388 bodies, the ones with a real BRANCH
//! (`condbr` or `switch`) and NO blocked construct — no aggregate build or read,
//! no memory, no call — number **ZERO**. Forty-six have control flow and clear
//! the other filters, and every one of them is a straight-line `br` passthrough.
//!
//! So every chain that could be added to this spec without first taking one of
//! the decisions below is another straight-line body like `ir_its` or `ir_cf`.
//! Width of that kind is available and cheap; DEPTH — a body that branches, or
//! builds a value, or calls anything — is on the far side of step 0.
//!
//! ## Step 0 was ATTEMPTED and the spec's own gates refused it
//!
//! The obvious fix — give `undef` an arity so it materialises a spine — was built
//! end to end and then reverted, because three pins say it is not a build item.
//! Recorded so nobody rebuilds it to learn the same thing.
//!
//! The attempt: an `IREnc.sfields S n` arity row (conservative by the encodings
//! table's own argument — an `IRModule.mk` has no rows, so every pre-Phase-B
//! chain's `undef` stays definitionally what it was), a separate `ir_fields_find`
//! so `ir_enc_find`'s first-match contract over nicheptr/ptrwrap could not
//! collide, and `ir_undef_eval m t`. It compiled; the EvalIR gates did not pass.
//!
//! **`ir_exec_undef_ty_irrelevant`** is a kernel-checked theorem stating that
//! `undef` "binds the one untyped poison value IRScalar.undef_ whatever type the
//! instruction is declared at; the annotation is inert." The change makes it
//! FALSE. The adequacy grid carries it at `state: irrelevance-proved-await-mint`.
//!
//! And the grid's `undef-execution` row is a **declared delta**: the pinned
//! reference interpreter **refuses to execute `Inst::Undef` at all** — "executing
//! undef would read an undefined value" — and faults `undefined_behavior`, where
//! Clean binds a poison value (measured 2026-08-25 at trust-ir `a4e81b6`,
//! `interpret.rs:619-623`; a `SynthExpect::DeclaredDelta`, asserted to reproduce
//! exactly and NEVER counted as agreement).
//!
//! So the reference is STRICTER than Clean here, not looser, and materialising a
//! spine would move a declared delta FURTHER from it while overturning a proved
//! theorem. That is an owner decision about the modelled semantics, and the three
//! pins are the evidence rather than a judgement of mine.
//!
//! # What it would take to go further, in order
//!
//! 0. `undef` materializing an aggregate spine — for the STRUCT form this needs
//!    a field table in `IRModule` (see above), which is an owner-level change to
//!    the reflected object language rather than a build item.
//! 1. `tick_heartbeat` in the module (it is the cut that makes the closure
//!    acyclic: 396 functions / 12 back edges -> 113 / 0). It MUTATES a counter,
//!    so its model is a state obligation, not a read — harder than `ir_lzb_deref`.
//! 2. `infer_type_fast` and its own closure — 113 functions after the cut.
//! 3. Only then an A4 statement, and it needs a spec-side meaning for a
//!    `Result<Expr, TypeError>` whose payloads this module carries as opaque
//!    zero-field datatypes.
//!
//! None of those is claimed here. `DerivedProved`, empty axiom closures.

use crate::spec::error::SpecError;
use crate::spec::Specification;

/// The minted definition script, replayed line for line.
const MINTED_IR_IT: &str = include_str!("generated/ir_it.defs.txt");

/// Registration rationales, one per minted line, in script order.
const MINTED_IR_IT_DOCS: &[&str] = &[
    "ir_it_tresult: `Result<Expr, TypeError>` -- THE RETURN TYPE, as the flat [__tag, __v0_0, __v1_0] struct the producer renders it, crate id 2. The alloca, the load and both stores name it. This is the type the proven-output gate refuses infer_type on, and it carries NO recorded size. DerivedProved, zero axiom_deps.",
    "ir_it_ttyerr_opaque: `TypeError` as the OPAQUE datatype rendering -- zero fields, crate id 1. `ty_convert.rs` routes the recursive kernel cluster to Ty::Datatype by def path, and this is what that looks like from inside the spec. DerivedProved, zero axiom_deps.",
    "ir_it_ttyerr_flat: the SAME Rust type as the previous alias, rendered FLAT with 34 fields, crate id 16. Both spellings appear in one body -- the undefs are typed with this one, the extractfields with the opaque one -- which is worth registering because it is the producer inconsistency the link-5 census traced, visible as two aliases for one type. DerivedProved, zero axiom_deps.",
    "ir_it_tresult2: a SECOND `Result` instantiation, crate id 18, distinct from ir_it_tresult by crate id alone. Built by insertfield out of undefs on the error path and taken apart again two nodes later. DerivedProved, zero axiom_deps.",
    "ir_it_tcflow: `ControlFlow`, crate id 19 -- the `?` desugaring's carrier, flat [__tag, __v0_0, __v1_0], built and destructured entirely inside the error path. DerivedProved, zero axiom_deps.",
    "ir_it_b0: the ENTRY block -- alloca the Result slot, call tick_heartbeat with the receiver, br. Three nodes, and the second of them is where this module stops. DerivedProved, zero axiom_deps.",
    "ir_it_b1: the dispatch -- read the heartbeat result's tag and switch, ok to b5, err to b4, default to the unreachable. Two nodes. DerivedProved, zero axiom_deps.",
    "ir_it_b2: `unreachable`, the switch default. Registered rather than elided: a transcription that dropped it would change the switch's default target and agree with the artifact nowhere a test was looking. DerivedProved, zero axiom_deps.",
    "ir_it_b3: the JOIN -- load the Result out of the alloca slot and return it. Both paths reach it by `br` with no arguments, which is why this body has no block parameters at all. DerivedProved, zero axiom_deps.",
    "ir_it_b4: the ERROR path, twenty-five nodes, and the shape is the finding: it builds its Err payload out of `undef` (ir_d7, ir_d9, ir_d23, ir_d25, ir_d26) and computes an icmp whose result is never used. The real Rust constructs a specific TypeError here; the derived body says Err(undefined). That is a producer-fidelity gap, registered so it is executable rather than described. DerivedProved, zero axiom_deps.",
    "ir_it_b5: the OK path -- call infer_type_fast with both parameters, store the result, join. Three nodes, and the body's whole inference is that one call. This is why the ok path TRANSPORTS its return rather than constructing it. DerivedProved, zero axiom_deps.",
    "ir_it_func: `TypeChecker::infer_type` as EvalIR -- id 0, TWO pointer parameters, entry block 0, six blocks. The designated target's control-flow graph exactly as the compiler emits it. DerivedProved, zero axiom_deps.",
    "ir_it_module: *** THE DESIGNATED TARGET'S MODULE. *** One function, minted from the emitted trust-ir rather than transcribed from it. It CALLS two functions it does not define, so it halts stuck at the first -- see ir_it_halts_at_the_heartbeat. A4 is NOT claimed over it, exactly as for ir_lz_module. DerivedProved, zero axiom_deps.",
];

/// The minted script's lines, in registration order.
static MINTED_IR_IT_LINES: std::sync::LazyLock<Vec<&'static str>> =
    std::sync::LazyLock::new(|| {
        MINTED_IR_IT
            .lines()
            .map(str::trim)
            .filter(|l| !l.is_empty())
            .collect()
    });

/// The minted `infer_type` module definitions, in registration order.
#[must_use]
pub(crate) fn ir_it_module_defs() -> &'static [&'static str] {
    &MINTED_IR_IT_LINES
}

const SRC_IT_UNDEF_AGG_GAP: &str = "def ir_undef_then_insertfield_faults (k : Nat) (v : IRScalar) : Eq IRStepResult (ir_insert_field IRScalar.undef_ k v) (IRStepResult.fault (IROutcome.type_error IRFault.not_agg)) := Eq.refl IRStepResult (IRStepResult.fault (IROutcome.type_error IRFault.not_agg))";

const SRC_IT_MACH0: &str = "def ir_it_mach0 (mem : IRList IRMemSlot) (p : Nat) (q : Nat) (na : Nat) : IRMachine := IRMachine.mk (IRList.cons IRFrame (IRFrame.mk ir_d0 ir_d0 Nat.zero (ir_bind_params (ir_nl2 ir_d0 ir_d1) (ir_vl2 (IRScalar.ptr_ p) (IRScalar.ptr_ q)) (IRList.nil IRBinding)) (IRList.nil Nat)) (IRList.nil IRFrame)) mem na";

const SRC_IT_INIT: &str = "def ir_it_init_is_mach0 (mem : IRList IRMemSlot) (p : Nat) (q : Nat) (na : Nat) : Eq IRConfig (ir_init ir_it_module ir_d0 (ir_vl2 (IRScalar.ptr_ p) (IRScalar.ptr_ q)) mem na) (IRConfig.running (ir_it_mach0 mem p q na)) := Eq.refl IRConfig (IRConfig.running (ir_it_mach0 mem p q na))";

const SRC_IT_STUCK: &str = "def ir_it_halts_at_the_heartbeat (mem : IRList IRMemSlot) (p : Nat) (q : Nat) (na : Nat) : Eq IROutcome (ir_eval ir_d8 ir_it_module ir_d0 (ir_vl2 (IRScalar.ptr_ p) (IRScalar.ptr_ q)) mem na) (IROutcome.stuck IRFault.no_func) := Eq.refl IROutcome (IROutcome.stuck IRFault.no_func)";

const SRC_IT_STUCK_MORE_FUEL: &str = "def ir_it_more_fuel_does_not_help (mem : IRList IRMemSlot) (p : Nat) (q : Nat) (na : Nat) : Eq IROutcome (ir_eval ir_d40 ir_it_module ir_d0 (ir_vl2 (IRScalar.ptr_ p) (IRScalar.ptr_ q)) mem na) (IROutcome.stuck IRFault.no_func) := Eq.refl IROutcome (IROutcome.stuck IRFault.no_func)";

impl Specification {
    /// `ir_it` — the designated target, minted, and where it stops.
    pub(super) fn add_eval_ir_it(&mut self) -> Result<(), SpecError> {
        let minted = ir_it_module_defs();
        if minted.len() != MINTED_IR_IT_DOCS.len() {
            return Err(SpecError::EnvError(format!(
                "the minted ir_it script has {} definitions but {} rationales are declared; \
                 regenerate the docs table with the script rather than reusing it",
                minted.len(),
                MINTED_IR_IT_DOCS.len()
            )));
        }
        for (line, doc) in minted.iter().zip(MINTED_IR_IT_DOCS) {
            self.add_recursive_def(line, doc)?;
        }
        self.add_recursive_def(SRC_IT_UNDEF_AGG_GAP, "*** THE MACHINE CANNOT EXECUTE THE PRODUCER'S STANDARD AGGREGATE-CONSTRUCTION IDIOM, kernel-checked. *** `IRInst.undef t` binds a BARE IRScalar.undef_ and ignores `t` entirely (eval_ir_machine.rs:1450), while ir_insert_field requires an IRScalar.aggv and faults not_agg on undef_ (eval_ir_machine.rs:1076). So `undef T` followed by `insertfield T` -- which is how the producer builds EVERY aggregate, and exactly what ir_it_b4 does five times -- cannot step. This fact is registered for EVERY index and value rather than at one witness, because the gap is in the SHAPE and not in any particular field. \n\nIt is why ir_it's error path could not execute even if the machine reached it, and it is not local to this chain: the 2026-09-16 link-5 census measured InsertField/ExtractField among the axes blocking 1,857 of 2,388 bodies. Closing it means `undef` at an aggregate type materializing a spine of undefs, which needs the ARITY -- immediate for `tuple_ k` if k is the arity, a module-table lookup for `struct_ k` / `enum_ k`, and `IRInst.undef` currently carries only the type. That is a design question about the reflected machine, recorded here as an executable fact rather than a paragraph. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IT_MACH0, "ir_it_mach0: the machine ir_init produces for this module -- TWO pointer parameters bound on entry, where every earlier chain binds at most one. The module declares no globals, so ir_mem_concat is the identity on the caller heap. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IT_INIT, "ir_it_init_is_mach0: the hand-written initial machine IS the one ir_init builds, for every heap, both pointer arguments and every counter, by computation. Registered rather than assumed so a change to ir_init stops this reducing instead of silently making the execution fact a statement about a different starting state. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IT_STUCK, "ir_it_halts_at_the_heartbeat: *** THE KERNEL RUNS THE DESIGNATED TARGET, AND IT STOPS AT ITS FIRST CALLEE. *** For every heap, both arguments and every counter, the machine reaches IROutcome.stuck IRFault.no_func -- the alloca, then `call 1` into tick_heartbeat, which this module does not define. Fail-closed, never a misroute: ir_func_find matches a candidate on its OWN id, so an absent callee halts rather than resolving to the body itself (the 2026-08-20 namespace defect). This is the ir_lz posture and it is the honest state of the target: the body is in the spec, it executes, and A4 is not claimed. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IT_STUCK_MORE_FUEL, "ir_it_more_fuel_does_not_help: the same outcome at forty steps as at eight. Registered separately because `stuck` and `fuel_out` are different refusals and only one of them is about the MODULE -- a reader who saw a single low-fuel witness could reasonably wonder whether the machine simply ran out. It did not. DerivedProved, zero axiom_deps.")?;
        Ok(())
    }
}
