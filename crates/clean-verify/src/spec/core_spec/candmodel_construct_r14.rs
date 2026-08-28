// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! R14 of the candidate-model construction ladder — **the weakening and
//! substitution OPERATIONS on shape derivations, and the semantic lemmas they
//! exist for.**
//!
//! ## Why this rung
//!
//! R13 closed with a precise handoff:
//!
//! > *"`val_psub` / `val_lift` are still not registered, and the reason
//! > CHANGED. What was blocking them is gone; what is missing now is that R12
//! > built no substitution or weakening OPERATION on `WK` derivations, and the
//! > corpus lemmas are statements about one. R13 lands the congruence engine
//! > those proofs consume, not the proofs. That is the new binding
//! > constraint."*
//!
//! That is exactly right, and it is what this rung builds. The corpus's
//! `val_lift`/`val_psub` (`FInterp.lean:159/209`) are inductions on the TERM,
//! because the corpus's `val` recurses on the term. R12's `sval` recurses on
//! the **shape derivation**, so spec-side those lemmas are inductions on a
//! derivation and their subjects are `wk_lift`/`wk_psub` — functions that did
//! not exist. They do now.
//!
//! ## A — the operations, and the shape of the dependency
//!
//! * **`wk_lift`** (corpus `wk_lift`, `FWK.lean:109`) — a `WK D e s` derivation
//!   transports to `WK (skins k t D) (lift_at e k 1) s`, one slot inserted at an
//!   arbitrary cutoff. **`wk_lift0`** is the cutoff-zero corollary.
//! * **`wk_psub`** (corpus `wk_psub`, `FWK.lean:149`) — a `WK Dp e s` derivation
//!   transports along any substitution whose components are shape-typed at the
//!   matching slots: `WK D (psubst sg e) s`. **`wk_inst`** is the single-slot
//!   corollary at the kernel's own `instantiate`.
//! * **`wk_up`** — the `up`-closure of a shape-typed substitution. This is the
//!   ONLY place weakening enters substitution, and it is why the two cannot be
//!   proved in either order alone: `psubst sg (pi A B)` is
//!   `pi (psubst sg A) (psubst (up sg) B)` and `up sg (succ n)` is
//!   `lift_at (sg n) 0 1`, so the pi/lam cases of `wk_psub` need `wk_lift0`,
//!   whose own induction has to pass under binders at cutoff `succ k`.
//!
//! **The one design decision that pays for everything.** The corpus's `skins`
//! is `fun i => if i < c then Δ i else if i = c then t else Δ (i-1)`, and its
//! `skins_succ` needs `funext` plus four `omega` calls. R14's `skins` recurses
//! on the CUTOFF, which makes `skins (succ c) t (skcons s D)` DEFINITIONALLY
//! `skcons s (skins c t D)` — `Nat.rec` iota at `Nat.succ qj`, then function
//! eta. Consequence: **every binder case of `wk_lift` is transport-free**, and
//! the whole rung has exactly three transport sites (`r14_wk_lift_var`'s two
//! and `wk_inst`'s `instantiate_eq_psubst`). `r14_skins_zero`/`r14_skins_succ`
//! are registered as `Eq.refl` GUARDS so a future re-spelling of `skins` with a
//! decidable comparison fails here rather than three lemmas later.
//!
//! ## B — the semantic lemmas
//!
//! * **`r14_val_lift`** — `sval` of the weakened derivation at a valuation is
//!   `sval` of the original at the dropped valuation, at EVERY shape
//!   environment, term, shape, derivation, cutoff and inserted shape. Corpus
//!   `val_lift`.
//! * **`r14_val_psub`** — `sval` of the substituted derivation is `sval` of the
//!   original at the induced valuation. Corpus `val_psub`. Its `var` case is
//!   `Eq.refl`, which is the payoff of stating `wk_psub` with a hypothesis
//!   rather than with a cutoff.
//! * **`r14_val_inst`** — corpus `val_inst`, at the kernel's `instantiate`.
//! * **`r14_val_beta`** — corpus `val_beta` (`FInterp.lean:248`). **This is the
//!   head-beta case of `val_step` in the corpus's actual form**, which R12 could
//!   not state: `r12_sval_beta` equates the redex's interpretation with a
//!   VALUATION EXTENSION, not with the interpretation of a TERM. Here the two
//!   TERMS — `app (lam A b) a` and `instantiate b a` — have the same
//!   interpretation, and `r14_beta_step` is the real `whnf_step` between them.
//! * **`r14_sval_transports_real_beta`** — membership transports across that
//!   real step at an arbitrary shape-typed redex. This is the class
//!   `r11_candInterp_step_conv_refuted` proves `candInterp` cannot do even once,
//!   now with the contractum spelled exactly as `beta_reduces.beta` produces it.
//!
//! Three ingredients make the derivation-indexed versions go through, and the
//! first two are new machinery R12/R13 did not need:
//!
//! 1. **`r14_sval_cast_term` / `r14_sval_cast_shape`.** `sval` recurses on the
//!    derivation, so a derivation transported along an `Eq` does not reduce.
//!    Both are based `Eq.rec` (Martin-Lof J) with a PROOF-DEPENDENT motive —
//!    the spec's `Eq.rec` supports it (`foundation_types.rs:213` uses the same
//!    shape for `Eq.symm`).
//! 2. **`r14_cast_idx`, and the kernel's K-like reduction.** `Eq` is K-like in
//!    this kernel (`env/inductive_recursor.rs:1036`: Prop, one constructor, no
//!    fields after parameter promotion — the comment names `Eq` and says it
//!    enables UIP), so a `VD`-cast along a REFLEXIVE shape equality computes
//!    away even when the proof term is stuck. That is what makes
//!    `r14_venvLift_at`'s zero/succ corner `Eq.refl`, and it is why the
//!    dependent valuation `VEnvD` (R12's deliberate divergence from the corpus's
//!    untyped `VEnv` + `MatchEnv`) does not cost a cast at every index.
//! 3. **R13's `r13_venvD_funext` and `r13_vd_arr_funext`.** Every valuation law
//!    here (`r14_venvLift_vcons`, `r14_venvSub_up`, `r14_venvSub_scons`) is a
//!    pointwise `Nat.rec` turned into an equality of VALUATIONS, and the lam
//!    case of both semantic lemmas is a pointwise equality of two SEMANTIC
//!    FUNCTIONS turned into an equality of functions. R13 predicted this rung
//!    would consume them; it does, and it could not be written without them.
//!
//! ## What did NOT land, and why — read before quoting
//!
//! * **This is not `val_step`, and it is not `val_conv`.** The corpus's
//!   `val_step` (`FWK.lean:290`) is an induction over `Step` with five arms;
//!   R14 lands its BETA arm at the real `whnf_step` plus the two congruence
//!   COMBINATORS (`r14_sval_pi_congr`, `r14_vapply_congr`) that its `piA`/`piB`/
//!   `appL`/`appR` arms consume. The arms themselves need `wk_step` — subject
//!   reduction for shapes — and that needs inversion of the spec's `whnf_step`,
//!   which is NOT the corpus's five-constructor `Step`: it carries delta, iota,
//!   zeta, `let_`, `proj` and `forall_` congruences over a NINE-constructor
//!   `KExpr`, none of which `WK` types. `val_conv` additionally needs
//!   confluence. Both are a rung of their own; nothing here claims them.
//! * **R12's TWO HORNS are untouched and still stand.** HORN 1 (predicativity:
//!   `piCandV` lands one universe above the candidates) and HORN 2 (the
//!   derivation-indexed clause calls `sval` at derivations of unrelated terms,
//!   so it is not structural) are obstructions about universes and about
//!   structural recursion. Substitution is neither, exactly as extensionality
//!   was neither. `test_candmodel_r14_leaves_r12_horns_standing` re-asserts both
//!   from R12's own source tables, as R13's test does.
//! * **R10's `cr3` refutation and R11's `candInterp` conversion refutation are
//!   untouched.** Nothing here is about `candInterp`.
//! * **No SN capstone, and `sval` is still PARTIAL.** `WK` types five of
//!   `KExpr`'s nine constructors. Nothing here advances
//!   `whnf_terminates_well_typed_dependent` or discharges `M : CandModel tenv`.
//!
//! ## Non-degeneracy (no automated gate performs this)
//!
//! Every operation is applied at a REGISTERED R12 object and the result pinned:
//!
//! * `r14_lift_bvar0_witness` — `lift_at (bvar 0) 0 1` IS `bvar 1`. If lifting
//!   were the identity on variables this does not typecheck.
//! * `r14_wk_lift_witness` / `r14_wk_lift_shifts` — weakening R12's all-`Sk.ty`
//!   environment by a `Sk.kd Sk.ty` slot at the head leaves the old variable at
//!   `bvar 1` and STILL at shape `Sk.ty`. The paired refusal test
//!   `test_candmodel_r14_weakening_does_not_confuse_the_inserted_slot` feeds the
//!   kernel the same derivation claimed at `Sk.kd Sk.ty` and asserts REJECTION,
//!   so the witness is not compatible with a junk operation.
//! * `r14_wk_inst_witness` — substituting `sort 0` into `bvar 0` yields a
//!   derivation of `sort 0`, transported through R12's own
//!   `r12_beta_contractum_is_arg`.
//! * `r14_val_lift_witness` — the value of the WEAKENED variable is the original
//!   valuation's slot 0, not the inserted value `v`.
//! * `r14_val_inst_witness` — the value of `instantiate (bvar 0) (sort 0)` is
//!   the sort's candidate, COMPUTED through `r14_val_inst`.
//!
//! ## Census
//!
//! ZERO new axioms. 47 constants — 16 `add_recursive_def` and 31 value-bearing
//! theorems through `add_definition` with kernel `add_decl` checking. Everything
//! rests on `Eq`/`Eq.rec`/`Nat.rec`/`WK.rec` and on R12/R13 constants whose own
//! closures are empty; `r13_venvD_funext` reaches `Quot.sound` and the quotient
//! formers, every one of them inside `EXPLICIT_FOUNDATIONAL_BASE`, so
//! `computed_axiom_closure` stays EMPTY.
//!
//! ## Two elaborator facts, both measured, both worth the next rung's time
//!
//! 1. **`Eq.substType` does NOT delta-unfold.** It is registered with
//!    `add_definition_checked` (`foundation_types.rs:350`), so a transport
//!    written with it never exposes its `Eq.rec` and therefore never iota-
//!    reduces at `Eq.refl`. `r14_sval_cast_term`'s base case died on exactly
//!    that. Every transport a later proof must REDUCE THROUGH has to go through
//!    a `def` whose body is a bare `Eq.rec` — hence `r14_wkCastT` /
//!    `r14_wkCastS` / `r14_vdCast`. This is R12's
//!    `add_definition`-lowers-to-`Opaque` note one level further in, and it
//!    applies to the FOUNDATION's own transport combinator, not just to spec
//!    witnesses.
//! 2. **A proof-irrelevance step must be a standalone constant, not an inline
//!    recursor minor.** The first spelling of `r14_cast_idx` closed its base
//!    case with `Eq.refl` on the grounds that two proofs of one `Prop` are
//!    definitionally equal; the ELABORATOR refused, comparing the two proof
//!    binders as free variables and reporting an `fvar` mismatch. The KERNEL
//!    does apply proof irrelevance — the identical statement registers cleanly
//!    as a standalone `add_recursive_def`, which
//!    `test_candmodel_r14_cast_irrelevance_needs_a_standalone_constant`
//!    asserts, and which refuted the first version of that very test. So the
//!    fact is a POSITION dependence in the elaborator's unifier, and the fix is
//!    to factor the step into `r14_vdCast_irrel` and APPLY it. Separately,
//!    `r14_vdCast_refl` records that a cast along a stuck REFLEXIVE proof
//!    computes away at all — that one is K-like reduction
//!    (`env/inductive_recursor.rs:1036`), which proof irrelevance cannot
//!    supply: irrelevance identifies two proofs, it does not reduce a recursor
//!    applied to one.

use std::collections::HashSet;

use super::candmodel_construct_r14_src::*;
use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

/// R6-R13's theorem helper, verbatim: one `add_definition` per theorem so the
/// kernel's `add_decl` type-checks the proof term against the declared type.
fn add_thm(
    spec: &mut Specification,
    name: &str,
    ty: String,
    val: String,
    deps: &[&str],
    desc: &str,
) -> Result<(), SpecError> {
    spec.add_definition(SpecDefinition {
        name: name.to_string(),
        type_src: ty,
        value_src: Some(val),
        is_axiom: false,
        description: desc.to_string(),
        category: AxiomCategory::DerivedLemma,
        proof_status: ProofStatus::DerivedProved,
        elaborated_type: None,
        elaborated_value: None,
        dependencies: Some(
            deps.iter()
                .map(|d| (*d).to_string())
                .collect::<HashSet<_>>(),
        ),
        axiom_deps: HashSet::new(),
    })
}

/// `(dependencies, description)` for every R14 constant. Kept in one table so
/// the census/coverage tooling SEES each name with its own meaning — the
/// aggregation-blindness control the port design calls for (§6.4).
#[allow(clippy::too_many_lines)]
fn meta(name: &str) -> (&'static [&'static str], &'static str) {
    match name {
        "skins" => (
            &["skcons"],
            "Inserting a shape slot at cutoff c (corpus skins, FWK.lean:39), by Nat.rec on the \
             CUTOFF rather than by a decidable comparison. That makes skins_zero and skins_succ \
             DEFINITIONAL and every binder case of wk_lift transport-free; the corpus needs \
             funext + omega for skins_succ.",
        ),
        "r14_wkpos" => (
            &["Nat.sub"],
            "The de Bruijn position of variable i after inserting a slot at cutoff c. Same \
             Nat.rec-on-(c - i) discriminator shape as lift_bvar_at, so the two compute in step. \
             A private copy of the subject-reduction bundle's wkpos, which is Full-bundle-only.",
        ),
        "r14_wkCastT" | "r14_wkCastS" => (
            &["WK", "Eq.rec"],
            "Transport a WK derivation along an equality of TERMS (T) or of SHAPES (S), as a \
             REDUCIBLE def whose body is a bare Eq.rec. MEASURED 2026-08-27, and the elaborator \
             fact that cost this rung a cycle: Eq.substType is registered with \
             add_definition_checked and does NOT delta-unfold, so a transport spelled with it \
             never exposes its Eq.rec and never iota-reduces at Eq.refl — r14_sval_cast_term's \
             base case died on exactly that. Every transport a later proof must REDUCE THROUGH \
             has to go through a def that unfolds to a bare Eq.rec. This is R12's \
             add_definition-lowers-to-Opaque note one level further in.",
        ),
        "r14_vdCast" => (
            &["VD", "Eq.rec"],
            "Transport a VALUE along an equality of shapes, likewise as a reducible def over a \
             bare Eq.rec. This is the cast the kernel's K-LIKE reduction acts on: at a REFLEXIVE \
             shape equality the Eq.rec collapses even though the proof term is stuck, which is \
             what makes r14_venvLift_at's corners Eq.refl and what keeps R12's DEPENDENT \
             valuations from costing a cast at every index.",
        ),
        "r14_skins_zero" => (
            &["skins", "skcons"],
            "GUARD: skins at cutoff zero IS skcons, by Eq.refl. wk_lift0 and val_lift0 are the \
             cutoff-zero corollaries and are definitional only while this holds.",
        ),
        "r14_skins_succ" => (
            &["skins", "skcons"],
            "GUARD: skins (succ c) t (skcons s D) IS skcons s (skins c t D), by Eq.refl (Nat.rec \
             iota at Nat.succ qj, then function eta). The corpus proves the same statement with \
             funext and four omega calls. If a future edit re-spells skins with a decidable \
             comparison this stops being Eq.refl and every binder case of wk_lift silently starts \
             needing a transport.",
        ),
        "r14_wkpos_zero" => (
            &["r14_wkpos", "nat_sub_zero_left"],
            "r14_wkpos i 0 = succ i: insertion at the head shifts every variable.",
        ),
        "r14_wkpos_rec_succ" => (
            &["Nat.rec"],
            "Discriminator step law: the (succ succ j / succ j) Nat.rec equals succ of the \
             (succ j / j) Nat.rec, at EVERY discriminant. Both arms Eq.refl.",
        ),
        "r14_wkpos_succ_succ" => (
            &["r14_wkpos", "r14_wkpos_rec_succ", "nat_sub_succ_succ"],
            "r14_wkpos (succ j) (succ c) = succ (r14_wkpos j c) — the index law that carries the \
             succ/succ corner of r14_skins_idx and of r14_venvLift_at.",
        ),
        "r14_lift_bvar_wkpos_rec" => (
            &["Nat.rec", "KExpr"],
            "lift_bvar_at's KExpr-discriminator and r14_wkpos's Nat-discriminator agree pointwise. \
             The base arm is Eq.refl because Nat.add i (Nat.succ Nat.zero) reduces to Nat.succ i — \
             Nat.add recurses on its SECOND argument, which is why the lift amount is pinned at 1.",
        ),
        "r14_lift_at_bvar_wkpos" => (
            &["r14_wkpos", "r14_lift_bvar_wkpos_rec", "lift_at"],
            "lift_at (bvar i) c 1 = bvar (r14_wkpos i c). The bridge from the kernel's lifting \
             function to the index algebra; lift_at on a bvar is otherwise STUCK on Nat.sub c i.",
        ),
        "r14_skins_idx" => (
            &["skins", "r14_wkpos", "r14_wkpos_zero", "r14_wkpos_succ_succ"],
            "THE SHAPE-LOOKUP LAW OF INSERTION: skins c t D (r14_wkpos i c) = D i. Double Nat.rec \
             (cutoff, then index); the succ/zero corner is Eq.refl because Nat.sub (succ c) zero \
             reduces to succ c and r14_wkpos then takes its below-the-cut branch definitionally.",
        ),
        "r14_wk_lift_var" => (
            &["skins", "r14_skins_idx", "r14_lift_at_bvar_wkpos", "WK.var"],
            "The var leaf of weakening, and the ONLY site in the rung with two transports: one in \
             TERM position (lift_at (bvar i) c 1 is stuck, so it is rewritten to bvar (wkpos i c)) \
             and one in SHAPE position (WK.var concludes at skins c t D (wkpos i c), which \
             r14_skins_idx identifies with D i). Registered as a def, not a theorem: \
             r14_val_lift's var case must REDUCE wk_lift down to this constant, and an \
             add_definition registration lowers to Opaque and stops that.",
        ),
        "wk_lift" => (
            &["WK.rec", "skins", "lift_at", "r14_wk_lift_var"],
            "THE WEAKENING OPERATION (corpus wk_lift, FWK.lean:109): a WK derivation transports to \
             the shape environment with one slot inserted at an arbitrary cutoff, at the lifted \
             term. Every binder case is transport-free because skins (succ c) t (skcons s D) is \
             DEFINITIONALLY skcons s (skins c t D).",
        ),
        "wk_lift0" => (
            &["wk_lift", "skcons"],
            "Weakening at the HEAD of the shape environment (corpus wk_lift0, FWK.lean:142). \
             Definitional at cutoff zero: skins Nat.zero t D IS skcons t D.",
        ),
        "wk_up" => (
            &["wk_lift0", "up", "scons", "WK.var"],
            "The up-closure of a shape-typed substitution — the ONE place weakening enters \
             substitution, and the reason the two operations cannot be proved in either order \
             alone. up sg Nat.zero is bvar 0 (closed by WK.var with no transport, since \
             skcons d Dp Nat.zero reduces to d) and up sg (succ n) is lift_at (sg n) Nat.zero 1, \
             which is exactly wk_lift0's conclusion.",
        ),
        "wk_psub" => (
            &["WK.rec", "psubst", "wk_up"],
            "THE SUBSTITUTION OPERATION (corpus wk_psub, FWK.lean:149): a WK derivation transports \
             along any substitution whose every component is shape-typed at the matching slot. \
             Completely transport-free — the var case is literally the hypothesis at i, which is \
             why the corpus states it with a hypothesis rather than with a cutoff.",
        ),
        "r14_scons_typed" => (
            &["scons", "idsubst", "skcons", "WK.var"],
            "The single-slot substitution scons a idsubst, shape-typed (corpus wk_inst's inner \
             index split, FWK.lean:175-179). Transport-free on both branches.",
        ),
        "wk_inst" => (
            &["wk_psub", "r14_scons_typed", "instantiate_eq_psubst"],
            "Substitution for the ZEROTH slot at the kernel's own instantiate (corpus wk_inst, \
             FWK.lean:172). The one transport is the spec's landed instantiate/psubst bridge.",
        ),
        "venvLiftD" => (
            &["skins", "VEnvD", "VD"],
            "Dropping the inserted slot from a DEPENDENT valuation (corpus venvLift, \
             FInterp.lean:140). The corpus's index formula would need a VD-cast at every index \
             because R12's valuations are dependent; recursing on the cutoff instead makes every \
             clause typecheck definitionally and leaves r14_venvLift_vcons — the lemma the binder \
             cases consume — provable with Eq.refl in both branches.",
        ),
        "venvSubD" => (
            &["sval", "VEnvD"],
            "The valuation induced by a shape-typed substitution (corpus venvSub, \
             FInterp.lean:197). NO cast is needed and none is used: hsg i is a derivation at \
             exactly Dp i, so sval lands in VD (Dp i) on the nose.",
        ),
        "r14_sval_cast_term" => (
            &["sval", "Eq.rec", "Eq.substType"],
            "sval of a derivation transported along an equality of TERMS is sval of the original. \
             Needed because sval recurses on the DERIVATION, so a transported derivation does not \
             reduce. Based Eq.rec with a PROOF-DEPENDENT motive.",
        ),
        "r14_sval_cast_shape" => (
            &["sval", "Eq.rec", "Eq.substType"],
            "The same for a transport in SHAPE position, with the corresponding VD-cast on the \
             value side. The var case of val_lift is exactly this composed with the term version.",
        ),
        "r14_vdCast_refl" => (
            &["r14_vdCast", "Eq.refl"],
            "THE K-LIKE MEASUREMENT: a VD-cast along a STUCK proof of a REFLEXIVE shape equality \
             is the value itself, by Eq.refl. Its acceptance is a fact about the KERNEL, not \
             about the proof — Eq.rec reduces here only because Eq is K-like \
             (env/inductive_recursor.rs:1036, which names Eq and says it enables UIP). Proof \
             irrelevance cannot supply it: irrelevance identifies two PROOFS, it does not reduce \
             a recursor applied to one. Registered here, where the appeal to K is visible, rather \
             than buried inside a bigger proof.",
        ),
        "r14_vdCast_irrel" => (
            &["r14_vdCast_refl", "Eq.rec"],
            "UIP for the cast: two VD-casts along two proofs of the SAME shape equality agree. \
             Based Eq.rec on the first proof reduces the goal to the reflexive case, where \
             r14_vdCast_refl closes it. It is a SEPARATE constant for a measured reason: the \
             identical step written INLINE as the base minor of r14_cast_idx's Eq.rec was \
             refused by the elaborator with an fvar mismatch between the two proof binders, \
             while the kernel accepts it as its own declaration. An irrelevance step has to be \
             a standalone constant the proof term APPLIES.",
        ),
        "r14_cast_idx" => (
            &["Eq.rec", "Eq.substType", "VEnvD"],
            "Two VD-casts of the SAME valuation at two PROVABLY EQUAL indices agree. Its base \
             case at j2 := j1 leaves two casts differing only in their Eq proofs, and that is \
             discharged by APPLYING r14_vdCast_irrel — the elaborator refuses the same step \
             written inline here.",
        ),
        "r14_venvLift_at" => (
            &[
                "venvLiftD",
                "r14_cast_idx",
                "r14_skins_idx",
                "r14_wkpos_zero",
                "r14_wkpos_succ_succ",
            ],
            "The recursive venvLiftD agrees with the corpus's index formula read as a cast. The \
             bridge between the definition that makes the BINDER cases definitional and the form \
             the VAR case produces. Its zero/succ corner is Eq.refl only because Eq is K-LIKE in \
             this kernel (env/inductive_recursor.rs:1036), so a cast along a reflexive shape \
             equality computes away even when the proof term is stuck.",
        ),
        "r14_sval_wk_lift_var" => (
            &[
                "r14_sval_cast_term",
                "r14_sval_cast_shape",
                "r14_venvLift_at",
                "r14_wk_lift_var",
            ],
            "THE VALUE OF A WEAKENED VARIABLE — the whole var case of r14_val_lift, as the \
             composite of the two cast lemmas and r14_venvLift_at.",
        ),
        "r14_venvLift_vcons" => (
            &["venvLiftD", "vconsD", "r13_venvD_funext"],
            "WEAKENING COMMUTES WITH VALUATION EXTENSION (corpus venvLift_vcons, \
             FInterp.lean:142). Both branches are Eq.refl — the point of defining venvLiftD by \
             recursion on the cutoff — and R13's dependent funext turns the pointwise statement \
             into the equality of the two VALUATIONS, which is what Eq.cong needs downstream. The \
             first place the ladder cashes r13_venvD_funext for something other than a congruence.",
        ),
        "r14_vapply_congr" => (
            &["VD", "Eq.cong"],
            "Semantic application is a congruence in both slots. VD (Sk.arr d c) iota-reduces to \
             VD d -> VD c, which is what lets qF x typecheck. The appL/appR arms of the corpus's \
             val_step consume exactly this.",
        ),
        "r14_sval_pi_congr" => (
            &["mkTyD", "PiSet", "vcarD", "Eq.cong"],
            "The Pi clause of sval is a congruence in the domain value and in the codomain value — \
             the corpus's piA/piB pair as ONE combinator. Unlike the corpus's piVal_congr it needs \
             no propext: R13 already showed the congruence is an Eq.cong in the VALUE, never a \
             biimplication between two Types.",
        ),
        "r14_val_lift" => (
            &[
                "wk_lift",
                "venvLiftD",
                "r14_sval_wk_lift_var",
                "r14_venvLift_vcons",
                "r14_sval_pi_congr",
                "r14_vapply_congr",
                "r13_vd_arr_funext",
            ],
            "THE SEMANTIC WEAKENING LEMMA (corpus val_lift, FInterp.lean:159). The corpus's is an \
             induction on the TERM because its val recurses on the term; sval recurses on the \
             DERIVATION, so this is an induction on the derivation and its subject is wk_lift — \
             which is precisely why the OPERATION had to exist before the lemma could be stated. \
             This is the constant R13 named as blocked.",
        ),
        "r14_val_lift0" => (
            &["r14_val_lift", "vconsD"],
            "val_lift at the context HEAD (corpus val_lift0, FInterp.lean:191). Definitional on \
             both sides at cutoff zero: skins Nat.zero t D is skcons t D, and \
             venvLiftD Nat.zero t D (vconsD t D v r) is r (one Nat.rec iota, then function eta).",
        ),
        "r14_venvSub_up" => (
            &["venvSubD", "wk_up", "r14_val_lift0", "r13_venvD_funext"],
            "SUBSTITUTION COMMUTES WITH VALUATION EXTENSION (corpus venvSub_up, FInterp.lean:199). \
             Its succ branch IS r14_val_lift0 — this is where the semantic weakening lemma is \
             consumed, and why val_psub cannot be proved before val_lift.",
        ),
        "r14_val_psub" => (
            &[
                "wk_psub",
                "venvSubD",
                "r14_venvSub_up",
                "r14_sval_pi_congr",
                "r14_vapply_congr",
                "r13_vd_arr_funext",
            ],
            "THE SEMANTIC SUBSTITUTION LEMMA (corpus val_psub, FInterp.lean:209) — the second \
             constant R13 named as blocked. Its var case is Eq.refl, the payoff of stating \
             wk_psub with a hypothesis rather than with a cutoff: the derivation the operation \
             produces at a variable IS the hypothesis, so the interpretation is the induced \
             valuation on the nose.",
        ),
        "r14_venvSub_scons" => (
            &["venvSubD", "r14_scons_typed", "r13_venvD_funext"],
            "The valuation induced by scons a idsubst IS the extension by a's value (corpus \
             val_inst's valuation half, FInterp.lean:237-243). Both branches Eq.refl.",
        ),
        "r14_val_inst" => (
            &[
                "r14_val_psub",
                "r14_venvSub_scons",
                "r14_sval_cast_term",
                "wk_inst",
            ],
            "Corpus val_inst (FInterp.lean:237), at the KERNEL's own instantiate rather than at a \
             hand-written substitution: val_psub at scons a idsubst, with instantiate_eq_psubst \
             peeled by r14_sval_cast_term and the valuation identified by r14_venvSub_scons.",
        ),
        "r14_beta_step" => (
            &["whnf_step.beta", "beta_reduces.beta"],
            "The head-beta step of an ARBITRARY redex, at the kernel's own contractum. R12's \
             r12_beta_step_general is the bvar-0 body only, because without wk_inst there was no \
             derivation at instantiate b a to pair it with.",
        ),
        "r14_val_beta" => (
            &["r14_val_inst", "wk_inst"],
            "THE CORPUS'S val_beta (FInterp.lean:248), SPEC-SIDE — the head-beta case of val_step \
             in its actual form. R12's r12_sval_beta equates the redex's interpretation with a \
             VALUATION EXTENSION; this equates the interpretations of two TERMS, the redex and \
             the real instantiate contractum, so it composes with r14_beta_step.",
        ),
        "r14_sval_transports_real_beta" => (
            &["r14_val_beta", "vcarD", "Eq.substType"],
            "THE CONTRAST WITH R11, at the real step: membership transports across the real \
             head-beta step at an ARBITRARY shape-typed redex, with the contractum spelled exactly \
             as beta_reduces.beta produces it. r11_candInterp_step_conv_refuted proves candInterp \
             cannot transport membership across even ONE whnf_step of the type.",
        ),
        "r14_lift_bvar0_witness" => (
            &["r14_lift_at_bvar_wkpos"],
            "NON-VACUITY of the index algebra: lift_at (bvar 0) 0 1 IS bvar 1. If lifting were the \
             identity on variables this does not typecheck.",
        ),
        "r14_wk_lift_witness" => (
            &["wk_lift0", "r12_piEnv", "WK.var"],
            "The weakening operation applied at a REAL derivation: R12's all-Sk.ty shape \
             environment with a KIND-of-kinds slot inserted at the head.",
        ),
        "r14_wk_lift_shifts" => (
            &["r14_wk_lift_witness", "r14_lift_bvar0_witness"],
            "THE DISCRIMINATING FORM: after weakening, the old variable is bvar 1 and STILL has \
             shape Sk.ty, even though slot 0 now holds Sk.kd Sk.ty. The paired refusal test feeds \
             the kernel the same derivation claimed at Sk.kd Sk.ty and asserts REJECTION, so this \
             witness is not compatible with a junk operation.",
        ),
        "r14_wk_inst_witness" => (
            &["wk_inst", "r12_beta_contractum_is_arg", "r12_piEnv"],
            "The substitution operation applied at a REAL derivation: substituting sort 0 for the \
             zeroth variable of bvar 0 yields a derivation of sort 0, not of bvar 0 and not of junk.",
        ),
        "r14_val_lift_witness" => (
            &["r14_val_lift0", "r12_piEnv"],
            "val_lift0 at that same weakening: the value of the WEAKENED variable is the ORIGINAL \
             valuation's slot 0, not the inserted value v.",
        ),
        "r14_val_inst_witness" => (
            &["r14_val_inst", "r12_piEnv"],
            "val_inst at that same substitution: the value of instantiate (bvar 0) (sort 0) is the \
             SORT's candidate — the substituted value's interpretation, COMPUTED, not assumed.",
        ),
        _ => (&[], "R14 weakening/substitution operations."),
    }
}

impl Specification {
    /// Register R14: the weakening and substitution operations on `WK`
    /// derivations, and `val_lift` / `val_psub` / `val_inst` / `val_beta`.
    pub(super) fn add_candmodel_construct_r14(&mut self) -> Result<(), SpecError> {
        for item in r14_items() {
            match item {
                R14Item::Def { name, src } => {
                    let (_, desc) = meta(&name);
                    self.add_recursive_def(&src, desc)?;
                }
                R14Item::Thm { name, ty, val } => {
                    let (deps, desc) = meta(&name);
                    add_thm(self, &name, ty, val, deps, desc)?;
                }
            }
        }
        Ok(())
    }
}

#[cfg(test)]
#[path = "candmodel_construct_r14_tests.rs"]
mod tests;
