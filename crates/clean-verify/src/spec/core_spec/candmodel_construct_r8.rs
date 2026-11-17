// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! R8 of the candidate-model construction ladder — the CONVERGENCE rung: the
//! judgment `SynTyL : ListType KExpr -> KExpr -> KExpr -> Type` whose `var`
//! rule is `TypingCtx.var` VERBATIM (concluding at `lift_at A Nat.zero
//! (Nat.succ i)`), which adds `TypingCtx`'s `pi` FORMATION rule at the literal
//! `Level.imax`, and which adds a `let_` rule at the sort-annotated fragment;
//! the fundamental theorem `synTyL_fundamental`; the still-UNCONDITIONAL
//! capstones `synTyL_sn_subst` / `synTyL_sn` / `synTyL_sn_closed`; and the
//! bridge `synTyT_to_synTyL` that subsumes R7 over simple contexts.
//!
//! ## A — what R7 left between `SynTyT` and `TypingCtx`, and what R8 closes
//!
//! R7's own list was: no `const` rule, no `let_` rule, no `pi` formation rule,
//! `SimpleTy` domains only, and a `var` rule that does NOT lift where
//! `TypingCtx.var` does. R8 closes the `var` gap and the `pi` gap outright,
//! and the `let_` gap at a named fragment (§B).
//!
//! ### A.1 The `var` gap, and the correction to R7's diagnosis
//!
//! R7 predicted: *"closing that gap DOES need `RecEnvLiftClosed`, which is
//! discharged and sitting unused one stage earlier."* **Measured here: it does
//! not.** `RecEnvLiftClosed` is what a TERM lift needs — `whnf_acc e ->
//! whnf_acc (lift_at e 0 1)` transports a reduction through a lift, and its
//! iota arm is the blocked one. The `var` gap is a TYPE lift: the term stays
//! `s i`, only the type moves from `A` to `lift_at A Nat.zero (Nat.succ i)`.
//! And R5's `candInterp` reads NOTHING of a type but its Pi-skeleton — every
//! non-Pi former goes to the top candidate `whnf_acc` — while `lift_at`
//! preserves that skeleton exactly. So the whole gap is discharged by
//!
//! ```text
//! candInterp_lift_eq : forall k T d, Eq (KExpr -> Type) (candInterp (lift_at T d k)) (candInterp T)
//! ```
//!
//! one `KExpr.rec` on the TYPE: eight of the ten arms are `Eq.refl` (both
//! sides are the top candidate), the `bvar` arm is a two-case `Nat.rec` on
//! `Nat.sub d i` (`lift_bvar_at` is stuck there, so it needs the split, and
//! both branches are still `bvar`-headed hence still top), and the `pi` arm is
//! two `Eq.cong`s on the two IHs. It is stated as an equality of the two
//! MEMBERSHIP PREDICATES rather than as a pair of implications on purpose:
//! `PiSet` is contravariant in its domain, so an implication-only induction
//! would need both directions carried simultaneously, whereas function
//! equality congruences through `PiSet` in one step and needs no funext (the
//! IHs already equate the families). `candInterp_lift` / `candInterp_unlift`
//! are its two transports.
//!
//! `RecEnvLiftClosed` therefore remains untouched by the ladder, exactly as
//! after R7 — and now for a stated reason rather than by accident.
//!
//! Because `SubstOK` (R6) is unchanged, so are `substOK_idsubst` and
//! `substOK_extend`: R8 adds NO substitution infrastructure. R6 justified
//! `SubstOK`'s missing lift bookkeeping by simple-type closedness; R8 keeps
//! the same `SubstOK` and pays the lift in the `var` ARM of the fundamental
//! theorem, where `candInterp_lift` discharges it for an ARBITRARY looked-up
//! type.
//!
//! ### A.2 The `pi` formation rule
//!
//! `SynTyL.pi` is `TypingCtx.pi` character-for-character up to the judgment
//! name, including the literal `Level.imax n m` (a raw `Level` constructor
//! here, not a smart constructor — R0's `level_imax_ne_zero` / Hurkens-block
//! work is why that matters). Its fundamental-theorem arm is the landed
//! `fundamental_pi` (`dependent_sn_richmodel.rs:3888`) with the `CandModel`
//! law projections swapped for R5 theorems: `red_sort` becomes
//! `candInterp_sort_mem`, `CR1` becomes `candInterp_cr1`, `red_var` becomes
//! `candInterp_var`, `models_extend` becomes `substOK_extend`, and
//! `whnfAcc_pi` + `whnfAcc_of_instantiate_bvar0` +
//! `psubst_scons_instantiate` are consumed unchanged.
//!
//! This is the rung's sharpest strictness fact: `synTyT_no_pi_formation`
//! proves that NO `SynTyT` derivation concludes at a `pi` EXPRESSION in any
//! context at any type (a `KExpr.rec` discriminator over R7's four rules), so
//! `synTyL_pi_formation_witness` types a term R7's judgment cannot reach, and
//! `synTyL_sn_witness` obtains its SN THROUGH R8's capstone.
//!
//! ## B — the `let_` rule: LANDED at the sort-annotated fragment, and the
//! obstruction to the general clause PROVED
//!
//! R1 refuted the per-candidate-set zeta engine (`zeta_expansion_not_generic`)
//! and landed `whnfAcc_zeta_expand` at the BASE whole-SN set only. R5's
//! `candInterp T` is the base set at EVERY non-Pi `T` and `PiSet` at a Pi
//! `T`. So the zeta clause splits exactly there, and R8 lands both halves:
//!
//! - **Positive.** `candInterp_zeta_expand_sort` is the zeta clause through
//!   the contractum at a sort-typed slot: it IS `whnfAcc_zeta_expand`
//!   retyped, because `candInterp (sort m) e` reduces to `whnf_acc e`. On it
//!   rests `SynTyL.letTy`, the rule
//!   `SynTyL G v (sort n) -> SynTyL (cons (sort n) G) b (sort m) ->
//!    SynTyL G (let_ (sort n) v b) (sort m)`.
//!   The annotation must be a literal `sort n` for a reason that is visible
//!   in the proof and not cosmetic: `whnfAcc_zeta_expand`'s contractum family
//!   quantifies over EVERY `whnf_acc v2`, and feeding the body IH needs
//!   `SubstOK (scons v2 s) (cons (sort n) G)`, i.e. `candInterp (sort n) v2`
//!   — which is `whnf_acc v2` only because the annotation's interpretation is
//!   the top candidate. At a Pi annotation the two differ and the family
//!   cannot be built. The DEVELOPMENT half of the family
//!   (`betaStar (psubst (up s) b) b2`) is carried by R7's discharged
//!   `betaStar_inst_transport_env` + `candInterp_betaStar_closed`, so R8
//!   consumes the `RecEnvClosed` discharge exactly as R7 does.
//! - **Obstruction, proved and LOCATED.** `r8_let_not_neutral` :
//!   `Neutral (let_ ty v b) -> Empty` at every `ty v b` — cr3, the only
//!   generic membership introduction a non-top candidate has, is INAPPLICABLE
//!   at the zeta redex itself. `r8_zeta_spine_is_neutral` :
//!   `Neutral (app (let_ ty v b) a)` — one layer out, at the `PiSet`
//!   elimination site, cr3 IS applicable. `r8_zeta_obstruction_located` pairs
//!   them. So the missing clause is named precisely: for a Pi-typed slot,
//!   `candInterp (pi A B) (let_ ty v b)` unfolds to `PiSet`, whose membership
//!   is a statement about `app (let_ ty v b) a`, and proving it needs an
//!   APP-SPINE zeta expansion engine — a five-fold nested `Acc` induction
//!   (`ty`, `v`, `b`, the argument `a`, and the development family) of
//!   `candExp_beta`'s size. R1's refutation says that engine cannot be
//!   obtained per-candidate-set; nothing in R0–R7 contains it at the spine;
//!   R8 does not attempt it and does not pretend the sort fragment is it.
//!
//! ## Premise freedom, unchanged and guarded the same way
//!
//! ```text
//! synTyL_fundamental : SynTyL G e T -> forall s, SubstOK s G -> candInterp T (psubst s e)
//! synTyL_sn_subst    : SynTyL G e T -> forall s, SubstOK s G -> whnf_acc (psubst s e)
//! synTyL_sn          : SynTyL G e T -> whnf_acc e
//! synTyL_sn_closed   : SynTyL nil e T -> whnf_acc e
//! ```
//!
//! carry NO premise of any kind — no `CandModel`, no `RecEnvClosed`, no
//! `RecEnvLiftClosed`, no `DefEnvClosed`, no `EnvAcyclic`. The shape guard
//! refuses every one of those names in the STATEMENT of the capstone chain,
//! of `SynTyL` itself and of the lift unlock, and a complementary guard
//! REQUIRES that the discharged `RecEnvClosed` witness is still consumed
//! (through `betaStar_inst_transport_env`) inside the `letTy` arm.
//!
//! ## The bridge, and its direction
//!
//! `synTyT_to_synTyL : SynTyT G e T -> CtxSimple G -> SynTyL G e T`. The
//! hypothesis is REAL and is the price of the faithful `var` rule: R7's `var`
//! concludes at the looked-up type, R8's at its lift, and the two agree
//! exactly when the looked-up type is lift-inert. `simpleTy_lift`
//! (`SimpleTy T -> lift_at T d k = T` — simple types are closed) supplies
//! that, and `CtxSimple G` (every entry of `G` is a `SimpleTy`) supplies it
//! pointwise. The induction goes through because `SynTyT.lam` ALREADY carries
//! `SimpleTy A`, so `ctxSimple_cons` rebuilds the hypothesis in the extended
//! context — no new side condition anywhere.
//!
//! **The converse is FALSE, not merely unproved**, and that is registered:
//! `synTyL_pi_formation_witness` is a `SynTyL` derivation of a `pi`
//! expression and `synTyT_no_pi_formation` proves `SynTyT` has no such
//! derivation at all. `synTyT_sn_via_synTyL` re-derives R7's capstone through
//! R8's over simple contexts; R7's own `synTyT_sn` remains the unrestricted
//! statement and is NOT superseded.
//!
//! ## Honesty notes (read before quoting)
//!
//! - **Nothing here discharges `M : CandModel tenv`.** `synTyL_sn` is SN for
//!   `SynTyL`, NOT for `TypingCtx`, and must never be described as advancing
//!   `whnf_terminates_well_typed_dependent` (design §6.2).
//! - **What still separates `SynTyL` from `TypingCtx`, after this rung:**
//!   (1) no `const` rule — that is the δ/`redConst` rung, needing a
//!   `WfEnv`/`EnvAcyclic` rank witness for the real reflected env (design B3);
//!   (2) `app` is NON-DEPENDENT (`SynTyL G (app f a) B` where `TypingCtx`
//!   concludes at `instantiate B a`) and `lam` still carries `SimpleTy A`,
//!   both forced by R5's non-dependent Pi clause, whose dependent version is
//!   PROVED non-portable (`r6_dependent_pi_self_reachable`);
//!   (3) the `let_` rule is the sort-annotated fragment only (§B), where
//!   `TypingCtx.let_` is general and concludes at `instantiate B v`;
//!   (4) `lam` has no `TypingCtx G A (sort u)` premise (it has `SimpleTy A`
//!   instead) and `SynTyL` has no conversion rule.
//!   That list is shorter than R7's by two entries and is the honest one.
//! - **The judgment is not total.** `synTyL_not_total`: `r5_omegaLam` — a
//!   strongly normalizing term — is not `SynTyL`-derivable at
//!   `pi (sort 0) (sort 0)` in ANY context. The `micro_has_type`
//!   total-predicate trap guard; no automated gate performs it.
//! - **Every predicate R8 introduces in hypothesis position is WITNESSED
//!   here.** `SynTyL` is concluded by `synTyL_id`, `synTyL_sort_witness`,
//!   `synTyL_var_lift_witness`, `synTyL_pi_formation_witness` and
//!   `synTyL_let_witness`; `CtxSimple` by `ctxSimple_nil` and
//!   `ctxSimple_cons`. Constructors do not count on the supply side, which is
//!   why those are registered definitions and why the ladder guard
//!   `test_candmodel_ladder_premises_are_witnessed` names both.
//! - **Recursor conventions are taken from landed consumers, not guessed.**
//!   ALL FIELDS FIRST, THEN ALL IHs, in constructor order
//!   (`fundamental_general`, R6's and R7's fundamental theorems).
//!   `SynTyL.pi`, `SynTyL.app` and `SynTyL.letTy` each have TWO recursive
//!   premises, `SynTyL.lam` one. Pinned by the shape guard.
//! - **No `fixedIndicesToParams` promotion.** The leading
//!   `(G : ListType KExpr)` is uniform across the six conclusions, but the
//!   `pi`, `lam` and `letTy` recursive premises conclude at
//!   `ListType.cons KExpr _ G`, so the first index is not fixed.
//! - **Prop/Type discipline.** `Eq` is Prop; `candInterp T`, `SynTyL`,
//!   `SimpleTy`, `CtxSimple`, `SubstOK`, `Neutral`, `betaStar`,
//!   `beta_reduces` and `whnf_acc` are Type. `AndType (A : Type) (B : Type)`
//!   is `Type 0`-in and the kernel is NON-CUMULATIVE, so an `AndType` slot may
//!   hold neither an `Eq` nor a `Type 1` term — the lift equalities are
//!   therefore registered as their own constants and never paired.
//!   `candInterp_lift_eq` is the one place the spec equates two `KExpr ->
//!   Type` values, i.e. `Eq` at `Sort 2`; `Eq`, `Eq.refl`, `Eq.trans`,
//!   `Eq.cong` and `Eq.substType` are all declared `(α : Sort u)` in
//!   `foundation_types.rs`, so this is inside the foundation's stated
//!   polymorphism, not a widening of it.
//!
//! ## Census
//!
//! ZERO new axioms: one genuine inductive via `add_inductive`, one plain def
//! via `add_recursive_def`, everything else a value-bearing theorem via
//! `add_definition` with kernel `add_decl` checking. Census-neutral.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

// ==== R8 SOURCES BEGIN (pure string builders; every source in this region is ====
// ==== pre-validated through the stable-toolchain clean-parser harness).      ====

/// `bvar 0` — the canonical irreducible neutral.
const V0: &str = "(KExpr.bvar Nat.zero)";
/// `bvar 1`.
const V1: &str = "(KExpr.bvar (Nat.succ Nat.zero))";
/// `bvar 2` — the LIFTED index the faithful `var` rule produces.
const V2: &str = "(KExpr.bvar (Nat.succ (Nat.succ Nat.zero)))";
/// `sort 0`, the fragment's base type.
const S0: &str = "(KExpr.sort Level.zero)";
/// `sort 1`.
const S1: &str = "(KExpr.sort (Level.succ Level.zero))";
/// The non-dependent function type `pi (sort 0) (sort 0)`.
const PI00: &str = "(KExpr.pi (KExpr.sort Level.zero) (KExpr.sort Level.zero))";
/// `sort (imax 1 1)` — the type `SynTyL.pi` gives `PI00`, with the LITERAL
/// `Level.imax` of `TypingCtx.pi` (not a smart constructor).
const SIMAX11: &str = "(KExpr.sort (Level.imax (Level.succ Level.zero) (Level.succ Level.zero)))";
/// The fragment's identity function, annotated at the base type.
const IDLAM0: &str = "(KExpr.lam (KExpr.sort Level.zero) (KExpr.bvar Nat.zero))";
/// The empty context.
const NILCTX: &str = "(@ListType.nil KExpr)";
/// The one-entry context `[sort 0]`.
const CTX1: &str = "(@ListType.cons KExpr (KExpr.sort Level.zero) (@ListType.nil KExpr))";
/// The one-entry context `[sort 1]` — the context `SynTyL.letTy` opens.
const CTX1S1: &str =
    "(@ListType.cons KExpr (KExpr.sort (Level.succ Level.zero)) (@ListType.nil KExpr))";
/// The TWO-entry context `[sort 0 ; bvar 0]`, whose entry at index 1 is
/// `bvar 0` — a type the lift genuinely MOVES.
const CTX2: &str = "(@ListType.cons KExpr (KExpr.sort Level.zero) (@ListType.cons KExpr (KExpr.bvar Nat.zero) (@ListType.nil KExpr)))";
/// The witness zeta redex `let_ (sort 1) (sort 0) (bvar 0)` — a `let` whose
/// BODY IS THE BOUND VARIABLE, so the contractum is the value.
const LETREDEX: &str = "(KExpr.let_ (KExpr.sort (Level.succ Level.zero)) (KExpr.sort Level.zero) (KExpr.bvar Nat.zero))";

// ================================================================
// Group A — THE VAR UNLOCK: the interpretation is invariant under de Bruijn
// lifting of the TYPE.
// ================================================================

pub(super) const TY_CANDINTERP_LIFT_EQ: &str = "forall (k : Nat) (T : KExpr) (d : Nat), @Eq (KExpr -> Type) (candInterp (lift_at T d k)) (candInterp T)";

pub(super) fn val_candinterp_lift_eq() -> String {
    let ih = |x: &str| {
        format!("forall (qd : Nat), @Eq (KExpr -> Type) (candInterp (lift_at {x} qd k)) (candInterp {x})")
    };
    let motive = "(fun (qT : KExpr) => forall (qd : Nat), @Eq (KExpr -> Type) (candInterp (lift_at qT qd k)) (candInterp qT))";
    // sort: lift_at fixes a sort, both sides are the top candidate.
    let a_sort =
        "(fun (qn : Level) (qd : Nat) => @Eq.refl (KExpr -> Type) (candInterp (KExpr.sort qn)))";
    // bvar: lift_bvar_at is STUCK on Nat.sub qd qi, so the arm splits on it —
    // and both branches are still bvar-headed, hence still the top candidate.
    let lifted_bvar = "(@Nat.rec (fun (_ : Nat) => KExpr) (KExpr.bvar (Nat.add qi k)) (fun (_ : Nat) (_ : KExpr) => KExpr.bvar qi) qj)";
    let lifted_bvar_m = "(@Nat.rec (fun (_ : Nat) => KExpr) (KExpr.bvar (Nat.add qi k)) (fun (_ : Nat) (_ : KExpr) => KExpr.bvar qi) qm)";
    let a_bvar = format!(
        "(fun (qi : Nat) (qd : Nat) => @Nat.rec (fun (qj : Nat) => @Eq (KExpr -> Type) (candInterp {lifted_bvar}) (candInterp (KExpr.bvar qi))) (@Eq.refl (KExpr -> Type) (candInterp (KExpr.bvar qi))) (fun (qm : Nat) (_qih : @Eq (KExpr -> Type) (candInterp {lifted_bvar_m}) (candInterp (KExpr.bvar qi))) => @Eq.refl (KExpr -> Type) (candInterp (KExpr.bvar qi))) (Nat.sub qd qi))"
    );
    let a_app = format!(
        "(fun (qf : KExpr) (qa : KExpr) (_qihf : {}) (_qiha : {}) (qd : Nat) => @Eq.refl (KExpr -> Type) (candInterp (KExpr.app qf qa)))",
        ih("qf"),
        ih("qa")
    );
    let a_lam = format!(
        "(fun (qty : KExpr) (qb : KExpr) (_qihty : {}) (_qihb : {}) (qd : Nat) => @Eq.refl (KExpr -> Type) (candInterp (KExpr.lam qty qb)))",
        ih("qty"),
        ih("qb")
    );
    // pi: THE ONLY ARM THAT DOES WORK. candInterp (pi A B) reduces to
    // PiSet (candInterp A) (fun _ => candInterp B); rewrite each family by its
    // IH. Function equality congruences through PiSet directly — no funext.
    let a_pi = format!(
        "(fun (qA : KExpr) (qB : KExpr) (qihA : {}) (qihB : {}) (qd : Nat) => @Eq.trans (KExpr -> Type) (PiSet (candInterp (lift_at qA qd k)) (fun (_ : KExpr) => candInterp (lift_at qB (Nat.succ qd) k))) (PiSet (candInterp qA) (fun (_ : KExpr) => candInterp (lift_at qB (Nat.succ qd) k))) (PiSet (candInterp qA) (fun (_ : KExpr) => candInterp qB)) (@Eq.cong (KExpr -> Type) (KExpr -> Type) (fun (qF : KExpr -> Type) => PiSet qF (fun (_ : KExpr) => candInterp (lift_at qB (Nat.succ qd) k))) (candInterp (lift_at qA qd k)) (candInterp qA) (qihA qd)) (@Eq.cong (KExpr -> Type) (KExpr -> Type) (fun (qF : KExpr -> Type) => PiSet (candInterp qA) (fun (_ : KExpr) => qF)) (candInterp (lift_at qB (Nat.succ qd) k)) (candInterp qB) (qihB (Nat.succ qd))))",
        ih("qA"),
        ih("qB")
    );
    let a_const = "(fun (qn : Name) (qus : ListType Level) (qd : Nat) => @Eq.refl (KExpr -> Type) (candInterp (KExpr.const qn qus)))";
    let a_let = format!(
        "(fun (qlty : KExpr) (qlv : KExpr) (qlb : KExpr) (_qih1 : {}) (_qih2 : {}) (_qih3 : {}) (qd : Nat) => @Eq.refl (KExpr -> Type) (candInterp (KExpr.let_ qlty qlv qlb)))",
        ih("qlty"),
        ih("qlv"),
        ih("qlb")
    );
    let a_proj = format!(
        "(fun (qps : Name) (qpidx : Nat) (qsub : KExpr) (_qihs : {}) (qd : Nat) => @Eq.refl (KExpr -> Type) (candInterp (KExpr.proj qps qpidx qsub)))",
        ih("qsub")
    );
    let a_lit =
        "(fun (qv : Nat) (qd : Nat) => @Eq.refl (KExpr -> Type) (candInterp (KExpr.lit qv)))";
    format!(
        "fun (k : Nat) (T : KExpr) => @KExpr.rec {motive} {a_sort} {a_bvar} {a_app} {a_lam} {a_pi} {a_const} {a_let} {a_proj} {a_lit} T"
    )
}

pub(super) const TY_CANDINTERP_LIFT: &str = "forall (T : KExpr) (d : Nat) (k : Nat) (e : KExpr), candInterp T e -> candInterp (lift_at T d k) e";

pub(super) const VAL_CANDINTERP_LIFT: &str = "fun (T : KExpr) (d : Nat) (k : Nat) (e : KExpr) (h : candInterp T e) => @Eq.substType (KExpr -> Type) (fun (qF : KExpr -> Type) => qF e) (candInterp T) (candInterp (lift_at T d k)) (@Eq.symm (KExpr -> Type) (candInterp (lift_at T d k)) (candInterp T) (candInterp_lift_eq k T d)) h";

pub(super) const TY_CANDINTERP_UNLIFT: &str = "forall (T : KExpr) (d : Nat) (k : Nat) (e : KExpr), candInterp (lift_at T d k) e -> candInterp T e";

pub(super) const VAL_CANDINTERP_UNLIFT: &str = "fun (T : KExpr) (d : Nat) (k : Nat) (e : KExpr) (h : candInterp (lift_at T d k) e) => @Eq.substType (KExpr -> Type) (fun (qF : KExpr -> Type) => qF e) (candInterp (lift_at T d k)) (candInterp T) (candInterp_lift_eq k T d) h";

/// The lift is not a no-op at a loose variable: this is what makes
/// `candInterp_lift_eq` a THEOREM rather than a restatement of reflexivity.
pub(super) fn ty_r8_lift_moves_index() -> String {
    format!("@Eq KExpr (lift_at {V0} Nat.zero (Nat.succ (Nat.succ Nat.zero))) {V2}")
}

pub(super) fn val_r8_lift_moves_index() -> String {
    format!("@Eq.refl KExpr {V2}")
}

/// ...and it moves UNDER a `pi` binder too, at the shifted cutoff — the only
/// arm of `candInterp_lift_eq` that is not `Eq.refl`.
pub(super) fn ty_r8_lift_moves_under_pi() -> String {
    format!(
        "@Eq KExpr (lift_at (KExpr.pi {S0} {V1}) Nat.zero (Nat.succ Nat.zero)) (KExpr.pi {S0} {V2})"
    )
}

pub(super) fn val_r8_lift_moves_under_pi() -> String {
    format!("@Eq.refl KExpr (KExpr.pi {S0} {V2})")
}

/// The interpretation is unmoved where the syntax moved.
pub(super) fn ty_r8_candinterp_lift_bvar_witness() -> String {
    format!("@Eq (KExpr -> Type) (candInterp (lift_at {V0} Nat.zero (Nat.succ (Nat.succ Nat.zero)))) (candInterp {V0})")
}

pub(super) fn val_r8_candinterp_lift_bvar_witness() -> String {
    format!("candInterp_lift_eq (Nat.succ (Nat.succ Nat.zero)) {V0} Nat.zero")
}

// ================================================================
// Group B — the ZETA clause: the positive half at a sort-typed slot, and the
// obstruction to the Pi-typed slot, LOCATED.
// ================================================================

pub(super) const TY_CANDINTERP_ZETA_EXPAND_SORT: &str = "forall (n : Level) (m : Level) (v : KExpr) (b : KExpr), whnf_acc v -> whnf_acc b -> (forall (b2 : KExpr), betaStar b b2 -> forall (v2 : KExpr), candInterp (KExpr.sort n) v2 -> candInterp (KExpr.sort m) (instantiate b2 v2)) -> candInterp (KExpr.sort m) (KExpr.let_ (KExpr.sort n) v b)";

pub(super) const VAL_CANDINTERP_ZETA_EXPAND_SORT: &str = "fun (n : Level) (m : Level) (v : KExpr) (b : KExpr) (hv : whnf_acc v) (hb : whnf_acc b) (hfam : forall (b2 : KExpr), betaStar b b2 -> forall (v2 : KExpr), candInterp (KExpr.sort n) v2 -> candInterp (KExpr.sort m) (instantiate b2 v2)) => whnfAcc_zeta_expand (KExpr.sort n) (whnfAcc_sort n) b hb hfam v hv";

pub(super) const TY_R8_LET_NOT_NEUTRAL: &str =
    "forall (ty : KExpr) (v : KExpr) (b : KExpr), Neutral (KExpr.let_ ty v b) -> Empty";

pub(super) const VAL_R8_LET_NOT_NEUTRAL: &str =
    "fun (ty : KExpr) (v : KExpr) (b : KExpr) (h : Neutral (KExpr.let_ ty v b)) => h";

pub(super) const TY_R8_ZETA_SPINE_IS_NEUTRAL: &str = "forall (ty : KExpr) (v : KExpr) (b : KExpr) (a : KExpr), Neutral (KExpr.app (KExpr.let_ ty v b) a)";

pub(super) const VAL_R8_ZETA_SPINE_IS_NEUTRAL: &str =
    "fun (ty : KExpr) (v : KExpr) (b : KExpr) (a : KExpr) => ConstFreeUnit.triv";

pub(super) const TY_R8_ZETA_OBSTRUCTION_LOCATED: &str = "forall (ty : KExpr) (v : KExpr) (b : KExpr) (a : KExpr), AndType (Neutral (KExpr.app (KExpr.let_ ty v b) a)) (Neutral (KExpr.let_ ty v b) -> Empty)";

pub(super) const VAL_R8_ZETA_OBSTRUCTION_LOCATED: &str = "fun (ty : KExpr) (v : KExpr) (b : KExpr) (a : KExpr) => @AndType.intro (Neutral (KExpr.app (KExpr.let_ ty v b) a)) (Neutral (KExpr.let_ ty v b) -> Empty) ConstFreeUnit.triv (fun (h : Neutral (KExpr.let_ ty v b)) => h)";

// ================================================================
// Group C — the CONVERGED judgment.
// ================================================================

/// `TypingCtx.var`'s rule, transcribed. Spelled once so the inductive source
/// and the shape guard cannot drift apart.
const VAR_RULE_LIFTED: &str = "| var : forall (G : ListType KExpr) (i : Nat) (A : KExpr), @Eq (OptionType KExpr) (ctx_lookup G i) (@OptionType.some KExpr A) -> SynTyL G (KExpr.bvar i) (lift_at A Nat.zero (Nat.succ i))";

/// `TypingCtx.pi`'s formation rule, transcribed — including the literal
/// `Level.imax`.
const PI_RULE_IMAX: &str = "| pi : forall (G : ListType KExpr) (A : KExpr) (B : KExpr) (n : Level) (m : Level), SynTyL G A (KExpr.sort n) -> SynTyL (@ListType.cons KExpr A G) B (KExpr.sort m) -> SynTyL G (KExpr.pi A B) (KExpr.sort (Level.imax n m))";

/// The zeta rule, at the sort-annotated fragment §B licenses.
const LET_RULE_SORT: &str = "| letTy : forall (G : ListType KExpr) (n : Level) (m : Level) (v : KExpr) (b : KExpr), SynTyL G v (KExpr.sort n) -> SynTyL (@ListType.cons KExpr (KExpr.sort n) G) b (KExpr.sort m) -> SynTyL G (KExpr.let_ (KExpr.sort n) v b) (KExpr.sort m)";

pub(super) fn src_syn_ty_l() -> String {
    format!(
        "inductive SynTyL : ListType KExpr -> KExpr -> KExpr -> Type\n\
         {VAR_RULE_LIFTED}\n\
         | sort : forall (G : ListType KExpr) (n : Level), SynTyL G (KExpr.sort n) (KExpr.sort (Level.succ n))\n\
         {PI_RULE_IMAX}\n\
         | app : forall (G : ListType KExpr) (A : KExpr) (B : KExpr) (f : KExpr) (a : KExpr), SynTyL G f (KExpr.pi A B) -> SynTyL G a A -> SynTyL G (KExpr.app f a) B\n\
         | lam : forall (G : ListType KExpr) (A : KExpr) (B : KExpr) (b : KExpr), SimpleTy A -> SynTyL (@ListType.cons KExpr A G) b B -> SynTyL G (KExpr.lam A b) (KExpr.pi A B)\n\
         {LET_RULE_SORT}"
    )
}

// ================================================================
// Group D — the fundamental theorem and the capstones.
// ================================================================

pub(super) const TY_SYNTYL_FUNDAMENTAL: &str = "forall (G : ListType KExpr) (e : KExpr) (T : KExpr), SynTyL G e T -> forall (s : Nat -> KExpr), SubstOK s G -> candInterp T (psubst s e)";

pub(super) fn val_syntyl_fundamental() -> String {
    let motive = "(fun (qG : ListType KExpr) (qe : KExpr) (qT : KExpr) (_ : SynTyL qG qe qT) => forall (qs : Nat -> KExpr), SubstOK qs qG -> candInterp qT (psubst qs qe))";
    // var: THE RUNG. The SubstOK lookup gives membership at the UNLIFTED type;
    // candInterp_lift carries it to the lifted one, which is what
    // TypingCtx.var's conclusion demands. psubst qs (bvar qi) is defeq qs qi.
    let m_var = "(fun (qG : ListType KExpr) (qi : Nat) (qA : KExpr) (qhget : @Eq (OptionType KExpr) (ctx_lookup qG qi) (@OptionType.some KExpr qA)) (qs : Nat -> KExpr) (qhs : SubstOK qs qG) => candInterp_lift qA Nat.zero (Nat.succ qi) (qs qi) (qhs qi qA qhget))";
    // sort: red_sort at the interpretation, with the landed SN of sorts.
    let m_sort = "(fun (qG : ListType KExpr) (qn : Level) (qs : Nat -> KExpr) (_qhs : SubstOK qs qG) => candInterp_sort_mem (Level.succ qn) (KExpr.sort qn) (whnfAcc_sort qn))";
    // The extended-context closing substitution at the fresh variable, and the
    // SN of a substituted body under a binder — the landed fundamental_pi
    // idiom, reused by both the pi arm and the letTy arm.
    let fresh_ext = |dom: &str| {
        format!("(substOK_extend qs qG {dom} (KExpr.bvar Nat.zero) (candInterp_var {dom} Nat.zero) qhs)")
    };
    let body_acc = |ihname: &str, cod: &str, body: &str, dom: &str| {
        format!(
            "(whnfAcc_of_instantiate_bvar0 (psubst (up qs) {body}) (@Eq.substType KExpr (fun (qw : KExpr) => whnf_acc qw) (psubst (scons (KExpr.bvar Nat.zero) qs) {body}) (instantiate (psubst (up qs) {body}) (KExpr.bvar Nat.zero)) (psubst_scons_instantiate {body} (KExpr.bvar Nat.zero) qs) (candInterp_cr1 {cod} (psubst (scons (KExpr.bvar Nat.zero) qs) {body}) ({ihname} (scons (KExpr.bvar Nat.zero) qs) {ext}))))",
            ext = fresh_ext(dom)
        )
    };
    // pi FORMATION: fundamental_pi with the CandModel law projections swapped
    // for R5 theorems.
    let ih_pi_a =
        "forall (qs2 : Nat -> KExpr), SubstOK qs2 qG -> candInterp (KExpr.sort qn) (psubst qs2 qA)";
    let ih_pi_b = "forall (qs2 : Nat -> KExpr), SubstOK qs2 (@ListType.cons KExpr qA qG) -> candInterp (KExpr.sort qm) (psubst qs2 qB)";
    let m_pi = format!(
        "(fun (qG : ListType KExpr) (qA : KExpr) (qB : KExpr) (qn : Level) (qm : Level) (_qhA : SynTyL qG qA (KExpr.sort qn)) (_qhB : SynTyL (@ListType.cons KExpr qA qG) qB (KExpr.sort qm)) (qihA : {ih_pi_a}) (qihB : {ih_pi_b}) (qs : Nat -> KExpr) (qhs : SubstOK qs qG) => candInterp_sort_mem (Level.imax qn qm) (KExpr.pi (psubst qs qA) (psubst (up qs) qB)) (whnfAcc_pi (psubst qs qA) (psubst (up qs) qB) (candInterp_cr1 (KExpr.sort qn) (psubst qs qA) (qihA qs qhs)) {codacc}))",
        codacc = body_acc("qihB", "(KExpr.sort qm)", "qB", "qA")
    );
    // app: pi_elim at the interpretation on the two IHs (non-dependent).
    let m_app = "(fun (qG : ListType KExpr) (qA : KExpr) (qB : KExpr) (qf : KExpr) (qa : KExpr) (_qhf : SynTyL qG qf (KExpr.pi qA qB)) (_qha : SynTyL qG qa qA) (qihf : forall (qs : Nat -> KExpr), SubstOK qs qG -> candInterp (KExpr.pi qA qB) (psubst qs qf)) (qiha : forall (qs : Nat -> KExpr), SubstOK qs qG -> candInterp qA (psubst qs qa)) (qs : Nat -> KExpr) (qhs : SubstOK qs qG) => candInterp_app qA qB (psubst qs qf) (psubst qs qa) (qihf qs qhs) (qiha qs qhs))";
    // lam: R7's arm, unchanged.
    let ih_lam = "forall (qs2 : Nat -> KExpr), SubstOK qs2 (@ListType.cons KExpr qA qG) -> candInterp qB (psubst qs2 qb)";
    let hty = "(@Eq.substType KExpr (fun (qw : KExpr) => whnf_acc qw) qA (psubst qs qA) (@Eq.symm KExpr (psubst qs qA) qA (simpleTy_psubst qA qhA qs)) (simpleTy_whnfAcc qA qhA))";
    let hfam = "(fun (qb2 : KExpr) (qstar : betaStar (psubst (up qs) qb) qb2) (qa : KExpr) (qha : candInterp qA qa) => candInterp_betaStar_closed qB (instantiate (psubst (up qs) qb) qa) (instantiate qb2 qa) (betaStar_inst_transport_env (psubst (up qs) qb) qb2 qstar qa) (@Eq.substType KExpr (fun (qw : KExpr) => candInterp qB qw) (psubst (scons qa qs) qb) (instantiate (psubst (up qs) qb) qa) (psubst_scons_instantiate qb qa qs) (qih (scons qa qs) (substOK_extend qs qG qA qa qha qhs))))";
    let m_lam = format!(
        "(fun (qG : ListType KExpr) (qA : KExpr) (qB : KExpr) (qb : KExpr) (qhA : SimpleTy qA) (_qhb : SynTyL (@ListType.cons KExpr qA qG) qb qB) (qih : {ih_lam}) (qs : Nat -> KExpr) (qhs : SubstOK qs qG) => candInterp_lam qA qB (psubst qs qA) (psubst (up qs) qb) {hty} {bodyacc} {hfam})",
        bodyacc = body_acc("qih", "qB", "qb", "qA")
    );
    // letTy: THE ZETA ARM. whnfAcc_zeta_expand at the base set (which is what
    // candInterp (sort m) IS), with the contractum family built from the body
    // IH at scons v2 qs — closable precisely because candInterp (sort n) v2 is
    // whnf_acc v2 — and carried along the development by R7's DISCHARGED
    // substitution transport plus betaStar-closure.
    let ih_let_v =
        "forall (qs2 : Nat -> KExpr), SubstOK qs2 qG -> candInterp (KExpr.sort qn) (psubst qs2 qv)";
    let ih_let_b = "forall (qs2 : Nat -> KExpr), SubstOK qs2 (@ListType.cons KExpr (KExpr.sort qn) qG) -> candInterp (KExpr.sort qm) (psubst qs2 qb)";
    let let_fam = "(fun (qb2 : KExpr) (qstar : betaStar (psubst (up qs) qb) qb2) (qv2 : KExpr) (qhv2 : whnf_acc qv2) => candInterp_betaStar_closed (KExpr.sort qm) (instantiate (psubst (up qs) qb) qv2) (instantiate qb2 qv2) (betaStar_inst_transport_env (psubst (up qs) qb) qb2 qstar qv2) (@Eq.substType KExpr (fun (qw : KExpr) => candInterp (KExpr.sort qm) qw) (psubst (scons qv2 qs) qb) (instantiate (psubst (up qs) qb) qv2) (psubst_scons_instantiate qb qv2 qs) (qihb (scons qv2 qs) (substOK_extend qs qG (KExpr.sort qn) qv2 qhv2 qhs))))";
    let m_let = format!(
        "(fun (qG : ListType KExpr) (qn : Level) (qm : Level) (qv : KExpr) (qb : KExpr) (_qhv : SynTyL qG qv (KExpr.sort qn)) (_qhb : SynTyL (@ListType.cons KExpr (KExpr.sort qn) qG) qb (KExpr.sort qm)) (qihv : {ih_let_v}) (qihb : {ih_let_b}) (qs : Nat -> KExpr) (qhs : SubstOK qs qG) => whnfAcc_zeta_expand (KExpr.sort qn) (whnfAcc_sort qn) (psubst (up qs) qb) {bodyacc} {let_fam} (psubst qs qv) (qihv qs qhs))",
        bodyacc = body_acc("qihb", "(KExpr.sort qm)", "qb", "(KExpr.sort qn)")
    );
    format!(
        "fun (G : ListType KExpr) (e : KExpr) (T : KExpr) (h : SynTyL G e T) => @SynTyL.rec {motive} {m_var} {m_sort} {m_pi} {m_app} {m_lam} {m_let} G e T h"
    )
}

pub(super) const TY_SYNTYL_SN_SUBST: &str = "forall (G : ListType KExpr) (e : KExpr) (T : KExpr), SynTyL G e T -> forall (s : Nat -> KExpr), SubstOK s G -> whnf_acc (psubst s e)";

pub(super) const VAL_SYNTYL_SN_SUBST: &str = "fun (G : ListType KExpr) (e : KExpr) (T : KExpr) (h : SynTyL G e T) (s : Nat -> KExpr) (hs : SubstOK s G) => candInterp_cr1 T (psubst s e) (synTyL_fundamental G e T h s hs)";

pub(super) const TY_SYNTYL_SN: &str =
    "forall (G : ListType KExpr) (e : KExpr) (T : KExpr), SynTyL G e T -> whnf_acc e";

pub(super) const VAL_SYNTYL_SN: &str = "fun (G : ListType KExpr) (e : KExpr) (T : KExpr) (h : SynTyL G e T) => @Eq.substType KExpr (fun (qw : KExpr) => whnf_acc qw) (psubst idsubst e) e (psubst_id e) (synTyL_sn_subst G e T h idsubst (substOK_idsubst G))";

pub(super) const TY_SYNTYL_SN_CLOSED: &str =
    "forall (e : KExpr) (T : KExpr), SynTyL (@ListType.nil KExpr) e T -> whnf_acc e";

pub(super) const VAL_SYNTYL_SN_CLOSED: &str = "fun (e : KExpr) (T : KExpr) (h : SynTyL (@ListType.nil KExpr) e T) => synTyL_sn (@ListType.nil KExpr) e T h";

// ================================================================
// Group E — the bridge from R7 (and the proof that the converse is FALSE).
// ================================================================

pub(super) const TY_SIMPLETY_LIFT: &str =
    "forall (T : KExpr), SimpleTy T -> forall (d : Nat) (k : Nat), @Eq KExpr (lift_at T d k) T";

pub(super) const VAL_SIMPLETY_LIFT: &str = "fun (T : KExpr) (h : SimpleTy T) => @SimpleTy.rec (fun (qT : KExpr) (_ : SimpleTy qT) => forall (qd : Nat) (qk : Nat), @Eq KExpr (lift_at qT qd qk) qT) (fun (qn : Level) (qd : Nat) (qk : Nat) => @Eq.refl KExpr (KExpr.sort qn)) (fun (qA : KExpr) (qB : KExpr) (_qhA : SimpleTy qA) (_qhB : SimpleTy qB) (qihA : forall (qd : Nat) (qk : Nat), @Eq KExpr (lift_at qA qd qk) qA) (qihB : forall (qd : Nat) (qk : Nat), @Eq KExpr (lift_at qB qd qk) qB) (qd : Nat) (qk : Nat) => @Eq.trans KExpr (KExpr.pi (lift_at qA qd qk) (lift_at qB (Nat.succ qd) qk)) (KExpr.pi qA (lift_at qB (Nat.succ qd) qk)) (KExpr.pi qA qB) (@Eq.cong KExpr KExpr (fun (qw : KExpr) => KExpr.pi qw (lift_at qB (Nat.succ qd) qk)) (lift_at qA qd qk) qA (qihA qd qk)) (@Eq.cong KExpr KExpr (fun (qw : KExpr) => KExpr.pi qA qw) (lift_at qB (Nat.succ qd) qk) qB (qihB (Nat.succ qd) qk))) T h";

pub(super) const SRC_CTX_SIMPLE: &str = "def CtxSimple (G : ListType KExpr) : Type := forall (i : Nat) (A : KExpr), @Eq (OptionType KExpr) (ctx_lookup G i) (@OptionType.some KExpr A) -> SimpleTy A";

pub(super) const TY_CTXSIMPLE_NIL: &str = "CtxSimple (@ListType.nil KExpr)";

pub(super) const VAL_CTXSIMPLE_NIL: &str = "fun (i : Nat) (A : KExpr) (hget : @Eq (OptionType KExpr) (ctx_lookup (@ListType.nil KExpr) i) (@OptionType.some KExpr A)) => option_none_ne_some_type KExpr A (SimpleTy A) hget";

pub(super) const TY_CTXSIMPLE_CONS: &str = "forall (A : KExpr) (G : ListType KExpr), SimpleTy A -> CtxSimple G -> CtxSimple (@ListType.cons KExpr A G)";

pub(super) const VAL_CTXSIMPLE_CONS: &str = "fun (A : KExpr) (G : ListType KExpr) (hA : SimpleTy A) (hG : CtxSimple G) (i : Nat) (A2 : KExpr) (hget : @Eq (OptionType KExpr) (ctx_lookup (@ListType.cons KExpr A G) i) (@OptionType.some KExpr A2)) => @Nat.rec (fun (qi : Nat) => @Eq (OptionType KExpr) (ctx_lookup (@ListType.cons KExpr A G) qi) (@OptionType.some KExpr A2) -> SimpleTy A2) (fun (qh0 : @Eq (OptionType KExpr) (ctx_lookup (@ListType.cons KExpr A G) Nat.zero) (@OptionType.some KExpr A2)) => @Eq.substType KExpr (fun (qw : KExpr) => SimpleTy qw) A A2 (option_some_inj KExpr A A2 qh0) hA) (fun (qk : Nat) (_qih : @Eq (OptionType KExpr) (ctx_lookup (@ListType.cons KExpr A G) qk) (@OptionType.some KExpr A2) -> SimpleTy A2) (qhk : @Eq (OptionType KExpr) (ctx_lookup (@ListType.cons KExpr A G) (Nat.succ qk)) (@OptionType.some KExpr A2)) => hG qk A2 qhk) i hget";

pub(super) const TY_SYNTYT_TO_SYNTYL: &str = "forall (G : ListType KExpr) (e : KExpr) (T : KExpr), SynTyT G e T -> CtxSimple G -> SynTyL G e T";

pub(super) fn val_syntyt_to_syntyl() -> String {
    let motive = "(fun (qG : ListType KExpr) (qe : KExpr) (qT : KExpr) (_ : SynTyT qG qe qT) => CtxSimple qG -> SynTyL qG qe qT)";
    let m_var = "(fun (qG : ListType KExpr) (qi : Nat) (qT : KExpr) (qhget : @Eq (OptionType KExpr) (ctx_lookup qG qi) (@OptionType.some KExpr qT)) (qhc : CtxSimple qG) => @Eq.substType KExpr (fun (qw : KExpr) => SynTyL qG (KExpr.bvar qi) qw) (lift_at qT Nat.zero (Nat.succ qi)) qT (simpleTy_lift qT (qhc qi qT qhget) Nat.zero (Nat.succ qi)) (SynTyL.var qG qi qT qhget))";
    let m_sort =
        "(fun (qG : ListType KExpr) (qn : Level) (_qhc : CtxSimple qG) => SynTyL.sort qG qn)";
    let m_app = "(fun (qG : ListType KExpr) (qA : KExpr) (qB : KExpr) (qf : KExpr) (qa : KExpr) (_qhf : SynTyT qG qf (KExpr.pi qA qB)) (_qha : SynTyT qG qa qA) (qihf : CtxSimple qG -> SynTyL qG qf (KExpr.pi qA qB)) (qiha : CtxSimple qG -> SynTyL qG qa qA) (qhc : CtxSimple qG) => SynTyL.app qG qA qB qf qa (qihf qhc) (qiha qhc))";
    let m_lam = "(fun (qG : ListType KExpr) (qA : KExpr) (qB : KExpr) (qb : KExpr) (qhA : SimpleTy qA) (_qhb : SynTyT (@ListType.cons KExpr qA qG) qb qB) (qih : CtxSimple (@ListType.cons KExpr qA qG) -> SynTyL (@ListType.cons KExpr qA qG) qb qB) (qhc : CtxSimple qG) => SynTyL.lam qG qA qB qb qhA (qih (ctxSimple_cons qA qG qhA qhc)))";
    format!(
        "fun (G : ListType KExpr) (e : KExpr) (T : KExpr) (h : SynTyT G e T) => @SynTyT.rec {motive} {m_var} {m_sort} {m_app} {m_lam} G e T h"
    )
}

pub(super) const TY_SYNTYT_SN_VIA_SYNTYL: &str = "forall (G : ListType KExpr) (e : KExpr) (T : KExpr), SynTyT G e T -> CtxSimple G -> whnf_acc e";

pub(super) const VAL_SYNTYT_SN_VIA_SYNTYL: &str = "fun (G : ListType KExpr) (e : KExpr) (T : KExpr) (h : SynTyT G e T) (hc : CtxSimple G) => synTyL_sn G e T (synTyT_to_synTyL G e T h hc)";

/// `KExpr.rec` discriminator into `Type`: the `pi` constructor maps to
/// `Empty`, every other constructor to `Nat` (the R2/R5/R6 `kexpr_discr`
/// idiom, at the `pi` slot).
fn kexpr_discr_pi() -> String {
    "(@KExpr.rec (fun (_ : KExpr) => Type) (fun (_ : Level) => Nat) (fun (_ : Nat) => Nat) (fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) (fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) (fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Empty) (fun (_ : Name) (_ : ListType Level) => Nat) (fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) (_ : Type) => Nat) (fun (_ : Name) (_ : Nat) (_ : KExpr) (_ : Type) => Nat) (fun (_ : Nat) => Nat))".to_string()
}

pub(super) const TY_SYNTYT_NO_PI_FORMATION: &str = "forall (G : ListType KExpr) (A : KExpr) (B : KExpr) (T : KExpr), SynTyT G (KExpr.pi A B) T -> Empty";

pub(super) fn val_syntyt_no_pi_formation() -> String {
    let d = kexpr_discr_pi();
    let motive = format!(
        "(fun (qG : ListType KExpr) (qe : KExpr) (qT : KExpr) (_ : SynTyT qG qe qT) => {d} qe)"
    );
    let m_var = "(fun (qG : ListType KExpr) (qi : Nat) (qT : KExpr) (_qhget : @Eq (OptionType KExpr) (ctx_lookup qG qi) (@OptionType.some KExpr qT)) => Nat.zero)";
    let m_sort = "(fun (qG : ListType KExpr) (qn : Level) => Nat.zero)";
    // The IH binders are the MOTIVE at the recursive premise's SUBJECT — a
    // STUCK `KExpr.rec` application, NOT `Nat`. Writing `Nat` there is the
    // measured 2026-08-25 failure of this constant: the discriminator only
    // reduces on a constructor, and `qf` / `qa` / `qb` are variables.
    let m_app = format!(
        "(fun (qG : ListType KExpr) (qA : KExpr) (qB : KExpr) (qf : KExpr) (qa : KExpr) (_qhf : SynTyT qG qf (KExpr.pi qA qB)) (_qha : SynTyT qG qa qA) (_qihf : {d} qf) (_qiha : {d} qa) => Nat.zero)"
    );
    let m_lam = format!(
        "(fun (qG : ListType KExpr) (qA : KExpr) (qB : KExpr) (qb : KExpr) (_qhA : SimpleTy qA) (_qhb : SynTyT (@ListType.cons KExpr qA qG) qb qB) (_qih : {d} qb) => Nat.zero)"
    );
    format!(
        "fun (G : ListType KExpr) (A : KExpr) (B : KExpr) (T : KExpr) (h : SynTyT G (KExpr.pi A B) T) => @SynTyT.rec {motive} {m_var} {m_sort} {m_app} {m_lam} G (KExpr.pi A B) T h"
    )
}

// ================================================================
// Group F — witnesses and the non-degeneracy guard.
// ================================================================

pub(super) fn ty_syntyl_id() -> String {
    format!("forall (G : ListType KExpr), SynTyL G {IDLAM0} {PI00}")
}

pub(super) fn val_syntyl_id() -> String {
    format!(
        "fun (G : ListType KExpr) => SynTyL.lam G {S0} {S0} {V0} (SimpleTy.base Level.zero) (SynTyL.var (@ListType.cons KExpr {S0} G) Nat.zero {S0} (@Eq.refl (OptionType KExpr) (@OptionType.some KExpr {S0})))"
    )
}

pub(super) fn ty_syntyl_sort_witness() -> String {
    format!("SynTyL {NILCTX} {S0} {S1}")
}

pub(super) fn val_syntyl_sort_witness() -> String {
    format!("SynTyL.sort {NILCTX} Level.zero")
}

/// THE VAR WITNESS THAT MAKES THE LIFT VISIBLE: at index 1 of a context whose
/// entry is `bvar 0`, the faithful rule types `bvar 1` at `bvar 2`.
pub(super) fn ty_syntyl_var_lift_witness() -> String {
    format!("SynTyL {CTX2} {V1} {V2}")
}

pub(super) fn val_syntyl_var_lift_witness() -> String {
    format!(
        "SynTyL.var {CTX2} (Nat.succ Nat.zero) {V0} (@Eq.refl (OptionType KExpr) (@OptionType.some KExpr {V0}))"
    )
}

pub(super) fn ty_syntyl_pi_formation_witness() -> String {
    format!("SynTyL {NILCTX} {PI00} {SIMAX11}")
}

pub(super) fn val_syntyl_pi_formation_witness() -> String {
    format!(
        "SynTyL.pi {NILCTX} {S0} {S0} (Level.succ Level.zero) (Level.succ Level.zero) (SynTyL.sort {NILCTX} Level.zero) (SynTyL.sort {CTX1} Level.zero)"
    )
}

pub(super) fn ty_syntyl_let_witness() -> String {
    format!("SynTyL {NILCTX} {LETREDEX} {S1}")
}

pub(super) fn val_syntyl_let_witness() -> String {
    format!(
        "SynTyL.letTy {NILCTX} (Level.succ Level.zero) (Level.succ Level.zero) {S0} {V0} (SynTyL.sort {NILCTX} Level.zero) (SynTyL.var {CTX1S1} Nat.zero {S1} (@Eq.refl (OptionType KExpr) (@OptionType.some KExpr {S1})))"
    )
}

/// The let witness's body genuinely ZETA-STEPS.
pub(super) fn ty_r8_let_body_fires() -> String {
    format!("whnf_step {LETREDEX} (instantiate {V0} {S0})")
}

pub(super) fn val_r8_let_body_fires() -> String {
    format!("@whnf_step.beta {LETREDEX} (instantiate {V0} {S0}) (beta_reduces.zeta {S1} {S0} {V0})")
}

/// SN of a `pi` EXPRESSION, obtained THROUGH the capstone — a term R7's
/// judgment cannot type at all (`synTyT_no_pi_formation`).
pub(super) fn ty_syntyl_sn_witness() -> String {
    format!("whnf_acc {PI00}")
}

pub(super) fn val_syntyl_sn_witness() -> String {
    format!("synTyL_sn {NILCTX} {PI00} {SIMAX11} synTyL_pi_formation_witness")
}

/// SN of a live ZETA REDEX, obtained THROUGH the capstone.
pub(super) fn ty_syntyl_let_sn_witness() -> String {
    format!("whnf_acc {LETREDEX}")
}

pub(super) fn val_syntyl_let_sn_witness() -> String {
    format!("synTyL_sn {NILCTX} {LETREDEX} {S1} synTyL_let_witness")
}

pub(super) fn ty_syntyl_not_total() -> String {
    format!("forall (G : ListType KExpr), SynTyL G r5_omegaLam {PI00} -> Empty")
}

pub(super) fn val_syntyl_not_total() -> String {
    format!(
        "fun (G : ListType KExpr) (h : SynTyL G r5_omegaLam {PI00}) => candInterp_pi_not_total (@Eq.substType KExpr (fun (qw : KExpr) => candInterp {PI00} qw) (psubst idsubst r5_omegaLam) r5_omegaLam (psubst_id r5_omegaLam) (synTyL_fundamental G r5_omegaLam {PI00} h idsubst (substOK_idsubst G)))"
    )
}

// ==== R8 SOURCES END ====

/// Register one value-bearing theorem (R6/R7's helper, verbatim).
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

impl Specification {
    /// Register the R8 lift unlock, the CONVERGED typing judgment `SynTyL`
    /// (faithful `TypingCtx.var`, `TypingCtx.pi` formation at the literal
    /// `Level.imax`, and a sort-annotated `let_`), its fundamental theorem,
    /// the unconditional SN capstones, the `CtxSimple` bridge subsuming R7,
    /// the proof that the converse bridge is FALSE, and the discriminating
    /// witnesses.
    ///
    /// MUST be registered AFTER `add_candmodel_construct_r7` (`SynTyT`,
    /// `betaStar_inst_transport_env`, `candInterp_betaStar_closed`), which
    /// itself sits after `add_the_red_env_faithful_discharge`. Also requires
    /// `add_candmodel_construct_r0..r6` (`whnfAcc_zeta_expand`, the
    /// `candInterp` layer, `PiSet`, `SimpleTy` + its lemmas, `SubstOK` +
    /// `substOK_idsubst`/`substOK_extend`, `r5_omegaLam`,
    /// `candInterp_pi_not_total`), `add_dependent_sn_richmodel`
    /// (`ctx_lookup`, the psubst calculus, `psubst_scons_instantiate`,
    /// `whnfAcc_of_instantiate_bvar0`, `whnfAcc_sort`, `whnfAcc_pi`,
    /// `Neutral`), `add_whnf_reduction` (`beta_reduces`, `whnf_step`,
    /// `whnf_acc`) and `add_expr_model` (`KExpr`, `Level`, `lift_at`,
    /// `instantiate`).
    pub(super) fn add_candmodel_construct_r8(&mut self) -> Result<(), SpecError> {
        // --- Group A: the var unlock ---
        add_thm(
            self,
            "candInterp_lift_eq",
            TY_CANDINTERP_LIFT_EQ.to_string(),
            val_candinterp_lift_eq(),
            &["candInterp", "lift_at", "PiSet", "Eq.cong", "Eq.trans"],
            "THE R8 UNLOCK: R5's type interpretation is INVARIANT under de Bruijn lifting of the \
             TYPE — candInterp (lift_at T d k) and candInterp T are the SAME membership \
             predicate, at every T, d and k. One KExpr.rec on T generalizing the cutoff. Eight of \
             the ten arms are Eq.refl because candInterp sends every non-Pi former to the top \
             candidate whnf_acc and lift_at preserves the former; the bvar arm is a two-case \
             Nat.rec on Nat.sub d i (lift_bvar_at is STUCK there, and both branches are still \
             bvar-headed hence still top); the pi arm is two Eq.congs on the two IHs, using that \
             candInterp (pi A B) reduces to PiSet (candInterp A) (fun _ => candInterp B). Stated \
             as an equality of the two KExpr -> Type values rather than as a pair of implications \
             ON PURPOSE: PiSet is CONTRAVARIANT in its domain, so an implication-only induction \
             would have to carry both directions simultaneously, whereas function equality \
             congruences through PiSet in one step and needs NO funext (the IHs already equate the \
             families). CORRECTION TO R7'S DIAGNOSIS: R7 predicted this gap needs \
             RecEnvLiftClosed. It does not — that discharge is what a TERM lift needs (whnf_acc e \
             -> whnf_acc (lift_at e 0 1), whose iota arm is the blocked one), and the var gap is a \
             TYPE lift, where the term is unmoved. RecEnvLiftClosed stays untouched by the whole \
             ladder. Eq at Sort 2 here (KExpr -> Type is Type 1) is inside the foundation's stated \
             polymorphism: Eq, Eq.refl, Eq.trans, Eq.cong and Eq.substType are all declared \
             (alpha : Sort u). Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "candInterp_lift",
            TY_CANDINTERP_LIFT.to_string(),
            VAL_CANDINTERP_LIFT.to_string(),
            &["candInterp_lift_eq", "Eq.substType", "Eq.symm"],
            "The forward transport of the unlock: membership at T is membership at lift_at T d k, \
             by Eq.substType along candInterp_lift_eq at the pointwise motive (fun F => F e). This \
             is the constant the fundamental theorem's var arm applies, and it is the whole cost \
             of making SynTyL.var conclude at lift_at A 0 (i+1) exactly as TypingCtx.var does. \
             Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "candInterp_unlift",
            TY_CANDINTERP_UNLIFT.to_string(),
            VAL_CANDINTERP_UNLIFT.to_string(),
            &["candInterp_lift_eq", "Eq.substType"],
            "The BACKWARD transport, registered because the invariance is genuinely two-way and \
             saying so is the honest scope of the unlock: candInterp is BLIND to type lifting, not \
             merely monotone under it. That blindness is a property of R5's interpretation (only \
             the Pi-skeleton of a type is read), not a property of the metatheory, and it is why \
             the var gap was cheap. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "r8_lift_moves_index",
            ty_r8_lift_moves_index(),
            val_r8_lift_moves_index(),
            &["lift_at", "Eq.refl"],
            "NON-DEGENERACY OF THE UNLOCK, syntax side: lift_at (bvar 0) 0 2 IS bvar 2, by kernel \
             computation (Eq.refl). Without this, candInterp_lift_eq could be read as a \
             restatement of reflexivity; with it, the equated types are demonstrably different \
             terms. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "r8_lift_moves_under_pi",
            ty_r8_lift_moves_under_pi(),
            val_r8_lift_moves_under_pi(),
            &["lift_at", "Eq.refl"],
            "The lift also descends UNDER a pi binder at the SHIFTED cutoff: lift_at (pi (sort 0) \
             (bvar 1)) 0 1 = pi (sort 0) (bvar 2). That is the arm of candInterp_lift_eq which is \
             not Eq.refl, exercised at a concrete type. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "r8_candInterp_lift_bvar_witness",
            ty_r8_candinterp_lift_bvar_witness(),
            val_r8_candinterp_lift_bvar_witness(),
            &["candInterp_lift_eq"],
            "...and the interpretation is nevertheless UNMOVED there: candInterp (lift_at (bvar 0) \
             0 2) is candInterp (bvar 0). Read against r8_lift_moves_index, this is the rung's \
             thesis in two constants — the syntax moves, the semantics does not. Zero axiom_deps.",
        )?;

        // --- Group B: the zeta clause and its located obstruction ---
        add_thm(
            self,
            "candInterp_zeta_expand_sort",
            TY_CANDINTERP_ZETA_EXPAND_SORT.to_string(),
            VAL_CANDINTERP_ZETA_EXPAND_SORT.to_string(),
            &[
                "whnfAcc_zeta_expand",
                "whnfAcc_sort",
                "candInterp",
                "betaStar",
            ],
            "THE ZETA CLAUSE THROUGH THE CONTRACTUM, at a SORT-TYPED slot: let_ (sort n) v b \
             inhabits candInterp (sort m) whenever v and b are SN and every betaStar-development \
             of b, instantiated at every member of the ANNOTATION's interpretation, does. It is \
             R1's whnfAcc_zeta_expand retyped and nothing more — candInterp (sort m) e REDUCES to \
             whnf_acc e — which is exactly the point: R5's candInterp IS the base whole-SN set at \
             every non-Pi type, and R1's engine exists at the base set. The annotation must be a \
             literal sort for a reason visible in the proof: whnfAcc_zeta_expand's contractum \
             family quantifies over EVERY whnf_acc v2, and feeding a typing IH with it needs \
             candInterp (sort n) v2, which IS whnf_acc v2 only because the annotation's \
             interpretation is the top candidate. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "r8_let_not_neutral",
            TY_R8_LET_NOT_NEUTRAL.to_string(),
            VAL_R8_LET_NOT_NEUTRAL.to_string(),
            &["Neutral"],
            "THE ZETA OBSTRUCTION, half one: a let_ is NEVER Neutral — Neutral's let_ arm is \
             unconditionally Empty, so the identity function has this type. cr3 is the ONLY \
             generic membership introduction a non-top candidate has, and it demands Neutral of \
             the term it introduces. So at a Pi-typed slot no cr3 argument can reach a zeta redex \
             AT ALL, which is the mechanism behind R1's zeta_expansion_not_generic (that \
             refutation exhibits a genuine candidate set excluding a specific let_ redex). Zero \
             axiom_deps.",
        )?;
        add_thm(
            self,
            "r8_zeta_spine_is_neutral",
            TY_R8_ZETA_SPINE_IS_NEUTRAL.to_string(),
            VAL_R8_ZETA_SPINE_IS_NEUTRAL.to_string(),
            &["Neutral", "ConstFreeUnit.triv"],
            "THE ZETA OBSTRUCTION, half two: one layer OUT, at the app spine, cr3 IS applicable — \
             Neutral's app arm is unconditional (the head is irrelevant), so app (let_ ty v b) a is \
             Neutral by ConstFreeUnit.triv. This is where the missing clause would have to be \
             proved, because candInterp (pi A B) e unfolds to PiSet, whose membership is a \
             statement about app e a and not about e. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "r8_zeta_obstruction_located",
            TY_R8_ZETA_OBSTRUCTION_LOCATED.to_string(),
            VAL_R8_ZETA_OBSTRUCTION_LOCATED.to_string(),
            &["AndType.intro", "Neutral", "ConstFreeUnit.triv"],
            "THE OBSTRUCTION AS ONE KERNEL-CHECKED CONSTANT, so the scope of B is a fact rather \
             than prose: at every ty, v, b, a, the app spine over a zeta redex IS Neutral and the \
             zeta redex itself is NOT. Therefore the Pi-typed zeta clause is not blocked by \
             neutrality per se — it is DISPLACED to the spine, where proving PiSet membership for \
             app (let_ ty v b) a requires a five-fold nested Acc induction (ty, v, b, the argument \
             a, and the development family) of candExp_beta's size, over the complete reduct set \
             of an app whose head is a let_. Nothing in R0-R7 contains that engine, R1 PROVED it \
             cannot be obtained per-candidate-set, and R8 does not attempt it: SynTyL.letTy is the \
             sort-annotated fragment and is not described as more. Both AndType slots are Type \
             (Neutral is Type-valued), as a non-cumulative AndType requires. Zero axiom_deps.",
        )?;

        // --- Group C: the converged judgment ---
        self.add_inductive(
            &src_syn_ty_l(),
            "SynTyL G e T — THE CONVERGED TYPING JUDGMENT of the ladder, and the closest one yet \
             to the spec's own TypingCtx. Six rules. TWO of them are TypingCtx's transcribed: var \
             concludes at lift_at A Nat.zero (Nat.succ i) from ctx_lookup G i (R7's SynTyT.var did \
             NOT lift), and pi is the FORMATION rule TypingCtx G A (sort n) -> TypingCtx (cons A \
             G) B (sort m) -> TypingCtx G (pi A B) (sort (Level.imax n m)) with the LITERAL raw \
             Level.imax constructor, which R7 had no analogue of at all. letTy is TypingCtx.let_ \
             restricted to a sort ANNOTATION and a sort-typed body — the fragment where R1's \
             base-set zeta engine applies (see candInterp_zeta_expand_sort and \
             r8_zeta_obstruction_located for exactly why it stops there). sort, app and lam are \
             R7's, unchanged: app stays NON-DEPENDENT and lam keeps SimpleTy A, both forced by \
             R5's non-dependent Pi clause whose dependent version is PROVED non-portable \
             (r6_dependent_pi_self_reachable). The judgment mentions NO candInterp, NO CandModel \
             and no closedness premise; the shape guard refuses all of them. Strict positivity is \
             immediate (every recursive premise is a bare SynTyL). No fixedIndicesToParams \
             promotion: the leading (G : ListType KExpr) is uniform across the six conclusions but \
             the pi, lam and letTy premises conclude at ListType.cons KExpr _ G. SCOPE: still \
             narrower than TypingCtx — no const rule, non-dependent app, SimpleTy lam domains, \
             sort-annotated let only, no conversion rule — and nothing about it advances M : \
             CandModel tenv. Not total: synTyL_not_total. ZERO new axioms.",
        )?;

        // --- Group D: the fundamental theorem and the capstones ---
        add_thm(
            self,
            "synTyL_fundamental",
            TY_SYNTYL_FUNDAMENTAL.to_string(),
            val_syntyl_fundamental(),
            &[
                "SynTyL.rec",
                "SubstOK",
                "candInterp_lift",
                "candInterp_sort_mem",
                "candInterp_app",
                "candInterp_lam",
                "candInterp_cr1",
                "candInterp_var",
                "candInterp_betaStar_closed",
                "betaStar_inst_transport_env",
                "whnfAcc_zeta_expand",
                "whnfAcc_pi",
                "whnfAcc_sort",
                "whnfAcc_of_instantiate_bvar0",
                "simpleTy_psubst",
                "simpleTy_whnfAcc",
                "substOK_extend",
                "psubst_scons_instantiate",
                "Eq.substType",
            ],
            "THE FUNDAMENTAL THEOREM for the CONVERGED judgment: every SynTyL-derivable term \
             inhabits its type's interpretation at every closing substitution. One SynTyL.rec with \
             a full four-binder motive and six minors. THE VAR ARM IS THE RUNG: SubstOK's lookup \
             gives membership at the UNLIFTED declared type and candInterp_lift carries it to \
             lift_at A 0 (i+1), which is what the faithful rule concludes at — so R6's SubstOK is \
             reused UNCHANGED and R8 adds no substitution infrastructure at all (R6 justified the \
             missing lift bookkeeping by simple-type closedness; R8 pays it here, for an ARBITRARY \
             looked-up type). THE PI ARM is the landed fundamental_pi \
             (dependent_sn_richmodel.rs:3888) with the CandModel law projections swapped for R5 \
             theorems: red_sort becomes candInterp_sort_mem, CR1 becomes candInterp_cr1, red_var \
             becomes candInterp_var, models_extend becomes substOK_extend, and whnfAcc_pi + \
             whnfAcc_of_instantiate_bvar0 + psubst_scons_instantiate are consumed unchanged. THE \
             LETTY ARM is whnfAcc_zeta_expand at the base set (which is what candInterp at a sort \
             IS), with the contractum family built from the body IH at scons v2 s — closable \
             precisely because candInterp (sort n) v2 reduces to whnf_acc v2 — and carried along \
             the development by R7's DISCHARGED betaStar_inst_transport_env plus \
             candInterp_betaStar_closed, so R8 consumes the RecEnvClosed discharge exactly as R7 \
             does. sort/app/lam are R7's arms verbatim. Carries NO premise: no CandModel, no \
             RecEnvClosed, no RecEnvLiftClosed, no DefEnvClosed. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "synTyL_sn_subst",
            TY_SYNTYL_SN_SUBST.to_string(),
            VAL_SYNTYL_SN_SUBST.to_string(),
            &["synTyL_fundamental", "candInterp_cr1"],
            "SN OF EVERY CLOSING INSTANCE for the converged judgment: SynTyL G e T implies \
             whnf_acc (psubst s e) for every s that closes G — the fundamental theorem composed \
             with R5's cr1 projection. UNCONDITIONAL. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "synTyL_sn",
            TY_SYNTYL_SN.to_string(),
            VAL_SYNTYL_SN.to_string(),
            &["synTyL_sn_subst", "substOK_idsubst", "psubst_id"],
            "THE R8 CAPSTONE — UNCONDITIONAL strong normalization for the CONVERGED judgment: \
             SynTyL G e T implies whnf_acc e, at an ARBITRARY context, for the spec's FULL \
             env-fixed one-step reduction (beta, zeta, iota at red_rec the_red_env with full \
             congruence, and delta at red_def the_red_env). Instantiate synTyL_sn_subst at idsubst \
             and cancel with psubst_id. NO carried premise of any kind (pinned by the \
             premise-freedom shape guard). WHAT IS NEW OVER R7: the terms this reaches include pi \
             EXPRESSIONS (synTyL_pi_formation_witness — and synTyT_no_pi_formation proves R7's \
             judgment reaches none of them), zeta redexes (synTyL_let_witness), and variables at \
             non-zero indices typed at their LIFTED declared type \
             (synTyL_var_lift_witness). HONESTY: this is SN for SynTyL, NOT for TypingCtx — it \
             neither discharges nor advances the M : CandModel tenv hypothesis of \
             whnf_terminates_well_typed_dependent, and must never be described as doing so (design \
             section 6.2). Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "synTyL_sn_closed",
            TY_SYNTYL_SN_CLOSED.to_string(),
            VAL_SYNTYL_SN_CLOSED.to_string(),
            &["synTyL_sn"],
            "The closed-term corollary: SynTyL nil e T implies whnf_acc e. A one-line \
             specialization of synTyL_sn, which already holds at every context. Zero axiom_deps.",
        )?;

        // --- Group E: the bridge from R7 ---
        add_thm(
            self,
            "simpleTy_lift",
            TY_SIMPLETY_LIFT.to_string(),
            VAL_SIMPLETY_LIFT.to_string(),
            &["SimpleTy.rec", "lift_at", "Eq.trans", "Eq.cong", "Eq.refl"],
            "A SIMPLE TYPE IS LIFT-INERT: lift_at T d k = T at every cutoff and amount, by \
             SimpleTy.rec generalizing the cutoff — a simple type is built from sort and pi only, \
             hence closed, hence untouched by a lift. This is the exact hinge of the bridge below: \
             R7's SynTyT.var concludes at the LOOKED-UP type and R8's SynTyL.var at its lift, and \
             the two agree precisely on lift-inert types. Zero axiom_deps.",
        )?;
        self.add_recursive_def(
            SRC_CTX_SIMPLE,
            "CtxSimple G — every entry of the context G is a SimpleTy. The pointwise hypothesis \
             the R7-to-R8 bridge needs, spelled in SubstOK's own shape (a lookup-indexed def, not \
             a new inductive, so no recursor and no inversion lemma are minted). Type-valued plain \
             def.",
        )?;
        add_thm(
            self,
            "ctxSimple_nil",
            TY_CTXSIMPLE_NIL.to_string(),
            VAL_CTXSIMPLE_NIL.to_string(),
            &["CtxSimple", "ctx_lookup", "option_none_ne_some_type"],
            "The EMPTY context is simple, vacuously: ctx_lookup nil i REDUCES to none, so the \
             lookup hypothesis is none = some A and option_none_ne_some_type eliminates it into \
             the Type-valued goal SimpleTy A. Also a PREMISE-SATISFIABILITY WITNESS for CtxSimple \
             (constructors do not count on the supply side, and a def has none). Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "ctxSimple_cons",
            TY_CTXSIMPLE_CONS.to_string(),
            VAL_CTXSIMPLE_CONS.to_string(),
            &[
                "CtxSimple",
                "Nat.rec",
                "ctx_lookup",
                "option_some_inj",
                "Eq.substType",
            ],
            "Extending a simple context by a simple type keeps it simple, by Nat.rec on the \
             looked-up index (substOK_extend's proof shape verbatim): index zero is the new entry \
             transported along option_some_inj, and every successor index falls through to the \
             tail. This is what makes the bridge's lam arm go through WITHOUT a new side \
             condition: SynTyT.lam already carries SimpleTy A, which is exactly the field this \
             consumes. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "synTyT_to_synTyL",
            TY_SYNTYT_TO_SYNTYL.to_string(),
            val_syntyt_to_syntyl(),
            &[
                "SynTyT.rec",
                "SynTyL.var",
                "SynTyL.sort",
                "SynTyL.app",
                "SynTyL.lam",
                "CtxSimple",
                "simpleTy_lift",
                "ctxSimple_cons",
                "Eq.substType",
            ],
            "THE BRIDGE: every R7 derivation over a SIMPLE context is an R8 derivation. SynTyT.rec \
             with the motive CtxSimple qG -> SynTyL qG qe qT; sort and app map \
             constructor-for-constructor, the lam arm rebuilds the context hypothesis by \
             ctxSimple_cons on the SimpleTy field the rule already carries, and the VAR arm is \
             where the hypothesis is spent: SynTyL.var concludes at lift_at T 0 (i+1) and \
             simpleTy_lift collapses that to T. THE HYPOTHESIS IS REAL AND IS THE PRICE OF THE \
             FAITHFUL RULE — it is not a proof artifact: on a context entry the lift MOVES \
             (r8_lift_moves_index), the two judgments assign genuinely different types to the same \
             variable, and synTyL_var_lift_witness exhibits the R8 side of that. THE CONVERSE IS \
             FALSE, not merely unproved: synTyL_pi_formation_witness is a SynTyL derivation of a \
             pi expression and synTyT_no_pi_formation proves SynTyT has none, in any context at \
             any type. R7's own synTyT_sn remains the unrestricted statement and is NOT \
             superseded. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "synTyT_sn_via_synTyL",
            TY_SYNTYT_SN_VIA_SYNTYL.to_string(),
            VAL_SYNTYT_SN_VIA_SYNTYL.to_string(),
            &["synTyL_sn", "synTyT_to_synTyL"],
            "R7's capstone RE-DERIVED THROUGH R8's, over simple contexts: SynTyT G e T and \
             CtxSimple G give whnf_acc e. Registered so the subsumption is a kernel-checked fact \
             rather than a claim about two developments that look alike — and stated with its \
             hypothesis, because R7's synTyT_sn holds at EVERY context and this does not. That \
             asymmetry is the honest content of the bridge. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "synTyT_no_pi_formation",
            TY_SYNTYT_NO_PI_FORMATION.to_string(),
            val_syntyt_no_pi_formation(),
            &["SynTyT.rec", "KExpr.rec"],
            "R8 IS STRICTLY WIDER, PROVED: NO SynTyT derivation concludes at a pi EXPRESSION, in \
             any context, at any type. SynTyT.rec against a KExpr.rec discriminator that sends the \
             pi constructor to Empty and every other constructor to Nat; each of R7's four rules \
             concludes at a bvar, a sort, an app or a lam, so every minor is Nat.zero and the \
             recursor lands in Empty at a pi. Read with synTyL_pi_formation_witness this settles \
             the bridge direction as a fact: SynTyT embeds into SynTyL over simple contexts, and \
             SynTyL does not embed into SynTyT at all. Zero axiom_deps.",
        )?;

        // --- Group F: witnesses and the non-degeneracy guard ---
        add_thm(
            self,
            "synTyL_id",
            ty_syntyl_id(),
            val_syntyl_id(),
            &["SynTyL.lam", "SynTyL.var", "SimpleTy.base"],
            "The fragment's identity function is typed by the converged judgment, in every \
             context: lam (sort 0) (bvar 0) : pi (sort 0) (sort 0). Note what the FAITHFUL var \
             rule costs here: nothing, because the looked-up type is sort 0 and lift_at (sort 0) 0 \
             1 REDUCES to sort 0, so the SynTyL.var application typechecks with no transport at \
             all. The lift bites only at types with loose variables — see \
             synTyL_var_lift_witness. Also a PREMISE-SATISFIABILITY WITNESS for SynTyL. Zero \
             axiom_deps.",
        )?;
        add_thm(
            self,
            "synTyL_sort_witness",
            ty_syntyl_sort_witness(),
            val_syntyl_sort_witness(),
            &["SynTyL.sort"],
            "sort 0 : sort 1 in the empty context — the judgment's non-vacuity at its simplest \
             rule, a pure constructor application, and a closed-conclusion \
             premise-satisfiability witness for SynTyL. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "synTyL_var_lift_witness",
            ty_syntyl_var_lift_witness(),
            val_syntyl_var_lift_witness(),
            &["SynTyL.var", "ctx_lookup", "lift_at", "Eq.refl"],
            "THE WITNESS THAT THE FAITHFUL VAR RULE BUYS SOMETHING REAL, and the one the brief \
             demands be VISIBLE: in the context [sort 0 ; bvar 0], the variable bvar 1 is typed at \
             bvar 2 — the declared type bvar 0 LIFTED by i+1 = 2, exactly as TypingCtx.var does \
             it. R7's SynTyT.var would have typed the same variable at bvar 0, the un-lifted \
             lookup, which is the wrong de Bruijn reading in the extended context. The type in the \
             statement is written as the literal bvar 2 rather than as lift_at (bvar 0) 0 2 so the \
             kernel has to compute the lift to accept it. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "synTyL_pi_formation_witness",
            ty_syntyl_pi_formation_witness(),
            val_syntyl_pi_formation_witness(),
            &["SynTyL.pi", "SynTyL.sort"],
            "THE PI-FORMATION WITNESS: pi (sort 0) (sort 0) : sort (imax 1 1) in the empty \
             context, by one SynTyL.pi over two SynTyL.sorts. The conclusion's universe is the \
             LITERAL raw Level.imax (Level.succ Level.zero) (Level.succ Level.zero) — not \
             normalized, not a smart constructor — which is TypingCtx.pi's own spelling and the \
             reason R0's level_imax_ne_zero / Hurkens-block work is relevant to this ladder at \
             all. synTyT_no_pi_formation proves R7 cannot type this term at any type. Zero \
             axiom_deps.",
        )?;
        add_thm(
            self,
            "synTyL_let_witness",
            ty_syntyl_let_witness(),
            val_syntyl_let_witness(),
            &["SynTyL.letTy", "SynTyL.sort", "SynTyL.var"],
            "THE ZETA WITNESS: let_ (sort 1) (sort 0) (bvar 0) : sort 1 in the empty context — a \
             let whose BODY IS THE BOUND VARIABLE, so the rule is exercised where the binding is \
             actually used and the contractum is the value. The body's typing goes through the \
             FAITHFUL var rule in the extended context [sort 1], where lift_at (sort 1) 0 1 \
             reduces to sort 1. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "r8_let_body_fires",
            ty_r8_let_body_fires(),
            val_r8_let_body_fires(),
            &["whnf_step.beta", "beta_reduces.zeta"],
            "The let witness is a LIVE zeta redex: let_ (sort 1) (sort 0) (bvar 0) whnf-steps to \
             instantiate (bvar 0) (sort 0), by the zeta constructor under whnf_step.beta. This is \
             what makes synTyL_let_sn_witness a real SN claim about a firing redex rather than \
             about an inert term. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "synTyL_sn_witness",
            ty_syntyl_sn_witness(),
            val_syntyl_sn_witness(),
            &["synTyL_sn", "synTyL_pi_formation_witness"],
            "THE POSITIVE WITNESS, obtained THROUGH the capstone: whnf_acc of a PI EXPRESSION, \
             derived as synTyL_sn applied to synTyL_pi_formation_witness — i.e. through SynTyL.pi, \
             the fundamental theorem's pi arm (whnfAcc_pi over whnfAcc_of_instantiate_bvar0 at the \
             fresh variable), and the cr1 projection. Not by a direct whnfAcc_pi. Strictly outside \
             R7's reach: synTyT_no_pi_formation. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "synTyL_let_sn_witness",
            ty_syntyl_let_sn_witness(),
            val_syntyl_let_sn_witness(),
            &["synTyL_sn", "synTyL_let_witness"],
            "THE SECOND POSITIVE WITNESS, also through the capstone: whnf_acc of the live zeta \
             redex (r8_let_body_fires), derived as synTyL_sn applied to synTyL_let_witness — i.e. \
             through SynTyL.letTy, the fundamental theorem's zeta arm (R1's whnfAcc_zeta_expand \
             with the contractum family built from the body IH and carried along the development \
             by R7's discharged substitution transport), and the cr1 projection. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "synTyL_not_total",
            ty_syntyl_not_total(),
            val_syntyl_not_total(),
            &[
                "synTyL_fundamental",
                "substOK_idsubst",
                "psubst_id",
                "candInterp_pi_not_total",
            ],
            "THE NON-DEGENERACY GUARD (design section 6.1; the micro_has_type total-predicate \
             trap): r5_omegaLam — a STRONGLY NORMALIZING term — is NOT SynTyL-derivable at pi \
             (sort 0) (sort 0), in ANY context. The fundamental theorem at idsubst would place it \
             in candInterp (pi (sort 0) (sort 0)), which R5's candInterp_pi_not_total refutes. So \
             adding the faithful var rule, pi formation and the zeta rule did NOT widen the \
             judgment to the total relation, and since the excluded term IS whnf_acc the judgment \
             is not a disguised restatement of strong normalization either. No automated gate \
             performs this discrimination. Zero axiom_deps.",
        )?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_utils::parse_check;

    /// Every (name, type, value) triple registered via `add_definition`, in
    /// registration order.
    fn theorem_sources() -> Vec<(String, String, String)> {
        vec![
            (
                "candInterp_lift_eq".to_string(),
                TY_CANDINTERP_LIFT_EQ.to_string(),
                val_candinterp_lift_eq(),
            ),
            (
                "candInterp_lift".to_string(),
                TY_CANDINTERP_LIFT.to_string(),
                VAL_CANDINTERP_LIFT.to_string(),
            ),
            (
                "candInterp_unlift".to_string(),
                TY_CANDINTERP_UNLIFT.to_string(),
                VAL_CANDINTERP_UNLIFT.to_string(),
            ),
            (
                "r8_lift_moves_index".to_string(),
                ty_r8_lift_moves_index(),
                val_r8_lift_moves_index(),
            ),
            (
                "r8_lift_moves_under_pi".to_string(),
                ty_r8_lift_moves_under_pi(),
                val_r8_lift_moves_under_pi(),
            ),
            (
                "r8_candInterp_lift_bvar_witness".to_string(),
                ty_r8_candinterp_lift_bvar_witness(),
                val_r8_candinterp_lift_bvar_witness(),
            ),
            (
                "candInterp_zeta_expand_sort".to_string(),
                TY_CANDINTERP_ZETA_EXPAND_SORT.to_string(),
                VAL_CANDINTERP_ZETA_EXPAND_SORT.to_string(),
            ),
            (
                "r8_let_not_neutral".to_string(),
                TY_R8_LET_NOT_NEUTRAL.to_string(),
                VAL_R8_LET_NOT_NEUTRAL.to_string(),
            ),
            (
                "r8_zeta_spine_is_neutral".to_string(),
                TY_R8_ZETA_SPINE_IS_NEUTRAL.to_string(),
                VAL_R8_ZETA_SPINE_IS_NEUTRAL.to_string(),
            ),
            (
                "r8_zeta_obstruction_located".to_string(),
                TY_R8_ZETA_OBSTRUCTION_LOCATED.to_string(),
                VAL_R8_ZETA_OBSTRUCTION_LOCATED.to_string(),
            ),
            (
                "synTyL_fundamental".to_string(),
                TY_SYNTYL_FUNDAMENTAL.to_string(),
                val_syntyl_fundamental(),
            ),
            (
                "synTyL_sn_subst".to_string(),
                TY_SYNTYL_SN_SUBST.to_string(),
                VAL_SYNTYL_SN_SUBST.to_string(),
            ),
            (
                "synTyL_sn".to_string(),
                TY_SYNTYL_SN.to_string(),
                VAL_SYNTYL_SN.to_string(),
            ),
            (
                "synTyL_sn_closed".to_string(),
                TY_SYNTYL_SN_CLOSED.to_string(),
                VAL_SYNTYL_SN_CLOSED.to_string(),
            ),
            (
                "simpleTy_lift".to_string(),
                TY_SIMPLETY_LIFT.to_string(),
                VAL_SIMPLETY_LIFT.to_string(),
            ),
            (
                "ctxSimple_nil".to_string(),
                TY_CTXSIMPLE_NIL.to_string(),
                VAL_CTXSIMPLE_NIL.to_string(),
            ),
            (
                "ctxSimple_cons".to_string(),
                TY_CTXSIMPLE_CONS.to_string(),
                VAL_CTXSIMPLE_CONS.to_string(),
            ),
            (
                "synTyT_to_synTyL".to_string(),
                TY_SYNTYT_TO_SYNTYL.to_string(),
                val_syntyt_to_syntyl(),
            ),
            (
                "synTyT_sn_via_synTyL".to_string(),
                TY_SYNTYT_SN_VIA_SYNTYL.to_string(),
                VAL_SYNTYT_SN_VIA_SYNTYL.to_string(),
            ),
            (
                "synTyT_no_pi_formation".to_string(),
                TY_SYNTYT_NO_PI_FORMATION.to_string(),
                val_syntyt_no_pi_formation(),
            ),
            ("synTyL_id".to_string(), ty_syntyl_id(), val_syntyl_id()),
            (
                "synTyL_sort_witness".to_string(),
                ty_syntyl_sort_witness(),
                val_syntyl_sort_witness(),
            ),
            (
                "synTyL_var_lift_witness".to_string(),
                ty_syntyl_var_lift_witness(),
                val_syntyl_var_lift_witness(),
            ),
            (
                "synTyL_pi_formation_witness".to_string(),
                ty_syntyl_pi_formation_witness(),
                val_syntyl_pi_formation_witness(),
            ),
            (
                "synTyL_let_witness".to_string(),
                ty_syntyl_let_witness(),
                val_syntyl_let_witness(),
            ),
            (
                "r8_let_body_fires".to_string(),
                ty_r8_let_body_fires(),
                val_r8_let_body_fires(),
            ),
            (
                "synTyL_sn_witness".to_string(),
                ty_syntyl_sn_witness(),
                val_syntyl_sn_witness(),
            ),
            (
                "synTyL_let_sn_witness".to_string(),
                ty_syntyl_let_sn_witness(),
                val_syntyl_let_sn_witness(),
            ),
            (
                "synTyL_not_total".to_string(),
                ty_syntyl_not_total(),
                val_syntyl_not_total(),
            ),
        ]
    }

    /// The one inductive and the one plain def, as full declaration sources.
    fn decl_sources() -> Vec<(String, String)> {
        vec![
            ("SynTyL".to_string(), src_syn_ty_l()),
            ("CtxSimple".to_string(), SRC_CTX_SIMPLE.to_string()),
        ]
    }

    /// Parse-check every generated source — the fast guard for the commonest
    /// failure class (assembly mistakes invisible to `cargo check`).
    #[test]
    fn test_candmodel_r8_sources_parse() {
        for (name, ty, val) in theorem_sources() {
            let assembled = format!("def {name} : {ty} := {val}");
            parse_check(&assembled)
                .unwrap_or_else(|e| panic!("{name} should parse as a def: {e}\n{assembled}"));
        }
        for (name, src) in decl_sources() {
            parse_check(&src).unwrap_or_else(|e| panic!("{name} should parse: {e}\n{src}"));
        }
    }

    /// PER-STRING paren balance on every source.
    #[test]
    fn test_candmodel_r8_sources_paren_balanced() {
        let mut all: Vec<(String, String)> = Vec::new();
        for (n, ty, val) in theorem_sources() {
            all.push((format!("{n}::ty"), ty));
            all.push((format!("{n}::val"), val));
        }
        for (n, src) in decl_sources() {
            all.push((format!("{n}::decl"), src));
        }
        for (name, src) in &all {
            let mut depth: i64 = 0;
            for ch in src.chars() {
                match ch {
                    '(' => depth += 1,
                    ')' => depth -= 1,
                    _ => {}
                }
                assert!(depth >= 0, "close paren before its open in {name}: {src}");
            }
            assert_eq!(depth, 0, "unbalanced parens in {name}: {src}");
        }
    }

    /// Skip a run of parenthesised binder groups starting at `i`, returning
    /// (index after the groups, how many groups were skipped).
    fn skip_binder_groups(b: &[char], mut i: usize) -> (usize, usize) {
        let mut n = 0usize;
        loop {
            while i < b.len() && b[i] == ' ' {
                i += 1;
            }
            if i >= b.len() || b[i] != '(' {
                break;
            }
            let mut d = 0i64;
            while i < b.len() {
                if b[i] == '(' {
                    d += 1;
                } else if b[i] == ')' {
                    d -= 1;
                    if d == 0 {
                        i += 1;
                        break;
                    }
                }
                i += 1;
            }
            n += 1;
        }
        while i < b.len() && b[i] == ' ' {
            i += 1;
        }
        (i, n)
    }

    /// STRUCTURAL GUARD: a `forall` binder run must be terminated by a COMMA
    /// and a `fun` binder run by `=>`.
    #[test]
    fn test_candmodel_r8_binder_runs_terminated() {
        let mut all: Vec<(String, String)> = Vec::new();
        for (n, ty, val) in theorem_sources() {
            all.push((format!("{n}::ty"), ty));
            all.push((format!("{n}::val"), val));
        }
        for (name, src) in &all {
            let b: Vec<char> = src.chars().collect();
            for (kw, close) in [("forall ", ","), ("fun ", "=>")] {
                let mut from = 0usize;
                while let Some(rel) = src[from..].find(kw) {
                    let start = from + rel;
                    from = start + 1;
                    let ci = src[..start].chars().count() + kw.chars().count();
                    let (after, groups) = skip_binder_groups(&b, ci);
                    assert!(groups > 0, "{name}: `{kw}` with no parenthesised binder");
                    let tail: String = b[after..(after + 2).min(b.len())].iter().collect();
                    assert!(
                        tail.starts_with(close),
                        "{name}: `{kw}` binder run is not terminated by `{close}` — found \
                         `{tail}`"
                    );
                }
            }
        }
    }

    /// Shape guards.
    #[test]
    fn test_candmodel_r8_shape_guards() {
        let syntyl = src_syn_ty_l();

        // (1) THE HEADLINE PROPERTY OF THE LADDER: the judgment is SYNTACTIC.
        for forbidden in [
            "candInterp",
            "CandModel",
            "cm_Red",
            "RecEnvClosed",
            "RecEnvLiftClosed",
            "DefEnvClosed",
            "IsCandHF",
            "IsCandSet",
            "PiSet",
        ] {
            assert!(
                !syntyl.contains(forbidden),
                "SynTyL must not mention {forbidden} — the judgment is SYNTACTIC"
            );
        }

        // (2) THE FIRST HEADLINE PROPERTY OF R8: `var` is TypingCtx.var, i.e.
        // it LIFTS. A judgment whose var rule concluded at the bare lookup
        // would be R7 again.
        assert!(
            syntyl.contains(VAR_RULE_LIFTED),
            "SynTyL.var must be the LIFTING rule `{VAR_RULE_LIFTED}`"
        );
        assert!(
            syntyl.contains("SynTyL G (KExpr.bvar i) (lift_at A Nat.zero (Nat.succ i))"),
            "SynTyL.var must conclude at lift_at A Nat.zero (Nat.succ i), exactly as TypingCtx.var"
        );

        // (3) THE SECOND: `pi` FORMATION, at the LITERAL raw Level.imax.
        assert!(
            syntyl.contains(PI_RULE_IMAX),
            "SynTyL must carry the pi FORMATION rule `{PI_RULE_IMAX}`"
        );
        assert!(
            syntyl.contains("(KExpr.sort (Level.imax n m))"),
            "the pi rule must conclude at the LITERAL Level.imax — TypingCtx.pi's own spelling; a \
             normalized or smart-constructed level would be a different rule"
        );

        // (4) THE THIRD (stretch, §B): the zeta rule, and it is the
        // SORT-ANNOTATED fragment, not the general TypingCtx.let_.
        assert!(
            syntyl.contains(LET_RULE_SORT),
            "SynTyL must carry the sort-annotated zeta rule `{LET_RULE_SORT}`"
        );
        assert!(
            syntyl.contains("SynTyL G (KExpr.let_ (KExpr.sort n) v b) (KExpr.sort m)"),
            "the let rule must be stated at a LITERAL sort annotation and a sort-typed body — that \
             restriction is what candInterp_zeta_expand_sort licenses and \
             r8_zeta_obstruction_located explains"
        );

        // (5) The three inherited rules are R7's, unchanged.
        for needle in [
            "| sort : forall (G : ListType KExpr) (n : Level), SynTyL G (KExpr.sort n) \
             (KExpr.sort (Level.succ n))",
            "SynTyL G f (KExpr.pi A B) -> SynTyL G a A -> SynTyL G (KExpr.app f a) B",
            "SimpleTy A -> SynTyL (@ListType.cons KExpr A G) b B -> SynTyL G (KExpr.lam A b) \
             (KExpr.pi A B)",
        ] {
            assert!(
                syntyl.contains(needle),
                "SynTyL must carry the rule `{needle}`"
            );
        }

        // (6) RECURSOR-SHAPE PIN: no fixedIndicesToParams promotion of the
        // uniform leading (G : ListType KExpr) — three recursive premises
        // conclude at the EXTENDED context.
        for extended in [
            "SynTyL (@ListType.cons KExpr A G) B (KExpr.sort m)",
            "SynTyL (@ListType.cons KExpr A G) b B",
            "SynTyL (@ListType.cons KExpr (KExpr.sort n) G) b (KExpr.sort m)",
        ] {
            assert!(
                syntyl.contains(extended),
                "a recursive premise must conclude at the EXTENDED context (`{extended}`), or the \
                 leading index becomes fixed and fixedIndicesToParams promotes it"
            );
        }

        // (7) ARM-ARITY PIN: fields-then-IHs in constructor order.
        let fund = val_syntyl_fundamental();
        assert!(
            fund.contains(
                "(_qhA : SynTyL qG qA (KExpr.sort qn)) (_qhB : SynTyL (@ListType.cons KExpr qA qG) \
                 qB (KExpr.sort qm)) (qihA :"
            ),
            "the pi minor must bind BOTH recursive fields before the first IH (fields-then-IHs)"
        );
        assert!(
            fund.contains(
                "(_qhf : SynTyL qG qf (KExpr.pi qA qB)) (_qha : SynTyL qG qa qA) (qihf :"
            ),
            "the app minor must bind BOTH recursive fields before the first IH"
        );
        assert!(
            fund.contains(
                "(qhA : SimpleTy qA) (_qhb : SynTyL (@ListType.cons KExpr qA qG) qb qB) (qih :"
            ),
            "the lam minor must bind the SimpleTy field, then the single recursive field, then the \
             single IH"
        );
        assert!(
            fund.contains(
                "(_qhv : SynTyL qG qv (KExpr.sort qn)) (_qhb : SynTyL (@ListType.cons KExpr \
                 (KExpr.sort qn) qG) qb (KExpr.sort qm)) (qihv :"
            ),
            "the letTy minor must bind BOTH recursive fields before the first IH"
        );

        // (8) THE VAR ARM IS THE RUNG: it must consume candInterp_lift. A var
        // arm that used the lookup directly would be typing bvar i at the
        // UN-lifted declared type, i.e. R7's rule wearing R8's conclusion.
        assert!(
            fund.contains("candInterp_lift qA Nat.zero (Nat.succ qi)"),
            "synTyL_fundamental's var arm must carry the SubstOK lookup along candInterp_lift to \
             the LIFTED type"
        );
        // ...and the letTy arm must go through the base-set zeta engine AND
        // R7's DISCHARGED transport, never through a re-hoisted premise.
        assert!(
            fund.contains("whnfAcc_zeta_expand (KExpr.sort qn) (whnfAcc_sort qn)"),
            "the letTy arm must go through R1's base-set zeta engine at the sort annotation"
        );
        assert!(
            fund.contains("betaStar_inst_transport_env")
                && fund.contains("candInterp_betaStar_closed"),
            "the letTy and lam arms must build their development families from R7's DISCHARGED \
             transport and betaStar-closure"
        );
        assert!(
            !fund.contains("betaStar_inst_transport ") && !fund.contains("betaRed_inst_transport "),
            "synTyL_fundamental must not consume R2's premise-carrying transports directly"
        );

        // (9) PREMISE-FREEDOM GUARD: nothing in the capstone chain, the
        // judgment, the unlock TYPES or the bridge may carry a closedness or
        // model premise.
        for (name, ty) in [
            ("synTyL_sn", TY_SYNTYL_SN.to_string()),
            ("synTyL_sn_closed", TY_SYNTYL_SN_CLOSED.to_string()),
            ("synTyL_sn_subst", TY_SYNTYL_SN_SUBST.to_string()),
            ("synTyL_fundamental", TY_SYNTYL_FUNDAMENTAL.to_string()),
            ("candInterp_lift_eq", TY_CANDINTERP_LIFT_EQ.to_string()),
            ("candInterp_lift", TY_CANDINTERP_LIFT.to_string()),
            ("candInterp_unlift", TY_CANDINTERP_UNLIFT.to_string()),
            (
                "candInterp_zeta_expand_sort",
                TY_CANDINTERP_ZETA_EXPAND_SORT.to_string(),
            ),
            ("synTyT_to_synTyL", TY_SYNTYT_TO_SYNTYL.to_string()),
            ("synTyT_sn_via_synTyL", TY_SYNTYT_SN_VIA_SYNTYL.to_string()),
            ("SynTyL", syntyl.clone()),
        ] {
            for forbidden in [
                "RecEnvClosed",
                "DefEnvClosed",
                "RecEnvLiftClosed",
                "CandModel",
                "cm_Red",
                "EnvAcyclic",
            ] {
                assert!(
                    !ty.contains(forbidden),
                    "{name} must carry no {forbidden} premise — the R8 capstone is unconditional"
                );
            }
        }
        // The capstone really is context-general, not closed-terms-only.
        assert!(
            TY_SYNTYL_SN.contains("forall (G : ListType KExpr)"),
            "synTyL_sn must hold at an ARBITRARY context (idsubst models every context)"
        );

        // (10) BRIDGE-DIRECTION PIN: R8 claims SynTyT -> SynTyL under
        // CtxSimple, and states the converse is FALSE by a registered proof.
        assert!(
            TY_SYNTYT_TO_SYNTYL.contains("SynTyT G e T -> CtxSimple G -> SynTyL G e T"),
            "the bridge must go from R7's judgment INTO R8's, under the CtxSimple hypothesis"
        );
        assert!(
            !TY_SYNTYT_TO_SYNTYL.contains("SynTyL G e T -> SynTyT G e T"),
            "the converse bridge is FALSE (synTyT_no_pi_formation) and must not be claimed"
        );
        assert!(
            val_syntyt_to_syntyl().contains("simpleTy_lift")
                && val_syntyt_to_syntyl().contains("ctxSimple_cons"),
            "the bridge's var arm must collapse the lift by simpleTy_lift and its lam arm must \
             rebuild the context hypothesis by ctxSimple_cons"
        );
        assert!(
            TY_SYNTYT_NO_PI_FORMATION.contains("SynTyT G (KExpr.pi A B) T -> Empty"),
            "the strictness proof must refute SynTyT at a pi EXPRESSION"
        );
        // ...and its recursor IHs must be the MOTIVE at each recursive
        // premise's subject — a STUCK KExpr.rec application, never `Nat`. That
        // mistake is the measured 2026-08-25 failure of this constant: the
        // discriminator reduces only on a constructor, and the subjects are
        // variables.
        let nopi = val_syntyt_no_pi_formation();
        assert!(
            !nopi.contains("(_qihf : Nat)") && !nopi.contains("(_qih : Nat)"),
            "synTyT_no_pi_formation's IH binders must be the discriminator at the premise subject, \
             not Nat"
        );
        assert!(
            nopi.contains("(_qihf : (KExpr.rec ") && nopi.contains("(_qih : (KExpr.rec "),
            "synTyT_no_pi_formation's IH binders must be the STUCK discriminator application"
        );

        // (11) The lift unlock must be an equality of the two MEMBERSHIP
        // PREDICATES (the contravariance point), not a one-way implication
        // dressed up as one.
        assert!(
            TY_CANDINTERP_LIFT_EQ.contains("Eq (KExpr -> Type) (candInterp (lift_at T d k))"),
            "candInterp_lift_eq must equate the two KExpr -> Type predicates, not their pointwise \
             memberships"
        );
        assert!(
            val_candinterp_lift_eq().contains("Eq.cong (KExpr -> Type) (KExpr -> Type)"),
            "the pi arm must congruence through PiSet on both families"
        );

        // (12) THE ZETA SCOPE IS NOT OVERSTATED: the positive clause is at a
        // sort, and the obstruction constants are present.
        assert!(
            TY_CANDINTERP_ZETA_EXPAND_SORT
                .contains("candInterp (KExpr.sort m) (KExpr.let_ (KExpr.sort n) v b)"),
            "the landed zeta clause must be at a SORT-typed slot with a SORT annotation"
        );
        assert!(
            TY_R8_LET_NOT_NEUTRAL.contains("Neutral (KExpr.let_ ty v b) -> Empty")
                && TY_R8_ZETA_SPINE_IS_NEUTRAL
                    .contains("Neutral (KExpr.app (KExpr.let_ ty v b) a)"),
            "the obstruction must be LOCATED: cr3 inapplicable at the redex, applicable at the \
             spine"
        );

        // (13) AndType SLOT PIN (the universe trap R6 measured): a slot may
        // hold neither a Prop (an `Eq`) nor a Type-1 term. The lift equalities
        // are therefore separate constants and never paired.
        assert!(
            !TY_R8_ZETA_OBSTRUCTION_LOCATED.contains("Eq ")
                && !TY_R8_ZETA_OBSTRUCTION_LOCATED.contains("(C : Type)"),
            "r8_zeta_obstruction_located: an AndType slot may hold neither a Prop `Eq` nor a \
             Type-1 `(C : Type)` quantification"
        );

        // (14) The witnesses must exercise what they claim: the var witness
        // must be at a NON-ZERO index and state the LIFTED type literally, and
        // both SN witnesses must go THROUGH the capstone.
        assert!(
            ty_syntyl_var_lift_witness().contains(V1) && ty_syntyl_var_lift_witness().contains(V2),
            "the var witness must type bvar 1 at bvar 2 — a NON-ZERO index where the lift moves"
        );
        assert!(
            !ty_syntyl_var_lift_witness().contains("lift_at"),
            "the var witness must state the LIFTED type literally, so the kernel has to compute \
             the lift rather than accept it syntactically"
        );
        assert!(
            val_syntyl_sn_witness().starts_with("synTyL_sn ")
                && val_syntyl_let_sn_witness().starts_with("synTyL_sn "),
            "both SN witnesses must be obtained by applying the capstone"
        );
    }

    /// Registration + kernel re-verification against the substitution bundle.
    #[test]
    fn test_candmodel_r8_registered_and_reverifies() {
        let spec = crate::test_utils::build_substitution_spec_with_stack();
        let mut names: Vec<String> = theorem_sources().into_iter().map(|(n, _, _)| n).collect();
        for (n, _) in decl_sources() {
            names.push(n);
        }
        for name in &names {
            assert!(
                spec.definitions().contains_key(name),
                "{name} should be registered by the candmodel_construct_r8 stage"
            );
        }
        for (name, _, _) in theorem_sources() {
            spec.verify_definition(&name).unwrap_or_else(|e| {
                panic!("{name} should re-typecheck in the spec environment: {e:?}")
            });
        }
    }
}
