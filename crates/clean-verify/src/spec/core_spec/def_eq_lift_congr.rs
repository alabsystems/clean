// Copyright 2026 Andrew Yates.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! DefEq congruence lemmas for lift_at and instantiate argument position.
//!
//! Contains:
//! - `def_eq_instantiate_arg_congr_at`: KExpr structural induction on B showing
//!   that DefEq a a' implies DefEq (instantiate_at B a d) (instantiate_at B a' d)
//! - `instantiate_bvar_at_arg_congr`: bvar case helper for the above
//!
//! These lemmas complete the proof infrastructure for `def_eq_instantiate_arg_congr`
//! (registered in type_preservation_subst.rs).
//!
//! Part of #3221: Build genuine proof coverage for def_eq_instantiate_arg_congr.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

impl Specification {
    pub(super) fn add_def_eq_lift_congr_lemmas(&mut self) -> Result<(), SpecError> {
        // === def_eq_respects_lift_at ===
        //
        // Brick 9 (church_rosser_whnf retirement): lift_at preserves DefEq.
        //   forall (a a' : KExpr) (d : Nat),
        //     RedEnvFaithful the_red_env ->
        //     DefEq a a' -> DefEq (lift_at a 0 d) (lift_at a' 0 d)
        //
        // Proof by INDUCTION ON THE DefEq DERIVATION (DefEq.rec), NOT on term
        // structure and NOT by normalizing. The motive generalizes the lift cutoff
        // `c` (held by the recursor; the AMOUNT `d` is fixed) so the binder arms
        // (lam/pi) can apply their body IH at the incremented cutoff (succ c):
        //   P x y _ := forall (c : Nat), DefEq (lift_at x c d) (lift_at y c d)
        // The nine DefEq.rec arms close as follows:
        //   - refl/symm/trans/app_cong/lam_cong/pi_cong : the matching DefEq
        //     congruence applied to the IH(s); lift_at pushes through app/lam/pi by
        //     its computation rules (lift_at_app/lam/pi), with the +1 cutoff shift on
        //     lam/pi bodies.
        //   - beta : the lifted redex `lift_at (app (lam A b) a) c d` rewrites (via
        //     lift_at_app + lift_at_lam) to `app (lam (lift A c d)(lift b (succ c) d))
        //     (lift a c d)`; DefEq.beta contracts it to `instantiate (lift b (succ c) d)
        //     (lift a c d)`, which equals `lift_at (instantiate b a) c d` by
        //     lift_instantiate_swap at (d:=0, k:=c, a:=d) (modulo nat_zero_add on the
        //     `0+c` cutoffs). Composed with def_eq_eq_left/right.
        //   - delta : the def value is lift-closed (redenv_faithful_i6 ->
        //     DefEnvLiftClosed), so the directed delta step commutes with lift_at
        //     (delta_lift_commutes, already DerivedProved). Project the step out of the
        //     `delta_reduces` witness (delta_reduces_to_step), lift it, re-wrap with
        //     delta_reduces.mk, close with DefEq.delta. (`delta_step` is reducibly the
        //     reduct equation `delta_reduct env e = some e'`, so delta_lift_commutes's
        //     conclusion IS the lifted step.) NO term-structure recursion, NO
        //     WellFounded/delta-chain cascade — that wall is the confluence
        //     delta-normalization problem, NOT this lemma.
        //   - iota : the exact mirror of delta over red_rec / RecEnvLiftClosed
        //     (redenv_faithful_i4) / iota_lift_commutes / iota_reduces_to_step.
        // RedEnvFaithful the_red_env is CARRIED as a hypothesis (the same posture as
        // the rest of the church_rosser_whnf-retirement cone), NOT discharged over
        // the_red_env's concrete value. DerivedProved, ZERO axiom_deps. Part of #2859
        // (Brick 9) / #3221.
        self.add_definition(SpecDefinition {
            name: "def_eq_respects_lift_at".to_string(),
            type_src: concat!(
                "forall (a : KExpr) (a' : KExpr) (d : Nat), ",
                "RedEnvFaithful the_red_env -> ",
                "DefEq a a' -> ",
                "DefEq (lift_at a Nat.zero d) (lift_at a' Nat.zero d)"
            )
            .to_string(),
            value_src: Some(def_eq_respects_lift_at_value()),
            is_axiom: false,
            description: concat!(
                "lift_at preserves DefEq: if a ~ a' then (lift_at a 0 d) ~ (lift_at a' 0 d). ",
                "Proof by DefEq.rec induction on the derivation (motive generalizes the lift ",
                "cutoff); congruence/refl/symm/trans/beta arms are structural (beta uses ",
                "lift_instantiate_swap), and the delta/iota arms commute the directed step with ",
                "lift via delta_lift_commutes / iota_lift_commutes under the carried ",
                "RedEnvFaithful the_red_env (DefEnvLiftClosed / RecEnvLiftClosed projectors). ",
                "DerivedProved, zero axiom_deps. Part of #2859 (Brick 9) / #3221."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "DefEq.rec".to_string(),
                "DefEq.refl".to_string(),
                "DefEq.symm".to_string(),
                "DefEq.trans".to_string(),
                "DefEq.beta".to_string(),
                "DefEq.app_cong".to_string(),
                "DefEq.lam_cong".to_string(),
                "DefEq.pi_cong".to_string(),
                "DefEq.delta".to_string(),
                "DefEq.iota".to_string(),
                "DefEq.zeta".to_string(),
                "DefEq.let_cong".to_string(),
                "DefEq.proj_cong".to_string(),
                "def_eq_eq_left".to_string(),
                "def_eq_eq_right".to_string(),
                "lift_at".to_string(),
                "lift_at_app".to_string(),
                "lift_at_lam".to_string(),
                "lift_at_pi".to_string(),
                "lift_at_let_".to_string(),
                "lift_at_proj".to_string(),
                "lift_instantiate_swap".to_string(),
                "instantiate".to_string(),
                "instantiate_at".to_string(),
                "nat_zero_add".to_string(),
                "Eq.cong".to_string(),
                "Eq.symm".to_string(),
                "Eq.trans".to_string(),
                "delta_reduces.mk".to_string(),
                "delta_reduces_to_step".to_string(),
                "delta_lift_commutes".to_string(),
                "redenv_faithful_i6".to_string(),
                "red_def".to_string(),
                "iota_reduces.mk".to_string(),
                "iota_reduces_to_step".to_string(),
                "iota_lift_commutes".to_string(),
                "redenv_faithful_i4".to_string(),
                "red_rec".to_string(),
                "the_red_env".to_string(),
                "RedEnvFaithful".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // === def_eq_respects_lift_at_gen (cutoff-general) ===
        //
        // The cutoff-GENERAL form of def_eq_respects_lift_at: for EVERY cutoff c,
        // DefEq a a' -> DefEq (lift_at a c d) (lift_at a' c d). Same DefEq.rec proof
        // term (the motive already universalizes the cutoff `c`); this variant simply
        // does NOT specialize `c` to Nat.zero at the discharge. Consumed by the
        // weakening/lift-preservation lemma weakening_typing_gen, whose conv arm needs
        // the congruence at the ambient cutoff the Typing.rec recursion is threading
        // through binders. RedEnvFaithful the_red_env is CARRIED as a hypothesis, same
        // posture as def_eq_respects_lift_at. DerivedProved, ZERO axiom_deps.
        self.add_definition(SpecDefinition {
            name: "def_eq_respects_lift_at_gen".to_string(),
            type_src: concat!(
                "forall (a : KExpr) (a' : KExpr) (d : Nat), ",
                "RedEnvFaithful the_red_env -> ",
                "DefEq a a' -> ",
                "forall (c : Nat), DefEq (lift_at a c d) (lift_at a' c d)"
            )
            .to_string(),
            value_src: Some(def_eq_respects_lift_at_gen_value()),
            is_axiom: false,
            description: concat!(
                "Cutoff-general lift/DefEq congruence: if a ~ a' then for EVERY cutoff c, ",
                "(lift_at a c d) ~ (lift_at a' c d). Same kernel-checked DefEq.rec term as ",
                "def_eq_respects_lift_at (whose motive already generalizes the cutoff), only ",
                "WITHOUT the trailing specialization to cutoff 0. Needed by weakening_typing_gen's ",
                "conv arm, which recurses through binders at increasing cutoffs. DerivedProved, ",
                "zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "DefEq.rec".to_string(),
                "DefEq.refl".to_string(),
                "DefEq.symm".to_string(),
                "DefEq.trans".to_string(),
                "DefEq.beta".to_string(),
                "DefEq.app_cong".to_string(),
                "DefEq.lam_cong".to_string(),
                "DefEq.pi_cong".to_string(),
                "DefEq.delta".to_string(),
                "DefEq.iota".to_string(),
                "DefEq.zeta".to_string(),
                "DefEq.let_cong".to_string(), "DefEq.proj_cong".to_string(),
                "def_eq_eq_left".to_string(),
                "def_eq_eq_right".to_string(),
                "lift_at".to_string(),
                "lift_at_app".to_string(),
                "lift_at_lam".to_string(),
                "lift_at_pi".to_string(),
                "lift_at_let_".to_string(), "lift_at_proj".to_string(),
                "lift_instantiate_swap".to_string(),
                "instantiate".to_string(),
                "instantiate_at".to_string(),
                "nat_zero_add".to_string(),
                "Eq.cong".to_string(),
                "Eq.symm".to_string(),
                "Eq.trans".to_string(),
                "delta_reduces.mk".to_string(),
                "delta_reduces_to_step".to_string(),
                "delta_lift_commutes".to_string(),
                "redenv_faithful_i6".to_string(),
                "red_def".to_string(),
                "iota_reduces.mk".to_string(),
                "iota_reduces_to_step".to_string(),
                "iota_lift_commutes".to_string(),
                "redenv_faithful_i4".to_string(),
                "red_rec".to_string(),
                "the_red_env".to_string(),
                "RedEnvFaithful".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // === instantiate_bvar_at_arg_congr ===
        //
        // The bvar case of def_eq_instantiate_arg_congr_at.
        // Shows: forall (i d : Nat) (a a' : KExpr),
        //   RedEnvFaithful the_red_env -> DefEq a a' ->
        //   DefEq (instantiate_bvar_at i d a) (instantiate_bvar_at i d a')
        //
        // Brick 9 (church_rosser_whnf retirement): rerouted off the FALSE
        // def_eq_to_eq bridge onto an HONEST nested-Nat.rec three-way case
        // analysis. By definition
        //   instantiate_bvar_at i d x
        //     = Nat.rec _ (instantiate_bvar_geq i d x) (fun _ _ => bvar i) (Nat.sub d i)
        //   instantiate_bvar_geq i d x
        //     = Nat.rec _ (lift_at x 0 d) (fun _ _ => bvar (i-1)) (Nat.sub i d)
        // so x appears ONLY at the all-zero leaf as `lift_at x 0 d`. The proof
        // induces on (Nat.sub d i) (outer) and (Nat.sub i d) (inner):
        //   - i < d (Nat.sub d i = succ _): both sides are bvar i        → DefEq.refl
        //   - i > d (Nat.sub i d = succ _): both sides are bvar (i-1)    → DefEq.refl
        //   - i = d (both subs = 0): lift_at a 0 d vs lift_at a' 0 d     → def_eq_respects_lift_at
        // RedEnvFaithful the_red_env is CARRIED as a hypothesis (same posture as
        // def_eq_respects_lift_at and the rest of the cone), NEVER discharged over
        // the_red_env's concrete value. DerivedProved, ZERO axiom_deps. Part of
        // #2859 (Brick 9) / #3221.
        self.add_definition(SpecDefinition {
            name: "instantiate_bvar_at_arg_congr".to_string(),
            type_src: concat!(
                "forall (i : Nat) (d : Nat) (a : KExpr) (a' : KExpr), ",
                "RedEnvFaithful the_red_env -> ",
                "DefEq a a' -> ",
                "DefEq (instantiate_bvar_at i d a) (instantiate_bvar_at i d a')"
            )
            .to_string(),
            value_src: Some(instantiate_bvar_at_arg_congr_value()),
            is_axiom: false,
            description: concat!(
                "Bvar case helper: instantiate_bvar_at preserves argument DefEq. ",
                "Honest nested-Nat.rec three-way analysis on (Nat.sub d i) / (Nat.sub i d): ",
                "i<d -> bvar i (refl); i>d -> bvar (i-1) (refl); i=d -> lift_at a/a' 0 d closed by ",
                "def_eq_respects_lift_at under the carried RedEnvFaithful the_red_env. ",
                "DerivedProved, zero axiom_deps (Brick 9: rerouted off the FALSE def_eq_to_eq). ",
                "Part of #2859 (Brick 9) / #3221."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Nat.rec".to_string(),
                "DefEq.refl".to_string(),
                "def_eq_respects_lift_at".to_string(),
                "instantiate_bvar_geq".to_string(),
                "instantiate_bvar_at".to_string(),
                "lift_at".to_string(),
                "RedEnvFaithful".to_string(),
                "the_red_env".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // === def_eq_instantiate_arg_congr_at ===
        //
        // If a ~ a', then instantiate_at B a d ~ instantiate_at B a' d for any B, d.
        // Proof by KExpr.rec structural induction on B:
        //   - sort: DefEq.refl (instantiate_at on sort is identity)
        //   - bvar i: instantiate_bvar_at_arg_congr i d a a' h
        //   - app f arg0: instantiate_at_app + DefEq.app_cong on IH(f), IH(arg0)
        //   - lam ty body: instantiate_at_lam + DefEq.lam_cong on IH(ty) at d, IH(body) at succ d
        //   - pi ty body: instantiate_at_pi + DefEq.pi_cong on IH(ty) at d, IH(body) at succ d
        //   - const: DefEq.refl (instantiate_at on const is identity)
        //
        // DerivedProved, ZERO axiom_deps: the complete KExpr.rec term below is
        // kernel-checked on every spec build (add_definition -> env.add_decl);
        // the proof_status flag previously lagged at DerivedPending after the
        // Brick 9 reroute made the bvar case (instantiate_bvar_at_arg_congr)
        // def_eq_to_eq-free. RedEnvFaithful the_red_env is CARRIED as a
        // hypothesis (same posture as the rest of the cone), not discharged.
        //
        // Part of #3221.
        self.add_definition(SpecDefinition {
            name: "def_eq_instantiate_arg_congr_at".to_string(),
            type_src: concat!(
                "forall (B : KExpr) (a : KExpr) (a' : KExpr) (d : Nat), ",
                "RedEnvFaithful the_red_env -> ",
                "DefEq a a' -> ",
                "DefEq (instantiate_at B a d) (instantiate_at B a' d)"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (B : KExpr) (a : KExpr) (a' : KExpr) (d : Nat) ",
                    "(hf : RedEnvFaithful the_red_env) (h : DefEq a a') => ",
                    "KExpr.rec ",
                    "(fun (e : KExpr) => ",
                    "forall (a0 : KExpr) (a0' : KExpr) (d0 : Nat), DefEq a0 a0' -> ",
                    "DefEq (instantiate_at e a0 d0) (instantiate_at e a0' d0)) ",
                    "(fun (n : Level) (a0 : KExpr) (a0' : KExpr) (d0 : Nat) ",
                    "(_h0 : DefEq a0 a0') => ",
                    "def_eq_eq_right ",
                    "(instantiate_at (KExpr.sort n) a0 d0) ",
                    "(KExpr.sort n) ",
                    "(instantiate_at (KExpr.sort n) a0' d0) ",
                    "(def_eq_eq_left ",
                    "(instantiate_at (KExpr.sort n) a0 d0) ",
                    "(KExpr.sort n) ",
                    "(KExpr.sort n) ",
                    "(instantiate_at_sort n a0 d0) ",
                    "(DefEq.refl (KExpr.sort n))) ",
                    "(Eq.symm KExpr ",
                    "(instantiate_at (KExpr.sort n) a0' d0) ",
                    "(KExpr.sort n) ",
                    "(instantiate_at_sort n a0' d0))) ",
                    "(fun (i : Nat) (a0 : KExpr) (a0' : KExpr) (d0 : Nat) ",
                    "(h0 : DefEq a0 a0') => ",
                    "def_eq_eq_right ",
                    "(instantiate_at (KExpr.bvar i) a0 d0) ",
                    "(instantiate_bvar_at i d0 a0') ",
                    "(instantiate_at (KExpr.bvar i) a0' d0) ",
                    "(def_eq_eq_left ",
                    "(instantiate_at (KExpr.bvar i) a0 d0) ",
                    "(instantiate_bvar_at i d0 a0) ",
                    "(instantiate_bvar_at i d0 a0') ",
                    "(instantiate_at_bvar i a0 d0) ",
                    "(instantiate_bvar_at_arg_congr i d0 a0 a0' hf h0)) ",
                    "(Eq.symm KExpr ",
                    "(instantiate_at (KExpr.bvar i) a0' d0) ",
                    "(instantiate_bvar_at i d0 a0') ",
                    "(instantiate_at_bvar i a0' d0))) ",
                    "(fun (f : KExpr) (arg0 : KExpr) ",
                    "(ih_f : forall (a0 : KExpr) (a0' : KExpr) (d0 : Nat), DefEq a0 a0' -> ",
                    "DefEq (instantiate_at f a0 d0) (instantiate_at f a0' d0)) ",
                    "(ih_arg : forall (a0 : KExpr) (a0' : KExpr) (d0 : Nat), DefEq a0 a0' -> ",
                    "DefEq (instantiate_at arg0 a0 d0) (instantiate_at arg0 a0' d0)) ",
                    "(a0 : KExpr) (a0' : KExpr) (d0 : Nat) (h0 : DefEq a0 a0') => ",
                    "def_eq_eq_right ",
                    "(instantiate_at (KExpr.app f arg0) a0 d0) ",
                    "(KExpr.app (instantiate_at f a0' d0) (instantiate_at arg0 a0' d0)) ",
                    "(instantiate_at (KExpr.app f arg0) a0' d0) ",
                    "(def_eq_eq_left ",
                    "(instantiate_at (KExpr.app f arg0) a0 d0) ",
                    "(KExpr.app (instantiate_at f a0 d0) (instantiate_at arg0 a0 d0)) ",
                    "(KExpr.app (instantiate_at f a0' d0) (instantiate_at arg0 a0' d0)) ",
                    "(instantiate_at_app f arg0 a0 d0) ",
                    "(DefEq.app_cong ",
                    "(instantiate_at f a0 d0) (instantiate_at f a0' d0) ",
                    "(instantiate_at arg0 a0 d0) (instantiate_at arg0 a0' d0) ",
                    "(ih_f a0 a0' d0 h0) (ih_arg a0 a0' d0 h0))) ",
                    "(Eq.symm KExpr ",
                    "(instantiate_at (KExpr.app f arg0) a0' d0) ",
                    "(KExpr.app (instantiate_at f a0' d0) (instantiate_at arg0 a0' d0)) ",
                    "(instantiate_at_app f arg0 a0' d0))) ",
                    "(fun (ty : KExpr) (body : KExpr) ",
                    "(ih_ty : forall (a0 : KExpr) (a0' : KExpr) (d0 : Nat), DefEq a0 a0' -> ",
                    "DefEq (instantiate_at ty a0 d0) (instantiate_at ty a0' d0)) ",
                    "(ih_body : forall (a0 : KExpr) (a0' : KExpr) (d0 : Nat), DefEq a0 a0' -> ",
                    "DefEq (instantiate_at body a0 d0) (instantiate_at body a0' d0)) ",
                    "(a0 : KExpr) (a0' : KExpr) (d0 : Nat) (h0 : DefEq a0 a0') => ",
                    "def_eq_eq_right ",
                    "(instantiate_at (KExpr.lam ty body) a0 d0) ",
                    "(KExpr.lam (instantiate_at ty a0' d0) (instantiate_at body a0' (Nat.succ d0))) ",
                    "(instantiate_at (KExpr.lam ty body) a0' d0) ",
                    "(def_eq_eq_left ",
                    "(instantiate_at (KExpr.lam ty body) a0 d0) ",
                    "(KExpr.lam (instantiate_at ty a0 d0) (instantiate_at body a0 (Nat.succ d0))) ",
                    "(KExpr.lam (instantiate_at ty a0' d0) (instantiate_at body a0' (Nat.succ d0))) ",
                    "(instantiate_at_lam ty body a0 d0) ",
                    "(DefEq.lam_cong ",
                    "(instantiate_at ty a0 d0) (instantiate_at ty a0' d0) ",
                    "(instantiate_at body a0 (Nat.succ d0)) (instantiate_at body a0' (Nat.succ d0)) ",
                    "(ih_ty a0 a0' d0 h0) (ih_body a0 a0' (Nat.succ d0) h0))) ",
                    "(Eq.symm KExpr ",
                    "(instantiate_at (KExpr.lam ty body) a0' d0) ",
                    "(KExpr.lam (instantiate_at ty a0' d0) (instantiate_at body a0' (Nat.succ d0))) ",
                    "(instantiate_at_lam ty body a0' d0))) ",
                    "(fun (ty : KExpr) (body : KExpr) ",
                    "(ih_ty : forall (a0 : KExpr) (a0' : KExpr) (d0 : Nat), DefEq a0 a0' -> ",
                    "DefEq (instantiate_at ty a0 d0) (instantiate_at ty a0' d0)) ",
                    "(ih_body : forall (a0 : KExpr) (a0' : KExpr) (d0 : Nat), DefEq a0 a0' -> ",
                    "DefEq (instantiate_at body a0 d0) (instantiate_at body a0' d0)) ",
                    "(a0 : KExpr) (a0' : KExpr) (d0 : Nat) (h0 : DefEq a0 a0') => ",
                    "def_eq_eq_right ",
                    "(instantiate_at (KExpr.pi ty body) a0 d0) ",
                    "(KExpr.pi (instantiate_at ty a0' d0) (instantiate_at body a0' (Nat.succ d0))) ",
                    "(instantiate_at (KExpr.pi ty body) a0' d0) ",
                    "(def_eq_eq_left ",
                    "(instantiate_at (KExpr.pi ty body) a0 d0) ",
                    "(KExpr.pi (instantiate_at ty a0 d0) (instantiate_at body a0 (Nat.succ d0))) ",
                    "(KExpr.pi (instantiate_at ty a0' d0) (instantiate_at body a0' (Nat.succ d0))) ",
                    "(instantiate_at_pi ty body a0 d0) ",
                    "(DefEq.pi_cong ",
                    "(instantiate_at ty a0 d0) (instantiate_at ty a0' d0) ",
                    "(instantiate_at body a0 (Nat.succ d0)) (instantiate_at body a0' (Nat.succ d0)) ",
                    "(ih_ty a0 a0' d0 h0) (ih_body a0 a0' (Nat.succ d0) h0))) ",
                    "(Eq.symm KExpr ",
                    "(instantiate_at (KExpr.pi ty body) a0' d0) ",
                    "(KExpr.pi (instantiate_at ty a0' d0) (instantiate_at body a0' (Nat.succ d0))) ",
                    "(instantiate_at_pi ty body a0' d0))) ",
                    "(fun (n : Name) (us : ListType Level) ",
                    "(a0 : KExpr) (a0' : KExpr) (d0 : Nat) ",
                    "(_h0 : DefEq a0 a0') => ",
                    "def_eq_eq_right ",
                    "(instantiate_at (KExpr.const n us) a0 d0) ",
                    "(KExpr.const n us) ",
                    "(instantiate_at (KExpr.const n us) a0' d0) ",
                    "(def_eq_eq_left ",
                    "(instantiate_at (KExpr.const n us) a0 d0) ",
                    "(KExpr.const n us) ",
                    "(KExpr.const n us) ",
                    "(instantiate_at_const n us a0 d0) ",
                    "(DefEq.refl (KExpr.const n us))) ",
                    "(Eq.symm KExpr ",
                    "(instantiate_at (KExpr.const n us) a0' d0) ",
                    "(KExpr.const n us) ",
                    "(instantiate_at_const n us a0' d0))) ",
                    // let_ ty val body: instantiate_at_let_ + DefEq.let_cong on IH(ty) at d,
                    // IH(val) at d, IH(body) at succ d (mirror of the lam/pi arms with the
                    // added val field). DefEq.let_cong is the let-promotion DefEq congruence
                    // (registered with the DefEq inductive in typing_def_eq.rs).
                    "(fun (ty : KExpr) (val : KExpr) (body : KExpr) ",
                    "(ih_ty : forall (a0 : KExpr) (a0' : KExpr) (d0 : Nat), DefEq a0 a0' -> ",
                    "DefEq (instantiate_at ty a0 d0) (instantiate_at ty a0' d0)) ",
                    "(ih_val : forall (a0 : KExpr) (a0' : KExpr) (d0 : Nat), DefEq a0 a0' -> ",
                    "DefEq (instantiate_at val a0 d0) (instantiate_at val a0' d0)) ",
                    "(ih_body : forall (a0 : KExpr) (a0' : KExpr) (d0 : Nat), DefEq a0 a0' -> ",
                    "DefEq (instantiate_at body a0 d0) (instantiate_at body a0' d0)) ",
                    "(a0 : KExpr) (a0' : KExpr) (d0 : Nat) (h0 : DefEq a0 a0') => ",
                    "def_eq_eq_right ",
                    "(instantiate_at (KExpr.let_ ty val body) a0 d0) ",
                    "(KExpr.let_ (instantiate_at ty a0' d0) (instantiate_at val a0' d0) (instantiate_at body a0' (Nat.succ d0))) ",
                    "(instantiate_at (KExpr.let_ ty val body) a0' d0) ",
                    "(def_eq_eq_left ",
                    "(instantiate_at (KExpr.let_ ty val body) a0 d0) ",
                    "(KExpr.let_ (instantiate_at ty a0 d0) (instantiate_at val a0 d0) (instantiate_at body a0 (Nat.succ d0))) ",
                    "(KExpr.let_ (instantiate_at ty a0' d0) (instantiate_at val a0' d0) (instantiate_at body a0' (Nat.succ d0))) ",
                    "(instantiate_at_let_ ty val body a0 d0) ",
                    "(DefEq.let_cong ",
                    "(instantiate_at ty a0 d0) (instantiate_at ty a0' d0) ",
                    "(instantiate_at val a0 d0) (instantiate_at val a0' d0) ",
                    "(instantiate_at body a0 (Nat.succ d0)) (instantiate_at body a0' (Nat.succ d0)) ",
                    "(ih_ty a0 a0' d0 h0) (ih_val a0 a0' d0 h0) (ih_body a0 a0' (Nat.succ d0) h0))) ",
                    "(Eq.symm KExpr ",
                    "(instantiate_at (KExpr.let_ ty val body) a0' d0) ",
                    "(KExpr.let_ (instantiate_at ty a0' d0) (instantiate_at val a0' d0) (instantiate_at body a0' (Nat.succ d0))) ",
                    "(instantiate_at_let_ ty val body a0' d0))) ",
                    // proj (proj/lit rung): single-hole mirror via instantiate_at_proj + DefEq.proj_cong.
                    "(fun (s : Name) (i : Nat) (sub : KExpr) ",
                    "(ih_sub : forall (a0 : KExpr) (a0' : KExpr) (d0 : Nat), DefEq a0 a0' -> DefEq (instantiate_at sub a0 d0) (instantiate_at sub a0' d0)) ",
                    "(a0 : KExpr) (a0' : KExpr) (d0 : Nat) (h0 : DefEq a0 a0') => ",
                    "def_eq_eq_right ",
                    "(instantiate_at (KExpr.proj s i sub) a0 d0) ",
                    "(KExpr.proj s i (instantiate_at sub a0' d0)) ",
                    "(instantiate_at (KExpr.proj s i sub) a0' d0) ",
                    "(def_eq_eq_left ",
                    "(instantiate_at (KExpr.proj s i sub) a0 d0) ",
                    "(KExpr.proj s i (instantiate_at sub a0 d0)) ",
                    "(KExpr.proj s i (instantiate_at sub a0' d0)) ",
                    "(instantiate_at_proj s i sub a0 d0) ",
                    "(DefEq.proj_cong s i (instantiate_at sub a0 d0) (instantiate_at sub a0' d0) (ih_sub a0 a0' d0 h0))) ",
                    "(Eq.symm KExpr (instantiate_at (KExpr.proj s i sub) a0' d0) (KExpr.proj s i (instantiate_at sub a0' d0)) (instantiate_at_proj s i sub a0' d0))) ",
                    // lit (proj/lit rung): leaf, like sort (instantiate_at identity, DefEq.refl).
                    "(fun (v : Nat) (a0 : KExpr) (a0' : KExpr) (d0 : Nat) (_h0 : DefEq a0 a0') => ",
                    "def_eq_eq_right ",
                    "(instantiate_at (KExpr.lit v) a0 d0) (KExpr.lit v) (instantiate_at (KExpr.lit v) a0' d0) ",
                    "(def_eq_eq_left (instantiate_at (KExpr.lit v) a0 d0) (KExpr.lit v) (KExpr.lit v) ",
                    "(instantiate_at_lit v a0 d0) (DefEq.refl (KExpr.lit v))) ",
                    "(Eq.symm KExpr (instantiate_at (KExpr.lit v) a0' d0) (KExpr.lit v) (instantiate_at_lit v a0' d0))) ",
                    "B a a' d h",
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "DefEq congruence for instantiate_at argument position: if a ~ a', then ",
                "instantiate_at B a d ~ instantiate_at B a' d for any B and depth d. ",
                "Proof via KExpr.rec structural induction on B; the bvar case threads the carried ",
                "RedEnvFaithful the_red_env into instantiate_bvar_at_arg_congr (Brick 9: ",
                "def_eq_to_eq-free). DerivedProved, zero axiom_deps: the term is kernel-checked ",
                "at every spec build; the status flag previously lagged. Part of #2859, #3221."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "DefEq.refl".to_string(),
                "DefEq.app_cong".to_string(),
                "DefEq.lam_cong".to_string(),
                "DefEq.pi_cong".to_string(),
                "DefEq.let_cong".to_string(), "DefEq.proj_cong".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
                "instantiate_at_sort".to_string(),
                "instantiate_at_app".to_string(),
                "instantiate_at_lam".to_string(),
                "instantiate_at_pi".to_string(),
                "instantiate_at_let_".to_string(), "instantiate_at_proj".to_string(), "instantiate_at_lit".to_string(),
                "instantiate_at_const".to_string(),
                "instantiate_at_bvar".to_string(),
                "instantiate_bvar_at_arg_congr".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}

/// Proof term for `def_eq_respects_lift_at` — DefEq.rec induction on the
/// derivation, motive generalizing the lift cutoff `c` (amount `d` fixed).
///
/// No Rust-side interpolation: the term is pure proof syntax. The nine minor
/// premises appear in DefEq.rec order: refl, symm, trans, beta, app_cong,
/// lam_cong, pi_cong, delta, iota. The recursor's bound names are chosen fresh
/// (p/q/r, bA/bb/ba, f0/g0, lA/lb, qA/qB, de, ie) so none collide with the outer
/// `a a' d hf` or the per-arm cutoff `c`.
fn def_eq_respects_lift_at_core() -> &'static str {
    concat!(
        "fun (a : KExpr) (a' : KExpr) (d : Nat) ",
        "(hf : RedEnvFaithful the_red_env) (h : DefEq a a') => ",
        "DefEq.rec ",
        // ----- motive: generalize the lift cutoff c (amount d is fixed) -----
        "(fun (x : KExpr) (y : KExpr) (_dpf : DefEq x y) => ",
        "forall (c : Nat), DefEq (lift_at x c d) (lift_at y c d)) ",
        // ----- refl -----
        "(fun (x : KExpr) (c : Nat) => DefEq.refl (lift_at x c d)) ",
        // ----- symm -----
        "(fun (x : KExpr) (y : KExpr) (_hxy : DefEq x y) ",
        "(ihxy : forall (c : Nat), DefEq (lift_at x c d) (lift_at y c d)) ",
        "(c : Nat) => DefEq.symm (lift_at x c d) (lift_at y c d) (ihxy c)) ",
        // ----- trans -----
        "(fun (p : KExpr) (q : KExpr) (r : KExpr) (_hpq : DefEq p q) (_hqr : DefEq q r) ",
        "(ihpq : forall (c : Nat), DefEq (lift_at p c d) (lift_at q c d)) ",
        "(ihqr : forall (c : Nat), DefEq (lift_at q c d) (lift_at r c d)) ",
        "(c : Nat) => DefEq.trans (lift_at p c d) (lift_at q c d) (lift_at r c d) ",
        "(ihpq c) (ihqr c)) ",
        // ----- beta -----
        "(fun (bA : KExpr) (bb : KExpr) (ba : KExpr) (c : Nat) => ",
        "def_eq_eq_left ",
        "(lift_at (KExpr.app (KExpr.lam bA bb) ba) c d) ",
        "(KExpr.app (KExpr.lam (lift_at bA c d) (lift_at bb (Nat.succ c) d)) (lift_at ba c d)) ",
        "(lift_at (instantiate bb ba) c d) ",
        // E1 : Eq LHSg RED  (lift_at_app then cong lift_at_lam on the fn position)
        "(Eq.trans KExpr ",
        "(lift_at (KExpr.app (KExpr.lam bA bb) ba) c d) ",
        "(KExpr.app (lift_at (KExpr.lam bA bb) c d) (lift_at ba c d)) ",
        "(KExpr.app (KExpr.lam (lift_at bA c d) (lift_at bb (Nat.succ c) d)) (lift_at ba c d)) ",
        "(lift_at_app (KExpr.lam bA bb) ba c d) ",
        "(Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.app x (lift_at ba c d)) ",
        "(lift_at (KExpr.lam bA bb) c d) ",
        "(KExpr.lam (lift_at bA c d) (lift_at bb (Nat.succ c) d)) ",
        "(lift_at_lam bA bb c d))) ",
        // DefEq RED BETARED via DefEq.beta, then Eq BETARED RHSg via swap
        "(def_eq_eq_right ",
        "(KExpr.app (KExpr.lam (lift_at bA c d) (lift_at bb (Nat.succ c) d)) (lift_at ba c d)) ",
        "(instantiate (lift_at bb (Nat.succ c) d) (lift_at ba c d)) ",
        "(lift_at (instantiate bb ba) c d) ",
        "(DefEq.beta (lift_at bA c d) (lift_at bb (Nat.succ c) d) (lift_at ba c d)) ",
        // E2 : Eq BETARED RHSg  = Eq.symm of LR, where
        //   L' = (lift_at (instantiate_at bb ba 0) c d)              [def-eq RHSg]
        //   R' = (instantiate_at (lift_at bb (succ c) d)(lift_at ba c d) 0)  [def-eq BETARED]
        //   LR : Eq L' R' chains symm(RW_L) ; SWAP ; RW_R.
        "(Eq.symm KExpr ",
        "(lift_at (instantiate_at bb ba Nat.zero) c d) ",
        "(instantiate_at (lift_at bb (Nat.succ c) d) (lift_at ba c d) Nat.zero) ",
        "(Eq.trans KExpr ",
        "(lift_at (instantiate_at bb ba Nat.zero) c d) ",
        "(instantiate_at (lift_at bb (Nat.succ (Nat.add Nat.zero c)) d) (lift_at ba c d) Nat.zero) ",
        "(instantiate_at (lift_at bb (Nat.succ c) d) (lift_at ba c d) Nat.zero) ",
        // inner : Eq L' SWAP_R = trans (symm RW_L) SWAP
        "(Eq.trans KExpr ",
        "(lift_at (instantiate_at bb ba Nat.zero) c d) ",
        "(lift_at (instantiate_at bb ba Nat.zero) (Nat.add Nat.zero c) d) ",
        "(instantiate_at (lift_at bb (Nat.succ (Nat.add Nat.zero c)) d) (lift_at ba c d) Nat.zero) ",
        // symm RW_L : Eq L' SWAP_L
        "(Eq.symm KExpr ",
        "(lift_at (instantiate_at bb ba Nat.zero) (Nat.add Nat.zero c) d) ",
        "(lift_at (instantiate_at bb ba Nat.zero) c d) ",
        "(Eq.cong Nat KExpr (fun (n : Nat) => lift_at (instantiate_at bb ba Nat.zero) n d) ",
        "(Nat.add Nat.zero c) c (nat_zero_add c))) ",
        // SWAP : Eq SWAP_L SWAP_R
        "(lift_instantiate_swap bb ba Nat.zero c d)) ",
        // RW_R : Eq SWAP_R R'
        "(Eq.cong Nat KExpr ",
        "(fun (n : Nat) => instantiate_at (lift_at bb (Nat.succ n) d) (lift_at ba c d) Nat.zero) ",
        "(Nat.add Nat.zero c) c (nat_zero_add c)))))) ",
        // ----- app_cong -----
        "(fun (f0 : KExpr) (f0' : KExpr) (g0 : KExpr) (g0' : KExpr) ",
        "(_hf0 : DefEq f0 f0') (_hg0 : DefEq g0 g0') ",
        "(ihf0 : forall (c : Nat), DefEq (lift_at f0 c d) (lift_at f0' c d)) ",
        "(ihg0 : forall (c : Nat), DefEq (lift_at g0 c d) (lift_at g0' c d)) ",
        "(c : Nat) => ",
        "def_eq_eq_left ",
        "(lift_at (KExpr.app f0 g0) c d) ",
        "(KExpr.app (lift_at f0 c d) (lift_at g0 c d)) ",
        "(lift_at (KExpr.app f0' g0') c d) ",
        "(lift_at_app f0 g0 c d) ",
        "(def_eq_eq_right ",
        "(KExpr.app (lift_at f0 c d) (lift_at g0 c d)) ",
        "(KExpr.app (lift_at f0' c d) (lift_at g0' c d)) ",
        "(lift_at (KExpr.app f0' g0') c d) ",
        "(DefEq.app_cong (lift_at f0 c d) (lift_at f0' c d) (lift_at g0 c d) (lift_at g0' c d) ",
        "(ihf0 c) (ihg0 c)) ",
        "(Eq.symm KExpr (lift_at (KExpr.app f0' g0') c d) ",
        "(KExpr.app (lift_at f0' c d) (lift_at g0' c d)) (lift_at_app f0' g0' c d)))) ",
        // ----- lam_cong -----
        "(fun (lA : KExpr) (lA' : KExpr) (lb : KExpr) (lb' : KExpr) ",
        "(_hlA : DefEq lA lA') (_hlb : DefEq lb lb') ",
        "(ihlA : forall (c : Nat), DefEq (lift_at lA c d) (lift_at lA' c d)) ",
        "(ihlb : forall (c : Nat), DefEq (lift_at lb c d) (lift_at lb' c d)) ",
        "(c : Nat) => ",
        "def_eq_eq_left ",
        "(lift_at (KExpr.lam lA lb) c d) ",
        "(KExpr.lam (lift_at lA c d) (lift_at lb (Nat.succ c) d)) ",
        "(lift_at (KExpr.lam lA' lb') c d) ",
        "(lift_at_lam lA lb c d) ",
        "(def_eq_eq_right ",
        "(KExpr.lam (lift_at lA c d) (lift_at lb (Nat.succ c) d)) ",
        "(KExpr.lam (lift_at lA' c d) (lift_at lb' (Nat.succ c) d)) ",
        "(lift_at (KExpr.lam lA' lb') c d) ",
        "(DefEq.lam_cong (lift_at lA c d) (lift_at lA' c d) ",
        "(lift_at lb (Nat.succ c) d) (lift_at lb' (Nat.succ c) d) ",
        "(ihlA c) (ihlb (Nat.succ c))) ",
        "(Eq.symm KExpr (lift_at (KExpr.lam lA' lb') c d) ",
        "(KExpr.lam (lift_at lA' c d) (lift_at lb' (Nat.succ c) d)) (lift_at_lam lA' lb' c d)))) ",
        // ----- pi_cong -----
        "(fun (qA : KExpr) (qA' : KExpr) (qB : KExpr) (qB' : KExpr) ",
        "(_hqA : DefEq qA qA') (_hqB : DefEq qB qB') ",
        "(ihqA : forall (c : Nat), DefEq (lift_at qA c d) (lift_at qA' c d)) ",
        "(ihqB : forall (c : Nat), DefEq (lift_at qB c d) (lift_at qB' c d)) ",
        "(c : Nat) => ",
        "def_eq_eq_left ",
        "(lift_at (KExpr.pi qA qB) c d) ",
        "(KExpr.pi (lift_at qA c d) (lift_at qB (Nat.succ c) d)) ",
        "(lift_at (KExpr.pi qA' qB') c d) ",
        "(lift_at_pi qA qB c d) ",
        "(def_eq_eq_right ",
        "(KExpr.pi (lift_at qA c d) (lift_at qB (Nat.succ c) d)) ",
        "(KExpr.pi (lift_at qA' c d) (lift_at qB' (Nat.succ c) d)) ",
        "(lift_at (KExpr.pi qA' qB') c d) ",
        "(DefEq.pi_cong (lift_at qA c d) (lift_at qA' c d) ",
        "(lift_at qB (Nat.succ c) d) (lift_at qB' (Nat.succ c) d) ",
        "(ihqA c) (ihqB (Nat.succ c))) ",
        "(Eq.symm KExpr (lift_at (KExpr.pi qA' qB') c d) ",
        "(KExpr.pi (lift_at qA' c d) (lift_at qB' (Nat.succ c) d)) (lift_at_pi qA' qB' c d)))) ",
        // ----- delta -----
        // Lift the directed delta step (delta_lift_commutes) under DefEnvLiftClosed
        // (redenv_faithful_i6), re-wrap with delta_reduces.mk, close with DefEq.delta.
        "(fun (de : KExpr) (de' : KExpr) (hde : delta_reduces de de') (c : Nat) => ",
        "DefEq.delta (lift_at de c d) (lift_at de' c d) ",
        "(delta_reduces.mk (lift_at de c d) (lift_at de' c d) ",
        "(delta_lift_commutes (red_def the_red_env) de de' c d ",
        "(redenv_faithful_i6 the_red_env hf) ",
        "(delta_reduces_to_step de de' hde)))) ",
        // ----- iota (mirror of delta over red_rec / RecEnvLiftClosed) -----
        "(fun (ie : KExpr) (ie' : KExpr) (hie : iota_reduces ie ie') (c : Nat) => ",
        "DefEq.iota (lift_at ie c d) (lift_at ie' c d) ",
        "(iota_reduces.mk (lift_at ie c d) (lift_at ie' c d) ",
        "(iota_lift_commutes (red_rec the_red_env) ie ie' c d ",
        "(redenv_faithful_i4 the_red_env hf) ",
        "(iota_reduces_to_step ie ie' hie)))) ",
        // ----- zeta (let_ reduction; mirror of the beta arm over KExpr.let_) -----
        // lift_at (let_ ty v b) c d rewrites (lift_at_let_) to
        // let_ (lift ty c d)(lift v c d)(lift b (succ c) d); DefEq.zeta contracts it to
        // instantiate (lift b (succ c) d)(lift v c d), which equals lift_at (instantiate b v) c d
        // by the SAME lift_instantiate_swap fact the beta arm uses (bb:=b, ba:=v).
        "(fun (ty : KExpr) (v : KExpr) (b : KExpr) (c : Nat) => ",
        "def_eq_eq_left ",
        "(lift_at (KExpr.let_ ty v b) c d) ",
        "(KExpr.let_ (lift_at ty c d) (lift_at v c d) (lift_at b (Nat.succ c) d)) ",
        "(lift_at (instantiate b v) c d) ",
        // E1 : Eq (lift_at (let_ ty v b) c d) (let_ (lift ty)(lift v)(lift b succ)) via lift_at_let_
        "(lift_at_let_ ty v b c d) ",
        // DefEq (let_ (lift ..)) ZETARED via DefEq.zeta, then Eq ZETARED RHSg via swap
        "(def_eq_eq_right ",
        "(KExpr.let_ (lift_at ty c d) (lift_at v c d) (lift_at b (Nat.succ c) d)) ",
        "(instantiate (lift_at b (Nat.succ c) d) (lift_at v c d)) ",
        "(lift_at (instantiate b v) c d) ",
        "(DefEq.zeta (lift_at ty c d) (lift_at v c d) (lift_at b (Nat.succ c) d)) ",
        // E2 : Eq ZETARED RHSg  (byte-identical swap chain to the beta arm, bb->b, ba->v)
        "(Eq.symm KExpr ",
        "(lift_at (instantiate_at b v Nat.zero) c d) ",
        "(instantiate_at (lift_at b (Nat.succ c) d) (lift_at v c d) Nat.zero) ",
        "(Eq.trans KExpr ",
        "(lift_at (instantiate_at b v Nat.zero) c d) ",
        "(instantiate_at (lift_at b (Nat.succ (Nat.add Nat.zero c)) d) (lift_at v c d) Nat.zero) ",
        "(instantiate_at (lift_at b (Nat.succ c) d) (lift_at v c d) Nat.zero) ",
        "(Eq.trans KExpr ",
        "(lift_at (instantiate_at b v Nat.zero) c d) ",
        "(lift_at (instantiate_at b v Nat.zero) (Nat.add Nat.zero c) d) ",
        "(instantiate_at (lift_at b (Nat.succ (Nat.add Nat.zero c)) d) (lift_at v c d) Nat.zero) ",
        "(Eq.symm KExpr ",
        "(lift_at (instantiate_at b v Nat.zero) (Nat.add Nat.zero c) d) ",
        "(lift_at (instantiate_at b v Nat.zero) c d) ",
        "(Eq.cong Nat KExpr (fun (n : Nat) => lift_at (instantiate_at b v Nat.zero) n d) ",
        "(Nat.add Nat.zero c) c (nat_zero_add c))) ",
        "(lift_instantiate_swap b v Nat.zero c d)) ",
        "(Eq.cong Nat KExpr ",
        "(fun (n : Nat) => instantiate_at (lift_at b (Nat.succ n) d) (lift_at v c d) Nat.zero) ",
        "(Nat.add Nat.zero c) c (nat_zero_add c)))))) ",
        // ----- let_cong (mirror of lam_cong/pi_cong over KExpr.let_; body at succ c) -----
        "(fun (ty : KExpr) (ty' : KExpr) (v : KExpr) (v' : KExpr) (b : KExpr) (b' : KExpr) ",
        "(_hty : DefEq ty ty') (_hv : DefEq v v') (_hb : DefEq b b') ",
        "(ihty : forall (c : Nat), DefEq (lift_at ty c d) (lift_at ty' c d)) ",
        "(ihv : forall (c : Nat), DefEq (lift_at v c d) (lift_at v' c d)) ",
        "(ihb : forall (c : Nat), DefEq (lift_at b c d) (lift_at b' c d)) ",
        "(c : Nat) => ",
        "def_eq_eq_left ",
        "(lift_at (KExpr.let_ ty v b) c d) ",
        "(KExpr.let_ (lift_at ty c d) (lift_at v c d) (lift_at b (Nat.succ c) d)) ",
        "(lift_at (KExpr.let_ ty' v' b') c d) ",
        "(lift_at_let_ ty v b c d) ",
        "(def_eq_eq_right ",
        "(KExpr.let_ (lift_at ty c d) (lift_at v c d) (lift_at b (Nat.succ c) d)) ",
        "(KExpr.let_ (lift_at ty' c d) (lift_at v' c d) (lift_at b' (Nat.succ c) d)) ",
        "(lift_at (KExpr.let_ ty' v' b') c d) ",
        "(DefEq.let_cong (lift_at ty c d) (lift_at ty' c d) ",
        "(lift_at v c d) (lift_at v' c d) ",
        "(lift_at b (Nat.succ c) d) (lift_at b' (Nat.succ c) d) ",
        "(ihty c) (ihv c) (ihb (Nat.succ c))) ",
        "(Eq.symm KExpr (lift_at (KExpr.let_ ty' v' b') c d) ",
        "(KExpr.let_ (lift_at ty' c d) (lift_at v' c d) (lift_at b' (Nat.succ c) d)) (lift_at_let_ ty' v' b' c d)))) ",
        // ----- proj_cong (proj/lit rung): single-hole mirror of let_cong via lift_at_proj -----
        "(fun (s : Name) (i : Nat) (sub : KExpr) (sub' : KExpr) (_hsub : DefEq sub sub') ",
        "(ih_sub : forall (c : Nat), DefEq (lift_at sub c d) (lift_at sub' c d)) ",
        "(c : Nat) => ",
        "def_eq_eq_right ",
        "(lift_at (KExpr.proj s i sub) c d) ",
        "(KExpr.proj s i (lift_at sub' c d)) ",
        "(lift_at (KExpr.proj s i sub') c d) ",
        "(def_eq_eq_left ",
        "(lift_at (KExpr.proj s i sub) c d) ",
        "(KExpr.proj s i (lift_at sub c d)) ",
        "(KExpr.proj s i (lift_at sub' c d)) ",
        "(lift_at_proj s i sub c d) ",
        "(DefEq.proj_cong s i (lift_at sub c d) (lift_at sub' c d) (ih_sub c))) ",
        "(Eq.symm KExpr (lift_at (KExpr.proj s i sub') c d) ",
        "(KExpr.proj s i (lift_at sub' c d)) (lift_at_proj s i sub' c d))) ",
        // ----- discharge: recursor applied to a a' h yields `forall (c : Nat), ...` -----
        "a a' h ",
    )
}

/// Cutoff-0 specialization: the original `def_eq_respects_lift_at` conclusion
/// (`DefEq (lift_at a 0 d) (lift_at a' 0 d)`). Feeds the cutoff-general core
/// `Nat.zero`, reproducing the byte-identical proof term the lemma shipped with.
fn def_eq_respects_lift_at_value() -> String {
    format!("{}Nat.zero", def_eq_respects_lift_at_core())
}

/// Cutoff-GENERAL form: keeps the recursor's `forall (c : Nat), ...` conclusion
/// (the motive already generalizes the cutoff `c`). Same kernel-checked core term
/// as `def_eq_respects_lift_at_value`, only NOT specialized to cutoff 0 — needed
/// by the weakening (lift-preservation) proof's conv case, which recurses through
/// binders at increasing cutoffs.
fn def_eq_respects_lift_at_gen_value() -> String {
    def_eq_respects_lift_at_core().to_string()
}

/// Proof term for `instantiate_bvar_at_arg_congr` — honest nested-Nat.rec
/// three-way case analysis (Brick 9; replaces the FALSE def_eq_to_eq bridge).
///
/// `instantiate_bvar_at i d x` unfolds (delta) to
///   `Nat.rec _ (instantiate_bvar_geq i d x) (fun _ _ => bvar i) (Nat.sub d i)`
/// and `instantiate_bvar_geq i d x` to
///   `Nat.rec _ (lift_at x 0 d) (fun _ _ => bvar (i-1)) (Nat.sub i d)`,
/// so `x` occurs ONLY at the all-zero leaf as `lift_at x 0 d`. The outer Nat.rec
/// (on `Nat.sub d i`) closes the i<d arm by refl on `bvar i`; the inner Nat.rec
/// (on `Nat.sub i d`) closes the i>d arm by refl on `bvar (i-1)` and the i=d leaf
/// by `def_eq_respects_lift_at a a' d hf h`. The kernel bridges
/// `instantiate_bvar_at`/`instantiate_bvar_geq` to their Nat.rec unfoldings by
/// delta during type-checking, and the per-arm motive equalities by Nat.rec iota.
fn instantiate_bvar_at_arg_congr_value() -> String {
    concat!(
        "fun (i : Nat) (d : Nat) (a : KExpr) (a' : KExpr) ",
        "(hf : RedEnvFaithful the_red_env) (h : DefEq a a') => ",
        // ----- outer Nat.rec on (Nat.sub d i): motive over the instantiate_bvar_at unfolding -----
        "Nat.rec ",
        "(fun (n : Nat) => DefEq ",
        "(Nat.rec (fun (_ : Nat) => KExpr) (instantiate_bvar_geq i d a) ",
        "(fun (_ : Nat) (_ : KExpr) => KExpr.bvar i) n) ",
        "(Nat.rec (fun (_ : Nat) => KExpr) (instantiate_bvar_geq i d a') ",
        "(fun (_ : Nat) (_ : KExpr) => KExpr.bvar i) n)) ",
        // ----- outer zero case (i >= d): DefEq (instantiate_bvar_geq i d a) (.. a') -----
        // inner Nat.rec on (Nat.sub i d) over the instantiate_bvar_geq unfolding
        "(Nat.rec ",
        "(fun (m : Nat) => DefEq ",
        "(Nat.rec (fun (_ : Nat) => KExpr) (lift_at a Nat.zero d) ",
        "(fun (_ : Nat) (_ : KExpr) => KExpr.bvar (Nat.sub i (Nat.succ Nat.zero))) m) ",
        "(Nat.rec (fun (_ : Nat) => KExpr) (lift_at a' Nat.zero d) ",
        "(fun (_ : Nat) (_ : KExpr) => KExpr.bvar (Nat.sub i (Nat.succ Nat.zero))) m)) ",
        // inner zero case (i = d): the lift_at leaf, closed by def_eq_respects_lift_at
        "(def_eq_respects_lift_at a a' d hf h) ",
        // inner succ case (i > d): both sides bvar (i-1) -> refl
        "(fun (mk : Nat) ",
        "(_ihm : DefEq ",
        "(Nat.rec (fun (_ : Nat) => KExpr) (lift_at a Nat.zero d) ",
        "(fun (_ : Nat) (_ : KExpr) => KExpr.bvar (Nat.sub i (Nat.succ Nat.zero))) mk) ",
        "(Nat.rec (fun (_ : Nat) => KExpr) (lift_at a' Nat.zero d) ",
        "(fun (_ : Nat) (_ : KExpr) => KExpr.bvar (Nat.sub i (Nat.succ Nat.zero))) mk)) => ",
        "DefEq.refl (KExpr.bvar (Nat.sub i (Nat.succ Nat.zero)))) ",
        "(Nat.sub i d)) ",
        // ----- outer succ case (i < d): both sides bvar i -> refl -----
        "(fun (nk : Nat) ",
        "(_ihn : DefEq ",
        "(Nat.rec (fun (_ : Nat) => KExpr) (instantiate_bvar_geq i d a) ",
        "(fun (_ : Nat) (_ : KExpr) => KExpr.bvar i) nk) ",
        "(Nat.rec (fun (_ : Nat) => KExpr) (instantiate_bvar_geq i d a') ",
        "(fun (_ : Nat) (_ : KExpr) => KExpr.bvar i) nk)) => ",
        "DefEq.refl (KExpr.bvar i)) ",
        // ----- discharge: target index (Nat.sub d i) -----
        "(Nat.sub d i)",
    )
    .to_string()
}

#[cfg(test)]
mod tests {
    use crate::spec::types::ProofStatus;

    #[test]
    fn test_def_eq_respects_lift_at_is_derived_proved() {
        let spec = crate::test_utils::build_substitution_spec_with_stack();

        let def = spec
            .definitions()
            .get("def_eq_respects_lift_at")
            .expect("def_eq_respects_lift_at should be registered");
        assert!(
            def.value_src.is_some(),
            "def_eq_respects_lift_at should carry a closed proof term"
        );
        assert!(
            !def.is_axiom,
            "def_eq_respects_lift_at must not be an axiom"
        );
        assert_eq!(
            def.proof_status,
            ProofStatus::DerivedProved,
            "def_eq_respects_lift_at should be DerivedProved"
        );
        assert!(
            def.axiom_deps.is_empty(),
            "def_eq_respects_lift_at must have zero axiom_deps: {:?}",
            def.axiom_deps
        );
    }

    #[test]
    fn test_def_eq_instantiate_arg_congr_at_is_derived_proved() {
        // Substitution-typing pillar promotion: the complete KExpr.rec term is
        // kernel-checked at every spec build; the status flag no longer lags.
        let spec = crate::test_utils::build_substitution_spec_with_stack();

        let def = spec
            .definitions()
            .get("def_eq_instantiate_arg_congr_at")
            .expect("def_eq_instantiate_arg_congr_at should be registered");
        assert!(
            def.value_src.is_some(),
            "def_eq_instantiate_arg_congr_at should carry a closed proof term"
        );
        assert!(
            !def.is_axiom,
            "def_eq_instantiate_arg_congr_at must not be an axiom"
        );
        assert_eq!(
            def.proof_status,
            ProofStatus::DerivedProved,
            "def_eq_instantiate_arg_congr_at should be DerivedProved"
        );
        assert!(
            def.axiom_deps.is_empty(),
            "def_eq_instantiate_arg_congr_at must have zero axiom_deps: {:?}",
            def.axiom_deps
        );
    }
}
