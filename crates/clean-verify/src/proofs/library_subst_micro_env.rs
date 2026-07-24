// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Substitution, micro-checker, and environment extension proof terms
//! for the kernel ProofLibrary.
//!
//! Covers: substitution_def_eq.rs, micro_soundness.rs, and
//! env_extensions.rs spec definitions.
//!
//! Part of #3221.

use super::{ProofLibrary, ProofTerm};

impl ProofLibrary {
    pub(super) fn add_subst_micro_env_proofs(&mut self) {
        // === substitution_def_eq.rs: def_eq_respects_subst_at ===
        self.proofs.insert(
            "def_eq_respects_subst_at".to_string(),
            ProofTerm::new(
                "def_eq_respects_subst_at",
                concat!(
                    "fun (A : KExpr) (B : KExpr) (val : KExpr) (depth : Nat) (wd : DefEnvWellformed the_red_env) (wr : RecEnvWellformed (red_rec the_red_env)) (h : DefEq A B) => ",
                    "DefEq.rec ",
                    "(fun (a : KExpr) (b : KExpr) (_h : DefEq a b) => ",
                    "forall (w : KExpr) (d : Nat), DefEq (instantiate_at a w d) (instantiate_at b w d)) ",
                    "(fun (a : KExpr) (w : KExpr) (d : Nat) => DefEq.refl (instantiate_at a w d)) ",
                    "(fun (a : KExpr) (b : KExpr) (_h : DefEq a b) ",
                    "(ih : forall (w : KExpr) (d : Nat), DefEq (instantiate_at a w d) (instantiate_at b w d)) ",
                    "(w : KExpr) (d : Nat) => ",
                    "DefEq.symm (instantiate_at a w d) (instantiate_at b w d) (ih w d)) ",
                    "(fun (a : KExpr) (b : KExpr) (c : KExpr) (_hab : DefEq a b) (_hbc : DefEq b c) ",
                    "(ih_ab : forall (w : KExpr) (d : Nat), DefEq (instantiate_at a w d) (instantiate_at b w d)) ",
                    "(ih_bc : forall (w : KExpr) (d : Nat), DefEq (instantiate_at b w d) (instantiate_at c w d)) ",
                    "(w : KExpr) (d : Nat) => ",
                    "DefEq.trans (instantiate_at a w d) (instantiate_at b w d) (instantiate_at c w d) (ih_ab w d) (ih_bc w d)) ",
                    "(fun (A0 : KExpr) (body : KExpr) (arg : KExpr) ",
                    "(w : KExpr) (d : Nat) => ",
                    "beta_subst_commutes_at A0 body arg w d wd wr) ",
                    "(fun (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr) ",
                    "(_hf : DefEq f f') (_ha : DefEq a a') ",
                    "(ih_f : forall (w : KExpr) (d : Nat), DefEq (instantiate_at f w d) (instantiate_at f' w d)) ",
                    "(ih_a : forall (w : KExpr) (d : Nat), DefEq (instantiate_at a w d) (instantiate_at a' w d)) ",
                    "(w : KExpr) (d : Nat) => ",
                    "instantiate_at_app_preserves_def_eq f f' a a' w d (ih_f w d) (ih_a w d)) ",
                    "(fun (A0 : KExpr) (A0' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
                    "(_hA : DefEq A0 A0') (_hb : DefEq b0 b0') ",
                    "(ih_A : forall (w : KExpr) (d : Nat), DefEq (instantiate_at A0 w d) (instantiate_at A0' w d)) ",
                    "(ih_b : forall (w : KExpr) (d : Nat), DefEq (instantiate_at b0 w d) (instantiate_at b0' w d)) ",
                    "(w : KExpr) (d : Nat) => ",
                    "instantiate_at_lam_preserves_def_eq A0 A0' b0 b0' w d (ih_A w d) (ih_b w (Nat.succ d))) ",
                    "(fun (A0 : KExpr) (A0' : KExpr) (B0 : KExpr) (B0' : KExpr) ",
                    "(_hA : DefEq A0 A0') (_hB : DefEq B0 B0') ",
                    "(ih_A : forall (w : KExpr) (d : Nat), DefEq (instantiate_at A0 w d) (instantiate_at A0' w d)) ",
                    "(ih_B : forall (w : KExpr) (d : Nat), DefEq (instantiate_at B0 w d) (instantiate_at B0' w d)) ",
                    "(w : KExpr) (d : Nat) => ",
                    "instantiate_at_pi_preserves_def_eq A0 A0' B0 B0' w d (ih_A w d) (ih_B w (Nat.succ d))) ",
                    "(fun (e : KExpr) (e' : KExpr) (hd : delta_reduces e e') (w : KExpr) (d : Nat) => ",
                    "delta_subst_preserves_def_eq_at e e' w d wd hd) ",
                    "(fun (e : KExpr) (e' : KExpr) (hi : iota_reduces e e') (w : KExpr) (d : Nat) => ",
                    "iota_subst_preserves_def_eq_at e e' w d wr hi) ",
                    // zeta: inline mirror of the beta minor (beta_subst_commutes_at shape)
                    // over KExpr.let_. instantiate_at_let_ unfolds the redex, DefEq.zeta
                    // contracts it, instantiate_nested_commutes_zero_subst (SAME lemma the
                    // beta case uses, body:=b, arg:=v) closes the residual raw-term equality.
                    "(fun (ty : KExpr) (v : KExpr) (b : KExpr) (w : KExpr) (d : Nat) => ",
                    "def_eq_eq_right ",
                    "(instantiate_at (KExpr.let_ ty v b) w d) ",
                    "(instantiate (instantiate_at b w (Nat.succ d)) (instantiate_at v w d)) ",
                    "(instantiate_at (instantiate b v) w d) ",
                    "(def_eq_eq_left ",
                    "(instantiate_at (KExpr.let_ ty v b) w d) ",
                    "(KExpr.let_ (instantiate_at ty w d) (instantiate_at v w d) (instantiate_at b w (Nat.succ d))) ",
                    "(instantiate (instantiate_at b w (Nat.succ d)) (instantiate_at v w d)) ",
                    "(instantiate_at_let_ ty v b w d) ",
                    "(DefEq.zeta (instantiate_at ty w d) (instantiate_at v w d) (instantiate_at b w (Nat.succ d)))) ",
                    "(Eq.symm KExpr ",
                    "(instantiate_at (instantiate b v) w d) ",
                    "(instantiate_at (instantiate_at b w (Nat.succ d)) (instantiate_at v w d) Nat.zero) ",
                    "(instantiate_nested_commutes_zero_subst b v w d))) ",
                    // let_cong: inline mirror of the lam_cong minor over KExpr.let_
                    // (ty/val at d, body at succ d) via instantiate_at_let_ + DefEq.let_cong.
                    "(fun (ty : KExpr) (ty' : KExpr) (v : KExpr) (v' : KExpr) (b : KExpr) (b' : KExpr) ",
                    "(_hty : DefEq ty ty') (_hv : DefEq v v') (_hb : DefEq b b') ",
                    "(ih_ty : forall (w : KExpr) (d : Nat), DefEq (instantiate_at ty w d) (instantiate_at ty' w d)) ",
                    "(ih_v : forall (w : KExpr) (d : Nat), DefEq (instantiate_at v w d) (instantiate_at v' w d)) ",
                    "(ih_b : forall (w : KExpr) (d : Nat), DefEq (instantiate_at b w d) (instantiate_at b' w d)) ",
                    "(w : KExpr) (d : Nat) => ",
                    "def_eq_eq_right ",
                    "(instantiate_at (KExpr.let_ ty v b) w d) ",
                    "(KExpr.let_ (instantiate_at ty' w d) (instantiate_at v' w d) (instantiate_at b' w (Nat.succ d))) ",
                    "(instantiate_at (KExpr.let_ ty' v' b') w d) ",
                    "(def_eq_eq_left ",
                    "(instantiate_at (KExpr.let_ ty v b) w d) ",
                    "(KExpr.let_ (instantiate_at ty w d) (instantiate_at v w d) (instantiate_at b w (Nat.succ d))) ",
                    "(KExpr.let_ (instantiate_at ty' w d) (instantiate_at v' w d) (instantiate_at b' w (Nat.succ d))) ",
                    "(instantiate_at_let_ ty v b w d) ",
                    "(DefEq.let_cong ",
                    "(instantiate_at ty w d) (instantiate_at ty' w d) ",
                    "(instantiate_at v w d) (instantiate_at v' w d) ",
                    "(instantiate_at b w (Nat.succ d)) (instantiate_at b' w (Nat.succ d)) ",
                    "(ih_ty w d) (ih_v w d) (ih_b w (Nat.succ d)))) ",
                    "(Eq.symm KExpr ",
                    "(instantiate_at (KExpr.let_ ty' v' b') w d) ",
                    "(KExpr.let_ (instantiate_at ty' w d) (instantiate_at v' w d) (instantiate_at b' w (Nat.succ d))) ",
                    "(instantiate_at_let_ ty' v' b' w d))) ",
                    "A B h val depth",
                ),
                "DefEq is preserved by instantiate_at at any binder depth. Via DefEq.rec (eleven minors incl. trailing zeta/let_cong).",
            ),
        );

        // === substitution_def_eq.rs: def_eq_respects_subst ===
        self.proofs.insert(
            "def_eq_respects_subst".to_string(),
            ProofTerm::new(
                "def_eq_respects_subst",
                "fun (A : KExpr) (B : KExpr) (v : KExpr) (wd : DefEnvWellformed the_red_env) (wr : RecEnvWellformed (red_rec the_red_env)) (h : DefEq A B) => def_eq_respects_subst_at A B v Nat.zero wd wr h",
                "If A = B, then A[v/0] = B[v/0]. Via def_eq_respects_subst_at at depth 0.",
            ),
        );

        // === substitution_def_eq.rs: beta_subst_commutes ===
        self.proofs.insert(
            "beta_subst_commutes".to_string(),
            ProofTerm::new(
                "beta_subst_commutes",
                concat!(
                    "fun (A : KExpr) (body : KExpr) (arg : KExpr) (w : KExpr) ",
                    "(wd : DefEnvWellformed the_red_env) ",
                    "(wr : RecEnvWellformed (red_rec the_red_env)) => ",
                    "def_eq_respects_subst ",
                    "(KExpr.app (KExpr.lam A body) arg) ",
                    "(instantiate body arg) ",
                    "w wd wr ",
                    "(DefEq.beta A body arg)"
                ),
                "Beta-subst commutation at depth 0: untyped DefEq.beta then def_eq_respects_subst.",
            ),
        );

        // === substitution_def_eq.rs: beta_subst_commutes_at ===
        // GENUINE, non-circular proof (the #2872 cycle is removed). MUST stay
        // byte-identical to the spec definition's value (the BETA_SUBST_COMMUTES_AT_PROOF
        // const in spec/core_spec/substitution_def_eq.rs). It reduces the
        // binder-depth beta redex arithmetically: instantiate_at_app/lam unfold
        // it, DefEq.beta contracts it, and the DerivedProved de Bruijn lemma
        // instantiate_nested_commutes_zero_subst closes the residual raw-term
        // equality — NO route through def_eq_respects_subst_at.
        self.proofs.insert(
            "beta_subst_commutes_at".to_string(),
            ProofTerm::new(
                "beta_subst_commutes_at",
                concat!(
                    "fun (A : KExpr) (body : KExpr) (arg : KExpr) (val : KExpr) (depth : Nat) ",
                    "(wd : DefEnvWellformed the_red_env) ",
                    "(wr : RecEnvWellformed (red_rec the_red_env)) => ",
                    "def_eq_eq_right ",
                    "(instantiate_at (KExpr.app (KExpr.lam A body) arg) val depth) ",
                    "(instantiate (instantiate_at body val (Nat.succ depth)) (instantiate_at arg val depth)) ",
                    "(instantiate_at (instantiate body arg) val depth) ",
                    "(def_eq_eq_left ",
                    "(instantiate_at (KExpr.app (KExpr.lam A body) arg) val depth) ",
                    "(KExpr.app (KExpr.lam (instantiate_at A val depth) (instantiate_at body val (Nat.succ depth))) ",
                    "(instantiate_at arg val depth)) ",
                    "(instantiate (instantiate_at body val (Nat.succ depth)) (instantiate_at arg val depth)) ",
                    "(Eq.trans KExpr ",
                    "(instantiate_at (KExpr.app (KExpr.lam A body) arg) val depth) ",
                    "(KExpr.app (instantiate_at (KExpr.lam A body) val depth) (instantiate_at arg val depth)) ",
                    "(KExpr.app (KExpr.lam (instantiate_at A val depth) (instantiate_at body val (Nat.succ depth))) ",
                    "(instantiate_at arg val depth)) ",
                    "(instantiate_at_app (KExpr.lam A body) arg val depth) ",
                    "(Eq.cong KExpr KExpr ",
                    "(fun (x : KExpr) => KExpr.app x (instantiate_at arg val depth)) ",
                    "(instantiate_at (KExpr.lam A body) val depth) ",
                    "(KExpr.lam (instantiate_at A val depth) (instantiate_at body val (Nat.succ depth))) ",
                    "(instantiate_at_lam A body val depth))) ",
                    "(DefEq.beta (instantiate_at A val depth) (instantiate_at body val (Nat.succ depth)) ",
                    "(instantiate_at arg val depth))) ",
                    "(Eq.symm KExpr ",
                    "(instantiate_at (instantiate body arg) val depth) ",
                    "(instantiate_at (instantiate_at body val (Nat.succ depth)) (instantiate_at arg val depth) Nat.zero) ",
                    "(instantiate_nested_commutes_zero_subst body arg val depth))"
                ),
                "Binder-depth beta-subst commutation: arithmetic reduction (instantiate_at_app/lam \
                 + DefEq.beta + instantiate_nested_commutes_zero_subst), no def_eq_respects_subst_at cycle.",
            ),
        );

        // === def_eq_lift_congr.rs: instantiate_bvar_at_arg_congr ===
        // Bvar case: three-way Nat.rec produces DefEq.refl for i!=d and uses
        // hypothesis for i=d (through lift_at). The proof delegates to the
        // existing instantiate_bvar_at machinery.
        self.proofs.insert(
            "instantiate_bvar_at_arg_congr".to_string(),
            ProofTerm::new(
                "instantiate_bvar_at_arg_congr",
                concat!(
                    "fun (i : Nat) (d : Nat) (a : KExpr) (a' : KExpr) ",
                    "(hf : RedEnvFaithful the_red_env) (h : DefEq a a') => ",
                    "instantiate_bvar_at_arg_congr i d a a' hf h"
                ),
                "Bvar case: instantiate_bvar_at preserves argument DefEq. Part of #3221.",
            ),
        );

        // === def_eq_lift_congr.rs: def_eq_instantiate_arg_congr_at ===
        // KExpr.rec structural induction on B proving argument congruence
        // at arbitrary depth d.
        self.proofs.insert(
            "def_eq_instantiate_arg_congr_at".to_string(),
            ProofTerm::new(
                "def_eq_instantiate_arg_congr_at",
                concat!(
                    "fun (B : KExpr) (a : KExpr) (a' : KExpr) (d : Nat) ",
                    "(hf : RedEnvFaithful the_red_env) (h : DefEq a a') => ",
                    "KExpr.rec ",
                    "(fun (e : KExpr) => ",
                    "forall (a0 : KExpr) (a0' : KExpr) (d0 : Nat), DefEq a0 a0' -> ",
                    "DefEq (instantiate_at e a0 d0) (instantiate_at e a0' d0)) ",
                    // sort case: instantiate_at (sort n) a d = sort n for both
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
                    // bvar case: delegate to instantiate_bvar_at_arg_congr
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
                    // app case: distribute + app_cong on IHs
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
                    // lam case: distribute + lam_cong on IHs
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
                    // pi case: distribute + pi_cong on IHs
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
                    // const case: instantiate_at (const n us) a d = const n us for both
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
                    // let_ case: distribute (instantiate_at_let_) + let_cong on IHs
                    // (ty/val at d0, body at succ d0 — mirror of the lam/pi arms with
                    // the added val field)
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
                    // Apply the recursor to B and the arguments
                    "B a a' d h",
                ),
                concat!(
                    "DefEq congruence for instantiate_at argument position: if a ~ a', ",
                    "then instantiate_at B a d ~ instantiate_at B a' d. ",
                    "Via KExpr.rec structural induction on B. Part of #3221.",
                ),
            ),
        );

        // === type_preservation_subst.rs: def_eq_instantiate_arg_congr ===
        // Top-level wrapper: delegates to def_eq_instantiate_arg_congr_at at depth 0.
        self.proofs.insert(
            "def_eq_instantiate_arg_congr".to_string(),
            ProofTerm::new(
                "def_eq_instantiate_arg_congr",
                concat!(
                    "fun (B : KExpr) (a : KExpr) (a' : KExpr) ",
                    "(hf : RedEnvFaithful the_red_env) (h : DefEq a a') => ",
                    "def_eq_instantiate_arg_congr_at B a a' Nat.zero hf h"
                ),
                "DefEq congruence for instantiate argument: delegates to depth-0 case. Part of #3221.",
            ),
        );

        // === micro_soundness.rs: micro_verify_sound ===
        self.proofs.insert(
            "micro_verify_sound".to_string(),
            ProofTerm::new(
                "micro_verify_sound",
                concat!(
                    "fun (cert : MicroCert) (e : MicroExpr) (T0 : MicroExpr) ",
                    "(_h : Eq MicroExpr (micro_verify cert e) T0) => micro_has_type_total e T0",
                ),
                "Micro-checker soundness: if verify succeeds with type T, then e : T. \
                 VACUITY-DRAINED to the totality corollary (micro_has_type_total); \
                 MicroCert_rec retired.",
            ),
        );

        // === micro_soundness.rs: micro_type_preservation ===
        self.proofs.insert(
            "micro_type_preservation".to_string(),
            ProofTerm::new(
                "micro_type_preservation",
                concat!(
                    "fun (e : MicroExpr) (T : MicroExpr) (e' : MicroExpr) ",
                    "(ht : micro_has_type e T) ",
                    "(heq : Eq Bool (micro_def_eq e e') Bool.true) => ",
                    "micro_def_eq_preserves_typing e e' T ht heq",
                ),
                "Micro-checker type preservation: forwards to micro_def_eq_preserves_typing.",
            ),
        );

        // === micro_soundness.rs: translation_preserves_typing ===
        self.proofs.insert(
            "translation_preserves_typing".to_string(),
            ProofTerm::new(
                "translation_preserves_typing",
                "fun (e : KExpr) (T : KExpr) (ht : has_type e T) => kernel_to_micro_typing e T ht",
                "Translation preserves typing judgments: forwards to kernel_to_micro_typing.",
            ),
        );

        // === micro_soundness.rs: translation_preserves_def_eq REMOVED (Brick 3) ===
        // It forwarded to the FALSE `kernel_to_micro_def_eq` axiom, which was
        // refuted-and-deleted (a DefEq.beta redex under a lambda binder is invisible
        // to weak-head micro_whnf). See micro_soundness.rs for the machine-checked
        // counterexample and the honest successor obligation.

        // === env_extensions.rs: definitional_extension_sound ===
        self.proofs.insert(
            "definitional_extension_sound".to_string(),
            ProofTerm::new(
                "definitional_extension_sound",
                concat!(
                    "fun (env : KEnv) (env' : KEnv) ",
                    "(h_ext : DefinitionalExtension env env') ",
                    "(h_sound : EnvSound env) => ",
                    "DefinitionalExtension.rec ",
                    "(fun (src_env : KEnv) (dst_env : KEnv) (h_ext_step : DefinitionalExtension src_env dst_env) => EnvSound src_env -> EnvSound dst_env) ",
                    "(fun (base : KEnv) (base_sound : EnvSound base) => base_sound) ",
                    "(fun (src_env : KEnv) (dst_env : KEnv) (h_const : ConstantExtension src_env dst_env) ",
                    "(src_sound : EnvSound src_env) => ",
                    "constant_extension_preserves_soundness src_env dst_env h_const src_sound) ",
                    "(fun (src_env : KEnv) (dst_env : KEnv) (h_ind : InductiveExtension src_env dst_env) ",
                    "(src_sound : EnvSound src_env) => ",
                    "inductive_extension_preserves_soundness src_env dst_env h_ind src_sound) ",
                    "(fun (src_env : KEnv) (mid_env : KEnv) (dst_env : KEnv) ",
                    "(h_left : DefinitionalExtension src_env mid_env) ",
                    "(h_right : DefinitionalExtension mid_env dst_env) ",
                    "(ih_left : EnvSound src_env -> EnvSound mid_env) ",
                    "(ih_right : EnvSound mid_env -> EnvSound dst_env) ",
                    "(src_sound : EnvSound src_env) => ",
                    "ih_right (ih_left src_sound)) ",
                    "env env' h_ext h_sound",
                ),
                "Any chain of definitional extensions preserves EnvSound. Via DefinitionalExtension.rec.",
            ),
        );
    }
}
