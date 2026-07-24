// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Matrix Rank Supporting Lemmas — STATED CONJECTURES (NOT PROVED)
//!
//! **WARNING: All "theorem" declarations here are `Declaration::Axiom` with NO
//! proof terms. These are formally stated but not proved. Replace with
//! `Declaration::Theorem` + constructive proof terms to make genuine proofs.**
//!
//! Ones-matrix rank lemma and rank-deficient zonotope width equivalence.
//! Formalizes supporting lemmas for C002 (LayerNorm correlation firewall).
//!
//! Definitions: `ones_matrix` (reducible). `mean_projection` is `Opaque`
//! (#3587 Branch A, re-demoted from reducible Definition/#3458).
//! Conjectures (axiom-backed): `ones_matrix_rank_one`, `mean_projection_idempotent`,
//! `identity_minus_projection_rank`, `zonotope_rankdef_width_eq`.
//!
//! Proof approach (not yet implemented): mean_projection rank 1, complementary
//! orthogonal projection I-P, rank-nullity, rank-deficient collapse.
//!
//! Part of #3207.

use super::nn_verify_matrix_rank_defs;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::Expr;
use crate::level::Level;
use crate::name::Name;

/// Shared constants for matrix rank declaration construction.
pub(super) struct MatrixRankConsts {
    pub(super) nat: Expr,
    pub(super) rat: Expr,
    pub(super) fin: Expr,
    pub(super) nn_mat: Expr,
    pub(super) ib: Expr,
    pub(super) eq: Expr,
    pub(super) nat_one: Expr,
    pub(super) nat_sub: Expr,
    pub(super) le_le: Expr,
    pub(super) inst_le_nat: Expr,
    pub(super) rat_one: Expr,
    /// `NNVerify.ones_matrix`
    pub(super) ones_matrix: Expr,
    /// `NNVerify.mean_projection`
    pub(super) mean_projection: Expr,
    /// `NNVerify.matrix_rank`
    pub(super) matrix_rank: Expr,
    /// `NNVerify.matrix_mul`
    pub(super) matrix_mul: Expr,
    /// `NNVerify.matrix_sub`
    pub(super) matrix_sub: Expr,
    /// `NNVerify.identity_matrix`
    pub(super) identity_matrix: Expr,
    /// `NNVerify.interval_hull_width`
    pub(super) interval_hull_width: Expr,
    /// `NNVerify.linear_image_zonotope`
    pub(super) linear_image_zonotope: Expr,
    /// `NNVerify.fresh_zonotope_from_hull`
    pub(super) fresh_zonotope_from_hull: Expr,
    /// `Rat.zero`
    pub(super) rat_zero: Expr,
    /// `Rat.sub`
    pub(super) rat_sub: Expr,
    /// `@ite : {α : Sort u} → (c : Prop) → [Decidable c] → α → α → α`
    pub(super) ite: Expr,
    /// `instDecidableEqFin : {n : Nat} → (a b : Fin n) → Decidable (a = b)`
    pub(super) inst_dec_eq_fin: Expr,
    /// `@Eq` at universe 1
    pub(super) eq_u1: Expr,
}

impl MatrixRankConsts {
    fn new() -> Self {
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            nn_mat: Expr::const_(Name::from_string("NNVerify.NNMat"), vec![]),
            ib: Expr::const_(Name::from_string("NNVerify.IntervalBounds"), vec![]),
            eq: Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            nat_one: Expr::app(
                Expr::const_(Name::from_string("Nat.succ"), vec![]),
                Expr::const_(Name::from_string("Nat.zero"), vec![]),
            ),
            nat_sub: Expr::const_(Name::from_string("Nat.sub"), vec![]),
            le_le: Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
            inst_le_nat: Expr::const_(Name::from_string("instLENat"), vec![]),
            rat_one: Expr::const_(Name::from_string("Rat.one"), vec![]),
            ones_matrix: Expr::const_(Name::from_string("NNVerify.ones_matrix"), vec![]),
            mean_projection: Expr::const_(Name::from_string("NNVerify.mean_projection"), vec![]),
            matrix_rank: Expr::const_(Name::from_string("NNVerify.matrix_rank"), vec![]),
            matrix_mul: Expr::const_(Name::from_string("NNVerify.matrix_mul"), vec![]),
            matrix_sub: Expr::const_(Name::from_string("NNVerify.matrix_sub"), vec![]),
            identity_matrix: Expr::const_(Name::from_string("NNVerify.identity_matrix"), vec![]),
            interval_hull_width: Expr::const_(
                Name::from_string("NNVerify.interval_hull_width"),
                vec![],
            ),
            linear_image_zonotope: Expr::const_(
                Name::from_string("NNVerify.linear_image_zonotope"),
                vec![],
            ),
            fresh_zonotope_from_hull: Expr::const_(
                Name::from_string("NNVerify.fresh_zonotope_from_hull"),
                vec![],
            ),
            rat_zero: Expr::const_(Name::from_string("Rat.zero"), vec![]),
            rat_sub: Expr::const_(Name::from_string("Rat.sub"), vec![]),
            ite: Expr::const_(Name::from_string("ite"), vec![Level::succ(Level::zero())]),
            inst_dec_eq_fin: Expr::const_(Name::from_string("instDecidableEqFin"), vec![]),
            eq_u1: Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        }
    }

    /// `Nat.sub a b`
    pub(super) fn nat_sub_app(&self, a: Expr, b: Expr) -> Expr {
        Expr::app(Expr::app(self.nat_sub.clone(), a), b)
    }

    /// `Eq @Nat a b`
    pub(super) fn nat_eq(&self, a: Expr, b: Expr) -> Expr {
        Expr::app(
            Expr::app(Expr::app(self.eq.clone(), self.nat.clone()), a),
            b,
        )
    }

    /// `Eq @(NNMat n n) a b`
    pub(super) fn mat_eq(&self, n: &Expr, a: Expr, b: Expr) -> Expr {
        let mat_nn = self.mat_of(n.clone(), n.clone());
        Expr::app(Expr::app(Expr::app(self.eq.clone(), mat_nn), a), b)
    }

    /// `NNMat m n`
    pub(super) fn mat_of(&self, m: Expr, n: Expr) -> Expr {
        Expr::app(Expr::app(self.nn_mat.clone(), m), n)
    }

    /// `NNVerify.matrix_rank n n M`
    pub(super) fn rank_app(&self, n: &Expr, m: Expr) -> Expr {
        Expr::apps(self.matrix_rank.clone(), [n.clone(), n.clone(), m])
    }

    /// `NNVerify.matrix_mul n n n A B`
    pub(super) fn mat_mul_app(&self, n: &Expr, a: Expr, b: Expr) -> Expr {
        Expr::apps(
            self.matrix_mul.clone(),
            [n.clone(), n.clone(), n.clone(), a, b],
        )
    }

    /// `NNVerify.matrix_sub n n A B`
    pub(super) fn mat_sub_app(&self, n: &Expr, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.matrix_sub.clone(), [n.clone(), n.clone(), a, b])
    }

    /// `LE.le @Nat instLENat a b`
    pub(super) fn nat_le(&self, a: Expr, b: Expr) -> Expr {
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(self.le_le.clone(), self.nat.clone()),
                    self.inst_le_nat.clone(),
                ),
                a,
            ),
            b,
        )
    }
}

// ---- Environment impl ----

impl Environment {
    /// Initialize ones-matrix rank and zonotope rank-deficiency declarations.
    /// Depends on init_nn_verify_types, init_eq, init_nat, init_rat,
    /// init_rat_arith. Part of #3207.
    pub(crate) fn init_nn_verify_matrix_rank(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("NNVerify.ones_matrix"))
            .is_some()
        {
            return Ok(());
        }
        self.init_nn_verify_types()?;
        self.init_eq()?;
        self.init_nat()?;
        self.init_rat()?;
        self.init_rat_arith()?;

        let c = MatrixRankConsts::new();

        // Remaining axioms: matrix_rank, matrix_mul,
        // interval_hull_width, linear_image_zonotope
        self.register_matrix_rank_axiom(&c)?;
        self.register_matrix_mul_axiom(&c)?;
        // Definitions (#3372): matrix_sub, identity_matrix, fresh_zonotope_from_hull
        self.register_matrix_sub_axiom(&c)?;
        // identity_matrix needs instDecidableEqFin for the Kronecker delta
        self.ensure_inst_decidable_eq_fin_for_matrix_rank(&c)?;
        self.register_identity_matrix_axiom(&c)?;
        self.register_interval_hull_width_axiom(&c)?;
        self.register_linear_image_zonotope_axiom(&c)?;
        self.register_fresh_zonotope_from_hull_axiom(&c)?;

        // Definitions: ones_matrix. Opaque: mean_projection (#3587 Branch A
        // re-demotion from reducible Definition/#3458).
        self.register_ones_matrix(&c)?;
        self.register_mean_projection(&c)?;

        // Supporting axioms for C002 constructive proofs (Part of #3307)
        self.register_scalar_mat_mul(&c)?;
        self.register_scalar_mat_rank_le(&c)?;
        self.register_nat_eq_pred_succ_le(&c)?;
        self.register_le_trans_nat(&c)?;
        self.register_nat_succ_le_succ(&c)?;

        // Conjectures (axiom-backed, no proof terms)
        self.register_ones_matrix_rank_one(&c)?;
        self.register_mean_projection_idempotent(&c)?;
        self.register_identity_minus_projection_rank(&c)?;
        self.register_zonotope_rankdef_width_eq(&c)?;

        Ok(())
    }

    // ---- Helper axioms ----

    /// Ensure `instDecidableEqFin` is registered for the identity_matrix
    /// Kronecker delta value.
    ///
    /// `instDecidableEqFin : {n : Nat} -> (a b : Fin n) -> Decidable (Eq (Fin n) a b)`
    ///
    /// TCB-shrink: now delegates to the constructive, axiom-free
    /// `register_fin_dec_eq_proof` (`algebra_fin_dec_eq_proof.rs`) — a real
    /// `Declaration::Definition` computing on `Nat.decEq (Fin.val a)(Fin.val b)`
    /// — instead of registering a bare `Declaration::Axiom`.
    fn ensure_inst_decidable_eq_fin_for_matrix_rank(
        &mut self,
        _c: &MatrixRankConsts,
    ) -> Result<(), EnvError> {
        self.register_fin_dec_eq_proof()
    }

    fn register_matrix_rank_axiom(&mut self, c: &MatrixRankConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("NNVerify.matrix_rank"))
            .is_some()
        {
            return Ok(());
        }
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("NNVerify.matrix_rank"),
            level_params: vec![],
            type_: nn_verify_matrix_rank_defs::build_matrix_rank_type(c),
        })
    }

    fn register_matrix_mul_axiom(&mut self, c: &MatrixRankConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("NNVerify.matrix_mul"))
            .is_some()
        {
            return Ok(());
        }
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("NNVerify.matrix_mul"),
            level_params: vec![],
            type_: nn_verify_matrix_rank_defs::build_matrix_mul_type(c),
        })
    }

    /// `NNVerify.matrix_sub : (m n : Nat) -> NNMat m n -> NNMat m n -> NNMat m n`
    /// Definition (#3372): `fun m n A B i j => Rat.sub (A i j) (B i j)`.
    fn register_matrix_sub_axiom(&mut self, c: &MatrixRankConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("NNVerify.matrix_sub"))
            .is_some()
        {
            return Ok(());
        }
        self.add_decl(Declaration::Definition {
            name: Name::from_string("NNVerify.matrix_sub"),
            level_params: vec![],
            type_: nn_verify_matrix_rank_defs::build_matrix_sub_type(c),
            value: nn_verify_matrix_rank_defs::build_matrix_sub_value(c),
            is_reducible: true,
        })
    }

    /// `NNVerify.identity_matrix : (n : Nat) -> NNMat n n`
    /// Definition (#3372): Kronecker delta `fun n i j => ite (i = j) 1 0`.
    fn register_identity_matrix_axiom(&mut self, c: &MatrixRankConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("NNVerify.identity_matrix"))
            .is_some()
        {
            return Ok(());
        }
        // Ensure ite and instDecidableEqFin are available for the Kronecker delta
        self.init_ite()?;
        self.init_decidable_eq()?;
        self.add_decl(Declaration::Definition {
            name: Name::from_string("NNVerify.identity_matrix"),
            level_params: vec![],
            type_: nn_verify_matrix_rank_defs::build_identity_matrix_type(c),
            value: nn_verify_matrix_rank_defs::build_identity_matrix_value(c),
            is_reducible: true,
        })
    }

    fn register_interval_hull_width_axiom(&mut self, c: &MatrixRankConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("NNVerify.interval_hull_width"))
            .is_some()
        {
            return Ok(());
        }
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("NNVerify.interval_hull_width"),
            level_params: vec![],
            type_: nn_verify_matrix_rank_defs::build_interval_hull_width_type(c),
        })
    }

    fn register_linear_image_zonotope_axiom(
        &mut self,
        c: &MatrixRankConsts,
    ) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("NNVerify.linear_image_zonotope"))
            .is_some()
        {
            return Ok(());
        }
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("NNVerify.linear_image_zonotope"),
            level_params: vec![],
            type_: nn_verify_matrix_rank_defs::build_linear_image_zonotope_type(c),
        })
    }

    /// Opaque with body `fun (n : Nat) (B : IntervalBounds n) => B`.
    ///
    /// **#3639 Branch A MASQUERADE co-demotion (2026-04-20):** flipped from
    /// `Declaration::Definition { is_reducible: true }` (#3371) to
    /// `Declaration::Opaque` with the SAME body — only the declaration kind
    /// flipped. The reducible Definition let `def_eq` δ-unfold
    /// `fresh_zonotope_from_hull n B → B`, which let the `layernorm_ibp_bridge`
    /// Theorem close via `Eq.refl` over the identity carrier (Rule M2
    /// placeholder-body + Rule M4 Eq.refl root per
    /// `designs/2026-04-19-demasquerade-cxxx-pattern.md`). Opaques are not
    /// δ-unfolded, so the alias-collapse path is closed; the former
    /// `layernorm_ibp_bridge`, `C002.correlation_firewall_core`, and
    /// `C002.correlation_firewall` Theorems are co-demoted to
    /// `Declaration::Axiom` on their original Pi types (see
    /// `nn_verification_c002.rs`). Guard tests:
    /// `test_c002_fresh_zonotope_from_hull_is_opaque_not_reducible_definition`.
    fn register_fresh_zonotope_from_hull_axiom(
        &mut self,
        c: &MatrixRankConsts,
    ) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("NNVerify.fresh_zonotope_from_hull"))
            .is_some()
        {
            return Ok(());
        }
        self.add_decl(Declaration::Opaque {
            name: Name::from_string("NNVerify.fresh_zonotope_from_hull"),
            level_params: vec![],
            type_: nn_verify_matrix_rank_defs::build_fresh_zonotope_from_hull_type(c),
            value: nn_verify_matrix_rank_defs::build_fresh_zonotope_from_hull_value(c),
        })
    }

    // ---- Supporting axioms for C002 constructive proofs (#3307) ----

    /// `NNVerify.scalar_mat_mul : (m n : Nat) -> Rat -> NNMat m n -> NNMat m n`
    /// Definition (#3372): `fun m n s A i j => Rat.mul s (A i j)`.
    fn register_scalar_mat_mul(&mut self, c: &MatrixRankConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.scalar_mat_mul");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        use crate::env::decl_builder::EnvDeclBuilder;
        use crate::expr::BinderInfo;
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(c.nat.clone());
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let mat_mn = c.mat_of(m.clone(), n.clone());
            let (s_id, _) = b.fresh_local(c.rat.clone());
            let (a_id, _) = b.fresh_local(mat_mn.clone());
            let r = b.mk_pi(a_id, BinderInfo::Default, mat_mn.clone(), mat_mn);
            let r = b.mk_pi(s_id, BinderInfo::Default, c.rat.clone(), r);
            let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
            let r = b.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };
        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: ty,
            value: nn_verify_matrix_rank_defs::build_scalar_mat_mul_value(c),
            is_reducible: true,
        })
    }

    fn register_scalar_mat_rank_le(&mut self, c: &MatrixRankConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.scalar_mat_rank_le");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Axiom {
            name,
            level_params: vec![],
            type_: nn_verify_matrix_rank_defs::build_scalar_mat_rank_le_type(c),
        })
    }

    fn register_nat_eq_pred_succ_le(&mut self, c: &MatrixRankConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.nat_eq_pred_succ_le");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Axiom {
            name,
            level_params: vec![],
            type_: nn_verify_matrix_rank_defs::build_nat_eq_pred_succ_le_type(c),
        })
    }

    fn register_le_trans_nat(&mut self, c: &MatrixRankConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.le_trans_nat");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Axiom {
            name,
            level_params: vec![],
            type_: nn_verify_matrix_rank_defs::build_le_trans_nat_type(c),
        })
    }

    fn register_nat_succ_le_succ(&mut self, c: &MatrixRankConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.nat_succ_le_succ");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Axiom {
            name,
            level_params: vec![],
            type_: nn_verify_matrix_rank_defs::build_nat_succ_le_succ_type(c),
        })
    }

    // ---- Definitions ----

    fn register_ones_matrix(&mut self, c: &MatrixRankConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("NNVerify.ones_matrix"))
            .is_some()
        {
            return Ok(());
        }
        self.add_decl(Declaration::Definition {
            name: Name::from_string("NNVerify.ones_matrix"),
            level_params: vec![],
            type_: nn_verify_matrix_rank_defs::build_ones_matrix_type(c),
            value: nn_verify_matrix_rank_defs::build_ones_matrix_value(c),
            is_reducible: true,
        })
    }

    /// `NNVerify.mean_projection : (n : Nat) -> NNMat n n`. Opaque (#3587
    /// Branch A, re-demoted from reducible Definition/#3458). Placeholder
    /// `ones_matrix n` for real `(1/n)*J_n`; Opaque closes the δ-reduction
    /// MASQUERADE path (Rule M2, designs/2026-04-19-demasquerade-cxxx-pattern.md).
    fn register_mean_projection(&mut self, c: &MatrixRankConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("NNVerify.mean_projection"))
            .is_some()
        {
            return Ok(());
        }
        self.add_decl(Declaration::Opaque {
            name: Name::from_string("NNVerify.mean_projection"),
            level_params: vec![],
            type_: nn_verify_matrix_rank_defs::build_mean_projection_type(c),
            value: nn_verify_matrix_rank_defs::build_mean_projection_value(c),
        })
    }

    // ---- Conjectures (axiom-backed, no proof terms) ----

    fn register_ones_matrix_rank_one(&mut self, c: &MatrixRankConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.ones_matrix_rank_one");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        // Registered as axiom — no proof term. This is an unproved conjecture.
        self.add_decl(Declaration::Axiom {
            name,
            level_params: vec![],
            type_: nn_verify_matrix_rank_defs::build_ones_matrix_rank_one_type(c),
        })
    }

    fn register_mean_projection_idempotent(
        &mut self,
        c: &MatrixRankConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.mean_projection_idempotent");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Axiom {
            name,
            level_params: vec![],
            type_: nn_verify_matrix_rank_defs::build_mean_projection_idempotent_type(c),
        })
    }

    fn register_identity_minus_projection_rank(
        &mut self,
        c: &MatrixRankConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.identity_minus_projection_rank");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Axiom {
            name,
            level_params: vec![],
            type_: nn_verify_matrix_rank_defs::build_identity_minus_projection_rank_type(c),
        })
    }

    fn register_zonotope_rankdef_width_eq(&mut self, c: &MatrixRankConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.zonotope_rankdef_width_eq");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Axiom {
            name,
            level_params: vec![],
            type_: nn_verify_matrix_rank_defs::build_zonotope_rankdef_width_eq_type(c),
        })
    }
}
