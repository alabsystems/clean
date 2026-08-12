// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel-level zonotope type definitions for NN verification.
//!
//! Registers the zonotope abstract domain types and operations needed
//! to state and prove zonotope compression soundness (T10-T12):
//!
//! ## Types
//!
//! - `NNVerify.Zonotope n k : Type` — zonotope with dimension n, k error terms
//!   Defined as `{ center : NNVec n, generators : NNMat n k }`
//! - `NNVerify.Zonotope.center` — center vector accessor (projection 0)
//! - `NNVerify.Zonotope.generators` — generator matrix accessor (projection 1)
//!
//! ## Operations
//!
//! - `NNVerify.Zonotope.contains` — containment predicate:
//!   `contains z x := exists (eps : NNVec k), (forall i, -1 <= eps i <= 1) /\
//!     x = z.center + z.generators * eps`
//! - `NNVerify.Zonotope.compress` — compression operation (faithful reducible
//!   `Definition`, box-cover body): `compress n k k' (h : k' ≤ k) :
//!   Zonotope n k -> Zonotope n k'`
//! - `NNVerify.Zonotope.to_ibp` — conversion to interval bounds (axiom):
//!   `to_ibp : Zonotope n k -> IntervalBounds n`
//!
//! Part of #3152.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

/// Shared constants for zonotope type construction.
pub(super) struct ZonotopeConsts {
    pub(super) nat: Expr,
    pub(super) rat: Expr,
    pub(super) fin: Expr,
    pub(super) type0: Expr,
    pub(super) prop: Expr,
    pub(super) nn_vec: Expr,
    pub(super) nn_mat: Expr,
    pub(super) ib: Expr,
    pub(super) ib_contains: Expr,
    pub(super) le_le: Expr,
    pub(super) inst_le_rat: Expr,
    pub(super) and: Expr,
    pub(super) eq: Expr,
    #[cfg(test)]
    #[allow(dead_code)]
    // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
    pub(super) exists: Expr,
    /// `Exists` applied at universe `Sort (u+1)` — used for witness types in
    /// `Type 0` (like `NNVec k`).
    pub(super) exists_type0: Expr,
    pub(super) rat_neg: Expr,
    pub(super) rat_one: Expr,
    pub(super) nn_vec_add: Expr,
    pub(super) nn_mat_mul_vec: Expr,
    pub(super) zonotope: Expr,
    pub(super) zono_contains: Expr,
    pub(super) zono_compress: Expr,
    pub(super) zono_to_ibp: Expr,
}

impl ZonotopeConsts {
    pub(super) fn new() -> Self {
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            type0: Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))),
            prop: Expr::from_kind(ExprKind::Sort(Level::zero())),
            nn_vec: Expr::const_(Name::from_string("NNVerify.NNVec"), vec![]),
            nn_mat: Expr::const_(Name::from_string("NNVerify.NNMat"), vec![]),
            ib: Expr::const_(Name::from_string("NNVerify.IntervalBounds"), vec![]),
            ib_contains: Expr::const_(
                Name::from_string("NNVerify.IntervalBounds.contains"),
                vec![],
            ),
            le_le: Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
            inst_le_rat: Expr::const_(Name::from_string("instLERat"), vec![]),
            and: Expr::const_(Name::from_string("And"), vec![]),
            eq: Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            #[cfg(test)]
            exists: Expr::const_(Name::from_string("Exists"), vec![Level::zero()]),
            exists_type0: Expr::const_(
                Name::from_string("Exists"),
                vec![Level::succ(Level::zero())],
            ),
            rat_neg: Expr::const_(Name::from_string("Rat.neg"), vec![]),
            rat_one: Expr::const_(Name::from_string("Rat.one"), vec![]),
            nn_vec_add: Expr::const_(Name::from_string("NNVerify.NNVec.add"), vec![]),
            nn_mat_mul_vec: Expr::const_(Name::from_string("NNVerify.NNMat.mulVec"), vec![]),
            zonotope: Expr::const_(Name::from_string("NNVerify.Zonotope"), vec![]),
            zono_contains: Expr::const_(Name::from_string("NNVerify.Zonotope.contains"), vec![]),
            zono_compress: Expr::const_(Name::from_string("NNVerify.Zonotope.compress"), vec![]),
            zono_to_ibp: Expr::const_(Name::from_string("NNVerify.Zonotope.to_ibp"), vec![]),
        }
    }

    /// Build `LE.le @Rat instLERat lhs rhs`.
    pub(super) fn rat_le(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(self.le_le.clone(), self.rat.clone()),
                    self.inst_le_rat.clone(),
                ),
                lhs,
            ),
            rhs,
        )
    }

    /// Build `Eq @α lhs rhs`.
    pub(super) fn eq_of(&self, alpha: Expr, lhs: Expr, rhs: Expr) -> Expr {
        Expr::app(Expr::app(Expr::app(self.eq.clone(), alpha), lhs), rhs)
    }

    /// Build `NNVerify.NNVec n`.
    pub(super) fn vec_of(&self, n: Expr) -> Expr {
        Expr::app(self.nn_vec.clone(), n)
    }

    /// Build `NNVerify.NNMat m n`.
    pub(super) fn mat_of(&self, m: Expr, n: Expr) -> Expr {
        Expr::app(Expr::app(self.nn_mat.clone(), m), n)
    }

    /// Build `NNVerify.IntervalBounds d`.
    pub(super) fn ib_of(&self, d: Expr) -> Expr {
        Expr::app(self.ib.clone(), d)
    }

    /// Build `NNVerify.Zonotope n k`.
    pub(super) fn zono_of(&self, n: Expr, k: Expr) -> Expr {
        Expr::app(Expr::app(self.zonotope.clone(), n), k)
    }

    /// Build `NNVerify.Zonotope.contains n k z x`.
    pub(super) fn contains(&self, n: &Expr, k: &Expr, z: &Expr, x: &Expr) -> Expr {
        Expr::app(
            Expr::app(
                Expr::app(Expr::app(self.zono_contains.clone(), n.clone()), k.clone()),
                z.clone(),
            ),
            x.clone(),
        )
    }

    /// Build `NNVerify.IntervalBounds.contains n b x`.
    pub(super) fn ib_contains_app(&self, n: &Expr, b: &Expr, x: &Expr) -> Expr {
        Expr::app(
            Expr::app(Expr::app(self.ib_contains.clone(), n.clone()), b.clone()),
            x.clone(),
        )
    }
}

impl Environment {
    /// Initialize zonotope type definitions (T10-T12 infrastructure).
    ///
    /// Registers Zonotope type, containment predicate, compress, and to_ibp
    /// operations. Depends on `init_nn_verify_types()` for NNVec/NNMat/IB.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment
    /// ENSURES: On success, `self.nn_verify_zonotope_init == true`
    /// ENSURES: Idempotent
    pub(crate) fn init_nn_verify_zonotope(&mut self) -> Result<(), EnvError> {
        if self.nn_verify_zonotope_compress_init {
            return Ok(());
        }
        self.init_nn_verify_types()?;
        self.init_nn_verify_types_ops()?;
        self.init_rat_arith()?;
        self.init_rat_ord()?;
        // `Rat.le_refl` is required by `register_zonotope_to_ibp`'s reducible
        // body (zero-interval carrier — see its WHY comment). Pull it in via
        // the linear-order initializer before `to_ibp` type-checks. #3435.
        self.init_rat_linear_order()?;
        self.init_and()?;
        self.init_eq()?;
        // `Zonotope.contains` is a reducible `Declaration::Definition` whose
        // body uses `Exists` (see `register_zonotope_contains`). #3556.
        self.init_exists()?;
        // FAITHFUL `to_ibp` body + its `valid` proof require:
        //   - `Rat.abs` (faithful `max a (-a)` carrier) + `Rat.abs_nonneg`,
        //   - `Fin.sum` + `Fin.sum_nonneg`,
        //   - the Rat-quotient order lemmas `Rat.le_trans`,
        //     `Rat.add_le_add_left`, `Rat.le_add_of_nonneg_right`,
        //     `Rat.add_zero` (via `register_rat_le_trans_proof`),
        //   - `Rat.neg_le_neg`, and the `Rat.neg 0 ≡ 0` def-eq witness
        //     (`init_nn_verify_tier_a_rat_neg_zero_zero`) so `h_neg_le` retypes.
        self.init_rat_abs()?;
        self.init_fin_sum()?;
        self.register_rat_le_trans_proof()?;
        self.register_rat_neg_le_neg()?;
        self.init_nn_verify_tier_a_rat_neg_zero_zero()?;

        // FAITHFUL box-cover `compress` body (reducible `Declaration::Definition`)
        // needs, beyond `Fin.sum` + `Rat.abs` above:
        //   - `Decidable` + `Decidable.rec` (the `Fin k'` / `Fin k` index split),
        //   - `Nat.decLt` (decision procedure for the split discriminant),
        //   - `Fin.mk` / `Fin.val` (re-index the kept input column),
        //   - the constructive Nat bound bricks `Nat.pred_le`, `Nat.le_trans`,
        //     and `Nat.lt_of_lt_of_le` (build `val j < k` from `val j < pred k'`
        //     and the `k' ≤ k` hypothesis).
        self.init_decidable()?;
        self.init_nat_decidable_ord()?;
        self.register_fin_dec_eq_proof()?;
        self.register_nat_arith_order_proofs()?;
        self.register_nat_le_trans_proof()?;
        self.init_nat_trans_lt_le_lt()?;

        let c = ZonotopeConsts::new();
        self.register_zonotope_type(&c)?;
        self.register_zonotope_contains(&c)?;
        self.register_zonotope_compress(&c)?;
        self.register_zonotope_to_ibp(&c)?;

        self.nn_verify_zonotope_compress_init = true;
        Ok(())
    }

    /// `NNVerify.Zonotope (n : Nat) (k : Nat) : Type`
    ///
    /// A zonotope in R^n with k error terms, represented as:
    /// - center : NNVec n (center vector)
    /// - generators : NNMat n k (generator matrix)
    ///
    /// Registered as an inductive structure (like IntervalBounds).
    fn register_zonotope_type(&mut self, c: &ZonotopeConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("NNVerify.Zonotope"))
            .is_some()
        {
            return Ok(());
        }

        // Zonotope : Nat -> Nat -> Type
        let zono_type = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, _n) = b.fresh_local(c.nat.clone());
            let (k_id, _k) = b.fresh_local(c.nat.clone());
            let r = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), c.type0.clone());
            let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };

        // Zonotope.mk : {n k : Nat} -> NNVec n -> NNMat n k -> Zonotope n k
        let mk_type = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let (k_id, k) = b.fresh_local(c.nat.clone());
            let vec_n = c.vec_of(n.clone());
            let mat_nk = c.mat_of(n.clone(), k.clone());
            let zono_nk = c.zono_of(n.clone(), k.clone());
            let (center_id, _) = b.fresh_local(vec_n.clone());
            let (gen_id, _) = b.fresh_local(mat_nk.clone());
            let r = b.mk_pi(gen_id, BinderInfo::Default, mat_nk, zono_nk);
            let r = b.mk_pi(center_id, BinderInfo::Default, vec_n, r);
            let r = b.mk_pi(k_id, BinderInfo::Implicit, c.nat.clone(), r);
            let r = b.mk_pi(n_id, BinderInfo::Implicit, c.nat.clone(), r);
            b.finish(r)
        };

        use crate::inductive::{Constructor, InductiveDecl, InductiveType};
        self.add_inductive(InductiveDecl {
            level_params: vec![],
            num_params: 2,
            types: vec![InductiveType {
                name: Name::from_string("NNVerify.Zonotope"),
                type_: zono_type,
                constructors: vec![Constructor {
                    name: Name::from_string("NNVerify.Zonotope.mk"),
                    type_: mk_type,
                }],
            }],
        })?;
        self.register_structure_fields(
            Name::from_string("NNVerify.Zonotope"),
            vec![Name::from_string("center"), Name::from_string("generators")],
        )
    }

    /// `NNVerify.Zonotope.compress`:
    /// `(n k k' : Nat) -> (Nat.le k' k) -> Zonotope n k -> Zonotope n k'`
    ///
    /// Compression reduces the number of error terms from `k` to `k'`, requiring
    /// `k' ≤ k`. FAITHFUL BOX-COVER body (this change, retiring the historical
    /// body-less `Declaration::Axiom`): the first `k'-1` output generator columns
    /// are kept verbatim, and the LAST output column (index `k'-1`) absorbs every
    /// dropped input column (input indices `≥ k'-1`) as their per-row L1 magnitude
    /// `Σ_{l ≥ k'-1} |G_il|`. See `nn_verify_zonotope_compress_define::
    /// build_compress_value`.
    ///
    /// History:
    /// - #3152: registered as a bare `Declaration::Axiom` (body-less operation
    ///   signature) `(n k k' : Nat) → Zonotope n k → Zonotope n k'`. It sat in
    ///   the admitted-axiom census ONLY because it had no body — it claimed
    ///   nothing, but a body-less op is still trusted.
    /// - RETIREMENT (this change): refined the type with an explicit `k' ≤ k`
    ///   hypothesis and registered a genuine, total, reducible
    ///   `Declaration::Definition` box-cover body. A `Definition` is a
    ///   computation, not a claim, so it drops out of the trusted axiom set with
    ///   no Prop proof required for the retirement itself. The body genuinely
    ///   depends on `z.center` (kept unchanged) and `z.generators` (the absorbed
    ///   column folds the dropped data), so it is NOT an argument-discarding
    ///   masquerade. Soundness CONTENT (over-approximation) remains a separate,
    ///   honestly hypothesis-wrapped concern in `compress_sound` (T11) — the
    ///   retirement only removes the body-less op from the TCB.
    fn register_zonotope_compress(&mut self, c: &ZonotopeConsts) -> Result<(), EnvError> {
        // The legacy axiom (if present) must be replaced; only short-circuit
        // when the faithful Definition is already in place.
        if self
            .get_const(&Name::from_string("NNVerify.Zonotope.compress"))
            .is_some_and(|ci| ci.kind == crate::env::types::ConstantKind::Definition)
        {
            return Ok(());
        }
        let nat_le = Expr::const_(Name::from_string("Nat.le"), vec![]);
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let (k_id, k) = b.fresh_local(c.nat.clone());
            let (kp_id, kp) = b.fresh_local(c.nat.clone());
            let zono_nk = c.zono_of(n.clone(), k.clone());
            let zono_nkp = c.zono_of(n.clone(), kp.clone());
            // h_le : Nat.le k' k.
            let h_le_ty = Expr::apps(nat_le.clone(), [kp.clone(), k.clone()]);
            let (z_id, _) = b.fresh_local(zono_nk.clone());
            let (hle_id, _) = b.fresh_local(h_le_ty.clone());
            let r = b.mk_pi(z_id, BinderInfo::Default, zono_nk, zono_nkp);
            let r = b.mk_pi(hle_id, BinderInfo::Default, h_le_ty, r);
            let r = b.mk_pi(kp_id, BinderInfo::Default, c.nat.clone(), r);
            let r = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), r);
            let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };
        let value = super::nn_verify_zonotope_compress_define::build_compress_value(c);
        self.add_decl(Declaration::Definition {
            name: Name::from_string("NNVerify.Zonotope.compress"),
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    /// `NNVerify.Zonotope.to_ibp`:
    /// `(n k : Nat) -> Zonotope n k -> IntervalBounds n`
    ///
    /// Converts a zonotope to interval bounds via the mathematically FAITHFUL
    /// element-wise range
    /// ```text
    /// radius_i = Fin.sum k (fun j => Rat.abs (z.generators i j))
    /// lower_i  = Rat.sub (z.center i) radius_i
    /// upper_i  = Rat.add (z.center i) radius_i
    /// ```
    /// with a REAL `valid : ∀ i, lower_i ≤ upper_i` proof (radius ≥ 0; see
    /// `nn_verify_zonotope_to_ibp_faithful::build_to_ibp_value`).
    ///
    /// History:
    /// - #3435: Registered as reducible `Declaration::Definition` (FAKE
    ///   zero-interval carrier) so T20/T21 could close by `Eq.refl`.
    /// - #3509 / #3591 (2026-04-19/20): the FAKE body was first demoted to
    ///   `Declaration::Opaque` to close an M1 masquerade attack surface — any
    ///   `to_ibp z₁ = to_ibp z₂` or `lo (to_ibp z) i = Rat.zero` could close by
    ///   `Eq.refl` on the *argument-discarding* zero-interval carrier.
    /// - FAITHFUL ZONOTOPE→IBP (this change): the body is now the genuine
    ///   `[center - Σ|G|, center + Σ|G|]` range. Registered back as a REDUCIBLE
    ///   `Declaration::Definition` because `to_ibp_sound` (T12) must δ-unfold it
    ///   to reach `(to_ibp z).lower i = center i - radius i` etc. The #3591 M1
    ///   masquerade concern was *specific to the argument-discarding zero
    ///   body*: with a faithful body that genuinely depends on `z.center` /
    ///   `z.generators`, a false `to_ibp z₁ = to_ibp z₂` cannot close by
    ///   `Eq.refl` (the bodies differ structurally), and `lo (to_ibp z) i`
    ///   reduces to `center i - Σ|G_ij|`, never to `Rat.zero`. So re-opening
    ///   reducibility does not re-open the masquerade — it is closed
    ///   STRUCTURALLY by the faithful carrier, the same way the `Rat.abs`
    ///   demasquerade was (TCB-shrink Tier 1, `algebra_rat_abs_proof.rs`).
    fn register_zonotope_to_ibp(&mut self, c: &ZonotopeConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("NNVerify.Zonotope.to_ibp"))
            .is_some()
        {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let (k_id, k) = b.fresh_local(c.nat.clone());
            let zono_nk = c.zono_of(n.clone(), k.clone());
            let ib_n = c.ib_of(n.clone());
            let (z_id, _) = b.fresh_local(zono_nk.clone());
            let r = b.mk_pi(z_id, BinderInfo::Default, zono_nk, ib_n);
            let r = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), r);
            let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };
        let value = super::nn_verify_zonotope_to_ibp_faithful::build_to_ibp_value(c);
        self.add_decl(Declaration::Definition {
            name: Name::from_string("NNVerify.Zonotope.to_ibp"),
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }
}
