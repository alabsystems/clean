// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! C006 complexity helpers (T60-T61) — MASQUERADE DEMOTED.
//!
//! **Status:** Both T60 (`blockwise_crown_equiv`) and T61
//! (`blockwise_complexity`) are now `Declaration::Axiom` after Branch A
//! demasquerade sweeps (#3494 for T60, #3648 for T61). The two
//! placeholder carriers (`crown_cost`, `total_dim`) are `Declaration::Opaque`
//! entries with the same stored bodies (`fun _ _ => Nat.zero`) so they cannot
//! be δ-reduced into the old T61 `Nat.le_refl` masquerade.
//!
//! Part of #3375, #3646, #3648.
//!
//! See: designs/2026-04-17-publication-quality-gamma-crown-proofs.md,
//!      reports/triage/2026-04-20-3646-masquerade-grandfathered-triage.md.
//!
//! ---
//!
//! Block-wise CROWN complexity helpers (T60-T61 support, split from
//! `nn_verify_blockwise_crown_ext.rs` for file-size compliance).
//!
//! Contains:
//! - `NNVerify.Block.crown_cost` — block-wise cost function (Opaque,
//!   arg-discarding `fun _ _ => Nat.zero` placeholder carrier).
//! - `NNVerify.Block.total_dim` — total dimension accumulator (Opaque,
//!   arg-discarding `fun _ _ => Nat.zero` placeholder carrier).
//! - T60: `NNVerify.Block.blockwise_crown_equiv` — equivalence axiom
//!   (demoted in #3494).
//! - T61: `NNVerify.Block.blockwise_complexity` — cost bound axiom
//!   (demoted in #3648 per #3646 triage Site 4).
//!
//! Part of #3153.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::nn_verify_blockwise_crown::BlockwiseCrownConsts;
use crate::env::nn_verify_blockwise_crown_hyp;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Re-create a minimal constants struct for the complexity theorems.
/// (Mirrors the subset of `BlockExtConsts` needed here.)
struct BlockComplexityConsts {
    nat: Expr,
    #[cfg(test)]
    rat: Expr,
    #[cfg(test)]
    ib: Expr,
    #[cfg(test)]
    eq: Expr,
    #[cfg(test)]
    le_le: Expr,
    nat_mul: Expr,
    #[cfg(test)]
    nn_vec: Expr,
}

impl BlockComplexityConsts {
    fn new() -> Self {
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            #[cfg(test)]
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            #[cfg(test)]
            ib: Expr::const_(Name::from_string("NNVerify.IntervalBounds"), vec![]),
            #[cfg(test)]
            eq: Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            #[cfg(test)]
            le_le: Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
            nat_mul: Expr::const_(Name::from_string("Nat.mul"), vec![]),
            #[cfg(test)]
            nn_vec: Expr::const_(Name::from_string("NNVerify.NNVec"), vec![]),
        }
    }

    #[cfg(test)]
    fn ib_of(&self, d: &Expr) -> Expr {
        Expr::app(self.ib.clone(), d.clone())
    }

    #[cfg(test)]
    fn ib_eq(&self, d: &Expr, lhs: Expr, rhs: Expr) -> Expr {
        Expr::app(
            Expr::app(Expr::app(self.eq.clone(), self.ib_of(d)), lhs),
            rhs,
        )
    }

    fn nat_le(&self, lhs: Expr, rhs: Expr) -> Expr {
        let le_nat = Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]);
        let inst_le_nat = Expr::const_(Name::from_string("instLENat"), vec![]);
        Expr::app(
            Expr::app(
                Expr::app(Expr::app(le_nat, self.nat.clone()), inst_le_nat),
                lhs,
            ),
            rhs,
        )
    }

    fn mul_nat(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::app(Expr::app(self.nat_mul.clone(), a.clone()), b.clone())
    }

    #[cfg(test)]
    fn vec_of(&self, n: &Expr) -> Expr {
        Expr::app(self.nn_vec.clone(), n.clone())
    }

    fn add_nat(&self, a: &Expr, b: &Expr) -> Expr {
        let nat_add = Expr::const_(Name::from_string("Nat.add"), vec![]);
        Expr::app(Expr::app(nat_add, a.clone()), b.clone())
    }

    /// `Nat.rec.{1}` specialised to the non-dependent motive `fun _ : Nat => Nat`.
    /// Returns `@Nat.rec.{1} (fun _ : Nat => Nat) Nat.zero step k`, the standard
    /// fold over `k : Nat` accumulating in `Nat`.
    fn nat_rec_fold(&self, parent: &EnvDeclBuilder, k: Expr, step: Expr) -> Expr {
        let nat_rec = Expr::const_(
            Name::from_string("Nat.rec"),
            vec![Level::succ(Level::zero())],
        );
        // motive : Nat -> Type := fun _ => Nat
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(parent);
            let (x_id, _) = mb.fresh_local(self.nat.clone());
            let lam = mb.mk_lam(
                x_id,
                BinderInfo::Default,
                self.nat.clone(),
                self.nat.clone(),
            );
            mb.finish_child(lam)
        };
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        Expr::apps(nat_rec, [motive, nat_zero, step, k])
    }

    /// Step branch for `crown_cost`:
    /// `fun (m : Nat) (ih : Nat) => Nat.add ih (Nat.mul (bd m) (bd m))`.
    fn nat_rec_step_square(&self, parent: &EnvDeclBuilder, bd: &Expr) -> Expr {
        let mut sb = EnvDeclBuilder::child_of(parent);
        let (m_id, m) = sb.fresh_local(self.nat.clone());
        let (ih_id, ih) = sb.fresh_local(self.nat.clone());
        let bd_m = Expr::app(bd.clone(), m.clone());
        let body = self.add_nat(&ih, &self.mul_nat(&bd_m, &bd_m));
        let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, self.nat.clone(), body);
        let lam_m = sb.mk_lam(m_id, BinderInfo::Default, self.nat.clone(), lam_ih);
        sb.finish_child(lam_m)
    }

    /// Step branch for `total_dim`:
    /// `fun (m : Nat) (ih : Nat) => Nat.add ih (bd m)`.
    fn nat_rec_step_add(&self, parent: &EnvDeclBuilder, bd: &Expr) -> Expr {
        let mut sb = EnvDeclBuilder::child_of(parent);
        let (m_id, m) = sb.fresh_local(self.nat.clone());
        let (ih_id, ih) = sb.fresh_local(self.nat.clone());
        let bd_m = Expr::app(bd.clone(), m.clone());
        let body = self.add_nat(&ih, &bd_m);
        let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, self.nat.clone(), body);
        let lam_m = sb.mk_lam(m_id, BinderInfo::Default, self.nat.clone(), lam_ih);
        sb.finish_child(lam_m)
    }
}

impl Environment {
    /// `NNVerify.Block.crown_cost`:
    /// `(k : Nat) -> (block_dim : Nat -> Nat) -> Nat`
    ///
    /// Block-wise CROWN cost function: `Σ_{m<k} (block_dim m)²`.
    ///
    /// FAITHFUL CARRIER (#3648 Branch B): a reducible `Declaration::Definition`
    /// whose body is a real `Nat.rec` fold that *consumes* both `k` and
    /// `block_dim`:
    /// ```text
    /// crown_cost k bd := Nat.rec 0 (fun m ih => ih + bd m * bd m) k
    /// ```
    /// The step branch references the induction-hypothesis accumulator `ih`,
    /// the block index `m`, and the cost `bd m * bd m`, so this is NOT an
    /// argument-discarding placeholder. It is the genuine combinatorial cost,
    /// enabling the faithful T61 proof in
    /// `nn_verify_blockwise_crown_ext_t61_proof.rs`. See triage Site 4
    /// (reports/triage/2026-04-20-3646-masquerade-grandfathered-triage.md).
    #[cfg(any(test, feature = "math-overlays"))]
    pub(crate) fn register_blockwise_crown_cost_ext(&mut self) -> Result<(), EnvError> {
        let c = BlockComplexityConsts::new();
        let name = Name::from_string("NNVerify.Block.crown_cost");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let block_dim_ty = Expr::pi(BinderInfo::Default, c.nat.clone(), c.nat.clone());
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (k_id, _) = b.fresh_local(c.nat.clone());
            let (bd_id, _) = b.fresh_local(block_dim_ty.clone());
            let r = b.mk_pi(
                bd_id,
                BinderInfo::Default,
                block_dim_ty.clone(),
                c.nat.clone(),
            );
            let r = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };
        // Value: fun (k : Nat) (bd : Nat -> Nat) =>
        //   @Nat.rec.{1} (fun _ => Nat) Nat.zero
        //     (fun (m : Nat) (ih : Nat) => Nat.add ih (Nat.mul (bd m) (bd m))) k
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (k_id, k) = b.fresh_local(c.nat.clone());
            let (bd_id, bd) = b.fresh_local(block_dim_ty.clone());
            let step = c.nat_rec_step_square(&b, &bd);
            let rec_app = c.nat_rec_fold(&b, k, step);
            let r = b.mk_lam(bd_id, BinderInfo::Default, block_dim_ty.clone(), rec_app);
            let r = b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };
        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    /// `NNVerify.Block.total_dim : (k : Nat) -> (Nat -> Nat) -> Nat`
    ///
    /// Total dimension: `Σ_{m<k} block_dim m`.
    ///
    /// FAITHFUL CARRIER (#3648 Branch B): a reducible `Declaration::Definition`
    /// whose body is a real `Nat.rec` fold that *consumes* both `k` and
    /// `block_dim`:
    /// ```text
    /// total_dim k bd := Nat.rec 0 (fun m ih => ih + bd m) k
    /// ```
    /// The step branch references the accumulator `ih` and `bd m`, so this is
    /// NOT an argument-discarding placeholder.
    #[cfg(any(test, feature = "math-overlays"))]
    pub(crate) fn register_block_total_dim_ext(&mut self) -> Result<(), EnvError> {
        let c = BlockComplexityConsts::new();
        let name = Name::from_string("NNVerify.Block.total_dim");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let block_dim_ty = Expr::pi(BinderInfo::Default, c.nat.clone(), c.nat.clone());
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (k_id, _) = b.fresh_local(c.nat.clone());
            let (bd_id, _) = b.fresh_local(block_dim_ty.clone());
            let r = b.mk_pi(
                bd_id,
                BinderInfo::Default,
                block_dim_ty.clone(),
                c.nat.clone(),
            );
            let r = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };
        // Value: fun (k : Nat) (bd : Nat -> Nat) =>
        //   @Nat.rec.{1} (fun _ => Nat) Nat.zero
        //     (fun (m : Nat) (ih : Nat) => Nat.add ih (bd m)) k
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (k_id, k) = b.fresh_local(c.nat.clone());
            let (bd_id, bd) = b.fresh_local(block_dim_ty.clone());
            let step = c.nat_rec_step_add(&b, &bd);
            let rec_app = c.nat_rec_fold(&b, k, step);
            let r = b.mk_lam(bd_id, BinderInfo::Default, block_dim_ty.clone(), rec_app);
            let r = b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };
        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    /// T60: `NNVerify.Block.blockwise_crown_equiv` (axiom — MASQUERADE DEMOTED).
    ///
    /// Block-wise CROWN produces the same bounds as full CROWN (restating
    /// C006 with explicit cost annotations).
    ///
    /// SOUNDNESS (2026-04-19 demotion, #3494): previously registered as a
    /// `Declaration::Theorem` whose body delegated to
    /// `C006.blockwise_equals_monolithic`. With that theorem now demoted
    /// RETIRES the false unconditional T60 axiom `NNVerify.Block.blockwise_crown_equiv`.
    ///
    /// That axiom asserted `Block.compose k .. = Block.monolithic_crown k ..` for ALL
    /// `cb` — which is FALSE: at `k = succ`, `compose`'s step applies `cb i ih` while
    /// `monolithic_crown`'s step is `mono_step .. i ih = zero_ib`, so for a generic `cb`
    /// the two folds diverge (verified: nn_verify_blockwise_crown_*_value_builders.rs).
    ///
    /// Replaced by the honest, kernel-checked soundness theorem
    /// `NNVerify.Block.blockwise_crown_sound`: the SAME equality, gated on the per-block
    /// hypothesis `forall i X, cb i X = C006.mono_step .. i X` that closes the divergence.
    /// Its `type_`/`value` are reused VERBATIM from the already-kernel-checked C006
    /// builders (`build_blockwise_equals_monolithic_hyp_type`/`_proof`, a genuine
    /// `Nat.rec` induction whose succ branch consumes both the hypothesis and the IH).
    /// Empty domain-axiom closure (Constructive). NON-VACUOUS: `compose`/`monolithic_crown`
    /// are syntactically distinct reducible folds (post-#3638) and the proof instantiates
    /// the hypothesis at the real recursive value — not an `Eq.refl` masquerade.
    ///
    /// The fn name is kept so the init wiring (`nn_verify_blockwise_crown_ext.rs`) is
    /// untouched; it now registers the `_sound` Theorem, not the retired `_equiv` axiom.
    /// Retirement: kernel TCB domain axioms 6 -> 5 (toward the 3-axiom goal). See the
    /// triage docs/abstract-axiom-triage-2026-06-17.md and handoff-zero-faith-campaign.md.
    #[cfg(any(test, feature = "math-overlays"))]
    pub(crate) fn register_t60_blockwise_crown_equiv_ext(&mut self) -> Result<(), EnvError> {
        let c = BlockwiseCrownConsts::new();
        let name = Name::from_string("NNVerify.Block.blockwise_crown_sound");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: nn_verify_blockwise_crown_hyp::build_blockwise_equals_monolithic_hyp_type(&c),
            value: nn_verify_blockwise_crown_hyp::build_blockwise_equals_monolithic_hyp_proof(&c),
        })
    }

    /// T61: `NNVerify.Block.blockwise_complexity` — FAITHFUL CONSTRUCTIVE
    /// THEOREM (#3648 Branch B; was MASQUERADE-demoted Axiom).
    ///
    /// Block-wise CROWN cost is bounded by the square of the total dimension:
    /// ```text
    /// forall (k : Nat) (block_dim : Nat -> Nat),
    ///   crown_cost k block_dim <= total_dim k block_dim * total_dim k block_dim
    /// ```
    /// i.e. `Σ_{m<k} bd(m)² ≤ (Σ_{m<k} bd(m))²` — a true combinatorial fact.
    ///
    /// HISTORY: the carrier was previously an arg-discarding `fun _ _ =>
    /// Nat.zero` placeholder (Opaque), and the theorem a vacuous
    /// `Nat.le_refl 0` (#3648 Branch A demotion). Branch B replaces the
    /// carriers with FAITHFUL reducible `Nat.rec` folds (see
    /// `register_blockwise_crown_cost_ext` / `register_block_total_dim_ext`)
    /// that structurally consume `k`, `block_dim`, and the IH accumulator, and
    /// discharges T61 with a genuine `Nat.rec` induction (no `sorry`, no
    /// `add_decl_structural`). Proof term in
    /// `nn_verify_blockwise_crown_ext_t61_proof.rs`. The transitive axiom
    /// closure is `⊆` the constructive Nat-order / distributivity lemma set
    /// (`Nat.add_le_add`, `Nat.mul_le_mul`, `Nat.le_add_right`, `Nat.le_trans`,
    /// `Nat.left_distrib`, `Nat.right_distrib`, `Eq.subst`).
    #[cfg(any(test, feature = "math-overlays"))]
    pub(crate) fn register_t61_blockwise_complexity_ext(&mut self) -> Result<(), EnvError> {
        let c = BlockComplexityConsts::new();
        let name = Name::from_string("NNVerify.Block.blockwise_complexity");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        // Pull in the constructive Nat-order + distributivity lemma surface the
        // T61 proof depends on (all self-contained over inits already present).
        self.register_nat_arith_order_proofs()?;
        self.register_nat_mul_le_mul_left_proof()?; // also brings Nat.le_add_right
        self.register_nat_right_distrib_proof()?; // also brings Nat.left_distrib
        self.register_nat_left_distrib_proof()?;
        self.register_nat_add_comm_proof()?;

        let crown_cost = Expr::const_(Name::from_string("NNVerify.Block.crown_cost"), vec![]);
        let total_dim = Expr::const_(Name::from_string("NNVerify.Block.total_dim"), vec![]);
        let block_dim_ty = Expr::pi(BinderInfo::Default, c.nat.clone(), c.nat.clone());
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (k_id, k) = b.fresh_local(c.nat.clone());
            let (bd_id, block_dim) = b.fresh_local(block_dim_ty.clone());
            let cost = Expr::apps(crown_cost, [k.clone(), block_dim.clone()]);
            let n_total = Expr::apps(total_dim, [k, block_dim]);
            let n_squared = c.mul_nat(&n_total, &n_total);
            let concl = c.nat_le(cost, n_squared);
            let r = b.mk_pi(bd_id, BinderInfo::Default, block_dim_ty.clone(), concl);
            let r = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };
        let value = super::nn_verify_blockwise_crown_ext_t61_proof::build_t61_proof_value();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}
