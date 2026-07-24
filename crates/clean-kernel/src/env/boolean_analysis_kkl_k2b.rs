// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL pre-build — K2b layer (run 2): the threshold tail bound proper.
//!
//! Two lemmas:
//!
//! ```text
//! Rat.threshold_term_le :                                      -- per-S core
//!   ∀ (k size w : Rat) (bit : Bool),
//!     0 ≤ w → 0 ≤ size → (bit = Bool.true → k ≤ size)
//!       → Rat.mul k (Rat.mul (ind bit) w) ≤ Rat.mul size w
//!
//! BoolAnalysis.subsetSum_threshold_le :                        -- lifted K2b
//!   ∀ (n : Nat) (k : Rat) (w : HCPoint n → Rat) (b : HCPoint n → Bool),
//!     (∀ S, 0 ≤ w S) → (∀ S, 0 ≤ setSize n S)
//!       → (∀ S, b S = Bool.true → k ≤ setSize n S)
//!       → subsetSum n (fun S => k · (ind (b S) · w S))
//!           ≤ subsetSum n (fun S => setSize n S · w S)
//! ```
//!
//! The lifted form is the threshold tail bound `k·Σ_{bit}f̂² ≤ Σ size·f̂²` with
//! the per-S threshold indicator `b` and its correctness supplied abstractly
//! (general `w`, no `f̂²` specialization), exactly the shape the KKL assembly
//! consumes — it instantiates `b S := Nat.ble k (popcount S)` and discharges
//! the `b S = true → k ≤ setSize` hypothesis from the Nat-popcount bridge.
//! (The `k·subsetSum(g)` form folds the scalar `k` into the integrand here, so
//! no `subsetSum_smul` is needed at this layer.)
//!
//! ## Proofs (constructive, empty domain-axiom closure)
//!
//! **Per-S core** — `Bool.rec` on `bit` (the `chi_flip`/`pm_not` precedent):
//! - `bit = false`: `ind false` δ-reduces to `Rat.zero`. Rewrite
//!   `k·(0·w) = k·0 = 0` (`Rat.zero_mul`, `Rat.mul_zero` via `Eq.subst`), then
//!   `0 ≤ size·w` from `Rat.mul_nonneg size w h_size h_w`.
//! - `bit = true`: `ind true` δ-reduces to `Rat.one`. Rewrite `1·w = w`
//!   (`Rat.one_mul`), then `k·w ≤ size·w` from `k ≤ size`
//!   (`hyp Eq.refl`) and `0 ≤ w` via `Rat.mul_le_mul_of_nonneg_right`.
//!
//! **Lift** — the per-S core applied pointwise at `(k, setSize n S, w S, b S)`
//! is the hypothesis `subsetSum_le_of_pointwise` consumes; the integrands
//! `fun S => k·(ind (b S)·w S)` and `fun S => setSize n S · w S` match the
//! conclusion sides definitionally.
//!
//! Every dependency (`Rat.zero_mul`, `Rat.mul_zero`, `Rat.one_mul`,
//! `Rat.mul_nonneg`, `Rat.mul_le_mul_of_nonneg_right`, `BoolAnalysis.ind`,
//! `BoolAnalysis.setSize`, `subsetSum_le_of_pointwise`) is `Constructive` with
//! empty closure, so both lemmas are too.

use super::boolean_analysis_order_toolkit::OrderConsts;
use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared atoms for the K2b construction.
struct K2bConsts {
    order: OrderConsts,
    bool_: Expr,
    bool_true: Expr,
    bool_false: Expr,
    ind: Expr,
    rat_mul: Expr,
    u1: Level,
}

impl K2bConsts {
    fn new() -> Self {
        Self {
            order: OrderConsts::new(),
            bool_: Expr::const_(Name::from_string("Bool"), vec![]),
            bool_true: Expr::const_(Name::from_string("Bool.true"), vec![]),
            bool_false: Expr::const_(Name::from_string("Bool.false"), vec![]),
            ind: Expr::const_(Name::from_string("BoolAnalysis.ind"), vec![]),
            rat_mul: Expr::const_(Name::from_string("Rat.mul"), vec![]),
            u1: Level::succ(Level::zero()),
        }
    }

    fn rat(&self) -> Expr {
        self.order.rat.clone()
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn rat_le(&self, a: Expr, b: Expr) -> Expr {
        self.order.rat_le(a, b)
    }
    fn ind_of(&self, bit: Expr) -> Expr {
        Expr::app(self.ind.clone(), bit)
    }
    /// `bit = Bool.true` (the threshold-correctness antecedent).
    fn bit_eq_true(&self, bit: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![self.u1.clone()]),
            [self.bool_.clone(), bit, self.bool_true.clone()],
        )
    }
    fn subst(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h_motive_a: Expr) -> Expr {
        self.order.subst(motive, a, b, h_eq, h_motive_a)
    }
}

/// `Rat.mul_le_mul_of_nonneg_right a b c h_bc h_a : (b·a) ≤ (c·a)`.
/// Signature `∀ a b c, b ≤ c → 0 ≤ a → b·a ≤ c·a`.
fn mul_le_right(a: Expr, b: Expr, cc: Expr, h_bc: Expr, h_a: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Rat.mul_le_mul_of_nonneg_right"), vec![]),
        [a, b, cc, h_bc, h_a],
    )
}

/// `Rat.mul_nonneg a b ha hb : 0 ≤ a·b`.
fn mul_nonneg(a: Expr, b: Expr, ha: Expr, hb: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Rat.mul_nonneg"), vec![]),
        [a, b, ha, hb],
    )
}

impl Environment {
    /// Register the K2b threshold layer: `Rat.threshold_term_le` (per-S core)
    /// and `BoolAnalysis.subsetSum_threshold_le` (the lifted tail bound).
    /// Idempotent.
    pub fn init_boolean_analysis_kkl_k2b(&mut self) -> Result<(), EnvError> {
        self.register_rat_threshold_term_le()?;
        self.register_subset_sum_threshold_le()?;
        Ok(())
    }

    /// `Rat.threshold_term_le : ∀ (k size w : Rat) (bit : Bool),
    ///   0 ≤ w → 0 ≤ size → (bit = true → k ≤ size)
    ///     → k · (ind bit · w) ≤ size · w`.
    ///
    /// The per-S threshold term bound. Kernel-checked, constructive, empty
    /// closure.
    pub fn register_rat_threshold_term_le(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.threshold_term_le");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_bool()?;
        self.init_boolean_analysis()?; // ind
        self.init_boolean_analysis_order_toolkit()?; // mul_nonneg, mul_le_mul_of_nonneg_right
        self.init_rat_field_inst()?; // one_mul, zero_mul, mul_zero

        // Re-check the guard: `init_boolean_analysis` above is the always-on KKL
        // aggregate, which transitively re-enters this registrar (the low-band
        // spectral-extraction rung pulls `Rat.threshold_term_le`); if it already
        // registered the theorem, short-circuit instead of double-`add_decl`.
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let c = K2bConsts::new();
        let ty = threshold_term_type(&c);
        let value = build_threshold_term_proof(&c);
        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `BoolAnalysis.subsetSum_threshold_le :
    ///   ∀ (n) (k) (w : HCPoint n → Rat) (b : HCPoint n → Bool),
    ///     (∀ S, 0 ≤ w S) → (∀ S, 0 ≤ setSize n S)
    ///       → (∀ S, b S = true → k ≤ setSize n S)
    ///       → subsetSum n (fun S => k · (ind (b S) · w S))
    ///           ≤ subsetSum n (fun S => setSize n S · w S)`.
    ///
    /// The lifted threshold tail bound. Kernel-checked, constructive, empty
    /// closure.
    pub fn register_subset_sum_threshold_le(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.subsetSum_threshold_le");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_rat_threshold_term_le()?;
        self.register_subset_sum_le_of_pointwise()?;
        self.register_set_size()?;

        let c = K2bConsts::new();
        let ty = subset_sum_threshold_type(&c);
        let value = build_subset_sum_threshold_proof(&c);
        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

// ── Per-S core: Rat.threshold_term_le ──────────────────────────────────────

/// Type `∀ (k size w : Rat) (bit : Bool), 0≤w → 0≤size → (bit=true → k≤size)
///   → k·(ind bit · w) ≤ size·w`.
fn threshold_term_type(c: &K2bConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.rat());
    let (size_id, size) = b.fresh_local(c.rat());
    let (w_id, w) = b.fresh_local(c.rat());
    let (bit_id, bit) = b.fresh_local(c.bool_.clone());
    let h_w_ty = c.rat_le(c.order.rat_zero.clone(), w.clone());
    let h_size_ty = c.rat_le(c.order.rat_zero.clone(), size.clone());
    let h_thr_ty = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let ante = c.bit_eq_true(bit.clone());
        let (a_id, _) = ch.fresh_local(ante.clone());
        let cons = c.rat_le(k.clone(), size.clone());
        ch.finish_child(ch.mk_pi(a_id, BinderInfo::Default, ante, cons))
    };
    let concl = c.rat_le(
        c.mul(k.clone(), c.mul(c.ind_of(bit.clone()), w.clone())),
        c.mul(size.clone(), w.clone()),
    );
    let (hw_id, _) = b.fresh_local(h_w_ty.clone());
    let (hsize_id, _) = b.fresh_local(h_size_ty.clone());
    let (hthr_id, _) = b.fresh_local(h_thr_ty.clone());
    let e = b.mk_pi(hthr_id, BinderInfo::Default, h_thr_ty, concl);
    let e = b.mk_pi(hsize_id, BinderInfo::Default, h_size_ty, e);
    let e = b.mk_pi(hw_id, BinderInfo::Default, h_w_ty, e);
    let e = b.mk_pi(bit_id, BinderInfo::Default, c.bool_.clone(), e);
    let e = b.mk_pi(w_id, BinderInfo::Default, c.rat(), e);
    let e = b.mk_pi(size_id, BinderInfo::Default, c.rat(), e);
    let e = b.mk_pi(k_id, BinderInfo::Default, c.rat(), e);
    b.finish(e)
}

/// Build the proof term for `Rat.threshold_term_le` (Bool.rec on `bit`).
fn build_threshold_term_proof(c: &K2bConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.rat());
    let (size_id, size) = b.fresh_local(c.rat());
    let (w_id, w) = b.fresh_local(c.rat());
    let (bit_id, bit) = b.fresh_local(c.bool_.clone());
    let h_w_ty = c.rat_le(c.order.rat_zero.clone(), w.clone());
    let h_size_ty = c.rat_le(c.order.rat_zero.clone(), size.clone());
    let h_thr_ty = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let ante = c.bit_eq_true(bit.clone());
        let (a_id, _) = ch.fresh_local(ante.clone());
        let cons = c.rat_le(k.clone(), size.clone());
        ch.finish_child(ch.mk_pi(a_id, BinderInfo::Default, ante, cons))
    };
    let (hw_id, h_w) = b.fresh_local(h_w_ty.clone());
    let (hsize_id, h_size) = b.fresh_local(h_size_ty.clone());
    let (hthr_id, h_thr) = b.fresh_local(h_thr_ty.clone());

    // Goal closure G(bit) := k·(ind bit · w) ≤ size·w.
    let goal_of = |bb: &Expr| {
        c.rat_le(
            c.mul(k.clone(), c.mul(c.ind_of(bb.clone()), w.clone())),
            c.mul(size.clone(), w.clone()),
        )
    };
    // Per-bit threshold-hypothesis type: (b' = true → k ≤ size).
    let thr_ty_of = |bb: &Expr, parent: &EnvDeclBuilder| -> Expr {
        let mut ch = EnvDeclBuilder::child_of(parent);
        let ante = c.bit_eq_true(bb.clone());
        let (a_id, _) = ch.fresh_local(ante.clone());
        let cons = c.rat_le(k.clone(), size.clone());
        ch.finish_child(ch.mk_pi(a_id, BinderInfo::Default, ante, cons))
    };

    // motive : fun (b' : Bool) => (b' = true → k ≤ size) → k·(ind b' · w) ≤ size·w
    // (the threshold hypothesis is carried INTO the motive so the true-branch
    // can apply it at `b' := Bool.true`).
    let motive = {
        let mut m = EnvDeclBuilder::child_of(&b);
        let (bp_id, bp) = m.fresh_local(c.bool_.clone());
        let thr = thr_ty_of(&bp, &m);
        let (h_id, _) = m.fresh_local(thr.clone());
        let imp = m.mk_pi(h_id, BinderInfo::Default, thr, goal_of(&bp));
        m.finish_child(m.mk_lam(bp_id, BinderInfo::Default, c.bool_.clone(), imp))
    };

    let size_w = c.mul(size.clone(), w.clone()); // size·w

    // ── false case: fun (_ : false=true→k≤size) => k·(ind false · w) ≤ size·w
    // ind false δ-reduces to Rat.zero. Build 0 ≤ size·w then transport along
    // 0 = k·(0·w) (chain: 0·w=0 [zero_mul], k·0=0 [mul_zero], symm/congr).
    let false_proof = {
        // h_nn : 0 ≤ size·w  [mul_nonneg size w h_size h_w]
        let h_nn = mul_nonneg(size.clone(), w.clone(), h_size.clone(), h_w.clone());
        // We must produce: k·(ind false · w) ≤ size·w. Since `ind false`
        // δ-reduces to Rat.zero, the goal is defeq to `k·(0·w) ≤ size·w`.
        // Rewrite the LHS `k·(0·w)` to `0`:
        //   e0 : 0·w = 0      [Rat.zero_mul w]
        //   e1 : k·(0·w) = k·0   via congrArg (k · ·) e0    (Eq.subst)
        //   e2 : k·0 = 0      [Rat.mul_zero k]
        //   so k·(0·w) = 0 (trans), and (symm) 0 = k·(0·w); subst h_nn.
        let zero = c.order.rat_zero.clone();
        let zero_mul_w = c.mul(zero.clone(), w.clone()); // 0·w
        let k_zero_mul_w = c.mul(k.clone(), zero_mul_w.clone()); // k·(0·w)
        let k_zero = c.mul(k.clone(), zero.clone()); // k·0

        // e0 : 0·w = 0
        let e0 = Expr::app(
            Expr::const_(Name::from_string("Rat.zero_mul"), vec![]),
            w.clone(),
        );
        // e1 : k·(0·w) = k·0   via Eq.subst, motive t => (k·(0·w)) = (k·t)
        let motive1 = {
            let mut m = EnvDeclBuilder::child_of(&b);
            let (t_id, t) = m.fresh_local(c.rat());
            let body = c.order.rat_eq(k_zero_mul_w.clone(), c.mul(k.clone(), t));
            m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.rat(), body))
        };
        // base for subst: refl (k·(0·w)) = (k·(0·w))  at t := 0·w
        let refl_kzw = Expr::apps(
            Expr::const_(Name::from_string("Eq.refl"), vec![c.u1.clone()]),
            [c.rat(), k_zero_mul_w.clone()],
        );
        let e1 = c.subst(motive1, zero_mul_w.clone(), zero.clone(), e0, refl_kzw);
        // e2 : k·0 = 0   [Rat.mul_zero k]
        let e2 = Expr::app(
            Expr::const_(Name::from_string("Rat.mul_zero"), vec![]),
            k.clone(),
        );
        // e_lhs0 : k·(0·w) = 0   [trans e1 e2]
        let e_lhs0 = c
            .order
            .trans(k_zero_mul_w.clone(), k_zero, zero.clone(), e1, e2);
        // symm : 0 = k·(0·w)
        let e_sym = c.order.symm(k_zero_mul_w.clone(), zero.clone(), e_lhs0);
        // subst h_nn (0 ≤ size·w) along 0 = k·(0·w):
        //   motive t => t ≤ size·w
        let motive2 = {
            let mut m = EnvDeclBuilder::child_of(&b);
            let (t_id, t) = m.fresh_local(c.rat());
            let body = c.rat_le(t, size_w.clone());
            m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.rat(), body))
        };
        c.subst(motive2, zero, k_zero_mul_w, e_sym, h_nn)
    };
    // Wrap: false_case = fun (_ : false=true→k≤size) => false_proof.
    let false_case = {
        let mut m = EnvDeclBuilder::child_of(&b);
        let thr_false = thr_ty_of(&c.bool_false, &m);
        let (h_id, _) = m.fresh_local(thr_false.clone());
        m.finish_child(m.mk_lam(h_id, BinderInfo::Default, thr_false, false_proof))
    };

    // ── true case: fun (ht : true=true→k≤size) => k·(ind true · w) ≤ size·w
    // ind true δ-reduces to Rat.one. Rewrite 1·w=w, reduce k·(1·w)=k·w,
    // then mul_le_mul_of_nonneg_right with k≤size (= ht (refl true)) + 0≤w.
    let true_case = {
        let mut m = EnvDeclBuilder::child_of(&b);
        let thr_true = thr_ty_of(&c.bool_true, &m);
        let (ht_id, ht) = m.fresh_local(thr_true.clone());

        let one = c.order.rat_one.clone();
        let one_w = c.mul(one.clone(), w.clone()); // 1·w

        // hk : k ≤ size   [ht (Eq.refl true)]
        let refl_true = Expr::apps(
            Expr::const_(Name::from_string("Eq.refl"), vec![c.u1.clone()]),
            [c.bool_.clone(), c.bool_true.clone()],
        );
        let hk = Expr::app(ht, refl_true);
        // base : k·w ≤ size·w   [mul_le_mul_of_nonneg_right w k size hk h_w]
        let base = mul_le_right(w.clone(), k.clone(), size.clone(), hk, h_w.clone());
        // Transport LHS k·w -> k·(1·w) via 1·w=w (Rat.one_mul w), reversed.
        let e0 = Expr::app(
            Expr::const_(Name::from_string("Rat.one_mul"), vec![]),
            w.clone(),
        );
        let e_sym = c.order.symm(one_w.clone(), w.clone(), e0); // w = 1·w
        let motive1 = {
            let mut mm = EnvDeclBuilder::child_of(&m);
            let (t_id, t) = mm.fresh_local(c.rat());
            let body = c.rat_le(c.mul(k.clone(), t), size_w.clone());
            mm.finish_child(mm.mk_lam(t_id, BinderInfo::Default, c.rat(), body))
        };
        // subst: from (k·w ≤ size·w) [motive at t=w] to (k·(1·w) ≤ size·w).
        let proof = c.subst(motive1, w.clone(), one_w, e_sym, base);
        m.finish_child(m.mk_lam(ht_id, BinderInfo::Default, thr_true, proof))
    };

    // Bool.rec motive false_case true_case bit
    //   : (bit = true → k ≤ size) → goal_of bit
    // then apply to h_thr to get goal_of bit.
    let bool_rec = Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]);
    let rec = Expr::apps(bool_rec, [motive, false_case, true_case, bit.clone()]);
    let body = Expr::app(rec, h_thr);

    let e = b.mk_lam(hthr_id, BinderInfo::Default, h_thr_ty, body);
    let e = b.mk_lam(hsize_id, BinderInfo::Default, h_size_ty, e);
    let e = b.mk_lam(hw_id, BinderInfo::Default, h_w_ty, e);
    let e = b.mk_lam(bit_id, BinderInfo::Default, c.bool_.clone(), e);
    let e = b.mk_lam(w_id, BinderInfo::Default, c.rat(), e);
    let e = b.mk_lam(size_id, BinderInfo::Default, c.rat(), e);
    let e = b.mk_lam(k_id, BinderInfo::Default, c.rat(), e);
    b.finish(e)
}

// ── Lifted K2b: BoolAnalysis.subsetSum_threshold_le ────────────────────────

/// Shared HCPoint/subsetSum atoms for the lift.
struct LiftAtoms {
    nat: Expr,
    rat: Expr,
    bool_: Expr,
    bool_true: Expr,
    ind: Expr,
    set_size: Expr,
    subset_sum: Expr,
    hcpoint: Expr,
    rat_mul: Expr,
    le_le: Expr,
    inst_le_rat: Expr,
    u1: Level,
}

impl LiftAtoms {
    fn new() -> Self {
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            bool_: Expr::const_(Name::from_string("Bool"), vec![]),
            bool_true: Expr::const_(Name::from_string("Bool.true"), vec![]),
            ind: Expr::const_(Name::from_string("BoolAnalysis.ind"), vec![]),
            set_size: Expr::const_(Name::from_string("BoolAnalysis.setSize"), vec![]),
            subset_sum: Expr::const_(Name::from_string("BoolAnalysis.subsetSum"), vec![]),
            hcpoint: Expr::const_(Name::from_string("BoolAnalysis.HCPoint"), vec![]),
            rat_mul: Expr::const_(Name::from_string("Rat.mul"), vec![]),
            le_le: Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
            inst_le_rat: Expr::const_(Name::from_string("instLERat"), vec![]),
            u1: Level::succ(Level::zero()),
        }
    }
    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    fn hcpoint_to_rat(&self, n: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.hcpoint_of(n), self.rat.clone())
    }
    fn hcpoint_to_bool(&self, n: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.hcpoint_of(n), self.bool_.clone())
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn rat_le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(
            self.le_le.clone(),
            [self.rat.clone(), self.inst_le_rat.clone(), a, b],
        )
    }
    fn rat_zero(&self) -> Expr {
        Expr::const_(Name::from_string("Rat.zero"), vec![])
    }
    fn set_size_of(&self, n: &Expr, s: &Expr) -> Expr {
        Expr::apps(self.set_size.clone(), [n.clone(), s.clone()])
    }
    fn ind_of(&self, bit: Expr) -> Expr {
        Expr::app(self.ind.clone(), bit)
    }
    fn subset_sum_of(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(self.subset_sum.clone(), [n.clone(), g])
    }
    /// `fun (S : HCPoint n) => k · (ind (b S) · w S)` — the LHS integrand.
    fn lhs_fn(&self, parent: &EnvDeclBuilder, n: &Expr, k: &Expr, w: &Expr, bf: &Expr) -> Expr {
        let mut ch = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = ch.fresh_local(hcp.clone());
        let bit = Expr::app(bf.clone(), s.clone());
        let body = self.mul(
            k.clone(),
            self.mul(self.ind_of(bit), Expr::app(w.clone(), s)),
        );
        ch.finish_child(ch.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }
    /// `fun (S : HCPoint n) => setSize n S · w S` — the RHS integrand.
    fn rhs_fn(&self, parent: &EnvDeclBuilder, n: &Expr, w: &Expr) -> Expr {
        let mut ch = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = ch.fresh_local(hcp.clone());
        let body = self.mul(self.set_size_of(n, &s), Expr::app(w.clone(), s));
        ch.finish_child(ch.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }
    /// `∀ S, P S` over `HCPoint n`.
    fn forall_s(&self, parent: &EnvDeclBuilder, n: &Expr, body_of: impl Fn(&Expr) -> Expr) -> Expr {
        let mut ch = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = ch.fresh_local(hcp.clone());
        let body = body_of(&s);
        ch.finish_child(ch.mk_pi(s_id, BinderInfo::Default, hcp, body))
    }
}

/// Type of `BoolAnalysis.subsetSum_threshold_le`.
fn subset_sum_threshold_type(_c: &K2bConsts) -> Expr {
    let a = LiftAtoms::new();
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(a.nat.clone());
    let (k_id, k) = b.fresh_local(a.rat.clone());
    let w_ty = a.hcpoint_to_rat(&n);
    let (w_id, w) = b.fresh_local(w_ty.clone());
    let bf_ty = a.hcpoint_to_bool(&n);
    let (bf_id, bf) = b.fresh_local(bf_ty.clone());

    // hyp1 : ∀ S, 0 ≤ w S
    let hyp1 = a.forall_s(&b, &n, |s| {
        a.rat_le(a.rat_zero(), Expr::app(w.clone(), s.clone()))
    });
    // hyp2 : ∀ S, 0 ≤ setSize n S
    let hyp2 = a.forall_s(&b, &n, |s| a.rat_le(a.rat_zero(), a.set_size_of(&n, s)));
    // hyp3 : ∀ S, b S = true → k ≤ setSize n S
    let hyp3 = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let hcp = a.hcpoint_of(&n);
        let (s_id, s) = ch.fresh_local(hcp.clone());
        let ante = Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![a.u1.clone()]),
            [
                a.bool_.clone(),
                Expr::app(bf.clone(), s.clone()),
                a.bool_true.clone(),
            ],
        );
        let cons = a.rat_le(k.clone(), a.set_size_of(&n, &s));
        let (an_id, _) = ch.fresh_local(ante.clone());
        let imp = ch.mk_pi(an_id, BinderInfo::Default, ante, cons);
        ch.finish_child(ch.mk_pi(s_id, BinderInfo::Default, hcp, imp))
    };

    let lhs = a.subset_sum_of(&n, a.lhs_fn(&b, &n, &k, &w, &bf));
    let rhs = a.subset_sum_of(&n, a.rhs_fn(&b, &n, &w));
    let concl = a.rat_le(lhs, rhs);

    let (h1_id, _) = b.fresh_local(hyp1.clone());
    let (h2_id, _) = b.fresh_local(hyp2.clone());
    let (h3_id, _) = b.fresh_local(hyp3.clone());
    let e = b.mk_pi(h3_id, BinderInfo::Default, hyp3, concl);
    let e = b.mk_pi(h2_id, BinderInfo::Default, hyp2, e);
    let e = b.mk_pi(h1_id, BinderInfo::Default, hyp1, e);
    let e = b.mk_pi(bf_id, BinderInfo::Default, bf_ty, e);
    let e = b.mk_pi(w_id, BinderInfo::Default, w_ty, e);
    let e = b.mk_pi(k_id, BinderInfo::Default, a.rat.clone(), e);
    let e = b.mk_pi(n_id, BinderInfo::Default, a.nat.clone(), e);
    b.finish(e)
}

/// Build the proof of `BoolAnalysis.subsetSum_threshold_le`.
///
/// `subsetSum_le_of_pointwise n (lhs_fn) (rhs_fn) pointwise`, where `pointwise`
/// is `fun S => Rat.threshold_term_le k (setSize n S) (w S) (b S)
///   (hyp1 S) (hyp2 S) (hyp3 S)`.
fn build_subset_sum_threshold_proof(_c: &K2bConsts) -> Expr {
    let a = LiftAtoms::new();
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(a.nat.clone());
    let (k_id, k) = b.fresh_local(a.rat.clone());
    let w_ty = a.hcpoint_to_rat(&n);
    let (w_id, w) = b.fresh_local(w_ty.clone());
    let bf_ty = a.hcpoint_to_bool(&n);
    let (bf_id, bf) = b.fresh_local(bf_ty.clone());

    let hyp1 = a.forall_s(&b, &n, |s| {
        a.rat_le(a.rat_zero(), Expr::app(w.clone(), s.clone()))
    });
    let hyp2 = a.forall_s(&b, &n, |s| a.rat_le(a.rat_zero(), a.set_size_of(&n, s)));
    let hyp3 = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let hcp = a.hcpoint_of(&n);
        let (s_id, s) = ch.fresh_local(hcp.clone());
        let ante = Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![a.u1.clone()]),
            [
                a.bool_.clone(),
                Expr::app(bf.clone(), s.clone()),
                a.bool_true.clone(),
            ],
        );
        let cons = a.rat_le(k.clone(), a.set_size_of(&n, &s));
        let (an_id, _) = ch.fresh_local(ante.clone());
        let imp = ch.mk_pi(an_id, BinderInfo::Default, ante, cons);
        ch.finish_child(ch.mk_pi(s_id, BinderInfo::Default, hcp, imp))
    };
    let (h1_id, h1) = b.fresh_local(hyp1.clone());
    let (h2_id, h2) = b.fresh_local(hyp2.clone());
    let (h3_id, h3) = b.fresh_local(hyp3.clone());

    let lhs_fn = a.lhs_fn(&b, &n, &k, &w, &bf);
    let rhs_fn = a.rhs_fn(&b, &n, &w);

    // pointwise : fun (S : HCPoint n) => Rat.threshold_term_le k (setSize n S)
    //   (w S) (b S) (h1 S) (h2 S) (h3 S) : (lhs_fn S) ≤ (rhs_fn S)
    let pointwise = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let hcp = a.hcpoint_of(&n);
        let (s_id, s) = ch.fresh_local(hcp.clone());
        let size_s = a.set_size_of(&n, &s);
        let w_s = Expr::app(w.clone(), s.clone());
        let bit_s = Expr::app(bf.clone(), s.clone());
        let term = Expr::apps(
            Expr::const_(Name::from_string("Rat.threshold_term_le"), vec![]),
            [
                k.clone(),
                size_s,
                w_s,
                bit_s,
                Expr::app(h1.clone(), s.clone()),
                Expr::app(h2.clone(), s.clone()),
                Expr::app(h3.clone(), s.clone()),
            ],
        );
        ch.finish_child(ch.mk_lam(s_id, BinderInfo::Default, hcp, term))
    };

    // subsetSum_le_of_pointwise n lhs_fn rhs_fn pointwise
    let body = Expr::apps(
        Expr::const_(
            Name::from_string("BoolAnalysis.subsetSum_le_of_pointwise"),
            vec![],
        ),
        [n.clone(), lhs_fn, rhs_fn, pointwise],
    );

    let e = b.mk_lam(h3_id, BinderInfo::Default, hyp3, body);
    let e = b.mk_lam(h2_id, BinderInfo::Default, hyp2, e);
    let e = b.mk_lam(h1_id, BinderInfo::Default, hyp1, e);
    let e = b.mk_lam(bf_id, BinderInfo::Default, bf_ty, e);
    let e = b.mk_lam(w_id, BinderInfo::Default, w_ty, e);
    let e = b.mk_lam(k_id, BinderInfo::Default, a.rat.clone(), e);
    let e = b.mk_lam(n_id, BinderInfo::Default, a.nat.clone(), e);
    b.finish(e)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    const LEMMAS: &[&str] = &[
        "Rat.threshold_term_le",
        "BoolAnalysis.subsetSum_threshold_le",
    ];

    fn env() -> Environment {
        let mut env = Environment::new();
        env.init_boolean_analysis().expect("init_boolean_analysis");
        env.init_boolean_analysis_kkl_k2b()
            .expect("init_boolean_analysis_kkl_k2b");
        env
    }

    #[test]
    fn test_k2b_all_constructive_theorems() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in LEMMAS {
            let nm = Name::from_string(name);
            let info = env
                .get_const(&nm)
                .unwrap_or_else(|| panic!("{name} registered"));
            assert_eq!(info.kind, ConstantKind::Theorem, "{name} must be Theorem");
            let value = info.value.clone().expect("proof present");
            tc.check_type(&value, &info.type_)
                .unwrap_or_else(|e| panic!("{name} must kernel-check: {e:?}"));
            assert_eq!(
                env.proof_quality(&nm),
                Some(ProofQuality::Constructive),
                "{name} must be Constructive"
            );
            assert!(
                env.axiom_deps(&nm).expect("deps").is_empty(),
                "{name} closure must be empty"
            );
        }
    }

    #[test]
    fn test_k2b_idempotent() {
        let mut env = Environment::new();
        env.init_boolean_analysis().expect("init_boolean_analysis");
        env.init_boolean_analysis_kkl_k2b().expect("first");
        env.init_boolean_analysis_kkl_k2b()
            .expect("second (idempotent)");
    }
}
