// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Friedgut junta-theorem roadmap — STEP (b): the GENERAL masked-`Fin.sum`
//! toolkit.
//!
//! Friedgut's L2 conclusion charges the masked Fourier mass `Σ_{S⊄J} f̂(S)²`
//! and the masked influence aggregate `Σ_{i∉J} Inf_i`. Both are sums of a
//! coordinate function restricted to the coordinates picked out by a Bool mask
//! `m : Fin n → Bool` (the OUTSIDE-`J` mask `m i := (Inf_i < τ)`). This module
//! banks the three GENERAL masked-sum facts the masked aggregation rungs
//! consume, each over the masked summand
//! `fun i => Rat.mul (BoolAnalysis.ind (m i)) (g i)` — the `{0,1}`-indicator-
//! weighted `Fin.sum` (`ind true ≡ 1`, `ind false ≡ 0`, so this IS the sum of
//! `g i` over `{i : m i = true}`):
//!
//! ```text
//! BoolAnalysis.masked_finSum_le :                                      -- (1)
//!   ∀ (n : Nat) (m : Fin n → Bool) (g h : Fin n → Rat),
//!     (∀ i, Rat.le (g i) (h i)) →
//!       Rat.le (Fin.sum n (fun i => Rat.mul (ind (m i)) (g i)))
//!              (Fin.sum n (fun i => Rat.mul (ind (m i)) (h i)))
//!
//! BoolAnalysis.masked_finSum_smul :                                    -- (2)
//!   ∀ (n : Nat) (m : Fin n → Bool) (c : Rat) (g : Fin n → Rat),
//!     Eq (Fin.sum n (fun i => Rat.mul (ind (m i)) (Rat.mul c (g i))))
//!        (Rat.mul c (Fin.sum n (fun i => Rat.mul (ind (m i)) (g i))))
//!
//! BoolAnalysis.masked_finSum_le_full :                                 -- (3)
//!   ∀ (n : Nat) (m : Fin n → Bool) (g : Fin n → Rat),
//!     (∀ i, Rat.le Rat.zero (g i)) →
//!       Rat.le (Fin.sum n (fun i => Rat.mul (ind (m i)) (g i)))
//!              (Fin.sum n g)
//! ```
//!
//! ## Proofs (constructive, EMPTY admitted-axiom closure)
//!
//! - **(1) `masked_finSum_le`**: per-coordinate
//!   `Rat.mul_le_mul_of_nonneg_left (ind (m i)) (g i) (h i) (hgh i)
//!      (ind_nonneg (m i)) : ind(m i)·g i ≤ ind(m i)·h i`
//!   (left-scaling by the nonneg `ind(m i)`), then `Fin.sum_le` lifts the
//!   pointwise bound over `Fin n`.
//! - **(2) `masked_finSum_smul`**: per-coordinate reassociation
//!   `ind(m i)·(c·g i) = c·(ind(m i)·g i)` via the `Rat.mul_assoc` /
//!   `Rat.mul_comm` chain
//!   `a·(c·b) =[assoc⁻¹] (a·c)·b =[comm on a·c] (c·a)·b =[assoc] c·(a·b)`,
//!   lifted by `Fin.sum_congr` to rewrite the integrand to
//!   `fun i => c·(ind(m i)·g i)`, then `Fin.sum_smul n c (fun i => ind(m i)·g i)`
//!   pulls `c` out of the sum.
//! - **(3) `masked_finSum_le_full`**: per-coordinate
//!   `ind(m i)·g i ≤ 1·g i = g i`: since `ind(m i) ≤ 1` (`ind_le_one`) and
//!   `0 ≤ g i` (`hnn i`), `Rat.mul_le_mul_of_nonneg_right (ind (m i)) 1 (g i) …`
//!   gives `ind(m i)·g i ≤ 1·g i`, and `Rat.one_mul (g i)` rewrites the RHS to
//!   `g i`; `Fin.sum_le` lifts it. The auxiliary `BoolAnalysis.ind_le_one`
//!   (`∀ b, ind b ≤ 1`, `Bool.casesOn` on `b` — `ind false ≡ 0 ≤ 1`,
//!   `ind true ≡ 1 ≤ 1`) is registered here.
//!
//! Every dependency (`Fin.sum_le`, `Fin.sum_smul`, `Fin.sum_congr`,
//! `Rat.mul_le_mul_of_nonneg_left`, `Rat.mul_le_mul_of_nonneg_right`,
//! `Rat.mul_assoc`, `Rat.mul_comm`, `Rat.one_mul`, `BoolAnalysis.ind`,
//! `BoolAnalysis.ind_nonneg`, `Eq`/`Eq.trans`/`Eq.symm`/`Eq.subst`/`Eq.refl`,
//! `Bool.casesOn`) is itself `Constructive` with an EMPTY admitted-axiom
//! closure, so every lemma here is `Constructive` with an EMPTY closure. NO
//! `sorry` / `add_decl_unchecked` / `add_decl_structural` / `native_decide` /
//! `unsafe` / `Real`. No axiom added or removed.

use super::boolean_analysis_order_toolkit::OrderConsts;
use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared atoms for the masked-`Fin.sum` toolkit. Embeds `OrderConsts` for the
/// `LE.le @Rat instLERat` order spelling shared with `Fin.sum_le`.
struct MaskedConsts {
    order: OrderConsts,
    nat: Expr,
    rat: Expr,
    bool_: Expr,
    fin: Expr,
    ind: Expr,
    ind_nonneg: Expr,
    fin_sum: Expr,
    fin_sum_le: Expr,
    fin_sum_smul: Expr,
    fin_sum_congr: Expr,
    rat_mul: Expr,
    rat_one: Expr,
    rat_mul_assoc: Expr,
    rat_mul_comm: Expr,
    rat_one_mul: Expr,
    mul_le_left: Expr,
    mul_le_right: Expr,
}

impl MaskedConsts {
    fn new() -> Self {
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            order: OrderConsts::new(),
            nat: k("Nat"),
            rat: k("Rat"),
            bool_: k("Bool"),
            fin: k("Fin"),
            ind: k("BoolAnalysis.ind"),
            ind_nonneg: k("BoolAnalysis.ind_nonneg"),
            fin_sum: k("Fin.sum"),
            fin_sum_le: k("Fin.sum_le"),
            fin_sum_smul: k("Fin.sum_smul"),
            fin_sum_congr: k("Fin.sum_congr"),
            rat_mul: k("Rat.mul"),
            rat_one: k("Rat.one"),
            rat_mul_assoc: k("Rat.mul_assoc"),
            rat_mul_comm: k("Rat.mul_comm"),
            rat_one_mul: k("Rat.one_mul"),
            mul_le_left: k("Rat.mul_le_mul_of_nonneg_left"),
            mul_le_right: k("Rat.mul_le_mul_of_nonneg_right"),
        }
    }

    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
    /// `Fin n → Rat`.
    fn fn_ty(&self, n: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.fin_of(n), self.rat.clone())
    }
    /// `Fin n → Bool`.
    fn mask_ty(&self, n: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.fin_of(n), self.bool_.clone())
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn rat_le(&self, a: Expr, b: Expr) -> Expr {
        self.order.rat_le(a, b)
    }
    fn rat_eq(&self, a: Expr, b: Expr) -> Expr {
        self.order.rat_eq(a, b)
    }
    fn ind_of(&self, bit: Expr) -> Expr {
        Expr::app(self.ind.clone(), bit)
    }
    /// `BoolAnalysis.ind_nonneg b : 0 ≤ ind b`.
    fn ind_nonneg_of(&self, bit: Expr) -> Expr {
        Expr::app(self.ind_nonneg.clone(), bit)
    }
    fn fin_sum_of(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(self.fin_sum.clone(), [n.clone(), g])
    }
    /// `Rat.mul_le_mul_of_nonneg_left a b c (h : b ≤ c) (h0 : 0 ≤ a) : a·b ≤ a·c`.
    fn mul_le_left_of(&self, a: Expr, b: Expr, cc: Expr, hbc: Expr, ha: Expr) -> Expr {
        Expr::apps(self.mul_le_left.clone(), [a, b, cc, hbc, ha])
    }
    /// `Rat.mul_le_mul_of_nonneg_right a b c (h : b ≤ c) (h0 : 0 ≤ a) : b·a ≤ c·a`.
    fn mul_le_right_of(&self, a: Expr, b: Expr, cc: Expr, hbc: Expr, ha: Expr) -> Expr {
        Expr::apps(self.mul_le_right.clone(), [a, b, cc, hbc, ha])
    }
    /// `Rat.mul_assoc a b c : (a·b)·c = a·(b·c)`.
    fn mul_assoc(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(self.rat_mul_assoc.clone(), [a, b, cc])
    }
    /// `Rat.mul_comm a b : a·b = b·a`.
    fn mul_comm(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul_comm.clone(), [a, b])
    }
    /// `Rat.one_mul a : 1·a = a`.
    fn one_mul(&self, a: Expr) -> Expr {
        Expr::app(self.rat_one_mul.clone(), a)
    }
    /// `Eq.symm.{1} Rat a b h`.
    fn symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        self.order.symm(a, b, h)
    }
    /// `Eq.trans.{1} Rat a b c h1 h2`.
    fn trans(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        self.order.trans(a, b, cc, h1, h2)
    }
    /// `Eq.subst.{1} Rat motive a b h_eq h_motive_a`.
    fn subst(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h_a: Expr) -> Expr {
        self.order.subst(motive, a, b, h_eq, h_a)
    }
    /// `Fin.sum_congr n f g (h : ∀ i, f i = g i) : Fin.sum n f = Fin.sum n g`.
    fn sum_congr(&self, n: &Expr, f: Expr, g: Expr, h: Expr) -> Expr {
        Expr::apps(self.fin_sum_congr.clone(), [n.clone(), f, g, h])
    }
    /// `Fin.sum_le n f g (h : ∀ i, f i ≤ g i) : Fin.sum n f ≤ Fin.sum n g`.
    fn sum_le(&self, n: &Expr, f: Expr, g: Expr, h: Expr) -> Expr {
        Expr::apps(self.fin_sum_le.clone(), [n.clone(), f, g, h])
    }
    /// `Fin.sum_smul n c g : Fin.sum n (fun i => c·g i) = c·Fin.sum n g`.
    fn sum_smul(&self, n: &Expr, cc: Expr, g: Expr) -> Expr {
        Expr::apps(self.fin_sum_smul.clone(), [n.clone(), cc, g])
    }

    /// `fun (i : Fin n) => Rat.mul (ind (m i)) (k i)` — the masked summand for an
    /// integrand `k` built by `mk_body(i) ↦ k i`.
    fn masked_fn<F: Fn(&Expr) -> Expr>(
        &self,
        parent: &EnvDeclBuilder,
        n: &Expr,
        m: &Expr,
        mk_body: F,
    ) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, i) = b.fresh_local(fin_n.clone());
        let body = self.mul(self.ind_of(Expr::app(m.clone(), i.clone())), mk_body(&i));
        b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_n, body))
    }

    /// `∀ (i : Fin n), P (g i) (h i)` for a pointwise relation `mk_rel`.
    fn forall_pointwise<F: Fn(&Expr) -> Expr>(
        &self,
        parent: &EnvDeclBuilder,
        n: &Expr,
        mk_rel: F,
    ) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, i) = b.fresh_local(fin_n.clone());
        let body = mk_rel(&i);
        b.finish_child(b.mk_pi(i_id, BinderInfo::Default, fin_n, body))
    }
}

impl Environment {
    /// Initialize the Friedgut masked-`Fin.sum` toolkit (STEP b). Registers the
    /// auxiliary `BoolAnalysis.ind_le_one` and the three masked-sum lemmas
    /// `masked_finSum_le`, `masked_finSum_smul`, `masked_finSum_le_full`.
    /// Idempotent; no axiom added or removed.
    pub fn init_boolean_analysis_friedgut_masked_finsum(&mut self) -> Result<(), EnvError> {
        // Carriers / bricks (each idempotent, constructive, empty closure):
        self.init_boolean_analysis()?; // BoolAnalysis.ind
        self.init_boolean_analysis_kkl_hcdual()?; // BoolAnalysis.ind_nonneg
        self.init_boolean_analysis_order_toolkit()?; // mul_le_mul_of_nonneg_{left,right}, LE.le
        self.init_rat_field_inst()?; // Rat.mul_assoc, Rat.mul_comm, Rat.one_mul, Rat.one
        self.init_fin_sum()?; // Fin.sum, Fin.sum_le, Fin.sum_smul, Fin.sum_congr
        self.init_bool()?; // Bool.casesOn, Bool.true/false
        self.init_eq()?; // Eq, Eq.refl, Eq.symm, Eq.trans, Eq.subst

        self.register_ind_le_one()?;
        self.register_masked_finsum_le()?;
        self.register_masked_finsum_le_cond()?;
        self.register_masked_finsum_smul()?;
        self.register_masked_finsum_le_full()?;
        Ok(())
    }

    /// `BoolAnalysis.ind_le_one : ∀ (b : Bool), Rat.le (ind b) Rat.one`.
    ///
    /// `Bool.casesOn` on `b` (eq-threaded like RUNG 2's `pointwise_bound`):
    /// `b = false` ⟹ `ind false ≡ 0 ≤ 1`; `b = true` ⟹ `ind true ≡ 1 ≤ 1`.
    /// Both branches discharged by the closed `0 ≤ 1` / `1 ≤ 1` facts via
    /// `Rat.le_of_ble_eq_true`. Constructive, empty closure. Idempotent.
    fn register_ind_le_one(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.ind_le_one");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = MaskedConsts::new();
        let l0 = Level::zero();
        let l1 = Level::succ(Level::zero());
        let bool_cases_on = Expr::const_(Name::from_string("Bool.casesOn"), vec![l0]);
        let eq_bool = Expr::const_(Name::from_string("Eq"), vec![l1.clone()]);
        let eq_refl_bool = Expr::const_(Name::from_string("Eq.refl"), vec![l1]);
        let bool_true = Expr::const_(Name::from_string("Bool.true"), vec![]);
        let bool_false = Expr::const_(Name::from_string("Bool.false"), vec![]);
        let le_of_ble = Expr::const_(Name::from_string("Rat.le_of_ble_eq_true"), vec![]);
        let btrue = Expr::const_(Name::from_string("Bool.true"), vec![]);
        let bool_c = c.bool_.clone();
        // `@Eq.refl Bool Bool.true : Bool.true = Bool.true` — the `Nat.ble`-evaluated
        // witness `(0 ≤ 1) = true` / `(1 ≤ 1) = true` consumed by `le_of_ble_eq_true`.
        let refl_btrue = Expr::apps(eq_refl_bool.clone(), [bool_c.clone(), btrue.clone()]);
        // `Rat.le_of_ble_eq_true a b (h : Rat.ble a b = true) : a ≤ b`.
        let ble_le = |a: Expr, b: Expr| Expr::apps(le_of_ble.clone(), [a, b, refl_btrue.clone()]);

        // Type: ∀ (b : Bool), Rat.le (ind b) Rat.one.
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (bb_id, bb) = b.fresh_local(c.bool_.clone());
            let body = c.rat_le(c.ind_of(bb), c.rat_one.clone());
            b.finish(b.mk_pi(bb_id, BinderInfo::Default, c.bool_.clone(), body))
        };

        // Value: fun (b : Bool) => Bool.casesOn motive b false_branch true_branch (refl b).
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (bb_id, bb) = b.fresh_local(c.bool_.clone());

            // motive : fun (x : Bool) => (b = x) → ind x ≤ 1.
            let goal_at = |x: Expr| c.rat_le(c.ind_of(x), c.rat_one.clone());
            let eq_bool_of = |a: Expr, x: Expr| Expr::apps(eq_bool.clone(), [bool_c.clone(), a, x]);
            let motive = {
                let mut m = EnvDeclBuilder::child_of(&b);
                let (x_id, x) = m.fresh_local(c.bool_.clone());
                let prem = eq_bool_of(bb.clone(), x.clone());
                let body = Expr::pi(BinderInfo::Default, prem, goal_at(x));
                m.finish_child(m.mk_lam(x_id, BinderInfo::Default, c.bool_.clone(), body))
            };
            // false branch : (b = false) → ind false ≤ 1.   ind false ≡ 0; 0 ≤ 1.
            let false_branch = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let prem = eq_bool_of(bb.clone(), bool_false.clone());
                let (he_id, _he) = d.fresh_local(prem.clone());
                let body = ble_le(c.ind_of(bool_false.clone()), c.rat_one.clone());
                d.finish_child(d.mk_lam(he_id, BinderInfo::Default, prem, body))
            };
            // true branch : (b = true) → ind true ≤ 1.   ind true ≡ 1; 1 ≤ 1.
            let true_branch = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let prem = eq_bool_of(bb.clone(), bool_true.clone());
                let (he_id, _he) = d.fresh_local(prem.clone());
                let body = ble_le(c.ind_of(bool_true.clone()), c.rat_one.clone());
                d.finish_child(d.mk_lam(he_id, BinderInfo::Default, prem, body))
            };
            let refl_bb = Expr::apps(eq_refl_bool.clone(), [bool_c.clone(), bb.clone()]);
            let cases = Expr::apps(
                bool_cases_on.clone(),
                [motive, bb.clone(), false_branch, true_branch, refl_bb],
            );
            b.finish(b.mk_lam(bb_id, BinderInfo::Default, c.bool_.clone(), cases))
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// STEP (b.1): `BoolAnalysis.masked_finSum_le`. Masked monotonicity of
    /// `Fin.sum` from a pointwise `g i ≤ h i`.
    fn register_masked_finsum_le(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.masked_finSum_le");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = MaskedConsts::new();

        let mk = |for_value: bool| -> Expr {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let mask_ty = c.mask_ty(&n);
            let fn_ty = c.fn_ty(&n);
            let (m_id, m) = b.fresh_local(mask_ty.clone());
            let (g_id, g) = b.fresh_local(fn_ty.clone());
            let (h_id, h) = b.fresh_local(fn_ty.clone());

            // hyp : ∀ i, g i ≤ h i.
            let hyp_ty = c.forall_pointwise(&b, &n, |i| {
                c.rat_le(
                    Expr::app(g.clone(), i.clone()),
                    Expr::app(h.clone(), i.clone()),
                )
            });
            let (hgh_id, hgh) = b.fresh_local(hyp_ty.clone());

            let mg = c.masked_fn(&b, &n, &m, |i| Expr::app(g.clone(), i.clone()));
            let mh = c.masked_fn(&b, &n, &m, |i| Expr::app(h.clone(), i.clone()));
            let concl = c.rat_le(c.fin_sum_of(&n, mg.clone()), c.fin_sum_of(&n, mh.clone()));

            let body = if for_value {
                // pointwise : ∀ i, ind(m i)·g i ≤ ind(m i)·h i
                //   := fun i => mul_le_left (ind(m i)) (g i) (h i) (hgh i) (ind_nonneg (m i)).
                let pointwise = {
                    let mut pb = EnvDeclBuilder::child_of(&b);
                    let fin_n = c.fin_of(&n);
                    let (i_id, i) = pb.fresh_local(fin_n.clone());
                    let ind_mi = c.ind_of(Expr::app(m.clone(), i.clone()));
                    let gi = Expr::app(g.clone(), i.clone());
                    let hi = Expr::app(h.clone(), i.clone());
                    let hgh_i = Expr::app(hgh.clone(), i.clone());
                    let h0 = c.ind_nonneg_of(Expr::app(m.clone(), i.clone()));
                    let term = c.mul_le_left_of(ind_mi, gi, hi, hgh_i, h0);
                    pb.finish_child(pb.mk_lam(i_id, BinderInfo::Default, fin_n, term))
                };
                c.sum_le(&n, mg, mh, pointwise)
            } else {
                concl
            };

            let bind = |b: &EnvDeclBuilder, id, ty: Expr, body: Expr| -> Expr {
                if for_value {
                    b.mk_lam(id, BinderInfo::Default, ty, body)
                } else {
                    b.mk_pi(id, BinderInfo::Default, ty, body)
                }
            };
            let e = bind(&b, hgh_id, hyp_ty, body);
            let e = bind(&b, h_id, fn_ty.clone(), e);
            let e = bind(&b, g_id, fn_ty, e);
            let e = bind(&b, m_id, mask_ty, e);
            let e = bind(&b, n_id, c.nat.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: mk(false),
            value: mk(true),
        })
    }

    /// STEP (b.1'): `BoolAnalysis.masked_finSum_le_cond`. CONDITIONAL masked
    /// monotonicity — the pointwise bound `g i ≤ h i` is only required ON the
    /// masked coordinates (`m i = true`), since off-mask both sides are `0·g =
    /// 0·h`. This is the variant the masked dual-HC aggregate consumes: the
    /// per-coordinate bound `W_norm_i ≤ 4·d·Inf_i` holds only for `m i := (Inf_i
    /// ≤ d²)` coordinates (it needs `Inf_i < 1`, which fails inside `J`).
    ///
    /// ```text
    /// BoolAnalysis.masked_finSum_le_cond :
    ///   ∀ (n : Nat) (m : Fin n → Bool) (g h : Fin n → Rat),
    ///     (∀ i, m i = Bool.true → Rat.le (g i) (h i)) →
    ///       Rat.le (Fin.sum n (fun i => ind (m i)·g i))
    ///              (Fin.sum n (fun i => ind (m i)·h i))
    /// ```
    ///
    /// Per-coordinate via eq-threaded `Bool.casesOn` on `m i`:
    /// `m i = false` ⟹ `ind false·g i ≡ 0·g i` and `0·g i ≤ 0·h i` reduces to
    /// `0 ≤ 0` (`Rat.le_refl`, after `Rat.zero_mul` rewrites both sides);
    /// `m i = true` ⟹ `ind true·g i ≡ 1·g i`, and `1·g i ≤ 1·h i` from the hyp
    /// `g i ≤ h i` via `Rat.mul_le_mul_of_nonneg_left 1 (g i) (h i) (hgh i …) (0≤1)`.
    /// Lifted by `Fin.sum_le`. Constructive, empty closure.
    fn register_masked_finsum_le_cond(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.masked_finSum_le_cond");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = MaskedConsts::new();
        let l0 = Level::zero();
        let l1 = Level::succ(Level::zero());
        let bool_cases_on = Expr::const_(Name::from_string("Bool.casesOn"), vec![l0]);
        let eq_bool = Expr::const_(Name::from_string("Eq"), vec![l1.clone()]);
        let eq_refl_bool = Expr::const_(Name::from_string("Eq.refl"), vec![l1]);
        let bool_true = Expr::const_(Name::from_string("Bool.true"), vec![]);
        let bool_false = Expr::const_(Name::from_string("Bool.false"), vec![]);

        let mk = |for_value: bool| -> Expr {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let mask_ty = c.mask_ty(&n);
            let fn_ty = c.fn_ty(&n);
            let (m_id, m) = b.fresh_local(mask_ty.clone());
            let (g_id, g) = b.fresh_local(fn_ty.clone());
            let (h_id, h) = b.fresh_local(fn_ty.clone());

            // hyp : ∀ i, m i = true → g i ≤ h i.
            let hyp_ty = c.forall_pointwise(&b, &n, |i| {
                let prem = Expr::apps(
                    eq_bool.clone(),
                    [
                        c.bool_.clone(),
                        Expr::app(m.clone(), i.clone()),
                        bool_true.clone(),
                    ],
                );
                let concl = c.rat_le(
                    Expr::app(g.clone(), i.clone()),
                    Expr::app(h.clone(), i.clone()),
                );
                Expr::pi(BinderInfo::Default, prem, concl)
            });
            let (hgh_id, hgh) = b.fresh_local(hyp_ty.clone());

            let mg = c.masked_fn(&b, &n, &m, |i| Expr::app(g.clone(), i.clone()));
            let mh = c.masked_fn(&b, &n, &m, |i| Expr::app(h.clone(), i.clone()));
            let concl = c.rat_le(c.fin_sum_of(&n, mg.clone()), c.fin_sum_of(&n, mh.clone()));

            let body = if for_value {
                // pointwise : ∀ i, ind(m i)·g i ≤ ind(m i)·h i  (Bool.casesOn on m i).
                let pointwise = {
                    let mut pb = EnvDeclBuilder::child_of(&b);
                    let fin_n = c.fin_of(&n);
                    let (i_id, i) = pb.fresh_local(fin_n.clone());
                    let mi = Expr::app(m.clone(), i.clone());
                    let gi = Expr::app(g.clone(), i.clone());
                    let hi = Expr::app(h.clone(), i.clone());
                    let hgh_i = Expr::app(hgh.clone(), i.clone()); // m i = true → g i ≤ h i

                    // goal at bit `bb` : ind bb · g i ≤ ind bb · h i.
                    let goal_at = |bb: Expr| {
                        c.rat_le(
                            c.mul(c.ind_of(bb.clone()), gi.clone()),
                            c.mul(c.ind_of(bb), hi.clone()),
                        )
                    };
                    let eq_bool_of =
                        |a: Expr, x: Expr| Expr::apps(eq_bool.clone(), [c.bool_.clone(), a, x]);
                    // motive : fun (bb : Bool) => (m i = bb) → ind bb·g i ≤ ind bb·h i.
                    let motive = {
                        let mut mb = EnvDeclBuilder::child_of(&pb);
                        let (bb_id, bb) = mb.fresh_local(c.bool_.clone());
                        let prem = eq_bool_of(mi.clone(), bb.clone());
                        let body = Expr::pi(BinderInfo::Default, prem, goal_at(bb));
                        mb.finish_child(mb.mk_lam(
                            bb_id,
                            BinderInfo::Default,
                            c.bool_.clone(),
                            body,
                        ))
                    };
                    // false branch : (m i = false) → ind false·g i ≤ ind false·h i.
                    //   ind false ≡ 0, so 0·g i ≤ 0·h i, i.e. 0 ≤ 0 after Rat.zero_mul both sides.
                    let false_branch = {
                        let mut d = EnvDeclBuilder::child_of(&pb);
                        let prem = eq_bool_of(mi.clone(), bool_false.clone());
                        let (he_id, _he) = d.fresh_local(prem.clone());
                        // 0·g i ≤ 0·h i  via  mul_le_left 0 (g i) (h i) (?) — NO: g≤h not given.
                        // Instead rewrite both 0·g, 0·h to 0 and use le_refl.
                        let zero = c.order.rat_zero.clone();
                        let zero_gi = c.mul(zero.clone(), gi.clone());
                        let zero_hi = c.mul(zero.clone(), hi.clone());
                        let zero_mul = |x: Expr| {
                            Expr::app(Expr::const_(Name::from_string("Rat.zero_mul"), vec![]), x)
                        };
                        // hrefl : 0 ≤ 0.
                        let hrefl = Expr::app(
                            Expr::const_(Name::from_string("Rat.le_refl"), vec![]),
                            zero.clone(),
                        );
                        // step1 : 0 ≤ 0·h i  via subst (fun t => 0 ≤ t) (symm (zero_mul h i)) hrefl.
                        let motive_r = {
                            let mut mb = EnvDeclBuilder::child_of(&d);
                            let (t_id, t) = mb.fresh_local(c.rat.clone());
                            let body = c.rat_le(zero.clone(), t);
                            mb.finish_child(mb.mk_lam(
                                t_id,
                                BinderInfo::Default,
                                c.rat.clone(),
                                body,
                            ))
                        };
                        let h_zh = c.symm(zero_hi.clone(), zero.clone(), zero_mul(hi.clone())); // 0 = 0·h i
                        let step1 = c.subst(motive_r, zero.clone(), zero_hi.clone(), h_zh, hrefl); // 0 ≤ 0·h i
                                                                                                   // step2 : 0·g i ≤ 0·h i  via subst (fun t => t ≤ 0·h i) (symm (zero_mul g i)) step1.
                        let motive_l = {
                            let mut mb = EnvDeclBuilder::child_of(&d);
                            let (t_id, t) = mb.fresh_local(c.rat.clone());
                            let body = c.rat_le(t, zero_hi.clone());
                            mb.finish_child(mb.mk_lam(
                                t_id,
                                BinderInfo::Default,
                                c.rat.clone(),
                                body,
                            ))
                        };
                        let h_zg = c.symm(zero_gi.clone(), zero.clone(), zero_mul(gi.clone())); // 0 = 0·g i
                        let step2 = c.subst(motive_l, zero.clone(), zero_gi.clone(), h_zg, step1);
                        d.finish_child(d.mk_lam(he_id, BinderInfo::Default, prem, step2))
                    };
                    // true branch : (m i = true) → ind true·g i ≤ ind true·h i.
                    //   ind true ≡ 1, so 1·g i ≤ 1·h i  via mul_le_left 1 (g i)(h i)(hgh i he)(0≤1).
                    let true_branch = {
                        let mut d = EnvDeclBuilder::child_of(&pb);
                        let prem = eq_bool_of(mi.clone(), bool_true.clone());
                        let (he_id, he) = d.fresh_local(prem.clone());
                        let one = c.rat_one.clone();
                        let hle = Expr::app(hgh_i.clone(), he); // g i ≤ h i
                                                                // 0 ≤ 1.
                        let bool_c = c.bool_.clone();
                        let btrue = bool_true.clone();
                        let refl_btrue = Expr::apps(eq_refl_bool.clone(), [bool_c, btrue]);
                        let h_one_nonneg = Expr::apps(
                            Expr::const_(Name::from_string("Rat.le_of_ble_eq_true"), vec![]),
                            [c.order.rat_zero.clone(), one.clone(), refl_btrue],
                        );
                        let term = c.mul_le_left_of(one, gi.clone(), hi.clone(), hle, h_one_nonneg);
                        d.finish_child(d.mk_lam(he_id, BinderInfo::Default, prem, term))
                    };
                    let refl_mi = Expr::apps(eq_refl_bool.clone(), [c.bool_.clone(), mi.clone()]);
                    let cases = Expr::apps(
                        bool_cases_on.clone(),
                        [motive, mi, false_branch, true_branch, refl_mi],
                    );
                    pb.finish_child(pb.mk_lam(i_id, BinderInfo::Default, fin_n, cases))
                };
                c.sum_le(&n, mg, mh, pointwise)
            } else {
                concl
            };

            let bind = |b: &EnvDeclBuilder, id, ty: Expr, body: Expr| -> Expr {
                if for_value {
                    b.mk_lam(id, BinderInfo::Default, ty, body)
                } else {
                    b.mk_pi(id, BinderInfo::Default, ty, body)
                }
            };
            let e = bind(&b, hgh_id, hyp_ty, body);
            let e = bind(&b, h_id, fn_ty.clone(), e);
            let e = bind(&b, g_id, fn_ty, e);
            let e = bind(&b, m_id, mask_ty, e);
            let e = bind(&b, n_id, c.nat.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: mk(false),
            value: mk(true),
        })
    }

    /// STEP (b.2): `BoolAnalysis.masked_finSum_smul`. Pull a scalar `c` through
    /// the masked sum.
    fn register_masked_finsum_smul(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.masked_finSum_smul");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = MaskedConsts::new();

        let mk = |for_value: bool| -> Expr {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let mask_ty = c.mask_ty(&n);
            let fn_ty = c.fn_ty(&n);
            let (m_id, m) = b.fresh_local(mask_ty.clone());
            let (cc_id, cc) = b.fresh_local(c.rat.clone());
            let (g_id, g) = b.fresh_local(fn_ty.clone());

            // lhs_fn := fun i => ind(m i)·(c·g i)   (the masked, c-scaled summand)
            let lhs_fn = c.masked_fn(&b, &n, &m, |i| {
                c.mul(cc.clone(), Expr::app(g.clone(), i.clone()))
            });
            // mid_fn := fun i => c·(ind(m i)·g i)   (the Fin.sum_smul integrand)
            let mid_fn = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let fin_n = c.fin_of(&n);
                let (i_id, i) = d.fresh_local(fin_n.clone());
                let ind_mi = c.ind_of(Expr::app(m.clone(), i.clone()));
                let gi = Expr::app(g.clone(), i.clone());
                let body = c.mul(cc.clone(), c.mul(ind_mi, gi));
                d.finish_child(d.mk_lam(i_id, BinderInfo::Default, fin_n, body))
            };
            // masked_g := fun i => ind(m i)·g i  (Fin.sum_smul's `g` argument).
            let masked_g = c.masked_fn(&b, &n, &m, |i| Expr::app(g.clone(), i.clone()));

            let lhs_sum = c.fin_sum_of(&n, lhs_fn.clone());
            let rhs = c.mul(cc.clone(), c.fin_sum_of(&n, masked_g.clone()));
            let concl = c.rat_eq(lhs_sum.clone(), rhs.clone());

            let body = if for_value {
                // per_i : ∀ i, ind(m i)·(c·g i) = c·(ind(m i)·g i).
                //   a·(c·b) =[symm assoc a c b] (a·c)·b
                //          =[congr ·b on (comm a c)] (c·a)·b
                //          =[assoc c a b] c·(a·b).
                let per_i = {
                    let mut pb = EnvDeclBuilder::child_of(&b);
                    let fin_n = c.fin_of(&n);
                    let (i_id, i) = pb.fresh_local(fin_n.clone());
                    let a = c.ind_of(Expr::app(m.clone(), i.clone())); // ind(m i)
                    let gi = Expr::app(g.clone(), i.clone()); // g i

                    let a_c_b = c.mul(c.mul(a.clone(), cc.clone()), gi.clone()); // (a·c)·b
                    let c_a_b = c.mul(c.mul(cc.clone(), a.clone()), gi.clone()); // (c·a)·b
                    let lhs_i = c.mul(a.clone(), c.mul(cc.clone(), gi.clone())); // a·(c·b)
                    let rhs_i = c.mul(cc.clone(), c.mul(a.clone(), gi.clone())); // c·(a·b)

                    // e1 : a·(c·b) = (a·c)·b   := symm (mul_assoc a c b).
                    let e1 = c.symm(
                        a_c_b.clone(),
                        lhs_i.clone(),
                        c.mul_assoc(a.clone(), cc.clone(), gi.clone()),
                    );
                    // e2 : (a·c)·b = (c·a)·b   := congrArg (·b) (mul_comm a c).
                    let mul_left_fn = {
                        let mut mb = EnvDeclBuilder::child_of(&pb);
                        let (t_id, t) = mb.fresh_local(c.rat.clone());
                        let body = c.mul(t, gi.clone());
                        mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                    };
                    let congr_arg = Expr::const_(
                        Name::from_string("congrArg"),
                        vec![Level::succ(Level::zero()), Level::succ(Level::zero())],
                    );
                    let e2 = Expr::apps(
                        congr_arg,
                        [
                            c.rat.clone(),
                            c.rat.clone(),
                            c.mul(a.clone(), cc.clone()),
                            c.mul(cc.clone(), a.clone()),
                            mul_left_fn,
                            c.mul_comm(a.clone(), cc.clone()),
                        ],
                    );
                    // e3 : (c·a)·b = c·(a·b)   := mul_assoc c a b.
                    let e3 = c.mul_assoc(cc.clone(), a.clone(), gi.clone());
                    // e12 : a·(c·b) = (c·a)·b  := trans e1 e2.
                    let e12 = c.trans(lhs_i.clone(), a_c_b.clone(), c_a_b.clone(), e1, e2);
                    // term : a·(c·b) = c·(a·b)  := trans e12 e3.
                    let term = c.trans(lhs_i, c_a_b, rhs_i, e12, e3);
                    pb.finish_child(pb.mk_lam(i_id, BinderInfo::Default, fin_n, term))
                };
                // congr : Fin.sum n lhs_fn = Fin.sum n mid_fn  := sum_congr n lhs_fn mid_fn per_i.
                let congr = c.sum_congr(&n, lhs_fn.clone(), mid_fn.clone(), per_i);
                // smul : Fin.sum n mid_fn = c · Fin.sum n masked_g  := Fin.sum_smul n c masked_g.
                //   (mid_fn ≡ fun i => c·(masked_g i) by β.)
                let smul = c.sum_smul(&n, cc.clone(), masked_g.clone());
                let mid_sum = c.fin_sum_of(&n, mid_fn.clone());
                // trans congr smul : Fin.sum n lhs_fn = c · Fin.sum n masked_g.
                c.trans(lhs_sum, mid_sum, rhs, congr, smul)
            } else {
                concl
            };

            let bind = |b: &EnvDeclBuilder, id, ty: Expr, body: Expr| -> Expr {
                if for_value {
                    b.mk_lam(id, BinderInfo::Default, ty, body)
                } else {
                    b.mk_pi(id, BinderInfo::Default, ty, body)
                }
            };
            let e = bind(&b, g_id, fn_ty, body);
            let e = bind(&b, cc_id, c.rat.clone(), e);
            let e = bind(&b, m_id, mask_ty, e);
            let e = bind(&b, n_id, c.nat.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: mk(false),
            value: mk(true),
        })
    }

    /// STEP (b.3): `BoolAnalysis.masked_finSum_le_full`. The masked sum is
    /// dominated by the FULL sum when the integrand is nonneg.
    fn register_masked_finsum_le_full(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.masked_finSum_le_full");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = MaskedConsts::new();
        let ind_le_one = Expr::const_(Name::from_string("BoolAnalysis.ind_le_one"), vec![]);

        let mk = |for_value: bool| -> Expr {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let mask_ty = c.mask_ty(&n);
            let fn_ty = c.fn_ty(&n);
            let (m_id, m) = b.fresh_local(mask_ty.clone());
            let (g_id, g) = b.fresh_local(fn_ty.clone());

            // hyp : ∀ i, 0 ≤ g i.
            let hyp_ty = c.forall_pointwise(&b, &n, |i| {
                c.rat_le(c.order.rat_zero.clone(), Expr::app(g.clone(), i.clone()))
            });
            let (hnn_id, hnn) = b.fresh_local(hyp_ty.clone());

            let mg = c.masked_fn(&b, &n, &m, |i| Expr::app(g.clone(), i.clone()));
            let concl = c.rat_le(c.fin_sum_of(&n, mg.clone()), c.fin_sum_of(&n, g.clone()));

            let body = if for_value {
                // pointwise : ∀ i, ind(m i)·g i ≤ g i.
                //   step  : ind(m i)·g i ≤ 1·g i
                //           := mul_le_right (g i) (ind(m i)) 1 (ind_le_one (m i)) (hnn i)
                //              (mul_le_mul_of_nonneg_right a b c (b≤c)(0≤a) : b·a ≤ c·a,
                //               with a := g i, b := ind(m i), c := 1).
                //   eq1mul: 1·g i = g i  := Rat.one_mul (g i).
                //   close : subst (motive t => ind(m i)·g i ≤ t) (1·g i) (g i) eq1mul step.
                let pointwise = {
                    let mut pb = EnvDeclBuilder::child_of(&b);
                    let fin_n = c.fin_of(&n);
                    let (i_id, i) = pb.fresh_local(fin_n.clone());
                    let mi = Expr::app(m.clone(), i.clone());
                    let ind_mi = c.ind_of(mi.clone());
                    let gi = Expr::app(g.clone(), i.clone());
                    let ind_le_one_i = Expr::app(ind_le_one.clone(), mi);
                    let hnn_i = Expr::app(hnn.clone(), i.clone());
                    // step : ind(m i)·g i ≤ 1·g i.
                    let step = c.mul_le_right_of(
                        gi.clone(),
                        ind_mi.clone(),
                        c.rat_one.clone(),
                        ind_le_one_i,
                        hnn_i,
                    );
                    // eq1mul : 1·g i = g i.
                    let one_gi = c.mul(c.rat_one.clone(), gi.clone());
                    let eq1mul = c.one_mul(gi.clone());
                    // motive : fun t => ind(m i)·g i ≤ t.
                    let ind_mi_gi = c.mul(ind_mi.clone(), gi.clone());
                    let motive = {
                        let mut mb = EnvDeclBuilder::child_of(&pb);
                        let (t_id, t) = mb.fresh_local(c.rat.clone());
                        let body = c.rat_le(ind_mi_gi.clone(), t);
                        mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                    };
                    // close : ind(m i)·g i ≤ g i.
                    let term = c.subst(motive, one_gi, gi.clone(), eq1mul, step);
                    pb.finish_child(pb.mk_lam(i_id, BinderInfo::Default, fin_n, term))
                };
                c.sum_le(&n, mg, g.clone(), pointwise)
            } else {
                concl
            };

            let bind = |b: &EnvDeclBuilder, id, ty: Expr, body: Expr| -> Expr {
                if for_value {
                    b.mk_lam(id, BinderInfo::Default, ty, body)
                } else {
                    b.mk_pi(id, BinderInfo::Default, ty, body)
                }
            };
            let e = bind(&b, hnn_id, hyp_ty, body);
            let e = bind(&b, g_id, fn_ty, e);
            let e = bind(&b, m_id, mask_ty, e);
            let e = bind(&b, n_id, c.nat.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: mk(false),
            value: mk(true),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_friedgut_masked_finsum()
            .expect("init_boolean_analysis_friedgut_masked_finsum");
        env.init_boolean_analysis_friedgut_masked_finsum()
            .expect("idempotent");
        env
    }

    fn assert_constructive(env: &Environment, name: &str) {
        let nm = Name::from_string(name);
        let info = env
            .get_const(&nm)
            .unwrap_or_else(|| panic!("{name} registered"));
        assert_eq!(info.kind, ConstantKind::Theorem, "{name} must be a Theorem");
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(env, env.mode());
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("{name} must kernel-check: {e:?}"));
        assert_eq!(
            env.proof_quality(&nm),
            Some(ProofQuality::Constructive),
            "{name} must be Constructive"
        );
        assert!(
            env.axiom_deps(&nm).expect("deps").is_empty(),
            "{name} closure must be foundational-only: {:?}",
            env.axiom_deps(&nm)
        );
    }

    #[test]
    fn test_ind_le_one_is_constructive_theorem() {
        assert_constructive(&env(), "BoolAnalysis.ind_le_one");
    }

    #[test]
    fn test_masked_finsum_le_is_constructive_theorem() {
        assert_constructive(&env(), "BoolAnalysis.masked_finSum_le");
    }

    #[test]
    fn test_masked_finsum_le_cond_is_constructive_theorem() {
        assert_constructive(&env(), "BoolAnalysis.masked_finSum_le_cond");
    }

    #[test]
    fn test_masked_finsum_smul_is_constructive_theorem() {
        assert_constructive(&env(), "BoolAnalysis.masked_finSum_smul");
    }

    #[test]
    fn test_masked_finsum_le_full_is_constructive_theorem() {
        assert_constructive(&env(), "BoolAnalysis.masked_finSum_le_full");
    }
}
