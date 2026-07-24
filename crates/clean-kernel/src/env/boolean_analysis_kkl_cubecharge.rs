// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL root-free CUBIC charge — the rational small-influence collapse
//! `Σ_i Inf_i³ ≤ ε²·I[f]` (under `max_i Inf_i ≤ ε`).
//!
//! ## Why this brick exists (the root-free obstruction context)
//!
//! The sharp-KKL retirement is walled by a non-rational `Inf_i^{3/2}`
//! hypercontractive step: the genuine per-coordinate bound is
//! `W^{≤k}[D_i f] ≤ C^k · Inf_i^{3/2}` (O'Donnell §9.6 / Thm 9.28, exponent
//! `2/(1+ρ²) = 3/2`). The `^{3/2}` has no `Rat.powNat` carrier in the
//! `BoolAnalysis` overlay (`designs/2026-06-13-sharp-kkl-max-influence-roadmap.md`,
//! BRIDGE OBSTRUCTION REPORT 2026-06-18).
//!
//! The investigated escape was the **root-free squared route**: prove the
//! per-coordinate SQUARED bound `(W^{≤k}[D_i f])² ≤ C²ᵏ·Inf_i³` (rational —
//! `Inf_i³` IS `Rat`-expressible), then sum WITHOUT a square root via finite
//! Cauchy–Schwarz `(Σ a_i)² ≤ n·Σ a_i²` (`Fin.sum_cauchy_schwarz`, LANDED). The
//! summed root-free bound is `M_{1..k}² ≤ n·C²ᵏ·Σ_i Inf_i³`. This brick proves
//! the RATIONAL factor `Σ_i Inf_i³ ≤ ε²·I[f]` of that route — and, by exposing
//! exactly where the `n` enters, it makes the FACTOR-`n` OBSTRUCTION concrete:
//! composing `(Σ Inf^{3/2})² ≤ n·Σ Inf³` (Cauchy–Schwarz) with this
//! `Σ Inf³ ≤ ε²·I[f]` yields `(Σ Inf^{3/2})² ≤ n·ε²·I[f]`, i.e.
//! `M_{1..k} ≤ √n·Cᵏ·ε·√(I[f])` — a **bare `√n`** that is UNBOUNDED in the KKL
//! regime `2^k ≤ n` (`n` arbitrarily large). The sharp `n`-free target needs
//! `Σ Inf^{3/2} ≤ ε^{1/2}·I[f]` (linear in `I[f]`, no `n`), which the squared
//! route cannot recover: the `n` enters through a Cauchy–Schwarz step that is
//! TIGHT on the equal-influence (tribes) instance and so cannot be divided back
//! out. The `√n` IS the `log n`-vs-`n` gap KKL exists to close — the same
//! factor-`n` disease that killed the false `hc_dual_total`→`hc_dual_sharp`
//! reduction (R4/R6). See the design note `2026-06-18-kkl-root-free-obstruction.md`.
//!
//! This brick is therefore a SOUND, n-free, root-free RATIONAL fact that is
//! genuinely on the KKL critical path (it is the cubic analogue of the landed
//! `sum_sq_le_eps_mul_sum`, and the exact RHS factor the squared route emits),
//! while the surrounding analysis records that the route it serves cannot reach
//! the sharp bound. It asserts NO hypercontractive inequality.
//!
//! ## What this proves
//!
//! ```text
//! BoolAnalysis.sum_cube_le_eps_sq_mul_sum :                        -- abstract core
//!   ∀ (n : Nat) (g : Fin n → Rat) (eps : Rat),
//!     (∀ (i : Fin n), Rat.le Rat.zero (g i))                       -- nonnegativity
//!     → (∀ (i : Fin n), Rat.le (g i) eps)                          -- the small-`g` hyp
//!     → Rat.le (Fin.sum n (fun i => Rat.mul (Rat.mul (g i) (g i)) (g i)))
//!              (Rat.mul (Rat.mul eps eps) (Fin.sum n g))
//!
//! BoolAnalysis.kkl_sum_cube_influence_le :                         -- the KKL instance
//!   ∀ (n : Nat) (f : BoolFn n) (eps : Rat),
//!     (∀ (i : Fin n), Rat.le Rat.zero (Influence n f i))           -- influences ≥ 0
//!     → (∀ (i : Fin n), Rat.le (Influence n f i) eps)              -- max-influence ≤ ε
//!     → Rat.le
//!         (Fin.sum n (fun i =>
//!            Rat.mul (Rat.mul (Influence n f i) (Influence n f i)) (Influence n f i)))
//!         (Rat.mul (Rat.mul eps eps) (TotalInfluence n f))
//! ```
//!
//! i.e. `Σ_i g_i³ ≤ ε²·(Σ_i g_i)` whenever `0 ≤ g_i ≤ ε` for all `i`; at
//! `g := Influence n f` (with `Fin.sum n (Influence n f) ≡ TotalInfluence n f`
//! by reducible-`Definition` δ + η) it is `Σ_i Inf_i³ ≤ ε²·I[f]`.
//!
//! ## Proof (constructive, empty admitted-axiom closure)
//!
//! **`sum_cube_le_eps_sq_mul_sum`** (the abstract core). Per coordinate `i`,
//! writing `gi := g i`:
//! 1. `h0eps : 0 ≤ eps` := `Rat.le_trans 0 gi eps (h_nn i) (h_le i)`.
//! 2. `h_g_sq : gi·gi ≤ eps·gi` :=
//!    `Rat.mul_le_mul_of_nonneg_right gi gi eps (h_le i) (h_nn i)`.
//! 3. `h_eps_g : eps·gi ≤ eps·eps` :=
//!    `Rat.mul_le_mul_of_nonneg_left eps gi eps (h_le i) h0eps`.
//! 4. `h_sq : gi·gi ≤ eps·eps` := `Rat.le_trans (gi·gi) (eps·gi) (eps·eps) (2) (3)`.
//! 5. `h_cube : (gi·gi)·gi ≤ (eps·eps)·gi` :=
//!    `Rat.mul_le_mul_of_nonneg_right gi (gi·gi) (eps·eps) h_sq (h_nn i)`.
//!    THIS is where the `gi ≤ eps` hypothesis is consumed (twice, in 2 and 3).
//! 6. `Fin.sum_le n (fun i => (gi·gi)·gi) (fun i => (eps·eps)·gi) (per) :
//!    Fin.sum n (fun i => gi³) ≤ Fin.sum n (fun i => (eps·eps)·gi)`.
//! 7. `Fin.sum_smul n (eps·eps) g : Fin.sum n (fun i => (eps·eps)·gi) = (eps·eps)·Fin.sum n g`.
//! 8. `Eq.subst` (motive `t ↦ Fin.sum n (fun i => gi³) ≤ t`) transports (6) along
//!    (7) to the goal `Fin.sum n (fun i => gi³) ≤ (eps·eps)·Fin.sum n g`.
//!
//! **`kkl_sum_cube_influence_le`** (the KKL instance): apply
//! `sum_cube_le_eps_sq_mul_sum n (fun i => Influence n f i) eps` to the two
//! influence hypotheses; its conclusion's RHS `(eps·eps)·Fin.sum n (Influence n f)`
//! is def-eq (δ on the reducible `TotalInfluence` Definition + η) to
//! `(eps·eps)·TotalInfluence n f`.
//!
//! Every leaf (`Rat.le_trans`, `Rat.mul_le_mul_of_nonneg_left`/`_right`,
//! `Fin.sum_le`, `Fin.sum_smul`, `Eq.subst`) is `Constructive` with empty closure,
//! so both lemmas are too. No axiom is added or removed. Refute-checked against
//! the dictator/parity/constant battery (the hypothesis is essential — the
//! unconditional version refutes on the dictator with `ε < 1`:
//! `Σ Inf³ = 1 > ε² = ε²·I[f]`).

use super::boolean_analysis_order_toolkit::OrderConsts;
use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

/// Shared atoms for the small-influence cubic charge.
struct CubeChargeConsts {
    order: OrderConsts,
    nat: Expr,
    fin: Expr,
    bool_fn: Expr,
    influence: Expr,
    total_influence: Expr,
    fin_sum: Expr,
    fin_sum_le: Expr,
    fin_sum_smul: Expr,
    mul_le_mul_right: Expr,
    mul_le_mul_left: Expr,
    le_trans: Expr,
}

impl CubeChargeConsts {
    fn new() -> Self {
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            order: OrderConsts::new(),
            nat: k("Nat"),
            fin: k("Fin"),
            bool_fn: k("BoolAnalysis.BoolFn"),
            influence: k("BoolAnalysis.Influence"),
            total_influence: k("BoolAnalysis.TotalInfluence"),
            fin_sum: k("Fin.sum"),
            fin_sum_le: k("Fin.sum_le"),
            fin_sum_smul: k("Fin.sum_smul"),
            mul_le_mul_right: k("Rat.mul_le_mul_of_nonneg_right"),
            mul_le_mul_left: k("Rat.mul_le_mul_of_nonneg_left"),
            le_trans: k("Rat.le_trans"),
        }
    }

    fn rat(&self) -> Expr {
        self.order.rat.clone()
    }
    fn zero(&self) -> Expr {
        self.order.rat_zero.clone()
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        self.order.mul(a, b)
    }
    fn le(&self, a: Expr, b: Expr) -> Expr {
        self.order.rat_le(a, b)
    }
    fn le0(&self, a: Expr) -> Expr {
        self.le(self.zero(), a)
    }
    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
    fn fin_to_rat(&self, n: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.fin_of(n), self.rat())
    }
    fn bool_fn_of(&self, n: &Expr) -> Expr {
        Expr::app(self.bool_fn.clone(), n.clone())
    }
    /// `Fin.sum n h`.
    fn sum(&self, n: &Expr, h: Expr) -> Expr {
        Expr::apps(self.fin_sum.clone(), [n.clone(), h])
    }
    /// `Influence n f i`.
    fn influence_of(&self, n: &Expr, f: &Expr, i: &Expr) -> Expr {
        Expr::apps(self.influence.clone(), [n.clone(), f.clone(), i.clone()])
    }
    /// `TotalInfluence n f`.
    fn total_influence_of(&self, n: &Expr, f: &Expr) -> Expr {
        Expr::apps(self.total_influence.clone(), [n.clone(), f.clone()])
    }
    /// `Rat.mul_le_mul_of_nonneg_right a b c h_bc h_0a : b·a ≤ c·a`.
    fn mul_le_right(&self, a: Expr, b: Expr, c: Expr, h_bc: Expr, h_0a: Expr) -> Expr {
        Expr::apps(self.mul_le_mul_right.clone(), [a, b, c, h_bc, h_0a])
    }
    /// `Rat.mul_le_mul_of_nonneg_left a b c h_bc h_0a : a·b ≤ a·c`.
    fn mul_le_left(&self, a: Expr, b: Expr, c: Expr, h_bc: Expr, h_0a: Expr) -> Expr {
        Expr::apps(self.mul_le_mul_left.clone(), [a, b, c, h_bc, h_0a])
    }
    /// `Rat.le_trans a b c h_ab h_bc : a ≤ c`.
    fn le_trans_of(&self, a: Expr, b: Expr, c: Expr, h_ab: Expr, h_bc: Expr) -> Expr {
        Expr::apps(self.le_trans.clone(), [a, b, c, h_ab, h_bc])
    }
}

impl Environment {
    /// Register the small-influence cubic charge bricks. Idempotent.
    pub fn init_boolean_analysis_kkl_cubecharge(&mut self) -> Result<(), EnvError> {
        self.register_sum_cube_le_eps_sq_mul_sum()?;
        self.register_kkl_sum_cube_influence_le()?;
        Ok(())
    }

    /// `BoolAnalysis.sum_cube_le_eps_sq_mul_sum` — the abstract small-`g` cubic
    /// charge `(∀ i, 0 ≤ g i) → (∀ i, g i ≤ ε) → Σ_i g_i³ ≤ ε²·Σ_i g_i`. See
    /// module docs. Constructive, empty admitted-axiom closure. Idempotent.
    pub fn register_sum_cube_le_eps_sq_mul_sum(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.sum_cube_le_eps_sq_mul_sum");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_fin_sum()?; // Fin.sum, Fin.sum_le, Fin.sum_smul
        self.init_boolean_analysis_order_toolkit()?; // Rat.mul_le_mul_of_nonneg_{left,right}
        self.register_rat_le_trans_proof()?; // Rat.le_trans

        let c = CubeChargeConsts::new();

        // ∀-quantified nonnegativity hypothesis `∀ i, 0 ≤ g i`.
        let nn_hyp = |b: &EnvDeclBuilder, n: &Expr, g: &Expr| -> Expr {
            let mut ch = EnvDeclBuilder::child_of(b);
            let fin_n = c.fin_of(n);
            let (i_id, i) = ch.fresh_local(fin_n.clone());
            let body = c.le0(Expr::app(g.clone(), i));
            ch.finish_child(ch.mk_pi(i_id, BinderInfo::Default, fin_n, body))
        };
        // ∀-quantified small-`g` hypothesis `∀ i, g i ≤ eps`.
        let le_hyp = |b: &EnvDeclBuilder, n: &Expr, g: &Expr, eps: &Expr| -> Expr {
            let mut ch = EnvDeclBuilder::child_of(b);
            let fin_n = c.fin_of(n);
            let (i_id, i) = ch.fresh_local(fin_n.clone());
            let body = c.le(Expr::app(g.clone(), i), eps.clone());
            ch.finish_child(ch.mk_pi(i_id, BinderInfo::Default, fin_n, body))
        };
        // integrand `fun i => (g i · g i) · g i`  (= g i³).
        let cube_fn = |b: &EnvDeclBuilder, n: &Expr, g: &Expr| -> Expr {
            let mut ch = EnvDeclBuilder::child_of(b);
            let fin_n = c.fin_of(n);
            let (i_id, i) = ch.fresh_local(fin_n.clone());
            let gi = Expr::app(g.clone(), i);
            let body = c.mul(c.mul(gi.clone(), gi.clone()), gi);
            ch.finish_child(ch.mk_lam(i_id, BinderInfo::Default, fin_n, body))
        };
        // integrand `fun i => (eps · eps) · g i`.
        let scaled_fn = |b: &EnvDeclBuilder, n: &Expr, g: &Expr, eps: &Expr| -> Expr {
            let mut ch = EnvDeclBuilder::child_of(b);
            let fin_n = c.fin_of(n);
            let (i_id, i) = ch.fresh_local(fin_n.clone());
            let body = c.mul(c.mul(eps.clone(), eps.clone()), Expr::app(g.clone(), i));
            ch.finish_child(ch.mk_lam(i_id, BinderInfo::Default, fin_n, body))
        };

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let g_ty = c.fin_to_rat(&n);
            let (g_id, g) = b.fresh_local(g_ty.clone());
            let (eps_id, eps) = b.fresh_local(c.rat());
            let h_nn = nn_hyp(&b, &n, &g);
            let (hnn_id, _) = b.fresh_local(h_nn.clone());
            let h_le = le_hyp(&b, &n, &g, &eps);
            let (hle_id, _) = b.fresh_local(h_le.clone());

            let lhs = c.sum(&n, cube_fn(&b, &n, &g));
            let rhs = c.mul(c.mul(eps.clone(), eps.clone()), c.sum(&n, g.clone()));
            let concl = c.le(lhs, rhs);

            let e = b.mk_pi(hle_id, BinderInfo::Default, h_le, concl);
            let e = b.mk_pi(hnn_id, BinderInfo::Default, h_nn, e);
            let e = b.mk_pi(eps_id, BinderInfo::Default, c.rat(), e);
            let e = b.mk_pi(g_id, BinderInfo::Default, g_ty, e);
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let g_ty = c.fin_to_rat(&n);
            let (g_id, g) = b.fresh_local(g_ty.clone());
            let (eps_id, eps) = b.fresh_local(c.rat());
            let h_nn = nn_hyp(&b, &n, &g);
            let (hnn_id, hnn) = b.fresh_local(h_nn.clone());
            let h_le = le_hyp(&b, &n, &g, &eps);
            let (hle_id, hle) = b.fresh_local(h_le.clone());

            let cube = cube_fn(&b, &n, &g);
            let scaled = scaled_fn(&b, &n, &g, &eps);
            let eps_sq = c.mul(eps.clone(), eps.clone());

            // per i : (g i · g i) · g i ≤ (eps · eps) · g i  (consumes hle twice).
            let per = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let fin_n = c.fin_of(&n);
                let (i_id, i) = ch.fresh_local(fin_n.clone());
                let gi = Expr::app(g.clone(), i.clone());
                let h_le_i = Expr::app(hle.clone(), i.clone()); // g i ≤ eps
                let h_nn_i = Expr::app(hnn.clone(), i.clone()); // 0 ≤ g i

                // h0eps : 0 ≤ eps  := le_trans 0 (g i) eps (0≤g i) (g i≤eps)
                let h0eps = c.le_trans_of(
                    c.zero(),
                    gi.clone(),
                    eps.clone(),
                    h_nn_i.clone(),
                    h_le_i.clone(),
                );
                // h_g_sq : g i · g i ≤ eps · g i
                //   := mul_le_mul_of_nonneg_right (a:=g i) (b:=g i) (c:=eps) (g i≤eps) (0≤g i)
                let h_g_sq = c.mul_le_right(
                    gi.clone(),
                    gi.clone(),
                    eps.clone(),
                    h_le_i.clone(),
                    h_nn_i.clone(),
                );
                // h_eps_g : eps · g i ≤ eps · eps
                //   := mul_le_mul_of_nonneg_left (a:=eps) (b:=g i) (c:=eps) (g i≤eps) (0≤eps)
                let h_eps_g =
                    c.mul_le_left(eps.clone(), gi.clone(), eps.clone(), h_le_i.clone(), h0eps);
                // h_sq : g i · g i ≤ eps · eps  := le_trans (g i·g i) (eps·g i) (eps·eps) h_g_sq h_eps_g
                let h_sq = c.le_trans_of(
                    c.mul(gi.clone(), gi.clone()),
                    c.mul(eps.clone(), gi.clone()),
                    eps_sq.clone(),
                    h_g_sq,
                    h_eps_g,
                );
                // h_cube : (g i · g i) · g i ≤ (eps · eps) · g i
                //   := mul_le_mul_of_nonneg_right (a:=g i) (b:=g i·g i) (c:=eps·eps) h_sq (0≤g i)
                let body = c.mul_le_right(
                    gi.clone(),
                    c.mul(gi.clone(), gi.clone()),
                    eps_sq.clone(),
                    h_sq,
                    h_nn_i,
                );
                ch.finish_child(ch.mk_lam(i_id, BinderInfo::Default, fin_n, body))
            };

            // h_sumle : Fin.sum n cube ≤ Fin.sum n scaled.
            let h_sumle = Expr::apps(
                c.fin_sum_le.clone(),
                [n.clone(), cube.clone(), scaled.clone(), per],
            );

            // h_smul : Fin.sum n scaled = (eps·eps) · Fin.sum n g.
            let h_smul = Expr::apps(
                c.fin_sum_smul.clone(),
                [n.clone(), eps_sq.clone(), g.clone()],
            );

            // motive t => Fin.sum n cube ≤ t.
            let lhs = c.sum(&n, cube.clone());
            let motive = {
                let mut m = EnvDeclBuilder::child_of(&b);
                let (t_id, t) = m.fresh_local(c.rat());
                let body = c.le(lhs.clone(), t);
                m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.rat(), body))
            };
            let a = c.sum(&n, scaled); // Fin.sum n scaled
            let bb = c.mul(eps_sq, c.sum(&n, g.clone())); // (eps·eps) · Fin.sum n g
            let body = c.order.subst(motive, a, bb, h_smul, h_sumle);

            let e = b.mk_lam(hle_id, BinderInfo::Default, h_le, body);
            let e = b.mk_lam(hnn_id, BinderInfo::Default, h_nn, e);
            let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat(), e);
            let e = b.mk_lam(g_id, BinderInfo::Default, g_ty, e);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

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

    /// `BoolAnalysis.kkl_sum_cube_influence_le` — the KKL instance of the
    /// small-influence cubic charge: `(∀ i, 0 ≤ Inf_i) → (∀ i, Inf_i ≤ ε) →
    /// Σ_i Inf_i³ ≤ ε²·I[f]`. See module docs. Constructive, empty admitted-axiom
    /// closure. Idempotent.
    pub fn register_kkl_sum_cube_influence_le(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.kkl_sum_cube_influence_le");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_sum_cube_le_eps_sq_mul_sum()?;
        self.init_boolean_analysis()?; // Influence, TotalInfluence (reducible defs)
                                       // KKL-finish idempotency: `init_boolean_analysis` may now register
                                       // this declaration transitively, so re-check after the deps.
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let c = CubeChargeConsts::new();

        // `fun i => Influence n f i` — the instantiation `g`.
        let infl_fn = |b: &EnvDeclBuilder, n: &Expr, f: &Expr| -> Expr {
            let mut ch = EnvDeclBuilder::child_of(b);
            let fin_n = c.fin_of(n);
            let (i_id, i) = ch.fresh_local(fin_n.clone());
            let body = c.influence_of(n, f, &i);
            ch.finish_child(ch.mk_lam(i_id, BinderInfo::Default, fin_n, body))
        };
        // `∀ i, 0 ≤ Influence n f i`.
        let nn_hyp = |b: &EnvDeclBuilder, n: &Expr, f: &Expr| -> Expr {
            let mut ch = EnvDeclBuilder::child_of(b);
            let fin_n = c.fin_of(n);
            let (i_id, i) = ch.fresh_local(fin_n.clone());
            let body = c.le0(c.influence_of(n, f, &i));
            ch.finish_child(ch.mk_pi(i_id, BinderInfo::Default, fin_n, body))
        };
        // `∀ i, Influence n f i ≤ eps`.
        let le_hyp = |b: &EnvDeclBuilder, n: &Expr, f: &Expr, eps: &Expr| -> Expr {
            let mut ch = EnvDeclBuilder::child_of(b);
            let fin_n = c.fin_of(n);
            let (i_id, i) = ch.fresh_local(fin_n.clone());
            let body = c.le(c.influence_of(n, f, &i), eps.clone());
            ch.finish_child(ch.mk_pi(i_id, BinderInfo::Default, fin_n, body))
        };
        // `fun i => (Influence n f i · Influence n f i) · Influence n f i`.
        let cube_fn = |b: &EnvDeclBuilder, n: &Expr, f: &Expr| -> Expr {
            let mut ch = EnvDeclBuilder::child_of(b);
            let fin_n = c.fin_of(n);
            let (i_id, i) = ch.fresh_local(fin_n.clone());
            let inf = c.influence_of(n, f, &i);
            let body = c.mul(c.mul(inf.clone(), inf.clone()), inf);
            ch.finish_child(ch.mk_lam(i_id, BinderInfo::Default, fin_n, body))
        };

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let bool_fn_n = c.bool_fn_of(&n);
            let (f_id, f) = b.fresh_local(bool_fn_n.clone());
            let (eps_id, eps) = b.fresh_local(c.rat());
            let h_nn = nn_hyp(&b, &n, &f);
            let (hnn_id, _) = b.fresh_local(h_nn.clone());
            let h_le = le_hyp(&b, &n, &f, &eps);
            let (hle_id, _) = b.fresh_local(h_le.clone());

            let lhs = c.sum(&n, cube_fn(&b, &n, &f));
            let rhs = c.mul(
                c.mul(eps.clone(), eps.clone()),
                c.total_influence_of(&n, &f),
            );
            let concl = c.le(lhs, rhs);

            let e = b.mk_pi(hle_id, BinderInfo::Default, h_le, concl);
            let e = b.mk_pi(hnn_id, BinderInfo::Default, h_nn, e);
            let e = b.mk_pi(eps_id, BinderInfo::Default, c.rat(), e);
            let e = b.mk_pi(f_id, BinderInfo::Default, bool_fn_n, e);
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        let abstract_core = Expr::const_(
            Name::from_string("BoolAnalysis.sum_cube_le_eps_sq_mul_sum"),
            vec![],
        );

        // value: fun (n) (f) (eps) (hnn) (hle) =>
        //   sum_cube_le_eps_sq_mul_sum n (fun i => Influence n f i) eps hnn hle
        // (RHS `(eps·eps) · Fin.sum n (fun i => Influence n f i)` is def-eq to
        //  `(eps·eps) · TotalInfluence n f` by δ on the reducible `TotalInfluence`.)
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let bool_fn_n = c.bool_fn_of(&n);
            let (f_id, f) = b.fresh_local(bool_fn_n.clone());
            let (eps_id, eps) = b.fresh_local(c.rat());
            let h_nn = nn_hyp(&b, &n, &f);
            let (hnn_id, hnn) = b.fresh_local(h_nn.clone());
            let h_le = le_hyp(&b, &n, &f, &eps);
            let (hle_id, hle) = b.fresh_local(h_le.clone());

            let g = infl_fn(&b, &n, &f);
            let body = Expr::apps(abstract_core.clone(), [n.clone(), g, eps.clone(), hnn, hle]);

            let e = b.mk_lam(hle_id, BinderInfo::Default, h_le, body);
            let e = b.mk_lam(hnn_id, BinderInfo::Default, h_nn, e);
            let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat(), e);
            let e = b.mk_lam(f_id, BinderInfo::Default, bool_fn_n, e);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    const LEMMAS: &[&str] = &[
        "BoolAnalysis.sum_cube_le_eps_sq_mul_sum",
        "BoolAnalysis.kkl_sum_cube_influence_le",
    ];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_kkl_cubecharge()
            .expect("init_boolean_analysis_kkl_cubecharge");
        env.init_boolean_analysis_kkl_cubecharge()
            .expect("idempotent");
        env
    }

    #[test]
    fn test_kkl_cubecharge_all_constructive_theorems() {
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

    /// THE TARGET-REFUTATION GATE (sharp-KKL rule). `refute_conjecture` must NOT
    /// refute either bound. Both are TRUE conditional inequalities whose truth
    /// DEPENDS on the small-`g` / small-influence hypothesis carried in the Pi
    /// type (an UNCONDITIONAL `Σ g³ ≤ ε²·Σ g` is FALSE — the dictator `χ_i` has
    /// `Σ Inf³ = 1 > ε² = ε²·I[f]` for `ε < 1`; the same refute-trap that killed
    /// the false R4/R6).
    ///
    /// HONESTY NOTE on coverage (identical to `kkl_sum_sq_influence_le`'s):
    /// `refute_conjecture` walks leading Pi binders with concrete batteries and
    /// bails (`None`) at the higher-order binder `g : Fin n → Rat` / the
    /// universally-quantified `∀ i, …` hypotheses it cannot instantiate. `None`
    /// here is the correct, expected verdict (no counterexample); the
    /// load-bearing soundness is the kernel-checked proof plus the structural
    /// presence of the conditional hypothesis, NOT a deep battery sweep. The
    /// TRIBES case (the witness the `n ≤ 4` battery cannot construct) is checked
    /// BY HAND in the design note: tribes have all `Inf_i = δ ≤ ε`, so
    /// `Σ Inf³ = n·δ³ ≤ ε²·n·δ = ε²·I[f]` holds since `δ² ≤ ε²` — TRUE, no
    /// refutation, consistent with the kernel proof.
    #[test]
    fn test_kkl_cubecharge_not_refuted() {
        use super::super::carrier_refutation::refute_conjecture;
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in LEMMAS {
            let info = env.get_const(&Name::from_string(name)).expect("registered");
            assert_eq!(
                refute_conjecture(&tc, &info.type_),
                None,
                "{name} is a TRUE conditional inequality; it must NOT refute on the \
                 dictator/parity/constant battery"
            );
        }
    }
}
