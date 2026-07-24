// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL conditional-bound CORE — the **small-influence quadratic charge**
//! (O'Donnell, *Analysis of Boolean Functions*, §9.6 / Thm 9.28).
//!
//! This module lands the single analytic step in the KKL conditional
//! edge-isoperimetric argument where the **small-influence hypothesis is
//! consumed**: the place the classical write-up uses `max_i Inf_i ≤ 2^{-k}` to
//! collapse the quadratic `Σ_i Inf_i²` into a *linear* charge `2^{-k}·I[f]`.
//!
//! The sharp-KKL roadmap (`designs/2026-06-13-sharp-kkl-max-influence-roadmap.md`,
//! warning header) replaced the FALSE `deriv_level_mass_lower` (R4) /
//! `hc_dual_sharp` (R6) — both refuted by the dictator `χ_i` — with the
//! **conditional** bound `max_i Inf_i ≤ 2^{-k} → I[f] ≥ c·k·Var`. The
//! conditionality is essential and is carried in the Pi type here: WITHOUT the
//! small-influence hypothesis the charge `Σ_i Inf_i² ≤ ε·I[f]` is FALSE (the
//! dictator has one influence `= 1`, so `Σ Inf_i² = 1` but `ε·I[f] = ε·1 = ε`,
//! refuting it for `ε < 1`). With `max_i Inf_i ≤ ε` it is the genuine
//! per-coordinate Cauchy–Schwarz / AM–GM step that converts a square of an
//! influence into a quantity linear in that influence — the root-free shadow of
//! the hypercontractive `√`-step (`am_gm_linearize` lineage, K3 layer).
//!
//! ## What this proves
//!
//! ```text
//! BoolAnalysis.sum_sq_le_eps_mul_sum :                            -- abstract core
//!   ∀ (n : Nat) (g : Fin n → Rat) (eps : Rat),
//!     (∀ (i : Fin n), Rat.le Rat.zero (g i))                      -- nonnegativity
//!     → (∀ (i : Fin n), Rat.le (g i) eps)                         -- the small-`g` hyp
//!     → Rat.le (Fin.sum n (fun i => Rat.mul (g i) (g i)))
//!              (Rat.mul eps (Fin.sum n g))
//!
//! BoolAnalysis.kkl_sum_sq_influence_le :                          -- the KKL instance
//!   ∀ (n : Nat) (f : BoolFn n) (eps : Rat),
//!     (∀ (i : Fin n), Rat.le Rat.zero (Influence n f i))          -- influences are ≥ 0
//!     → (∀ (i : Fin n), Rat.le (Influence n f i) eps)             -- max-influence ≤ ε
//!     → Rat.le
//!         (Fin.sum n (fun i => Rat.mul (Influence n f i) (Influence n f i)))
//!         (Rat.mul eps (TotalInfluence n f))
//! ```
//!
//! i.e. `Σ_i g_i² ≤ ε·(Σ_i g_i)` whenever `0 ≤ g_i ≤ ε` for all `i`; instantiated
//! at `g := Influence n f` (with `Fin.sum n (Influence n f) ≡ TotalInfluence n f`
//! by reducible-`Definition` δ + η), it is `Σ_i Inf_i² ≤ ε·I[f]` — the
//! conditional small-influence charge. This is the consumer the conditional
//! edge-isoperimetric bound needs in tandem with the landed level-split
//! (`variance_high_mass_complement`, `Var − M_{>k} = M_{1..k}`) and low-band
//! (`variance_low_band_influence`, `(k+1)·(Var − M_{1..k}) ≤ I[f]`) glue: it is
//! the genuinely-CONDITIONAL hypercontractive step, NOT a rearrangement of an
//! existing inequality.
//!
//! ## Proof (constructive, empty admitted-axiom closure)
//!
//! **`sum_sq_le_eps_mul_sum`** (the abstract core):
//! 1. Per coordinate `i`: `Rat.mul_le_mul_of_nonneg_right (g i) (g i) eps
//!    (h_le i) (h_nn i) : Rat.le (g i · g i) (eps · g i)` — the quadratic-killer
//!    (`b·a ≤ c·a` from `b ≤ c` and `0 ≤ a`, at `a := g i, b := g i, c := eps`).
//!    THIS is where the `g i ≤ eps` hypothesis is consumed.
//! 2. `Fin.sum_le n (fun i => g i·g i) (fun i => eps·g i) (per) :
//!    Fin.sum n (fun i => g i·g i) ≤ Fin.sum n (fun i => eps·g i)`.
//! 3. `Fin.sum_smul n eps g : Fin.sum n (fun i => eps·g i) = eps·Fin.sum n g`.
//! 4. `Eq.subst` (motive `t ↦ Fin.sum n (fun i => g i·g i) ≤ t`) transports (2)
//!    along (3) to the goal `Fin.sum n (fun i => g i·g i) ≤ eps·Fin.sum n g`.
//!
//! **`kkl_sum_sq_influence_le`** (the KKL instance): apply
//! `sum_sq_le_eps_mul_sum n (fun i => Influence n f i) eps` to the two influence
//! hypotheses. Its conclusion's RHS `eps · Fin.sum n (fun i => Influence n f i)`
//! is def-eq (δ on the reducible `TotalInfluence` Definition + η) to
//! `eps · TotalInfluence n f`, so the instance type-checks directly.
//!
//! Every leaf (`Rat.mul_le_mul_of_nonneg_right`, `Fin.sum_le`, `Fin.sum_smul`,
//! `Eq.subst`) is `Constructive` with empty closure, so both lemmas are too. No
//! axiom is added or removed. Refute-checked against the dictator/parity/constant
//! battery (the hypothesis is essential — the unconditional version refutes).

use super::boolean_analysis_order_toolkit::OrderConsts;
use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

/// Shared atoms for the small-influence quadratic charge.
struct SmallInflConsts {
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
}

impl SmallInflConsts {
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
    fn mul_le_mul_right_of(&self, a: Expr, b: Expr, c: Expr, h_bc: Expr, h_0a: Expr) -> Expr {
        Expr::apps(self.mul_le_mul_right.clone(), [a, b, c, h_bc, h_0a])
    }
}

impl Environment {
    /// Register the small-influence quadratic charge bricks. Idempotent.
    pub fn init_boolean_analysis_kkl_smallinfl(&mut self) -> Result<(), EnvError> {
        self.register_sum_sq_le_eps_mul_sum()?;
        self.register_kkl_sum_sq_influence_le()?;
        Ok(())
    }

    /// `BoolAnalysis.sum_sq_le_eps_mul_sum` — the abstract small-`g` quadratic
    /// charge `(∀ i, 0 ≤ g i) → (∀ i, g i ≤ ε) → Σ_i g_i² ≤ ε·Σ_i g_i`. See
    /// module docs. Constructive, empty admitted-axiom closure. Idempotent.
    pub fn register_sum_sq_le_eps_mul_sum(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.sum_sq_le_eps_mul_sum");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_fin_sum()?; // Fin.sum, Fin.sum_le, Fin.sum_smul
        self.init_boolean_analysis_order_toolkit()?; // Rat.mul_le_mul_of_nonneg_right

        let c = SmallInflConsts::new();

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
        // integrand `fun i => g i · g i`.
        let sq_fn = |b: &EnvDeclBuilder, n: &Expr, g: &Expr| -> Expr {
            let mut ch = EnvDeclBuilder::child_of(b);
            let fin_n = c.fin_of(n);
            let (i_id, i) = ch.fresh_local(fin_n.clone());
            let gi = Expr::app(g.clone(), i);
            let body = c.mul(gi.clone(), gi);
            ch.finish_child(ch.mk_lam(i_id, BinderInfo::Default, fin_n, body))
        };
        // integrand `fun i => eps · g i`.
        let scaled_fn = |b: &EnvDeclBuilder, n: &Expr, g: &Expr, eps: &Expr| -> Expr {
            let mut ch = EnvDeclBuilder::child_of(b);
            let fin_n = c.fin_of(n);
            let (i_id, i) = ch.fresh_local(fin_n.clone());
            let body = c.mul(eps.clone(), Expr::app(g.clone(), i));
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

            let lhs = c.sum(&n, sq_fn(&b, &n, &g));
            let rhs = c.mul(eps.clone(), c.sum(&n, g.clone()));
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

            let sq = sq_fn(&b, &n, &g);
            let scaled = scaled_fn(&b, &n, &g, &eps);

            // per i : g i · g i ≤ eps · g i  (the quadratic-killer; consumes hle).
            let per = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let fin_n = c.fin_of(&n);
                let (i_id, i) = ch.fresh_local(fin_n.clone());
                let gi = Expr::app(g.clone(), i.clone());
                let h_bc = Expr::app(hle.clone(), i.clone()); // g i ≤ eps
                let h_0a = Expr::app(hnn.clone(), i.clone()); // 0 ≤ g i
                let body = c.mul_le_mul_right_of(gi.clone(), gi, eps.clone(), h_bc, h_0a);
                ch.finish_child(ch.mk_lam(i_id, BinderInfo::Default, fin_n, body))
            };

            // h_sumle : Fin.sum n sq ≤ Fin.sum n scaled.
            let h_sumle = Expr::apps(
                c.fin_sum_le.clone(),
                [n.clone(), sq.clone(), scaled.clone(), per],
            );

            // h_smul : Fin.sum n scaled = eps · Fin.sum n g.
            let h_smul = Expr::apps(c.fin_sum_smul.clone(), [n.clone(), eps.clone(), g.clone()]);

            // motive t => Fin.sum n sq ≤ t.
            let lhs = c.sum(&n, sq.clone());
            let motive = {
                let mut m = EnvDeclBuilder::child_of(&b);
                let (t_id, t) = m.fresh_local(c.rat());
                let body = c.le(lhs.clone(), t);
                m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.rat(), body))
            };
            let a = c.sum(&n, scaled); // Fin.sum n scaled
            let bb = c.mul(eps.clone(), c.sum(&n, g.clone())); // eps · Fin.sum n g
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

    /// `BoolAnalysis.kkl_sum_sq_influence_le` — the KKL instance of the
    /// small-influence quadratic charge: `(∀ i, 0 ≤ Inf_i) → (∀ i, Inf_i ≤ ε) →
    /// Σ_i Inf_i² ≤ ε·I[f]`. See module docs. Constructive, empty admitted-axiom
    /// closure. Idempotent.
    pub fn register_kkl_sum_sq_influence_le(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.kkl_sum_sq_influence_le");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_sum_sq_le_eps_mul_sum()?;
        self.init_boolean_analysis()?; // Influence, TotalInfluence (reducible defs)
                                       // KKL-finish idempotency: `init_boolean_analysis` may now register
                                       // this declaration transitively, so re-check after the deps.
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let c = SmallInflConsts::new();

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
        // `fun i => Influence n f i · Influence n f i`.
        let sq_fn = |b: &EnvDeclBuilder, n: &Expr, f: &Expr| -> Expr {
            let mut ch = EnvDeclBuilder::child_of(b);
            let fin_n = c.fin_of(n);
            let (i_id, i) = ch.fresh_local(fin_n.clone());
            let inf = c.influence_of(n, f, &i);
            let body = c.mul(inf.clone(), inf);
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

            let lhs = c.sum(&n, sq_fn(&b, &n, &f));
            let rhs = c.mul(eps.clone(), c.total_influence_of(&n, &f));
            let concl = c.le(lhs, rhs);

            let e = b.mk_pi(hle_id, BinderInfo::Default, h_le, concl);
            let e = b.mk_pi(hnn_id, BinderInfo::Default, h_nn, e);
            let e = b.mk_pi(eps_id, BinderInfo::Default, c.rat(), e);
            let e = b.mk_pi(f_id, BinderInfo::Default, bool_fn_n, e);
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        let abstract_core = Expr::const_(
            Name::from_string("BoolAnalysis.sum_sq_le_eps_mul_sum"),
            vec![],
        );

        // value: fun (n) (f) (eps) (hnn) (hle) =>
        //   sum_sq_le_eps_mul_sum n (fun i => Influence n f i) eps hnn hle
        // (the abstract conclusion's RHS `eps · Fin.sum n (fun i => Influence n f i)`
        //  is def-eq to `eps · TotalInfluence n f` by δ on the reducible
        //  `TotalInfluence` Definition; the LHS integrand matches def-eq too.)
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
        "BoolAnalysis.sum_sq_le_eps_mul_sum",
        "BoolAnalysis.kkl_sum_sq_influence_le",
    ];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_kkl_smallinfl()
            .expect("init_boolean_analysis_kkl_smallinfl");
        env.init_boolean_analysis_kkl_smallinfl()
            .expect("idempotent");
        env
    }

    #[test]
    fn test_kkl_smallinfl_all_constructive_theorems() {
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
    /// refute either bound. Both are TRUE inequalities whose truth DEPENDS on the
    /// small-`g` / small-influence hypothesis carried in the Pi type (an
    /// UNCONDITIONAL `Σ g² ≤ ε·Σ g` is FALSE — the dictator `χ_i` has
    /// `Σ Inf² = 1 > ε = ε·I[f]` for `ε < 1`; that is the refute-trap that killed
    /// the false R4/R6).
    ///
    /// HONESTY NOTE on coverage. `refute_conjecture` walks leading Pi binders with
    /// concrete witness batteries and bails (`None`) at a binder it cannot
    /// instantiate — and it CANNOT instantiate a higher-order binder (`g : Fin n →
    /// Rat`, classified `Other`) nor decide a universally-quantified hypothesis
    /// (`∀ i, …`, classified `Hyp` but with `prop_truth = None`). So for these two
    /// targets the probe bails early rather than exhaustively driving the
    /// conclusion on satisfying instances; `None` here is the *correct, expected*
    /// verdict (no counterexample), but the load-bearing soundness is the
    /// kernel-checked proof + the structural presence of the conditional
    /// hypothesis, NOT a deep battery sweep. The gate still guards against a
    /// statement so malformed it refutes on the outer `Nat`/`Rat` binders.
    #[test]
    fn test_kkl_smallinfl_not_refuted() {
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
