// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL dual-HC — R2, the **rational 4th-power Hölder lemma** (the ONE new
//! lemma of the verified per-coordinate squared dual-HC route).
//!
//! ## What this proves
//!
//! The genuinely-new analytic brick of the dual-HC route is a rational
//! 4th-power Hölder inequality. For a discrete derivative `g ∈ {0,±2}` written
//! `g = 2·e` with `e ∈ {0,±1}` and support indicator `χ = e²` (so `e·χ = e`,
//! `χ·χ = χ`, and `m := Σ_x χ x = #{x : g x ≠ 0}`), and ANY weight `w`:
//!
//! ```text
//!   (Σ_x e·w)⁴  ≤  m³ · Σ_x w⁴
//! ```
//!
//! The irrational `2^{4/3}` of the textbook Hölder step never appears: the
//! fractional power COLLAPSES to integers because `g` is two-valued. (Downstream
//! the `{0,±2}` factor `(Σ g·w)⁴ = 16·(Σ e·w)⁴` supplies the constant `16`.)
//!
//! This module proves the abstract algebraic core, taking the two-valued
//! structure as EXPLICIT hypotheses so the proof is pure Cauchy–Schwarz
//! chaining (no Bool case-split, no support-set extraction):
//!
//! ```text
//! BoolAnalysis.sum_prod_pow4_le_m3_sumpow4 :
//!   ∀ (N : Nat) (e w chi : Fin N → Rat) (m : Rat),
//!     (∀ x, chi x = e x · e x)        -- H1: χ = e²
//!   → (∀ x, e x · chi x = e x)         -- H2: e·χ = e   (e³ = e)
//!   → (∀ x, chi x · chi x = chi x)     -- H3: χ² = χ    (idempotent)
//!   → (∀ x, chi x ≤ 1)                 -- H4: χ ≤ 1     (indicator bound)
//!   → 0 ≤ m                            -- H5: 0 ≤ m
//!   → m = Fin.sum N chi                -- H6: m = Σχ
//!   → Rat.le
//!       (pow4 (Fin.sum N (fun x => e x · w x)))
//!       (Rat.mul (Rat.mul m (Rat.mul m m))
//!                (Fin.sum N (fun x => pow4 (w x))))
//! ```
//!
//! where `pow4 t := (t·t)·(t·t)`. All six hypotheses are TRUE for the intended
//! `e = (D_i f)/2`, `χ = e²` (so they are not load-bearing in a vacuous way —
//! they specialise the abstract bound to the genuine instance), and the bound is
//! a sound consequence of finite Cauchy–Schwarz.
//!
//! ## Proof (constructive, EMPTY admitted-axiom closure)
//!
//! Let `P := Σ (e·w)`, `Q := Σ (χ·w)²`, `R := Σ (χ·w²)²`. Two applications of
//! the landed `Fin.sum_cauchy_schwarz` (`(Σ aᵢbᵢ)² ≤ (Σaᵢ²)(Σbᵢ²)`):
//!
//!   * **CS1** at `a := e`, `b := χ·w`. `Σ e·(χ·w) = Σ e·w = P` (H2, assoc);
//!     `Σ e² = Σ χ = m` (H1, H6); RHS-`b` leg is `Q`. ⇒ `P·P ≤ m·Q`.
//!   * **CS2** at `a := χ`, `b := χ·w²`. LHS `Σ χ·(χ·w²) = Q` (both equal
//!     `Σ (χ·χ)·(w·w)`, by `mul_mul_mul_comm`/`mul_assoc`); `Σ χ² = m` (H3, H6);
//!     RHS-`b` leg is `R`. ⇒ `Q·Q ≤ m·R`.
//!
//! Then `R = Σ (χ·w²)² ≤ Σ w⁴` (per `x`: `(χ·w²)² = χ·w⁴ ≤ 1·w⁴ = w⁴` via H3,
//! H4 and `w⁴ ≥ 0`; `Fin.sum_le`). Chaining with `0 ≤ P·P` (sq_nonneg),
//! `0 ≤ m·Q` (mul_nonneg, `Q ≥ 0` by `Fin.sum_nonneg`+`sq_nonneg`):
//!
//! ```text
//!   pow4 P = (P·P)·(P·P)
//!     ≤ (m·Q)·(m·Q)          [square the CS1 bound: two mul_le_mul_of_nonneg]
//!     = (m·m)·(Q·Q)          [mul_mul_mul_comm]
//!     ≤ (m·m)·(m·R)          [mul_le_left by CS2, 0 ≤ m·m]
//!     ≤ (m·m)·(m·Σw⁴)        [mul_le_left by R ≤ Σw⁴, 0 ≤ m·m, 0 ≤ m·R chain]
//!     = (m·(m·m))·Σw⁴        [regroup via mul_assoc/mul_comm]
//! ```
//!
//! Every leaf (`Fin.sum_cauchy_schwarz`, `Fin.sum_congr`, `Fin.sum_le`,
//! `Fin.sum_nonneg`, `Rat.mul_le_mul_of_nonneg_{left,right}`, `Rat.le_trans`,
//! `Rat.mul_nonneg`, `Rat.sq_nonneg`, `Rat.mul_assoc`/`_comm`/`mul_mul_mul_comm`,
//! `Rat.mul_one`, `Eq.subst`/`symm`/`trans`/`refl`) is `Constructive` with empty
//! closure, so this lemma is too. No axiom is added or removed.

#![allow(clippy::too_many_arguments)]

use super::boolean_analysis_order_toolkit::OrderConsts;
use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

/// Shared atoms for the rational 4th-power Hölder lemma.
struct HolderConsts {
    order: OrderConsts,
    nat: Expr,
    fin: Expr,
    fin_sum: Expr,
    fin_sum_le: Expr,
    fin_sum_congr: Expr,
    fin_sum_nonneg: Expr,
    cauchy_schwarz: Expr,
    mul_le_left: Expr,
    mul_le_right: Expr,
    le_trans: Expr,
    mul_nonneg: Expr,
    sq_nonneg: Expr,
    mul_assoc: Expr,
    mul_comm: Expr,
    mul_mul_mul_comm: Expr,
    mul_one: Expr,
    congr_arg: Expr,
}

impl HolderConsts {
    fn new() -> Self {
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            order: OrderConsts::new(),
            nat: k("Nat"),
            fin: k("Fin"),
            fin_sum: k("Fin.sum"),
            fin_sum_le: k("Fin.sum_le"),
            fin_sum_congr: k("Fin.sum_congr"),
            fin_sum_nonneg: k("Fin.sum_nonneg"),
            cauchy_schwarz: k("Fin.sum_cauchy_schwarz"),
            mul_le_left: k("Rat.mul_le_mul_of_nonneg_left"),
            mul_le_right: k("Rat.mul_le_mul_of_nonneg_right"),
            le_trans: k("Rat.le_trans"),
            mul_nonneg: k("Rat.mul_nonneg"),
            sq_nonneg: k("Rat.sq_nonneg"),
            mul_assoc: k("Rat.mul_assoc"),
            mul_comm: k("Rat.mul_comm"),
            mul_mul_mul_comm: k("Rat.mul_mul_mul_comm"),
            mul_one: k("Rat.mul_one"),
            congr_arg: Expr::const_(
                Name::from_string("congrArg"),
                vec![
                    crate::level::Level::succ(crate::level::Level::zero()),
                    crate::level::Level::succ(crate::level::Level::zero()),
                ],
            ),
        }
    }

    fn rat(&self) -> Expr {
        self.order.rat.clone()
    }
    fn zero(&self) -> Expr {
        self.order.rat_zero.clone()
    }
    fn one(&self) -> Expr {
        self.order.rat_one.clone()
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
    fn eq(&self, a: Expr, b: Expr) -> Expr {
        self.order.rat_eq(a, b)
    }
    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
    fn fin_to_rat(&self, n: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.fin_of(n), self.rat())
    }
    /// `Fin.sum N h`.
    fn sum(&self, n: &Expr, h: Expr) -> Expr {
        Expr::apps(self.fin_sum.clone(), [n.clone(), h])
    }
    /// `t·t`.
    fn sq(&self, t: Expr) -> Expr {
        self.mul(t.clone(), t)
    }
    /// `(t·t)·(t·t)`.
    fn pow4(&self, t: Expr) -> Expr {
        let s = self.sq(t);
        self.mul(s.clone(), s)
    }
    /// `Rat.mul_le_mul_of_nonneg_left a b c (h_bc:b≤c) (h_0a:0≤a) : a·b ≤ a·c`.
    fn mul_le_left(&self, a: Expr, b: Expr, c: Expr, h_bc: Expr, h_0a: Expr) -> Expr {
        Expr::apps(self.mul_le_left.clone(), [a, b, c, h_bc, h_0a])
    }
    /// `Rat.mul_le_mul_of_nonneg_right a b c (h_bc:b≤c) (h_0a:0≤a) : b·a ≤ c·a`.
    fn mul_le_right(&self, a: Expr, b: Expr, c: Expr, h_bc: Expr, h_0a: Expr) -> Expr {
        Expr::apps(self.mul_le_right.clone(), [a, b, c, h_bc, h_0a])
    }
    /// `Rat.le_trans a b c h_ab h_bc : a ≤ c`.
    fn le_trans(&self, a: Expr, b: Expr, c: Expr, h_ab: Expr, h_bc: Expr) -> Expr {
        Expr::apps(self.le_trans.clone(), [a, b, c, h_ab, h_bc])
    }
    /// `Rat.mul_nonneg a b ha hb : 0 ≤ a·b`.
    fn mul_nonneg(&self, a: Expr, b: Expr, ha: Expr, hb: Expr) -> Expr {
        Expr::apps(self.mul_nonneg.clone(), [a, b, ha, hb])
    }
    /// `Rat.sq_nonneg a : 0 ≤ a·a`.
    fn sq_nonneg(&self, a: Expr) -> Expr {
        Expr::app(self.sq_nonneg.clone(), a)
    }
    /// `Rat.mul_assoc a b c : (a·b)·c = a·(b·c)`.
    fn mul_assoc(&self, a: Expr, b: Expr, c: Expr) -> Expr {
        Expr::apps(self.mul_assoc.clone(), [a, b, c])
    }
    /// `Rat.mul_comm a b : a·b = b·a`.
    fn mul_comm(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.mul_comm.clone(), [a, b])
    }
    /// `Rat.mul_mul_mul_comm a b c d : (a·b)·(c·d) = (a·c)·(b·d)`.
    fn mul_mul_mul_comm(&self, a: Expr, b: Expr, c: Expr, d: Expr) -> Expr {
        Expr::apps(self.mul_mul_mul_comm.clone(), [a, b, c, d])
    }
    /// `Rat.mul_one a : a·1 = a`.
    fn mul_one(&self, a: Expr) -> Expr {
        Expr::app(self.mul_one.clone(), a)
    }
    /// `Fin.sum_congr N f g (pw : ∀ i, f i = g i) : Fin.sum N f = Fin.sum N g`.
    fn sum_congr(&self, n: &Expr, f: Expr, g: Expr, pw: Expr) -> Expr {
        Expr::apps(self.fin_sum_congr.clone(), [n.clone(), f, g, pw])
    }
    /// `Fin.sum_le N f g (per : ∀ i, f i ≤ g i) : Fin.sum N f ≤ Fin.sum N g`.
    fn sum_le(&self, n: &Expr, f: Expr, g: Expr, per: Expr) -> Expr {
        Expr::apps(self.fin_sum_le.clone(), [n.clone(), f, g, per])
    }
    /// `Fin.sum_nonneg N f (per : ∀ i, 0 ≤ f i) : 0 ≤ Fin.sum N f`.
    fn sum_nonneg(&self, n: &Expr, f: Expr, per: Expr) -> Expr {
        Expr::apps(self.fin_sum_nonneg.clone(), [n.clone(), f, per])
    }
    /// `Eq.symm`/`trans`/`subst` over `Rat`.
    fn symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        self.order.symm(a, b, h)
    }
    fn trans(&self, a: Expr, b: Expr, c: Expr, h1: Expr, h2: Expr) -> Expr {
        self.order.trans(a, b, c, h1, h2)
    }
    fn subst(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h_ma: Expr) -> Expr {
        self.order.subst(motive, a, b, h_eq, h_ma)
    }
    /// `@Eq.refl Rat x : x = x`.
    #[cfg(test)]
    #[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
    fn eq_refl(&self, x: Expr) -> Expr {
        Expr::apps(self.order.eq_refl.clone(), [self.rat(), x])
    }
    /// `congrArg.{1,1} Rat Rat a b f (h : a = b) : f a = f b`.
    fn congr_arg(&self, a: Expr, b: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(self.congr_arg.clone(), [self.rat(), self.rat(), a, b, f, h])
    }

    /// `Fin.sum_cauchy_schwarz N a b : (Σ a·b)·(Σ a·b) ≤ (Σ a·a)·(Σ b·b)`.
    fn cauchy(&self, n: &Expr, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.cauchy_schwarz.clone(), [n.clone(), a, b])
    }
}

impl Environment {
    /// Register the rational 4th-power Hölder lemma R2. Idempotent;
    /// kernel-checked, `Constructive`, empty domain-axiom closure.
    pub fn init_boolean_analysis_kkl_dualhc_holder(&mut self) -> Result<(), EnvError> {
        self.register_sum_prod_pow4_le_m3_sumpow4()?;
        Ok(())
    }

    /// `BoolAnalysis.sum_prod_pow4_le_m3_sumpow4` — R2, the rational 4th-power
    /// Hölder lemma. See the module docs for the statement and proof. Kernel-
    /// checked, `Constructive`, empty admitted-axiom closure. Idempotent.
    pub fn register_sum_prod_pow4_le_m3_sumpow4(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.sum_prod_pow4_le_m3_sumpow4");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_fin_sum()?; // Fin.sum, Fin.sum_le, Fin.sum_congr, Fin.sum_nonneg
        self.init_boolean_analysis_order_toolkit()?; // mul_le_mul_of_nonneg_*, sq_nonneg, mul_nonneg
        self.register_rat_le_trans_proof()?; // Rat.le_trans
        self.register_fin_sum_cauchy_schwarz_theorem()?; // Fin.sum_cauchy_schwarz
        self.init_rat()?; // Rat.mul_assoc, mul_comm, mul_one, mul_mul_mul_comm
        self.init_rat_field_inst()?; // Rat.mul_assoc / mul_mul_mul_comm surface

        let c = HolderConsts::new();
        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_holder(&c, false),
            value: build_holder(&c, true),
        })
    }
}

/// One per-`x` integrand `fun x => body(x)` over `Fin N → Rat`. The per-point
/// closure receives the CHILD builder `d` (which owns `x`) so any nested
/// binders it creates chain from `d` and get FVarIds disjoint from `x`'s. Using
/// the parent builder for nested binders would alias `x`'s id (both children
/// start at the same `next_fvar`) — the source of capture bugs.
fn lam_fn<F: Fn(&EnvDeclBuilder, &Expr) -> Expr>(
    c: &HolderConsts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    body: F,
) -> Expr {
    let mut d = EnvDeclBuilder::child_of(parent);
    let fin_n = c.fin_of(n);
    let (x_id, x) = d.fresh_local(fin_n.clone());
    let b = body(&d, &x);
    d.finish_child(d.mk_lam(x_id, BinderInfo::Default, fin_n, b))
}

/// A `∀ x : Fin N, P(x)` proof term `fun x => proof(x)`, or its type
/// `∀ x, P(x)` (when `as_pi`). The per-point closure receives the CHILD builder
/// `d` (which owns `x`) — see `lam_fn` for why this matters.
fn forall_x<F: Fn(&EnvDeclBuilder, &Expr) -> Expr>(
    c: &HolderConsts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    as_pi: bool,
    body: F,
) -> Expr {
    let mut d = EnvDeclBuilder::child_of(parent);
    let fin_n = c.fin_of(n);
    let (x_id, x) = d.fresh_local(fin_n.clone());
    let b = body(&d, &x);
    let e = if as_pi {
        d.mk_pi(x_id, BinderInfo::Default, fin_n, b)
    } else {
        d.mk_lam(x_id, BinderInfo::Default, fin_n, b)
    };
    d.finish_child(e)
}

/// Build the type (`for_value = false`) or the proof value (`for_value = true`)
/// of `sum_prod_pow4_le_m3_sumpow4`.
fn build_holder(c: &HolderConsts, for_value: bool) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let fty = c.fin_to_rat(&n);
    let (e_id, e) = b.fresh_local(fty.clone());
    let (w_id, w) = b.fresh_local(fty.clone());
    let (chi_id, chi) = b.fresh_local(fty.clone());
    let (m_id, m) = b.fresh_local(c.rat());

    // Pointwise atoms (closures over the bound local `x`).
    let e_of = |x: &Expr| Expr::app(e.clone(), x.clone());
    let w_of = |x: &Expr| Expr::app(w.clone(), x.clone());
    let chi_of = |x: &Expr| Expr::app(chi.clone(), x.clone());

    // ── Hypotheses (as Pi-types).
    // H1 : ∀ x, chi x = e x · e x
    let h1_ty = forall_x(c, &b, &n, true, |_d, x| {
        c.eq(chi_of(x), c.mul(e_of(x), e_of(x)))
    });
    // H2 : ∀ x, e x · chi x = e x
    let h2_ty = forall_x(c, &b, &n, true, |_d, x| {
        c.eq(c.mul(e_of(x), chi_of(x)), e_of(x))
    });
    // H3 : ∀ x, chi x · chi x = chi x
    let h3_ty = forall_x(c, &b, &n, true, |_d, x| {
        c.eq(c.mul(chi_of(x), chi_of(x)), chi_of(x))
    });
    // H4 : ∀ x, chi x ≤ 1
    let h4_ty = forall_x(c, &b, &n, true, |_d, x| c.le(chi_of(x), c.one()));
    // H5 : 0 ≤ m
    let h5_ty = c.le0(m.clone());
    // H6 : m = Fin.sum N chi
    let h6_ty = c.eq(m.clone(), c.sum(&n, chi.clone()));

    // ── Key integrands.
    let ew_fn = lam_fn(c, &b, &n, |_d, x| c.mul(e_of(x), w_of(x))); // x ↦ e·w
    let w4_fn = lam_fn(c, &b, &n, |_d, x| c.pow4(w_of(x))); // x ↦ w⁴

    // P := Σ (e·w), and the conclusion.
    let p = c.sum(&n, ew_fn.clone());
    let sum_w4 = c.sum(&n, w4_fn.clone());
    let m_sq = c.mul(m.clone(), m.clone()); // m·m
    let m_cube = c.mul(m.clone(), m_sq.clone()); // m·(m·m)
    let concl = c.le(c.pow4(p.clone()), c.mul(m_cube.clone(), sum_w4.clone()));

    // Bind hypotheses as locals.
    let (h1_id, h1) = b.fresh_local(h1_ty.clone());
    let (h2_id, h2) = b.fresh_local(h2_ty.clone());
    let (h3_id, h3) = b.fresh_local(h3_ty.clone());
    let (h4_id, h4) = b.fresh_local(h4_ty.clone());
    let (h5_id, h5) = b.fresh_local(h5_ty.clone());
    let (h6_id, h6) = b.fresh_local(h6_ty.clone());

    let tail = if for_value {
        build_holder_proof(
            c, &b, &n, &e, &w, &chi, &m, &p, &sum_w4, &m_sq, &m_cube, &ew_fn, &w4_fn, &h1, &h2,
            &h3, &h4, &h5, &h6,
        )
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
    let e_ = bind(&b, h6_id, h6_ty, tail);
    let e_ = bind(&b, h5_id, h5_ty, e_);
    let e_ = bind(&b, h4_id, h4_ty, e_);
    let e_ = bind(&b, h3_id, h3_ty, e_);
    let e_ = bind(&b, h2_id, h2_ty, e_);
    let e_ = bind(&b, h1_id, h1_ty, e_);
    let e_ = bind(&b, m_id, c.rat(), e_);
    let e_ = bind(&b, chi_id, fty.clone(), e_);
    let e_ = bind(&b, w_id, fty.clone(), e_);
    let e_ = bind(&b, e_id, fty, e_);
    let e_ = bind(&b, n_id, c.nat.clone(), e_);
    b.finish(e_)
}

// Proof-term builders (`build_holder_proof`, `build_holder_chain`) live in the
// sibling build file to keep each file under the 500-line convention.
include!("boolean_analysis_kkl_dualhc_holder_build.rs");

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_kkl_dualhc_holder()
            .expect("init_boolean_analysis_kkl_dualhc_holder");
        env.init_boolean_analysis_kkl_dualhc_holder()
            .expect("idempotent");
        env
    }

    /// R2 is a kernel-checked, `Constructive`, empty-closure Theorem.
    #[test]
    fn test_sum_prod_pow4_le_m3_sumpow4_is_constructive_theorem() {
        let env = env();
        let nm = Name::from_string("BoolAnalysis.sum_prod_pow4_le_m3_sumpow4");
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "must be Theorem");
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("must kernel-check: {e:?}"));
        assert_eq!(
            env.proof_quality(&nm),
            Some(ProofQuality::Constructive),
            "must be Constructive"
        );
        assert!(
            env.axiom_deps(&nm).expect("deps").is_empty(),
            "closure must be empty, got {:?}",
            env.axiom_deps(&nm)
                .expect("deps")
                .iter()
                .map(|d| d.to_string())
                .collect::<Vec<_>>()
        );
    }
}
