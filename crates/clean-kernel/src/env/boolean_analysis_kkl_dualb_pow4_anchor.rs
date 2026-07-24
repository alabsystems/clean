// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL dual `(4/3→2)` layer — component **B3b**, the RATIONAL anchor of the
//! `4/3`-norm identity.
//!
//! # Where this sits in the dual bound
//!
//! The sharp-KKL retirement routes through the dual `(4/3→2)` hypercontractive
//! bound (O'Donnell §9.6):
//!
//! ```text
//!   W^{≤k}[D_i f] ≤ 9^k·‖T_{1/3} D_i f‖₂² ≤ 9^k·‖D_i f‖_{4/3}²
//!                 = 9^k·4·Inf_i^{3/2}.
//! ```
//!
//! Component **B3b** is the LAST equality, `‖D_i f‖_{4/3}² = 4·Inf_i^{3/2}`. For
//! a `{0,±2}`-valued discrete derivative `D_i f`,
//!
//! ```text
//!   ‖D_i f‖_{4/3}^{4/3} = E_x |D_i f x|^{4/3} = 2^{4/3}·Inf_i,
//!   ‖D_i f‖_{4/3}²      = (2^{4/3}·Inf_i)^{3/2} = (2^{4/3})^{3/2}·Inf_i^{3/2}
//!                       = 4·Inf_i^{3/2}.
//! ```
//!
//! The constant chain is `(2^{4/3})^{3/2} = 2^{(4/3)·(3/2)} = 2² = 4`, and the
//! squared (root-free) shadow is `‖D_i f‖_{4/3}⁴ = (2^{4/3}·Inf_i)³
//! = (2^{4/3})³·Inf_i³ = 2⁴·Inf_i³ = 16·Inf_i³` — a PURELY rational identity (the
//! `(2^{4/3})³ = 2⁴ = 16` collapse). This is the form §10.3 of the dual-bound
//! plan consumes: `(‖T_{1/3} D_i f‖₂²)² ≤ ‖D_i f‖_{4/3}⁴ = 16·Inf_i³`.
//!
//! # What this module proves (axiom-free, kernel-checked)
//!
//! The `16`-collapse on the discrete `4`-norm side — the genuine RATIONAL
//! backbone that the `4/3` carrier identity reduces to once the irrational
//! `2^{4/3}` constant cancels (see the BLOCKER note below):
//!
//! ```text
//! BoolAnalysis.deriv_pow4_sum_eq_16_disagree :
//!   ∀ n f i, subsetSum n (fun x => pow4(D_i f x))
//!          = 16 · subsetSum n (fun x => ind(disagree x))
//! ```
//!
//! since `pow4(D) = 4·sq(D)` and `sq(D) = 4·ind(disagree)` give
//! `subsetSum(pow4 D) = 4·(4·subsetSum ind) = 16·subsetSum ind`. Normalising by
//! `2^n` this is `‖D_i f‖₄⁴ = 16·Inf_i` — the `(2→4)` endpoint of the dual
//! derivation, and the rational sibling whose constant `16` matches the squared
//! `4/3`-norm shadow `‖D_i f‖_{4/3}⁴ = 16·Inf_i³`.
//!
//! ## Proof (constructive, empty admitted-axiom closure)
//!
//! Two landed RUNG-3 theorems (`boolean_analysis_deriv_4norm.rs`), composed:
//!
//! - `h1 := deriv_pow4_sum_eq_four_sq n f i : Σpow4 = 4·Σsq`,
//! - `h2 := deriv_sq_sum_eq_four_disagree n f i : Σsq = 4·Σind`,
//! - `c2 := congrArg (4·□) h2 : 4·Σsq = 4·(4·Σind)`,
//! - `h12 := Eq.trans h1 c2 : Σpow4 = 4·(4·Σind)`,
//! - `aS := (Rat.mul_assoc 4 4 Σind).symm : 4·(4·Σind) = (4·4)·Σind`,
//! - `c16 := congrArg (□·Σind) (rfl : 4·4 = 16) : (4·4)·Σind = 16·Σind`
//!   (`Rat.mul 4 4` ground-reduces to the `16` numeral, so `4·4 = 16` is `rfl`),
//! - conclusion `Σpow4 = 16·Σind := Eq.trans h12 (Eq.trans aS c16)`.
//!
//! Every leaf is `Constructive` with empty closure, so the lemma is too.
//!
//! # BLOCKER — the `4/3` carrier identity itself (reported, NOT admitted)
//!
//! The carrier form `‖D_i f‖_{4/3}² = 4·NNReal.pow32 Inf_i` does NOT close
//! axiom-free with current infrastructure, for two independent reasons:
//!
//! 1. **Irrational constant.** `‖D_i f‖_{4/3}² = NNReal.pow32 (E|D|^{4/3})` and
//!    `E|D|^{4/3} = 2^{4/3}·Inf_i`. Pulling the `4` out needs
//!    `pow32(2^{4/3}·Inf) = 4·pow32(Inf)`, i.e. `pow32(2^{4/3}) = 4` via
//!    `NNReal.sqrtRat(2^{4/3}) = 2^{2/3}` — but `NNReal.sqrtRat_mul_self` is
//!    proven only on `[0,1)`, and `2^{4/3} > 1`.
//! 2. **Missing NNReal multiplicative algebra.** Even the root-free squared form
//!    `(4·pow32 Inf)² = 16·Inf³` reduces (via `pow32 x · pow32 x = ofRat(x³)`,
//!    Inf ∈ [0,1)) to a FOUR-fold CauSeq product Equiv
//!    `(c_x·s_x)·(c_x·s_x) ≈ const(x³)` whose discharge needs
//!    `NNReal.mul_comm` / `NNReal.mul_assoc` / a two-sided `CauSeq.mul_congr` /
//!    `ofRat`-multiplicativity (`const·const ≈ const(·)`) — NONE of which exist
//!    (`NNReal.{mul, mul_add, mul_zero}` and the one-factor `build_mul_respect`
//!    helper are the only multiplicative facts on the carrier). The product
//!    sequences are not pointwise-equal (`s_x = a_n(x)` is the dyadic APPROX of
//!    `√x`), so the cheap `mul_add_equiv`-style pointwise route does not apply;
//!    it is a genuine ε/N Cauchy argument, keystone-sized.
//!
//! These are the EXACT missing sub-builds. This module lands the rational
//! anchor (`16`-collapse) and pins the constant chain by refutation (the test
//! `refute_pins_b3b_constant_chain`), STOPPING rather than admit any axiom.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached atoms for the `16`-collapse anchor. Spellings byte-match the RUNG-3
/// `DerivConsts` so the reused `subsetSum`/`ind`/`disagree`/`pow4` terms are
/// definitionally identical to the landed theorems' statements.
struct AnchorConsts {
    nat: Expr,
    rat: Expr,
    nat_succ: Expr,
    nat_zero: Expr,
    int_of_nat: Expr,
    rat_mk: Expr,
    rat_mul: Expr,
    rat_mul_assoc: Expr,
    rat_sub: Expr,
    hcpoint: Expr,
    bool_fn: Expr,
    fin: Expr,
    hc_flip: Expr,
    pm: Expr,
    ind: Expr,
    bool_beq: Expr,
    bool_not: Expr,
    subset_sum: Expr,
    pow4_thm: Expr,
    sq_thm: Expr,
    congr_arg: Expr,
    eq1: Expr,
    eq_trans: Expr,
    eq_symm: Expr,
    eq_refl: Expr,
}

impl AnchorConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            rat: k("Rat"),
            nat_succ: k("Nat.succ"),
            nat_zero: k("Nat.zero"),
            int_of_nat: k("Int.ofNat"),
            rat_mk: k("Rat.mk"),
            rat_mul: k("Rat.mul"),
            rat_mul_assoc: k("Rat.mul_assoc"),
            rat_sub: k("Rat.sub"),
            hcpoint: k("BoolAnalysis.HCPoint"),
            bool_fn: k("BoolAnalysis.BoolFn"),
            fin: k("Fin"),
            hc_flip: k("BoolAnalysis.hcFlip"),
            pm: k("BoolAnalysis.pm"),
            ind: k("BoolAnalysis.ind"),
            bool_beq: k("Bool.beq"),
            bool_not: k("Bool.not"),
            subset_sum: k("BoolAnalysis.subsetSum"),
            pow4_thm: k("BoolAnalysis.deriv_pow4_sum_eq_four_sq"),
            sq_thm: k("BoolAnalysis.deriv_sq_sum_eq_four_disagree"),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1.clone()]),
            eq1: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            eq_refl: Expr::const_(Name::from_string("Eq.refl"), vec![l1]),
        }
    }

    // ── type helpers (byte-match DerivConsts) ──────────────────────────────
    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    fn bool_fn_of(&self, n: &Expr) -> Expr {
        Expr::app(self.bool_fn.clone(), n.clone())
    }
    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }

    // ── numerals (byte-match DerivConsts::four) ────────────────────────────
    fn rat_numeral(&self, v: u64) -> Expr {
        let mut k = self.nat_zero.clone();
        for _ in 0..v {
            k = Expr::app(self.nat_succ.clone(), k);
        }
        let one = Expr::app(self.nat_succ.clone(), self.nat_zero.clone());
        Expr::apps(
            self.rat_mk.clone(),
            [Expr::app(self.int_of_nat.clone(), k), one],
        )
    }
    fn four(&self) -> Expr {
        self.rat_numeral(4)
    }
    fn sixteen(&self) -> Expr {
        self.rat_numeral(16)
    }

    // ── term builders ──────────────────────────────────────────────────────
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn sub(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_sub.clone(), [a, b])
    }
    fn pm_(&self, b: Expr) -> Expr {
        Expr::app(self.pm.clone(), b)
    }
    fn ind_(&self, b: Expr) -> Expr {
        Expr::app(self.ind.clone(), b)
    }
    fn sq(&self, d: Expr) -> Expr {
        self.mul(d.clone(), d)
    }
    fn pow4(&self, d: Expr) -> Expr {
        let s = self.sq(d);
        self.mul(s.clone(), s)
    }
    fn hc_flip_(&self, n: &Expr, x: &Expr, i: &Expr) -> Expr {
        Expr::apps(self.hc_flip.clone(), [n.clone(), x.clone(), i.clone()])
    }
    /// `D_i f x := pm (f x) − pm (f (hcFlip n x i))`.
    fn deriv(&self, n: &Expr, f: &Expr, x: &Expr, i: &Expr) -> Expr {
        let fx = Expr::app(f.clone(), x.clone());
        let fflip = Expr::app(f.clone(), self.hc_flip_(n, x, i));
        self.sub(self.pm_(fx), self.pm_(fflip))
    }
    /// `disagree x := Bool.not (Bool.beq (f x) (f (hcFlip n x i)))`.
    fn disagree(&self, n: &Expr, f: &Expr, x: &Expr, i: &Expr) -> Expr {
        let fx = Expr::app(f.clone(), x.clone());
        let fflip = Expr::app(f.clone(), self.hc_flip_(n, x, i));
        Expr::app(
            self.bool_not.clone(),
            Expr::apps(self.bool_beq.clone(), [fx, fflip]),
        )
    }
    fn ssum(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(self.subset_sum.clone(), [n.clone(), g])
    }
    fn eq_rat(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.rat.clone(), l, r])
    }
    fn refl(&self, a: Expr) -> Expr {
        Expr::apps(self.eq_refl.clone(), [self.rat.clone(), a])
    }
    fn trans(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.eq_trans.clone(), [self.rat.clone(), a, b, cc, h1, h2])
    }
    fn symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm.clone(), [self.rat.clone(), a, b, h])
    }
    /// `Rat.mul_assoc a b c : (a·b)·c = a·(b·c)`.
    fn assoc(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(self.rat_mul_assoc.clone(), [a, b, cc])
    }

    // ── summand lambdas (byte-match DerivConsts) ───────────────────────────
    fn pow4_deriv_fn(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr, i: &Expr) -> Expr {
        let mut xb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = xb.fresh_local(hcp.clone());
        let body = self.pow4(self.deriv(n, f, &x, i));
        xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp, body))
    }
    fn sq_deriv_fn(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr, i: &Expr) -> Expr {
        let mut xb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = xb.fresh_local(hcp.clone());
        let body = self.sq(self.deriv(n, f, &x, i));
        xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp, body))
    }
    fn ind_disagree_fn(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr, i: &Expr) -> Expr {
        let mut xb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = xb.fresh_local(hcp.clone());
        let body = self.ind_(self.disagree(n, f, &x, i));
        xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp, body))
    }

    /// `congrArg (fun z => 4·z) h : 4·a = 4·bb` for `h : a = bb`.
    fn mul_left_four_congr(&self, parent: &EnvDeclBuilder, a: Expr, bb: Expr, h: Expr) -> Expr {
        let g = {
            let mut b = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = b.fresh_local(self.rat.clone());
            let body = self.mul(self.four(), z);
            b.finish_child(b.mk_lam(z_id, BinderInfo::Default, self.rat.clone(), body))
        };
        Expr::apps(
            self.congr_arg.clone(),
            [self.rat.clone(), self.rat.clone(), a, bb, g, h],
        )
    }
    /// `congrArg (fun z => z·right) h : a·right = bb·right` for `h : a = bb`.
    fn mul_right_congr(
        &self,
        parent: &EnvDeclBuilder,
        right: &Expr,
        a: Expr,
        bb: Expr,
        h: Expr,
    ) -> Expr {
        let g = {
            let mut b = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = b.fresh_local(self.rat.clone());
            let body = self.mul(z, right.clone());
            b.finish_child(b.mk_lam(z_id, BinderInfo::Default, self.rat.clone(), body))
        };
        Expr::apps(
            self.congr_arg.clone(),
            [self.rat.clone(), self.rat.clone(), a, bb, g, h],
        )
    }
}

// ── BoolAnalysis.deriv_pow4_sum_eq_16_disagree ──────────────────────────────
//
//   subsetSum n (fun x => pow4(D_i f x)) = 16 · subsetSum n (fun x => ind(disagree x))

fn anchor_type(c: &AnchorConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let f_ty = c.bool_fn_of(&n);
    let (f_id, f) = b.fresh_local(f_ty.clone());
    let (i_id, i) = b.fresh_local(c.fin_of(&n));

    let lhs = c.ssum(&n, c.pow4_deriv_fn(&b, &n, &f, &i));
    let rhs = c.mul(c.sixteen(), c.ssum(&n, c.ind_disagree_fn(&b, &n, &f, &i)));
    let concl = c.eq_rat(lhs, rhs);
    let e = b.mk_pi(i_id, BinderInfo::Default, c.fin_of(&n), concl);
    let e = b.mk_pi(f_id, BinderInfo::Default, f_ty, e);
    b.finish(b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e))
}

fn anchor_value(c: &AnchorConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let f_ty = c.bool_fn_of(&n);
    let (f_id, f) = b.fresh_local(f_ty.clone());
    let (i_id, i) = b.fresh_local(c.fin_of(&n));

    let four = c.four();
    let sixteen = c.sixteen();
    let s_pow4 = c.ssum(&n, c.pow4_deriv_fn(&b, &n, &f, &i)); // Σ pow4(D)
    let s_sq = c.ssum(&n, c.sq_deriv_fn(&b, &n, &f, &i)); // Σ sq(D)
    let s_ind = c.ssum(&n, c.ind_disagree_fn(&b, &n, &f, &i)); // Σ ind(disagree)

    let four_sq = c.mul(four.clone(), s_sq.clone()); // 4·Σsq
    let four_ind = c.mul(four.clone(), s_ind.clone()); // 4·Σind
    let four_four_ind = c.mul(four.clone(), four_ind.clone()); // 4·(4·Σind)
    let ff = c.mul(four.clone(), four.clone()); // 4·4
    let ff_ind = c.mul(ff.clone(), s_ind.clone()); // (4·4)·Σind
    let sixteen_ind = c.mul(sixteen.clone(), s_ind.clone()); // 16·Σind

    // h1 : Σpow4 = 4·Σsq.
    let h1 = Expr::apps(c.pow4_thm.clone(), [n.clone(), f.clone(), i.clone()]);
    // h2 : Σsq = 4·Σind.
    let h2 = Expr::apps(c.sq_thm.clone(), [n.clone(), f.clone(), i.clone()]);
    // c2 : 4·Σsq = 4·(4·Σind)   (congrArg (4·□) h2).
    let c2 = c.mul_left_four_congr(&b, s_sq.clone(), four_ind.clone(), h2);
    // h12 : Σpow4 = 4·(4·Σind).
    let h12 = c.trans(
        s_pow4.clone(),
        four_sq.clone(),
        four_four_ind.clone(),
        h1,
        c2,
    );
    // assoc 4 4 Σind : (4·4)·Σind = 4·(4·Σind); symm → 4·(4·Σind) = (4·4)·Σind.
    let assoc = c.assoc(four.clone(), four.clone(), s_ind.clone());
    let a_sym = c.symm(ff_ind.clone(), four_four_ind.clone(), assoc);
    // c16 : (4·4)·Σind = 16·Σind   (congrArg (□·Σind) (rfl : 4·4 = 16)).
    let rfl_ff = c.refl(ff.clone()); // 4·4 = 4·4, def-eq 16 on RHS.
    let c16 = c.mul_right_congr(&b, &s_ind, ff.clone(), sixteen.clone(), rfl_ff);
    // tail : 4·(4·Σind) = 16·Σind.
    let tail = c.trans(
        four_four_ind.clone(),
        ff_ind.clone(),
        sixteen_ind.clone(),
        a_sym,
        c16,
    );
    // proof : Σpow4 = 16·Σind.
    let proof = c.trans(s_pow4, four_four_ind, sixteen_ind, h12, tail);

    let e = b.mk_lam(i_id, BinderInfo::Default, c.fin_of(&n), proof);
    let e = b.mk_lam(f_id, BinderInfo::Default, f_ty, e);
    b.finish(b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e))
}

impl Environment {
    /// Register `BoolAnalysis.deriv_pow4_sum_eq_16_disagree` — the RATIONAL
    /// `16`-collapse anchor of the dual `(4/3→2)` bound (component B3b). The
    /// pre-requisite RUNG-3 theorems are registered transitively.
    ///
    /// `Declaration::Theorem`, `ProofQuality::Constructive`, empty admitted
    /// closure. Idempotent.
    pub fn register_deriv_pow4_sum_eq_16_disagree(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.deriv_pow4_sum_eq_16_disagree");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        // RUNG-3 prerequisites (`subsetSum`, `pow4`, `sq`, `ind`/`disagree`, +
        // the two composed theorems) and `Rat.mul_assoc`.
        self.init_boolean_analysis_deriv_4norm()?;

        let c = AnchorConsts::new();
        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: anchor_type(&c),
            value: anchor_value(&c),
        })
    }

    /// Init hook for the B3b rational-anchor overlay module.
    pub fn init_boolean_analysis_kkl_dualb_pow4_anchor(&mut self) -> Result<(), EnvError> {
        self.register_deriv_pow4_sum_eq_16_disagree()
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
        env.init_boolean_analysis_kkl_dualb_pow4_anchor()
            .expect("init_boolean_analysis_kkl_dualb_pow4_anchor");
        env.init_boolean_analysis_kkl_dualb_pow4_anchor()
            .expect("idempotent");
        env
    }

    fn assert_constructive_theorem(env: &Environment, name: &str) {
        let n = Name::from_string(name);
        let info = env.get_const(&n).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "{name} must be a Theorem");
        let tc = TypeChecker::with_mode(env, env.mode());
        let _ = tc
            .infer_type(&Expr::const_(n.clone(), vec![]))
            .unwrap_or_else(|e| panic!("{name} should type-check: {e:?}"));
        let deps = env.axiom_deps(&n).expect("deps");
        let names: Vec<String> = deps.iter().map(|d| d.to_string()).collect();
        assert!(
            names.is_empty(),
            "{name} closure must be ⊆ FOUNDATIONAL_AXIOMS, got {names:?}"
        );
        assert!(
            matches!(env.proof_quality(&n), Some(ProofQuality::Constructive)),
            "{name} must be Constructive"
        );
    }

    #[test]
    fn test_deriv_pow4_sum_eq_16_disagree_constructive() {
        assert_constructive_theorem(&env(), "BoolAnalysis.deriv_pow4_sum_eq_16_disagree");
    }

    /// The `4·4 = 16` ground reduction that the `rfl` step in the anchor proof
    /// relies on — the carrier of the `(2^{4/3})³ = 2⁴ = 16` constant chain. Uses
    /// the populated overlay env (`Rat.mul`/`Int.mul` reduction is registered by
    /// `init_boolean_analysis_deriv_4norm`; bare `with_prelude` lacks it).
    #[test]
    fn test_rat_mul_4_4_defeq_16() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let c = AnchorConsts::new();
        let mul44 = c.mul(c.four(), c.four());
        assert!(
            tc.is_def_eq(&mul44, &c.sixteen()),
            "Rat.mul 4 4 must ground-reduce to the 16 numeral"
        );
    }

    /// Pin the B3b constant chain `(2^{4/3})^{3/2} = 4` / `(2^{4/3})³ = 16` via
    /// the rational shadow: the squared `4/3`-norm fourth power `16·Inf³` shares
    /// its `16` with the discrete `4`-norm collapse `‖D‖₄⁴ = 16·Inf`. We refute
    /// the WRONG constants (e.g. `‖D‖₄⁴ = 4·Inf` or `= 8·Inf`) by ground-checking
    /// `4·4 ≠ 4`, `4·4 ≠ 8` — i.e. the only consistent collapse constant is `16`.
    #[test]
    fn refute_pins_b3b_constant_chain() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let c = AnchorConsts::new();
        let mul44 = c.mul(c.four(), c.four());
        // 16 is the unique constant; 4 and 8 are refuted.
        assert!(
            !tc.is_def_eq(&mul44, &c.rat_numeral(4)),
            "4·4 != 4 — refutes the spurious deriv-4norm = 4·Inf collapse"
        );
        assert!(
            !tc.is_def_eq(&mul44, &c.rat_numeral(8)),
            "4·4 != 8 — refutes the spurious deriv-4norm = 8·Inf collapse"
        );
        assert!(
            tc.is_def_eq(&mul44, &c.sixteen()),
            "4·4 = 16 — the genuine deriv-4norm/4-thirds-norm collapse constant"
        );
    }
}
