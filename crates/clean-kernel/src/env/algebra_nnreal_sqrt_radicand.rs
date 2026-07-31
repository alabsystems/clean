// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/sqrt layer — the QUANTITATIVE radicand ½-Hölder bound on the
//! dyadic-floor numerators (Stage C, Component A, radicand-difference rung).
//!
//! # Why this module exists
//!
//! The landed radicand machinery is single-radicand-QUALITATIVE: the floor
//! numerators are MONOTONE in the radicand (`Rat.dyadicNum_mono`,
//! `Rat.dyadicApprox_mono_radicand`) but there is NO QUANTITATIVE control on the
//! GAP `dyadicApprox(y,n) − dyadicApprox(x,n)` as a function of `y − x`. That gap
//! bound is the confirmed missing rung for lifting the literal
//! `NNReal.sqrt : NNReal → NNReal` over its radicand (the diagonal `Quot.lift`
//! needs `dyadicApprox` to be ½-Hölder IN ITS RADICAND, not just monotone).
//!
//! # The bound (subtraction-free, integer-numerator form)
//!
//! Write `b := dyadicNum x n`, `a := dyadicNum y n` (so `a_n(x) = b/2^n`,
//! `a_n(y) = a/2^n`). The landed squeeze pins each numerator:
//!
//! ```text
//!   LOWER at y (Rat.dyadicNum_sq_le):       (ofNat a)² ≤ y · 4^n
//!   UPPER at x (Rat.dyadicNum_sq_lt_succ):  x · 4^n   < (ofNat (a+1))²   -- at x: (ofNat(b+1))²
//! ```
//!
//! Adding the LOWER bound at `y` to (the `≤`-weakening of) the UPPER bound at `x`
//! gives the COMBINATORIAL radicand bound proved here:
//!
//! ```text
//!   Rat.dyadicNum_sq_le_radicand :
//!     0≤x → x≤y → y<1 → ∀ n,
//!       (ofNat a)·(ofNat a) + x·4^n  ≤  y·4^n + (ofNat (b+1))·(ofNat (b+1))
//! ```
//!
//! This is EXACTLY `a² − b² ≤ (y−x)·4^n + (2b+1)` rearranged subtraction-free
//! (`(ofNat(b+1))² = b² + (2b+1)`). Dividing by `4^n`, the slack `(2b+1)/4^n` is
//! `O(inv 2^n) → 0` (since `b ≤ 2^n`), so this IS the ½-Hölder radicand control
//! `a_n(y)² ≤ a_n(x)² + (y−x) + O(inv 2^n)`.
//!
//! # Non-circular / NO MASQUERADE
//!
//! The derivation uses ONLY the landed combinatorial squeeze bounds
//! (`Rat.dyadicNum_sq_le`, `Rat.dyadicNum_sq_lt_succ`) — it NEVER references the
//! exact square root `NNReal.sqrtRat`/`sqrtGen` being built. It is pure
//! `Nat`/`Rat` floor algebra. The two side-conditions `0≤y` and `x<1` (needed to
//! instantiate the landed bounds at `y` and at `x` respectively) are DERIVED from
//! the radicand hypotheses by `Rat.le_trans` / `Rat.lt_of_le_of_lt`.
//!
//! `Declaration::Theorem`, `ProofQuality::Constructive`, empty admitted-axiom
//! closure. NO `sorry` / `add_decl_unchecked` / `add_decl_structural`.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

/// Pre-resolved handles + smart-constructors for the radicand ½-Hölder bound.
pub(crate) struct RadicandConsts {
    nat: Expr,
    #[cfg(test)]
    nat_zero: Expr,
    nat_succ: Expr,
    rat: Expr,
    rat_zero: Expr,
    rat_one: Expr,
    rat_mul: Expr,
    rat_add: Expr,
    rat_le: Expr,
    rat_lt: Expr,
    rat_ofnat: Expr,
    rat_dyadic_num: Expr,
    rat_dyadic_pow4: Expr,
    rat_dyadic_num_sq_le: Expr,
    rat_dyadic_num_sq_lt_succ: Expr,
    rat_add_le_add: Expr,
    rat_le_trans: Expr,
    rat_lt_of_le_of_lt: Expr,
    rat_lt_iff: Expr,
    and_c: Expr,
    and_left: Expr,
    not_c: Expr,
    iff_mp: Expr,
}

impl RadicandConsts {
    pub(crate) fn new() -> Self {
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            #[cfg(test)]
            nat_zero: k("Nat.zero"),
            nat_succ: k("Nat.succ"),
            rat: k("Rat"),
            rat_zero: k("Rat.zero"),
            rat_one: k("Rat.one"),
            rat_mul: k("Rat.mul"),
            rat_add: k("Rat.add"),
            rat_le: k("Rat.le"),
            rat_lt: k("Rat.lt"),
            rat_ofnat: k("Rat.ofNat"),
            rat_dyadic_num: k("Rat.dyadicNum"),
            rat_dyadic_pow4: k("Rat.dyadicPow4"),
            rat_dyadic_num_sq_le: k("Rat.dyadicNum_sq_le"),
            rat_dyadic_num_sq_lt_succ: k("Rat.dyadicNum_sq_lt_succ"),
            rat_add_le_add: k("Rat.add_le_add"),
            rat_le_trans: k("Rat.le_trans"),
            rat_lt_of_le_of_lt: k("Rat.lt_of_le_of_lt"),
            rat_lt_iff: k("Rat.lt_iff_le_not_le"),
            and_c: k("And"),
            and_left: k("And.left"),
            not_c: k("Not"),
            iff_mp: k("Iff.mp"),
        }
    }

    // ── small constructors ──
    fn succ(&self, n: Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n)
    }
    fn rmul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn radd(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_add.clone(), [a, b])
    }
    fn rle(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_le.clone(), [a, b])
    }
    fn rlt(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_lt.clone(), [a, b])
    }
    fn ofnat(&self, n: Expr) -> Expr {
        Expr::app(self.rat_ofnat.clone(), n)
    }
    fn dnum(&self, x: &Expr, n: Expr) -> Expr {
        Expr::apps(self.rat_dyadic_num.clone(), [x.clone(), n])
    }
    fn pow4(&self, n: Expr) -> Expr {
        Expr::app(self.rat_dyadic_pow4.clone(), n)
    }
    /// `(ofNat m)² := Rat.mul (ofNat m)(ofNat m)`.
    fn sq_ofnat(&self, m: Expr) -> Expr {
        let r = self.ofnat(m);
        self.rmul(r.clone(), r)
    }
    /// `Rat.dyadicNum_sq_le x h0 n : (ofNat (dnum x n))² ≤ x·4^n`.
    fn dnum_sq_le(&self, x: &Expr, h0: Expr, n: Expr) -> Expr {
        Expr::apps(self.rat_dyadic_num_sq_le.clone(), [x.clone(), h0, n])
    }
    /// `Rat.dyadicNum_sq_lt_succ x h0 h1 n : x·4^n < (ofNat (succ (dnum x n)))²`.
    fn dnum_sq_lt_succ(&self, x: &Expr, h0: Expr, h1: Expr, n: Expr) -> Expr {
        Expr::apps(
            self.rat_dyadic_num_sq_lt_succ.clone(),
            [x.clone(), h0, h1, n],
        )
    }
    /// `Rat.add_le_add a b c d (a≤b)(c≤d) : (a+c) ≤ (b+d)`.
    fn add_le_add(&self, a: Expr, b: Expr, cc: Expr, d: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.rat_add_le_add.clone(), [a, b, cc, d, h1, h2])
    }
    /// `Rat.le_trans a b c (a≤b)(b≤c) : a ≤ c`.
    fn le_trans(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.rat_le_trans.clone(), [a, b, cc, h1, h2])
    }
    /// `Rat.lt_of_le_of_lt a b c (a≤b)(b<c) : a < c`.
    fn lt_of_le_of_lt(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.rat_lt_of_le_of_lt.clone(), [a, b, cc, h1, h2])
    }
    /// `a ≤ b` from `hlt : a < b` via `And.left (Iff.mp (lt_iff_le_not_le a b) hlt)`.
    fn le_of_lt(&self, a: Expr, b: Expr, hlt: Expr) -> Expr {
        let le_ab = self.rle(a.clone(), b.clone());
        let not_le = Expr::app(self.not_c.clone(), self.rle(b.clone(), a.clone()));
        let and_ty = Expr::apps(self.and_c.clone(), [le_ab.clone(), not_le.clone()]);
        let lt_ab = self.rlt(a.clone(), b.clone());
        let iff = Expr::apps(self.rat_lt_iff.clone(), [a, b]);
        let mp = Expr::apps(self.iff_mp.clone(), [lt_ab, and_ty, iff, hlt]);
        Expr::apps(self.and_left.clone(), [le_ab, not_le, mp])
    }
}

impl Environment {
    /// Register `Rat.dyadicNum_sq_le_radicand`. Idempotent; axiom-free.
    pub fn init_algebra_nnreal_sqrt_radicand(&mut self) -> Result<(), EnvError> {
        // dyadicNum_sq_le (LOWER) — pulls dyadicNum, dyadicPow4, ofNat.
        self.init_algebra_nnreal_sqrt_invariant()?;
        // dyadicNum_sq_lt_succ (UPPER).
        self.init_algebra_nnreal_sqrt_upper()?;
        // Rat.add_le_add.
        self.register_rat_add_le_add()?;
        // Rat.le_trans, Rat.lt_iff_le_not_le, Rat.lt_of_le_of_lt.
        self.init_rat_linear_order()?;
        self.init_boolean_analysis_order_toolkit_b1c()?; // lt_of_le_of_lt
        self.init_and()?;
        self.init_iff()?;

        let c = RadicandConsts::new();
        self.register_dyadic_num_sq_le_radicand(&c)
    }

    fn register_dyadic_num_sq_le_radicand(&mut self, c: &RadicandConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.dyadicNum_sq_le_radicand");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        // LHS(n) := (ofNat (dnum y n))² + x·4^n.
        // RHS(n) := y·4^n + (ofNat (succ (dnum x n)))².
        let lhs = |c: &RadicandConsts, x: &Expr, y: &Expr, n: &Expr| -> Expr {
            c.radd(
                c.sq_ofnat(c.dnum(y, n.clone())),
                c.rmul(x.clone(), c.pow4(n.clone())),
            )
        };
        let rhs = |c: &RadicandConsts, x: &Expr, y: &Expr, n: &Expr| -> Expr {
            c.radd(
                c.rmul(y.clone(), c.pow4(n.clone())),
                c.sq_ofnat(c.succ(c.dnum(x, n.clone()))),
            )
        };

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.rat.clone());
            let (y_id, y) = b.fresh_local(c.rat.clone());
            let h0_ty = c.rle(c.rat_zero.clone(), x.clone());
            let (h0_id, _h0) = b.fresh_local(h0_ty.clone());
            let hxy_ty = c.rle(x.clone(), y.clone());
            let (hxy_id, _hxy) = b.fresh_local(hxy_ty.clone());
            let hy1_ty = c.rlt(y.clone(), c.rat_one.clone());
            let (hy1_id, _hy1) = b.fresh_local(hy1_ty.clone());
            let inner = {
                let mut ib = EnvDeclBuilder::child_of(&b);
                let (n_id, n) = ib.fresh_local(c.nat.clone());
                let body = c.rle(lhs(c, &x, &y, &n), rhs(c, &x, &y, &n));
                ib.finish_child(ib.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), body))
            };
            let e = b.mk_pi(hy1_id, BinderInfo::Default, hy1_ty, inner);
            let e = b.mk_pi(hxy_id, BinderInfo::Default, hxy_ty, e);
            let e = b.mk_pi(h0_id, BinderInfo::Default, h0_ty, e);
            let e = b.mk_pi(y_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_pi(x_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.rat.clone());
            let (y_id, y) = b.fresh_local(c.rat.clone());
            let h0_ty = c.rle(c.rat_zero.clone(), x.clone());
            let (h0_id, h0) = b.fresh_local(h0_ty.clone());
            let hxy_ty = c.rle(x.clone(), y.clone());
            let (hxy_id, hxy) = b.fresh_local(hxy_ty.clone());
            let hy1_ty = c.rlt(y.clone(), c.rat_one.clone());
            let (hy1_id, hy1) = b.fresh_local(hy1_ty.clone());
            let (n_id, n) = b.fresh_local(c.nat.clone());

            // 0 ≤ y  := le_trans 0 x y h0 hxy.
            let h0y = c.le_trans(
                c.rat_zero.clone(),
                x.clone(),
                y.clone(),
                h0.clone(),
                hxy.clone(),
            );
            // x < 1  := lt_of_le_of_lt x y 1 hxy hy1.
            let hx1 = c.lt_of_le_of_lt(
                x.clone(),
                y.clone(),
                c.rat_one.clone(),
                hxy.clone(),
                hy1.clone(),
            );

            // Endpoint expressions.
            let a_sq = c.sq_ofnat(c.dnum(&y, n.clone())); // (ofNat a)²
            let x_pow = c.rmul(x.clone(), c.pow4(n.clone())); // x·4^n
            let y_pow = c.rmul(y.clone(), c.pow4(n.clone())); // y·4^n
            let b1_sq = c.sq_ofnat(c.succ(c.dnum(&x, n.clone()))); // (ofNat(b+1))²

            // hL : (ofNat a)² ≤ y·4^n   := dyadicNum_sq_le y h0y n.
            let h_lower = c.dnum_sq_le(&y, h0y, n.clone());
            // hU_lt : x·4^n < (ofNat(b+1))²   := dyadicNum_sq_lt_succ x h0 hx1 n.
            let h_upper_lt = c.dnum_sq_lt_succ(&x, h0.clone(), hx1, n.clone());
            // hU : x·4^n ≤ (ofNat(b+1))²   := le_of_lt.
            let h_upper = c.le_of_lt(x_pow.clone(), b1_sq.clone(), h_upper_lt);

            // add_le_add (a²) (y·4^n) (x·4^n) ((b+1)²) hL hU :
            //   ((ofNat a)² + x·4^n) ≤ (y·4^n + (ofNat(b+1))²).
            let body = c.add_le_add(a_sq, y_pow, x_pow, b1_sq, h_lower, h_upper);

            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), body);
            let e = b.mk_lam(hy1_id, BinderInfo::Default, hy1_ty, e);
            let e = b.mk_lam(hxy_id, BinderInfo::Default, hxy_ty, e);
            let e = b.mk_lam(h0_id, BinderInfo::Default, h0_ty, e);
            let e = b.mk_lam(y_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };

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

    const THEOREMS: &[&str] = &["Rat.dyadicNum_sq_le_radicand"];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_sqrt_radicand()
            .expect("init_algebra_nnreal_sqrt_radicand");
        env.init_algebra_nnreal_sqrt_radicand().expect("idempotent");
        env
    }

    #[test]
    fn test_dyadic_num_sq_le_radicand_kernel_checks() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in THEOREMS {
            let nm = Name::from_string(name);
            let info = env
                .get_const(&nm)
                .unwrap_or_else(|| panic!("{name} registered"));
            assert_eq!(info.kind, ConstantKind::Theorem, "{name} must be Theorem");
            let value = info.value.clone().expect("value present");
            tc.check_type(&value, &info.type_)
                .unwrap_or_else(|e| panic!("{name} must kernel-check: {e:?}"));
        }
    }

    #[test]
    fn test_dyadic_num_sq_le_radicand_constructive_empty_closure() {
        let env = env();
        for name in THEOREMS {
            let nm = Name::from_string(name);
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
    }
}
