// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `Rat.powNat` PRODUCT-BASE distributivity + base positivity — the two `powNat`
//! primitives the per-coordinate dual-HC `2^n`-bookkeeping pivots through.
//!
//! The `Rat.powNat` ladder already has `powNat_zero` / `powNat_succ` /
//! `powNat_add` (exponent-additivity, SAME base) and `powNat_nonneg`. The KKL
//! dual-HC normalization needs the orthogonal CROSS-base facts:
//!
//! ```text
//! Rat.powNat_mul_base : ∀ (a b : Rat) (k : Nat),
//!   Rat.powNat (Rat.mul a b) k = Rat.mul (Rat.powNat a k) (Rat.powNat b k)
//! Rat.powNat_pos      : ∀ (b : Rat) (k : Nat),
//!   Rat.lt Rat.zero b → Rat.lt Rat.zero (Rat.powNat b k)
//! ```
//!
//! i.e. `(a·b)^k = a^k·b^k` and `0 < b → 0 < b^k`. With these, `64^n = (8·8)^n =
//! 8^n·8^n = (8^n)²` and `8^n = (2·2·2)^n = (2^n)³` collapse, clearing the
//! `64^n` measure power so the squared dual-HC `W² ≤ 16·m³·8^n` cancels to the
//! sharp `W_norm² ≤ 16·Inf³`.
//!
//! ## Proofs (constructive, EMPTY admitted-axiom closure)
//!
//! - **`powNat_mul_base`** — `Nat.rec` on `k`, motive `λk. (a·b)^k = a^k·b^k`:
//!   * base `k=0`: goal ≡ `1 = 1·1`, closed by `Eq.symm (Rat.mul_one 1)`.
//!   * step `k+1`, ih `(a·b)^k = a^k·b^k`: goal ι-reduces to
//!     `(a·b)·(a·b)^k = (a·a^k)·(b·b^k)`. Chain
//!       (a·b)·(a·b)^k = (a·b)·(a^k·b^k)   congr (a·b)·_ ih
//!                     = (a·b)·(b^k·a^k)   congr (a·b)·_ (mul_comm a^k b^k)
//!                     = a·(b·(b^k·a^k))   mul_assoc a b (b^k·a^k)
//!                     = a·((b·b^k)·a^k)   congr a·_ (symm mul_assoc b b^k a^k)
//!                     = a·(a^k·(b·b^k))   congr a·_ (mul_comm (b·b^k) a^k)
//!                     = (a·a^k)·(b·b^k)   symm (mul_assoc a a^k (b·b^k)).
//! - **`powNat_pos`** — `Nat.rec` on `k`, motive `λk. 0 < b^k`:
//!   * base `k=0`: goal ≡ `0 < 1`, closed by `Rat.zero_lt_one`.
//!   * step `k+1`, ih `0 < b^k`: goal ι-reduces to `0 < b·b^k`, closed by
//!     `Rat.mul_pos b (b^k) hb ih`.
//!
//! Every leaf (`Rat.mul_one`, `Rat.mul_assoc`, `Rat.mul_comm`, `Rat.zero_lt_one`,
//! `Rat.mul_pos`, `Rat.powNat_succ` def-eq, `Nat.rec`, `Eq` built-ins) is
//! `Constructive` with empty closure, so both are too. No axiom added/removed.
//! Idempotent.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles + smart-constructors for the two `powNat` primitives.
struct PowMulConsts {
    nat: Expr,
    #[cfg(test)]
    nat_succ: Expr,
    #[cfg(test)]
    nat_zero: Expr,
    rat: Expr,
    rat_zero: Expr,
    rat_one: Expr,
    rat_mul: Expr,
    rat_lt: Expr,
    pow_nat: Expr,
    mul_one: Expr,
    mul_assoc: Expr,
    mul_comm: Expr,
    mul_pos: Expr,
    zero_lt_one: Expr,
    eq1: Expr,
    eq_symm1: Expr,
    eq_trans1: Expr,
    congr_arg1: Expr,
}

impl PowMulConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            #[cfg(test)]
            nat_succ: k("Nat.succ"),
            #[cfg(test)]
            nat_zero: k("Nat.zero"),
            rat: k("Rat"),
            rat_zero: k("Rat.zero"),
            rat_one: k("Rat.one"),
            rat_mul: k("Rat.mul"),
            rat_lt: k("Rat.lt"),
            pow_nat: k("Rat.powNat"),
            mul_one: k("Rat.mul_one"),
            mul_assoc: k("Rat.mul_assoc"),
            mul_comm: k("Rat.mul_comm"),
            mul_pos: k("Rat.mul_pos"),
            zero_lt_one: k("Rat.zero_lt_one"),
            eq1: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_symm1: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            eq_trans1: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            congr_arg1: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
        }
    }

    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn lt(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_lt.clone(), [a, b])
    }
    fn pow(&self, b: &Expr, k: &Expr) -> Expr {
        Expr::apps(self.pow_nat.clone(), [b.clone(), k.clone()])
    }
    #[cfg(test)]
    fn succ(&self, k: &Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), k.clone())
    }
    fn eq_rat(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.rat.clone(), a, b])
    }
    fn symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm1.clone(), [self.rat.clone(), a, b, h])
    }
    fn trans(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.eq_trans1.clone(), [self.rat.clone(), a, b, cc, h1, h2])
    }
    /// `Rat.mul_one a : a·1 = a`.
    fn mul_one_at(&self, a: Expr) -> Expr {
        Expr::app(self.mul_one.clone(), a)
    }
    /// `Rat.mul_assoc a b c : (a·b)·c = a·(b·c)`.
    fn assoc(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(self.mul_assoc.clone(), [a, b, cc])
    }
    /// `Rat.mul_comm a b : a·b = b·a`.
    fn comm(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.mul_comm.clone(), [a, b])
    }
    /// `congrArg (fun z => left·z) h : left·a = left·b`.
    fn congr_l(&self, parent: &EnvDeclBuilder, left: &Expr, a: Expr, b: Expr, h: Expr) -> Expr {
        let f = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = d.fresh_local(self.rat.clone());
            let body = self.mul(left.clone(), z);
            d.finish_child(d.mk_lam(z_id, BinderInfo::Default, self.rat.clone(), body))
        };
        Expr::apps(
            self.congr_arg1.clone(),
            [self.rat.clone(), self.rat.clone(), a, b, f, h],
        )
    }
}

impl Environment {
    /// Register `Rat.powNat_mul_base` and `Rat.powNat_pos`. Idempotent; both
    /// kernel-checked, `Constructive`, empty admitted-axiom closure.
    pub(crate) fn register_rat_pow_nat_mul_base(&mut self) -> Result<(), EnvError> {
        self.init_eq()?;
        self.register_rat_pow_nat()?; // Rat.powNat (+ powNat_succ def-eq)
        self.init_rat_arith()?;
        // `Rat.mul_one` / `Rat.mul_assoc` / `Rat.mul_comm` are the quotient
        // structural lemmas (idempotent; each guarded on its own name).
        {
            let qc = crate::env::algebra_rat_quotient::RatRawConsts::new();
            self.register_rat_q_structural(&qc)?;
        }
        self.register_rat_order_proofs()?; // Rat.zero_lt_one, Rat.mul_pos

        let c = PowMulConsts::new();
        self.register_pow_nat_mul_base_thm(&c)?;
        self.register_pow_nat_pos_thm(&c)?;
        Ok(())
    }

    fn register_pow_nat_mul_base_thm(&mut self, c: &PowMulConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.powNat_mul_base");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.rat.clone());
            let (bv_id, bv) = b.fresh_local(c.rat.clone());
            let (k_id, k) = b.fresh_local(c.nat.clone());
            let lhs = c.pow(&c.mul(a.clone(), bv.clone()), &k);
            let rhs = c.mul(c.pow(&a, &k), c.pow(&bv, &k));
            let concl = c.eq_rat(lhs, rhs);
            let e = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), concl);
            let e = b.mk_pi(bv_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };
        let value = build_mul_base_value(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    fn register_pow_nat_pos_thm(&mut self, c: &PowMulConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.powNat_pos");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (bv_id, bv) = b.fresh_local(c.rat.clone());
            let (k_id, k) = b.fresh_local(c.nat.clone());
            let hb_ty = c.lt(c.rat_zero.clone(), bv.clone());
            let (hb_id, _hb) = b.fresh_local(hb_ty.clone());
            let concl = c.lt(c.rat_zero.clone(), c.pow(&bv, &k));
            let e = b.mk_pi(hb_id, BinderInfo::Default, hb_ty, concl);
            let e = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(bv_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };
        let value = build_pos_value(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// `powNat_mul_base` proof: `fun a b => Nat.rec motive base step`.
fn build_mul_base_value(c: &PowMulConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.rat.clone());
    let (bv_id, bv) = b.fresh_local(c.rat.clone());

    let ab = c.mul(a.clone(), bv.clone());

    // motive : fun (k : Nat) => (a·b)^k = a^k·b^k
    let motive = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (k_id, k) = d.fresh_local(c.nat.clone());
        let body = c.eq_rat(c.pow(&ab, &k), c.mul(c.pow(&a, &k), c.pow(&bv, &k)));
        d.finish_child(d.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), body))
    };

    // base : (a·b)^0 = a^0·b^0   (def-eq to 1 = 1·1) := symm (mul_one 1).
    let base = {
        let one = c.rat_one.clone();
        let one_one = c.mul(one.clone(), one.clone());
        c.symm(one_one, one.clone(), c.mul_one_at(one))
    };

    // step : fun (k : Nat) (ih : (a·b)^k = a^k·b^k) => <chain>
    //   goal (succ k) ι-reduces to (a·b)·(a·b)^k = (a·a^k)·(b·b^k).
    let step = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (k_id, k) = d.fresh_local(c.nat.clone());
        let ih_ty = c.eq_rat(c.pow(&ab, &k), c.mul(c.pow(&a, &k), c.pow(&bv, &k)));
        let (ih_id, ih) = d.fresh_local(ih_ty.clone());

        let pak = c.pow(&a, &k);
        let pbk = c.pow(&bv, &k);
        let pabk = c.pow(&ab, &k);
        let pak_pbk = c.mul(pak.clone(), pbk.clone()); // a^k·b^k
        let pbk_pak = c.mul(pbk.clone(), pak.clone()); // b^k·a^k

        // t0 = (a·b)·(a·b)^k
        let t0 = c.mul(ab.clone(), pabk.clone());
        // t1 = (a·b)·(a^k·b^k)   congr (a·b)·_ ih
        let t1 = c.mul(ab.clone(), pak_pbk.clone());
        let s01 = c.congr_l(&d, &ab, pabk.clone(), pak_pbk.clone(), ih);
        // t2 = (a·b)·(b^k·a^k)   congr (a·b)·_ (mul_comm a^k b^k)
        let t2 = c.mul(ab.clone(), pbk_pak.clone());
        let s12 = c.congr_l(
            &d,
            &ab,
            pak_pbk.clone(),
            pbk_pak.clone(),
            c.comm(pak.clone(), pbk.clone()),
        );
        // t3 = a·(b·(b^k·a^k))   mul_assoc a b (b^k·a^k)
        let b_inner = c.mul(bv.clone(), pbk_pak.clone()); // b·(b^k·a^k)
        let t3 = c.mul(a.clone(), b_inner.clone());
        let s23 = c.assoc(a.clone(), bv.clone(), pbk_pak.clone());
        // t4 = a·((b·b^k)·a^k)   congr a·_ (symm (mul_assoc b b^k a^k))
        let b_pbk = c.mul(bv.clone(), pbk.clone()); // b·b^k
        let bpbk_pak = c.mul(b_pbk.clone(), pak.clone()); // (b·b^k)·a^k
        let assoc_b = c.assoc(bv.clone(), pbk.clone(), pak.clone()); // (b·b^k)·a^k = b·(b^k·a^k)
        let s34 = c.congr_l(
            &d,
            &a,
            b_inner.clone(),
            bpbk_pak.clone(),
            c.symm(bpbk_pak.clone(), b_inner.clone(), assoc_b),
        );
        let t4 = c.mul(a.clone(), bpbk_pak.clone());
        // t5 = a·(a^k·(b·b^k))   congr a·_ (mul_comm (b·b^k) a^k)
        let pak_bpbk = c.mul(pak.clone(), b_pbk.clone()); // a^k·(b·b^k)
        let s45 = c.congr_l(
            &d,
            &a,
            bpbk_pak.clone(),
            pak_bpbk.clone(),
            c.comm(b_pbk.clone(), pak.clone()),
        );
        let t5 = c.mul(a.clone(), pak_bpbk.clone());
        // t6 = (a·a^k)·(b·b^k)   symm (mul_assoc a a^k (b·b^k))
        let a_pak = c.mul(a.clone(), pak.clone()); // a·a^k
        let t6 = c.mul(a_pak.clone(), b_pbk.clone());
        let assoc_a = c.assoc(a.clone(), pak.clone(), b_pbk.clone()); // (a·a^k)·(b·b^k) = a·(a^k·(b·b^k))
        let s56 = c.symm(t6.clone(), t5.clone(), assoc_a); // t5 = t6

        // chain t0..t6.
        let ch = c.trans(t0.clone(), t1.clone(), t2.clone(), s01, s12);
        let ch = c.trans(t0.clone(), t2.clone(), t3.clone(), ch, s23);
        let ch = c.trans(t0.clone(), t3.clone(), t4.clone(), ch, s34);
        let ch = c.trans(t0.clone(), t4.clone(), t5.clone(), ch, s45);
        let proof = c.trans(t0, t5, t6, ch, s56);

        let r = d.mk_lam(ih_id, BinderInfo::Default, ih_ty, proof);
        d.finish_child(d.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), r))
    };

    let nat_rec = Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]);
    let body = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (k_id, k) = d.fresh_local(c.nat.clone());
        let rec_app = Expr::apps(nat_rec, [motive, base, step, k.clone()]);
        d.finish_child(d.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), rec_app))
    };
    let val = b.mk_lam(bv_id, BinderInfo::Default, c.rat.clone(), body);
    let val = b.mk_lam(a_id, BinderInfo::Default, c.rat.clone(), val);
    b.finish(val)
}

/// `powNat_pos` proof: `fun b k hb => Nat.rec motive base step k` (binder order
/// `b, k, hb` matches the type).
fn build_pos_value(c: &PowMulConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (bv_id, bv) = b.fresh_local(c.rat.clone());
    let (k_id, k_top) = b.fresh_local(c.nat.clone());
    let hb_ty = c.lt(c.rat_zero.clone(), bv.clone());
    let (hb_id, hb) = b.fresh_local(hb_ty.clone());

    // motive : fun (k : Nat) => 0 < b^k
    let motive = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (m_id, m) = d.fresh_local(c.nat.clone());
        let body = c.lt(c.rat_zero.clone(), c.pow(&bv, &m));
        d.finish_child(d.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), body))
    };

    // base : 0 < b^0   (def-eq to 0 < 1) := Rat.zero_lt_one.
    let base = c.zero_lt_one.clone();

    // step : fun (k : Nat) (ih : 0 < b^k) => Rat.mul_pos b (b^k) hb ih
    //   (goal (succ k) ι-reduces to 0 < b·b^k).
    let step = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (sk_id, sk) = d.fresh_local(c.nat.clone());
        let ih_ty = c.lt(c.rat_zero.clone(), c.pow(&bv, &sk));
        let (ih_id, ih) = d.fresh_local(ih_ty.clone());
        let pbk = c.pow(&bv, &sk);
        let body = Expr::apps(c.mul_pos.clone(), [bv.clone(), pbk, hb.clone(), ih]);
        let r = d.mk_lam(ih_id, BinderInfo::Default, ih_ty, body);
        d.finish_child(d.mk_lam(sk_id, BinderInfo::Default, c.nat.clone(), r))
    };

    let nat_rec = Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]);
    let rec_app = Expr::apps(nat_rec, [motive, base, step, k_top.clone()]);

    let val = b.mk_lam(hb_id, BinderInfo::Default, hb_ty, rec_app);
    let val = b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), val);
    let val = b.mk_lam(bv_id, BinderInfo::Default, c.rat.clone(), val);
    b.finish(val)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    const THEOREMS: &[&str] = &["Rat.powNat_mul_base", "Rat.powNat_pos"];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.register_rat_pow_nat_mul_base()
            .expect("register_rat_pow_nat_mul_base");
        env.register_rat_pow_nat_mul_base().expect("idempotent");
        env
    }

    #[test]
    fn test_pownat_mulbase_kernel_check() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in THEOREMS {
            let nm = Name::from_string(name);
            let info = env
                .get_const(&nm)
                .unwrap_or_else(|| panic!("{name} registered"));
            let value = info.value.clone().expect("value present");
            tc.check_type(&value, &info.type_)
                .unwrap_or_else(|e| panic!("{name} must kernel-check: {e:?}"));
        }
    }

    #[test]
    fn test_pownat_mulbase_constructive_empty_closure() {
        let env = env();
        for name in THEOREMS {
            let nm = Name::from_string(name);
            let info = env.get_const(&nm).expect("registered");
            assert_eq!(info.kind, ConstantKind::Theorem, "{name} must be Theorem");
            assert_eq!(
                env.proof_quality(&nm),
                Some(ProofQuality::Constructive),
                "{name} must be Constructive"
            );
            assert!(
                env.axiom_deps(&nm).expect("deps").is_empty(),
                "{name} closure must be empty: {:?}",
                env.axiom_deps(&nm)
            );
        }
    }
}
