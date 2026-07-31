// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Friedgut SIZE bridge — `natCast(9^d)·natCast(9^d) = natCast(9^(2d))` (the
//! `dr²` square-of-9^d identity the C-thr SIZE division needs).
//!
//! `friedgut_low_budget_cancel` defines `dr := eps/(2·natCast(9^d)·K)`, so
//! `dr² = eps²/(4·natCast(9^d)²·K²)`. `friedgut_size_poly_bound` carries the
//! junta-size exponent as `natCast(9^(2d)) ≡ natCast(Nat.pow 9 (Nat.mul 2 d))`.
//! To cancel `dr²` against the size bound, the two `9^d` spellings must agree —
//! i.e. `natCast(9^d)² = natCast(9^(2d))`. This brick proves exactly that:
//!
//! ```text
//! BoolAnalysis.natCast_nine_pow_sq :
//!   ∀ (d : Nat),
//!     @Eq Rat
//!       (Rat.mul (natCast (Nat.pow 9 d)) (natCast (Nat.pow 9 d)))
//!       (natCast (Nat.pow 9 (Nat.mul 2 d)))
//! ```
//! where `natCast m ≡ Rat.mk (Int.ofNat m) 1`.
//!
//! ## Proof (constructive, hand-built `Expr`, EMPTY admitted-axiom closure)
//!
//! 1. `two_mul : Nat.mul 2 d = Nat.add d d`. Since `Nat.mul` recurses on its
//!    second argument and `2 ≡ succ (succ 0)`:
//!    - `Nat.succ_mul 1 d : Nat.mul 2 d = Nat.add d (Nat.mul 1 d)`;
//!    - `Nat.succ_mul 0 d : Nat.mul 1 d = Nat.add d (Nat.mul 0 d)`;
//!    - `Nat.zero_mul d : Nat.mul 0 d = 0`, then `Nat.add d 0 = d`
//!      (`Nat.add_zero`), so `Nat.mul 1 d = d`; congr through `Nat.add d ·`
//!      gives `Nat.mul 2 d = Nat.add d d`.
//! 2. `pow_add : Nat.pow 9 (Nat.add d d) = Nat.mul (Nat.pow 9 d) (Nat.pow 9 d)`
//!    (`Nat.pow_add 9 d d`).
//! 3. Chain in `Nat`: `Nat.pow 9 (Nat.mul 2 d) = Nat.pow 9 (Nat.add d d)`
//!    (`congrArg (Nat.pow 9 ·) two_mul`) `= Nat.mul (9^d) (9^d)` (`pow_add`).
//! 4. Lift to `Rat`: `natCast(9^(2d)) = natCast(Nat.mul (9^d) (9^d))`
//!    (`congrArg natCast` on step 3), and
//!    `Rat.ofNat_mul (9^d) (9^d) : natCast(Nat.mul (9^d) (9^d))
//!       = natCast(9^d)·natCast(9^d)` (`natCast ≡ Rat.ofNat` reducible).
//!    Compose + `Eq.symm` to land
//!    `natCast(9^d)·natCast(9^d) = natCast(9^(2d))`.
//!
//! Every leaf (`Nat.succ_mul`, `Nat.zero_mul`, `Nat.add_zero`, `Nat.pow_add`,
//! `Rat.ofNat_mul`, `Eq.refl/symm/trans/congrArg`) is a `Constructive`
//! empty-closure `Theorem`/built-in, so this bridge is too. NO axiom is added or
//! removed. NO `sorry` / `add_decl_unchecked` / `add_decl_structural` /
//! `native_decide` / `unsafe` / `Real`. Idempotent. Gated behind
//! `cfg(any(test, feature = "math-overlays"))`.

#![allow(clippy::too_many_arguments)]

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared atoms for the `natCast(9^d)²` bridge.
struct NineSqConsts {
    l1: Level,
    nat: Expr,
    rat: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nat_add: Expr,
    nat_mul: Expr,
    nat_pow: Expr,
    int_of_nat: Expr,
    rat_mk: Expr,
    rat_mul: Expr,
    succ_mul: Expr,
    zero_mul: Expr,
    add_zero: Expr,
    pow_add: Expr,
    ofnat_mul: Expr,
}

impl NineSqConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            l1,
            nat: k("Nat"),
            rat: k("Rat"),
            nat_zero: k("Nat.zero"),
            nat_succ: k("Nat.succ"),
            nat_add: k("Nat.add"),
            nat_mul: k("Nat.mul"),
            nat_pow: k("Nat.pow"),
            int_of_nat: k("Int.ofNat"),
            rat_mk: k("Rat.mk"),
            rat_mul: k("Rat.mul"),
            succ_mul: k("Nat.succ_mul"),
            zero_mul: k("Nat.zero_mul"),
            add_zero: k("Nat.add_zero"),
            pow_add: k("Nat.pow_add"),
            ofnat_mul: k("Rat.ofNat_mul"),
        }
    }

    fn nat_lit(&self, n: u32) -> Expr {
        let mut e = self.nat_zero.clone();
        for _ in 0..n {
            e = Expr::app(self.nat_succ.clone(), e);
        }
        e
    }
    fn nadd(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_add.clone(), [a, b])
    }
    fn nmul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_mul.clone(), [a, b])
    }
    fn npow(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_pow.clone(), [a, b])
    }
    /// `natCast m ≡ Rat.mk (Int.ofNat m) 1`.
    fn natcast(&self, m: Expr) -> Expr {
        Expr::apps(
            self.rat_mk.clone(),
            [Expr::app(self.int_of_nat.clone(), m), self.nat_lit(1)],
        )
    }
    fn rmul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    #[cfg(test)]
    fn eq_nat(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![self.l1.clone()]),
            [self.nat.clone(), a, b],
        )
    }
    fn eq_rat(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![self.l1.clone()]),
            [self.rat.clone(), a, b],
        )
    }
    #[cfg(test)]
    fn symm_nat(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.symm"), vec![self.l1.clone()]),
            [self.nat.clone(), a, b, h],
        )
    }
    fn symm_rat(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.symm"), vec![self.l1.clone()]),
            [self.rat.clone(), a, b, h],
        )
    }
    fn trans_nat(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.trans"), vec![self.l1.clone()]),
            [self.nat.clone(), a, b, cc, h1, h2],
        )
    }
    fn trans_rat(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.trans"), vec![self.l1.clone()]),
            [self.rat.clone(), a, b, cc, h1, h2],
        )
    }
    /// `congrArg.{1,1} Nat Nat a b g h`.
    fn congr_nn(&self, a: Expr, b: Expr, g: Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(
                Name::from_string("congrArg"),
                vec![self.l1.clone(), self.l1.clone()],
            ),
            [self.nat.clone(), self.nat.clone(), a, b, g, h],
        )
    }
    /// `congrArg.{1,1} Nat Rat a b g h`.
    fn congr_nr(&self, a: Expr, b: Expr, g: Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(
                Name::from_string("congrArg"),
                vec![self.l1.clone(), self.l1.clone()],
            ),
            [self.nat.clone(), self.rat.clone(), a, b, g, h],
        )
    }
}

fn build(c: &NineSqConsts, for_value: bool) -> Expr {
    let nine = c.nat_lit(9);
    let two = c.nat_lit(2);
    let one = c.nat_lit(1);
    let zero = c.nat_zero.clone();

    let mut b = EnvDeclBuilder::new();
    let (d_id, d) = b.fresh_local(c.nat.clone());

    let pow9_d = c.npow(nine.clone(), d.clone()); // 9^d
    let cast_pow9_d = c.natcast(pow9_d.clone()); // natCast(9^d)
    let lhs = c.rmul(cast_pow9_d.clone(), cast_pow9_d.clone()); // natCast(9^d)·natCast(9^d)
    let two_d = c.nmul(two.clone(), d.clone()); // 2·d
    let pow9_2d = c.npow(nine.clone(), two_d.clone()); // 9^(2d)
    let rhs = c.natcast(pow9_2d.clone()); // natCast(9^(2d))

    let concl = c.eq_rat(lhs.clone(), rhs.clone());

    if !for_value {
        return b.finish(b.mk_pi(d_id, BinderInfo::Default, c.nat.clone(), concl));
    }

    // ── Step 1: two_mul : Nat.mul 2 d = Nat.add d d. ──
    // sm1 : Nat.mul 2 d = Nat.add d (Nat.mul 1 d)   [Nat.succ_mul 1 d].
    let mul1_d = c.nmul(one.clone(), d.clone()); // Nat.mul 1 d
    let add_d_mul1d = c.nadd(d.clone(), mul1_d.clone());
    let sm1 = Expr::apps(c.succ_mul.clone(), [one.clone(), d.clone()]);
    // sm0 : Nat.mul 1 d = Nat.add d (Nat.mul 0 d)   [Nat.succ_mul 0 d].
    let mul0_d = c.nmul(zero.clone(), d.clone()); // Nat.mul 0 d
    let add_d_mul0d = c.nadd(d.clone(), mul0_d.clone());
    let sm0 = Expr::apps(c.succ_mul.clone(), [zero.clone(), d.clone()]);
    // zm : Nat.mul 0 d = 0   [Nat.zero_mul d].
    let zm = Expr::app(c.zero_mul.clone(), d.clone());
    // add_d_zm : Nat.add d (Nat.mul 0 d) = Nat.add d 0   [congr (Nat.add d ·) zm].
    let f_add_d = {
        let mut g = EnvDeclBuilder::child_of(&b);
        let (z_id, z) = g.fresh_local(c.nat.clone());
        let body = c.nadd(d.clone(), z);
        g.finish_child(g.mk_lam(z_id, BinderInfo::Default, c.nat.clone(), body))
    };
    let add_d_zero = c.nadd(d.clone(), zero.clone());
    let add_d_zm = c.congr_nn(mul0_d.clone(), zero.clone(), f_add_d.clone(), zm);
    // az : Nat.add d 0 = d   [Nat.add_zero d].
    let az = Expr::app(c.add_zero.clone(), d.clone());
    // mul1d_eq_d : Nat.mul 1 d = d.
    //   sm0 : mul1d = add d (mul0d) ; add_d_zm : add d (mul0d) = add d 0 ; az : add d 0 = d.
    let t01 = c.trans_nat(
        mul1_d.clone(),
        add_d_mul0d.clone(),
        add_d_zero.clone(),
        sm0,
        add_d_zm,
    );
    let mul1d_eq_d = c.trans_nat(mul1_d.clone(), add_d_zero.clone(), d.clone(), t01, az);
    // add_d_mul1d_eq_add_d_d : Nat.add d (Nat.mul 1 d) = Nat.add d d   [congr (Nat.add d ·)].
    let add_d_d = c.nadd(d.clone(), d.clone());
    let add_d_mul1d_eq = c.congr_nn(mul1_d.clone(), d.clone(), f_add_d, mul1d_eq_d);
    // two_mul : Nat.mul 2 d = Nat.add d d.
    //   sm1 : mul2d = add d (mul1d) ; add_d_mul1d_eq : add d (mul1d) = add d d.
    let two_mul = c.trans_nat(
        two_d.clone(),
        add_d_mul1d.clone(),
        add_d_d.clone(),
        sm1,
        add_d_mul1d_eq,
    );

    // ── Step 2: pow_add : Nat.pow 9 (Nat.add d d) = Nat.mul (9^d) (9^d). ──
    let pow_add = Expr::apps(c.pow_add.clone(), [nine.clone(), d.clone(), d.clone()]);
    let pow9_add_dd = c.npow(nine.clone(), add_d_d.clone()); // 9^(d+d)
    let mul_pow_pow = c.nmul(pow9_d.clone(), pow9_d.clone()); // (9^d)·(9^d)

    // ── Step 3: pow9_2d = Nat.mul (9^d) (9^d). ──
    // pow_congr : Nat.pow 9 (2·d) = Nat.pow 9 (d+d)   [congr (Nat.pow 9 ·) two_mul].
    let f_pow9 = {
        let mut g = EnvDeclBuilder::child_of(&b);
        let (z_id, z) = g.fresh_local(c.nat.clone());
        let body = c.npow(nine.clone(), z);
        g.finish_child(g.mk_lam(z_id, BinderInfo::Default, c.nat.clone(), body))
    };
    let pow_congr = c.congr_nn(two_d.clone(), add_d_d.clone(), f_pow9, two_mul);
    // pow9_2d_eq_mul : Nat.pow 9 (2·d) = Nat.mul (9^d) (9^d).
    let pow9_2d_eq_mul = c.trans_nat(
        pow9_2d.clone(),
        pow9_add_dd.clone(),
        mul_pow_pow.clone(),
        pow_congr,
        pow_add,
    );

    // ── Step 4: lift to Rat. ──
    // cast_congr : natCast(9^(2d)) = natCast(Nat.mul (9^d) (9^d))
    //   [congrArg natCast pow9_2d_eq_mul].
    let f_cast = {
        let mut g = EnvDeclBuilder::child_of(&b);
        let (z_id, z) = g.fresh_local(c.nat.clone());
        let body = c.natcast(z);
        g.finish_child(g.mk_lam(z_id, BinderInfo::Default, c.nat.clone(), body))
    };
    let cast_mul_pow = c.natcast(mul_pow_pow.clone()); // natCast(Nat.mul (9^d)(9^d))
    let cast_congr = c.congr_nr(pow9_2d.clone(), mul_pow_pow.clone(), f_cast, pow9_2d_eq_mul);
    // ofnat_mul : natCast(Nat.mul (9^d)(9^d)) = natCast(9^d)·natCast(9^d)
    //   [Rat.ofNat_mul (9^d) (9^d)].
    //   Rat.ofNat_mul m n : natCast(Nat.mul m n) = natCast m · natCast n
    //   (natCast ≡ Rat.ofNat reducible).
    let ofnm = Expr::apps(c.ofnat_mul.clone(), [pow9_d.clone(), pow9_d.clone()]);
    // rhs_eq_lhs : natCast(9^(2d)) = natCast(9^d)·natCast(9^d).
    let rhs_eq_lhs = c.trans_rat(
        rhs.clone(),
        cast_mul_pow.clone(),
        lhs.clone(),
        cast_congr,
        ofnm,
    );
    // body : lhs = rhs   [symm rhs_eq_lhs].
    let body = c.symm_rat(rhs.clone(), lhs.clone(), rhs_eq_lhs);

    b.finish(b.mk_lam(d_id, BinderInfo::Default, c.nat.clone(), body))
}

impl Environment {
    /// Register `BoolAnalysis.natCast_nine_pow_sq`:
    /// `∀ d, natCast(9^d)·natCast(9^d) = natCast(9^(2·d))`.
    /// Kernel-checked, `Constructive`, EMPTY admitted-axiom closure. Idempotent.
    pub fn register_natcast_nine_pow_sq(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.natCast_nine_pow_sq");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_nat()?;
        self.init_rat()?; // Rat, Rat.mk, Rat.mul, Int.ofNat
        self.register_nat_succ_mul_proof()?; // Nat.succ_mul
        self.register_nat_zero_mul_proof()?; // Nat.zero_mul
        self.register_nat_pow_add_proof()?; // Nat.pow_add
        self.register_rat_ofnat_mul()?; // Rat.ofNat_mul
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = NineSqConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build(&c, false),
            value: build(&c, true),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    #[test]
    fn test_natcast_nine_pow_sq_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.register_natcast_nine_pow_sq()
            .expect("register_natcast_nine_pow_sq");
        env.register_natcast_nine_pow_sq().expect("idempotent");
        let nm = Name::from_string("BoolAnalysis.natCast_nine_pow_sq");
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
