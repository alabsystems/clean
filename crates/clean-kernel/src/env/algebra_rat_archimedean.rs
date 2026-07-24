// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/sqrt layer — Component (A): the `Rat` Archimedean primitive.
//!
//! # Why this module exists
//!
//! Every sqrt-convergence route in the NNReal layer (plan
//! `designs/2026-06-18-kkl-real-sqrt-layer-plan.md`, Stage B/B3) needs a `Nat`
//! convergence witness toward an irrational limit: for every `eps > 0` there is
//! a `Nat` `N` with `1/2^N < eps`. That is the Archimedean property of `Rat`
//! specialised to the dyadic modulus.
//!
//! This module builds the AXIOM-FREE supporting layer for that primitive: a
//! `Rat.ofNat` cast and the `Nat → Rat` Archimedean BRIDGE lemmas that lift the
//! existing pure-`Nat` two-power facts (`Nat.one_le_two_pow`,
//! `Nat.le_two_pow_self`) onto the live `Rat` carrier. Concretely:
//!
//! ```text
//! Rat.ofNat (n : Nat) : Rat := Rat.mk (Int.ofNat n) (Nat.succ Nat.zero)   -- (reducible Def)
//!
//! Rat.ofNat_le_ofNat_of_le :                                              -- natCast order lift
//!   ∀ (k m : Nat), Nat.le k m → Rat.le (Rat.ofNat k) (Rat.ofNat m)
//!
//! Rat.one_le_ofNat_two_pow :                                              -- 1 ≤ 2^N  (Rat)
//!   ∀ (N : Nat), Rat.le Rat.one (Rat.ofNat (Nat.pow 2 N))
//!
//! Rat.self_le_ofNat_two_pow :                                             -- N ≤ 2^N  (Rat)
//!   ∀ (N : Nat), Rat.le (Rat.ofNat N) (Rat.ofNat (Nat.pow 2 N))
//! ```
//!
//! Each is a checked `Declaration::Theorem`/`Definition` through `self.add_decl`;
//! every theorem's transitive admitted-axiom closure is empty (foundational
//! only). NO `sorry` / `add_decl_unchecked` / `add_decl_structural`.
//!
//! # The two-power bridge to `Rat`
//!
//! `Rat.le (Rat.ofNat k) (Rat.ofNat m)` unfolds (reducible `Rat.ofNat`, then the
//! `Rat.le` lift on the representatives `Rat.mk (ofNat k) 1`, `Rat.mk (ofNat m)
//! 1`, whose effective denominators reduce to `Nat.succ Nat.zero ≡ 1`) to the
//! `Int` inequality `Int.le (Int.mul (ofNat k) (ofNat 1)) (Int.mul (ofNat m)
//! (ofNat 1))`. We get the un-multiplied `Int.le (ofNat k) (ofNat m)` from
//! `Int.ofNat_le_ofNat_of_le` (the on-main natCast monotonicity, built from
//! `Nat.le.rec`, axiom-free) and transport it across `Int.mul_one` on both
//! operands — the exact pattern `Nat.cast_le_of_ble` uses. Composing with
//! `Nat.one_le_two_pow` / `Nat.le_two_pow_self` (both on-main, axiom-free)
//! yields the two-power bridges.
//!
//! See the run report for the remaining rung — the full
//! `Rat.exists_pow_inv_lt` witness — and its precise axiom-free blocker.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved constant handles + smart-constructors for the Archimedean
/// bridge. All operate on the live `Rat` carrier through the same `Rat.mk
/// (Int.ofNat ·) (Nat.succ Nat.zero)` natCast shape the KKL Nat-bridge uses.
struct ArchimedeanConsts {
    nat: Expr,
    int: Expr,
    rat: Expr,
    // natCast machinery.
    rat_mk: Expr,
    int_of_nat: Expr,
    int_mul: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nat_pow: Expr,
    rat_ofnat: Expr,
    rat_one: Expr,
    // Order surface (`Rat.le` written through `LE.le`/`instLERat`, matching the
    // KKL order toolkit so terms stay byte-identical).
    le_le: Expr,
    inst_le_rat: Expr,
    int_le: Expr,
    nat_le: Expr,
    // Bridge lemmas (each an on-main axiom-free Theorem).
    ofnat_le_ofnat_of_le: Expr,
    int_mul_one: Expr,
    one_le_two_pow: Expr,
    le_two_pow_self: Expr,
    rat_le_trans: Expr,
    // Eq.{1} / subst machinery.
    eq1: Expr,
    eq_symm: Expr,
    eq_subst: Expr,
}

impl ArchimedeanConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            int: k("Int"),
            rat: k("Rat"),
            rat_mk: k("Rat.mk"),
            int_of_nat: k("Int.ofNat"),
            int_mul: k("Int.mul"),
            nat_zero: k("Nat.zero"),
            nat_succ: k("Nat.succ"),
            nat_pow: k("Nat.pow"),
            rat_ofnat: k("Rat.ofNat"),
            rat_one: k("Rat.one"),
            le_le: Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
            inst_le_rat: k("instLERat"),
            int_le: k("Int.le"),
            nat_le: k("Nat.le"),
            ofnat_le_ofnat_of_le: k("Int.ofNat_le_ofNat_of_le"),
            int_mul_one: k("Int.mul_one"),
            one_le_two_pow: k("Nat.one_le_two_pow"),
            le_two_pow_self: k("Nat.le_two_pow_self"),
            rat_le_trans: k("Rat.le_trans"),
            eq1: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![l1]),
        }
    }

    // ── term constructors ────────────────────────────────────────────────────
    fn nat_one(&self) -> Expr {
        Expr::app(self.nat_succ.clone(), self.nat_zero.clone())
    }
    fn of_nat(&self, n: Expr) -> Expr {
        Expr::app(self.int_of_nat.clone(), n)
    }
    fn imul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.int_mul.clone(), [a, b])
    }
    /// `Rat.ofNat n` (the reducible cast, unfolds to `Rat.mk (ofNat n) 1`).
    fn rofnat(&self, n: Expr) -> Expr {
        Expr::app(self.rat_ofnat.clone(), n)
    }
    /// `Rat.mk (Int.ofNat n) (Nat.succ Nat.zero)` — the unfolded `Rat.ofNat n`.
    fn natcast(&self, n: Expr) -> Expr {
        Expr::apps(self.rat_mk.clone(), [self.of_nat(n), self.nat_one()])
    }
    /// `Nat.pow 2 n` (with `2 ≡ succ (succ zero)`).
    fn two_pow(&self, n: Expr) -> Expr {
        let two = Expr::app(self.nat_succ.clone(), self.nat_one());
        Expr::apps(self.nat_pow.clone(), [two, n])
    }
    /// `@LE.le Rat instLERat a b` — the surface `a ≤ b` the KKL toolkit uses.
    fn rat_le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(
            self.le_le.clone(),
            [self.rat.clone(), self.inst_le_rat.clone(), a, b],
        )
    }
    fn int_le_of(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.int_le.clone(), [a, b])
    }
    fn nle(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_le.clone(), [a, b])
    }
    /// `Int.mul_one a : Int.mul a (Int.ofNat 1) = a`.
    fn imul_one(&self, a: Expr) -> Expr {
        Expr::app(self.int_mul_one.clone(), a)
    }
    /// `@Eq.symm Int x y h : Eq Int y x`.
    fn symm_int(&self, x: Expr, y: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm.clone(), [self.int.clone(), x, y, h])
    }
    /// `@Eq.subst Int motive a b h_eq h_a`.
    fn subst_int(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h_a: Expr) -> Expr {
        Expr::apps(
            self.eq_subst.clone(),
            [self.int.clone(), motive, a, b, h_eq, h_a],
        )
    }
    /// `Rat.le_trans a b c h_ab h_bc : a ≤ c` (the toolkit `Rat.le_trans`,
    /// stated over the bare `Rat.le`; defeq to the `LE.le` surface).
    fn le_trans_of(&self, a: Expr, b: Expr, c: Expr, h_ab: Expr, h_bc: Expr) -> Expr {
        Expr::apps(self.rat_le_trans.clone(), [a, b, c, h_ab, h_bc])
    }
}

impl Environment {
    /// Register the KKL Archimedean supporting layer. Idempotent.
    ///
    /// Registers `Rat.ofNat` (Definition) and the bridge Theorems
    /// `Rat.ofNat_le_ofNat_of_le`, `Rat.one_le_ofNat_two_pow`,
    /// `Rat.self_le_ofNat_two_pow` — all constructive with empty admitted-axiom
    /// closure.
    pub fn init_algebra_rat_archimedean(&mut self) -> Result<(), EnvError> {
        self.register_rat_ofnat()?;
        self.register_rat_ofnat_le_ofnat_of_le()?;
        self.register_rat_one_le_ofnat_two_pow()?;
        self.register_rat_self_le_ofnat_two_pow()?;
        Ok(())
    }

    /// `Rat.ofNat (n : Nat) : Rat := Rat.mk (Int.ofNat n) (Nat.succ Nat.zero)`.
    ///
    /// Reducible `Declaration::Definition`; closure bottoms out in `Rat.mk` /
    /// `Int.ofNat`, so theorems over it stay `Constructive`. Defeq to the
    /// `Nat.succ Nat.zero`-denominator natCast the KKL Nat-bridge uses, so its
    /// `Rat.le` lift collapses the effective denominator to `Int.ofNat 1`.
    pub fn register_rat_ofnat(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.ofNat");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_rat()?; // Rat.mk, Int.ofNat

        let c = ArchimedeanConsts::new();
        let ty = Expr::pi(BinderInfo::Default, c.nat.clone(), c.rat.clone());
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let body = c.natcast(n);
            b.finish(b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), body))
        };
        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    /// `Rat.ofNat_le_ofNat_of_le :
    ///   ∀ (k m : Nat), Nat.le k m → Rat.le (Rat.ofNat k) (Rat.ofNat m)`.
    ///
    /// The natCast order lift. Constructive, empty admitted-axiom closure.
    ///
    /// Proof: `Int.ofNat_le_ofNat_of_le k m h : Int.le (ofNat k) (ofNat m)`,
    /// transported across `Int.mul_one` on both operands into the
    /// `Int.le (mul (ofNat k) 1) (mul (ofNat m) 1)` form, which is DEFEQ to
    /// `Rat.le (mk (ofNat k) 1) (mk (ofNat m) 1)` ≡ `Rat.le (ofNat k) (ofNat m)`
    /// (reducible `Rat.ofNat`). Mirrors `Nat.cast_le_of_ble`'s `step2`.
    pub fn register_rat_ofnat_le_ofnat_of_le(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.ofNat_le_ofNat_of_le");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.register_rat_ofnat()?;
        // `Int.ofNat_le_ofNat_of_le`, `Int.mul_one` (both via the Nat-bridge entry).
        self.register_nat_cast_le_of_ble()?;

        let c = ArchimedeanConsts::new();

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (k_id, k) = b.fresh_local(c.nat.clone());
            let (m_id, m) = b.fresh_local(c.nat.clone());
            let h_ty = c.nle(k.clone(), m.clone());
            let (h_id, _h) = b.fresh_local(h_ty.clone());
            let concl = c.rat_le(c.rofnat(k.clone()), c.rofnat(m.clone()));
            let e = b.mk_pi(h_id, BinderInfo::Default, h_ty, concl);
            let e = b.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (k_id, k) = b.fresh_local(c.nat.clone());
            let (m_id, m) = b.fresh_local(c.nat.clone());
            let h_ty = c.nle(k.clone(), m.clone());
            let (h_id, h) = b.fresh_local(h_ty.clone());

            let of_k = c.of_nat(k.clone());
            let of_m = c.of_nat(m.clone());
            let o1 = c.of_nat(c.nat_one());

            // h_int : Int.le (ofNat k) (ofNat m)
            let h_int = Expr::apps(
                c.ofnat_le_ofnat_of_le.clone(),
                [k.clone(), m.clone(), h.clone()],
            );

            let mul_k1 = c.imul(of_k.clone(), o1.clone());
            let mul_m1 = c.imul(of_m.clone(), o1.clone());

            // e_k : ofNat k = mul (ofNat k) 1  := symm (Int.mul_one (ofNat k))
            let e_k = c.symm_int(mul_k1.clone(), of_k.clone(), c.imul_one(of_k.clone()));
            // e_m : ofNat m = mul (ofNat m) 1  := symm (Int.mul_one (ofNat m))
            let e_m = c.symm_int(mul_m1.clone(), of_m.clone(), c.imul_one(of_m.clone()));

            // subst the left operand: motive_left x := Int.le x (ofNat m)
            let motive_left = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (x_id, x) = d.fresh_local(c.int.clone());
                let body = c.int_le_of(x, of_m.clone());
                d.finish_child(d.mk_lam(x_id, BinderInfo::Default, c.int.clone(), body))
            };
            // step1 : Int.le (mul (ofNat k) 1) (ofNat m)
            let step1 = c.subst_int(motive_left, of_k.clone(), mul_k1.clone(), e_k, h_int);

            // subst the right operand: motive_right y := Int.le (mul (ofNat k) 1) y
            let motive_right = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (y_id, y) = d.fresh_local(c.int.clone());
                let body = c.int_le_of(mul_k1.clone(), y);
                d.finish_child(d.mk_lam(y_id, BinderInfo::Default, c.int.clone(), body))
            };
            // step2 : Int.le (mul (ofNat k) 1) (mul (ofNat m) 1)
            //   ≡ Rat.le (ofNat k) (ofNat m)  (reducible Rat.ofNat + Rat.le lift).
            let step2 = c.subst_int(motive_right, of_m.clone(), mul_m1.clone(), e_m, step1);

            let e = b.mk_lam(h_id, BinderInfo::Default, h_ty, step2);
            let e = b.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Rat.one_le_ofNat_two_pow :
    ///   ∀ (N : Nat), Rat.le Rat.one (Rat.ofNat (Nat.pow 2 N))`.
    ///
    /// Positivity of the dyadic modulus on `Rat`. Constructive, empty closure.
    ///
    /// Proof: `Nat.one_le_two_pow N : Nat.le 1 (Nat.pow 2 N)`, lifted by
    /// `Rat.ofNat_le_ofNat_of_le 1 (2^N)` to `Rat.le (Rat.ofNat 1) (Rat.ofNat
    /// (2^N))`. `Rat.ofNat 1 ≡ Rat.mk (ofNat 1) 1`, which is DEFEQ to `Rat.one
    /// ≡ Rat.mk (ofNat 1) 1` (both `Quot.mk` of the same raw class), so the
    /// conclusion retypes to `Rat.le Rat.one (Rat.ofNat (2^N))`.
    pub fn register_rat_one_le_ofnat_two_pow(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.one_le_ofNat_two_pow");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_rat_ofnat_le_ofnat_of_le()?;
        // `register_nat_le_two_pow_self` transitively registers `Nat.one_le_two_pow`
        // (via `register_expect_one_theorems`).
        self.register_nat_le_two_pow_self()?;

        let c = ArchimedeanConsts::new();

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let concl = c.rat_le(c.rat_one.clone(), c.rofnat(c.two_pow(n.clone())));
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), concl);
            b.finish(e)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let two_pow_n = c.two_pow(n.clone());
            // h_nat : Nat.le 1 (2^N)
            let h_nat = Expr::app(c.one_le_two_pow.clone(), n.clone());
            // lift : Rat.le (Rat.ofNat 1) (Rat.ofNat (2^N))
            //   ≡ Rat.le Rat.one (Rat.ofNat (2^N))  (Rat.ofNat 1 ≡ Rat.one defeq).
            let body = Expr::apps(
                Expr::const_(Name::from_string("Rat.ofNat_le_ofNat_of_le"), vec![]),
                [c.nat_one(), two_pow_n, h_nat],
            );
            b.finish(b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), body))
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Rat.self_le_ofNat_two_pow :
    ///   ∀ (N : Nat), Rat.le (Rat.ofNat N) (Rat.ofNat (Nat.pow 2 N))`.
    ///
    /// The `N ≤ 2^N` Archimedean bridge on `Rat` (the `2^N ≥ N+1`-flavoured rung
    /// the plan calls out). Constructive, empty closure.
    ///
    /// Proof: `Nat.le_two_pow_self N : Nat.le N (Nat.pow 2 N)`, lifted by
    /// `Rat.ofNat_le_ofNat_of_le N (2^N)`.
    pub fn register_rat_self_le_ofnat_two_pow(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.self_le_ofNat_two_pow");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_rat_ofnat_le_ofnat_of_le()?;
        self.register_nat_le_two_pow_self()?; // Nat.le_two_pow_self

        let c = ArchimedeanConsts::new();

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let concl = c.rat_le(c.rofnat(n.clone()), c.rofnat(c.two_pow(n.clone())));
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), concl);
            b.finish(e)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let two_pow_n = c.two_pow(n.clone());
            // h_nat : Nat.le N (2^N)
            let h_nat = Expr::app(c.le_two_pow_self.clone(), n.clone());
            let body = Expr::apps(
                Expr::const_(Name::from_string("Rat.ofNat_le_ofNat_of_le"), vec![]),
                [n.clone(), two_pow_n, h_nat],
            );
            b.finish(b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), body))
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

    const THEOREMS: &[&str] = &[
        "Rat.ofNat_le_ofNat_of_le",
        "Rat.one_le_ofNat_two_pow",
        "Rat.self_le_ofNat_two_pow",
    ];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis().expect("init_boolean_analysis"); // Nat-bridge deps
        env.init_algebra_rat_archimedean()
            .expect("init_algebra_rat_archimedean");
        env.init_algebra_rat_archimedean().expect("idempotent");
        env
    }

    #[test]
    fn test_rat_ofnat_is_reducible_definition() {
        let env = env();
        let info = env
            .get_const(&Name::from_string("Rat.ofNat"))
            .expect("Rat.ofNat registered");
        assert_eq!(
            info.kind,
            ConstantKind::Definition,
            "Rat.ofNat is a Definition"
        );
    }

    #[test]
    fn test_rat_archimedean_all_constructive_theorems() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in THEOREMS {
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
                "{name} closure must be empty (foundational-only), got {:?}",
                env.axiom_deps(&nm)
            );
        }
    }
}
