// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of the SIZE power comparison
//! `Nat.pow_nine_le_pow_two_eightfold :
//!     ∀ d : Nat, Nat.le (Nat.pow 9 (Nat.mul 2 d)) (Nat.pow 2 (Nat.mul 8 d))`,
//! i.e. `9^(2d) ≤ 2^(8d)`.
//!
//! This is the junta-SIZE bound's power inequality for the corrected-budget
//! (v3) Friedgut helper: with `d := 2^(e+2)`, the threshold junta has size
//! `K/dr² = 4·9^(2d)·K³/eps²`, and the `9^(2d)` factor must be dominated by a
//! pure power of two so the `48·2^e` budget exponent (`Nat.pow 2 (48·2^e)`) can
//! absorb it. Here `9^(2d) ≤ 2^(8d)` discharges exactly the `9^(2d) ≤ 16^(2d) =
//! 2^(8d)` step of the v3 SIZE derivation (see
//! `fourier_boolean_theorems.rs::friedgut_budget_v3`).
//!
//! # Why it is true (and not a third FALSE body)
//!
//! `9^(2d) = (9^2)^d = 81^d` and `2^(8d) = (2^8)^d = 256^d`. Since `81 ≤ 256`,
//! `81^d ≤ 256^d` for every `d ≥ 0` (monotonicity of `(·)^d`). At `d = 0` both
//! sides are `1`. There is NO dropped square here: the statement is a literal
//! power-of-base comparison with no `e`-dependent admissibility window, so it is
//! immune to the v1 (affine-budget, parity-junta) and v2 (dropped-`τ²`,
//! `9^d`-not-`9^(2d)`) errors that defeated the earlier helper bodies. The
//! `#[test] test_..._holds_numerically` cross-checks the closed form.
//!
//! # Proof term (hand-built `Expr`, NO tactics)
//!
//! Numerals `9`, `2`, `8` are the unary `Nat.succ^k Nat.zero` (matching the
//! `fourier_boolean_theorems.rs` numeral convention so the lemma composes by
//! defeq with the v3 body). Write
//! - `A  := Nat.pow 9 (Nat.mul 2 d)`,     `A' := Nat.pow (Nat.pow 9 2) d`
//! - `B  := Nat.pow 2 (Nat.mul 8 d)`,     `B' := Nat.pow (Nat.pow 2 8) d`
//!
//! Three landed constructive theorems supply the pieces:
//! - `e_lhs := Nat.pow_mul 9 2 d : Eq Nat A A'`   (`a^(m·n) = (a^m)^n`),
//! - `e_rhs := Nat.pow_mul 2 8 d : Eq Nat B B'`,
//! - `core  := Nat.pow_le_pow_left (Nat.pow 9 2) (Nat.pow 2 8) d h81
//!              : Nat.le A' B'`   (`a ≤ b → a^d ≤ b^d`),
//!   where `h81 := Nat.le_of_ble_eq_true (Nat.pow 9 2) (Nat.pow 2 8)
//!                   (@Eq.refl.{1} Bool Bool.true) : Nat.le (Nat.pow 9 2) (Nat.pow 2 8)`
//!   — the kernel reduces `Nat.ble (Nat.pow 9 2) (Nat.pow 2 8) ≡ Nat.ble 81 256 ≡ true`
//!   (delta on `Nat.pow`, iota on `Nat.ble`), so the `Eq.refl Bool true` typechecks.
//!
//! `core : Nat.le A' B'` is transported back to the goal `Nat.le A B` with two
//! `@Eq.subst.{1}` rewrites over `Nat` (motive `Nat → Prop`), each fed
//! `Eq.symm` of the `Nat.pow_mul` equation:
//! - subst₁: motive `λ x => Nat.le x B'`, along `Eq.symm e_lhs : A' = A`
//!   ⟹ `Nat.le A B'`;
//! - subst₂: motive `λ y => Nat.le A y`, along `Eq.symm e_rhs : B' = B`
//!   ⟹ `Nat.le A B`.
//!
//! # Axiom closure
//!
//! The proof term mentions only `Nat`, `Nat.zero`, `Nat.succ`, `Nat.pow`,
//! `Nat.mul`, `Nat.le`, `Bool`, `Bool.true`, `Eq`, `Eq.refl`, `Eq.symm`,
//! `Eq.subst`, and the constructive `Declaration::Theorem`s `Nat.pow_mul`,
//! `Nat.pow_le_pow_left`, `Nat.le_of_ble_eq_true`. None are
//! `Declaration::Axiom`, so `env.axiom_deps("Nat.pow_nine_le_pow_two_eightfold")`
//! is empty and the proof quality is `Constructive`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached kernel constants reused across type and value construction.
struct PowNineConsts {
    nat: Expr,
    nat_succ: Expr,
    nat_zero: Expr,
    pow: Expr,
    mul: Expr,
    le: Expr,
    /// `9` as the unary numeral `Nat.succ^9 Nat.zero`.
    nine: Expr,
    /// `2` as the unary numeral `Nat.succ^2 Nat.zero`.
    two: Expr,
    /// `8` as the unary numeral `Nat.succ^8 Nat.zero`.
    eight: Expr,
    bool_type: Expr,
    bool_true: Expr,
    eq_refl_bool: Expr,
    /// `@Eq.symm.{1}` — equalities over `Nat` (Sort 1).
    eq_symm: Expr,
    /// `@Eq.subst.{1}` — transport over `Nat` (Sort 1), motive `Nat → Prop`.
    eq_subst: Expr,
    pow_mul: Expr,
    pow_le_pow_left: Expr,
    le_of_ble_eq_true: Expr,
}

impl PowNineConsts {
    fn new() -> Self {
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let unary = |k: usize| -> Expr {
            let mut e = nat_zero.clone();
            for _ in 0..k {
                e = Expr::app(nat_succ.clone(), e);
            }
            e
        };
        let type1 = Level::succ(Level::zero());
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            pow: Expr::const_(Name::from_string("Nat.pow"), vec![]),
            mul: Expr::const_(Name::from_string("Nat.mul"), vec![]),
            le: Expr::const_(Name::from_string("Nat.le"), vec![]),
            nine: unary(9),
            two: unary(2),
            eight: unary(8),
            bool_type: Expr::const_(Name::from_string("Bool"), vec![]),
            bool_true: Expr::const_(Name::from_string("Bool.true"), vec![]),
            eq_refl_bool: Expr::const_(Name::from_string("Eq.refl"), vec![type1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![type1.clone()]),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![type1]),
            pow_mul: Expr::const_(Name::from_string("Nat.pow_mul"), vec![]),
            pow_le_pow_left: Expr::const_(Name::from_string("Nat.pow_le_pow_left"), vec![]),
            le_of_ble_eq_true: Expr::const_(Name::from_string("Nat.le_of_ble_eq_true"), vec![]),
            nat_succ,
            nat_zero,
        }
    }

    fn pow_of(&self, a: Expr, n: Expr) -> Expr {
        Expr::apps(self.pow.clone(), [a, n])
    }

    fn mul_of(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.mul.clone(), [x, y])
    }

    fn le_of(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.le.clone(), [x, y])
    }
}

/// Build `∀ d : Nat, Nat.le (Nat.pow 9 (Nat.mul 2 d)) (Nat.pow 2 (Nat.mul 8 d))`.
fn build_type(c: &PowNineConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (d_id, d) = b.fresh_local(c.nat.clone());
    let lhs = c.pow_of(c.nine.clone(), c.mul_of(c.two.clone(), d.clone()));
    let rhs = c.pow_of(c.two.clone(), c.mul_of(c.eight.clone(), d.clone()));
    let concl = c.le_of(lhs, rhs);
    let ty = b.mk_pi(d_id, BinderInfo::Default, c.nat.clone(), concl);
    b.finish(ty)
}

/// Body: `λ (d : Nat) => Eq.subst … (Eq.subst … core)`.
fn build_value(c: &PowNineConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (d_id, d) = b.fresh_local(c.nat.clone());

    // 9^2 and 2^8 (kept in `Nat.pow` form; defeq to 81 / 256).
    let pow_9_2 = c.pow_of(c.nine.clone(), c.two.clone());
    let pow_2_8 = c.pow_of(c.two.clone(), c.eight.clone());

    // A  = Nat.pow 9 (Nat.mul 2 d),  A' = Nat.pow (Nat.pow 9 2) d
    let a_lhs = c.pow_of(c.nine.clone(), c.mul_of(c.two.clone(), d.clone()));
    let a_prime = c.pow_of(pow_9_2.clone(), d.clone());
    // B  = Nat.pow 2 (Nat.mul 8 d),  B' = Nat.pow (Nat.pow 2 8) d
    let b_lhs = c.pow_of(c.two.clone(), c.mul_of(c.eight.clone(), d.clone()));
    let b_prime = c.pow_of(pow_2_8.clone(), d.clone());

    // h81 := Nat.le_of_ble_eq_true (9^2) (2^8) (@Eq.refl.{1} Bool Bool.true)
    //   : Nat.le (Nat.pow 9 2) (Nat.pow 2 8)
    // (kernel reduces Nat.ble (9^2) (2^8) ≡ Nat.ble 81 256 ≡ true).
    let refl_true = Expr::apps(
        c.eq_refl_bool.clone(),
        [c.bool_type.clone(), c.bool_true.clone()],
    );
    let h81 = Expr::apps(
        c.le_of_ble_eq_true.clone(),
        [pow_9_2.clone(), pow_2_8.clone(), refl_true],
    );

    // core := Nat.pow_le_pow_left (9^2) (2^8) d h81 : Nat.le A' B'
    let core = Expr::apps(
        c.pow_le_pow_left.clone(),
        [pow_9_2.clone(), pow_2_8.clone(), d.clone(), h81],
    );

    // e_lhs := Nat.pow_mul 9 2 d : Eq Nat A A'
    let e_lhs = Expr::apps(
        c.pow_mul.clone(),
        [c.nine.clone(), c.two.clone(), d.clone()],
    );
    // symm_lhs := Eq.symm Nat A A' e_lhs : Eq Nat A' A
    let symm_lhs = Expr::apps(
        c.eq_symm.clone(),
        [c.nat.clone(), a_lhs.clone(), a_prime.clone(), e_lhs],
    );

    // e_rhs := Nat.pow_mul 2 8 d : Eq Nat B B'
    let e_rhs = Expr::apps(
        c.pow_mul.clone(),
        [c.two.clone(), c.eight.clone(), d.clone()],
    );
    // symm_rhs := Eq.symm Nat B B' e_rhs : Eq Nat B' B
    let symm_rhs = Expr::apps(
        c.eq_symm.clone(),
        [c.nat.clone(), b_lhs.clone(), b_prime.clone(), e_rhs],
    );

    // subst₁: motive_x := λ (x : Nat) => Nat.le x B'
    //   @Eq.subst.{1} Nat motive_x A' A symm_lhs core : Nat.le A B'
    let motive_x = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (x_id, x) = mb.fresh_local(c.nat.clone());
        let body = c.le_of(x, b_prime.clone());
        let lam = mb.mk_lam(x_id, BinderInfo::Default, c.nat.clone(), body);
        mb.finish_child(lam)
    };
    let after_lhs = Expr::apps(
        c.eq_subst.clone(),
        [
            c.nat.clone(),
            motive_x,
            a_prime.clone(),
            a_lhs.clone(),
            symm_lhs,
            core,
        ],
    );

    // subst₂: motive_y := λ (y : Nat) => Nat.le A y
    //   @Eq.subst.{1} Nat motive_y B' B symm_rhs after_lhs : Nat.le A B
    let motive_y = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (y_id, y) = mb.fresh_local(c.nat.clone());
        let body = c.le_of(a_lhs.clone(), y);
        let lam = mb.mk_lam(y_id, BinderInfo::Default, c.nat.clone(), body);
        mb.finish_child(lam)
    };
    let goal = Expr::apps(
        c.eq_subst.clone(),
        [
            c.nat.clone(),
            motive_y,
            b_prime.clone(),
            b_lhs.clone(),
            symm_rhs,
            after_lhs,
        ],
    );

    let val = b.mk_lam(d_id, BinderInfo::Default, c.nat.clone(), goal);
    b.finish(val)
}

impl Environment {
    /// Register `Nat.pow_nine_le_pow_two_eightfold` as a kernel-checked
    /// `Declaration::Theorem`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_nat()` registered `Nat`, `Nat.zero`, `Nat.succ`,
    ///           `Nat.pow`, `Nat.mul`.
    /// REQUIRES: `self.init_le()` registered `Nat.le`.
    /// REQUIRES: `self.init_eq()` registered `Eq`, `Eq.refl`, `Eq.symm`,
    ///           `Eq.subst`.
    /// REQUIRES: `self.init_bool()` registered `Bool`, `Bool.true`.
    /// REQUIRES: `Nat.pow_mul`, `Nat.pow_le_pow_left`, `Nat.le_of_ble_eq_true`
    ///           are registered as constructive `Declaration::Theorem`s.
    /// ENSURES: On success, `Nat.pow_nine_le_pow_two_eightfold` is a
    ///          `Declaration::Theorem` with `proof_quality == Constructive`.
    /// ENSURES: Idempotent — if already registered with any declaration kind,
    ///          this returns `Ok(())` without modification.
    pub(crate) fn register_nat_pow_nine_le_pow_two_eightfold_proof(
        &mut self,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.pow_nine_le_pow_two_eightfold");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_nat()?;
        self.init_le()?;
        self.init_eq()?;
        self.init_bool()?;
        // Constructive dependencies (this lane).
        self.register_nat_pow_mul_proof()?;
        self.register_nat_pow_le_pow_left_proof()?;
        self.register_nat_ble_le_lemmas()?;

        let c = PowNineConsts::new();
        let type_ = build_type(&c);
        let value = build_value(&c);

        // SOUNDNESS: Real kernel-checked proof term. `9^(2d) ≤ 2^(8d)` is
        // proved by rewriting both exponents with the constructive
        // `Nat.pow_mul` (`a^(m·n) = (a^m)^n`) into `(9^2)^d` and `(2^8)^d`,
        // then `Nat.pow_le_pow_left (9^2) (2^8) d` with the base inequality
        // `9^2 ≤ 2^8` (i.e. `81 ≤ 256`) discharged by
        // `Nat.le_of_ble_eq_true (9^2) (2^8) (Eq.refl Bool true)` (the kernel
        // reduces `Nat.ble (9^2) (2^8) ≡ true`). The `Nat.le A' B'` witness is
        // transported back to the goal by two `Eq.subst` over `Nat` along the
        // `Eq.symm` of the two `Nat.pow_mul` equations. No `sorry`, no
        // self-reference, no domain-axiom dependency — all three consumed
        // theorems are themselves constructive.
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::{ConstantKind, ProofQuality};

    /// Sanity cross-check of the closed form `9^(2d) = 81^d ≤ 256^d = 2^(8d)`
    /// over a range of `d`. Guards against a third FALSE budget body.
    #[test]
    fn test_nat_pow_nine_le_pow_two_eightfold_holds_numerically() {
        // `2^(8d)` overflows `u128` once `8d > 127`, so cap `d` at 15
        // (`2^120 < 2^128`). The base comparison `9^2 = 81 ≤ 256 = 2^8` plus
        // monotonicity of `(·)^d` already gives the general statement; this
        // range just guards against an arithmetic typo in the exponents.
        for d in 0u32..=15 {
            let lhs: u128 = 9u128.pow(2 * d);
            let rhs: u128 = 2u128.pow(8 * d);
            assert!(lhs <= rhs, "9^(2·{d}) = {lhs} must be ≤ 2^(8·{d}) = {rhs}");
        }
    }

    /// Kernel accepts the `Eq.subst` / `Nat.pow_mul` / `Nat.pow_le_pow_left`
    /// proof term; the theorem is registered as a Theorem (not Axiom) and
    /// idempotent re-invocation is a no-op.
    #[test]
    fn test_nat_pow_nine_le_pow_two_eightfold_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_nat_pow_nine_le_pow_two_eightfold_proof()
            .expect("first registration");
        env.register_nat_pow_nine_le_pow_two_eightfold_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Nat.pow_nine_le_pow_two_eightfold"))
            .expect("Nat.pow_nine_le_pow_two_eightfold should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    /// Axiom closure is empty (constructive proof).
    #[test]
    fn test_nat_pow_nine_le_pow_two_eightfold_axiom_deps_empty() {
        let mut env = Environment::new();
        env.register_nat_pow_nine_le_pow_two_eightfold_proof()
            .unwrap();
        let deps = env
            .axiom_deps(&Name::from_string("Nat.pow_nine_le_pow_two_eightfold"))
            .expect("registered, axiom_deps should return Some");
        let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            domain_deps.is_empty(),
            "Nat.pow_nine_le_pow_two_eightfold must have empty axiom closure \
             (constructive proof), got {domain_deps:?}"
        );
    }

    /// Proof quality is `Constructive` (the `check_constructive` test).
    #[test]
    fn test_nat_pow_nine_le_pow_two_eightfold_proof_quality_constructive() {
        let mut env = Environment::new();
        env.register_nat_pow_nine_le_pow_two_eightfold_proof()
            .unwrap();
        let quality = env
            .proof_quality(&Name::from_string("Nat.pow_nine_le_pow_two_eightfold"))
            .expect("proof_quality should be reported");
        assert!(
            matches!(quality, ProofQuality::Constructive),
            "Nat.pow_nine_le_pow_two_eightfold must be Constructive, got {quality:?}"
        );
    }
}
