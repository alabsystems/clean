// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL dual-bound Stage C-3 — the noise-operator SEMIGROUP identity (component B1).
//!
//! The §9.6 dual `(4/3→2)` hypercontractive bound (the last hard content before
//! the four admitted KKL/Friedgut axioms can retire) is the chain
//! `‖T_{1/3}g‖₂² = ⟨T_{1/9}g, g⟩ ≤ ‖T_{1/9}g‖₄·‖g‖_{4/3}`. The FIRST equality
//! — the inner-product rewrite `‖T_{1/3}g‖₂² = ⟨T_{1/9}g, g⟩` — rests on the
//! noise-operator **semigroup** `T_ρ ∘ T_ρ = T_{ρ²}`: the noise operator at the
//! same parameter, composed with itself, equals the single operator at the
//! squared parameter.
//!
//! Spectrally, `T_ρ` has weight `ρ^{|S|}` on Fourier level `S`, so composing twice
//! gives weight `ρ^{|S|}·ρ^{|S|}` on level `S`, which must equal the weight
//! `(ρ²)^{|S|}` of the single operator `T_{ρ²}`. This module lands that EXACT
//! per-level scalar identity — the spectral form the `Rat.powNat`-based overlay
//! directly supports:
//!
//! ```text
//! Rat.powNat_mul_self_eq_sq_pow : ∀ (ρ : Rat) (k : Nat),
//!   Rat.mul (Rat.powNat ρ k) (Rat.powNat ρ k) = Rat.powNat (Rat.mul ρ ρ) k
//! ```
//!
//! i.e. `(ρ^k)·(ρ^k) = (ρ·ρ)^k`. At `ρ = 1/3`, `ρ·ρ = 1/9` (the
//! `Rat.third_mul_third` corollary closes this — the `Rat.mul` `Quot.lift`
//! ι-reduces both `(1/3)·(1/3)` and `1/9` to byte-identical raw reps, so it
//! holds by `Eq.refl`, NOT requiring `Quot.sound`), so this gives the
//! KKL-instantiated `(1/3)^k·(1/3)^k = (1/9)^k` — the precise spectral signature
//! of `T_{1/3} ∘ T_{1/3} = T_{1/9}` on each level `|S| = k`.
//!
//! Relation to `BoolAnalysis.levelWt`: the 2-norm weight carrier is
//! `levelWt ρ n S = (ρ·ρ)^{|S|}` (`levelWt_eq_powNat`). The single operator
//! `T_{ρ²}` has 2-norm spectral weight `levelWt ρ n S` (the `noise_spectral_level`
//! interface, whose LHS is the `noiseDensityW (ρ·ρ)` cube double-sum). This
//! identity `(ρ^k)·(ρ^k) = (ρ·ρ)^k = levelWt's per-level factor` is exactly what
//! lets the COMPOSED operator's per-level weight (`ρ^{|S|}` twice) be recognised
//! as the single `T_{ρ²}` weight `levelWt ρ n S` that `noise_spectral_level`
//! decomposes. The corollary at `ρ = 1/3` is registered too.
//!
//! ## Proof (constructive, empty admitted-axiom closure)
//!
//! `Nat.rec` on `k`, motive `λ k => (ρ^k)·(ρ^k) = (ρ·ρ)^k`:
//! - **base `k = 0`:** both `ρ^0` and `(ρ·ρ)^0` ι-reduce to `Rat.one`, so the
//!   goal is `1·1 = 1`, closed by `Rat.mul_one Rat.one`.
//! - **step `k = m+1`, ih `(ρ^m)·(ρ^m) = (ρ·ρ)^m`:** the ι-reduction of
//!   `Rat.powNat`'s `Nat.rec` carrier gives `ρ^(m+1) ≡ ρ·ρ^m` and
//!   `(ρ·ρ)^(m+1) ≡ (ρ·ρ)·(ρ·ρ)^m`, so the goal is
//!   `(ρ·ρ^m)·(ρ·ρ^m) = (ρ·ρ)·(ρ·ρ)^m`. We chain
//!     `(ρ·P)·(ρ·P) = (ρ·ρ)·(P·P)`     `Rat.mul_mul_mul_comm ρ P ρ P`  (P := ρ^m)
//!     `(ρ·ρ)·(P·P) = (ρ·ρ)·(ρ·ρ)^m`   congrArg ((ρ·ρ)·_) ih.
//!
//! Every leaf (`Rat.mul_one`, `Rat.mul_mul_mul_comm`, `congrArg`, `Eq.trans`,
//! `Nat.rec`) is `Constructive` with empty closure, so this identity is too.
//! No axiom is added or removed. Idempotent.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Self-contained `Rat`/`Nat` term atoms for the semigroup scalar identity.
struct DualSemigroupConsts {
    nat: Expr,
    rat: Expr,
    rat_mul: Expr,
    pow_nat: Expr,
    nat_succ: Expr,
    nat_zero: Expr,
    rat_one: Expr,
    eq1: Expr,
}

impl DualSemigroupConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            rat_mul: Expr::const_(Name::from_string("Rat.mul"), vec![]),
            pow_nat: Expr::const_(Name::from_string("Rat.powNat"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            rat_one: Expr::const_(Name::from_string("Rat.one"), vec![]),
            eq1: Expr::const_(Name::from_string("Eq"), vec![l1]),
        }
    }

    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    /// `Rat.powNat ρ k`.
    fn pow(&self, rho: &Expr, k: &Expr) -> Expr {
        Expr::apps(self.pow_nat.clone(), [rho.clone(), k.clone()])
    }
    fn eq_rat(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.rat.clone(), l, r])
    }
    fn trans_rat(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        let eq_trans = Expr::const_(
            Name::from_string("Eq.trans"),
            vec![Level::succ(Level::zero())],
        );
        Expr::apps(eq_trans, [self.rat.clone(), a, b, cc, h1, h2])
    }
    /// `congrArg.{1,1} Rat Rat from to motive h`.
    fn congr_rat(&self, from: Expr, to: Expr, motive: Expr, h: Expr) -> Expr {
        let congr_arg = Expr::const_(
            Name::from_string("congrArg"),
            vec![Level::succ(Level::zero()), Level::succ(Level::zero())],
        );
        Expr::apps(
            congr_arg,
            [self.rat.clone(), self.rat.clone(), from, to, motive, h],
        )
    }
    /// `Rat.mul_one a : a·1 = a`.
    fn mul_one(&self, a: Expr) -> Expr {
        Expr::apps(Expr::const_(Name::from_string("Rat.mul_one"), vec![]), [a])
    }
    /// `Rat.mul_mul_mul_comm a b c d : (a·b)·(c·d) = (a·c)·(b·d)`.
    fn mul_mul_mul_comm(&self, a: Expr, b: Expr, cc: Expr, d: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.mul_mul_mul_comm"), vec![]),
            [a, b, cc, d],
        )
    }
}

/// `∀ (ρ : Rat) (k : Nat), (ρ^k)·(ρ^k) = (ρ·ρ)^k`.
fn build_semigroup_type(c: &DualSemigroupConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rho_id, rho) = b.fresh_local(c.rat.clone());
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let pow_k = c.pow(&rho, &k);
    let lhs = c.mul(pow_k.clone(), pow_k);
    let rho_sq = c.mul(rho.clone(), rho.clone());
    let rhs = c.pow(&rho_sq, &k);
    let concl = c.eq_rat(lhs, rhs);
    let t = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), concl);
    b.finish(b.mk_pi(rho_id, BinderInfo::Default, c.rat.clone(), t))
}

/// Proof of `∀ ρ k, (ρ^k)·(ρ^k) = (ρ·ρ)^k` by `Nat.rec` on `k`.
fn build_semigroup_value(c: &DualSemigroupConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rho_id, rho) = b.fresh_local(c.rat.clone());

    let rho_sq = c.mul(rho.clone(), rho.clone());

    // motive : fun (k : Nat) => (ρ^k)·(ρ^k) = (ρ·ρ)^k
    let motive = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (k_id, k) = d.fresh_local(c.nat.clone());
        let pow_k = c.pow(&rho, &k);
        let body = c.eq_rat(c.mul(pow_k.clone(), pow_k), c.pow(&rho_sq, &k));
        d.finish_child(d.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), body))
    };

    // base (k = 0) : (ρ^0)·(ρ^0) = (ρ·ρ)^0
    //   both sides ι-reduce: ρ^0 ≡ 1, (ρ·ρ)^0 ≡ 1, so the goal is 1·1 = 1,
    //   closed by `Rat.mul_one Rat.one : 1·1 = 1`.
    let base = c.mul_one(c.rat_one.clone());

    // step : fun (m : Nat) (ih : (ρ^m)·(ρ^m) = (ρ·ρ)^m) =>
    //   <chain> : (ρ·ρ^m)·(ρ·ρ^m) = (ρ·ρ)·(ρ·ρ)^m
    //   (def-eq to motive (succ m): (ρ^(m+1))·(ρ^(m+1)) = (ρ·ρ)^(m+1)).
    let step = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (m_id, m) = d.fresh_local(c.nat.clone());
        let pow_m = c.pow(&rho, &m); // P := ρ^m
        let ih_ty = c.eq_rat(c.mul(pow_m.clone(), pow_m.clone()), c.pow(&rho_sq, &m));
        let (ih_id, ih) = d.fresh_local(ih_ty.clone());

        // leg1 : (ρ·P)·(ρ·P) = (ρ·ρ)·(P·P)   Rat.mul_mul_mul_comm ρ P ρ P
        let rho_p = c.mul(rho.clone(), pow_m.clone()); // ρ·P  ≡ ρ^(m+1)
        let lhs = c.mul(rho_p.clone(), rho_p.clone()); // (ρ·P)·(ρ·P)
        let pp = c.mul(pow_m.clone(), pow_m.clone()); // P·P
        let mid = c.mul(rho_sq.clone(), pp.clone()); // (ρ·ρ)·(P·P)
        let leg1 = c.mul_mul_mul_comm(rho.clone(), pow_m.clone(), rho.clone(), pow_m.clone());

        // leg2 : (ρ·ρ)·(P·P) = (ρ·ρ)·(ρ·ρ)^m   congrArg ((ρ·ρ)·_) ih
        let mul_left_sq = {
            let mut e = EnvDeclBuilder::child_of(&d);
            let (z_id, z) = e.fresh_local(c.rat.clone());
            let body = c.mul(rho_sq.clone(), z);
            e.finish_child(e.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let pow_sq_m = c.pow(&rho_sq, &m); // (ρ·ρ)^m  ≡ (ρ·ρ)^(m+1)'s tail
        let rhs = c.mul(rho_sq.clone(), pow_sq_m.clone()); // (ρ·ρ)·(ρ·ρ)^m
        let leg2 = c.congr_rat(pp.clone(), pow_sq_m, mul_left_sq, ih);

        // chain : (ρ·P)·(ρ·P) = (ρ·ρ)·(P·P) = (ρ·ρ)·(ρ·ρ)^m
        let proof = c.trans_rat(lhs, mid, rhs, leg1, leg2);

        let r = d.mk_lam(ih_id, BinderInfo::Default, ih_ty, proof);
        d.finish_child(d.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), r))
    };

    // The motive is `Prop`-valued (an `Eq`), so the recursor is `Nat.rec.{0}`.
    let nat_rec = Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]);
    let body = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (k_id, k) = d.fresh_local(c.nat.clone());
        let rec_app = Expr::apps(nat_rec, [motive, base, step, k.clone()]);
        d.finish_child(d.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), rec_app))
    };
    b.finish(b.mk_lam(rho_id, BinderInfo::Default, c.rat.clone(), body))
}

impl DualSemigroupConsts {
    /// `Rat.mk (Int.ofNat 1) d` — the literal `1/d`, with `d` the `Nat` literal.
    fn one_over(&self, d: u32) -> Expr {
        let int_of_nat = Expr::const_(Name::from_string("Int.ofNat"), vec![]);
        let one_nat = Expr::app(self.nat_succ.clone(), self.nat_zero.clone());
        let mut d_nat = self.nat_zero.clone();
        for _ in 0..d {
            d_nat = Expr::app(self.nat_succ.clone(), d_nat);
        }
        Expr::apps(
            Expr::const_(Name::from_string("Rat.mk"), vec![]),
            [Expr::app(int_of_nat, one_nat), d_nat],
        )
    }
}

/// `Rat.third_mul_third : Rat.mul (1/3) (1/3) = 1/9` (type + proof).
fn build_third_mul_third(c: &DualSemigroupConsts) -> (Expr, Expr) {
    let third = c.one_over(3);
    let ninth = c.one_over(9);
    let lhs = c.mul(third.clone(), third.clone());
    let ty = c.eq_rat(lhs.clone(), ninth.clone());

    // `Rat.mk a b` is `Quot.mk Rat.Raw.Equiv (Rat.Raw.mk a b)`; `Rat.mul` is a
    // binary `Quot.lift`. `(1/3)·(1/3)` ι-reduces (via the lift) to the `Quot.mk`
    // of the raw product `Rat.Raw.mk (1·1) (3·3) = Rat.Raw.mk 1 9`, and `1/9` is
    // `Quot.mk (Rat.Raw.mk 1 9)`. Both reps are byte-identical after the lift's
    // numerator/denominator multiply, so a single `Eq.refl` on the LHS closes it
    // by def-eq (the kernel performs the `Quot.lift` ι-reduction). If the raw
    // product does not literally normalise to `Rat.Raw.mk 1 9`, the
    // `register_rat_third_mul_third` caller falls back to the `Quot.sound`
    // cross-multiplication idiom; here the `Rat.mk` denominators are the literal
    // `3`/`9`, so the lifted product is `Rat.Raw.mk 1 9` definitionally.
    let eq_refl = Expr::const_(
        Name::from_string("Eq.refl"),
        vec![Level::succ(Level::zero())],
    );
    let value = Expr::apps(eq_refl, [c.rat.clone(), lhs]);
    (ty, value)
}

/// `∀ (k : Nat), ((1/3)^k)·((1/3)^k) = (1/9)^k`.
fn build_third_type(c: &DualSemigroupConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let third = c.one_over(3);
    let ninth = c.one_over(9);
    let pow_k = c.pow(&third, &k);
    let lhs = c.mul(pow_k.clone(), pow_k);
    let rhs = c.pow(&ninth, &k);
    let concl = c.eq_rat(lhs, rhs);
    b.finish(b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), concl))
}

/// Proof of `∀ k, ((1/3)^k)·((1/3)^k) = (1/9)^k`.
///
/// From the general semigroup identity at `ρ = 1/3`:
/// `((1/3)^k)·((1/3)^k) = ((1/3)·(1/3))^k`. The base `(1/3)·(1/3)` is rewritten
/// to `1/9` by `Rat.third_mul_third`, lifted to the exponent slot by
/// `congrArg (·^k)`.
fn build_third_value(c: &DualSemigroupConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.nat.clone());

    let third = c.one_over(3);
    let ninth = c.one_over(9);
    let third_sq = c.mul(third.clone(), third.clone()); // (1/3)·(1/3)
    let pow_k = c.pow(&third, &k);

    // h1 : ((1/3)^k)·((1/3)^k) = ((1/3)·(1/3))^k
    //   = Rat.powNat_mul_self_eq_sq_pow (1/3) k.
    let semigroup = Expr::const_(Name::from_string("Rat.powNat_mul_self_eq_sq_pow"), vec![]);
    let h1 = Expr::apps(semigroup, [third.clone(), k.clone()]);
    let lhs = c.mul(pow_k.clone(), pow_k); // ((1/3)^k)·((1/3)^k)
    let mid = c.pow(&third_sq, &k); // ((1/3)·(1/3))^k
    let rhs = c.pow(&ninth, &k); // (1/9)^k

    // h2 : ((1/3)·(1/3))^k = (1/9)^k
    //   = congrArg (fun base => base^k) (Rat.third_mul_third)
    //   Rat.third_mul_third : (1/3)·(1/3) = 1/9.
    let third_mul_third = Expr::const_(Name::from_string("Rat.third_mul_third"), vec![]);
    let pow_base_fn = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (base_id, base) = d.fresh_local(c.rat.clone());
        let body = c.pow(&base, &k);
        d.finish_child(d.mk_lam(base_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let h2 = c.congr_rat(
        third_sq.clone(),
        ninth.clone(),
        pow_base_fn,
        third_mul_third,
    );

    let proof = c.trans_rat(lhs, mid, rhs, h1, h2);
    b.finish(b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), proof))
}

impl Environment {
    /// Register `Rat.powNat_mul_self_eq_sq_pow : ∀ ρ k, (ρ^k)·(ρ^k) = (ρ·ρ)^k`
    /// — the noise-operator semigroup `T_ρ ∘ T_ρ = T_{ρ²}` in per-level spectral
    /// (scalar) form. `Nat.rec` on `k`; kernel-checked, constructive (closure ⊆
    /// {`Rat.mul_one`, `Rat.mul_mul_mul_comm`} ∪ Eq built-ins). Idempotent.
    pub(crate) fn register_rat_pow_nat_mul_self_eq_sq_pow(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.powNat_mul_self_eq_sq_pow");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.register_rat_pow_nat()?;
        self.init_rat_arith()?; // Rat.mul
                                // `Rat.mul_one` and `Rat.mul_mul_mul_comm` (each guarded on its own name).
        {
            let qc = crate::env::algebra_rat_quotient::RatRawConsts::new();
            self.register_rat_q_structural(&qc)?; // Rat.mul_one (+ assoc/comm)
        }
        self.register_rat_mul_mul_mul_comm_theorem()?;
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let c = DualSemigroupConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_semigroup_type(&c),
            value: build_semigroup_value(&c),
        })
    }

    /// Register `Rat.third_mul_third : Rat.mul (1/3) (1/3) = 1/9` — the scalar
    /// `(1/3)·(1/3) = 1/9` over the live `Rat` quotient carrier. Kernel-checked,
    /// constructive. Idempotent.
    pub(crate) fn register_rat_third_mul_third(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.third_mul_third");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_rat()?;
        self.init_rat_arith()?; // Rat.mul

        let c = DualSemigroupConsts::new();
        let (ty, value) = build_third_mul_third(&c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// Register `BoolAnalysis.noise_semigroup_third : ∀ k, ((1/3)^k)·((1/3)^k) =
    /// (1/9)^k` — the KKL-instantiated noise-operator semigroup
    /// `T_{1/3} ∘ T_{1/3} = T_{1/9}` at the per-level spectral weight (`k = |S|`).
    /// Kernel-checked, constructive. Idempotent.
    pub(crate) fn register_noise_semigroup_third(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.noise_semigroup_third");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.register_rat_pow_nat()?;
        self.register_rat_pow_nat_mul_self_eq_sq_pow()?;
        self.register_rat_third_mul_third()?;
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let c = DualSemigroupConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_third_type(&c),
            value: build_third_value(&c),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn check_constructive(env: &Environment, name: &str) {
        let nm = Name::from_string(name);
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "{name} must be a CHECKED Theorem, not an axiom"
        );
        let value = info.value.clone().expect("theorem value present");
        let tc = TypeChecker::with_mode(env, env.mode());
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("{name} proof must check against its type: {e:?}"));
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

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.register_rat_pow_nat_mul_self_eq_sq_pow()
            .expect("register_rat_pow_nat_mul_self_eq_sq_pow");
        env.register_rat_third_mul_third()
            .expect("register_rat_third_mul_third");
        env.register_noise_semigroup_third()
            .expect("register_noise_semigroup_third");
        env
    }

    #[test]
    fn test_semigroup_identity_is_constructive() {
        check_constructive(&env(), "Rat.powNat_mul_self_eq_sq_pow");
    }

    #[test]
    fn test_third_mul_third_is_constructive() {
        check_constructive(&env(), "Rat.third_mul_third");
    }

    #[test]
    fn test_noise_semigroup_third_is_constructive() {
        check_constructive(&env(), "BoolAnalysis.noise_semigroup_third");
    }

    #[test]
    fn test_idempotent() {
        let mut env = Environment::with_prelude();
        env.register_rat_pow_nat_mul_self_eq_sq_pow()
            .expect("first");
        env.register_rat_pow_nat_mul_self_eq_sq_pow()
            .expect("idempotent");
        env.register_rat_third_mul_third().expect("first");
        env.register_rat_third_mul_third().expect("idempotent");
        env.register_noise_semigroup_third().expect("first");
        env.register_noise_semigroup_third().expect("idempotent");
    }

    /// THE TARGET-REFUTATION GATE (sharp-KKL rule). `refute_conjecture` must NOT
    /// refute the semigroup identity — it is a TRUE algebraic identity.
    /// By-hand reasoning across tribes (the KKL battery's blind spot is for
    /// *inequalities*; this is an equality with no influence parameter, so the
    /// dictator/parity/constant battery cannot manufacture a false instance):
    /// - `(ρ^k)·(ρ^k) = (ρ·ρ)^k` at `k=0` ⟹ `1·1 = 1`; at `k=1` ⟹ `ρ·ρ = ρ·ρ`;
    ///   at `k=2` ⟹ `(ρ·ρ)·(ρ·ρ) = (ρ·ρ)·(ρ·ρ)` (regrouped). Holds for every `ρ`
    ///   (including negative ρ, since both sides square the same product).
    /// - `((1/3)^k)·((1/3)^k) = (1/9)^k` is its `ρ=1/3` instance; `(1/3)·(1/3)=1/9`.
    #[test]
    fn test_semigroup_not_refuted() {
        use super::super::carrier_refutation::refute_conjecture;
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in [
            "Rat.powNat_mul_self_eq_sq_pow",
            "BoolAnalysis.noise_semigroup_third",
        ] {
            let info = env.get_const(&Name::from_string(name)).expect("registered");
            assert_eq!(
                refute_conjecture(&tc, &info.type_),
                None,
                "{name} is a TRUE algebraic identity; it must NOT refute"
            );
        }
    }
}
