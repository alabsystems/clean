// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bonami-Beckner campaign — the (2,4)-hypercontractivity two-point bound.
//!
//! The per-coordinate heart of O'Donnell 9.22. Two `Rat`-pure theorems, both
//! kernel-checked through the CHECKED `add_decl` path:
//!
//! - `Rat.fourth_power_rho_even_pair` — the ρ-version of the B5 even-pair
//!   identity, obtained by substituting `B := ρ·B` into the landed
//!   `Rat.fourth_power_even_pair_expanded`:
//!
//!   ```text
//!   (A+ρB)⁴ + (A−ρB)⁴
//!     = (2·A⁴ + 2·(ρB)⁴) + ((2·2) + 2·(2·2))·(A²·(ρB)²)
//!   ```
//!
//!   with `A⁴ := (A·A)·(A·A)`, `(ρB)⁴ := ((ρB)·(ρB))·((ρB)·(ρB))`,
//!   `A²·(ρB)² := (A·A)·((ρB)·(ρB))`. The coefficient `(2·2)+2·(2·2)` is the
//!   honest `4+8 = 12` cross split. This IS the textbook
//!   `(A+ρB)⁴+(A−ρB)⁴ = 2A⁴ + 12ρ²A²B² + 2ρ⁴B⁴` with ρ riding inside the `B`
//!   slot; the proof is the landed expanded identity instantiated at `(A, ρ·B)`.
//!
//! - `Rat.fourth_power_rho_two_point_bound` — THE two-point inequality (the
//!   heart). Under the hypercontractivity hypothesis `3·ρ² ≤ 1`:
//!
//!   ```text
//!   (A+ρB)⁴ + (A−ρB)⁴ ≤ (1+1)·(M·M),      M := A·A + B·B
//!   ```
//!
//!   i.e. `2·(A²+B²)²`. Derived from the ρ-even-pair by bounding the two
//!   ρ-weighted legs through the B6 coefficient bounds
//!   (`hc_six_rho_sq_t_le_two_t` on the cross term, `hc_rho_four_t_le_t` on the
//!   `B⁴` term) and closing with the ring identity
//!   `2A⁴ + 4A²B² + 2B⁴ = 2·(A²+B²)²`.
//!
//! Every dependency is `ProofQuality::Constructive` with empty domain-axiom
//! closure (the expanded even-pair, the B6 bounds, the `Rat` ring/order
//! surface), so both theorems are too.

use super::boolean_analysis_ring_identities_proofs::RingConsts;
use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

/// The expanded even-pair RHS `((2·X⁴ + 2·Y⁴) + coeff·(X²·Y²))` for free
/// `Rat` terms `x`, `y`, matching `fourth_power_even_pair_expanded`'s
/// `expanded_rhs` exactly (so an instantiation of that theorem at `(x, y)`
/// inhabits the corresponding `Eq` type built here).
fn expanded_rhs_at(c: &RingConsts, x: &Expr, y: &Expr) -> Expr {
    let two = c.two();
    let xx = c.mul(x.clone(), x.clone());
    let yy = c.mul(y.clone(), y.clone());
    let x4 = c.mul(xx.clone(), xx.clone());
    let y4 = c.mul(yy.clone(), yy.clone());
    let x2y2 = c.mul(xx.clone(), yy.clone());
    let two_two = c.mul(two.clone(), two.clone());
    let two_x4 = c.nmul(two.clone(), x4);
    let two_y4 = c.nmul(two.clone(), y4);
    let coeff = c.add(two_two.clone(), c.nmul(two.clone(), two_two.clone())); // (2·2) + 2·(2·2)
    c.add(c.add(two_x4, two_y4), c.mul(coeff, x2y2))
}

/// The `((s)·(s))·((s)·(s))` fourth-power shape for `s := step`.
fn pow4_of(c: &RingConsts, step: &Expr) -> Expr {
    let sq = c.mul(step.clone(), step.clone());
    c.mul(sq.clone(), sq)
}

impl Environment {
    /// Initialize the (2,4)-hypercontractivity two-point bound layer.
    ///
    /// Registers `Rat.fourth_power_rho_even_pair` and
    /// `Rat.fourth_power_rho_two_point_bound` as kernel-checked
    /// `Declaration::Theorem`s. Idempotent.
    ///
    /// Depends on `init_boolean_analysis_fourth_power` (the expanded even-pair
    /// identity) and `init_boolean_analysis_hc_bounds` (the B6 coefficient
    /// bounds + the `Rat` order surface). No axiom is added or removed.
    pub fn init_boolean_analysis_two_point_bound(&mut self) -> Result<(), EnvError> {
        self.init_boolean_analysis_fourth_power()?;
        self.init_boolean_analysis_hc_bounds()?;

        let c = RingConsts::new();
        self.register_rat_fourth_power_rho_even_pair(&c)?;
        self.register_rat_fourth_power_rho_two_point_bound(&c)?;
        Ok(())
    }

    /// `Rat.fourth_power_rho_even_pair :
    ///   ∀ A B ρ, (A+ρB)⁴ + (A−ρB)⁴
    ///       = (2·A⁴ + 2·(ρB)⁴) + ((2·2)+2·(2·2))·(A²·(ρB)²)`.
    /// The landed expanded even-pair instantiated at `(A, ρ·B)`. Constructive.
    fn register_rat_fourth_power_rho_even_pair(&mut self, c: &RingConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.fourth_power_rho_even_pair");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let (ty, value) = build_rho_even_pair(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Rat.fourth_power_rho_two_point_bound :
    ///   ∀ A B ρ, Rat.le (3·(ρ·ρ)) 1 →
    ///       Rat.le ((A+ρB)⁴ + (A−ρB)⁴) ((1+1)·((A·A + B·B)·(A·A + B·B)))`.
    /// THE two-point inequality. Constructive.
    fn register_rat_fourth_power_rho_two_point_bound(
        &mut self,
        c: &RingConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.fourth_power_rho_two_point_bound");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let (ty, value) = build_two_point_bound(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// Build the type + proof of `Rat.fourth_power_rho_even_pair`.
fn build_rho_even_pair(c: &RingConsts) -> (Expr, Expr) {
    // The proof is `fourth_power_even_pair_expanded A (ρ·B)`; the stated type is
    // that theorem's conclusion at `(A, ρ·B)`, built here so the application
    // inhabits it directly.
    let expanded = Expr::const_(
        Name::from_string("Rat.fourth_power_even_pair_expanded"),
        vec![],
    );

    let ty = {
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(c.rat());
        let (bv_id, bv) = b.fresh_local(c.rat());
        let (rho_id, rho) = b.fresh_local(c.rat());
        let rho_b = c.mul(rho.clone(), bv.clone()); // ρ·B
        let s = c.add(a.clone(), rho_b.clone()); // A + ρB
        let d = c.sub(a.clone(), rho_b.clone()); // A − ρB
        let lhs = c.add(pow4_of(c, &s), pow4_of(c, &d));
        let rhs = expanded_rhs_at(c, &a, &rho_b);
        let concl = c.eq(lhs, rhs);
        let e = b.mk_pi(rho_id, BinderInfo::Default, c.rat(), concl);
        let e = b.mk_pi(bv_id, BinderInfo::Default, c.rat(), e);
        let e = b.mk_pi(a_id, BinderInfo::Default, c.rat(), e);
        b.finish(e)
    };

    let value = {
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(c.rat());
        let (bv_id, bv) = b.fresh_local(c.rat());
        let (rho_id, rho) = b.fresh_local(c.rat());
        let rho_b = c.mul(rho.clone(), bv.clone());
        let proof = Expr::apps(expanded.clone(), [a.clone(), rho_b]);
        let e = b.mk_lam(rho_id, BinderInfo::Default, c.rat(), proof);
        let e = b.mk_lam(bv_id, BinderInfo::Default, c.rat(), e);
        let e = b.mk_lam(a_id, BinderInfo::Default, c.rat(), e);
        b.finish(e)
    };

    (ty, value)
}

include!("boolean_analysis_two_point_bound_proof.rs");

#[cfg(test)]
mod debug_tests {
    use super::super::boolean_analysis_hc_bounds_proofs::HcBoundsConsts;
    use super::super::boolean_analysis_ring_identities_proofs::RingConsts;
    use super::super::decl_builder::EnvDeclBuilder;
    use super::*;
    use crate::env::Environment;
    use crate::expr::BinderInfo;
    use crate::tc::TypeChecker;

    fn debug_env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_fourth_power().expect("fp");
        env.init_boolean_analysis_hc_bounds().expect("hc");
        env
    }

    /// Build a closed `∀ A B ρ, eq` wrapper around an equality and kernel-check it.
    fn check_eq3(
        name: &str,
        f: impl Fn(&RingConsts, &EnvDeclBuilder, &Expr, &Expr, &Expr) -> (Expr, Expr, Expr),
    ) {
        let env = debug_env();
        let c = RingConsts::new();
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(c.rat());
        let (bv_id, bv) = b.fresh_local(c.rat());
        let (rho_id, rho) = b.fresh_local(c.rat());
        let (proof, _lhs, _rhs) = f(&c, &b, &a, &bv, &rho);
        let val = b.mk_lam(rho_id, BinderInfo::Default, c.rat(), proof);
        let val = b.mk_lam(bv_id, BinderInfo::Default, c.rat(), val);
        let val = b.mk_lam(a_id, BinderInfo::Default, c.rat(), val);
        let val = b.finish(val);
        // Check the closed lambda against ∀ A B ρ, ty.
        let pi = {
            let mut bb = EnvDeclBuilder::new();
            let (a2_id, a2) = bb.fresh_local(c.rat());
            let (bv2_id, bv2) = bb.fresh_local(c.rat());
            let (rho2_id, rho2) = bb.fresh_local(c.rat());
            let (_p, l2, r2) = f(&c, &bb, &a2, &bv2, &rho2);
            let body = c.eq(l2, r2);
            let e = bb.mk_pi(rho2_id, BinderInfo::Default, c.rat(), body);
            let e = bb.mk_pi(bv2_id, BinderInfo::Default, c.rat(), e);
            let e = bb.mk_pi(a2_id, BinderInfo::Default, c.rat(), e);
            bb.finish(e)
        };
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&val, &pi)
            .unwrap_or_else(|e| panic!("{name} failed: {e:?}"));
    }

    #[test]
    fn dbg_eq_rb4() {
        check_eq3("eq_rb4", |c, b, _a, bv, rho| {
            let p = build_eq_rb4(c, b, rho, bv);
            let rho_b = c.mul(rho.clone(), bv.clone());
            let rb_sq = c.mul(rho_b.clone(), rho_b.clone());
            let lhs = c.mul(rb_sq.clone(), rb_sq.clone());
            let s = c.mul(rho.clone(), rho.clone());
            let bb = c.mul(bv.clone(), bv.clone());
            let rhs = c.mul(c.mul(s.clone(), s.clone()), c.mul(bb.clone(), bb.clone()));
            (p, lhs, rhs)
        });
    }

    #[test]
    fn dbg_twelve() {
        check_eq3("twelve", |c, b, _a, _bv, _rho| {
            let hc = HcBoundsConsts::new();
            let six = hc.six();
            let two = c.two();
            let two_two = c.mul(two.clone(), two.clone());
            let coeff = c.add(two_two.clone(), c.nmul(two.clone(), two_two.clone()));
            let p = build_twelve_eq(c, b, &six, &two, &coeff);
            let lhs = c.mul(six.clone(), two.clone());
            (p, lhs, coeff)
        });
    }

    #[test]
    fn dbg_eq_cross() {
        check_eq3("eq_cross", |c, b, a, bv, rho| {
            let hc = HcBoundsConsts::new();
            let six = hc.six();
            let two = c.two();
            let two_two = c.mul(two.clone(), two.clone());
            let coeff = c.add(two_two.clone(), c.nmul(two.clone(), two_two.clone()));
            let p = build_eq_cross(c, b, a, bv, rho, &coeff, &six);
            let aa = c.mul(a.clone(), a.clone());
            let rho_b = c.mul(rho.clone(), bv.clone());
            let rb_sq = c.mul(rho_b.clone(), rho_b.clone());
            let lhs = c.mul(coeff.clone(), c.mul(aa.clone(), rb_sq.clone()));
            let s = c.mul(rho.clone(), rho.clone());
            let bb = c.mul(bv.clone(), bv.clone());
            let a2b2 = c.mul(aa.clone(), bb.clone());
            let six_s = c.mul(six.clone(), s.clone());
            let rhs = c.mul(six_s.clone(), c.nmul(two.clone(), a2b2.clone()));
            (p, lhs, rhs)
        });
    }

    #[test]
    fn dbg_eq_final() {
        check_eq3("eq_final", |c, b, a, bv, _rho| {
            let p = build_eq_final(c, b, a, bv);
            let two = c.two();
            let aa = c.mul(a.clone(), a.clone());
            let bb = c.mul(bv.clone(), bv.clone());
            let a4 = c.mul(aa.clone(), aa.clone());
            let b4 = c.mul(bb.clone(), bb.clone());
            let a2b2 = c.mul(aa.clone(), bb.clone());
            let two_a4 = c.nmul(two.clone(), a4);
            let two_b4 = c.nmul(two.clone(), b4);
            let two_a2b2 = c.nmul(two.clone(), a2b2);
            let two_two_a2b2 = c.nmul(two.clone(), two_a2b2);
            let lhs = c.add(c.add(two_a4, two_b4), two_two_a2b2);
            let m = c.add(aa.clone(), bb.clone());
            let rhs = c.nmul(two.clone(), c.mul(m.clone(), m.clone()));
            (p, lhs, rhs)
        });
    }

    #[test]
    fn dbg_nonneg() {
        let env = debug_env();
        let c = RingConsts::new();
        let hc = HcBoundsConsts::new();
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(c.rat());
        let (bv_id, bv) = b.fresh_local(c.rat());
        let p = build_nonneg_two_a2b2(&c, &hc, &b, &a, &bv);
        let aa = c.mul(a.clone(), a.clone());
        let bb = c.mul(bv.clone(), bv.clone());
        let a2b2 = c.mul(aa.clone(), bb.clone());
        let two_a2b2 = c.nmul(c.two(), a2b2);
        let ty = hc.le(hc.zero(), two_a2b2);
        let val = b.mk_lam(bv_id, BinderInfo::Default, c.rat(), p);
        let val = b.mk_lam(a_id, BinderInfo::Default, c.rat(), val);
        let val = b.finish(val);
        let pi = {
            let mut bb2 = EnvDeclBuilder::new();
            let (a2_id, a2) = bb2.fresh_local(c.rat());
            let (bv2_id, bv2) = bb2.fresh_local(c.rat());
            let aa2 = c.mul(a2.clone(), a2.clone());
            let bb_2 = c.mul(bv2.clone(), bv2.clone());
            let a2b2_2 = c.mul(aa2.clone(), bb_2.clone());
            let two_a2b2_2 = c.nmul(c.two(), a2b2_2);
            let body = hc.le(hc.zero(), two_a2b2_2);
            let e = bb2.mk_pi(bv2_id, BinderInfo::Default, c.rat(), body);
            let e = bb2.mk_pi(a2_id, BinderInfo::Default, c.rat(), e);
            bb2.finish(e)
        };
        let _ = ty;
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&val, &pi).expect("nonneg failed");
    }
}

#[cfg(test)]
mod tests {
    use crate::env::types::ConstantKind;
    use crate::env::{Environment, ProofQuality};
    use crate::expr::{Expr, ExprKind};
    use crate::name::Name;
    use crate::tc::TypeChecker;

    const THMS: &[&str] = &[
        "Rat.fourth_power_rho_even_pair",
        "Rat.fourth_power_rho_two_point_bound",
    ];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_two_point_bound()
            .expect("init_boolean_analysis_two_point_bound should succeed");
        env
    }

    #[test]
    fn test_init_idempotent() {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_two_point_bound()
            .expect("first init");
        env.init_boolean_analysis_two_point_bound()
            .expect("second init should be a no-op");
    }

    #[test]
    fn test_all_registered_as_theorems() {
        let env = env();
        for name in THMS {
            let info = env
                .get_const(&Name::from_string(name))
                .unwrap_or_else(|| panic!("{name} should be registered"));
            assert_eq!(
                info.kind,
                ConstantKind::Theorem,
                "{name} must be Declaration::Theorem, got {:?}",
                info.kind
            );
        }
    }

    #[test]
    fn test_all_type_check() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in THMS {
            let info = env
                .get_const(&Name::from_string(name))
                .unwrap_or_else(|| panic!("{name} registered"));
            let value = info.value.clone().expect("proof present");
            tc.check_type(&value, &info.type_)
                .unwrap_or_else(|e| panic!("{name} proof must check against its type: {e:?}"));
            assert!(
                matches!(info.type_.kind(), ExprKind::Pi(..)),
                "{name} type is a Pi"
            );
        }
    }

    #[test]
    fn test_all_constructive_empty_axiom_closure() {
        let env = env();
        for name in THMS {
            let deps = env
                .axiom_deps(&Name::from_string(name))
                .unwrap_or_else(|| panic!("axiom_deps should work for {name}"));
            let dep_names: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
            assert!(
                dep_names.is_empty(),
                "{name} must have empty domain-axiom closure, got {dep_names:?}"
            );
            assert_eq!(
                env.proof_quality(&Name::from_string(name)),
                Some(ProofQuality::Constructive),
                "{name} must be Constructive"
            );
        }
    }

    /// Sanity: the two-point bound's conclusion is an `LE.le` (≤), not an `Eq`.
    /// (`OrderConsts::rat_le` builds the `@LE.le Rat instLERat _ _` head, which
    /// is defeq to `Rat.le` but syntactically `LE.le`.)
    #[test]
    fn test_two_point_bound_is_inequality() {
        let env = env();
        let info = env
            .get_const(&Name::from_string("Rat.fourth_power_rho_two_point_bound"))
            .expect("registered");
        // Walk to the final conclusion head; it must be `Rat.le`.
        fn final_head(ty: &Expr) -> String {
            let mut cur = ty.clone();
            while let ExprKind::Pi(_, _, body) = cur.kind() {
                cur = (**body).clone();
            }
            let mut head = cur;
            while let ExprKind::App(f, _) = head.kind() {
                head = (**f).clone();
            }
            match head.kind() {
                ExprKind::Const(n, _) => n.to_string(),
                _ => String::new(),
            }
        }
        assert_eq!(
            final_head(&info.type_),
            "LE.le",
            "two-point bound conclusion must be LE.le (≤)"
        );
    }
}
