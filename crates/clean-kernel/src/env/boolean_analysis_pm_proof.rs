// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of `BoolAnalysis.pm_mul_self` — the `{+1,-1}` sign
//! embedding squares to `1`.
//!
//! `pm_mul_self : ∀ (b : Bool), Rat.mul (pm b) (pm b) = Rat.one`
//!
//! `pm` is the `{+1,-1}` embedding (`pm false = +1`, `pm true = -1`). On either
//! closed constructor the squared value is a closed Rat that the kernel computes
//! definitionally:
//!   - `pm false · pm false ≡ 1 · 1 ≡ 1`
//!   - `pm true  · pm true  ≡ (1-2) · (1-2) ≡ 1`
//!
//! so a `Bool.rec` case split with an `@Eq.refl Rat (pm b · pm b)` leaf in each
//! branch closes the goal (the RHS `Rat.one` is def-eq to the reduced LHS).
//!
//! This is the per-coordinate `f̃² = 1` fact for `±1`-valued functions — the
//! kernel of both the diagonal character inner product `⟨χ_S, χ_S⟩ = 1` and the
//! `E[f̃²] = 1` normalization Parseval uses for Boolean `f`. Kernel-checked,
//! `ProofQuality::Constructive` (the only dependency is the `pm` Definition and
//! the `Bool.rec`/`Eq.refl` built-ins — empty admitted-axiom closure).

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Register `BoolAnalysis.pm_mul_self : ∀ b, pm b * pm b = 1` as a
    /// kernel-checked, constructive theorem. Idempotent.
    pub(crate) fn register_pm_mul_self_theorem(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.pm_mul_self");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        // `pm` (the {+1,-1} embedding) is registered by `register_boolfn_embeddings`
        // inside `init_boolean_analysis`; this theorem is wired in there, after
        // the embeddings, so `pm` is already present. We do NOT call
        // `init_boolean_analysis()` here to avoid re-entrancy.

        let one = Level::succ(Level::zero());
        let bool_c = Expr::const_(Name::from_string("Bool"), vec![]);
        let btrue = Expr::const_(Name::from_string("Bool.true"), vec![]);
        let bfalse = Expr::const_(Name::from_string("Bool.false"), vec![]);
        let rat = Expr::const_(Name::from_string("Rat"), vec![]);
        let rat_one = Expr::const_(Name::from_string("Rat.one"), vec![]);
        let rat_mul = Expr::const_(Name::from_string("Rat.mul"), vec![]);
        let pm = Expr::const_(Name::from_string("BoolAnalysis.pm"), vec![]);
        let eq_c = Expr::const_(Name::from_string("Eq"), vec![one.clone()]);
        let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![one.clone()]);
        // Motive is an `Eq` proposition (Prop = Sort 0), so the recursor is at
        // universe 0.
        let bool_rec = Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]);

        // `pm b * pm b`.
        let pm_sq = |b: Expr| {
            let pm_b = Expr::app(pm.clone(), b);
            Expr::apps(rat_mul.clone(), [pm_b.clone(), pm_b])
        };
        // The proposition `pm b * pm b = 1`.
        let goal = |b: Expr| Expr::apps(eq_c.clone(), [rat.clone(), pm_sq(b), rat_one.clone()]);
        // Leaf for a closed ctor: `@Eq.refl Rat (pm ctor * pm ctor)`; its type
        // `(…) = (…)` is def-eq to the goal `(…) = 1` because the LHS computes to
        // the closed Rat `1`.
        let leaf = |b: Expr| Expr::apps(eq_refl.clone(), [rat.clone(), pm_sq(b)]);

        // type: (b : Bool) → pm b * pm b = 1
        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (b_id, bv) = b.fresh_local(bool_c.clone());
            let concl = goal(bv);
            let e = b.mk_pi(b_id, BinderInfo::Default, bool_c.clone(), concl);
            b.finish(e)
        };

        // value: fun (b : Bool) => @Bool.rec (fun b' => pm b' * pm b' = 1)
        //          <b=false leaf> <b=true leaf> b
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (b_id, bv) = b.fresh_local(bool_c.clone());
            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (bp_id, bp) = c.fresh_local(bool_c.clone());
                c.finish_child(c.mk_lam(bp_id, BinderInfo::Default, bool_c.clone(), goal(bp)))
            };
            // Bool.rec minors are in constructor order: false-case, then true.
            let rec = Expr::apps(
                bool_rec.clone(),
                [motive, leaf(bfalse.clone()), leaf(btrue.clone()), bv],
            );
            let e = b.mk_lam(b_id, BinderInfo::Default, bool_c.clone(), rec);
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
            type_,
            value,
        })
    }

    /// Register `BoolAnalysis.pm_false_add_pm_true_eq_zero`:
    ///
    /// `Rat.add (pm Bool.false) (pm Bool.true) = Rat.zero`
    ///
    /// The per-coordinate **vanishing average numerator** of a parity character
    /// over a coordinate that belongs to the subset: `pm false = +1` and
    /// `pm true = -1`, so `(+1) + (-1) = 0`. Over the `Rat` quotient,
    /// `Rat.add Rat.one (Rat.neg Rat.one)` ι/Quot-reduces to `Rat.zero` (the rep
    /// numerator `1·1 + (-1)·1 = 0` cancels with no `Quot.sound` needed), so the
    /// goal closes by `@Eq.refl Rat (Rat.add (pm false) (pm true))` — the LHS is
    /// def-eq to the closed `Rat.zero`. This is the per-coordinate `Σ_{xᵢ∈{0,1}}
    /// (1-2⟦xᵢ⟧) = 0` fact that makes the off-diagonal cube average `E[χ_U]`
    /// vanish for any `U` containing that coordinate (O'Donnell, *AoBF*, §1.4:
    /// `E[χ_S] = [S=∅]`). Kernel-checked, `ProofQuality::Constructive` (the only
    /// dependency is the `pm` Definition + the `Eq.refl` built-in).
    ///
    /// Idempotent.
    pub(crate) fn register_pm_coordinate_vanishing_theorem(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.pm_false_add_pm_true_eq_zero");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        // `pm` is registered by `register_boolfn_embeddings` inside
        // `init_boolean_analysis`; this theorem is wired in there, after the
        // embeddings, so `pm` is already present.

        let one = Level::succ(Level::zero());
        let btrue = Expr::const_(Name::from_string("Bool.true"), vec![]);
        let bfalse = Expr::const_(Name::from_string("Bool.false"), vec![]);
        let rat = Expr::const_(Name::from_string("Rat"), vec![]);
        let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
        let rat_add = Expr::const_(Name::from_string("Rat.add"), vec![]);
        let pm = Expr::const_(Name::from_string("BoolAnalysis.pm"), vec![]);
        let eq_c = Expr::const_(Name::from_string("Eq"), vec![one.clone()]);
        let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![one]);

        // lhs = Rat.add (pm false) (pm true)
        let lhs = Expr::apps(
            rat_add.clone(),
            [
                Expr::app(pm.clone(), bfalse.clone()),
                Expr::app(pm.clone(), btrue.clone()),
            ],
        );
        // type: lhs = 0
        let type_ = Expr::apps(eq_c.clone(), [rat.clone(), lhs.clone(), rat_zero.clone()]);
        // value: @Eq.refl Rat lhs  (lhs def-reduces to Rat.zero)
        let value = Expr::apps(eq_refl.clone(), [rat.clone(), lhs]);

        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
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
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn make_env() -> Environment {
        let mut env = Environment::new();
        env.init_boolean_analysis().expect("init_boolean_analysis");
        env.register_pm_mul_self_theorem()
            .expect("register_pm_mul_self_theorem");
        env
    }

    /// `pm_mul_self` is a genuine kernel-checked, `Constructive`
    /// `Declaration::Theorem` (empty admitted-axiom closure), and its proof term
    /// re-checks under C1.
    #[test]
    fn test_pm_mul_self_is_constructive_theorem() {
        let env = make_env();
        let info = env
            .get_const(&Name::from_string("BoolAnalysis.pm_mul_self"))
            .expect("pm_mul_self should be registered");
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "pm_mul_self must be a kernel-checked Theorem, not an Axiom"
        );
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .expect("pm_mul_self proof must check against its declared type");

        assert_eq!(
            env.proof_quality(&Name::from_string("BoolAnalysis.pm_mul_self")),
            Some(ProofQuality::Constructive),
            "pm_mul_self must be Constructive"
        );
        assert!(
            env.axiom_deps(&Name::from_string("BoolAnalysis.pm_mul_self"))
                .expect("deps")
                .is_empty(),
            "pm_mul_self's transitive axiom closure must be empty"
        );
    }

    /// `pm_false_add_pm_true_eq_zero` is a genuine kernel-checked, `Constructive`
    /// `Declaration::Theorem` (empty admitted-axiom closure): the per-coordinate
    /// vanishing average numerator `(+1)+(-1) = 0`. Its proof term re-checks
    /// under C1.
    #[test]
    fn test_pm_coordinate_vanishing_is_constructive_theorem() {
        let env = make_env();
        let info = env
            .get_const(&Name::from_string(
                "BoolAnalysis.pm_false_add_pm_true_eq_zero",
            ))
            .expect("pm_false_add_pm_true_eq_zero should be registered");
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "pm_false_add_pm_true_eq_zero must be a kernel-checked Theorem, not an Axiom"
        );
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .expect("pm_false_add_pm_true_eq_zero proof must check against its declared type");

        assert_eq!(
            env.proof_quality(&Name::from_string(
                "BoolAnalysis.pm_false_add_pm_true_eq_zero"
            )),
            Some(ProofQuality::Constructive),
            "pm_false_add_pm_true_eq_zero must be Constructive"
        );
        assert!(
            env.axiom_deps(&Name::from_string(
                "BoolAnalysis.pm_false_add_pm_true_eq_zero"
            ))
            .expect("deps")
            .is_empty(),
            "pm_false_add_pm_true_eq_zero's transitive axiom closure must be empty"
        );
    }
}
