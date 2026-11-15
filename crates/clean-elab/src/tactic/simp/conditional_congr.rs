// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Transport an `ite` condition without leaving its dependent instance stale.
//!
//! This is ordinary congruence, independent of the optional `reduceIte`
//! simproc. In particular, `simp only [h, ite_false]` must first rewrite the
//! condition using `h` before the named `ite_false` lemma can match. Rebuilding
//! only that argument would retain a `Decidable` of the old condition.

use clean_kernel::{BinderInfo, Expr, Level, Name};

use super::budget::SimpBudget;
use super::expr::peel_ite;
use super::instance_slot::synthesize_class_slot;
use super::types::SimpResult;
use crate::tactic::core::{Goal, ProofState};

/// Apply the imported `ite_congr` theorem to a proved condition rewrite.
///
/// Branches are unchanged. The replacement instance comes from the existing
/// class resolver and is checked against `Decidable new_condition`. No branch
/// is selected here: `simp only` still needs its named reduction lemma or
/// simproc. A missing theorem/instance or ill-typed proof leaves the term alone.
pub(super) fn rewrite_condition(
    state: &ProofState,
    goal: &Goal,
    original: &Expr,
    condition: &SimpResult,
    budget: &SimpBudget,
) -> Option<SimpResult> {
    let (level, alpha, old_condition, old_instance, then_value, else_value) = peel_ite(original)?;
    if condition.expr == old_condition {
        return None;
    }
    let condition_proof = condition.proof.as_ref()?;
    let condition_equality = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [Expr::prop(), old_condition.clone(), condition.expr.clone()],
    );
    state
        .check_type_strict(goal, condition_proof, &condition_equality)
        .ok()?;
    let congr_name = Name::from_string("ite_congr");
    state.env.get_const(&congr_name)?;
    let instance_type = Expr::app(
        Expr::const_(Name::from_string("Decidable"), vec![]),
        condition.expr.clone(),
    );
    let new_instance = synthesize_class_slot(state, goal, &instance_type, budget)?;
    let reflexivity = |value: &Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.refl"), vec![level.clone()]),
            [alpha.clone(), value.clone()],
        )
        .lift(1)
    };
    let same_then = Expr::lam(
        BinderInfo::Default,
        condition.expr.clone(),
        reflexivity(&then_value),
    );
    let same_else = Expr::lam(
        BinderInfo::Default,
        Expr::app(
            Expr::const_(Name::from_string("Not"), vec![]),
            condition.expr.clone(),
        ),
        reflexivity(&else_value),
    );
    let rewritten = Expr::apps(
        Expr::const_(Name::from_string("ite"), vec![level.clone()]),
        [
            alpha.clone(),
            condition.expr.clone(),
            new_instance.clone(),
            then_value.clone(),
            else_value.clone(),
        ],
    );
    let expected_equality = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![level.clone()]),
        [alpha.clone(), original.clone(), rewritten.clone()],
    );
    let proof = Expr::apps(
        Expr::const_(congr_name, vec![level]),
        [
            alpha,
            old_condition,
            condition.expr.clone(),
            then_value.clone(),
            else_value.clone(),
            then_value,
            else_value,
            old_instance,
            new_instance,
            condition_proof.clone(),
            same_then,
            same_else,
        ],
    );
    state
        .check_type_strict(goal, &proof, &expected_equality)
        .ok()?;
    Some(SimpResult {
        expr: rewritten,
        proof: Some(proof),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::{Declaration, Environment, Level};

    #[test]
    fn imported_conditional_transport_refuses_missing_and_malformed_witnesses() {
        std::thread::Builder::new()
            .stack_size(64 << 20)
            .spawn(|| {
                let lib = clean_olean::installed_lean_lib_path("leanprover/lean4:v4.8.0")
                    .expect("exact Lean 4.8 is required for the imported-congruence regression");
                let mut imported = Environment::default();
                imported.ensure_native_reducers();
                clean_olean::load_module_with_deps(&mut imported, "Init.Data.Bool", &[lib])
                    .unwrap();
                let one = Level::succ(Level::zero());
                let nat = Expr::const_(Name::from_string("Nat"), vec![]);
                let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
                let old = Expr::apps(
                    Expr::const_(Name::from_string("Eq"), vec![one.clone()]),
                    [nat.clone(), zero.clone(), zero.clone()],
                );
                let original = Expr::apps(
                    Expr::const_(Name::from_string("ite"), vec![one.clone()]),
                    [
                        nat.clone(),
                        old.clone(),
                        Expr::apps(
                            Expr::const_(Name::from_string("Nat.decEq"), vec![]),
                            [zero.clone(), zero.clone()],
                        ),
                        zero.clone(),
                        Expr::app(
                            Expr::const_(Name::from_string("Nat.succ"), vec![]),
                            zero.clone(),
                        ),
                    ],
                );
                let changed = SimpResult {
                    expr: Expr::const_(Name::from_string("True"), vec![]),
                    proof: Some(Expr::apps(
                        Expr::const_(Name::from_string("eq_self"), vec![one.clone()]),
                        [nat.clone(), zero],
                    )),
                };
                let check = |env: Environment, candidate: &SimpResult| {
                    let state =
                        ProofState::new(env, Expr::const_(Name::from_string("True"), vec![]));
                    rewrite_condition(
                        &state,
                        state.current_goal().unwrap(),
                        &original,
                        candidate,
                        &SimpBudget::for_target(&original),
                    )
                };
                assert!(
                    check(imported.clone(), &changed).is_some(),
                    "real imported theorem checks"
                );
                let mut missing = imported.clone();
                assert!(missing.forget_decl(&Name::from_string("ite_congr")));
                assert!(check(missing.clone(), &changed).is_none());
                missing
                    .add_decl(Declaration::Axiom {
                        name: Name::from_string("ite_congr"),
                        level_params: vec![],
                        type_: Expr::const_(Name::from_string("True"), vec![]),
                    })
                    .unwrap();
                assert!(
                    check(missing, &changed).is_none(),
                    "a homonym is not the theorem"
                );
                let wrong_proof = SimpResult {
                    expr: changed.expr.clone(),
                    proof: Some(Expr::const_(Name::from_string("True.intro"), vec![])),
                };
                assert!(
                    check(imported.clone(), &wrong_proof).is_none(),
                    "wrong condition witness"
                );
                let mut unavailable = imported;
                let unknown = Expr::const_(Name::from_string("unknownCondition"), vec![]);
                unavailable
                    .add_decl(Declaration::Axiom {
                        name: Name::from_string("unknownCondition"),
                        level_params: vec![],
                        type_: Expr::prop(),
                    })
                    .unwrap();
                unavailable
                    .add_decl(Declaration::Axiom {
                        name: Name::from_string("conditionEquality"),
                        level_params: vec![],
                        type_: Expr::apps(
                            Expr::const_(Name::from_string("Eq"), vec![one]),
                            [Expr::prop(), old, unknown.clone()],
                        ),
                    })
                    .unwrap();
                let unavailable_instance = SimpResult {
                    expr: unknown,
                    proof: Some(Expr::const_(Name::from_string("conditionEquality"), vec![])),
                };
                assert!(
                    check(unavailable, &unavailable_instance).is_none(),
                    "no Decidable of new condition"
                );
            })
            .unwrap()
            .join()
            .unwrap();
    }
}
