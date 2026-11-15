// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Already-realized equation theorems, including imported course-of-values
//! definitions. Lean's `Meta.Eqns.alreadyGenerated?` reads the contiguous
//! `f.eq_1`, `f.eq_2`, ... family before attempting equation generation.
//! Read actual theorem statements here; never infer a rewrite from a name.

use clean_kernel::env::ConstantKind;
use clean_kernel::{Environment, ExprKind, Name};

use super::expr::extract_equality_full;
use super::types::{SimpIndexMode, SimpLemma};

pub(super) fn collect(
    env: &Environment,
    definition: &Name,
    priority: u32,
) -> Option<Vec<SimpLemma>> {
    let decl = env.get_const(definition)?;
    if !matches!(decl.kind, ConstantKind::Definition) {
        return None;
    }
    let mut result = Vec::new();
    let mut index = 1usize;
    loop {
        let name = definition.clone().str(format!("eq_{index}"));
        let Some(equation) = env.get_const(&name) else {
            break;
        };
        // A coincidentally named axiom or unrelated statement is not an
        // equation family. Decline the whole family, keeping the old fallback.
        if !matches!(equation.kind, ConstantKind::Theorem) || equation.value.is_none() {
            return None;
        }
        let (eq_type, lhs, rhs) = extract_equality_full(&equation.type_)?;
        if !matches!(lhs.get_app_fn().kind(), ExprKind::Const(head, _) if head == definition) {
            return None;
        }
        result.push(SimpLemma {
            name,
            lhs,
            rhs,
            eq_type: Some(eq_type),
            proof_expr: None,
            index_mode: SimpIndexMode::Normal,
            priority,
        });
        index = index.checked_add(1)?;
    }
    (!result.is_empty()).then_some(result)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn add(env: &mut Environment, source: &str) {
        let patterns = crate::tactic::builtins::builtin_tactic_patterns();
        let decl =
            clean_parser::parse_decl_with_tactics(source, &patterns).expect("fixture parses");
        crate::elaborate_decl_and_register(env, &decl).expect("fixture kernel checks");
    }

    #[test]
    fn declared_equations_require_a_proved_family_with_the_right_head() {
        let mut env = Environment::with_prelude();
        add(&mut env, "def fixture (x : Nat) : Nat := x");
        add(
            &mut env,
            "theorem fixture.eq_1 (x : Nat) : fixture x = x := by rfl",
        );
        let name = Name::from_string("fixture");
        let equations = collect(&env, &name, 27).expect("actual equation");
        assert_eq!(equations.len(), 1);
        assert_eq!(equations[0].priority, 27);
        add(&mut env, "axiom fixture.eq_2 : fixture 0 = 0");
        assert!(
            collect(&env, &name, 27).is_none(),
            "an axiom is not an equation proof"
        );
    }

    #[test]
    fn declared_equations_refuse_unrelated_named_theorems() {
        let mut env = Environment::with_prelude();
        add(&mut env, "def fixture (x : Nat) : Nat := x");
        add(&mut env, "theorem fixture.eq_1 (x : Nat) : x = x := by rfl");
        assert!(collect(&env, &Name::from_string("fixture"), 50).is_none());
    }
}
