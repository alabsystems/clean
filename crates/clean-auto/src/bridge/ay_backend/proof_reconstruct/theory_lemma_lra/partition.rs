// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Additive-atom partition helpers for LRA Farkas reconstruction.

use clean_kernel::Expr;
use std::collections::HashSet;

use super::super::expr_builders_arith;
use super::ActiveBound;

pub(super) fn connected_bound_components<'a>(
    bounds: &'a [ActiveBound<'a>],
) -> Vec<Vec<ActiveBound<'a>>> {
    let atom_sets = bounds.iter().map(active_bound_atoms).collect::<Vec<_>>();
    let mut visited = vec![false; bounds.len()];
    let mut components = Vec::new();

    for start in 0..bounds.len() {
        if visited[start] {
            continue;
        }

        visited[start] = true;
        let mut stack = vec![start];
        let mut component = Vec::new();

        while let Some(idx) = stack.pop() {
            component.push(bounds[idx]);
            for next in 0..bounds.len() {
                if visited[next] || !atom_sets_related(&atom_sets[idx], &atom_sets[next]) {
                    continue;
                }
                visited[next] = true;
                stack.push(next);
            }
        }

        components.push(component);
    }

    components
}

fn atom_sets_related(lhs: &HashSet<Expr>, rhs: &HashSet<Expr>) -> bool {
    if lhs.is_empty() || rhs.is_empty() {
        return false;
    }

    let (smaller, larger) = if lhs.len() <= rhs.len() {
        (lhs, rhs)
    } else {
        (rhs, lhs)
    };
    smaller.iter().any(|atom| larger.contains(atom))
}

fn active_bound_atoms(bound: &ActiveBound<'_>) -> HashSet<Expr> {
    let mut atoms = HashSet::new();
    collect_additive_atoms(bound.sort(), bound.lhs_expr(), &mut atoms);
    collect_additive_atoms(bound.sort(), bound.rhs_expr(), &mut atoms);
    atoms
}

fn collect_additive_atoms(sort: &ay::Sort, expr: &Expr, atoms: &mut HashSet<Expr>) {
    crate::bridge::stack_safe(|| {
        let expr = expr.strip_mdata();
        if let Some((lhs, rhs)) = additive_children(sort, expr) {
            collect_additive_atoms(sort, lhs, atoms);
            collect_additive_atoms(sort, rhs, atoms);
            return;
        }

        let is_concrete = match sort {
            ay::Sort::Int => expr_builders_arith::extract_concrete_int_from_expr(expr).is_some(),
            ay::Sort::Real => {
                super::super::expr_builders_real_downcast::extract_concrete_int_from_real_expr(expr)
                    .is_some()
            }
            _ => false,
        };
        if is_concrete {
            return;
        }

        atoms.insert(expr.clone());
    })
}

fn additive_children<'a>(sort: &ay::Sort, expr: &'a Expr) -> Option<(&'a Expr, &'a Expr)> {
    use crate::bridge::head_family::{classify_arith_head_name, ArithFamily, SortHint};

    let args = expr.get_app_args();
    if args.len() < 2 {
        return None;
    }

    let name = match expr.get_app_fn().strip_mdata().kind() {
        clean_kernel::ExprKind::Const(name, _) => Some(name),
        _ => None,
    }?;

    let head = classify_arith_head_name(name)?;
    if head.family != ArithFamily::Add {
        return None;
    }
    // Direct forms must match the expected sort; typeclass forms match any sort.
    // Nat.add is not matched here — LRA reconstruction operates on Int/Real only.
    let sort_ok = match head.sort_hint {
        SortHint::Int => matches!(sort, ay::Sort::Int),
        SortHint::Real => matches!(sort, ay::Sort::Real),
        SortHint::Nat => false,
        SortHint::FromArgs => true,
    };
    if !sort_ok {
        return None;
    }

    let arity = args.len();
    Some((args[arity - 2], args[arity - 1]))
}

#[cfg(test)]
mod tests_additive_children {
    use clean_kernel::name::Name;

    use super::*;

    fn mk_add_app(head: &str, a: &Expr, b: &Expr) -> Expr {
        Expr::app(
            Expr::app(Expr::const_(Name::from_string(head), vec![]), a.clone()),
            b.clone(),
        )
    }

    #[test]
    fn test_nat_add_rejected_in_int_context() {
        // Nat.add should NOT match in LRA — reconstruction operates on Int/Real only.
        let a = Expr::bvar(0);
        let b = Expr::bvar(1);
        let nat_add = mk_add_app("Nat.add", &a, &b);
        assert!(
            additive_children(&ay::Sort::Int, &nat_add).is_none(),
            "Nat.add should be rejected in Int context"
        );
    }

    #[test]
    fn test_nat_add_rejected_in_real_context() {
        let a = Expr::bvar(0);
        let b = Expr::bvar(1);
        let nat_add = mk_add_app("Nat.add", &a, &b);
        assert!(
            additive_children(&ay::Sort::Real, &nat_add).is_none(),
            "Nat.add should be rejected in Real context"
        );
    }

    #[test]
    fn test_int_add_rejected_in_real_context() {
        // Sort mismatch: Int.add appearing with Real sort context.
        let a = Expr::bvar(0);
        let b = Expr::bvar(1);
        let int_add = mk_add_app("Int.add", &a, &b);
        assert!(
            additive_children(&ay::Sort::Real, &int_add).is_none(),
            "Int.add should be rejected in Real context"
        );
    }

    #[test]
    fn test_real_add_rejected_in_int_context() {
        let a = Expr::bvar(0);
        let b = Expr::bvar(1);
        let real_add = mk_add_app("Real.add", &a, &b);
        assert!(
            additive_children(&ay::Sort::Int, &real_add).is_none(),
            "Real.add should be rejected in Int context"
        );
    }

    #[test]
    fn test_int_add_accepted_in_int_context() {
        let a = Expr::bvar(0);
        let b = Expr::bvar(1);
        let int_add = mk_add_app("Int.add", &a, &b);
        let result = additive_children(&ay::Sort::Int, &int_add);
        assert!(result.is_some(), "Int.add should match in Int context");
        let (lhs, rhs) = result.expect("Int.add should yield two additive children");
        assert_eq!(*lhs, a);
        assert_eq!(*rhs, b);
    }

    #[test]
    fn test_real_add_accepted_in_real_context() {
        let a = Expr::bvar(0);
        let b = Expr::bvar(1);
        let real_add = mk_add_app("Real.add", &a, &b);
        let result = additive_children(&ay::Sort::Real, &real_add);
        assert!(result.is_some(), "Real.add should match in Real context");
    }

    #[test]
    fn test_typeclass_add_accepted_in_any_context() {
        // HAdd.hAdd (typeclass form) matches any sort since SortHint::FromArgs.
        let a = Expr::bvar(0);
        let b = Expr::bvar(1);
        let hadd = mk_add_app("HAdd.hAdd", &a, &b);
        assert!(
            additive_children(&ay::Sort::Int, &hadd).is_some(),
            "HAdd.hAdd should match in Int context"
        );
        assert!(
            additive_children(&ay::Sort::Real, &hadd).is_some(),
            "HAdd.hAdd should match in Real context"
        );
    }

    #[test]
    fn test_non_add_arith_rejected() {
        // Int.sub is ArithFamily::Sub, not Add — should be rejected.
        let a = Expr::bvar(0);
        let b = Expr::bvar(1);
        let int_sub = mk_add_app("Int.sub", &a, &b);
        assert!(
            additive_children(&ay::Sort::Int, &int_sub).is_none(),
            "Int.sub should not match as additive child"
        );
    }

    #[test]
    fn test_non_arith_head_rejected() {
        let a = Expr::bvar(0);
        let b = Expr::bvar(1);
        let and_expr = mk_add_app("And", &a, &b);
        assert!(
            additive_children(&ay::Sort::Int, &and_expr).is_none(),
            "And should not match as additive child"
        );
    }

    #[test]
    fn test_single_arg_rejected() {
        // additive_children requires >= 2 args.
        let a = Expr::bvar(0);
        let single_arg = Expr::app(Expr::const_(Name::from_string("Int.add"), vec![]), a);
        assert!(
            additive_children(&ay::Sort::Int, &single_arg).is_none(),
            "single-arg application should be rejected"
        );
    }
}

#[cfg(test)]
mod tests_connected_bound_components {
    use ay_core::TermId;
    use clean_kernel::name::Name;

    use super::super::super::expr_builders_arith::CmpOp;
    use super::super::super::theory_lemma_lra_chain::BoundInfo;
    use super::*;

    fn mk_expr(name: &str) -> Expr {
        Expr::const_(Name::from_string(name), vec![])
    }

    fn mk_bound(lhs_term: u32, rhs_term: u32, lhs_expr: &Expr, rhs_expr: &Expr) -> BoundInfo {
        BoundInfo {
            sort: ay::Sort::Int,
            op: CmpOp::Le,
            lhs_term: TermId(lhs_term),
            rhs_term: TermId(rhs_term),
            lhs_expr: lhs_expr.clone(),
            rhs_expr: rhs_expr.clone(),
        }
    }

    fn mk_active_bounds<'a>(bounds: &'a [BoundInfo]) -> Vec<ActiveBound<'a>> {
        bounds
            .iter()
            .enumerate()
            .map(|(clause_idx, bound)| ActiveBound { clause_idx, bound })
            .collect()
    }

    #[test]
    fn test_connected_bound_components_partitions_three_independent_groups() {
        let x = mk_expr("x");
        let y = mk_expr("y");
        let z = mk_expr("z");
        let a = mk_expr("a");
        let b = mk_expr("b");
        let c = mk_expr("c");
        let m = mk_expr("m");
        let n = mk_expr("n");

        let bounds = vec![
            mk_bound(1, 2, &x, &y),
            mk_bound(2, 3, &y, &z),
            mk_bound(10, 11, &a, &b),
            mk_bound(11, 12, &b, &c),
            mk_bound(20, 21, &m, &n),
        ];
        let active_bounds = mk_active_bounds(&bounds);

        let mut component_sizes = connected_bound_components(&active_bounds)
            .into_iter()
            .map(|component| component.len())
            .collect::<Vec<_>>();
        component_sizes.sort_unstable();

        assert_eq!(
            component_sizes,
            vec![1, 2, 2],
            "connected_bound_components should keep two linked pairs separate from an isolated singleton",
        );
    }
}
