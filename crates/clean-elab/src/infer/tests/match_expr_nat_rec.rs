// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Focused first-arm expected-type regressions for match elaboration.

use super::*;

fn expr_contains_any<'a>(exprs: impl IntoIterator<Item = &'a Expr>, needle: &str) -> bool {
    exprs
        .into_iter()
        .any(|expr| expr_contains_const(expr, needle))
}

fn expr_contains_const(expr: &Expr, needle: &str) -> bool {
    match expr.kind() {
        ExprKind::Const(name, _) => name.to_string() == needle,
        ExprKind::App(f, a) => expr_contains_any([f.as_ref(), a.as_ref()], needle),
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            expr_contains_any([ty.as_ref(), body.as_ref()], needle)
        }
        ExprKind::Let(_, ty, val, body, _) => {
            expr_contains_any([ty.as_ref(), val.as_ref(), body.as_ref()], needle)
        }
        ExprKind::MData(_, inner)
        | ExprKind::Squash(inner)
        | ExprKind::Proj(_, _, inner)
        | ExprKind::CubicalPathLam { body: inner } => expr_contains_const(inner, needle),
        ExprKind::CubicalPath { ty, left, right } => {
            expr_contains_any([ty.as_ref(), left.as_ref(), right.as_ref()], needle)
        }
        ExprKind::CubicalPathApp { path, arg } => {
            expr_contains_any([path.as_ref(), arg.as_ref()], needle)
        }
        ExprKind::CubicalHComp { ty, phi, u, base } => expr_contains_any(
            [ty.as_ref(), phi.as_ref(), u.as_ref(), base.as_ref()],
            needle,
        ),
        ExprKind::CubicalTransp { ty, phi, base } => {
            expr_contains_any([ty.as_ref(), phi.as_ref(), base.as_ref()], needle)
        }
        ExprKind::CubicalCoe { ty, r, s, base } => {
            expr_contains_any([ty.as_ref(), r.as_ref(), s.as_ref(), base.as_ref()], needle)
        }
        ExprKind::ZFCMem { element, set } => {
            expr_contains_any([element.as_ref(), set.as_ref()], needle)
        }
        ExprKind::ZFCComprehension { domain, pred } => {
            expr_contains_any([domain.as_ref(), pred.as_ref()], needle)
        }
        ExprKind::Sort(_)
        | ExprKind::BVar(_)
        | ExprKind::FVar(_)
        | ExprKind::Lit(_)
        | ExprKind::SProp
        | ExprKind::CubicalInterval
        | ExprKind::CubicalI0
        | ExprKind::CubicalI1
        | ExprKind::ZFCSet(_) => false,
    }
}

fn elaborate_decl(env: &mut Environment, decl_src: &str) {
    let decl = parse_decl_for_elab(decl_src).expect("match regression decl should parse");
    let result = crate::elaborate_decl_and_register(env, &decl);
    assert!(
        result.is_ok(),
        "match regression decl should elaborate, got {result:?} for {decl_src}"
    );
}

fn definition_value<'a>(env: &'a Environment, name: &str) -> &'a Expr {
    env.get_const(&Name::from_string(name))
        .unwrap_or_else(|| panic!("{name} should be registered after elaboration"))
        .value
        .as_ref()
        .unwrap_or_else(|| panic!("{name} should keep an elaborated value"))
}

fn assert_match_definition_uses_int_of_nat(name: &str, decl_src: &str) {
    let mut env = Environment::with_prelude();
    elaborate_decl(&mut env, decl_src);
    let value = definition_value(&env, name);
    assert!(
        expr_contains_const(value, "Int.ofNat"),
        "{name} should elaborate match-arm literals against the expected Int result type, got {value:?}"
    );
}

/// #2727: wildcard first-arm inference must thread the enclosing expected type.
#[test]
fn test_match_first_arm_wildcard_threads_expected_type() {
    assert_match_definition_uses_int_of_nat(
        "match_first_arm_wildcard_int",
        r"def match_first_arm_wildcard_int (b : Bool) : Int := match b with
            | _ => 0
            | Bool.true => 1",
    );
}

/// #2727: nullary constructor first-arm inference must thread the expected type.
#[test]
fn test_match_first_arm_nullary_ctor_threads_expected_type() {
    assert_match_definition_uses_int_of_nat(
        "match_first_arm_nullary_ctor_int",
        r"def match_first_arm_nullary_ctor_int (b : Bool) : Int := match b with
            | Bool.true => 0
            | Bool.false => 1",
    );
}

/// #2727 / #469: keep the concrete Nat.rec reproducer green for larger inductives.
#[test]
fn test_match_arm_nat_rec_body_elaborates_for_micro_expr() {
    let mut env = Environment::with_prelude();
    let decls = [
        r"inductive MicroLevel : Type
            | zero : MicroLevel
            | succ : MicroLevel -> MicroLevel",
        r"inductive MicroExpr : Type
            | bvar : Nat -> MicroExpr
            | sort : MicroLevel -> MicroExpr
            | app : MicroExpr -> MicroExpr -> MicroExpr
            | lam : MicroExpr -> MicroExpr -> MicroExpr
            | pi : MicroExpr -> MicroExpr -> MicroExpr
            | let_ : MicroExpr -> MicroExpr -> MicroExpr -> MicroExpr
            | opaque_ : MicroExpr -> MicroExpr",
        r"def micro_inline_nat_rec (body : MicroExpr) (val : MicroExpr) : MicroExpr := match body with
            | MicroExpr.bvar i => Nat.rec (fun _ => MicroExpr) val (fun n _ => MicroExpr.bvar n) i
            | _ => val",
    ];

    for decl_src in decls {
        elaborate_decl(&mut env, decl_src);
    }

    assert!(
        env.get_const(&Name::from_string("micro_inline_nat_rec"))
            .is_some(),
        "micro_inline_nat_rec should be registered after elaboration"
    );
}
