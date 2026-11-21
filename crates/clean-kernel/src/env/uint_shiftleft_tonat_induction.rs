// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Induction over the actual native Nat.shiftLeft recursion, without a name-based reduction.
use super::*;
fn eq(a: Expr, b: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [k("Nat"), a, b],
    )
}
fn symmetry(a: Expr, b: Expr, proof: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.symm"),
            vec![Level::succ(Level::zero())],
        ),
        [k("Nat"), a, b, proof],
    )
}
pub(super) fn declaration() -> Declaration {
    let mut scope = EnvDeclBuilder::new();
    let (m_id, m) = scope.fresh_local(k("Nat"));
    let (n_id, n) = scope.fresh_local(k("Nat"));
    let power = |n| app("Nat.pow", [Expr::nat_lit(2), n]);
    let product = |n| app("Nat.mul", [m.clone(), power(n)]);
    let statement = |n: Expr| eq(app("Nat.shiftLeft", [m.clone(), n.clone()]), product(n));
    let claim = statement(n.clone());
    let base = symmetry(
        app("Nat.mul", [m.clone(), Expr::nat_lit(1)]),
        m.clone(),
        app("Nat.mul_one", [m.clone()]),
    );
    let (step_id, step) = scope.fresh_local(k("Nat"));
    let (ih_id, ih) = scope.fresh_local(statement(step.clone()));
    let left = app(
        "Nat.mul",
        [
            app("Nat.shiftLeft", [m.clone(), step.clone()]),
            Expr::nat_lit(2),
        ],
    );
    let mid = app("Nat.mul", [product(step.clone()), Expr::nat_lit(2)]);
    let right = app(
        "Nat.mul",
        [
            m.clone(),
            app("Nat.mul", [power(step.clone()), Expr::nat_lit(2)]),
        ],
    );
    let congruence = Expr::apps(
        Expr::const_(
            Name::from_string("congrArg"),
            vec![Level::succ(Level::zero()), Level::succ(Level::zero())],
        ),
        [
            k("Nat"),
            k("Nat"),
            app("Nat.shiftLeft", [m.clone(), step.clone()]),
            product(step.clone()),
            Expr::lam(
                BinderInfo::Default,
                k("Nat"),
                app("Nat.mul", [Expr::bvar(0), Expr::nat_lit(2)]),
            ),
            ih,
        ],
    );
    let next = Expr::apps(
        Expr::const_(
            Name::from_string("Eq.trans"),
            vec![Level::succ(Level::zero())],
        ),
        [
            k("Nat"),
            left,
            mid,
            right,
            congruence,
            app(
                "Nat.mul_assoc",
                [m.clone(), power(step.clone()), Expr::nat_lit(2)],
            ),
        ],
    );
    let next = scope.mk_lam(ih_id, BinderInfo::Default, statement(step.clone()), next);
    let next = scope.mk_lam(step_id, BinderInfo::Default, k("Nat"), next);
    let motive = scope.mk_lam(n_id, BinderInfo::Default, k("Nat"), claim.clone());
    let proof = Expr::apps(
        Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
        [motive, base, next, n],
    );
    let claim = scope.mk_pi(n_id, BinderInfo::Default, k("Nat"), claim);
    let claim = scope.mk_pi(m_id, BinderInfo::Default, k("Nat"), claim);
    let proof = scope.mk_lam(n_id, BinderInfo::Default, k("Nat"), proof);
    let proof = scope.mk_lam(m_id, BinderInfo::Default, k("Nat"), proof);
    Declaration::Theorem {
        name: Name::from_string("Nat.shiftLeft_eq"),
        level_params: vec![],
        type_: scope.finish(claim),
        value: scope.finish(proof),
    }
}
