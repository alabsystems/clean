// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! F1: isolate theory gating from fold-origin authority in its own process.
//! Test-fixture authority bypass makes Extended the positive native-fold control;
//! opaque heads prevent ordinary delta reduction from explaining the result.
use clean_kernel::env::native_fold_mint_bypass;
use clean_kernel::{
    BigNat, BinderInfo, Declaration, Environment, Expr, Level, Name, ReferenceKernel, TheoryId,
    TypeChecker,
};

fn c(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}
fn eq(ty: Expr, left: Expr, right: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [ty, left, right],
    )
}
fn refl(ty: Expr, value: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [ty, value],
    )
}
fn probe(head: &str, domain: Expr, arity: usize, body: Expr, arguments: Vec<Expr>, result: Expr) {
    assert!(
        !TheoryId::LeanReferenceV1.nat_extensions().contains(&head),
        "probe head must be outside the digested reference rule inventory"
    );
    native_fold_mint_bypass::run(|| {
        let mut env = Environment::with_prelude();
        env.forget_decl(&Name::from_string(head));
        let mut ty = domain.clone();
        let mut value = body;
        for _ in 0..arity {
            ty = Expr::arrow(domain.clone(), ty);
            value = Expr::lam(BinderInfo::Default, domain.clone(), value);
        }
        env.add_decl(Declaration::Opaque {
            name: Name::from_string(head),
            level_params: vec![],
            type_: ty,
            value,
        })
        .expect("well-typed opaque fold control");
        let term = Expr::apps(c(head), arguments);
        let proposed = eq(domain.clone(), term.clone(), result.clone());
        let proof = refl(domain.clone(), result.clone());
        TypeChecker::new(&env)
            .check_type(&proof, &proposed)
            .expect("Extended native-fold positive");
        let kernel = ReferenceKernel::new(env).expect("fenced entry");
        kernel
            .check_closed_term(
                &eq(domain.clone(), term.clone(), term.clone()),
                &refl(domain.clone(), term),
            )
            .expect("same head is well-typed through the actual entry");
        kernel
            .check_closed_term(&eq(domain.clone(), result.clone(), result.clone()), &proof)
            .expect("the same proof passes its real reflexive type");
        let refusal = kernel.check_closed_term(&proposed, &proof);
        assert!(
            refusal.is_err(),
            "{head}: hard-wired native fold escaped the reference fence: {refusal:?}"
        );
    });
}
#[test]
fn reference_refuses_int_big_literal_fold() {
    let big = BigNat::from_limbs(vec![0, 2]);
    let successor = big.checked_add_big(&BigNat::Small(1));
    probe(
        "Int.add",
        c("Int"),
        2,
        Expr::app(c("Int.ofNat"), Expr::nat_lit(0)),
        vec![
            Expr::app(c("Int.ofNat"), Expr::bignat_lit(big)),
            Expr::app(c("Int.ofNat"), Expr::nat_lit(1)),
        ],
        Expr::app(c("Int.ofNat"), Expr::bignat_lit(successor)),
    );
}
#[test]
fn reference_refuses_nat_pred_fold() {
    probe(
        "Nat.pred",
        c("Nat"),
        1,
        Expr::nat_lit(0),
        vec![Expr::nat_lit(2)],
        Expr::nat_lit(1),
    );
}
#[test]
fn reference_refuses_reduce_bool_fold() {
    probe(
        "Lean.reduceBool",
        c("Bool"),
        1,
        c("Bool.false"),
        vec![c("Bool.true")],
        c("Bool.true"),
    );
}
#[test]
fn reference_refuses_reduce_nat_fold() {
    probe(
        "Lean.reduceNat",
        c("Nat"),
        1,
        Expr::nat_lit(0),
        vec![Expr::nat_lit(2)],
        Expr::nat_lit(2),
    );
}

#[test]
fn reference_refuses_int_big_literal_sub_fold() {
    let big = BigNat::from_limbs(vec![0, 2]);
    let predecessor = big.saturating_sub_big(&BigNat::Small(1));
    probe(
        "Int.sub",
        c("Int"),
        2,
        Expr::app(c("Int.ofNat"), Expr::nat_lit(0)),
        vec![
            Expr::app(c("Int.ofNat"), Expr::bignat_lit(big)),
            Expr::app(c("Int.ofNat"), Expr::nat_lit(1)),
        ],
        Expr::app(c("Int.ofNat"), Expr::bignat_lit(predecessor)),
    );
}
#[test]
fn reference_refuses_int_big_literal_mul_fold() {
    let big = BigNat::from_limbs(vec![0, 2]);
    let twice = big
        .checked_mul_big(&BigNat::Small(2))
        .expect("two-limb product");
    probe(
        "Int.mul",
        c("Int"),
        2,
        Expr::app(c("Int.ofNat"), Expr::nat_lit(0)),
        vec![
            Expr::app(c("Int.ofNat"), Expr::bignat_lit(big)),
            Expr::app(c("Int.ofNat"), Expr::nat_lit(2)),
        ],
        Expr::app(c("Int.ofNat"), Expr::bignat_lit(twice)),
    );
}
