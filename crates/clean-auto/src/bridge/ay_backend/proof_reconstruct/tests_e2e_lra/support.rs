// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared helpers for LRA e2e proof reconstruction tests.

use super::*;

pub(super) type LraHypothesisSetup = Vec<(FVarId, &'static str, Expr)>;

pub(super) fn ensure_int_add_eq_lemma_support(env: &mut Environment) {
    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    let int_add = Expr::const_(Name::from_string("Int.add"), vec![]);
    let int_zero = Expr::app(
        Expr::const_(Name::from_string("Int.ofNat"), vec![]),
        Expr::nat_lit(0),
    );
    let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    let mk_int_eq = |lhs: Expr, rhs: Expr| {
        Expr::app(Expr::app(Expr::app(eq.clone(), int_ty.clone()), lhs), rhs)
    };

    if env.get_const(&Name::from_string("Int.add_comm")).is_none() {
        let a = Expr::bvar(1);
        let b = Expr::bvar(0);
        let lhs = Expr::app(Expr::app(int_add.clone(), a.clone()), b.clone());
        let rhs = Expr::app(Expr::app(int_add.clone(), b), a);
        let type_ = Expr::pi(
            BinderInfo::Default,
            int_ty.clone(),
            Expr::pi(BinderInfo::Default, int_ty.clone(), mk_int_eq(lhs, rhs)),
        );
        env.add_decl(Declaration::Axiom {
            name: Name::from_string("Int.add_comm"),
            level_params: vec![],
            type_,
        })
        .expect("add Int.add_comm");
    }

    if env.get_const(&Name::from_string("Int.add_assoc")).is_none() {
        let a = Expr::bvar(2);
        let b = Expr::bvar(1);
        let c = Expr::bvar(0);
        let ab = Expr::app(Expr::app(int_add.clone(), a.clone()), b.clone());
        let bc = Expr::app(Expr::app(int_add.clone(), b), c.clone());
        let lhs = Expr::app(Expr::app(int_add.clone(), ab), c);
        let rhs = Expr::app(Expr::app(int_add.clone(), a), bc);
        let type_ = Expr::pi(
            BinderInfo::Default,
            int_ty.clone(),
            Expr::pi(
                BinderInfo::Default,
                int_ty.clone(),
                Expr::pi(BinderInfo::Default, int_ty.clone(), mk_int_eq(lhs, rhs)),
            ),
        );
        env.add_decl(Declaration::Axiom {
            name: Name::from_string("Int.add_assoc"),
            level_params: vec![],
            type_,
        })
        .expect("add Int.add_assoc");
    }

    if env.get_const(&Name::from_string("Int.zero_add")).is_none() {
        let a = Expr::bvar(0);
        let lhs = Expr::app(Expr::app(int_add, int_zero), a.clone());
        let type_ = Expr::pi(BinderInfo::Default, int_ty.clone(), mk_int_eq(lhs, a));
        env.add_decl(Declaration::Axiom {
            name: Name::from_string("Int.zero_add"),
            level_params: vec![],
            type_,
        })
        .expect("add Int.zero_add");
    }
}

pub(super) fn ensure_int_hadd_support(env: &mut Environment) {
    env.init_hadd().expect("init_hadd for HAdd.hAdd");
    if env.get_const(&Name::from_string("instHAddInt")).is_some() {
        return;
    }

    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    let h_add = Expr::const_(
        Name::from_string("HAdd"),
        vec![Level::zero(), Level::zero(), Level::zero()],
    );
    let h_add_mk = Expr::const_(
        Name::from_string("HAdd.mk"),
        vec![Level::zero(), Level::zero(), Level::zero()],
    );
    let inst_type = Expr::app(
        Expr::app(Expr::app(h_add, int_ty.clone()), int_ty.clone()),
        int_ty.clone(),
    );
    let inst_value = Expr::app(
        Expr::app(
            Expr::app(Expr::app(h_add_mk, int_ty.clone()), int_ty.clone()),
            int_ty.clone(),
        ),
        Expr::const_(Name::from_string("Int.add"), vec![]),
    );

    env.add_decl(Declaration::Definition {
        name: Name::from_string("instHAddInt"),
        level_params: vec![],
        type_: inst_type,
        value: inst_value,
        is_reducible: true,
    })
    .expect("add instHAddInt");
}

/// Create an environment for type-checking Int LRA proof terms.
pub(crate) fn mk_env_for_lra() -> Environment {
    let mut env = Environment::new();
    env.init_int_ord_lemmas()
        .expect("init_int_ord_lemmas (pulls in all Int arithmetic + ordering)");
    ensure_int_add_eq_lemma_support(&mut env);
    ensure_int_hadd_support(&mut env);

    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    for name in ["testX", "testY", "testZ", "testW"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: int_ty.clone(),
        })
        .expect("add Int test axiom decl");
    }
    env
}

/// Create an environment for type-checking Real LRA proof terms that downcast
/// through the Int additive closing path.
pub(crate) fn mk_env_for_real_lra() -> Environment {
    let mut env = Environment::new();
    env.init_true_false()
        .expect("init_true_false for False/Not/absurd");
    env.init_int_ord_lemmas()
        .expect("init_int_ord_lemmas for downcast Int chain/additive closers");
    ensure_int_add_eq_lemma_support(&mut env);
    env.init_real_linear_order()
        .expect("init_real_linear_order (pulls in Real order/additive/downcast axioms)");
    ensure_int_hadd_support(&mut env);
    env.init_real_hadd_inst()
        .expect("init_real_hadd_inst for symbolic Real additive terms");
    env.init_real_hmul_inst()
        .expect("init_real_hmul_inst for symbolic Real multiplicative terms");
    env.init_real_neg_inst()
        .expect("init_real_neg_inst for symbolic Real negation terms");
    env.init_ite()
        .expect("init_ite for translated ay ite terms");

    let real_ty = Expr::const_(Name::from_string("Real"), vec![]);
    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    for name in ["testX", "testY"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: real_ty.clone(),
        })
        .expect("add Real test axiom decl");
    }
    for name in ["testXI", "testYI"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: int_ty.clone(),
        })
        .expect("add Int downcast test axiom decl");
    }
    env
}

/// Build `@LE.le.{0} Int instLEInt a b`.
pub(crate) fn mk_le_int(a: &Expr, b: &Expr) -> Expr {
    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
                    int_ty,
                ),
                Expr::const_(Name::from_string("instLEInt"), vec![]),
            ),
            a.clone(),
        ),
        b.clone(),
    )
}

/// Build `@Int.ofNat (Nat.lit n)` — a concrete Int from a natural number.
pub(crate) fn mk_int_ofnat(n: u64) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Int.ofNat"), vec![]),
        Expr::nat_lit(n),
    )
}

pub(crate) fn mk_int_add_expr(a: &Expr, b: &Expr) -> Expr {
    super::super::expr_builders::mk_add(&Sort::Int, a, b)
}

pub(crate) fn mk_real_add_expr(a: &Expr, b: &Expr) -> Expr {
    super::super::expr_builders::mk_add(&Sort::Real, a, b)
}

/// Build `Real.ofNat n`.
pub(crate) fn mk_real_ofnat(n: u64) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Real.ofNat"), vec![]),
        Expr::nat_lit(n),
    )
}

pub(crate) fn mk_real_ofint_expr(a: &Expr) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Real.ofInt"), vec![]),
        a.clone(),
    )
}

/// Build a concrete Real integer literal in kernel form.
pub(crate) fn mk_real_int_const_expr(value: i64) -> Expr {
    if value >= 0 {
        return mk_real_ofnat(value as u64);
    }

    Expr::app(
        Expr::const_(Name::from_string("Real.ofInt"), vec![]),
        Expr::app(
            Expr::const_(Name::from_string("Int.negSucc"), vec![]),
            Expr::nat_lit((-value - 1) as u64),
        ),
    )
}

/// Build `@LE.le.{0} Real instLEReal a b`.
pub(crate) fn mk_le_real(a: &Expr, b: &Expr) -> Expr {
    let real_ty = Expr::const_(Name::from_string("Real"), vec![]);
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
                    real_ty,
                ),
                Expr::const_(Name::from_string("instLEReal"), vec![]),
            ),
            a.clone(),
        ),
        b.clone(),
    )
}

/// Build `@LT.lt.{0} Real instLTReal a b`.
pub(crate) fn mk_lt_real(a: &Expr, b: &Expr) -> Expr {
    let real_ty = Expr::const_(Name::from_string("Real"), vec![]);
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("LT.lt"), vec![Level::zero()]),
                    real_ty,
                ),
                Expr::const_(Name::from_string("instLTReal"), vec![]),
            ),
            a.clone(),
        ),
        b.clone(),
    )
}

pub(super) fn negated_false_goal() -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Not"), vec![]),
        Expr::const_(Name::from_string("False"), vec![]),
    )
}

pub(super) fn add_three_literal_farkas_resolution(
    proof: &mut Proof,
    clause: [ay_core::TermId; 3],
    assumptions: [ay_core::TermId; 3],
) {
    let [not_a, not_b, not_c] = clause;
    let [a, b, c] = assumptions;
    let farkas = FarkasAnnotation::from_ints(&[1, 1, 1]);
    let s0 = proof.add_theory_lemma_with_farkas("LRA", vec![not_a, not_b, not_c], farkas);
    let s1 = proof.add_assume(a, None);
    let s2 = proof.add_resolution(vec![not_b, not_c], not_a, s0, s1);
    let s3 = proof.add_assume(b, None);
    let s4 = proof.add_resolution(vec![not_c], not_b, s2, s3);
    let s5 = proof.add_assume(c, None);
    proof.add_resolution(vec![], not_c, s4, s5);
}
