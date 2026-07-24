// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use crate::bridge::ay_backend::{
    AyLogic, AyProofBackend, AyProofResult, KernelReconstructionCandidate, TrustBudget,
};
use clean_kernel::name::Name;
use clean_kernel::{Declaration, Environment, Expr, FVarId, Level};

pub(super) fn reconstruct_refutation_from_backend(
    backend: &mut AyProofBackend,
    map: &super::VariableMapping,
    negated_goal: &Expr,
) -> KernelReconstructionCandidate {
    reconstruct_refutation_from_backend_with_budget(
        backend,
        map,
        negated_goal,
        TrustBudget::Unlimited,
    )
}

pub(super) fn reconstruct_refutation_from_backend_with_budget(
    backend: &mut AyProofBackend,
    map: &super::VariableMapping,
    negated_goal: &Expr,
    budget: TrustBudget,
) -> KernelReconstructionCandidate {
    let result = backend
        .check_sat()
        .expect("clean backend should solve the fixture");
    assert!(
        matches!(&result, AyProofResult::Unsat { .. }),
        "expected UNSAT from clean backend, got {result:?}",
    );
    backend
        .attempt_kernel_reconstruction_with_budget(map, negated_goal, budget)
        .expect("clean must produce an accepted refutation for the positive contract fixture")
}

pub(super) fn neg_false() -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Not"), vec![]),
        Expr::const_(Name::from_string("False"), vec![]),
    )
}

pub(super) fn mk_bool_env() -> Environment {
    let mut env = Environment::new();
    env.init_true_false().expect("init_true_false");
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("P"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .expect("add P : Prop");
    env
}

pub(super) fn mk_bool_backend_and_mapping(
) -> (AyProofBackend, super::VariableMapping, [FVarId; 2], Expr) {
    let p_prop = Expr::const_(Name::from_string("P"), vec![]);
    let not_p = Expr::app(
        Expr::const_(Name::from_string("Not"), vec![]),
        p_prop.clone(),
    );

    let h_p_id = FVarId::new(30);
    let h_not_p_id = FVarId::new(31);

    let mut backend = AyProofBackend::new_with_proofs(AyLogic::QfUf);
    let p_name = backend.fresh_bool("P");
    backend.assert_formula(&p_name);
    backend.assert_formula(&format!("(not {p_name})"));

    let mut map = super::VariableMapping::new();
    map.register_var(&p_name, p_prop.clone(), Expr::prop());
    map.register_hypothesis(&p_name, h_p_id, Expr::fvar(h_p_id), p_prop);
    map.register_hypothesis("h_not_p", h_not_p_id, Expr::fvar(h_not_p_id), not_p.clone());

    (backend, map, [h_p_id, h_not_p_id], not_p)
}

pub(super) fn mk_qf_uf_env() -> Environment {
    let mut env = Environment::new();
    env.init_eq().expect("init_eq");
    env.init_true_false().expect("init_true_false");
    env.init_classical().expect("init_classical");

    let u_sort = Expr::sort(Level::succ(Level::zero()));
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("U"),
        level_params: vec![],
        type_: u_sort,
    })
    .expect("add U : Sort 1");

    let u_ty = Expr::const_(Name::from_string("U"), vec![]);
    for name in ["a", "b", "c"] {
        let add_result = env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: u_ty.clone(),
        });
        assert!(add_result.is_ok(), "add {name}: {add_result:?}");
    }
    env
}

pub(super) fn mk_eq_u(x: &str, y: &str) -> Expr {
    let u_ty = Expr::const_(Name::from_string("U"), vec![]);
    let u1 = Level::succ(Level::zero());
    Expr::app(
        Expr::app(
            Expr::app(Expr::const_(Name::from_string("Eq"), vec![u1]), u_ty),
            Expr::const_(Name::from_string(x), vec![]),
        ),
        Expr::const_(Name::from_string(y), vec![]),
    )
}

pub(super) fn mk_qf_uf_backend_and_mapping(
) -> (AyProofBackend, super::VariableMapping, [FVarId; 3], Expr) {
    let u_ty = Expr::const_(Name::from_string("U"), vec![]);
    let eq_ab = mk_eq_u("a", "b");
    let eq_bc = mk_eq_u("b", "c");
    let neq_ac = Expr::app(
        Expr::const_(Name::from_string("Not"), vec![]),
        mk_eq_u("a", "c"),
    );

    let h_ab_id = FVarId::new(40);
    let h_bc_id = FVarId::new(41);
    let h_neq_ac_id = FVarId::new(42);

    let mut backend = AyProofBackend::new_with_proofs(AyLogic::QfUf);
    backend.add_raw_declaration("(declare-sort U 0)");
    backend.add_raw_declaration("(declare-fun a () U)");
    backend.add_raw_declaration("(declare-fun b () U)");
    backend.add_raw_declaration("(declare-fun c () U)");
    backend.assert_formula("(= a b)");
    backend.assert_formula("(= b c)");
    backend.assert_formula("(not (= a c))");

    let mut map = super::VariableMapping::new();
    for (smt_name, lean_name) in [("a", "a"), ("b", "b"), ("c", "c")] {
        map.register_var(
            smt_name,
            Expr::const_(Name::from_string(lean_name), vec![]),
            u_ty.clone(),
        );
    }
    map.register_hypothesis("h_ab", h_ab_id, Expr::fvar(h_ab_id), eq_ab);
    map.register_hypothesis("h_bc", h_bc_id, Expr::fvar(h_bc_id), eq_bc);
    map.register_hypothesis(
        "h_neq_ac",
        h_neq_ac_id,
        Expr::fvar(h_neq_ac_id),
        neq_ac.clone(),
    );

    (backend, map, [h_ab_id, h_bc_id, h_neq_ac_id], neq_ac)
}

pub(super) fn mk_qf_lia_env() -> Environment {
    let mut env = Environment::new();
    env.init_int_ord_lemmas()
        .expect("init_int_ord_lemmas (pulls in Int arithmetic + ordering)");

    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("x"),
        level_params: vec![],
        type_: int_ty,
    })
    .expect("add x : Int");
    env
}

pub(super) fn mk_lt_int(a: &Expr, b: &Expr) -> Expr {
    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("LT.lt"), vec![Level::zero()]),
                    int_ty,
                ),
                Expr::const_(Name::from_string("instLTInt"), vec![]),
            ),
            a.clone(),
        ),
        b.clone(),
    )
}

pub(super) fn mk_int_ofnat(n: u64) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Int.ofNat"), vec![]),
        Expr::nat_lit(n),
    )
}

pub(super) fn mk_qf_lia_backend_and_mapping() -> (
    AyProofBackend,
    super::VariableMapping,
    [FVarId; 2],
    Expr,
    Expr,
) {
    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    let x_expr = Expr::const_(Name::from_string("x"), vec![]);
    let zero = mk_int_ofnat(0);

    let lt_x_0 = mk_lt_int(&x_expr, &zero);
    let lt_0_x = mk_lt_int(&zero, &x_expr);

    let h_x_neg_id = FVarId::new(50);
    let h_x_pos_id = FVarId::new(51);

    let mut backend = AyProofBackend::new_with_proofs(AyLogic::QfLia);
    let x_smt = backend.fresh_int("x");
    backend.assert_formula(&format!("(< {x_smt} 0)"));
    backend.assert_formula(&format!("(< 0 {x_smt})"));

    let mut map = super::VariableMapping::new();
    map.register_var(&x_smt, x_expr, int_ty);
    map.register_hypothesis(
        "h_x_neg",
        h_x_neg_id,
        Expr::fvar(h_x_neg_id),
        lt_x_0.clone(),
    );
    map.register_hypothesis(
        "h_x_pos",
        h_x_pos_id,
        Expr::fvar(h_x_pos_id),
        lt_0_x.clone(),
    );

    (backend, map, [h_x_neg_id, h_x_pos_id], lt_x_0, lt_0_x)
}
