// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Native SmtBridge vs AyBackend fast-path comparison benchmark.
//!
//! Part of #2386: measures whether the native solver lane earns its keep as a
//! fast path on the simple fragments clean actually routes through SMT.
//!
//! Three formula classes, matching existing cross-validation fixtures:
//! 1. QF_UF equality transitivity: a = b, b = c ⊢ a = c
//! 2. QF_UF congruence: a = b ⊢ f(a) = f(b)
//! 3. QF_LIA arithmetic: a ≤ b, b ≤ c ⊢ a ≤ c
//!
//! Each is benchmarked through:
//! - Native SmtBridge (in-process DPLL(T))
//! - AyBackend (in-process ay via ay-translate API)
//! - AyProofBackend (in-process ay with proof production, SMT-LIB string API)

use criterion::{criterion_group, criterion_main, Criterion};
use std::hint::black_box;

use clean_auto::bridge::ay_contract::{AyBackend, AyLogic, AyProofBackend};
use clean_auto::bridge::SmtBridge;
use clean_kernel::env::Declaration;
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Environment, Expr, FVarId, Level};

// ---------------------------------------------------------------------------
// Environment setup (duplicated from bridge/test_helpers.rs — pub(super))
// ---------------------------------------------------------------------------

fn setup_env() -> Environment {
    let mut env = Environment::new();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Eq"),
        level_params: vec![Name::from_string("u")],
        type_: Expr::pi(
            BinderInfo::Implicit,
            Expr::sort(Level::param(Name::from_string("u"))),
            Expr::pi(
                BinderInfo::Default,
                Expr::bvar(0),
                Expr::pi(BinderInfo::Default, Expr::bvar(1), Expr::prop()),
            ),
        ),
    })
    .expect("invariant: Eq decl");
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Eq.refl"),
        level_params: vec![Name::from_string("u")],
        type_: Expr::pi(
            BinderInfo::Implicit,
            Expr::sort(Level::param(Name::from_string("u"))),
            Expr::pi(
                BinderInfo::Implicit,
                Expr::bvar(0),
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::const_(
                                Name::from_string("Eq"),
                                vec![Level::param(Name::from_string("u"))],
                            ),
                            Expr::bvar(1),
                        ),
                        Expr::bvar(0),
                    ),
                    Expr::bvar(0),
                ),
            ),
        ),
    })
    .expect("invariant: Eq.refl decl");
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("A"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .expect("invariant: A decl");
    for name in ["a", "b", "c"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: Expr::const_(Name::from_string("A"), vec![]),
        })
        .expect("invariant: const decl");
    }
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("f"),
        level_params: vec![],
        type_: Expr::arrow(
            Expr::const_(Name::from_string("A"), vec![]),
            Expr::const_(Name::from_string("A"), vec![]),
        ),
    })
    .expect("invariant: f decl");
    env
}

// ---------------------------------------------------------------------------
// Expr helpers
// ---------------------------------------------------------------------------

fn make_eq_fvar(lhs: Expr, rhs: Expr) -> Expr {
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                a_ty,
            ),
            lhs,
        ),
        rhs,
    )
}

fn make_nat_le(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Nat.le"), vec![]), lhs),
        rhs,
    )
}

fn build_fvar_app(fvar_id: FVarId, args: &[Expr]) -> Expr {
    let mut result = Expr::fvar(fvar_id);
    for arg in args {
        result = Expr::app(result, arg.clone());
    }
    result
}

// ---------------------------------------------------------------------------
// Native SmtBridge benchmarks
// ---------------------------------------------------------------------------

fn bench_native_transitivity(c: &mut Criterion) {
    let env = setup_env();
    let (a_id, b_id, c_id) = (FVarId::new(100), FVarId::new(101), FVarId::new(102));
    let (a, b, ce) = (Expr::fvar(a_id), Expr::fvar(b_id), Expr::fvar(c_id));
    let hyp1 = make_eq_fvar(a.clone(), b.clone());
    let hyp2 = make_eq_fvar(b, ce.clone());
    let goal = make_eq_fvar(a, ce);

    c.bench_function("native/qf_uf/transitivity", |bencher| {
        bencher.iter(|| {
            let mut bridge = SmtBridge::new(&env);
            bridge
                .add_hypothesis_with_fvar(black_box(&hyp1), Some(FVarId::new(300)))
                .expect("invariant: hyp1 translation succeeds on valid Eq expr");
            bridge
                .add_hypothesis_with_fvar(black_box(&hyp2), Some(FVarId::new(301)))
                .expect("invariant: hyp2 translation succeeds on valid Eq expr");
            black_box(
                bridge
                    .prove(black_box(&goal))
                    .expect("invariant: prove succeeds on valid Eq goal"),
            )
        })
    });
}

fn bench_native_congruence(c: &mut Criterion) {
    let env = setup_env();
    let (a_id, b_id, f_id) = (FVarId::new(100), FVarId::new(101), FVarId::new(200));
    let (a, b) = (Expr::fvar(a_id), Expr::fvar(b_id));
    let hyp = make_eq_fvar(a.clone(), b.clone());
    let goal = make_eq_fvar(
        build_fvar_app(f_id, std::slice::from_ref(&a)),
        build_fvar_app(f_id, std::slice::from_ref(&b)),
    );

    c.bench_function("native/qf_uf/congruence", |bencher| {
        bencher.iter(|| {
            let mut bridge = SmtBridge::new(&env);
            bridge
                .add_hypothesis_with_fvar(black_box(&hyp), Some(FVarId::new(300)))
                .expect("invariant: hyp translation succeeds on valid Eq expr");
            black_box(
                bridge
                    .prove(black_box(&goal))
                    .expect("invariant: prove succeeds on valid congruence goal"),
            )
        })
    });
}

fn bench_native_lia_transitivity(c: &mut Criterion) {
    let env = setup_env();
    let (a_id, b_id, c_id) = (FVarId::new(100), FVarId::new(101), FVarId::new(102));
    let (a, b, ce) = (Expr::fvar(a_id), Expr::fvar(b_id), Expr::fvar(c_id));
    let hyp1 = make_nat_le(a.clone(), b.clone());
    let hyp2 = make_nat_le(b, ce.clone());
    let goal = make_nat_le(a, ce);

    c.bench_function("native/qf_lia/le_transitivity", |bencher| {
        bencher.iter(|| {
            let mut bridge = SmtBridge::new(&env);
            bridge
                .add_hypothesis_with_fvar(black_box(&hyp1), Some(FVarId::new(300)))
                .expect("invariant: hyp1 translation succeeds on valid Nat.le expr");
            bridge
                .add_hypothesis_with_fvar(black_box(&hyp2), Some(FVarId::new(301)))
                .expect("invariant: hyp2 translation succeeds on valid Nat.le expr");
            black_box(
                bridge
                    .prove(black_box(&goal))
                    .expect("invariant: prove succeeds on valid Nat.le goal"),
            )
        })
    });
}

// ---------------------------------------------------------------------------
// AyBackend benchmarks (in-process ay, no proof production)
// ---------------------------------------------------------------------------

fn bench_ay_transitivity(c: &mut Criterion) {
    let (a_id, b_id, c_id) = (FVarId::new(100), FVarId::new(101), FVarId::new(102));
    let (a, b, ce) = (Expr::fvar(a_id), Expr::fvar(b_id), Expr::fvar(c_id));
    let hyp1 = make_eq_fvar(a.clone(), b.clone());
    let hyp2 = make_eq_fvar(b, ce.clone());
    let goal = make_eq_fvar(a, ce);
    let a_type = Expr::const_(Name::from_string("A"), vec![]);

    c.bench_function("ay/qf_uf/transitivity", |bencher| {
        bencher.iter(|| {
            let mut be = AyBackend::new(AyLogic::QfUf);
            be.register_fvar_from_lean_type(a_id, &a_type)
                .expect("type A is opaque, not rejected");
            be.register_fvar_from_lean_type(b_id, &a_type)
                .expect("type A is opaque, not rejected");
            be.register_fvar_from_lean_type(c_id, &a_type)
                .expect("type A is opaque, not rejected");
            let t1 = be
                .translate_expr(black_box(&hyp1))
                .expect("invariant: translate Eq expr");
            be.assert_term(t1);
            let t2 = be
                .translate_expr(black_box(&hyp2))
                .expect("invariant: translate Eq expr");
            be.assert_term(t2);
            let g = be
                .translate_expr(black_box(&goal))
                .expect("invariant: translate Eq goal");
            let ng = be.not(g);
            be.assert_term(ng);
            black_box(be.check_sat())
        })
    });
}

fn bench_ay_congruence(c: &mut Criterion) {
    let (a_id, b_id, f_id) = (FVarId::new(100), FVarId::new(101), FVarId::new(200));
    let (a, b) = (Expr::fvar(a_id), Expr::fvar(b_id));
    let hyp = make_eq_fvar(a.clone(), b.clone());
    let goal = make_eq_fvar(
        build_fvar_app(f_id, std::slice::from_ref(&a)),
        build_fvar_app(f_id, std::slice::from_ref(&b)),
    );
    let a_type = Expr::const_(Name::from_string("A"), vec![]);

    c.bench_function("ay/qf_uf/congruence", |bencher| {
        bencher.iter(|| {
            let mut be = AyBackend::new(AyLogic::QfUf);
            be.register_fvar_from_lean_type(a_id, &a_type)
                .expect("type A is opaque, not rejected");
            be.register_fvar_from_lean_type(b_id, &a_type)
                .expect("type A is opaque, not rejected");
            be.register_fvar_from_lean_type(f_id, &a_type)
                .expect("type A is opaque, not rejected");
            let t = be
                .translate_expr(black_box(&hyp))
                .expect("invariant: translate Eq expr");
            be.assert_term(t);
            let g = be
                .translate_expr(black_box(&goal))
                .expect("invariant: translate congruence goal");
            let ng = be.not(g);
            be.assert_term(ng);
            black_box(be.check_sat())
        })
    });
}

fn bench_ay_lia_transitivity(c: &mut Criterion) {
    let (a_id, b_id, c_id) = (FVarId::new(100), FVarId::new(101), FVarId::new(102));
    let (a, b, ce) = (Expr::fvar(a_id), Expr::fvar(b_id), Expr::fvar(c_id));
    let hyp1 = make_nat_le(a.clone(), b.clone());
    let hyp2 = make_nat_le(b, ce.clone());
    let goal = make_nat_le(a, ce);

    c.bench_function("ay/qf_lia/le_transitivity", |bencher| {
        bencher.iter(|| {
            let mut be = AyBackend::new(AyLogic::QfLia);
            be.register_fvar_int(a_id);
            be.register_fvar_int(b_id);
            be.register_fvar_int(c_id);
            let t1 = be
                .translate_expr(black_box(&hyp1))
                .expect("invariant: translate Nat.le expr");
            be.assert_term(t1);
            let t2 = be
                .translate_expr(black_box(&hyp2))
                .expect("invariant: translate Nat.le expr");
            be.assert_term(t2);
            let g = be
                .translate_expr(black_box(&goal))
                .expect("invariant: translate Nat.le goal");
            let ng = be.not(g);
            be.assert_term(ng);
            black_box(be.check_sat())
        })
    });
}

// ---------------------------------------------------------------------------
// AyProofBackend benchmarks (in-process ay, with proof production)
// ---------------------------------------------------------------------------

fn bench_ay_proof_transitivity(c: &mut Criterion) {
    c.bench_function("ay_proof/qf_uf/transitivity", |bencher| {
        bencher.iter(|| {
            let mut be = AyProofBackend::new_with_proofs(AyLogic::QfUf);
            be.add_raw_declaration("(declare-sort U 0)");
            be.add_raw_declaration("(declare-fun a () U)");
            be.add_raw_declaration("(declare-fun b () U)");
            be.add_raw_declaration("(declare-fun c () U)");
            be.assert_formula("(= a b)");
            be.assert_formula("(= b c)");
            be.assert_formula("(not (= a c))");
            black_box(be.check_sat())
        })
    });
}

fn bench_ay_proof_congruence(c: &mut Criterion) {
    c.bench_function("ay_proof/qf_uf/congruence", |bencher| {
        bencher.iter(|| {
            let mut be = AyProofBackend::new_with_proofs(AyLogic::QfUf);
            be.add_raw_declaration("(declare-sort U 0)");
            be.add_raw_declaration("(declare-fun a () U)");
            be.add_raw_declaration("(declare-fun b () U)");
            be.add_raw_declaration("(declare-fun f (U) U)");
            be.assert_formula("(= a b)");
            be.assert_formula("(not (= (f a) (f b)))");
            black_box(be.check_sat())
        })
    });
}

fn bench_ay_proof_lia_transitivity(c: &mut Criterion) {
    c.bench_function("ay_proof/qf_lia/le_transitivity", |bencher| {
        bencher.iter(|| {
            let mut be = AyProofBackend::new_with_proofs(AyLogic::QfLia);
            be.add_raw_declaration("(declare-fun a () Int)");
            be.add_raw_declaration("(declare-fun b () Int)");
            be.add_raw_declaration("(declare-fun c () Int)");
            be.assert_formula("(<= a b)");
            be.assert_formula("(<= b c)");
            be.assert_formula("(not (<= a c))");
            black_box(be.check_sat())
        })
    });
}

// ---------------------------------------------------------------------------
// Criterion harness
// ---------------------------------------------------------------------------

criterion_group!(
    native_benches,
    bench_native_transitivity,
    bench_native_congruence,
    bench_native_lia_transitivity,
);
criterion_group!(
    ay_benches,
    bench_ay_transitivity,
    bench_ay_congruence,
    bench_ay_lia_transitivity,
);
criterion_group!(
    ay_proof_benches,
    bench_ay_proof_transitivity,
    bench_ay_proof_congruence,
    bench_ay_proof_lia_transitivity,
);
criterion_main!(native_benches, ay_benches, ay_proof_benches);
