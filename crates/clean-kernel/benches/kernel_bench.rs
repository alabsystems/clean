// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel benchmarks
//!
//! Benchmarks for core kernel operations to measure performance against targets.
//!
//! Performance targets live in `docs/DESIGN.md`.
//! Reproducible methodology and last verified results/commit hashes live in
//! `docs/BENCHMARKS.md`.

use clean_kernel::{
    env::{Declaration, Environment},
    expr::{BinderInfo, Expr},
    inductive::{Constructor, InductiveDecl, InductiveType},
    level::Level,
    name::Name,
    tc::TypeChecker,
};
use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use std::hint::black_box;

/// Create a simple environment with basic types
fn simple_env() -> Environment {
    let mut env = Environment::new();

    // Add a simple axiom
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("P"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .unwrap();

    // Add identity function: id : {A : Sort u} → A → A
    let u = Name::from_string("u");
    let id_type = Expr::pi(
        BinderInfo::Implicit,
        Expr::sort(Level::param(u.clone())),
        Expr::pi(BinderInfo::Default, Expr::bvar(0), Expr::bvar(1)),
    );
    let id_value = Expr::lam(
        BinderInfo::Implicit,
        Expr::sort(Level::param(u.clone())),
        Expr::lam(BinderInfo::Default, Expr::bvar(0), Expr::bvar(0)),
    );
    env.add_decl(Declaration::Definition {
        name: Name::from_string("id"),
        level_params: vec![u],
        type_: id_type,
        value: id_value,
        is_reducible: true,
    })
    .unwrap();

    env
}

/// Create environment with Nat inductive type
fn nat_env() -> Environment {
    let mut env = Environment::new();

    let nat = Name::from_string("Nat");
    let nat_ref = Expr::const_(nat.clone(), vec![]);

    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: nat.clone(),
            type_: Expr::type_(),
            constructors: vec![
                Constructor {
                    name: Name::from_string("Nat.zero"),
                    type_: nat_ref.clone(),
                },
                Constructor {
                    name: Name::from_string("Nat.succ"),
                    type_: Expr::arrow(nat_ref.clone(), nat_ref),
                },
            ],
        }],
    };

    env.add_inductive(decl).unwrap();
    env
}

/// Build a Nat literal using successor constructor
fn build_nat(env: &Environment, n: u32) -> Expr {
    let _ = env; // env used to ensure Nat is defined
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);

    let mut result = zero;
    for _ in 0..n {
        result = Expr::app(succ.clone(), result);
    }
    result
}

/// Build a nested identity application: id (id (id ... P)) where P : Prop
fn nested_id_app(env: &Environment, depth: u32) -> Expr {
    let _ = env; // ensure id is defined
    let one = Level::succ(Level::zero());
    let id = Expr::const_(Name::from_string("id"), vec![one]);
    // P is a constant of type Prop
    let p = Expr::const_(Name::from_string("P"), vec![]);

    let mut result = p;
    for _ in 0..depth {
        // id.{1} Prop : Prop → Prop (since Prop : Type = Sort 1)
        let id_prop = Expr::app(id.clone(), Expr::prop());
        // id.{1} Prop result : Prop
        result = Expr::app(id_prop, result);
    }
    result
}

/// Build a nested lambda: λ x. λ y. λ z. ... x
fn nested_lambda(depth: u32) -> Expr {
    let mut body = Expr::bvar(depth - 1);
    for i in 0..depth {
        body = Expr::lam(
            BinderInfo::Default,
            Expr::sort(Level::zero().add_offset(i)),
            body,
        );
    }
    body
}

/// Build a nested beta redex: (λ x. x) ((λ x. x) ((λ x. x) Prop))
fn nested_beta_redex(depth: u32) -> Expr {
    let id_lam = Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(0));

    let mut result = Expr::prop();
    for _ in 0..depth {
        result = Expr::app(id_lam.clone(), result);
    }
    result
}

// === Benchmarks ===

fn bench_infer_type_sort(c: &mut Criterion) {
    let env = Environment::new();

    c.bench_function("infer_type/Sort_0", |b| {
        b.iter(|| {
            let tc = TypeChecker::new(&env);
            tc.infer_type(black_box(&Expr::prop())).unwrap()
        });
    });

    c.bench_function("infer_type/Sort_1", |b| {
        b.iter(|| {
            let tc = TypeChecker::new(&env);
            tc.infer_type(black_box(&Expr::type_())).unwrap()
        });
    });
}

fn bench_infer_type_lambda(c: &mut Criterion) {
    let env = Environment::new();

    // λ (x : Prop). x
    let simple_lam = Expr::lam(BinderInfo::Default, Expr::prop(), Expr::bvar(0));

    c.bench_function("infer_type/lambda_simple", |b| {
        b.iter(|| {
            let tc = TypeChecker::new(&env);
            tc.infer_type(black_box(&simple_lam)).unwrap()
        });
    });

    let mut group = c.benchmark_group("infer_type/lambda_nested");
    for depth in [2, 4, 8, 16, 32, 64] {
        let nested = nested_lambda(depth);
        group.bench_with_input(BenchmarkId::from_parameter(depth), &nested, |b, expr| {
            b.iter(|| {
                let tc = TypeChecker::new(&env);
                tc.infer_type(black_box(expr)).unwrap()
            });
        });
    }
    group.finish();
}

fn bench_infer_type_app(c: &mut Criterion) {
    let env = simple_env();

    // id.{1} Prop P
    let one = Level::succ(Level::zero());
    let id_app = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("id"), vec![one]),
            Expr::prop(),
        ),
        Expr::const_(Name::from_string("P"), vec![]),
    );

    c.bench_function("infer_type/app_simple", |b| {
        b.iter(|| {
            let tc = TypeChecker::new(&env);
            tc.infer_type(black_box(&id_app)).unwrap()
        });
    });

    let mut group = c.benchmark_group("infer_type/app_nested");
    for depth in [2, 4, 8, 16] {
        let nested = nested_id_app(&env, depth);
        group.bench_with_input(BenchmarkId::from_parameter(depth), &nested, |b, expr| {
            b.iter(|| {
                let tc = TypeChecker::new(&env);
                tc.infer_type(black_box(expr)).unwrap()
            });
        });
    }
    group.finish();
}

fn bench_whnf_beta(c: &mut Criterion) {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // (λ x. x) Prop
    let simple_beta = Expr::app(
        Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(0)),
        Expr::prop(),
    );

    c.bench_function("whnf/beta_simple", |b| {
        b.iter(|| tc.whnf(black_box(&simple_beta)));
    });

    let mut group = c.benchmark_group("whnf/beta_nested");
    for depth in [2, 4, 8, 16, 32] {
        let nested = nested_beta_redex(depth);
        group.bench_with_input(BenchmarkId::from_parameter(depth), &nested, |b, expr| {
            b.iter(|| tc.whnf(black_box(expr)));
        });
    }
    group.finish();
}

fn bench_whnf_delta(c: &mut Criterion) {
    let env = simple_env();
    let tc = TypeChecker::new(&env);

    // id.{1} - should unfold the definition
    let one = Level::succ(Level::zero());
    let id_const = Expr::const_(Name::from_string("id"), vec![one]);

    c.bench_function("whnf/delta_unfold", |b| {
        b.iter(|| tc.whnf(black_box(&id_const)));
    });
}

fn bench_whnf_iota(c: &mut Criterion) {
    let env = nat_env();
    let tc = TypeChecker::new(&env);

    // Build Nat.rec application on Nat.zero
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let motive = Expr::lam(BinderInfo::Default, nat.clone(), Expr::prop());
    let zero_case = Expr::prop();
    let succ_case = Expr::lam(
        BinderInfo::Default,
        nat.clone(),
        Expr::lam(BinderInfo::Default, Expr::prop(), Expr::prop()),
    );
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);

    let rec = Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]);
    let rec_app = Expr::app(
        Expr::app(Expr::app(Expr::app(rec, motive), zero_case), succ_case),
        zero,
    );

    c.bench_function("whnf/iota_nat_zero", |b| {
        b.iter(|| tc.whnf(black_box(&rec_app)));
    });
}

fn bench_is_def_eq_simple(c: &mut Criterion) {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    c.bench_function("is_def_eq/identical", |b| {
        let prop = Expr::prop();
        b.iter(|| tc.is_def_eq(black_box(&prop), black_box(&prop)));
    });

    c.bench_function("is_def_eq/different_sorts", |b| {
        let prop = Expr::prop();
        let type_ = Expr::type_();
        b.iter(|| tc.is_def_eq(black_box(&prop), black_box(&type_)));
    });

    // max(0, 0) == 0
    c.bench_function("is_def_eq/level_normalize", |b| {
        let max_00 = Expr::sort(Level::max(Level::zero(), Level::zero()));
        let zero = Expr::prop();
        b.iter(|| tc.is_def_eq(black_box(&max_00), black_box(&zero)));
    });
}

fn bench_is_def_eq_beta(c: &mut Criterion) {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // (λ x. x) Prop == Prop
    let beta_lhs = Expr::app(
        Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(0)),
        Expr::prop(),
    );
    let beta_rhs = Expr::prop();

    c.bench_function("is_def_eq/beta_reduce", |b| {
        b.iter(|| tc.is_def_eq(black_box(&beta_lhs), black_box(&beta_rhs)));
    });
}

fn bench_is_def_eq_structural(c: &mut Criterion) {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let mut group = c.benchmark_group("is_def_eq/structural");
    for depth in [2, 4, 8, 16, 32, 64] {
        let lam1 = nested_lambda(depth);
        let lam2 = nested_lambda(depth);
        group.bench_with_input(
            BenchmarkId::from_parameter(depth),
            &(lam1, lam2),
            |b, (l1, l2)| {
                b.iter(|| tc.is_def_eq(black_box(l1), black_box(l2)));
            },
        );
    }
    group.finish();
}

/// Build a deeply nested Pi type: Π (_: Prop). Π (_: Prop). ... BVar(depth)
///
/// Uses `BVar(depth)` as the innermost body to ensure `has_loose_bvars()` is
/// true at every level of the Pi chain. This forces `is_def_eq_binding`'s
/// iterative loop to process all N binders (the closed-body optimization at
/// line 1247 cannot fire when bodies contain loose BVars).
///
/// Without loose BVars (body = Prop), the optimization short-circuits on the
/// first iteration, and remaining levels are compared via recursive dispatch
/// through `is_def_eq_impl` — defeating the purpose of the benchmark.
fn nested_pi(depth: u32) -> Expr {
    let mut body = Expr::bvar(depth);
    for _ in 0..depth {
        body = Expr::pi(BinderInfo::Default, Expr::prop(), body);
    }
    body
}

/// Benchmark `is_def_eq` on deeply nested same-kind Pi binders.
///
/// This directly exercises the iterative loop in `is_def_eq_binding` (#1664).
/// The old recursive implementation processed N binders via N re-dispatches
/// through the 8-phase algorithm. The iterative version handles all N
/// consecutive same-kind binders in a single loop.
fn bench_is_def_eq_binding(c: &mut Criterion) {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let mut group = c.benchmark_group("is_def_eq/binding_pi");
    for depth in [5, 10, 20, 40] {
        let pi1 = nested_pi(depth);
        let pi2 = nested_pi(depth);
        group.bench_with_input(
            BenchmarkId::from_parameter(depth),
            &(pi1, pi2),
            |b, (p1, p2)| {
                b.iter(|| tc.is_def_eq(black_box(p1), black_box(p2)));
            },
        );
    }
    group.finish();
}

/// Environment for the delta-loaded `is_def_eq` benchmarks: identity
/// definitions exercising the lazy-delta lane (`lazy_delta_reduction`),
/// including the same-head args-first fast path in `lazy_delta_step_equal`.
///
/// `delta_f`/`delta_g` get `Regular(0)` hints (`is_reducible: false`);
/// `delta_r` gets `Reducible` (`is_reducible: true`).
fn delta_env() -> Environment {
    let mut env = Environment::new();
    let ty = || Expr::pi(BinderInfo::Default, Expr::prop(), Expr::prop());
    let body = || Expr::lam(BinderInfo::Default, Expr::prop(), Expr::bvar(0));
    for (name, is_reducible) in [("delta_f", false), ("delta_g", false), ("delta_r", true)] {
        env.add_decl(Declaration::Definition {
            name: Name::from_string(name),
            level_params: vec![],
            type_: ty(),
            value: body(),
            is_reducible,
        })
        .unwrap();
    }
    env
}

/// Delta-loaded `is_def_eq` (the lazy-delta lane previously had zero
/// microbench coverage — designs/2026-07-15-lazy-delta-ordering-parity.md
/// STEP 1e). Four shapes:
///
/// - `same_head_regular_hit`   — same Regular head, args def-eq but not
///   syntactically identical → the ext==ext args-first fast path accepts
///   (TRUE-early);
/// - `same_head_regular_miss`  — same Regular head, non-def-eq args → the
///   args attempt fails, the failure is cached, unfold-both rejects;
/// - `different_head`          — distinct same-height heads → pure
///   ordering+unfold path (never enters the args attempt); measures the
///   per-iteration overhead of the same-head gate itself;
/// - `same_head_reducible_hit` — the Reducible-head twin of `hit` (the lane
///   changed by the same-head gate widening).
///
/// A fresh `TypeChecker` per iteration (precedent: `nat/infer_type` above)
/// defeats the def-eq/equiv-manager caches so each iteration genuinely runs
/// the lazy-delta loop instead of replaying a cached verdict.
fn bench_is_def_eq_delta(c: &mut Criterion) {
    let env = delta_env();

    let f = Expr::const_(Name::from_string("delta_f"), vec![]);
    let g = Expr::const_(Name::from_string("delta_g"), vec![]);
    let r = Expr::const_(Name::from_string("delta_r"), vec![]);

    // (fun x : Type => x) Prop — def-eq to Prop but not syntactically equal,
    // so the args comparison is a real recursive is_def_eq, not Expr::eq.
    let beta_prop = || {
        Expr::app(
            Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(0)),
            Expr::prop(),
        )
    };

    let hit = (
        Expr::app(f.clone(), beta_prop()),
        Expr::app(f.clone(), Expr::prop()),
    );
    let miss = (
        Expr::app(f.clone(), Expr::prop()),
        Expr::app(f.clone(), Expr::type_()),
    );
    let diff = (Expr::app(f, Expr::prop()), Expr::app(g, Expr::prop()));
    let red_hit = (
        Expr::app(r.clone(), beta_prop()),
        Expr::app(r, Expr::prop()),
    );

    let mut group = c.benchmark_group("is_def_eq/delta");
    for (id, pair) in [
        ("same_head_regular_hit", &hit),
        ("same_head_regular_miss", &miss),
        ("different_head", &diff),
        ("same_head_reducible_hit", &red_hit),
    ] {
        let (lhs, rhs) = pair;
        group.bench_function(id, |b| {
            b.iter(|| {
                let tc = TypeChecker::new(&env);
                tc.is_def_eq(black_box(lhs), black_box(rhs))
            });
        });
    }
    group.finish();
}

fn bench_nat_operations(c: &mut Criterion) {
    let env = nat_env();

    let mut group = c.benchmark_group("nat/build");
    for n in [1, 5, 10, 20, 50] {
        group.bench_with_input(BenchmarkId::from_parameter(n), &n, |b, &n| {
            b.iter(|| build_nat(&env, black_box(n)));
        });
    }
    group.finish();

    let mut group = c.benchmark_group("nat/infer_type");
    for n in [1, 5, 10, 20] {
        let nat_n = build_nat(&env, n);
        group.bench_with_input(BenchmarkId::from_parameter(n), &nat_n, |b, expr| {
            b.iter(|| {
                let tc = TypeChecker::new(&env);
                tc.infer_type(black_box(expr)).unwrap()
            });
        });
    }
    group.finish();
}

fn bench_environment_lookup(c: &mut Criterion) {
    let mut env = Environment::new();

    // Add many declarations
    for i in 0..100 {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(&format!("decl_{i}")),
            level_params: vec![],
            type_: Expr::prop(),
        })
        .unwrap();
    }

    c.bench_function("env/lookup_first", |b| {
        b.iter(|| env.get_const(black_box(&Name::from_string("decl_0"))));
    });

    c.bench_function("env/lookup_middle", |b| {
        b.iter(|| env.get_const(black_box(&Name::from_string("decl_50"))));
    });

    c.bench_function("env/lookup_last", |b| {
        b.iter(|| env.get_const(black_box(&Name::from_string("decl_99"))));
    });

    c.bench_function("env/lookup_missing", |b| {
        b.iter(|| env.get_const(black_box(&Name::from_string("nonexistent"))));
    });
}

criterion_group!(
    benches,
    bench_infer_type_sort,
    bench_infer_type_lambda,
    bench_infer_type_app,
    bench_whnf_beta,
    bench_whnf_delta,
    bench_whnf_iota,
    bench_is_def_eq_simple,
    bench_is_def_eq_beta,
    bench_is_def_eq_structural,
    bench_is_def_eq_binding,
    bench_is_def_eq_delta,
    bench_nat_operations,
    bench_environment_lookup,
);

criterion_main!(benches);
