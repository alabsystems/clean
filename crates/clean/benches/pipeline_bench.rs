// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Benchmark harness for the clean check pipeline.
//!
//! Measures end-to-end throughput: Lean source -> parse -> elaborate -> typecheck.
//! Provides reproducible performance numbers for the check pipeline.
//!
//! Run with:
//!   cargo bench -p clean --bench pipeline_bench

use clean::kernel::Environment;
use clean::{check_source, load_source_into, CheckConfig};
use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use std::hint::black_box;

fn default_config() -> CheckConfig {
    CheckConfig::default()
}

/// Generate N independent `def` declarations as a single source string.
fn generate_n_defs(n: usize) -> String {
    let mut source = String::with_capacity(n * 30);
    for i in 0..n {
        source.push_str(&format!("def bench_{i} : Nat := {i}\n"));
    }
    source
}

/// Benchmark: check_source with a single trivial definition.
fn bench_single_def(c: &mut Criterion) {
    c.bench_function("check_source/single_def", |b| {
        b.iter(|| {
            let result = check_source(black_box("def benchSingle : Nat := 0"), &default_config())
                .expect("should succeed");
            black_box(result)
        });
    });
}

/// Benchmark: check_source with a single theorem.
fn bench_single_theorem(c: &mut Criterion) {
    c.bench_function("check_source/single_theorem", |b| {
        b.iter(|| {
            let result = check_source(
                black_box("theorem benchThm : True := True.intro"),
                &default_config(),
            )
            .expect("should succeed");
            black_box(result)
        });
    });
}

/// Benchmark: check_source scaling with N definitions.
fn bench_n_defs(c: &mut Criterion) {
    let mut group = c.benchmark_group("check_source/n_defs");

    for n in [1, 5, 10, 25, 50] {
        let source = generate_n_defs(n);
        group.bench_with_input(BenchmarkId::from_parameter(n), &source, |b, src| {
            b.iter(|| {
                let result =
                    check_source(black_box(src), &default_config()).expect("should succeed");
                black_box(result)
            });
        });
    }

    group.finish();
}

/// Benchmark: incremental loading via load_source_into.
fn bench_incremental_load(c: &mut Criterion) {
    let mut group = c.benchmark_group("load_source_into/incremental");

    for n in [1, 5, 10] {
        group.bench_with_input(BenchmarkId::from_parameter(n), &n, |b, &count| {
            b.iter(|| {
                let mut env = Environment::try_with_prelude().expect("prelude");
                let config = default_config();
                for i in 0..count {
                    let src = format!("def bench_incr_{i} : Nat := {i}");
                    let result = load_source_into(&mut env, &src, &config).expect("should succeed");
                    black_box(&result);
                }
            });
        });
    }

    group.finish();
}

/// Benchmark: environment initialization (prelude setup).
fn bench_env_init(c: &mut Criterion) {
    c.bench_function("env_init/try_with_prelude", |b| {
        b.iter(|| {
            let env = Environment::try_with_prelude().expect("prelude");
            black_box(env)
        });
    });
}

/// Benchmark: check_source with a lambda definition.
fn bench_lambda_def(c: &mut Criterion) {
    c.bench_function("check_source/lambda_def", |b| {
        b.iter(|| {
            let result = check_source(
                black_box("def myId : Nat -> Nat := fun x => x"),
                &default_config(),
            )
            .expect("should succeed");
            black_box(result)
        });
    });
}

/// Benchmark: check_source with a multi-parameter function.
fn bench_multi_param_def(c: &mut Criterion) {
    c.bench_function("check_source/multi_param_def", |b| {
        b.iter(|| {
            let result = check_source(
                black_box("def add3 (a b c : Nat) : Nat := Nat.add a (Nat.add b c)"),
                &default_config(),
            )
            .expect("should succeed");
            black_box(result)
        });
    });
}

/// Benchmark: check_source with an inductive type.
fn bench_inductive(c: &mut Criterion) {
    let source = r#"
inductive BenchColor where
  | red : BenchColor
  | green : BenchColor
  | blue : BenchColor
"#;
    c.bench_function("check_source/inductive", |b| {
        b.iter(|| {
            let result =
                check_source(black_box(source), &default_config()).expect("should succeed");
            black_box(result)
        });
    });
}

/// Benchmark: check_source with a structure type.
fn bench_structure(c: &mut Criterion) {
    let source = r#"
structure BenchPoint where
  x : Nat
  y : Nat
"#;
    c.bench_function("check_source/structure", |b| {
        b.iter(|| {
            let result =
                check_source(black_box(source), &default_config()).expect("should succeed");
            black_box(result)
        });
    });
}

/// Benchmark: mixed declaration types scaling.
fn bench_mixed_decls(c: &mut Criterion) {
    let mut group = c.benchmark_group("check_source/mixed_decls");

    for n in [5, 10, 25] {
        let mut source = String::with_capacity(n * 60);
        for i in 0..n {
            if i % 3 == 0 {
                source.push_str(&format!("theorem mixBench_{i} : True := True.intro\n"));
            } else {
                source.push_str(&format!("def mixBench_{i} : Nat := {i}\n"));
            }
        }
        group.bench_with_input(BenchmarkId::from_parameter(n), &source, |b, src| {
            b.iter(|| {
                let result =
                    check_source(black_box(src), &default_config()).expect("should succeed");
                black_box(result)
            });
        });
    }

    group.finish();
}

/// Benchmark: incremental loading with dependent definitions.
fn bench_incremental_dependent(c: &mut Criterion) {
    c.bench_function("load_source_into/dependent_chain_5", |b| {
        b.iter(|| {
            let mut env = Environment::try_with_prelude().expect("prelude");
            let config = default_config();

            load_source_into(&mut env, "def depBase : Nat := 1", &config).expect("should succeed");
            load_source_into(&mut env, "def dep1 : Nat := depBase", &config)
                .expect("should succeed");
            load_source_into(&mut env, "def dep2 : Nat := dep1", &config).expect("should succeed");
            load_source_into(&mut env, "def dep3 : Nat := dep2", &config).expect("should succeed");
            let result = load_source_into(&mut env, "def dep4 : Nat := dep3", &config)
                .expect("should succeed");
            black_box(result)
        });
    });
}

/// Benchmark: let-binding definition.
fn bench_let_binding(c: &mut Criterion) {
    let source = r#"
def benchLet : Nat :=
  let x := 10
  let y := 20
  Nat.add x y
"#;
    c.bench_function("check_source/let_binding", |b| {
        b.iter(|| {
            let result =
                check_source(black_box(source), &default_config()).expect("should succeed");
            black_box(result)
        });
    });
}

criterion_group!(
    benches,
    bench_single_def,
    bench_single_theorem,
    bench_n_defs,
    bench_incremental_load,
    bench_env_init,
    bench_lambda_def,
    bench_multi_param_def,
    bench_inductive,
    bench_structure,
    bench_mixed_decls,
    bench_incremental_dependent,
    bench_let_binding,
);
criterion_main!(benches);
