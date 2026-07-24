// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! E2E validation benchmark harness for the clean check pipeline.
//!
//! Complements `pipeline_bench.rs` with broader coverage of declaration
//! types: pattern matching, typeclasses, tactic proofs, recursive functions,
//! dependent types, and mixed real-world scenarios.
//!
//! Run with:
//!   cargo bench -p clean --bench e2e_bench
//!
//! For JSON output (CI consumption):
//!   cargo bench -p clean --bench e2e_bench -- --output-format bencher

use clean::kernel::Environment;
use clean::{check_source, load_source_into, CheckConfig};
use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use std::hint::black_box;

fn default_config() -> CheckConfig {
    CheckConfig::default()
}

// ---------------------------------------------------------------------------
// Pattern matching benchmarks
// ---------------------------------------------------------------------------

fn bench_match_bool(c: &mut Criterion) {
    let source = r#"
def boolToNat (b : Bool) : Nat :=
  match b with
  | true => 1
  | false => 0
"#;
    c.bench_function("e2e/match_bool", |b| {
        b.iter(|| {
            let result =
                check_source(black_box(source), &default_config()).expect("should succeed");
            black_box(result)
        });
    });
}

fn bench_match_nat(c: &mut Criterion) {
    let source = r#"
def isZero (n : Nat) : Bool :=
  match n with
  | Nat.zero => true
  | Nat.succ _ => false
"#;
    c.bench_function("e2e/match_nat", |b| {
        b.iter(|| {
            let result =
                check_source(black_box(source), &default_config()).expect("should succeed");
            black_box(result)
        });
    });
}

// ---------------------------------------------------------------------------
// Let binding benchmarks
// ---------------------------------------------------------------------------

fn bench_let_simple(c: &mut Criterion) {
    let source = r#"
def letBench : Nat :=
  let x := 10
  let y := 20
  Nat.add x y
"#;
    c.bench_function("e2e/let_simple", |b| {
        b.iter(|| {
            let result =
                check_source(black_box(source), &default_config()).expect("should succeed");
            black_box(result)
        });
    });
}

fn bench_let_chained_5(c: &mut Criterion) {
    let source = r#"
def letChain5 : Nat :=
  let a := 1
  let b := 2
  let c := 3
  let d := 4
  let e := 5
  Nat.add a (Nat.add b (Nat.add c (Nat.add d e)))
"#;
    c.bench_function("e2e/let_chained_5", |b| {
        b.iter(|| {
            let result =
                check_source(black_box(source), &default_config()).expect("should succeed");
            black_box(result)
        });
    });
}

// ---------------------------------------------------------------------------
// Typeclass benchmarks
// ---------------------------------------------------------------------------

fn bench_class_decl(c: &mut Criterion) {
    let source = r#"
class BenchShow (a : Type) where
  show : a -> Nat
"#;
    c.bench_function("e2e/class_decl", |b| {
        b.iter(|| {
            let result =
                check_source(black_box(source), &default_config()).expect("should succeed");
            black_box(result)
        });
    });
}

// ---------------------------------------------------------------------------
// Tactic benchmarks
// ---------------------------------------------------------------------------

fn bench_tactic_rfl(c: &mut Criterion) {
    c.bench_function("e2e/tactic_rfl", |b| {
        b.iter(|| {
            let result = check_source(
                black_box("theorem benchRfl : 1 = 1 := by rfl"),
                &default_config(),
            )
            .expect("should succeed");
            black_box(result)
        });
    });
}

fn bench_tactic_exact(c: &mut Criterion) {
    c.bench_function("e2e/tactic_exact", |b| {
        b.iter(|| {
            let result = check_source(
                black_box("theorem benchExact : True := by exact True.intro"),
                &default_config(),
            )
            .expect("should succeed");
            black_box(result)
        });
    });
}

// ---------------------------------------------------------------------------
// Dependent type benchmarks
// ---------------------------------------------------------------------------

fn bench_polymorphic_id(c: &mut Criterion) {
    c.bench_function("e2e/polymorphic_id", |b| {
        b.iter(|| {
            let result = check_source(
                black_box("def polyId (a : Type) (x : a) : a := x"),
                &default_config(),
            )
            .expect("should succeed");
            black_box(result)
        });
    });
}

fn bench_implicit_param(c: &mut Criterion) {
    c.bench_function("e2e/implicit_param", |b| {
        b.iter(|| {
            let result = check_source(
                black_box("def impId {a : Type} (x : a) : a := x"),
                &default_config(),
            )
            .expect("should succeed");
            black_box(result)
        });
    });
}

// ---------------------------------------------------------------------------
// Scaling benchmarks: inductive + def chain
// ---------------------------------------------------------------------------

fn bench_inductive_plus_def(c: &mut Criterion) {
    let source = r#"
inductive BenchSeason where
  | spring : BenchSeason
  | summer : BenchSeason
  | autumn : BenchSeason
  | winter : BenchSeason

def benchDefault : BenchSeason := BenchSeason.spring
"#;
    c.bench_function("e2e/inductive_plus_def", |b| {
        b.iter(|| {
            let result =
                check_source(black_box(source), &default_config()).expect("should succeed");
            black_box(result)
        });
    });
}

// ---------------------------------------------------------------------------
// Realistic mixed workload benchmark
// ---------------------------------------------------------------------------

fn bench_mixed_realistic(c: &mut Criterion) {
    let mut group = c.benchmark_group("e2e/mixed_realistic");

    for n in [5, 10, 20] {
        let mut source = String::with_capacity(n * 80);
        for i in 0..n {
            match i % 5 {
                0 => source.push_str(&format!("def mix_{i} : Nat := {i}\n")),
                1 => source.push_str(&format!("def mix_{i} (x : Nat) : Nat := Nat.add x {i}\n")),
                2 => source.push_str(&format!("theorem mixThm_{i} : True := True.intro\n")),
                3 => source.push_str(&format!("def mix_{i} : Nat -> Nat := fun x => x\n")),
                4 => source.push_str(&format!("def mix_{i} : Nat := let v := {i} in v\n")),
                _ => unreachable!(),
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

// ---------------------------------------------------------------------------
// Incremental loading benchmark with mixed types
// ---------------------------------------------------------------------------

fn bench_incremental_mixed(c: &mut Criterion) {
    let mut group = c.benchmark_group("e2e/incremental_mixed");

    for n in [5, 10] {
        group.bench_with_input(BenchmarkId::from_parameter(n), &n, |b, &count| {
            b.iter(|| {
                let mut env = Environment::try_with_prelude().expect("prelude");
                let config = default_config();
                for i in 0..count {
                    let src = if i % 2 == 0 {
                        format!("def incMix_{i} : Nat := {i}")
                    } else {
                        format!("def incMix_{i} : Nat -> Nat := fun x => x")
                    };
                    let result = load_source_into(&mut env, &src, &config).expect("should succeed");
                    black_box(&result);
                }
            });
        });
    }

    group.finish();
}

// ---------------------------------------------------------------------------
// Dependency chain scaling
// ---------------------------------------------------------------------------

fn bench_dependency_chain(c: &mut Criterion) {
    let mut group = c.benchmark_group("e2e/dependency_chain");

    for depth in [3, 5, 10] {
        let mut source = String::new();
        source.push_str("def chain_0 : Nat := 0\n");
        for i in 1..depth {
            source.push_str(&format!(
                "def chain_{i} : Nat := Nat.succ chain_{prev}\n",
                prev = i - 1
            ));
        }

        group.bench_with_input(BenchmarkId::from_parameter(depth), &source, |b, src| {
            b.iter(|| {
                let result =
                    check_source(black_box(src), &default_config()).expect("should succeed");
                black_box(result)
            });
        });
    }

    group.finish();
}

criterion_group!(
    benches,
    bench_match_bool,
    bench_match_nat,
    bench_let_simple,
    bench_let_chained_5,
    bench_class_decl,
    bench_tactic_rfl,
    bench_tactic_exact,
    bench_polymorphic_id,
    bench_implicit_param,
    bench_inductive_plus_def,
    bench_mixed_realistic,
    bench_incremental_mixed,
    bench_dependency_chain,
);
criterion_main!(benches);
