// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! CertBuilder and macrobenchmarks
//!
//! Split from kernel_bench.rs to stay under the 500-line file limit.
//! CertBuilder benchmarks from designs/2026-01-28-incremental-cert-verification.md.
//! Macrobenchmarks from designs/2026-01-31-macrobenchmarks-design.md.

use clean_kernel::{
    cert::{batch_build_verify_sequential_with_stats, BatchBuildInput, CertBuilder},
    env::{Declaration, Environment},
    expr::{BinderInfo, Expr},
    level::Level,
    name::Name,
    tc::TypeChecker,
};
use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use std::hint::black_box;
use sysinfo::System;

// ============================================================================
// CertBuilder Benchmarks (Phase 5 from designs/2026-01-28-incremental-cert-verification.md)
// ============================================================================

/// Benchmark CertBuilder vs traditional approach for valid proofs.
fn bench_cert_builder_valid(c: &mut Criterion) {
    let env = Environment::new();

    // Simple valid certificate: Sort(0) : Sort(1)
    c.bench_function("cert_builder/valid/sort", |b| {
        b.iter(|| {
            let mut builder = CertBuilder::new(&env);
            let _ = builder.sort(black_box(Level::zero()));
        });
    });

    // More complex: nested lambda type
    c.bench_function("cert_builder/valid/lambda_4", |b| {
        b.iter(|| {
            let mut builder = CertBuilder::new(&env);
            // Build: Sort(0)
            let s0 = builder.sort(Level::zero()).unwrap();
            // Build: λ _: Sort(0). λ _: Sort(0). λ _: Sort(0). λ _: Sort(0). BVar(3)
            let result = builder.lam(BinderInfo::Default, s0, |b| {
                let s1 = b.sort(Level::zero()).unwrap();
                b.lam(BinderInfo::Default, s1, |b| {
                    let s2 = b.sort(Level::zero()).unwrap();
                    b.lam(BinderInfo::Default, s2, |b| {
                        let s3 = b.sort(Level::zero()).unwrap();
                        b.lam(BinderInfo::Default, s3, |b| b.bvar(3))
                    })
                })
            });
            black_box(result)
        });
    });
}

/// Benchmark CertBuilder fail-fast behavior.
///
/// This is the key benchmark - failures should be much faster with CertBuilder
/// since we fail early instead of building complete certificates.
fn bench_cert_builder_fail_fast(c: &mut Criterion) {
    let env = Environment::new();

    // Immediate failure: bvar(0) with no context
    c.bench_function("cert_builder/fail/bvar_immediate", |b| {
        b.iter(|| {
            let mut builder = CertBuilder::new(&env);
            let result = builder.bvar(black_box(0));
            black_box(result)
        });
    });

    // Failure after 1 node: sort, then invalid bvar
    c.bench_function("cert_builder/fail/bvar_after_1", |b| {
        b.iter(|| {
            let mut builder = CertBuilder::new(&env);
            let _ = builder.sort(Level::zero());
            let result = builder.bvar(black_box(0)); // Fails
            black_box(result)
        });
    });

    // Failure at depth 3
    c.bench_function("cert_builder/fail/depth_3", |b| {
        b.iter(|| {
            let mut builder = CertBuilder::new(&env);
            let s0 = builder.sort(Level::zero()).unwrap();
            let result = builder.lam(BinderInfo::Default, s0, |b| {
                let s1 = b.sort(Level::zero()).unwrap();
                b.lam(BinderInfo::Default, s1, |b| b.bvar(5)) // Fails - bvar(5) out of range
            });
            black_box(result)
        });
    });
}

/// Benchmark batch building with mixed valid/invalid proofs.
///
/// This benchmark demonstrates the fail-fast benefit for AI prover workloads
/// where ~99% of proof attempts fail.
fn bench_cert_builder_batch(c: &mut Criterion) {
    let env = Environment::new();

    let mut group = c.benchmark_group("cert_builder/batch");

    // 1% valid (AI prover typical)
    for batch_size in [100, 1000] {
        group.bench_with_input(
            BenchmarkId::new("1pct_valid", batch_size),
            &batch_size,
            |b, &size| {
                b.iter(|| {
                    let inputs: Vec<BatchBuildInput> = (0..size)
                        .map(|i| {
                            if i % 100 == 0 {
                                // 1% valid
                                BatchBuildInput::new(format!("valid_{}", i), |builder| {
                                    builder.sort(Level::zero())
                                })
                            } else {
                                // 99% invalid - fail at first node
                                BatchBuildInput::new(format!("invalid_{}", i), |builder| {
                                    builder.bvar(0)
                                })
                            }
                        })
                        .collect();
                    let (_, stats) = batch_build_verify_sequential_with_stats(&env, inputs);
                    black_box(stats)
                });
            },
        );
    }

    // 50% valid
    for batch_size in [100, 1000] {
        group.bench_with_input(
            BenchmarkId::new("50pct_valid", batch_size),
            &batch_size,
            |b, &size| {
                b.iter(|| {
                    let inputs: Vec<BatchBuildInput> = (0..size)
                        .map(|i| {
                            if i % 2 == 0 {
                                // 50% valid
                                BatchBuildInput::new(format!("valid_{}", i), |builder| {
                                    builder.sort(Level::zero())
                                })
                            } else {
                                // 50% invalid
                                BatchBuildInput::new(format!("invalid_{}", i), |builder| {
                                    builder.bvar(0)
                                })
                            }
                        })
                        .collect();
                    let (_, stats) = batch_build_verify_sequential_with_stats(&env, inputs);
                    black_box(stats)
                });
            },
        );
    }

    group.finish();
}

// ============================================================================
// Macrobenchmarks (from designs/2026-01-31-macrobenchmarks-design.md)
// Real-world workload performance for AI-agentic verification
// ============================================================================

/// Macrobenchmark 1: Cold Start
///
/// Measures time from Environment::new() to first successful type check.
/// Target: <10ms (per DESIGN.md)
fn bench_macrobench_cold_start(c: &mut Criterion) {
    c.bench_function("macrobench/cold_start", |b| {
        b.iter(|| {
            let env = Environment::new();
            let tc = TypeChecker::new(&env);
            tc.infer_type(black_box(&Expr::prop())).unwrap()
        });
    });
}

/// Generate N simple axiom declarations for batch benchmarks
fn generate_simple_lemmas(n: usize) -> Vec<Declaration> {
    (0..n)
        .map(|i| Declaration::Axiom {
            name: Name::from_string(&format!("lemma_{}", i)),
            level_params: vec![],
            type_: Expr::prop(),
        })
        .collect()
}

/// Macrobenchmark 2: Batch Declaration Insertion
///
/// Inserts N simple axiom declarations into the environment.
/// Note: This measures insertion throughput, not type-checking - axioms
/// bypass verification (they declare types without proof terms).
/// Targets:
/// - 100 axioms: <20ms (200us/decl)
/// - 1000 axioms: <100ms (100us/decl)
/// - 10000 axioms: <1s (100us/decl)
fn bench_macrobench_batch_lemmas(c: &mut Criterion) {
    let mut group = c.benchmark_group("macrobench/batch_lemmas");

    for n in [100, 1000, 10000] {
        let lemmas = generate_simple_lemmas(n);
        group.throughput(Throughput::Elements(n as u64));

        group.bench_with_input(BenchmarkId::from_parameter(n), &lemmas, |b, lemmas| {
            b.iter(|| {
                let mut env = Environment::new();
                for lemma in lemmas {
                    env.add_decl(lemma.clone()).unwrap();
                }
            });
        });
    }
    group.finish();
}

/// Get current process RSS in megabytes
fn measure_rss_mb() -> f64 {
    let mut system = System::new();
    system.refresh_all();
    let pid = sysinfo::get_current_pid().expect("Failed to get current PID");
    system
        .process(pid)
        .map(|p| p.memory() as f64 / 1024.0 / 1024.0)
        .unwrap_or(0.0)
}

/// Macrobenchmark 3: Memory Pressure
///
/// Tracks RSS growth under sustained load (100K operations).
/// Target: Linear or sub-linear growth, no unbounded accumulation.
fn bench_macrobench_memory_pressure(c: &mut Criterion) {
    let mut group = c.benchmark_group("macrobench/memory");

    // Run once outside benchmark to get memory stats (criterion iterations
    // would interfere with meaningful memory measurement)
    let baseline_mb = measure_rss_mb();

    let mut env = Environment::new();
    for i in 0..100_000 {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(&format!("m_{}", i)),
            level_params: vec![],
            type_: Expr::prop(),
        })
        .unwrap();
    }

    let final_mb = measure_rss_mb();
    let growth_mb = final_mb - baseline_mb;

    // Print memory stats to stderr for visibility
    eprintln!(
        "\n[Memory] Baseline: {:.1}MB, Final: {:.1}MB, Growth: {:.1}MB ({:.2} KB/decl)",
        baseline_mb,
        final_mb,
        growth_mb,
        growth_mb * 1024.0 / 100_000.0
    );

    // Benchmark one type check to get criterion output (the memory measurement
    // above is the meaningful metric)
    group.bench_function("100k_ops_typecheck", |b| {
        let tc = TypeChecker::new(&env);
        b.iter(|| tc.infer_type(black_box(&Expr::prop())));
    });

    group.finish();
}

criterion_group!(
    cert_benches,
    bench_cert_builder_valid,
    bench_cert_builder_fail_fast,
    bench_cert_builder_batch,
);

criterion_group!(
    macrobenches,
    bench_macrobench_cold_start,
    bench_macrobench_batch_lemmas,
    bench_macrobench_memory_pressure,
);

criterion_main!(cert_benches, macrobenches);
