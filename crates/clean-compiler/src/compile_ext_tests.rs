// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the extended compilation pipeline (`compile_ext`).
//!
//! Part of #3083.

use super::compile_ext::*;
use crate::compile::{CompileConfig, OptLevel};
use crate::lcnf::{Code, Decl, DeclValue, Param};
use clean_kernel::{Environment, FVarId, Name};
use std::collections::HashMap;

fn make_test_decl(name: &str) -> Decl {
    let x = FVarId::new(0);
    Decl {
        name: Name::from_string(name),
        level_params: vec![Name::from_string("u")],
        ty: clean_kernel::Expr::const_str("Nat"),
        params: vec![Param::new(
            x,
            Name::from_string("x"),
            clean_kernel::Expr::const_str("Nat"),
        )],
        body: DeclValue::Code(Box::new(Code::Return(x))),
        recursive: false,
    }
}

fn make_recursive_decl(name: &str) -> Decl {
    let x = FVarId::new(0);
    Decl {
        name: Name::from_string(name),
        level_params: vec![],
        ty: clean_kernel::Expr::const_str("Nat"),
        params: vec![Param::new(
            x,
            Name::from_string("x"),
            clean_kernel::Expr::const_str("Nat"),
        )],
        body: DeclValue::Code(Box::new(Code::Return(x))),
        recursive: true,
    }
}

fn default_env() -> Environment {
    Environment::new()
}

// --- CompileStage tests ---

#[test]
fn test_compile_stage_all_ordered_returns_five_stages() {
    let stages = CompileStage::all_ordered();
    assert_eq!(stages.len(), 5);
}

#[test]
fn test_compile_stage_ordering_lcnf_first() {
    let stages = CompileStage::all_ordered();
    assert_eq!(stages[0], CompileStage::Lcnf);
    assert_eq!(stages[1], CompileStage::Mono);
    assert_eq!(stages[2], CompileStage::IrLower);
    assert_eq!(stages[3], CompileStage::Optimize);
    assert_eq!(stages[4], CompileStage::Backend);
}

#[test]
fn test_compile_stage_names() {
    assert_eq!(CompileStage::Lcnf.name(), "lcnf");
    assert_eq!(CompileStage::Mono.name(), "mono");
    assert_eq!(CompileStage::IrLower.name(), "ir_lower");
    assert_eq!(CompileStage::Optimize.name(), "optimize");
    assert_eq!(CompileStage::Backend.name(), "backend");
}

// --- Backend tests ---

#[test]
fn test_backend_default_is_c() {
    assert_eq!(Backend::default(), Backend::C);
}

#[test]
fn test_backend_names() {
    assert_eq!(Backend::C.name(), "c");
    assert_eq!(Backend::Rust.name(), "rust");
    assert_eq!(Backend::Llvm.name(), "llvm");
    assert_eq!(Backend::Interpreter.name(), "interpreter");
}

// --- ProfileData tests ---

#[test]
fn test_profile_data_empty() {
    let profile = ProfileData::empty();
    assert!(profile.decl_profiles.is_empty());
    assert!(profile.inline_threshold_override.is_none());
}

#[test]
fn test_profile_data_is_hot_returns_false_for_unknown() {
    let profile = ProfileData::empty();
    let name = Name::from_string("unknown_fn");
    assert!(!profile.is_hot(&name));
}

#[test]
fn test_profile_data_is_hot_returns_true_for_hot_decl() {
    let mut profile = ProfileData::empty();
    let name = Name::from_string("hot_fn");
    profile.decl_profiles.insert(
        name.clone(),
        DeclProfile {
            call_count: 10000,
            is_hot: true,
        },
    );
    assert!(profile.is_hot(&name));
}

#[test]
fn test_profile_data_effective_inline_threshold_no_override() {
    let profile = ProfileData::empty();
    assert_eq!(profile.effective_inline_threshold(50), 50);
}

#[test]
fn test_profile_data_effective_inline_threshold_with_override() {
    let mut profile = ProfileData::empty();
    profile.inline_threshold_override = Some(200);
    assert_eq!(profile.effective_inline_threshold(50), 200);
}

// --- CompileStats tests ---

#[test]
fn test_compile_stats_default_zeroes() {
    let stats = CompileStats::default();
    assert_eq!(stats.decls_compiled, 0);
    assert_eq!(stats.decls_skipped, 0);
    assert_eq!(stats.optimizations_applied, 0);
    assert_eq!(stats.cache_hits, 0);
    assert_eq!(stats.cache_misses, 0);
    assert_eq!(stats.errors_recovered, 0);
}

#[test]
fn test_compile_stats_total_duration_empty() {
    let stats = CompileStats::default();
    assert_eq!(stats.total_duration(), std::time::Duration::ZERO);
}

// --- CompileCache tests ---

#[test]
fn test_compile_cache_new_is_empty() {
    let cache = CompileCache::new();
    assert!(cache.is_empty());
    assert_eq!(cache.len(), 0);
}

#[test]
fn test_compile_cache_insert_and_get() {
    let mut cache = CompileCache::new();
    let name = Name::from_string("test_fn");
    let hash = 42u64;
    let ir_decls = vec![]; // empty for testing
    cache.insert(name.clone(), hash, ir_decls);

    assert_eq!(cache.len(), 1);
    assert!(!cache.is_empty());
    assert!(cache.get(&name, hash).is_some());
}

#[test]
fn test_compile_cache_miss_on_different_hash() {
    let mut cache = CompileCache::new();
    let name = Name::from_string("test_fn");
    cache.insert(name.clone(), 42, vec![]);

    // Different hash should miss
    assert!(cache.get(&name, 99).is_none());
}

#[test]
fn test_compile_cache_miss_on_unknown_name() {
    let mut cache = CompileCache::new();
    cache.insert(Name::from_string("known"), 42, vec![]);

    let unknown = Name::from_string("unknown");
    assert!(cache.get(&unknown, 42).is_none());
}

#[test]
fn test_compile_cache_clear() {
    let mut cache = CompileCache::new();
    cache.insert(Name::from_string("fn_a"), 1, vec![]);
    cache.insert(Name::from_string("fn_b"), 2, vec![]);
    assert_eq!(cache.len(), 2);

    cache.clear();
    assert!(cache.is_empty());
    assert_eq!(cache.len(), 0);
}

// --- ExtCompileConfig tests ---

#[test]
fn test_ext_compile_config_default() {
    let config = ExtCompileConfig::default();
    assert_eq!(config.backend, Backend::C);
    assert!(!config.incremental);
    assert!(!config.error_recovery);
    assert!(!config.enable_cache);
    assert!(!config.parallel);
    assert!(config.profile_data.is_none());
}

// --- decl_hash tests ---

#[test]
fn test_decl_hash_same_decl_same_hash() {
    let decl = make_test_decl("my_fn");
    let h1 = decl_hash(&decl);
    let h2 = decl_hash(&decl);
    assert_eq!(h1, h2);
}

#[test]
fn test_decl_hash_different_names_different_hash() {
    let d1 = make_test_decl("fn_a");
    let d2 = make_test_decl("fn_b");
    assert_ne!(decl_hash(&d1), decl_hash(&d2));
}

#[test]
fn test_decl_hash_recursive_flag_affects_hash() {
    let d1 = make_test_decl("fn_x");
    let d2 = make_recursive_decl("fn_x");
    assert_ne!(decl_hash(&d1), decl_hash(&d2));
}

// --- partition_independent_decls tests ---

#[test]
fn test_partition_empty_input() {
    let result = partition_independent_decls(&[]);
    assert!(result.is_empty());
}

#[test]
fn test_partition_single_decl() {
    let decl = make_test_decl("single");
    let result = partition_independent_decls(&[decl]);
    assert_eq!(result.len(), 1);
    assert_eq!(result[0], vec![0]);
}

#[test]
fn test_partition_multiple_decls() {
    let decls = vec![
        make_test_decl("fn_a"),
        make_test_decl("fn_b"),
        make_test_decl("fn_c"),
    ];
    let result = partition_independent_decls(&decls);
    assert_eq!(result.len(), 3);
    for (i, group) in result.iter().enumerate() {
        assert_eq!(group, &vec![i]);
    }
}

// --- CompileContext tests ---

#[test]
fn test_compile_context_new_starts_at_lcnf() {
    let ctx = CompileContext::new(ExtCompileConfig::default());
    assert_eq!(ctx.current_stage, CompileStage::Lcnf);
    assert!(ctx.diagnostics.is_empty());
    assert_eq!(ctx.stats.decls_compiled, 0);
}

#[test]
fn test_compile_context_add_diagnostic_recovered() {
    let mut ctx = CompileContext::new(ExtCompileConfig::default());
    ctx.add_diagnostic(
        Some(Name::from_string("failing_fn")),
        "some error".to_owned(),
        true,
    );
    assert_eq!(ctx.diagnostics.len(), 1);
    assert!(ctx.diagnostics[0].recovered);
    assert_eq!(ctx.stats.errors_recovered, 1);
}

#[test]
fn test_compile_context_add_diagnostic_not_recovered() {
    let mut ctx = CompileContext::new(ExtCompileConfig::default());
    ctx.add_diagnostic(None, "warning".to_owned(), false);
    assert_eq!(ctx.diagnostics.len(), 1);
    assert!(!ctx.diagnostics[0].recovered);
    assert_eq!(ctx.stats.errors_recovered, 0);
}

#[test]
fn test_compile_context_record_stage_duration() {
    let mut ctx = CompileContext::new(ExtCompileConfig::default());
    let dur = std::time::Duration::from_millis(50);
    ctx.record_stage_duration(CompileStage::Mono, dur);
    assert_eq!(
        ctx.stats.stage_durations.get(&CompileStage::Mono),
        Some(&dur)
    );
}

// --- Thread-local context tests ---

#[test]
fn test_init_and_take_compile_context() {
    init_compile_context(ExtCompileConfig::default());
    let ctx = take_compile_context();
    assert!(ctx.is_some());
    // After take, should be None
    let ctx2 = take_compile_context();
    assert!(ctx2.is_none());
}

// --- apply_pgo_adjustments tests ---

#[test]
fn test_apply_pgo_adjustments_with_threshold_override() {
    let mut config = ExtCompileConfig::default();
    config.base.optimization_level = OptLevel::Basic;

    let mut profile = ProfileData::empty();
    profile.inline_threshold_override = Some(300);

    apply_pgo_adjustments(&mut config, &profile);
    assert_eq!(config.base.optimization_level, OptLevel::Full);
}

#[test]
fn test_apply_pgo_adjustments_no_override_no_change() {
    let mut config = ExtCompileConfig::default();
    config.base.optimization_level = OptLevel::Basic;

    let profile = ProfileData::empty();
    apply_pgo_adjustments(&mut config, &profile);
    // No threshold override means no change
    assert_eq!(config.base.optimization_level, OptLevel::Basic);
}

// --- compile_ext integration tests ---

#[test]
fn test_compile_ext_empty_input() {
    let env = default_env();
    let config = ExtCompileConfig::default();
    let mut cache = CompileCache::new();
    let prev_hashes = HashMap::new();

    let result = compile_ext(&[], &env, &config, &mut cache, &prev_hashes)
        .expect("empty input should succeed");
    assert!(result.base_result.decls.is_empty());
    assert_eq!(result.stats.decls_compiled, 0);
    assert_eq!(result.stats.decls_skipped, 0);
}

#[test]
fn test_compile_ext_single_decl() {
    let env = default_env();
    let config = ExtCompileConfig::default();
    let mut cache = CompileCache::new();
    let prev_hashes = HashMap::new();
    let decl = make_test_decl("single_fn");

    let result = compile_ext(&[decl], &env, &config, &mut cache, &prev_hashes)
        .expect("single decl should compile");
    assert!(!result.base_result.decls.is_empty());
    assert_eq!(result.stats.decls_compiled, 1);
    assert_eq!(result.backend, Backend::C);
}

#[test]
fn test_compile_ext_backend_selection_rust() {
    let env = default_env();
    let config = ExtCompileConfig {
        backend: Backend::Rust,
        ..ExtCompileConfig::default()
    };
    let mut cache = CompileCache::new();
    let prev_hashes = HashMap::new();
    let decl = make_test_decl("fn_rust");

    let result = compile_ext(&[decl], &env, &config, &mut cache, &prev_hashes)
        .expect("compile should succeed");
    assert_eq!(result.backend, Backend::Rust);
    assert!(
        result
            .base_result
            .passes_run
            .iter()
            .any(|p| p.contains("rust")),
        "passes should reference rust backend"
    );
}

#[test]
fn test_compile_ext_backend_selection_llvm() {
    let env = default_env();
    let config = ExtCompileConfig {
        backend: Backend::Llvm,
        ..ExtCompileConfig::default()
    };
    let mut cache = CompileCache::new();
    let prev_hashes = HashMap::new();
    let decl = make_test_decl("fn_llvm");

    let result = compile_ext(&[decl], &env, &config, &mut cache, &prev_hashes)
        .expect("compile should succeed");
    assert_eq!(result.backend, Backend::Llvm);
}

#[test]
fn test_compile_ext_backend_selection_interpreter() {
    let env = default_env();
    let config = ExtCompileConfig {
        backend: Backend::Interpreter,
        ..ExtCompileConfig::default()
    };
    let mut cache = CompileCache::new();
    let prev_hashes = HashMap::new();
    let decl = make_test_decl("fn_interp");

    let result = compile_ext(&[decl], &env, &config, &mut cache, &prev_hashes)
        .expect("compile should succeed");
    assert_eq!(result.backend, Backend::Interpreter);
}

#[test]
fn test_compile_ext_incremental_skip_unchanged() {
    let env = default_env();
    let decl = make_test_decl("cached_fn");
    let hash = decl_hash(&decl);

    let mut prev_hashes = HashMap::new();
    prev_hashes.insert(decl.name.clone(), hash);

    let config = ExtCompileConfig {
        incremental: true,
        ..ExtCompileConfig::default()
    };
    let mut cache = CompileCache::new();

    let result = compile_ext(&[decl], &env, &config, &mut cache, &prev_hashes)
        .expect("incremental compile should succeed");
    assert_eq!(result.stats.decls_skipped, 1);
    assert_eq!(result.stats.decls_compiled, 0);
}

#[test]
fn test_compile_ext_incremental_compiles_changed() {
    let env = default_env();
    let decl = make_test_decl("changed_fn");

    // Previous hash differs from current
    let mut prev_hashes = HashMap::new();
    prev_hashes.insert(decl.name.clone(), 0u64);

    let config = ExtCompileConfig {
        incremental: true,
        ..ExtCompileConfig::default()
    };
    let mut cache = CompileCache::new();

    let result = compile_ext(&[decl], &env, &config, &mut cache, &prev_hashes)
        .expect("incremental compile of changed decl should succeed");
    assert_eq!(result.stats.decls_compiled, 1);
    assert_eq!(result.stats.decls_skipped, 0);
}

#[test]
fn test_compile_ext_cache_populates_on_compile() {
    let env = default_env();
    let decl = make_test_decl("cacheable_fn");
    let config = ExtCompileConfig {
        enable_cache: true,
        ..ExtCompileConfig::default()
    };
    let mut cache = CompileCache::new();
    let prev_hashes = HashMap::new();

    assert!(cache.is_empty());
    compile_ext(
        std::slice::from_ref(&decl),
        &env,
        &config,
        &mut cache,
        &prev_hashes,
    )
    .expect("compile should succeed");
    assert_eq!(cache.len(), 1);

    // Second compile should hit cache
    let result = compile_ext(&[decl], &env, &config, &mut cache, &prev_hashes)
        .expect("second compile should succeed");
    assert_eq!(result.stats.cache_hits, 1);
}

#[test]
fn test_compile_ext_stats_track_time() {
    let env = default_env();
    let decl = make_test_decl("timed_fn");
    let config = ExtCompileConfig::default();
    let mut cache = CompileCache::new();
    let prev_hashes = HashMap::new();

    let result = compile_ext(&[decl], &env, &config, &mut cache, &prev_hashes)
        .expect("compile should succeed");
    // At minimum, lcnf stage should have a duration recorded
    assert!(result
        .stats
        .stage_durations
        .contains_key(&CompileStage::Lcnf));
}

#[test]
fn test_compile_ext_multiple_decls() {
    let env = default_env();
    let decls = vec![
        make_test_decl("fn_one"),
        make_test_decl("fn_two"),
        make_test_decl("fn_three"),
    ];
    let config = ExtCompileConfig::default();
    let mut cache = CompileCache::new();
    let prev_hashes = HashMap::new();

    let result = compile_ext(&decls, &env, &config, &mut cache, &prev_hashes)
        .expect("multiple decls should compile");
    assert_eq!(result.stats.decls_compiled, 3);
    assert!(result.base_result.decls.len() >= 3);
}

#[test]
fn test_compile_ext_incremental_with_cache_returns_cached_on_skip() {
    let env = default_env();
    let decl = make_test_decl("inc_cache_fn");
    let hash = decl_hash(&decl);

    // First pass: compile normally to populate cache
    let config = ExtCompileConfig {
        incremental: true,
        enable_cache: true,
        ..ExtCompileConfig::default()
    };
    let mut cache = CompileCache::new();
    let prev_hashes_empty = HashMap::new();

    compile_ext(
        std::slice::from_ref(&decl),
        &env,
        &config,
        &mut cache,
        &prev_hashes_empty,
    )
    .expect("first compile should succeed");
    assert_eq!(cache.len(), 1);

    // Second pass: same hash in prev_hashes, should hit cache
    let mut prev_hashes = HashMap::new();
    prev_hashes.insert(decl.name.clone(), hash);

    let result = compile_ext(&[decl], &env, &config, &mut cache, &prev_hashes)
        .expect("incremental+cached compile should succeed");
    assert_eq!(result.stats.decls_skipped, 1);
    assert_eq!(result.stats.cache_hits, 1);
}

#[test]
fn test_compile_ext_passes_run_includes_backend() {
    let env = default_env();
    let decl = make_test_decl("backend_fn");
    let config = ExtCompileConfig {
        backend: Backend::C,
        ..ExtCompileConfig::default()
    };
    let mut cache = CompileCache::new();
    let prev_hashes = HashMap::new();

    let result = compile_ext(&[decl], &env, &config, &mut cache, &prev_hashes)
        .expect("compile should succeed");
    assert!(
        result
            .base_result
            .passes_run
            .iter()
            .any(|p| p == "backend:c"),
        "passes_run should include backend:c"
    );
}

#[test]
fn test_compile_ext_parallel_flag_accepted() {
    let env = default_env();
    let decl = make_test_decl("parallel_fn");
    let config = ExtCompileConfig {
        parallel: true,
        ..ExtCompileConfig::default()
    };
    let mut cache = CompileCache::new();
    let prev_hashes = HashMap::new();

    // parallel=true should not cause failure (scheduling is logical, not threaded here)
    let result = compile_ext(&[decl], &env, &config, &mut cache, &prev_hashes)
        .expect("parallel compile should succeed");
    assert_eq!(result.stats.decls_compiled, 1);
}

#[test]
fn test_compile_ext_profile_data_integration() {
    let env = default_env();
    let decl = make_test_decl("profiled_fn");

    let mut profile = ProfileData::empty();
    profile.decl_profiles.insert(
        Name::from_string("profiled_fn"),
        DeclProfile {
            call_count: 5000,
            is_hot: true,
        },
    );
    profile.inline_threshold_override = Some(150);

    let config = ExtCompileConfig {
        profile_data: Some(profile),
        ..ExtCompileConfig::default()
    };
    let mut cache = CompileCache::new();
    let prev_hashes = HashMap::new();

    let result = compile_ext(&[decl], &env, &config, &mut cache, &prev_hashes)
        .expect("profiled compile should succeed");
    assert_eq!(result.stats.decls_compiled, 1);
}

#[test]
fn test_compile_ext_all_error_input_with_recovery() {
    // When error_recovery is enabled and all decls error, we should get
    // a result with 0 compiled and recovered errors instead of a hard failure.
    // We use an extern decl with an unknown symbol to trigger an error.
    let env = default_env();
    let bad_decl = crate::lcnf::Decl::extern_decl(
        Name::from_string("bad_fn"),
        vec![],
        clean_kernel::Expr::const_str("Unit"),
        vec![],
        vec![crate::lcnf::ExternEntry {
            backend: "c".to_owned(),
            name: "unknown_symbol_that_does_not_exist".to_owned(),
        }],
    );

    let config = ExtCompileConfig {
        error_recovery: true,
        ..ExtCompileConfig::default()
    };
    let mut cache = CompileCache::new();
    let prev_hashes = HashMap::new();

    let result = compile_ext(&[bad_decl], &env, &config, &mut cache, &prev_hashes)
        .expect("error recovery should prevent hard failure");
    assert_eq!(result.stats.decls_compiled, 0);
    assert!(result.stats.errors_recovered > 0);
}

#[test]
fn test_compile_ext_no_error_recovery_propagates_error() {
    let env = default_env();
    let bad_decl = crate::lcnf::Decl::extern_decl(
        Name::from_string("bad_fn2"),
        vec![],
        clean_kernel::Expr::const_str("Unit"),
        vec![],
        vec![crate::lcnf::ExternEntry {
            backend: "c".to_owned(),
            name: "unknown_symbol_that_does_not_exist".to_owned(),
        }],
    );

    let config = ExtCompileConfig {
        error_recovery: false,
        ..ExtCompileConfig::default()
    };
    let mut cache = CompileCache::new();
    let prev_hashes = HashMap::new();

    let err = compile_ext(&[bad_decl], &env, &config, &mut cache, &prev_hashes)
        .expect_err("without error recovery, bad decl should fail");
    // Verify it is a pipeline error
    let msg = format!("{err}");
    assert!(!msg.is_empty());
}

#[test]
fn test_compile_diagnostic_fields() {
    let diag = CompileDiagnostic {
        decl_name: Some(Name::from_string("test")),
        stage: CompileStage::Mono,
        message: "test diagnostic".to_owned(),
        recovered: true,
    };
    assert_eq!(diag.stage, CompileStage::Mono);
    assert!(diag.recovered);
    assert_eq!(diag.message, "test diagnostic");
    assert!(diag.decl_name.is_some());
}
