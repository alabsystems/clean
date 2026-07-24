// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for native_codegen_ext2: compilation pipelines, caching, JIT.

use std::path::{Path, PathBuf};
use std::time::Duration;

use super::native_codegen_ext2::*;
use crate::native_codegen_ext::NativeTarget;

// ---------------------------------------------------------------------------
// TargetTriple parsing
// ---------------------------------------------------------------------------

#[test]
fn test_target_triple_parse_x86_64_apple_darwin() {
    let t = TargetTriple::parse("x86_64-apple-darwin").expect("should parse");
    assert_eq!(t.arch, Arch::X86_64);
    assert_eq!(t.vendor, "apple");
    assert_eq!(t.os, Os::Darwin);
    assert_eq!(t.as_str(), "x86_64-apple-darwin");
}

#[test]
fn test_target_triple_parse_aarch64_apple_darwin() {
    let t = TargetTriple::parse("aarch64-apple-darwin").expect("should parse");
    assert_eq!(t.arch, Arch::Aarch64);
    assert_eq!(t.os, Os::Darwin);
}

#[test]
fn test_target_triple_parse_arm64_alias() {
    let t = TargetTriple::parse("arm64-apple-darwin").expect("should parse arm64 alias");
    assert_eq!(t.arch, Arch::Aarch64);
}

#[test]
fn test_target_triple_parse_x86_64_linux_gnu() {
    let t = TargetTriple::parse("x86_64-unknown-linux-gnu").expect("should parse");
    assert_eq!(t.arch, Arch::X86_64);
    assert_eq!(t.vendor, "unknown");
    assert_eq!(t.os, Os::Linux);
}

#[test]
fn test_target_triple_parse_aarch64_linux_gnu() {
    let t = TargetTriple::parse("aarch64-unknown-linux-gnu").expect("should parse");
    assert_eq!(t.arch, Arch::Aarch64);
    assert_eq!(t.os, Os::Linux);
}

#[test]
fn test_target_triple_parse_wasm32() {
    let t = TargetTriple::parse("wasm32-unknown-unknown").expect("should parse");
    assert_eq!(t.arch, Arch::Wasm32);
    assert_eq!(t.os, Os::Unknown);
}

#[test]
fn test_target_triple_parse_windows() {
    let t = TargetTriple::parse("x86_64-pc-windows-msvc").expect("should parse");
    assert_eq!(t.arch, Arch::X86_64);
    assert_eq!(t.os, Os::Windows);
}

#[test]
fn test_target_triple_parse_invalid_too_few_parts() {
    let err = TargetTriple::parse("x86_64").unwrap_err();
    assert!(matches!(err, NativeCompileError::UnsupportedTarget(_)));
}

#[test]
fn test_target_triple_parse_invalid_arch() {
    let err = TargetTriple::parse("mips-unknown-linux-gnu").unwrap_err();
    assert!(matches!(err, NativeCompileError::UnsupportedTarget(_)));
}

#[test]
fn test_target_triple_host_returns_valid() {
    let host = TargetTriple::host();
    assert!(!host.as_str().is_empty());
    // Host must parse back to itself
    let reparsed = TargetTriple::parse(host.as_str()).expect("host triple should re-parse");
    assert_eq!(reparsed.arch, host.arch);
    assert_eq!(reparsed.os, host.os);
}

#[test]
fn test_target_triple_display() {
    let t = TargetTriple::parse("x86_64-apple-darwin").expect("should parse");
    assert_eq!(format!("{t}"), "x86_64-apple-darwin");
}

// ---------------------------------------------------------------------------
// Shared lib / object extensions
// ---------------------------------------------------------------------------

#[test]
fn test_shared_lib_ext_darwin() {
    let t = TargetTriple::parse("aarch64-apple-darwin").expect("parse");
    assert_eq!(t.shared_lib_ext(), "dylib");
}

#[test]
fn test_shared_lib_ext_linux() {
    let t = TargetTriple::parse("x86_64-unknown-linux-gnu").expect("parse");
    assert_eq!(t.shared_lib_ext(), "so");
}

#[test]
fn test_shared_lib_ext_windows() {
    let t = TargetTriple::parse("x86_64-pc-windows-msvc").expect("parse");
    assert_eq!(t.shared_lib_ext(), "dll");
}

#[test]
fn test_object_ext_unix() {
    let t = TargetTriple::parse("x86_64-unknown-linux-gnu").expect("parse");
    assert_eq!(t.object_ext(), "o");
}

#[test]
fn test_object_ext_windows() {
    let t = TargetTriple::parse("x86_64-pc-windows-msvc").expect("parse");
    assert_eq!(t.object_ext(), "obj");
}

// ---------------------------------------------------------------------------
// Backend selection
// ---------------------------------------------------------------------------

#[test]
fn test_select_backend_default_is_c() {
    let t = TargetTriple::parse("x86_64-unknown-linux-gnu").expect("parse");
    assert_eq!(select_backend(&t, None), NativeTarget::C);
}

#[test]
fn test_select_backend_preferred_override() {
    let t = TargetTriple::parse("x86_64-unknown-linux-gnu").expect("parse");
    assert_eq!(
        select_backend(&t, Some(NativeTarget::Llvm)),
        NativeTarget::Llvm
    );
}

#[test]
fn test_select_backend_wasm_default_c() {
    let t = TargetTriple::parse("wasm32-unknown-unknown").expect("parse");
    assert_eq!(select_backend(&t, None), NativeTarget::C);
}

#[test]
fn test_select_backend_preferred_rust() {
    let t = TargetTriple::parse("aarch64-apple-darwin").expect("parse");
    assert_eq!(
        select_backend(&t, Some(NativeTarget::Rust)),
        NativeTarget::Rust
    );
}

// ---------------------------------------------------------------------------
// CompilerCommand construction
// ---------------------------------------------------------------------------

#[test]
fn test_c_compile_command_linux() {
    let t = TargetTriple::parse("x86_64-unknown-linux-gnu").expect("parse");
    let cmd = CompilerCommand::c_compile(
        Path::new("/tmp/test.c"),
        Path::new("/tmp/test.o"),
        &t,
        false,
    );
    assert_eq!(cmd.tool, "cc");
    assert!(cmd.args.contains(&"-c".to_owned()));
    assert!(cmd.args.contains(&"-fPIC".to_owned()));
    assert!(!cmd.args.contains(&"-O2".to_owned()));
}

#[test]
fn test_c_compile_command_darwin() {
    let t = TargetTriple::parse("aarch64-apple-darwin").expect("parse");
    let cmd =
        CompilerCommand::c_compile(Path::new("/tmp/test.c"), Path::new("/tmp/test.o"), &t, true);
    assert_eq!(cmd.tool, "clang");
    assert!(cmd.args.contains(&"-O2".to_owned()));
}

#[test]
fn test_c_compile_command_has_output_path() {
    let t = TargetTriple::parse("x86_64-unknown-linux-gnu").expect("parse");
    let cmd =
        CompilerCommand::c_compile(Path::new("/src/mod.c"), Path::new("/out/mod.o"), &t, false);
    assert_eq!(cmd.output, PathBuf::from("/out/mod.o"));
    assert_eq!(cmd.source, PathBuf::from("/src/mod.c"));
}

#[test]
fn test_rust_compile_command() {
    let t = TargetTriple::parse("x86_64-unknown-linux-gnu").expect("parse");
    let cmd =
        CompilerCommand::rust_compile(Path::new("/tmp/lib.rs"), Path::new("/tmp/lib.o"), &t, true);
    assert_eq!(cmd.tool, "rustc");
    assert!(cmd.args.contains(&"--crate-type".to_owned()));
    assert!(cmd.args.contains(&"staticlib".to_owned()));
    assert!(cmd.args.contains(&"-O".to_owned()));
    assert!(cmd.args.contains(&"--target".to_owned()));
}

// ---------------------------------------------------------------------------
// LinkerCommand
// ---------------------------------------------------------------------------

#[test]
fn test_linker_command_darwin() {
    let t = TargetTriple::parse("aarch64-apple-darwin").expect("parse");
    let objs = vec![PathBuf::from("/tmp/a.o"), PathBuf::from("/tmp/b.o")];
    let cmd = LinkerCommand::for_target(&objs, Path::new("/tmp/lib.dylib"), &t);
    assert_eq!(cmd.tool, "clang");
    assert!(cmd.args.contains(&"-dynamiclib".to_owned()));
    assert_eq!(cmd.objects.len(), 2);
}

#[test]
fn test_linker_command_linux() {
    let t = TargetTriple::parse("x86_64-unknown-linux-gnu").expect("parse");
    let objs = vec![PathBuf::from("/tmp/a.o")];
    let cmd = LinkerCommand::for_target(&objs, Path::new("/tmp/lib.so"), &t);
    assert_eq!(cmd.tool, "cc");
    assert!(cmd.args.contains(&"-shared".to_owned()));
}

#[test]
fn test_linker_command_windows() {
    let t = TargetTriple::parse("x86_64-pc-windows-msvc").expect("parse");
    let objs = vec![PathBuf::from("a.obj")];
    let cmd = LinkerCommand::for_target(&objs, Path::new("lib.dll"), &t);
    assert_eq!(cmd.tool, "link.exe");
    assert!(cmd.args.contains(&"/DLL".to_owned()));
}

// ---------------------------------------------------------------------------
// CompilationCache
// ---------------------------------------------------------------------------

#[test]
fn test_cache_new_valid_dir() {
    let cache = CompilationCache::new(Path::new("/tmp")).expect("should create cache");
    assert!(cache.is_empty());
    assert_eq!(cache.len(), 0);
}

#[test]
fn test_cache_new_invalid_dir() {
    let err = CompilationCache::new(Path::new("/nonexistent_dir_abc123")).unwrap_err();
    assert!(matches!(err, NativeCompileError::CacheError(_)));
}

#[test]
fn test_cache_insert_and_lookup() {
    let mut cache = CompilationCache::new(Path::new("/tmp")).expect("should create");
    assert!(cache.lookup(42).is_none());
    cache.insert(42, Path::new("/tmp/cached.o"));
    assert_eq!(cache.lookup(42), Some(Path::new("/tmp/cached.o")));
    assert_eq!(cache.len(), 1);
    assert!(!cache.is_empty());
}

#[test]
fn test_cache_overwrite() {
    let mut cache = CompilationCache::new(Path::new("/tmp")).expect("should create");
    cache.insert(1, Path::new("/tmp/v1.o"));
    cache.insert(1, Path::new("/tmp/v2.o"));
    assert_eq!(cache.lookup(1), Some(Path::new("/tmp/v2.o")));
    assert_eq!(cache.len(), 1);
}

#[test]
fn test_cache_hash_content_deterministic() {
    let h1 = CompilationCache::hash_content(b"hello world");
    let h2 = CompilationCache::hash_content(b"hello world");
    assert_eq!(h1, h2);
}

#[test]
fn test_cache_hash_content_different_inputs() {
    let h1 = CompilationCache::hash_content(b"hello");
    let h2 = CompilationCache::hash_content(b"world");
    assert_ne!(h1, h2);
}

#[test]
fn test_cache_hash_content_empty() {
    let h = CompilationCache::hash_content(b"");
    // FNV-1a offset basis
    assert_eq!(h, 0xcbf2_9ce4_8422_2325);
}

#[test]
fn test_cache_dir_accessor() {
    let cache = CompilationCache::new(Path::new("/tmp")).expect("should create");
    assert_eq!(cache.cache_dir(), Path::new("/tmp"));
}

// ---------------------------------------------------------------------------
// ParallelCompilePlan
// ---------------------------------------------------------------------------

#[test]
fn test_parallel_plan_empty() {
    let t = TargetTriple::parse("x86_64-unknown-linux-gnu").expect("parse");
    let plan = ParallelCompilePlan::new(t, false, PathBuf::from("/tmp/out"));
    assert_eq!(plan.unit_count(), 0);
}

#[test]
fn test_parallel_plan_add_units() {
    let t = TargetTriple::parse("x86_64-unknown-linux-gnu").expect("parse");
    let mut plan = ParallelCompilePlan::new(t, true, PathBuf::from("/tmp/out"));
    plan.add_unit(CompilationUnit {
        name: "mod_a".to_owned(),
        source_path: PathBuf::from("/tmp/mod_a.c"),
        backend: NativeTarget::C,
        content_hash: 100,
    });
    plan.add_unit(CompilationUnit {
        name: "mod_b".to_owned(),
        source_path: PathBuf::from("/tmp/mod_b.c"),
        backend: NativeTarget::C,
        content_hash: 200,
    });
    assert_eq!(plan.unit_count(), 2);
}

#[test]
fn test_parallel_plan_generate_commands_no_cache() {
    let t = TargetTriple::parse("x86_64-unknown-linux-gnu").expect("parse");
    let mut plan = ParallelCompilePlan::new(t, false, PathBuf::from("/tmp/out"));
    plan.add_unit(CompilationUnit {
        name: "test_mod".to_owned(),
        source_path: PathBuf::from("/tmp/test_mod.c"),
        backend: NativeTarget::C,
        content_hash: 999,
    });
    let cache = CompilationCache::new(Path::new("/tmp")).expect("cache");
    let (cmds, cached) = plan.generate_commands(&cache);
    assert_eq!(cmds.len(), 1);
    assert!(cached.is_empty());
    assert_eq!(cmds[0].output, PathBuf::from("/tmp/out/test_mod.o"));
}

#[test]
fn test_parallel_plan_generate_commands_with_cache_hit() {
    let t = TargetTriple::parse("x86_64-unknown-linux-gnu").expect("parse");
    let mut plan = ParallelCompilePlan::new(t, false, PathBuf::from("/tmp/out"));
    plan.add_unit(CompilationUnit {
        name: "cached_mod".to_owned(),
        source_path: PathBuf::from("/tmp/cached_mod.c"),
        backend: NativeTarget::C,
        content_hash: 555,
    });
    let mut cache = CompilationCache::new(Path::new("/tmp")).expect("cache");
    cache.insert(555, Path::new("/tmp/cache/cached_mod.o"));
    let (cmds, cached) = plan.generate_commands(&cache);
    assert!(cmds.is_empty());
    assert_eq!(cached.len(), 1);
    assert_eq!(cached[0], PathBuf::from("/tmp/cache/cached_mod.o"));
}

// ---------------------------------------------------------------------------
// JitModule
// ---------------------------------------------------------------------------

#[test]
fn test_jit_module_new() {
    let m = JitModule::new("test_jit", PathBuf::from("/tmp/libjit.dylib"));
    assert_eq!(m.name, "test_jit");
    assert!(m.symbols.is_empty());
}

#[test]
fn test_jit_module_symbols() {
    let mut m = JitModule::new("test_jit", PathBuf::from("/tmp/libjit.so"));
    m.add_symbol("clean_eval_main");
    m.add_symbol("clean_init");
    assert!(m.has_symbol("clean_eval_main"));
    assert!(m.has_symbol("clean_init"));
    assert!(!m.has_symbol("nonexistent"));
}

#[test]
fn test_plan_jit_compile_missing_source() {
    let t = TargetTriple::parse("x86_64-unknown-linux-gnu").expect("parse");
    let err = plan_jit_compile(
        Path::new("/nonexistent_source_abc.c"),
        Path::new("/tmp"),
        "test",
        &t,
        false,
    )
    .unwrap_err();
    assert!(matches!(err, NativeCompileError::SourceNotFound(_)));
}

// ---------------------------------------------------------------------------
// SharedLibHandle
// ---------------------------------------------------------------------------

#[test]
fn test_shared_lib_handle_new() {
    let h = SharedLibHandle::new(PathBuf::from("/tmp/lib.so"));
    assert!(!h.loaded);
    assert_eq!(h.symbol_count(), 0);
}

#[test]
fn test_shared_lib_handle_mark_loaded() {
    let mut h = SharedLibHandle::new(PathBuf::from("/tmp/lib.dylib"));
    h.mark_loaded();
    assert!(h.loaded);
}

#[test]
fn test_shared_lib_handle_symbols() {
    let mut h = SharedLibHandle::new(PathBuf::from("/tmp/lib.so"));
    assert!(h.symbol_addr("init").is_none());
    h.register_symbol("init", 0xDEAD_BEEF);
    assert_eq!(h.symbol_addr("init"), Some(0xDEAD_BEEF));
    assert_eq!(h.symbol_count(), 1);
}

#[test]
fn test_shared_lib_handle_multiple_symbols() {
    let mut h = SharedLibHandle::new(PathBuf::from("/tmp/lib.so"));
    h.register_symbol("a", 1);
    h.register_symbol("b", 2);
    h.register_symbol("c", 3);
    assert_eq!(h.symbol_count(), 3);
    assert_eq!(h.symbol_addr("b"), Some(2));
}

// ---------------------------------------------------------------------------
// CompileStats
// ---------------------------------------------------------------------------

#[test]
fn test_compile_stats_new_zeroed() {
    let s = CompileStats::new();
    assert_eq!(s.modules_compiled, 0);
    assert_eq!(s.cache_hits, 0);
    assert_eq!(s.compile_time, Duration::ZERO);
    assert_eq!(s.link_time, Duration::ZERO);
    assert_eq!(s.total_time, Duration::ZERO);
}

#[test]
fn test_compile_stats_default() {
    let s = CompileStats::default();
    assert_eq!(s.modules_compiled, 0);
}

#[test]
fn test_compile_stats_record_compile() {
    let mut s = CompileStats::new();
    s.record_compile(Duration::from_millis(100));
    s.record_compile(Duration::from_millis(50));
    assert_eq!(s.modules_compiled, 2);
    assert_eq!(s.compile_time, Duration::from_millis(150));
}

#[test]
fn test_compile_stats_record_cache_hit() {
    let mut s = CompileStats::new();
    s.record_cache_hit();
    s.record_cache_hit();
    assert_eq!(s.cache_hits, 2);
}

#[test]
fn test_compile_stats_record_link() {
    let mut s = CompileStats::new();
    s.record_link(Duration::from_millis(200));
    assert_eq!(s.link_time, Duration::from_millis(200));
}

#[test]
fn test_compile_stats_finalize() {
    let mut s = CompileStats::new();
    s.finalize(Duration::from_secs(1));
    assert_eq!(s.total_time, Duration::from_secs(1));
}

#[test]
fn test_compile_stats_cache_hit_rate_zero() {
    let s = CompileStats::new();
    assert_eq!(s.cache_hit_rate(), 0.0);
}

#[test]
fn test_compile_stats_cache_hit_rate_half() {
    let mut s = CompileStats::new();
    s.record_compile(Duration::from_millis(10));
    s.record_cache_hit();
    let rate = s.cache_hit_rate();
    assert!((rate - 0.5).abs() < f64::EPSILON);
}

#[test]
fn test_compile_stats_cache_hit_rate_full() {
    let mut s = CompileStats::new();
    s.record_cache_hit();
    s.record_cache_hit();
    s.record_cache_hit();
    assert_eq!(s.cache_hit_rate(), 1.0);
}

#[test]
fn test_compile_stats_display() {
    let s = CompileStats::new();
    let display = format!("{s}");
    assert!(display.contains("compiled=0"));
    assert!(display.contains("cache_hits=0"));
}

// ---------------------------------------------------------------------------
// CompilePipeline
// ---------------------------------------------------------------------------

#[test]
fn test_pipeline_new() {
    let t = TargetTriple::parse("x86_64-unknown-linux-gnu").expect("parse");
    let p = CompilePipeline::new(t, NativeTarget::C, true);
    assert!(p.cache.is_none());
    assert_eq!(p.stats().modules_compiled, 0);
}

#[test]
fn test_pipeline_with_cache() {
    let t = TargetTriple::parse("x86_64-unknown-linux-gnu").expect("parse");
    let cache = CompilationCache::new(Path::new("/tmp")).expect("cache");
    let p = CompilePipeline::new(t, NativeTarget::C, false).with_cache(cache);
    assert!(p.cache.is_some());
}

#[test]
fn test_pipeline_plan_compile_missing_source() {
    let t = TargetTriple::parse("x86_64-unknown-linux-gnu").expect("parse");
    let mut p = CompilePipeline::new(t, NativeTarget::C, false);
    let err = p
        .plan_compile(
            Path::new("/nonexistent_file_xyz.c"),
            Path::new("/tmp"),
            "test",
        )
        .unwrap_err();
    assert!(matches!(err, NativeCompileError::SourceNotFound(_)));
}

#[test]
fn test_pipeline_plan_link() {
    let t = TargetTriple::parse("aarch64-apple-darwin").expect("parse");
    let mut p = CompilePipeline::new(t, NativeTarget::C, true);
    let objs = vec![PathBuf::from("/tmp/a.o"), PathBuf::from("/tmp/b.o")];
    let cmd = p.plan_link(&objs, Path::new("/tmp/lib.dylib"));
    assert_eq!(cmd.tool, "clang");
    assert_eq!(cmd.objects.len(), 2);
}

// ---------------------------------------------------------------------------
// Arch and Os Display
// ---------------------------------------------------------------------------

#[test]
fn test_arch_display() {
    assert_eq!(format!("{}", Arch::X86_64), "x86_64");
    assert_eq!(format!("{}", Arch::Aarch64), "aarch64");
    assert_eq!(format!("{}", Arch::Wasm32), "wasm32");
}

#[test]
fn test_os_display() {
    assert_eq!(format!("{}", Os::Linux), "linux");
    assert_eq!(format!("{}", Os::Darwin), "darwin");
    assert_eq!(format!("{}", Os::Windows), "windows");
    assert_eq!(format!("{}", Os::Unknown), "unknown");
}

// ---------------------------------------------------------------------------
// Error Display
// ---------------------------------------------------------------------------

#[test]
fn test_error_tool_failed_display() {
    let e = NativeCompileError::ToolFailed {
        tool: "cc".to_owned(),
        exit_code: 1,
        stderr: "undefined reference".to_owned(),
    };
    let msg = format!("{e}");
    assert!(msg.contains("cc"));
    assert!(msg.contains("undefined reference"));
}

#[test]
fn test_error_link_failed_display() {
    let e = NativeCompileError::LinkFailed {
        tool: "ld".to_owned(),
        exit_code: 2,
        stderr: "symbol not found".to_owned(),
    };
    assert!(format!("{e}").contains("ld"));
}

#[test]
fn test_error_source_not_found_display() {
    let e = NativeCompileError::SourceNotFound(PathBuf::from("/tmp/missing.c"));
    assert!(format!("{e}").contains("missing.c"));
}

#[test]
fn test_error_jit_display() {
    let e = NativeCompileError::JitError("dlopen failed".to_owned());
    assert!(format!("{e}").contains("dlopen"));
}

#[test]
fn test_error_io_display() {
    let e = NativeCompileError::Io("permission denied".to_owned());
    assert!(format!("{e}").contains("permission denied"));
}
