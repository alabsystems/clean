// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Round-trip integration tests for the Rust emission backend.
//!
//! Tests the full pipeline: LCNF → mono → optimize → RC → IR → boxing → emit_rust.
//! Compares emit_rust output against emit_c for structural equivalence.
//! Verifies behavioral correctness using the native Rust runtime.
//!
//! Part of #2158 — Round-trip integration tests (emit_rust vs emit_c).

use clean_compiler::boxing::explicit_boxing_with_config;
use clean_compiler::emit_c::{emit_c_with_config, CEmitConfig};
use clean_compiler::emit_rust::{emit_rust_with_config, RustEmitConfig};
use clean_compiler::lcnf::{Alt, Arg, Cases, Code, Decl, FunDecl, LetDecl, LetValue, Param};
use clean_compiler::rc;
use clean_compiler::to_ir::to_ir;
use clean_compiler::to_mono::to_mono;
use clean_compiler::{BoxingConfig, OptConfig, RCConfig};
use clean_kernel::{Environment, Expr, FVarId, Name};

fn fvar(n: u64) -> FVarId {
    FVarId::new(n)
}

fn name(s: &str) -> Name {
    Name::from_string(s)
}

fn nat_type() -> Expr {
    Expr::const_str("Nat")
}

// ============================================================================
// Pipeline helpers
// ============================================================================

/// Shared pipeline stages: LCNF → mono → optimize → RC → IR → boxing.
///
/// Returns the boxed IR declarations for consumption by either emit_c or emit_rust.
fn run_pipeline_to_ir(decls: &[Decl]) -> Vec<clean_compiler::ir::IRDecl> {
    let env = Environment::default();

    // Stage 1: Monomorphize
    let mono_decls: Vec<Decl> = decls.iter().map(|d| to_mono(d, &env)).collect();

    // Stage 2: Optimize (default config)
    let opt_config = OptConfig::default();
    let opt_decls: Vec<Decl> = mono_decls
        .iter()
        .map(|d| clean_compiler::optimize(d, &opt_config))
        .collect();

    // Stage 3: RC transform
    let rc_config = RCConfig::default();
    let rc_decls = rc::transform(&opt_decls, &rc_config);

    // Stage 4: Lower to IR
    let ir_decls = to_ir(&rc_decls).expect("RC declarations should lower to IR");

    // Stage 5: Explicit boxing
    explicit_boxing_with_config(&ir_decls, &BoxingConfig::default())
}

/// Full pipeline ending at emit_rust.
fn run_rust_pipeline(decls: &[Decl]) -> String {
    run_rust_pipeline_checked(decls, true)
}

/// Full pipeline ending at emit_rust with configurable IR checking.
///
/// The boxing pass can produce IR where RC operations (inc/dec) apply to
/// USize-typed variables (e.g., from Nat case analysis where Nat is boxed).
/// The IR checker rejects this as "inc requires object type". Disabling
/// the checker allows testing the emitter on these valid-but-checker-rejected
/// programs.
fn run_rust_pipeline_checked(decls: &[Decl], check_ir: bool) -> String {
    let boxed = run_pipeline_to_ir(decls);
    let config = RustEmitConfig {
        check_ir,
        ..Default::default()
    };
    emit_rust_with_config(&boxed, config)
        .expect("emit_rust should succeed for valid pipeline output")
}

/// Full pipeline ending at emit_c.
fn run_c_pipeline(decls: &[Decl]) -> String {
    run_c_pipeline_checked(decls, true)
}

/// Full pipeline ending at emit_c with configurable IR checking.
fn run_c_pipeline_checked(decls: &[Decl], check_ir: bool) -> String {
    let boxed = run_pipeline_to_ir(decls);
    let config = CEmitConfig {
        check_ir,
        ..Default::default()
    };
    emit_c_with_config(&boxed, config).expect("emit_c should succeed for valid pipeline output")
}

// ============================================================================
// Test programs
// ============================================================================

/// Program 1: Simple identity function.
/// def id (x : Nat) : Nat := return x
fn make_identity_decl() -> Decl {
    Decl::new(
        name("id"),
        vec![],
        nat_type(),
        vec![Param::new(fvar(0), name("x"), nat_type())],
        Code::ret(fvar(0)),
        false,
    )
}

/// Program 2: Closure application (exercises apply dispatch).
/// def apply_f (f : Nat → Nat) (x : Nat) : Nat :=
///   let _1 := f x
///   return _1
fn make_closure_apply_decl() -> Decl {
    Decl::new(
        name("apply_f"),
        vec![],
        nat_type(),
        vec![
            Param::new(fvar(0), name("f"), nat_type()),
            Param::new(fvar(1), name("x"), nat_type()),
        ],
        Code::let_bind(
            LetDecl::new(
                fvar(2),
                name("_1"),
                nat_type(),
                LetValue::FVar {
                    fvar: fvar(0),
                    args: vec![Arg::FVar(fvar(1))],
                },
            ),
            Code::ret(fvar(2)),
        ),
        false,
    )
}

/// Program 3: Pattern match (case analysis on constructor tag).
///
/// Uses Nat (object type) as scrutinee instead of Bool (scalar type),
/// because the boxing pass does not support Bool-to-USize scalar casts
/// needed for tag extraction.
///
/// def match_nat (x : Nat) : Nat :=
///   cases x
///     | Nat.zero => let _1 := 0; return _1
///     | Nat.succ n => return n
fn make_case_analysis_decl() -> Decl {
    Decl::new(
        name("match_nat"),
        vec![],
        nat_type(),
        vec![Param::new(fvar(0), name("x"), nat_type())],
        Code::Cases(Cases::new(
            name("Nat"),
            nat_type(),
            fvar(0),
            vec![
                // Nat.zero (tag 0) → return 0
                Alt::ctor(
                    name("Nat.zero"),
                    vec![],
                    Code::let_bind(
                        LetDecl::new(fvar(1), name("_1"), nat_type(), LetValue::nat(0)),
                        Code::ret(fvar(1)),
                    ),
                ),
                // Nat.succ (tag 1) → return argument
                Alt::ctor(
                    name("Nat.succ"),
                    vec![Param::new(fvar(2), name("n"), nat_type())],
                    Code::ret(fvar(2)),
                ),
            ],
        )),
        false,
    )
}

/// Program 4: Constant literal (exercises literal emission).
/// def const42 : Nat :=
///   let _1 := 42
///   return _1
fn make_constant_decl() -> Decl {
    Decl::new(
        name("const42"),
        vec![],
        nat_type(),
        vec![],
        Code::let_bind(
            LetDecl::new(fvar(0), name("_1"), nat_type(), LetValue::nat(42)),
            Code::ret(fvar(0)),
        ),
        false,
    )
}

/// Program 5: Join point (exercises the state-machine loop lowering).
/// def jp_example (x : Nat) (y : Nat) : Nat :=
///   jp loop (a : Nat) : Nat :=
///     return a
///   jmp loop x
fn make_join_point_decl() -> Decl {
    Decl::new(
        name("jp_example"),
        vec![],
        nat_type(),
        vec![
            Param::new(fvar(0), name("x"), nat_type()),
            Param::new(fvar(1), name("y"), nat_type()),
        ],
        Code::join_point(
            FunDecl::new(
                fvar(10),
                name("loop"),
                vec![Param::new(fvar(2), name("a"), nat_type())],
                nat_type(),
                Code::ret(fvar(2)),
            ),
            Code::jmp(fvar(10), vec![Arg::FVar(fvar(0))]),
        ),
        false,
    )
}

/// Program 6: Multi-use arguments (exercises RC inc/dec insertion).
/// def use_twice (f : Nat → Nat) (x : Nat) : Nat :=
///   let _1 := f x
///   let _2 := f x
///   return _2
fn make_rc_decl() -> Decl {
    Decl::new(
        name("use_twice"),
        vec![],
        nat_type(),
        vec![
            Param::new(fvar(0), name("f"), nat_type()),
            Param::new(fvar(1), name("x"), nat_type()),
        ],
        Code::let_bind(
            LetDecl::new(
                fvar(2),
                name("_1"),
                nat_type(),
                LetValue::FVar {
                    fvar: fvar(0),
                    args: vec![Arg::FVar(fvar(1))],
                },
            ),
            Code::let_bind(
                LetDecl::new(
                    fvar(3),
                    name("_2"),
                    nat_type(),
                    LetValue::FVar {
                        fvar: fvar(0),
                        args: vec![Arg::FVar(fvar(1))],
                    },
                ),
                Code::ret(fvar(3)),
            ),
        ),
        false,
    )
}

// ============================================================================
// Test 1: Rust pipeline structural tests (IR → emit_rust → verify structure)
// ============================================================================

// Part of #2158: identity function through Rust pipeline
#[test]
fn test_rust_pipeline_identity_function() {
    let decl = make_identity_decl();
    let rust_code = run_rust_pipeline(&[decl]);

    // Verify header
    assert!(
        rust_code.contains("use clean_runtime::*;"),
        "Rust header should import clean_runtime: {rust_code}"
    );
    // Verify function definition exists with pub unsafe fn
    assert!(
        rust_code.contains("pub unsafe fn l_id("),
        "id function should be emitted as pub unsafe fn: {rust_code}"
    );
    // Verify Rust-specific type (*mut CleanObj, not clean_obj*)
    assert!(
        rust_code.contains("*mut CleanObj"),
        "Rust emitter should use *mut CleanObj type: {rust_code}"
    );
}

// Part of #2158: closure application through Rust pipeline
#[test]
fn test_rust_pipeline_closure_application() {
    let decl = make_closure_apply_decl();
    let rust_code = run_rust_pipeline(&[decl]);

    // Rust closure application uses the slice-based runtime API.
    assert!(
        rust_code.contains("clean_closure_apply(_x0, &[_x1])"),
        "single-arg closure should use clean_closure_apply: {rust_code}"
    );
    // Function should exist
    assert!(
        rust_code.contains("pub unsafe fn l_apply__f("),
        "apply_f function should be emitted: {rust_code}"
    );
}

// Part of #2158: pattern match through Rust pipeline
//
// Uses check_ir=false because the boxing pass produces IR where RC operations
// (inc/dec) apply to USize-typed variables from Nat case analysis. The IR
// checker rejects this as "inc requires object type" — a known limitation.
//
// Note: Nat case analysis is transformed by the mono/optimize passes (Nat.decEq
// optimization), so we check for case analysis structure rather than exact tags.
#[test]
fn test_rust_pipeline_pattern_match() {
    let decl = make_case_analysis_decl();
    let rust_code = run_rust_pipeline_checked(&[decl], false);

    // Rust case analysis uses `match clean_obj_tag(...)` (not C's switch)
    assert!(
        rust_code.contains("match clean_obj_tag("),
        "case analysis should use match clean_obj_tag: {rust_code}"
    );
    // Should have at least one numbered branch
    assert!(
        rust_code.contains("0 =>") || rust_code.contains("0 => {"),
        "at least one numbered branch should be emitted: {rust_code}"
    );
    // Should have a default/unreachable arm
    assert!(
        rust_code.contains("_ =>"),
        "default arm should be emitted: {rust_code}"
    );
    // Function should be emitted
    assert!(
        rust_code.contains("l_match__nat"),
        "match_nat function should be emitted: {rust_code}"
    );
}

// Part of #2158: constant literal through Rust pipeline
#[test]
fn test_rust_pipeline_constant_literal() {
    let decl = make_constant_decl();
    let rust_code = run_rust_pipeline(&[decl]);

    assert!(
        rust_code.contains("pub unsafe fn l_const42("),
        "const42 function should be emitted: {rust_code}"
    );
    // Literal 42 should appear somewhere (as clean_box(42) or similar)
    assert!(
        rust_code.contains("42"),
        "literal 42 should appear in output: {rust_code}"
    );
}

// Part of #2158: join point through Rust pipeline (state-machine loop)
#[test]
fn test_rust_pipeline_join_point() {
    let decl = make_join_point_decl();
    let rust_code = run_rust_pipeline(&[decl]);

    assert!(
        rust_code.contains("pub unsafe fn l_jp__example("),
        "jp_example function should be emitted: {rust_code}"
    );
    // Join points lower to state-machine loops in the Rust backend
    assert!(
        rust_code.contains("loop {") || rust_code.contains("_state"),
        "join point should lower to loop/state machine: {rust_code}"
    );
}

// Part of #2158: RC operations in Rust pipeline
#[test]
fn test_rust_pipeline_rc_operations() {
    let decl = make_rc_decl();
    let rust_code = run_rust_pipeline(&[decl]);

    // With RC, multi-use variables should have clean_inc/clean_dec calls
    assert!(
        rust_code.contains("clean_inc(") || rust_code.contains("clean_dec("),
        "RC pass should insert inc/dec for multi-use args in Rust output: {rust_code}"
    );
}

// Part of #2158: multiple declarations through Rust pipeline
// Uses check_ir=false because case analysis decl triggers the USize inc issue.
#[test]
fn test_rust_pipeline_multiple_decls() {
    let id_decl = make_identity_decl();
    let const_decl = make_constant_decl();
    let case_decl = make_case_analysis_decl();

    let rust_code = run_rust_pipeline_checked(&[id_decl, const_decl, case_decl], false);

    assert!(
        rust_code.contains("l_id("),
        "id should be in multi-decl output: {rust_code}"
    );
    assert!(
        rust_code.contains("l_const42("),
        "const42 should be in multi-decl output: {rust_code}"
    );
    assert!(
        rust_code.contains("l_match__nat("),
        "match_nat should be in multi-decl output: {rust_code}"
    );
}

// ============================================================================
// Test 2: Cross-backend comparison (emit_rust vs emit_c structural equivalence)
// ============================================================================

/// Verify that emit_rust and emit_c produce structurally equivalent output
/// for the same IR input. Both should contain matching operations even though
/// syntax differs (Rust: `match` vs C: `switch`, `*mut CleanObj` vs `clean_obj*`).
// Part of #2158: cross-backend comparison — identity function
#[test]
fn test_cross_backend_identity() {
    let decl = make_identity_decl();
    let rust_code = run_rust_pipeline(std::slice::from_ref(&decl));
    let c_code = run_c_pipeline(&[decl]);

    // Both should define the id function
    assert!(rust_code.contains("l_id("), "Rust: id missing: {rust_code}");
    assert!(c_code.contains("l_id("), "C: id missing: {c_code}");

    // Both should have object type parameters
    assert!(
        rust_code.contains("*mut CleanObj"),
        "Rust should use *mut CleanObj: {rust_code}"
    );
    assert!(
        c_code.contains("clean_obj*"),
        "C should use clean_obj*: {c_code}"
    );
}

// Part of #2158: cross-backend comparison — closure application
#[test]
fn test_cross_backend_closure_apply() {
    let decl = make_closure_apply_decl();
    let rust_code = run_rust_pipeline(std::slice::from_ref(&decl));
    let c_code = run_c_pipeline(&[decl]);

    // Rust uses the slice-based runtime API; C uses specialized apply_N.
    assert!(
        rust_code.contains("clean_closure_apply(_x0, &[_x1])"),
        "Rust should use clean_closure_apply: {rust_code}"
    );
    assert!(
        c_code.contains("clean_apply_1("),
        "C should use clean_apply_1: {c_code}"
    );
}

// Part of #2158: cross-backend comparison — pattern match
// Uses check_ir=false (see test_rust_pipeline_pattern_match comment).
#[test]
fn test_cross_backend_pattern_match() {
    let decl = make_case_analysis_decl();
    let rust_code = run_rust_pipeline_checked(std::slice::from_ref(&decl), false);
    let c_code = run_c_pipeline_checked(&[decl], false);

    // Rust uses `match clean_obj_tag(...)`. The C backend's ToMono lowering of
    // this `Nat` match materializes the discriminant as an *unboxed* `size_t`
    // (via `Nat.decEq` + `clean_unbox`) before the switch, so the C `switch`
    // dispatches on that scalar value directly. Wrapping it in `clean_obj_tag`
    // (which takes a `clean_obj*`) would be a C type error, so the switch
    // condition must NOT call `clean_obj_tag` here.
    assert!(
        rust_code.contains("match clean_obj_tag("),
        "Rust should use match on clean_obj_tag: {rust_code}"
    );
    assert!(
        c_code.contains("switch ("),
        "C should use a switch: {c_code}"
    );
    assert!(
        !c_code.contains("switch (clean_obj_tag("),
        "C must switch on the already-unboxed scalar, not clean_obj_tag of it: {c_code}"
    );
}

// Part of #2158: cross-backend comparison — RC operations
#[test]
fn test_cross_backend_rc_operations() {
    let decl = make_rc_decl();
    let rust_code = run_rust_pipeline(std::slice::from_ref(&decl));
    let c_code = run_c_pipeline(&[decl]);

    // Both should contain inc or dec operations
    let rust_has_rc = rust_code.contains("clean_inc(") || rust_code.contains("clean_dec(");
    let c_has_rc = c_code.contains("clean_inc(") || c_code.contains("clean_dec(");

    assert!(rust_has_rc, "Rust should have RC operations: {rust_code}");
    assert!(c_has_rc, "C should have RC operations: {c_code}");
}

// ============================================================================
// Test 3: Behavioral verification using native runtime
// ============================================================================

/// Verify that the native Rust runtime produces correct results for the same
/// operations that the emitter generates. This tests behavioral equivalence
/// without requiring standalone rustc compilation of the emitted code.
///
/// The emitter generates calls to `clean_box`, `clean_alloc_ctor`, etc.
/// We call the underlying native runtime functions directly to verify they
/// produce the correct results.
// Part of #2158: behavioral verification — tagged pointer roundtrip
#[test]
fn test_behavioral_tagged_pointer_roundtrip() {
    // Emitter generates: clean_box(42 as usize)
    // Native equivalent: box_val(42)
    let tagged = clean_runtime::native::box_val(42);
    assert!(clean_runtime::native::is_scalar(tagged));
    assert_eq!(clean_runtime::native::unbox_val(tagged), 42);
}

// Part of #2158: behavioral verification — constructor allocation
#[test]
fn test_behavioral_ctor_alloc_and_field_access() {
    unsafe {
        // Emitter generates: clean_alloc_ctor(tag, num_objs, scalar_sz, &[fields])
        // Native equivalent: alloc_ctor(tag, &[fields])
        let field_a = clean_runtime::native::box_val(10);
        let field_b = clean_runtime::native::box_val(20);
        let obj = clean_runtime::native::alloc_ctor(5, &[field_a, field_b]);

        // Emitter generates: clean_obj_tag(obj)
        assert_eq!(clean_runtime::native::obj_tag(obj), 5);

        // Emitter generates: clean_ctor_get(obj, 0), clean_ctor_get(obj, 1)
        assert_eq!(clean_runtime::native::ctor_get(obj, 0), field_a);
        assert_eq!(clean_runtime::native::ctor_get(obj, 1), field_b);

        clean_runtime::native::dec(obj);
    }
}

// Part of #2158: behavioral verification — RC operations
#[test]
fn test_behavioral_rc_inc_dec() {
    unsafe {
        // Emitter generates: clean_inc(obj); clean_dec(obj);
        let obj = clean_runtime::native::alloc_ctor(0, &[]);
        assert!(clean_runtime::native::is_unique(obj));

        clean_runtime::native::inc(obj);
        assert!(!clean_runtime::native::is_unique(obj));

        clean_runtime::native::dec(obj);
        assert!(clean_runtime::native::is_unique(obj));

        clean_runtime::native::dec(obj);
    }
}

// Part of #2158: behavioral verification — boxing/unboxing
#[test]
fn test_behavioral_box_unbox_uint64() {
    unsafe {
        // Emitter generates: clean_box_uint64(val)
        let boxed = clean_runtime::native::box_uint64(0x0123_4567_89AB_CDEF);
        // Emitter generates: clean_unbox_uint64(boxed)
        let unboxed = clean_runtime::native::unbox_uint64(boxed);
        assert_eq!(unboxed, 0x0123_4567_89AB_CDEF);
        clean_runtime::native::dec(boxed);
    }
}

// Part of #2158: behavioral verification — float boxing/unboxing
#[test]
fn test_behavioral_box_unbox_float() {
    unsafe {
        // Emitter generates: clean_box_float(val)
        let boxed = clean_runtime::native::box_float(std::f64::consts::PI);
        // Emitter generates: clean_unbox_float(boxed)
        let unboxed = clean_runtime::native::unbox_float(boxed);
        assert!((unboxed - std::f64::consts::PI).abs() < f64::EPSILON);
        clean_runtime::native::dec(boxed);
    }
}

// Part of #2158: behavioral verification — string creation
#[test]
fn test_behavioral_mk_string() {
    unsafe {
        // Emitter generates: clean_mk_string("hello")
        let s = clean_runtime::native::mk_string_from_str("hello");
        assert!(!s.is_null());
        let len = clean_runtime::native::string_len(s);
        assert_eq!(len, 5);
        clean_runtime::native::dec(s);
    }
}

// Part of #2158: behavioral verification — reset/reuse cycle
#[test]
fn test_behavioral_reset_reuse() {
    unsafe {
        // Emitter generates:
        //   let slot = clean_reset(obj);
        //   let reused = clean_reuse(slot, tag, scalar_sz, &[new_fields]);
        let child = clean_runtime::native::box_val(42);
        let obj = clean_runtime::native::alloc_ctor(0, &[child]);
        let slot = clean_runtime::native::reset(obj);
        assert!(!slot.is_null());

        let new_child = clean_runtime::native::box_val(99);
        let reused = clean_runtime::native::reuse(slot, 3, &[new_child], 0);
        assert_eq!(clean_runtime::native::obj_tag(reused), 3);
        assert_eq!(clean_runtime::native::ctor_get(reused, 0), new_child);
        clean_runtime::native::dec(reused);
    }
}

// ============================================================================
// Test 4: Rust compilation test
// ============================================================================

/// Test that emitted Rust code compiles with rustc.
///
/// Creates a temporary Cargo project that depends on clean-runtime via path,
/// writes the emitted code with a compatibility prelude, and runs `cargo check`.
// Part of #2158: emitted Rust compiles with rustc
#[test]
fn test_rust_pipeline_compilation() {
    let decl = make_identity_decl();
    let rust_code = run_rust_pipeline(&[decl]);

    let tmp_dir = setup_temp_crate();
    let full_rust = build_compilable_source(&rust_code);
    std::fs::write(tmp_dir.join("src").join("lib.rs"), &full_rust).expect("write lib.rs");

    let output = std::process::Command::new("cargo")
        .arg("check")
        .arg("--manifest-path")
        .arg(tmp_dir.join("Cargo.toml"))
        .env("CARGO_TARGET_DIR", tmp_dir.join("target"))
        .output()
        .expect("run cargo check");

    let _ = std::fs::remove_dir_all(&tmp_dir);

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        panic!("Rust compilation failed!\n\nEmitted:\n{full_rust}\n\nstderr:\n{stderr}");
    }
}

/// Create a temporary Cargo project directory with clean-runtime dependency.
///
/// Uses PID to avoid races when `cargo test` runs tests in parallel threads.
fn setup_temp_crate() -> std::path::PathBuf {
    let tmp_dir = std::env::temp_dir().join(format!("clean_rust_e2e_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&tmp_dir);
    std::fs::create_dir_all(tmp_dir.join("src")).expect("create temp src dir");

    let manifest_dir = env!("CARGO_MANIFEST_DIR");
    let runtime_path = std::path::Path::new(manifest_dir)
        .parent()
        .expect("parent dir")
        .join("clean-runtime");

    let cargo_toml = format!(
        "[package]\nname = \"clean-rust-e2e-test\"\nversion = \"0.1.0\"\n\
         edition = \"2021\"\n\n[dependencies]\nclean-runtime = {{ path = \"{}\" }}\n",
        runtime_path.display()
    );
    std::fs::write(tmp_dir.join("Cargo.toml"), &cargo_toml).expect("write Cargo.toml");
    tmp_dir
}

/// Build compilable Rust source from emitted code by prepending a compatibility
/// prelude that maps clean_* names to the native runtime functions.
fn build_compilable_source(emitted_code: &str) -> String {
    let stripped = strip_emit_header(emitted_code);
    format!("{COMPAT_PRELUDE}\n\n{stripped}")
}

#[test]
fn test_compat_prelude_preserves_scalar_layout_contract() {
    assert!(COMPAT_PRELUDE.contains(
        "clean_runtime::clean_alloc_ctor(tag, _num_objs as u8, _scalar_sz as u8, fields)"
    ));
    assert!(
        COMPAT_PRELUDE.contains("clean_runtime::clean_reuse(slot, tag, _scalar_sz as u8, fields)")
    );
    assert!(!COMPAT_PRELUDE.contains("clean_runtime::native::alloc_ctor(tag, fields)"));
    assert!(!COMPAT_PRELUDE.contains("clean_runtime::native::reuse(slot, tag, fields, 0)"));
}

/// Strip the standard header emitted by emit_rust (Generated by... / use clean_runtime::*;)
/// since the compilation test provides its own compatibility prelude.
fn strip_emit_header(code: &str) -> String {
    let mut lines: Vec<&str> = Vec::new();
    let mut past_header = false;
    for line in code.lines() {
        if !past_header {
            if line.starts_with("//")
                || line.starts_with("#![")
                || line.starts_with("use clean_runtime")
                || line.is_empty()
            {
                continue;
            }
            past_header = true;
        }
        lines.push(line);
    }
    lines.join("\n")
}

/// Compatibility prelude: maps clean_* emitter names to clean_runtime::native::*.
///
/// The emitter generates `clean_box`, `clean_inc`, etc. matching Lean 4's C API
/// naming convention. The native Rust runtime uses unprefixed names (`box_val`,
/// `inc`, etc.). This prelude bridges the gap for compilation testing.
///
/// Coverage: all functions that emit_rust.rs and body.rs can generate, including
/// scalar getters/setters (Proj/SSet) and higher-arity apply (Ap).
const COMPAT_PRELUDE: &str = r#"#![allow(unused_variables, unused_assignments, unreachable_code, unused_imports, dead_code)]
#![allow(non_snake_case)]

use clean_runtime::native::LeanObj;

pub type CleanObj = LeanObj;

// -- Core object ops --
#[inline] pub unsafe fn clean_box(n: usize) -> *mut CleanObj { clean_runtime::native::box_val(n) }
#[inline] pub unsafe fn clean_unbox(o: *mut CleanObj) -> usize { clean_runtime::native::unbox_val(o as *const CleanObj) }
#[inline] pub unsafe fn clean_inc(o: *mut CleanObj) { clean_runtime::native::inc(o) }
#[inline] pub unsafe fn clean_inc_n(o: *mut CleanObj, n: u32) { clean_runtime::native::inc_n(o, n) }
#[inline] pub unsafe fn clean_dec(o: *mut CleanObj) { clean_runtime::native::dec(o) }
#[inline] pub unsafe fn clean_obj_tag(o: *const CleanObj) -> u8 { clean_runtime::native::obj_tag(o) }

// -- Constructor field access (object fields) --
#[inline] pub unsafe fn clean_ctor_get(o: *const CleanObj, idx: usize) -> *mut CleanObj { clean_runtime::native::ctor_get(o, idx) }
#[inline] pub unsafe fn clean_ctor_set(o: *mut CleanObj, idx: usize, v: *mut CleanObj) { clean_runtime::native::ctor_set(o, idx, v) }
#[inline] pub unsafe fn clean_alloc_ctor(tag: u8, _num_objs: u32, _scalar_sz: u32, fields: &[*mut CleanObj]) -> *mut CleanObj { debug_assert!(_num_objs <= u8::MAX as u32); debug_assert!(_scalar_sz <= u8::MAX as u32); clean_runtime::clean_alloc_ctor(tag, _num_objs as u8, _scalar_sz as u8, fields) }

// -- Scalar field getters (IRExpr::Proj with scalar types) --
#[inline] pub unsafe fn clean_ctor_get_uint8(o: *mut CleanObj, offset: usize) -> u8 { clean_runtime::native::ctor_get_uint8(o, offset) }
#[inline] pub unsafe fn clean_ctor_get_uint16(o: *mut CleanObj, offset: usize) -> u16 { clean_runtime::native::ctor_get_uint16(o, offset) }
#[inline] pub unsafe fn clean_ctor_get_uint32(o: *mut CleanObj, offset: usize) -> u32 { clean_runtime::native::ctor_get_uint32(o, offset) }
#[inline] pub unsafe fn clean_ctor_get_uint64(o: *mut CleanObj, offset: usize) -> u64 { clean_runtime::native::ctor_get_uint64(o, offset) }
#[inline] pub unsafe fn clean_ctor_get_usize(o: *mut CleanObj, offset: usize) -> usize { clean_runtime::native::ctor_get_usize(o, offset) }
#[inline] pub unsafe fn clean_ctor_get_float(o: *mut CleanObj, offset: usize) -> f64 { clean_runtime::native::ctor_get_float(o, offset) }
#[inline] pub unsafe fn clean_ctor_get_float32(o: *mut CleanObj, offset: usize) -> f32 { clean_runtime::native::ctor_get_float32(o, offset) }

// -- Scalar field setters (LoweredBody::SSet via scalar_setter_name) --
#[inline] pub unsafe fn clean_ctor_set_uint8(o: *mut CleanObj, offset: usize, v: u8) { clean_runtime::native::ctor_set_uint8(o, offset, v) }
#[inline] pub unsafe fn clean_ctor_set_uint16(o: *mut CleanObj, offset: usize, v: u16) { clean_runtime::native::ctor_set_uint16(o, offset, v) }
#[inline] pub unsafe fn clean_ctor_set_uint32(o: *mut CleanObj, offset: usize, v: u32) { clean_runtime::native::ctor_set_uint32(o, offset, v) }
#[inline] pub unsafe fn clean_ctor_set_uint64(o: *mut CleanObj, offset: usize, v: u64) { clean_runtime::native::ctor_set_uint64(o, offset, v) }
#[inline] pub unsafe fn clean_ctor_set_usize(o: *mut CleanObj, offset: usize, v: usize) { clean_runtime::native::ctor_set_usize(o, offset, v) }
#[inline] pub unsafe fn clean_ctor_set_float(o: *mut CleanObj, offset: usize, v: f64) { clean_runtime::native::ctor_set_float(o, offset, v) }
#[inline] pub unsafe fn clean_ctor_set_float32(o: *mut CleanObj, offset: usize, v: f32) { clean_runtime::native::ctor_set_float32(o, offset, v) }

// -- Boxing/unboxing (IRExpr::Box/Unbox) --
#[inline] pub unsafe fn clean_box_uint64(n: u64) -> *mut CleanObj { clean_runtime::native::box_uint64(n) }
#[inline] pub unsafe fn clean_box_uint32(n: u32) -> *mut CleanObj { clean_runtime::native::box_uint32(n) }
#[inline] pub unsafe fn clean_box_float(f: f64) -> *mut CleanObj { clean_runtime::native::box_float(f) }
#[inline] pub unsafe fn clean_unbox_uint64(o: *mut CleanObj) -> u64 { clean_runtime::native::unbox_uint64(o) }
#[inline] pub unsafe fn clean_unbox_uint32(o: *mut CleanObj) -> u32 { clean_runtime::native::unbox_uint32(o) }
#[inline] pub unsafe fn clean_unbox_float(o: *mut CleanObj) -> f64 { clean_runtime::native::unbox_float(o) }

// -- Closure application (IRExpr::Ap via emit_ap) --
#[inline] pub unsafe fn clean_apply_1(f: *mut CleanObj, a: *mut CleanObj) -> *mut CleanObj { clean_runtime::native::apply_1(f, a) }
#[inline] pub unsafe fn clean_apply_2(f: *mut CleanObj, a: *mut CleanObj, b: *mut CleanObj) -> *mut CleanObj { clean_runtime::native::apply_2(f, a, b) }
#[inline] pub unsafe fn clean_apply_3(f: *mut CleanObj, a: *mut CleanObj, b: *mut CleanObj, c: *mut CleanObj) -> *mut CleanObj { clean_runtime::native::apply_3(f, a, b, c) }
#[inline] pub unsafe fn clean_apply_4(f: *mut CleanObj, a: *mut CleanObj, b: *mut CleanObj, c: *mut CleanObj, d: *mut CleanObj) -> *mut CleanObj { clean_runtime::native::apply_4(f, a, b, c, d) }
#[inline] pub unsafe fn clean_apply_n(f: *mut CleanObj, args: &[*mut CleanObj]) -> *mut CleanObj { clean_runtime::native::apply_n(f, args) }

// -- String, reset/reuse, closure alloc, panic --
#[inline] pub unsafe fn clean_mk_string(s: &str) -> *mut CleanObj { clean_runtime::native::mk_string_from_str(s) }
#[inline] pub unsafe fn clean_reset(o: *mut CleanObj) -> *mut CleanObj { clean_runtime::native::reset(o) }
#[inline] pub unsafe fn clean_reuse(slot: *mut CleanObj, tag: u8, _scalar_sz: u32, fields: &[*mut CleanObj]) -> *mut CleanObj { debug_assert!(_scalar_sz <= u8::MAX as u32); clean_runtime::clean_reuse(slot, tag, _scalar_sz as u8, fields) }
#[inline] pub unsafe fn clean_alloc_closure(fun: *const (), arity: u16, args: &[*mut CleanObj]) -> *mut CleanObj { clean_runtime::native::alloc_closure(fun as *mut (), arity, args) }
#[inline] pub fn clean_panic(msg: &str) -> ! { panic!("{}", msg) }
"#;
