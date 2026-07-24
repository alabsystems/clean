// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the trait-based optimization pass infrastructure.
//!
//! Part of #3084 - Compiler IR optimization passes.

use super::*;
use crate::lcnf::{Arg, Code, Decl, FunDecl, LetDecl, LetValue, Param};
use clean_kernel::{Expr, FVarId, Name};

fn fvar(n: u64) -> FVarId {
    FVarId::new(n)
}

fn name(s: &str) -> Name {
    Name::from_string(s)
}

fn nat_type() -> Expr {
    Expr::const_str("Nat")
}

// ---------------------------------------------------------------------------
// Dead code elimination tests
// ---------------------------------------------------------------------------

#[test]
fn test_dce_removes_unused_let() {
    // let _1 := 42
    // let _2 := 10  -- unused
    // return _1
    let code = Code::let_bind(
        LetDecl::new(fvar(1), name("_1"), nat_type(), LetValue::nat(42)),
        Code::let_bind(
            LetDecl::new(fvar(2), name("_2"), nat_type(), LetValue::nat(10)),
            Code::ret(fvar(1)),
        ),
    );

    let pass = DeadCodeElimination;
    let result = pass.run_on_code(&code);

    let s = result.to_string();
    assert!(s.contains("_x1 := 42"), "Should keep used binding: {s}");
    assert!(!s.contains("_x2"), "Should remove unused binding: {s}");
    assert!(s.contains("return _x1"), "Should preserve return: {s}");
}

#[test]
fn test_dce_keeps_used_let() {
    // let _1 := 42
    // let _2 := Nat.add _1 _1
    // return _2
    let code = Code::let_bind(
        LetDecl::new(fvar(1), name("_1"), nat_type(), LetValue::nat(42)),
        Code::let_bind(
            LetDecl::new(
                fvar(2),
                name("_2"),
                nat_type(),
                LetValue::Const {
                    name: name("Nat.add"),
                    levels: vec![],
                    args: vec![Arg::FVar(fvar(1)), Arg::FVar(fvar(1))],
                },
            ),
            Code::ret(fvar(2)),
        ),
    );

    let pass = DeadCodeElimination;
    let result = pass.run_on_code(&code);

    let s = result.to_string();
    assert!(s.contains("_x1 := 42"), "Should keep _1: {s}");
    assert!(s.contains("_x2 := Nat.add"), "Should keep _2: {s}");
    assert!(s.contains("return _x2"), "Should return _2: {s}");
}

// ---------------------------------------------------------------------------
// Constant folding tests
// ---------------------------------------------------------------------------

#[test]
fn test_fold_nat_add() {
    // let _1 := 2
    // let _2 := 3
    // let _3 := Nat.add _1 _2
    // return _3
    let code = Code::let_bind(
        LetDecl::new(fvar(1), name("_1"), nat_type(), LetValue::nat(2)),
        Code::let_bind(
            LetDecl::new(fvar(2), name("_2"), nat_type(), LetValue::nat(3)),
            Code::let_bind(
                LetDecl::new(
                    fvar(3),
                    name("_3"),
                    nat_type(),
                    LetValue::Const {
                        name: name("Nat.add"),
                        levels: vec![],
                        args: vec![Arg::FVar(fvar(1)), Arg::FVar(fvar(2))],
                    },
                ),
                Code::ret(fvar(3)),
            ),
        ),
    );

    let pass = ConstantFolding;
    let result = pass.run_on_code(&code);

    // After folding, _3 should be the literal 5 (not Nat.add _1 _2)
    let s = result.to_string();
    assert!(s.contains("_x3 := 5"), "Nat.add 2 3 should fold to 5: {s}");
}

#[test]
fn test_fold_bool_comparison() {
    // let _1 := 2
    // let _2 := 3
    // let _3 := Nat.ble _1 _2
    // return _3
    let code = Code::let_bind(
        LetDecl::new(fvar(1), name("_1"), nat_type(), LetValue::nat(2)),
        Code::let_bind(
            LetDecl::new(fvar(2), name("_2"), nat_type(), LetValue::nat(3)),
            Code::let_bind(
                LetDecl::new(
                    fvar(3),
                    name("_3"),
                    Expr::const_str("Bool"),
                    LetValue::Const {
                        name: name("Nat.ble"),
                        levels: vec![],
                        args: vec![Arg::FVar(fvar(1)), Arg::FVar(fvar(2))],
                    },
                ),
                Code::ret(fvar(3)),
            ),
        ),
    );

    let pass = ConstantFolding;
    let result = pass.run_on_code(&code);

    // Nat.ble 2 3 = true -> Bool.true constructor
    let s = result.to_string();
    assert!(
        s.contains("Bool.true"),
        "Nat.ble 2 3 should fold to Bool.true: {s}"
    );
}

#[test]
fn test_fold_string_append() {
    // let _1 := "hello"
    // let _2 := " world"
    // let _3 := String.append _1 _2
    // return _3
    let code = Code::let_bind(
        LetDecl::new(
            fvar(1),
            name("_1"),
            Expr::const_str("String"),
            LetValue::Lit(clean_kernel::Literal::String("hello".into())),
        ),
        Code::let_bind(
            LetDecl::new(
                fvar(2),
                name("_2"),
                Expr::const_str("String"),
                LetValue::Lit(clean_kernel::Literal::String(" world".into())),
            ),
            Code::let_bind(
                LetDecl::new(
                    fvar(3),
                    name("_3"),
                    Expr::const_str("String"),
                    LetValue::Const {
                        name: name("String.append"),
                        levels: vec![],
                        args: vec![Arg::FVar(fvar(1)), Arg::FVar(fvar(2))],
                    },
                ),
                Code::ret(fvar(3)),
            ),
        ),
    );

    let pass = ConstantFolding;
    let result = pass.run_on_code(&code);

    let s = result.to_string();
    assert!(
        s.contains("hello world"),
        "String.append should fold to \"hello world\": {s}"
    );
}

#[test]
fn test_fold_nested_constants() {
    // let _1 := 10
    // let _2 := 20
    // let _3 := Nat.add _1 _2     -- folds to 30
    // let _4 := 5
    // let _5 := Nat.add _3 _4     -- folds to 35 (since _3 is now 30)
    // return _5
    let code = Code::let_bind(
        LetDecl::new(fvar(1), name("_1"), nat_type(), LetValue::nat(10)),
        Code::let_bind(
            LetDecl::new(fvar(2), name("_2"), nat_type(), LetValue::nat(20)),
            Code::let_bind(
                LetDecl::new(
                    fvar(3),
                    name("_3"),
                    nat_type(),
                    LetValue::Const {
                        name: name("Nat.add"),
                        levels: vec![],
                        args: vec![Arg::FVar(fvar(1)), Arg::FVar(fvar(2))],
                    },
                ),
                Code::let_bind(
                    LetDecl::new(fvar(4), name("_4"), nat_type(), LetValue::nat(5)),
                    Code::let_bind(
                        LetDecl::new(
                            fvar(5),
                            name("_5"),
                            nat_type(),
                            LetValue::Const {
                                name: name("Nat.add"),
                                levels: vec![],
                                args: vec![Arg::FVar(fvar(3)), Arg::FVar(fvar(4))],
                            },
                        ),
                        Code::ret(fvar(5)),
                    ),
                ),
            ),
        ),
    );

    let pass = ConstantFolding;
    let result = pass.run_on_code(&code);

    let s = result.to_string();
    // _3 should fold to 30, _5 should fold to 35
    assert!(s.contains("_x3 := 30"), "First add should fold to 30: {s}");
    assert!(s.contains("_x5 := 35"), "Nested add should fold to 35: {s}");
}

// ---------------------------------------------------------------------------
// Inline tests
// ---------------------------------------------------------------------------

#[test]
fn test_inline_small_function() {
    // fun f () : Nat :=
    //   let _10 := 42
    //   return _10
    // let _2 := f()
    // return _2
    let fun_decl = FunDecl::new(
        fvar(1),
        name("f"),
        vec![],
        nat_type(),
        Code::let_bind(
            LetDecl::new(fvar(10), name("_inner"), nat_type(), LetValue::nat(42)),
            Code::ret(fvar(10)),
        ),
    );

    let code = Code::fun(
        fun_decl,
        Code::let_bind(
            LetDecl::new(
                fvar(2),
                name("_result"),
                nat_type(),
                LetValue::FVar {
                    fvar: fvar(1),
                    args: vec![],
                },
            ),
            Code::ret(fvar(2)),
        ),
    );

    let pass = InlineSmall::new(10);
    let result = pass.run_on_code(&code);

    // The function body (size 2: 1 let + 1 return) is below threshold 10,
    // so it should be inlined.
    let s = result.to_string();
    // After inlining, the FVar call to f should be replaced by the body.
    // The fun declaration may still be present (DCE would remove it), but
    // the call site should no longer reference f.
    assert!(
        !s.contains("_result := _x1"),
        "Call to f should be inlined: {s}"
    );
}

#[test]
fn test_inline_respects_threshold() {
    // A function with body size > threshold should NOT be inlined.
    // Build a function with many let-bindings to exceed threshold 1.
    let fun_body = Code::let_bind(
        LetDecl::new(fvar(10), name("a"), nat_type(), LetValue::nat(1)),
        Code::let_bind(
            LetDecl::new(fvar(11), name("b"), nat_type(), LetValue::nat(2)),
            Code::let_bind(
                LetDecl::new(fvar(12), name("c"), nat_type(), LetValue::nat(3)),
                Code::ret(fvar(12)),
            ),
        ),
    );
    // Body size: 3 lets + 1 return = 4

    let fun_decl = FunDecl::new(fvar(1), name("big_fn"), vec![], nat_type(), fun_body);

    let code = Code::fun(
        fun_decl,
        Code::let_bind(
            LetDecl::new(
                fvar(2),
                name("_result"),
                nat_type(),
                LetValue::FVar {
                    fvar: fvar(1),
                    args: vec![],
                },
            ),
            Code::ret(fvar(2)),
        ),
    );

    // Threshold = 1, function body size = 4 -- should NOT inline
    let pass = InlineSmall::new(1);
    let result = pass.run_on_code(&code);

    let s = result.to_string();
    // Function should still be called (not inlined)
    assert!(
        s.contains("fun _x1"),
        "Large function should NOT be inlined with threshold 1: {s}"
    );
}

// ---------------------------------------------------------------------------
// Pipeline composition tests
// ---------------------------------------------------------------------------

#[test]
fn test_pipeline_composes_passes() {
    // let _1 := 2
    // let _2 := 3
    // let _3 := Nat.add _1 _2   -- constant fold -> 5
    // let _4 := 99              -- unused, DCE removes
    // return _3
    let code = Code::let_bind(
        LetDecl::new(fvar(1), name("_1"), nat_type(), LetValue::nat(2)),
        Code::let_bind(
            LetDecl::new(fvar(2), name("_2"), nat_type(), LetValue::nat(3)),
            Code::let_bind(
                LetDecl::new(
                    fvar(3),
                    name("_3"),
                    nat_type(),
                    LetValue::Const {
                        name: name("Nat.add"),
                        levels: vec![],
                        args: vec![Arg::FVar(fvar(1)), Arg::FVar(fvar(2))],
                    },
                ),
                Code::let_bind(
                    LetDecl::new(fvar(4), name("_4"), nat_type(), LetValue::nat(99)),
                    Code::ret(fvar(3)),
                ),
            ),
        ),
    );

    let pipeline = OptimizationPipeline::builder()
        .max_iterations(3)
        .pass(ConstantFolding)
        .pass(DeadCodeElimination)
        .build();

    let result = pipeline.run_on_code(&code);
    let s = result.to_string();

    // Constant folding should have folded Nat.add 2 3 -> 5
    assert!(s.contains("_x3 := 5"), "Should fold constant: {s}");
    // DCE should remove _4 (unused)
    assert!(!s.contains("_x4"), "Should eliminate dead code for _4: {s}");
    // After DCE, _1 and _2 become unused (only _3 uses them, but _3 is now a literal).
    // A second iteration of DCE should remove them.
    assert!(
        !s.contains("_x1 := 2") || !s.contains("_x2 := 3"),
        "Fixpoint should eventually remove newly dead bindings"
    );
}

#[test]
fn test_pipeline_idempotent() {
    // Running the pipeline twice should give the same result as running once.
    let code = Code::let_bind(
        LetDecl::new(fvar(1), name("_1"), nat_type(), LetValue::nat(42)),
        Code::let_bind(
            LetDecl::new(fvar(2), name("_2"), nat_type(), LetValue::nat(99)),
            Code::ret(fvar(1)),
        ),
    );

    let pipeline = OptimizationPipeline::default();
    let once = pipeline.run_on_code(&code);
    let twice = pipeline.run_on_code(&once);

    assert_eq!(
        once, twice,
        "Pipeline should be idempotent: running twice gives same result"
    );
}

#[test]
fn test_pipeline_run_on_decl() {
    let decl = Decl::new(
        name("test_fn"),
        vec![],
        nat_type(),
        vec![],
        Code::let_bind(
            LetDecl::new(fvar(1), name("_1"), nat_type(), LetValue::nat(100)),
            Code::let_bind(
                LetDecl::new(fvar(2), name("_unused"), nat_type(), LetValue::nat(200)),
                Code::ret(fvar(1)),
            ),
        ),
        false,
    );

    let pipeline = OptimizationPipeline::default();
    let result = pipeline.run(&decl);

    assert_eq!(result.name, name("test_fn"));
    match &result.body {
        DeclValue::Code(code) => {
            let s = code.to_string();
            assert!(
                !s.contains("_unused") && !s.contains("_x2"),
                "DCE should remove unused binding from declaration: {s}"
            );
        }
        DeclValue::Extern(_) => panic!("Expected code body"),
    }
}

#[test]
fn test_pipeline_builder_custom() {
    // Build a pipeline with only DCE
    let pipeline = OptimizationPipeline::builder()
        .max_iterations(1)
        .pass(DeadCodeElimination)
        .build();

    assert_eq!(pipeline.pass_count(), 1);
    assert_eq!(pipeline.finalization_count(), 0);
    assert_eq!(pipeline.pass_names(), vec!["dce"]);
}

#[test]
fn test_pipeline_finalization_runs_once() {
    // Build a pipeline with finalization
    let pipeline = OptimizationPipeline::builder()
        .max_iterations(3)
        .pass(DeadCodeElimination)
        .finalize(FindJoinPoints)
        .build();

    assert_eq!(pipeline.pass_count(), 1);
    assert_eq!(pipeline.finalization_count(), 1);

    // Test that finalization converts eligible functions to join points
    let loop_decl = FunDecl::new(
        fvar(1),
        name("loop"),
        vec![Param::new(fvar(10), name("n"), nat_type())],
        nat_type(),
        Code::ret(fvar(10)),
    );

    let code = Code::fun(
        loop_decl,
        Code::let_bind(
            LetDecl::new(
                fvar(2),
                name("_1"),
                nat_type(),
                LetValue::FVar {
                    fvar: fvar(1),
                    args: vec![Arg::FVar(fvar(100))],
                },
            ),
            Code::ret(fvar(2)),
        ),
    );

    let result = pipeline.run_on_code(&code);
    // FindJoinPoints should convert the tail-called function to a join point
    match result {
        Code::JoinPoint(jp_decl, _) => {
            assert_eq!(jp_decl.fvar_id, fvar(1));
        }
        _ => panic!("Expected JoinPoint after finalization, got: {result:?}"),
    }
}

#[test]
fn test_default_pipeline_matches_opt_config() {
    // Verify the default pipeline produces the same pass ordering as
    // opt::optimize_code with default config.
    let pipeline = OptimizationPipeline::default();
    let names = pipeline.pass_names();
    assert_eq!(
        names,
        vec!["dce", "cse", "constant_fold", "simp_value", "inline"],
        "Default pipeline should match opt::optimize_code pass order"
    );
    assert_eq!(pipeline.finalization_count(), 1);
}

#[test]
fn test_extern_decl_passthrough() {
    use crate::lcnf::ExternEntry;

    let decl = Decl::extern_decl(
        name("extern_fn"),
        vec![],
        nat_type(),
        vec![],
        vec![ExternEntry {
            backend: "c".to_string(),
            name: "lean_extern_fn".to_string(),
        }],
    );

    let pipeline = OptimizationPipeline::default();
    let result = pipeline.run(&decl);

    assert!(
        result.is_extern(),
        "Extern decls should pass through unchanged"
    );
    match &result.body {
        DeclValue::Extern(attr) => {
            assert_eq!(attr.entries.len(), 1);
            assert_eq!(attr.entries[0].name, "lean_extern_fn");
        }
        _ => panic!("Expected extern body"),
    }
}
