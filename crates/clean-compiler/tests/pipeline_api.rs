// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_compiler::emit_c::CEmitConfig;
use clean_compiler::emit_rust::RustEmitConfig;
use clean_compiler::ir::{IRBody, IRExpr};
use clean_compiler::lcnf::{Alt, Cases, Code, Decl, LetDecl, LetValue, Param};
use clean_compiler::pass_manager::{
    compile_lcnf_decls, compile_lcnf_to_c, compile_lcnf_to_rust, PipelineConfig,
};
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

#[test]
fn test_compile_lcnf_decls_exposes_all_pipeline_stages() {
    let decl = Decl::new(
        name("id"),
        vec![],
        nat_type(),
        vec![Param::new(fvar(0), name("x"), nat_type())],
        Code::ret(fvar(0)),
        false,
    );
    let env = Environment::default();

    let artifacts = compile_lcnf_decls(&[decl], &env, &PipelineConfig::default())
        .expect("pipeline should succeed for a simple identity function");

    assert_eq!(
        artifacts.mono_decls.len(),
        1,
        "monomorphization should preserve the declaration count here"
    );
    assert_eq!(
        artifacts.optimized_decls.len(),
        1,
        "batch optimization should preserve the declaration count here"
    );
    assert_eq!(
        artifacts.rc_decls.len(),
        1,
        "RC transformation should preserve the declaration count here"
    );
    assert_eq!(
        artifacts.ir_decls.len(),
        1,
        "IR lowering should emit one declaration for this identity function"
    );
    assert!(
        artifacts.boxed_ir_decls.len() >= artifacts.ir_decls.len(),
        "boxing should preserve or extend the IR declaration set"
    );
    assert!(
        artifacts.warnings.is_empty(),
        "simple identity function should not produce IR warnings: {:?}",
        artifacts.warnings
    );
}

#[test]
fn test_compile_lcnf_emitters_generate_named_functions() {
    let decl = Decl::new(
        name("const42"),
        vec![],
        nat_type(),
        vec![],
        Code::let_bind(
            LetDecl::new(fvar(0), name("_1"), nat_type(), LetValue::nat(42)),
            Code::ret(fvar(0)),
        ),
        false,
    );
    let env = Environment::default();
    let pipeline = PipelineConfig::default();

    let c_code = compile_lcnf_to_c(
        std::slice::from_ref(&decl),
        &env,
        &pipeline,
        CEmitConfig {
            check_ir: true,
            ..Default::default()
        },
    )
    .expect("pipeline should emit C for a constant declaration");
    assert!(
        c_code.contains("l_const42("),
        "C emitter should generate a named function: {c_code}"
    );

    let rust_code = compile_lcnf_to_rust(
        &[decl],
        &env,
        &pipeline,
        RustEmitConfig {
            check_ir: true,
            ..Default::default()
        },
    )
    .expect("pipeline should emit Rust for a constant declaration");
    assert!(
        rust_code.contains("pub unsafe fn l_const42("),
        "Rust emitter should generate a named function: {rust_code}"
    );
}

/// `match x with | 0 => 0 | _ => x` in the shape `to_lcnf::lower_nat_cases`
/// produces: a `Cases` over `Nat` with a `Nat.zero` alternative and a default.
fn nat_match_decl() -> Decl {
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
                Alt::ctor(
                    name("Nat.zero"),
                    vec![],
                    Code::let_bind(
                        LetDecl::new(fvar(1), name("_1"), nat_type(), LetValue::nat(0)),
                        Code::ret(fvar(1)),
                    ),
                ),
                Alt::default(Code::ret(fvar(0))),
            ],
        )),
        false,
    )
}

/// The scrutinee variable of the first `case` in `body`, if any.
fn first_case_scrutinee(body: &IRBody) -> Option<clean_compiler::ir::VarId> {
    match body {
        IRBody::Case { scrutinee, .. } => Some(*scrutinee),
        IRBody::VDecl { rest, .. }
        | IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => first_case_scrutinee(rest),
        IRBody::JDecl { body, rest, .. } => {
            first_case_scrutinee(body).or_else(|| first_case_scrutinee(rest))
        }
        _ => None,
    }
}

/// The value `var` is bound to by a `VDecl` in `body`.
fn binding_of(body: &IRBody, var: clean_compiler::ir::VarId) -> Option<&IRExpr> {
    match body {
        IRBody::VDecl {
            var: v,
            value,
            rest,
            ..
        } => {
            if *v == var {
                Some(value)
            } else {
                binding_of(rest, var)
            }
        }
        IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => binding_of(rest, var),
        IRBody::JDecl { body, rest, .. } => binding_of(body, var).or_else(|| binding_of(rest, var)),
        _ => None,
    }
}

/// A `Nat` pattern match never reads a constructor tag off the `Nat`: `to_mono`
/// rewrites every `Cases` over `Nat` into `Nat.decEq n 0` and a `case` on
/// that `Decidable` (`to_mono/cases/numeric.rs`), so the dispatch is correct
/// at every width, a heap `Nat` (>= 2^63) included. The C, Rust and trust-cg
/// lanes all emit from these boxed declarations, so none of them hands a `Nat`
/// to `clean_obj_tag`: a `Nat` of 300 never meets a tag read of any width.
#[test]
fn test_nat_match_dispatches_on_dec_eq_never_a_tag_read_of_the_nat() {
    let env = Environment::default();
    let pipeline = PipelineConfig::default();
    let artifacts = compile_lcnf_decls(&[nat_match_decl()], &env, &pipeline)
        .expect("a Nat match must compile through the production pipeline");
    let decl = artifacts
        .boxed_ir_decls
        .iter()
        .find(|d| d.name == name("match_nat"))
        .expect("match_nat must be lowered");
    let param = decl.params[0].0;
    let scrutinee = first_case_scrutinee(&decl.body).expect("the match must stay a case");
    assert_ne!(
        scrutinee, param,
        "the case must not dispatch on the Nat itself: {:#?}",
        decl.body
    );
    let mut root = scrutinee;
    while let Some(IRExpr::Unbox { arg, .. }) = binding_of(&decl.body, root) {
        match arg {
            clean_compiler::ir::IRArg::Var(v) => root = *v,
            clean_compiler::ir::IRArg::Erased => break,
        }
    }
    match binding_of(&decl.body, root) {
        Some(IRExpr::Apply { fn_id, args }) => {
            assert_eq!(fn_id.0, name("Nat.decEq"), "dispatch must be Nat.decEq");
            assert_eq!(
                args.first(),
                Some(&clean_compiler::ir::IRArg::Var(param)),
                "Nat.decEq must test the matched Nat"
            );
        }
        other => panic!(
            "the case must dispatch on Nat.decEq, got {other:?}: {:#?}",
            decl.body
        ),
    }

    let c = artifacts
        .emit_c(CEmitConfig {
            check_ir: true,
            ..Default::default()
        })
        .expect("the C lane must emit the Nat match");
    let rust = artifacts
        .emit_rust(RustEmitConfig {
            check_ir: true,
            ..Default::default()
        })
        .expect("the Rust lane must emit the Nat match");
    for (lane, code) in [("C", &c), ("Rust", &rust)] {
        assert!(
            code.contains("l_Nat_decEq(_x0"),
            "{lane}: the Nat match must call Nat.decEq on the Nat:\n{code}"
        );
        assert!(
            !code.contains("clean_obj_tag(_x0)"),
            "{lane}: the Nat must never reach clean_obj_tag:\n{code}"
        );
    }
}
