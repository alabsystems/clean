// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! W2-140 claim_verification: wrap_with_ground_bindings + DCE interaction.
//!
//! Verifies that the let bindings added by `wrap_with_ground_bindings`
//! (Part of #1954 Bug 3) interact correctly with DCE:
//! - Dead bindings (ground param unreferenced) are removed by DCE
//! - Live bindings (ground param in Return or Const args) are kept by DCE

use super::*;
use crate::opt::dce;

/// Extract the specialized function body from Code output.
/// Finds the first Fun declaration whose fvar_id is NOT `original_fvar`.
fn extract_spec_fun_body(code: &Code, original_fvar: FVarId) -> Option<Box<Code>> {
    match code {
        Code::Fun(decl, body) => {
            if decl.fvar_id != original_fvar {
                Some(decl.body.clone())
            } else {
                extract_spec_fun_body(body, original_fvar)
            }
        }
        Code::Let(_, body) | Code::JoinPoint(_, body) => extract_spec_fun_body(body, original_fvar),
        _ => None,
    }
}

/// Count let bindings at the top of a code block.
fn count_top_lets(code: &Code) -> usize {
    match code {
        Code::Let(_, body) => 1 + count_top_lets(body),
        _ => 0,
    }
}

/// Build the standard test harness: local fun with ground+non-ground args.
fn build_spec_harness(fun_body: Code) -> Code {
    use crate::lcnf::Param;

    Code::Fun(
        FunDecl::new(
            fvar(100),
            name("f"),
            vec![
                Param::new(fvar(101), name("inst"), nat_type()),
                Param::new(fvar(102), name("x"), nat_type()),
            ],
            nat_type(),
            fun_body,
        ),
        Box::new(Code::let_bind(
            LetDecl::new(fvar(1), name("_ground"), nat_type(), LetValue::nat(42)),
            Code::let_bind(
                LetDecl::new(
                    fvar(2),
                    name("_result"),
                    nat_type(),
                    LetValue::FVar {
                        fvar: fvar(100),
                        args: vec![Arg::FVar(fvar(1)), Arg::FVar(fvar(3))],
                    },
                ),
                Code::ret(fvar(2)),
            ),
        )),
    )
}

fn run_specialize(code: &Code) -> Code {
    let mut ctx = SpecContext::new(name("test"));
    ctx.scope.insert(fvar(3)); // non-ground param
    let mut state = SpecState::new();
    let config = SpecConfig::default();
    specialize_code(&mut ctx, &mut state, code, &config)
}

#[test]
fn test_ground_binding_dead_after_dce_when_unused() {
    // fun f (inst : Nat) (x : Nat) := return x
    // inst is never referenced → wrapping let is dead → DCE removes it.
    let code = build_spec_harness(Code::ret(fvar(102)));
    let result = run_specialize(&code);

    let spec_body =
        extract_spec_fun_body(&result, fvar(100)).expect("Specialized function should be emitted");

    assert_eq!(
        count_top_lets(&spec_body),
        1,
        "wrap_with_ground_bindings should add 1 let for inst"
    );

    let after_dce = dce::eliminate_dead_code_in_code(&spec_body);
    assert_eq!(
        count_top_lets(&after_dce),
        0,
        "DCE should remove the dead ground binding"
    );
}

#[test]
fn test_ground_binding_kept_by_dce_when_returned() {
    // fun f (inst : Nat) (x : Nat) := return inst
    // substitute_ground_in_code doesn't handle Code::Return,
    // so inst's FVarId remains → wrapping let is needed → DCE keeps it.
    let code = build_spec_harness(Code::ret(fvar(101)));
    let result = run_specialize(&code);

    let spec_body =
        extract_spec_fun_body(&result, fvar(100)).expect("Specialized function should be emitted");

    assert_eq!(count_top_lets(&spec_body), 1);

    let after_dce = dce::eliminate_dead_code_in_code(&spec_body);
    assert_eq!(
        count_top_lets(&after_dce),
        1,
        "DCE should keep the ground binding (inst used in Return)"
    );

    // Verify return still references inst
    fn find_return_fvar(code: &Code) -> Option<FVarId> {
        match code {
            Code::Return(fvar) => Some(*fvar),
            Code::Let(_, body) => find_return_fvar(body),
            _ => None,
        }
    }
    assert_eq!(
        find_return_fvar(&after_dce),
        Some(fvar(101)),
        "Return should still reference inst"
    );
}

#[test]
fn test_ground_binding_kept_by_dce_when_in_const_args() {
    // fun f (inst : Nat) (x : Nat) :=
    //   let _q := Nat.succ(inst)  -- inst as Arg::FVar in Const args
    //   return _q
    //
    // substitute_ground_in_code doesn't substitute Arg::FVar inside
    // LetValue::Const args → inst's FVarId remains → transitively live.
    let fun_body = Code::let_bind(
        LetDecl::new(
            fvar(103),
            name("_q"),
            nat_type(),
            LetValue::Const {
                name: name("Nat.succ"),
                levels: vec![],
                args: vec![Arg::FVar(fvar(101))],
            },
        ),
        Code::ret(fvar(103)),
    );

    let code = build_spec_harness(fun_body);
    let result = run_specialize(&code);

    let spec_body =
        extract_spec_fun_body(&result, fvar(100)).expect("Specialized function should be emitted");

    assert_eq!(
        count_top_lets(&spec_body),
        2,
        "Should have 2 lets: ground binding + let _q"
    );

    let after_dce = dce::eliminate_dead_code_in_code(&spec_body);
    assert_eq!(
        count_top_lets(&after_dce),
        2,
        "DCE should keep both (inst transitively live via Nat.succ)"
    );
}
