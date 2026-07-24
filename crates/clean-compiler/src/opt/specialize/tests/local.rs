// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Local function (FVar) specialization tests.

use super::*;

#[test]
fn test_local_fun_specialization_basic() {
    use crate::lcnf::Param;

    // fun f (inst : Nat) (x : Nat) := return x
    // let _ground := 42
    // let _result := f _ground _arg  -- _ground is ground, _arg is param
    // return _result
    //
    // After specialization:
    // fun f (inst : Nat) (x : Nat) := return x
    // fun f_spec (x : Nat) := return x  -- inst substituted
    // let _ground := 42
    // let _result := f_spec _arg  -- ground arg removed
    // return _result

    let code = Code::Fun(
        FunDecl::new(
            fvar(100),
            name("f"),
            vec![
                Param::new(fvar(101), name("inst"), nat_type()),
                Param::new(fvar(102), name("x"), nat_type()),
            ],
            nat_type(),
            Code::ret(fvar(102)),
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
    );

    let mut ctx = SpecContext::new(name("test"));
    ctx.scope.insert(fvar(3)); // param, not ground

    let mut state = SpecState::new();
    let config = SpecConfig::default();

    let result = specialize_code(&mut ctx, &mut state, &code, &config);

    let (call_fvar, call_args) =
        extract_first_fvar_call(&result).expect("invariant: should contain an FVar call");

    assert_ne!(
        call_fvar,
        fvar(100),
        "Call should be rewritten to specialized version"
    );
    assert_eq!(
        call_args.len(),
        1,
        "Specialized call should have 1 remaining arg, got {}",
        call_args.len()
    );
}

#[test]
fn test_local_fun_no_spec_without_ground_args() {
    use crate::lcnf::Param;

    let code = Code::Fun(
        FunDecl::new(
            fvar(100),
            name("f"),
            vec![Param::new(fvar(101), name("x"), nat_type())],
            nat_type(),
            Code::ret(fvar(101)),
        ),
        Box::new(Code::let_bind(
            LetDecl::new(
                fvar(2),
                name("_result"),
                nat_type(),
                LetValue::FVar {
                    fvar: fvar(100),
                    args: vec![Arg::FVar(fvar(1))],
                },
            ),
            Code::ret(fvar(2)),
        )),
    );

    let mut ctx = SpecContext::new(name("test"));
    ctx.scope.insert(fvar(1)); // param, not ground

    let mut state = SpecState::new();
    let config = SpecConfig::default();

    let result = specialize_code(&mut ctx, &mut state, &code, &config);

    let (call_fvar, call_args) =
        extract_first_fvar_call(&result).expect("invariant: should contain an FVar call");
    assert_eq!(call_fvar, fvar(100), "Call should remain unchanged");
    assert_eq!(call_args.len(), 1);
}

#[test]
fn test_local_fun_specialization_cache_hit() {
    use crate::lcnf::Param;

    // Two calls to same local function with same ground args should share one spec
    let code = Code::Fun(
        FunDecl::new(
            fvar(100),
            name("f"),
            vec![
                Param::new(fvar(101), name("inst"), nat_type()),
                Param::new(fvar(102), name("x"), nat_type()),
            ],
            nat_type(),
            Code::ret(fvar(102)),
        ),
        Box::new(Code::let_bind(
            LetDecl::new(fvar(1), name("_ground"), nat_type(), LetValue::nat(42)),
            Code::let_bind(
                LetDecl::new(
                    fvar(2),
                    name("_r1"),
                    nat_type(),
                    LetValue::FVar {
                        fvar: fvar(100),
                        args: vec![Arg::FVar(fvar(1)), Arg::FVar(fvar(3))],
                    },
                ),
                Code::let_bind(
                    LetDecl::new(
                        fvar(4),
                        name("_r2"),
                        nat_type(),
                        LetValue::FVar {
                            fvar: fvar(100),
                            args: vec![Arg::FVar(fvar(1)), Arg::FVar(fvar(5))],
                        },
                    ),
                    Code::ret(fvar(4)),
                ),
            ),
        )),
    );

    let mut ctx = SpecContext::new(name("test"));
    ctx.scope.insert(fvar(3));
    ctx.scope.insert(fvar(5));

    let mut state = SpecState::new();
    let config = SpecConfig::default();

    let _ = specialize_code(&mut ctx, &mut state, &code, &config);

    assert_eq!(
        state.local_spec_cache.len(),
        1,
        "Same ground args should produce one cache entry"
    );
}

#[test]
fn test_local_fun_specialization_disabled() {
    use crate::lcnf::Param;

    let code = Code::Fun(
        FunDecl::new(
            fvar(100),
            name("f"),
            vec![
                Param::new(fvar(101), name("inst"), nat_type()),
                Param::new(fvar(102), name("x"), nat_type()),
            ],
            nat_type(),
            Code::ret(fvar(102)),
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
    );

    let mut ctx = SpecContext::new(name("test"));
    ctx.scope.insert(fvar(3));

    let mut state = SpecState::new();
    let config = SpecConfig {
        specialize_instances: false,
        ..Default::default()
    };

    let result = specialize_code(&mut ctx, &mut state, &code, &config);

    let (call_fvar, _) =
        extract_first_fvar_call(&result).expect("invariant: should contain an FVar call");
    assert_eq!(call_fvar, fvar(100), "Call should remain unchanged");
}
