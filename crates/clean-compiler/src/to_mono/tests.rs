// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the monomorphization pass.

use super::cases::{
    cases_array_to_mono, cases_byte_array_to_mono, cases_nat_to_mono, cases_string_to_mono,
    cases_task_to_mono, cases_thunk_to_mono, cases_to_mono_with_depth, cases_uint_to_mono,
    trivial_struct_to_mono,
};
use super::names::special_names;
use super::*;
use crate::lcnf::{Alt, Arg, Cases, LetDecl, LetValue, Param};
use clean_kernel::env::TrustedEnvExt;
use clean_kernel::inductive::{ConstructorVal, InductiveVal};
use clean_kernel::BinderInfo;
use clean_kernel::Level;
use clean_kernel::Literal;

fn make_test_decl(name: &str, params: Vec<Param>, body: Code) -> Decl {
    make_decl(name, params, Expr::prop(), body)
}

fn make_decl(name: &str, params: Vec<Param>, ty: Expr, body: Code) -> Decl {
    Decl {
        name: Name::from_string(name),
        level_params: vec![Name::from_string("u")],
        ty,
        params,
        body: DeclValue::Code(Box::new(body)),
        recursive: false,
    }
}

fn make_param(id: u64, name: &str, is_type: bool) -> Param {
    let ty = if is_type {
        Expr::sort(Level::zero())
    } else {
        Expr::const_(Name::from_string("Nat"), vec![])
    };
    Param {
        fvar_id: FVarId::new(id),
        name: Name::from_string(name),
        ty,
        borrow: false,
    }
}

fn make_const_call_body(result_id: u64, result_ty: Expr, callee: Name, args: Vec<Arg>) -> Code {
    Code::Let(
        LetDecl {
            fvar_id: FVarId::new(result_id),
            name: Name::from_string("result"),
            ty: result_ty,
            value: LetValue::Const {
                name: callee,
                levels: vec![],
                args,
            },
        },
        Box::new(Code::Return(FVarId::new(result_id))),
    )
}

fn register_single_ctor_inductive(
    env: &mut Environment,
    type_name: &Name,
    ctor_name: &Name,
    ctor_type: Expr,
    num_fields: u32,
) {
    env.register_inductive(InductiveVal {
        name: type_name.clone(),
        level_params: vec![],
        type_: Expr::type_(),
        num_params: 0,
        num_indices: 0,
        all_names: vec![type_name.clone()],
        constructor_names: vec![ctor_name.clone()],
        is_recursive: false,
        is_reflexive: false,
        is_large_elim: true,
        is_nested: false,
    });
    env.register_constructor(ConstructorVal {
        name: ctor_name.clone(),
        inductive_name: type_name.clone(),
        level_params: vec![],
        type_: ctor_type,
        num_params: 0,
        num_fields,
        constructor_idx: 0,
    });
}

fn make_pair_payload_cases(type_name: &Name, ctor_name: &Name, field_type: &Expr) -> Cases {
    Cases::new(
        type_name.clone(),
        field_type.clone(),
        FVarId::new(1),
        vec![Alt::Ctor {
            ctor_name: ctor_name.clone(),
            params: vec![
                Param {
                    fvar_id: FVarId::new(10),
                    name: Name::from_string("lhs"),
                    ty: field_type.clone(),
                    borrow: false,
                },
                Param {
                    fvar_id: FVarId::new(11),
                    name: Name::from_string("rhs"),
                    ty: field_type.clone(),
                    borrow: false,
                },
            ],
            body: Box::new(Code::Return(FVarId::new(10))),
        }],
    )
}

fn make_computed_type_carrier_fixture() -> (Environment, Cases) {
    let orig_type = Name::from_string("ComputedTypeCarrier");
    let orig_ctor = Name::from_string("ComputedTypeCarrier.mk");
    let impl_type = impl_name(&orig_type);
    let impl_ctor = impl_name(&orig_ctor);
    let bool_ty = Expr::const_(Name::from_string("Bool"), vec![]);

    let mut env = Environment::new();
    register_single_ctor_inductive(
        &mut env,
        &orig_type,
        &orig_ctor,
        Expr::arrow(Expr::type_(), Expr::const_(orig_type.clone(), vec![])),
        1,
    );
    register_single_ctor_inductive(
        &mut env,
        &impl_type,
        &impl_ctor,
        Expr::arrow(
            bool_ty,
            Expr::arrow(Expr::type_(), Expr::const_(impl_type.clone(), vec![])),
        ),
        2,
    );

    let cases = Cases::new(
        orig_type,
        Expr::type_(),
        FVarId::new(1),
        vec![Alt::Ctor {
            ctor_name: orig_ctor,
            params: vec![Param {
                fvar_id: FVarId::new(10),
                name: Name::from_string("carrier"),
                ty: Expr::type_(),
                borrow: false,
            }],
            body: Box::new(Code::Let(
                LetDecl {
                    fvar_id: FVarId::new(11),
                    name: Name::from_string("keep"),
                    ty: Expr::type_(),
                    value: LetValue::FVar {
                        fvar: FVarId::new(10),
                        args: vec![],
                    },
                },
                Box::new(Code::Return(FVarId::new(11))),
            )),
        }],
    );

    (env, cases)
}

fn make_cached_type_guided_fixture() -> (Decl, Decl, Name) {
    let callee_name = Name::from_string("callee");
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let callee = make_decl(
        "callee",
        vec![
            Param {
                fvar_id: FVarId::new(0),
                name: Name::from_string("x"),
                ty: nat.clone(),
                borrow: false,
            },
            Param {
                fvar_id: FVarId::new(1),
                name: Name::from_string("h"),
                ty: erased_expr(),
                borrow: false,
            },
        ],
        Expr::prop(),
        Code::Return(FVarId::new(0)),
    );
    let caller = make_decl(
        "caller",
        vec![
            Param {
                fvar_id: FVarId::new(10),
                name: Name::from_string("x"),
                ty: nat.clone(),
                borrow: false,
            },
            Param {
                fvar_id: FVarId::new(11),
                name: Name::from_string("h"),
                ty: erased_expr(),
                borrow: false,
            },
        ],
        Expr::prop(),
        make_const_call_body(
            12,
            nat,
            callee_name.clone(),
            vec![Arg::FVar(FVarId::new(10)), Arg::FVar(FVarId::new(11))],
        ),
    );
    (callee, caller, callee_name)
}

fn make_cached_red_arg_fixture() -> (Decl, Decl, Name) {
    let foo_name = Name::from_string("foo");
    let foo_red_arg = red_arg_name(&foo_name);
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let foo = make_decl(
        "foo",
        vec![
            Param {
                fvar_id: FVarId::new(0),
                name: Name::from_string("α"),
                ty: Expr::type_(),
                borrow: false,
            },
            Param {
                fvar_id: FVarId::new(1),
                name: Name::from_string("x"),
                ty: nat.clone(),
                borrow: false,
            },
            Param {
                fvar_id: FVarId::new(2),
                name: Name::from_string("y"),
                ty: nat.clone(),
                borrow: false,
            },
        ],
        Expr::prop(),
        make_const_call_body(
            3,
            nat.clone(),
            foo_red_arg.clone(),
            vec![Arg::FVar(FVarId::new(1))],
        ),
    );
    let caller = make_decl(
        "caller",
        vec![
            Param {
                fvar_id: FVarId::new(10),
                name: Name::from_string("x"),
                ty: nat.clone(),
                borrow: false,
            },
            Param {
                fvar_id: FVarId::new(11),
                name: Name::from_string("y"),
                ty: nat.clone(),
                borrow: false,
            },
        ],
        Expr::prop(),
        make_const_call_body(
            12,
            nat,
            foo_name.clone(),
            vec![
                Arg::Type(Expr::type_()),
                Arg::FVar(FVarId::new(10)),
                Arg::FVar(FVarId::new(11)),
            ],
        ),
    );
    (foo, caller, foo_red_arg)
}

#[test]
fn test_is_type_former_type() {
    // Sort is type-former
    assert!(is_type_former_type(&Expr::sort(Level::zero())));
    assert!(is_type_former_type(&Expr::type_()));

    // Pi returning Sort is type-former
    let pi_sort = Expr::pi(BinderInfo::Default, Expr::type_(), Expr::type_());
    assert!(is_type_former_type(&pi_sort));

    // Nat is not type-former
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    assert!(!is_type_former_type(&nat));
}

#[test]
fn test_arg_to_mono_erases_type() {
    let state = ToMonoState::new();

    // Type args become erased
    let type_arg = Arg::Type(Expr::type_());
    assert!(matches!(arg_to_mono(&type_arg, &state), Arg::Erased));

    // Already erased stays erased
    assert!(matches!(arg_to_mono(&Arg::Erased, &state), Arg::Erased));

    // FVar not in type_params stays
    let fvar_arg = Arg::FVar(FVarId::new(42));
    assert!(matches!(arg_to_mono(&fvar_arg, &state), Arg::FVar(_)));
}

#[test]
fn test_arg_to_mono_erases_type_param_fvar() {
    let mut state = ToMonoState::new();
    state.add_type_param(FVarId::new(10));

    // FVar that is a type param becomes erased
    let fvar_arg = Arg::FVar(FVarId::new(10));
    assert!(matches!(arg_to_mono(&fvar_arg, &state), Arg::Erased));

    // Other FVar stays
    let other_fvar = Arg::FVar(FVarId::new(20));
    assert!(matches!(arg_to_mono(&other_fvar, &state), Arg::FVar(_)));
}

#[test]
fn test_decidable_to_bool() {
    let state = ToMonoState::new();
    let env = Environment::new();

    // Decidable.isTrue → Bool.true
    let is_true = LetValue::Const {
        name: special_names::decidable_is_true(),
        levels: vec![],
        args: vec![],
    };
    let result = letvalue_to_mono(&is_true, &state, &env);
    if let LetValueTransform::Simple(LetValue::Const { name, .. }) = result {
        assert_eq!(name, special_names::bool_true());
    } else {
        panic!("Expected Bool.true");
    }

    // Decidable.isFalse → Bool.false
    let is_false = LetValue::Const {
        name: special_names::decidable_is_false(),
        levels: vec![],
        args: vec![],
    };
    let result = letvalue_to_mono(&is_false, &state, &env);
    if let LetValueTransform::Simple(LetValue::Const { name, .. }) = result {
        assert_eq!(name, special_names::bool_false());
    } else {
        panic!("Expected Bool.false");
    }
}

#[test]
fn test_nat_succ_to_add() {
    let state = ToMonoState::new();
    let env = Environment::new();

    let succ_value = LetValue::Const {
        name: special_names::nat_succ(),
        levels: vec![],
        args: vec![Arg::FVar(FVarId::new(5))],
    };

    let result = letvalue_to_mono(&succ_value, &state, &env);
    assert!(matches!(result, LetValueTransform::NatSucc(_)));
}

#[test]
fn test_nat_zero_to_literal() {
    let state = ToMonoState::new();
    let env = Environment::new();

    // Nat.zero as Const → Lit(Nat(0))
    let zero_value = LetValue::Const {
        name: special_names::nat_zero(),
        levels: vec![],
        args: vec![],
    };

    let result = letvalue_to_mono(&zero_value, &state, &env);
    if let LetValueTransform::Simple(LetValue::Lit(Literal::Nat(n))) = result {
        assert_eq!(n.to_u64(), Some(0));
    } else {
        panic!("Expected Lit(Nat(0))");
    }
}

#[test]
fn test_nat_zero_ctor_to_literal() {
    let state = ToMonoState::new();
    let env = Environment::new();

    // Nat.zero as Ctor → Lit(Nat(0))
    let zero_value = LetValue::Ctor {
        name: special_names::nat_zero(),
        levels: vec![],
        args: vec![],
    };

    let result = letvalue_to_mono(&zero_value, &state, &env);
    if let LetValueTransform::Simple(LetValue::Lit(Literal::Nat(n))) = result {
        assert_eq!(n.to_u64(), Some(0));
    } else {
        panic!("Expected Lit(Nat(0)) for Ctor variant");
    }
}

#[test]
fn test_nat_succ_ctor_to_add() {
    let state = ToMonoState::new();
    let env = Environment::new();

    // Nat.succ as Ctor → NatSucc transform
    let succ_value = LetValue::Ctor {
        name: special_names::nat_succ(),
        levels: vec![],
        args: vec![Arg::FVar(FVarId::new(5))],
    };

    let result = letvalue_to_mono(&succ_value, &state, &env);
    assert!(
        matches!(result, LetValueTransform::NatSucc(_)),
        "Expected NatSucc transform for Ctor variant"
    );
}

#[test]
fn test_quot_lc_inv_uses_primary_arg_and_preserves_tail_args() {
    let mut state = ToMonoState::new();
    state.add_type_param(FVarId::new(99));
    let env = Environment::new();

    let lc_inv = LetValue::Const {
        name: special_names::quot_lc_inv(),
        levels: vec![],
        args: vec![
            Arg::Type(Expr::type_()),
            Arg::Erased,
            Arg::FVar(FVarId::new(7)),
            Arg::FVar(FVarId::new(99)),
            Arg::FVar(FVarId::new(11)),
        ],
    };

    let result = letvalue_to_mono(&lc_inv, &state, &env);
    if let LetValueTransform::Simple(LetValue::FVar { fvar, args }) = result {
        assert_eq!(fvar, FVarId::new(7), "Quot.lcInv should use args[2]");
        assert_eq!(args.len(), 2, "tail args should be preserved");
        assert!(
            matches!(args[0], Arg::Erased),
            "type-param tail arg should be erased during lowering"
        );
        assert!(
            matches!(args[1], Arg::FVar(fvar) if fvar == FVarId::new(11)),
            "non-erased tail arg should stay in the lowered application"
        );
    } else {
        panic!("Expected Quot.lcInv to lower to direct FVar application");
    }
}

#[test]
fn test_quot_lc_inv_erased_primary_arg_returns_erased() {
    let state = ToMonoState::new();
    let env = Environment::new();

    let lc_inv = LetValue::Const {
        name: special_names::quot_lc_inv(),
        levels: vec![],
        args: vec![
            Arg::Type(Expr::type_()),
            Arg::Erased,
            Arg::Erased,
            Arg::FVar(FVarId::new(11)),
        ],
    };

    let result = letvalue_to_mono(&lc_inv, &state, &env);
    assert!(
        matches!(result, LetValueTransform::Simple(LetValue::Erased)),
        "erased/type-only primary argument should erase the Quot.lcInv call"
    );
}

#[test]
fn test_to_mono_erases_level_params() {
    let decl = make_test_decl(
        "test",
        vec![make_param(0, "x", false)],
        Code::Return(FVarId::new(0)),
    );

    let env = Environment::new();
    let mono_decl = to_mono(&decl, &env);
    assert!(mono_decl.level_params.is_empty());
}

#[test]
fn test_to_mono_erases_type_args() {
    let params = vec![
        make_param(0, "T", true),  // type param
        make_param(1, "x", false), // value param
    ];

    let body = Code::Let(
        LetDecl {
            fvar_id: FVarId::new(2),
            name: Name::from_string("y"),
            ty: Expr::prop(),
            value: LetValue::Const {
                name: Name::from_string("id"),
                levels: vec![],
                args: vec![Arg::FVar(FVarId::new(0)), Arg::FVar(FVarId::new(1))],
            },
        },
        Box::new(Code::Return(FVarId::new(2))),
    );

    let decl = make_test_decl("test", params, body);
    let env = Environment::new();
    let mono_decl = to_mono(&decl, &env);

    // Check that type param arg is erased
    if let DeclValue::Code(code) = &mono_decl.body {
        if let Code::Let(let_decl, _) = code.as_ref() {
            if let LetValue::Const { args, .. } = &let_decl.value {
                assert!(matches!(args[0], Arg::Erased));
                assert!(matches!(args[1], Arg::FVar(_)));
            }
        }
    }
}

#[test]
fn test_decidable_cases_to_bool_cases() {
    // Test that cases on Decidable are transformed to cases on Bool
    // Input: cases x of | Decidable.isTrue h => body1 | Decidable.isFalse h => body2
    // Output: cases x of | Bool.true => body1 | Bool.false => body2 (params erased)

    let proof_param = Param {
        fvar_id: FVarId::new(10),
        name: Name::from_string("h"),
        ty: Expr::prop(), // Proof type
        borrow: false,
    };

    let cases = Cases::new(
        Name::from_string("Decidable"),
        Expr::const_(Name::from_string("Nat"), vec![]),
        FVarId::new(1),
        vec![
            Alt::Ctor {
                ctor_name: special_names::decidable_is_true(),
                params: vec![proof_param.clone()],
                body: Box::new(Code::Return(FVarId::new(2))),
            },
            Alt::Ctor {
                ctor_name: special_names::decidable_is_false(),
                params: vec![proof_param],
                body: Box::new(Code::Return(FVarId::new(3))),
            },
        ],
    );

    let mut state = ToMonoState::new();
    let mut next_fvar = 20u64;
    let env = Environment::new();

    let result = cases_to_mono(&cases, &mut state, &mut next_fvar, &env);

    // Verify result is still a Cases
    if let Code::Cases(mono_cases) = result {
        assert_eq!(mono_cases.scrutinee.as_u64(), 1);
        assert_eq!(mono_cases.alts.len(), 2);

        // Check first alt: Decidable.isTrue -> Bool.true with erased params
        if let Alt::Ctor {
            ctor_name, params, ..
        } = &mono_cases.alts[0]
        {
            assert_eq!(*ctor_name, special_names::bool_true());
            assert!(params.is_empty(), "Bool.true should have no params");
        } else {
            panic!("Expected Ctor alt");
        }

        // Check second alt: Decidable.isFalse -> Bool.false with erased params
        if let Alt::Ctor {
            ctor_name, params, ..
        } = &mono_cases.alts[1]
        {
            assert_eq!(*ctor_name, special_names::bool_false());
            assert!(params.is_empty(), "Bool.false should have no params");
        } else {
            panic!("Expected Ctor alt");
        }
    } else {
        panic!("Expected Cases, got {:?}", result);
    }
}

#[test]
fn test_nat_cases_to_bool_cases() {
    // Test that cases on Nat are transformed to cases on Bool
    // Input: cases n of | Nat.zero => k0 | Nat.succ p => k1
    // Output: let zero := 0; let isZero := Nat.decEq n zero; cases isZero of ...

    let nat_type = Expr::const_(special_names::nat_(), vec![]);
    let pred_param = Param {
        fvar_id: FVarId::new(10),
        name: Name::from_string("p"),
        ty: nat_type.clone(),
        borrow: false,
    };

    let cases = Cases::new(
        special_names::nat_(),
        nat_type,
        FVarId::new(1),
        vec![
            Alt::Ctor {
                ctor_name: special_names::nat_zero(),
                params: vec![],
                body: Box::new(Code::Return(FVarId::new(2))),
            },
            Alt::Ctor {
                ctor_name: special_names::nat_succ(),
                params: vec![pred_param],
                body: Box::new(Code::Return(FVarId::new(10))),
            },
        ],
    );

    let mut state = ToMonoState::new();
    let mut next_fvar = 20u64;
    let env = Environment::new();

    let result = cases_nat_to_mono(&cases, &mut state, &mut next_fvar, &env, 0);

    // Result should be: let zero := 0; let isZero := ...; cases isZero of ...
    if let Code::Let(zero_decl, rest) = result {
        assert_eq!(zero_decl.name.to_string(), "_zero");
        if let LetValue::Lit(Literal::Nat(n)) = zero_decl.value {
            assert_eq!(n.to_u64(), Some(0));
        } else {
            panic!("Expected zero literal");
        }

        if let Code::Let(is_zero_decl, rest) = *rest {
            assert_eq!(is_zero_decl.name.to_string(), "_isZero");
            if let LetValue::Const { name, .. } = &is_zero_decl.value {
                assert_eq!(*name, special_names::nat_dec_eq());
            } else {
                panic!("Expected Nat.decEq call");
            }

            if let Code::Cases(mono_cases) = *rest {
                assert_eq!(mono_cases.type_name, special_names::bool_());
                assert_eq!(mono_cases.alts.len(), 2);
            } else {
                panic!("Expected Cases");
            }
        } else {
            panic!("Expected isZero let");
        }
    } else {
        panic!("Expected zero let, got {:?}", result);
    }
}

#[test]
fn test_uint_cases_to_extract() {
    // UInt cases become simple let extraction with toBitVec
    let uint_type = Expr::const_(special_names::uint32_(), vec![]);
    let bits_param = Param {
        fvar_id: FVarId::new(10),
        name: Name::from_string("bits"),
        ty: Expr::prop(),
        borrow: false,
    };

    let cases = Cases::new(
        special_names::uint32_(),
        uint_type,
        FVarId::new(1),
        vec![Alt::Ctor {
            ctor_name: Name::from_string("UInt32.mk"),
            params: vec![bits_param],
            body: Box::new(Code::Return(FVarId::new(10))),
        }],
    );

    let mut state = ToMonoState::new();
    let mut next_fvar = 20u64;
    let env = Environment::new();

    let result = cases_uint_to_mono(
        &cases,
        &mut state,
        &mut next_fvar,
        &env,
        0,
        special_names::uint32_to_bit_vec(),
    );

    // Result should be: let bits := UInt32.toBitVec scrutinee; body
    if let Code::Let(decl, body) = result {
        assert_eq!(decl.fvar_id.as_u64(), 10); // Reuses param's fvar_id
        if let LetValue::Const { name, args, .. } = &decl.value {
            assert_eq!(*name, special_names::uint32_to_bit_vec());
            assert_eq!(args.len(), 1);
        } else {
            panic!("Expected toBitVec call");
        }

        if let Code::Return(fvar) = *body {
            assert_eq!(fvar.as_u64(), 10);
        } else {
            panic!("Expected return");
        }
    } else {
        panic!("Expected let extraction, got {:?}", result);
    }
}

#[test]
fn test_array_cases_to_extract() {
    // Array cases become simple let extraction with toList
    let array_type = Expr::const_(special_names::array_(), vec![]);
    let list_param = Param {
        fvar_id: FVarId::new(10),
        name: Name::from_string("list"),
        ty: Expr::prop(),
        borrow: false,
    };

    let cases = Cases::new(
        special_names::array_(),
        array_type,
        FVarId::new(1),
        vec![Alt::Ctor {
            ctor_name: Name::from_string("Array.mk"),
            params: vec![list_param],
            body: Box::new(Code::Return(FVarId::new(10))),
        }],
    );

    let mut state = ToMonoState::new();
    let mut next_fvar = 20u64;
    let env = Environment::new();

    let result = cases_array_to_mono(&cases, &mut state, &mut next_fvar, &env, 0);

    // Result should be: let list := Array.toList ◇ scrutinee; body
    if let Code::Let(decl, body) = result {
        assert_eq!(decl.fvar_id.as_u64(), 10); // Reuses param's fvar_id
        if let LetValue::Const { name, args, .. } = &decl.value {
            assert_eq!(*name, special_names::array_to_list());
            // First arg is erased (type param), second is scrutinee
            assert_eq!(args.len(), 2);
            assert!(matches!(&args[0], Arg::Erased));
        } else {
            panic!("Expected toList call");
        }

        if let Code::Return(fvar) = *body {
            assert_eq!(fvar.as_u64(), 10);
        } else {
            panic!("Expected return");
        }
    } else {
        panic!("Expected let extraction, got {:?}", result);
    }
}

#[test]
fn test_string_cases_to_extract() {
    // String cases become simple let extraction with toList
    let string_type = Expr::const_(special_names::string_(), vec![]);
    let chars_param = Param {
        fvar_id: FVarId::new(10),
        name: Name::from_string("chars"),
        ty: Expr::prop(),
        borrow: false,
    };

    let cases = Cases::new(
        special_names::string_(),
        string_type,
        FVarId::new(1),
        vec![Alt::Ctor {
            ctor_name: Name::from_string("String.mk"),
            params: vec![chars_param],
            body: Box::new(Code::Return(FVarId::new(10))),
        }],
    );

    let mut state = ToMonoState::new();
    let mut next_fvar = 20u64;
    let env = Environment::new();

    let result = cases_string_to_mono(&cases, &mut state, &mut next_fvar, &env, 0);

    // Result should be: let chars := String.toList scrutinee; body
    if let Code::Let(decl, body) = result {
        assert_eq!(decl.fvar_id.as_u64(), 10); // Reuses param's fvar_id
        if let LetValue::Const { name, args, .. } = &decl.value {
            assert_eq!(*name, special_names::string_to_list());
            // Only arg is scrutinee
            assert_eq!(args.len(), 1);
        } else {
            panic!("Expected toList call");
        }

        if let Code::Return(fvar) = *body {
            assert_eq!(fvar.as_u64(), 10);
        } else {
            panic!("Expected return");
        }
    } else {
        panic!("Expected let extraction, got {:?}", result);
    }
}

#[test]
fn test_cases_dispatch_by_type_name() {
    // Test that cases_to_mono_with_depth dispatches correctly by type_name
    let env = Environment::new();
    let mut state = ToMonoState::new();
    let mut next_fvar = 100u64;

    // Nat type_name should trigger cases_nat_to_mono
    let nat_cases = Cases::new(
        special_names::nat_(),
        Expr::const_(special_names::nat_(), vec![]),
        FVarId::new(1),
        vec![
            Alt::Ctor {
                ctor_name: special_names::nat_zero(),
                params: vec![],
                body: Box::new(Code::Return(FVarId::new(2))),
            },
            Alt::Default(Box::new(Code::Return(FVarId::new(3)))),
        ],
    );

    let result = cases_to_mono_with_depth(&nat_cases, &mut state, &mut next_fvar, &env, 0);
    // Should produce let bindings for zero and isZero, then Bool cases
    assert!(
        matches!(result, Code::Let(_, _)),
        "Nat cases should produce Let structure"
    );
}

#[test]
fn test_cases_to_mono_rewrites_computed_field_impl_branch() {
    let orig_type = Name::from_string("Computed");
    let orig_ctor = Name::from_string("Computed.mk");
    let impl_type = impl_name(&orig_type);
    let impl_ctor = impl_name(&orig_ctor);
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let bool_ty = Expr::const_(Name::from_string("Bool"), vec![]);

    let mut env = Environment::new();
    register_single_ctor_inductive(
        &mut env,
        &orig_type,
        &orig_ctor,
        Expr::arrow(
            nat.clone(),
            Expr::arrow(nat.clone(), Expr::const_(orig_type.clone(), vec![])),
        ),
        2,
    );
    register_single_ctor_inductive(
        &mut env,
        &impl_type,
        &impl_ctor,
        Expr::arrow(
            bool_ty.clone(),
            Expr::arrow(
                nat.clone(),
                Expr::arrow(nat.clone(), Expr::const_(impl_type.clone(), vec![])),
            ),
        ),
        3,
    );

    let cases = make_pair_payload_cases(&orig_type, &orig_ctor, &nat);

    let mut state = ToMonoState::new();
    let mut next_fvar = 20;
    let result = cases_to_mono(&cases, &mut state, &mut next_fvar, &env);

    if let Code::Cases(mono_cases) = result {
        assert_eq!(mono_cases.type_name, impl_type);
        if let Alt::Ctor {
            ctor_name, params, ..
        } = &mono_cases.alts[0]
        {
            assert_eq!(*ctor_name, impl_ctor);
            assert_eq!(params.len(), 3, "computed field should be prepended");
            assert_eq!(params[0].fvar_id, FVarId::new(20));
            assert_eq!(params[0].ty, bool_ty);
            assert_eq!(params[1].fvar_id, FVarId::new(10));
            assert_eq!(params[2].fvar_id, FVarId::new(11));
        } else {
            panic!("Expected constructor alt");
        }
    } else {
        panic!("Expected cases result");
    }
    assert_eq!(
        next_fvar, 21,
        "computed-field binder should consume one fresh id"
    );
}

#[test]
fn test_cases_to_mono_preserves_old_field_binders_in_impl_branch() {
    let (env, cases) = make_computed_type_carrier_fixture();
    let mut state = ToMonoState::new();
    let mut next_fvar = 20;
    let result = cases_to_mono(&cases, &mut state, &mut next_fvar, &env);

    let Code::Cases(mono_cases) = result else {
        panic!("Expected cases result");
    };
    let Alt::Ctor { params, body, .. } = &mono_cases.alts[0] else {
        panic!("Expected constructor alt");
    };
    assert_eq!(params.len(), 2, "computed field should be prepended");
    assert_eq!(
        params[1].ty,
        Expr::type_(),
        "old field binder type should remain unchanged in the _impl branch"
    );

    let Code::Let(let_decl, _) = body.as_ref() else {
        panic!("Expected let-bound body");
    };
    match &let_decl.value {
        LetValue::FVar { fvar, args } => {
            assert_eq!(
                *fvar,
                FVarId::new(10),
                "old field binder should not be spuriously erased"
            );
            assert!(args.is_empty());
        }
        other => panic!("Expected preserved old field binder, got {other:?}"),
    }
}

#[test]
fn test_cases_to_mono_skips_impl_branch_when_env_lacks_impl_metadata() {
    let orig_type = Name::from_string("Plain");
    let orig_ctor = Name::from_string("Plain.mk");
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);

    let mut env = Environment::new();
    register_single_ctor_inductive(
        &mut env,
        &orig_type,
        &orig_ctor,
        Expr::arrow(
            nat.clone(),
            Expr::arrow(nat.clone(), Expr::const_(orig_type.clone(), vec![])),
        ),
        2,
    );

    let cases = make_pair_payload_cases(&orig_type, &orig_ctor, &nat);

    let mut state = ToMonoState::new();
    let mut next_fvar = 20;
    let result = cases_to_mono(&cases, &mut state, &mut next_fvar, &env);

    if let Code::Cases(mono_cases) = result {
        assert_eq!(mono_cases.type_name, orig_type);
        if let Alt::Ctor {
            ctor_name, params, ..
        } = &mono_cases.alts[0]
        {
            assert_eq!(*ctor_name, orig_ctor);
            assert_eq!(params.len(), 2);
            assert_eq!(params[0].fvar_id, FVarId::new(10));
            assert_eq!(params[1].fvar_id, FVarId::new(11));
        } else {
            panic!("Expected constructor alt");
        }
    } else {
        panic!("Expected cases result");
    }
}

#[test]
fn test_args_to_mono_red_arg() {
    // Test reduced-argument transformation
    let state = ToMonoState::new();

    // Set up params and args where redArg pattern selects a subset
    let params = vec![
        make_param(0, "α", true),  // type param
        make_param(1, "x", false), // value param
        make_param(2, "y", false), // value param
    ];

    let args = vec![
        Arg::Type(Expr::type_()),
        Arg::FVar(FVarId::new(10)),
        Arg::FVar(FVarId::new(11)),
    ];

    // red_args pattern: only wants param at index 1 (x)
    let red_args = vec![Arg::FVar(FVarId::new(1))];

    let result = args_to_mono_red_arg(&args, &params, &red_args, &state);

    // Should return transformed arg at index 1
    assert_eq!(result.len(), 1);
    assert!(matches!(result[0], Arg::FVar(fvar) if fvar.as_u64() == 10));
}

#[test]
fn test_ctor_app_to_mono() {
    // Test constructor param erasure
    let state = ToMonoState::new();
    let ctor_name = Name::from_string("List.cons");

    // List.cons takes 3 args: (α : Type), (head : α), (tail : List α)
    let args = vec![
        Arg::Type(Expr::type_()),   // type param
        Arg::FVar(FVarId::new(10)), // head
        Arg::FVar(FVarId::new(11)), // tail
    ];

    // 1 type param
    let result = ctor_app_to_mono(&ctor_name, &args, 1, &state);

    if let LetValue::Const {
        name,
        args: mono_args,
        ..
    } = result
    {
        assert_eq!(name, ctor_name);
        assert_eq!(mono_args.len(), 3);
        assert!(matches!(mono_args[0], Arg::Erased)); // type param erased
        assert!(matches!(mono_args[1], Arg::FVar(fvar) if fvar.as_u64() == 10)); // head preserved
        assert!(matches!(mono_args[2], Arg::FVar(fvar) if fvar.as_u64() == 11));
    // tail preserved
    } else {
        panic!("Expected Const");
    }
}

#[test]
fn test_fvar_type_param_erased() {
    // Test that FVar applications on type params are erased
    let mut state = ToMonoState::new();
    state.add_type_param(FVarId::new(5));
    let env = Environment::new();

    let value = LetValue::FVar {
        fvar: FVarId::new(5),
        args: vec![Arg::FVar(FVarId::new(10))],
    };

    let result = letvalue_to_mono(&value, &state, &env);
    if let LetValueTransform::Simple(LetValue::Erased) = result {
        // OK - type param fvar application is erased
    } else {
        panic!("Expected Erased for type param FVar");
    }
}

#[test]
fn test_proj_type_param_erased() {
    // Test that projections on type params are erased
    let mut state = ToMonoState::new();
    state.add_type_param(FVarId::new(5));
    let env = Environment::new();

    let value = LetValue::Proj {
        type_name: Name::from_string("Foo"),
        idx: 0,
        structure: FVarId::new(5),
    };

    let result = letvalue_to_mono(&value, &state, &env);
    if let LetValueTransform::Simple(LetValue::Erased) = result {
        // OK - projection on type param is erased
    } else {
        panic!("Expected Erased for projection on type param");
    }
}

#[test]
fn test_byte_array_cases_to_extract() {
    // ByteArray cases become let extraction with data accessor
    let byte_array_type = Expr::const_(special_names::byte_array_(), vec![]);
    let data_param = Param {
        fvar_id: FVarId::new(10),
        name: Name::from_string("data"),
        ty: Expr::prop(),
        borrow: false,
    };

    let cases = Cases::new(
        special_names::byte_array_(),
        byte_array_type,
        FVarId::new(1),
        vec![Alt::Ctor {
            ctor_name: Name::from_string("ByteArray.mk"),
            params: vec![data_param],
            body: Box::new(Code::Return(FVarId::new(10))),
        }],
    );

    let mut state = ToMonoState::new();
    let mut next_fvar = 20u64;
    let env = Environment::new();

    let result = cases_byte_array_to_mono(&cases, &mut state, &mut next_fvar, &env, 0);

    if let Code::Let(decl, _) = result {
        if let LetValue::Const { name, .. } = &decl.value {
            assert_eq!(*name, special_names::byte_array_data());
        } else {
            panic!("Expected ByteArray.data call");
        }
    } else {
        panic!("Expected let extraction");
    }
}

#[test]
fn test_task_cases_to_extract() {
    // Task cases become let extraction with get
    let task_type = Expr::const_(special_names::task_(), vec![]);
    let val_param = Param {
        fvar_id: FVarId::new(10),
        name: Name::from_string("val"),
        ty: Expr::prop(),
        borrow: false,
    };

    let cases = Cases::new(
        special_names::task_(),
        task_type,
        FVarId::new(1),
        vec![Alt::Ctor {
            ctor_name: Name::from_string("Task.mk"),
            params: vec![val_param],
            body: Box::new(Code::Return(FVarId::new(10))),
        }],
    );

    let mut state = ToMonoState::new();
    let mut next_fvar = 20u64;
    let env = Environment::new();

    let result = cases_task_to_mono(&cases, &mut state, &mut next_fvar, &env, 0);

    if let Code::Let(decl, _) = result {
        if let LetValue::Const { name, args, .. } = &decl.value {
            assert_eq!(*name, special_names::task_get());
            // First arg erased (type param), second is scrutinee
            assert!(matches!(&args[0], Arg::Erased));
        } else {
            panic!("Expected Task.get call");
        }
    } else {
        panic!("Expected let extraction");
    }
}

#[test]
fn test_thunk_cases_to_fun() {
    // Thunk cases become fun decl (lazy evaluation wrapper)
    let thunk_type = Expr::const_(special_names::thunk_(), vec![]);
    let val_param = Param {
        fvar_id: FVarId::new(10),
        name: Name::from_string("val"),
        ty: Expr::prop(),
        borrow: false,
    };

    let cases = Cases::new(
        special_names::thunk_(),
        thunk_type,
        FVarId::new(1),
        vec![Alt::Ctor {
            ctor_name: Name::from_string("Thunk.mk"),
            params: vec![val_param],
            body: Box::new(Code::Return(FVarId::new(10))),
        }],
    );

    let mut state = ToMonoState::new();
    let mut next_fvar = 20u64;
    let env = Environment::new();

    let result = cases_thunk_to_mono(&cases, &mut state, &mut next_fvar, &env, 0);

    // Thunk produces Code::Fun, not Code::Let
    assert!(
        matches!(result, Code::Fun(_, _)),
        "Thunk cases should produce Fun structure"
    );
}

#[test]
fn test_trivial_struct_to_mono() {
    // Test trivial structure elimination
    // A trivial struct wraps a single field - pattern match becomes identity
    let trivial_type = Expr::const_(Name::from_string("Trivial"), vec![]);
    let val_param = Param {
        fvar_id: FVarId::new(10),
        name: Name::from_string("val"),
        ty: Expr::const_(Name::from_string("Nat"), vec![]),
        borrow: false,
    };

    let cases = Cases::new(
        Name::from_string("Trivial"),
        trivial_type,
        FVarId::new(1),
        vec![Alt::Ctor {
            ctor_name: Name::from_string("Trivial.mk"),
            params: vec![val_param],
            body: Box::new(Code::Return(FVarId::new(10))),
        }],
    );

    let info = TrivialStructureInfo {
        ctor_name: Name::from_string("Trivial.mk"),
        num_params: 0,
        field_idx: 0,
    };

    let mut state = ToMonoState::new();
    let mut next_fvar = 20u64;
    let env = Environment::new();

    let result = trivial_struct_to_mono(&info, &cases, &mut state, &mut next_fvar, &env, 0);

    // Result should be: let val := scrutinee; body
    if let Code::Let(decl, body) = result {
        assert_eq!(decl.fvar_id.as_u64(), 10); // Reuses param's fvar_id
                                               // Value is just FVar to scrutinee (identity)
        if let LetValue::FVar { fvar, args } = &decl.value {
            assert_eq!(fvar.as_u64(), 1); // scrutinee
            assert!(args.is_empty());
        } else {
            panic!("Expected FVar value for trivial struct extraction");
        }

        if let Code::Return(fvar) = *body {
            assert_eq!(fvar.as_u64(), 10);
        } else {
            panic!("Expected return");
        }
    } else {
        panic!("Expected let extraction for trivial struct");
    }
}

#[test]
fn test_has_trivial_structure_detection() {
    // Test trivial structure detection via has_trivial_structure

    // Create a trivial structure: Wrapper with single field
    let wrapper_name = Name::from_string("Wrapper");
    let wrapper_mk = Name::from_string("Wrapper.mk");

    let mut env = Environment::new();

    // Register inductive type
    let ind_val = InductiveVal {
        name: wrapper_name.clone(),
        level_params: vec![],
        type_: Expr::type_(),
        num_params: 0,
        num_indices: 0,
        all_names: vec![wrapper_name.clone()],
        constructor_names: vec![wrapper_mk.clone()],
        is_recursive: false,
        is_reflexive: false,
        is_large_elim: true,
        is_nested: false,
    };
    env.register_inductive(ind_val);

    // Register constructor with single field
    let ctor_val = ConstructorVal {
        name: wrapper_mk.clone(),
        inductive_name: wrapper_name.clone(),
        level_params: vec![],
        type_: Expr::arrow(
            Expr::const_(Name::from_string("Nat"), vec![]),
            Expr::const_(wrapper_name.clone(), vec![]),
        ),
        num_params: 0,
        num_fields: 1,
        constructor_idx: 0,
    };
    env.register_constructor(ctor_val);

    // Should be detected as trivial
    let info = has_trivial_structure(&wrapper_name, &env);
    assert!(
        info.is_some(),
        "Wrapper should be detected as trivial structure"
    );
    let info = info.unwrap();
    assert_eq!(info.ctor_name, wrapper_mk);
    assert_eq!(info.num_params, 0);
    assert_eq!(info.field_idx, 0);
}

#[test]
fn test_has_trivial_structure_rejects_multiple_constructors() {
    // Bool has two constructors - should not be trivial
    let bool_name = Name::from_string("TestBool");

    let mut env = Environment::new();

    let ind_val = InductiveVal {
        name: bool_name.clone(),
        level_params: vec![],
        type_: Expr::type_(),
        num_params: 0,
        num_indices: 0,
        all_names: vec![bool_name.clone()],
        constructor_names: vec![
            Name::from_string("TestBool.true"),
            Name::from_string("TestBool.false"),
        ],
        is_recursive: false,
        is_reflexive: false,
        is_large_elim: true,
        is_nested: false,
    };
    env.register_inductive(ind_val);

    // Should NOT be trivial (two constructors)
    assert!(
        has_trivial_structure(&bool_name, &env).is_none(),
        "Type with multiple constructors should not be trivial"
    );
}

#[test]
fn test_has_trivial_structure_rejects_recursive() {
    // Recursive types should not be trivial
    let list_name = Name::from_string("TestList");
    let cons_name = Name::from_string("TestList.cons");

    let mut env = Environment::new();

    let ind_val = InductiveVal {
        name: list_name.clone(),
        level_params: vec![],
        type_: Expr::type_(),
        num_params: 0,
        num_indices: 0,
        all_names: vec![list_name.clone()],
        constructor_names: vec![cons_name.clone()],
        is_recursive: true, // Recursive!
        is_reflexive: false,
        is_large_elim: true,
        is_nested: false,
    };
    env.register_inductive(ind_val);

    // Should NOT be trivial (recursive)
    assert!(
        has_trivial_structure(&list_name, &env).is_none(),
        "Recursive type should not be trivial"
    );
}

#[test]
fn test_has_trivial_structure_rejects_multiple_relevant_fields() {
    // Structure with two data fields should not be trivial.
    // Pair.mk : Nat → Nat → Pair
    let pair_name = Name::from_string("Pair");
    let pair_mk = Name::from_string("Pair.mk");

    let mut env = Environment::new();

    let ind_val = InductiveVal {
        name: pair_name.clone(),
        level_params: vec![],
        type_: Expr::type_(),
        num_params: 0,
        num_indices: 0,
        all_names: vec![pair_name.clone()],
        constructor_names: vec![pair_mk.clone()],
        is_recursive: false,
        is_reflexive: false,
        is_large_elim: true,
        is_nested: false,
    };
    env.register_inductive(ind_val);

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    // Pair.mk : Nat → Nat → Pair (two data fields)
    let ctor_type = Expr::arrow(
        nat.clone(),
        Expr::arrow(nat, Expr::const_(pair_name.clone(), vec![])),
    );
    let ctor_val = ConstructorVal {
        name: pair_mk.clone(),
        inductive_name: pair_name.clone(),
        level_params: vec![],
        type_: ctor_type,
        num_params: 0,
        num_fields: 2,
        constructor_idx: 0,
    };
    env.register_constructor(ctor_val);

    // Should NOT be trivial (two relevant data fields)
    assert!(
        has_trivial_structure(&pair_name, &env).is_none(),
        "Type with multiple relevant fields should not be trivial"
    );
}

#[test]
fn test_has_trivial_structure_with_type_former_field() {
    // A structure like: TypeTagged.mk (α : Type) (val : Nat) → TypeTagged
    // has 2 fields but only 1 relevant (val). The α field is a type-former.
    let tagged_name = Name::from_string("TypeTagged");
    let tagged_mk = Name::from_string("TypeTagged.mk");

    let mut env = Environment::new();

    let ind_val = InductiveVal {
        name: tagged_name.clone(),
        level_params: vec![],
        type_: Expr::type_(),
        num_params: 0,
        num_indices: 0,
        all_names: vec![tagged_name.clone()],
        constructor_names: vec![tagged_mk.clone()],
        is_recursive: false,
        is_reflexive: false,
        is_large_elim: true,
        is_nested: false,
    };
    env.register_inductive(ind_val);

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    // TypeTagged.mk : Type → Nat → TypeTagged
    // Field 0: Type (irrelevant type-former), Field 1: Nat (relevant data)
    let ctor_type = Expr::arrow(
        Expr::type_(),
        Expr::arrow(nat, Expr::const_(tagged_name.clone(), vec![])),
    );
    let ctor_val = ConstructorVal {
        name: tagged_mk.clone(),
        inductive_name: tagged_name.clone(),
        level_params: vec![],
        type_: ctor_type,
        num_params: 0,
        num_fields: 2,
        constructor_idx: 0,
    };
    env.register_constructor(ctor_val);

    // Should be trivial: 2 fields but only 1 relevant (field_idx = 1)
    let info = has_trivial_structure(&tagged_name, &env);
    assert!(
        info.is_some(),
        "Type with one type-former + one data field should be trivial"
    );
    let info = info.unwrap();
    assert_eq!(info.field_idx, 1, "Relevant field should be at index 1");
    assert_eq!(info.ctor_name, tagged_mk);
}

#[test]
fn test_has_trivial_structure_with_prop_field() {
    // A structure like: Checked.mk (val : Nat) (ok : Prop) → Checked
    // has 2 fields but only 1 relevant (val). The Prop field is irrelevant.
    let checked_name = Name::from_string("Checked");
    let checked_mk = Name::from_string("Checked.mk");

    let mut env = Environment::new();

    let ind_val = InductiveVal {
        name: checked_name.clone(),
        level_params: vec![],
        type_: Expr::type_(),
        num_params: 0,
        num_indices: 0,
        all_names: vec![checked_name.clone()],
        constructor_names: vec![checked_mk.clone()],
        is_recursive: false,
        is_reflexive: false,
        is_large_elim: true,
        is_nested: false,
    };
    env.register_inductive(ind_val);

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let prop = Expr::sort(Level::zero()); // Prop = Sort 0
                                          // Checked.mk : Nat → Prop → Checked
                                          // Field 0: Nat (relevant), Field 1: Prop (irrelevant)
    let ctor_type = Expr::arrow(
        nat,
        Expr::arrow(prop, Expr::const_(checked_name.clone(), vec![])),
    );
    let ctor_val = ConstructorVal {
        name: checked_mk.clone(),
        inductive_name: checked_name.clone(),
        level_params: vec![],
        type_: ctor_type,
        num_params: 0,
        num_fields: 2,
        constructor_idx: 0,
    };
    env.register_constructor(ctor_val);

    // Should be trivial: Prop field is irrelevant
    let info = has_trivial_structure(&checked_name, &env);
    assert!(
        info.is_some(),
        "Type with one data + one Prop field should be trivial"
    );
    let info = info.unwrap();
    assert_eq!(info.field_idx, 0, "Relevant field should be at index 0");
}

#[test]
fn test_has_trivial_structure_with_params_and_irrelevant_field() {
    // Simulate: Subtype-like structure with type parameter
    // SubLike.mk {α : Type} (val : α) (prop : Prop) → SubLike α
    // num_params = 1, num_fields = 2, 1 relevant field (val at field idx 0)
    let sub_name = Name::from_string("SubLike");
    let sub_mk = Name::from_string("SubLike.mk");

    let mut env = Environment::new();

    let ind_val = InductiveVal {
        name: sub_name.clone(),
        level_params: vec![],
        type_: Expr::arrow(Expr::type_(), Expr::type_()),
        num_params: 1,
        num_indices: 0,
        all_names: vec![sub_name.clone()],
        constructor_names: vec![sub_mk.clone()],
        is_recursive: false,
        is_reflexive: false,
        is_large_elim: true,
        is_nested: false,
    };
    env.register_inductive(ind_val);

    let alpha = Expr::bvar(2); // bound variable for α
    let prop = Expr::sort(Level::zero());
    // SubLike.mk : (α : Type) → α → Prop → SubLike α
    // Pi(Type, Pi(BVar(1), Pi(Prop, SubLike (BVar(2)))))
    let result_type = Expr::app(Expr::const_(sub_name.clone(), vec![]), Expr::bvar(2));
    let ctor_type = Expr::pi(
        BinderInfo::Implicit,
        Expr::type_(),
        Expr::arrow(alpha, Expr::arrow(prop, result_type)),
    );
    let ctor_val = ConstructorVal {
        name: sub_mk.clone(),
        inductive_name: sub_name.clone(),
        level_params: vec![],
        type_: ctor_type,
        num_params: 1, // α is a parameter
        num_fields: 2, // val and prop are fields
        constructor_idx: 0,
    };
    env.register_constructor(ctor_val);

    // Should be trivial: skip 1 param (α), field 0 = BVar (data), field 1 = Prop (irrelevant)
    let info = has_trivial_structure(&sub_name, &env);
    assert!(
        info.is_some(),
        "SubLike with param + data field + Prop field should be trivial"
    );
    let info = info.unwrap();
    assert_eq!(
        info.field_idx, 0,
        "Data field (val) should be at field index 0"
    );
    assert_eq!(info.num_params, 1);
}

#[test]
fn test_has_trivial_structure_all_irrelevant_fields() {
    // A type with only type-former fields has 0 relevant fields → not trivial
    let phantom_name = Name::from_string("Phantom");
    let phantom_mk = Name::from_string("Phantom.mk");

    let mut env = Environment::new();

    let ind_val = InductiveVal {
        name: phantom_name.clone(),
        level_params: vec![],
        type_: Expr::type_(),
        num_params: 0,
        num_indices: 0,
        all_names: vec![phantom_name.clone()],
        constructor_names: vec![phantom_mk.clone()],
        is_recursive: false,
        is_reflexive: false,
        is_large_elim: true,
        is_nested: false,
    };
    env.register_inductive(ind_val);

    // Phantom.mk : Type → Type → Phantom (all irrelevant fields)
    let ctor_type = Expr::arrow(
        Expr::type_(),
        Expr::arrow(Expr::type_(), Expr::const_(phantom_name.clone(), vec![])),
    );
    let ctor_val = ConstructorVal {
        name: phantom_mk.clone(),
        inductive_name: phantom_name.clone(),
        level_params: vec![],
        type_: ctor_type,
        num_params: 0,
        num_fields: 2,
        constructor_idx: 0,
    };
    env.register_constructor(ctor_val);

    // Should NOT be trivial (0 relevant fields)
    assert!(
        has_trivial_structure(&phantom_name, &env).is_none(),
        "Type with only type-former fields should not be trivial"
    );
}

#[test]
fn test_has_trivial_structure_rejects_runtime_builtins() {
    // Runtime builtin types should not be treated as trivial even if they match criteria
    let env = Environment::new();

    // Even if String somehow matched structure criteria, it should be rejected
    // as a runtime builtin
    assert!(
        has_trivial_structure(&special_names::string_(), &env).is_none(),
        "String should be rejected as runtime builtin"
    );
    assert!(
        has_trivial_structure(&special_names::nat_(), &env).is_none(),
        "Nat should be rejected as runtime builtin"
    );
    assert!(
        has_trivial_structure(&special_names::array_(), &env).is_none(),
        "Array should be rejected as runtime builtin"
    );
    assert!(
        has_trivial_structure(&special_names::uint32_(), &env).is_none(),
        "UInt32 should be rejected as runtime builtin"
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// Tests for lcErased/lcAny helpers and to_mono_type
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn test_lc_erased_name() {
    assert_eq!(lc_erased_name(), Name::from_string("lcErased"));
}

#[test]
fn test_lc_any_name() {
    assert_eq!(lc_any_name(), Name::from_string("lcAny"));
}

#[test]
fn test_erased_expr() {
    let e = erased_expr();
    assert!(matches!(e.kind(), ExprKind::Const(name, _) if *name == lc_erased_name()));
}

#[test]
fn test_any_expr() {
    let e = any_expr();
    assert!(matches!(e.kind(), ExprKind::Const(name, _) if *name == lc_any_name()));
}

#[test]
fn test_is_erased() {
    assert!(is_erased(&erased_expr()));
    assert!(!is_erased(&any_expr()));
    assert!(!is_erased(&Expr::type_()));
    assert!(!is_erased(&Expr::const_(Name::from_string("Nat"), vec![])));
}

#[test]
fn test_is_any() {
    assert!(is_any(&any_expr()));
    assert!(!is_any(&erased_expr()));
    assert!(!is_any(&Expr::type_()));
}

#[test]
fn test_to_mono_type_sort_is_erased() {
    // Sort u → lcErased
    assert!(is_erased(&to_mono_type(&Expr::sort(Level::zero()))));
    assert!(is_erased(&to_mono_type(&Expr::type_())));
}

#[test]
fn test_to_mono_type_head_beta() {
    // (fun x : Type => x) Type → Type → lcErased after head beta
    let lam = Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(0));
    let app = Expr::app(lam, Expr::type_());
    assert!(is_erased(&to_mono_type(&app)));
}

#[test]
fn test_to_mono_type_head_beta_mdata() {
    // Metadata-wrapped lambdas should still reduce at head position.
    let lam = Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(0));
    let mdata = Expr::mdata(vec![], lam);
    let app = Expr::app(mdata, Expr::type_());
    assert!(is_erased(&to_mono_type(&app)));
}

#[test]
fn test_to_mono_type_decidable_becomes_bool() {
    // Decidable → Bool
    let decidable = Expr::const_(Name::from_string("Decidable"), vec![]);
    let result = to_mono_type(&decidable);
    assert!(matches!(
        result.kind(),
        ExprKind::Const(name, _) if *name == Name::from_string("Bool")
    ));
}

#[test]
fn test_to_mono_type_lc_erased_stays_erased() {
    let e = erased_expr();
    assert!(is_erased(&to_mono_type(&e)));
}

#[test]
fn test_to_mono_type_lc_any_stays_any() {
    let e = any_expr();
    assert!(is_any(&to_mono_type(&e)));
}

#[test]
fn test_to_mono_type_pi_with_erased_body() {
    // Pi _ _ (Sort 0) → lcErased (body is erased, so whole type is erased)
    let pi = Expr::pi(
        BinderInfo::Default,
        Expr::type_(),
        Expr::sort(Level::zero()),
    );
    assert!(is_erased(&to_mono_type(&pi)));
}

#[test]
fn test_to_mono_type_pi_with_non_erased_body() {
    // Pi _ Nat Nat → lcAny → lcAny (function type with any args)
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let pi = Expr::pi(BinderInfo::Default, nat.clone(), nat);
    let result = to_mono_type(&pi);
    // Result should be a Pi type
    assert!(matches!(result.kind(), ExprKind::Pi(_, _, _)));
}

#[test]
fn test_args_to_mono_with_fn_type_erases_sort_domain() {
    let state = ToMonoState::new();

    // fn_type: (α : Type) → Nat → α
    let alpha = Expr::type_();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let fn_type = Expr::pi(
        BinderInfo::Default,
        alpha.clone(),
        Expr::pi(BinderInfo::Default, nat.clone(), Expr::bvar(1)),
    );

    let args = vec![
        Arg::Type(Expr::const_(Name::from_string("Int"), vec![])),
        Arg::FVar(FVarId::new(100)),
    ];

    let result = args_to_mono_with_fn_type(&args, &fn_type, &state);

    // First arg (type param) should be erased
    assert!(matches!(result[0], Arg::Erased));
    // Second arg (value) should stay
    assert!(matches!(result[1], Arg::FVar(_)));
}

#[test]
fn test_args_to_mono_with_fn_type_erases_lc_erased_domain() {
    let state = ToMonoState::new();

    // fn_type: (◇ : lcErased) → Nat → Nat
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let fn_type = Expr::pi(
        BinderInfo::Default,
        erased_expr(),
        Expr::pi(BinderInfo::Default, nat.clone(), nat.clone()),
    );

    let args = vec![Arg::FVar(FVarId::new(1)), Arg::FVar(FVarId::new(2))];

    let result = args_to_mono_with_fn_type(&args, &fn_type, &state);

    // First arg (lcErased domain) should be erased
    assert!(matches!(result[0], Arg::Erased));
    // Second arg should stay
    assert!(matches!(result[1], Arg::FVar(_)));
}

#[test]
fn test_letvalue_ctor_uses_ctor_app_to_mono() {
    // Test that LetValue::Ctor with a known constructor uses ctor_app_to_mono
    // for precise type parameter erasure.
    // Note: Use 2 fields to avoid triggering trivial structure optimization.
    let state = ToMonoState::new();
    let mut env = Environment::new();

    // Create an inductive type with 1 type param and 2 fields (not trivial)
    let pair_name = Name::from_string("TypedPair");
    let pair_mk = Name::from_string("TypedPair.mk");

    let ind_val = InductiveVal {
        name: pair_name.clone(),
        level_params: vec![Name::from_string("u")],
        type_: Expr::type_(),
        num_params: 1, // One type param
        num_indices: 0,
        all_names: vec![pair_name.clone()],
        constructor_names: vec![pair_mk.clone()],
        is_recursive: false,
        is_reflexive: false,
        is_large_elim: true,
        is_nested: false,
    };
    env.register_inductive(ind_val);

    let ctor_val = ConstructorVal {
        name: pair_mk.clone(),
        inductive_name: pair_name.clone(),
        level_params: vec![Name::from_string("u")],
        type_: Expr::type_(),
        num_params: 1, // One type param
        num_fields: 2, // Two fields (not trivial!)
        constructor_idx: 0,
    };
    env.register_constructor(ctor_val);

    // Create TypedPair.mk with args: [Type, fst, snd]
    let ctor_value = LetValue::Ctor {
        name: pair_mk.clone(),
        levels: vec![Level::succ(Level::zero())],
        args: vec![
            Arg::Type(Expr::const_(Name::from_string("Nat"), vec![])),
            Arg::FVar(FVarId::new(42)),
            Arg::FVar(FVarId::new(43)),
        ],
    };

    let result = letvalue_to_mono(&ctor_value, &state, &env);

    // Should produce a Const (ctor_app_to_mono returns LetValue::Const)
    // with first arg erased and field args preserved
    if let LetValueTransform::Simple(LetValue::Const { args, levels, .. }) = result {
        assert_eq!(levels.len(), 0, "Universe levels should be erased");
        assert_eq!(args.len(), 3);
        assert!(
            matches!(args[0], Arg::Erased),
            "Type param should be erased"
        );
        assert!(
            matches!(args[1], Arg::FVar(fvar) if fvar.as_u64() == 42),
            "First field preserved"
        );
        assert!(
            matches!(args[2], Arg::FVar(fvar) if fvar.as_u64() == 43),
            "Second field preserved"
        );
    } else {
        panic!("Expected Const from ctor_app_to_mono");
    }
}

#[test]
fn test_letvalue_proj_trivial_struct_identity() {
    // Test that projecting the relevant field from a trivial structure
    // becomes identity (returns the structure fvar directly)
    let state = ToMonoState::new();
    let mut env = Environment::new();

    // Create a trivial structure: Wrapper with 1 constructor, 1 field
    let wrapper_name = Name::from_string("TrivialWrapper");
    let wrapper_mk = Name::from_string("TrivialWrapper.mk");

    let ind_val = InductiveVal {
        name: wrapper_name.clone(),
        level_params: vec![],
        type_: Expr::type_(),
        num_params: 0,
        num_indices: 0,
        all_names: vec![wrapper_name.clone()],
        constructor_names: vec![wrapper_mk.clone()],
        is_recursive: false,
        is_reflexive: false,
        is_large_elim: true,
        is_nested: false,
    };
    env.register_inductive(ind_val);

    let ctor_val = ConstructorVal {
        name: wrapper_mk.clone(),
        inductive_name: wrapper_name.clone(),
        level_params: vec![],
        type_: Expr::type_(),
        num_params: 0,
        num_fields: 1, // Single field = trivial
        constructor_idx: 0,
    };
    env.register_constructor(ctor_val);

    // Project field 0 from wrapper
    let proj_value = LetValue::Proj {
        type_name: wrapper_name.clone(),
        idx: 0, // The relevant field
        structure: FVarId::new(100),
    };

    let result = letvalue_to_mono(&proj_value, &state, &env);

    // Should become FVar identity (just return the structure)
    if let LetValueTransform::Simple(LetValue::FVar { fvar, args }) = result {
        assert_eq!(fvar, FVarId::new(100), "Should return structure fvar");
        assert!(args.is_empty(), "No args on identity projection");
    } else {
        panic!("Expected FVar identity for trivial struct projection");
    }
}

#[test]
fn test_to_mono_decls_uses_cached_mono_type_for_const_calls() {
    let (callee, caller, callee_name) = make_cached_type_guided_fixture();

    let env = Environment::new();
    let mono = to_mono_decls(vec![callee, caller], &env);

    let DeclValue::Code(code) = &mono[1].body else {
        panic!("Expected caller code body");
    };
    let Code::Let(let_decl, _) = code.as_ref() else {
        panic!("Expected let-bound call in caller");
    };
    let LetValue::Const { name, args, .. } = &let_decl.value else {
        panic!("Expected const call");
    };
    assert_eq!(*name, callee_name);
    assert!(
        matches!(args[0], Arg::FVar(fvar) if fvar == FVarId::new(10)),
        "value argument should be preserved"
    );
    assert!(
        matches!(args[1], Arg::Erased),
        "cached mono type should erase the lcErased-domain argument"
    );
}

#[test]
fn test_to_mono_decls_rewrites_cached_red_arg_calls() {
    let (foo, caller, foo_red_arg) = make_cached_red_arg_fixture();

    let env = Environment::new();
    let mono = to_mono_decls(vec![foo, caller], &env);

    let DeclValue::Code(code) = &mono[1].body else {
        panic!("Expected caller code body");
    };
    let Code::Let(let_decl, _) = code.as_ref() else {
        panic!("Expected let-bound call in caller");
    };
    let LetValue::Const { name, args, .. } = &let_decl.value else {
        panic!("Expected const call");
    };
    assert_eq!(*name, foo_red_arg);
    assert_eq!(
        args.len(),
        1,
        "_redArg rewrite should keep only selected args"
    );
    assert!(
        matches!(args[0], Arg::FVar(fvar) if fvar == FVarId::new(10)),
        "_redArg rewrite should forward the selected runtime argument"
    );
}
