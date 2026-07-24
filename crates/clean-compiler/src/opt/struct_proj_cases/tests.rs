// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::lcnf::{Alt, Arg, Code, FunDecl, LetDecl, LetValue, Param};
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

/// Build the target pattern for StructProjCases:
///
/// ```text
/// jp _j (s : struct_ty) :=
///   let r := proj(s, proj_idx)
///   <ret r>
/// cases scrutinee of
///   | Ctor1 a b => let t := Ctor(arg1, arg2); jmp _j t
///   | Ctor2 c d => let t := Ctor(arg3, arg4); jmp _j t
/// ```
fn jp_proj_cases(
    jp_fvar: FVarId,
    jp_param_fvar: FVarId,
    proj_result_fvar: FVarId,
    proj_idx: u32,
    struct_ty: Expr,
    proj_result_ty: Expr,
    scrutinee: FVarId,
    type_name: Name,
    alts: Vec<Alt>,
) -> Code {
    let jp_body = Code::let_bind(
        LetDecl::new(
            proj_result_fvar,
            name("r"),
            proj_result_ty.clone(),
            LetValue::Proj {
                type_name: type_name.clone(),
                idx: proj_idx,
                structure: jp_param_fvar,
            },
        ),
        Code::ret(proj_result_fvar),
    );

    let jp_decl = FunDecl::new(
        jp_fvar,
        name("_j"),
        vec![Param::new(jp_param_fvar, name("s"), struct_ty)],
        proj_result_ty,
        jp_body,
    );

    let cases = Code::cases(type_name, nat_type(), scrutinee, alts);
    Code::JoinPoint(jp_decl, Box::new(cases))
}

/// Build a case alternative: `| ctor_name params => let t := Ctor(args); jmp jp t`
fn ctor_jmp_alt(
    ctor_name: Name,
    params: Vec<Param>,
    ctor_fvar: FVarId,
    ctor_args: Vec<Arg>,
    jp_fvar: FVarId,
) -> Alt {
    let ctor_let = LetDecl::new(
        ctor_fvar,
        name("t"),
        nat_type(),
        LetValue::Ctor {
            name: ctor_name.clone(),
            levels: vec![],
            args: ctor_args,
        },
    );
    let jmp = Code::Jmp {
        jp: jp_fvar,
        args: vec![Arg::FVar(ctor_fvar)],
    };
    Alt::ctor(ctor_name, params, Code::let_bind(ctor_let, jmp))
}

#[test]
fn test_jp_proj_cases_pushes_projection_into_alt() {
    // Pattern:
    //   jp _j (s : Pair) := let r := proj(s, 0); ret r
    //   cases scrutinee of
    //     | Pair.mk a b => let t := Pair.mk(a, b); jmp _j t
    //
    // Expected after transform:
    //   jp _j (r : Nat) := ret r
    //   cases scrutinee of
    //     | Pair.mk a b => jmp _j a    (field 0 = first arg)
    let code = jp_proj_cases(
        fvar(100), // jp fvar
        fvar(101), // jp param
        fvar(102), // proj result
        0,         // proj idx
        Expr::const_str("Pair"),
        nat_type(),
        fvar(1), // scrutinee
        name("Pair"),
        vec![ctor_jmp_alt(
            name("Pair.mk"),
            vec![
                Param::new(fvar(10), name("a"), nat_type()),
                Param::new(fvar(11), name("b"), nat_type()),
            ],
            fvar(50),
            vec![Arg::FVar(fvar(10)), Arg::FVar(fvar(11))],
            fvar(100),
        )],
    );

    let result = struct_proj_cases_in_code(&code);

    // Should be JoinPoint with rewritten parameter and body
    match &result {
        Code::JoinPoint(jp, continuation) => {
            // JP parameter should now be the projection result (fvar 102)
            assert_eq!(jp.params.len(), 1);
            assert_eq!(jp.params[0].fvar_id, fvar(102));

            // JP body should be just `ret r` (projection removed)
            assert_eq!(*jp.body, Code::ret(fvar(102)));

            // Continuation should be Cases with rewritten alt
            match continuation.as_ref() {
                Code::Cases(cases) => {
                    assert_eq!(cases.alts.len(), 1);
                    // Alt body should be `jmp _j a` (field 0 = fvar(10))
                    match cases.alts[0].body() {
                        Code::Jmp { jp, args } => {
                            assert_eq!(*jp, fvar(100));
                            assert_eq!(args.len(), 1);
                            assert!(matches!(&args[0], Arg::FVar(f) if *f == fvar(10)));
                        }
                        other => panic!("expected jmp, got {other:?}"),
                    }
                }
                other => panic!("expected cases, got {other:?}"),
            }
        }
        other => panic!("expected JoinPoint, got {other:?}"),
    }
}

#[test]
fn test_jp_proj_cases_selects_correct_field_index() {
    // Same pattern but projecting field index 1 instead of 0
    let code = jp_proj_cases(
        fvar(100),
        fvar(101),
        fvar(102),
        1, // proj idx = 1
        Expr::const_str("Pair"),
        nat_type(),
        fvar(1),
        name("Pair"),
        vec![ctor_jmp_alt(
            name("Pair.mk"),
            vec![
                Param::new(fvar(10), name("a"), nat_type()),
                Param::new(fvar(11), name("b"), nat_type()),
            ],
            fvar(50),
            vec![Arg::FVar(fvar(10)), Arg::FVar(fvar(11))],
            fvar(100),
        )],
    );

    let result = struct_proj_cases_in_code(&code);

    match &result {
        Code::JoinPoint(_, continuation) => match continuation.as_ref() {
            Code::Cases(cases) => match cases.alts[0].body() {
                Code::Jmp { args, .. } => {
                    // Should pass field 1 = fvar(11) = "b"
                    assert!(matches!(&args[0], Arg::FVar(f) if *f == fvar(11)));
                }
                other => panic!("expected jmp, got {other:?}"),
            },
            other => panic!("expected cases, got {other:?}"),
        },
        other => panic!("expected JoinPoint, got {other:?}"),
    }
}

#[test]
fn test_multi_alt_cases_without_jp_are_unchanged() {
    // Plain Cases without a JP wrapper — should be unchanged
    let code = Code::cases(
        name("Bool"),
        nat_type(),
        fvar(1),
        vec![
            Alt::ctor(name("Bool.true"), vec![], Code::ret(fvar(10))),
            Alt::ctor(name("Bool.false"), vec![], Code::ret(fvar(11))),
        ],
    );

    assert_eq!(struct_proj_cases_in_code(&code), code);
}

#[test]
fn test_jp_with_multiple_params_is_not_transformed() {
    // JP with 2 params — should NOT be transformed (pass requires exactly 1 param)
    let jp_body = Code::ret(fvar(102));
    let jp_decl = FunDecl::new(
        fvar(100),
        name("_j"),
        vec![
            Param::new(fvar(101), name("a"), nat_type()),
            Param::new(fvar(102), name("b"), nat_type()),
        ],
        nat_type(),
        jp_body,
    );

    let cases = Code::cases(
        name("Pair"),
        nat_type(),
        fvar(1),
        vec![ctor_jmp_alt(
            name("Pair.mk"),
            vec![
                Param::new(fvar(10), name("x"), nat_type()),
                Param::new(fvar(11), name("y"), nat_type()),
            ],
            fvar(50),
            vec![Arg::FVar(fvar(10)), Arg::FVar(fvar(11))],
            fvar(100),
        )],
    );

    let code = Code::JoinPoint(jp_decl, Box::new(cases));
    let result = struct_proj_cases_in_code(&code);

    // Should be unchanged structurally (JP with 2 params)
    match &result {
        Code::JoinPoint(jp, _) => {
            assert_eq!(jp.params.len(), 2);
        }
        other => panic!("expected unchanged JoinPoint, got {other:?}"),
    }
}

#[test]
fn test_jp_without_proj_body_is_not_transformed() {
    // JP body doesn't start with a projection — should NOT be transformed
    let jp_body = Code::ret(fvar(101));
    let jp_decl = FunDecl::new(
        fvar(100),
        name("_j"),
        vec![Param::new(fvar(101), name("s"), Expr::const_str("Pair"))],
        nat_type(),
        jp_body,
    );

    let cases = Code::cases(
        name("Pair"),
        nat_type(),
        fvar(1),
        vec![ctor_jmp_alt(
            name("Pair.mk"),
            vec![
                Param::new(fvar(10), name("a"), nat_type()),
                Param::new(fvar(11), name("b"), nat_type()),
            ],
            fvar(50),
            vec![Arg::FVar(fvar(10)), Arg::FVar(fvar(11))],
            fvar(100),
        )],
    );

    let code = Code::JoinPoint(jp_decl, Box::new(cases));
    let result = struct_proj_cases_in_code(&code);

    // Should be unchanged
    match &result {
        Code::JoinPoint(jp, _) => {
            assert_eq!(jp.params.len(), 1);
            assert_eq!(*jp.body, Code::ret(fvar(101)));
        }
        other => panic!("expected unchanged JoinPoint, got {other:?}"),
    }
}
