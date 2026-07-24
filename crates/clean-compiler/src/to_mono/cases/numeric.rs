// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use crate::lcnf::{Alt, Arg, Cases, Code, LetDecl, LetValue};
use clean_kernel::{Environment, Expr, FVarId, Name};

use crate::to_mono::let_code::code_to_mono_with_depth;
use crate::to_mono::names::special_names;
use crate::to_mono::{to_mono_type, ToMonoState};

/// Transform Nat cases to Bool cases.
///
/// Converts:
/// ```text
/// cases n of
/// | Nat.zero => k_zero
/// | Nat.succ p => k_succ
/// ```
/// To:
/// ```text
/// let zero := 0
/// let isZero := Nat.decEq n zero
/// cases isZero of
/// | Bool.true => k_zero
/// | Bool.false => let one := 1; let p := Nat.sub n one; k_succ
/// ```
pub(crate) fn cases_nat_to_mono(
    cases: &Cases,
    state: &mut ToMonoState,
    next_fvar: &mut u64,
    env: &Environment,
    depth: usize,
) -> Code {
    let result_type = to_mono_type(&cases.result_type);
    let nat_type = Expr::const_(special_names::nat_(), vec![]);

    // let zero := 0
    let zero_fvar = FVarId::new(*next_fvar);
    *next_fvar += 1;
    let zero_decl = LetDecl {
        fvar_id: zero_fvar,
        name: Name::from_string("_zero"),
        ty: nat_type.clone(),
        value: LetValue::nat(0),
    };

    // let isZero := Nat.decEq n zero
    let is_zero_fvar = FVarId::new(*next_fvar);
    *next_fvar += 1;
    let is_zero_decl = LetDecl {
        fvar_id: is_zero_fvar,
        name: Name::from_string("_isZero"),
        ty: Expr::const_(special_names::bool_(), vec![]),
        value: LetValue::Const {
            name: special_names::nat_dec_eq(),
            levels: vec![],
            args: vec![Arg::FVar(cases.scrutinee), Arg::FVar(zero_fvar)],
        },
    };

    // Transform alternatives
    let alts: Vec<_> = cases
        .alts
        .iter()
        .map(|alt| match alt {
            Alt::Ctor {
                ctor_name,
                params,
                body,
            } => {
                if *ctor_name == special_names::nat_succ() {
                    // Nat.succ p => Bool.false with let p := Nat.sub n 1
                    let one_fvar = FVarId::new(*next_fvar);
                    *next_fvar += 1;
                    let one_decl = LetDecl {
                        fvar_id: one_fvar,
                        name: Name::from_string("_one"),
                        ty: nat_type.clone(),
                        value: LetValue::nat(1),
                    };

                    // Reuse param's fvar_id for the subtraction result
                    let p_fvar = params.first().map(|p| p.fvar_id).unwrap_or_else(|| {
                        let fvar = FVarId::new(*next_fvar);
                        *next_fvar += 1;
                        fvar
                    });
                    let sub_decl = LetDecl {
                        fvar_id: p_fvar,
                        name: params
                            .first()
                            .map(|p| p.name.clone())
                            .unwrap_or_else(|| Name::from_string("_pred")),
                        ty: nat_type.clone(),
                        value: LetValue::Const {
                            name: special_names::nat_sub(),
                            levels: vec![],
                            args: vec![Arg::FVar(cases.scrutinee), Arg::FVar(one_fvar)],
                        },
                    };

                    let mono_body = code_to_mono_with_depth(body, state, next_fvar, env, depth + 1);
                    let wrapped_body =
                        Code::Let(one_decl, Box::new(Code::Let(sub_decl, Box::new(mono_body))));

                    Alt::Ctor {
                        ctor_name: special_names::bool_false(),
                        params: vec![],
                        body: Box::new(wrapped_body),
                    }
                } else {
                    // Nat.zero => Bool.true
                    Alt::Ctor {
                        ctor_name: special_names::bool_true(),
                        params: vec![],
                        body: Box::new(code_to_mono_with_depth(
                            body,
                            state,
                            next_fvar,
                            env,
                            depth + 1,
                        )),
                    }
                }
            }
            Alt::Default(body) => Alt::Default(Box::new(code_to_mono_with_depth(
                body,
                state,
                next_fvar,
                env,
                depth + 1,
            ))),
        })
        .collect();

    // Wrap: let zero := 0; let isZero := decEq n zero; cases isZero of ...
    let cases_code = Code::Cases(Cases {
        type_name: special_names::bool_(),
        result_type,
        scrutinee: is_zero_fvar,
        alts,
    });

    Code::Let(
        zero_decl,
        Box::new(Code::Let(is_zero_decl, Box::new(cases_code))),
    )
}

/// Transform Int cases to Bool cases (is negative check).
///
/// Converts Int pattern match to Bool branch on sign using Int.decLt.
pub(crate) fn cases_int_to_mono(
    cases: &Cases,
    state: &mut ToMonoState,
    next_fvar: &mut u64,
    env: &Environment,
    depth: usize,
) -> Code {
    let result_type = to_mono_type(&cases.result_type);
    let nat_type = Expr::const_(special_names::nat_(), vec![]);
    let int_type = Expr::const_(special_names::int_(), vec![]);

    // let natZero := 0
    let nat_zero_fvar = FVarId::new(*next_fvar);
    *next_fvar += 1;
    let nat_zero_decl = LetDecl {
        fvar_id: nat_zero_fvar,
        name: Name::from_string("_natZero"),
        ty: nat_type.clone(),
        value: LetValue::nat(0),
    };

    // let intZero := Int.ofNat natZero
    let int_zero_fvar = FVarId::new(*next_fvar);
    *next_fvar += 1;
    let int_zero_decl = LetDecl {
        fvar_id: int_zero_fvar,
        name: Name::from_string("_intZero"),
        ty: int_type,
        value: LetValue::Const {
            name: special_names::int_of_nat(),
            levels: vec![],
            args: vec![Arg::FVar(nat_zero_fvar)],
        },
    };

    // let isNeg := Int.decLt n intZero
    let is_neg_fvar = FVarId::new(*next_fvar);
    *next_fvar += 1;
    let is_neg_decl = LetDecl {
        fvar_id: is_neg_fvar,
        name: Name::from_string("_isNeg"),
        ty: Expr::const_(special_names::bool_(), vec![]),
        value: LetValue::Const {
            name: special_names::int_dec_lt(),
            levels: vec![],
            args: vec![Arg::FVar(cases.scrutinee), Arg::FVar(int_zero_fvar)],
        },
    };

    // Transform alternatives
    let alts: Vec<_> = cases
        .alts
        .iter()
        .map(|alt| match alt {
            Alt::Ctor {
                ctor_name,
                params,
                body,
            } => {
                let p_fvar = params.first().map(|p| p.fvar_id).unwrap_or_else(|| {
                    let fvar = FVarId::new(*next_fvar);
                    *next_fvar += 1;
                    fvar
                });
                let p_name = params
                    .first()
                    .map(|p| p.name.clone())
                    .unwrap_or_else(|| Name::from_string("_n"));

                if *ctor_name == special_names::int_neg_succ() {
                    // Int.negSucc n => Bool.true (is negative)
                    // let abs := Int.natAbs scrutinee
                    // let one := 1
                    // let p := Nat.sub abs one
                    let abs_fvar = FVarId::new(*next_fvar);
                    *next_fvar += 1;
                    let abs_decl = LetDecl {
                        fvar_id: abs_fvar,
                        name: Name::from_string("_abs"),
                        ty: nat_type.clone(),
                        value: LetValue::Const {
                            name: special_names::int_nat_abs(),
                            levels: vec![],
                            args: vec![Arg::FVar(cases.scrutinee)],
                        },
                    };

                    let one_fvar = FVarId::new(*next_fvar);
                    *next_fvar += 1;
                    let one_decl = LetDecl {
                        fvar_id: one_fvar,
                        name: Name::from_string("_one"),
                        ty: nat_type.clone(),
                        value: LetValue::nat(1),
                    };

                    let sub_decl = LetDecl {
                        fvar_id: p_fvar,
                        name: p_name,
                        ty: nat_type.clone(),
                        value: LetValue::Const {
                            name: special_names::nat_sub(),
                            levels: vec![],
                            args: vec![Arg::FVar(abs_fvar), Arg::FVar(one_fvar)],
                        },
                    };

                    let mono_body = code_to_mono_with_depth(body, state, next_fvar, env, depth + 1);
                    let wrapped_body = Code::Let(
                        abs_decl,
                        Box::new(Code::Let(
                            one_decl,
                            Box::new(Code::Let(sub_decl, Box::new(mono_body))),
                        )),
                    );

                    Alt::Ctor {
                        ctor_name: special_names::bool_true(),
                        params: vec![],
                        body: Box::new(wrapped_body),
                    }
                } else {
                    // Int.ofNat n => Bool.false (is non-negative)
                    // let p := Int.natAbs scrutinee
                    let abs_decl = LetDecl {
                        fvar_id: p_fvar,
                        name: p_name,
                        ty: nat_type.clone(),
                        value: LetValue::Const {
                            name: special_names::int_nat_abs(),
                            levels: vec![],
                            args: vec![Arg::FVar(cases.scrutinee)],
                        },
                    };

                    let mono_body = code_to_mono_with_depth(body, state, next_fvar, env, depth + 1);
                    let wrapped_body = Code::Let(abs_decl, Box::new(mono_body));

                    Alt::Ctor {
                        ctor_name: special_names::bool_false(),
                        params: vec![],
                        body: Box::new(wrapped_body),
                    }
                }
            }
            Alt::Default(body) => Alt::Default(Box::new(code_to_mono_with_depth(
                body,
                state,
                next_fvar,
                env,
                depth + 1,
            ))),
        })
        .collect();

    // Wrap: let natZero := 0; let intZero := ...; let isNeg := ...; cases isNeg of ...
    let cases_code = Code::Cases(Cases {
        type_name: special_names::bool_(),
        result_type,
        scrutinee: is_neg_fvar,
        alts,
    });

    Code::Let(
        nat_zero_decl,
        Box::new(Code::Let(
            int_zero_decl,
            Box::new(Code::Let(is_neg_decl, Box::new(cases_code))),
        )),
    )
}
