// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::error::CompilerError;
use crate::ir::{IRArg, IRBody, IRExpr, IRType, VarId};
use crate::lcnf::{Alt, Arg, Code, Decl, LetDecl, LetValue, Param};
use clean_kernel::{Environment, Expr, FVarId, Name};
use std::collections::HashMap;

fn fvar(n: u64) -> FVarId {
    FVarId::new(n)
}

fn name(s: &str) -> Name {
    Name::from_string(s)
}

fn nat_type() -> Expr {
    Expr::const_str("Nat")
}

fn bool_type() -> Expr {
    Expr::const_str("Bool")
}

fn lower_decl_ok(decl: &Decl) -> crate::ir::IRDecl {
    lower_decl(decl)
        .expect("lower_decl should succeed")
        .expect("test declarations are not extern")
}

fn lower_decl_with_env_ok(
    decl: &Decl,
    arities: &HashMap<Name, u16>,
    ctor_env: &HashMap<Name, CtorMeta>,
    inductive_env: &HashMap<Name, CtorMeta>,
) -> crate::ir::IRDecl {
    let (ir_decl, _warnings) = lower_decl_with_env(decl, arities, ctor_env, inductive_env)
        .expect("lower_decl_with_env should succeed");
    ir_decl.expect("test declarations are not extern")
}

fn to_ir_ok(decls: &[Decl]) -> Vec<crate::ir::IRDecl> {
    to_ir(decls).expect("to_ir should succeed")
}

fn to_ir_with_env_ok(decls: &[Decl], env: &Environment) -> Vec<crate::ir::IRDecl> {
    to_ir_with_env(decls, env)
        .expect("to_ir_with_env should succeed")
        .decls
}

#[test]
fn test_lower_simple_return() {
    // def id (x : Nat) : Nat := return x
    let decl = Decl::new(
        name("id"),
        vec![],
        nat_type(),
        vec![Param::new(fvar(0), name("x"), nat_type())],
        Code::ret(fvar(0)),
        false,
    );

    let ir = lower_decl_ok(&decl);
    assert_eq!(ir.name, name("id"));
    assert_eq!(ir.params.len(), 1);
    assert!(matches!(ir.body, IRBody::Ret(IRArg::Var(_))));
}

#[test]
fn test_lower_let_literal() {
    // def const42 : Nat :=
    //   let _1 := 42
    //   return _1
    let decl = Decl::new(
        name("const42"),
        vec![],
        nat_type(),
        vec![],
        Code::let_bind(
            LetDecl::new(fvar(1), name("_1"), nat_type(), LetValue::nat(42)),
            Code::ret(fvar(1)),
        ),
        false,
    );

    let ir = lower_decl_ok(&decl);
    assert!(matches!(ir.body, IRBody::VDecl { .. }));
}

#[test]
fn test_lower_inc_pseudo_op() {
    // def f (x : Nat) : Nat :=
    //   let _inc := _inc(x)
    //   return x
    let decl = Decl::new(
        name("f"),
        vec![],
        nat_type(),
        vec![Param::new(fvar(0), name("x"), nat_type())],
        Code::let_bind(
            LetDecl::new(
                fvar(1),
                name("_inc"),
                Expr::const_str("_"),
                LetValue::Const {
                    name: name("_inc"),
                    levels: vec![],
                    args: vec![Arg::FVar(fvar(0))],
                },
            ),
            Code::ret(fvar(0)),
        ),
        false,
    );

    let ir = lower_decl_ok(&decl);
    // Should have Inc node
    assert!(matches!(ir.body, IRBody::Inc { .. }));
}

#[test]
fn test_lower_dec_pseudo_op() {
    // def f (x : Nat) : Nat :=
    //   let _dec := _dec(x)
    //   return x
    let decl = Decl::new(
        name("f"),
        vec![],
        nat_type(),
        vec![Param::new(fvar(0), name("x"), nat_type())],
        Code::let_bind(
            LetDecl::new(
                fvar(1),
                name("_dec"),
                Expr::const_str("_"),
                LetValue::Const {
                    name: name("_dec"),
                    levels: vec![],
                    args: vec![Arg::FVar(fvar(0))],
                },
            ),
            Code::ret(fvar(0)),
        ),
        false,
    );

    let ir = lower_decl_ok(&decl);
    // Should have Dec node
    assert!(matches!(ir.body, IRBody::Dec { .. }));
}

#[test]
fn test_lower_set_pseudo_op() {
    // def f (x y : Nat) : Nat :=
    //   let _set := _set(x, #1, y)
    //   return x
    let decl = Decl::new(
        name("f"),
        vec![],
        nat_type(),
        vec![
            Param::new(fvar(0), name("x"), nat_type()),
            Param::new(fvar(1), name("y"), nat_type()),
        ],
        Code::let_bind(
            LetDecl::new(
                fvar(2),
                name("_set"),
                Expr::const_str("_"),
                LetValue::Const {
                    name: name("_set"),
                    levels: vec![],
                    args: vec![Arg::FVar(fvar(0)), Arg::Index(1), Arg::FVar(fvar(1))],
                },
            ),
            Code::ret(fvar(0)),
        ),
        false,
    );

    let ir = lower_decl_ok(&decl);
    match &ir.body {
        IRBody::Set { idx, rest, .. } => {
            assert_eq!(*idx, 1);
            assert!(matches!(rest.as_ref(), IRBody::Ret(IRArg::Var(_))));
        }
        _ => panic!("Expected Set"),
    }
}

// Part of #1995: _uset pseudo-op produces USet (not Set).
#[test]
fn test_lower_uset_pseudo_op() {
    // _uset(obj, #1, val) → USet { var, idx: 1, value }
    let decl = Decl::new(
        name("f_uset"),
        vec![],
        nat_type(),
        vec![
            Param::new(fvar(0), name("x"), nat_type()),
            Param::new(fvar(1), name("y"), nat_type()),
        ],
        Code::let_bind(
            LetDecl::new(
                fvar(2),
                name("_uset"),
                Expr::const_str("_"),
                LetValue::Const {
                    name: name("_uset"),
                    levels: vec![],
                    args: vec![Arg::FVar(fvar(0)), Arg::Index(1), Arg::FVar(fvar(1))],
                },
            ),
            Code::ret(fvar(0)),
        ),
        false,
    );

    let ir = lower_decl_ok(&decl);
    match &ir.body {
        IRBody::USet { idx, rest, .. } => {
            assert_eq!(*idx, 1);
            assert!(matches!(rest.as_ref(), IRBody::Ret(IRArg::Var(_))));
        }
        other => panic!("Expected USet, got {:?}", other),
    }
}

// Part of #1995: _sset pseudo-op produces SSet (not Set).
#[test]
fn test_lower_sset_pseudo_op() {
    // _sset(obj, #2, #0, val) → SSet { var, n: 2, offset: 0, value, ty: UInt64 }
    let decl = Decl::new(
        name("f_sset"),
        vec![],
        nat_type(),
        vec![
            Param::new(fvar(0), name("x"), nat_type()),
            Param::new(fvar(1), name("y"), nat_type()),
        ],
        Code::let_bind(
            LetDecl::new(
                fvar(2),
                name("_sset"),
                Expr::const_str("_"),
                LetValue::Const {
                    name: name("_sset"),
                    levels: vec![],
                    args: vec![
                        Arg::FVar(fvar(0)),
                        Arg::Index(2),
                        Arg::Index(0),
                        Arg::FVar(fvar(1)),
                    ],
                },
            ),
            Code::ret(fvar(0)),
        ),
        false,
    );

    let ir = lower_decl_ok(&decl);
    match &ir.body {
        IRBody::SSet {
            n,
            offset,
            ty,
            rest,
            ..
        } => {
            assert_eq!(*n, 2);
            assert_eq!(*offset, 0);
            assert_eq!(*ty, IRType::UInt64);
            assert!(matches!(rest.as_ref(), IRBody::Ret(IRArg::Var(_))));
        }
        other => panic!("Expected SSet, got {:?}", other),
    }
}

// Part of #2123 (Bug 2): _sset with a UInt8-typed value should infer
// IRType::UInt8 instead of defaulting to UInt64.
#[test]
fn test_sset_infers_scalar_type_from_value() {
    // _sset(obj, #1, #0, val) where val : UInt8
    let decl = Decl::new(
        name("f_sset_u8"),
        vec![],
        nat_type(),
        vec![
            Param::new(fvar(0), name("obj"), nat_type()),
            Param::new(fvar(1), name("val"), Expr::const_str("UInt8")),
        ],
        Code::let_bind(
            LetDecl::new(
                fvar(2),
                name("_sset"),
                Expr::const_str("_"),
                LetValue::Const {
                    name: name("_sset"),
                    levels: vec![],
                    args: vec![
                        Arg::FVar(fvar(0)),
                        Arg::Index(1),
                        Arg::Index(0),
                        Arg::FVar(fvar(1)),
                    ],
                },
            ),
            Code::ret(fvar(0)),
        ),
        false,
    );

    let ir = lower_decl_ok(&decl);
    match &ir.body {
        IRBody::SSet { n, offset, ty, .. } => {
            assert_eq!(*n, 1);
            assert_eq!(*offset, 0);
            assert_eq!(
                *ty,
                IRType::UInt8,
                "SSet should infer UInt8 from value's param type, not default to UInt64"
            );
        }
        other => panic!("Expected SSet, got {:?}", other),
    }
}

// Part of #2123: a constructor parameter bound by a Case alternative whose
// type is a non-UInt64 scalar (Bool/UInt8/...) must have its IR type recorded,
// so a `_sset` in the branch body that uses that param infers the true scalar
// width instead of the UInt64 fallback. Without recording the bound param's
// type, the store is silently widened to UInt64 — a miscompilation.
//
// `scalar_field_ty` is the kernel type of the matched constructor field;
// `expected` is the scalar IR type the `_sset` must infer.
fn sset_on_case_bound_param_decl(field_ty: Expr) -> Decl {
    // def f (s : Nat) : Nat :=
    //   cases s of
    //   | C (p : field_ty) =>
    //       let _ := _sset(p_obj, #1, #0, p)   -- p is the bound ctor param
    //       return p_obj
    //
    // fvar(0): scrutinee `s`
    // fvar(1): bound ctor param `p` (the _sset *value*)
    // fvar(2): an object param `p_obj` to act as the _sset *target*
    // fvar(3): the _sset let-binding
    let branch_body = Code::let_bind(
        LetDecl::new(
            fvar(3),
            name("_sset"),
            Expr::const_str("_"),
            LetValue::Const {
                name: name("_sset"),
                levels: vec![],
                args: vec![
                    Arg::FVar(fvar(2)),
                    Arg::Index(1),
                    Arg::Index(0),
                    Arg::FVar(fvar(1)),
                ],
            },
        ),
        Code::ret(fvar(2)),
    );

    let alt = Alt::ctor(
        name("C"),
        vec![Param::new(fvar(1), name("p"), field_ty)],
        branch_body,
    );

    Decl::new(
        name("f_case_sset"),
        vec![],
        nat_type(),
        vec![
            Param::new(fvar(0), name("s"), nat_type()),
            Param::new(fvar(2), name("p_obj"), nat_type()),
        ],
        Code::cases(name("MyInd"), nat_type(), fvar(0), vec![alt]),
        false,
    )
}

// Walk into the single Case alternative's body and extract the SSet scalar type.
fn sset_ty_in_first_alt(body: &IRBody) -> IRType {
    match body {
        IRBody::Case { alts, .. } => {
            let alt = alts.first().expect("expected one ctor alternative");
            match alt.body.as_ref() {
                IRBody::SSet { ty, .. } => ty.clone(),
                other => panic!("expected SSet in alt body, got {:?}", other),
            }
        }
        other => panic!("expected Case, got {:?}", other),
    }
}

#[test]
fn test_case_bound_param_bool_sset_infers_bool() {
    let decl = sset_on_case_bound_param_decl(bool_type());
    let ir = lower_decl_ok(&decl);
    assert_eq!(
        sset_ty_in_first_alt(&ir.body),
        IRType::Bool,
        "Case-bound Bool param must drive SSet scalar type to Bool, not UInt64"
    );
}

#[test]
fn test_case_bound_param_uint8_sset_infers_uint8() {
    let decl = sset_on_case_bound_param_decl(Expr::const_str("UInt8"));
    let ir = lower_decl_ok(&decl);
    assert_eq!(
        sset_ty_in_first_alt(&ir.body),
        IRType::UInt8,
        "Case-bound UInt8 param must drive SSet scalar type to UInt8, not UInt64"
    );
}

#[test]
fn test_case_bound_param_uint64_sset_still_uint64() {
    // A genuine UInt64 field must continue to lower to UInt64 (no regression).
    let decl = sset_on_case_bound_param_decl(Expr::const_str("UInt64"));
    let ir = lower_decl_ok(&decl);
    assert_eq!(
        sset_ty_in_first_alt(&ir.body),
        IRType::UInt64,
        "Case-bound UInt64 param must still lower SSet scalar type to UInt64"
    );
}

#[test]
fn test_case_bound_param_multifield_ctor_sset_infers_per_field() {
    // Multi-field ctor: C (a : UInt64) (b : UInt16). The _sset on `b` must
    // infer UInt16 from b's recorded type, not from a's or the fallback.
    //
    // fvar(0): scrutinee `s`
    // fvar(1): bound ctor param `a : UInt64`
    // fvar(2): bound ctor param `b : UInt16`  (the _sset value)
    // fvar(3): object target `p_obj`
    // fvar(4): the _sset let-binding
    let branch_body = Code::let_bind(
        LetDecl::new(
            fvar(4),
            name("_sset"),
            Expr::const_str("_"),
            LetValue::Const {
                name: name("_sset"),
                levels: vec![],
                args: vec![
                    Arg::FVar(fvar(3)),
                    Arg::Index(1),
                    Arg::Index(0),
                    Arg::FVar(fvar(2)),
                ],
            },
        ),
        Code::ret(fvar(3)),
    );

    let alt = Alt::ctor(
        name("C"),
        vec![
            Param::new(fvar(1), name("a"), Expr::const_str("UInt64")),
            Param::new(fvar(2), name("b"), Expr::const_str("UInt16")),
        ],
        branch_body,
    );

    let decl = Decl::new(
        name("f_case_sset_multi"),
        vec![],
        nat_type(),
        vec![
            Param::new(fvar(0), name("s"), nat_type()),
            Param::new(fvar(3), name("p_obj"), nat_type()),
        ],
        Code::cases(name("MyInd"), nat_type(), fvar(0), vec![alt]),
        false,
    );

    let ir = lower_decl_ok(&decl);
    assert_eq!(
        sset_ty_in_first_alt(&ir.body),
        IRType::UInt16,
        "SSet on second ctor field must infer UInt16 from that field's recorded type"
    );
}

#[test]
fn test_lower_function_call() {
    // def double (x : Nat) : Nat :=
    //   let _1 := Nat.add x x
    //   return _1
    let decl = Decl::new(
        name("double"),
        vec![],
        nat_type(),
        vec![Param::new(fvar(0), name("x"), nat_type())],
        Code::let_bind(
            LetDecl::new(
                fvar(1),
                name("_1"),
                nat_type(),
                LetValue::Const {
                    name: name("Nat.add"),
                    levels: vec![],
                    args: vec![Arg::FVar(fvar(0)), Arg::FVar(fvar(0))],
                },
            ),
            Code::ret(fvar(1)),
        ),
        false,
    );

    let ir = lower_decl_ok(&decl);
    match &ir.body {
        IRBody::VDecl { value, .. } => {
            assert!(matches!(value, IRExpr::Apply { .. }));
        }
        _ => panic!("Expected VDecl"),
    }
}

#[test]
fn test_lower_constructor() {
    // def wrap (x : Nat) : Box Nat :=
    //   let _1 := Box.mk x
    //   return _1
    let decl = Decl::new(
        name("wrap"),
        vec![],
        nat_type(),
        vec![Param::new(fvar(0), name("x"), nat_type())],
        Code::let_bind(
            LetDecl::new(
                fvar(1),
                name("_1"),
                nat_type(),
                LetValue::Ctor {
                    name: name("Box.mk"),
                    levels: vec![],
                    args: vec![Arg::FVar(fvar(0))],
                },
            ),
            Code::ret(fvar(1)),
        ),
        false,
    );

    let ir = lower_decl_ok(&decl);
    match &ir.body {
        IRBody::VDecl { value, .. } => {
            assert!(matches!(value, IRExpr::Ctor { .. }));
        }
        _ => panic!("Expected VDecl"),
    }
}

#[test]
fn test_to_ir_batch() {
    let decl1 = Decl::new(
        name("f1"),
        vec![],
        nat_type(),
        vec![],
        Code::let_bind(
            LetDecl::new(fvar(1), name("_1"), nat_type(), LetValue::nat(1)),
            Code::ret(fvar(1)),
        ),
        false,
    );

    let decl2 = Decl::new(
        name("f2"),
        vec![],
        nat_type(),
        vec![],
        Code::let_bind(
            LetDecl::new(fvar(1), name("_1"), nat_type(), LetValue::nat(2)),
            Code::ret(fvar(1)),
        ),
        false,
    );

    let ir_decls = to_ir_ok(&[decl1, decl2]);
    assert_eq!(ir_decls.len(), 2);
    assert_eq!(ir_decls[0].name, name("f1"));
    assert_eq!(ir_decls[1].name, name("f2"));
}

#[test]
fn test_state_var_binding() {
    let mut state = ToIRState::new();

    let v1 = state.bind_var(fvar(0));
    let v2 = state.bind_var(fvar(1));

    assert_eq!(v1, VarId(0));
    assert_eq!(v2, VarId(1));

    assert!(matches!(state.get_var(fvar(0)), Ok(IRArg::Var(VarId(0)))));
    assert!(matches!(state.get_var(fvar(1)), Ok(IRArg::Var(VarId(1)))));
}

#[test]
fn test_type_conversion() {
    assert_eq!(name_to_ir_type(&name("Bool")), IRType::Bool);
    assert_eq!(name_to_ir_type(&name("Char")), IRType::UInt32);
    assert_eq!(name_to_ir_type(&name("UInt64")), IRType::UInt64);
    assert_eq!(name_to_ir_type(&name("Float")), IRType::Float64);
    assert_eq!(name_to_ir_type(&name("Nat")), IRType::Object);
    assert_eq!(name_to_ir_type(&name("Pair")), IRType::Object);

    assert_eq!(
        expr_to_ir_type(&Expr::const_str("Pair")).expect("nominal runtime types lower"),
        IRType::Object
    );
    assert_eq!(
        expr_to_ir_type(&Expr::bvar(0)).expect("generic binders lower"),
        IRType::Object
    );
    assert_eq!(
        expr_to_ir_type(&Expr::fvar(fvar(99))).expect("generic free vars lower"),
        IRType::Object
    );
}

#[test]
fn test_placeholder_type_is_rejected() {
    assert!(matches!(
        expr_to_ir_type(&Expr::const_str("_")),
        Err(CompilerError::UnsupportedIrType { .. })
    ));
}

// ════════════════════════════════════════════════════════════════════════════
// C4 — uniform boxed lowering for polymorphic/dependent RETURN-position types.
// Return position is calling convention only (no ctor layout is derived from
// it), so the shapes the strict conversion refuses lower as `Object` there.
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_return_position_placeholder_lowers_boxed() {
    use clean_kernel::BinderInfo;
    // The `_` inference-failure placeholder (lifted casesOn/recOn motive
    // lambdas, `Array.data`-class accessors): boxed in return position…
    assert_eq!(
        super::types::expr_to_ir_type_return(&Expr::const_str("_"))
            .expect("`_` lowers boxed in return position"),
        IRType::Object
    );
    // …while VALUE positions keep the #2826 fail-closed rejection
    // (`test_placeholder_type_is_rejected` pins the strict function).

    // Beta-unreduced motive application `(fun x => Nat) y`: head `Lam`.
    let motive_app = Expr::app(
        Expr::lam(BinderInfo::Default, nat_type(), nat_type()),
        Expr::bvar(0),
    );
    assert_eq!(
        super::types::expr_to_ir_type_return(&motive_app)
            .expect("dependent motive application lowers boxed"),
        IRType::Object
    );

    // Scalar and Sort-valued heads are unchanged by the return-position rules:
    // scalars stay scalar, type-level machinery keeps failing closed.
    assert_eq!(
        super::types::expr_to_ir_type_return(&Expr::const_str("UInt32")).unwrap(),
        IRType::UInt32
    );
    assert!(matches!(
        super::types::expr_to_ir_type_return(&Expr::sort(clean_kernel::Level::zero())),
        Err(CompilerError::UnsupportedIrType { .. })
    ));
}

// casesOn-motive class: a lifted `_lambda` decl whose RESULT type could not be
// kernel-inferred (open term) carries the `_` placeholder as its decl type.
// The decl must lower with an `Object` (boxed) return type — the shape that
// blocked ~189 prelude decls at `to_ir` before C4.
#[test]
fn test_decl_with_placeholder_return_type_lowers_object() {
    let decl = Decl::new(
        name("_lifted.Foo.casesOn._lambda.0"),
        vec![],
        Expr::const_str("_"),
        vec![Param::new(fvar(0), name("motive_val"), nat_type())],
        Code::ret(fvar(0)),
        false,
    );
    let ir = lower_decl_ok(&decl);
    assert_eq!(
        ir.return_type,
        IRType::Object,
        "uninferred lifted-lambda result type must lower boxed"
    );
}

// PARAM position stays strict: a `_`-typed param would corrupt the C2 scalar
// dispatch, so the decl keeps failing closed.
#[test]
fn test_decl_with_placeholder_param_type_still_rejected() {
    let decl = Decl::new(
        name("bad_param"),
        vec![],
        nat_type(),
        vec![Param::new(fvar(0), name("x"), Expr::const_str("_"))],
        Code::ret(fvar(0)),
        false,
    );
    assert!(matches!(
        lower_decl(&decl),
        Err(CompilerError::UnsupportedIrType { .. })
    ));
}

// C4 containment: a ctor SCALAR field fed by an Object-typed value has no
// faithful scalar store — refused fail-closed at to_ir, never garbage at a
// backend. The fixture ctor's parent (`Pixel`) is NOT a scalar-repr
// inductive, so the C5b scalar-carrier construction does not claim it and
// the guard must still fire for this genuinely unscalarizable feed.
#[test]
fn test_ctor_scalar_field_from_object_value_refused() {
    let mut ctor_env = HashMap::new();
    ctor_env.insert(
        name("Pixel.mk"),
        CtorMeta {
            num_params: 0,
            tag: 0,
            field_types: vec![IRType::UInt32, IRType::Object],
            num_scalars: 1,
            num_objects: 1,
        },
    );
    let decl = Decl::new(
        name("bad_pixel"),
        vec![],
        nat_type(),
        vec![
            // Object-typed value feeding the UInt32 scalar slot.
            Param::new(fvar(0), name("boxed_val"), nat_type()),
            Param::new(fvar(1), name("payload"), nat_type()),
        ],
        Code::let_bind(
            LetDecl::new(
                fvar(2),
                name("_1"),
                nat_type(),
                LetValue::Ctor {
                    name: name("Pixel.mk"),
                    levels: vec![],
                    args: vec![Arg::FVar(fvar(0)), Arg::FVar(fvar(1))],
                },
            ),
            Code::ret(fvar(2)),
        ),
        false,
    );
    let err = lower_decl_with_env(&decl, &HashMap::new(), &ctor_env, &HashMap::new())
        .expect_err("Object value into scalar ctor slot must be refused");
    assert!(
        matches!(err, CompilerError::BoxedValueInScalarField { .. }),
        "expected BoxedValueInScalarField, got {err:?}"
    );
}

// ── C5b scalar-carrier CONSTRUCTION ──────────────────────────────────────
// A newtype-style ctor of a scalar-repr inductive constructs the unboxed
// scalar itself (the dual of the emitters' C2 carrier projections).

fn char_mk_ctor_env() -> HashMap<Name, CtorMeta> {
    let mut ctor_env = HashMap::new();
    ctor_env.insert(
        name("Char.mk"),
        CtorMeta {
            num_params: 0,
            tag: 0,
            field_types: vec![IRType::UInt32, IRType::Object],
            num_scalars: 1,
            num_objects: 1,
        },
    );
    ctor_env
}

// `Char.mk v h` where `v` is already the `UInt32` carrier is pure renaming:
// no heap ctor, no instruction at all — the result IS `v`, and the
// proof-class `valid` field is dropped from the construction.
#[test]
fn test_char_mk_from_scalar_carrier_is_alias() {
    let decl = Decl::new(
        name("mk_char"),
        vec![],
        Expr::const_str("Char"),
        vec![
            Param::new(fvar(0), name("val"), Expr::const_str("UInt32")),
            Param::new(fvar(1), name("valid"), nat_type()),
        ],
        Code::let_bind(
            LetDecl::new(
                fvar(2),
                name("_1"),
                Expr::const_str("Char"),
                LetValue::Ctor {
                    name: name("Char.mk"),
                    levels: vec![],
                    args: vec![Arg::FVar(fvar(0)), Arg::FVar(fvar(1))],
                },
            ),
            Code::ret(fvar(2)),
        ),
        false,
    );
    let ir = lower_decl_with_env_ok(&decl, &HashMap::new(), &char_mk_ctor_env(), &HashMap::new());
    // The construction emits nothing: the body is a direct return of the
    // carrier param's own VarId.
    let param_var = ir.params[0].0;
    match &ir.body {
        IRBody::Ret(IRArg::Var(v)) => assert_eq!(
            *v, param_var,
            "Char.mk over a UInt32 carrier must alias the carrier value"
        ),
        other => panic!("expected bare Ret of the carrier var, got {other:?}"),
    }
}

// `Char.mk v h` where `v` is an OBJECT-typed value must be REFUSED, never
// raw-`Unbox`ed: `IRType::Object` cannot distinguish a tagged immediate from
// a heap ctor pointer, and no runtime unbox route decodes a heap ctor chain
// (`clean_unbox` is a raw tag shift; `clean_unbox_uint32`'s heap branch
// reads the first field's bytes). An earlier revision emitted
// `IRExpr::Unbox` here and reinterpreted `BitVec.ofFin` pointers as `Char`
// values.
#[test]
fn test_char_mk_from_object_carrier_refused() {
    let decl = Decl::new(
        name("mk_char_boxed"),
        vec![],
        Expr::const_str("Char"),
        vec![
            Param::new(fvar(0), name("boxed_val"), nat_type()),
            Param::new(fvar(1), name("valid"), nat_type()),
        ],
        Code::let_bind(
            LetDecl::new(
                fvar(2),
                name("_1"),
                Expr::const_str("Char"),
                LetValue::Ctor {
                    name: name("Char.mk"),
                    levels: vec![],
                    args: vec![Arg::FVar(fvar(0)), Arg::FVar(fvar(1))],
                },
            ),
            Code::ret(fvar(2)),
        ),
        false,
    );
    let err = lower_decl_with_env(&decl, &HashMap::new(), &char_mk_ctor_env(), &HashMap::new())
        .expect_err("object-typed carrier must be refused, never raw-unboxed");
    assert!(
        matches!(err, CompilerError::ScalarCarrierObjectCarrier { .. }),
        "expected ScalarCarrierObjectCarrier, got {err:?}"
    );
}

// `UInt32.ofBitVec b` over an Object-typed carrier: REFUSED (the dual of
// the Char.mk pin above). Falling through to the generic ctor path would be
// no better — it would heap-box a value whose consumers (C2 projections,
// scalar arithmetic) assume the unboxed-scalar representation.
// Spelled as `LetValue::Const` (the spelling that reaches to_ir for ctors).
#[test]
fn test_uint32_of_bitvec_object_carrier_refused() {
    let mut ctor_env = HashMap::new();
    ctor_env.insert(
        name("UInt32.ofBitVec"),
        CtorMeta {
            num_params: 0,
            tag: 0,
            field_types: vec![IRType::Object],
            num_scalars: 0,
            num_objects: 1,
        },
    );
    let decl = Decl::new(
        name("mk_u32"),
        vec![],
        Expr::const_str("UInt32"),
        vec![Param::new(fvar(0), name("bits"), nat_type())],
        Code::let_bind(
            LetDecl::new(
                fvar(1),
                name("_1"),
                Expr::const_str("UInt32"),
                LetValue::Const {
                    name: name("UInt32.ofBitVec"),
                    levels: vec![],
                    args: vec![Arg::FVar(fvar(0))],
                },
            ),
            Code::ret(fvar(1)),
        ),
        false,
    );
    let err = lower_decl_with_env(&decl, &HashMap::new(), &ctor_env, &HashMap::new())
        .expect_err("object-typed ofBitVec carrier must be refused");
    assert!(
        matches!(err, CompilerError::ScalarCarrierObjectCarrier { .. }),
        "expected ScalarCarrierObjectCarrier, got {err:?}"
    );
}

// THE ADVERSARIAL-REVIEW PIN (C5b soundness): a carrier that is
// AFFIRMATIVELY a heap ctor — here the result of a `BitVec.ofFin` heap
// construction, exactly the real `Char.ofNat`/`UInt32.ofNat` chain — must
// NOT go through the raw-`Unbox` path. The whole decl refuses instead, and
// no `IRExpr::Unbox` is ever fabricated for it.
#[test]
fn test_uint32_of_bitvec_heap_ctor_carrier_never_unboxed() {
    let mut ctor_env = HashMap::new();
    // BitVec has one VALUE-level inductive param (`w : Nat`) and a single
    // `Fin` field — a real heap ctor, nothing tagged about it.
    ctor_env.insert(
        name("BitVec.ofFin"),
        CtorMeta {
            num_params: 1,
            tag: 0,
            field_types: vec![IRType::Object],
            num_scalars: 0,
            num_objects: 1,
        },
    );
    ctor_env.insert(
        name("UInt32.ofBitVec"),
        CtorMeta {
            num_params: 0,
            tag: 0,
            field_types: vec![IRType::Object],
            num_scalars: 0,
            num_objects: 1,
        },
    );
    let decl = Decl::new(
        name("mk_u32_from_heap"),
        vec![],
        Expr::const_str("UInt32"),
        vec![
            Param::new(fvar(0), name("w"), nat_type()),
            Param::new(fvar(1), name("fin"), nat_type()),
        ],
        Code::let_bind(
            LetDecl::new(
                fvar(2),
                name("bv"),
                Expr::const_str("BitVec"),
                LetValue::Const {
                    name: name("BitVec.ofFin"),
                    levels: vec![],
                    args: vec![Arg::FVar(fvar(0)), Arg::FVar(fvar(1))],
                },
            ),
            Code::let_bind(
                LetDecl::new(
                    fvar(3),
                    name("u"),
                    Expr::const_str("UInt32"),
                    LetValue::Const {
                        name: name("UInt32.ofBitVec"),
                        levels: vec![],
                        args: vec![Arg::FVar(fvar(2))],
                    },
                ),
                Code::ret(fvar(3)),
            ),
        ),
        false,
    );
    let err = lower_decl_with_env(&decl, &HashMap::new(), &ctor_env, &HashMap::new())
        .expect_err("heap-ctor carrier must never take the raw-Unbox path");
    assert!(
        matches!(err, CompilerError::ScalarCarrierObjectCarrier { .. }),
        "expected ScalarCarrierObjectCarrier, got {err:?}"
    );
}

// F2 CORRECT PLACEMENT: `Fin.mk n val isLt` — the VALUE-level inductive
// param `n` is a leading spine arg with NO field slot. The lowered ctor
// must store exactly [val, isLt], never [n, val] (the silent-truncation
// corruption this pins against).
#[test]
fn test_fin_mk_value_param_dropped_from_fields() {
    let mut ctor_env = HashMap::new();
    ctor_env.insert(
        name("Fin.mk"),
        CtorMeta {
            num_params: 1,
            tag: 0,
            field_types: vec![IRType::Object, IRType::Object],
            num_scalars: 0,
            num_objects: 2,
        },
    );
    let decl = Decl::new(
        name("mk_fin"),
        vec![],
        Expr::const_str("Fin"),
        vec![
            Param::new(fvar(0), name("n"), nat_type()),
            Param::new(fvar(1), name("val"), nat_type()),
            Param::new(fvar(2), name("isLt"), nat_type()),
        ],
        Code::let_bind(
            LetDecl::new(
                fvar(3),
                name("_1"),
                Expr::const_str("Fin"),
                LetValue::Const {
                    name: name("Fin.mk"),
                    levels: vec![],
                    args: vec![Arg::FVar(fvar(0)), Arg::FVar(fvar(1)), Arg::FVar(fvar(2))],
                },
            ),
            Code::ret(fvar(3)),
        ),
        false,
    );
    let ir = lower_decl_with_env_ok(&decl, &HashMap::new(), &ctor_env, &HashMap::new());
    let val_var = ir.params[1].0;
    let is_lt_var = ir.params[2].0;
    match &ir.body {
        IRBody::VDecl { value, .. } => match value {
            IRExpr::Ctor { info, args } => {
                assert_eq!(info.field_types.len(), 2);
                assert_eq!(
                    args,
                    &vec![IRArg::Var(val_var), IRArg::Var(is_lt_var)],
                    "Fin.mk must store [val, isLt]; the leading param `n` \
                     carries no field slot"
                );
            }
            other => panic!("expected Ctor, got {other:?}"),
        },
        other => panic!("expected VDecl, got {other:?}"),
    }
}

// F2 FAIL-CLOSED: a ctor spine that cannot align (here a PARTIAL
// application — 1 arg for a 1-param + 2-field ctor) is a hard structured
// error in every profile, never a silent truncation.
#[test]
fn test_ctor_spine_misaligned_hard_error() {
    let mut ctor_env = HashMap::new();
    ctor_env.insert(
        name("Fin.mk"),
        CtorMeta {
            num_params: 1,
            tag: 0,
            field_types: vec![IRType::Object, IRType::Object],
            num_scalars: 0,
            num_objects: 2,
        },
    );
    let decl = Decl::new(
        name("partial_fin"),
        vec![],
        Expr::const_str("Fin"),
        vec![Param::new(fvar(0), name("n"), nat_type())],
        Code::let_bind(
            LetDecl::new(
                fvar(1),
                name("_1"),
                Expr::const_str("Fin"),
                LetValue::Const {
                    name: name("Fin.mk"),
                    levels: vec![],
                    args: vec![Arg::FVar(fvar(0))],
                },
            ),
            Code::ret(fvar(1)),
        ),
        false,
    );
    let err = lower_decl_with_env(&decl, &HashMap::new(), &ctor_env, &HashMap::new())
        .expect_err("misaligned ctor spine must be a hard error");
    assert!(
        matches!(err, CompilerError::CtorSpineMisaligned { args: 1, .. }),
        "expected CtorSpineMisaligned, got {err:?}"
    );
}

// C5b hygiene: a `Cases` whose scrutinee VAR is affirmatively `Erased`-typed
// (`let x := ◇; cases x …` — a proof-class value that survived erasure as a
// placeholder) has no faithful branch selection and used to emit an invalid
// module (`clean_ctor_get` on a `u64`). Refused fail-closed at to_ir.
#[test]
fn test_cases_on_erased_typed_var_refused() {
    let decl = Decl::new(
        name("cases_on_erased"),
        vec![],
        nat_type(),
        vec![Param::new(fvar(0), name("a"), nat_type())],
        Code::let_bind(
            LetDecl::new(fvar(1), name("h"), nat_type(), LetValue::Erased),
            Code::cases(
                name("Or"),
                nat_type(),
                fvar(1),
                vec![Alt::Default(Box::new(Code::ret(fvar(0))))],
            ),
        ),
        false,
    );
    let err = lower_decl(&decl).expect_err("cases on an erased-typed var must be refused");
    assert!(
        matches!(err, CompilerError::InvalidErasedCaseScrutinee { .. }),
        "expected InvalidErasedCaseScrutinee, got {err:?}"
    );
}

// PIN THE FAIL-CLOSED DIRECTION: a width-MISMATCHED scalar carrier is not
// claimed by the C5b construction — it falls through to the generic ctor
// path (whose partition/SSet mechanics and C4 guard stay authoritative).
#[test]
fn test_char_mk_width_mismatched_carrier_falls_back() {
    let decl = Decl::new(
        name("mk_char_narrow"),
        vec![],
        Expr::const_str("Char"),
        vec![
            Param::new(fvar(0), name("val8"), Expr::const_str("UInt8")),
            Param::new(fvar(1), name("valid"), nat_type()),
        ],
        Code::let_bind(
            LetDecl::new(
                fvar(2),
                name("_1"),
                Expr::const_str("Char"),
                LetValue::Ctor {
                    name: name("Char.mk"),
                    levels: vec![],
                    args: vec![Arg::FVar(fvar(0)), Arg::FVar(fvar(1))],
                },
            ),
            Code::ret(fvar(2)),
        ),
        false,
    );
    let ir = lower_decl_with_env_ok(&decl, &HashMap::new(), &char_mk_ctor_env(), &HashMap::new());
    // Generic path: a real Ctor allocation (with the scalar split into an
    // SSet chain), NOT an alias or Unbox of the mismatched carrier.
    match &ir.body {
        IRBody::VDecl { value, .. } => assert!(
            matches!(value, IRExpr::Ctor { .. }),
            "mismatched carrier must stay on the generic ctor path, got {value:?}"
        ),
        other => panic!("expected generic Ctor VDecl, got {other:?}"),
    }
}

// Part of #1065 - Missing Code::Unreachable test
#[test]
fn test_lower_unreachable() {
    // def absurd (x : Empty) : Nat :=
    //   unreachable
    let decl = Decl::new(
        name("absurd"),
        vec![],
        nat_type(),
        vec![Param::new(fvar(0), name("x"), Expr::const_str("Empty"))],
        Code::Unreachable(nat_type()),
        false,
    );

    let ir = lower_decl_ok(&decl);
    assert_eq!(ir.name, name("absurd"));
    assert!(matches!(ir.body, IRBody::Unreachable));
}

// Part of #1065 - Missing JoinPoint parameter type verification
// Self-audit round 1: Added rest field verification, fixed comment
#[test]
fn test_lower_join_point_params() {
    use crate::lcnf::FunDecl;

    // def f (x : Nat) : Nat :=
    //   jp cont (y : Bool) : Nat := return x
    //   jmp cont erased  -- erased arg for Bool param
    let jp_fvar = fvar(10);
    let jp_param = Param::new(fvar(1), name("y"), Expr::const_str("Bool"));

    let jp_decl = FunDecl {
        fvar_id: jp_fvar,
        name: name("cont"),
        params: vec![jp_param],
        ty: nat_type(),
        body: Box::new(Code::ret(fvar(0))),
    };

    let decl = Decl::new(
        name("f"),
        vec![],
        nat_type(),
        vec![Param::new(fvar(0), name("x"), nat_type())],
        Code::join_point(jp_decl, Code::jmp(jp_fvar, vec![Arg::Erased])),
        false,
    );

    let ir = lower_decl_ok(&decl);
    match &ir.body {
        IRBody::JDecl {
            params, body, rest, ..
        } => {
            // Verify parameter type is preserved
            assert_eq!(params.len(), 1);
            assert_eq!(params[0].1, IRType::Bool);
            // Verify body is converted (returns outer param x)
            assert!(matches!(body.as_ref(), IRBody::Ret(IRArg::Var(_))));
            // Verify rest is the jmp continuation
            assert!(matches!(rest.as_ref(), IRBody::Jmp { .. }));
        }
        _ => panic!("Expected JDecl"),
    }
}

// Part of #1065 - Missing erased scrutinee with no alternatives test
#[test]
fn test_lower_cases_erased_no_alts() {
    use crate::lcnf::Cases;

    // Unbound scrutinee must fail closed instead of executing a synthetic path.
    let cases = Cases::new(name("Empty"), nat_type(), fvar(99), vec![]);

    let decl = Decl::new(
        name("absurd_match"),
        vec![],
        nat_type(),
        vec![], // No params - fvar(99) remains unbound
        Code::Cases(cases),
        false,
    );

    let err = lower_decl(&decl).expect_err("unbound scrutinee must fail closed");
    assert!(
        matches!(err, CompilerError::UnboundToIrVar { fvar: actual_fvar } if actual_fvar == fvar(99))
    );
}

// Part of #1065, #1976 - Local functions are lambda-lifted before IR lowering
#[test]
fn test_lower_local_function() {
    use crate::lcnf::FunDecl;

    // def f (x : Nat) : Nat :=
    //   fun g (y : Nat) : Nat := return y  -- local function (lambda-lifted)
    //   return x
    let local_fn = FunDecl {
        fvar_id: fvar(10),
        name: name("g"),
        params: vec![Param::new(fvar(1), name("y"), nat_type())],
        ty: nat_type(),
        body: Box::new(Code::ret(fvar(1))),
    };

    let decl = Decl::new(
        name("f"),
        vec![],
        nat_type(),
        vec![Param::new(fvar(0), name("x"), nat_type())],
        Code::fun(local_fn, Code::ret(fvar(0))),
        false,
    );

    // Lambda lifting eliminates Code::Fun before IR lowering, so this succeeds.
    let ir_decl = lower_decl(&decl)
        .expect("lower_decl should succeed after lambda lifting")
        .expect("should not be extern");
    assert_eq!(ir_decl.name, name("f"));
    // The body should be Ret(x) since the local function is lifted out.
    assert!(matches!(ir_decl.body, IRBody::Ret(IRArg::Var(VarId(0)))));
}

// Part of #1976 - Capturing lifted decls must preserve capture param types in to_ir
#[test]
fn test_to_ir_lowers_capturing_lifted_function_with_outer_param_type() {
    use crate::lcnf::FunDecl;

    let local_fn = FunDecl {
        fvar_id: fvar(10),
        name: name("g"),
        params: vec![Param::new(fvar(1), name("y"), nat_type())],
        ty: bool_type(),
        body: Box::new(Code::ret(fvar(0))),
    };

    let decl = Decl::new(
        name("f"),
        vec![],
        bool_type(),
        vec![Param::new(fvar(0), name("flag"), bool_type())],
        Code::fun(local_fn, Code::ret(fvar(0))),
        false,
    );

    let ir_decls = to_ir_ok(&[decl]);
    assert_eq!(ir_decls.len(), 2, "outer decl + lifted local decl");

    let lifted = ir_decls
        .iter()
        .find(|ir_decl| ir_decl.name != name("f"))
        .expect("capturing local function should lower as a second IR decl");

    assert!(
        lifted.name.to_string().contains("g"),
        "lifted decl should preserve the local function name stem"
    );
    assert_eq!(lifted.params.len(), 2);
    assert_eq!(
        lifted.params[0].1,
        IRType::Bool,
        "captured outer Bool param should survive lambda lifting into IR"
    );
    assert_eq!(lifted.params[1].1, IRType::Object);
    assert!(matches!(lifted.body, IRBody::Ret(IRArg::Var(VarId(0)))));
}

// Part of #1930 - Verify unknown FVar/JP now fail closed
#[test]
fn test_unknown_fvar_returns_error() {
    let state = ToIRState::new();
    let result = state.get_var(fvar(42));
    assert!(
        matches!(result, Err(CompilerError::UnboundToIrVar { fvar: actual_fvar }) if actual_fvar == fvar(42))
    );
}

#[test]
fn test_unknown_jp_returns_error() {
    let state = ToIRState::new();
    let result = state.get_jp(fvar(99));
    assert!(matches!(
        result,
        Err(CompilerError::UnboundToIrJoinPoint { fvar: actual_fvar })
            if actual_fvar == fvar(99)
    ));
}

// Part of #1936 - PartialApply generation when args < arity
#[test]
fn test_partial_apply_from_const_with_arities() {
    // Scenario: List.map has arity 3 (type, fn, list), but is called with 1 arg.
    // This should produce PartialApply, not Apply.
    //
    // def apply_map (f : Nat → Nat) : (List Nat → List Nat) :=
    //   let _1 := List.map f       -- 1 arg, arity 3 → PartialApply
    //   return _1

    // Declare List.map with 3 params (so lower_decls builds arity=3)
    let list_map_decl = Decl::new(
        name("List.map"),
        vec![],
        nat_type(),
        vec![
            Param::new(fvar(100), name("alpha"), nat_type()),
            Param::new(fvar(101), name("f"), nat_type()),
            Param::new(fvar(102), name("xs"), nat_type()),
        ],
        Code::ret(fvar(102)),
        false,
    );

    // Declare caller that partially applies List.map with 1 arg
    let caller_decl = Decl::new(
        name("apply_map"),
        vec![],
        nat_type(),
        vec![Param::new(fvar(0), name("f"), nat_type())],
        Code::let_bind(
            LetDecl::new(
                fvar(1),
                name("_1"),
                nat_type(),
                LetValue::Const {
                    name: name("List.map"),
                    levels: vec![],
                    args: vec![Arg::FVar(fvar(0))],
                },
            ),
            Code::ret(fvar(1)),
        ),
        false,
    );

    let ir_decls = to_ir_ok(&[list_map_decl, caller_decl]);
    assert_eq!(ir_decls.len(), 2);

    // The caller's body should have PartialApply, not Apply
    let caller_ir = &ir_decls[1];
    match &caller_ir.body {
        IRBody::VDecl { value, .. } => match value {
            IRExpr::PartialApply { fn_id, arity, args } => {
                assert_eq!(fn_id.0, name("List.map"));
                assert_eq!(*arity, 3);
                assert_eq!(args.len(), 1);
            }
            other => panic!(
                "Expected PartialApply for under-applied const, got {:?}",
                other
            ),
        },
        _ => panic!("Expected VDecl"),
    }
}

// Part of #1936 - Full application still emits Apply when args == arity
#[test]
fn test_full_apply_when_args_match_arity() {
    // Nat.add has arity 2, called with 2 args → should still be Apply
    let nat_add_decl = Decl::new(
        name("Nat.add"),
        vec![],
        nat_type(),
        vec![
            Param::new(fvar(100), name("a"), nat_type()),
            Param::new(fvar(101), name("b"), nat_type()),
        ],
        Code::ret(fvar(100)),
        false,
    );

    let caller_decl = Decl::new(
        name("double"),
        vec![],
        nat_type(),
        vec![Param::new(fvar(0), name("x"), nat_type())],
        Code::let_bind(
            LetDecl::new(
                fvar(1),
                name("_1"),
                nat_type(),
                LetValue::Const {
                    name: name("Nat.add"),
                    levels: vec![],
                    args: vec![Arg::FVar(fvar(0)), Arg::FVar(fvar(0))],
                },
            ),
            Code::ret(fvar(1)),
        ),
        false,
    );

    let ir_decls = to_ir_ok(&[nat_add_decl, caller_decl]);
    let caller_ir = &ir_decls[1];
    match &caller_ir.body {
        IRBody::VDecl { value, .. } => {
            assert!(
                matches!(value, IRExpr::Apply { .. }),
                "Expected Apply when args == arity, got {:?}",
                value
            );
        }
        _ => panic!("Expected VDecl"),
    }
}

// Part of #1936 - Zero-arg application (thunk) generates PartialApply
#[test]
fn test_zero_arg_partial_apply() {
    // A constant reference with 0 args to a function with arity > 0
    // should produce PartialApply(arity, []).
    let id_decl = Decl::new(
        name("id"),
        vec![],
        nat_type(),
        vec![Param::new(fvar(100), name("x"), nat_type())],
        Code::ret(fvar(100)),
        false,
    );

    let ref_decl = Decl::new(
        name("get_id"),
        vec![],
        nat_type(),
        vec![],
        Code::let_bind(
            LetDecl::new(
                fvar(0),
                name("_1"),
                nat_type(),
                LetValue::Const {
                    name: name("id"),
                    levels: vec![],
                    args: vec![],
                },
            ),
            Code::ret(fvar(0)),
        ),
        false,
    );

    let ir_decls = to_ir_ok(&[id_decl, ref_decl]);
    let ref_ir = &ir_decls[1];
    match &ref_ir.body {
        IRBody::VDecl { value, .. } => match value {
            IRExpr::PartialApply { fn_id, arity, args } => {
                assert_eq!(fn_id.0, name("id"));
                assert_eq!(*arity, 1);
                assert!(args.is_empty());
            }
            other => panic!(
                "Expected PartialApply for 0-arg ref to arity-1 fn, got {:?}",
                other
            ),
        },
        _ => panic!("Expected VDecl"),
    }
}

// Part of #1936 - Unknown function (no arity info) falls back to Apply
#[test]
fn test_unknown_function_falls_back_to_apply() {
    // When lowering a single decl (no cross-decl arity map), unknown
    // functions should produce Apply regardless of arg count.
    let decl = Decl::new(
        name("caller"),
        vec![],
        nat_type(),
        vec![Param::new(fvar(0), name("x"), nat_type())],
        Code::let_bind(
            LetDecl::new(
                fvar(1),
                name("_1"),
                nat_type(),
                LetValue::Const {
                    name: name("Unknown.fn"),
                    levels: vec![],
                    args: vec![Arg::FVar(fvar(0))],
                },
            ),
            Code::ret(fvar(1)),
        ),
        false,
    );

    // lower_decl (single) has no arity info for Unknown.fn
    let ir = lower_decl_ok(&decl);
    match &ir.body {
        IRBody::VDecl { value, .. } => {
            assert!(
                matches!(value, IRExpr::Apply { .. }),
                "Expected Apply for unknown function, got {:?}",
                value
            );
        }
        _ => panic!("Expected VDecl"),
    }
}

// Part of #1936 - FVar application produces ClosureApply (proof_coverage)
#[test]
fn test_fvar_application_produces_closure_apply() {
    // def apply_fn (f : Nat → Nat) (x : Nat) : Nat :=
    //   let _1 := f x        -- FVar application → ClosureApply
    //   return _1
    let decl = Decl::new(
        name("apply_fn"),
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
    );

    let ir = lower_decl_ok(&decl);
    match &ir.body {
        IRBody::VDecl { ty, value, .. } => {
            match value {
                IRExpr::ClosureApply { closure, args } => {
                    // closure should be VarId(0) (param f)
                    assert!(
                        matches!(closure, IRArg::Var(VarId(0))),
                        "Closure should be Var(0), got {:?}",
                        closure
                    );
                    // args should contain VarId(1) (param x)
                    assert_eq!(args.len(), 1);
                    assert!(
                        matches!(args[0], IRArg::Var(VarId(1))),
                        "Arg should be Var(1), got {:?}",
                        args[0]
                    );
                }
                other => panic!(
                    "Expected ClosureApply for FVar application, got {:?}",
                    other
                ),
            }
            // FVar application return type is always Object (type-erased)
            assert_eq!(*ty, IRType::Object);
        }
        _ => panic!("Expected VDecl"),
    }
}

// Part of #1936 - Erased closure callee fails closed.
#[test]
fn test_erased_fvar_returns_error() {
    let decl = Decl::new(
        name("apply_erased"),
        vec![],
        nat_type(),
        vec![Param::new(fvar(0), name("x"), nat_type())],
        Code::let_bind(
            LetDecl::new(
                fvar(2),
                name("_1"),
                nat_type(),
                LetValue::FVar {
                    fvar: fvar(99), // unbound → Erased
                    args: vec![Arg::FVar(fvar(0))],
                },
            ),
            Code::ret(fvar(2)),
        ),
        false,
    );

    let err = lower_decl(&decl).expect_err("erased closure callee must fail closed");
    assert!(
        matches!(err, CompilerError::UnboundToIrVar { fvar: actual_fvar } if actual_fvar == fvar(99))
    );
}

// Part of #1936 - Multi-arg FVar application (proof_coverage)
#[test]
fn test_fvar_multi_arg_closure_apply() {
    // def apply3 (f : A → B → C → D) (a b c : Nat) : Nat :=
    //   let _1 := f a b c     -- 3-arg FVar application
    //   return _1
    let decl = Decl::new(
        name("apply3"),
        vec![],
        nat_type(),
        vec![
            Param::new(fvar(0), name("f"), nat_type()),
            Param::new(fvar(1), name("a"), nat_type()),
            Param::new(fvar(2), name("b"), nat_type()),
            Param::new(fvar(3), name("c"), nat_type()),
        ],
        Code::let_bind(
            LetDecl::new(
                fvar(4),
                name("_1"),
                nat_type(),
                LetValue::FVar {
                    fvar: fvar(0),
                    args: vec![Arg::FVar(fvar(1)), Arg::FVar(fvar(2)), Arg::FVar(fvar(3))],
                },
            ),
            Code::ret(fvar(4)),
        ),
        false,
    );

    let ir = lower_decl_ok(&decl);
    match &ir.body {
        IRBody::VDecl { value, .. } => match value {
            IRExpr::ClosureApply { closure, args } => {
                assert!(matches!(closure, IRArg::Var(VarId(0))));
                assert_eq!(args.len(), 3);
                assert!(matches!(args[0], IRArg::Var(VarId(1))));
                assert!(matches!(args[1], IRArg::Var(VarId(2))));
                assert!(matches!(args[2], IRArg::Var(VarId(3))));
            }
            other => panic!("Expected ClosureApply, got {:?}", other),
        },
        _ => panic!("Expected VDecl"),
    }
}

// Part of #1953 - Constructor with ctor_env uses real tag
#[test]
fn test_ctor_env_provides_correct_tag() {
    // Bool.true should get tag 1 (second constructor), not 0
    let mut ctor_env = HashMap::new();
    ctor_env.insert(
        name("Bool.true"),
        CtorMeta {
            num_params: 0,
            tag: 1,
            field_types: vec![],
            num_scalars: 0,
            num_objects: 0,
        },
    );
    ctor_env.insert(
        name("Bool.false"),
        CtorMeta {
            num_params: 0,
            tag: 0,
            field_types: vec![],
            num_scalars: 0,
            num_objects: 0,
        },
    );

    // def mk_true : Bool := Bool.true
    let decl = Decl::new(
        name("mk_true"),
        vec![],
        Expr::const_str("Bool"),
        vec![],
        Code::let_bind(
            LetDecl::new(
                fvar(0),
                name("_1"),
                Expr::const_str("Bool"),
                LetValue::Ctor {
                    name: name("Bool.true"),
                    levels: vec![],
                    args: vec![],
                },
            ),
            Code::ret(fvar(0)),
        ),
        false,
    );

    let ir = lower_decl_with_env_ok(&decl, &HashMap::new(), &ctor_env, &HashMap::new());
    match &ir.body {
        IRBody::VDecl { value, .. } => match value {
            IRExpr::Ctor { info, .. } => {
                assert_eq!(info.tag, 1, "Bool.true should have tag 1");
                assert_eq!(info.num_objects, 0);
                assert_eq!(info.num_scalars, 0);
            }
            other => panic!("Expected Ctor, got {:?}", other),
        },
        _ => panic!("Expected VDecl"),
    }
}

// Part of #1953 - Constructor with scalar fields gets correct counts
#[test]
fn test_ctor_env_scalar_field_counts() {
    // A constructor with mixed scalar and object fields
    let mut ctor_env = HashMap::new();
    ctor_env.insert(
        name("Pair.mk"),
        CtorMeta {
            num_params: 0,
            tag: 0,
            field_types: vec![IRType::UInt64, IRType::Object],
            num_scalars: 1,
            num_objects: 1,
        },
    );

    let decl = Decl::new(
        name("mk_pair"),
        vec![],
        nat_type(),
        vec![
            // `a` feeds the ctor's UInt64 SCALAR field, so its declared type
            // must BE that scalar (C4: an Object-typed value into a scalar
            // slot is refused fail-closed — `BoxedValueInScalarField`; the
            // partition mechanics under test here are unchanged).
            Param::new(fvar(0), name("a"), Expr::const_str("UInt64")),
            Param::new(fvar(1), name("b"), nat_type()),
        ],
        Code::let_bind(
            LetDecl::new(
                fvar(2),
                name("_1"),
                nat_type(),
                LetValue::Ctor {
                    name: name("Pair.mk"),
                    levels: vec![],
                    args: vec![Arg::FVar(fvar(0)), Arg::FVar(fvar(1))],
                },
            ),
            Code::ret(fvar(2)),
        ),
        false,
    );

    let ir = lower_decl_with_env_ok(&decl, &HashMap::new(), &ctor_env, &HashMap::new());
    // Fix #1993: Ctor.args should only contain object args.
    // Scalar args are emitted as SSet instructions after the VDecl.
    match &ir.body {
        IRBody::VDecl {
            var: ctor_var,
            value,
            rest,
            ..
        } => {
            match value {
                IRExpr::Ctor { info, args } => {
                    assert_eq!(info.tag, 0);
                    assert_eq!(info.num_scalars, 1);
                    assert_eq!(info.num_objects, 1);
                    assert_eq!(info.field_types, vec![IRType::UInt64, IRType::Object]);
                    // Only the object arg remains in Ctor.args
                    assert_eq!(
                        args.len(),
                        1,
                        "Ctor.args should only contain object args, got {}",
                        args.len()
                    );
                }
                other => panic!("Expected Ctor, got {:?}", other),
            }
            // Verify SSet follows for the scalar field (UInt64)
            match rest.as_ref() {
                IRBody::SSet {
                    var, n, offset, ty, ..
                } => {
                    assert_eq!(*var, *ctor_var, "SSet var must match Ctor var");
                    assert_eq!(*n, 1, "SSet n should be num_objects (1)");
                    assert_eq!(*offset, 0, "First scalar field at offset 0");
                    assert_eq!(*ty, IRType::UInt64, "Scalar type should be UInt64");
                }
                other => panic!("Expected SSet after Ctor VDecl, got {:?}", other),
            }
        }
        _ => panic!("Expected VDecl"),
    }
}

// Part of #1993 - Multiple scalar fields get correct SSet offset accumulation
#[test]
fn test_ctor_multiple_scalars_offset_accumulation() {
    // Triple with 1 object + UInt32 (4 bytes) + UInt64 (8 bytes)
    // SSet for UInt32: n=1, offset=0
    // SSet for UInt64: n=1, offset=4  (after 4 bytes of UInt32)
    let mut ctor_env = HashMap::new();
    ctor_env.insert(
        name("Triple.mk"),
        CtorMeta {
            num_params: 0,
            tag: 0,
            field_types: vec![IRType::Object, IRType::UInt32, IRType::UInt64],
            num_scalars: 2,
            num_objects: 1,
        },
    );

    let decl = Decl::new(
        name("mk_triple"),
        vec![],
        nat_type(),
        vec![
            Param::new(fvar(0), name("obj"), nat_type()),
            Param::new(fvar(1), name("u32_val"), Expr::const_str("UInt32")),
            Param::new(fvar(2), name("u64_val"), Expr::const_str("UInt64")),
        ],
        Code::let_bind(
            LetDecl::new(
                fvar(3),
                name("_1"),
                nat_type(),
                LetValue::Ctor {
                    name: name("Triple.mk"),
                    levels: vec![],
                    args: vec![Arg::FVar(fvar(0)), Arg::FVar(fvar(1)), Arg::FVar(fvar(2))],
                },
            ),
            Code::ret(fvar(3)),
        ),
        false,
    );

    let ir = lower_decl_with_env_ok(&decl, &HashMap::new(), &ctor_env, &HashMap::new());
    match &ir.body {
        IRBody::VDecl {
            var: ctor_var,
            value,
            rest,
            ..
        } => {
            // Ctor should only have the object arg
            match value {
                IRExpr::Ctor { args, .. } => {
                    assert_eq!(args.len(), 1, "only object arg in Ctor.args");
                }
                other => panic!("Expected Ctor, got {:?}", other),
            }
            // First SSet: UInt32 at offset 0
            match rest.as_ref() {
                IRBody::SSet {
                    var,
                    n,
                    offset,
                    ty,
                    rest: inner_rest,
                    ..
                } => {
                    assert_eq!(*var, *ctor_var);
                    assert_eq!(*n, 1, "n = num_objects");
                    assert_eq!(*offset, 0, "first scalar at byte offset 0");
                    assert_eq!(*ty, IRType::UInt32);
                    // Second SSet: UInt64 at offset 4 (after UInt32's 4 bytes)
                    match inner_rest.as_ref() {
                        IRBody::SSet {
                            var: var2,
                            n: n2,
                            offset: off2,
                            ty: ty2,
                            ..
                        } => {
                            assert_eq!(*var2, *ctor_var);
                            assert_eq!(*n2, 1, "n = num_objects");
                            assert_eq!(*off2, 4, "second scalar at byte offset 4 (after UInt32)");
                            assert_eq!(*ty2, IRType::UInt64);
                        }
                        other => panic!("Expected second SSet, got {:?}", other),
                    }
                }
                other => panic!("Expected first SSet, got {:?}", other),
            }
        }
        _ => panic!("Expected VDecl"),
    }
}

// Part of #1993 - Reuse with scalar fields generates SSet (proof_coverage)
//
// split_scalar_ctor_args handles both Ctor and Reuse, but prior tests
// only exercised Ctor. This test verifies Reuse produces equivalent SSet.
#[test]
fn test_reuse_scalar_field_generates_sset() {
    // WithScalar has [UInt64, Object]. Reuse should:
    // 1. Keep only Object arg in Reuse.args
    // 2. Generate SSet for UInt64 field
    let mut ctor_env = HashMap::new();
    ctor_env.insert(
        name("WithScalar.mk"),
        CtorMeta {
            num_params: 0,
            tag: 0,
            field_types: vec![IRType::UInt64, IRType::Object],
            num_scalars: 1,
            num_objects: 1,
        },
    );

    let decl = Decl::new(
        name("reuse_scalar"),
        vec![],
        nat_type(),
        vec![
            Param::new(fvar(0), name("slot"), nat_type()),
            Param::new(fvar(1), name("u64_val"), Expr::const_str("UInt64")),
            Param::new(fvar(2), name("obj"), nat_type()),
        ],
        Code::let_bind(
            LetDecl::new(
                fvar(3),
                name("_1"),
                nat_type(),
                LetValue::Reuse {
                    slot: fvar(0),
                    ctor_name: name("WithScalar.mk"),
                    levels: vec![],
                    args: vec![Arg::FVar(fvar(1)), Arg::FVar(fvar(2))],
                },
            ),
            Code::ret(fvar(3)),
        ),
        false,
    );

    let ir = lower_decl_with_env_ok(&decl, &HashMap::new(), &ctor_env, &HashMap::new());
    match &ir.body {
        IRBody::VDecl {
            var: ctor_var,
            value,
            rest,
            ..
        } => {
            // Reuse should only have the object arg
            match value {
                IRExpr::Reuse { ctor, args, .. } => {
                    assert_eq!(ctor.num_scalars, 1);
                    assert_eq!(ctor.num_objects, 1);
                    assert_eq!(
                        args.len(),
                        1,
                        "Reuse.args should only contain object args, got {}",
                        args.len()
                    );
                }
                other => panic!("Expected Reuse, got {:?}", other),
            }
            // SSet for UInt64 at offset 0
            match rest.as_ref() {
                IRBody::SSet {
                    var, n, offset, ty, ..
                } => {
                    assert_eq!(*var, *ctor_var, "SSet var must match Reuse var");
                    assert_eq!(*n, 1, "SSet n should be num_objects (1)");
                    assert_eq!(*offset, 0, "First scalar field at offset 0");
                    assert_eq!(*ty, IRType::UInt64, "Scalar type should be UInt64");
                }
                other => panic!("Expected SSet after Reuse VDecl, got {:?}", other),
            }
        }
        _ => panic!("Expected VDecl"),
    }
}

// Proof_coverage: All-scalar constructor (num_objects=0, num_scalars>0).
//
// partition_ctor_fields must handle the case where ALL fields are scalar
// and no object args remain. Ctor.args should be empty, and SSet/USet
// instructions should write all scalar data. The n parameter in SSet
// should be 0 (no objects, no usizes — assuming non-USize scalars).
#[test]
fn test_ctor_all_scalar_no_objects() {
    let mut ctor_env = HashMap::new();
    ctor_env.insert(
        name("Packed.mk"),
        CtorMeta {
            num_params: 0,
            tag: 0,
            field_types: vec![IRType::UInt32, IRType::UInt64],
            num_scalars: 2,
            num_objects: 0,
        },
    );

    let decl = Decl::new(
        name("mk_packed"),
        vec![],
        nat_type(),
        vec![
            Param::new(fvar(0), name("a"), Expr::const_str("UInt32")),
            Param::new(fvar(1), name("b"), Expr::const_str("UInt64")),
        ],
        Code::let_bind(
            LetDecl::new(
                fvar(2),
                name("_1"),
                nat_type(),
                LetValue::Ctor {
                    name: name("Packed.mk"),
                    levels: vec![],
                    args: vec![Arg::FVar(fvar(0)), Arg::FVar(fvar(1))],
                },
            ),
            Code::ret(fvar(2)),
        ),
        false,
    );

    let ir = lower_decl_with_env_ok(&decl, &HashMap::new(), &ctor_env, &HashMap::new());
    match &ir.body {
        IRBody::VDecl {
            var: ctor_var,
            value,
            rest,
            ..
        } => {
            // Ctor should have NO args (all scalar, extracted to SSet)
            match value {
                IRExpr::Ctor { info, args } => {
                    assert_eq!(info.num_objects, 0);
                    assert_eq!(info.num_scalars, 2);
                    assert_eq!(args.len(), 0, "all-scalar Ctor should have empty args");
                }
                other => panic!("Expected Ctor, got {:?}", other),
            }
            // First SSet: UInt32 at n=0, offset=0
            match rest.as_ref() {
                IRBody::SSet {
                    var,
                    n,
                    offset,
                    ty,
                    rest: inner_rest,
                    ..
                } => {
                    assert_eq!(*var, *ctor_var);
                    assert_eq!(*n, 0, "n = num_objects(0) + num_usizes(0) = 0");
                    assert_eq!(*offset, 0, "first scalar at byte offset 0");
                    assert_eq!(*ty, IRType::UInt32);
                    // Second SSet: UInt64 at n=0, offset=4
                    match inner_rest.as_ref() {
                        IRBody::SSet {
                            var: var2,
                            n: n2,
                            offset: off2,
                            ty: ty2,
                            ..
                        } => {
                            assert_eq!(*var2, *ctor_var);
                            assert_eq!(*n2, 0, "n = 0 (all-scalar)");
                            assert_eq!(*off2, 4, "second scalar at byte offset 4 (after UInt32)");
                            assert_eq!(*ty2, IRType::UInt64);
                        }
                        other => panic!("Expected second SSet, got {:?}", other),
                    }
                }
                other => panic!("Expected first SSet, got {:?}", other),
            }
        }
        _ => panic!("Expected VDecl"),
    }
}

// Proof_coverage: Ctor with erased (proof) arg preceding scalar field.
//
// When L5CNF Ctor args include Arg::Erased (proof term) before a scalar
// field, lower_ctor_args filters the Erased arg but field_types retains
// the proof field's type (IRType::Object). align_ctor_field_types filters
// field_types to match non-erased args, so partition_ctor_fields correctly
// identifies the UInt64 value as scalar and generates an SSet.
//
// This test verifies correct behavior when a proof field comes before
// a scalar field. The test models:
//   structure ProofFirst where (proof : Prop_val) (data : UInt64)
//   field_types = [Object, UInt64], args = [Erased, FVar(data)]
//   After alignment: field_types = [UInt64], args = [Var(data)]
//   Result: Ctor has 0 object args, SSet generated for UInt64 scalar.
// Fix: Part of #2123 (Bug 1).
#[test]
fn test_ctor_erased_before_scalar_misalignment() {
    let mut ctor_env = HashMap::new();
    ctor_env.insert(
        name("ProofFirst.mk"),
        CtorMeta {
            num_params: 0,
            tag: 0,
            // Proof field mapped to Object by expr_to_ir_type (Prop types
            // are not recognized as Erased), then UInt64 scalar.
            field_types: vec![IRType::Object, IRType::UInt64],
            num_scalars: 1,
            num_objects: 1,
        },
    );

    let decl = Decl::new(
        name("mk_proof_first"),
        vec![],
        nat_type(),
        vec![Param::new(fvar(0), name("data"), Expr::const_str("UInt64"))],
        Code::let_bind(
            LetDecl::new(
                fvar(1),
                name("_1"),
                nat_type(),
                LetValue::Ctor {
                    name: name("ProofFirst.mk"),
                    levels: vec![],
                    // Proof field is Erased, data field is FVar
                    args: vec![Arg::Erased, Arg::FVar(fvar(0))],
                },
            ),
            Code::ret(fvar(1)),
        ),
        false,
    );

    let ir = lower_decl_with_env_ok(&decl, &HashMap::new(), &ctor_env, &HashMap::new());
    match &ir.body {
        IRBody::VDecl {
            var: _ctor_var,
            value,
            rest,
            ..
        } => {
            match value {
                IRExpr::Ctor { info, args } => {
                    // After alignment, field_types excludes the erased proof field.
                    assert_eq!(info.field_types, vec![IRType::UInt64]);
                    assert_eq!(info.num_scalars, 1);
                    assert_eq!(info.num_objects, 0);
                    // No object args — the UInt64 value is split into SSet.
                    assert_eq!(
                        args.len(),
                        0,
                        "UInt64 data should be extracted as scalar, not kept as object arg"
                    );
                }
                other => panic!("Expected Ctor, got {:?}", other),
            }
            // SSet should be generated for the UInt64 scalar field.
            let has_sset = matches!(rest.as_ref(), IRBody::SSet { .. });
            assert!(has_sset, "SSet should be generated for UInt64 scalar field");
        }
        _ => panic!("Expected VDecl"),
    }
}

// Self-audit W1-1266 F1: USize fields generate USet (not SSet) and
// non-USize scalars use n = num_objects + num_usizes.
#[test]
fn test_ctor_usize_field_generates_uset_not_sset() {
    // WithUSize.mk has [Object, USize, UInt32]:
    // - Object → Ctor.args
    // - USize  → USet { idx: num_objects + 0 = 1 }
    // - UInt32 → SSet { n: num_objects + num_usizes = 2, offset: 0 }
    let mut ctor_env = HashMap::new();
    ctor_env.insert(
        name("WithUSize.mk"),
        CtorMeta {
            num_params: 0,
            tag: 0,
            field_types: vec![IRType::Object, IRType::USize, IRType::UInt32],
            num_scalars: 2,
            num_objects: 1,
        },
    );

    let decl = Decl::new(
        name("mk_with_usize"),
        vec![],
        nat_type(),
        vec![
            Param::new(fvar(0), name("obj"), nat_type()),
            Param::new(fvar(1), name("us"), Expr::const_str("USize")),
            Param::new(fvar(2), name("u32v"), Expr::const_str("UInt32")),
        ],
        Code::let_bind(
            LetDecl::new(
                fvar(3),
                name("_1"),
                nat_type(),
                LetValue::Ctor {
                    name: name("WithUSize.mk"),
                    levels: vec![],
                    args: vec![Arg::FVar(fvar(0)), Arg::FVar(fvar(1)), Arg::FVar(fvar(2))],
                },
            ),
            Code::ret(fvar(3)),
        ),
        false,
    );

    let ir = lower_decl_with_env_ok(&decl, &HashMap::new(), &ctor_env, &HashMap::new());
    match &ir.body {
        IRBody::VDecl {
            var: ctor_var,
            value,
            rest,
            ..
        } => {
            // Ctor.args should only have the object arg
            match value {
                IRExpr::Ctor { args, .. } => {
                    assert_eq!(args.len(), 1, "only object arg in Ctor.args");
                }
                other => panic!("Expected Ctor, got {:?}", other),
            }
            // First: USet for the USize field
            match rest.as_ref() {
                IRBody::USet {
                    var,
                    idx,
                    value: _,
                    rest: inner,
                } => {
                    assert_eq!(*var, *ctor_var, "USet var matches Ctor var");
                    assert_eq!(*idx, 1, "USize slot idx = num_objects(1) + usize_slot(0)");
                    // Next: SSet for the UInt32 field
                    match inner.as_ref() {
                        IRBody::SSet {
                            var: svar,
                            n,
                            offset,
                            ty,
                            ..
                        } => {
                            assert_eq!(*svar, *ctor_var, "SSet var matches Ctor var");
                            assert_eq!(*n, 2, "SSet n = num_objects(1) + num_usizes(1) = 2");
                            assert_eq!(*offset, 0, "first non-USize scalar at offset 0");
                            assert_eq!(*ty, IRType::UInt32);
                        }
                        other => panic!("Expected SSet after USet, got {:?}", other),
                    }
                }
                other => panic!("Expected USet after Ctor VDecl, got {:?}", other),
            }
        }
        _ => panic!("Expected VDecl"),
    }
}

// Part of #1953 - Without ctor_env, falls back to tag=0 (backward compat)
#[test]
fn test_ctor_without_env_falls_back_to_zero() {
    // Without ctor_env, existing behavior is preserved
    let decl = Decl::new(
        name("wrap"),
        vec![],
        nat_type(),
        vec![Param::new(fvar(0), name("x"), nat_type())],
        Code::let_bind(
            LetDecl::new(
                fvar(1),
                name("_1"),
                nat_type(),
                LetValue::Ctor {
                    name: name("Box.mk"),
                    levels: vec![],
                    args: vec![Arg::FVar(fvar(0))],
                },
            ),
            Code::ret(fvar(1)),
        ),
        false,
    );

    let ir = lower_decl_ok(&decl);
    match &ir.body {
        IRBody::VDecl { value, .. } => match value {
            IRExpr::Ctor { info, .. } => {
                assert_eq!(info.tag, 0, "Fallback should use tag=0");
                assert_eq!(info.num_scalars, 0);
                assert_eq!(info.num_objects, 1);
            }
            other => panic!("Expected Ctor, got {:?}", other),
        },
        _ => panic!("Expected VDecl"),
    }
}

// Part of #1953 - Alt::Ctor in case uses ctor_env for tag
#[test]
fn test_case_alt_uses_ctor_env_tag() {
    use crate::lcnf::Cases;

    let mut ctor_env = HashMap::new();
    ctor_env.insert(
        name("Nat.zero"),
        CtorMeta {
            num_params: 0,
            tag: 0,
            field_types: vec![],
            num_scalars: 0,
            num_objects: 0,
        },
    );
    ctor_env.insert(
        name("Nat.succ"),
        CtorMeta {
            num_params: 0,
            tag: 1,
            field_types: vec![IRType::Object],
            num_scalars: 0,
            num_objects: 1,
        },
    );

    let cases = Cases::new(
        name("Nat"),
        nat_type(),
        fvar(0),
        vec![
            Alt::Ctor {
                ctor_name: name("Nat.zero"),
                params: vec![],
                body: Box::new(Code::ret(fvar(0))),
            },
            Alt::Ctor {
                ctor_name: name("Nat.succ"),
                params: vec![Param::new(fvar(1), name("n"), nat_type())],
                body: Box::new(Code::ret(fvar(1))),
            },
        ],
    );

    let decl = Decl::new(
        name("pred"),
        vec![],
        nat_type(),
        vec![Param::new(fvar(0), name("x"), nat_type())],
        Code::Cases(cases),
        false,
    );

    let ir = lower_decl_with_env_ok(&decl, &HashMap::new(), &ctor_env, &HashMap::new());
    match &ir.body {
        IRBody::Case { alts, .. } => {
            assert_eq!(alts.len(), 2);
            assert_eq!(alts[0].ctor.tag, 0, "Nat.zero should have tag 0");
            assert_eq!(alts[0].ctor.num_objects, 0);
            assert_eq!(alts[1].ctor.tag, 1, "Nat.succ should have tag 1");
            assert_eq!(alts[1].ctor.num_objects, 1);
            assert_eq!(alts[1].ctor.field_types, vec![IRType::Object]);
        }
        _ => panic!("Expected Case"),
    }
}

// Part of #1953 - build_ctor_env extracts field types from Pi chain
#[test]
fn test_build_ctor_env_from_constructor_val() {
    use clean_kernel::ConstructorVal;

    // Nat.zero : Nat (no fields, idx 0)
    let zero_ctor = ConstructorVal {
        name: name("Nat.zero"),
        inductive_name: name("Nat"),
        level_params: vec![],
        type_: Expr::const_str("Nat"),
        num_params: 0,
        num_fields: 0,
        constructor_idx: 0,
    };

    // Nat.succ : Nat → Nat (one Object field, idx 1)
    let succ_ctor = ConstructorVal {
        name: name("Nat.succ"),
        inductive_name: name("Nat"),
        level_params: vec![],
        type_: Expr::arrow(Expr::const_str("Nat"), Expr::const_str("Nat")),
        num_params: 0,
        num_fields: 1,
        constructor_idx: 1,
    };

    let (env, inductive_env) =
        build_ctor_env(&[&zero_ctor, &succ_ctor]).expect("ctor env should build");

    let zero_meta = env
        .get(&name("Nat.zero"))
        .expect("Nat.zero should be in env");
    assert_eq!(zero_meta.tag, 0);
    assert_eq!(zero_meta.field_types.len(), 0);
    assert_eq!(zero_meta.num_scalars, 0);
    assert_eq!(zero_meta.num_objects, 0);

    let succ_meta = env
        .get(&name("Nat.succ"))
        .expect("Nat.succ should be in env");
    assert_eq!(succ_meta.tag, 1);
    assert_eq!(succ_meta.field_types.len(), 1);
    assert_eq!(succ_meta.field_types[0], IRType::Object);
    assert_eq!(succ_meta.num_scalars, 0);
    assert_eq!(succ_meta.num_objects, 1);

    // Part of #1941: inductive_env stores tag-0 ctor per inductive type
    let nat_meta = inductive_env
        .get(&name("Nat"))
        .expect("Nat should be in inductive_env");
    assert_eq!(nat_meta.tag, 0, "inductive_env stores first ctor (tag 0)");
    assert_eq!(nat_meta.field_types.len(), 0);
}

// Part of #1953 - build_ctor_env skips type parameters
#[test]
fn test_build_ctor_env_skips_params() {
    use clean_kernel::ConstructorVal;

    // List.cons : {A : Type} → A → List A → List A
    // num_params=1, so the first Pi (A : Type) is skipped.
    // Fields: A (Object), List A (Object)
    use clean_kernel::BinderInfo;
    let cons_ctor = ConstructorVal {
        name: name("List.cons"),
        inductive_name: name("List"),
        level_params: vec![],
        type_: Expr::pi(
            BinderInfo::Implicit,
            Expr::type_(),
            Expr::arrow(
                Expr::const_str("A"),
                Expr::arrow(Expr::const_str("List"), Expr::const_str("List")),
            ),
        ),
        num_params: 1,
        num_fields: 2,
        constructor_idx: 1,
    };

    let (env, _inductive_env) = build_ctor_env(&[&cons_ctor]).expect("ctor env should build");

    let meta = env.get(&name("List.cons")).expect("should be in env");
    assert_eq!(meta.tag, 1);
    assert_eq!(meta.field_types.len(), 2, "2 fields after skipping param");
    assert_eq!(meta.num_objects, 2);
    assert_eq!(meta.num_scalars, 0);
}

// Part of #1973 - build_ctor_env preserves scalar/object partitions for mixed fields
#[test]
fn test_build_ctor_env_classifies_float32_and_object_fields() {
    use clean_kernel::ConstructorVal;

    let mixed_ctor = ConstructorVal {
        name: name("Mixed.mk"),
        inductive_name: name("Mixed"),
        level_params: vec![],
        type_: Expr::arrow(
            Expr::const_str("Float32"),
            Expr::arrow(Expr::const_str("Nat"), Expr::const_str("Mixed")),
        ),
        num_params: 0,
        num_fields: 2,
        constructor_idx: 0,
    };

    let (env, inductive_env) = build_ctor_env(&[&mixed_ctor]).expect("ctor env should build");

    let meta = env
        .get(&name("Mixed.mk"))
        .expect("Mixed.mk should be in env");
    assert_eq!(meta.field_types, vec![IRType::Float32, IRType::Object]);
    assert_eq!(
        meta.num_scalars, 1,
        "Float32 should count as a scalar field"
    );
    assert_eq!(meta.num_objects, 1, "Nat should count as an object field");

    let mixed_inductive = inductive_env
        .get(&name("Mixed"))
        .expect("Mixed should be in inductive_env");
    assert_eq!(
        mixed_inductive.field_types,
        vec![IRType::Float32, IRType::Object]
    );
    assert_eq!(mixed_inductive.num_scalars, 1);
    assert_eq!(mixed_inductive.num_objects, 1);
}

// Part of #1953 - Unknown ctor with non-empty ctor_env produces warning
#[test]
fn test_unknown_ctor_with_env_produces_warning() {
    let mut ctor_env = HashMap::new();
    ctor_env.insert(
        name("Known.mk"),
        CtorMeta {
            num_params: 0,
            tag: 0,
            field_types: vec![],
            num_scalars: 0,
            num_objects: 0,
        },
    );

    let state = ToIRState::with_arities_and_ctors(HashMap::new(), ctor_env, HashMap::new());
    let info = state.make_ctor_info(&name("Unknown.mk"), 1);

    // Should fall back
    assert_eq!(info.tag, 0);
    assert_eq!(info.num_objects, 1);

    // Should produce a warning
    let warnings = state.warnings.borrow();
    assert_eq!(warnings.len(), 1);
    assert!(
        warnings[0].contains("not found in ctor_env"),
        "Warning should mention ctor_env lookup failure, got: {}",
        warnings[0]
    );
}

// Part of #1941, #1982 - Proj lowering uses inductive_env for field type.
// Scalar fields now emit SProj with correct (n, offset) byte addressing.
#[test]
fn test_proj_uses_inductive_env_for_field_type() {
    // Pair.mk has two fields: UInt64 (scalar) and Object
    // Projecting field 0 (UInt64) should emit SProj, not Proj.
    // SProj n = num_objects(1) + num_usizes(0) = 1, offset = 0.
    let mut inductive_env = HashMap::new();
    inductive_env.insert(
        name("Pair"),
        CtorMeta {
            num_params: 0,
            tag: 0,
            field_types: vec![IRType::UInt64, IRType::Object],
            num_scalars: 1,
            num_objects: 1,
        },
    );

    // def get_fst (p : Pair) : UInt64 := Pair.1 p
    let decl = Decl::new(
        name("get_fst"),
        vec![],
        Expr::const_str("UInt64"),
        vec![Param::new(fvar(0), name("p"), Expr::const_str("Pair"))],
        Code::let_bind(
            LetDecl::new(
                fvar(1),
                name("_1"),
                Expr::const_str("UInt64"),
                LetValue::Proj {
                    type_name: name("Pair"),
                    idx: 0,
                    structure: fvar(0),
                },
            ),
            Code::ret(fvar(1)),
        ),
        false,
    );

    let ir = lower_decl_with_env_ok(&decl, &HashMap::new(), &HashMap::new(), &inductive_env);

    match &ir.body {
        IRBody::VDecl { ty, value, .. } => {
            match value {
                IRExpr::SProj {
                    n,
                    offset,
                    ty: sproj_ty,
                    ..
                } => {
                    assert_eq!(*n, 1, "n = num_objects(1) + num_usizes(0)");
                    assert_eq!(*offset, 0, "first scalar field has offset 0");
                    assert_eq!(
                        *sproj_ty,
                        IRType::UInt64,
                        "SProj type should be UInt64 from inductive_env"
                    );
                }
                other => panic!("Expected SProj for scalar field, got {:?}", other),
            }
            assert_eq!(
                *ty,
                IRType::UInt64,
                "Let binding type should match SProj field type"
            );
        }
        _ => panic!("Expected VDecl"),
    }
}

// Part of #1982 - Pair Nat UInt64: snd projection (field 1, UInt64) should
// produce SProj { n: 1, offset: 0 }, NOT raw field index 1.
// This matches the exact scenario from the issue description.
#[test]
fn test_proj_pair_nat_uint64_snd_has_byte_offset_zero() {
    let mut inductive_env = HashMap::new();
    inductive_env.insert(
        name("Pair"),
        CtorMeta {
            num_params: 0,
            tag: 0,
            field_types: vec![IRType::Object, IRType::UInt64],
            num_scalars: 1,
            num_objects: 1,
        },
    );

    // def get_snd (p : Pair Nat UInt64) : UInt64 := Pair.2 p
    let decl = Decl::new(
        name("get_snd"),
        vec![],
        Expr::const_str("UInt64"),
        vec![Param::new(fvar(0), name("p"), Expr::const_str("Pair"))],
        Code::let_bind(
            LetDecl::new(
                fvar(1),
                name("_1"),
                Expr::const_str("UInt64"),
                LetValue::Proj {
                    type_name: name("Pair"),
                    idx: 1,
                    structure: fvar(0),
                },
            ),
            Code::ret(fvar(1)),
        ),
        false,
    );

    let ir = lower_decl_with_env_ok(&decl, &HashMap::new(), &HashMap::new(), &inductive_env);

    match &ir.body {
        IRBody::VDecl { ty, value, .. } => {
            match value {
                IRExpr::SProj {
                    n,
                    offset,
                    ty: sproj_ty,
                    ..
                } => {
                    assert_eq!(*n, 1, "n = num_objects(1) + num_usizes(0)");
                    assert_eq!(
                        *offset, 0,
                        "UInt64 is the first scalar field, byte offset must be 0 not raw idx 1"
                    );
                    assert_eq!(*sproj_ty, IRType::UInt64);
                }
                other => panic!("Expected SProj for UInt64 snd field, got {:?}", other),
            }
            assert_eq!(*ty, IRType::UInt64);
        }
        _ => panic!("Expected VDecl"),
    }
}

// Part of #1941 - Proj falls back to Object without inductive_env
#[test]
fn test_proj_falls_back_to_object_without_inductive_env() {
    // Without inductive_env, Proj should use Object (backward compat)
    let decl = Decl::new(
        name("get_fst"),
        vec![],
        nat_type(),
        vec![Param::new(fvar(0), name("p"), Expr::const_str("Pair"))],
        Code::let_bind(
            LetDecl::new(
                fvar(1),
                name("_1"),
                nat_type(),
                LetValue::Proj {
                    type_name: name("Pair"),
                    idx: 0,
                    structure: fvar(0),
                },
            ),
            Code::ret(fvar(1)),
        ),
        false,
    );

    let ir = lower_decl_ok(&decl);
    match &ir.body {
        IRBody::VDecl { ty, value, .. } => {
            match value {
                IRExpr::Proj { ty: proj_ty, .. } => {
                    assert_eq!(
                        *proj_ty,
                        IRType::Object,
                        "Without inductive_env, Proj should default to Object"
                    );
                }
                other => panic!("Expected Proj, got {:?}", other),
            }
            assert_eq!(*ty, IRType::Object);
        }
        _ => panic!("Expected VDecl"),
    }
}

// Part of #1982 - Object field Proj uses object-slot index, not raw LCNF index.
// Triple has fields [UInt64, Object, UInt8]. Projecting field 1 (Object) should
// emit Proj with obj_idx=0 (first object field), not raw idx=1.
#[test]
fn test_proj_object_field_uses_object_slot_index() {
    let mut inductive_env = HashMap::new();
    inductive_env.insert(
        name("Triple"),
        CtorMeta {
            num_params: 0,
            tag: 0,
            field_types: vec![IRType::UInt64, IRType::Object, IRType::UInt8],
            num_scalars: 2,
            num_objects: 1,
        },
    );

    let decl = Decl::new(
        name("get_mid"),
        vec![],
        nat_type(),
        vec![Param::new(fvar(0), name("t"), Expr::const_str("Triple"))],
        Code::let_bind(
            LetDecl::new(
                fvar(1),
                name("_1"),
                nat_type(),
                LetValue::Proj {
                    type_name: name("Triple"),
                    idx: 1,
                    structure: fvar(0),
                },
            ),
            Code::ret(fvar(1)),
        ),
        false,
    );

    let ir = lower_decl_with_env_ok(&decl, &HashMap::new(), &HashMap::new(), &inductive_env);

    match &ir.body {
        IRBody::VDecl { value, .. } => match value {
            IRExpr::Proj { idx, ty, .. } => {
                assert_eq!(
                    *idx, 0,
                    "Object at LCNF idx=1 is obj_slot 0 (first object field)"
                );
                assert_eq!(*ty, IRType::Object);
            }
            other => panic!("Expected Proj for object field, got {:?}", other),
        },
        _ => panic!("Expected VDecl"),
    }
}

// Part of #1982 - Scalar field after object emits SProj with correct byte offset.
// Triple [UInt64, Object, UInt8]: projecting field 2 (UInt8) should give
// SProj { n: 1, offset: 8 } (8 = byte size of preceding UInt64).
#[test]
fn test_proj_scalar_after_object_emits_sproj() {
    let mut inductive_env = HashMap::new();
    inductive_env.insert(
        name("Triple"),
        CtorMeta {
            num_params: 0,
            tag: 0,
            field_types: vec![IRType::UInt64, IRType::Object, IRType::UInt8],
            num_scalars: 2,
            num_objects: 1,
        },
    );

    let decl = Decl::new(
        name("get_third"),
        vec![],
        Expr::const_str("UInt8"),
        vec![Param::new(fvar(0), name("t"), Expr::const_str("Triple"))],
        Code::let_bind(
            LetDecl::new(
                fvar(1),
                name("_1"),
                Expr::const_str("UInt8"),
                LetValue::Proj {
                    type_name: name("Triple"),
                    idx: 2,
                    structure: fvar(0),
                },
            ),
            Code::ret(fvar(1)),
        ),
        false,
    );

    let ir = lower_decl_with_env_ok(&decl, &HashMap::new(), &HashMap::new(), &inductive_env);

    match &ir.body {
        IRBody::VDecl { value, ty, .. } => {
            match value {
                IRExpr::SProj {
                    n,
                    offset,
                    ty: sproj_ty,
                    ..
                } => {
                    assert_eq!(*n, 1, "n = num_objects(1) + num_usizes(0)");
                    assert_eq!(*offset, 8, "offset = 8 bytes (preceding UInt64)");
                    assert_eq!(*sproj_ty, IRType::UInt8);
                }
                other => panic!("Expected SProj for UInt8 field, got {:?}", other),
            }
            assert_eq!(*ty, IRType::UInt8);
        }
        _ => panic!("Expected VDecl"),
    }
}

// Part of #1982 - USize field emits UProj with USize-slot index.
#[test]
fn test_proj_usize_field_emits_uproj() {
    let mut inductive_env = HashMap::new();
    inductive_env.insert(
        name("WithUSize"),
        CtorMeta {
            num_params: 0,
            tag: 0,
            field_types: vec![IRType::Object, IRType::USize, IRType::UInt64],
            num_scalars: 2,
            num_objects: 1,
        },
    );

    let decl = Decl::new(
        name("get_usize"),
        vec![],
        Expr::const_str("USize"),
        vec![Param::new(fvar(0), name("w"), Expr::const_str("WithUSize"))],
        Code::let_bind(
            LetDecl::new(
                fvar(1),
                name("_1"),
                Expr::const_str("USize"),
                LetValue::Proj {
                    type_name: name("WithUSize"),
                    idx: 1,
                    structure: fvar(0),
                },
            ),
            Code::ret(fvar(1)),
        ),
        false,
    );

    let ir = lower_decl_with_env_ok(&decl, &HashMap::new(), &HashMap::new(), &inductive_env);

    match &ir.body {
        IRBody::VDecl { value, ty, .. } => {
            match value {
                IRExpr::UProj { idx, .. } => {
                    assert_eq!(*idx, 0, "First USize field has USize-slot index 0");
                }
                other => panic!("Expected UProj for USize field, got {:?}", other),
            }
            assert_eq!(*ty, IRType::USize);
        }
        _ => panic!("Expected VDecl"),
    }
}

// Part of #1982 - compute_proj_expr standalone unit tests.
#[test]
fn test_compute_proj_expr_mixed_fields() {
    // Fields: [Object, UInt64, Object, UInt8, USize]
    let field_types = vec![
        IRType::Object,
        IRType::UInt64,
        IRType::Object,
        IRType::UInt8,
        IRType::USize,
    ];
    let var0 = IRArg::Var(VarId(0));

    // Field 0: Object → Proj { idx: 0 }
    let (expr0, ty0) =
        compute_proj_expr(&name("Pair"), &field_types, 0, var0.clone()).expect("field 0");
    assert!(matches!(expr0, IRExpr::Proj { idx: 0, .. }));
    assert_eq!(ty0, IRType::Object);

    // Field 1: UInt64 → SProj { n: 2+1=3, offset: 0 }
    // n = num_objects(2) + num_usizes(1) = 3
    let (expr1, ty1) =
        compute_proj_expr(&name("Pair"), &field_types, 1, var0.clone()).expect("field 1");
    match expr1 {
        IRExpr::SProj { n, offset, ty, .. } => {
            assert_eq!(n, 3, "n = 2 objects + 1 usize");
            assert_eq!(offset, 0, "first non-USize scalar");
            assert_eq!(ty, IRType::UInt64);
        }
        other => panic!("Expected SProj, got {:?}", other),
    }
    assert_eq!(ty1, IRType::UInt64);

    // Field 2: Object → Proj { idx: 1 } (second object field)
    let (expr2, _) =
        compute_proj_expr(&name("Pair"), &field_types, 2, var0.clone()).expect("field 2");
    assert!(matches!(expr2, IRExpr::Proj { idx: 1, .. }));

    // Field 3: UInt8 → SProj { n: 3, offset: 8 } (after UInt64's 8 bytes)
    let (expr3, ty3) =
        compute_proj_expr(&name("Pair"), &field_types, 3, var0.clone()).expect("field 3");
    match expr3 {
        IRExpr::SProj { n, offset, ty, .. } => {
            assert_eq!(n, 3);
            assert_eq!(offset, 8, "offset = UInt64(8 bytes)");
            assert_eq!(ty, IRType::UInt8);
        }
        other => panic!("Expected SProj, got {:?}", other),
    }
    assert_eq!(ty3, IRType::UInt8);

    // Field 4: USize → UProj { idx: 0 } (first USize field)
    let (expr4, ty4) =
        compute_proj_expr(&name("Pair"), &field_types, 4, var0.clone()).expect("field 4");
    assert!(matches!(expr4, IRExpr::UProj { idx: 0, .. }));
    assert_eq!(ty4, IRType::USize);
}

// Part of #1982 - Out-of-bounds idx fails closed.
#[test]
fn test_compute_proj_expr_out_of_bounds() {
    let field_types = vec![IRType::Object];
    let var0 = IRArg::Var(VarId(0));

    let err = compute_proj_expr(&name("Pair"), &field_types, 5, var0)
        .expect_err("out-of-bounds projection must fail closed");
    assert!(matches!(
        err,
        CompilerError::ProjectionIndexOutOfBounds {
            ref type_name,
            idx,
            field_count
        } if *type_name == name("Pair") && idx == 5 && field_count == 1
    ));
}

// Verifies CtorMeta tag values match InductiveDecl constructor ordering.
// Tests 3-constructor inductive (Ordering: lt=0, eq=1, gt=2) to ensure
// build_ctor_env assigns tags from constructor_idx, not hardcoded values.
#[test]
fn test_ctor_env_ordering_3_constructors_tag_order() {
    use clean_kernel::ConstructorVal;

    let lt_ctor = ConstructorVal {
        name: name("Ordering.lt"),
        inductive_name: name("Ordering"),
        level_params: vec![],
        type_: Expr::const_str("Ordering"),
        num_params: 0,
        num_fields: 0,
        constructor_idx: 0,
    };

    let eq_ctor = ConstructorVal {
        name: name("Ordering.eq"),
        inductive_name: name("Ordering"),
        level_params: vec![],
        type_: Expr::const_str("Ordering"),
        num_params: 0,
        num_fields: 0,
        constructor_idx: 1,
    };

    let gt_ctor = ConstructorVal {
        name: name("Ordering.gt"),
        inductive_name: name("Ordering"),
        level_params: vec![],
        type_: Expr::const_str("Ordering"),
        num_params: 0,
        num_fields: 0,
        constructor_idx: 2,
    };

    let (ctor_env, inductive_env) =
        build_ctor_env(&[&lt_ctor, &eq_ctor, &gt_ctor]).expect("ctor env should build");

    // Verify all 3 constructors present with correct tags
    let lt_meta = ctor_env
        .get(&name("Ordering.lt"))
        .expect("lt should be in ctor_env");
    assert_eq!(lt_meta.tag, 0, "Ordering.lt must be tag 0");
    assert_eq!(lt_meta.field_types.len(), 0);
    assert_eq!(lt_meta.num_scalars, 0);
    assert_eq!(lt_meta.num_objects, 0);

    let eq_meta = ctor_env
        .get(&name("Ordering.eq"))
        .expect("eq should be in ctor_env");
    assert_eq!(eq_meta.tag, 1, "Ordering.eq must be tag 1");
    assert_eq!(eq_meta.field_types.len(), 0);

    let gt_meta = ctor_env
        .get(&name("Ordering.gt"))
        .expect("gt should be in ctor_env");
    assert_eq!(gt_meta.tag, 2, "Ordering.gt must be tag 2");
    assert_eq!(gt_meta.field_types.len(), 0);

    // inductive_env stores only tag-0 constructor per inductive
    let ordering_meta = inductive_env
        .get(&name("Ordering"))
        .expect("Ordering should be in inductive_env");
    assert_eq!(
        ordering_meta.tag, 0,
        "inductive_env should store tag-0 constructor only"
    );

    // Verify inductive_env has exactly 1 entry (not 3)
    assert_eq!(
        inductive_env.len(),
        1,
        "inductive_env should not duplicate entries for multi-constructor types"
    );
}

// Part of #1962 - Reuse with valid slot emits IRExpr::Reuse
#[test]
fn test_reuse_emits_ir_reuse() {
    // def f (slot x : Nat) : Nat :=
    //   let _1 := reuse slot Pair.mk [x, x]
    //   return _1
    let mut ctor_env = HashMap::new();
    ctor_env.insert(
        name("Pair.mk"),
        CtorMeta {
            num_params: 0,
            tag: 0,
            field_types: vec![IRType::Object, IRType::Object],
            num_scalars: 0,
            num_objects: 2,
        },
    );

    let decl = Decl::new(
        name("f"),
        vec![],
        nat_type(),
        vec![
            Param::new(fvar(0), name("slot"), nat_type()),
            Param::new(fvar(1), name("x"), nat_type()),
        ],
        Code::let_bind(
            LetDecl::new(
                fvar(2),
                name("_1"),
                nat_type(),
                LetValue::Reuse {
                    slot: fvar(0),
                    ctor_name: name("Pair.mk"),
                    levels: vec![],
                    args: vec![Arg::FVar(fvar(1)), Arg::FVar(fvar(1))],
                },
            ),
            Code::ret(fvar(2)),
        ),
        false,
    );

    let ir = lower_decl_with_env_ok(&decl, &HashMap::new(), &ctor_env, &HashMap::new());
    match &ir.body {
        IRBody::VDecl { value, .. } => match value {
            IRExpr::Reuse { var, ctor, args } => {
                assert_eq!(*var, VarId(0), "Reuse slot should be VarId(0)");
                assert_eq!(ctor.tag, 0);
                assert_eq!(ctor.num_objects, 2);
                assert_eq!(args.len(), 2);
            }
            other => panic!("Expected IRExpr::Reuse, got {:?}", other),
        },
        _ => panic!("Expected VDecl"),
    }
}

// Part of #1962 - Reuse with erased slot fails closed.
#[test]
fn test_reuse_erased_slot_returns_error() {
    let decl = Decl::new(
        name("f"),
        vec![],
        nat_type(),
        vec![Param::new(fvar(1), name("x"), nat_type())],
        Code::let_bind(
            LetDecl::new(
                fvar(2),
                name("_1"),
                nat_type(),
                LetValue::Reuse {
                    slot: fvar(99), // Unbound → Erased
                    ctor_name: name("Box.mk"),
                    levels: vec![],
                    args: vec![Arg::FVar(fvar(1))],
                },
            ),
            Code::ret(fvar(2)),
        ),
        false,
    );

    let err = lower_decl(&decl).expect_err("reuse with erased slot must fail closed");
    assert!(
        matches!(err, CompilerError::UnboundToIrVar { fvar: actual_fvar } if actual_fvar == fvar(99))
    );
}

// Part of #1965 - Erased type args filtered from constructor IR args
#[test]
fn test_ctor_filters_erased_type_args() {
    // Ctor with type args (Arg::Type) should have those filtered out.
    // List.cons {A} head tail → Ctor args should be [head, tail], not [erased, head, tail].
    // `num_params: 1` models the real `List` (one inductive parameter, `A`);
    // the spine-alignment discipline drops exactly that leading arg.
    let mut ctor_env = HashMap::new();
    ctor_env.insert(
        name("List.cons"),
        CtorMeta {
            num_params: 1,
            tag: 1,
            field_types: vec![IRType::Object, IRType::Object],
            num_scalars: 0,
            num_objects: 2,
        },
    );

    let decl = Decl::new(
        name("mk_cons"),
        vec![],
        nat_type(),
        vec![
            Param::new(fvar(0), name("head"), nat_type()),
            Param::new(fvar(1), name("tail"), nat_type()),
        ],
        Code::let_bind(
            LetDecl::new(
                fvar(2),
                name("_1"),
                nat_type(),
                LetValue::Ctor {
                    name: name("List.cons"),
                    levels: vec![],
                    // Type arg first, then runtime args
                    args: vec![
                        Arg::Type(Expr::const_str("Nat")),
                        Arg::FVar(fvar(0)),
                        Arg::FVar(fvar(1)),
                    ],
                },
            ),
            Code::ret(fvar(2)),
        ),
        false,
    );

    let ir = lower_decl_with_env_ok(&decl, &HashMap::new(), &ctor_env, &HashMap::new());
    match &ir.body {
        IRBody::VDecl { value, .. } => match value {
            IRExpr::Ctor { info, args } => {
                assert_eq!(
                    args.len(),
                    2,
                    "Type arg should be filtered, leaving 2 runtime args"
                );
                assert_eq!(info.tag, 1);
                assert_eq!(info.num_objects, 2);
                // Both args should be Var, not Erased
                assert!(matches!(args[0], IRArg::Var(_)));
                assert!(matches!(args[1], IRArg::Var(_)));
            }
            other => panic!("Expected Ctor, got {:?}", other),
        },
        _ => panic!("Expected VDecl"),
    }
}

// Verifies case lowering uses correct tags from ctor_env for 3+ constructors
#[test]
fn test_case_alt_3_constructors_uses_ctor_env_tags() {
    use clean_kernel::ConstructorVal;

    let lt_ctor = ConstructorVal {
        name: name("Ordering.lt"),
        inductive_name: name("Ordering"),
        level_params: vec![],
        type_: Expr::const_str("Ordering"),
        num_params: 0,
        num_fields: 0,
        constructor_idx: 0,
    };
    let eq_ctor = ConstructorVal {
        name: name("Ordering.eq"),
        inductive_name: name("Ordering"),
        level_params: vec![],
        type_: Expr::const_str("Ordering"),
        num_params: 0,
        num_fields: 0,
        constructor_idx: 1,
    };
    let gt_ctor = ConstructorVal {
        name: name("Ordering.gt"),
        inductive_name: name("Ordering"),
        level_params: vec![],
        type_: Expr::const_str("Ordering"),
        num_params: 0,
        num_fields: 0,
        constructor_idx: 2,
    };

    let (ctor_env, inductive_env) =
        build_ctor_env(&[&lt_ctor, &eq_ctor, &gt_ctor]).expect("ctor env should build");

    let decl = Decl::new(
        name("compare_ordering"),
        vec![],
        nat_type(),
        vec![Param::new(fvar(0), name("o"), Expr::const_str("Ordering"))],
        Code::cases(
            name("Ordering"),
            nat_type(),
            fvar(0),
            vec![
                Alt::ctor(name("Ordering.lt"), vec![], Code::ret(fvar(0))),
                Alt::ctor(name("Ordering.eq"), vec![], Code::ret(fvar(0))),
                Alt::ctor(name("Ordering.gt"), vec![], Code::ret(fvar(0))),
            ],
        ),
        false,
    );

    let ir = lower_decl_with_env_ok(&decl, &HashMap::new(), &ctor_env, &inductive_env);

    match &ir.body {
        IRBody::Case { alts, .. } => {
            assert_eq!(alts.len(), 3, "Should have 3 case alternatives");
            assert_eq!(alts[0].ctor.tag, 0, "Ordering.lt should be case tag 0");
            assert_eq!(alts[1].ctor.tag, 1, "Ordering.eq should be case tag 1");
            assert_eq!(alts[2].ctor.tag, 2, "Ordering.gt should be case tag 2");
        }
        other => panic!("Expected Case, got {:?}", other),
    }
}

// ── End-to-end tests for to_ir_with_env (Part of #1969, #1964) ──────

// Validates the full pipeline: Environment → constructors() → build_ctor_env
// → lower_decls_with_env. Prior tests exercise individual pieces; these
// exercise to_ir_with_env with a real kernel Environment.

fn make_nat_env() -> Environment {
    let mut env = Environment::new();
    let nat = name("Nat");
    let nat_ref = Expr::const_str("Nat");
    env.add_inductive(clean_kernel::InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![clean_kernel::InductiveType {
            name: nat,
            type_: Expr::type_(),
            constructors: vec![
                clean_kernel::Constructor {
                    name: name("Nat.zero"),
                    type_: nat_ref.clone(),
                },
                clean_kernel::Constructor {
                    name: name("Nat.succ"),
                    type_: Expr::arrow(nat_ref.clone(), nat_ref),
                },
            ],
        }],
    })
    .expect("Nat inductive should register");
    env
}

fn make_nat_bool_env() -> Environment {
    let mut env = make_nat_env();
    let bool_ref = Expr::const_str("Bool");
    env.add_inductive(clean_kernel::InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![clean_kernel::InductiveType {
            name: name("Bool"),
            type_: Expr::type_(),
            constructors: vec![
                clean_kernel::Constructor {
                    name: name("Bool.false"),
                    type_: bool_ref.clone(),
                },
                clean_kernel::Constructor {
                    name: name("Bool.true"),
                    type_: bool_ref,
                },
            ],
        }],
    })
    .expect("Bool inductive should register");
    env
}

#[test]
fn test_to_ir_with_env_nat_ctor_tags() {
    // End-to-end: real Environment → to_ir_with_env → correct Nat tags
    let env = make_nat_env();

    // def mk_zero : Nat := Nat.zero
    // def mk_succ (n : Nat) : Nat := Nat.succ n
    let mk_zero = Decl::new(
        name("mk_zero"),
        vec![],
        Expr::const_str("Nat"),
        vec![],
        Code::let_bind(
            LetDecl::new(
                fvar(0),
                name("_1"),
                Expr::const_str("Nat"),
                LetValue::Ctor {
                    name: name("Nat.zero"),
                    levels: vec![],
                    args: vec![],
                },
            ),
            Code::ret(fvar(0)),
        ),
        false,
    );

    let mk_succ = Decl::new(
        name("mk_succ"),
        vec![],
        Expr::const_str("Nat"),
        vec![Param::new(fvar(0), name("n"), Expr::const_str("Nat"))],
        Code::let_bind(
            LetDecl::new(
                fvar(1),
                name("_1"),
                Expr::const_str("Nat"),
                LetValue::Ctor {
                    name: name("Nat.succ"),
                    levels: vec![],
                    args: vec![Arg::FVar(fvar(0))],
                },
            ),
            Code::ret(fvar(1)),
        ),
        false,
    );

    let ir_decls = to_ir_with_env_ok(&[mk_zero, mk_succ], &env);
    assert_eq!(ir_decls.len(), 2);

    // mk_zero: Nat.zero → tag 0, 0 fields
    match &ir_decls[0].body {
        IRBody::VDecl { value, .. } => match value {
            IRExpr::Ctor { info, args } => {
                assert_eq!(info.tag, 0, "Nat.zero tag from real Environment");
                assert_eq!(info.num_objects, 0);
                assert_eq!(info.num_scalars, 0);
                assert_eq!(args.len(), 0);
            }
            other => panic!("Expected Ctor for mk_zero, got {:?}", other),
        },
        other => panic!("Expected VDecl for mk_zero, got {:?}", other),
    }

    // mk_succ: Nat.succ → tag 1, 1 Object field
    match &ir_decls[1].body {
        IRBody::VDecl { value, .. } => match value {
            IRExpr::Ctor { info, args } => {
                assert_eq!(info.tag, 1, "Nat.succ tag from real Environment");
                assert_eq!(info.num_objects, 1);
                assert_eq!(info.num_scalars, 0);
                assert_eq!(info.field_types, vec![IRType::Object]);
                assert_eq!(args.len(), 1);
            }
            other => panic!("Expected Ctor for mk_succ, got {:?}", other),
        },
        other => panic!("Expected VDecl for mk_succ, got {:?}", other),
    }
}

#[test]
fn test_to_ir_with_env_bool_ctor_tags() {
    // End-to-end: real Environment → to_ir_with_env → correct Bool tags
    let env = make_nat_bool_env();

    // def mk_true : Bool := Bool.true
    let mk_true = Decl::new(
        name("mk_true"),
        vec![],
        Expr::const_str("Bool"),
        vec![],
        Code::let_bind(
            LetDecl::new(
                fvar(0),
                name("_1"),
                Expr::const_str("Bool"),
                LetValue::Ctor {
                    name: name("Bool.true"),
                    levels: vec![],
                    args: vec![],
                },
            ),
            Code::ret(fvar(0)),
        ),
        false,
    );

    let mk_false = Decl::new(
        name("mk_false"),
        vec![],
        Expr::const_str("Bool"),
        vec![],
        Code::let_bind(
            LetDecl::new(
                fvar(0),
                name("_1"),
                Expr::const_str("Bool"),
                LetValue::Ctor {
                    name: name("Bool.false"),
                    levels: vec![],
                    args: vec![],
                },
            ),
            Code::ret(fvar(0)),
        ),
        false,
    );

    let ir_decls = to_ir_with_env_ok(&[mk_true, mk_false], &env);
    assert_eq!(ir_decls.len(), 2);

    // Bool.true → tag 1, 0 fields
    match &ir_decls[0].body {
        IRBody::VDecl { value, .. } => match value {
            IRExpr::Ctor { info, args } => {
                assert_eq!(info.tag, 1, "Bool.true should be tag 1");
                assert_eq!(info.num_objects, 0);
                assert_eq!(info.num_scalars, 0);
                assert_eq!(args.len(), 0);
            }
            other => panic!("Expected Ctor for mk_true, got {:?}", other),
        },
        other => panic!("Expected VDecl for mk_true, got {:?}", other),
    }

    // Bool.false → tag 0, 0 fields
    match &ir_decls[1].body {
        IRBody::VDecl { value, .. } => match value {
            IRExpr::Ctor { info, args } => {
                assert_eq!(info.tag, 0, "Bool.false should be tag 0");
                assert_eq!(info.num_objects, 0);
                assert_eq!(info.num_scalars, 0);
                assert_eq!(args.len(), 0);
            }
            other => panic!("Expected Ctor for mk_false, got {:?}", other),
        },
        other => panic!("Expected VDecl for mk_false, got {:?}", other),
    }
}

#[test]
fn test_to_ir_with_env_case_nat_tags() {
    // End-to-end: case match on Nat uses correct tags from Environment
    let env = make_nat_env();

    // def is_zero (n : Nat) : Nat :=
    //   cases n : Nat
    //     | Nat.zero => return n
    //     | Nat.succ (pred : Nat) => return n
    let decl = Decl::new(
        name("is_zero"),
        vec![],
        Expr::const_str("Nat"),
        vec![Param::new(fvar(0), name("n"), Expr::const_str("Nat"))],
        Code::cases(
            name("Nat"),
            Expr::const_str("Nat"),
            fvar(0),
            vec![
                Alt::ctor(name("Nat.zero"), vec![], Code::ret(fvar(0))),
                Alt::ctor(
                    name("Nat.succ"),
                    vec![Param::new(fvar(1), name("pred"), Expr::const_str("Nat"))],
                    Code::ret(fvar(0)),
                ),
            ],
        ),
        false,
    );

    let ir_decls = to_ir_with_env_ok(&[decl], &env);
    assert_eq!(ir_decls.len(), 1);

    match &ir_decls[0].body {
        IRBody::Case { alts, .. } => {
            assert_eq!(alts.len(), 2);
            assert_eq!(alts[0].ctor.tag, 0, "Nat.zero should be tag 0");
            assert_eq!(alts[0].ctor.num_objects, 0);
            assert_eq!(alts[1].ctor.tag, 1, "Nat.succ should be tag 1");
            assert_eq!(alts[1].ctor.num_objects, 1);
            assert_eq!(alts[1].ctor.field_types, vec![IRType::Object]);
        }
        other => panic!("Expected Case, got {:?}", other),
    }
}

#[test]
fn test_to_ir_with_env_proj_field_type() {
    // End-to-end: Proj on a structure (single-ctor inductive) gets correct
    // field types from inductive_env built via real Environment.
    //
    // We register a Pair type with two fields (Nat, Nat) → both Object.
    let mut env = make_nat_env();
    let nat_ref = Expr::const_str("Nat");
    // Pair : Type := Pair.mk (fst snd : Nat)
    env.add_inductive(clean_kernel::InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![clean_kernel::InductiveType {
            name: name("Pair"),
            type_: Expr::type_(),
            constructors: vec![clean_kernel::Constructor {
                name: name("Pair.mk"),
                type_: Expr::arrow(
                    nat_ref.clone(),
                    Expr::arrow(nat_ref, Expr::const_str("Pair")),
                ),
            }],
        }],
    })
    .expect("Pair inductive should register");

    // def get_fst (p : Pair) : Nat := Pair.1 p
    let decl = Decl::new(
        name("get_fst"),
        vec![],
        Expr::const_str("Nat"),
        vec![Param::new(fvar(0), name("p"), Expr::const_str("Pair"))],
        Code::let_bind(
            LetDecl::new(
                fvar(1),
                name("_1"),
                Expr::const_str("Nat"),
                LetValue::Proj {
                    type_name: name("Pair"),
                    idx: 0,
                    structure: fvar(0),
                },
            ),
            Code::ret(fvar(1)),
        ),
        false,
    );

    let ir_decls = to_ir_with_env_ok(&[decl], &env);
    assert_eq!(ir_decls.len(), 1);

    match &ir_decls[0].body {
        IRBody::VDecl { ty, value, .. } => match value {
            IRExpr::Proj {
                idx, ty: proj_ty, ..
            } => {
                assert_eq!(*idx, 0);
                assert_eq!(
                    *proj_ty,
                    IRType::Object,
                    "Nat field should be Object type from inductive_env"
                );
                assert_eq!(ty, &IRType::Object, "Let binding should match proj type");
            }
            other => panic!("Expected Proj, got {:?}", other),
        },
        other => panic!("Expected VDecl, got {:?}", other),
    }
}

// Part of #1974 - End-to-end: scalar-bearing constructor through to_ir_with_env
//
// The scalar_sz fix (#1974, W2-725) was tested at the emitter level but not
// through the full pipeline (Environment → build_ctor_env → to_ir_with_env).
// This test verifies that a constructor with UInt64 fields correctly propagates
// num_scalars and scalar_size through the IR lowering pipeline.
#[test]
fn test_to_ir_with_env_scalar_bearing_ctor() {
    let mut env = make_nat_env();
    // Register UInt64 manually (make_nat_env bypasses init_nat flag, so init_uint_types fails)
    env.add_inductive(clean_kernel::InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![clean_kernel::InductiveType {
            name: name("UInt64"),
            type_: Expr::type_(),
            constructors: vec![clean_kernel::Constructor {
                name: name("UInt64.mk"),
                type_: Expr::arrow(Expr::const_str("Nat"), Expr::const_str("UInt64")),
            }],
        }],
    })
    .expect("UInt64 inductive should register");
    let uint64_ref = Expr::const_str("UInt64");
    let nat_ref = Expr::const_str("Nat");

    // WithScalar : Type := WithScalar.mk (val : UInt64) (next : Nat)
    // Fields: UInt64 (scalar, 8 bytes) + Nat (object)
    env.add_inductive(clean_kernel::InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![clean_kernel::InductiveType {
            name: name("WithScalar"),
            type_: Expr::type_(),
            constructors: vec![clean_kernel::Constructor {
                name: name("WithScalar.mk"),
                type_: Expr::arrow(
                    uint64_ref.clone(),
                    Expr::arrow(nat_ref, Expr::const_str("WithScalar")),
                ),
            }],
        }],
    })
    .expect("WithScalar inductive should register");

    // def mk_ws (v : UInt64) (n : Nat) : WithScalar := WithScalar.mk v n
    let decl = Decl::new(
        name("mk_ws"),
        vec![],
        Expr::const_str("WithScalar"),
        vec![
            Param::new(fvar(0), name("v"), uint64_ref),
            Param::new(fvar(1), name("n"), Expr::const_str("Nat")),
        ],
        Code::let_bind(
            LetDecl::new(
                fvar(2),
                name("_1"),
                Expr::const_str("WithScalar"),
                LetValue::Ctor {
                    name: name("WithScalar.mk"),
                    levels: vec![],
                    args: vec![Arg::FVar(fvar(0)), Arg::FVar(fvar(1))],
                },
            ),
            Code::ret(fvar(2)),
        ),
        false,
    );

    let ir_decls = to_ir_with_env_ok(&[decl], &env);
    assert_eq!(ir_decls.len(), 1);

    // Fix #1993: Ctor.args should only have object args; scalar args
    // become SSet instructions.
    match &ir_decls[0].body {
        IRBody::VDecl {
            var: ctor_var,
            value,
            rest,
            ..
        } => {
            match value {
                IRExpr::Ctor { info, args } => {
                    assert_eq!(info.tag, 0, "sole constructor gets tag 0");
                    assert_eq!(
                        info.field_types,
                        vec![IRType::UInt64, IRType::Object],
                        "field_types should be [UInt64, Object] from environment"
                    );
                    assert_eq!(info.num_scalars, 1, "UInt64 is 1 scalar field");
                    assert_eq!(info.num_objects, 1, "Nat is 1 object field");
                    assert_eq!(
                        info.scalar_size(),
                        8,
                        "UInt64 scalar_size should be 8 bytes"
                    );
                    // Only the object arg in Ctor.args
                    assert_eq!(args.len(), 1, "only object args in Ctor.args");
                }
                other => panic!("Expected Ctor for WithScalar.mk, got {:?}", other),
            }
            // SSet for the UInt64 scalar field follows the VDecl
            match rest.as_ref() {
                IRBody::SSet {
                    var, n, offset, ty, ..
                } => {
                    assert_eq!(*var, *ctor_var, "SSet var matches Ctor var");
                    assert_eq!(*n, 1, "n = num_objects = 1");
                    assert_eq!(*offset, 0, "first scalar at offset 0");
                    assert_eq!(ty, &IRType::UInt64, "scalar type = UInt64");
                }
                other => panic!("Expected SSet after Ctor VDecl, got {:?}", other),
            }
        }
        other => panic!("Expected VDecl, got {:?}", other),
    }
}

// Part of #2032 - Char fields lower through the env-backed path as UInt32 scalars
#[test]
fn test_to_ir_with_env_char_ctor_uses_uint32_scalar_layout() {
    let mut env = make_nat_env();
    // UInt32 must be a known type before Char.mk's type (UInt32 → Char) can
    // pass the environment's type-checker.
    env.add_decl(clean_kernel::Declaration::Axiom {
        name: name("UInt32"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .expect("UInt32 axiom should register");
    env.add_inductive(clean_kernel::InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![clean_kernel::InductiveType {
            name: name("Char"),
            type_: Expr::type_(),
            constructors: vec![clean_kernel::Constructor {
                name: name("Char.mk"),
                type_: Expr::arrow(Expr::const_str("UInt32"), Expr::const_str("Char")),
            }],
        }],
    })
    .expect("Char inductive should register");
    env.add_inductive(clean_kernel::InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![clean_kernel::InductiveType {
            name: name("BoxChar"),
            type_: Expr::type_(),
            constructors: vec![clean_kernel::Constructor {
                name: name("BoxChar.mk"),
                type_: Expr::arrow(Expr::const_str("Char"), Expr::const_str("BoxChar")),
            }],
        }],
    })
    .expect("BoxChar inductive should register");

    let decl = Decl::new(
        name("mk_box_char"),
        vec![],
        Expr::const_str("BoxChar"),
        vec![Param::new(fvar(0), name("c"), Expr::const_str("Char"))],
        Code::let_bind(
            LetDecl::new(
                fvar(1),
                name("_1"),
                Expr::const_str("BoxChar"),
                LetValue::Ctor {
                    name: name("BoxChar.mk"),
                    levels: vec![],
                    args: vec![Arg::FVar(fvar(0))],
                },
            ),
            Code::ret(fvar(1)),
        ),
        false,
    );

    let ir_decls = to_ir_with_env_ok(&[decl], &env);
    assert_eq!(ir_decls.len(), 1);

    match &ir_decls[0].body {
        IRBody::VDecl {
            var: ctor_var,
            value,
            rest,
            ..
        } => {
            match value {
                IRExpr::Ctor { info, args } => {
                    assert_eq!(info.tag, 0);
                    assert_eq!(info.field_types, vec![IRType::UInt32]);
                    assert_eq!(
                        info.num_scalars, 1,
                        "Char should lower as one UInt32 scalar"
                    );
                    assert_eq!(info.num_objects, 0);
                    assert_eq!(
                        args.len(),
                        0,
                        "scalar-only ctors should not keep object args"
                    );
                }
                other => panic!("Expected Ctor for BoxChar.mk, got {:?}", other),
            }

            match rest.as_ref() {
                IRBody::SSet {
                    var, n, offset, ty, ..
                } => {
                    assert_eq!(*var, *ctor_var);
                    assert_eq!(*n, 0, "scalar-only ctor should not allocate object slots");
                    assert_eq!(*offset, 0);
                    assert_eq!(ty, &IRType::UInt32, "Char payload uses UInt32 layout");
                }
                other => panic!("Expected SSet after Char ctor VDecl, got {:?}", other),
            }
        }
        other => panic!("Expected VDecl, got {:?}", other),
    }
}

// Part of #1953 - Reuse with erased type args filters them correctly
#[test]
fn test_reuse_filters_erased_type_args() {
    // Reuse with type args (Arg::Type) should have those filtered out,
    // matching the behavior of Ctor (test_ctor_filters_erased_type_args).
    // List.cons {A} head tail → Reuse args should be [head, tail], not [erased, head, tail].
    // `num_params: 1` models the real `List` (one inductive parameter, `A`).
    let mut ctor_env = HashMap::new();
    ctor_env.insert(
        name("List.cons"),
        CtorMeta {
            num_params: 1,
            tag: 1,
            field_types: vec![IRType::Object, IRType::Object],
            num_scalars: 0,
            num_objects: 2,
        },
    );

    let decl = Decl::new(
        name("reuse_cons"),
        vec![],
        nat_type(),
        vec![
            Param::new(fvar(0), name("slot"), nat_type()),
            Param::new(fvar(1), name("head"), nat_type()),
            Param::new(fvar(2), name("tail"), nat_type()),
        ],
        Code::let_bind(
            LetDecl::new(
                fvar(3),
                name("_1"),
                nat_type(),
                LetValue::Reuse {
                    slot: fvar(0),
                    ctor_name: name("List.cons"),
                    levels: vec![],
                    // Type arg first, then runtime args
                    args: vec![
                        Arg::Type(Expr::const_str("Nat")),
                        Arg::FVar(fvar(1)),
                        Arg::FVar(fvar(2)),
                    ],
                },
            ),
            Code::ret(fvar(3)),
        ),
        false,
    );

    let ir = lower_decl_with_env_ok(&decl, &HashMap::new(), &ctor_env, &HashMap::new());
    match &ir.body {
        IRBody::VDecl { value, .. } => match value {
            IRExpr::Reuse { var, ctor, args } => {
                assert_eq!(
                    args.len(),
                    2,
                    "Type arg should be filtered, leaving 2 runtime args"
                );
                assert_eq!(ctor.tag, 1);
                assert_eq!(ctor.num_objects, 2);
                assert_eq!(*var, VarId(0), "Reuse slot should be VarId(0)");
                // Verify args are the FVar-based runtime args, not erased
                assert!(
                    matches!(&args[0], IRArg::Var(VarId(1))),
                    "First arg should be head (VarId(1)), got {:?}",
                    args[0]
                );
                assert!(
                    matches!(&args[1], IRArg::Var(VarId(2))),
                    "Second arg should be tail (VarId(2)), got {:?}",
                    args[1]
                );
            }
            other => panic!("Expected IRExpr::Reuse, got {:?}", other),
        },
        other => panic!("Expected VDecl, got {:?}", other),
    }
}

// Part of #1976 - Code::Fun without lambda lifting returns UnexpectedLocalFunction
#[test]
fn test_lower_code_fun_returns_unexpected_local_function_error() {
    use crate::lcnf::FunDecl;

    let local_fn = FunDecl {
        fvar_id: fvar(10),
        name: name("g"),
        params: vec![Param::new(fvar(1), name("y"), nat_type())],
        ty: nat_type(),
        body: Box::new(Code::ret(fvar(1))),
    };

    let code = Code::fun(local_fn, Code::ret(fvar(0)));
    let mut state = ToIRState::new();
    state.bind_var(fvar(0));

    let err = lower_code(&code, &mut state).expect_err("Code::Fun must fail closed");
    assert!(
        matches!(err, CompilerError::UnexpectedLocalFunction { ref name } if name.to_string().contains("g")),
        "expected UnexpectedLocalFunction for 'g', got: {err:?}"
    );
}

// Part of #1976 - The fail-closed guard preserves the local function's name so
// callers can diagnose which un-lifted function violated the invariant.
#[test]
fn test_lower_code_fun_error_preserves_local_function_name() {
    use crate::lcnf::FunDecl;

    let local_fn = FunDecl {
        fvar_id: fvar(10),
        name: name("inner_helper"),
        params: vec![],
        ty: nat_type(),
        body: Box::new(Code::ret(fvar(0))),
    };

    // The continuation references a let-bound variable, confirming the guard
    // fires before (and instead of) silently dropping the continuation body.
    let code = Code::fun(
        local_fn,
        Code::let_bind(
            LetDecl {
                fvar_id: fvar(2),
                name: name("z"),
                ty: nat_type(),
                value: LetValue::Erased,
            },
            Code::ret(fvar(2)),
        ),
    );
    let mut state = ToIRState::new();
    state.bind_var(fvar(0));

    let err = lower_code(&code, &mut state).expect_err("un-lifted Code::Fun must fail closed");
    match err {
        CompilerError::UnexpectedLocalFunction { name } => {
            assert_eq!(name, self::name("inner_helper"));
        }
        other => panic!("expected UnexpectedLocalFunction, got {other:?}"),
    }
}

// Part of #1976 - Lambda lifting eliminates every Code::Fun before IR lowering,
// so the to_ir guard is unreachable through the public entry points. This pins
// that end-to-end invariant for a function that itself nests another function.
#[test]
fn test_lambda_lift_eliminates_all_nested_code_fun() {
    use crate::lcnf::FunDecl;

    // def f (x : Nat) : Nat :=
    //   fun g (y : Nat) : Nat :=
    //     fun h (z : Nat) : Nat := return z   -- doubly nested local function
    //     return y
    //   return x
    let inner = FunDecl {
        fvar_id: fvar(20),
        name: name("h"),
        params: vec![Param::new(fvar(2), name("z"), nat_type())],
        ty: nat_type(),
        body: Box::new(Code::ret(fvar(2))),
    };
    let outer = FunDecl {
        fvar_id: fvar(10),
        name: name("g"),
        params: vec![Param::new(fvar(1), name("y"), nat_type())],
        ty: nat_type(),
        body: Box::new(Code::fun(inner, Code::ret(fvar(1)))),
    };
    let decl = Decl::new(
        name("f"),
        vec![],
        nat_type(),
        vec![Param::new(fvar(0), name("x"), nat_type())],
        Code::fun(outer, Code::ret(fvar(0))),
        false,
    );

    // Lowering must succeed (no UnexpectedLocalFunction): every Code::Fun is
    // lifted out into its own top-level IRDecl, and no IRBody can contain a
    // nested function declaration.
    let ir_decls = to_ir_ok(&[decl]);
    assert!(
        ir_decls.len() >= 2,
        "outer decl plus at least one lifted local decl, got {} decls",
        ir_decls.len()
    );

    // No lowered IRBody may itself contain a nested function: the IR model has
    // no such variant, so a successful lowering proves Code::Fun was eliminated.
    fn body_is_well_formed(body: &IRBody) -> bool {
        match body {
            IRBody::JDecl { body, rest, .. } => {
                body_is_well_formed(body) && body_is_well_formed(rest)
            }
            IRBody::VDecl { rest, .. }
            | IRBody::Inc { rest, .. }
            | IRBody::Dec { rest, .. }
            | IRBody::Set { rest, .. }
            | IRBody::SetTag { rest, .. }
            | IRBody::USet { rest, .. }
            | IRBody::SSet { rest, .. } => body_is_well_formed(rest),
            IRBody::Case { alts, default, .. } => {
                alts.iter().all(|a| body_is_well_formed(&a.body))
                    && default.as_ref().is_none_or(|d| body_is_well_formed(d))
            }
            IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => true,
        }
    }
    for ir_decl in &ir_decls {
        assert!(
            body_is_well_formed(&ir_decl.body),
            "lowered IRDecl {:?} has a malformed body",
            ir_decl.name
        );
    }
}

// Part of #2012 - lower_decl_with_env surfaces ctor_env fallback warnings
#[test]
fn test_lower_decl_with_env_surfaces_ctor_warnings() {
    // Create a ctor_env with one entry so the fallback warning triggers
    // for a different constructor.
    let mut ctor_env = HashMap::new();
    ctor_env.insert(
        name("Bool.true"),
        CtorMeta {
            num_params: 0,
            tag: 0,
            field_types: vec![],
            num_scalars: 0,
            num_objects: 0,
        },
    );

    // Build a decl that uses a constructor NOT in ctor_env.
    let decl = Decl::new(
        name("make_missing"),
        vec![],
        nat_type(),
        vec![Param::new(fvar(0), name("x"), nat_type())],
        Code::let_bind(
            LetDecl::new(
                fvar(1),
                name("result"),
                nat_type(),
                LetValue::Ctor {
                    name: name("Missing.mk"),
                    levels: vec![],
                    args: vec![Arg::FVar(fvar(0))],
                },
            ),
            Code::ret(fvar(1)),
        ),
        false,
    );

    let (ir_decl, warnings) =
        lower_decl_with_env(&decl, &HashMap::new(), &ctor_env, &HashMap::new())
            .expect("lowering should succeed");

    assert!(ir_decl.is_some(), "decl should lower to Some");
    assert!(
        !warnings.is_empty(),
        "should have a warning about missing constructor"
    );
    assert!(
        warnings[0].contains("Missing") && warnings[0].contains("mk"),
        "warning should mention the missing constructor, got: {}",
        warnings[0]
    );
}

// Part of #2012 - lower_decls_with_env aggregates warnings across decls
#[test]
fn test_lower_decls_with_env_aggregates_warnings() {
    let mut ctor_env = HashMap::new();
    ctor_env.insert(
        name("Bool.true"),
        CtorMeta {
            num_params: 0,
            tag: 0,
            field_types: vec![],
            num_scalars: 0,
            num_objects: 0,
        },
    );

    let decl1 = Decl::new(
        name("f1"),
        vec![],
        nat_type(),
        vec![Param::new(fvar(0), name("x"), nat_type())],
        Code::let_bind(
            LetDecl::new(
                fvar(1),
                name("r1"),
                nat_type(),
                LetValue::Ctor {
                    name: name("Unknown1.mk"),
                    levels: vec![],
                    args: vec![Arg::FVar(fvar(0))],
                },
            ),
            Code::ret(fvar(1)),
        ),
        false,
    );

    let decl2 = Decl::new(
        name("f2"),
        vec![],
        nat_type(),
        vec![Param::new(fvar(0), name("x"), nat_type())],
        Code::let_bind(
            LetDecl::new(
                fvar(1),
                name("r2"),
                nat_type(),
                LetValue::Ctor {
                    name: name("Unknown2.mk"),
                    levels: vec![],
                    args: vec![Arg::FVar(fvar(0))],
                },
            ),
            Code::ret(fvar(1)),
        ),
        false,
    );

    let output = lower_decls_with_env(&[decl1, decl2], &ctor_env, &HashMap::new())
        .expect("lowering should succeed");

    assert_eq!(output.decls.len(), 2);
    assert!(
        output.warnings.len() >= 2,
        "should have warnings from both decls, got {}",
        output.warnings.len()
    );
    assert!(
        output
            .warnings
            .iter()
            .any(|warning| warning.contains("Unknown1") && warning.contains("mk")),
        "warnings should mention Unknown1.mk, got: {:?}",
        output.warnings
    );
    assert!(
        output
            .warnings
            .iter()
            .any(|warning| warning.contains("Unknown2") && warning.contains("mk")),
        "warnings should mention Unknown2.mk, got: {:?}",
        output.warnings
    );
}

// Part of #2012 - to_ir_with_env returns warnings through the public API
#[test]
fn test_to_ir_with_env_returns_ctor_warnings() {
    let mut env = Environment::new();
    env.add_inductive(clean_kernel::InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![clean_kernel::InductiveType {
            name: name("Known"),
            type_: Expr::type_(),
            constructors: vec![clean_kernel::Constructor {
                name: name("Known.mk"),
                type_: Expr::const_str("Known"),
            }],
        }],
    })
    .expect("Known inductive should register");
    let decl = Decl::new(
        name("make_missing_with_env"),
        vec![],
        nat_type(),
        vec![Param::new(fvar(0), name("x"), nat_type())],
        Code::let_bind(
            LetDecl::new(
                fvar(1),
                name("result"),
                nat_type(),
                LetValue::Ctor {
                    name: name("Missing.from_env"),
                    levels: vec![],
                    args: vec![Arg::FVar(fvar(0))],
                },
            ),
            Code::ret(fvar(1)),
        ),
        false,
    );

    let output = to_ir_with_env(&[decl], &env).expect("to_ir_with_env should succeed");

    assert_eq!(output.decls.len(), 1);
    assert!(
        output
            .warnings
            .iter()
            .any(|warning| warning.contains("Missing") && warning.contains("from_env")),
        "public API warnings should mention Missing.from_env, got: {:?}",
        output.warnings
    );
}

// ════════════════════════════════════════════════════════════════════════════
// Phase 0 #1 — function-typed (`Pi`) constructor fields lower to `Object`.
//
// Before this arm, `expr_to_ir_type` rejected any field whose TYPE is a
// function (`Pi`). Empirically 41/98 prelude constructors carry such fields
// (type-class `.mk` and proof-carrying `intro` constructors). All of them are
// runtime-kept by LCNF (`classify_expr_arg` → `Normal`), so they must classify
// as `Object`, never `Erased`. See the SOUNDNESS comment in to_ir/types.rs.
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_expr_to_ir_type_function_value_field_is_object() {
    // A function-VALUE field `α → β` (codomain head is a data type).
    // e.g. `ToString.toString : α → String`.
    let f_ty = Expr::arrow(Expr::const_str("A"), Expr::const_str("String"));
    assert_eq!(
        expr_to_ir_type(&f_ty).expect("function-typed field must lower"),
        IRType::Object,
        "a function value is a boxed closure → Object"
    );
}

#[test]
fn test_expr_to_ir_type_type_family_field_is_object_not_erased() {
    // A type-FAMILY field `α → α → Prop` (codomain head is `Sort`/Prop).
    // This is exactly the shape of `LT.lt`/`LE.lt`. LCNF keeps the arg
    // (its type is a `Pi`, not a bare Prop/Sort/singleton), so it must be an
    // object slot — `Erased` here would corrupt `num_objects` and projection
    // offsets.
    let rel_ty = Expr::arrow(
        Expr::const_str("A"),
        Expr::arrow(Expr::const_str("A"), Expr::prop()),
    );
    let got = expr_to_ir_type(&rel_ty).expect("relation-typed field must lower");
    assert_eq!(
        got,
        IRType::Object,
        "type-family field `α → α → Prop` must be Object (LCNF keeps it), not Erased"
    );
    assert_ne!(got, IRType::Erased, "must not erase an LCNF-kept field");
}

#[test]
fn test_build_ctor_env_function_typed_fields_no_longer_error() {
    use clean_kernel::{BinderInfo, ConstructorVal};

    // A type-class-style `.mk`: `{α : Type} → (α → β) → (α → α → Prop) → C α`
    // field 0: function VALUE `α → β`  → Object
    // field 1: type FAMILY  `α → α → Prop` → Object
    let mk_ctor = ConstructorVal {
        name: name("C.mk"),
        inductive_name: name("C"),
        level_params: vec![],
        type_: Expr::pi(
            BinderInfo::Implicit,
            Expr::type_(),
            Expr::arrow(
                // (α → β)
                Expr::arrow(Expr::const_str("A"), Expr::const_str("B")),
                Expr::arrow(
                    // (α → α → Prop)
                    Expr::arrow(
                        Expr::const_str("A"),
                        Expr::arrow(Expr::const_str("A"), Expr::prop()),
                    ),
                    Expr::const_str("C"),
                ),
            ),
        ),
        num_params: 1,
        num_fields: 2,
        constructor_idx: 0,
    };

    let (env, _ind) =
        build_ctor_env(&[&mk_ctor]).expect("function-typed fields must not error build_ctor_env");
    let meta = env.get(&name("C.mk")).expect("C.mk should be in env");
    assert_eq!(
        meta.field_types,
        vec![IRType::Object, IRType::Object],
        "both function-typed fields lower to Object"
    );
    assert_eq!(meta.num_objects, 2);
    assert_eq!(meta.num_scalars, 0);
}

#[test]
fn test_proj_offsets_consistent_with_function_typed_field() {
    // Single-constructor structure with a scalar field BEFORE and AFTER a
    // function-typed (Object) field, to prove projection byte/object offsets
    // stay consistent once a `Pi` field participates in the layout.
    //
    // Fields: [UInt8 (scalar), (α → β) (Object), UInt16 (scalar)]
    let field_types = vec![IRType::UInt8, IRType::Object, IRType::UInt16];
    let var0 = IRArg::Var(VarId(0));

    // Field 0: UInt8 scalar. n = num_objects(1) + num_usizes(0) = 1, offset 0.
    let (e0, t0) = compute_proj_expr(&name("S"), &field_types, 0, var0.clone()).expect("field 0");
    match e0 {
        IRExpr::SProj { n, offset, ty, .. } => {
            assert_eq!(n, 1, "1 pointer-sized slot (the function-typed Object)");
            assert_eq!(offset, 0);
            assert_eq!(ty, IRType::UInt8);
        }
        other => panic!("expected SProj, got {other:?}"),
    }
    assert_eq!(t0, IRType::UInt8);

    // Field 1: the function-typed Object. obj_idx counts preceding objects = 0.
    let (e1, t1) = compute_proj_expr(&name("S"), &field_types, 1, var0.clone()).expect("field 1");
    assert!(
        matches!(e1, IRExpr::Proj { idx: 0, .. }),
        "function-typed field projects as object slot 0"
    );
    assert_eq!(t1, IRType::Object);

    // Field 2: UInt16 scalar AFTER the object. offset must skip only UInt8's
    // 1 byte (objects do not consume scalar bytes), not be shifted by the
    // Object field.
    let (e2, t2) = compute_proj_expr(&name("S"), &field_types, 2, var0).expect("field 2");
    match e2 {
        IRExpr::SProj { n, offset, ty, .. } => {
            assert_eq!(n, 1, "still 1 pointer-sized slot");
            assert_eq!(
                offset, 1,
                "offset = UInt8(1 byte); Object adds no scalar bytes"
            );
            assert_eq!(ty, IRType::UInt16);
        }
        other => panic!("expected SProj, got {other:?}"),
    }
    assert_eq!(t2, IRType::UInt16);
}

#[test]
fn test_build_ctor_env_over_full_prelude_no_error() {
    // Integration probe: walking every prelude constructor through
    // build_ctor_env must no longer hit the `UnsupportedIrType` catch-all.
    // Before the `Pi` arm, 41/98 prelude constructors failed here.
    let env = Environment::with_prelude();
    let ctors: Vec<&clean_kernel::ConstructorVal> = env.constructors().collect();
    assert!(
        !ctors.is_empty(),
        "prelude should contain constructors to exercise the path"
    );
    let result = build_ctor_env(&ctors);
    assert!(
        result.is_ok(),
        "build_ctor_env over the full prelude must succeed, got: {:?}",
        result.err()
    );
}

// ════════════════════════════════════════════════════════════════════════════
// #16 — function-as-value: an EXTERNAL (env/prelude) function referenced with
// fewer args than its arity must lower to PartialApply (closure), NOT a 0-arg
// Apply. Regression for the `l_Nat_add()` 0-arg call bug.
// ════════════════════════════════════════════════════════════════════════════

// build_external_arities counts the Pi-telescope length of an env constant.
// Uses the real prelude `Nat.add : Nat → Nat → Nat` — the exact function from
// the codegen bug, which must report arity 2 (matching clean_alloc_closure(...,2,0)).
#[test]
fn test_build_external_arities_counts_pi_telescope() {
    let env = Environment::with_prelude();
    let arities = super::ctor_env::build_external_arities(&env);
    assert_eq!(
        arities.get(&name("Nat.add")).copied(),
        Some(2),
        "prelude Nat.add (Nat → Nat → Nat) must have Pi-telescope arity 2, got {:?}",
        arities.get(&name("Nat.add"))
    );
    assert_eq!(
        arities.get(&name("Nat.succ")).copied(),
        Some(1),
        "prelude Nat.succ (Nat → Nat) must have arity 1"
    );
}

// An external fn (arity from the arity map, NOT in the lowered batch) referenced
// with 0 args lowers to PartialApply { arity, args: [] } — the closure path.
#[test]
fn test_to_ir_with_env_external_fn_value_is_closure() {
    // Caller references `ext.add2` (arity 2, external) with ZERO args, as a value.
    let caller_decl = Decl::new(
        name("passes_fn_as_value"),
        vec![],
        nat_type(),
        vec![],
        Code::let_bind(
            LetDecl::new(
                fvar(1),
                name("_1"),
                nat_type(),
                LetValue::Const {
                    name: name("ext.add2"),
                    levels: vec![],
                    args: vec![],
                },
            ),
            Code::ret(fvar(1)),
        ),
        false,
    );

    // ext.add2 has arity 2 — supplied via the external arity map (NOT lowered).
    let mut external_arities: HashMap<Name, u16> = HashMap::new();
    external_arities.insert(name("ext.add2"), 2);

    let output = super::decl::lower_decls_with_env_and_arities(
        &[caller_decl],
        &HashMap::new(),
        &HashMap::new(),
        &external_arities,
    )
    .expect("lowering should succeed");

    assert_eq!(output.decls.len(), 1);
    match &output.decls[0].body {
        IRBody::VDecl { value, .. } => match value {
            IRExpr::PartialApply { fn_id, arity, args } => {
                assert_eq!(fn_id.0, name("ext.add2"));
                assert_eq!(*arity, 2, "arity must come from external map");
                assert!(
                    args.is_empty(),
                    "0 fixed args → num_fixed 0 closure, got {:?}",
                    args
                );
            }
            other => panic!(
                "external fn-as-value must be PartialApply (closure), got {:?}",
                other
            ),
        },
        other => panic!("Expected VDecl, got {:?}", other),
    }
}

// ── R2 scalar-carrier CHAIN: `Fin.ofNat` / `BitVec.ofNatLT` decodes ──────
// The `Nat -> scalar` decode fires ONLY on affirmative compile-time width
// evidence (a KNOWN all-ones modulus / width literal); widths 8/16/32 only.

fn bitvec_chain_ctor_env() -> HashMap<Name, CtorMeta> {
    let mut ctor_env = HashMap::new();
    ctor_env.insert(
        name("BitVec.ofFin"),
        CtorMeta {
            num_params: 1,
            tag: 0,
            field_types: vec![IRType::Object],
            num_scalars: 0,
            num_objects: 1,
        },
    );
    ctor_env.insert(
        name("UInt32.ofBitVec"),
        CtorMeta {
            num_params: 0,
            tag: 0,
            field_types: vec![IRType::Object],
            num_scalars: 0,
            num_objects: 1,
        },
    );
    ctor_env
}

fn nat_lit(v: u64) -> LetValue {
    LetValue::Lit(clean_kernel::Literal::Nat(clean_kernel::BigNat::Small(v)))
}

/// Walk an IRBody spine collecting (var, expr) pairs of every VDecl.
fn vdecls(body: &IRBody) -> Vec<(crate::ir::VarId, IRExpr)> {
    let mut out = Vec::new();
    let mut cur = body;
    loop {
        match cur {
            IRBody::VDecl {
                var, value, rest, ..
            } => {
                out.push((*var, value.clone()));
                cur = rest;
            }
            IRBody::Inc { rest, .. } | IRBody::Dec { rest, .. } => cur = rest,
            _ => return out,
        }
    }
}

// The real `UInt32.ofNat` chain: `Fin.ofNat (lit 2^32-1) x` decodes to
// `Unbox {{ UInt32 }}` of the Nat operand; `BitVec.ofFin` and
// `UInt32.ofBitVec` then alias it, so the decl RETURNS the decoded scalar
// with no call, no heap ctor, and no refusal.
#[test]
fn test_fin_ofnat_known_modulus_decodes_full_chain_to_scalar() {
    let decl = Decl::new(
        name("u32_of_nat"),
        vec![],
        Expr::const_str("UInt32"),
        vec![Param::new(fvar(0), name("x"), nat_type())],
        Code::let_bind(
            LetDecl::new(fvar(1), name("m"), nat_type(), nat_lit(4294967295)),
            Code::let_bind(
                LetDecl::new(
                    fvar(2),
                    name("f"),
                    Expr::const_str("Fin"),
                    LetValue::Const {
                        name: name("Fin.ofNat"),
                        levels: vec![],
                        args: vec![Arg::FVar(fvar(1)), Arg::FVar(fvar(0))],
                    },
                ),
                Code::let_bind(
                    LetDecl::new(fvar(3), name("w"), nat_type(), nat_lit(32)),
                    Code::let_bind(
                        LetDecl::new(
                            fvar(4),
                            name("b"),
                            Expr::const_str("BitVec"),
                            LetValue::Const {
                                name: name("BitVec.ofFin"),
                                levels: vec![],
                                args: vec![Arg::FVar(fvar(3)), Arg::FVar(fvar(2))],
                            },
                        ),
                        Code::let_bind(
                            LetDecl::new(
                                fvar(5),
                                name("u"),
                                Expr::const_str("UInt32"),
                                LetValue::Const {
                                    name: name("UInt32.ofBitVec"),
                                    levels: vec![],
                                    args: vec![Arg::FVar(fvar(4))],
                                },
                            ),
                            Code::ret(fvar(5)),
                        ),
                    ),
                ),
            ),
        ),
        false,
    );
    let ir = lower_decl_with_env_ok(
        &decl,
        &HashMap::new(),
        &bitvec_chain_ctor_env(),
        &HashMap::new(),
    );
    let param_var = ir.params[0].0;
    let decls = vdecls(&ir.body);

    // The decode: exactly one Unbox, at UInt32, of the Nat PARAM.
    let unbox: Vec<_> = decls
        .iter()
        .filter_map(|(var, e)| match e {
            IRExpr::Unbox { ty, arg } => Some((*var, ty.clone(), arg.clone())),
            _ => None,
        })
        .collect();
    assert_eq!(unbox.len(), 1, "exactly one decode: {decls:?}");
    assert_eq!(unbox[0].1, IRType::UInt32);
    assert_eq!(unbox[0].2, IRArg::Var(param_var), "decodes the Nat operand");
    // No residual runtime call of the replaced chain, no heap ctor.
    assert!(
        !decls.iter().any(|(_, e)| matches!(
            e,
            IRExpr::Apply { fn_id, .. } if fn_id.0.to_string().contains("ofNat") || fn_id.0.to_string().contains("ofFin")
        )),
        "the chain must be decoded, not called: {decls:?}"
    );
    assert!(
        !decls.iter().any(|(_, e)| matches!(e, IRExpr::Ctor { .. })),
        "no heap ctor for the scalarized chain: {decls:?}"
    );
    // The aliases collapse: the decl returns the decoded scalar's own var.
    let mut cur = &ir.body;
    loop {
        match cur {
            IRBody::VDecl { rest, .. } | IRBody::Inc { rest, .. } | IRBody::Dec { rest, .. } => {
                cur = rest
            }
            IRBody::Ret(IRArg::Var(v)) => {
                assert_eq!(*v, unbox[0].0, "returns the decoded scalar");
                break;
            }
            other => panic!("expected Ret of the decoded scalar, got {other:?}"),
        }
    }
}

// Width 64 must DECLINE the decode (both emitters' Unbox route for 64 is the
// heap-only `clean_unbox_uint64`, garbage on tagged Nats; >= 2^63 payloads
// cannot round-trip the tagged box at all). The chain then still dies at the
// C5b object-carrier refusal — never a silent wrong-width decode.
#[test]
fn test_fin_ofnat_width64_modulus_declines_decode_and_chain_refuses() {
    let mut ctor_env = bitvec_chain_ctor_env();
    ctor_env.insert(
        name("UInt64.ofBitVec"),
        CtorMeta {
            num_params: 0,
            tag: 0,
            field_types: vec![IRType::Object],
            num_scalars: 0,
            num_objects: 1,
        },
    );
    let decl = Decl::new(
        name("u64_of_nat"),
        vec![],
        Expr::const_str("UInt64"),
        vec![Param::new(fvar(0), name("x"), nat_type())],
        Code::let_bind(
            LetDecl::new(fvar(1), name("m"), nat_type(), nat_lit(u64::MAX)),
            Code::let_bind(
                LetDecl::new(
                    fvar(2),
                    name("f"),
                    Expr::const_str("Fin"),
                    LetValue::Const {
                        name: name("Fin.ofNat"),
                        levels: vec![],
                        args: vec![Arg::FVar(fvar(1)), Arg::FVar(fvar(0))],
                    },
                ),
                Code::let_bind(
                    LetDecl::new(fvar(3), name("w"), nat_type(), nat_lit(64)),
                    Code::let_bind(
                        LetDecl::new(
                            fvar(4),
                            name("b"),
                            Expr::const_str("BitVec"),
                            LetValue::Const {
                                name: name("BitVec.ofFin"),
                                levels: vec![],
                                args: vec![Arg::FVar(fvar(3)), Arg::FVar(fvar(2))],
                            },
                        ),
                        Code::let_bind(
                            LetDecl::new(
                                fvar(5),
                                name("u"),
                                Expr::const_str("UInt64"),
                                LetValue::Const {
                                    name: name("UInt64.ofBitVec"),
                                    levels: vec![],
                                    args: vec![Arg::FVar(fvar(4))],
                                },
                            ),
                            Code::ret(fvar(5)),
                        ),
                    ),
                ),
            ),
        ),
        false,
    );
    let err = lower_decl_with_env(&decl, &HashMap::new(), &ctor_env, &HashMap::new())
        .expect_err("width-64 chain must refuse, never decode");
    assert!(
        matches!(err, CompilerError::ScalarCarrierObjectCarrier { .. }),
        "expected the C5b object-carrier refusal, got {err:?}"
    );
}

// `BitVec.ofNatLT w n h` with the width threaded through the elaborator's
// `OfNat.ofNat {Nat} (lit) (inst)` spelling: the known-value propagation
// recovers 32 and the decode fires on `n`.
#[test]
fn test_bitvec_ofnatlt_known_width_via_ofnat_chain_decodes() {
    let decl = Decl::new(
        name("u32_of_nat_lt"),
        vec![],
        Expr::const_str("UInt32"),
        vec![
            Param::new(fvar(0), name("n"), nat_type()),
            Param::new(fvar(1), name("h"), nat_type()),
        ],
        Code::let_bind(
            LetDecl::new(fvar(2), name("w0"), nat_type(), nat_lit(32)),
            Code::let_bind(
                LetDecl::new(
                    fvar(3),
                    name("inst"),
                    Expr::const_str("_"),
                    LetValue::Const {
                        name: name("instOfNatNat"),
                        levels: vec![],
                        args: vec![Arg::FVar(fvar(2))],
                    },
                ),
                Code::let_bind(
                    LetDecl::new(
                        fvar(4),
                        name("w"),
                        nat_type(),
                        LetValue::Const {
                            name: name("OfNat.ofNat"),
                            levels: vec![],
                            args: vec![Arg::Erased, Arg::FVar(fvar(2)), Arg::FVar(fvar(3))],
                        },
                    ),
                    Code::let_bind(
                        LetDecl::new(
                            fvar(5),
                            name("b"),
                            Expr::const_str("BitVec"),
                            LetValue::Const {
                                name: name("BitVec.ofNatLT"),
                                levels: vec![],
                                args: vec![
                                    Arg::FVar(fvar(4)),
                                    Arg::FVar(fvar(0)),
                                    Arg::FVar(fvar(1)),
                                ],
                            },
                        ),
                        Code::let_bind(
                            LetDecl::new(
                                fvar(6),
                                name("u"),
                                Expr::const_str("UInt32"),
                                LetValue::Const {
                                    name: name("UInt32.ofBitVec"),
                                    levels: vec![],
                                    args: vec![Arg::FVar(fvar(5))],
                                },
                            ),
                            Code::ret(fvar(6)),
                        ),
                    ),
                ),
            ),
        ),
        false,
    );
    let ir = lower_decl_with_env_ok(
        &decl,
        &HashMap::new(),
        &bitvec_chain_ctor_env(),
        &HashMap::new(),
    );
    let n_var = ir.params[0].0;
    let decls = vdecls(&ir.body);
    assert!(
        decls.iter().any(|(_, e)| matches!(
            e,
            IRExpr::Unbox { ty: IRType::UInt32, arg } if *arg == IRArg::Var(n_var)
        )),
        "ofNatLT with OfNat-chained width 32 must decode n: {decls:?}"
    );
}

// An OPAQUE width (no literal evidence) must not decode — the fail-closed
// direction of the width-evidence rule; the chain then refuses at the C5b
// object-carrier guard as before.
#[test]
fn test_bitvec_ofnatlt_opaque_width_declines_decode() {
    let decl = Decl::new(
        name("u32_of_nat_lt_opaque"),
        vec![],
        Expr::const_str("UInt32"),
        vec![
            Param::new(fvar(0), name("w"), nat_type()),
            Param::new(fvar(1), name("n"), nat_type()),
        ],
        Code::let_bind(
            LetDecl::new(
                fvar(2),
                name("b"),
                Expr::const_str("BitVec"),
                LetValue::Const {
                    name: name("BitVec.ofNatLT"),
                    levels: vec![],
                    args: vec![Arg::FVar(fvar(0)), Arg::FVar(fvar(1)), Arg::Erased],
                },
            ),
            Code::let_bind(
                LetDecl::new(
                    fvar(3),
                    name("u"),
                    Expr::const_str("UInt32"),
                    LetValue::Const {
                        name: name("UInt32.ofBitVec"),
                        levels: vec![],
                        args: vec![Arg::FVar(fvar(2))],
                    },
                ),
                Code::ret(fvar(3)),
            ),
        ),
        false,
    );
    let err = lower_decl_with_env(
        &decl,
        &HashMap::new(),
        &bitvec_chain_ctor_env(),
        &HashMap::new(),
    )
    .expect_err("opaque width must not decode; the chain refuses");
    assert!(
        matches!(err, CompilerError::ScalarCarrierObjectCarrier { .. }),
        "expected the C5b object-carrier refusal, got {err:?}"
    );
}
