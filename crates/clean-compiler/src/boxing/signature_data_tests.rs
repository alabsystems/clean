// Copyright 2026 Andrew Yates | Apache-2.0
use super::mk_boxed_version_from_signature;
use crate::ir::{FnId, IRArg, IRBody, IRExpr, IRType, VarId};
use clean_kernel::Name;

#[test]
fn test_signature_data_reads_both_owned_boxes_before_releasing_either() {
    let original = Name::from_string("ForeignOwner.operation");
    let adapter = mk_boxed_version_from_signature(
        &original,
        &[(VarId(19), IRType::UInt64), (VarId(27), IRType::UInt64)],
        &IRType::UInt64,
    );
    assert_eq!(
        adapter.params,
        [(VarId(0), IRType::Object), (VarId(1), IRType::Object)]
    );
    assert_eq!(adapter.return_type, IRType::Object);
    let mut body = &adapter.body;
    for (unboxed, boxed) in [(2, 0), (3, 1)] {
        let IRBody::VDecl {
            var,
            ty,
            value,
            rest,
        } = body
        else {
            panic!("both reads must precede ownership consumption: {body:?}")
        };
        assert_eq!(*var, VarId(unboxed));
        assert_eq!(*ty, IRType::UInt64);
        assert_eq!(
            *value,
            IRExpr::Unbox {
                ty: IRType::UInt64,
                arg: IRArg::Var(VarId(boxed))
            }
        );
        body = rest;
    }
    for owned in [0, 1] {
        let IRBody::Dec { var, rest } = body else {
            panic!("each scalar box transfers one owned reference: {body:?}")
        };
        assert_eq!(*var, VarId(owned));
        body = rest;
    }
    let IRBody::VDecl {
        var,
        ty,
        value,
        rest,
    } = body
    else {
        panic!("the original callable receives the two scalar values")
    };
    assert_eq!(*var, VarId(4));
    assert_eq!(*ty, IRType::UInt64);
    assert_eq!(
        *value,
        IRExpr::Apply {
            fn_id: FnId(original),
            args: vec![IRArg::Var(VarId(2)), IRArg::Var(VarId(3))],
        }
    );
    let IRBody::VDecl {
        var,
        ty,
        value,
        rest,
    } = &**rest
    else {
        panic!("the scalar result needs a fresh UInt64 box")
    };
    assert_eq!(*var, VarId(5));
    assert_eq!(*ty, IRType::Object);
    assert_eq!(
        *value,
        IRExpr::Box {
            ty: IRType::UInt64,
            arg: IRArg::Var(VarId(4))
        }
    );
    assert_eq!(**rest, IRBody::Ret(IRArg::Var(VarId(5))));
}

#[test]
fn test_signature_data_does_not_select_arithmetic_from_a_display_name() {
    for text in ["UInt64.add", "UInt64.mul", "Unrelated.userCallable"] {
        let name = Name::from_string(text);
        let adapter = mk_boxed_version_from_signature(
            &name,
            &[(VarId(0), IRType::UInt64), (VarId(1), IRType::UInt64)],
            &IRType::UInt64,
        );
        let mut body = &adapter.body;
        loop {
            match body {
                IRBody::VDecl {
                    value: IRExpr::Apply { fn_id, .. },
                    ..
                } => {
                    assert_eq!(fn_id.0, name);
                    break;
                }
                IRBody::VDecl { rest, .. } | IRBody::Dec { rest, .. } => body = rest,
                _ => panic!("signature DATA must retain its actual target: {body:?}"),
            }
        }
    }
}
