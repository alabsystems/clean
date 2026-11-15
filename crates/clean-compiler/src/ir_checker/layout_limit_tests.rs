// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Rule C1 at the runtime header's widths: the constructor shapes Clean's
//! 8-byte object header would truncate are refused by name.
//!
//! Pinned Lean's IR checker (`Checker.lean`@v4.30.0-rc2:137-141) refuses a
//! reference constructor tag above 243, more than 256 object fields and more
//! than 1024 scalar bytes. Clean's header stores tag, `num_objs` and
//! `scalar_sz` in one byte each, so the heap bounds here are Lean's
//! intersected with a byte. A boxed (nullary) constructor's tag lives in the
//! pointer bits and every lane reads it at 32 bits, so it takes only the
//! general `MAX_CTOR_TAG` bound, as pinned Lean accepts such enums. Each test
//! pins the boundary on both sides: the last accepted shape and the first
//! refused one.

use super::*;
use crate::ir::{CtorInfo, IRAlt, IRArg, IRBody, IRDecl, IRExpr, IRType, VarId};
use clean_kernel::Name;

fn name(s: &str) -> Name {
    Name::from_string(s)
}

/// A constructor whose counts are derived from its field types, as
/// `to_ir::ctor_env::build_ctor_env` derives them.
fn ctor(ctor_name: &str, tag: u32, field_types: Vec<IRType>) -> CtorInfo {
    CtorInfo {
        name: name(ctor_name),
        tag,
        num_scalars: field_types.iter().filter(|t| t.is_scalar()).count() as u32,
        num_objects: field_types.iter().filter(|t| t.is_rc_type()).count() as u32,
        field_types,
    }
}

/// `fun x0 .. x(n-1) => let y := ctor x0 .. x(n-1); ret y`, one object
/// parameter per object field (scalar fields are written by `sset`, never
/// passed as constructor arguments).
fn build(info: CtorInfo) -> Result<(), IRError> {
    let n = info.num_objects;
    let decl = IRDecl {
        name: name("test"),
        params: (0..n).map(|i| (VarId(i), IRType::Object)).collect(),
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: VarId(n),
            ty: IRType::Object,
            value: IRExpr::Ctor {
                info,
                args: (0..n).map(|i| IRArg::Var(VarId(i))).collect(),
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(n)))),
        },
    };
    check_decl(&decl, &[])
}

fn objects(n: usize) -> Vec<IRType> {
    vec![IRType::Object; n]
}

#[test]
fn test_checker_ref_ctor_tag_244_refused() {
    build(ctor("Big.c243", 243, objects(1)))
        .expect("a heap constructor tag of 243 is Lean's LeanMaxCtorTag and must be accepted");
    let err = build(ctor("Big.c244", 244, objects(1)))
        .expect_err("a heap constructor tag of 244 is above LeanMaxCtorTag");
    assert!(
        matches!(
            err,
            IRError::RefCtorTagTooLarge {
                tag: 244,
                max: 243,
                ..
            }
        ),
        "expected RefCtorTagTooLarge, got {err:?}"
    );
    assert!(
        err.to_string().contains("Big.c244"),
        "the refusal must name the constructor: {err}"
    );
    // A scalar-only constructor is heap-allocated too (it needs a scalar area).
    let err = build(ctor("Big.s244", 244, vec![IRType::UInt8]))
        .expect_err("a scalar-only constructor is a heap constructor");
    assert!(
        matches!(err, IRError::RefCtorTagTooLarge { tag: 244, .. }),
        "expected RefCtorTagTooLarge, got {err:?}"
    );
}

#[test]
fn test_checker_256_object_fields_refused() {
    build(ctor("Wide.mk", 0, objects(255)))
        .expect("255 object fields fit the header's 8-bit num_objs");
    let err = build(ctor("Wide.mk", 0, objects(256)))
        .expect_err("256 object fields would allocate 0 slots and write 256 pointers");
    assert!(
        matches!(
            err,
            IRError::CtorTooManyObjectFields {
                count: 256,
                max: 255,
                ..
            }
        ),
        "expected CtorTooManyObjectFields, got {err:?}"
    );
    assert!(
        err.to_string().contains("Wide.mk"),
        "the refusal must name the constructor: {err}"
    );
}

#[test]
fn test_checker_scalar_bytes_256_refused() {
    // 31 x 8 + 7 x 1 = 255 bytes: the largest scalar area the byte holds.
    let mut fits = vec![IRType::UInt64; 31];
    fits.extend(vec![IRType::UInt8; 7]);
    build(ctor("Wide.mk", 0, fits)).expect("255 scalar bytes fit the header's 8-bit scalar_sz");

    // 32 x UInt64 = 256 bytes, which the byte truncates to 0.
    let err = build(ctor("Wide.mk", 0, vec![IRType::UInt64; 32]))
        .expect_err("256 scalar bytes truncate to 0 in the header");
    assert!(
        matches!(
            err,
            IRError::CtorScalarSizeTooLarge {
                bytes: 256,
                max: 255,
                ..
            }
        ),
        "expected CtorScalarSizeTooLarge, got {err:?}"
    );
    assert!(
        err.to_string().contains("Wide.mk"),
        "the refusal must name the constructor: {err}"
    );

    // The battery probe's shape: 40 x UInt64 = 320 bytes (pinned Lean prints 41).
    let err = build(ctor("Wide.mk", 0, vec![IRType::UInt64; 40]))
        .expect_err("320 scalar bytes truncate to 64 in the header");
    assert!(
        matches!(err, IRError::CtorScalarSizeTooLarge { bytes: 320, .. }),
        "expected CtorScalarSizeTooLarge, got {err:?}"
    );
}

/// Nullary constructors are boxed, so Lean's 243 heap bound does not apply to
/// them, and every lane reads a boxed tag at 32 bits (the C header, the
/// trust-cg `clean_obj_tag` import, the Rust runtime): pinned Lean runs an
/// enum of 300 constructors (the `layout_enum_300` battery probe), and so does
/// Clean. The bound left is `MAX_CTOR_TAG`.
#[test]
fn test_checker_boxed_ctor_tag_above_255_accepted() {
    for tag in [244, 255, 256, 299, MAX_CTOR_TAG] {
        build(ctor(&format!("E.c{tag}"), tag, vec![]))
            .unwrap_or_else(|e| panic!("a boxed tag of {tag} must be accepted, as Lean does: {e}"));
    }
    let err = build(ctor("E.big", MAX_CTOR_TAG + 1, vec![]))
        .expect_err("a tag above MAX_CTOR_TAG is still refused");
    assert!(
        matches!(err, IRError::CtorTagTooLarge { .. }),
        "expected CtorTagTooLarge, got {err:?}"
    );
}

/// The dispatch side: a `case` alternative on boxed tag 299 is accepted (every
/// lane's `switch` reads the tag whole), while an alternative naming a heap
/// constructor above 243 is refused, as building one is.
#[test]
fn test_checker_case_alt_boxed_tag_299_accepted() {
    let alt = |info: CtorInfo| IRAlt {
        ctor: info,
        body: Box::new(IRBody::Ret(IRArg::Var(VarId(0)))),
    };
    let decl = |info: CtorInfo| IRDecl {
        name: name("isLast"),
        params: vec![(VarId(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::Case {
            scrutinee: VarId(0),
            alts: vec![alt(info)],
            default: Some(Box::new(IRBody::Ret(IRArg::Var(VarId(0))))),
        },
    };
    for tag in [255, 256, 299] {
        check_decl(&decl(ctor(&format!("E.c{tag}"), tag, vec![])), &[])
            .unwrap_or_else(|e| panic!("a case on boxed tag {tag} must be accepted: {e}"));
    }
    let err = check_decl(&decl(ctor("Big.c244", 244, objects(1))), &[])
        .expect_err("a case on heap tag 244 must be refused");
    assert!(
        matches!(err, IRError::RefCtorTagTooLarge { tag: 244, .. }),
        "expected RefCtorTagTooLarge, got {err:?}"
    );
}

/// `reuse` always yields a heap cell (`clean_reuse` never boxes), so its
/// constructor carries a heap tag whatever its field count.
#[test]
fn test_checker_reuse_heap_tag_244_refused() {
    let decl = |tag: u32| IRDecl {
        name: name("test"),
        params: vec![(VarId(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: VarId(1),
            ty: IRType::Object,
            value: IRExpr::Reuse {
                var: VarId(0),
                ctor: ctor(&format!("E.c{tag}"), tag, vec![]),
                args: vec![],
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(1)))),
        },
    };
    check_decl(&decl(243), &[]).expect("reuse at heap tag 243 is accepted");
    let err = check_decl(&decl(244), &[]).expect_err("reuse at heap tag 244 must be refused");
    assert!(
        matches!(
            err,
            IRError::RefCtorTagTooLarge {
                tag: 244,
                max: 243,
                ..
            }
        ),
        "expected RefCtorTagTooLarge, got {err:?}"
    );
}

/// `setTag` writes a heap constructor's tag byte in place
/// (`clean_ctor_set_tag(o, uint8_t)`), so it takes the heap bound.
#[test]
fn test_checker_set_tag_244_refused() {
    let decl = |tag: u32| IRDecl {
        name: name("test"),
        params: vec![(VarId(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::SetTag {
            var: VarId(0),
            tag,
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(0)))),
        },
    };
    check_decl(&decl(243), &[]).expect("setTag to 243 is accepted");
    let err = check_decl(&decl(244), &[]).expect_err("setTag to 244 must be refused");
    assert!(
        matches!(err, IRError::SetTagTooLarge { tag: 244, max: 243 }),
        "expected SetTagTooLarge, got {err:?}"
    );
}

/// `reuse` rebuilds a cell in place through `clean_reuse`, which takes the
/// same one-byte `num_objs` and `scalar_sz` as an allocation, so its
/// constructor takes the same field and scalar-byte bounds.
#[test]
fn test_checker_reuse_256_object_fields_and_scalar_bytes_refused() {
    let reuse = |info: CtorInfo| {
        let n = info.num_objects;
        let decl = IRDecl {
            name: name("test"),
            params: (0..=n).map(|i| (VarId(i), IRType::Object)).collect(),
            return_type: IRType::Object,
            body: IRBody::VDecl {
                var: VarId(n + 1),
                ty: IRType::Object,
                value: IRExpr::Reuse {
                    var: VarId(0),
                    ctor: info,
                    args: (1..=n).map(|i| IRArg::Var(VarId(i))).collect(),
                },
                rest: Box::new(IRBody::Ret(IRArg::Var(VarId(n + 1)))),
            },
        };
        check_decl(&decl, &[])
    };
    reuse(ctor("Wide.mk", 0, objects(255))).expect("reuse with 255 object fields is accepted");
    let err = reuse(ctor("Wide.mk", 0, objects(256)))
        .expect_err("reuse with 256 object fields must be refused");
    assert!(
        matches!(
            err,
            IRError::CtorTooManyObjectFields {
                count: 256,
                max: 255,
                ..
            }
        ),
        "expected CtorTooManyObjectFields, got {err:?}"
    );
    let err = reuse(ctor("Wide.mk", 0, vec![IRType::UInt64; 32]))
        .expect_err("reuse with 256 scalar bytes must be refused");
    assert!(
        matches!(err, IRError::CtorScalarSizeTooLarge { bytes: 256, .. }),
        "expected CtorScalarSizeTooLarge, got {err:?}"
    );
}
