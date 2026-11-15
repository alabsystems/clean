// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::expr::BinOp;

#[test]
fn test_emp() {
    let emp = SepAssertion::emp();
    assert!(emp.is_emp());
    assert!(emp.is_pure());
}

#[test]
fn test_points_to() {
    let ptr = CExpr::var("p");
    let val = CExpr::int(42);
    let pts = SepAssertion::points_to(ptr, CType::int(), val);

    assert!(!pts.is_pure());
    assert_eq!(pts.mentioned_pointers().len(), 1);
}

#[test]
fn test_sep_conj() {
    let p1 = SepAssertion::points_to(CExpr::var("p"), CType::int(), CExpr::int(1));
    let p2 = SepAssertion::points_to(CExpr::var("q"), CType::int(), CExpr::int(2));
    let conj = SepAssertion::sep_conj(p1, p2);

    assert!(matches!(conj, SepAssertion::SepConj(_, _)));
    assert_eq!(conj.mentioned_pointers().len(), 2);
}

#[test]
fn test_sep_conj_emp() {
    let p = SepAssertion::points_to(CExpr::var("p"), CType::int(), CExpr::int(1));
    let emp = SepAssertion::emp();

    // emp * P = P
    let conj = SepAssertion::sep_conj(emp.clone(), p.clone());
    assert!(matches!(conj, SepAssertion::PointsTo { .. }));

    // P * emp = P
    let conj2 = SepAssertion::sep_conj(p, emp);
    assert!(matches!(conj2, SepAssertion::PointsTo { .. }));
}

#[test]
fn test_magic_wand() {
    let p = SepAssertion::points_to(CExpr::var("p"), CType::int(), CExpr::int(1));
    let q = SepAssertion::points_to(CExpr::var("q"), CType::int(), CExpr::int(2));
    let wand = SepAssertion::wand(p, q);

    assert!(matches!(wand, SepAssertion::Wand(_, _)));
}

#[test]
fn test_share_join() {
    // Full + Top = Full
    assert_eq!(Share::Full.join(&Share::Top), Some(Share::Full));

    // Full + Full = None (can't combine)
    assert_eq!(Share::Full.join(&Share::Full), None);

    // ReadOnly + ReadOnly = ReadOnly
    assert_eq!(
        Share::ReadOnly.join(&Share::ReadOnly),
        Some(Share::ReadOnly)
    );

    // 1/2 + 1/2 = Full
    assert_eq!(
        Share::Frac(1, 2).join(&Share::Frac(1, 2)),
        Some(Share::Full)
    );

    // 1/4 + 1/4 = 1/2
    assert_eq!(
        Share::Frac(1, 4).join(&Share::Frac(1, 4)),
        Some(Share::Frac(1, 2))
    );
}

#[test]
fn test_share_split() {
    // Full splits to 1/2 + 1/2
    let (a, b) = Share::Full.split().unwrap();
    assert_eq!(a, Share::Frac(1, 2));
    assert_eq!(b, Share::Frac(1, 2));

    // 1/2 splits to 1/4 + 1/4
    let (a, b) = Share::Frac(1, 2).split().unwrap();
    assert_eq!(a, Share::Frac(1, 4));
    assert_eq!(b, Share::Frac(1, 4));
}

#[test]
fn test_frame_rule() {
    let pre = SepAssertion::points_to(CExpr::var("x"), CType::int(), CExpr::int(1));
    let post = SepAssertion::points_to(CExpr::var("x"), CType::int(), CExpr::int(2));
    let frame = SepAssertion::points_to(CExpr::var("y"), CType::int(), CExpr::int(42));

    let (framed_pre, framed_post) = FrameContext::frame_rule(pre, post, frame);

    // Both should be separating conjunctions
    assert!(matches!(framed_pre, SepAssertion::SepConj(_, _)));
    assert!(matches!(framed_post, SepAssertion::SepConj(_, _)));
}

#[test]
fn test_sep_to_spec() {
    // points_to(p, 42) -> valid(p) && *p == 42
    let pts = SepAssertion::points_to(CExpr::var("p"), CType::int(), CExpr::int(42));
    let spec: Spec = pts.into();

    assert!(matches!(spec, Spec::And(_)));
}

#[test]
fn test_exists() {
    let body = SepAssertion::points_to(CExpr::var("p"), CType::int(), CExpr::var("x"));
    let ex = SepAssertion::exists("x", CType::int(), body);

    assert!(matches!(ex, SepAssertion::Exists { .. }));
}

#[test]
fn test_iter() {
    // ⊛_{i ∈ 0..n} p[i] ↦ a[i]
    let body = SepAssertion::DataAt {
        ptr: CExpr::index(CExpr::var("p"), CExpr::var("i")),
        ty: CType::int(),
        value: Spec::Index {
            base: Box::new(Spec::var("a")),
            index: Box::new(Spec::var("i")),
        },
        share: Share::Full,
    };

    let iter = SepAssertion::iter("i", Spec::int(0), Spec::var("n"), body);
    assert!(matches!(iter, SepAssertion::Iter { .. }));
}

#[test]
fn test_pure_part() {
    let pure = SepAssertion::pure(Spec::ge(Spec::var("x"), Spec::int(0)));
    let pts = SepAssertion::points_to(CExpr::var("p"), CType::int(), CExpr::int(1));
    let conj = SepAssertion::sep_conj(pure, pts);

    let pp = conj.pure_part();
    let pp_val = pp.expect("sep_conj with pure part should return Some from pure_part()");
    assert!(matches!(pp_val, Spec::BinOp { op: BinOp::Ge, .. }));
}

#[test]
fn test_frame_context_consume() {
    let mut ctx = FrameContext::new();

    // Add two resources
    let p1 = SepAssertion::points_to(CExpr::var("x"), CType::int(), CExpr::int(1));
    let p2 = SepAssertion::points_to(CExpr::var("y"), CType::int(), CExpr::int(2));
    ctx.add_resource(p1.clone());
    ctx.add_resource(p2.clone());

    // Consume p1
    let remaining = ctx.consume(&p1);
    // Should have p2 left
    let r = remaining.expect("consuming p1 should return remaining resources");
    assert!(!r.is_emp());
}

#[test]
fn test_data_at() {
    let da = SepAssertion::data_at(CExpr::var("p"), CType::int(), Spec::var("v"), Share::Full);

    assert!(!da.is_pure());
    let spec: Spec = da.into();
    assert!(matches!(spec, Spec::And(_)));
}

#[test]
fn test_memory_block() {
    let mb = SepAssertion::memory_block(CExpr::var("p"), Spec::int(100));
    assert!(!mb.is_pure());
}

#[test]
fn test_array_at() {
    let arr = SepAssertion::array_at(
        CExpr::var("a"),
        CType::int(),
        vec![Spec::int(1), Spec::int(2), Spec::int(3)],
        Share::Full,
    );

    assert!(!arr.is_pure());
    let ptrs = arr.mentioned_pointers();
    assert_eq!(ptrs.len(), 1);
}

#[test]
fn test_sep_func_spec() {
    // swap(int *x, int *y)
    // PRE:  x ↦ a * y ↦ b
    // POST: x ↦ b * y ↦ a
    let pre = SepAssertion::sep_conj(
        SepAssertion::data_at(CExpr::var("x"), CType::int(), Spec::var("a"), Share::Full),
        SepAssertion::data_at(CExpr::var("y"), CType::int(), Spec::var("b"), Share::Full),
    );
    let post = SepAssertion::sep_conj(
        SepAssertion::data_at(CExpr::var("x"), CType::int(), Spec::var("b"), Share::Full),
        SepAssertion::data_at(CExpr::var("y"), CType::int(), Spec::var("a"), Share::Full),
    );

    let spec = SepFuncSpec::new(pre, post);
    assert!(spec.frame.is_none(), "new spec should have no frame");

    // Add a frame
    let frame = SepAssertion::points_to(CExpr::var("z"), CType::int(), CExpr::int(42));
    let framed_spec = spec.with_frame(frame);
    assert!(
        framed_spec.frame.is_some(),
        "spec.with_frame() should set the frame"
    );
}

#[test]
fn test_list_predicate() {
    let lst = list(CExpr::var("head"), vec![Spec::int(1), Spec::int(2)]);
    assert!(matches!(lst, SepAssertion::Pred { .. }));
}
