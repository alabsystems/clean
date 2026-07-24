// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended IR ID normalization.
//!
//! Part of #3083 — Extensibility.

use crate::ir::{
    CtorInfo, FnId, IRAlt, IRArg, IRBody, IRDecl, IRExpr, IRLiteral, IRType, JoinPointId, VarId,
};
use crate::ir_norm_ids_ext::{
    alpha_equiv, canonical_form, content_hash, decl_names_equivalent, detect_collisions,
    normalize_and_detect, normalize_decl_name, normalize_ids_ext, IdCollisions, NormStats,
};
use clean_kernel::Name;

// ─── Helpers ───────────────────────────────────────────────────────────

fn mk_name(s: &str) -> Name {
    Name::from_string(s)
}
fn mk_fn_id(s: &str) -> FnId {
    FnId(mk_name(s))
}

fn mk_ctor(name: &str, tag: u32, n_obj: u32) -> CtorInfo {
    CtorInfo {
        name: mk_name(name),
        tag,
        num_scalars: 0,
        num_objects: n_obj,
        field_types: vec![],
    }
}

/// Simple decl: `fn f(x100: Object) -> Object { let x200 = x100; ret x200 }`
fn simple_decl(param_id: u32, body_id: u32) -> IRDecl {
    IRDecl {
        name: mk_name("f"),
        params: vec![(VarId(param_id), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: VarId(body_id),
            ty: IRType::Object,
            value: IRExpr::Tag(IRArg::Var(VarId(param_id))),
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(body_id)))),
        },
    }
}

/// Decl with a join point.
fn jp_decl(param_id: u32, jp_id: u32, jp_param_id: u32, body_var: u32) -> IRDecl {
    IRDecl {
        name: mk_name("g"),
        params: vec![(VarId(param_id), IRType::UInt64)],
        return_type: IRType::UInt64,
        body: IRBody::JDecl {
            jp: JoinPointId(jp_id),
            params: vec![(VarId(jp_param_id), IRType::UInt64)],
            body: Box::new(IRBody::Ret(IRArg::Var(VarId(jp_param_id)))),
            rest: Box::new(IRBody::VDecl {
                var: VarId(body_var),
                ty: IRType::UInt64,
                value: IRExpr::Lit(IRLiteral::UInt64(42)),
                rest: Box::new(IRBody::Jmp {
                    jp: JoinPointId(jp_id),
                    args: vec![IRArg::Var(VarId(body_var))],
                }),
            }),
        },
    }
}

// ─── normalize_ids_ext ─────────────────────────────────────────────────

#[test]
fn test_normalize_ids_ext_sequential_vars() {
    let d = simple_decl(100, 200);
    let (norm, stats) = normalize_ids_ext(&d);
    assert_eq!(norm.params[0].0, VarId(0));
    if let IRBody::VDecl { var, .. } = &norm.body {
        assert_eq!(*var, VarId(1));
    }
    assert_eq!(stats.vars_renamed, 2);
    assert_eq!(stats.jps_renamed, 0);
}

#[test]
fn test_normalize_ids_ext_already_normalized() {
    let d = simple_decl(0, 1);
    let (_, stats) = normalize_ids_ext(&d);
    assert_eq!(stats.vars_renamed, 0);
}

#[test]
fn test_normalize_ids_ext_jp_separate_counter() {
    let d = jp_decl(50, 99, 51, 52);
    let (norm, stats) = normalize_ids_ext(&d);
    assert_eq!(norm.params[0].0, VarId(0));
    if let IRBody::JDecl {
        jp, params, rest, ..
    } = &norm.body
    {
        // JP params bound before JP itself in the counter
        assert_eq!(params[0].0, VarId(1));
        assert_eq!(*jp, JoinPointId(0));
        if let IRBody::VDecl { var, .. } = rest.as_ref() {
            assert_eq!(*var, VarId(2));
        }
    }
    assert!(stats.vars_renamed > 0);
    assert!(stats.jps_renamed > 0);
}

#[test]
fn test_normalize_ids_ext_preserves_types() {
    let d = simple_decl(100, 200);
    let (norm, _) = normalize_ids_ext(&d);
    assert_eq!(norm.return_type, IRType::Object);
    assert_eq!(norm.params[0].1, IRType::Object);
}

#[test]
fn test_normalize_ids_ext_preserves_name() {
    let d = simple_decl(10, 20);
    let (norm, _) = normalize_ids_ext(&d);
    assert_eq!(norm.name, mk_name("f"));
}

// ─── canonical_form ────────────────────────────────────────────────────

#[test]
fn test_canonical_form_idempotent() {
    let d = simple_decl(100, 200);
    let c1 = canonical_form(&d);
    let c2 = canonical_form(&c1);
    assert_eq!(content_hash(&c1), content_hash(&c2));
}

#[test]
fn test_canonical_form_same_structure_different_ids() {
    let d1 = simple_decl(100, 200);
    let d2 = simple_decl(500, 600);
    let c1 = canonical_form(&d1);
    let c2 = canonical_form(&d2);
    assert_eq!(content_hash(&c1), content_hash(&c2));
}

#[test]
fn test_canonical_form_different_structure() {
    let d1 = simple_decl(0, 1);
    // Different: two params
    let d2 = IRDecl {
        name: mk_name("f"),
        params: vec![(VarId(0), IRType::Object), (VarId(1), IRType::UInt64)],
        return_type: IRType::Object,
        body: IRBody::Ret(IRArg::Var(VarId(0))),
    };
    assert_ne!(
        content_hash(&canonical_form(&d1)),
        content_hash(&canonical_form(&d2))
    );
}

// ─── alpha_equiv ───────────────────────────────────────────────────────

#[test]
fn test_alpha_equiv_same_decl() {
    let d = simple_decl(5, 10);
    assert!(alpha_equiv(&d, &d));
}

#[test]
fn test_alpha_equiv_renamed_vars() {
    let d1 = simple_decl(100, 200);
    let d2 = simple_decl(999, 888);
    assert!(alpha_equiv(&d1, &d2));
}

#[test]
fn test_alpha_equiv_different_types_not_equiv() {
    let d1 = simple_decl(0, 1);
    let mut d2 = simple_decl(0, 1);
    d2.return_type = IRType::UInt64;
    assert!(!alpha_equiv(&d1, &d2));
}

#[test]
fn test_alpha_equiv_different_param_count_not_equiv() {
    let d1 = simple_decl(0, 1);
    let d2 = IRDecl {
        name: mk_name("f"),
        params: vec![],
        return_type: IRType::Object,
        body: IRBody::Ret(IRArg::Erased),
    };
    assert!(!alpha_equiv(&d1, &d2));
}

#[test]
fn test_alpha_equiv_jp_decls() {
    let d1 = jp_decl(10, 20, 30, 40);
    let d2 = jp_decl(1, 2, 3, 4);
    assert!(alpha_equiv(&d1, &d2));
}

#[test]
fn test_alpha_equiv_reflexive() {
    let d = jp_decl(0, 1, 2, 3);
    assert!(alpha_equiv(&d, &d));
}

#[test]
fn test_alpha_equiv_symmetric() {
    let d1 = simple_decl(1, 2);
    let d2 = simple_decl(99, 100);
    assert_eq!(alpha_equiv(&d1, &d2), alpha_equiv(&d2, &d1));
}

#[test]
fn test_alpha_equiv_different_literal_not_equiv() {
    let mk = |lit_val: u64| IRDecl {
        name: mk_name("h"),
        params: vec![],
        return_type: IRType::UInt64,
        body: IRBody::VDecl {
            var: VarId(0),
            ty: IRType::UInt64,
            value: IRExpr::Lit(IRLiteral::UInt64(lit_val)),
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(0)))),
        },
    };
    assert!(!alpha_equiv(&mk(1), &mk(2)));
}

#[test]
fn test_alpha_equiv_same_literal() {
    let mk = |v: u32| IRDecl {
        name: mk_name("h"),
        params: vec![],
        return_type: IRType::UInt64,
        body: IRBody::VDecl {
            var: VarId(v),
            ty: IRType::UInt64,
            value: IRExpr::Lit(IRLiteral::UInt64(42)),
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(v)))),
        },
    };
    assert!(alpha_equiv(&mk(0), &mk(99)));
}

// ─── content_hash ──────────────────────────────────────────────────────

#[test]
fn test_content_hash_deterministic() {
    let d = canonical_form(&simple_decl(0, 1));
    assert_eq!(content_hash(&d), content_hash(&d));
}

#[test]
fn test_content_hash_canonical_equiv_same_hash() {
    let c1 = canonical_form(&simple_decl(10, 20));
    let c2 = canonical_form(&simple_decl(30, 40));
    assert_eq!(content_hash(&c1), content_hash(&c2));
}

#[test]
fn test_content_hash_different_structure_different_hash() {
    let c1 = canonical_form(&simple_decl(0, 1));
    let c2 = canonical_form(&jp_decl(0, 1, 2, 3));
    assert_ne!(content_hash(&c1), content_hash(&c2));
}

#[test]
fn test_content_hash_with_string_expr() {
    let mk = |s: &str| IRDecl {
        name: mk_name("f"),
        params: vec![],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: VarId(0),
            ty: IRType::Object,
            value: IRExpr::String(s.to_string()),
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(0)))),
        },
    };
    let c1 = canonical_form(&mk("hello"));
    let c2 = canonical_form(&mk("world"));
    assert_ne!(content_hash(&c1), content_hash(&c2));
}

// ─── detect_collisions ─────────────────────────────────────────────────

#[test]
fn test_detect_collisions_no_collisions() {
    let d = simple_decl(0, 1);
    let c = detect_collisions(&d);
    assert!(c.is_empty());
    assert_eq!(c.total(), 0);
}

#[test]
fn test_detect_collisions_var_collision() {
    // Both param and body use VarId(5)
    let d = simple_decl(5, 5);
    let c = detect_collisions(&d);
    assert_eq!(c.duplicate_vars, vec![5]);
    assert!(c.duplicate_jps.is_empty());
    assert_eq!(c.total(), 1);
}

#[test]
fn test_detect_collisions_jp_collision() {
    let d = IRDecl {
        name: mk_name("f"),
        params: vec![],
        return_type: IRType::Void,
        body: IRBody::JDecl {
            jp: JoinPointId(0),
            params: vec![],
            body: Box::new(IRBody::Unreachable),
            rest: Box::new(IRBody::JDecl {
                jp: JoinPointId(0), // duplicate!
                params: vec![],
                body: Box::new(IRBody::Unreachable),
                rest: Box::new(IRBody::Unreachable),
            }),
        },
    };
    let c = detect_collisions(&d);
    assert_eq!(c.duplicate_jps, vec![0]);
}

#[test]
fn test_detect_collisions_multiple() {
    // Three uses of VarId(7)
    let d = IRDecl {
        name: mk_name("f"),
        params: vec![(VarId(7), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: VarId(7),
            ty: IRType::Object,
            value: IRExpr::Tag(IRArg::Var(VarId(7))),
            rest: Box::new(IRBody::VDecl {
                var: VarId(7),
                ty: IRType::Object,
                value: IRExpr::Tag(IRArg::Var(VarId(7))),
                rest: Box::new(IRBody::Ret(IRArg::Var(VarId(7)))),
            }),
        },
    };
    let c = detect_collisions(&d);
    assert_eq!(c.duplicate_vars, vec![7]);
    assert!(!c.is_empty());
}

#[test]
fn test_detect_collisions_in_case_branches() {
    let d = IRDecl {
        name: mk_name("f"),
        params: vec![(VarId(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::Case {
            scrutinee: VarId(0),
            alts: vec![
                IRAlt {
                    ctor: mk_ctor("A", 0, 0),
                    body: Box::new(IRBody::VDecl {
                        var: VarId(1),
                        ty: IRType::Object,
                        value: IRExpr::Lit(IRLiteral::Bool(true)),
                        rest: Box::new(IRBody::Ret(IRArg::Var(VarId(1)))),
                    }),
                },
                IRAlt {
                    ctor: mk_ctor("B", 1, 0),
                    body: Box::new(IRBody::VDecl {
                        var: VarId(1), // same as other branch
                        ty: IRType::Object,
                        value: IRExpr::Lit(IRLiteral::Bool(false)),
                        rest: Box::new(IRBody::Ret(IRArg::Var(VarId(1)))),
                    }),
                },
            ],
            default: None,
        },
    };
    let c = detect_collisions(&d);
    assert_eq!(c.duplicate_vars, vec![1]);
}

// ─── normalize_and_detect ──────────────────────────────────────────────

#[test]
fn test_normalize_and_detect_clean() {
    let d = simple_decl(0, 1);
    let (norm, stats, collisions) = normalize_and_detect(&d);
    assert!(collisions.is_empty());
    assert_eq!(stats.collisions_found, 0);
    assert_eq!(norm.params[0].0, VarId(0));
}

#[test]
fn test_normalize_and_detect_with_collisions() {
    let d = simple_decl(5, 5);
    let (_, stats, collisions) = normalize_and_detect(&d);
    assert_eq!(collisions.duplicate_vars, vec![5]);
    assert_eq!(stats.collisions_found, 1);
}

// ─── normalize_decl_name ───────────────────────────────────────────────

#[test]
fn test_normalize_decl_name_plain() {
    assert_eq!(normalize_decl_name("Nat.add"), "nat.add");
}

#[test]
fn test_normalize_decl_name_private_prefix() {
    assert_eq!(
        normalize_decl_name("_private.Lean.Data.Nat.add"),
        "lean.data.nat.add"
    );
}

#[test]
fn test_normalize_decl_name_root_prefix() {
    assert_eq!(normalize_decl_name("_root_.Nat.add"), "nat.add");
}

#[test]
fn test_normalize_decl_name_consecutive_dots() {
    assert_eq!(normalize_decl_name("Foo..Bar...Baz"), "foo.bar.baz");
}

#[test]
fn test_normalize_decl_name_trailing_dot() {
    assert_eq!(normalize_decl_name("Foo.Bar."), "foo.bar");
}

#[test]
fn test_normalize_decl_name_empty() {
    assert_eq!(normalize_decl_name(""), "");
}

#[test]
fn test_normalize_decl_name_leading_dot() {
    assert_eq!(normalize_decl_name(".Foo"), "foo");
}

// ─── decl_names_equivalent ─────────────────────────────────────────────

#[test]
fn test_decl_names_equiv_case_insensitive() {
    assert!(decl_names_equivalent("Nat.Add", "nat.add"));
}

#[test]
fn test_decl_names_equiv_prefix_stripping() {
    assert!(decl_names_equivalent(
        "_private.Lean.Nat.add",
        "_root_.Lean.Nat.add"
    ));
}

#[test]
fn test_decl_names_not_equiv_different_names() {
    assert!(!decl_names_equivalent("Nat.add", "Int.sub"));
}

// ─── Edge cases ────────────────────────────────────────────────────────

#[test]
fn test_empty_decl() {
    let d = IRDecl {
        name: mk_name("empty"),
        params: vec![],
        return_type: IRType::Void,
        body: IRBody::Unreachable,
    };
    let (norm, stats) = normalize_ids_ext(&d);
    assert_eq!(stats.vars_renamed, 0);
    assert_eq!(stats.jps_renamed, 0);
    assert_eq!(norm.params.len(), 0);
}

#[test]
fn test_alpha_equiv_empty_decls() {
    let d1 = IRDecl {
        name: mk_name("a"),
        params: vec![],
        return_type: IRType::Void,
        body: IRBody::Unreachable,
    };
    let d2 = IRDecl {
        name: mk_name("b"),
        params: vec![],
        return_type: IRType::Void,
        body: IRBody::Unreachable,
    };
    assert!(alpha_equiv(&d1, &d2));
}

#[test]
fn test_normalize_inc_dec() {
    let d = IRDecl {
        name: mk_name("f"),
        params: vec![(VarId(10), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::Inc {
            var: VarId(10),
            n: 1,
            rest: Box::new(IRBody::Dec {
                var: VarId(10),
                rest: Box::new(IRBody::Ret(IRArg::Var(VarId(10)))),
            }),
        },
    };
    let (norm, _) = normalize_ids_ext(&d);
    if let IRBody::Inc { var, n, rest } = &norm.body {
        assert_eq!(*var, VarId(0));
        assert_eq!(*n, 1);
        if let IRBody::Dec { var: dv, .. } = rest.as_ref() {
            assert_eq!(*dv, VarId(0));
        }
    } else {
        panic!("expected Inc");
    }
}

#[test]
fn test_normalize_set_settag() {
    let d = IRDecl {
        name: mk_name("f"),
        params: vec![(VarId(10), IRType::Object), (VarId(20), IRType::Object)],
        return_type: IRType::Void,
        body: IRBody::Set {
            var: VarId(10),
            idx: 0,
            value: VarId(20),
            rest: Box::new(IRBody::SetTag {
                var: VarId(10),
                tag: 1,
                rest: Box::new(IRBody::Ret(IRArg::Erased)),
            }),
        },
    };
    let (norm, _) = normalize_ids_ext(&d);
    if let IRBody::Set {
        var,
        idx,
        value,
        rest,
    } = &norm.body
    {
        assert_eq!(*var, VarId(0));
        assert_eq!(*idx, 0);
        assert_eq!(*value, VarId(1));
        if let IRBody::SetTag { var: sv, tag, .. } = rest.as_ref() {
            assert_eq!(*sv, VarId(0));
            assert_eq!(*tag, 1);
        }
    } else {
        panic!("expected Set");
    }
}

#[test]
fn test_normalize_uset_sset() {
    let d = IRDecl {
        name: mk_name("f"),
        params: vec![(VarId(10), IRType::Object), (VarId(20), IRType::USize)],
        return_type: IRType::Void,
        body: IRBody::USet {
            var: VarId(10),
            idx: 0,
            value: VarId(20),
            rest: Box::new(IRBody::SSet {
                var: VarId(10),
                n: 1,
                offset: 0,
                value: VarId(20),
                ty: IRType::UInt64,
                rest: Box::new(IRBody::Ret(IRArg::Erased)),
            }),
        },
    };
    let (norm, _) = normalize_ids_ext(&d);
    if let IRBody::USet {
        var, value, rest, ..
    } = &norm.body
    {
        assert_eq!(*var, VarId(0));
        assert_eq!(*value, VarId(1));
        if let IRBody::SSet {
            var: sv,
            value: sval,
            ..
        } = rest.as_ref()
        {
            assert_eq!(*sv, VarId(0));
            assert_eq!(*sval, VarId(1));
        }
    } else {
        panic!("expected USet");
    }
}

#[test]
fn test_content_hash_with_case() {
    let d = IRDecl {
        name: mk_name("f"),
        params: vec![(VarId(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::Case {
            scrutinee: VarId(0),
            alts: vec![IRAlt {
                ctor: mk_ctor("Some", 0, 1),
                body: Box::new(IRBody::Ret(IRArg::Var(VarId(0)))),
            }],
            default: Some(Box::new(IRBody::Unreachable)),
        },
    };
    let h = content_hash(&canonical_form(&d));
    assert_eq!(h, content_hash(&canonical_form(&d)));
}

#[test]
fn test_alpha_equiv_with_apply() {
    let mk = |vid: u32| IRDecl {
        name: mk_name("f"),
        params: vec![(VarId(vid), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: VarId(vid + 1),
            ty: IRType::Object,
            value: IRExpr::Apply {
                fn_id: mk_fn_id("g"),
                args: vec![IRArg::Var(VarId(vid))],
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(vid + 1)))),
        },
    };
    assert!(alpha_equiv(&mk(0), &mk(100)));
}

#[test]
fn test_alpha_equiv_different_fn_id_not_equiv() {
    let mk = |fn_name: &str| IRDecl {
        name: mk_name("f"),
        params: vec![(VarId(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: VarId(1),
            ty: IRType::Object,
            value: IRExpr::Apply {
                fn_id: mk_fn_id(fn_name),
                args: vec![IRArg::Var(VarId(0))],
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(1)))),
        },
    };
    assert!(!alpha_equiv(&mk("g"), &mk("h")));
}

#[test]
fn test_normalize_partial_apply() {
    let d = IRDecl {
        name: mk_name("f"),
        params: vec![(VarId(50), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: VarId(51),
            ty: IRType::Object,
            value: IRExpr::PartialApply {
                fn_id: mk_fn_id("g"),
                arity: 3,
                args: vec![IRArg::Var(VarId(50))],
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(51)))),
        },
    };
    let (norm, _) = normalize_ids_ext(&d);
    if let IRBody::VDecl {
        value: IRExpr::PartialApply { arity, .. },
        ..
    } = &norm.body
    {
        assert_eq!(*arity, 3);
    } else {
        panic!("expected PartialApply");
    }
}

#[test]
fn test_normalize_closure_apply() {
    let d = IRDecl {
        name: mk_name("f"),
        params: vec![(VarId(10), IRType::Object), (VarId(20), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: VarId(30),
            ty: IRType::Object,
            value: IRExpr::ClosureApply {
                closure: IRArg::Var(VarId(10)),
                args: vec![IRArg::Var(VarId(20))],
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(30)))),
        },
    };
    let (norm, stats) = normalize_ids_ext(&d);
    assert_eq!(stats.vars_renamed, 3);
    if let IRBody::VDecl {
        value: IRExpr::ClosureApply { closure, args },
        ..
    } = &norm.body
    {
        assert_eq!(*closure, IRArg::Var(VarId(0)));
        assert_eq!(args[0], IRArg::Var(VarId(1)));
    } else {
        panic!("expected ClosureApply");
    }
}

#[test]
fn test_collision_detection_empty() {
    let d = IdCollisions::default();
    assert!(d.is_empty());
    assert_eq!(d.total(), 0);
}

#[test]
fn test_normalize_box_unbox() {
    let d = IRDecl {
        name: mk_name("f"),
        params: vec![(VarId(10), IRType::UInt64)],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: VarId(20),
            ty: IRType::Object,
            value: IRExpr::Box {
                ty: IRType::UInt64,
                arg: IRArg::Var(VarId(10)),
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(20)))),
        },
    };
    let (norm, _) = normalize_ids_ext(&d);
    if let IRBody::VDecl {
        value: IRExpr::Box { ty, arg },
        ..
    } = &norm.body
    {
        assert_eq!(*ty, IRType::UInt64);
        assert_eq!(*arg, IRArg::Var(VarId(0)));
    } else {
        panic!("expected Box");
    }
}

#[test]
fn test_normalize_erased_args() {
    let d = IRDecl {
        name: mk_name("f"),
        params: vec![],
        return_type: IRType::Erased,
        body: IRBody::Ret(IRArg::Erased),
    };
    let (norm, stats) = normalize_ids_ext(&d);
    assert_eq!(stats.vars_renamed, 0);
    assert_eq!(norm.body, IRBody::Ret(IRArg::Erased));
}

#[test]
fn test_normalize_reset_reuse() {
    let d = IRDecl {
        name: mk_name("f"),
        params: vec![(VarId(10), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: VarId(20),
            ty: IRType::Object,
            value: IRExpr::Reset(VarId(10)),
            rest: Box::new(IRBody::VDecl {
                var: VarId(30),
                ty: IRType::Object,
                value: IRExpr::Reuse {
                    var: VarId(20),
                    ctor: mk_ctor("Pair", 0, 2),
                    args: vec![IRArg::Var(VarId(10)), IRArg::Var(VarId(10))],
                },
                rest: Box::new(IRBody::Ret(IRArg::Var(VarId(30)))),
            }),
        },
    };
    let (norm, stats) = normalize_ids_ext(&d);
    assert!(stats.vars_renamed > 0);
    if let IRBody::VDecl {
        var,
        value: IRExpr::Reset(rv),
        ..
    } = &norm.body
    {
        assert_eq!(*var, VarId(1));
        assert_eq!(*rv, VarId(0));
    } else {
        panic!("expected Reset");
    }
}

#[test]
fn test_normalize_uproj_sproj() {
    let d = IRDecl {
        name: mk_name("f"),
        params: vec![(VarId(10), IRType::Object)],
        return_type: IRType::USize,
        body: IRBody::VDecl {
            var: VarId(20),
            ty: IRType::USize,
            value: IRExpr::UProj {
                idx: 0,
                var: VarId(10),
            },
            rest: Box::new(IRBody::VDecl {
                var: VarId(30),
                ty: IRType::UInt8,
                value: IRExpr::SProj {
                    n: 1,
                    offset: 0,
                    var: VarId(10),
                    ty: IRType::UInt8,
                },
                rest: Box::new(IRBody::Ret(IRArg::Var(VarId(20)))),
            }),
        },
    };
    let (norm, _) = normalize_ids_ext(&d);
    if let IRBody::VDecl {
        value: IRExpr::UProj { var, .. },
        ..
    } = &norm.body
    {
        assert_eq!(*var, VarId(0));
    } else {
        panic!("expected UProj");
    }
}

#[test]
fn test_normalize_isshared() {
    let d = IRDecl {
        name: mk_name("f"),
        params: vec![(VarId(10), IRType::Object)],
        return_type: IRType::UInt8,
        body: IRBody::VDecl {
            var: VarId(20),
            ty: IRType::UInt8,
            value: IRExpr::IsShared(VarId(10)),
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(20)))),
        },
    };
    let (norm, _) = normalize_ids_ext(&d);
    if let IRBody::VDecl {
        value: IRExpr::IsShared(v),
        ..
    } = &norm.body
    {
        assert_eq!(*v, VarId(0));
    } else {
        panic!("expected IsShared");
    }
}
