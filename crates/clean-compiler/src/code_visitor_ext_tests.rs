// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for code_visitor_ext: extended IR body visitor/folder.
//! Part of #3083 - Extensibility.

use crate::code_visitor_ext::*;
use crate::ir::*;
use clean_kernel::Name;

// -- helpers -----------------------------------------------------------------

fn var(n: u32) -> VarId {
    VarId(n)
}
fn jp(n: u32) -> JoinPointId {
    JoinPointId(n)
}
fn fname(s: &str) -> FnId {
    FnId(Name::from_string(s))
}
fn cname(s: &str) -> Name {
    Name::from_string(s)
}

fn mk_ctor_info(tag: u32) -> CtorInfo {
    CtorInfo {
        name: cname("C"),
        tag,
        num_scalars: 0,
        num_objects: 0,
        field_types: vec![],
    }
}

fn simple_ret() -> IRBody {
    IRBody::Ret(IRArg::Var(var(0)))
}

fn simple_chain() -> IRBody {
    // let v1 = Lit(42); let v2 = Lit(100); ret v2
    IRBody::VDecl {
        var: var(1),
        ty: IRType::UInt64,
        value: IRExpr::Lit(IRLiteral::UInt64(42)),
        rest: Box::new(IRBody::VDecl {
            var: var(2),
            ty: IRType::UInt64,
            value: IRExpr::Lit(IRLiteral::UInt64(100)),
            rest: Box::new(IRBody::Ret(IRArg::Var(var(2)))),
        }),
    }
}

fn with_jdecl() -> IRBody {
    // jdecl jp0 () = ret v0; jmp jp0
    IRBody::JDecl {
        jp: jp(0),
        params: vec![(var(10), IRType::Object)],
        body: Box::new(simple_ret()),
        rest: Box::new(IRBody::Jmp {
            jp: jp(0),
            args: vec![],
        }),
    }
}

fn with_case() -> IRBody {
    IRBody::Case {
        scrutinee: var(0),
        alts: vec![
            IRAlt {
                ctor: mk_ctor_info(0),
                body: Box::new(IRBody::Ret(IRArg::Var(var(1)))),
            },
            IRAlt {
                ctor: mk_ctor_info(1),
                body: Box::new(IRBody::Ret(IRArg::Var(var(2)))),
            },
        ],
        default: Some(Box::new(IRBody::Unreachable)),
    }
}

fn with_inc_dec() -> IRBody {
    IRBody::Inc {
        var: var(5),
        n: 1,
        rest: Box::new(IRBody::Dec {
            var: var(5),
            rest: Box::new(simple_ret()),
        }),
    }
}

fn with_apply() -> IRBody {
    IRBody::VDecl {
        var: var(3),
        ty: IRType::Object,
        value: IRExpr::Apply {
            fn_id: fname("f"),
            args: vec![IRArg::Var(var(0)), IRArg::Var(var(1))],
        },
        rest: Box::new(IRBody::Ret(IRArg::Var(var(3)))),
    }
}

fn with_set() -> IRBody {
    IRBody::Set {
        var: var(0),
        idx: 0,
        value: var(1),
        rest: Box::new(simple_ret()),
    }
}

fn mk_decl(body: IRBody) -> IRDecl {
    IRDecl {
        name: cname("test_fn"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body,
    }
}

// =============================================================================
// IRBodyVisitor tests
// =============================================================================

struct NodeCounter;
impl IRBodyVisitor for NodeCounter {
    type Result = usize;
    fn combine(&self, a: usize, b: usize) -> usize {
        a + b
    }
    fn visit_vdecl(&mut self, _: VarId, _: &IRType, _: &IRExpr, rest: &IRBody) -> usize {
        1 + self.visit_body(rest)
    }
    fn visit_jdecl(
        &mut self,
        _: JoinPointId,
        _: &[(VarId, IRType)],
        body: &IRBody,
        rest: &IRBody,
    ) -> usize {
        1 + self.visit_body(body) + self.visit_body(rest)
    }
    fn visit_inc(&mut self, _: VarId, _: u32, rest: &IRBody) -> usize {
        1 + self.visit_body(rest)
    }
    fn visit_dec(&mut self, _: VarId, rest: &IRBody) -> usize {
        1 + self.visit_body(rest)
    }
    fn visit_case(&mut self, _: VarId, alts: &[IRAlt], def: Option<&IRBody>) -> usize {
        let mut r = 1usize;
        for a in alts {
            r += self.visit_body(&a.body);
        }
        if let Some(d) = def {
            r += self.visit_body(d);
        }
        r
    }
    fn visit_jmp(&mut self, _: JoinPointId, _: &[IRArg]) -> usize {
        1
    }
    fn visit_ret(&mut self, _: &IRArg) -> usize {
        1
    }
    fn visit_unreachable(&mut self) -> usize {
        1
    }
}

#[test]
fn test_visitor_simple_ret() {
    assert_eq!(NodeCounter.visit_body(&simple_ret()), 1);
}

#[test]
fn test_visitor_chain() {
    assert_eq!(NodeCounter.visit_body(&simple_chain()), 3);
}

#[test]
fn test_visitor_jdecl() {
    assert_eq!(NodeCounter.visit_body(&with_jdecl()), 3);
}

#[test]
fn test_visitor_case() {
    assert_eq!(NodeCounter.visit_body(&with_case()), 4);
}

#[test]
fn test_visitor_inc_dec() {
    assert_eq!(NodeCounter.visit_body(&with_inc_dec()), 3);
}

#[test]
fn test_visitor_unreachable() {
    assert_eq!(NodeCounter.visit_body(&IRBody::Unreachable), 1);
}

struct RetCounter;
impl IRBodyVisitor for RetCounter {
    type Result = usize;
    fn combine(&self, a: usize, b: usize) -> usize {
        a + b
    }
    fn visit_ret(&mut self, _: &IRArg) -> usize {
        1
    }
}

#[test]
fn test_visitor_ret_count_chain() {
    assert_eq!(RetCounter.visit_body(&simple_chain()), 1);
}

#[test]
fn test_visitor_ret_count_case() {
    assert_eq!(RetCounter.visit_body(&with_case()), 2);
}

#[test]
fn test_visitor_ret_count_jdecl() {
    assert_eq!(RetCounter.visit_body(&with_jdecl()), 1);
}

// =============================================================================
// IRBodyFolder tests
// =============================================================================

struct IdentityFolder;
impl IRBodyFolder for IdentityFolder {}

// We need PartialEq on IRBody for testing. Use Debug format comparison since
// IRBody derives Serialize/Deserialize but not PartialEq.
fn body_eq(a: &IRBody, b: &IRBody) -> bool {
    format!("{:?}", a) == format!("{:?}", b)
}

#[test]
fn test_folder_identity_ret() {
    let b = simple_ret();
    assert!(body_eq(&IdentityFolder.fold_body(&b), &b));
}

#[test]
fn test_folder_identity_chain() {
    let b = simple_chain();
    assert!(body_eq(&IdentityFolder.fold_body(&b), &b));
}

#[test]
fn test_folder_identity_jdecl() {
    let b = with_jdecl();
    assert!(body_eq(&IdentityFolder.fold_body(&b), &b));
}

#[test]
fn test_folder_identity_case() {
    let b = with_case();
    assert!(body_eq(&IdentityFolder.fold_body(&b), &b));
}

#[test]
fn test_folder_identity_inc_dec() {
    let b = with_inc_dec();
    assert!(body_eq(&IdentityFolder.fold_body(&b), &b));
}

#[test]
fn test_folder_identity_set() {
    let b = with_set();
    assert!(body_eq(&IdentityFolder.fold_body(&b), &b));
}

/// Folder that removes all Inc nodes (dead RC elimination).
struct DropIncFolder;
impl IRBodyFolder for DropIncFolder {
    fn fold_inc(&mut self, _var: VarId, _n: u32, rest: IRBody) -> IRBody {
        self.fold_body(&rest)
    }
}

#[test]
fn test_folder_drop_inc() {
    let b = with_inc_dec();
    let folded = DropIncFolder.fold_body(&b);
    // Inc removed, only Dec + Ret remain = 2 nodes
    assert_eq!(NodeCounter.visit_body(&folded), 2);
}

/// Folder that rewrites Ret to always return var(99).
struct RetRewriter;
impl IRBodyFolder for RetRewriter {
    fn fold_ret(&mut self, _arg: IRArg) -> IRBody {
        IRBody::Ret(IRArg::Var(var(99)))
    }
}

#[test]
fn test_folder_rewrite_ret_chain() {
    let folded = RetRewriter.fold_body(&simple_chain());
    // Terminal should now be Ret(99)
    match &folded {
        IRBody::VDecl { rest, .. } => match rest.as_ref() {
            IRBody::VDecl { rest, .. } => match rest.as_ref() {
                IRBody::Ret(IRArg::Var(v)) => assert_eq!(*v, var(99)),
                other => panic!("expected Ret(99), got: {:?}", other),
            },
            other => panic!("expected VDecl, got: {:?}", other),
        },
        other => panic!("expected VDecl, got: {:?}", other),
    }
}

#[test]
fn test_folder_rewrite_ret_case() {
    let folded = RetRewriter.fold_body(&with_case());
    // Both case alt rets should be Var(99)
    if let IRBody::Case { alts, .. } = &folded {
        for alt in alts {
            match alt.body.as_ref() {
                IRBody::Ret(IRArg::Var(v)) => assert_eq!(*v, var(99)),
                other => panic!("expected Ret(99), got: {:?}", other),
            }
        }
    } else {
        panic!("expected Case");
    }
}

// =============================================================================
// IRExprVisitor tests
// =============================================================================

struct ExprCategoryCounter {
    ctors: usize,
    apps: usize,
    lits: usize,
    others: usize,
}
impl IRExprVisitor for ExprCategoryCounter {
    type Result = ();
    fn combine(&self, _: (), _: ()) {}
    fn visit_ctor(&mut self, _: &[IRArg]) {
        self.ctors += 1;
    }
    fn visit_apply(&mut self, _: &[IRArg]) {
        self.apps += 1;
    }
    fn visit_lit(&mut self) {
        self.lits += 1;
    }
    fn visit_other(&mut self) {
        self.others += 1;
    }
}

#[test]
fn test_expr_visitor_lit() {
    let mut v = ExprCategoryCounter {
        ctors: 0,
        apps: 0,
        lits: 0,
        others: 0,
    };
    v.visit_expr(&IRExpr::Lit(IRLiteral::UInt64(42)));
    assert_eq!(v.lits, 1);
}

#[test]
fn test_expr_visitor_apply() {
    let mut v = ExprCategoryCounter {
        ctors: 0,
        apps: 0,
        lits: 0,
        others: 0,
    };
    v.visit_expr(&IRExpr::Apply {
        fn_id: fname("f"),
        args: vec![],
    });
    assert_eq!(v.apps, 1);
}

#[test]
fn test_expr_visitor_ctor() {
    let mut v = ExprCategoryCounter {
        ctors: 0,
        apps: 0,
        lits: 0,
        others: 0,
    };
    v.visit_expr(&IRExpr::Ctor {
        info: mk_ctor_info(0),
        args: vec![],
    });
    assert_eq!(v.ctors, 1);
}

#[test]
fn test_expr_visitor_tag() {
    let mut v = ExprCategoryCounter {
        ctors: 0,
        apps: 0,
        lits: 0,
        others: 0,
    };
    v.visit_expr(&IRExpr::Tag(IRArg::Var(var(0))));
    assert_eq!(v.others, 1);
}

#[test]
fn test_expr_visitor_string_is_lit() {
    let mut v = ExprCategoryCounter {
        ctors: 0,
        apps: 0,
        lits: 0,
        others: 0,
    };
    v.visit_expr(&IRExpr::String("hello".to_string()));
    assert_eq!(v.lits, 1);
}

// =============================================================================
// ScopeTracker tests
// =============================================================================

#[test]
fn test_scope_tracker_empty() {
    let s = ScopeTracker::default();
    assert!(!s.is_bound(var(0)));
    assert_eq!(s.depth, 0);
}

#[test]
fn test_scope_tracker_enter_vdecl() {
    let mut s = ScopeTracker::default();
    s.enter_vdecl(var(1), &IRType::UInt64);
    assert!(s.is_bound(var(1)));
    assert_eq!(s.lookup(var(1)), Some(&IRType::UInt64));
}

#[test]
fn test_scope_tracker_enter_jdecl() {
    let mut s = ScopeTracker::default();
    s.enter_jdecl(jp(0), &[(var(10), IRType::Object)]);
    assert!(s.is_bound(var(10)));
    assert_eq!(s.depth, 1);
    assert!(s.join_points.contains_key(&jp(0)));
}

#[test]
fn test_scope_tracker_exit_jdecl() {
    let mut s = ScopeTracker::default();
    s.enter_jdecl(jp(0), &[]);
    s.exit_jdecl();
    assert_eq!(s.depth, 0);
}

#[test]
fn test_scope_tracker_depth_saturates() {
    let mut s = ScopeTracker::default();
    s.exit_jdecl(); // should not underflow
    assert_eq!(s.depth, 0);
}

#[test]
fn test_scope_tracker_multiple_bindings() {
    let mut s = ScopeTracker::default();
    s.enter_vdecl(var(1), &IRType::UInt32);
    s.enter_vdecl(var(2), &IRType::Bool);
    assert!(s.is_bound(var(1)));
    assert!(s.is_bound(var(2)));
    assert!(!s.is_bound(var(3)));
}

// =============================================================================
// SelectiveFilter tests
// =============================================================================

#[test]
fn test_filter_all_allows_everything() {
    let f = SelectiveFilter::all();
    assert!(f.allows(&simple_ret()));
    assert!(f.allows(&IRBody::Unreachable));
    assert!(f.allows(&IRBody::Jmp {
        jp: jp(0),
        args: vec![]
    }));
}

#[test]
fn test_filter_selective_only_ret() {
    let f = SelectiveFilter::new(&[NodeCategory::Ret]);
    assert!(f.allows(&simple_ret()));
    assert!(!f.allows(&IRBody::Unreachable));
    assert!(!f.allows(&IRBody::Jmp {
        jp: jp(0),
        args: vec![]
    }));
}

#[test]
fn test_filter_selective_inc_dec() {
    let f = SelectiveFilter::new(&[NodeCategory::Inc, NodeCategory::Dec]);
    let body = with_inc_dec();
    assert!(f.allows(&body)); // Inc at top
}

#[test]
fn test_filter_empty_rejects_all() {
    let f = SelectiveFilter::new(&[]);
    assert!(!f.allows(&simple_ret()));
    assert!(!f.allows(&IRBody::Unreachable));
}

// =============================================================================
// NodeCategory tests
// =============================================================================

#[test]
fn test_node_category_of_body() {
    assert_eq!(NodeCategory::of_body(&simple_ret()), NodeCategory::Ret);
    assert_eq!(
        NodeCategory::of_body(&IRBody::Unreachable),
        NodeCategory::Unreachable
    );
    assert_eq!(
        NodeCategory::of_body(&IRBody::Jmp {
            jp: jp(0),
            args: vec![]
        }),
        NodeCategory::Jmp
    );
    assert_eq!(NodeCategory::of_body(&simple_chain()), NodeCategory::VDecl);
}

// =============================================================================
// VarCollector tests
// =============================================================================

#[test]
fn test_var_collector_simple_ret() {
    let vars = VarCollector::collect(&simple_ret());
    assert_eq!(vars, vec![var(0)]);
}

#[test]
fn test_var_collector_chain() {
    let vars = VarCollector::collect(&simple_chain());
    assert!(vars.contains(&var(1)));
    assert!(vars.contains(&var(2)));
    assert_eq!(vars.len(), 3); // v1, v2, ret(v2)
}

#[test]
fn test_var_collector_jdecl() {
    let vars = VarCollector::collect(&with_jdecl());
    assert!(vars.contains(&var(10))); // param
    assert!(vars.contains(&var(0))); // ret
}

#[test]
fn test_var_collector_case() {
    let vars = VarCollector::collect(&with_case());
    assert!(vars.contains(&var(0))); // scrutinee
    assert!(vars.contains(&var(1)));
    assert!(vars.contains(&var(2)));
}

#[test]
fn test_var_collector_inc_dec() {
    let vars = VarCollector::collect(&with_inc_dec());
    let count_v5 = vars.iter().filter(|&&v| v == var(5)).count();
    assert_eq!(count_v5, 2); // inc(5) + dec(5)
}

#[test]
fn test_var_collector_apply_expr() {
    let vars = VarCollector::collect(&with_apply());
    assert!(vars.contains(&var(0)));
    assert!(vars.contains(&var(1)));
    assert!(vars.contains(&var(3)));
}

#[test]
fn test_var_collector_set() {
    let vars = VarCollector::collect(&with_set());
    assert!(vars.contains(&var(0)));
    assert!(vars.contains(&var(1)));
}

#[test]
fn test_var_collector_unreachable_empty() {
    let vars = VarCollector::collect(&IRBody::Unreachable);
    assert!(vars.is_empty());
}

// =============================================================================
// independent_subtrees tests
// =============================================================================

#[test]
fn test_subtrees_case() {
    let b = with_case();
    let subs = independent_subtrees(&b);
    assert_eq!(subs.len(), 3); // 2 alts + 1 default
}

#[test]
fn test_subtrees_jdecl() {
    let b = with_jdecl();
    let subs = independent_subtrees(&b);
    assert_eq!(subs.len(), 2); // body + rest
}

#[test]
fn test_subtrees_ret_empty() {
    assert!(independent_subtrees(&simple_ret()).is_empty());
}

#[test]
fn test_subtrees_chain_empty() {
    assert!(independent_subtrees(&simple_chain()).is_empty());
}

// =============================================================================
// compose_visitors tests
// =============================================================================

#[test]
fn test_compose_visitors_both_run() {
    let mut counter = NodeCounter;
    let mut ret_counter = RetCounter;
    let body = with_case();
    let (total, rets) = compose_visitors(&mut counter, &mut ret_counter, &body);
    assert_eq!(total, 4);
    assert_eq!(rets, 2);
}

#[test]
fn test_compose_visitors_simple() {
    let mut a = NodeCounter;
    let mut b = RetCounter;
    let (total, rets) = compose_visitors(&mut a, &mut b, &simple_ret());
    assert_eq!(total, 1);
    assert_eq!(rets, 1);
}

// =============================================================================
// VisitStats tests
// =============================================================================

#[test]
fn test_visit_stats_defaults() {
    let s = VisitStats::default();
    assert_eq!(s.total_visited(), 0);
    assert_eq!(s.transformed, 0);
    assert_eq!(s.skipped, 0);
}

#[test]
fn test_visit_stats_record() {
    let mut s = VisitStats::default();
    s.record_visit(NodeCategory::Ret);
    s.record_visit(NodeCategory::Ret);
    s.record_visit(NodeCategory::VDecl);
    s.record_transform();
    s.record_skip();
    assert_eq!(s.total_visited(), 3);
    assert_eq!(s.visited[&NodeCategory::Ret], 2);
    assert_eq!(s.visited[&NodeCategory::VDecl], 1);
    assert_eq!(s.transformed, 1);
    assert_eq!(s.skipped, 1);
}

// =============================================================================
// walk_with_stats tests
// =============================================================================

#[test]
fn test_walk_stats_topdown_all() {
    let mut stats = VisitStats::default();
    let mut count = 0usize;
    walk_with_stats(
        &simple_chain(),
        TraversalOrder::TopDown,
        &SelectiveFilter::all(),
        &mut stats,
        &mut |_| count += 1,
    );
    assert_eq!(count, 3);
    assert_eq!(stats.total_visited(), 3);
    assert_eq!(stats.skipped, 0);
}

#[test]
fn test_walk_stats_bottomup_all() {
    let mut stats = VisitStats::default();
    let mut order_check = Vec::new();
    walk_with_stats(
        &simple_chain(),
        TraversalOrder::BottomUp,
        &SelectiveFilter::all(),
        &mut stats,
        &mut |b| {
            order_check.push(NodeCategory::of_body(b));
        },
    );
    // Bottom-up: Ret first, then inner VDecl, then outer VDecl
    assert_eq!(
        order_check,
        vec![NodeCategory::Ret, NodeCategory::VDecl, NodeCategory::VDecl]
    );
}

#[test]
fn test_walk_stats_topdown_order() {
    let mut stats = VisitStats::default();
    let mut order_check = Vec::new();
    walk_with_stats(
        &simple_chain(),
        TraversalOrder::TopDown,
        &SelectiveFilter::all(),
        &mut stats,
        &mut |b| {
            order_check.push(NodeCategory::of_body(b));
        },
    );
    // Top-down: outer VDecl, inner VDecl, Ret
    assert_eq!(
        order_check,
        vec![NodeCategory::VDecl, NodeCategory::VDecl, NodeCategory::Ret]
    );
}

#[test]
fn test_walk_stats_selective_filter() {
    let mut stats = VisitStats::default();
    let filter = SelectiveFilter::new(&[NodeCategory::Ret]);
    let mut count = 0;
    walk_with_stats(
        &simple_chain(),
        TraversalOrder::TopDown,
        &filter,
        &mut stats,
        &mut |_| count += 1,
    );
    assert_eq!(count, 1); // Only Ret visited
    assert_eq!(stats.skipped, 2); // Two VDecl nodes skipped
    assert_eq!(stats.total_visited(), 1);
}

#[test]
fn test_walk_stats_case_branches() {
    let mut stats = VisitStats::default();
    let mut count = 0;
    walk_with_stats(
        &with_case(),
        TraversalOrder::TopDown,
        &SelectiveFilter::all(),
        &mut stats,
        &mut |_| count += 1,
    );
    assert_eq!(count, 4); // Case + 2 Ret + Unreachable
}

// =============================================================================
// visit_decl_exprs tests
// =============================================================================

#[test]
fn test_visit_decl_exprs_chain() {
    let decl = mk_decl(simple_chain());
    let mut exprs = Vec::new();
    visit_decl_exprs(&decl, &mut |e| exprs.push(format!("{:?}", e)));
    assert_eq!(exprs.len(), 2); // Two Lit expressions
}

#[test]
fn test_visit_decl_exprs_apply() {
    let decl = mk_decl(with_apply());
    let mut count = 0;
    visit_decl_exprs(&decl, &mut |_| count += 1);
    assert_eq!(count, 1); // One Apply expression
}

#[test]
fn test_visit_decl_exprs_none_in_ret() {
    let decl = mk_decl(simple_ret());
    let mut count = 0;
    visit_decl_exprs(&decl, &mut |_| count += 1);
    assert_eq!(count, 0); // No expressions in bare Ret
}

// =============================================================================
// TraversalOrder tests
// =============================================================================

#[test]
fn test_traversal_order_eq() {
    assert_eq!(TraversalOrder::TopDown, TraversalOrder::TopDown);
    assert_ne!(TraversalOrder::TopDown, TraversalOrder::BottomUp);
}

#[test]
fn test_traversal_order_clone() {
    let o = TraversalOrder::BottomUp;
    let o2 = o;
    assert_eq!(o, o2);
}
