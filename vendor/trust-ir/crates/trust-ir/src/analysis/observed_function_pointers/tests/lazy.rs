// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn constructor_borrows_without_initializing_any_component() {
    let f = chain();
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let a = ObservedStaticFunctionPointerAnalysis::new_observed(&f, &mut s, site()).unwrap();
    assert!(core::ptr::eq(a.function, &f));
    empty(&a.state);
    a.retire_observed(&mut s, site()).unwrap();
}
#[test]
fn unrelated_node_missing_block_and_bad_index_never_initialize_definitions() {
    let f = chain();
    for (block, index, value) in [(0, 4, 2), (991, 3, 2), (0, usize::MAX, 2), (0, 3, 77)] {
        assert_eq!(query(&f, value, block, index).0, None);
    }
}
#[test]
fn parameter_use_first_operand_does_not_walk_high_arity_unused_tail() {
    let mut traces = Vec::new();
    for size in [0, 4096] {
        let mut f = function(vec![call(0), ret()]);
        f.blocks[0].params.push((v(0), ft(0)));
        if let Inst::CallIndirect { args, .. } = &mut f.blocks[0].body[0].inst {
            *args = (1..=size).map(v).collect();
        }
        let mut o = Observer::default();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut a =
            ObservedStaticFunctionPointerAnalysis::new_observed(&f, &mut s, site()).unwrap();
        assert_eq!(
            a.resolve_typed_at_observed(v(0), BlockId::new(0), 0, &mut s, site())
                .unwrap(),
            None
        );
        assert!(a.state.use_built && !a.state.definitions_built && a.state.dominators.is_none());
        a.retire_observed(&mut s, site()).unwrap();
        drop(s);
        traces.push(o.events);
    }
    assert_eq!(traces[0], traces[1]);
}
#[test]
fn local_dynamic_forward_and_duplicate_prefilter_preserves_cache_free_rejection() {
    for (body, index) in [
        (
            vec![
                InstrNode::new(Inst::NullPtr).with_result(v(0)),
                call(0),
                ret(),
            ],
            1,
        ),
        (vec![call(0), seed(0, 7), ret()], 0),
        (vec![seed(0, 7), seed(0, 8), call(0), ret()], 2),
    ] {
        let f = function(body);
        let mut o = Observer::default();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut a =
            ObservedStaticFunctionPointerAnalysis::new_observed(&f, &mut s, site()).unwrap();
        assert_eq!(
            a.resolve_typed_at_observed(v(0), BlockId::new(0), index, &mut s, site())
                .unwrap(),
            None
        );
        assert!(!a.state.definitions_built && a.state.dominators.is_none());
        a.retire_observed(&mut s, site()).unwrap();
    }
}
#[test]
fn prefilter_inspects_only_single_result_header_inside_original_nine_window() {
    let mut traces = Vec::new();
    for size in [2, 4096] {
        let mut f = function(vec![seed(0, 7), call(0), ret()]);
        f.blocks[0].body[0].results = (0..size).map(v).collect();
        let mut o = Observer::default();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut work = Work {
            session: &mut s,
            site: site(),
        };
        assert!(!prefilter::dynamic(&f.blocks[0], v(0), 1, &mut work).unwrap());
        drop(work);
        drop(s);
        traces.push(o.events);
    }
    assert_eq!(traces[0], traces[1]);
}
#[test]
fn whole_caches_build_once_while_each_actual_use_still_authenticates() {
    let mut f = chain();
    f.blocks[0].body.insert(4, call(2));
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut a = ObservedStaticFunctionPointerAnalysis::new_observed(&f, &mut s, site()).unwrap();
    let first = a
        .resolve_typed_at_observed(v(2), BlockId::new(0), 3, &mut s, site())
        .unwrap();
    let rows = a.state.definitions.len();
    let memo = a.state.provenances.len();
    let second = a
        .resolve_typed_at_observed(v(2), BlockId::new(0), 4, &mut s, site())
        .unwrap();
    assert_eq!(first.unwrap().function(), second.unwrap().function());
    assert_eq!(a.state.definitions.len(), rows);
    assert_eq!(a.state.provenances.len(), memo);
    assert_eq!(
        a.resolve_typed_at_observed(v(2), BlockId::new(0), 5, &mut s, site())
            .unwrap(),
        None
    );
    assert_eq!(a.state.provenances.len(), memo);
    a.retire_observed(&mut s, site()).unwrap();
}
#[test]
fn unsupported_top_producer_outside_prefilter_builds_definitions_but_no_cfg() {
    let mut body = vec![InstrNode::new(Inst::NullPtr).with_result(v(0))];
    body.extend((1..12).map(|_| InstrNode::new(Inst::NullPtr)));
    let index = body.len();
    body.extend([call(0), ret()]);
    let f = function(body);
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut a = ObservedStaticFunctionPointerAnalysis::new_observed(&f, &mut s, site()).unwrap();
    assert_eq!(
        a.resolve_typed_at_observed(v(0), BlockId::new(0), index, &mut s, site())
            .unwrap(),
        None
    );
    assert!(a.state.definitions_built && !a.state.provenance_built && a.state.dominators.is_none());
    a.retire_observed(&mut s, site()).unwrap();
}
#[test]
fn malformed_cfg_retains_only_fail_closed_tree_and_no_provenance() {
    let mut f = chain();
    f.blocks[0].body.pop();
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut a = ObservedStaticFunctionPointerAnalysis::new_observed(&f, &mut s, site()).unwrap();
    assert_eq!(
        a.resolve_typed_at_observed(v(2), BlockId::new(0), 3, &mut s, site())
            .unwrap(),
        None
    );
    assert!(!a.state.dominators.as_ref().unwrap().is_well_formed());
    assert!(!a.state.provenance_built);
    a.retire_observed(&mut s, site()).unwrap();
}
