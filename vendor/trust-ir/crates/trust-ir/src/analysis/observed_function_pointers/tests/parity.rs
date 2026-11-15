// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn complete_copy_reify_origin_and_exact_use_fields_match_actual_original() {
    let f = chain();
    let (answer, _) = query(&f, 2, 0, 3);
    let a = answer.unwrap();
    assert_eq!(a.containing_function(), f.id);
    assert_eq!(a.function(), FuncId::new(7));
    assert_eq!(a.declared_signature(), FuncTyId::new(0));
    assert_eq!(a.carrier(), StaticFunctionPointerCarrier::Pointer);
    assert_eq!(a.origin_value(), v(0));
    assert_eq!(a.origin_instruction_index(), 0);
    assert_eq!(a.queried_value(), v(2));
    assert_eq!(a.use_instruction_index(), 3);
    assert_eq!(a.chain_definitions(), 3);
}
#[test]
fn duplicate_definitions_parameters_and_multi_results_remain_unresolvable() {
    let cases = [
        vec![seed(0, 7), seed(0, 8), call(0), ret()],
        vec![seed(0, 7).with_result(v(1)), call(0), ret()],
        vec![seed(0, 7), seed(0, 8).with_result(v(1)), call(0), ret()],
    ];
    for body in cases {
        let f = function(body);
        let index = f.blocks[0].body.len() - 2;
        assert_eq!(query(&f, 0, 0, index).0, None);
    }
    let mut f = function(vec![seed(0, 7), call(0), ret()]);
    f.blocks[0].params.push((v(0), ft(0)));
    assert_eq!(query(&f, 0, 0, 1).0, None);
    let mut duplicate_blocks = chain();
    duplicate_blocks
        .blocks
        .push(duplicate_blocks.blocks[0].clone());
    assert_eq!(query(&duplicate_blocks, 2, 0, 3).0, None);
}
#[test]
fn cycle_prefix_and_noncandidate_dependency_keep_the_original_sparse_memo() {
    for (body, value) in [
        (
            vec![
                copy(0, 1, ft(0)),
                copy(1, 0, ft(0)),
                copy(2, 0, ft(0)),
                call(2),
                ret(),
            ],
            2,
        ),
        (
            vec![
                copy(0, 1, Ty::Ptr),
                copy(1, 2, Ty::I32),
                copy(2, 3, Ty::I32),
                call(0),
                ret(),
            ],
            0,
        ),
    ] {
        let f = function(body);
        let mut o = Observer::default();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut a =
            ObservedStaticFunctionPointerAnalysis::new_observed(&f, &mut s, site()).unwrap();
        let old = StaticFunctionPointerAnalysis::new(&f);
        let index = f.blocks[0].body.len() - 2;
        assert_eq!(
            a.resolve_typed_at_observed(v(value), BlockId::new(0), index, &mut s, site())
                .unwrap(),
            old.resolve_typed_at(v(value), BlockId::new(0), index)
        );
        assert_eq!(
            format!("{:?}", a.state.provenances),
            format!("{:?}", old.provenances.get().unwrap().entries)
        );
        assert!(a.state.active.is_empty() && a.state.path.is_empty());
        a.retire_observed(&mut s, site()).unwrap();
    }
}
#[test]
fn dominating_cross_block_origin_accepts_but_sibling_and_unreachable_definitions_refuse() {
    let mut f = function(vec![
        seed(0, 7),
        InstrNode::new(Inst::CondBr {
            cond: v(9),
            then_target: BlockId::new(1),
            then_args: vec![],
            else_target: BlockId::new(2),
            else_args: vec![],
        }),
    ]);
    let mut b = Block::new(BlockId::new(1));
    b.body = vec![call(0), ret()];
    let mut c = Block::new(BlockId::new(2));
    c.body = vec![ret()];
    f.blocks.extend([b, c]);
    assert!(query(&f, 0, 1, 0).0.is_some());
    let seed = f.blocks[0].body.remove(0);
    f.blocks[1].body.insert(0, seed);
    f.blocks[2].body.insert(0, call(0));
    assert_eq!(query(&f, 0, 2, 0).0, None);
    f.blocks[0].body = vec![ret()];
    assert_eq!(query(&f, 0, 1, 1).0, None);
}
#[test]
fn complete_all_actual_cache_rows_match_original_after_success() {
    let f = chain();
    let old = StaticFunctionPointerAnalysis::new(&f);
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut a = ObservedStaticFunctionPointerAnalysis::new_observed(&f, &mut s, site()).unwrap();
    assert_eq!(
        a.resolve_typed_at_observed(v(2), BlockId::new(0), 3, &mut s, site())
            .unwrap(),
        old.resolve_typed_at(v(2), BlockId::new(0), 3)
    );
    assert_eq!(
        format!("{:?}", a.state.uses),
        format!("{:?}", old.use_sites.get().unwrap().blocks)
    );
    assert_eq!(
        format!("{:?}", a.state.definitions),
        format!("{:?}", old.definitions.get().unwrap().entries)
    );
    assert_eq!(
        format!("{:?}", a.state.provenances),
        format!("{:?}", old.provenances.get().unwrap().entries)
    );
    let tree = a.state.dominators.as_ref().unwrap();
    let expected = old.dominators.get().unwrap();
    assert_eq!(tree.reachable, expected.reachable);
    assert_eq!(tree.preorder, expected.preorder);
    assert_eq!(tree.postorder, expected.postorder);
    a.retire_observed(&mut s, site()).unwrap();
}
#[test]
fn raw_carrier_and_signature_laundering_and_same_carrier_reify_are_rejected() {
    for body in [
        vec![seed(0, 7), copy(1, 0, Ty::Ptr), call(1), ret()],
        vec![seed(0, 7), reify(1, 0, ft(0), ft(0)), call(1), ret()],
        vec![
            seed(0, 7),
            reify(1, 0, ft(0), Ty::Ptr),
            reify(2, 1, Ty::Ptr, ft(1)),
            call(2),
            ret(),
        ],
    ] {
        let f = function(body);
        let index = f.blocks[0].body.len() - 2;
        let value = if index == 3 { 2 } else { 1 };
        assert_eq!(query(&f, value, 0, index).0, None);
    }
    let f = function(vec![
        seed(0, 7),
        reify(1, 0, ft(0), Ty::Ptr),
        reify(2, 1, Ty::Ptr, ft(0)),
        call(2),
        ret(),
    ]);
    assert!(query(&f, 2, 0, 3).0.is_some());
}
#[test]
fn sorted_reverse_id_provenance_and_long_chain_have_no_arbitrary_depth_cutoff() {
    let mut body = vec![seed(128, 7)];
    for value in (0..128).rev() {
        body.push(copy(value, value + 1, ft(0)));
    }
    let index = body.len();
    body.extend([call(0), ret()]);
    let f = function(body);
    assert_eq!(query(&f, 0, 0, index).0.unwrap().chain_definitions(), 129);
}
#[test]
fn identical_ids_in_another_function_cannot_supply_a_borrowed_cache() {
    let f = chain();
    let mut other = chain();
    other.id = FuncId::new(99);
    other.blocks[0].body[0] = seed(0, 88);
    assert_eq!(query(&f, 2, 0, 3).0.unwrap().function(), FuncId::new(7));
    let a = query(&other, 2, 0, 3).0.unwrap();
    assert_eq!(a.function(), FuncId::new(88));
    assert_eq!(a.containing_function(), FuncId::new(99));
}
