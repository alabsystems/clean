// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
mod fixed;

#[test]
fn switch_preserves_selector_default_then_cases_and_every_duplicate() {
    assert_eq!(parity(&switch(false, 2)), ids(&[1, 2, 1, 3, 3, 4, 3, 3, 4]));
    assert_eq!(parity(&switch(true, 7)), ids(&[1]));
    assert_eq!(parity(&switch(false, 0)), ids(&[1, 2, 1]));
}

#[test]
fn all_four_invokes_preserve_call_kind_site_and_normal_edge_order() {
    let expected = [
        ids(&[1, 2, 3, 1]),
        ids(&[90, 1, 2, 3, 1]),
        ids(&[90, 3, 1]),
        ids(&[1, 2, 3, 4, 5, 1]),
    ];
    for (instruction, expected) in invocations().into_iter().zip(expected) {
        assert_eq!(parity(&instruction), expected);
    }
}

#[test]
fn every_assert_kind_location_and_optional_site_matches_original() {
    let mut kinds = vec![
        AssertKind::Unspecified,
        AssertKind::DivByZero,
        AssertKind::RemByZero,
        AssertKind::NullPtr,
        AssertKind::BoundsCheck {
            index: v(2),
            len: v(3),
        },
        AssertKind::MisalignedPtr {
            required: v(2),
            found: v(3),
        },
    ];
    kinds.extend(AssertOverflowOp::ALL.into_iter().map(AssertKind::Overflow));
    for kind in kinds {
        for location in [
            None,
            Some(PanicLocation::Global(GlobalId::new(80))),
            Some(PanicLocation::Value(v(4))),
        ] {
            let site = location.map(|location| PanicSite {
                entry: FuncId::new(81),
                location,
            });
            let instruction = Inst::Assert {
                cond: v(1),
                kind,
                site,
            };
            let mut expected = ids(&[1]);
            if matches!(
                kind,
                AssertKind::BoundsCheck { .. } | AssertKind::MisalignedPtr { .. }
            ) {
                expected.extend(ids(&[2, 3]));
            }
            if matches!(location, Some(PanicLocation::Value(_))) {
                expected.push(v(4));
            }
            assert_eq!(parity(&instruction), expected);
            if let Some(site) = site {
                let instruction = Inst::AssertInvoke {
                    cond: v(1),
                    kind,
                    site,
                    normal_dest: BlockId::new(82),
                    normal_args: ids(&[5, 1]),
                    unwind_dest: BlockId::new(83),
                };
                expected.extend(ids(&[5, 1]));
                assert_eq!(parity(&instruction), expected);
            }
        }
    }
}

#[test]
fn direct_and_indirect_calls_branches_and_argument_lists_keep_definition_ids_out() {
    let instructions = vec![
        Inst::Call {
            callee: FuncId::new(90),
            args: ids(&[1, 2, 1]),
        },
        Inst::CallCannotUnwind {
            callee: FuncId::new(90),
            args: ids(&[1, 2, 1]),
        },
        Inst::CallIndirect {
            callee: v(90),
            sig: FuncTyId::new(91),
            args: ids(&[1, 2, 1]),
            calling_conv: crate::CallingConv::C,
        },
        Inst::CallIndirectCannotUnwind {
            callee: v(90),
            sig: FuncTyId::new(91),
            args: ids(&[1, 2, 1]),
            calling_conv: crate::CallingConv::C,
        },
        Inst::Br {
            target: BlockId::new(92),
            args: ids(&[1, 2, 1]),
        },
        Inst::CondBr {
            cond: v(0),
            then_target: BlockId::new(92),
            then_args: ids(&[1, 2]),
            else_target: BlockId::new(93),
            else_args: ids(&[3, 1]),
        },
        Inst::Return {
            values: ids(&[1, 2, 1]),
        },
    ];
    for instruction in instructions {
        parity(&instruction);
    }
    assert_eq!(
        parity(&Inst::Call {
            callee: FuncId::new(90),
            args: vec![]
        }),
        vec![]
    );
}

#[test]
fn aggregate_gep_and_dialect_lists_are_actual_borrowed_operand_sequences() {
    let mut dialect = crate::dialect::DialectInst::new("observed", "operands");
    dialect.operands = ids(&[7, 8, 7]);
    dialect.result_tys = vec![Ty::Tuple(vec![Ty::U32; 5000])];
    let instructions = vec![
        Inst::GEP {
            pointee_ty: Ty::Tuple(vec![Ty::U32; 50]),
            base: v(1),
            indices: ids(&[2, 2, 3]),
            inbounds: true,
        },
        Inst::MakeAggregate {
            ty: Ty::Tuple(vec![Ty::U32; 3]),
            variant: Some(99),
            fields: ids(&[4, 5, 4]),
        },
        Inst::ArraySplat {
            ty: Ty::Array(TyId::new(99), u64::MAX),
            value: v(6),
        },
        Inst::DialectOp(Box::new(dialect)),
    ];
    for (instruction, expected) in instructions.into_iter().zip([
        ids(&[1, 2, 2, 3]),
        ids(&[4, 5, 4]),
        ids(&[6]),
        ids(&[7, 8, 7]),
    ]) {
        assert_eq!(parity(&instruction), expected);
    }
}

#[test]
fn optional_counts_empty_lists_and_operand_free_metadata_keep_exact_zero_behavior() {
    for count in [None, Some(v(3))] {
        for instruction in [
            Inst::Alloca {
                ty: Ty::U32,
                count,
                align: Some(8),
            },
            Inst::HeapAlloc {
                ty: Ty::U32,
                count,
                align: None,
                origin: AllocOrigin::RustHeap,
            },
        ] {
            assert_eq!(parity(&instruction), count.into_iter().collect::<Vec<_>>());
        }
    }
    let no_operands = vec![
        Inst::Fence {
            ordering: Ordering::SeqCst,
        },
        Inst::Const {
            ty: Ty::Ptr,
            value: Constant::SymbolAddr {
                symbol: "symbol".repeat(1000),
                addend: 0,
            },
        },
        Inst::NullPtr,
        Inst::GlobalAddr {
            global: GlobalId::new(80),
        },
        Inst::Undef {
            ty: Ty::Tuple(vec![Ty::U32; 5000]),
        },
        Inst::Unreachable,
        Inst::OpenFrame {
            def: BindingFrameDef::new(BindingFrameId::new(81), "frame".repeat(1000), vec![]),
        },
        Inst::LandingPad {
            is_cleanup: true,
            catch_type_indices: vec![82; 5000],
        },
    ];
    for instruction in no_operands {
        assert!(parity(&instruction).is_empty());
    }
}

#[test]
fn excluded_type_payload_size_does_not_add_a_hidden_type_walk_or_clone() {
    let (_, shallow) = observed(&Inst::Undef { ty: Ty::U32 });
    let (_, wide) = observed(&Inst::Undef {
        ty: Ty::Tuple(vec![Ty::U32; 100_000]),
    });
    assert_eq!(shallow.work, wide.work);
    assert_eq!(shallow.bytes, wide.bytes);
    assert_eq!(shallow.events, wide.events);
}

#[test]
fn wide_actual_operand_lists_match_the_real_original_visitor() {
    let instructions = [
        Inst::Return {
            values: (0..4000).map(v).collect(),
        },
        switch(false, 1000),
    ];
    for instruction in instructions {
        assert!(!parity(&instruction).is_empty());
    }
}
