// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn resolved_drop_edges_keep_original_glue_target_site_and_via_drop_flag() {
    for glue in [900, 404] {
        let mut module = module();
        let ty = Ty::Struct(StructId::new(5));
        module.drop_glue.push(crate::DropGlueEntry {
            ty: ty.clone(),
            glue: FuncId::new(glue),
        });
        module.functions[0].blocks[0].body[0] = InstrNode::new(Inst::Drop {
            ty,
            ptr: ValueId::new(0),
        });
        parity(&module);
        let actual = observed(&module, &mut Observer::default()).unwrap();
        assert!(
            actual
                .census
                .graph
                .edges
                .iter()
                .any(|edge| edge.via_drop && edge.site == location(0))
        );
    }
}
#[test]
fn duplicate_or_missing_drop_glue_keeps_exact_unknown_type_and_via_drop_edge() {
    for invoke in [false, true] {
        let mut module = module();
        let ty = Ty::Tuple(vec![Ty::Struct(StructId::new(5)); 257]);
        module.functions[0].blocks[0].body[0] = InstrNode::new(if invoke {
            Inst::DropInvoke {
                ty: ty.clone(),
                ptr: ValueId::new(0),
                normal_dest: BlockId::new(0),
                normal_args: vec![],
                unwind_dest: BlockId::new(0),
            }
        } else {
            Inst::Drop {
                ty: ty.clone(),
                ptr: ValueId::new(0),
            }
        });
        for duplicate in [false, true] {
            if duplicate {
                for glue in [900, 900] {
                    module.drop_glue.push(crate::DropGlueEntry {
                        ty: ty.clone(),
                        glue: FuncId::new(glue),
                    });
                }
            }
            parity(&module);
            let actual = observed(&module, &mut Observer::default()).unwrap();
            let root = actual
                .node(DependencyNode::Function(FuncId::new(73)))
                .unwrap();
            let edge = actual
                .census
                .graph
                .edges
                .iter()
                .find(|e| e.from == root && e.site == location(0) && e.via_drop)
                .unwrap();
            assert_eq!(edge.class, EdgeClass::Run);
            assert_eq!(
                actual.census.graph.nodes[edge.to.index()],
                ReachNodeKind::Sink(DependencyRefusalKind::ImplicitDestructor(ty.clone()))
            );
            assert_eq!(actual.census.verdict(root), Verdict::Unknown);
            assert!(!actual.census.thread_closure(Some(root)).modelable());
        }
    }
}
#[test]
fn every_unresolved_drop_boundary_keeps_first_stop_and_retires_partial_owned_diagnostics() {
    let mut module = module();
    module.functions[0].blocks[0].body[0] = InstrNode::new(Inst::Drop {
        ty: Ty::Tuple(vec![
            Ty::Rc(Box::new(Ty::Bool)),
            Ty::Handle(Box::new(crate::HandleTy::new("N", "R"))),
        ]),
        ptr: ValueId::new(0),
    });
    let mut baseline = Observer::default();
    observed(&module, &mut baseline).unwrap();
    for stop in 1..=baseline.events.len() {
        let mut observer = Observer {
            stop_at: Some(stop),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert!(matches!(
            inspect_native_module_reachability_observed(&module, &mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        ));
        assert_eq!(session.first_refusal().unwrap().cause, "original stop");
        assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
        assert!(
            observer
                .events
                .iter()
                .skip(stop)
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
