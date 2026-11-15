// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;

#[test]
fn every_actual_construction_callback_returns_only_original_stop_and_retires_afterward() {
    let function = diamond();
    let mut baseline = Observer::default();
    construct(&function, &mut baseline).unwrap();
    for stop_at in 1..=baseline.events.len() {
        let mut observer = Observer {
            stop_at: Some(stop_at),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert!(matches!(
            DominatorTree::new_observed(&function, &mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        ));
        assert_eq!(session.first_refusal().unwrap().cause, "original stop");
        assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
        assert!(
            observer
                .events
                .iter()
                .skip(stop_at)
                .all(|event| event.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}

#[test]
fn malformed_tree_retirement_and_publication_stops_are_not_successful_defaults() {
    let mut function = diamond();
    function.blocks[1].body[0] = InstrNode::new(Inst::Br {
        target: BlockId::new(123),
        args: vec![],
    });
    let mut baseline = Observer::default();
    assert!(
        !construct(&function, &mut baseline)
            .unwrap()
            .is_well_formed()
    );
    for stop_at in 1..=baseline.events.len() {
        let mut observer = Observer {
            stop_at: Some(stop_at),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert!(matches!(
            DominatorTree::new_observed(&function, &mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        ));
        assert_eq!(session.first_refusal().unwrap().cause, "original stop");
        assert!(
            observer
                .events
                .iter()
                .skip(stop_at)
                .all(|event| event.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}

#[derive(Clone, Copy)]
enum Query {
    Reach,
    Strict,
    Edge,
    Available,
}
fn query(
    tree: &DominatorTree,
    function: &Function,
    kind: Query,
    session: &mut ObservedSession<'_, Observer>,
) -> R<bool> {
    let target = function.blocks[3].id;
    match kind {
        Query::Reach => tree.is_reachable_observed(target, session, site()),
        Query::Strict => tree.strictly_dominates_observed(function.entry, target, session, site()),
        Query::Edge => {
            tree.edge_dominates_observed(function.entry, 0, function.blocks[1].id, session, site())
        }
        Query::Available => tree.definition_available_at_observed(
            SsaDefinitionSite {
                block: function.entry,
                instruction: Some(0),
            },
            SsaUseSite::BeforeInstruction {
                block: target,
                instruction: 0,
            },
            session,
            site(),
        ),
    }
}

#[test]
fn every_actual_query_callback_is_fallible_including_final_publication() {
    let function = diamond();
    let tree = DominatorTree::new(&function);
    for kind in [Query::Reach, Query::Strict, Query::Edge, Query::Available] {
        let mut baseline = Observer::default();
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
        query(&tree, &function, kind, &mut session).unwrap();
        for stop_at in 1..=baseline.events.len() {
            let mut observer = Observer {
                stop_at: Some(stop_at),
                ..Observer::default()
            };
            let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
            assert_eq!(
                query(&tree, &function, kind, &mut session),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(session.first_refusal().unwrap().cause, "original stop");
        }
    }
}

#[test]
fn construction_and_queries_share_original_cumulative_work_and_byte_caps() {
    let function = diamond();
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let tree = DominatorTree::new_observed(&function, &mut session, site()).unwrap();
    query(&tree, &function, Query::Available, &mut session).unwrap();
    for bytes in [false, true] {
        let mut observer = if bytes {
            Observer {
                byte_cap: Some(baseline.bytes - 1),
                ..Observer::default()
            }
        } else {
            Observer {
                work_cap: Some(baseline.work - 1),
                ..Observer::default()
            }
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        let tree = DominatorTree::new_observed(&function, &mut session, site()).unwrap();
        assert_eq!(
            query(&tree, &function, Query::Available, &mut session),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            session.first_refusal().unwrap().cause,
            if bytes { "bytes" } else { "work" }
        );
        assert_eq!(
            tree.retire_observed(&mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
    }
}

#[test]
fn first_btree_and_frontier_growth_refuse_before_allocation() {
    let mut observer = Observer {
        byte_cap: Some(0),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = State::default();
    assert_eq!(
        work.mark(&mut state.blocks, 7),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(state.blocks.is_empty());
    state.retire_scratch(&mut work);
    let mut observer = Observer {
        byte_cap: Some(0),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut frames = Vec::new();
    assert_eq!(
        work.push(&mut frames, (7u32, 0usize)),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!((frames.len(), frames.capacity()), (0, 0));
    work.retire_vec(frames);
}

#[test]
fn pending_owned_target_row_is_retained_before_map_storage_refusal() {
    let mut observer = Observer {
        byte_cap: Some(0),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut map = BTreeMap::new();
    let mut row = vec![1, 2, 3];
    assert_eq!(
        work.store_row(&mut map, 7, &mut row),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(map.is_empty());
    assert_eq!(row, vec![1, 2, 3]);
    work.retire_vec(row);
    work.retire_rows(&mut map);
}

#[test]
fn final_constructor_publication_refusal_retires_complete_tree_maps() {
    let function = diamond();
    let mut baseline = Observer::default();
    construct(&function, &mut baseline).unwrap();
    let stop_at = baseline.events.len();
    assert_eq!(
        baseline.events.last().unwrap().phase,
        ExecutionPhase::Publication
    );
    let mut observer = Observer {
        stop_at: Some(stop_at),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert!(matches!(
        DominatorTree::new_observed(&function, &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    ));
    assert_eq!(
        session.first_refusal().unwrap().progress.phase,
        ExecutionPhase::Publication
    );
    assert!(observer.events.len() > stop_at + 10);
    assert!(
        observer
            .events
            .iter()
            .skip(stop_at)
            .all(|event| event.phase == ExecutionPhase::ScratchRetirement)
    );
}

#[test]
fn output_retirement_runs_after_stop_and_observes_final_map_deallocation() {
    let function = diamond();
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let tree = DominatorTree::new_observed(&function, &mut session, site()).unwrap();
    tree.retire_observed(&mut session, site()).unwrap();
    assert_eq!(
        baseline.events.last().unwrap().phase,
        ExecutionPhase::Publication
    );
    let stop_at = baseline.events.len() - 1;
    assert_eq!(
        baseline.events[stop_at - 1].phase,
        ExecutionPhase::ScratchRetirement
    );
    let mut observer = Observer {
        stop_at: Some(stop_at),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let tree = DominatorTree::new_observed(&function, &mut session, site()).unwrap();
    assert_eq!(
        tree.retire_observed(&mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(session.first_refusal().unwrap().cause, "original stop");
    assert_eq!(
        session.first_refusal().unwrap().progress.phase,
        ExecutionPhase::ScratchRetirement
    );
    assert_eq!(observer.events.len(), stop_at);

    let mut measured = Observer::default();
    construct(&function, &mut measured).unwrap();
    let original_stop = measured.events.len() + 1;
    let mut observer = Observer {
        stop_at: Some(original_stop),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let tree = DominatorTree::new_observed(&function, &mut session, site()).unwrap();
    assert!(
        session
            .admit(ExecutionProgress {
                phase: ExecutionPhase::Validation,
                site: site(),
                work: 1,
                copy_bytes: 0
            })
            .is_err()
    );
    assert_eq!(
        tree.retire_observed(&mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(session.first_refusal().unwrap().cause, "original stop");
    assert!(observer.events.len() > original_stop + 10);
}
