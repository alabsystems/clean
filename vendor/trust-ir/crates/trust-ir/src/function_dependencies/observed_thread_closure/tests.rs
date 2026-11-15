// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use crate::interpret::InterpretOptions;

#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    stop_at: Option<usize>,
    stop_phase: Option<ExecutionPhase>,
    work_left: Option<usize>,
    bytes_left: Option<usize>,
}

impl ExecutionObserver for Observer {
    type Refusal = &'static str;

    fn admit(&mut self, progress: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(progress);
        if self.stop_at == Some(self.events.len()) || self.stop_phase == Some(progress.phase) {
            return Err("original stop");
        }
        if let Some(left) = &mut self.work_left {
            *left = left
                .checked_sub(progress.work)
                .ok_or("original work exhausted")?;
        }
        if let Some(left) = &mut self.bytes_left {
            *left = left
                .checked_sub(progress.copy_bytes)
                .ok_or("original copy exhausted")?;
        }
        Ok(())
    }
}

fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(73))
}

fn reach_site(index: usize) -> ReachSite {
    ReachSite::TrustIr(DependencySite::Instruction {
        function: FuncId::new(73),
        block: BlockId::new(9),
        index,
    })
}

fn program(graph: &mut ReachGraph, id: u32, body: NodeBody) -> ReachNode {
    graph.add_node(ReachNodeSpec {
        origin: NodeOrigin::TrustIr(DependencyNode::Function(FuncId::new(id))),
        definition: Some(DefinitionKey(u128::from(id))),
        locality: Locality::Local,
        body,
    })
}

fn derived_fixture() -> (ReachCensus, ReachNode, ReachNode, ReachNode) {
    let mut graph = ReachGraph::new();
    let root = program(&mut graph, 73, NodeBody::Walked);
    let direct = program(&mut graph, 74, NodeBody::Primitive);
    let member = program(&mut graph, 75, NodeBody::Walked);
    let seed = program(&mut graph, 76, NodeBody::Seed);
    let key = PoolKey::Fn(FnShape::unclassified());
    graph.add_edge(root, direct, EdgeClass::Run, reach_site(0), false);
    graph.add_edge(direct, root, EdgeClass::Run, reach_site(1), false);
    graph.add_edge(direct, seed, EdgeClass::Run, reach_site(2), false);
    graph.add_create(root, member, key.clone(), false, reach_site(3));
    graph.add_invoke(root, key.clone(), Vec::new(), reach_site(4), true);
    graph.add_invoke(root, key, Vec::new(), reach_site(5), false);
    (graph.solve(), root, member, seed)
}

fn observed(
    census: &ReachCensus,
    entry: Option<ReachNode>,
    observer: &mut Observer,
) -> Result<ThreadClosure, ObservedValueError> {
    let mut session = ObservedSession::new(InterpretOptions::default(), observer);
    census.thread_closure_observed(entry, &mut session, site())
}

#[test]
fn success_matches_all_roots_and_preserves_derived_edge_custody() {
    let (census, root, member, seed) = derived_fixture();
    assert!(census.fallback().is_none());
    let mut foreign = ReachGraph::new();
    let foreign = program(&mut foreign, 100, NodeBody::Walked);
    let entries = std::iter::once(None)
        .chain(census.expanded().nodes().map(|(node, _)| Some(node)))
        .chain(std::iter::once(Some(foreign)));
    for entry in entries {
        let mut observer = Observer::default();
        assert_eq!(
            observed(&census, entry, &mut observer).unwrap(),
            census.thread_closure(entry)
        );
        assert!(observer.events.iter().all(|event| event.site == site()));
    }
    let closure = observed(&census, Some(root), &mut Observer::default()).unwrap();
    assert!(closure.contains(member));
    assert!(closure.contains(seed));
    let edge = closure.reached[&member].unwrap();
    assert!(!edge.via_drop);
    assert_eq!(edge.site, reach_site(5));
    let seed_closure = observed(&census, Some(seed), &mut Observer::default()).unwrap();
    assert_eq!(seed_closure.nodes().collect::<Vec<_>>(), vec![seed]);
}

#[test]
fn param_unknown_and_fallback_retain_ordinary_modelability_and_contents() {
    for fallback in [false, true] {
        let mut graph = ReachGraph::new();
        let root = program(&mut graph, 73, NodeBody::Walked);
        let target = program(&mut graph, 74, NodeBody::Param);
        graph.add_edge(root, target, EdgeClass::Param, reach_site(0), false);
        graph.add_unknown(
            root,
            DependencyRefusalKind::OpaqueDialectOperation,
            EdgeClass::Run,
            reach_site(1),
            false,
        );
        if fallback {
            graph.add_edge(root, target, EdgeClass::Approx, reach_site(2), false);
        }
        let census = graph.solve();
        assert_eq!(census.fallback().is_some(), fallback);
        let actual = observed(&census, Some(root), &mut Observer::default()).unwrap();
        assert_eq!(actual, census.thread_closure(Some(root)));
        assert!(!actual.modelable());
    }
}

#[test]
fn every_actual_boundary_refuses_without_partial_closure_and_latches_first_cause() {
    let (census, root, _, _) = derived_fixture();
    let mut successful = Observer::default();
    observed(&census, Some(root), &mut successful).unwrap();
    assert!(
        successful
            .events
            .iter()
            .any(|event| event.phase == ExecutionPhase::Reachability)
    );
    assert!(
        successful
            .events
            .iter()
            .any(|event| event.phase == ExecutionPhase::ScratchRetirement)
    );
    assert_eq!(
        successful.events.last().unwrap().phase,
        ExecutionPhase::Publication
    );
    for stop in 1..=successful.events.len() {
        // This observer refuses only ONCE; the session itself must retain it.
        let mut observer = Observer {
            stop_at: Some(stop),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert_eq!(
            census.thread_closure_observed(Some(root), &mut session, site()),
            Err(ObservedValueError::AdmissionRefused),
            "actual stop boundary {stop}"
        );
        let first = session.first_refusal().unwrap();
        assert_eq!(first.cause, "original stop");
        let progress = first.progress;
        assert_eq!(
            census.thread_closure_observed(Some(root), &mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(session.first_refusal().unwrap().progress, progress);
    }
}

#[test]
fn initial_final_and_cleanup_stops_never_publish_even_an_unnamed_entry() {
    let (census, root, _, _) = derived_fixture();
    for entry in [None, Some(root)] {
        for phase in [
            ExecutionPhase::Publication,
            ExecutionPhase::ScratchRetirement,
        ] {
            let mut observer = Observer {
                stop_phase: Some(phase),
                ..Observer::default()
            };
            assert_eq!(
                observed(&census, entry, &mut observer),
                Err(ObservedValueError::AdmissionRefused)
            );
        }
        let mut stopped = Observer {
            stop_at: Some(1),
            ..Observer::default()
        };
        assert_eq!(
            observed(&census, entry, &mut stopped),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            stopped.events.len(),
            1,
            "initial refusal enters no traversal or cleanup"
        );
    }
}

#[test]
fn original_work_and_copy_are_cumulative_and_interpreter_fuel_is_untouched() {
    let (census, root, _, _) = derived_fixture();
    let mut baseline = Observer::default();
    observed(&census, Some(root), &mut baseline).unwrap();
    let work = baseline.events.iter().map(|event| event.work).sum();
    let bytes = baseline.events.iter().map(|event| event.copy_bytes).sum();
    for limits in [(Some(work), None), (None, Some(bytes))] {
        let mut observer = Observer {
            work_left: limits.0,
            bytes_left: limits.1,
            ..Observer::default()
        };
        let options = InterpretOptions {
            fuel: 3,
            ..InterpretOptions::default()
        };
        let mut session = ObservedSession::new(options, &mut observer);
        assert_eq!(
            census
                .thread_closure_observed(Some(root), &mut session, site())
                .unwrap(),
            census.thread_closure(Some(root))
        );
        assert_eq!(session.remaining_fuel(), 3);
        assert_eq!(
            census.thread_closure_observed(Some(root), &mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(session.remaining_fuel(), 3);
        assert!(session.first_refusal().is_some());
    }
}

#[test]
fn scratch_growth_is_admitted_before_reservation_and_failed_growth_retires() {
    // Header copying is affordable; the first outgoing buffer request is not.
    let (census, root, _, _) = derived_fixture();
    let mut observer = Observer {
        bytes_left: Some(size_of::<ThreadClosure>()),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        census.thread_closure_observed(Some(root), &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    let first = session.first_refusal().unwrap();
    assert_eq!(first.cause, "original copy exhausted");
    assert_eq!(first.progress.work, 2);
    assert_eq!(first.progress.copy_bytes, size_of::<Vec<usize>>());
    drop(session);
    assert!(
        observer
            .events
            .iter()
            .any(|event| event.phase == ExecutionPhase::ScratchRetirement)
    );
}
