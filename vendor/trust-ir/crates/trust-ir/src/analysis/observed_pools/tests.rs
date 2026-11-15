// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::function_dependencies::{Locality, NodeBody, NodeOrigin, ReachGraph, ReachNodeSpec};
use crate::interpret::InterpretOptions;

#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    stop_at: Option<usize>,
    stop_retirement: bool,
    work: usize,
    bytes: usize,
    work_limit: Option<usize>,
    byte_limit: Option<usize>,
}

impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, progress: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(progress);
        if self.stop_at == Some(self.events.len()) {
            return Err("interior");
        }
        if self.stop_retirement && progress.phase == ExecutionPhase::ScratchRetirement {
            return Err("retirement");
        }
        self.work = self
            .work
            .checked_add(progress.work)
            .ok_or("work overflow")?;
        self.bytes = self
            .bytes
            .checked_add(progress.copy_bytes)
            .ok_or("byte overflow")?;
        if self.work_limit.is_some_and(|limit| self.work > limit) {
            return Err("work");
        }
        if self.byte_limit.is_some_and(|limit| self.bytes > limit) {
            return Err("bytes");
        }
        Ok(())
    }
}

fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(71))
}
fn location(index: u64) -> ReachSite {
    ReachSite::Mir(index)
}
fn node(graph: &mut ReachGraph, index: u32) -> ReachNode {
    graph.add_node(ReachNodeSpec {
        origin: NodeOrigin::Mir(index),
        definition: None,
        locality: Locality::Local,
        body: NodeBody::Walked,
    })
}
fn method(principal: u64, method: u64) -> PoolKey {
    PoolKey::DynMethod {
        principal: PrincipalKey(principal),
        method: MethodKey(method),
    }
}
fn shape(abi: Option<u32>, params: Vec<ArgClass>) -> PoolKey {
    PoolKey::Fn(FnShape {
        abi,
        variadic: Some(false),
        params: Some(params),
    })
}

fn fixture() -> IndirectCallUniverse {
    let mut graph = ReachGraph::new();
    let first = node(&mut graph, 0);
    let second = node(&mut graph, 1);
    let third = node(&mut graph, 2);
    IndirectCallUniverse {
        members: vec![
            PoolMember {
                member: second,
                key: method(1, 9),
                confined: true,
            },
            PoolMember {
                member: first,
                key: PoolKey::DynDrop(PrincipalKey(1)),
                confined: true,
            },
            PoolMember {
                member: second,
                key: method(1, 9),
                confined: false,
            },
            PoolMember {
                member: third,
                key: shape(None, vec![ArgClass::Int(32), ArgClass::ThinPointer]),
                confined: true,
            },
            PoolMember {
                member: third,
                key: shape(None, vec![ArgClass::Int(8)]),
                confined: true,
            },
            PoolMember {
                member: third,
                key: PoolKey::Fn(FnShape::unclassified()),
                confined: false,
            },
        ],
        invokes: vec![PoolInvoke {
            node: first,
            key: method(8, 2),
            carried: vec![CarriedKey::Principal(PrincipalKey(10))],
            site: location(10),
            via_drop: false,
        }],
        handoffs: vec![PoolHandoff {
            node: second,
            callee: third,
            carried: vec![CarriedKey::Key(PoolKey::DynDrop(PrincipalKey(12)))],
            site: location(11),
            via_drop: true,
        }],
        launder: Some(location(12)),
        laundered: BTreeMap::from([
            (CarriedKey::Principal(PrincipalKey(4)), location(12)),
            (CarriedKey::AnyFn, location(13)),
        ]),
        erased: BTreeSet::from([PrincipalKey(2)]),
        upcasts: BTreeSet::from([
            (PrincipalKey(1), PrincipalKey(2)),
            (PrincipalKey(2), PrincipalKey(3)),
            (PrincipalKey(3), PrincipalKey(1)),
            (PrincipalKey(2), PrincipalKey(2)),
            (PrincipalKey(4), PrincipalKey(5)),
            (PrincipalKey(8), PrincipalKey(9)),
        ]),
    }
}

fn equal(actual: &ClosedPools, original: &ClosedPools) {
    assert_eq!(actual.members, original.members);
    assert_eq!(actual.launder, original.launder);
    assert_eq!(actual.laundered, original.laundered);
    assert_eq!(actual.laundered_fn, original.laundered_fn);
    assert_eq!(actual.open, original.open);
    assert_eq!(actual.unclosed, original.unclosed);
    assert_eq!(actual.upcast_reach, original.upcast_reach);
}

fn parity(universe: &IndirectCallUniverse, unenumerated: bool) -> ClosedPools {
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let actual = universe
        .close_observed(unenumerated, &mut session, site())
        .unwrap();
    equal(&actual, &universe.close(unenumerated));
    assert!(session.first_refusal().is_none());
    assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    assert!(observer.events.iter().all(|event| event.site == site()));
    actual
}

#[test]
fn empty_universe_and_unenumerated_flag_match_exact_original_state() {
    for unenumerated in [false, true] {
        let pools = parity(&IndirectCallUniverse::default(), unenumerated);
        assert!(pools.members.is_empty());
        assert!(pools.upcast_reach.is_empty());
        assert_eq!(pools.unclosed, unenumerated);
    }
}

#[test]
fn cycles_upcasts_demotion_duplicate_rows_and_full_fn_order_match() {
    let universe = fixture();
    let pools = parity(&universe, false);
    assert_eq!(
        pools.upcast_reach[&PrincipalKey(1)],
        BTreeSet::from([PrincipalKey(2), PrincipalKey(3)])
    );
    assert!(
        pools
            .members
            .iter()
            .filter(|row| row.key.principal().is_some())
            .all(|row| !row.confined)
    );
    assert_eq!(
        pools
            .members
            .iter()
            .filter(|row| matches!(row.key, PoolKey::Fn(_)))
            .count(),
        3
    );
    assert!(pools.open.contains(&PrincipalKey(4)));
    assert!(pools.open.contains(&PrincipalKey(5)));
    assert!(pools.open.contains(&PrincipalKey(8)));
    assert!(pools.open.contains(&PrincipalKey(9)));
    assert!(pools.open.contains(&PrincipalKey(10)));
    assert!(pools.open.contains(&PrincipalKey(12)));
}

#[test]
fn unrecorded_upcast_source_opens_recorded_target_but_self_edge_does_not() {
    let mut graph = ReachGraph::new();
    let member = node(&mut graph, 0);
    let universe = IndirectCallUniverse {
        members: vec![PoolMember {
            member,
            key: PoolKey::DynDrop(PrincipalKey(2)),
            confined: true,
        }],
        upcasts: BTreeSet::from([
            (PrincipalKey(1), PrincipalKey(2)),
            (PrincipalKey(2), PrincipalKey(3)),
            (PrincipalKey(4), PrincipalKey(4)),
        ]),
        ..IndirectCallUniverse::default()
    };
    let pools = parity(&universe, false);
    assert_eq!(
        pools.open,
        BTreeSet::from([PrincipalKey(2), PrincipalKey(3)])
    );
    assert!(pools.unclosed);
    assert!(pools.members.iter().all(|row| row.confined));
}

#[test]
fn every_launder_demotes_exactly_as_original_and_keeps_first_sites() {
    for key in [
        CarriedKey::Any,
        CarriedKey::AnyDyn,
        CarriedKey::AnyFn,
        CarriedKey::Key(method(1, 9)),
    ] {
        let mut universe = fixture();
        universe.erased.clear();
        universe.laundered = BTreeMap::from([(key.clone(), location(19))]);
        let pools = parity(&universe, false);
        assert_eq!(pools.laundered[&key], location(19));
        if matches!(key, CarriedKey::Any | CarriedKey::AnyDyn) {
            assert!(pools.members.iter().all(|row| !row.confined));
        }
    }
}

#[test]
fn fixed_retained_keys_and_distinct_shape_prefixes_preserve_exact_output() {
    let mut universe = fixture();
    universe.laundered = BTreeMap::from([
        (
            CarriedKey::Key(shape(Some(1), vec![ArgClass::Int(8); 17])),
            location(20),
        ),
        (
            CarriedKey::Key(shape(Some(2), vec![ArgClass::Int(8); 21])),
            location(21),
        ),
        (CarriedKey::Key(shape(Some(1), vec![])), location(22)),
        (CarriedKey::AnyFn, location(23)),
    ]);
    parity(&universe, true);
}

#[test]
fn variable_retained_key_comparison_is_typed_open_without_partial_pools() {
    let mut universe = fixture();
    universe.laundered = BTreeMap::from([
        (
            CarriedKey::Key(shape(None, vec![ArgClass::Int(8); 17])),
            location(20),
        ),
        (
            CarriedKey::Key(shape(None, vec![ArgClass::Int(8); 21])),
            location(21),
        ),
    ]);
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        universe
            .close_observed(false, &mut session, site())
            .unwrap_err(),
        ObservedValueError::UnsupportedValue
    );
    assert!(session.first_refusal().is_none());
    assert!(
        observer
            .events
            .iter()
            .any(|event| event.phase == ExecutionPhase::ScratchRetirement)
    );
    let mut observer = Observer {
        stop_retirement: true,
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        universe
            .close_observed(false, &mut session, site())
            .unwrap_err(),
        ObservedValueError::AdmissionRefused
    );
    assert_eq!(session.first_refusal().unwrap().cause, "retirement");
}

mod stops;
