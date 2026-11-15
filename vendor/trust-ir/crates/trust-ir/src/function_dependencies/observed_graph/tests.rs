// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use crate::interpret::InterpretOptions;
use crate::{Block, FuncTy, InstrNode};

#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    stop_at: Option<usize>,
    work_left: Option<usize>,
    bytes_left: Option<usize>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, progress: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(progress);
        if self.stop_at == Some(self.events.len()) {
            return Err("original stop");
        }
        if let Some(left) = &mut self.work_left {
            *left = left.checked_sub(progress.work).ok_or("original work")?;
        }
        if let Some(left) = &mut self.bytes_left {
            *left = left
                .checked_sub(progress.copy_bytes)
                .ok_or("original copy")?;
        }
        Ok(())
    }
}
struct NativeDeclarations;
impl DeclClassifier for NativeDeclarations {
    fn classify(&self, _: &Function) -> FunctionClass {
        FunctionClass::Walk
    }
    fn definition(&self, f: &Function) -> DefinitionKey {
        DefinitionKey(u128::from(f.id.index()))
    }
    fn runtime_service(&self, _: RuntimeService) -> ServiceClass {
        ServiceClass::Unknown(DependencyRefusalKind::UnresolvedExtern)
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(73))
}
fn location(index: usize) -> ReachSite {
    ReachSite::TrustIr(DependencySite::Instruction {
        function: FuncId::new(73),
        block: BlockId::new(0),
        index,
    })
}
fn function(id: u32, body: Vec<Inst>) -> Function {
    let mut function = Function::new(
        FuncId::new(id),
        format!("f{id}"),
        FuncTyId::new(0),
        BlockId::new(0),
    );
    let mut block = Block::new(BlockId::new(0));
    block.body = body.into_iter().map(InstrNode::new).collect();
    function.blocks.push(block);
    function
}
fn module() -> Module {
    let mut module = Module::new("observed_native_graph");
    module
        .func_types
        .push(FuncTy::unrecorded(vec![], vec![], false));
    module.functions.push(function(
        73,
        vec![
            Inst::Call {
                callee: FuncId::new(900),
                args: vec![],
            },
            Inst::Return { values: vec![] },
        ],
    ));
    module
        .functions
        .push(function(900, vec![Inst::Return { values: vec![] }]));
    module
}
fn observed<'m>(module: &'m Module, observer: &mut Observer) -> Observed<ModuleReachability<'m>> {
    let mut session = ObservedSession::new(InterpretOptions::default(), observer);
    inspect_native_module_reachability_observed(module, &mut session, site())
}
fn edge_identity(edge: &ReachEdge) -> (usize, usize, EdgeClass, ReachSite, bool) {
    (
        edge.from.index(),
        edge.to.index(),
        edge.class,
        edge.site,
        edge.via_drop,
    )
}
fn parity(module: &Module) {
    let ordinary = inspect_module_reachability(module, &NativeDeclarations);
    let actual = observed(module, &mut Observer::default()).unwrap();
    assert!(core::ptr::eq(actual.module(), module));
    assert_eq!(actual.census.certificate, ordinary.census.certificate);
    assert_eq!(actual.census.parents, ordinary.census.parents);
    assert_eq!(actual.census.graph.nodes, ordinary.census.graph.nodes);
    assert_eq!(
        actual.census.graph.pools.unclosed(),
        ordinary.census.graph.pools.unclosed()
    );
    assert_eq!(
        actual.census.graph.derivation_size(),
        ordinary.census.graph.derivation_size()
    );
    assert_eq!(
        actual
            .census
            .graph
            .edges
            .iter()
            .map(edge_identity)
            .collect::<Vec<_>>(),
        ordinary
            .census
            .graph
            .edges
            .iter()
            .map(edge_identity)
            .collect::<Vec<_>>()
    );
    for (key, node) in &ordinary.nodes {
        let actual_node = actual.node(*key).unwrap();
        assert_eq!(actual_node.index(), node.index());
        let expected = ordinary.census.thread_closure(Some(*node));
        let closure = actual.census.thread_closure(Some(actual_node));
        assert_eq!(closure.modelable(), expected.modelable());
        assert_eq!(
            closure.nodes().map(ReachNode::index).collect::<Vec<_>>(),
            expected.nodes().map(ReachNode::index).collect::<Vec<_>>()
        );
    }
}

#[test]
fn native_graph_preserves_sparse_duplicate_missing_and_all_stored_blocks() {
    let mut module = module();
    let mut unused = Block::new(BlockId::new(19));
    unused.body.push(InstrNode::new(Inst::Call {
        callee: FuncId::new(404),
        args: vec![],
    }));
    module.functions[0].blocks.push(unused);
    module.functions[1].blocks.push(Block::new(BlockId::new(0)));
    module.functions.push(function(4, vec![]));
    module.functions.last_mut().unwrap().blocks.clear();
    module.functions.push(function(900, vec![]));
    parity(&module);
}

#[test]
fn native_runtime_unknowns_globals_and_nested_constants_match_ordinary() {
    let mut module = module();
    module.functions[0].blocks[0]
        .body
        .push(InstrNode::new(Inst::Assert {
            cond: ValueId::new(0),
            kind: crate::AssertKind::Unspecified,
            site: None,
        }));
    module.functions[0].blocks[0]
        .body
        .push(InstrNode::new(Inst::GlobalAddr {
            global: GlobalId(0),
        }));
    for (name, initializer) in [
        ("missing", None),
        (
            "nested",
            Some(Constant::Aggregate(vec![
                Constant::Int(1),
                Constant::Splat {
                    elem: Box::new(Constant::Int(2)),
                    len: u64::MAX,
                },
            ])),
        ),
    ] {
        module.globals.push(crate::Global {
            name: name.into(),
            ty: Ty::I64,
            mutable: false,
            initializer,
            linkage: crate::Linkage::Internal,
            tls: None,
            align: None,
            section: None,
            visibility: crate::Visibility::Default,
            retained: false,
        });
    }
    parity(&module);
}

#[test]
fn unsupported_callable_or_indirect_surface_never_returns_a_smaller_graph() {
    for instruction in [
        Inst::Const {
            ty: Ty::Func(FuncTyId::new(0)),
            value: Constant::FnDef(FuncId::new(900)),
        },
        Inst::CallIndirect {
            callee: ValueId::new(0),
            sig: FuncTyId::new(0),
            args: vec![],
            calling_conv: CallingConv::C,
        },
    ] {
        let mut module = module();
        module.functions[0].blocks[0]
            .body
            .push(InstrNode::new(instruction));
        assert!(matches!(
            observed(&module, &mut Observer::default()),
            Err(ObservedValueError::UnsupportedValue)
        ));
    }
}

fn program(graph: &mut ReachGraph, id: u32, body: NodeBody) -> ReachNode {
    graph.add_node(ReachNodeSpec {
        origin: NodeOrigin::TrustIr(DependencyNode::Function(FuncId::new(id))),
        definition: Some(DefinitionKey(u128::from(id))),
        locality: Locality::Local,
        body,
    })
}
fn derived() -> ReachCensus {
    let mut graph = ReachGraph::new();
    let root = program(&mut graph, 73, NodeBody::Walked);
    let member = program(&mut graph, 74, NodeBody::Walked);
    let seed = program(&mut graph, 75, NodeBody::Seed);
    let key = PoolKey::Fn(FnShape::unclassified());
    graph.add_create(root, member, key.clone(), false, location(0));
    graph.add_edge(member, seed, EdgeClass::Run, location(1), false);
    graph.add_invoke(root, key.clone(), Vec::new(), location(2), true);
    graph.add_invoke(root, key, Vec::new(), location(3), false);
    graph.solve()
}

#[test]
fn observed_solver_matches_real_compressed_hub_certificates_and_parents() {
    let ordinary = derived();
    assert!(ordinary.graph.derivation_size().0 > 0);
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let (certificate, parents, fallback) =
        solve::solve(&ordinary.graph, &mut session, site()).unwrap();
    assert_eq!(certificate, ordinary.certificate);
    assert_eq!(parents, ordinary.parents);
    assert_eq!(fallback, ordinary.fallback);
}

#[test]
fn observed_certificate_checker_keeps_the_ordinary_mutant_refusals() {
    let ordinary = derived();
    for index in 0..ordinary.certificate.labels.len() {
        let mut certificate = ordinary.certificate.clone();
        certificate.labels[index] = if certificate.labels[index] == Verdict::Quiet {
            Verdict::Unknown
        } else {
            Verdict::Quiet
        };
        let expected = check_reach_certificate(&ordinary.graph, &certificate);
        let mut observer = Observer::default();
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        let actual = solve::check(
            &ordinary.graph,
            &certificate.labels,
            &certificate.justifications,
            &certificate.definitions,
            &mut session,
            site(),
        )
        .unwrap();
        assert_eq!(actual, expected);
        assert!(actual.is_err());
    }
}

#[test]
fn native_every_actual_boundary_has_terminal_original_stop_and_only_retirement_afterward() {
    let module = module();
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
        assert!(
            inspect_native_module_reachability_observed(&module, &mut session, site()).is_err()
        );
        drop(session);
        assert!(
            observer.events[stop..]
                .iter()
                .all(|event| event.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}

#[test]
fn compressed_solver_actual_interior_and_retirement_stops_do_not_return_a_certificate() {
    let ordinary = derived();
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    solve::solve(&ordinary.graph, &mut session, site()).unwrap();
    for stop in 1..=baseline.events.len() {
        let mut observer = Observer {
            stop_at: Some(stop),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert!(matches!(
            solve::solve(&ordinary.graph, &mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        ));
        assert_eq!(session.first_refusal().unwrap().cause, "original stop");
    }
}

#[test]
fn native_work_and_copy_remain_cumulative_across_graphs_without_spending_fuel() {
    let module = module();
    let mut baseline = Observer::default();
    observed(&module, &mut baseline).unwrap();
    let work = baseline.events.iter().map(|event| event.work).sum();
    let bytes = baseline.events.iter().map(|event| event.copy_bytes).sum();
    for limits in [(Some(work), None), (None, Some(bytes))] {
        let mut observer = Observer {
            work_left: limits.0,
            bytes_left: limits.1,
            ..Observer::default()
        };
        let mut session = ObservedSession::new(
            InterpretOptions {
                fuel: 7,
                ..InterpretOptions::default()
            },
            &mut observer,
        );
        inspect_native_module_reachability_observed(&module, &mut session, site()).unwrap();
        assert!(matches!(
            inspect_native_module_reachability_observed(&module, &mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        ));
        assert_eq!(session.remaining_fuel(), 7);
    }
}

#[test]
fn first_vector_growth_is_refused_before_reservation() {
    let mut values = Vec::<usize>::new();
    let mut observer = Observer {
        bytes_left: Some(0),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        push(&mut values, 7, &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(values.capacity(), 0);
    assert!(values.is_empty());
}

mod drops;
