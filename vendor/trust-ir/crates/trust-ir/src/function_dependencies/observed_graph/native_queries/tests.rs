// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
use crate::interpret::InterpretOptions;
use crate::request::{
    NativeAdapterInput, NativeBundleProducer, NativeRequestId, TrustMcNativeRequest,
    TrustMcVerificationMode, TrustWpNativeRequest, TrustWpVerificationMode,
};
use crate::{Block, FuncTy, InstrNode, ProofDigest, ProofLineageManifest};
#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    stop_at: Option<usize>,
    work: usize,
    bytes: usize,
    work_cap: Option<usize>,
    byte_cap: Option<usize>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, event: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(event);
        if self.stop_at == Some(self.events.len()) {
            return Err("interior");
        }
        self.work = self.work.checked_add(event.work).ok_or("overflow")?;
        self.bytes = self.bytes.checked_add(event.copy_bytes).ok_or("overflow")?;
        if self.work_cap.is_some_and(|cap| self.work > cap) {
            return Err("work");
        }
        if self.byte_cap.is_some_and(|cap| self.bytes > cap) {
            return Err("bytes");
        }
        Ok(())
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(3))
}
fn request(function: u32) -> NativeVerificationRequest {
    NativeVerificationRequest::TrustMc(TrustMcNativeRequest {
        id: NativeRequestId::new(function),
        mode: TrustMcVerificationMode::BoundedModelCheck,
        function: FuncId::new(function),
        obligations: vec![],
        lineage_roots: vec![],
        options: Default::default(),
        diagnostics: Default::default(),
        provenance: Default::default(),
    })
}
fn fixture() -> NativeVerificationBundle {
    let mut module = Module::new("observed_queries");
    module
        .func_types
        .push(FuncTy::unrecorded(vec![], vec![], false));
    for (id, body) in [
        (
            3,
            vec![
                Inst::Call {
                    callee: FuncId::new(17),
                    args: vec![],
                },
                Inst::Return { values: vec![] },
            ],
        ),
        (17, vec![Inst::Return { values: vec![] }]),
    ] {
        let mut function = Function::new(
            FuncId::new(id),
            "function",
            FuncTyId::new(0),
            BlockId::new(0),
        );
        let mut block = Block::new(BlockId::new(0));
        block.body = body.into_iter().map(InstrNode::new).collect();
        function.blocks.push(block);
        module.functions.push(function);
    }
    let mut bundle = NativeVerificationBundle::new(
        NativeBundleProducer::TRust,
        NativeAdapterInput::TrustIrModule,
        ProofDigest::zero(),
        module,
        ProofLineageManifest::new(),
    );
    bundle.requests = vec![request(3), request(17), request(3)];
    bundle
}
fn run(bundle: &NativeVerificationBundle) -> (BTreeSet<FuncId>, Observer) {
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let output = bundle
        .trust_mc_reached_functions_observed(&mut session, site())
        .unwrap();
    assert!(session.first_refusal().is_none());
    assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    (output, observer)
}
struct Declarations;
impl DeclClassifier for Declarations {
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
fn ordinary(bundle: &NativeVerificationBundle) -> BTreeSet<FuncId> {
    let reachability = inspect_module_reachability(&bundle.module, &Declarations);
    let mut result = BTreeSet::new();
    for request in &bundle.requests {
        if let NativeVerificationRequest::TrustMc(request) = request {
            let root = reachability.node(DependencyNode::Function(request.function));
            for node in reachability.census.thread_closure(root).nodes() {
                if let Some(ReachNodeKind::Program(ReachNodeSpec {
                    origin: NodeOrigin::TrustIr(DependencyNode::Function(id)),
                    ..
                })) = reachability.census.graph.nodes.get(node.index())
                {
                    result.insert(*id);
                }
            }
        }
    }
    result
}
#[test]
fn whole_native_query_matches_ordinary_closures_and_duplicate_root_skip() {
    let mut bundle = fixture();
    bundle.module.functions[1].blocks[0].body.insert(
        0,
        InstrNode::new(Inst::Drop {
            ty: Ty::Handle(Box::new(crate::HandleTy::new("N", "runtime"))),
            ptr: ValueId::new(0),
        }),
    );
    let (actual, observer) = run(&bundle);
    assert_eq!(actual, ordinary(&bundle));
    assert_eq!(actual, BTreeSet::from([FuncId::new(3), FuncId::new(17)]));
    let mut lookups = observer
        .events
        .iter()
        .filter(|event| event.phase == ExecutionPhase::ModuleLookup);
    assert_eq!(lookups.next().unwrap().site, site());
    for function in &bundle.module.functions {
        assert_eq!(
            lookups.next().unwrap().site,
            ExecutionSite::Entry(function.id)
        );
    }
    assert!(lookups.next().is_none());
    assert!(
        observer
            .events
            .iter()
            .all(|event| { event.phase == ExecutionPhase::ModuleLookup || event.site == site() })
    );
    assert_eq!(
        observer.events.last().unwrap().phase,
        ExecutionPhase::Publication
    );
    assert!(
        !bundle.validate().is_ok(),
        "query is not full bundle validity or source authority"
    );
}
#[test]
fn empty_and_non_mc_requests_preserve_ordinary_empty_function_selection() {
    let mut bundle = fixture();
    bundle.requests.clear();
    assert!(run(&bundle).0.is_empty());
    bundle
        .requests
        .push(NativeVerificationRequest::TrustWp(TrustWpNativeRequest {
            id: NativeRequestId::new(9),
            mode: TrustWpVerificationMode::WeakestPrecondition,
            function: FuncId::new(404),
            obligations: vec![],
            lineage_roots: vec![],
            options: Default::default(),
            diagnostics: Default::default(),
            provenance: Default::default(),
        }));
    assert_eq!(run(&bundle).0, ordinary(&bundle));
    assert!(run(&bundle).0.is_empty());
}
#[test]
fn missing_root_missing_reached_target_and_duplicate_id_refuse_without_partial_selection() {
    for variant in 0..3 {
        let mut bundle = fixture();
        match variant {
            0 => bundle.requests.push(request(404)),
            1 => {
                bundle.module.functions[0].blocks[0].body[0] = InstrNode::new(Inst::Call {
                    callee: FuncId::new(404),
                    args: vec![],
                })
            }
            _ => bundle
                .module
                .functions
                .push(bundle.module.functions[1].clone()),
        }
        let mut observer = Observer::default();
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert_eq!(
            bundle.trust_mc_reached_functions_observed(&mut session, site()),
            Err(ObservedValueError::InvalidRange)
        );
        assert!(session.first_refusal().is_none());
        assert_eq!(
            observer.events.last().unwrap().phase,
            ExecutionPhase::ScratchRetirement
        );
    }
}
#[test]
fn every_actual_query_event_refuses_and_only_original_retirement_continues() {
    let bundle = fixture();
    let (_, baseline) = run(&bundle);
    for stop in 1..=baseline.events.len() {
        let mut observer = Observer {
            stop_at: Some(stop),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert_eq!(
            bundle.trust_mc_reached_functions_observed(&mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(session.first_refusal().unwrap().cause, "interior");
        assert!(
            observer
                .events
                .iter()
                .skip(stop)
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn two_complete_queries_share_original_work_and_requested_byte_allowance() {
    let bundle = fixture();
    let (_, baseline) = run(&bundle);
    for bytes in [false, true] {
        let mut observer = if bytes {
            Observer {
                byte_cap: Some(baseline.bytes),
                ..Observer::default()
            }
        } else {
            Observer {
                work_cap: Some(baseline.work),
                ..Observer::default()
            }
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        bundle
            .trust_mc_reached_functions_observed(&mut session, site())
            .unwrap();
        assert_eq!(
            bundle.trust_mc_reached_functions_observed(&mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            session.first_refusal().unwrap().cause,
            if bytes { "bytes" } else { "work" }
        );
        assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    }
}
#[test]
fn final_query_publication_refusal_retires_completed_function_set_after_census_is_gone() {
    let bundle = fixture();
    let (_, baseline) = run(&bundle);
    let last = baseline.events.len();
    let mut observer = Observer {
        stop_at: Some(last),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        bundle.trust_mc_reached_functions_observed(&mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        session.first_refusal().unwrap().progress.phase,
        ExecutionPhase::Publication
    );
    assert!(observer.events.len() > last);
    assert!(
        observer
            .events
            .iter()
            .skip(last)
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
fn deep_drop(bundle: &mut NativeVerificationBundle) {
    let mut ty = Ty::Bool;
    for _ in 0..20_000 {
        ty = Ty::Ref(Box::new(ty));
    }
    bundle.module.functions[1].blocks[0].body.insert(
        0,
        InstrNode::new(Inst::Drop {
            ty,
            ptr: ValueId::new(0),
        }),
    );
}
fn retire_input_drop(
    bundle: &mut NativeVerificationBundle,
    session: &mut ObservedSession<'_, Observer>,
) {
    let instruction = bundle.module.functions[1].blocks[0].body.remove(0);
    if let Inst::Drop { ty, .. } = instruction.inst {
        ty.retire_observed(session, site()).unwrap();
    }
}
#[test]
fn deep_owned_unknown_census_retires_before_successful_fixed_id_output() {
    let mut bundle = fixture();
    deep_drop(&mut bundle);
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let actual = bundle
        .trust_mc_reached_functions_observed(&mut session, site())
        .unwrap();
    assert_eq!(actual, BTreeSet::from([FuncId::new(3), FuncId::new(17)]));
    retire_input_drop(&mut bundle, &mut session);
}
#[test]
fn later_missing_request_retires_the_completed_deep_unknown_census_before_error_return() {
    let mut bundle = fixture();
    deep_drop(&mut bundle);
    bundle.requests.push(request(404));
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        bundle.trust_mc_reached_functions_observed(&mut session, site()),
        Err(ObservedValueError::InvalidRange)
    );
    assert!(session.first_refusal().is_none());
    retire_input_drop(&mut bundle, &mut session);
}
