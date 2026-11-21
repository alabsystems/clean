// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::native_trustcg::{LaneError, ObjectBackend, TrustCg};
use crate::scalar_call::ScalarCall;
use clean_compiler::emit_trust_ir::serialize_tmbc;
use clean_compiler::primitive_uses::{ObservationGap, ObservationLimit};
use std::cell::RefCell;
use std::path::Path;

mod capture;

const SOURCE: &str = "def helper (x : UInt64) : UInt64 := x + 1\n\
def scalar (a b : UInt32) (c d : UInt64) : UInt64 :=\n\
  a.toUInt64 + b.toUInt64 * 65537 + helper c * 3 + d * 5\n\
def heap (a b : UInt32) (c d : UInt64) : UInt64 :=\n\
  UInt64.ofNat (c.toNat + d.toNat + a.toNat + b.toNat)\n\
def wrong (a : UInt64) (b : UInt32) (c d : UInt64) : UInt64 := c\n";

struct DelegatingBackend {
    real: TrustCg,
    input: RefCell<Option<Vec<u8>>>,
}
impl ObjectBackend for DelegatingBackend {
    fn identity(&self) -> String {
        self.real.identity()
    }
    fn compile_object(
        &self,
        module: &clean_compiler::emit_trust_ir_lane::Module,
        target: &str,
        dir: &Path,
    ) -> Result<PathBuf, LaneError> {
        *self.input.borrow_mut() =
            Some(serialize_tmbc(module).expect("test actual licensed module bytes"));
        self.real.compile_object(module, target, dir)
    }
}
fn backend() -> TrustCg {
    let path = crate::native_trustcg::select_trust_cg_path(
        std::env::var_os("CLEAN_TRUST_CG_BIN"),
        std::env::var_os("PATH"),
    )
    .unwrap()
    .expect("actual supported backend must exist");
    TrustCg::from_path(path).unwrap()
}

fn same_input_handoff(observed: &crate::scalar_call::ObservedScalarCall, dir: &Path) -> Vec<u8> {
    let trace = observed.observations();
    assert!(trace
        .decisions()
        .iter()
        .any(|event| event.role() == NativeInvocationRole::DependencyProbe));
    let compiler = trace
        .compiler()
        .expect("actual complete small compiler artifacts retained");
    let input = compiler
        .input()
        .expect("actual owned source frame retained");
    let delegate = DelegatingBackend {
        real: backend(),
        input: RefCell::new(None),
    };
    let out = dir.join("legacy-same-input.o");
    crate::compile::write_selected_object(
        input.declarations(),
        input.environment(),
        input.config(),
        input.emit_config(),
        (&delegate, crate::compile::host_trust_cg_target().unwrap()),
        &out,
        input.runtime_closure(),
    )
    .unwrap();
    let actual = trace
        .artifacts()
        .iter()
        .find_map(|artifact| match artifact.payload() {
            NativeArtifactPayload::Bytes {
                label: "TMBC input written",
                bytes,
                ..
            } => Some(bytes),
            _ => None,
        })
        .expect("actual backend input bytes");
    assert_eq!(
        actual,
        delegate.input.borrow().as_ref().unwrap(),
        "legacy and observed handoff on same actual selected input"
    );
    let invocation = trace
        .decisions()
        .iter()
        .find(|event| event.owner() == "actual backend invocation")
        .unwrap();
    assert!(matches!(
        trace
            .artifact(invocation.context().unwrap())
            .unwrap()
            .payload(),
        NativeArtifactPayload::Bytes {
            label: "TMBC input written",
            ..
        }
    ));
    let NativeArtifactPayload::Command { arguments, .. } = trace
        .artifact(invocation.artifact().unwrap())
        .unwrap()
        .payload()
    else {
        panic!("actual command")
    };
    assert!(arguments.iter().any(|arg| arg == "--refuse-unlicensed"));
    assert!(trace.artifacts().iter().any(|artifact| matches!(
        artifact.payload(),
        NativeArtifactPayload::ProcessStatus {
            success: true,
            code: Some(0)
        }
    )));
    assert!(trace
        .artifacts()
        .iter()
        .any(|artifact| artifact.owner() == "actual backend object"));
    assert!(trace
        .artifacts()
        .iter()
        .any(|artifact| artifact.owner() == "actual native module before license"));
    delegate.input.into_inner().unwrap()
}

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[test]
fn helper_scalar_acceptance_preserves_same_input_legacy_calls_and_consumer_refusal() {
    use clean_compiler::primitive_uses::{
        compile_lcnf_to_trust_ir_owned_observed, OwnedPipelineError,
    };
    let dir = tempfile::tempdir().unwrap();
    let file = dir.path().join("Observed.lean");
    std::fs::write(&file, SOURCE).unwrap();
    let mut observed =
        ScalarCall::from_source_observed(&file, "scalar", 2, NativeObservationLimits::default())
            .unwrap_or_else(|error| {
                capture::failure("helper-acceptance-refusal", &file, &error);
                panic!("actual helper scalar compilation must succeed: {error:#}")
            });
    capture::success("helper-acceptance", &file, &observed);
    let mut legacy = ScalarCall::from_source(&file, "scalar", 2).unwrap();
    for (a, b, c, d) in [
        (0, 0, 0, 0),
        (1, 2, 3, 4),
        (u32::MAX, u32::MAX, u64::MAX, u64::MAX),
        (0, u32::MAX, u64::MAX, 0),
        (u32::MAX, 0, 1u64 << 63, 1u64 << 63),
        (
            0x1234_5678,
            0x9abc_def0,
            u64::MAX - 1,
            0x1234_5678_9abc_def0,
        ),
    ] {
        let expected = u64::from(a)
            .wrapping_add(u64::from(b).wrapping_mul(65537))
            .wrapping_add(c.wrapping_add(1).wrapping_mul(3))
            .wrapping_add(d.wrapping_mul(5));
        let actual = observed.call(a, b, c, d);
        let baseline = legacy.call(a, b, c, d);
        capture::calls(
            "helper-acceptance",
            &[
                serde_json::json!({"args":[u64::from(a),u64::from(b),c,d],"observed":actual,"legacy":baseline,"expected":expected}),
            ],
        );
        eprintln!(
            "ACTUAL_HELPER_CALL {:?} observed={actual} legacy={baseline} expected={expected}",
            (a, b, c, d)
        );
        assert_eq!(actual, expected);
        assert_eq!(baseline, expected);
    }
    let legacy_input = same_input_handoff(&observed, dir.path());
    capture::legacy_module("helper-acceptance", &legacy_input);
    assert!(observed.observations().artifacts().iter().any(|artifact| {
        matches!(artifact.payload(), NativeArtifactPayload::LicenseCensus(census) if census.unvalidated > 0)
    }), "successful codegen remains explicitly compiler-unvalidated");

    // A test-only consumer removes a real body's license from the same selected
    // input. The unchanged actual backend must refuse; no mutated object is run.
    let input = observed.observations().compiler().unwrap().input().unwrap();
    let negative_dir = tempfile::tempdir().unwrap();
    let actual_backend = backend();
    let negative_input = RefCell::new(Vec::new());
    let missing_name = RefCell::new(String::new());
    let failed = compile_lcnf_to_trust_ir_owned_observed(
        Arc::from(input.declarations().to_vec()),
        Arc::new(input.environment().clone()),
        Arc::new(input.config().clone()),
        input.emit_config().clone(),
        input.meaning(),
        input
            .runtime_closure()
            .map(|closure| Arc::new(closure.clone())),
        ObservationLimits::default(),
        |module| {
            clean_compiler::emit_trust_ir_lane::restamp_ungated_as_unvalidated(module)
                .expect("the actual compiler module must have licensing claims");
            let baseline = serialize_tmbc(module).unwrap();
            assert_eq!(
                baseline, legacy_input,
                "the regenerated licensed baseline must equal the actual observed/legacy input"
            );
            let index = module
                .functions
                .iter()
                .position(|function| !function.blocks.is_empty())
                .expect("the actual helper source must emit a body");
            *missing_name.borrow_mut() = module.functions[index].name.clone();
            let claim = module.functions[index]
                .body_gate
                .take()
                .expect("the actual baseline body has a licensing claim");
            let mutant = serialize_tmbc(module).unwrap();
            assert_ne!(
                mutant, baseline,
                "the negative must actually remove a claim"
            );
            let mut restored = module.clone();
            restored.functions[index].body_gate = Some(claim);
            assert_eq!(
                serialize_tmbc(&restored).unwrap(),
                baseline,
                "restoring that one claim must reconstruct the exact actual baseline"
            );
            *negative_input.borrow_mut() = mutant;
            actual_backend
                .compile_object(
                    module,
                    crate::compile::host_trust_cg_target().unwrap(),
                    negative_dir.path(),
                )
                .map(|_| ())
        },
    )
    .expect_err("the genuine strict backend must reject an unlicensed body");
    let object = negative_dir.path().join("module.o");
    let object_state = std::fs::symlink_metadata(&object);
    capture::consumer_failure(
        "helper-unlicensed-refusal",
        &negative_input.borrow(),
        &failed,
        &object,
        &object_state,
    );
    assert!(
        matches!(&object_state, Err(error) if error.kind() == std::io::ErrorKind::NotFound),
        "a refused mutant must leave no object: {object_state:?}"
    );
    let OwnedPipelineError::Consumer(LaneError::TrustCg(message)) = failed.error() else {
        panic!("expected the actual typed backend consumer refusal: {failed:#}")
    };
    assert!(
        message.contains(&format!(
            "function `{}` has a body but no codegen license (`body_gate` absent) in a trust-ir v61 blob",
            missing_name.borrow().as_str()
        )) && message.contains("failed to read trust_ir module")
            && message.contains("producer omission")
            && message.contains("reader refuses it rather than grandfather it")
            && message.ends_with("(exit 1)"),
        "{message}"
    );
}

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[test]
fn actual_heap_shim_demand_is_recorded_separately_from_runtime_availability() {
    let dir = tempfile::tempdir().unwrap();
    let file = dir.path().join("ObservedHeap.lean");
    std::fs::write(&file, SOURCE).unwrap();
    let mut observed =
        ScalarCall::from_source_observed(&file, "heap", 2, NativeObservationLimits::default())
            .unwrap_or_else(|error| {
                capture::failure("heap-refusal", &file, &error);
                panic!("actual observed heap route: {error:#}")
            });
    capture::success("heap", &file, &observed);
    let mut legacy = ScalarCall::from_source(&file, "heap", 2).unwrap();
    for (a, b, c, d) in [
        (1, 2, 3, 4),
        (u32::MAX, u32::MAX, u64::MAX, u64::MAX),
        (0, 0, 1u64 << 63, 7),
    ] {
        let expected = c
            .wrapping_add(d)
            .wrapping_add(u64::from(a))
            .wrapping_add(u64::from(b));
        let actual = observed.call(a, b, c, d);
        let baseline = legacy.call(a, b, c, d);
        eprintln!(
            "ACTUAL_SCALAR_CALL {:?} observed={actual} legacy={baseline} expected={expected}",
            (a, b, c, d)
        );
        capture::calls(
            if observed.declaration() == &Name::from_string("heap") {
                "heap"
            } else {
                "scalar"
            },
            &[
                serde_json::json!({"args":[a as u64,b as u64,c,d],"observed":actual,"legacy":baseline,"expected":expected}),
            ],
        );
        assert_eq!(actual, expected);
        assert_eq!(baseline, expected);
    }
    let _ = same_input_handoff(&observed, dir.path());
    assert!(
        observed
            .observations()
            .artifacts()
            .iter()
            .any(|artifact| matches!(
                artifact.payload(),
                NativeArtifactPayload::ShimDemand {
                    definition: Some(_),
                    mismatch: None,
                    ..
                }
            )),
        "actual used shim signature, not the full linked union"
    );
}

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[test]
fn native_recording_truncation_keeps_actual_call_and_wrong_source_prototype_stays_refused() {
    let dir = tempfile::tempdir().unwrap();
    let file = dir.path().join("ObservedBudget.lean");
    std::fs::write(&file, SOURCE).unwrap();
    let tiny = ObservationLimits::new(1, 1, 1, 1, 1).unwrap();
    let mut observed = ScalarCall::from_source_observed(
        &file,
        "heap",
        2,
        NativeObservationLimits::new(tiny, tiny),
    )
    .unwrap_or_else(|error| {
        capture::failure("tiny-refusal", &file, &error);
        panic!("truncated recording must still compile normally: {error:#}")
    });
    capture::success("tiny-heap", &file, &observed);
    let actual = observed.call(1, 2, 3, 4);
    capture::calls(
        "tiny-heap",
        &[serde_json::json!({"args":[1,2,3,4],"observed":actual,"expected":10})],
    );
    assert_eq!(actual, 10);
    assert!(observed
        .observations()
        .gaps()
        .iter()
        .any(|gap| matches!(gap, ObservationGap::Truncated(_))));
    assert!(observed.observations().compiler().is_none());
    let legacy = match ScalarCall::from_source(&file, "wrong", 2) {
        Err(error) => error,
        Ok(_) => panic!("prototype must refuse"),
    };
    let observed = match ScalarCall::from_source_observed(
        &file,
        "wrong",
        2,
        NativeObservationLimits::default(),
    ) {
        Err(error) => error,
        Ok(_) => panic!("observed prototype must refuse"),
    };
    assert_eq!(observed.error().to_string(), legacy.to_string());
    assert!(observed.observations().compiler().is_none());
}

#[test]
fn native_ids_refuse_foreign_run_edges_and_finite_budget_is_sticky() {
    let first = NativeRecorder::new(NativeObservationLimits::default());
    let id = first
        .environment("actual first input", Arc::new(Environment::new()))
        .unwrap();
    let first = first.finish();
    let second = NativeRecorder::new(NativeObservationLimits::default());
    second.edge(
        NativeInvocationRole::Backend,
        "hostile foreign artifact",
        Some(&id),
        None,
        "cannot bind",
    );
    let second = second.finish();
    assert!(second.artifact(&id).is_none());
    assert!(first.artifact(&id).is_some());
    assert!(second.decisions().is_empty());
    assert!(second.gaps().iter().any(|gap| matches!(
        gap,
        ObservationGap::Unobserved {
            owner: "native event affinity",
            ..
        }
    )));
    let tiny = ObservationLimits::new(1, 1, 1, 1, 1).unwrap();
    let recorder = NativeRecorder::new(NativeObservationLimits::new(tiny, tiny));
    assert!(recorder
        .environment("actual byte-limited input", Arc::new(Environment::new()))
        .is_none());
    let trace = recorder.finish();
    assert!(matches!(
        trace.gaps(),
        [ObservationGap::Truncated(ObservationLimit::Bytes)]
    ));
}

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[test]
fn actual_selected_body_and_extern_attribute_changes_remain_source_affine() {
    let dir = tempfile::tempdir().unwrap();
    let first = dir.path().join("BodyOne.lean");
    let second = dir.path().join("BodyTwo.lean");
    let prefix = "def changed (a b : UInt32) (c d : UInt64) : UInt64 :=\n  UInt64.ofNat ";
    std::fs::write(
        &first,
        format!("{prefix}(c.toNat + d.toNat + a.toNat + b.toNat)\n"),
    )
    .unwrap();
    std::fs::write(
        &second,
        format!("{prefix}(c.toNat * d.toNat + a.toNat + b.toNat)\n"),
    )
    .unwrap();
    let mut one =
        ScalarCall::from_source_observed(&first, "changed", 2, NativeObservationLimits::default())
            .unwrap_or_else(|e| {
                capture::failure("body-one-error", &first, &e);
                panic!("{e:#}")
            });
    let mut two =
        ScalarCall::from_source_observed(&second, "changed", 2, NativeObservationLimits::default())
            .unwrap_or_else(|e| {
                capture::failure("body-two-error", &second, &e);
                panic!("{e:#}")
            });
    capture::success("body-one", &first, &one);
    capture::success("body-two", &second, &two);
    let first_actual = one.call(1, 2, 2, 3);
    let second_actual = two.call(1, 2, 2, 3);
    capture::calls(
        "body-one",
        &[serde_json::json!({"args":[1,2,2,3],"observed":first_actual,"expected":8})],
    );
    capture::calls(
        "body-two",
        &[serde_json::json!({"args":[1,2,2,3],"observed":second_actual,"expected":9})],
    );
    assert_eq!(first_actual, 8);
    assert_eq!(second_actual, 9);
    let prepared = |trace: &NativePrimitiveUseObservations| {
        trace
            .artifacts()
            .iter()
            .find_map(|artifact| match artifact.payload() {
                NativeArtifactPayload::PreparedConstant(info)
                    if info.name == Name::from_string("changed") =>
                {
                    Some(info.value.clone())
                }
                _ => None,
            })
            .unwrap()
    };
    assert_ne!(prepared(one.observations()), prepared(two.observations()));
    let id = one.observations().artifacts()[0].id();
    assert!(two.observations().artifact(id).is_none());
    let attributed = dir.path().join("ActualExtern.lean");
    std::fs::write(
        &attributed,
        "@[extern \"foreign_changed\"] def changed (a b : UInt32) (c d : UInt64) : UInt64 := c\n",
    )
    .unwrap();
    let legacy = match ScalarCall::from_source(&attributed, "changed", 2) {
        Err(e) => e,
        Ok(_) => panic!("existing extern-root check must refuse"),
    };
    let observed = match ScalarCall::from_source_observed(
        &attributed,
        "changed",
        2,
        NativeObservationLimits::default(),
    ) {
        Err(e) => e,
        Ok(_) => panic!("recording cannot permit an extern-root"),
    };
    capture::failure("extern-refusal", &attributed, &observed);
    assert_eq!(observed.error().to_string(), legacy.to_string());
    assert!(observed.observations().compiler().is_none());
    assert!(observed.observations().artifacts().iter().any(|artifact|matches!(artifact.payload(),NativeArtifactPayload::Environment(env)if env.get_extern(&Name::from_string("changed")).is_some())));
}
