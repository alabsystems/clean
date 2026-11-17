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

fn same_input_handoff(observed: &crate::scalar_call::ObservedScalarCall, dir: &Path) {
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
}

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[test]
fn helper_tv_refusal_preserves_same_input_legacy_module_and_typed_failure() {
    use clean_compiler::primitive_uses::OwnedPipelineError;
    let dir = tempfile::tempdir().unwrap();
    let file = dir.path().join("Observed.lean");
    std::fs::write(&file, SOURCE).unwrap();
    let observed = match ScalarCall::from_source_observed(
        &file,
        "scalar",
        2,
        NativeObservationLimits::default(),
    ) {
        Err(error) => error,
        Ok(_) => panic!("known helper TV refusal changed: requalify actual scalar acceptance"),
    };
    capture::failure("helper-tv-refusal", &file, &observed);
    let failed = observed
        .compiler_failure()
        .expect("actual typed consumer refusal");
    let OwnedPipelineError::Consumer(error) = failed.error() else {
        panic!("expected actual downstream native consumer refusal")
    };
    let Some(LaneError::TrustCg(message)) = error.downcast_ref::<LaneError>() else {
        panic!("actual TrustCG refusal retained: {error:#}")
    };
    assert!(
        message.contains("clean-kernel-tv") && message.contains("was not kernel-replayed"),
        "{message}"
    );
    let input = failed.input().expect("actual failed owned input frame");
    let delegate = DelegatingBackend {
        real: backend(),
        input: RefCell::new(None),
    };
    let error = crate::compile::write_selected_object(
        input.declarations(),
        input.environment(),
        input.config(),
        input.emit_config(),
        (&delegate, crate::compile::host_trust_cg_target().unwrap()),
        &dir.path().join("legacy-helper.o"),
        input.runtime_closure(),
    )
    .unwrap_err();
    assert!(
        error.to_string().contains("was not kernel-replayed"),
        "{error:#}"
    );
    let bytes = observed
        .observations()
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
        .unwrap();
    assert_eq!(
        bytes,
        delegate.input.borrow().as_ref().unwrap(),
        "same actual selected input and exact TV/license packet; equality is not acceptance"
    );
    capture::legacy_module(
        "helper-tv-refusal",
        delegate.input.borrow().as_ref().unwrap(),
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
    same_input_handoff(&observed, dir.path());
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
