// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
use crate::signature_abi::*;

fn abi() -> SignatureAbi {
    SignatureAbi {
        target: AbiTarget {
            triple: "example-target".into(),
            data_layout: "e-p:64:64".into(),
            abi: "c".into(),
            cpu: "generic".into(),
            features: vec!["feature".into()],
            target_spec: "identity-only".into(),
            pointer_bytes: 8,
            little_endian: true,
        },
        frontend: AbiFrontend {
            name: "producer λ".into(),
            revision: "revision".into(),
        },
        convention: "c".into(),
        lowered_convention: crate::CallingConv::C,
        source_abi: "C".into(),
        can_unwind: false,
        variadic: false,
        fixed_count: 0,
        arguments: vec![],
        result: AbiArgument {
            size: 0,
            align: 1,
            mode: AbiPassMode::Ignore,
            bindings: vec![],
        },
    }
}

#[test]
fn present_abi_is_checked_in_real_module_wire_identity_under_both_schemes() {
    let mut module = module();
    module.func_types[0].abi = Some(abi());
    for scheme in [IdentityScheme::V2, IdentityScheme::V3] {
        let mut observer = Observer::default();
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        let before = observed_module_identity(&module, scheme, &mut session, site()).unwrap();
        assert_eq!(before, module.stable_digest_under(scheme));
        module.func_types[0]
            .abi
            .as_mut()
            .unwrap()
            .frontend
            .revision
            .push('!');
        let after = observed_module_identity(&module, scheme, &mut session, site()).unwrap();
        assert_ne!(before, after);
        assert_eq!(after, module.stable_digest_under(scheme));
    }
}

#[test]
fn past_reader_abi_node_limit_is_refused_in_module_identity_without_a_prefix_digest() {
    let mut module = module();
    let mut descriptor = abi();
    descriptor.target.features = vec![String::new(); 65_536];
    assert!(descriptor.validate_encoding_limits().is_err());
    module.func_types[0].abi = Some(descriptor);
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        module.stable_digest_observed(&mut session, site()),
        Err(ObservedValueError::UnsupportedValue)
    );
    assert!(session.first_refusal().is_none());
}

#[test]
fn actual_abi_string_growth_inside_module_wire_can_stop_before_the_large_copy() {
    let mut module = module();
    let mut descriptor = abi();
    descriptor.frontend.revision = "x".repeat(4097);
    module.func_types[0].abi = Some(descriptor);
    let mut measured = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut measured);
    module.stable_digest_observed(&mut session, site()).unwrap();
    let stop = measured
        .events
        .iter()
        .position(|event| {
            event.phase == ExecutionPhase::CanonicalSerialization && event.copy_bytes > 4097
        })
        .expect("real ABI string allocation/copy storage");
    let mut observer = Observer {
        stop_at: Some(stop + 1),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        module.stable_digest_observed(&mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(session.first_refusal().unwrap().cause, "interior");
    assert!(
        observer
            .events
            .iter()
            .skip(stop + 1)
            .all(|event| event.phase == ExecutionPhase::ScratchRetirement)
    );
}
