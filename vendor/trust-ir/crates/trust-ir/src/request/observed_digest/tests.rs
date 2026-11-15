// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
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
    fn admit(&mut self, event: ExecutionProgress) -> core::result::Result<(), Self::Refusal> {
        self.events.push(event);
        if self.stop_at == Some(self.events.len()) {
            return Err("interior");
        }
        if self.stop_retirement && event.phase == ExecutionPhase::ScratchRetirement {
            return Err("retirement");
        }
        self.work = self.work.checked_add(event.work).ok_or("work overflow")?;
        self.bytes = self
            .bytes
            .checked_add(event.copy_bytes)
            .ok_or("byte overflow")?;
        if self.work_limit.is_some_and(|cap| self.work > cap) {
            return Err("work");
        }
        if self.byte_limit.is_some_and(|cap| self.bytes > cap) {
            return Err("bytes");
        }
        Ok(())
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(0))
}
fn bundle() -> NativeVerificationBundle {
    let mut value = crate::request::tests::native_bundle();
    fixtures::populate(&mut value);
    value
}
fn observed(bundle: &NativeVerificationBundle) -> ProofDigest {
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let answer = bundle
        .stable_digest_observed(&mut session, site())
        .expect("observed identity");
    assert!(session.first_refusal().is_none());
    assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    assert!(observer.events.iter().all(|event| event.site == site()));
    answer
}
fn parity(bytes: &[u8], write: impl FnOnce(&mut Writer<'_, '_, Observer>) -> Result) {
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let actual =
        digest(&mut session, site(), "canonical-field-test", write).expect("field identity");
    assert_eq!(
        actual,
        ProofDigest::sha256_domain("canonical-field-test", bytes)
    );
}

#[test]
fn complete_bundle_and_every_child_digest_match_unchanged_canonical_spelling() {
    let bundle = bundle();
    assert_eq!(bundle.evidence_bundles.len(), 3);
    assert_eq!(bundle.compiler_facts.adt_layouts.len(), 1);
    assert_eq!(bundle.compiler_facts.fat_pointers.len(), 1);
    assert_eq!(bundle.compiler_facts.trait_object_metadata.len(), 1);
    assert_eq!(bundle.compiler_facts.pointer_offsets.len(), 1);
    assert_eq!(bundle.compiler_facts.casts.len(), 1);
    assert_eq!(observed(&bundle), bundle.stable_digest());
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        bundle
            .compiler_facts
            .stable_digest_observed(&mut session, site())
            .unwrap(),
        bundle.compiler_facts.stable_digest()
    );
    assert_eq!(
        bundle
            .lineage
            .stable_digest_observed(&mut session, site())
            .unwrap(),
        bundle.lineage.stable_digest()
    );
    for node in &bundle.lineage.nodes {
        assert_eq!(
            node.stable_digest_observed(&mut session, site()).unwrap(),
            node.stable_digest()
        );
    }
    for request in &bundle.requests {
        assert_eq!(
            request
                .stable_digest_observed(&mut session, site())
                .unwrap(),
            request.stable_digest()
        );
    }
    for evidence in &bundle.evidence_bundles {
        assert_eq!(
            evidence
                .stable_digest_observed(&mut session, site())
                .unwrap(),
            evidence.stable_digest()
        );
    }
}

#[test]
fn unordered_rows_and_duplicate_key_ties_preserve_legacy_stable_order() {
    let mut value = bundle();
    value.requests.reverse();
    value.provenance.toolchain.reverse();
    value.lineage.nodes.reverse();
    value.lineage.roots.reverse();
    value.evidence_bundles.reverse();
    let mut duplicate = value.requests[0].clone();
    match &mut duplicate {
        NativeVerificationRequest::TrustVc(r) => {
            r.provenance.expected_verifier.name.push_str("-different")
        }
        NativeVerificationRequest::TrustMc(r) => {
            r.provenance.expected_verifier.name.push_str("-different")
        }
        NativeVerificationRequest::TrustWp(r) => {
            r.provenance.expected_verifier.name.push_str("-different")
        }
    }
    value.requests.push(duplicate);
    if let Some(node) = value.lineage.nodes.first().cloned() {
        let mut other = node;
        other.transform.name.push_str("-different");
        value.lineage.nodes.push(other);
    }
    assert_eq!(observed(&value), value.stable_digest());
    let before = observed(&value);
    value.requests.reverse();
    assert_eq!(observed(&value), value.stable_digest());
    // Duplicate keys are not a set: stable tie order remains identity-bearing.
    assert_ne!(before, observed(&value));
}

#[test]
fn canonical_tool_names_match_unicode_separators_families_and_long_input() {
    let long = format!("TRUST__MC_{}", "x_λ ".repeat(2050));
    for name in [
        "",
        " \u{2003}",
        "TRUSTVC",
        "trust-vc",
        "trust_vc--z",
        "TRUST___IR___x",
        "trustwp-x",
        "trust--mc-x",
        "λtrust_mcλ",
        long.as_str(),
    ] {
        let tool = NativeToolIdentity {
            name: name.into(),
            version: Some("vλ".into()),
            revision: None,
            digest: Some(ProofDigest::sha256([13; 32])),
        };
        let mut bytes = Vec::new();
        write_tool_identity_stable(&mut bytes, &tool);
        parity(&bytes, |out| write_tool_identity(out, &tool));
    }
}

#[test]
fn iterative_nested_type_and_constant_preimages_match_and_splat_is_not_expanded() {
    let ty = Ty::Tuple(vec![
        Ty::I32,
        Ty::Ref(Box::new(Ty::Vector(Box::new(Ty::U8), 16))),
        Ty::Tuple(vec![Ty::Isize, Ty::Usize, Ty::Char]),
        Ty::Tensor(Box::new(Ty::I32), 2),
    ]);
    let mut bytes = Vec::new();
    write_ty_stable(&mut bytes, &ty);
    parity(&bytes, |out| write_ty(out, &ty));
    let constant = Constant::Record(vec![
        (
            "bytes".into(),
            Constant::Bytes {
                data: vec![0, 255, 3],
                utf8: false,
            },
        ),
        (
            "splat".into(),
            Constant::Splat {
                elem: Box::new(Constant::Array(vec![
                    Constant::Int(-1),
                    Constant::U128(u128::MAX),
                ])),
                len: u64::MAX,
            },
        ),
    ]);
    bytes.clear();
    write_constant_stable(&mut bytes, &constant);
    parity(&bytes, |out| write_constant(out, &constant));
}

#[test]
fn producer_internal_type_hole_is_typed_refusal_without_hash_publication() {
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        digest(&mut session, site(), "hole", |out| write_ty(
            out,
            &Ty::Error
        )),
        Err(ObservedValueError::UnsupportedValue)
    );
}

#[test]
fn byte_tamper_changes_observed_bundle_identity_without_relabeling_its_source() {
    let original = bundle();
    let expected = observed(&original);
    for field in 0..3 {
        let mut changed = original.clone();
        match field {
            0 => changed.provenance.producer_version.push_str("-tamper"),
            1 => changed.lineage.nodes[0].transform.name.push_str("-tamper"),
            _ => changed.requests.reverse(),
        }
        assert_eq!(observed(&changed), changed.stable_digest());
        if field != 2 {
            assert_ne!(expected, observed(&changed));
        } else {
            assert_eq!(expected, observed(&changed));
        }
    }
}

mod held_result;
mod stops;

mod fixtures;

#[test]
fn every_variable_length_sort_key_field_matches_the_legacy_derived_order() {
    let mut tools = vec![
        NativeToolIdentity {
            name: "same".into(),
            version: Some("same".into()),
            revision: Some("b".into()),
            digest: Some(ProofDigest::sha256([1; 32])),
        },
        NativeToolIdentity {
            name: "same".into(),
            version: Some("same".into()),
            revision: Some("a".into()),
            digest: Some(ProofDigest::sha256([2; 32])),
        },
        NativeToolIdentity {
            name: "same".into(),
            version: None,
            revision: None,
            digest: None,
        },
        NativeToolIdentity {
            name: "same".into(),
            version: Some("same".into()),
            revision: Some("a".into()),
            digest: Some(ProofDigest::sha256([1; 32])),
        },
    ];
    let certificates = vec![
        ProofCertificateRef {
            obligation: ProofId::new(2),
            prover: "a".into(),
            evidence_digest: ProofDigest::sha256([1; 32]),
        },
        ProofCertificateRef {
            obligation: ProofId::new(1),
            prover: "z".into(),
            evidence_digest: ProofDigest::sha256([2; 32]),
        },
        ProofCertificateRef {
            obligation: ProofId::new(1),
            prover: "z".into(),
            evidence_digest: ProofDigest::sha256([1; 32]),
        },
        ProofCertificateRef {
            obligation: ProofId::new(1),
            prover: "a".into(),
            evidence_digest: ProofDigest::sha256([3; 32]),
        },
    ];
    for _ in 0..2 {
        let mut bytes = Vec::new();
        write_tool_identities_stable(&mut bytes, &tools);
        write_certificate_refs_stable(&mut bytes, &certificates);
        parity(&bytes, |out| {
            write_tool_identities(out, &tools)?;
            write_certificate_refs(out, &certificates)
        });
        tools.reverse();
    }
}
