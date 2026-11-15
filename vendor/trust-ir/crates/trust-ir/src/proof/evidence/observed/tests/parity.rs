// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn complete_original_stable_bytes_for_all_evidence_carriers_are_exact() {
    for e in [
        ProofEvidence::SmtProof(vec![0, 255]),
        ProofEvidence::LeanProof("é\0".into()),
        ProofEvidence::KaniHarness("h".into()),
        ProofEvidence::Trusted("why".into()),
        ProofEvidence::TranslationValidation {
            rule_name: "r".into(),
            smt_hash: [7; 32],
        },
        ProofEvidence::GammaCrownBound {
            epsilon: -0.0,
            verified_layers: u32::MAX,
        },
        ProofEvidence::InheritedFromCallee {
            callee: FuncId::new(9),
            obligation: ProofId::new(3),
            external: None,
        },
        rich().evidence,
    ] {
        exact(&certificate(e));
    }
}
#[test]
fn malformed_clean_binding_lists_and_island_bytes_are_data_without_authority() {
    let c = rich();
    exact(&c);
    assert!(!ordinary_bytes(&c).is_empty());
    // Arbitrary opaque term/context/digest and unknown anchor remain identity
    // DATA. No kernel/status decision is substituted for replay here.
    assert!(matches!(
        c.evidence,
        ProofEvidence::CleanCic {
            kernel_recheck: Some(_),
            ..
        }
    ));
}
#[test]
fn local_external_and_optional_zero_obligation_have_original_distinct_framing() {
    for obligation in [None, Some(ProofId::new(0)), Some(ProofId::new(u32::MAX))] {
        let e = ProofEvidence::InheritedFromCallee {
            callee: FuncId::new(2),
            obligation: ProofId::new(4),
            external: Some(crate::ExternRef {
                module: ImportId::new(8),
                symbol: "s\0é".into(),
                obligation,
            }),
        };
        exact(&certificate(e));
    }
}
#[test]
fn directive_and_binding_absences_preserve_original_tail_omissions() {
    for directive in 0..4 {
        let mut c = rich();
        if let ProofEvidence::CleanCic { kernel_recheck, .. } = &mut c.evidence {
            match directive {
                0 => *kernel_recheck = None,
                1 => kernel_recheck.as_mut().unwrap().binding = None,
                2 => {
                    kernel_recheck
                        .as_mut()
                        .unwrap()
                        .binding
                        .as_mut()
                        .unwrap()
                        .environment = None
                }
                _ => {}
            }
        }
        exact(&c);
    }
}
#[test]
fn all_float_bits_including_signed_zero_and_nan_payloads_keep_raw_identity() {
    for bits in [
        0,
        1,
        0x8000000000000000,
        0x7ff0000000000000,
        0xfff0000000000000,
        0x7ff8000000000001,
        0x7ff8000000000002,
        0x7ff0000000000001,
    ] {
        exact(&certificate(ProofEvidence::GammaCrownBound {
            epsilon: f64::from_bits(bits),
            verified_layers: 7,
        }));
    }
}
#[test]
fn full_prover_obligation_identity_and_coverage_exclusion_match_original() {
    let mut c = rich();
    c.prover = "é🦀\0".repeat(600);
    c.obligation = ProofId::new(u32::MAX);
    exact(&c);
    let old = c.lineage_ref();
    c.assurance = Some(crate::proof::CoverageAssurance {
        bound: crate::proof::CoverageBound::Unrecorded,
        request_digest: digest(88),
    });
    assert_eq!(c.lineage_ref(), old);
    exact(&c);
}
