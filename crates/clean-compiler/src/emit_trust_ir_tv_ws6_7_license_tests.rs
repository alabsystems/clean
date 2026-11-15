// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! WS6.7, continued (a child of `emit_trust_ir_tv::tests::ws6_7`, whose
//! fixtures it reuses): the c04 A2 retarget, license evidence, the transplant
//! mutation control, and roadmap parts (c) callee rows, (d) producer hygiene
//! and (e) `Gated` only with its evidence.

use super::*;

// ---- the c04 A2 shape ------------------------------------------------------------

/// c04 A2, the ONE-SIDED edit (verify.c04.L1): the call is retargeted and its
/// inheritance row still names `plus`. WS1.4's call-edge bijection refuses it
/// on a bound and an unbound certificate alike, and Clean's pre-flight
/// `validate_module_for_codegen` revokes `top`'s license.
#[test]
fn ws6_7_c04_call_retarget_is_refused() {
    for bound in [true, false] {
        let mut module = minted_c04(bound);
        assert!(
            !top_is_refused_for_codegen(&module),
            "control (bound = {bound})"
        );
        retarget_top(&mut module, "minus", false);
        assert!(
            top_is_refused_for_codegen(&module),
            "bound = {bound}: {:?}",
            validate_module_for_codegen(&module)
        );
    }
}

/// c04 A2, the CONSISTENT edit (verify.c04.L2): call AND inheritance row both
/// move to `minus`, which carries an honest TV of its own. The statement is
/// callee-parametric, so only the binding can see it: the bound certificate
/// is refused as `callees` and its license revoked by the pre-flight.
#[test]
fn ws6_7_c04_consistent_retarget_is_refused_by_the_binding() {
    let mut module = minted_c04(true);
    let top = tv_obligation(&module, "top").id;
    retarget_top(&mut module, "minus", true);
    let errors = validate_module(&module);
    assert!(
        binding_refusals(&errors, top).contains(&"callees".to_string()),
        "{errors:?}"
    );
    assert!(top_is_refused_for_codegen(&module));
}

/// CONTROL for the consistent edit on an UNBOUND certificate. The edit
/// rewrites `top`'s body, so a license left as minted names the OLD body and
/// is refused as `GatedEvidenceMismatch`. The body digest is not a secret,
/// though: an adversary who also RE-STAMPS it leaves a module the default
/// lanes admit — the disclosed residual that binding exists to close — and
/// only the bound policy refuses it, as `UnboundCertificate`.
#[test]
fn ws6_7_c04_consistent_retarget_residual_without_a_binding() {
    let mut module = minted_c04(false);
    retarget_top(&mut module, "minus", true);
    let top_fn = fid(&module, "top");
    assert!(
        evidence_mismatches(&validate_module(&module), top_fn)
            .iter()
            .any(|d| d.contains("another body")),
        "the retarget moved the body the license names"
    );
    let restamped = module.function_body_digest(top_fn).expect("digest");
    for func in module.functions.iter_mut().filter(|f| f.id == top_fn) {
        if let Some(BodyGate::Gated {
            evidence: Some(evidence),
            ..
        }) = &mut func.body_gate
        {
            evidence.body_digest = restamped;
        }
    }
    assert_eq!(validate_module_for_codegen(&module), Vec::new());
    let top = tv_obligation(&module, "top").id.index();
    assert!(validate_module_with_config(&module, &strict())
        .into_errors()
        .contains(&ValidationError::UnboundCertificate { obligation: top }));
}

// ---- (b) license evidence ------------------------------------------------------------

/// NEGATIVE TWIN (roadmap: stale `body_digest` — edit the body after mint):
/// `plus`'s `add` rewritten to `sub` after its license was stamped. Whatever
/// else the re-checker says about the edited body, its license is refused as
/// `GatedEvidenceMismatch`: it names the body the kernel judged, not this one.
#[test]
fn ws6_7_body_edited_after_mint_is_refused_by_its_evidence() {
    let mut module = minted_c04(true);
    let plus = fid(&module, "plus");
    let mut edited = 0;
    for func in module.functions.iter_mut().filter(|f| f.id == plus) {
        for node in func.blocks.iter_mut().flat_map(|b| b.body.iter_mut()) {
            if let Inst::BinOp {
                op: op @ BinOp::Add,
                ..
            } = &mut node.inst
            {
                *op = BinOp::Sub;
                edited += 1;
            }
        }
    }
    assert_eq!(edited, 1, "exactly one add rewritten");
    let errors = validate_module(&module);
    assert!(
        evidence_mismatches(&errors, plus)
            .iter()
            .any(|d| d.contains("another body")),
        "{errors:?}"
    );
}

/// NEGATIVE TWIN, isolated: the body untouched and ONE byte of the recorded
/// digest flipped. The kernel re-check still passes, so the only refusal is
/// the license's — `GatedEvidenceMismatch` on every lane, and the codegen
/// lane with it.
#[test]
fn ws6_7_stale_body_digest_is_refused() {
    let mut module = minted_c04(true);
    let plus = fid(&module, "plus");
    for func in module.functions.iter_mut().filter(|f| f.id == plus) {
        if let Some(BodyGate::Gated {
            evidence: Some(evidence),
            ..
        }) = &mut func.body_gate
        {
            evidence.body_digest.bytes[0] ^= 1;
        }
    }
    let errors = validate_module(&module);
    assert_eq!(
        evidence_mismatches(&errors, plus).len(),
        1,
        "exactly the digest half is refused: {errors:?}"
    );
    assert!(
        errors.iter().all(|e| matches!(
            e,
            ValidationError::GatedEvidenceMismatch { function, .. } if *function == plus.index()
        )),
        "{errors:?}"
    );
    assert!(!validate_module_for_codegen(&module).is_empty());
}

/// NEGATIVE TWIN: evidence citing ANOTHER function's TV row (`minus`'s) is
/// refused as `GatedEvidenceMismatch` — the row must be scoped to the
/// licensed function.
#[test]
fn ws6_7_evidence_citing_another_row_is_refused() {
    let mut module = minted_c04(true);
    let plus = fid(&module, "plus");
    let minus_row = tv_obligation(&module, "minus").id;
    for func in module.functions.iter_mut().filter(|f| f.id == plus) {
        if let Some(BodyGate::Gated {
            evidence: Some(evidence),
            ..
        }) = &mut func.body_gate
        {
            evidence.obligation = minus_row;
        }
    }
    assert!(
        evidence_mismatches(&validate_module(&module), plus)
            .iter()
            .any(|d| d.contains("scoped to this function")),
        "{:?}",
        validate_module(&module)
    );
}

/// NEGATIVE TWIN (roadmap: strip one binding — here, the license's half): a
/// license with its evidence stripped is what every pre-evidence producer
/// wrote, so the default lanes admit it; the evidence policy refuses it BY
/// NAME, `UnevidencedGate`, on exactly that function.
#[test]
fn ws6_7_stripped_evidence_is_refused_by_the_evidence_policy() {
    let mut module = minted_c04(true);
    let top = fid(&module, "top");
    for func in module.functions.iter_mut().filter(|f| f.id == top) {
        assert!(
            func.invalidate_gate_evidence(),
            "control: `top` had evidence"
        );
    }
    assert_eq!(validate_module_for_codegen(&module), Vec::new());
    assert_eq!(
        validate_module_with_config(&module, &strict()).into_errors(),
        vec![ValidationError::UnevidencedGate {
            function: top.index(),
            authority: CLEAN_KERNEL_TV_AUTHORITY.to_string(),
        }]
    );
}

// ---- transplant mutation control -------------------------------------------------

/// MUTATION CONTROL (roadmap: transplant a minted certificate onto a sibling
/// with the same signature): `plus2` has `plus`'s body byte for byte, so the
/// kernel equation would hold for it too. Re-scoping `plus`'s obligation to
/// `plus2` and moving `plus`'s license with it is still refused twice — the
/// certificate cites `CleanTV.plus.denotes` and its lineage is keyed on the
/// symbol `plus`, and the license's `GateEvidence.body_digest` names `plus`'s
/// body, not `plus2`'s (the digest binds the function's own identity) — and
/// `plus2`'s license is revoked.
#[test]
fn ws6_7_transplanted_certificate_is_refused_by_its_scope() {
    for bound in [true, false] {
        let (mut module, mut originals, env) = c04_program();
        originals.retain(|(n, _)| n != "plus2");
        let report = if bound {
            mint_bound(&mut module, &originals, &sources_in(&env, &originals))
        } else {
            certify_backend_translation(&mut module, &originals)
        };
        assert_eq!(report.certified.len(), 3, "{report:?}");
        let plus2 = fid(&module, "plus2");
        let plus = tv_obligation(&module, "plus").id;
        let plus_gate = module
            .functions
            .iter()
            .find(|f| f.name == "plus")
            .and_then(|f| f.body_gate.clone());
        assert!(
            plus_gate.as_ref().is_some_and(|g| g.evidence().is_some()),
            "control: `plus` carries an evidenced license"
        );
        for obligation in &mut module.proof_obligations {
            if obligation.id == plus {
                obligation.function = Some(plus2);
            }
        }
        for func in module.functions.iter_mut().filter(|f| f.id == plus2) {
            func.body_gate = plus_gate.clone();
        }
        // Both lineages key the owning function (v6 by index, v8 by link
        // symbol), so the re-scoped row no longer matches its certificate ...
        let errors = validate_module(&module);
        assert!(
            errors.contains(&ValidationError::CertifiedCleanCicLineageMismatch {
                obligation: plus.index()
            }),
            "bound = {bound}: {errors:?}"
        );
        // ... and the moved license's evidence names `plus`'s body.
        assert!(
            evidence_mismatches(&errors, plus2)
                .iter()
                .any(|d| d.contains("another body")),
            "bound = {bound}: {errors:?}"
        );
        let refused = validate_module_for_codegen(&module);
        assert!(
            refused.iter().any(|e| matches!(
                e,
                ValidationError::GatedWithoutEvidence { function, .. } if *function == plus2.index()
            )),
            "bound = {bound}: {refused:?}"
        );
    }
}

// ---- (c) callee rows keyed by the called function --------------------------------

/// (c): `top` carries exactly one `InheritedFromCallee` row, naming the
/// FuncId its `Call` targets and that function's OWN TV obligation — the
/// WS1.4 bijection, built from the call target rather than a source name.
#[test]
fn ws6_7_callee_rows_are_keyed_by_the_called_function() {
    let module = minted_c04(false);
    let top = tv_obligation(&module, "top").id;
    let called: Vec<FuncId> = module
        .functions
        .iter()
        .filter(|f| f.name == "top")
        .flat_map(|f| f.instructions())
        .filter_map(|n| match &n.inst {
            Inst::Call { callee, .. } => Some(*callee),
            _ => None,
        })
        .collect();
    let rows: Vec<(FuncId, ProofId)> = module
        .proof_certificates
        .iter()
        .filter(|c| c.obligation == top)
        .filter_map(|c| match &c.evidence {
            ProofEvidence::InheritedFromCallee {
                callee,
                obligation,
                external: None,
            } => Some((*callee, *obligation)),
            _ => None,
        })
        .collect();
    assert_eq!(called, vec![fid(&module, "plus")]);
    assert_eq!(
        rows,
        vec![(fid(&module, "plus"), tv_obligation(&module, "plus").id)]
    );
}

// ---- (d) producer hygiene --------------------------------------------------------

/// (d): the minter refuses a body Clean did not produce — relabelled `TRust`
/// or with no recorded producer — naming the reason, and leaves the module
/// untouched. The same body stamped `Clean` certifies (the control). This is
/// Clean-side hygiene; the `clean_backend_tv` anchor itself stays
/// producer-agnostic (trust-ir's WS1.4 decision on F-016).
#[test]
fn ws6_7_minter_refuses_a_body_clean_did_not_produce() {
    for producer in [Some(Producer::TRust), None] {
        let mut module = emit_trust_ir(&[tv_demo_decl()]).expect("lowers");
        for f in &mut module.functions {
            f.producer = producer.clone();
        }
        let before = module.clone();
        let report = certify_backend_translation(
            &mut module,
            &[("tv_demo".to_string(), tv_demo_original())],
        );
        assert!(report.certified.is_empty(), "{producer:?}: {report:?}");
        assert!(
            report
                .refused
                .iter()
                .any(|(n, r)| n == "tv_demo" && r.contains("producer hygiene")),
            "{producer:?}: {report:?}"
        );
        assert_eq!(module, before, "{producer:?}: a refusal mints nothing");
    }
    let mut module = emit_trust_ir(&[tv_demo_decl()]).expect("lowers");
    assert_eq!(module.functions[0].producer, Some(Producer::Clean));
    let report =
        certify_backend_translation(&mut module, &[("tv_demo".to_string(), tv_demo_original())]);
    assert_eq!(report.certified, vec!["tv_demo".to_string()]);
}

// ---- (e) Gated only with its evidence -----------------------------------------------

use crate::tv_gate_source_tests as gate_source;

/// (e), structurally: `BodyGate::Gated` is constructed in exactly ONE place
/// in the minter — the arm that also pushes the `Certified` obligation and its
/// certificate — and never by the emitter, which stamps `Ungated` only, nor by
/// the minter's bound half.
#[test]
fn ws6_7_gated_is_constructed_only_beside_its_evidence() {
    let sites = gate_source::gated_sites(include_str!("emit_trust_ir_tv.rs"));
    let [site] = sites.as_slice() else {
        panic!("exactly one Gated construction site in the minter, got {sites:?}");
    };
    assert!(
        site.certified_arm,
        "the Gated site is inside the Certified arm"
    );
    assert!(
        site.obligation && site.certificate,
        "the license, the obligation and its certificate are written in one arm"
    );
    assert!(
        gate_source::gated_sites(include_str!("emit_trust_ir.rs")).is_empty(),
        "the emitter never licenses a body"
    );
    assert!(
        gate_source::gated_sites(include_str!("emit_trust_ir_tv_binding.rs")).is_empty(),
        "the binding half never licenses a body"
    );
}

/// (e), behaviourally: over bound and unbound mints, a body is `Gated`
/// exactly when ONE `Certified` TV obligation is scoped to it and carries a
/// `clean_backend_tv` `CleanCic` certificate, and the license's evidence names
/// that row and the body's digest; a body that was skipped keeps `Ungated`
/// and carries no obligation.
#[test]
fn ws6_7_gated_iff_certified_with_evidence() {
    for bound in [true, false] {
        let (mut module, mut originals, env) = c04_program();
        originals.retain(|(n, _)| n != "minus");
        let report = if bound {
            mint_bound(&mut module, &originals, &sources_in(&env, &originals))
        } else {
            certify_backend_translation(&mut module, &originals)
        };
        assert_eq!(report.certified.len(), 3, "{report:?}");
        for f in &module.functions {
            let rows: Vec<&ProofObligation> = module
                .proof_obligations
                .iter()
                .filter(|o| o.function == Some(f.id))
                .collect();
            let gated = matches!(f.body_gate, Some(BodyGate::Gated { .. }));
            if gated {
                let [row] = rows.as_slice() else {
                    panic!("`{}` is Gated with {} rows", f.name, rows.len());
                };
                assert_eq!(row.status, ProofStatus::Certified, "`{}`", f.name);
                assert_eq!(
                    f.body_gate.as_ref().and_then(BodyGate::evidence),
                    Some(&GateEvidence {
                        obligation: row.id,
                        body_digest: module.function_body_digest(f.id).expect("digest"),
                    }),
                    "`{}`: the license cites its row and its body",
                    f.name
                );
                assert!(
                    module
                        .proof_certificates
                        .iter()
                        .any(|c| c.obligation == row.id
                            && c.evidence
                                .clean_cic_kernel_recheck()
                                .is_some_and(|r| r.anchor
                                    == clean_reflect::CLEAN_BACKEND_TV_ANCHOR
                                    && r.binding.is_some() == bound)),
                    "`{}` carries its clean_backend_tv certificate (bound = {bound})",
                    f.name
                );
            } else {
                assert!(rows.is_empty(), "`{}` is unlicensed and unproved", f.name);
                assert_eq!(f.body_gate, Some(BodyGate::Ungated), "`{}`", f.name);
            }
        }
        assert_eq!(
            validate_module_for_codegen(&module).len(),
            1,
            "bound = {bound}: exactly `minus` is refused"
        );
    }
}
