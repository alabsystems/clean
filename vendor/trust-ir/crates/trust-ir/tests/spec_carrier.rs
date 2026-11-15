// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// Wire v46 — the typed spec carrier (roadmap WS4.14, finding F-014's
// carrier / codec half): `SpecVar.sort`, `SpecInvariant.typed`,
// `SpecModule.temporal`, `ProofKind::CleanTheorem`, the spec-variable
// `ClausePlace`s and the obligation `spec` backref. This file pins the FORMAT
// half (version selection, read gates, the four codecs, the text loss, the
// digests) and the trust-ir-side S4 rules of `validate_spec_structure` /
// `link_spec_modules`. The trust-ir-build refusals (function summaries,
// module obligations, the `spec` backref resolution) live in
// `trust-ir-build/tests/spec_carrier_validation.rs`.

#![cfg(all(
    feature = "binary",
    feature = "diff",
    feature = "fmt",
    feature = "parser",
    feature = "serde"
))]

use trust_ir::binary::{
    self, BinaryProjectionError, ModuleBinaryBody, ModuleBinaryOptions, ProjectedModuleBinaryPlan,
    SPEC_CARRIER_FORMAT_VERSION,
};
use trust_ir::proof::{
    ClauseBinding, ClausePlace, ClauseSort, ObligationKind, ProofFormula, ProofObligation,
    ProofStatus, SpecObligationRef, clean_cic_lineage_digest,
};
use trust_ir::{
    KernelCertifiedTheorems, Module, ProofId, ProofKind, SpecEnforcementMode, SpecInvariant,
    SpecLinkOptions, SpecLinkViolation, SpecModule, SpecNonCertificationReason, SpecProof,
    SpecTemporal, SpecVar, TemporalForm, link_spec_modules, link_spec_modules_with_theorems,
    validate_spec_structure,
};

fn header_version(bytes: &[u8]) -> u32 {
    u32::from_le_bytes(bytes[8..12].try_into().unwrap())
}

fn bind(name: &str, sort: ClauseSort, place: ClausePlace) -> (String, ClauseBinding) {
    (name.to_string(), ClauseBinding { sort, place })
}

/// `formula` restated as the one SMT-LIB text `text` (payload and rendering
/// alike): a carrier states one formula, so a fixture that changes it changes
/// both.
fn restated(mut formula: ProofFormula, text: &str) -> ProofFormula {
    formula.payload = text.to_string();
    formula.smtlib = Some(text.to_string());
    formula
}

/// `(<= seq 7)` over state variable 0 — a SINGLE-STATE predicate.
fn bounded() -> ProofFormula {
    let mut f = ProofFormula::smtlib2("(<= seq 7)", "Bool");
    f.bindings = vec![bind(
        "seq",
        ClauseSort::Int,
        ClausePlace::SpecVar { index: 0 },
    )];
    f
}

/// `(= seq' (+ seq 1))` — the two-state relation of the `Push` action.
fn push_relation() -> ProofFormula {
    let mut f = ProofFormula::smtlib2("(= seq_next (+ seq 1))", "Bool");
    f.bindings = vec![
        bind("seq", ClauseSort::Int, ClausePlace::SpecVar { index: 0 }),
        bind(
            "seq_next",
            ClauseSort::Int,
            ClausePlace::SpecVarNext { index: 0 },
        ),
    ];
    f
}

fn full() -> ProofFormula {
    let mut f = ProofFormula::smtlib2("(= seq 7)", "Bool");
    f.bindings = vec![bind(
        "seq",
        ClauseSort::Int,
        ClausePlace::SpecVar { index: 0 },
    )];
    f
}

fn empty_flag() -> ProofFormula {
    let mut f = ProofFormula::smtlib2("(not empty)", "Bool");
    f.bindings = vec![bind(
        "empty",
        ClauseSort::Bool,
        ClausePlace::SpecVar { index: 1 },
    )];
    f
}

/// The typed `ring` machine: every v46 carrier feature at once, all well-formed.
fn typed_ring() -> SpecModule {
    let mut ring = SpecModule::design_only("ring");
    ring.vars = vec![
        SpecVar::new("seq", "0..7").with_sort(ClauseSort::Int),
        SpecVar::new("empty", "Bool").with_sort(ClauseSort::Bool),
    ];
    ring.actions = vec!["Push".to_string(), "Pop".to_string()];
    ring.invariants = vec![SpecInvariant::new("BoundedSeq", "(<= seq 7)").with_typed(bounded())];
    ring.temporal = vec![
        SpecTemporal::new("AlwaysBounded", TemporalForm::Always(bounded())),
        SpecTemporal::new("EventuallyFull", TemporalForm::Eventually(full())),
        SpecTemporal::new(
            "NonEmptyLeadsToFull",
            TemporalForm::LeadsTo(empty_flag(), full()),
        ),
        SpecTemporal::new(
            "PushFair",
            TemporalForm::WeakFair {
                action: "Push".to_string(),
                relation: Some(push_relation()),
            },
        ),
        SpecTemporal::new(
            "PopFair",
            TemporalForm::StrongFair {
                action: "Pop".to_string(),
                relation: None,
            },
        ),
    ];
    ring.proofs = vec![SpecProof {
        machine: "ring".to_string(),
        action: "Push".to_string(),
        proof_name: "ring_push_refines".to_string(),
        kind: ProofKind::CleanTheorem {
            name: "Ring.push_refines".to_string(),
        },
    }];
    ring
}

fn liveness_obligation() -> ProofObligation {
    let mut o = ProofObligation::new(
        ProofId::new(0),
        ObligationKind::Liveness,
        ProofStatus::Pending,
        "eventually the ring is full",
    )
    .with_formula(full());
    o.spec = Some(SpecObligationRef::new("ring", "EventuallyFull"));
    o
}

fn typed_module() -> Module {
    let mut m = Module::new("spec_carrier");
    m.spec_modules.push(typed_ring());
    m.proof_obligations.push(liveness_obligation());
    m
}

/// The same machine with every v46 feature stripped: what a pre-v46 producer
/// could have written.
fn legacy_module() -> Module {
    let mut m = typed_module();
    let ring = &mut m.spec_modules[0];
    for v in &mut ring.vars {
        v.sort = None;
    }
    for inv in &mut ring.invariants {
        inv.typed = None;
    }
    ring.temporal.clear();
    ring.proofs[0].kind = ProofKind::Kani;
    m.proof_obligations[0].spec = None;
    m.proof_obligations[0].formula = Some(ProofFormula::smtlib2("(= seq 7)", "Bool"));
    m
}

fn projected(module: &Module, body: ModuleBinaryBody) -> Result<Vec<u8>, BinaryProjectionError> {
    ProjectedModuleBinaryPlan::try_new(
        module,
        ModuleBinaryOptions {
            body,
            ..Default::default()
        },
    )
    .map(|mut plan| plan.to_vec().expect("to_vec: test fixture"))
}

// ---------------------------------------------------------------------------
// Version selection and the four codecs
// ---------------------------------------------------------------------------

/// Positive: the typed ring round-trips exactly through binary (at v46), JSON
/// and MessagePack; the text codec carries the `clean-theorem` kind and the
/// obligation `spec` backref, marks the `sort`/`typed`/`temporal` carrier
/// `#lossy`, and refuses the marked text.
#[test]
fn typed_ring_round_trips_through_every_codec_at_v46() {
    let module = typed_module();
    assert!(validate_spec_structure(&module.spec_modules).is_empty());

    let bytes = binary::serialize_module(&module).expect("serialize_module: test fixture");
    assert_eq!(header_version(&bytes), SPEC_CARRIER_FORMAT_VERSION);
    assert_eq!(header_version(&bytes), 46);
    let back = binary::deserialize_module(&bytes).unwrap();
    assert_eq!(back, module);
    assert_eq!(
        binary::serialize_module(&back).expect("serialize_module: test fixture"),
        bytes
    );
    assert_eq!(projected(&module, ModuleBinaryBody::Raw).unwrap(), bytes);
    let canonical = projected(&module, ModuleBinaryBody::Canonical).unwrap();
    assert_eq!(
        binary::deserialize_module(&canonical).unwrap().spec_modules,
        module.spec_modules
    );

    let json = serde_json::to_vec(&module).unwrap();
    let from_json: Module = serde_json::from_slice(&json).unwrap();
    assert_eq!(from_json, module);
    let msgpack = rmp_serde::to_vec(&module).unwrap();
    let from_msgpack: Module = rmp_serde::from_slice(&msgpack).unwrap();
    assert_eq!(from_msgpack, module);

    // Text: since roadmap WS4.4 the carrier (`var .. sort`, `invariant ..
    // typed`, `temporal ..`) and the obligation's typed bindings are CARRIED
    // in the shared sort / formula spelling, next to the `clean-theorem` kind
    // and the obligation `spec` backref. (Between v46 and WS4.4 they were the
    // named losses `clause-bindings` / `spec-carrier`, refused as `#lossy`.)
    assert_eq!(trust_ir::format::text_losses(&module), vec![]);
    let text = trust_ir::format::canonical_checked(&module).expect("loss-free since WS4.4");
    assert!(
        text.contains("kind \"clean-theorem\" theorem \"Ring.push_refines\""),
        "{text}"
    );
    assert!(text.contains(" spec \"ring\" \"EventuallyFull\""), "{text}");
    assert!(text.contains("  temporal \"EventuallyFull\" "), "{text}");
    let parsed = trust_ir::parser::parse_module(&text).unwrap();
    assert_eq!(parsed, trust_ir::format::canonicalize(&module));
    assert_eq!(parsed.spec_modules, module.spec_modules);
    assert_eq!(parsed.proof_obligations, module.proof_obligations);
    assert_eq!(trust_ir::format::canonical(&parsed), text);
    // Mutation control: the text with the carrier lines' typed tails deleted
    // parses to the untyped machine the pre-WS4.4 grammar produced, which is
    // NOT the module.
    let untyped: String = text
        .lines()
        .filter(|l| !l.trim_start().starts_with("temporal "))
        .map(|l| format!("{l}\n"))
        .collect();
    let lost = trust_ir::parser::parse_module(&untyped).unwrap();
    assert!(lost.spec_modules[0].temporal.is_empty());
    assert_ne!(lost, parsed);
}

/// Mutation control for version selection: with every v46 feature stripped the
/// same module keeps its pre-v46 header, and each feature ALONE selects v46.
#[test]
fn each_v46_feature_alone_selects_v46_and_none_keeps_the_legacy_header() {
    let legacy = legacy_module();
    let legacy_bytes = binary::serialize_module(&legacy).expect("serialize_module: test fixture");
    assert!(
        header_version(&legacy_bytes) < SPEC_CARRIER_FORMAT_VERSION,
        "got v{}",
        header_version(&legacy_bytes)
    );
    assert_eq!(
        projected(&legacy, ModuleBinaryBody::RawV38).unwrap(),
        legacy_bytes
    );

    type Feature = (&'static str, fn(&mut Module));
    let features: Vec<Feature> = vec![
        ("SpecVar.sort", |m| {
            m.spec_modules[0].vars[0].sort = Some(ClauseSort::Int);
        }),
        ("SpecInvariant.typed", |m| {
            m.spec_modules[0].invariants[0].typed = Some(bounded());
        }),
        ("SpecModule.temporal", |m| {
            m.spec_modules[0]
                .temporal
                .push(SpecTemporal::new("A", TemporalForm::Always(bounded())));
        }),
        ("ProofKind::CleanTheorem", |m| {
            m.spec_modules[0].proofs[0].kind = ProofKind::CleanTheorem {
                name: "Ring.push_refines".to_string(),
            };
        }),
        ("ProofObligation.spec", |m| {
            m.proof_obligations[0].spec = Some(SpecObligationRef::new("ring", "EventuallyFull"));
        }),
        ("ClausePlace::SpecVar in an obligation formula", |m| {
            m.proof_obligations[0].formula = Some(full());
        }),
    ];
    for (name, apply) in features {
        let mut one = legacy.clone();
        apply(&mut one);
        let bytes = binary::serialize_module(&one).expect("serialize_module: test fixture");
        assert_eq!(header_version(&bytes), 46, "{name} must select v46");
        assert_eq!(binary::deserialize_module(&bytes).unwrap(), one, "{name}");
        for body in [ModuleBinaryBody::RawV38, ModuleBinaryBody::CanonicalV38] {
            assert_eq!(
                projected(&one, body).unwrap_err(),
                BinaryProjectionError::SpecCarrierRequiresV46,
                "{name}: a v38 projection must refuse the carrier by name"
            );
        }
    }
}

/// The `version >= 46` read gate is load-bearing both ways: the v46 bytes
/// read under a v45 header must not reproduce the module (the reader would
/// stop before the carrier and misparse the trailing bytes), and the legacy
/// bytes read under a v46 header must not either.
#[test]
fn the_v46_read_gate_is_load_bearing_both_ways() {
    let module = typed_module();
    let mut late = binary::serialize_module(&module).expect("serialize_module: test fixture");
    late[8..12].copy_from_slice(&45u32.to_le_bytes());
    let misread = binary::deserialize_module(&late);
    assert!(
        misread.as_ref().map_or(true, |m| *m != module),
        "v46 bytes under a v45 header must not reproduce the module: {misread:?}"
    );

    let legacy = legacy_module();
    let mut early = binary::serialize_module(&legacy).expect("serialize_module: test fixture");
    early[8..12].copy_from_slice(&46u32.to_le_bytes());
    let misread = binary::deserialize_module(&early);
    assert!(
        misread.as_ref().map_or(true, |m| *m != legacy),
        "legacy bytes under a v46 header must not reproduce the module: {misread:?}"
    );
}

/// A pre-v46 blob decodes with every carrier field NOT RECORDED (`None` /
/// empty) and re-encodes to the same bytes — the additive contract.
#[test]
fn legacy_bytes_decode_with_the_carrier_absent_and_re_encode_identically() {
    let legacy = legacy_module();
    let bytes = binary::serialize_module(&legacy).expect("serialize_module: test fixture");
    let back = binary::deserialize_module(&bytes).unwrap();
    assert_eq!(back, legacy);
    assert!(back.spec_modules[0].vars.iter().all(|v| v.sort.is_none()));
    assert!(
        back.spec_modules[0]
            .invariants
            .iter()
            .all(|i| i.typed.is_none())
    );
    assert!(back.spec_modules[0].temporal.is_empty());
    assert_eq!(back.proof_obligations[0].spec, None);
    assert_eq!(
        binary::serialize_module(&back).expect("serialize_module: test fixture"),
        bytes
    );
}

// ---------------------------------------------------------------------------
// S4 — the typed carrier's structural rules
// ---------------------------------------------------------------------------

fn s4_typed_binding(v: &SpecLinkViolation) -> Option<(&str, &str, &str, &str)> {
    match v {
        SpecLinkViolation::SpecTypedBindingInvalid {
            subject,
            name,
            binding,
            detail,
            ..
        } => Some((subject, name, binding, detail)),
        _ => None,
    }
}

/// Negative twin: `typed` bound to an undeclared variable index.
#[test]
fn typed_invariant_bound_to_an_undeclared_variable_index_is_refused_by_name() {
    let mut ring = typed_ring();
    let mut typed = bounded();
    typed.bindings[0].1.place = ClausePlace::SpecVar { index: 9 };
    ring.invariants[0].typed = Some(typed);
    let violations = validate_spec_structure(&[ring]);
    let hits: Vec<_> = violations.iter().filter_map(s4_typed_binding).collect();
    assert_eq!(hits.len(), 1, "{violations:?}");
    let (subject, name, binding, detail) = hits[0];
    assert_eq!((subject, name, binding), ("invariant", "BoundedSeq", "seq"));
    assert!(
        detail.contains("state variable 9 is out of range: this machine declares 2 variable(s)"),
        "{detail}"
    );
    assert_eq!(violations[0].obligation(), "S4");
    assert!(violations[0].describe().contains("[S4 typed-carrier]"));
}

/// Negative twin: `SpecVarNext` inside an `Always` leaf (a single-state
/// predicate has no successor).
#[test]
fn primed_variable_in_an_always_leaf_is_refused_by_name() {
    let mut ring = typed_ring();
    ring.temporal[0] = SpecTemporal::new("AlwaysBounded", TemporalForm::Always(push_relation()));
    let violations = validate_spec_structure(&[ring]);
    let hits: Vec<_> = violations.iter().filter_map(s4_typed_binding).collect();
    assert_eq!(hits.len(), 1, "{violations:?}");
    let (subject, name, binding, detail) = hits[0];
    assert_eq!(
        (subject, name, binding),
        ("temporal", "AlwaysBounded", "seq_next")
    );
    assert!(
        detail.contains("SpecVarNext 0 names the SUCCESSOR state"),
        "{detail}"
    );

    // Same for the other single-state leaves; the same relation in a fairness
    // action relation is the mutation control and stays accepted.
    for form in [
        TemporalForm::Eventually(push_relation()),
        TemporalForm::LeadsTo(bounded(), push_relation()),
    ] {
        let mut ring = typed_ring();
        ring.temporal[0] = SpecTemporal::new("AlwaysBounded", form);
        assert_eq!(
            validate_spec_structure(&[ring])
                .iter()
                .filter_map(s4_typed_binding)
                .count(),
            1
        );
    }
    let mut ring = typed_ring();
    ring.temporal[0] = SpecTemporal::new(
        "AlwaysBounded",
        TemporalForm::StrongFair {
            action: "Push".to_string(),
            relation: Some(push_relation()),
        },
    );
    assert!(validate_spec_structure(&[ring]).is_empty());
}

/// Negative twin: a place from the function-signature space (`Param`) in a
/// typed carrier is refused — the spec carrier binds only spec variables.
#[test]
fn signature_place_in_a_typed_carrier_is_refused_by_name() {
    let mut ring = typed_ring();
    let mut typed = bounded();
    typed.bindings[0].1.place = ClausePlace::Param { index: 0 };
    ring.invariants[0].typed = Some(typed);
    let violations = validate_spec_structure(&[ring]);
    let hits: Vec<_> = violations.iter().filter_map(s4_typed_binding).collect();
    assert_eq!(hits.len(), 1, "{violations:?}");
    assert!(
        hits[0]
            .3
            .contains("belongs to a function signature, not to a spec machine's state"),
        "{}",
        hits[0].3
    );
}

/// Mutation control (the sort check): a typed invariant whose binding sort
/// disagrees with `SpecVar.sort` is refused; with the sorts agreeing, and with
/// the variable's sort NOT RECORDED, it is accepted — so the refusal is the
/// declared-sort rule, not an over-refusal.
#[test]
fn typed_binding_sort_must_agree_with_the_declared_variable_sort() {
    let mut ring = typed_ring();
    let mut typed = bounded();
    typed.bindings[0].1.sort = ClauseSort::BitVec(64);
    ring.invariants[0].typed = Some(typed.clone());
    let violations = validate_spec_structure(&[ring.clone()]);
    let hits: Vec<_> = violations.iter().filter_map(s4_typed_binding).collect();
    assert_eq!(hits.len(), 1, "{violations:?}");
    assert!(
        hits[0]
            .3
            .contains("at sort BitVec(64), but the variable declares sort Int"),
        "{}",
        hits[0].3
    );

    // Mutant that "skips the sort check" by leaving `sort` unrecorded: the
    // `"0..7"` tag still READS as `Int`, a carried fact, so the `BitVec(64)`
    // binding is refused all the same (`SpecVar::effective_sort`) — the width
    // strip cannot be smuggled through an absent declaration.
    ring.vars[0].sort = None;
    let violations = validate_spec_structure(&[ring.clone()]);
    let hits: Vec<_> = violations.iter().filter_map(s4_typed_binding).collect();
    assert_eq!(hits.len(), 1, "{violations:?}");
    assert!(
        hits[0]
            .3
            .contains("at sort BitVec(64), but the variable declares sort Int"),
        "{}",
        hits[0].3
    );

    // Only a variable with NO readable sort — no `sort` and a tag that does
    // not parse — leaves nothing to compare (S3 refuses that tag under
    // `Linked`; a `DesignOnly` machine certifies nothing).
    ring.vars[0].ty = "Nat".to_string();
    assert_eq!(ring.vars[0].effective_sort(), None);
    let violations = validate_spec_structure(&[ring.clone()]);
    assert!(
        violations
            .iter()
            .filter_map(s4_typed_binding)
            .next()
            .is_none(),
        "{violations:?}"
    );

    ring.vars[0].ty = "0..7".to_string();
    ring.vars[0].sort = Some(ClauseSort::Int);
    ring.invariants[0].typed = Some(bounded());
    assert!(validate_spec_structure(&[ring]).is_empty());
}

/// A declared `SpecVar.sort` that contradicts the `ty` tag is refused in BOTH
/// enforcement modes; an unparseable tag is left to S3 (Linked only).
#[test]
fn declared_variable_sort_must_agree_with_its_type_tag() {
    for mode in [SpecEnforcementMode::DesignOnly, SpecEnforcementMode::Linked] {
        let mut ring = typed_ring();
        ring.enforcement = mode;
        ring.vars[1].sort = Some(ClauseSort::Int); // `Bool` tag
        let violations = validate_spec_structure(&[ring]);
        let mismatches: Vec<_> = violations
            .iter()
            .filter(|v| matches!(v, SpecLinkViolation::SpecVariableSortMismatch { .. }))
            .collect();
        assert!(
            matches!(
                mismatches.as_slice(),
                [SpecLinkViolation::SpecVariableSortMismatch { machine, variable, detail }]
                    if machine == "ring" && variable == "empty"
                        && detail.contains("reads as sort Bool, but the declared sort is Int")
            ),
            "{mode:?}: {violations:?}"
        );
        // The typed leaf that binds `empty` at `Bool` now disagrees with the
        // (wrong) declaration too — the declared sort is what the carrier is
        // checked against, so that is reported as well, not instead.
        assert!(
            violations
                .iter()
                .any(|v| matches!(v, SpecLinkViolation::SpecTypedBindingInvalid { .. })),
            "{mode:?}: {violations:?}"
        );
    }
    let mut ring = typed_ring();
    ring.vars[1].ty = "this is not a type".to_string();
    assert!(
        !validate_spec_structure(&[ring])
            .iter()
            .any(|v| matches!(v, SpecLinkViolation::SpecVariableSortMismatch { .. })),
        "an unparseable tag is S3's finding, not a sort contradiction"
    );
}

/// A fairness property must name a declared action; a temporal name is an
/// identity and may not repeat.
#[test]
fn temporal_properties_are_named_once_and_name_declared_actions() {
    let mut ring = typed_ring();
    ring.temporal[3] = SpecTemporal::new(
        "PushFair",
        TemporalForm::WeakFair {
            action: "Shove".to_string(),
            relation: None,
        },
    );
    let violations = validate_spec_structure(&[ring]);
    assert!(
        violations.iter().any(|v| matches!(
            v,
            SpecLinkViolation::ActionMissing { action, from: "temporal", .. } if action == "Shove"
        )),
        "{violations:?}"
    );

    let mut ring = typed_ring();
    ring.temporal[1].name = "AlwaysBounded".to_string();
    let violations = validate_spec_structure(&[ring]);
    assert!(
        violations.iter().any(|v| matches!(
            v,
            SpecLinkViolation::DuplicateMemberIdentity { member: "temporal", name, .. }
                if name == "AlwaysBounded"
        )),
        "{violations:?}"
    );
}

fn s3_typed_carrier(v: &SpecLinkViolation) -> Option<(&str, &str, &str)> {
    match v {
        SpecLinkViolation::LinkedTypedCarrierUnparsed {
            subject,
            name,
            detail,
            ..
        } => Some((subject, name, detail)),
        _ => None,
    }
}

/// S3 under `Linked`, one layer up from WS1.10: a typed carrier's one
/// SMT-LIB text must READ over its own bindings. The same three twins the string
/// `formula` has — garbage syntax, an unbound free symbol, an ill-sorted
/// comparison — plus a name bound twice, each refused by name with the
/// specific reason; the well-formed ring and every `DesignOnly` machine are
/// untouched. Without this rule a `Linked` machine certifies a typed
/// invariant whose text is garbage beside a well-formed binding list.
#[test]
fn linked_typed_carrier_text_must_read_over_its_own_bindings() {
    let linked = || {
        let mut ring = typed_ring();
        ring.enforcement = SpecEnforcementMode::Linked;
        ring
    };
    let surface = |ring: &SpecModule| {
        let violations = trust_ir::validate_linked_spec_surface(std::slice::from_ref(ring));
        let hits: Vec<(String, String, String)> = violations
            .iter()
            .filter_map(s3_typed_carrier)
            .map(|(s, n, d)| (s.to_string(), n.to_string(), d.to_string()))
            .collect();
        (violations, hits)
    };

    // Positive: every carrier of the typed ring reads.
    let (violations, hits) = surface(&linked());
    assert!(hits.is_empty(), "{violations:?}");

    // Garbage syntax in a typed invariant.
    let mut ring = linked();
    let typed = restated(bounded(), "(<= seq");
    ring.invariants[0].typed = Some(typed);
    let (_, hits) = surface(&ring);
    assert_eq!(hits.len(), 1, "{hits:?}");
    assert_eq!(
        (hits[0].0.as_str(), hits[0].1.as_str()),
        ("invariant", "BoundedSeq")
    );
    assert!(
        hits[0].2.contains("not one quantifier-free SMT-LIB2 term"),
        "{}",
        hits[0].2
    );

    // A free symbol the bindings do not bind — even though the MACHINE
    // declares a variable of that name: bindings are the environment.
    let mut ring = linked();
    let typed = restated(bounded(), "(and (<= seq 7) (not empty))");
    ring.invariants[0].typed = Some(typed);
    let (_, hits) = surface(&ring);
    assert_eq!(hits.len(), 1, "{hits:?}");
    assert!(
        hits[0].2.contains("undeclared variable `empty`"),
        "{}",
        hits[0].2
    );

    // An ill-sorted comparison in a temporal leaf.
    let mut ring = linked();
    let leaf = restated(empty_flag(), "(<= empty 7)");
    ring.temporal[2] =
        SpecTemporal::new("NonEmptyLeadsToFull", TemporalForm::LeadsTo(leaf, full()));
    let (_, hits) = surface(&ring);
    assert_eq!(hits.len(), 1, "{hits:?}");
    assert_eq!(
        (hits[0].0.as_str(), hits[0].1.as_str()),
        ("temporal", "NonEmptyLeadsToFull")
    );
    assert!(hits[0].2.contains("`<=`"), "{}", hits[0].2);

    // A relation whose sort is not Bool.
    let mut ring = linked();
    let relation = restated(push_relation(), "(+ seq 1)");
    ring.temporal[3] = SpecTemporal::new(
        "PushFair",
        TemporalForm::WeakFair {
            action: "Push".to_string(),
            relation: Some(relation),
        },
    );
    let (_, hits) = surface(&ring);
    assert_eq!(hits.len(), 1, "{hits:?}");
    assert!(hits[0].2.contains("Bool"), "{}", hits[0].2);

    // A name bound twice is ambiguous, and a name no term can denote is dead.
    let mut ring = linked();
    let mut typed = bounded();
    typed.bindings.push(bind(
        "seq",
        ClauseSort::Int,
        ClausePlace::SpecVar { index: 0 },
    ));
    ring.invariants[0].typed = Some(typed);
    let (_, hits) = surface(&ring);
    assert!(
        hits.iter().any(|h| h.2.contains("bound more than once")),
        "{hits:?}"
    );
    let mut ring = linked();
    let mut typed = bounded();
    typed.bindings[0].0 = "seq'".to_string();
    ring.invariants[0].typed = Some(typed);
    let (_, hits) = surface(&ring);
    assert!(
        hits.iter()
            .any(|h| h.2.contains("\"seq'\" is not an SMT simple symbol")),
        "{hits:?}"
    );

    // `DesignOnly` strings stay opaque: the garbage twin is not read.
    let mut ring = typed_ring();
    let typed = restated(bounded(), "(<= seq");
    ring.invariants[0].typed = Some(typed);
    let (violations, hits) = surface(&ring);
    assert!(hits.is_empty(), "{violations:?}");

    // The rule is on the certifying path: `spec-link` refuses the garbage twin.
    let mut m = linked_ring_with_clean_theorem();
    let typed = restated(bounded(), "(<= seq");
    m.spec_modules[0].invariants[0].typed = Some(typed);
    let witness = KernelCertifiedTheorems::from_rechecked(["Ring.push_refines".to_string()]);
    let report =
        link_spec_modules_with_theorems(&m, None, Some(&witness), SpecLinkOptions::default())
            .unwrap();
    assert!(!report.is_certifying());
    assert!(
        report
            .violations
            .iter()
            .any(|v| s3_typed_carrier(v).is_some()),
        "{:?}",
        report.violations
    );
    assert_eq!(
        report
            .violations
            .iter()
            .find(|v| s3_typed_carrier(v).is_some())
            .unwrap()
            .obligation(),
        "S3"
    );
}

fn s3_disagrees(v: &SpecLinkViolation) -> Option<(&str, &str)> {
    match v {
        SpecLinkViolation::LinkedTypedCarrierDisagrees {
            invariant, detail, ..
        } => Some((invariant, detail)),
        _ => None,
    }
}

/// S3 under `Linked`: a typed invariant and its string `formula` are ONE
/// predicate. `typed` is documented as "the same predicate as `formula`";
/// before this rule a module could carry `(<= seq 7)` as the string and
/// `(<= seq 8)` as the typed carrier, and each consumer certified against the
/// rendering it happened to read. The comparison is structural over the
/// carrier's bound names renamed to the variables they index, so a carrier
/// that spells the variable differently still agrees; either text that does
/// not read is its own S3 refusal and is named once; `DesignOnly` is opaque.
#[test]
fn linked_typed_carrier_must_be_the_same_predicate_as_its_formula() {
    let linked = || {
        let mut ring = typed_ring();
        ring.enforcement = SpecEnforcementMode::Linked;
        ring
    };
    let surface = |ring: &SpecModule| {
        let violations = trust_ir::validate_linked_spec_surface(std::slice::from_ref(ring));
        let hits: Vec<(String, String)> = violations
            .iter()
            .filter_map(s3_disagrees)
            .map(|(i, d)| (i.to_string(), d.to_string()))
            .collect();
        (violations, hits)
    };

    // Positive: the ring's typed invariant IS its formula.
    let (violations, hits) = surface(&linked());
    assert!(hits.is_empty(), "{violations:?}");

    // A different constant is a different predicate, refused by name.
    let mut ring = linked();
    let typed = restated(bounded(), "(<= seq 8)");
    ring.invariants[0].typed = Some(typed);
    let (violations, hits) = surface(&ring);
    assert_eq!(hits.len(), 1, "{violations:?}");
    assert_eq!(hits[0].0, "BoundedSeq");
    assert!(
        hits[0].1.contains("(<= seq 8)") && hits[0].1.contains("(<= seq 7)"),
        "{}",
        hits[0].1
    );
    let v = violations
        .iter()
        .find(|v| s3_disagrees(v).is_some())
        .unwrap();
    assert_eq!(v.obligation(), "S3");
    assert!(
        v.describe().contains("different predicate"),
        "{}",
        v.describe()
    );

    // Renaming control: a carrier bound as `s` for variable 0 (`seq`) agrees
    // — the binding, not the spelling, says which variable a name denotes.
    let mut ring = linked();
    let mut typed = ProofFormula::smtlib2("(<= s 7)", "Bool");
    typed.bindings = vec![bind(
        "s",
        ClauseSort::Int,
        ClausePlace::SpecVar { index: 0 },
    )];
    ring.invariants[0].typed = Some(typed);
    let (violations, hits) = surface(&ring);
    assert!(hits.is_empty(), "{violations:?}");

    // …and the same renamed carrier over the OTHER variable is refused: the
    // reading over the machine is `(<= empty 7)`, not `(<= seq 7)`.
    let mut ring = linked();
    let mut typed = ProofFormula::smtlib2("(<= s 7)", "Bool");
    typed.bindings = vec![bind(
        "s",
        ClauseSort::Int,
        ClausePlace::SpecVar { index: 1 },
    )];
    ring.vars[1] = SpecVar::new("empty", "Int").with_sort(ClauseSort::Int);
    ring.invariants[0].typed = Some(typed);
    let (violations, hits) = surface(&ring);
    assert_eq!(hits.len(), 1, "{violations:?}");
    assert!(hits[0].1.contains("(<= empty 7)"), "{}", hits[0].1);

    // Whitespace is not content.
    let mut ring = linked();
    let typed = restated(bounded(), "( <=  seq\n7 )");
    ring.invariants[0].typed = Some(typed);
    let (violations, hits) = surface(&ring);
    assert!(hits.is_empty(), "{violations:?}");

    // Garbage in either rendering is that rendering's own refusal — named
    // once, never also as a disagreement.
    let mut ring = linked();
    let typed = restated(bounded(), "(<= seq");
    ring.invariants[0].typed = Some(typed);
    let (violations, hits) = surface(&ring);
    assert!(hits.is_empty(), "{violations:?}");
    assert!(violations.iter().any(|v| s3_typed_carrier(v).is_some()));
    let mut ring = linked();
    ring.invariants[0].formula = "(<= seq".to_string();
    let (violations, hits) = surface(&ring);
    assert!(hits.is_empty(), "{violations:?}");
    assert!(
        violations
            .iter()
            .any(|v| matches!(v, SpecLinkViolation::LinkedFormulaUnparsed { .. }))
    );

    // A carrier with no rendering is read by its `smtlib2` payload — here the
    // same predicate (`a_linked_typed_carrier_is_read_by_its_one_formula_text`
    // has the payload that is not).
    let mut ring = linked();
    let mut typed = bounded();
    typed.smtlib = None;
    ring.invariants[0].typed = Some(typed);
    let (violations, hits) = surface(&ring);
    assert!(hits.is_empty(), "{violations:?}");
    assert!(
        !violations.iter().any(|v| s3_typed_carrier(v).is_some()),
        "{violations:?}"
    );

    // `DesignOnly` strings stay opaque.
    let mut ring = typed_ring();
    let typed = restated(bounded(), "(<= seq 8)");
    ring.invariants[0].typed = Some(typed);
    let (violations, hits) = surface(&ring);
    assert!(hits.is_empty(), "{violations:?}");

    // The rule is on the certifying path: `spec-link` refuses the twin.
    let mut m = linked_ring_with_clean_theorem();
    let typed = restated(bounded(), "(<= seq 8)");
    m.spec_modules[0].invariants[0].typed = Some(typed);
    let witness = KernelCertifiedTheorems::from_rechecked(["Ring.push_refines".to_string()]);
    let report =
        link_spec_modules_with_theorems(&m, None, Some(&witness), SpecLinkOptions::default())
            .unwrap();
    assert!(!report.is_certifying());
    assert!(
        report.violations.iter().any(|v| s3_disagrees(v).is_some()),
        "{:?}",
        report.violations
    );
}

// ---------------------------------------------------------------------------
// `ProofKind::CleanTheorem` resolves only against the kernel re-check witness
// ---------------------------------------------------------------------------

fn linked_ring_with_clean_theorem() -> Module {
    let mut m = typed_module();
    m.spec_modules[0].enforcement = SpecEnforcementMode::Linked;
    // Cover both actions so only the theorem binding decides certification.
    m.spec_modules[0].waivers = vec![
        trust_ir::SpecWaiver {
            machine: "ring".to_string(),
            action: "Push".to_string(),
            reason: "spec_carrier probe".to_string(),
        },
        trust_ir::SpecWaiver {
            machine: "ring".to_string(),
            action: "Pop".to_string(),
            reason: "spec_carrier probe".to_string(),
        },
    ];
    m
}

/// A `CleanTheorem` binding with no witness: a Linked machine is refused by
/// name; under the exploratory option it is non-certifying; a `Certified`
/// status written into the module by hand changes nothing, because the linker
/// never reads it.
#[test]
fn clean_theorem_without_a_kernel_witness_is_unresolved_never_trusted() {
    let mut m = linked_ring_with_clean_theorem();
    // A module that merely CLAIMS the theorem is certified.
    m.proof_obligations[0].status = ProofStatus::Certified;
    let report = link_spec_modules(&m, None, SpecLinkOptions::default()).unwrap();
    assert!(!report.is_certifying());
    assert!(
        matches!(
            report.violations.as_slice(),
            [SpecLinkViolation::CleanTheoremUnresolved { machine, action, theorem, detail }]
                if machine == "ring" && action == "Push" && theorem == "Ring.push_refines"
                    && detail.contains("no kernel re-check witness was supplied")
        ),
        "{:?}",
        report.violations
    );
    assert_eq!(report.violations[0].obligation(), "S4");
    assert!(report.non_certifying_reasons.contains(
        &SpecNonCertificationReason::CleanTheoremUnverified {
            machine: "ring".to_string()
        }
    ));

    let exploratory = link_spec_modules(
        &m,
        None,
        SpecLinkOptions::exploratory_allow_unverified_proofs(),
    )
    .unwrap();
    assert!(exploratory.is_ok(), "{:?}", exploratory.violations);
    assert!(!exploratory.is_certifying());
    assert_eq!(
        exploratory.non_certifying_reasons,
        vec![SpecNonCertificationReason::CleanTheoremUnverified {
            machine: "ring".to_string()
        }]
    );
    assert_eq!(
        exploratory.non_certifying_reasons[0].code(),
        "clean-theorem-unverified"
    );

    // A design-only machine is not asked for a witness (it certifies nothing).
    let mut design = m.clone();
    design.spec_modules[0].enforcement = SpecEnforcementMode::DesignOnly;
    let report = link_spec_modules(&design, None, SpecLinkOptions::default()).unwrap();
    assert!(report.is_ok(), "{:?}", report.violations);
    assert_eq!(
        report.non_certifying_reasons,
        vec![SpecNonCertificationReason::DesignOnlyMachine {
            machine: "ring".to_string()
        }]
    );
}

/// With a witness, the binding resolves exactly when the witness names the
/// theorem; a witness naming another theorem is a refusal with the same
/// named reason. No manifest is demanded for a Clean-theorem-only machine.
#[test]
fn clean_theorem_resolves_only_against_the_witness() {
    let m = linked_ring_with_clean_theorem();
    let witness = KernelCertifiedTheorems::from_rechecked(["Ring.push_refines".to_string()]);
    let report =
        link_spec_modules_with_theorems(&m, None, Some(&witness), SpecLinkOptions::default())
            .unwrap();
    assert!(report.is_certifying(), "{report:?}");

    let other = KernelCertifiedTheorems::from_rechecked(["Ring.pop_refines".to_string()]);
    let report =
        link_spec_modules_with_theorems(&m, None, Some(&other), SpecLinkOptions::default())
            .unwrap();
    assert!(
        matches!(
            report.violations.as_slice(),
            [SpecLinkViolation::CleanTheoremUnresolved { theorem, detail, .. }]
                if theorem == "Ring.push_refines"
                    && detail == "the kernel re-check witness does not establish it"
        ),
        "{:?}",
        report.violations
    );
    assert!(!report.is_certifying());

    // A blank theorem name is the S0 blank refusal, witness or not.
    let mut blank = m.clone();
    blank.spec_modules[0].proofs[0].kind = ProofKind::CleanTheorem {
        name: "  ".to_string(),
    };
    let report =
        link_spec_modules_with_theorems(&blank, None, Some(&witness), SpecLinkOptions::default())
            .unwrap();
    assert!(
        report.violations.iter().any(|v| matches!(
            v,
            SpecLinkViolation::BlankSemanticValue {
                subject: "proof",
                field: "clean theorem",
                ..
            }
        )),
        "{:?}",
        report.violations
    );
}

// ---------------------------------------------------------------------------
// Digests: the `spec` backref is part of what an obligation MEANS
// ---------------------------------------------------------------------------

/// Two obligations differing only in `spec` have different content digests
/// (`trust_ir.obligation.digest.v7`, now v8) and different CleanCic lineage digests
/// (`…lineage.v7`, presence-gated); an obligation with no backref keeps the
/// pre-v46 lineage domain, so every existing certificate still replays.
#[test]
fn obligations_differing_only_in_spec_have_different_digests() {
    let a = typed_module();
    let mut b = a.clone();
    b.proof_obligations[0].spec = Some(SpecObligationRef::new("ring", "AlwaysBounded"));
    let mut none = a.clone();
    none.proof_obligations[0].spec = None;

    let da = a.obligation_digest(ProofId::new(0)).unwrap();
    let db = b.obligation_digest(ProofId::new(0)).unwrap();
    let dn = none.obligation_digest(ProofId::new(0)).unwrap();
    assert_ne!(da, db, "which temporal property is discharged is identity");
    assert_ne!(da, dn, "backref presence is identity");

    let la = clean_cic_lineage_digest(&a.proof_obligations[0]);
    let lb = clean_cic_lineage_digest(&b.proof_obligations[0]);
    let ln = clean_cic_lineage_digest(&none.proof_obligations[0]);
    assert_ne!(la, lb);
    assert_ne!(la, ln);

    // The presence gate: a backref-free obligation hashes under the original
    // v5 / v6 domains with an unchanged preimage, so every certificate minted
    // before v46 still replays. The byte-level control is the conformance
    // corpus: the `lean_library_envelope` and kernel-certified goldens carry
    // CleanCic lineages and are byte-identical across this version.
    assert_eq!(
        ln,
        clean_cic_lineage_digest(&none.proof_obligations[0].clone())
    );
}

/// Ported GAP row `b7.spec.temporal_obligation_is_untyped` (format half): a
/// `Liveness` obligation can now carry a typed first-order formula over the
/// machine's state variables AND name the temporal property it discharges.
#[test]
fn b7_spec_temporal_obligation_is_typed_and_backreferenced() {
    let m = typed_module();
    let o = &m.proof_obligations[0];
    assert_eq!(o.kind, ObligationKind::Liveness);
    let formula = o.formula.as_ref().unwrap();
    assert_eq!(
        formula.bindings,
        vec![bind(
            "seq",
            ClauseSort::Int,
            ClausePlace::SpecVar { index: 0 }
        )]
    );
    assert_eq!(
        o.spec,
        Some(SpecObligationRef::new("ring", "EventuallyFull"))
    );
    let property = m.spec_modules[0]
        .temporal
        .iter()
        .find(|t| t.name == "EventuallyFull")
        .unwrap();
    assert_eq!(property.form, TemporalForm::Eventually(full()));
    assert_eq!(property.form.tag(), "eventually");
}

// ---------------------------------------------------------------------------
// Adversarial review (WS4.14): inputs the carrier must refuse or must NOT
// refuse, written against the implementation rather than from its design.
// ---------------------------------------------------------------------------

/// ADVERSARIAL — a bound name that SPELLS a different state variable.
///
/// The bindings are the carrier's whole environment, so the binding wins and
/// `(not seq)` "means" `empty`. But the agreement check reads the carrier's
/// text beside the machine's `vars`, and so does any human or consumer: there
/// `seq` is state variable 0, an `Int`. One name with two readings is exactly
/// the hazard `LinkedTypedCarrierDisagrees` refuses one layer up, so it is
/// refused at the binding, in BOTH enforcement modes.
#[test]
fn a_bound_name_may_not_spell_a_different_state_variable() {
    for mode in [SpecEnforcementMode::DesignOnly, SpecEnforcementMode::Linked] {
        let mut ring = typed_ring();
        ring.enforcement = mode;
        // `empty` is variable 1 and IS a `Bool`, so every sort agrees and the
        // index is in range: the shadow is the only thing wrong.
        let mut typed = ProofFormula::smtlib2("(not seq)", "Bool");
        typed.bindings = vec![bind(
            "seq",
            ClauseSort::Bool,
            ClausePlace::SpecVar { index: 1 },
        )];
        ring.invariants = vec![SpecInvariant::new("NotEmpty", "(not empty)").with_typed(typed)];
        let violations = validate_spec_structure(&[ring.clone()]);
        let hits: Vec<_> = violations.iter().filter_map(s4_typed_binding).collect();
        assert_eq!(hits.len(), 1, "{mode:?}: {violations:?}");
        assert_eq!(hits[0].0, "invariant");
        assert_eq!(hits[0].2, "seq");
        assert!(
            hits[0].3.contains("is the name of state variable 0")
                && hits[0].3.contains("indexes state variable 1"),
            "{}",
            hits[0].3
        );

        // Mutation control: binding a name to the variable it SPELLS is the
        // natural spelling and stays legal — the rule refuses the mismatch,
        // not the coincidence.
        let mut honest = ProofFormula::smtlib2("(not empty)", "Bool");
        honest.bindings = vec![bind(
            "empty",
            ClauseSort::Bool,
            ClausePlace::SpecVar { index: 1 },
        )];
        ring.invariants = vec![SpecInvariant::new("NotEmpty", "(not empty)").with_typed(honest)];
        let violations = validate_spec_structure(&[ring.clone()]);
        assert!(
            violations
                .iter()
                .filter_map(s4_typed_binding)
                .next()
                .is_none(),
            "{mode:?}: an honest binding must not be refused: {violations:?}"
        );

        // …and so does a name that spells NO state variable at all.
        let mut fresh = ProofFormula::smtlib2("(not e)", "Bool");
        fresh.bindings = vec![bind(
            "e",
            ClauseSort::Bool,
            ClausePlace::SpecVar { index: 1 },
        )];
        ring.invariants = vec![SpecInvariant::new("NotEmpty", "(not e)").with_typed(fresh)];
        let violations = validate_spec_structure(&[ring]);
        assert!(
            violations
                .iter()
                .filter_map(s4_typed_binding)
                .next()
                .is_none(),
            "{mode:?}: {violations:?}"
        );
    }
}

/// ADVERSARIAL — two bound names that index ONE state variable.
///
/// The renaming that reads a carrier over the machine is SIMULTANEOUS and
/// per-atom, so an aliased pair collapses to one variable and the comparison
/// stays structural: it must accept the twin that really is the same
/// predicate and refuse the one that is not.
#[test]
fn aliased_bindings_to_one_state_variable_compare_structurally() {
    let alias = |text: &str| {
        let mut f = ProofFormula::smtlib2(text, "Bool");
        f.bindings = vec![
            bind("a", ClauseSort::Int, ClausePlace::SpecVar { index: 0 }),
            bind("b", ClauseSort::Int, ClausePlace::SpecVar { index: 0 }),
        ];
        f
    };
    let mut ring = typed_ring();
    ring.enforcement = SpecEnforcementMode::Linked;
    ring.temporal.clear();
    ring.proofs.clear();
    ring.invariants =
        vec![SpecInvariant::new("Refl", "(<= seq seq)").with_typed(alias("(<= a b)"))];
    assert!(
        trust_ir::validate_linked_spec_surface(&[ring.clone()]).is_empty(),
        "an aliased pair that really is the same predicate must not be refused"
    );

    // The twin: the same aliased bindings over a text that is NOT the
    // invariant's predicate.
    ring.invariants = vec![SpecInvariant::new("Refl", "(<= seq seq)").with_typed(alias("(< a b)"))];
    let violations = trust_ir::validate_linked_spec_surface(&[ring]);
    assert!(
        violations.iter().any(|v| matches!(
            v,
            SpecLinkViolation::LinkedTypedCarrierDisagrees { invariant, .. } if invariant == "Refl"
        )),
        "{violations:?}"
    );
}

/// ADVERSARIAL — a legitimate machine must NOT be refused. A `sort` that was
/// never recorded falls back to the tag the variable really carries, and every
/// surface tag the spec surface spells is accepted at the sort it parses to.
#[test]
fn an_unrecorded_sort_falls_back_to_the_tag_without_over_refusing() {
    for (tag, sort) in [
        ("Bool", ClauseSort::Bool),
        ("Int", ClauseSort::Int),
        ("0..7", ClauseSort::Int),
        ("BitVec(8)", ClauseSort::BitVec(8)),
    ] {
        let mut ring = SpecModule::design_only("m");
        ring.vars = vec![SpecVar::new("x", tag)];
        let mut typed = ProofFormula::smtlib2("(= x x)", "Bool");
        typed.bindings = vec![bind("x", sort.clone(), ClausePlace::SpecVar { index: 0 })];
        ring.invariants = vec![SpecInvariant::new("Refl", "(= x x)").with_typed(typed)];
        assert_eq!(ring.vars[0].effective_sort(), Some(sort.clone()));
        assert!(
            validate_spec_structure(&[ring.clone()]).is_empty(),
            "tag {tag:?} at sort {sort:?} must be accepted with no declared sort"
        );
        // And the same machine with the sort ALSO recorded is identical.
        ring.vars[0].sort = Some(sort.clone());
        assert!(
            validate_spec_structure(&[ring]).is_empty(),
            "tag {tag:?} with sort {sort:?} recorded must be accepted"
        );
    }
}

/// ONE FORMULA in the spec lane (the R10 verifier's residual on 794601e2). S3
/// read a typed carrier's `smtlib` RENDERING whatever its schema and skipped a
/// carrier with none — the pattern r5 removed from contract grounding — so a
/// Linked machine whose string invariant is `(<= seq 7)` CERTIFIED beside a
/// carrier stating another predicate: an `smtlib2` payload `(<= seq 8)` with
/// no rendering, the same payload beside the agreeing rendering `(<= seq 7)`,
/// an opaque payload beside that rendering, and a temporal leaf doing either.
/// S3 now reads only the carrier's one SMT-LIB text
/// (`ProofFormula::smtlib_text`) and refuses a carrier that states none or
/// two. Controls: the one-text spellings (identical rendering, payload only)
/// still certify.
#[test]
fn a_linked_typed_carrier_is_read_by_its_one_formula_text() {
    let witness = KernelCertifiedTheorems::from_rechecked(["Ring.push_refines".to_string()]);
    let link = |m: &Module| {
        link_spec_modules_with_theorems(m, None, Some(&witness), SpecLinkOptions::default())
            .unwrap()
    };
    let with_invariant = |typed: ProofFormula| {
        let mut m = linked_ring_with_clean_theorem();
        m.spec_modules[0].invariants[0].typed = Some(typed);
        m
    };
    let with_always = |leaf: ProofFormula| {
        let mut m = linked_ring_with_clean_theorem();
        m.spec_modules[0].temporal[0] =
            SpecTemporal::new("AlwaysBounded", TemporalForm::Always(leaf));
        m
    };
    let mut other_payload_only = bounded();
    other_payload_only.payload = "(<= seq 8)".to_string();
    other_payload_only.smtlib = None;
    let mut two_texts = bounded();
    two_texts.payload = "(<= seq 8)".to_string();
    let mut opaque = bounded();
    opaque.schema = "trust-types.Formula@1".to_string();
    opaque.payload = "{\"le\":[\"seq\",8]}".to_string();
    let mut payload_only = bounded();
    payload_only.smtlib = None;

    let disagrees = |v: &SpecLinkViolation| s3_disagrees(v).is_some();
    let two = |v: &SpecLinkViolation| {
        s3_typed_carrier(v).is_some_and(|(_, _, d)| d.contains("two SMT-LIB texts"))
    };
    let none = |v: &SpecLinkViolation| {
        s3_typed_carrier(v).is_some_and(|(_, _, d)| d.contains("no SMT-LIB text"))
    };
    type Expect = Option<fn(&SpecLinkViolation) -> bool>;
    let cases: [(&str, Module, Expect); 8] = [
        (
            "invariant: smtlib2 payload (<= seq 8), no rendering",
            with_invariant(other_payload_only),
            Some(disagrees),
        ),
        (
            "invariant: smtlib2 payload (<= seq 8), rendering (<= seq 7)",
            with_invariant(two_texts.clone()),
            Some(two),
        ),
        (
            "invariant: opaque payload, rendering (<= seq 7)",
            with_invariant(opaque.clone()),
            Some(none),
        ),
        (
            "temporal: smtlib2 payload (<= seq 8), rendering (<= seq 7)",
            with_always(two_texts),
            Some(two),
        ),
        (
            "temporal: opaque payload, rendering (<= seq 7)",
            with_always(opaque),
            Some(none),
        ),
        (
            "control: the ring as built",
            linked_ring_with_clean_theorem(),
            None,
        ),
        (
            "control: invariant payload (<= seq 7), no rendering",
            with_invariant(payload_only.clone()),
            None,
        ),
        (
            "control: temporal payload (<= seq 7), no rendering",
            with_always(payload_only),
            None,
        ),
    ];
    let mut wrong = Vec::new();
    for (case, module, refusal) in cases {
        let report = link(&module);
        let right = match refusal {
            Some(expected) => !report.is_certifying() && report.violations.iter().any(expected),
            None => report.is_certifying(),
        };
        if !right {
            wrong.push(format!(
                "{case}: certifying {}, violations {:?}",
                report.is_certifying(),
                report.violations
            ));
        }
    }
    assert!(
        wrong.is_empty(),
        "a typed carrier read by a text it does not state:\n{}",
        wrong.join("\n")
    );
}

/// The one-formula rule on EVERY Linked temporal form (the r10 reverifier's
/// probe, measured certifying on d46593b1 and refused since 031ddd64): the
/// SECOND leaf of a `LeadsTo`, an `Eventually` leaf, and the two-state
/// RELATION of both fairness forms, each carrying a text the machine does not
/// state beside a rendering that reads.
#[test]
fn every_linked_temporal_leaf_is_read_by_its_one_text() {
    let witness = KernelCertifiedTheorems::from_rechecked(["Ring.push_refines".to_string()]);
    let link = |m: &Module| {
        link_spec_modules_with_theorems(m, None, Some(&witness), SpecLinkOptions::default())
            .unwrap()
    };
    let with_temporal = |index: usize, form: TemporalForm| {
        let mut m = linked_ring_with_clean_theorem();
        let name = m.spec_modules[0].temporal[index].name.clone();
        m.spec_modules[0].temporal[index] = SpecTemporal::new(name, form);
        m
    };
    let opaque = |mut f: ProofFormula| {
        f.schema = "trust-types.Formula@1".to_string();
        f.payload = "{\"opaque\":true}".to_string();
        f
    };
    let two_texts = |mut f: ProofFormula, payload: &str| {
        f.payload = payload.to_string();
        f
    };
    let cases: Vec<(&str, Module)> = vec![
        (
            "LeadsTo second leaf: opaque payload, rendering (= seq 7)",
            with_temporal(2, TemporalForm::LeadsTo(empty_flag(), opaque(full()))),
        ),
        (
            "LeadsTo second leaf: smtlib2 payload (= seq 0), rendering (= seq 7)",
            with_temporal(
                2,
                TemporalForm::LeadsTo(empty_flag(), two_texts(full(), "(= seq 0)")),
            ),
        ),
        (
            "Eventually: smtlib2 payload (= seq 0), rendering (= seq 7)",
            with_temporal(1, TemporalForm::Eventually(two_texts(full(), "(= seq 0)"))),
        ),
        (
            "WeakFair relation: smtlib2 payload (= seq_next seq), rendering (= seq_next (+ seq 1))",
            with_temporal(
                3,
                TemporalForm::WeakFair {
                    action: "Push".to_string(),
                    relation: Some(two_texts(push_relation(), "(= seq_next seq)")),
                },
            ),
        ),
        (
            "StrongFair relation: opaque payload, rendering (= seq_next (+ seq 1))",
            with_temporal(
                4,
                TemporalForm::StrongFair {
                    action: "Pop".to_string(),
                    relation: Some(opaque(push_relation())),
                },
            ),
        ),
    ];
    let mut wrong = Vec::new();
    for (case, module) in cases {
        let report = link(&module);
        let refused = !report.is_certifying()
            && report
                .violations
                .iter()
                .any(|v| s3_typed_carrier(v).is_some());
        if !refused {
            wrong.push(format!(
                "{case}: certifying {}, violations {:?}",
                report.is_certifying(),
                report.violations
            ));
        }
    }
    assert!(link(&linked_ring_with_clean_theorem()).is_certifying());
    assert!(
        wrong.is_empty(),
        "a Linked temporal leaf read by a text it does not state:\n{}",
        wrong.join("\n")
    );
}

/// S3 decides a Linked carrier's schema over EVERY schema trust-ir owns
/// (`OwnedFormulaSchema`, no wildcard): only an `smtlib2` payload is a
/// predicate over the machine's state. A `trust-ir.Pred@1` citation is a
/// refinement predicate over one value `self`, and a claim schema states no
/// predicate, so each is refused on the certifying path by its own reason
/// even beside a rendering that IS the invariant — the rendering is never
/// read as the formula. The carrier's text is read by trust-ir's one
/// SMT-LIB2 reader: a `'` or a non-SMT-LIB character is refused.
#[test]
fn a_linked_carrier_states_its_predicate_only_as_smtlib2_source() {
    use trust_ir::proof::{BVBLAST_GOAL_SCHEMA, LINEAGE_TRANSFORM_BINDING_SCHEMA};
    let witness = KernelCertifiedTheorems::from_rechecked(["Ring.push_refines".to_string()]);
    let link = |m: &Module| {
        link_spec_modules_with_theorems(m, None, Some(&witness), SpecLinkOptions::default())
            .unwrap()
    };
    let in_schema = |schema: &str, payload: String| {
        let mut f = bounded();
        f.schema = schema.to_string();
        f.payload = payload;
        f
    };
    let cases = [
        (
            "trust-ir.Pred@1 citation beside the invariant's rendering",
            in_schema("trust-ir.Pred@1", "pred.0".to_string()),
            "refinement predicate over one value `self`",
        ),
        (
            "bit-blast goal claim beside the invariant's rendering",
            in_schema(
                BVBLAST_GOAL_SCHEMA,
                format!("site=0:0:0\nkind=BoundsCheck\ngoal={}", "a".repeat(64)),
            ),
            "claim schema",
        ),
        (
            "SAT-refutation claim beside the invariant's rendering",
            in_schema(
                "trust-ir.satres.cnf.v2",
                "rule=r\ncnf=sha256:00".to_string(),
            ),
            "claim schema",
        ),
        (
            "lineage binding beside the invariant's rendering",
            in_schema(
                LINEAGE_TRANSFORM_BINDING_SCHEMA,
                format!("sha256:{}", "ab".repeat(32)),
            ),
            "claim schema",
        ),
        (
            "an unowned schema beside the invariant's rendering",
            in_schema("trust-types.Formula@1", "{\"le\":[\"seq\",7]}".to_string()),
            "does not own schema",
        ),
        (
            "smtlib2 spaced with U+3000",
            restated(bounded(), "(<=\u{3000}seq 7)"),
            "neither printable ASCII",
        ),
        (
            "smtlib2 naming a primed symbol",
            restated(bounded(), "(<= seq' 7)"),
            "no SMT-LIB2 token",
        ),
    ];
    let mut wrong = Vec::new();
    for (case, typed, reason) in cases {
        let mut module = linked_ring_with_clean_theorem();
        module.spec_modules[0].invariants[0].typed = Some(typed);
        let report = link(&module);
        let refused = !report.is_certifying()
            && report
                .violations
                .iter()
                .filter_map(s3_typed_carrier)
                .any(|(_, _, detail)| detail.contains(reason));
        if !refused {
            wrong.push(format!(
                "{case}: certifying {}, violations {:?}",
                report.is_certifying(),
                report.violations
            ));
        }
    }
    assert!(
        wrong.is_empty(),
        "a Linked carrier read outside the one-formula rule:\n{}",
        wrong.join("\n")
    );
}
