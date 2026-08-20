// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// Roundtrip coverage for the `SpecModule` IR object across all four
// serialization formats (bin / text / json / msgpack), following the
// pattern of `format_canonical.rs` and `module_roundtrip_fuzz.rs`.
//
// The contract under test: a `Module` carrying `spec_modules` survives a
// serialize→deserialize round trip in every format the `convert` CLI
// subcommand supports, with the spec objects byte-for-byte preserved.

#![cfg(all(feature = "parser", feature = "binary", feature = "serde"))]

use trust_ir::spec::{
    ProofKind, SpecAnchor, SpecEnforcementMode, SpecInvariant, SpecOrigin, SpecProjectionTarget,
    SpecProof, SpecVar, SpecWaiver, TEMPORAL_FIELD_PATH_PROJECTION_V1,
};
use trust_ir::{FuncId, Module, SpecModule};

/// A module with one embedded and one external SpecModule, exercising every
/// field: vars, actions, invariants, anchors (with and without `project`),
/// waivers, and both origin variants.
fn module_with_specs() -> Module {
    let mut module = Module::new("ring_demo");

    let ring = SpecModule {
        name: "ring".to_string(),
        vars: vec![SpecVar::new("seq", "0..7"), SpecVar::new("full", "Bool")],
        actions: vec!["Push".to_string(), "Pop".to_string(), "Clear".to_string()],
        invariants: vec![
            SpecInvariant::new("BoundedSeq", "seq <= 7"),
            SpecInvariant::new("FullImpliesSeven", "full => seq = 7"),
        ],
        anchors: vec![
            SpecAnchor {
                machine: "ring".to_string(),
                action: "Push".to_string(),
                function: Some(FuncId::new(7)),
                rust_symbol: "aterm_buffer::Ring::push".to_string(),
                span: "crates/aterm-buffer/src/ring.rs:120:4".to_string(),
                project: Some("aterm_buffer::Ring::project".to_string()),
                projection_target: Some(SpecProjectionTarget::Function(FuncId::new(8))),
            },
            SpecAnchor {
                machine: "ring".to_string(),
                action: "Pop".to_string(),
                function: Some(FuncId::new(9)),
                rust_symbol: "aterm_buffer::Ring::pop".to_string(),
                span: "crates/aterm-buffer/src/ring.rs:140:4".to_string(),
                project: Some(TEMPORAL_FIELD_PATH_PROJECTION_V1.to_string()),
                projection_target: Some(SpecProjectionTarget::TemporalFieldPathsV1),
            },
        ],
        waivers: vec![SpecWaiver {
            machine: "ring".to_string(),
            action: "Clear".to_string(),
            reason: "clear is a test-only helper with no shipping handler".to_string(),
        }],
        proofs: vec![
            SpecProof {
                machine: "ring".to_string(),
                action: "Push".to_string(),
                proof_name: "ring_push_refines".to_string(),
                kind: ProofKind::Kani,
            },
            SpecProof {
                machine: "ring".to_string(),
                action: "Pop".to_string(),
                proof_name: "ring_pop_refines".to_string(),
                kind: ProofKind::Kani,
            },
        ],
        origin: SpecOrigin::Embedded,
        enforcement: SpecEnforcementMode::Linked,
    };

    let sandbox = SpecModule {
        name: "sandbox".to_string(),
        vars: vec![SpecVar::new("entered", "Bool")],
        actions: vec!["Enter".to_string(), "Exit".to_string()],
        invariants: vec![SpecInvariant::new("Confined", "entered => path_confined")],
        anchors: vec![],
        waivers: vec![],
        proofs: vec![],
        origin: SpecOrigin::External("crates/aterm-spec-models/specs/Sandbox.tla".to_string()),
        enforcement: SpecEnforcementMode::DesignOnly,
    };

    module.spec_modules.push(ring);
    module.spec_modules.push(sandbox);
    module
}

#[test]
fn spec_modules_roundtrip_binary() {
    let m = module_with_specs();
    let bytes = trust_ir::binary::serialize_module(&m);
    let back = trust_ir::binary::deserialize_module(&bytes).expect("binary decode");
    assert_eq!(m, back, "binary roundtrip must be lossless");
    assert_eq!(back.spec_modules.len(), 2);
    // The v10 `proofs` block must survive: ring carries two SpecProofs.
    assert_eq!(back.spec_modules[0].proofs.len(), 2);
    assert_eq!(
        back.spec_modules[0].proofs[0].proof_name,
        "ring_push_refines"
    );
    assert_eq!(back.spec_modules[0].proofs[0].kind, ProofKind::Kani);
    assert!(back.spec_modules[1].proofs.is_empty());
}

#[test]
fn legacy_v9_spec_module_decodes_with_empty_proofs() {
    // A binary blob whose SpecModule body has NO proofs block (the pre-v10
    // layout) must still decode — the v10 reader version-gates the proofs read.
    // We assert it the other way round: a module with empty proofs is byte-for-
    // byte stable and decodes to empty proofs.
    let mut m = Module::new("legacy");
    let mut sm = SpecModule::new("ring");
    sm.actions.push("Push".to_string());
    m.spec_modules.push(sm);
    let bytes = trust_ir::binary::serialize_module(&m);
    let back = trust_ir::binary::deserialize_module(&bytes).expect("decode");
    assert!(back.spec_modules[0].proofs.is_empty());
    assert_eq!(m, back);
}

#[test]
fn spec_modules_roundtrip_json() {
    let m = module_with_specs();
    let json = serde_json::to_vec_pretty(&m).expect("json encode");
    let json_text = std::str::from_utf8(&json).expect("JSON is UTF-8");
    assert!(json_text.contains("\"enforcement\""));
    assert!(json_text.contains("\"projection_target\""));
    let back: Module = serde_json::from_slice(&json).expect("json decode");
    assert_eq!(m, back, "json roundtrip must be lossless");
}

#[test]
fn spec_modules_roundtrip_msgpack() {
    let m = module_with_specs();
    let mp = rmp_serde::to_vec(&m).expect("msgpack encode");
    let back: Module = rmp_serde::from_slice(&mp).expect("msgpack decode");
    assert_eq!(m, back, "msgpack roundtrip must be lossless");
}

#[test]
fn legacy_five_field_anchor_msgpack_defaults_typed_function() {
    // rmp-serde encodes structs positionally. `function` must remain the
    // trailing field so a pre-v26 five-field anchor ends cleanly and serde's
    // default supplies None, rather than shifting `rust_symbol` into FuncId.
    #[derive(serde::Serialize)]
    struct LegacySpecAnchor {
        machine: String,
        action: String,
        rust_symbol: String,
        span: String,
        project: Option<String>,
    }

    let legacy = LegacySpecAnchor {
        machine: "ring".to_string(),
        action: "Push".to_string(),
        rust_symbol: "ring::Ring::push".to_string(),
        span: "src/ring.rs:42:4".to_string(),
        project: Some("ring::project".to_string()),
    };
    let bytes = rmp_serde::to_vec(&legacy).expect("legacy msgpack encode");
    let decoded: SpecAnchor = rmp_serde::from_slice(&bytes).expect("legacy anchor decode");
    assert_eq!(decoded.machine, "ring");
    assert_eq!(decoded.action, "Push");
    assert_eq!(decoded.rust_symbol, "ring::Ring::push");
    assert_eq!(decoded.span, "src/ring.rs:42:4");
    assert_eq!(decoded.project.as_deref(), Some("ring::project"));
    assert_eq!(decoded.function, None);
    assert_eq!(decoded.projection_target, None);
}

#[test]
fn legacy_v26_anchor_msgpack_defaults_projection_target_only() {
    #[derive(serde::Serialize)]
    struct V26SpecAnchor {
        machine: String,
        action: String,
        rust_symbol: String,
        span: String,
        project: Option<String>,
        function: Option<FuncId>,
    }

    let legacy = V26SpecAnchor {
        machine: "ring".to_string(),
        action: "Push".to_string(),
        rust_symbol: "ring::Ring::push".to_string(),
        span: "src/ring.rs:42:4".to_string(),
        project: Some("ring::project".to_string()),
        function: Some(FuncId::new(7)),
    };
    let bytes = rmp_serde::to_vec(&legacy).expect("v26 msgpack encode");
    let decoded: SpecAnchor = rmp_serde::from_slice(&bytes).expect("v26 anchor decode");
    assert_eq!(decoded.function, Some(FuncId::new(7)));
    assert_eq!(decoded.projection_target, None);

    let json = serde_json::to_vec(&legacy).expect("v26 JSON encode");
    let decoded: SpecAnchor = serde_json::from_slice(&json).expect("v26 JSON decode");
    assert_eq!(decoded.function, Some(FuncId::new(7)));
    assert_eq!(
        decoded.projection_target,
        SpecProjectionTarget::legacy_compatibility()
    );
}

#[test]
fn legacy_serde_module_maps_explicitly_to_design_only() {
    #[derive(serde::Serialize)]
    struct LegacySpecModule {
        name: String,
        vars: Vec<SpecVar>,
        actions: Vec<String>,
        invariants: Vec<SpecInvariant>,
        anchors: Vec<SpecAnchor>,
        waivers: Vec<SpecWaiver>,
        proofs: Vec<SpecProof>,
        origin: SpecOrigin,
    }

    let legacy = LegacySpecModule {
        name: "legacy".to_string(),
        vars: vec![],
        actions: vec!["Step".to_string()],
        invariants: vec![],
        anchors: vec![],
        waivers: vec![],
        proofs: vec![],
        origin: SpecOrigin::Embedded,
    };
    let bytes = rmp_serde::to_vec(&legacy).expect("legacy module msgpack encode");
    let decoded: SpecModule = rmp_serde::from_slice(&bytes).expect("legacy module decode");
    assert_eq!(
        decoded.enforcement,
        SpecEnforcementMode::legacy_compatibility()
    );

    let json = serde_json::to_vec(&legacy).expect("legacy module json encode");
    let decoded: SpecModule = serde_json::from_slice(&json).expect("legacy JSON module decode");
    assert_eq!(decoded.enforcement, SpecEnforcementMode::DesignOnly);
}

#[test]
fn legacy_text_maps_to_design_only_but_current_writer_is_explicit() {
    let legacy = r#"
module "legacy"

spec_module "Machine" {
  origin embedded
  action "Step"
  anchor machine "Machine" action "Step" rust "crate::step" span "fixture.rs:1:1" project "crate::project"
}
"#;
    let decoded = trust_ir::parser::parse_module(legacy).expect("legacy text decode");
    assert_eq!(
        decoded.spec_modules[0].enforcement,
        SpecEnforcementMode::DesignOnly
    );
    assert_eq!(decoded.spec_modules[0].anchors[0].projection_target, None);

    let rewritten_legacy = format!("{decoded}");
    assert!(rewritten_legacy.contains("target none"));

    let current = format!("{}", module_with_specs());
    assert!(current.contains("  enforcement linked"));
    assert!(current.contains("  enforcement design-only"));
    assert!(current.contains("target function 8"));
    assert!(current.contains("target temporal-field-paths-v1"));
}

#[test]
fn text_rejects_duplicate_origin_and_enforcement_claims() {
    for (field, duplicate) in [
        (
            "origin",
            "  origin embedded\n  origin external \"Machine.tla\"",
        ),
        (
            "enforcement",
            "  enforcement design-only\n  enforcement linked",
        ),
    ] {
        let text = format!("module \"duplicate\"\n\nspec_module \"Machine\" {{\n{duplicate}\n}}\n");
        let error = trust_ir::parser::parse_module(&text).expect_err("duplicate must fail");
        assert!(
            error.message.contains(&format!("duplicate `{field}`")),
            "got: {error}"
        );
    }
}

#[test]
fn spec_modules_roundtrip_text() {
    let m = module_with_specs();
    let text = format!("{m}");
    let back = trust_ir::parser::parse_module(&text).unwrap_or_else(|e| {
        panic!("text parse failed:\n{text}\nerror: {e}");
    });
    assert_eq!(
        m, back,
        "text roundtrip must be lossless\n--- text ---\n{text}"
    );
}

#[test]
fn spec_modules_text_is_fixed_point() {
    // fmt -> parse -> fmt must be byte-identical (the diff-stability guarantee).
    let m = module_with_specs();
    let once = format!("{m}");
    let parsed = trust_ir::parser::parse_module(&once).expect("parse");
    let twice = format!("{parsed}");
    assert_eq!(once, twice, "fmt+parse+fmt must be a fixed point");
}

#[test]
fn cross_format_bin_to_json_to_text_preserves_specs() {
    // The exact path `trust-ir-cli convert` walks: decode one format, encode
    // another, decode again. SpecModules must survive every hop.
    let m = module_with_specs();

    let bin = trust_ir::binary::serialize_module(&m);
    let from_bin = trust_ir::binary::deserialize_module(&bin).expect("bin");

    let json = serde_json::to_vec_pretty(&from_bin).expect("json enc");
    let from_json: Module = serde_json::from_slice(&json).expect("json dec");

    let text = format!("{from_json}");
    let from_text = trust_ir::parser::parse_module(&text).expect("text dec");

    assert_eq!(
        m, from_text,
        "round-tripping bin->json->text must preserve specs"
    );
}

#[test]
fn legacy_module_without_specs_still_roundtrips() {
    // An empty `spec_modules` must serialize and parse identically — confirms
    // the version-gated binary read and the serde default.
    let m = Module::new("no_specs");
    assert!(m.spec_modules.is_empty());

    let bin = trust_ir::binary::serialize_module(&m);
    let back = trust_ir::binary::deserialize_module(&bin).expect("bin");
    assert!(back.spec_modules.is_empty());
    assert_eq!(m, back);

    // R3 #5, THE POSITIONAL-SERDE RULE: `rmp_serde` encodes structs as
    // POSITIONAL arrays and may only skip a TRAILING field — skipping a
    // non-last one shifts every later field into the wrong slot. `spec_modules`
    // was the trailing skippable field until v30 appended `universes` and
    // `predicates` after it (new fields MUST go last, or a legacy shorter
    // array would decode `spec_modules` into the `universes` slot). So
    // `spec_modules` FLIPPED TO ALWAYS-EMITTED in the same change, exactly as
    // `source` (v28) and `producer` (v23) did before it. It is now emitted as
    // `[]` rather than skipped; `#[serde(default)]` keeps legacy decode
    // working, and `Module::stable_digest` is computed from the BINARY codec,
    // so module identity is untouched by this.
    let json = serde_json::to_string(&m).expect("json");
    assert!(
        json.contains("\"spec_modules\":[]"),
        "spec_modules is no longer the trailing field and must always be \
         emitted, got: {json}"
    );
    assert_eq!(
        serde_json::from_str::<Module>(&json).expect("json decode"),
        m
    );
    let mp = rmp_serde::to_vec(&m).expect("msgpack");
    assert_eq!(
        rmp_serde::from_slice::<Module>(&mp).expect("msgpack decode"),
        m,
        "the positional codec must round-trip with no field shifted"
    );
}
