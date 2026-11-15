// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// Wire v59 — typed effect summaries and world epochs (roadmap WS1.14, finding
// F-013): `FunctionSummary.effects: Option<EffectSummary>` and the
// `ClausePlace::WorldPre` / `WorldPost` epochs. This file pins the FORMAT half:
// version selection, both read gates, the codecs (binary, JSON, MessagePack
// and text: the `; #effects:` summary directive and the `world_pre` /
// `world_post` places), the strict flag bytes, the v38-projection refusal and
// the
// `trust_ir.obligation.digest.v8` identity. The validator's rules live in
// `trust-ir-build/tests/effect_summary_validation.rs`.

#![cfg(all(
    feature = "binary",
    feature = "diff",
    feature = "fmt",
    feature = "parser",
    feature = "serde"
))]

use trust_ir::binary::{
    self, BinaryError, BinaryProjectionError, EFFECT_SUMMARY_FORMAT_VERSION, ModuleBinaryBody,
    ModuleBinaryOptions, ProjectedModuleBinaryPlan,
};
use trust_ir::proof::{
    ClauseBinding, ClausePlace, ClauseSort, ObligationKind, ProofFormula, ProofObligation,
    ProofStatus,
};
use trust_ir::ty::{FuncTy, Ty};
use trust_ir::value::{FuncId, GlobalId, ProofId};
use trust_ir::{
    EffectPlace, EffectSet, EffectSummary, Function, FunctionSummary, Module, Producer,
};

fn header_version(bytes: &[u8]) -> u32 {
    u32::from_le_bytes(bytes[8..12].try_into().unwrap())
}

fn with_header(bytes: &[u8], version: u32) -> Vec<u8> {
    let mut out = bytes.to_vec();
    out[8..12].copy_from_slice(&version.to_le_bytes());
    out
}

fn heap() -> ClauseSort {
    ClauseSort::Array(
        Box::new(ClauseSort::BitVec(64)),
        Box::new(ClauseSort::BitVec(64)),
    )
}

/// `(= (select after 0) (select before 0))` over the two world epochs.
fn frame_clause() -> ProofFormula {
    let mut f = ProofFormula::smtlib2(
        "(= (select after #x0000000000000000) (select before #x0000000000000000))",
        "Bool",
    );
    f.bindings = vec![
        (
            "before".to_string(),
            ClauseBinding {
                sort: heap(),
                place: ClausePlace::WorldPre,
            },
        ),
        (
            "after".to_string(),
            ClauseBinding {
                sort: heap(),
                place: ClausePlace::WorldPost,
            },
        ),
    ];
    f
}

fn effects() -> EffectSummary {
    EffectSummary {
        reads: EffectSet::Everything,
        writes: EffectSet::of([
            EffectPlace::ParamPointee { index: 0 },
            EffectPlace::Global(GlobalId::new(0)),
        ]),
        allocates: true,
        frees: false,
        may_unwind: true,
        io: false,
    }
}

/// A module whose one body-less declaration carries `summary`, plus a legacy
/// obligation scoped to it (so the obligation digest reads the summary).
fn module_with(summary: FunctionSummary) -> Module {
    let mut m = Module::new("effect_summaries");
    let ft = m
        .add_func_type(FuncTy {
            abi: None,
            params: vec![Ty::PtrMut(Box::new(Ty::U64))],
            returns: vec![],
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = Function::declaration(FuncId::new(0), "tick", ft, summary);
    f.producer = Some(Producer::TRust);
    m.try_add_function(f)
        .expect("Module::try_add_function: test fixture");
    m.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(0),
            ObligationKind::Postcondition,
            ProofStatus::Pending,
            "ensures of tick",
        )
        .with_function(FuncId::new(0))
        .with_formula(ProofFormula::smtlib2("(= 1 1)", "Bool")),
    );
    m
}

/// Every v59 feature at once.
fn full() -> Module {
    module_with(
        FunctionSummary::new()
            .with_params(vec!["p".to_string()])
            .ensuring(frame_clause())
            .with_effects(effects()),
    )
}

/// The same module with every v59 feature stripped.
fn legacy() -> Module {
    module_with(
        FunctionSummary::new()
            .with_params(vec!["p".to_string()])
            .ensuring(ProofFormula::smtlib2("(= 1 1)", "Bool")),
    )
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

/// Positive: the full module round-trips exactly through binary (at v59),
/// JSON, MessagePack and text.
#[test]
fn effects_and_epochs_round_trip_through_every_codec() {
    let module = full();
    let bytes = binary::serialize_module(&module).expect("serialize_module: test fixture");
    assert_eq!(header_version(&bytes), EFFECT_SUMMARY_FORMAT_VERSION);
    let back = binary::deserialize_module(&bytes).unwrap();
    assert_eq!(back, module);
    assert_eq!(
        binary::serialize_module(&back).expect("serialize_module: test fixture"),
        bytes
    );
    assert_eq!(projected(&module, ModuleBinaryBody::Raw).unwrap(), bytes);

    let json = serde_json::to_vec(&module).unwrap();
    assert_eq!(serde_json::from_slice::<Module>(&json).unwrap(), module);
    let msgpack = rmp_serde::to_vec(&module).unwrap();
    assert_eq!(rmp_serde::from_slice::<Module>(&msgpack).unwrap(), module);

    let text = trust_ir::format::canonical_checked(&module).expect("text carries the summary");
    for spelling in [
        "; #effects: reads everything writes places [param(0), global(0)] allocates true \
         frees false may_unwind true io false\n",
        "bind \"before\" ",
        " world_pre",
        " world_post",
    ] {
        assert!(text.contains(spelling), "missing `{spelling}`: {text}");
    }
    let parsed = trust_ir::parser::parse_module(&text).expect("the parser reads it back");
    assert_eq!(parsed, module);
    assert_eq!(trust_ir::format::canonical(&parsed), text, "idempotent");
}

/// Text: `None` (UNRECORDED) prints no `#effects` line and `pure()` prints
/// its affirmative line, and each reads back as itself — the two are never
/// conflated.
#[test]
fn text_keeps_unrecorded_and_pure_apart() {
    let unrecorded = legacy();
    let text = trust_ir::format::canonical_checked(&unrecorded).expect("legacy text");
    assert!(!text.contains("#effects"), "{text}");
    assert_eq!(trust_ir::parser::parse_module(&text).unwrap(), unrecorded);

    let pure = module_with(
        FunctionSummary::new()
            .with_params(vec!["p".to_string()])
            .with_effects(EffectSummary::pure()),
    );
    let text = trust_ir::format::canonical_checked(&pure).expect("pure text");
    assert!(
        text.contains(
            "; #effects: reads nothing writes nothing allocates false frees false \
             may_unwind false io false\n"
        ),
        "{text}"
    );
    let back = trust_ir::parser::parse_module(&text).unwrap();
    assert_eq!(back, pure);
    assert_ne!(back, unrecorded);
}

/// A non-canonical effect set (built in memory; every decoder refuses it, the
/// text parser included) is a named text LOSS, never lossless text the parser
/// would then refuse: `canonical_checked` refuses it, for either side.
#[test]
fn a_non_canonical_effect_set_is_a_text_loss() {
    use trust_ir::format::TextLoss;
    let lossless = full();
    assert!(trust_ir::format::text_losses(&lossless).is_empty());
    for (what, set) in [
        ("empty", EffectSet::Places(vec![])),
        (
            "unordered",
            EffectSet::Places(vec![
                EffectPlace::Global(GlobalId::new(0)),
                EffectPlace::ParamPointee { index: 0 },
            ]),
        ),
        (
            "duplicated",
            EffectSet::Places(vec![
                EffectPlace::ParamPointee { index: 0 },
                EffectPlace::ParamPointee { index: 0 },
            ]),
        ),
    ] {
        for side in ["reads", "writes"] {
            let mut module = full();
            let effects = module.functions[0]
                .summary
                .as_mut()
                .and_then(|s| s.effects.as_mut())
                .expect("the full module records effects");
            if side == "reads" {
                effects.reads = set.clone();
            } else {
                effects.writes = set.clone();
            }
            assert!(
                trust_ir::format::text_losses(&module).contains(&TextLoss::FunctionSummary {
                    func: FuncId::new(0)
                }),
                "{what} {side}: a named loss"
            );
            assert!(
                trust_ir::format::canonical_checked(&module).is_err(),
                "{what} {side}: never offered as lossless text"
            );
        }
    }
}

/// Adversarial twins of the `#effects` line: each is one edit of the printed
/// text and each must be REFUSED, never read as some other summary — a second
/// spelling of a place set (empty, out of order, duplicated), an unknown set or
/// place word, a non-strict flag, a flag out of order or missing, a second
/// `#effects`, an `#effects` before `#backed-by`/a clause or outside the
/// summary block, and an unknown clause place.
#[test]
fn text_refuses_every_malformed_effects_line() {
    let text = trust_ir::format::canonical(&full());
    let line = "; #effects: reads everything writes places [param(0), global(0)] allocates true \
                frees false may_unwind true io false";
    assert!(text.contains(line), "{text}");
    let mut twins: Vec<(String, &str)> = vec![
        (
            text.replacen("places [param(0), global(0)]", "places []", 1),
            "empty place list",
        ),
        (
            text.replacen(
                "places [param(0), global(0)]",
                "places [global(0), param(0)]",
                1,
            ),
            "out-of-order place list",
        ),
        (
            text.replacen(
                "places [param(0), global(0)]",
                "places [param(0), param(0)]",
                1,
            ),
            "duplicated place",
        ),
        (
            text.replacen("reads everything", "reads all", 1),
            "unknown set word",
        ),
        (
            text.replacen("[param(0),", "[local(0),", 1),
            "unknown place word",
        ),
        (
            text.replacen("allocates true", "allocates 1", 1),
            "non-strict flag",
        ),
        (
            text.replacen(
                "allocates true frees false",
                "frees false allocates true",
                1,
            ),
            "flags out of order",
        ),
        (text.replacen(" io false", "", 1), "missing flag"),
        (
            text.replacen("reads everything writes", "writes", 1),
            "missing reads",
        ),
        (
            text.replacen(line, &format!("{line}\n    {line}"), 1),
            "second #effects",
        ),
        (
            text.replacen("world_post", "world_after", 1),
            "unknown clause place",
        ),
    ];
    // `#effects` before an `#ensures` clause (out of the fixed order).
    let ensures_at = text.find("    ; #ensures:").expect("an ensures line");
    let mut reordered = text.replacen(&format!("    {line}\n"), "", 1);
    reordered.insert_str(ensures_at, &format!("    {line}\n"));
    twins.push((reordered, "#effects before #ensures"));
    twins.push((
        text.replacen(" io false\n", " io false extra\n", 1),
        "trailing token",
    ));
    for (broken, what) in &twins {
        assert_ne!(broken, &text, "{what}: the edit applies");
    }
    // `#effects` with no `#summary` block at all, on a summary whose ONLY
    // other line is the header (so nothing else can be what is refused).
    let pure = trust_ir::format::canonical(&module_with(
        FunctionSummary::new().with_effects(EffectSummary::pure()),
    ));
    let summary_start = pure.find("    ; #summary:").expect("a summary line");
    let summary_end = summary_start + pure[summary_start..].find('\n').unwrap() + 1;
    assert!(pure[summary_end..].starts_with("    ; #effects:"), "{pure}");
    let mut headless = pure.clone();
    headless.replace_range(summary_start..summary_end, "");
    assert!(
        trust_ir::parser::parse_module(&pure).is_ok(),
        "control: {pure}"
    );
    twins.push((headless, "#effects without #summary"));
    for (broken, what) in twins {
        assert!(
            trust_ir::parser::parse_module(&broken).is_err(),
            "{what} must not parse:\n{broken}"
        );
    }
}

/// Mutation control for selection: stripped, the module keeps its pre-v59
/// header and bytes; each feature ALONE selects v59 and is refused by a v38
/// projection by name.
#[test]
fn each_feature_alone_selects_the_effect_version_and_none_keeps_the_legacy_header() {
    let base = legacy();
    let base_bytes = binary::serialize_module(&base).expect("serialize_module: test fixture");
    assert!(header_version(&base_bytes) < EFFECT_SUMMARY_FORMAT_VERSION);
    type Feature = (&'static str, fn(&mut FunctionSummary));
    let features: [Feature; 4] = [
        ("effects: pure", |s| s.effects = Some(EffectSummary::pure())),
        ("effects: top", |s| s.effects = Some(EffectSummary::top())),
        ("a WorldPre binding", |s| {
            let mut c = ProofFormula::smtlib2("(= w w)", "Bool");
            c.bindings = vec![(
                "w".to_string(),
                ClauseBinding {
                    sort: heap(),
                    place: ClausePlace::WorldPre,
                },
            )];
            s.requires.push(c);
        }),
        ("a WorldPost binding", |s| s.ensures = vec![frame_clause()]),
    ];
    for (name, apply) in features {
        let mut one = base.clone();
        apply(one.functions[0].summary.as_mut().unwrap());
        let bytes = binary::serialize_module(&one).expect("serialize_module: test fixture");
        assert_eq!(
            header_version(&bytes),
            EFFECT_SUMMARY_FORMAT_VERSION,
            "{name} must select v59"
        );
        assert_eq!(binary::deserialize_module(&bytes).unwrap(), one, "{name}");
        for body in [ModuleBinaryBody::RawV38, ModuleBinaryBody::CanonicalV38] {
            assert_eq!(
                projected(&one, body).unwrap_err(),
                BinaryProjectionError::EffectSummaryRequiresV59,
                "{name}: a v38 projection must refuse by name"
            );
        }
    }
}

/// `None` is UNRECORDED, never pure: a v59 module spells both, and they decode
/// apart.
#[test]
fn unrecorded_and_pure_stay_distinct_on_the_wire() {
    let mut m = full();
    let unrecorded = FunctionSummary::new().with_params(vec!["p".to_string()]);
    let pure = unrecorded.clone().with_effects(EffectSummary::pure());
    let ft = m.functions[0].ty;
    m.try_add_function(Function::declaration(FuncId::new(1), "a", ft, unrecorded))
        .expect("Module::try_add_function: test fixture");
    m.try_add_function(Function::declaration(FuncId::new(2), "b", ft, pure))
        .expect("Module::try_add_function: test fixture");
    let back = binary::deserialize_module(
        &binary::serialize_module(&m).expect("serialize_module: test fixture"),
    )
    .unwrap();
    assert_eq!(back.functions[1].summary.as_ref().unwrap().effects, None);
    assert_eq!(
        back.functions[2].summary.as_ref().unwrap().effects,
        Some(EffectSummary::pure())
    );
}

/// The `version >= 59` read gates are load-bearing: a world-epoch tag under
/// an older header is refused as `InvalidTag`, and the effect bytes under an
/// older header do not reproduce the module.
#[test]
fn the_effect_read_gates_are_load_bearing() {
    let older = EFFECT_SUMMARY_FORMAT_VERSION - 1;

    // Epoch only (no effects): the first thing the older reader trips on is
    // clause-place tag 8 (`WorldPre`).
    let mut epochs = legacy();
    epochs.functions[0].summary.as_mut().unwrap().ensures = vec![frame_clause()];
    let bytes = with_header(
        &binary::serialize_module(&epochs).expect("serialize_module: test fixture"),
        older,
    );
    // Versions land in number order, so the header just below v59 is one this
    // reader accepts: the refusal is the read gate's, not the header check's.
    assert_eq!(
        binary::deserialize_module(&bytes),
        Err(BinaryError::InvalidTag(8)),
        "a WorldPre tag under a v{older} header must be refused"
    );

    // Effects: under the older header the reader never reads the presence
    // byte, so the module cannot come back.
    let mut effectful = legacy();
    effectful.functions[0].summary.as_mut().unwrap().effects = Some(effects());
    let bytes = with_header(
        &binary::serialize_module(&effectful).expect("serialize_module: test fixture"),
        older,
    );
    let misread = binary::deserialize_module(&bytes);
    assert!(
        misread.as_ref().map_or(true, |m| *m != effectful),
        "v59 effect bytes under a v{older} header must not reproduce the module: {misread:?}"
    );
}

/// A pre-v59 blob decodes with `effects = None` and re-encodes identically.
#[test]
fn legacy_bytes_decode_unrecorded_and_re_encode_identically() {
    let base = legacy();
    let bytes = binary::serialize_module(&base).expect("serialize_module: test fixture");
    let back = binary::deserialize_module(&bytes).unwrap();
    assert_eq!(back.functions[0].summary.as_ref().unwrap().effects, None);
    assert_eq!(
        binary::serialize_module(&back).expect("serialize_module: test fixture"),
        bytes
    );
    // JSON: the trailing field is skipped when `None`, so a pre-v59 spelling
    // is byte-identical.
    let json = serde_json::to_string(&base).unwrap();
    assert!(!json.contains("\"effects\""), "{json}");
}

/// The four flags are strict bool bytes: a `2` is `InvalidTag(2)`, never
/// silently `true` (which would re-encode to different bytes).
#[test]
fn a_non_boolean_flag_byte_is_refused() {
    let mut m = legacy();
    m.functions[0].summary.as_mut().unwrap().effects = Some(EffectSummary::pure());
    let honest = binary::serialize_module(&m).expect("serialize_module: test fixture");
    let mut flipped = m.clone();
    flipped.functions[0]
        .summary
        .as_mut()
        .unwrap()
        .effects
        .as_mut()
        .unwrap()
        .io = true;
    let other = binary::serialize_module(&flipped).expect("serialize_module: test fixture");
    assert_eq!(honest.len(), other.len());
    let at = honest
        .iter()
        .zip(&other)
        .position(|(a, b)| a != b)
        .expect("the io flag moves one byte");
    assert_eq!((honest[at], other[at]), (0, 1));
    let mut forged = honest.clone();
    forged[at] = 2;
    assert_eq!(
        binary::deserialize_module(&forged),
        Err(BinaryError::InvalidTag(2))
    );
}

/// The obligation content digest (v8) reads the owning summary's effects:
/// changing, adding or dropping them moves the cache identity; the epochs a
/// clause binds are part of it too.
#[test]
fn the_obligation_digest_binds_the_effect_frame_and_the_epochs() {
    let digest = |m: &Module| m.obligation_digest(ProofId::new(0)).unwrap();
    let base = full();
    let mut widened = base.clone();
    widened.functions[0]
        .summary
        .as_mut()
        .unwrap()
        .effects
        .as_mut()
        .unwrap()
        .writes = EffectSet::Everything;
    let mut dropped = base.clone();
    dropped.functions[0].summary.as_mut().unwrap().effects = None;
    let mut swapped = base.clone();
    for (_, binding) in &mut swapped.functions[0].summary.as_mut().unwrap().ensures[0].bindings {
        binding.place = match binding.place {
            ClausePlace::WorldPre => ClausePlace::WorldPost,
            _ => ClausePlace::WorldPre,
        };
    }
    let all = [
        digest(&base),
        digest(&widened),
        digest(&dropped),
        digest(&swapped),
    ];
    for (i, a) in all.iter().enumerate() {
        for b in &all[i + 1..] {
            assert_ne!(a, b);
        }
    }
    assert_eq!(digest(&base), digest(&full()), "deterministic");
}

/// `Module::stable_digest` (the module identity) sees the effect frame too.
#[test]
fn the_module_identity_sees_the_effect_frame() {
    let base = full();
    let mut other = base.clone();
    other.functions[0]
        .summary
        .as_mut()
        .unwrap()
        .effects
        .as_mut()
        .unwrap()
        .frees = true;
    assert_ne!(base.stable_digest(), other.stable_digest());
}

/// One spelling per set (SPEC_RATIFICATIONS §3), checked on READ by every
/// decoder, like a non-canonical `U128` or `Splat`: a place list that is empty
/// (the empty set is `Nothing`), out of order (across and within variants) or
/// duplicated is refused by the binary, JSON and MessagePack readers alike.
/// The writers spell what they are handed, so each forged set really reaches
/// the reader. Control: the canonical spelling of the same places decodes.
#[test]
fn a_non_canonical_place_list_is_refused_by_every_decoder() {
    let p = |index| EffectPlace::ParamPointee { index };
    let g = EffectPlace::Global(GlobalId::new(0));
    let with_writes = |writes: EffectSet| {
        let mut m = legacy();
        m.functions[0].summary.as_mut().unwrap().effects =
            Some(EffectSummary::pure().writing(writes));
        m
    };
    for (name, forged, canonical) in [
        ("empty", vec![], EffectSet::Nothing),
        ("descending", vec![p(1), p(0)], EffectSet::of([p(0), p(1)])),
        ("duplicate", vec![p(0), p(0)], EffectSet::of([p(0)])),
        (
            "global before param",
            vec![g, p(0)],
            EffectSet::of([p(0), g]),
        ),
    ] {
        let module = with_writes(EffectSet::Places(forged));
        match binary::deserialize_module(
            &binary::serialize_module(&module).expect("serialize_module: test fixture"),
        ) {
            Err(BinaryError::InvalidData(message)) => assert!(
                message.contains("non-canonical EffectSet::Places"),
                "{name}: {message}"
            ),
            other => panic!("{name}: the binary reader must refuse the place list: {other:?}"),
        }
        let json = serde_json::to_vec(&module).unwrap();
        let error = serde_json::from_slice::<Module>(&json)
            .expect_err("the JSON reader must refuse a non-canonical place list");
        assert!(
            error
                .to_string()
                .contains("non-canonical EffectSet::Places"),
            "{name}: {error}"
        );
        let msgpack = rmp_serde::to_vec(&module).unwrap();
        let error = rmp_serde::from_slice::<Module>(&msgpack)
            .expect_err("the MessagePack reader must refuse a non-canonical place list");
        assert!(
            error
                .to_string()
                .contains("non-canonical EffectSet::Places"),
            "{name}: {error}"
        );

        let honest = with_writes(canonical);
        let bytes = binary::serialize_module(&honest).expect("serialize_module: test fixture");
        assert_eq!(
            binary::deserialize_module(&bytes).unwrap(),
            honest,
            "{name}"
        );
        let json = serde_json::to_vec(&honest).unwrap();
        assert_eq!(
            serde_json::from_slice::<Module>(&json).unwrap(),
            honest,
            "{name}"
        );
        let msgpack = rmp_serde::to_vec(&honest).unwrap();
        assert_eq!(
            rmp_serde::from_slice::<Module>(&msgpack).unwrap(),
            honest,
            "{name}"
        );
    }
}
