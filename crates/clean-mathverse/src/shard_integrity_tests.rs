use super::*;
use crate::shard::ShardWriter;
use crate::types::{
    AxiomProfile, ContentDomain, ImportConfidence, MathverseConstantHeader, SourceSystem, NO_VALUE,
};
use clean_kernel::flat::{FlatExpr, FlatLevel};

fn header_with_level_params(
    writer: &mut ShardWriter,
    name: &str,
    lp_start: u32,
    lp_count: u16,
) -> MathverseConstantHeader {
    let name_idx = writer.add_string(name);
    // A trivial Sort type; the audit never inspects the type expr, but a
    // valid `type_idx` keeps the shard well-formed for the reader.
    let l0 = writer.add_level(FlatLevel::zero());
    let type_idx = writer.add_expr(FlatExpr::sort(l0));
    MathverseConstantHeader {
        name_idx,
        type_idx,
        value_idx: NO_VALUE,
        source_system: SourceSystem::Lean4 as u8,
        import_confidence: ImportConfidence::Axiomatized as u8,
        content_domain: ContentDomain::PureMath as u8,
        decl_kind: DeclKind::Definition as u8,
        axiom_profile: AxiomProfile::NONE,
        sidecar_digest: 0,
        provenance_idx: 0,
        level_params_start: lp_start,
        level_params_count: lp_count,
        _pad2: [0u8; 26],
    }
}

fn round_trip(writer: &ShardWriter) -> ShardReader {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("audit.mathverse");
    writer.write_to_file(&path).expect("write shard");
    ShardReader::from_file(&path).expect("read shard")
}

#[test]
fn test_audit_clean_contiguous_level_params_pass() {
    let mut writer = ShardWriter::new();
    // Two constants, each with a contiguous universe block written via the
    // block API — the correct build path.
    let start_a = writer.add_string_block(&["u", "v"]);
    let a = header_with_level_params(&mut writer, "Foo", start_a, 2);
    writer.add_constant(a);
    let start_b = writer.add_string_block(&["u_1", "u_2", "u_3"]);
    let b = header_with_level_params(&mut writer, "Bar", start_b, 3);
    writer.add_constant(b);

    let reader = round_trip(&writer);
    let report = audit_level_param_integrity(&reader);
    assert_eq!(report.with_params, 2, "both constants carry level params");
    assert!(
        report.is_clean(),
        "contiguous blocks must audit clean, got {:?}",
        report.sample
    );
    assert_eq!(report.corrupt_rate(), 0.0);
}

#[test]
fn test_audit_detects_dedup_corruption() {
    // Reproduce the released-shard corruption: intern the FIRST param via the
    // dedup path (so its recorded start is an early, shared index) while the
    // real second param lives elsewhere; the window's second slot then reads
    // an unrelated (dotted) constant name.
    let mut writer = ShardWriter::new();
    // Pre-intern a dotted constant name so it occupies the slot AFTER "u".
    let u_idx = writer.add_string("u"); // dedup index of the first param
    let _dotted = writer.add_string("Option.some"); // lands at u_idx + 1
                                                    // A constant that CLAIMS 2 level params starting at `u_idx`: slot 0 = "u"
                                                    // (valid), slot 1 = "Option.some" (leaked constant name → corruption).
    let bad = header_with_level_params(&mut writer, "Bundle.Pullback", u_idx, 2);
    writer.add_constant(bad);

    let reader = round_trip(&writer);
    let report = audit_level_param_integrity(&reader);
    assert_eq!(report.with_params, 1);
    assert_eq!(report.corrupt, 1, "dedup corruption must be detected");
    assert!(!report.is_clean());
    assert_eq!(report.sample.len(), 1);
    assert_eq!(report.sample[0].constant, "Bundle.Pullback");
    assert!(
        report.sample[0].params.iter().any(|p| p.contains('.')),
        "sampled corruption should surface the leaked dotted name, got {:?}",
        report.sample[0].params
    );
}

#[test]
fn test_audit_hygienic_universe_names_not_flagged() {
    // Lean's macro hygiene generates dotted universe-parameter names
    // (`v._@.Module.hash._hygCtx._hyg.13`, `u._@._hyg.5`). These are VALID
    // universe parameters and must NOT be reported as corruption, even
    // though they contain '.'. Written contiguously via the block API.
    let mut writer = ShardWriter::new();
    let start = writer.add_string_block(&[
        "u_1",
        "u",
        "v",
        "u._@._hyg.5",
        "v._@.Init.MetaTypes.502562599._hygCtx._hyg.7",
    ]);
    let c = header_with_level_params(&mut writer, "PSigma.casesOn._arg_pusher", start, 5);
    writer.add_constant(c);

    let reader = round_trip(&writer);
    let report = audit_level_param_integrity(&reader);
    assert_eq!(report.with_params, 1);
    assert!(
        report.is_clean(),
        "hygienic universe names must not be flagged, got {:?}",
        report.sample
    );
}

#[test]
fn test_audit_single_param_dedup_is_not_flagged() {
    // A single-parameter constant survives the dedup path (only the first
    // slot is read), so it is genuinely NOT corrupt — the audit must not
    // false-flag it.
    let mut writer = ShardWriter::new();
    let u_idx = writer.add_string("u");
    let _other = writer.add_string("Option.some");
    let ok = header_with_level_params(&mut writer, "Mono", u_idx, 1);
    writer.add_constant(ok);

    let reader = round_trip(&writer);
    let report = audit_level_param_integrity(&reader);
    assert_eq!(report.with_params, 1);
    assert!(report.is_clean(), "single-param const is not corrupt");
}

#[test]
fn test_repair_recomputes_corrupt_level_params_from_type() {
    // Build a constant `Foo.{u,v} : Sort u -> Sort v -> Sort (max u v)` whose
    // stored level_params window is CORRUPT (points at a dedup'd first param
    // followed by a leaked constant name), then repair it from the type.
    let mut writer = ShardWriter::new();
    // String table laid out so the corrupt window `[su, su+1]` reads
    // ["u", "Option.some"] (a leaked constant name), not ["u", "v"].
    let su = writer.add_string("u");
    let _leak = writer.add_string("Option.some");
    let sv = writer.add_string("v");
    let name_idx = writer.add_string("Foo");
    // Level pool: params u, v (FlatLevel::param takes a STRING index).
    let lu = writer.add_level(FlatLevel::param(su));
    let lv = writer.add_level(FlatLevel::param(sv));
    let l_maxuv = writer.add_level(FlatLevel::max(lu, lv));
    // Type: Sort u -> Sort v -> Sort (max u v).  (binder_info 0 = default)
    let sort_u = writer.add_expr(FlatExpr::sort(lu));
    let sort_v = writer.add_expr(FlatExpr::sort(lv));
    let sort_max = writer.add_expr(FlatExpr::sort(l_maxuv));
    let inner = writer.add_expr(FlatExpr::pi(0, sort_v, sort_max));
    let type_idx = writer.add_expr(FlatExpr::pi(0, sort_u, inner));
    // Corrupt window: start at "u", count 2 -> ["u", "Option.some"].
    let mut hdr = header_with_level_params(&mut writer, "Foo_placeholder", su, 2);
    hdr.name_idx = name_idx;
    hdr.type_idx = type_idx;
    writer.add_constant(hdr);

    let mut reader = round_trip(&writer);
    assert!(
        !audit_level_param_integrity(&reader).is_clean(),
        "precondition: window is corrupt before repair"
    );

    let stats = repair_level_params(&mut reader);
    assert_eq!(stats.examined, 1);
    assert_eq!(stats.repaired, 1);
    assert_eq!(stats.unrepairable, 0);

    // After repair the window must reconstruct to exactly [u, v].
    let report = audit_level_param_integrity(&reader);
    assert!(
        report.is_clean(),
        "repair must clear the corruption: {report:?}"
    );
    let hdr = &reader.constants[0];
    let params = reconstruct_level_params(
        &reader.strings,
        hdr.level_params_start,
        hdr.level_params_count,
    )
    .expect("params");
    let names: Vec<String> = params.iter().map(ToString::to_string).collect();
    assert_eq!(names, vec!["u".to_string(), "v".to_string()]);
}

#[test]
fn test_repair_preserves_declared_order_via_anchor() {
    // Declared order [v, u] (like `Quiver.{v,u}`): the morphism universe `v`
    // is first, but `u` occurs first in the type `Sort u -> Sort v -> ...`.
    // Naive first-occurrence would wrongly yield [u, v]; anchoring on the
    // reliable stored first param ("v") must recover [v, u].
    let mut writer = ShardWriter::new();
    let sv = writer.add_string("v");
    let _leak = writer.add_string("Except.rec");
    let su = writer.add_string("u");
    let name_idx = writer.add_string("Q");
    let lu = writer.add_level(FlatLevel::param(su));
    let lv = writer.add_level(FlatLevel::param(sv));
    let l_maxuv = writer.add_level(FlatLevel::max(lu, lv));
    // Type: Sort u -> Sort v -> Sort (max u v)  (u occurs first).
    let sort_u = writer.add_expr(FlatExpr::sort(lu));
    let sort_v = writer.add_expr(FlatExpr::sort(lv));
    let sort_max = writer.add_expr(FlatExpr::sort(l_maxuv));
    let inner = writer.add_expr(FlatExpr::pi(0, sort_v, sort_max));
    let type_idx = writer.add_expr(FlatExpr::pi(0, sort_u, inner));
    // Corrupt window: start at "v", count 2 -> ["v", "Except.rec"].
    let mut hdr = header_with_level_params(&mut writer, "Q_placeholder", sv, 2);
    hdr.name_idx = name_idx;
    hdr.type_idx = type_idx;
    writer.add_constant(hdr);

    let mut reader = round_trip(&writer);
    let stats = repair_level_params(&mut reader);
    assert_eq!(stats.repaired, 1);
    let hdr = &reader.constants[0];
    let params = reconstruct_level_params(
        &reader.strings,
        hdr.level_params_start,
        hdr.level_params_count,
    )
    .expect("params");
    let names: Vec<String> = params.iter().map(ToString::to_string).collect();
    assert_eq!(
        names,
        vec!["v".to_string(), "u".to_string()],
        "anchor on stored first param must preserve declared order [v, u]"
    );
}

#[test]
fn test_repair_leaves_clean_constants_untouched() {
    let mut writer = ShardWriter::new();
    let start = writer.add_string_block(&["u", "v"]);
    let c = header_with_level_params(&mut writer, "Clean", start, 2);
    writer.add_constant(c);
    let mut reader = round_trip(&writer);
    let stats = repair_level_params(&mut reader);
    assert_eq!(stats.examined, 1);
    assert_eq!(stats.repaired, 0, "a clean constant must not be rewritten");
}

#[test]
fn test_audit_no_params_population_empty() {
    let mut writer = ShardWriter::new();
    let none = header_with_level_params(&mut writer, "Prop0", 0, 0);
    writer.add_constant(none);
    let reader = round_trip(&writer);
    let report = audit_level_param_integrity(&reader);
    assert_eq!(report.with_params, 0);
    assert!(report.is_clean());
    assert_eq!(report.corrupt_rate(), 0.0);
}
