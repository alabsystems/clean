// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for shard-to-kernel reconstruction and verification.

use super::*;
use crate::shard::{ShardReader, ShardWriter};
use crate::types::{AxiomProfile, ContentDomain, MathverseConstantHeader, SourceSystem};

fn reader_from_writer(writer: &ShardWriter) -> ShardReader {
    let mut bytes = Vec::new();
    writer.write(&mut bytes).unwrap();
    ShardReader::from_bytes(&bytes).unwrap()
}

fn add_header(
    writer: &mut ShardWriter,
    name_idx: u32,
    type_idx: u32,
    value_idx: u32,
    import_confidence: ImportConfidence,
) {
    writer.add_constant(MathverseConstantHeader {
        name_idx,
        type_idx,
        value_idx,
        source_system: SourceSystem::Lean4 as u8,
        import_confidence: import_confidence as u8,
        content_domain: ContentDomain::PureMath as u8,
        decl_kind: 0,
        axiom_profile: if value_idx == NO_VALUE {
            AxiomProfile::AXIOMATIZED
        } else {
            AxiomProfile::NONE
        },
        sidecar_digest: 0,
        provenance_idx: 0,
        level_params_start: 0,
        level_params_count: 0,
        _pad2: [0u8; 26],
    });
}

#[test]
fn reconstruct_shard_levels_handles_composite_levels() {
    let mut writer = ShardWriter::new();
    let u_idx = writer.add_string("u");

    let zero = writer.add_level(FlatLevel::zero());
    let param = writer.add_level(FlatLevel::param(u_idx));
    let succ = writer.add_level(FlatLevel::succ(param));
    let max = writer.add_level(FlatLevel::max(zero, succ));
    let mut imax_level = FlatLevel::max(param, succ);
    imax_level.tag = FlatLevel::TAG_IMAX;
    let imax = writer.add_level(imax_level);

    let reader = reader_from_writer(&writer);
    let levels = reconstruct_shard_levels(&reader).unwrap();

    assert_eq!(levels[zero as usize], Level::zero());
    assert_eq!(levels[param as usize], Level::param(Name::from_string("u")));
    assert_eq!(
        levels[succ as usize],
        Level::succ(Level::param(Name::from_string("u")))
    );
    assert_eq!(
        levels[max as usize],
        Level::max(
            Level::zero(),
            Level::succ(Level::param(Name::from_string("u")))
        )
    );
    assert_eq!(
        levels[imax as usize],
        Level::imax(
            Level::param(Name::from_string("u")),
            Level::succ(Level::param(Name::from_string("u")))
        )
    );
}

#[test]
fn reconstruct_shard_expr_handles_const_and_app() {
    let mut writer = ShardWriter::new();
    let zero = writer.add_level(FlatLevel::zero());
    let fn_name = writer.add_string("Shard.f");

    let const_expr = writer.add_expr(FlatExpr::const_ref(fn_name, u32::MAX));
    let arg_expr = writer.add_expr(FlatExpr::sort(zero));
    let app_expr = writer.add_expr(FlatExpr::app(const_expr, arg_expr));

    let reader = reader_from_writer(&writer);
    let reconstructed = reconstruct_shard_expr(&reader, app_expr).unwrap();
    let expected = Expr::app(
        Expr::const_(Name::from_string("Shard.f"), Vec::<Level>::new()),
        Expr::sort(Level::zero()),
    );

    assert_eq!(format!("{reconstructed:?}"), format!("{expected:?}"));
}

#[test]
fn verify_shard_accepts_axiom_and_theorem() {
    let mut writer = ShardWriter::new();
    let ax_name = writer.add_string("Shard.A");
    let thm_name = writer.add_string("Shard.id");
    let level_zero = writer.add_level(FlatLevel::zero());

    let prop = writer.add_expr(FlatExpr::sort(level_zero));
    add_header(
        &mut writer,
        ax_name,
        prop,
        NO_VALUE,
        ImportConfidence::Axiomatized,
    );

    let bvar0 = writer.add_expr(FlatExpr::bvar(0));
    let bvar1 = writer.add_expr(FlatExpr::bvar(1));
    let inner_pi = writer.add_expr(FlatExpr::pi(0, bvar0, bvar1));
    let theorem_type = writer.add_expr(FlatExpr::pi(0, prop, inner_pi));
    let inner_lam = writer.add_expr(FlatExpr::lam(0, bvar0, bvar0));
    let theorem_value = writer.add_expr(FlatExpr::lam(0, prop, inner_lam));
    add_header(
        &mut writer,
        thm_name,
        theorem_type,
        theorem_value,
        ImportConfidence::KernelVerified,
    );

    let reader = reader_from_writer(&writer);
    let result = verify_shard(&reader).unwrap();

    assert_eq!(result.total, 2);
    assert_eq!(result.kernel_verified, 1);
    assert_eq!(result.axiom_accepted, 1);
    assert_eq!(result.failed, 0);
    assert!(result.failures.is_empty());
}

#[test]
fn verify_shard_into_env_uses_existing_declarations() {
    let mut axiom_writer = ShardWriter::new();
    let ax_name = axiom_writer.add_string("Shard.A");
    let level_zero = axiom_writer.add_level(FlatLevel::zero());
    let prop = axiom_writer.add_expr(FlatExpr::sort(level_zero));
    add_header(
        &mut axiom_writer,
        ax_name,
        prop,
        NO_VALUE,
        ImportConfidence::Axiomatized,
    );

    let mut dependent_writer = ShardWriter::new();
    let dep_name = dependent_writer.add_string("Shard.useA");
    let a_name = dependent_writer.add_string("Shard.A");
    let a_const = dependent_writer.add_expr(FlatExpr::const_ref(a_name, u32::MAX));
    let dep_type = dependent_writer.add_expr(FlatExpr::pi(0, a_const, a_const));
    let bvar0 = dependent_writer.add_expr(FlatExpr::bvar(0));
    let dep_value = dependent_writer.add_expr(FlatExpr::lam(0, a_const, bvar0));
    add_header(
        &mut dependent_writer,
        dep_name,
        dep_type,
        dep_value,
        ImportConfidence::KernelVerified,
    );

    let axiom_reader = reader_from_writer(&axiom_writer);
    let dependent_reader = reader_from_writer(&dependent_writer);

    let mut env = Environment::new();
    let first = verify_shard_into_env(&axiom_reader, &mut env).unwrap();
    let second = verify_shard_into_env(&dependent_reader, &mut env).unwrap();

    assert_eq!(first.failed, 0);
    assert_eq!(second.failed, 0);
    assert!(env.get_const(&Name::from_string("Shard.A")).is_some());
    assert!(env.get_const(&Name::from_string("Shard.useA")).is_some());
}

#[test]
fn verify_shard_reports_unsupported_constants() {
    let mut writer = ShardWriter::new();
    let name_idx = writer.add_string("Shard.unsupported");
    let level_zero = writer.add_level(FlatLevel::zero());
    let mut unsupported_type = FlatExpr::sort(level_zero);
    unsupported_type.flags |= 0x10;
    let type_idx = writer.add_expr(unsupported_type);

    add_header(
        &mut writer,
        name_idx,
        type_idx,
        NO_VALUE,
        ImportConfidence::Axiomatized,
    );

    let reader = reader_from_writer(&writer);
    let result = verify_shard(&reader).unwrap();

    assert_eq!(result.total, 1);
    assert_eq!(result.failed, 1);
    assert_eq!(result.kernel_verified, 0);
    assert_eq!(result.axiom_accepted, 0);
    assert_eq!(result.failures.len(), 1);
    assert!(result.failures[0].1.contains("unsupported"));
}
