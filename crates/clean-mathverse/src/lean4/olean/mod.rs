// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `.olean`-oriented Lean 4 import/verification modules.
//!
//! These modules were consolidated from the former top-level `lean4_*`
//! modules. Callers use the canonical `crate::lean4::olean::*` paths directly
//! (the transitional `crate::lean4_*` lib.rs aliases were removed).

pub mod alpha;
pub mod axiom_profile;
pub mod batch;
pub mod decl_kind;
pub mod olean_bridge;
pub mod shard;
pub mod verify;

/// These shard writers lower Lean ConstantInfos only. A Clean payload owns its
/// declarations instead of its Lean-format mirrors; sharding those mirrors or
/// dropping them as compiler auxiliaries would claim a different population.
pub(crate) fn require_lean_records_only(
    module: &clean_olean::ParsedModule,
) -> crate::error::MathverseResult<()> {
    if module
        .clean_payload
        .as_ref()
        .is_some_and(|payload| payload.total_constants() > 0)
    {
        return Err(crate::error::MathverseError::ImportFailed {
            system: "Lean4".into(),
            reason: "module carries Clean payload declarations; this shard importer lowers only Lean records".into(),
        });
    }
    Ok(())
}

#[cfg(test)]
pub(crate) mod compiler_record_roles_tests {
    use crate::provenance::ProvenanceSidecar;
    use crate::shard::ShardWriter;
    use clean_kernel::env::{ConstantInfo, Environment, TrustedEnvExt};
    use clean_kernel::expr::{BinderInfo, Expr};
    use clean_kernel::name::Name;

    pub(crate) fn fixture_bytes() -> Vec<u8> {
        let name = Name::from_string("PayloadRoles._spec_1");
        let ty = Expr::pi(BinderInfo::Default, Expr::type_(), Expr::type_());
        let mut mirror = Environment::default();
        mirror.extend_constants_unchecked(
            [ConstantInfo::new(
                name.clone(),
                vec![],
                ty.clone(),
                Some(Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(0))),
                true,
            )]
            .into_iter(),
        );
        mirror.mark_unsafe(name.clone());
        let payload = clean_olean::CleanPayload {
            constants: vec![ConstantInfo::new(
                name,
                vec![],
                ty,
                Some(Expr::prop()),
                true,
            )],
            ..clean_olean::CleanPayload::default()
        };
        clean_olean::OleanExporter::export_with_env_and_payload(
            &mirror,
            &[],
            &[],
            "0000000000000000000000000000000000000000",
            &payload,
        )
        .unwrap()
    }

    #[test]
    fn compiler_record_roles_shard_entrypoints_refuse_payload_before_mutation() {
        let module = clean_olean::parse_module(&fixture_bytes()).unwrap();
        assert_eq!(
            module.constants[0].definition_safety,
            Some(clean_olean::DefinitionSafety::Unsafe)
        );
        for route in 0..3 {
            let mut writer = ShardWriter::new();
            writer.add_string("existing data");
            let before = (
                writer.string_count(),
                writer.expr_count(),
                writer.constant_count(),
            );
            let mut sidecar = ProvenanceSidecar::new();
            let result = match route {
                0 => super::alpha::import_module_verified(&module, &mut writer, None).map(|_| ()),
                1 => super::alpha::import_with_provenance(
                    &module,
                    &mut writer,
                    &super::alpha::Lean4ImportConfig::default(),
                )
                .map(|_| ()),
                _ => super::olean_bridge::import_module_with_provenance_verified(
                    &module,
                    &mut writer,
                    &mut sidecar,
                    Some("PayloadRoles"),
                    None,
                )
                .map(|_| ()),
            };
            let error = result.expect_err("raw Lean records cannot represent the payload owner");
            assert!(matches!(
                error,
                crate::error::MathverseError::ImportFailed { .. }
            ));
            assert!(error.to_string().contains("Clean payload declarations"));
            assert_eq!(
                (
                    writer.string_count(),
                    writer.expr_count(),
                    writer.constant_count()
                ),
                before
            );
            assert_eq!(sidecar.len(), 0);
        }
        let mut empty_payload = module;
        empty_payload.clean_payload = Some(clean_olean::CleanPayload::default());
        super::require_lean_records_only(&empty_payload)
            .expect("empty payload has no shadowing declarations");
    }
}
