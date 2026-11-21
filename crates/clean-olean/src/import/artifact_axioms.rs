// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Original Lean axiom signatures used by the native module writer. This
//! observation neither promotes an imported origin nor admits a declaration.

use super::{lean_declaration_artifact, ledger_idx, ArtifactLedger};
use crate::import::convert_expr_direct::{read_and_convert_expr_with_memo, RegionPtrCache};
use crate::import::load_parse::LoadModule;
use crate::import::ExprInternCache;
use crate::{ConstantKind, DefinitionSafety};
use clean_kernel::env::{ConstantInfo, ConstantKind as ResidentKind};
use clean_kernel::{Environment, Expr, Name};
use hashbrown::{HashMap, HashSet};

#[derive(Clone, Debug)]
struct AxiomSignature {
    parameters: Vec<Name>,
    type_: Expr,
}

impl AxiomSignature {
    fn matches(&self, resident: &ConstantInfo) -> bool {
        resident.kind == ResidentKind::Axiom
            && resident.value.is_none()
            && self.parameters == resident.level_params
            && self.type_ == resident.type_
    }
}

#[derive(Clone, Debug, Default)]
pub(super) struct ImportedAxioms {
    by_name: HashMap<Name, (String, AxiomSignature)>,
    /// A shadowed declaration or failed completion anywhere in the import
    /// graph cannot become an axiom merely because another part has its name.
    disputed: HashSet<Name>,
}

impl ImportedAxioms {
    pub(super) fn begin_load(&mut self, module: &str) {
        self.by_name.retain(|_, (owner, _)| owner != module);
    }

    pub(super) fn forget_declaration(&mut self, name: &Name) -> bool {
        self.by_name.remove(name).is_some()
    }
}

/// Does the actual Lean-format authoritative part declare exactly this
/// resident safe axiom? A stub in a public/server part supplies no evidence.
/// No snapshot or Clean payload can mint this in-process observation.
#[must_use]
pub fn is_authoritative_lean_axiom(env: &Environment, name: &Name) -> bool {
    let Some(owner) = lean_declaration_artifact(env, name) else {
        return false;
    };
    let Some(ledger) = env.get_ext_state::<ArtifactLedger>(ledger_idx()) else {
        return false;
    };
    !env.is_unsafe(name)
        && !ledger.axioms.disputed.contains(name)
        && ledger
            .axioms
            .by_name
            .get(name)
            .zip(env.get_const(name))
            .is_some_and(|((source, record), resident)| {
                *source == owner && record.matches(resident)
            })
}

/// Called after the whole artifact has passed the reader, world and ledger
/// checks. Read the same captured authoritative region the importer used.
/// A later load replaces this module's evidence, including removed names.
pub(in crate::import) fn observe_authoritative_axioms(
    env: &mut Environment,
    module: &str,
    raw: &LoadModule,
    payload_names: &HashSet<Name>,
    intern: &mut ExprInternCache,
) {
    if crate::import::world_gate::environment_world(env) != Some("v4.36.0") {
        return;
    }
    // Selected Lean worlds reject incompatible Lean writers but also allow
    // neutral Clean payloads. Those cannot authenticate a Lean record.
    let lean = matches!(
        crate::world::part_writer_of_bytes(&raw.bytes),
        Ok(crate::world::PartWriter::Lean { .. })
    );
    let region = raw.region();
    let mut memo = RegionPtrCache::for_region();
    let mut axioms = Vec::new();
    let mut disputed = Vec::new();
    for record in &raw.constants {
        let name = &record.kernel_name;
        let resident = env.get_const(name);
        if resident.is_some_and(|info| info.kind != ResidentKind::Axiom) {
            continue;
        }
        // A family is not an axiom even where it has no ConstantInfo entry.
        if env.get_inductive(name).is_some()
            || env.get_constructor(name).is_some()
            || env.get_recursor(name).is_some()
            || env.get_quot(name).is_some()
        {
            continue;
        }
        if !lean
            || record.kind != ConstantKind::Axiom
            || record.type_ptr == 0
            || record.value_ptr != 0
            || record.definition_safety != Some(DefinitionSafety::Safe)
            || payload_names.contains(name)
            || lean_declaration_artifact(env, name).as_deref() != Some(module)
            || env.is_unsafe(name)
        {
            disputed.push(name.clone());
            continue;
        }
        if let Ok((type_, _)) = read_and_convert_expr_with_memo(
            &region,
            record.type_ptr,
            &record.name,
            intern,
            &mut memo,
        ) {
            let signature = AxiomSignature {
                parameters: record.kernel_level_params.clone(),
                type_,
            };
            if resident.is_some_and(|info| signature.matches(info)) {
                axioms.push((name.clone(), (module.to_owned(), signature)));
                continue;
            }
        }
        disputed.push(name.clone());
    }
    let observations = &mut env.get_ext_state_mut::<ArtifactLedger>(ledger_idx()).axioms;
    observations.disputed.extend(disputed);
    observations.by_name.extend(axioms);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::export::{
        write_lean_v2_module, LeanV2ModuleDeclaration, LeanV2ModuleOptions, LeanV2Visibility,
    };
    use crate::OleanHeader;
    use clean_kernel::{ConstantOrigin, Declaration, Reducibility};

    #[test]
    fn a_private_theorem_with_a_rejected_completion_is_never_an_imported_axiom() {
        let dir = tempfile::tempdir().unwrap();
        let header = OleanHeader::parse(include_bytes!(
            "../../../../tests/fixtures/olean/v4.36.0/plain/StablePlain.olean"
        ))
        .unwrap();
        let p = Name::from_string("Record.P");
        let bad = Name::from_string("Record.bad");
        let axiom = ConstantInfo::new_with_reducibility(
            p.clone(),
            vec![],
            Expr::prop(),
            None,
            Reducibility::Opaque,
            ResidentKind::Axiom,
        );
        // The theorem's value is a sort, although its type is the axiom P.
        // The public record is a well-formed axiom stub; its completion fails.
        let theorem = ConstantInfo::new_with_reducibility(
            bad.clone(),
            vec![],
            Expr::const_(p.clone(), vec![]),
            Some(Expr::prop()),
            Reducibility::Opaque,
            ResidentKind::Theorem,
        );
        let parts = write_lean_v2_module(
            &header,
            &Name::from_string("Record"),
            &[],
            &[
                LeanV2ModuleDeclaration {
                    info: &axiom,
                    safety: DefinitionSafety::Safe,
                    all: &[],
                    visibility: LeanV2Visibility::Exported,
                    axioms: std::slice::from_ref(&p),
                },
                LeanV2ModuleDeclaration {
                    info: &theorem,
                    safety: DefinitionSafety::Safe,
                    all: std::slice::from_ref(&bad),
                    visibility: LeanV2Visibility::ExportedAsAxiom,
                    axioms: std::slice::from_ref(&p),
                },
            ],
            LeanV2ModuleOptions {
                is_module: true,
                namespaces: &[],
                emit_ir: false,
            },
        )
        .unwrap();
        for (extension, bytes) in [
            ("olean", parts.base),
            ("olean.server", parts.server.unwrap()),
            ("olean.private", parts.private.unwrap()),
        ] {
            std::fs::write(dir.path().join(format!("Record.{extension}")), bytes).unwrap();
        }
        let mut env = Environment::for_lean_replay();
        crate::declare_environment_world(&mut env, "v4.36.0").unwrap();
        let summaries =
            crate::load_module_with_deps(&mut env, "Record", &[dir.path().to_owned()]).unwrap();
        assert!(summaries
            .iter()
            .any(|s| s.refused_completions.iter().any(|(n, _)| n == &bad)));
        assert_eq!(env.get_const(&bad).unwrap().kind, ResidentKind::Axiom);
        assert!(is_authoritative_lean_axiom(&env, &p));
        assert!(!is_authoritative_lean_axiom(&env, &bad));

        let mut wrong_origin = env.clone();
        assert!(wrong_origin.set_constant_origin(
            p.clone(),
            ConstantOrigin::clean_payload(Some("Record".into()))
        ));
        assert!(!is_authoritative_lean_axiom(&wrong_origin, &p));
        // An identical-looking locally installed replacement is not the imported record.
        let mut replaced = env.clone();
        assert!(replaced.forget_decl(&p));
        replaced
            .add_decl(Declaration::Axiom {
                name: p.clone(),
                level_params: vec![],
                type_: Expr::prop(),
            })
            .unwrap();
        replaced.set_constant_origin(
            p.clone(),
            ConstantOrigin::olean_import(Some("Record".into())),
        );
        assert_eq!(
            lean_declaration_artifact(&replaced, &p).as_deref(),
            Some("Record")
        );
        assert!(!is_authoritative_lean_axiom(&replaced, &p));

        assert!(env.forget_decl(&p));
        env.add_decl(Declaration::Axiom {
            name: p.clone(),
            level_params: vec![],
            type_: Expr::type_(),
        })
        .unwrap();
        env.set_constant_origin(
            p.clone(),
            ConstantOrigin::olean_import(Some("Record".into())),
        );
        assert_eq!(
            lean_declaration_artifact(&env, &p).as_deref(),
            Some("Record")
        );
        assert!(!is_authoritative_lean_axiom(&env, &p));
    }
}
