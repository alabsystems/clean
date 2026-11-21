// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Make native Lean v2 records from checked source declarations.

use std::collections::HashSet;

use clean_kernel::env::{
    is_trust_marker, ConstantInfo, ConstantKind, ConstantOrigin, DeclarationVerification,
    KernelTheory, OriginTrust,
};
use clean_kernel::expr::UsedConstants;
use clean_kernel::name::NameInner;
use clean_kernel::{Environment, Name, QuotKind};
use clean_olean::export::{
    write_lean_v2_module, LeanV2ModuleDeclaration, LeanV2ModuleOptions, LeanV2ModuleParts,
    LeanV2Visibility,
};
use clean_olean::import::{is_authoritative_lean_axiom, lean_declaration_artifact};
use clean_olean::{DefinitionSafety, OleanHeader, TypedImport, TypedImportFlags};
use clean_parser::{DeclModifiers, DeclScope, FileHeader, SurfaceDecl, Visibility};

use crate::print_axioms::used_constants_in_order;
use crate::ElabError;

/// The import boundary and source features of a module destined for native
/// Lean 4.36 output. The driver owns elaboration diagnostics and import
/// admission. Export consumes this capture only after that driver succeeds.
pub struct CheckedLeanV2Source {
    baseline: HashSet<Name>,
    families: HashSet<Name>,
    namespaces: HashSet<Name>,
    expected: Option<DeclarationCounts>,
}

#[derive(Clone, Copy, Default, PartialEq, Eq)]
struct DeclarationCounts {
    axioms: usize,
    theorems: usize,
}

impl CheckedLeanV2Source {
    /// Remember the constants and namespaces after imports and ambient setup,
    /// immediately before elaborating the module body.
    #[must_use]
    pub fn capture(env: &Environment) -> Self {
        Self {
            baseline: env.constants().map(|info| info.name.clone()).collect(),
            families: kernel_family_names(env).cloned().collect(),
            namespaces: env.registered_namespaces().cloned().collect(),
            expected: None,
        }
    }

    /// Inspect the full parsed source so registration that lives outside the
    /// kernel declaration table cannot be dropped during serialization.
    ///
    /// # Errors
    /// Refuses source commands whose persistent effects this writer cannot
    /// represent.
    pub fn observe_source(&mut self, decls: &[SurfaceDecl]) -> Result<(), ElabError> {
        self.expected = None;
        let mut expected = DeclarationCounts::default();
        observe_decls(decls, &mut expected)?;
        self.expected = Some(expected);
        Ok(())
    }

    /// Serialize the declaration delta and source import order for this file.
    ///
    /// # Errors
    /// Refuses unobserved source, incomplete checked declarations or axiom
    /// closures, and records the native writer cannot express.
    pub fn export(
        self,
        env: &Environment,
        header: &FileHeader,
        target: &OleanHeader,
        module: &Name,
    ) -> Result<LeanV2ModuleParts, ElabError> {
        if env.kernel_theory() != KernelTheory::LeanReference {
            return Err(unsupported(
                "proof export requires the Lean reference kernel theory",
            ));
        }
        let expected = self
            .expected
            .ok_or_else(|| unsupported("the parsed module body was not observed"))?;
        self.refuse_new_kernel_families(env)?;
        let mut source: Vec<_> = env
            .constants()
            .filter(|info| !self.baseline.contains(&info.name))
            .collect();
        source.sort_unstable_by(|left, right| left.name.cmp(&right.name));

        let mut actual = DeclarationCounts::default();
        for info in &source {
            match (&info.kind, &info.value) {
                (ConstantKind::Axiom, None) => actual.axioms += 1,
                (ConstantKind::Theorem, Some(_)) => actual.theorems += 1,
                _ => {
                    return Err(unsupported(format!(
                        "declaration `{}` has no supported native record",
                        info.name
                    )));
                }
            }
            require_checked_local(env, info)?;
            self.require_native_references(env, header, info)?;
        }
        if expected != actual {
            return Err(unsupported(
                "the checked declarations do not match the observed source axioms and theorems",
            ));
        }

        let mut namespaces: HashSet<_> = env
            .registered_namespaces()
            .filter(|name| !self.namespaces.contains(*name))
            .cloned()
            .collect();
        for info in &source {
            add_name_prefixes(&mut namespaces, &self.namespaces, &info.name);
        }
        let namespaces: Vec<_> = namespaces.into_iter().collect();

        // Even the private rows need a genuine dependency cone. The writer
        // emits the resulting summary only where Lean records those entries.
        let axioms: Vec<_> = source
            .iter()
            .map(|info| self.axiom_closure(env, &info.name, header))
            .collect::<Result<_, _>>()?;
        let declarations: Vec<_> = source
            .into_iter()
            .zip(&axioms)
            .map(|(info, axioms)| LeanV2ModuleDeclaration {
                info,
                safety: if env.is_unsafe(&info.name) {
                    DefinitionSafety::Unsafe
                } else {
                    DefinitionSafety::Safe
                },
                all: if info.kind == ConstantKind::Theorem {
                    std::slice::from_ref(&info.name)
                } else {
                    &[]
                },
                visibility: if header.is_module && env.is_private(&info.name) {
                    LeanV2Visibility::Private
                } else if header.is_module && info.kind == ConstantKind::Theorem {
                    LeanV2Visibility::ExportedAsAxiom
                } else {
                    LeanV2Visibility::Exported
                },
                axioms,
            })
            .collect();

        write_lean_v2_module(
            target,
            module,
            &typed_imports(header),
            &declarations,
            LeanV2ModuleOptions {
                is_module: header.is_module,
                namespaces: &namespaces,
                emit_ir: header.is_module,
            },
        )
        .map_err(|error| unsupported(error.to_string()))
    }

    fn refuse_new_kernel_families(&self, env: &Environment) -> Result<(), ElabError> {
        if let Some(name) = kernel_family_names(env)
            .filter(|name| !self.families.contains(*name))
            .min()
        {
            return Err(unsupported(format!(
                "kernel family member `{name}` requires a native record"
            )));
        }
        Ok(())
    }

    fn require_native_references(
        &self,
        env: &Environment,
        header: &FileHeader,
        info: &ConstantInfo,
    ) -> Result<(), ElabError> {
        let public = header.is_module && !env.is_private(&info.name);
        let mut references = HashSet::new();
        info.type_
            .used_constants_dag(UsedConstants::WithProjectionStructures, &mut references);
        for name in &references {
            if public && (env.is_private(name) || crate::private_names::is_private_name(name)) {
                return Err(unsupported(format!(
                    "public signature of `{}` refers to private declaration `{name}`",
                    info.name
                )));
            }
            if public && !self.has_public_signature_dependency(env, header, name) {
                return Err(unsupported(format!(
                    "public signature of `{}` has no public import evidence for `{name}`",
                    info.name
                )));
            }
        }
        if let Some(value) = &info.value {
            value.used_constants_dag(UsedConstants::WithProjectionStructures, &mut references);
        }
        // Lean's axiom census skips projection structure names. Check their
        // availability as well because Lean needs them to type the proof.
        for name in references {
            if env.get_const(&name).is_none() || !self.dependency_in_imports(env, header, &name) {
                return Err(unsupported(format!(
                    "no native declaration supplies `{name}`, used by `{}`",
                    info.name
                )));
            }
        }
        Ok(())
    }

    fn has_public_signature_dependency(
        &self,
        env: &Environment,
        header: &FileHeader,
        name: &Name,
    ) -> bool {
        if header.imports.is_empty()
            || (!self.baseline.contains(name) && !self.families.contains(name))
            || env
                .get_quot(name)
                .is_some_and(|q| q.kind != QuotKind::Sound)
        {
            return true;
        }
        let Some(owner) = lean_declaration_artifact(env, name) else {
            return false;
        };
        // The import ledger exposes display labels. A dotted label can name
        // either a nested module or a single quoted component, so it cannot
        // establish typed module ownership. Transitive visibility also needs
        // a public-edge path that the declaration origin does not record.
        !owner.contains('.')
            && ((!header.is_prelude && owner == "Init")
                || header.imports.iter().any(|import| {
                    import.is_exported
                        && matches!(
                            import.module.name().inner(),
                            NameInner::Str(parent, label)
                                if parent.is_anon() && label.as_ref() == owner.as_str()
                        )
                }))
    }

    fn dependency_in_imports(&self, env: &Environment, header: &FileHeader, name: &Name) -> bool {
        if !self.baseline.contains(name) && !self.families.contains(name) {
            return true;
        }
        // This is Lean's kernel-owned quotient primitive set. `Quot.sound`
        // is an ordinary axiom and must come from an actual artifact.
        (env.get_quot(name)
            .is_some_and(|q| q.kind != QuotKind::Sound)
            && (!header.is_prelude || !header.imports.is_empty()))
            || lean_declaration_artifact(env, name).is_some()
    }

    fn axiom_closure(
        &self,
        env: &Environment,
        root: &Name,
        header: &FileHeader,
    ) -> Result<Vec<Name>, ElabError> {
        let mut pending = vec![root.clone()];
        let mut visited = HashSet::new();
        let mut axioms = Vec::new();
        let sorry_ax = Name::from_string("sorryAx");
        while let Some(name) = pending.pop() {
            if !visited.insert(name.clone()) {
                continue;
            }
            let unavailable = |reason: &str| {
                unsupported(format!("cannot export `{root}` through `{name}`: {reason}"))
            };
            let quotient = env.get_quot(&name);
            if is_trust_marker(&name) && name != sorry_ax {
                return Err(unavailable("the dependency is a Clean trust marker"));
            }
            let info = env.get_const(&name);
            if quotient.is_none()
                && self.baseline.contains(&name)
                && info.is_some_and(|info| info.kind == ConstantKind::Axiom)
                && !is_authoritative_lean_axiom(env, &name)
            {
                // A refused completion can leave an imported theorem's axiom
                // stub resident. Only the original authoritative record can
                // distinguish that stub from a genuine imported axiom.
                return Err(unavailable(
                    "the import does not establish whether this is an axiom or a proof stub",
                ));
            }
            if !self.dependency_in_imports(env, header, &name) {
                return Err(unavailable("no Lean import supplies this dependency"));
            }
            if let Some(quotient) = quotient {
                // Lean represents `Quot.sound` as an axiom and the other
                // quotient symbols as primitive QuotInfo entries.
                if quotient.kind == QuotKind::Sound {
                    pending.extend(used_constants_in_order(&quotient.type_));
                    axioms.push(name);
                }
                continue;
            }
            if let Some(inductive) = env.get_inductive(&name) {
                pending.extend(used_constants_in_order(&inductive.type_));
                pending.extend(inductive.constructor_names.iter().cloned());
                continue;
            }
            if let Some(constructor) = env.get_constructor(&name) {
                pending.extend(used_constants_in_order(&constructor.type_));
                continue;
            }
            let info = info.ok_or_else(|| unavailable("its declaration is missing"))?;
            match (&info.kind, &info.value) {
                (ConstantKind::Axiom, None) => {
                    pending.extend(used_constants_in_order(&info.type_));
                    axioms.push(name);
                }
                (
                    ConstantKind::Definition | ConstantKind::Theorem | ConstantKind::Opaque,
                    Some(value),
                ) => {
                    // A value-bearing `casesOn` or `recOn` can also be in
                    // Clean's recursor registry. Lean's record is a definition.
                    pending.extend(used_constants_in_order(&info.type_));
                    pending.extend(used_constants_in_order(value));
                }
                (ConstantKind::Definition, None) if env.get_recursor(&name).is_some() => {
                    pending.extend(used_constants_in_order(&info.type_));
                }
                _ => return Err(unavailable("its checked value was not retained")),
            }
        }
        Ok(axioms)
    }
}

fn kernel_family_names(env: &Environment) -> impl Iterator<Item = &Name> {
    env.inductives()
        .map(|val| &val.name)
        .chain(env.constructors().map(|val| &val.name))
        .chain(env.recursors().map(|val| &val.name))
        .chain(env.quotients().map(|val| &val.name))
}

fn require_checked_local(env: &Environment, info: &ConstantInfo) -> Result<(), ElabError> {
    let name = &info.name;
    if env.declaration_verification(name) != Some(DeclarationVerification::FullKernelCheck)
        || env.get_constant_origin(name)
            != Some(&ConstantOrigin::Kernel {
                trust: OriginTrust::KernelChecked,
            })
    {
        return Err(unsupported(format!(
            "declaration `{name}` lacks local full kernel-check evidence"
        )));
    }
    if env.is_partial(name)
        || env.is_protected(name)
        || env.is_noncomputable(name)
        || (info.kind == ConstantKind::Theorem && env.is_unsafe(name))
    {
        return Err(unsupported(format!(
            "declaration `{name}` has unsupported native metadata"
        )));
    }
    if info.type_.has_synthetic_sorry()
        || info
            .value
            .as_ref()
            .is_some_and(|value| value.has_synthetic_sorry())
    {
        return Err(unsupported(format!(
            "declaration `{name}` contains a synthetic sorry"
        )));
    }
    Ok(())
}

fn observe_decls(decls: &[SurfaceDecl], expected: &mut DeclarationCounts) -> Result<(), ElabError> {
    for decl in decls {
        match decl {
            SurfaceDecl::Axiom {
                name,
                attrs,
                modifiers,
                ..
            } => {
                require_supported_modifiers(name.name(), attrs.is_empty(), modifiers)?;
                expected.axioms += 1;
            }
            SurfaceDecl::Theorem {
                name,
                attrs,
                modifiers,
                where_decls,
                ..
            } => {
                require_supported_modifiers(name.name(), attrs.is_empty(), modifiers)?;
                if !where_decls.is_empty() {
                    return Err(unsupported(format!(
                        "theorem `{name}` has declarations in its `where` clause"
                    )));
                }
                expected.theorems += 1;
            }
            SurfaceDecl::Namespace { decls, .. } | SurfaceDecl::Section { decls, .. } => {
                observe_decls(decls, expected)?;
            }
            SurfaceDecl::Open { body, .. } => {
                if let Some(body) = body {
                    observe_decls(std::slice::from_ref(body.as_ref()), expected)?;
                }
            }
            SurfaceDecl::Import { .. }
            | SurfaceDecl::Prelude { .. }
            | SurfaceDecl::Check { .. }
            | SurfaceDecl::Print { .. }
            | SurfaceDecl::PrintAxioms { .. }
            | SurfaceDecl::Example { .. }
            | SurfaceDecl::UniverseDecl { .. }
            | SurfaceDecl::Variable { .. }
            | SurfaceDecl::IncludeVars { .. }
            | SurfaceDecl::OmitVars { .. } => {}
            _ => {
                let span = decl.span();
                return Err(unsupported(format!(
                    "the command at byte {} needs unsupported native metadata or code",
                    span.start
                )));
            }
        }
    }
    Ok(())
}

fn require_supported_modifiers(
    name: &Name,
    no_attributes: bool,
    modifiers: &DeclModifiers,
) -> Result<(), ElabError> {
    if !no_attributes
        || modifiers.visibility == Visibility::Protected
        || modifiers.scope != DeclScope::Default
        || modifiers.is_partial
        || modifiers.is_noncomputable
        || modifiers.is_abbrev
    {
        return Err(unsupported(format!(
            "declaration `{name}` has unsupported modifiers or attributes"
        )));
    }
    Ok(())
}

fn add_name_prefixes(namespaces: &mut HashSet<Name>, imported: &HashSet<Name>, name: &Name) {
    let user = crate::private_names::private_to_user_name(name);
    let name = user.as_ref().unwrap_or(name);
    let NameInner::Str(parent, component) = name.inner() else {
        return;
    };
    if component.starts_with('_') || !is_string_namespace(parent) {
        return;
    }
    let mut parent = parent.as_ref();
    while let NameInner::Str(next, _) = parent.inner() {
        if !imported.contains(parent) {
            namespaces.insert(parent.clone());
        }
        parent = next;
    }
}

fn is_string_namespace(mut name: &Name) -> bool {
    loop {
        match name.inner() {
            NameInner::Anon => return true,
            NameInner::Str(parent, _) => name = parent,
            NameInner::Num(_, _) => return false,
        }
    }
}

fn typed_imports(header: &FileHeader) -> Vec<TypedImport> {
    let mut imports = Vec::new();
    if !header.is_prelude {
        let init = Name::from_string("Init");
        imports.extend([false, true].map(|is_meta| TypedImport {
            module_name: init.clone(),
            flags: TypedImportFlags::LeanV2 {
                import_all: false,
                is_exported: true,
                is_meta,
            },
        }));
    }
    imports.extend(header.imports.iter().map(|import| TypedImport {
        module_name: import.module.name().clone(),
        flags: TypedImportFlags::LeanV2 {
            import_all: import.import_all,
            is_exported: import.is_exported,
            is_meta: import.is_meta,
        },
    }));
    imports
}

fn unsupported(feature: impl std::fmt::Display) -> ElabError {
    ElabError::Unsupported {
        feature: format!("Lean 4.36 native output: {feature}"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::{Declaration, Expr, LeanWorld};

    #[test]
    fn typed_header_preserves_both_implicit_init_rows_and_explicit_imports() {
        let header = clean_parser::Parser::parse_header_in_world(
            "module\npublic meta import Init\nimport all Library\n",
            LeanWorld::Lean436,
        )
        .expect("valid stable module header");
        let expected = [
            ("Init", false, true, false),
            ("Init", false, true, true),
            ("Init", false, true, true),
            ("Library", true, false, false),
        ]
        .map(|(name, import_all, is_exported, is_meta)| TypedImport {
            module_name: Name::from_string(name),
            flags: TypedImportFlags::LeanV2 {
                import_all,
                is_exported,
                is_meta,
            },
        });
        assert_eq!(typed_imports(&header), expected);
    }

    #[test]
    fn an_axiom_carries_the_axioms_mentioned_in_its_type() {
        let mut env = Environment::default();
        let capture = CheckedLeanV2Source::capture(&env);
        let proposition = Name::from_string("P");
        let inhabitant = Name::from_string("H");
        for (name, type_) in [
            (proposition.clone(), Expr::prop()),
            (
                inhabitant.clone(),
                Expr::const_(proposition.clone(), vec![]),
            ),
        ] {
            env.add_decl(Declaration::Axiom {
                name,
                level_params: vec![],
                type_,
            })
            .expect("well-formed axiom");
        }
        let axioms: HashSet<_> = capture
            .axiom_closure(&env, &inhabitant, &FileHeader::default())
            .expect("complete checked axiom closure")
            .into_iter()
            .collect();
        assert_eq!(axioms, HashSet::from([proposition, inhabitant]));
    }

    #[test]
    fn an_imported_proof_stub_cannot_supply_a_local_axiom_type() {
        let mut env = Environment::default();
        let stub = Name::from_string("importedProofStub");
        env.add_decl(Declaration::Axiom {
            name: stub.clone(),
            level_params: vec![],
            type_: Expr::prop(),
        })
        .expect("resident shape of an imported proof stub");
        assert!(env.set_constant_origin(
            stub.clone(),
            ConstantOrigin::olean_import(Some("Imported".to_owned())),
        ));
        let capture = CheckedLeanV2Source::capture(&env);
        let dependent = Name::from_string("localDependentAxiom");
        env.add_decl(Declaration::Axiom {
            name: dependent.clone(),
            level_params: vec![],
            type_: Expr::const_(stub, vec![]),
        })
        .expect("well-formed local axiom over the resident stub");
        let error = capture
            .axiom_closure(&env, &dependent, &FileHeader::default())
            .expect_err("the imported stub cannot be listed as a genuine axiom");
        assert!(
            error.to_string().contains("axiom or a proof stub"),
            "{error}"
        );
    }
}
