// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Independently replay a library-only source baseline. Model artifacts are
//! dependency hints, never declarations installed in this baseline.
use super::custody::{captured_optional as optional, validate_artifact_census};
use super::{hash, load_expected, Manifest};
use crate::expr::ParsedExpr;
use crate::import::parse_module;
use clean_kernel::{Environment, Name, ReferenceKernel};
use serde_json::Value;
use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

/// Original-reference checked declarations from an independently loaded exact
/// module cohort. There is no constructor from an Environment or public report.
/// Its fixed caller must still authenticate the manifest and source identity.
pub struct CheckedSourceContext {
    kernel: ReferenceKernel,
    environment: Environment,
    identity: String,
    modules: BTreeSet<String>,
    roots: BTreeSet<Name>,
}

impl CheckedSourceContext {
    pub fn environment(&self) -> &Environment {
        &self.environment
    }
    pub fn identity(&self) -> &str {
        &self.identity
    }
    pub fn modules(&self) -> &BTreeSet<String> {
        &self.modules
    }
    pub fn roots(&self) -> &BTreeSet<Name> {
        &self.roots
    }
    pub fn reference_digest(&self) -> clean_kernel::EnvDigest {
        self.kernel.env_digest()
    }
}

/// Imported elaboration records are untrusted suggestions over declarations
/// already admitted by the reference entry. They add no mathematical record,
/// reducer, verification stamp, lazy provider or model declaration.
fn elaboration_metadata(
    imported: &Environment,
    checked: &Environment,
) -> Result<Environment, String> {
    let mut environment = checked.clone();
    for info in checked.constants() {
        let name = &info.name;
        if let (Some(names), Some(kinds)) = (
            imported.get_typed_param_names(name),
            imported.get_param_binder_infos(name),
        ) {
            if names.len() != kinds.len() {
                return Err(format!("incomplete captured binder metadata: {name}"));
            }
            environment
                .add_checked_param_infos(
                    name,
                    names.iter().cloned().zip(kinds.iter().copied()).collect(),
                    false,
                )
                .map_err(|error| error.to_string())?;
        }
        if let Some(fields) = imported.get_structure_field_names(name) {
            environment
                .register_structure_fields(name.clone(), fields.to_vec())
                .map_err(|error| error.to_string())?;
        }
        if let Some(parents) = imported.get_structure_parents(name) {
            environment.register_structure_parents(name.clone(), parents.to_vec());
        }
        if let Some(binders) = imported.get_value_forall_binder_names(name) {
            environment.record_value_forall_binder_names(
                name.clone(),
                binders.lambdas,
                binders.names.clone(),
            );
        }
        if let Some(class) = imported.get_class_info(name) {
            environment.register_class(class.clone());
        }
        if let Some(lemma) = imported.get_simp_lemma(name) {
            environment.register_simp_lemma(name.clone(), lemma.priority);
        }
    }
    let mut classes = imported.classes().collect::<Vec<_>>();
    classes.sort_by(|left, right| left.name.cmp(&right.name));
    for class in classes {
        if checked.get_const(&class.name).is_none() {
            continue;
        }
        // Registry insertion is newest-first. Replay the recorded vector in
        // reverse so equal-priority source resolution keeps its exact order.
        for instance in imported.get_class_instances(&class.name).iter().rev() {
            if checked.get_const(&instance.name).is_some() {
                environment.register_instance(instance.clone());
                if imported.is_local_instance(&instance.name) {
                    environment.mark_local_instance(instance.name.clone());
                }

                if let Some(order) = imported.get_instance_synth_order(&instance.name) {
                    environment.set_instance_synth_order(instance.name.clone(), order.to_vec());
                }
            }
        }
    }
    // Global, scoped and local entries have different visibility in Lean.
    // Project only instance records for admitted names into this context,
    // preserving the import order of namespace activation.
    let scope_index = crate::scoped_instance_idx();
    if let Some(scoped) = imported.get_ext_state::<crate::ScopedInstanceState>(scope_index) {
        let mut selected = crate::ScopedInstanceState::default();
        selected.scope_of.extend(
            scoped
                .scope_of
                .iter()
                .filter(|(instance, _)| environment.is_instance(instance))
                .map(|(instance, namespace)| (instance.clone(), namespace.clone())),
        );
        selected.entries.extend(
            scoped
                .entries
                .iter()
                .filter(|(_, instance, _)| environment.is_instance(instance))
                .cloned(),
        );
        *environment.get_ext_state_mut::<crate::ScopedInstanceState>(scope_index) = selected;
    }
    // Lean source can name an exported declaration without its namespace
    // (for example, Init exports Decidable.decide as decide). Preserve the
    // complete original candidate list, or omit the alias: filtering out one
    // target of an ambiguous name could silently change name resolution.
    let aliases: BTreeSet<_> = imported
        .export_alias_pairs()
        .map(|(alias, _)| alias)
        .collect();
    for alias in aliases {
        let targets = imported.export_alias_targets(alias);
        if targets
            .iter()
            .all(|target| checked.get_const(target).is_some())
        {
            for target in targets {
                environment.register_export_alias(alias.clone(), target.clone());
            }
        }
    }
    for info in checked.constants() {
        let name = &info.name;
        if environment.get_const(name) != checked.get_const(name)
            || environment.get_inductive(name) != checked.get_inductive(name)
            || environment.get_constructor(name) != checked.get_constructor(name)
            || environment.get_recursor(name) != checked.get_recursor(name)
            || environment.get_quot(name) != checked.get_quot(name)
        {
            return Err(format!(
                "elaboration metadata changed an admitted mathematical payload: {name}"
            ));
        }
    }
    if environment.num_constants() != checked.num_constants() {
        return Err("elaboration metadata added mathematical declarations".into());
    }
    for quotient in checked.quotients() {
        if environment.get_quot(&quotient.name) != Some(quotient) {
            return Err(format!(
                "elaboration metadata changed original quotient payload: {}",
                quotient.name
            ));
        }
    }
    Ok(environment)
}

fn module_path(directory: &Path, name: &str) -> Result<PathBuf, String> {
    if name.split('.').any(|part| {
        part.is_empty()
            || !part
                .bytes()
                .all(|byte| byte.is_ascii_alphanumeric() || byte == b'_')
    }) {
        return Err("invalid fixed source module identity".into());
    }
    let path = directory.join(name.replace('.', "/") + ".olean");
    if path.canonicalize().map_err(|error| error.to_string())? != path {
        return Err("fixed source hint path or symlink differs".into());
    }
    Ok(path)
}

fn used(expr: &ParsedExpr, names: &mut BTreeSet<String>) {
    let mut pending = vec![expr];
    while let Some(expr) = pending.pop() {
        match expr {
            ParsedExpr::Const(name, _) => {
                names.insert(name.clone());
            }
            ParsedExpr::Proj(owner, _, value) => {
                names.insert(owner.clone());
                pending.push(value);
            }
            ParsedExpr::App(left, right)
            | ParsedExpr::Lam(_, left, right, _)
            | ParsedExpr::ForallE(_, left, right, _) => {
                pending.push(left);
                pending.push(right);
            }
            ParsedExpr::LetE(_, ty, value, body, _) => {
                pending.push(ty);
                pending.push(value);
                pending.push(body);
            }
            ParsedExpr::MData(_, value) => pending.push(value),
            ParsedExpr::BVar(_)
            | ParsedExpr::FVar(_)
            | ParsedExpr::MVar(_)
            | ParsedExpr::Sort(_)
            | ParsedExpr::Lit(_) => {}
        }
    }
}

struct Plan {
    manifest: String,
    modules: BTreeSet<String>,
    library_imports: BTreeSet<String>,
    roots: BTreeSet<String>,
}

fn plan(directory: &Path, manifest: &str, schema: &str, sources: &[&str]) -> Result<Plan, String> {
    let expected: Manifest = serde_json::from_str(manifest).map_err(|error| error.to_string())?;
    let source_set = sources.iter().copied().collect::<BTreeSet<_>>();
    if expected.schema != schema
        || expected.lean_version != "4.30.0-rc2"
        || sources.is_empty()
        || source_set.len() != sources.len()
        || !source_set
            .iter()
            .all(|module| expected.modules.contains_key(*module))
    {
        return Err("invalid fixed source-context partition".into());
    }
    if source_set.len() == expected.modules.len() {
        return Err("empty fixed library module population".into());
    }
    // Inventory the COMPLETE original cohort, including model artifacts that
    // will deliberately remain physically present but never enter this baseline.
    validate_artifact_census(directory, &expected)?;
    // Select the exact library module population BEFORE loading an Environment.
    // No namespace-prefix predicate, declaration subtraction or loaded model is
    // used. The independent loader must later observe this complete population.
    let modules = expected
        .modules
        .keys()
        .filter(|module| !source_set.contains(module.as_str()))
        .cloned()
        .collect::<BTreeSet<_>>();
    if modules.is_empty() {
        return Err("empty fixed library module population".into());
    }
    let mut input: Value = serde_json::from_str(manifest).map_err(|error| error.to_string())?;
    let table = input["modules"]
        .as_object_mut()
        .ok_or("missing fixed module population")?;
    for module in sources {
        table.remove(*module);
    }
    let manifest = serde_json::to_string(&input).map_err(|error| error.to_string())?;
    let mut owned = BTreeSet::new();
    let mut dependencies = BTreeSet::new();
    let mut library_imports = BTreeSet::new();
    for module in sources {
        let path = module_path(directory, module)?;
        let base = optional(&path)?
            .ok_or_else(|| format!("missing captured source hint artifact: {module}"))?;
        let server = optional(&path.with_extension("olean.server"))?;
        let private = optional(&path.with_extension("olean.private"))?;
        let ir = optional(&path.with_extension("ir"))?;
        let wanted = &expected.modules[*module];
        if hash(&base) != wanted.base
            || server.as_deref().map(hash) != wanted.server
            || private.as_deref().map(hash) != wanted.private
            || ir.as_deref().map(hash) != wanted.ir
        {
            return Err(format!(
                "captured source hint module bytes differ: {module}"
            ));
        }
        // Current fixed model artifacts are classic, base-only exports. Do not
        // silently omit declarations if a future producer introduces companions.
        if server.is_some() || private.is_some() {
            return Err("source-context dependency hints require complete multipart parsing; no companion is omitted".into());
        }
        let parsed = parse_module(&base).map_err(|error| error.to_string())?;
        if parsed.clean_payload.is_some() {
            return Err("source hints must be original Lean artifacts".into());
        }
        for import in parsed.imports {
            if source_set.contains(import.module_name.as_str()) {
                continue;
            }
            if !modules.contains(&import.module_name) {
                return Err(format!(
                    "source hint imports an unmanifested library module: {}",
                    import.module_name
                ));
            }
            library_imports.insert(import.module_name);
        }
        owned.extend(parsed.const_names);
        owned.extend(parsed.extra_const_names);
        for constant in parsed.constants {
            owned.insert(constant.name);
            if let Some(expr) = constant.type_ {
                used(&expr, &mut dependencies);
            }
            if let Some(expr) = constant.value {
                used(&expr, &mut dependencies);
            }
            if let Some(recursor) = constant.recursor_val {
                for rule in recursor.rules {
                    if let Some(expr) = rule.rhs {
                        used(&expr, &mut dependencies);
                    }
                }
            }
        }
    }
    dependencies.retain(|name| !owned.contains(name));
    if library_imports.is_empty() {
        // Classic Lean modules carry their actual implicit Init dependency.
        // Absence is a refusal, never an invented prelude or ambient search.
        return Err("fixed source hints contain no captured library import".into());
    }
    if dependencies.is_empty() {
        return Err("fixed source hints contain no library declaration dependencies".into());
    }
    Ok(Plan {
        manifest,
        modules,
        library_imports,
        roots: dependencies,
    })
}

/// Build an unbound checked library context from an authenticated fixed cohort.
/// Every source module is excluded before any Environment load. Its exact
/// artifact bytes supply dependency hints only; all baseline declarations come
/// from the separate library module graph and earn original closed replay.
/// The caller must still perform the unchanged complete model cohort replay,
/// original source checking and source-payload comparison.
pub fn open_source_context(
    directory: &Path,
    manifest: &str,
    schema: &str,
    source_modules: &[&str],
    elaboration_roots: &[&str],
) -> Result<CheckedSourceContext, String> {
    let directory = directory
        .canonicalize()
        .map_err(|error| error.to_string())?;
    let mut planned = plan(&directory, manifest, schema, source_modules)?;
    planned
        .roots
        .extend(elaboration_roots.iter().map(|name| (*name).to_owned()));
    let imports = planned
        .library_imports
        .iter()
        .map(String::as_str)
        .collect::<Vec<_>>();
    let roots = planned.roots.iter().map(String::as_str).collect::<Vec<_>>();
    let expected: Manifest =
        serde_json::from_str(&planned.manifest).map_err(|error| error.to_string())?;
    let imported = load_expected(&directory, &expected, &imports)?;
    let root_names = roots
        .iter()
        .map(|name| Name::from_string(name))
        .collect::<BTreeSet<_>>();
    let options = crate::recheck_closed::ClosedRecheckOptions {
        max_closure: Some(100_000),
        ..crate::recheck_closed::ClosedRecheckOptions::default()
    };
    let reference = crate::reference_base_closed(&imported, &root_names, &options)
        .map_err(|error| error.to_string())?;
    let kernel = reference
        .into_kernel()
        .map_err(|report| report.verdict_sentence())?;
    let environment = elaboration_metadata(&imported, kernel.environment())?;
    let identity = serde_json::json!({"kind":"clean.fixed-source-context.v1", "cohort":hash(manifest.as_bytes()), "sources":source_modules, "library_manifest":hash(planned.manifest.as_bytes()), "roots":planned.roots, "reference":format!("{:?}",kernel.env_digest()), "environment":format!("{:?}",environment.content_digest())});
    Ok(CheckedSourceContext {
        kernel,
        environment,
        identity: hash(
            serde_json::to_string(&identity)
                .map_err(|error| error.to_string())?
                .as_bytes(),
        ),
        modules: planned.modules,
        roots: root_names,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn partition_refuses_empty_duplicate_and_missing_source_members_before_io() {
        let manifest = serde_json::json!({"schema":"cohort", "ir_commit":"data", "lean_version":"4.30.0-rc2", "lean_githash":"data", "source_sha256":{}, "modules":{"Init":{"base":"data"},"Model":{"base":"data"}}}).to_string();
        for (sources, expected) in [
            (vec![], "invalid fixed source-context partition"),
            (
                vec!["Model", "Model"],
                "invalid fixed source-context partition",
            ),
            (vec!["Absent"], "invalid fixed source-context partition"),
            (
                vec!["Init", "Model"],
                "empty fixed library module population",
            ),
        ] {
            assert_eq!(
                plan(
                    Path::new("/missing-library-data"),
                    &manifest,
                    "cohort",
                    &sources
                )
                .err()
                .as_deref(),
                Some(expected)
            );
        }
    }
    #[test]
    fn hint_dependency_walk_retains_projection_owners_and_nested_terms() {
        let expr = ParsedExpr::Proj(
            "Owned.Record".into(),
            0,
            Box::new(ParsedExpr::App(
                Box::new(ParsedExpr::Const("Library.call".into(), vec![])),
                Box::new(ParsedExpr::Const("Library.argument".into(), vec![])),
            )),
        );
        let mut names = BTreeSet::new();
        used(&expr, &mut names);
        assert_eq!(
            names,
            BTreeSet::from([
                "Owned.Record".into(),
                "Library.call".into(),
                "Library.argument".into()
            ])
        );
    }
    #[test]
    fn field_tables_follow_their_admitted_structure_owners() {
        use clean_kernel::env::EnvError;
        use clean_kernel::inductive::{Constructor, InductiveDecl, InductiveType};
        use clean_kernel::Expr;

        let name = Name::from_string;
        let left = name("Left.Pair");
        let right = name("Right.Pair");
        let omitted = name("Omitted.Pair");
        let tables = [
            (left.clone(), [name("leftOnly"), name("shared")]),
            (right.clone(), [name("shared"), name("rightOnly")]),
            (omitted.clone(), [name("one"), name("two")]),
        ];
        let mut imported = Environment::for_lean_replay();
        for (owner, fields) in &tables {
            let result = Expr::const_(owner.clone(), vec![]);
            imported
                .add_inductive_core(InductiveDecl {
                    level_params: vec![],
                    num_params: 0,
                    types: vec![InductiveType {
                        name: owner.clone(),
                        type_: Expr::type_(),
                        constructors: vec![Constructor {
                            name: owner.clone().str("mk"),
                            type_: Expr::arrow(Expr::prop(), Expr::arrow(Expr::prop(), result)),
                        }],
                    }],
                })
                .unwrap();
            imported
                .register_structure_fields(owner.clone(), fields.to_vec())
                .unwrap();
        }

        let roots = BTreeSet::from([left.clone(), right.clone()]);
        let kernel = crate::reference_base_closed(&imported, &roots, &Default::default())
            .unwrap()
            .into_kernel()
            .unwrap();
        let reference = kernel.environment();
        let mut projected = elaboration_metadata(&imported, reference).unwrap();

        for (owner, fields) in &tables[..2] {
            assert_eq!(
                projected.get_structure_field_names(owner),
                Some(fields.as_slice())
            );
            assert!(reference.get_structure_field_names(owner).is_none());
            assert_eq!(
                projected.get_inductive(owner),
                reference.get_inductive(owner)
            );
        }
        assert!(projected
            .get_structure_field_index(&left, &name("rightOnly"))
            .is_none());
        assert!(projected.get_structure_field_names(&omitted).is_none());
        assert!(projected.get_const(&omitted).is_none());
        let imported_fields = imported.get_structure_field_names(&omitted).unwrap();
        assert!(matches!(
            projected.register_structure_fields(omitted.clone(), imported_fields.to_vec()),
            Err(EnvError::UnknownInductive(owner)) if owner == omitted
        ));
    }

    #[test]
    fn only_admitted_instance_entries_keep_their_lean_visibility() {
        use clean_kernel::env::{Declaration, KernelClassInfo, KernelInstanceInfo};
        use clean_kernel::{Expr, Level};
        let name = Name::from_string;
        let class = name("Carrier");
        let namespace = name("Domain");
        let mut kernel = ReferenceKernel::new(Environment::for_lean_replay()).unwrap();
        let one = Level::succ(Level::zero());
        kernel
            .add_checked(Declaration::Definition {
                name: class.clone(),
                level_params: vec![],
                type_: Expr::sort(Level::succ(one.clone())),
                value: Expr::sort(one),
                is_reducible: true,
            })
            .unwrap();
        let definition = |label: &str| Declaration::Definition {
            name: name(label),
            level_params: vec![],
            type_: Expr::const_(class.clone(), vec![]),
            value: Expr::sort(Level::zero()),
            is_reducible: true,
        };
        for label in ["scoped", "localOnly", "global"] {
            kernel.add_checked(definition(label)).unwrap();
        }
        let mut imported = kernel.environment().clone();
        imported.add_decl(definition("omitted")).unwrap();
        imported.register_class(KernelClassInfo {
            name: class.clone(),
            num_params: 0,
            out_params: vec![],
            semi_out_params: vec![],
        });
        for label in ["scoped", "localOnly", "global", "omitted"] {
            imported.register_instance(KernelInstanceInfo {
                name: name(label),
                class_name: class.clone(),
                priority: 900,
                type_: None,
                value: None,
            });
        }
        imported.mark_local_instance(name("localOnly"));
        let idx = crate::scoped_instance_idx();
        let scope = imported.get_ext_state_mut::<crate::ScopedInstanceState>(idx);
        for label in ["scoped", "omitted"] {
            scope.scope_of.insert(name(label), namespace.clone());
        }
        for (label, prio) in [("scoped", 850), ("omitted", 950), ("scoped", 900)] {
            scope.entries.push((namespace.clone(), name(label), prio));
        }
        let checked = elaboration_metadata(&imported, kernel.environment()).unwrap();
        assert!(crate::import::has_global_instance_entry(
            &checked,
            &name("global")
        ));
        assert!(checked.is_local_instance(&name("localOnly")));
        for label in ["scoped", "localOnly", "omitted"] {
            assert!(!crate::import::has_global_instance_entry(
                &checked,
                &name(label)
            ));
        }
        assert!(!checked.is_instance(&name("omitted")));
        let visible = checked
            .get_ext_state::<crate::ScopedInstanceState>(idx)
            .unwrap();
        assert_eq!(visible.scope_of.len(), 1);
        assert_eq!(visible.scope_of.get(&name("scoped")), Some(&namespace));
        assert_eq!(
            visible.entries,
            vec![
                (namespace.clone(), name("scoped"), 850),
                (namespace, name("scoped"), 900)
            ]
        );
    }

    #[test]
    fn imported_metadata_cannot_make_an_unadmitted_mathematical_record_citable() {
        use clean_kernel::env::{Declaration, KernelClassInfo};
        use clean_kernel::{Expr, Level};
        let mut kernel =
            ReferenceKernel::new(Environment::for_lean_replay()).expect("empty original entry");
        let declaration = |name: &str| Declaration::Definition {
            name: Name::from_string(name),
            level_params: vec![],
            type_: Expr::sort(Level::succ(Level::zero())),
            value: Expr::sort(Level::zero()),
            is_reducible: true,
        };
        kernel
            .add_checked(declaration("Admitted"))
            .expect("actual original-kernel admission");
        kernel
            .add_checked(declaration("OtherAdmitted"))
            .expect("second original-kernel admission");
        let mut imported = kernel.environment().clone();
        imported
            .add_decl(declaration("Unadmitted"))
            .expect("untrusted producer data");
        for (alias, target) in [
            ("short", "Admitted"),
            ("ambiguous", "OtherAdmitted"),
            ("ambiguous", "Admitted"),
            ("partial", "Admitted"),
            ("partial", "Unadmitted"),
            ("unavailable", "Unadmitted"),
        ] {
            imported.register_export_alias(Name::from_string(alias), Name::from_string(target));
        }
        imported.register_class(KernelClassInfo {
            name: Name::from_string("Unadmitted"),
            num_params: 0,
            out_params: vec![],
            semi_out_params: vec![],
        });
        let context = elaboration_metadata(&imported, kernel.environment())
            .expect("read-only metadata projection");
        let admitted = Name::from_string("Admitted");
        let other = Name::from_string("OtherAdmitted");
        assert_eq!(
            context.export_alias_targets(&Name::from_string("short")),
            [&admitted]
        );
        assert_eq!(
            context.export_alias_targets(&Name::from_string("ambiguous")),
            [&other, &admitted]
        );
        for withheld in ["partial", "unavailable"] {
            assert!(context
                .export_alias_targets(&Name::from_string(withheld))
                .is_empty());
        }
        assert!(context.get_const(&Name::from_string("short")).is_none());
        assert_eq!(
            context.get_const(&Name::from_string("Admitted")),
            kernel
                .environment()
                .get_const(&Name::from_string("Admitted"))
        );
        assert!(context
            .get_const(&Name::from_string("Unadmitted"))
            .is_none());
        assert!(context
            .get_class_info(&Name::from_string("Unadmitted"))
            .is_none());
        assert_eq!(
            context.num_constants(),
            kernel.environment().num_constants()
        );
    }
}
