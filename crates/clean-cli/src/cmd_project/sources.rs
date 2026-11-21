// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The project's sources and module graph: which files are modules, what
//! each imports, the import cycles, and the order Lean loads them in.

use super::*;

pub(super) fn scan_project_sources(root: &Path) -> anyhow::Result<Vec<ProjectSource>> {
    let mut sources = Vec::new();
    let walker = WalkDir::new(root)
        .sort_by_file_name()
        .into_iter()
        .filter_entry(|entry| should_descend(entry.path(), root));

    for entry in walker {
        let entry = entry?;
        if !entry.file_type().is_file() || !is_source_file(entry.path()) {
            continue;
        }
        let path = entry.path().to_path_buf();
        let relative = path
            .strip_prefix(root)
            .map(Path::to_path_buf)
            .unwrap_or_else(|_| path.clone());
        let relative_path = slash_path(&relative);
        let identity = module_identity_for_relative_path(&relative).ok_or_else(|| {
            anyhow::anyhow!(
                "module path contains a non-UTF-8 or non-relative component: {}",
                relative.display()
            )
        })?;
        let module = SurfaceName::from_name(identity.clone())
            .source_spelling()
            .unwrap_or_else(|| format!("{identity:?}"));
        let extension = path
            .extension()
            .and_then(|ext| ext.to_str())
            .unwrap_or_default()
            .to_owned();
        sources.push(ProjectSource {
            path,
            relative_path,
            module,
            identity,
            extension,
        });
    }

    sources.sort_by(|left, right| left.relative_path.cmp(&right.relative_path));
    Ok(sources)
}

pub(super) fn should_descend(path: &Path, root: &Path) -> bool {
    if path == root || !path.is_dir() {
        return true;
    }
    path.file_name()
        .and_then(|name| name.to_str())
        .is_none_or(|name| !EXCLUDED_DIRS.contains(&name))
}

pub(super) fn is_source_file(path: &Path) -> bool {
    if path.file_name().and_then(|name| name.to_str()) == Some("lakefile.lean") {
        return false;
    }
    path.extension()
        .and_then(|ext| ext.to_str())
        .is_some_and(|ext| SOURCE_EXTENSIONS.contains(&ext))
}

pub(super) fn check_project_modules(
    sources: &[ProjectSource],
    module_sources: &BTreeMap<Name, String>,
    allow_sorry: bool,
) -> Vec<ProjectModuleReport> {
    let mut parsed_modules = sources
        .iter()
        .map(|source| parse_project_module(source, module_sources))
        .collect::<Vec<_>>();

    let cycle_modules = project_module_cycles(sources, &parsed_modules);
    for idx in &cycle_modules {
        let source = &sources[*idx];
        let blocker = AuthorityBlocker::module(
            "project_import_cycle",
            &source.module,
            &source.relative_path,
            "project-local imports form a cycle; Clean project check cannot topologically load these modules as authority",
        );
        parsed_modules[*idx]
            .diagnostics
            .push(ProjectDiagnostic::from_blocker(&blocker));
        parsed_modules[*idx].authority_blockers.push(blocker);
    }

    let load_order = topological_project_module_order(sources, &parsed_modules, &cycle_modules);
    let mut checked_reports =
        check_project_modules_in_order(sources, parsed_modules, load_order, allow_sorry);
    sources
        .iter()
        .map(|source| {
            checked_reports
                .remove(&source.relative_path)
                .expect("every source should produce a module report")
        })
        .collect()
}

pub(super) fn parse_project_module(
    source: &ProjectSource,
    module_sources: &BTreeMap<Name, String>,
) -> ParsedProjectModule {
    let mut diagnostics = Vec::new();
    let mut authority_blockers = Vec::new();
    let mut parsed = false;
    let mut decl_count = 0;
    let mut decls = Vec::new();
    let mut local_import_order = Vec::new();
    let imports = match parse_project_imports(source, module_sources) {
        Ok(scan) => {
            parsed = true;
            decl_count = scan.decl_count;
            decls = scan.decls;
            local_import_order = scan.local_import_order;
            for import in &scan.imports {
                if !import.project_local {
                    let blocker = AuthorityBlocker::module(
                        "external_import",
                        &source.module,
                        &source.relative_path,
                        format!(
                            "import `{}` is not project-local; Clean project check did not use external Lean/Lake artifacts as authority",
                            import.module
                        ),
                    );
                    diagnostics.push(ProjectDiagnostic::from_blocker(&blocker));
                    authority_blockers.push(blocker);
                }
            }
            scan.imports
        }
        Err(message) => {
            let blocker = AuthorityBlocker::module(
                "parse_error",
                &source.module,
                &source.relative_path,
                message,
            );
            diagnostics.push(ProjectDiagnostic::from_blocker(&blocker));
            authority_blockers.push(blocker);
            Vec::new()
        }
    };

    ParsedProjectModule {
        module: source.module.clone(),
        source_path: source.relative_path.clone(),
        extension: source.extension.clone(),
        parsed,
        decl_count,
        decls,
        imports,
        local_import_order,
        diagnostics,
        authority_blockers,
    }
}

pub(super) fn project_module_cycles(
    sources: &[ProjectSource],
    parsed_modules: &[ParsedProjectModule],
) -> BTreeSet<usize> {
    let index_by_path = sources
        .iter()
        .enumerate()
        .map(|(idx, source)| (source.relative_path.clone(), idx))
        .collect::<BTreeMap<_, _>>();
    let deps = parsed_modules
        .iter()
        .map(|module| project_local_dependency_indices(module, &index_by_path))
        .collect::<Vec<_>>();
    let mut state = vec![0_u8; sources.len()];
    let mut stack = Vec::new();
    let mut cycle_modules = BTreeSet::new();
    for idx in 0..sources.len() {
        detect_project_module_cycles(idx, &deps, &mut state, &mut stack, &mut cycle_modules);
    }
    cycle_modules
}

pub(super) fn detect_project_module_cycles(
    idx: usize,
    deps: &[Vec<usize>],
    state: &mut [u8],
    stack: &mut Vec<usize>,
    cycle_modules: &mut BTreeSet<usize>,
) {
    match state[idx] {
        1 => {
            if let Some(pos) = stack.iter().position(|stack_idx| *stack_idx == idx) {
                cycle_modules.extend(stack[pos..].iter().copied());
            }
            return;
        }
        2 => return,
        _ => {}
    }
    state[idx] = 1;
    stack.push(idx);
    for dep in &deps[idx] {
        detect_project_module_cycles(*dep, deps, state, stack, cycle_modules);
    }
    stack.pop();
    state[idx] = 2;
}

pub(super) fn topological_project_module_order(
    sources: &[ProjectSource],
    parsed_modules: &[ParsedProjectModule],
    cycle_modules: &BTreeSet<usize>,
) -> Vec<usize> {
    let index_by_path = sources
        .iter()
        .enumerate()
        .map(|(idx, source)| (source.relative_path.clone(), idx))
        .collect::<BTreeMap<_, _>>();
    let deps = parsed_modules
        .iter()
        .map(|module| project_local_dependency_indices(module, &index_by_path))
        .collect::<Vec<_>>();
    let mut visited = BTreeSet::new();
    let mut order = Vec::new();
    for idx in 0..sources.len() {
        push_topological_project_module(idx, &deps, cycle_modules, &mut visited, &mut order);
    }
    order
}

pub(super) fn push_topological_project_module(
    idx: usize,
    deps: &[Vec<usize>],
    cycle_modules: &BTreeSet<usize>,
    visited: &mut BTreeSet<usize>,
    order: &mut Vec<usize>,
) {
    if cycle_modules.contains(&idx) || !visited.insert(idx) {
        return;
    }
    for dep in &deps[idx] {
        push_topological_project_module(*dep, deps, cycle_modules, visited, order);
    }
    order.push(idx);
}

pub(super) fn project_local_dependency_indices(
    module: &ParsedProjectModule,
    index_by_path: &BTreeMap<String, usize>,
) -> Vec<usize> {
    module
        .imports
        .iter()
        .filter_map(|import| {
            if !import.project_local {
                return None;
            }
            import
                .source_path
                .as_ref()
                .and_then(|path| index_by_path.get(path))
                .copied()
        })
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect()
}

/// The project-local modules `idx` imports, in the order Lean loads them:
/// depth-first through the imports in the order each module names them, a
/// module after its own imports, each module once (Lean's `importModules`).
pub(super) fn lean_import_order(idx: usize, ordered_deps: &[Vec<usize>]) -> Vec<usize> {
    fn visit(
        idx: usize,
        ordered_deps: &[Vec<usize>],
        seen: &mut BTreeSet<usize>,
        order: &mut Vec<usize>,
    ) {
        for dep in &ordered_deps[idx] {
            if seen.insert(*dep) {
                visit(*dep, ordered_deps, seen, order);
                order.push(*dep);
            }
        }
    }
    let mut seen = BTreeSet::new();
    let mut order = Vec::new();
    visit(idx, ordered_deps, &mut seen, &mut order);
    order
}

pub(super) fn parse_project_imports(
    source: &ProjectSource,
    module_sources: &BTreeMap<Name, String>,
) -> Result<ImportScan, String> {
    let text = fs::read_to_string(&source.path)
        .map_err(|err| format!("failed to read {}: {err}", source.relative_path))?;
    let patterns = clean_elab::tactic::builtins::builtin_tactic_patterns();
    let decls = parse_file_with_tactics(&text, &patterns)
        .map_err(|err| format!("parse error in {}: {err}", source.relative_path))?;
    let mut imports = Vec::new();
    collect_imports(&decls, module_sources, &mut imports);
    // Lean's import order (the order the file names them, first occurrence),
    // kept before the report's sorted list is made from the same scan.
    let mut local_import_order: Vec<String> = Vec::new();
    for import in &imports {
        if let Some(path) = &import.source_path {
            if !local_import_order.contains(path) {
                local_import_order.push(path.clone());
            }
        }
    }
    imports.sort_by(|left, right| left.identity.cmp(&right.identity));
    imports.dedup_by(|left, right| left.identity == right.identity);
    // Count LEAF declarations, not top-level blocks: a file whose whole body
    // sits inside `namespace Foo … end Foo` has one top-level decl and N
    // declarations, and reporting `declarations_parsed: 1` for it is the
    // parse-side half of the same under-report the checker used to make.
    let decl_count = decls.iter().map(count_declaration_leaves).sum();
    Ok(ImportScan {
        decl_count,
        imports,
        local_import_order,
        decls,
    })
}

/// Number of DECLARATION leaves in one top-level surface declaration.
///
/// `namespace` / `section` / `mutual` bodies and the single-declaration bodies
/// of `open … in` / `set_option … in` are flattened. Administrative forms
/// (`import`, `open`, `variable`, `notation`, `#check`, …) declare nothing and
/// count zero, so a positive count means the checker HAS declarations to
/// examine: `declarations_checked == 0` while this is positive means they went
/// unchecked, and blocks. It is not an upper bound on what the checker examines
/// — a `#command` can still elaborate to anonymous checked units — so never
/// read the two as a ratio. A parse-recovered `RawDecl` counts, because it IS a
/// declaration the parser could not read: it must be reported, never absorbed.
///
/// The match is exhaustive on purpose: a new `SurfaceDecl` variant should make
/// this fail to compile rather than silently join the uncounted side.
pub(super) fn count_declaration_leaves(decl: &SurfaceDecl) -> usize {
    match decl {
        SurfaceDecl::Alias { names, .. } => names.len(),
        SurfaceDecl::Namespace { decls, .. }
        | SurfaceDecl::Section { decls, .. }
        | SurfaceDecl::Mutual { decls, .. } => decls.iter().map(count_declaration_leaves).sum(),
        SurfaceDecl::Open { body, .. } | SurfaceDecl::SetOption { body, .. } => body
            .as_ref()
            .map_or(0, |body| count_declaration_leaves(body)),
        // `#guard_msgs … in cmd` is a checked assertion even over a command
        // that declares nothing (`#print axioms c`).
        SurfaceDecl::GuardMsgs { cmd, .. } => count_declaration_leaves(cmd).max(1),
        SurfaceDecl::Def { .. }
        | SurfaceDecl::Theorem { .. }
        | SurfaceDecl::Axiom { .. }
        | SurfaceDecl::Opaque { .. }
        | SurfaceDecl::Inductive { .. }
        | SurfaceDecl::Coinductive { .. }
        | SurfaceDecl::Codata { .. }
        | SurfaceDecl::Codef { .. }
        | SurfaceDecl::Structure { .. }
        | SurfaceDecl::Class { .. }
        | SurfaceDecl::Instance { .. }
        | SurfaceDecl::Example { .. }
        | SurfaceDecl::Guard { .. }
        | SurfaceDecl::DerivingInstance { .. }
        | SurfaceDecl::RawDecl { .. } => 1,
        SurfaceDecl::Prelude { .. }
        | SurfaceDecl::Import { .. }
        | SurfaceDecl::UniverseDecl { .. }
        | SurfaceDecl::Variable { .. }
        | SurfaceDecl::IncludeVars { .. }
        | SurfaceDecl::OmitVars { .. }
        | SurfaceDecl::Export { .. }
        | SurfaceDecl::Check { .. }
        | SurfaceDecl::Eval { .. }
        | SurfaceDecl::Reduce { .. }
        | SurfaceDecl::Print { .. }
        | SurfaceDecl::PrintAxioms { .. }
        | SurfaceDecl::PrintEquations { .. }
        | SurfaceDecl::Syntax { .. }
        | SurfaceDecl::DeclareSyntaxCat { .. }
        | SurfaceDecl::Macro { .. }
        | SurfaceDecl::MacroRules { .. }
        | SurfaceDecl::Notation { .. }
        | SurfaceDecl::Elab { .. }
        | SurfaceDecl::Attribute { .. }
        | SurfaceDecl::DeclareAesopRuleSets { .. }
        | SurfaceDecl::LibraryNote { .. } => 0,
    }
}

pub(super) fn collect_imports(
    decls: &[SurfaceDecl],
    module_sources: &BTreeMap<Name, String>,
    imports: &mut Vec<ProjectImport>,
) {
    for decl in decls {
        match decl {
            SurfaceDecl::Import { paths, .. } => {
                for path in paths {
                    let identity = path.name().clone();
                    let module = path
                        .source_spelling()
                        .unwrap_or_else(|| format!("{identity:?}"));
                    let source_path = module_sources.get(&identity).cloned();
                    imports.push(ProjectImport {
                        module,
                        identity,
                        project_local: source_path.is_some(),
                        source_path,
                    });
                }
            }
            SurfaceDecl::Namespace { decls, .. }
            | SurfaceDecl::Section { decls, .. }
            | SurfaceDecl::Mutual { decls, .. } => collect_imports(decls, module_sources, imports),
            SurfaceDecl::Open {
                body: Some(body), ..
            }
            | SurfaceDecl::SetOption {
                body: Some(body), ..
            } => collect_imports(std::slice::from_ref(body.as_ref()), module_sources, imports),
            _ => {}
        }
    }
}

pub(super) fn module_identity_for_relative_path(path: &Path) -> Option<Name> {
    path.with_extension("")
        .components()
        .try_fold(Name::anon(), |name, component| {
            let std::path::Component::Normal(component) = component else {
                return None;
            };
            Some(name.str(component.to_str()?))
        })
}

pub(super) fn slash_path(path: &Path) -> String {
    path.components()
        .filter_map(|component| component.as_os_str().to_str())
        .collect::<Vec<_>>()
        .join("/")
}

#[derive(Debug, Clone)]
pub(super) struct ProjectSource {
    pub(super) path: PathBuf,
    pub(super) relative_path: String,
    pub(super) module: String,
    pub(super) identity: Name,
    pub(super) extension: String,
}

pub(super) struct ImportScan {
    pub(super) decl_count: usize,
    pub(super) imports: Vec<ProjectImport>,
    /// Source paths of the project-local imports, in the order the file
    /// names them.
    pub(super) local_import_order: Vec<String>,
    pub(super) decls: Vec<SurfaceDecl>,
}

#[derive(Debug, Clone)]
pub(super) struct ParsedProjectModule {
    pub(super) module: String,
    pub(super) source_path: String,
    pub(super) extension: String,
    pub(super) parsed: bool,
    pub(super) decl_count: usize,
    pub(super) decls: Vec<SurfaceDecl>,
    pub(super) imports: Vec<ProjectImport>,
    /// Source paths of the project-local imports, in the order the file
    /// names them (`imports` is sorted for the report).
    pub(super) local_import_order: Vec<String>,
    pub(super) diagnostics: Vec<ProjectDiagnostic>,
    pub(super) authority_blockers: Vec<AuthorityBlocker>,
}
