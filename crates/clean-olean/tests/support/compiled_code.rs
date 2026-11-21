// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The compiled-checker refusal (plan unit E2's follow-up part 2;
//! `docs/DECISIONS.md`, "Compiled-checker packages refuse what changes executed
//! code without moving a pin", and its correction of 2026-11-19, part 3). The
//! packages Trust is to compile and run are pinned by meaning
//! (`support/meaning_digest.rs`): a pin moves when a kernel term a pinned
//! constant reaches changes. Lean has ways to change the code a declaration
//! compiles to, or to add code no declaration states, that move no kernel term,
//! and so no pin. A package Trust compiles must use none of them. This file
//! reads, from each package module's compiled `.olean`, everything that does,
//! and returns one refusal per occurrence:
//!
//! * an import, read from the module's `.olean` header, of anything but `Init`
//!   (and its submodules) and the modules the call reads (the package): `Std`
//!   and `Lean` included. `import Lean` is what gives a module the compiler's
//!   own tables and the metaprograms that write them: a pass installer
//!   (`@[cpass]`), a constant folder, or an `addDecl` of a partial
//!   `<d>._unsafe_rec` beside a safe `<d>`, which has the shape of the
//!   compiler's own copy below and which compiled code runs in `<d>`'s place
//!   (the control `CompiledCodeImportLean`, refused by this rule alone);
//! * a row in one of [`REFUSED_TABLES`]: `@[implemented_by]` and `@[extern]`
//!   (compiled code runs another body or a C symbol in the declaration's
//!   place), `@[csimp]` (the code generator replaces one constant by another
//!   everywhere), `@[export]` (the compiled function is emitted under a C
//!   symbol, which a link can bind in place of another), `@[init]` and
//!   `@[builtin_init]` (an `IO` action runs when the program starts),
//!   `@[cpass]` (a compiler pass, run on this module's declarations and every
//!   importing module's, rewrites compiled bodies: the pinned Lean evaluates a
//!   `spec 3` to `4` beside a `rfl` proof that it is `3`) and a constant
//!   folder (`registerFolder`: the code generator folds applications of a
//!   constant to what the folder returns, with the same effect). Lean writes a
//!   module's table only when it has rows, so a table present is a refusal.
//!   The last two need `import Lean`, so the import rule refuses them first;
//!   the table rule is kept beside it;
//! * an `opaque` constant: compiled code runs its value and no kernel theorem
//!   can depend on it;
//! * an `unsafe` or `partial` declaration, which the kernel never checks;
//!   one exception, counted: the copy `<d>._unsafe_rec` Lean's compiler
//!   generates, as a `partial` definition in `<d>`'s own module, beside a safe
//!   recursive definition `<d>` of the package. Upstream Lean compiles `<d>`
//!   from that copy, generated from the same source as the kernel term, so a
//!   change to the source moves both; that the compiled code is the kernel
//!   term at all is the compiled-lineage work (plan units W1 and W3), not this
//!   check's;
//! * any other declaration named `<d>._unsafe_rec`. Lean's code generator
//!   compiles `<d>` from a constant of that name whatever declared it, so a
//!   hand-written safe `def <d>._unsafe_rec` beside a safe `def <d>` runs its
//!   own body wherever compiled code calls `<d>`, while the kernel (and every
//!   pin) still unfolds `<d>` (the pinned Lean evaluates such a `<d> 3` to the
//!   copy's `4` beside a `rfl` proof that it is `3`; the control is
//!   `CompiledCodeUnsafeRec`).
//!
//! Both readers of the compiled data are consulted: the module parser
//! ([`clean_olean::parse_module_types_only`], independent of any load policy)
//! and the loader's own reading ([`LoadSummary::extension_accounting`], the
//! tables the load read, and [`LoadSummary::imports`]). A refused table or an
//! import either reports is refused, and a module whose compiled data holds
//! tables the load did not read is refused too, so a load that reads no
//! extension data cannot pass vacuously. A package module the test's own root
//! does not import is loaded into a scratch environment for its summary
//! ([`complete_summaries`]), so the loader reads every package module, not
//! only the root's closure. A module-system artifact (a `.olean.server` or
//! `.olean.private` part beside the `.olean`) is refused: this check reads
//! single-part artifacts only, and none of these packages is a module-system
//! package.
//!
//! Looked at and left out (the pinned Lean's compiler tables): `@[inline]`,
//! `@[noinline]`, `@[macro_inline]`, `@[always_inline]` (`inlineAttrs`),
//! `@[specialize]`, `@[nospecialize]`, `@[weak_specialize]`, `@[never_extract]`
//! and `@[unbox]` direct where and how the declaration's own body is compiled,
//! which a code generator assumed to preserve meaning does (the
//! compiler-correctness obligation, not this one); `@[tagged_return]` is valid
//! only on an `@[extern]` declaration, refused above; `noncomputable` emits no
//! code; `@[computed_field]` writes `implementedByAttr` rows, refused above;
//! the compiler's own output and caches (`IR.declMapExt`, `LCNF.baseExt`,
//! `monoExt`, `impureSigExt`, `specExtension`, `Specialize.specCacheExt`,
//! `UnreachableBranches.functionSummariesExt`) are written for every module
//! with code, and a forged row needs a metaprogram, which needs the `Lean`
//! import refused above; `postponedCompileDeclsExt` and the `meta` tables
//! belong to module-system artifacts, refused above.
//!
//! Not covered: `attribute [local csimp] thm`. A local entry is never exported,
//! so no table holds it and no reader of the compiled data sees it, and it
//! needs no import of `Lean`: the pinned Lean compiles the module's own calls
//! of the replaced constant to the replacement. A `csimp` lemma still needs a
//! proved `@slow = @quick`, so the module's compiled code computes what the
//! kernel term does, but the refusal of `@[csimp]` does not reach its local
//! form. The other refused attributes have no local form under the pinned Lean
//! (`implemented_by`, `extern`, `export`, `init`, `builtin_init` and `cpass`
//! must be global; a constant folder has no attribute), and `scoped csimp` is
//! exported and refused.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use clean_kernel::env::Environment;
use clean_olean::{
    discover_olean_parts, load_modules_with_deps, parse_module_types_only,
    ConstantKind as ParsedKind, DefinitionSafety, LoadSummary,
};

/// Every extension table whose rows change what compiled code runs without
/// moving a kernel term: `(table, attribute)`.
pub(crate) const REFUSED_TABLES: &[(&str, &str)] = &[
    ("Lean.Compiler.implementedByAttr", "@[implemented_by]"),
    ("Lean.externAttr", "@[extern]"),
    ("Lean.Compiler.CSimp.ext", "@[csimp]"),
    ("Lean.exportAttr", "@[export]"),
    ("Lean.regularInitAttr", "@[init] (initialize)"),
    (
        "Lean.builtinInitAttr",
        "@[builtin_init] (builtin_initialize)",
    ),
    ("Lean.Compiler.LCNF.passManagerExt", "@[cpass]"),
    (
        "Lean.Compiler.LCNF.Simp.ConstantFold.folderExt",
        "a constant folder (registerFolder)",
    ),
];

/// The library every package module may import beside the package's own
/// modules: `Init` and its submodules.
const INIT: &str = "Init";

/// Whether `import` is `Init` or one of its submodules.
fn is_init(import: &str) -> bool {
    import
        .strip_prefix(INIT)
        .is_some_and(|rest| rest.is_empty() || rest.starts_with('.'))
}

/// The suffix of the compiler's unsafe copy of a recursive definition.
const UNSAFE_REC: &str = "._unsafe_rec";

/// One thing in a package module's compiled data that changes executed code
/// without moving a pin.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, thiserror::Error)]
pub(crate) enum CompiledCodeRefusal {
    /// A refused extension table holds rows for this module.
    #[error("{module} carries {attribute}: {rows} row(s) of {table}")]
    Attribute {
        module: String,
        table: String,
        attribute: &'static str,
        rows: usize,
    },
    /// The module imports a module that is neither `Init` (or a submodule)
    /// nor a module of the package.
    #[error("{module} imports {import}, which is neither Init nor a module of the package")]
    Import { module: String, import: String },
    /// The module's artifact has parts beside its `.olean`.
    #[error("{module} is a module-system artifact of {parts} parts; only single-part artifacts are read")]
    MultiPart { module: String, parts: usize },
    /// The load returned no summary for a package module.
    #[error("{module} is a package module the load did not read")]
    NotLoaded { module: String },
    /// The module's compiled data holds extension tables and the load read
    /// none of them.
    #[error("{module} holds {tables} extension table(s) and the load read none")]
    NotRead { module: String, tables: usize },
    /// An `opaque` constant.
    #[error("{module} declares {name} opaque")]
    Opaque { module: String, name: String },
    /// An `unsafe` declaration.
    #[error("{module} declares {name} unsafe")]
    Unsafe { module: String, name: String },
    /// A `partial` declaration that is not the compiler's copy of a safe
    /// recursive definition of the same module.
    #[error("{module} declares {name} partial")]
    Partial { module: String, name: String },
    /// A declaration named `<d>._unsafe_rec` that is not the compiler's copy
    /// of a safe recursive definition `<d>` of the same module: compiled code
    /// runs it in `<d>`'s place.
    #[error("{module} declares {name}, which compiled code runs in place of {base}")]
    CompiledReplacement {
        module: String,
        name: String,
        base: String,
    },
}

/// What [`refusals`] found.
pub(crate) struct CompiledCodeCensus {
    /// Every refusal, sorted.
    pub(crate) refusals: Vec<CompiledCodeRefusal>,
    /// Package modules read.
    pub(crate) modules: usize,
    /// Extension tables the parser read across them.
    pub(crate) tables: usize,
    /// Imports read across them (each module's distinct imports).
    pub(crate) imports: usize,
    /// The compiler's `._unsafe_rec` copies allowed, by name.
    pub(crate) compiler_copies: BTreeSet<String>,
}

/// One declaration as the module parser reads it.
struct Declared {
    module: String,
    kind: ParsedKind,
    safety: Option<DefinitionSafety>,
    family_unsafe: bool,
}

/// `summaries` (the test's own load) and, for every module of `modules` they
/// do not cover, the summaries of a load of those modules into a scratch
/// environment over `search_paths`: a package module the test's root does not
/// import is read by the loader too.
pub(crate) fn complete_summaries(
    summaries: &[LoadSummary],
    modules: &[String],
    search_paths: &[PathBuf],
) -> Vec<LoadSummary> {
    let covered: BTreeSet<String> = summaries
        .iter()
        .filter_map(|summary| summary.module_name.clone())
        .collect();
    let missing: Vec<String> = modules
        .iter()
        .filter(|module| !covered.contains(module.as_str()))
        .cloned()
        .collect();
    let mut all = summaries.to_vec();
    if !missing.is_empty() {
        let mut scratch = Environment::for_lean_replay();
        let extra = load_modules_with_deps(&mut scratch, &missing, search_paths)
            .unwrap_or_else(|error| panic!("load the package modules outside the root: {error}"));
        all.extend(extra.into_iter().filter(|summary| {
            summary
                .module_name
                .as_deref()
                .is_some_and(|module| !covered.contains(module))
        }));
    }
    all
}

/// Every refusal for `modules` (dotted module names, whose `.olean` files are
/// under `compiled`), read from their compiled data and from the loader's
/// summaries of a load that read each of them.
pub(crate) fn refusals(
    compiled: &Path,
    modules: &[String],
    summaries: &[LoadSummary],
) -> CompiledCodeCensus {
    let mut refusals = Vec::new();
    let mut declared: BTreeMap<String, Declared> = BTreeMap::new();
    let mut tables = 0_usize;
    let mut imports_read = 0_usize;
    let package: BTreeSet<&str> = modules.iter().map(String::as_str).collect();
    for module in modules {
        let path = compiled.join(format!("{}.olean", module.replace('.', "/")));
        let parts = discover_olean_parts(&path).len();
        if parts != 1 {
            refusals.push(CompiledCodeRefusal::MultiPart {
                module: module.clone(),
                parts,
            });
        }
        let bytes =
            std::fs::read(&path).unwrap_or_else(|error| panic!("read {}: {error}", path.display()));
        let parsed = parse_module_types_only(&bytes)
            .unwrap_or_else(|error| panic!("parse {}: {error}", path.display()));
        let mut found: BTreeMap<String, usize> = BTreeMap::new();
        for extension in &parsed.entries {
            *found.entry(extension.extension_name.clone()).or_default() +=
                extension.entries.len() + extension.undecoded_entries;
        }
        tables += found.len();
        // The imports the module's header states, as the parser reads them.
        let mut imports: BTreeSet<String> = parsed
            .imports
            .iter()
            .map(|import| import.module_name.clone())
            .collect();
        match summaries
            .iter()
            .find(|summary| summary.module_name.as_deref() == Some(module.as_str()))
        {
            None => refusals.push(CompiledCodeRefusal::NotLoaded {
                module: module.clone(),
            }),
            Some(summary) => {
                if !found.is_empty() && summary.extension_accounting.is_empty() {
                    refusals.push(CompiledCodeRefusal::NotRead {
                        module: module.clone(),
                        tables: found.len(),
                    });
                }
                for row in &summary.extension_accounting {
                    let rows = row
                        .source_rows
                        .unwrap_or(row.decoded_rows + row.undecoded_rows);
                    let entry = found.entry(row.extension_name.to_string()).or_default();
                    *entry = (*entry).max(rows);
                }
                imports.extend(summary.imports.iter().cloned());
            }
        }
        imports_read += imports.len();
        for import in imports {
            if !is_init(&import) && !package.contains(import.as_str()) {
                refusals.push(CompiledCodeRefusal::Import {
                    module: module.clone(),
                    import,
                });
            }
        }
        for (table, attribute) in REFUSED_TABLES {
            if let Some(rows) = found.get(*table) {
                refusals.push(CompiledCodeRefusal::Attribute {
                    module: module.clone(),
                    table: (*table).to_owned(),
                    attribute,
                    rows: *rows,
                });
            }
        }
        for constant in parsed.constants {
            let family_unsafe = constant.inductive_val.as_ref().is_some_and(|v| v.is_unsafe)
                || constant
                    .constructor_val
                    .as_ref()
                    .is_some_and(|v| v.is_unsafe)
                || constant.recursor_val.as_ref().is_some_and(|v| v.is_unsafe);
            declared.insert(
                constant.name,
                Declared {
                    module: module.clone(),
                    kind: constant.kind,
                    safety: constant.definition_safety,
                    family_unsafe,
                },
            );
        }
    }
    let mut compiler_copies = BTreeSet::new();
    for (name, declaration) in &declared {
        let module = declaration.module.clone();
        if declaration.kind == ParsedKind::Opaque {
            refusals.push(CompiledCodeRefusal::Opaque {
                module: module.clone(),
                name: name.clone(),
            });
        }
        if declaration.safety == Some(DefinitionSafety::Unsafe) || declaration.family_unsafe {
            refusals.push(CompiledCodeRefusal::Unsafe {
                module: module.clone(),
                name: name.clone(),
            });
        }
        // The compiler's copy: a partial definition `<d>._unsafe_rec` beside a
        // safe definition `<d>` of the same module.
        let base = name.strip_suffix(UNSAFE_REC);
        let compiler_copy = declaration.kind == ParsedKind::Definition
            && declaration.safety == Some(DefinitionSafety::Partial)
            && base.is_some_and(|base| {
                declared.get(base).is_some_and(|base| {
                    base.module == declaration.module
                        && base.kind == ParsedKind::Definition
                        && base.safety == Some(DefinitionSafety::Safe)
                })
            });
        if compiler_copy {
            compiler_copies.insert(name.clone());
            continue;
        }
        if declaration.safety == Some(DefinitionSafety::Partial) {
            refusals.push(CompiledCodeRefusal::Partial {
                module: module.clone(),
                name: name.clone(),
            });
        }
        if let Some(base) = base {
            refusals.push(CompiledCodeRefusal::CompiledReplacement {
                module,
                name: name.clone(),
                base: base.to_owned(),
            });
        }
    }
    refusals.sort();
    CompiledCodeCensus {
        refusals,
        modules: modules.len(),
        tables,
        imports: imports_read,
        compiler_copies,
    }
}

/// The modules of `theories`, each theory's `ORDER` stems in order, for a
/// test that does not build a meaning-digest package.
#[allow(dead_code)] // kcheck_core and kcheck_labelled take their meaning-digest package's modules
pub(crate) fn theory_modules(theories: &[&str]) -> Vec<String> {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../theories");
    theories
        .iter()
        .flat_map(|theory| {
            let path = root.join(theory).join("ORDER");
            let text = std::fs::read_to_string(&path)
                .unwrap_or_else(|error| panic!("read {}: {error}", path.display()));
            text.lines()
                .map(str::trim)
                .filter(|line| !line.is_empty() && !line.starts_with('#'))
                .map(|stem| stem.replace('/', "."))
                .collect::<Vec<_>>()
        })
        .collect()
}

/// Panics, naming each refusal, unless `census` holds none; otherwise one line
/// for the log.
pub(crate) fn require_none(census: &CompiledCodeCensus, what: &str) -> String {
    assert!(
        census.refusals.is_empty(),
        "{what}: a package Trust is to compile changes executed code without moving a pin:\n{}",
        census
            .refusals
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>()
            .join("\n")
    );
    assert!(
        census.tables > 0,
        "{what}: the parser read no extension table in {} modules",
        census.modules
    );
    assert!(
        census.imports > 0,
        "{what}: the parser read no import in {} modules",
        census.modules
    );
    format!(
        "compiled-code refusal {what}: {} modules, {} extension tables and {} imports read, no \
         import outside Init and the package, none of {} refused tables, no opaque, unsafe or \
         partial declaration and no other ._unsafe_rec name; {} compiler copies (._unsafe_rec) \
         of safe recursive definitions",
        census.modules,
        census.tables,
        census.imports,
        REFUSED_TABLES.len(),
        census.compiler_copies.len()
    )
}
