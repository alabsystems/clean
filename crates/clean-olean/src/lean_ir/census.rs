// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Per-module IR census: the rows `clean olean ir-census` prints and the
//! pinned-Lean oracle (`tests/fixtures/lean/v4.30.0-rc2/oracle/IRCensusOracle.lean`
//! in this crate) prints in the same format, so the two can be diffed line by
//! line.

use std::collections::{BTreeMap, HashSet, VecDeque};
use std::path::PathBuf;

use rayon::prelude::*;

use super::error::{LeanIrError, LeanIrResult};
use super::format::name_to_string;
use super::format_decl::{format_decl, quote_string};
use super::module_ir::{
    find_module_ir_olean, load_module_ir_at, read_module_imports, InterpSource, ModuleIr,
};
use super::profile::IrProfile;
use super::types::{Decl, ExternAttrData, ExternEntry};
use clean_kernel::Name;

/// One module's census row (the oracle's `MOD` line).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CensusRow {
    /// Module name as `Name.toString` prints it.
    pub(crate) module: String,
    /// `fdecl`s in the main data's `declMapExt`.
    pub(crate) fdecl_olean: usize,
    /// `extern`s in the main data's `declMapExt`.
    pub(crate) extern_olean: usize,
    /// `fdecl`s in the interpreter data's `declMapExt`.
    pub(crate) fdecl_ir: usize,
    /// `extern`s in the interpreter data's `declMapExt`.
    pub(crate) extern_ir: usize,
    /// `externAttr` entries.
    pub(crate) extern_attr: usize,
    /// `implementedByAttr` entries.
    pub(crate) implemented_by: usize,
    /// `regularInitAttr` entries (main data).
    pub(crate) regular_init: usize,
    /// `regularInitAttr` entries (interpreter data).
    pub(crate) regular_init_ir: usize,
    /// `builtinInitAttr` entries.
    pub(crate) builtin_init: usize,
}

fn split(decls: &[Decl]) -> (usize, usize) {
    let externs = decls.iter().filter(|d| d.is_extern()).count();
    (decls.len() - externs, externs)
}

impl CensusRow {
    /// The row for one decoded module.
    #[must_use]
    pub(crate) fn from_module(m: &ModuleIr) -> Self {
        let (fdecl_olean, extern_olean) = split(&m.olean_decls);
        let (fdecl_ir, extern_ir) = split(m.ir_decls());
        Self {
            module: name_to_string(&m.module),
            fdecl_olean,
            extern_olean,
            fdecl_ir,
            extern_ir,
            extern_attr: m.extern_attr.len(),
            implemented_by: m.implemented_by.len(),
            regular_init: m.regular_init.len(),
            regular_init_ir: m.regular_init_ir().len(),
            builtin_init: m.builtin_init.len(),
        }
    }

    fn counts(&self) -> [usize; 9] {
        [
            self.fdecl_olean,
            self.extern_olean,
            self.fdecl_ir,
            self.extern_ir,
            self.extern_attr,
            self.implemented_by,
            self.regular_init,
            self.regular_init_ir,
            self.builtin_init,
        ]
    }

    /// The oracle's `MOD` line.
    #[must_use]
    pub(crate) fn to_line(&self) -> String {
        format!("MOD {} {}", self.module, fields(&self.counts()))
    }
}

fn fields(c: &[usize; 9]) -> String {
    format!(
        "fdecl_olean={} extern_olean={} fdecl_ir={} extern_ir={} extern_attr={} \
         implemented_by={} regular_init={} regular_init_ir={} builtin_init={}",
        c[0], c[1], c[2], c[3], c[4], c[5], c[6], c[7], c[8]
    )
}

/// The oracle's `TOTAL` line over `rows`.
#[must_use]
pub(crate) fn total_line(rows: &[CensusRow]) -> String {
    let mut sum = [0usize; 9];
    for row in rows {
        for (acc, v) in sum.iter_mut().zip(row.counts()) {
            *acc += v;
        }
    }
    format!("TOTAL modules={} {}", rows.len(), fields(&sum))
}

/// The transitive import closure of `roots`, each module with its resolved
/// base `.olean`, ordered as the oracle orders it (by `Name.toString`).
///
/// # Errors
///
/// Refuses when any module of the closure is not on the search path or its
/// import list cannot be read.
pub(crate) fn import_closure(
    roots: &[Name],
    search_paths: &[PathBuf],
) -> LeanIrResult<Vec<(Name, PathBuf)>> {
    let mut seen: HashSet<Name> = HashSet::new();
    let mut queue: VecDeque<Name> = roots.iter().cloned().collect();
    let mut found: BTreeMap<String, (Name, PathBuf)> = BTreeMap::new();
    while let Some(module) = queue.pop_front() {
        if !seen.insert(module.clone()) {
            continue;
        }
        let olean = find_module_ir_olean(&module, search_paths)?;
        for import in read_module_imports(&module, &olean)? {
            if !seen.contains(&import) {
                queue.push_back(import);
            }
        }
        found.insert(name_to_string(&module), (module, olean));
    }
    Ok(found.into_values().collect())
}

/// Resolve `roots` without walking imports, ordered by `Name.toString`.
///
/// # Errors
///
/// Refuses when a module is not on the search path.
pub(crate) fn resolve_modules(
    roots: &[Name],
    search_paths: &[PathBuf],
) -> LeanIrResult<Vec<(Name, PathBuf)>> {
    let mut found: BTreeMap<String, (Name, PathBuf)> = BTreeMap::new();
    for module in roots {
        let olean = find_module_ir_olean(module, search_paths)?;
        found.insert(name_to_string(module), (module.clone(), olean));
    }
    Ok(found.into_values().collect())
}

/// What one module contributed.
struct ModuleOutcome {
    row: CensusRow,
    blocks: Vec<String>,
    attrs: Vec<String>,
    decls: usize,
    nesting: usize,
    profile: IrProfile,
}

/// What a census covers and what it prints besides the rows.
#[derive(Debug, Clone, Default)]
pub(crate) struct CensusRequest {
    /// Root modules.
    pub(crate) modules: Vec<Name>,
    /// Walk the transitive import closure of the roots.
    pub(crate) closure: bool,
    /// `.olean` search paths, `LEAN_PATH` order.
    pub(crate) search_paths: Vec<PathBuf>,
    /// Declarations to render (`Name.toString` spelling).
    pub(crate) print_decls: Vec<String>,
    /// Modules whose every declaration is rendered (`*`: every module).
    pub(crate) print_modules: Vec<String>,
    /// Print `ATTR` / `DECLEXT` / `DECLSORRY` lines.
    pub(crate) print_attrs: bool,
    /// Modules decoded in parallel (at least one).
    pub(crate) jobs: usize,
}

fn entries_line(ext: &ExternAttrData) -> String {
    if ext.entries.is_empty() {
        return "none".to_owned();
    }
    ext.entries
        .iter()
        .map(|e| match e {
            ExternEntry::Adhoc { backend } => format!("adhoc {}", name_to_string(backend)),
            ExternEntry::Inline { backend, pattern } => {
                format!(
                    "inline {} {}",
                    name_to_string(backend),
                    quote_string(pattern)
                )
            }
            ExternEntry::Standard { backend, symbol } => {
                format!(
                    "standard {} {}",
                    name_to_string(backend),
                    quote_string(symbol)
                )
            }
            ExternEntry::Opaque => "opaque".to_owned(),
        })
        .collect::<Vec<_>>()
        .join(" | ")
}

fn attr_lines(ir: &ModuleIr, module: &str) -> Vec<String> {
    let mut out = Vec::new();
    for (decl, ext) in &ir.extern_attr {
        out.push(format!(
            "ATTR {module} extern {} {}",
            name_to_string(decl),
            entries_line(ext)
        ));
    }
    let pairs: [(&str, &[(Name, Name)]); 4] = [
        ("implemented_by", &ir.implemented_by),
        ("regular_init", &ir.regular_init),
        ("regular_init_ir", ir.regular_init_ir()),
        ("builtin_init", &ir.builtin_init),
    ];
    for (kind, entries) in pairs {
        for (decl, target) in entries {
            out.push(format!(
                "ATTR {module} {kind} {} {}",
                name_to_string(decl),
                name_to_string(target)
            ));
        }
    }
    for (level, decls) in [("olean", ir.olean_decls.as_slice()), ("ir", ir.ir_decls())] {
        for decl in decls {
            match decl {
                Decl::Extern { f, ext, .. } => out.push(format!(
                    "DECLEXT {module} {level} {} {}",
                    name_to_string(f),
                    entries_line(ext)
                )),
                Decl::FDecl { f, info, .. } => {
                    if let Some(dep) = &info.sorry_dep {
                        out.push(format!(
                            "DECLSORRY {module} {level} {} {}",
                            name_to_string(f),
                            name_to_string(dep)
                        ));
                    }
                }
            }
        }
    }
    out
}

fn census_one(
    module: &Name,
    olean: &std::path::Path,
    print: &CensusRequest,
) -> LeanIrResult<ModuleOutcome> {
    let ir = load_module_ir_at(module, olean)?;
    let row = CensusRow::from_module(&ir);
    let whole = print
        .print_modules
        .iter()
        .any(|m| m == "*" || *m == row.module);
    let mut blocks = Vec::new();
    if whole || !print.print_decls.is_empty() {
        for (level, decls) in [("olean", ir.olean_decls.as_slice()), ("ir", ir.ir_decls())] {
            for decl in decls {
                let name = name_to_string(decl.name());
                if whole || print.print_decls.contains(&name) {
                    blocks.push(format!(
                        "DECL {} {level} {name}\n{}\nENDDECL",
                        row.module,
                        format_decl(decl)
                    ));
                }
            }
        }
    }
    let attrs = if print.print_attrs {
        attr_lines(&ir, &row.module)
    } else {
        Vec::new()
    };
    let decls = ir.olean_decls.len()
        + match ir.interp_source {
            InterpSource::IrFile => ir.ir_decls().len(),
            InterpSource::MainData => 0,
        };
    let mut profile = IrProfile::default();
    profile.module(&ir);
    Ok(ModuleOutcome {
        row,
        blocks,
        attrs,
        decls,
        nesting: ir.max_nesting,
        profile,
    })
}

/// The rendered census: what `ir-census` prints, before it prints it.
#[derive(Debug)]
pub(crate) struct CensusReport {
    /// Standard output: `MOD` rows, the `TOTAL` row, `DECL` blocks, then
    /// `ATTR`/`DECLEXT`/`DECLSORRY` lines.
    pub(crate) stdout: String,
    /// One line per module that failed to decode (the census is refused).
    pub(crate) failures: Vec<String>,
    /// The closing statistics line (decls decoded, nesting, time).
    pub(crate) summary: String,
    /// Modules in the census.
    pub(crate) modules: usize,
    /// Construct profile of every decoded module (`PROFILE` lines).
    pub(crate) profile: IrProfile,
}

/// Compute the census `request` asks for — exactly the text
/// `clean olean ir-census` prints, so what the tests compare with the
/// pinned-Lean oracle is what the verb prints.
///
/// # Errors
///
/// Refuses when a module of the census cannot be resolved or its imports
/// read. A module whose IR fails to DECODE is not an error here: it is listed
/// in [`CensusReport::failures`] and the `TOTAL` row is withheld.
pub(crate) fn run_census(request: &CensusRequest) -> LeanIrResult<CensusReport> {
    let started = std::time::Instant::now();
    let modules = if request.closure {
        import_closure(&request.modules, &request.search_paths)?
    } else {
        resolve_modules(&request.modules, &request.search_paths)?
    };
    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(request.jobs.max(1))
        .build()
        .map_err(|e| LeanIrError::Module {
            module: "<census>".to_owned(),
            detail: format!("thread pool: {e}"),
        })?;
    let outcomes: Vec<_> = pool.install(|| {
        modules
            .par_iter()
            .map(|(module, olean)| census_one(module, olean, request))
            .collect()
    });

    let mut stdout = String::new();
    let mut rows = Vec::with_capacity(outcomes.len());
    let mut blocks = Vec::new();
    let mut attrs = Vec::new();
    let mut failures = Vec::new();
    let (mut decls, mut nesting) = (0usize, 0usize);
    let mut profile = IrProfile::default();
    for ((module, _), outcome) in modules.iter().zip(outcomes) {
        match outcome {
            Ok(done) => {
                stdout.push_str(&done.row.to_line());
                stdout.push('\n');
                rows.push(done.row);
                blocks.extend(done.blocks);
                attrs.extend(done.attrs);
                decls += done.decls;
                nesting = nesting.max(done.nesting);
                profile.merge(done.profile);
            }
            Err(error) => failures.push(format!("{}: {error}", name_to_string(module))),
        }
    }
    if failures.is_empty() {
        stdout.push_str(&total_line(&rows));
        stdout.push('\n');
        for line in blocks.iter().chain(&attrs) {
            stdout.push_str(line);
            stdout.push('\n');
        }
    }
    let summary = format!(
        "ir-census: {} module(s), {decls} IR declaration(s) decoded, max nesting {nesting}, {:.1}s",
        rows.len(),
        started.elapsed().as_secs_f64()
    );
    Ok(CensusReport {
        stdout,
        failures,
        summary,
        modules: modules.len(),
        profile,
    })
}
