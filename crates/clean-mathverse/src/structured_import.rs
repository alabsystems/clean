// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Directory-level conversion drivers for the five structured importers.
//!
//! Each `convert_*_dir` function scans a directory tree for source files,
//! parses them via the corresponding importer module, writes a single
//! `.mathverse` shard, and returns [`ConvertDirStats`].

use std::collections::HashSet;
use std::path::{Path, PathBuf};

use crate::shard::ShardWriter;

/// Summary statistics returned by structured importer `convert_dir` functions.
#[derive(Clone, Debug, Default)]
pub struct ConvertDirStats {
    /// Number of source files successfully parsed.
    pub files_processed: usize,
    /// Total declarations written to the shard.
    pub total_declarations: usize,
    /// Number of files or writes that failed.
    pub errors: usize,
}

/// Scan `dir` for `.thy` files, parse via [`isabelle_thy_import`], write shard.
pub fn convert_isabelle_thy_dir(dir: &Path, shard_output_dir: &Path) -> ConvertDirStats {
    convert_generic(
        dir,
        shard_output_dir,
        "thy",
        "isabelle_thy.mathverse",
        |content, filename, writer| {
            let decls = crate::isabelle_thy_import::parse_isabelle_file(content, filename);
            crate::isabelle_thy_import::write_isabelle_shard(&decls, writer).unwrap_or(0)
        },
    )
}

/// Scan `dir` for `.dfy` files, parse via [`dafny_import`], write shard.
pub fn convert_dafny_dir(dir: &Path, shard_output_dir: &Path) -> ConvertDirStats {
    convert_generic(
        dir,
        shard_output_dir,
        "dfy",
        "dafny.mathverse",
        |content, filename, writer| {
            let decls = crate::dafny_import::parse_dafny_file(content, filename);
            crate::dafny_import::write_dafny_shard(&decls, writer).unwrap_or(0)
        },
    )
}

/// Scan `dir` for `.lisp` files, parse via [`acl2_import`], write shard.
pub fn convert_acl2_dir(dir: &Path, shard_output_dir: &Path) -> ConvertDirStats {
    convert_generic(
        dir,
        shard_output_dir,
        "lisp",
        "acl2.mathverse",
        |content, filename, writer| {
            let decls = crate::acl2_import::parse_acl2_file(content, filename);
            crate::acl2_import::write_acl2_shard(&decls, writer).unwrap_or(0)
        },
    )
}

/// Scan `dir` for `.lean` files, parse via [`lean3_import`], write shard.
pub fn convert_lean3_dir(dir: &Path, shard_output_dir: &Path) -> ConvertDirStats {
    convert_generic(
        dir,
        shard_output_dir,
        "lean",
        "lean3.mathverse",
        |content, filename, writer| {
            let decls = crate::lean3_import::parse_lean3_file(content, filename);
            crate::lean3_import::write_lean3_shard(&decls, writer).unwrap_or(0)
        },
    )
}

/// Scan `dir` for `.v` files, parse via [`coq_v_import`], write shard.
pub fn convert_coq_v_dir(dir: &Path, shard_output_dir: &Path) -> ConvertDirStats {
    convert_generic(
        dir,
        shard_output_dir,
        "v",
        "coq_v.mathverse",
        |content, filename, writer| {
            let decls = crate::coq::v_import::parse_coq_v_file(content, filename);
            crate::coq::v_import::write_coq_v_shard(&decls, writer).unwrap_or(0)
        },
    )
}

/// Scan `dir` for `.agda` files, parse via [`crate::agda_source`], write shard.
///
/// Mirrors [`convert_coq_v_dir`]: each file's top-level `name : type`
/// signatures become Unverified name+type shard entries with a real type
/// `FlatExpr` (`value_idx = NO_VALUE`; Agda source carries no proof term).
pub fn convert_agda_dir(dir: &Path, shard_output_dir: &Path) -> ConvertDirStats {
    convert_generic(
        dir,
        shard_output_dir,
        "agda",
        "agda.mathverse",
        |content, filename, writer| {
            let decls = crate::agda_source::parse_agda_file(content, filename);
            crate::agda_source::write_agda_shard(&decls, writer)
        },
    )
}

/// Scan `dir` for `.fst` **and `.fsti`** files, parse via
/// [`crate::fstar_source`], write shard.
///
/// Mirrors [`convert_agda_dir`]: each file's top-level `val` / `assume val` /
/// `let` / `type` signatures become Unverified name+type shard entries with a
/// real type `FlatExpr` (`value_idx = NO_VALUE`; F* source carries no proof
/// term). Interface files (`.fsti`) are included because a large share of F* /
/// HACL* `val` signatures live there, separate from the `.fst` implementation.
pub fn convert_fstar_dir(dir: &Path, shard_output_dir: &Path) -> ConvertDirStats {
    convert_generic_exts(
        dir,
        shard_output_dir,
        &["fst", "fsti"],
        "fstar.mathverse",
        |content, filename, writer| {
            let decls = crate::fstar_source::parse_fstar_file(content, filename);
            crate::fstar_source::write_fstar_shard(&decls, writer)
        },
    )
}

/// Scan `dir` for `.idr` files, parse via [`crate::idris_source`], write shard.
///
/// Mirrors [`convert_agda_dir`]: each file's column-0 `name : type`
/// signatures (and `data Name : type where` heads) become Unverified
/// name+type shard entries with a real type `FlatExpr` (`value_idx =
/// NO_VALUE`; Idris source carries no proof term). Layout-aware: indented
/// `where`-block locals are skipped.
pub fn convert_idris_dir(dir: &Path, shard_output_dir: &Path) -> ConvertDirStats {
    convert_generic(
        dir,
        shard_output_dir,
        "idr",
        "idris.mathverse",
        |content, filename, writer| {
            let decls = crate::idris_source::parse_idris_file(content, filename);
            crate::idris_source::write_idris_shard(&decls, writer)
        },
    )
}

/// Scan `dir` for `.pvs` files, parse via [`crate::pvs_source`], write shard.
///
/// Mirrors [`convert_agda_dir`]: each file's THEORY-body `TYPE`, constant /
/// function, and formula declarations become Unverified name+type shard
/// entries with a real type `FlatExpr` (`value_idx = NO_VALUE`; PVS source
/// carries no proof term we reconstruct here).
pub fn convert_pvs_dir(dir: &Path, shard_output_dir: &Path) -> ConvertDirStats {
    convert_generic(
        dir,
        shard_output_dir,
        "pvs",
        "pvs.mathverse",
        |content, filename, writer| {
            let decls = crate::pvs_source::parse_pvs_file(content, filename);
            crate::pvs_source::write_pvs_shard(&decls, writer)
        },
    )
}

/// Scan `dir` for `.elf` files, parse via [`crate::twelf_source`], write shard.
///
/// Mirrors [`convert_agda_dir`]: each file's top-level `name : type[ = term].`
/// statement becomes an Unverified name+type shard entry with a real type
/// `FlatExpr` (`-> Pi`, `{x:A}` dependent Pi, juxtaposition App, `type`/`kind`
/// sorts; `value_idx = NO_VALUE` — the `= term` LF body is dropped, and LF
/// source carries no proof term we reconstruct here).
pub fn convert_twelf_dir(dir: &Path, shard_output_dir: &Path) -> ConvertDirStats {
    convert_generic(
        dir,
        shard_output_dir,
        "elf",
        "twelf.mathverse",
        |content, filename, writer| {
            let decls = crate::twelf_source::parse_twelf_file(content, filename);
            crate::twelf_source::write_twelf_shard(&decls, writer)
        },
    )
}

/// Scan `dir` for `.miz` files, parse via [`crate::mizar_source`], write shard.
///
/// Toolchain-free Mizar SOURCE importer (distinct from the unwired XML
/// [`crate::mizar`] module): each file's `theorem` statements and
/// `definition` func/pred/mode/attr signatures become Unverified name+type
/// shard entries with a real type `FlatExpr` (`value_idx = NO_VALUE`; proof
/// bodies are dropped). The shard name (`mizar_source.mathverse`) is distinct
/// from the XML module's output so the two never collide.
pub fn convert_mizar_source_dir(dir: &Path, shard_output_dir: &Path) -> ConvertDirStats {
    convert_generic(
        dir,
        shard_output_dir,
        "miz",
        "mizar_source.mathverse",
        |content, filename, writer| {
            let decls = crate::mizar_source::parse_mizar_file(content, filename);
            crate::mizar_source::write_mizar_shard(&decls, writer)
        },
    )
}

/// Scan `dir` for `.ma` files, parse via [`crate::matita_source`], write shard.
///
/// Mirrors [`convert_coq_v_dir`]: each file's keyword-led
/// `theorem`/`definition`/`axiom`/`inductive` declaration heads become
/// Unverified name+type shard entries with a real CIC type `FlatExpr`
/// (`value_idx = NO_VALUE`; Matita source carries no proof term we
/// reconstruct here — `:=` bodies and `qed.`-terminated scripts are dropped).
pub fn convert_matita_dir(dir: &Path, shard_output_dir: &Path) -> ConvertDirStats {
    convert_generic(
        dir,
        shard_output_dir,
        "ma",
        "matita.mathverse",
        |content, filename, writer| {
            let decls = crate::matita_source::parse_matita_file(content, filename);
            crate::matita_source::write_matita_shard(&decls, writer)
        },
    )
}

/// Cap applied to each aggregated per-reason list in [`CoqConvertDirStats`].
///
/// Corpus-scale imports (the full Coq stdlib is hundreds of modules) can skip
/// or drop thousands of forms; the COUNTS are always exact, but the
/// per-item reason lists are capped so the stats stay cheap to hold and
/// serialize. When a list hits the cap its `*_truncated` flag is set — the
/// truncation is never silent.
pub const COQ_REASON_LIST_CAP: usize = 200;

/// Rich statistics for [`convert_coq_sexp_dir_named`].
///
/// Extends [`ConvertDirStats`] semantics with the full loss accounting the
/// underlying [`crate::coq::alpha::CoqImportStats`] already tracks per file:
/// nothing the importer counts (skips, dropped values, unparsable files) is
/// swallowed at the directory level. All counts are exact; only the reason
/// LISTS are capped at [`COQ_REASON_LIST_CAP`] entries (with a `*_truncated`
/// flag when the cap is hit).
#[derive(Clone, Debug, Default)]
#[non_exhaustive]
pub struct CoqConvertDirStats {
    /// Files whose s-expression stream parsed and imported.
    pub files_processed: usize,
    /// Files that could not be read or whose top-level s-expression stream
    /// failed to parse (`import_sexp` returned `Err`). Never silent: each
    /// failure is also recorded in [`Self::file_failures`].
    pub files_failed: usize,
    /// Total declarations written to the shard (`translated + axiomatized`).
    pub total_declarations: usize,
    /// Declarations imported with a real translated type/value
    /// (`ImportConfidence::Translated`, plus checked inductive-family decls).
    pub translated: usize,
    /// Declarations imported type-only as trust-gated axioms.
    pub axiomatized: usize,
    /// Top-level forms skipped entirely (nothing written), with reasons in
    /// [`Self::skip_reasons`].
    pub skipped: usize,
    /// Value-bearing constants whose VALUE failed translation and was dropped
    /// (imported type-only, axiomatized and trust-gated), with reasons in
    /// [`Self::value_failure_reasons`].
    pub value_translation_failed: usize,
    /// `(file path, error)` for every entry counted in [`Self::files_failed`]
    /// (capped at [`COQ_REASON_LIST_CAP`]).
    pub file_failures: Vec<(String, String)>,
    /// Set when [`Self::file_failures`] hit the cap and entries were dropped.
    pub file_failures_truncated: bool,
    /// `(name-or-form, reason)` aggregated from every file's skip reasons
    /// (capped at [`COQ_REASON_LIST_CAP`]).
    pub skip_reasons: Vec<(String, String)>,
    /// Set when [`Self::skip_reasons`] hit the cap and entries were dropped.
    pub skip_reasons_truncated: bool,
    /// `(constant name, reason)` aggregated from every file's dropped values
    /// (capped at [`COQ_REASON_LIST_CAP`]).
    pub value_failure_reasons: Vec<(String, String)>,
    /// Set when [`Self::value_failure_reasons`] hit the cap.
    pub value_failure_reasons_truncated: bool,
    /// Set when the output shard could not be created or written; the caller
    /// must treat the conversion as failed (declaration counts describe the
    /// in-memory import, not durable output).
    pub shard_write_error: Option<String>,
}

/// The effective reason-list cap: [`COQ_REASON_LIST_CAP`] by default, or the
/// value of the `COQ_REASON_LIST_CAP` environment variable when set (a triage
/// escape hatch — raise it to capture the full drop census for a regression
/// diff, at the cost of a larger report).
fn reason_list_cap() -> usize {
    std::env::var("COQ_REASON_LIST_CAP")
        .ok()
        .and_then(|v| v.parse::<usize>().ok())
        .unwrap_or(COQ_REASON_LIST_CAP)
}

/// Append `items` to `dst`, stopping at [`reason_list_cap`] entries and
/// raising `truncated` if anything was dropped.
fn extend_reasons_capped(
    dst: &mut Vec<(String, String)>,
    truncated: &mut bool,
    items: impl IntoIterator<Item = (String, String)>,
) {
    let cap = reason_list_cap();
    for item in items {
        if dst.len() >= cap {
            *truncated = true;
            return;
        }
        dst.push(item);
    }
}

/// Extract the dump-salvage STAND-IN names recorded in a Coq dump module's
/// `.meta.json` sidecar notes (LEGACY-dump evidence source for
/// [`crate::types::AxiomProfile::SALVAGED_STAND_IN`]).
///
/// The dumper's crash-salvage rungs write one machine-generated note per
/// salvaged declaration, always `"<name>: <detail>"`. A note denotes a KEPT
/// type-only stand-in exactly when its detail says a statement-only axiom /
/// type-only stand-in was emitted:
/// - `"… emitted statement-only axiom (type serialized)"`,
/// - `"… emitted statement-only axiom from the `Check` sort-arrow arity"`,
/// - `"… emitted statement-only axiom parsed from the flagged `Check` …"`,
/// - `"… (fail closed; the inline type-only stand-in, if any, is kept)"`.
///
/// Notes that do NOT denote a kept stand-in are excluded by the filter:
/// `"reconstructed the REAL inductive from parts"` (a real `CoqInductive`
/// replaced the stand-in) and the informational PrimRecord accessor note.
/// The extraction is belt-and-suspenders anyway: the importer sets the
/// profile bit ONLY on rows that actually import as value-less `CoqAxiom`
/// forms, so a name whose dump carries a real definition never gains it.
/// New dumps additionally carry the inline `(CoqAxiom … StandIn)` marker;
/// this sidecar route keeps every pre-marker dump working without a re-dump.
pub(crate) fn salvaged_standin_names_from_meta(meta_json: &str) -> HashSet<String> {
    let mut names = HashSet::new();
    let Ok(value) = serde_json::from_str::<serde_json::Value>(meta_json) else {
        return names;
    };
    let Some(notes) = value
        .get("counts")
        .and_then(|c| c.get("notes"))
        .and_then(|n| n.as_array())
    else {
        return names;
    };
    for note in notes.iter().filter_map(|n| n.as_str()) {
        let Some((name, detail)) = note.split_once(": ") else {
            continue;
        };
        if detail.contains("statement-only axiom") || detail.contains("type-only stand-in") {
            names.insert(name.to_string());
        }
    }
    names
}

/// Load the dump-salvage stand-in names for a `.sexp` module file from its
/// `.meta.json` sidecar (same basename, `.meta.json` extension). A missing or
/// unreadable sidecar yields the empty set — the import then behaves exactly
/// as before the stand-in lever (fail-closed toward MORE taint, never less).
fn salvaged_standin_names_for(sexp_path: &Path) -> HashSet<String> {
    let meta_path = sexp_path.with_extension("meta.json");
    match std::fs::read_to_string(&meta_path) {
        Ok(s) => salvaged_standin_names_from_meta(&s),
        Err(_) => HashSet::new(),
    }
}

/// Convert a directory of Coq SerAPI/CIC s-expression dumps (`.sexp`, with
/// top-level `(CoqConstant name type [value])` / `(CoqAxiom name type)` /
/// `(CoqInductive ...)` forms) into ONE `.mathverse` shard named
/// `shard_file_name` via the richer [`crate::coq::alpha::CoqImporter`]
/// CIC-lowering path, surfacing the importer's full loss accounting.
///
/// This is the per-library workhorse behind `mathverse_shard coq-import`:
/// unlike the legacy [`convert_coq_sexp_dir`] wrapper it never collapses an
/// `import_sexp` error to zero declarations silently — unparsable files are
/// counted in [`CoqConvertDirStats::files_failed`] with their error recorded.
/// No-op (all-zero stats) when no `.sexp` files are present.
///
/// Runs TWO passes over the collected files: pass 1 registers every file's
/// `(CoqInductive ...)` metadata into a shared
/// [`crate::coq::alpha::CoqSessionRegistry`] (order-independent), pass 2
/// imports each file seeded with that registry so `Case`/`Fix` nodes over
/// inductives declared in other modules of the same library reconstruct.
pub fn convert_coq_sexp_dir_named(
    dir: &Path,
    shard_output_dir: &Path,
    shard_file_name: &str,
) -> CoqConvertDirStats {
    convert_coq_sexp_dir_with_context(dir, &[], shard_output_dir, shard_file_name)
}

/// [`convert_coq_sexp_dir_named`] with REGISTRATION-ONLY context directories:
/// every `.sexp` file under each `context_dirs` entry runs the pass-1/1b
/// registrations (inductive metadata, constant result-sorts / relation-defs /
/// const-types) into the shared session registry, but is NOT imported into the
/// shard. Lets a dependent library (mathcomp) reconstruct `Case`/`Fix` nodes
/// over inductives its files reference from an upstream library (the Coq
/// stdlib's `bool`/`nat`/`prod`/…) without duplicating the upstream
/// declarations in its own shard. Context files register FIRST, so a library's
/// own registration wins on any name collision.
pub fn convert_coq_sexp_dir_with_context(
    dir: &Path,
    context_dirs: &[PathBuf],
    shard_output_dir: &Path,
    shard_file_name: &str,
) -> CoqConvertDirStats {
    let mut stats = CoqConvertDirStats::default();
    let mut files = Vec::new();
    collect_files_recursive(dir, "sexp", &mut files);
    files.sort();
    files.dedup();
    if files.is_empty() {
        return stats;
    }
    let mut context_files = Vec::new();
    for cdir in context_dirs {
        collect_files_recursive(cdir, "sexp", &mut context_files);
    }
    context_files.sort();
    context_files.dedup();

    // PASS 1 — cross-file inductive registry: register every file's
    // `(CoqInductive ...)` metadata BEFORE any import so a module's `Case`s
    // on inductives declared in another module (e.g. `Coq.Init.Peano`
    // matching on `Coq.Init.Datatypes.nat`) resolve regardless of file
    // order. Context-library files register first (registration only — they
    // are never imported below). Read/parse failures are deliberately not
    // counted here: pass 2 re-reads the same file and counts them in
    // `files_failed` (counting in both passes would double-book the same
    // failure).
    let mut registry = crate::coq::alpha::CoqSessionRegistry::default();

    // PASS 0 — global universe re-leveling (see
    // `crate::coq::universe_releveling`): mine `binder ≥ argument-type-level`
    // constraints from every application site of the session (context
    // libraries included — cross-library constraints on upstream levels are
    // real), solve the max-plus fixpoint, and install the resulting
    // `uid → base` map BEFORE any registration or import so every rendering
    // of a named global level (registries included) is consistent. Runs on
    // RAW s-expressions only, so no normalization state is needed yet.
    //
    // DEFAULT ON (opt OUT with `CLEAN_COQ_UID_RELEVEL=0`) — the raise resolves
    // the pure `Sort(1)`-vs-`Sort(2)` over-leveling class (stdlib +246 KV incl.
    // the whole `List.app_assoc` cluster; mathcomp +5, REGRESSED 0, measured
    // 2026-07-14 against the 22,574-KV baseline). It was opt-in-default-off
    // until 2026-07-12 because a residual 128 stdlib decls regressed on the
    // recursor ELIM-SHAPE MIRROR divergence for raised-param Prop records
    // (`Berardi.retract.0.rec` level-count mismatch); that prerequisite landed
    // in the kernel (commit 0ed0b876a: `elim_only_at_universe_zero` +
    // inductive-builder cumulativity companion), and the raise then gates
    // 0-regression on BOTH libraries — so it is now the default. Full lever
    // history in the `universe_releveling` module docs.
    if std::env::var_os("CLEAN_COQ_UID_RELEVEL").is_none_or(|v| v != "0") {
        let mut miner = crate::coq::universe_releveling::UniverseConstraintMiner::default();
        for path in context_files.iter().chain(files.iter()) {
            if let Ok(content) = std::fs::read_to_string(path) {
                let _ = miner.scan_signatures(&content);
            }
        }
        for path in context_files.iter().chain(files.iter()) {
            if let Ok(content) = std::fs::read_to_string(path) {
                let _ = miner.scan_constraints(&content);
            }
        }
        let bases = miner.solve();
        if std::env::var("CLEAN_COQ_UID_RELEVEL_DEBUG").is_ok() {
            eprintln!(
                "  [universe-relevel] raised {} named level uid(s)",
                bases.len()
            );
            for (uid, base) in bases.raised_entries() {
                eprintln!("  [universe-relevel]   {uid} -> Type base {base}");
            }
        }
        registry.install_universe_bases(bases);
    }

    for path in context_files.iter().chain(files.iter()) {
        if let Ok(content) = std::fs::read_to_string(path) {
            let _ =
                crate::coq::alpha::CoqImporter.register_inductive_forms(&content, &mut registry);
        }
    }
    // PASS 1b — cross-file constant result-sort registry: after every
    // inductive is registered (so a constant's type normalizes against the
    // full inductive set), register each `(CoqConstant …)`/`(CoqAxiom …)` whose
    // type ends in a sort. This lets a module's `match … return (x < y)` over a
    // relation declared in another module (`Z.le`, `R`) derive its recursor
    // motive universe rather than failing closed.
    for path in context_files.iter().chain(files.iter()) {
        if let Ok(content) = std::fs::read_to_string(path) {
            let _ =
                crate::coq::alpha::CoqImporter.register_constant_shapes(&content, &mut registry);
        }
    }

    // PASS 1c — inductive-registry CONSISTENCY re-pass. `register_inductive_forms`
    // normalizes each family's constructor types through the canonical-first
    // inductive Dual flip (`resolve_ind_family_name`): an `Include`-copy
    // reference (`BinPos.Pos.mask` → the canonical `BinPosDef.Pos.mask`) resolves
    // to the canonical family ONLY once that family is registered. In file order
    // a family (`Pos.SqrtSpec`, whose constructor carries a `prod positive mask`
    // index) can register in PASS 1 BEFORE the canonical copy of a type it
    // mentions (`BinPosDef.Pos.mask`, dumped in the later `BinPosDef` file),
    // FREEZING its registry constructor types at the unflipped spelling — while
    // PASS 2 imports every term against the now-complete registry and flips them.
    // A `Case`/`Fix` on that family then rebuilds its branch field types from the
    // stale registry entry (`convert_serapi_case` reads `info.ctor_types`),
    // producing the measured `prod positive BinPosDef.Pos.mask`-vs-
    // `…BinPos.Pos.mask` mismatch the kernel rejects (the `Pos`/`Positive_as_DT`/
    // `OrdersEx` `SqrtSpec`/`SubMaskSpec` eliminators and `N`/`Z.sqrtrem_spec`).
    // Re-registering after the WHOLE inductive + constant name set is known makes
    // every constructor type flip EXACTLY as the import does — PASS 1c and PASS 2
    // both consult the identical (fully populated) `inductives`/`known_names`
    // state, so the reconstructed branch types match the imported scrutinee.
    // `register` overwrites its map entry, so families already consistent are
    // rewritten byte-for-byte (idempotent); it never removes a constructor type.
    for path in context_files.iter().chain(files.iter()) {
        if let Ok(content) = std::fs::read_to_string(path) {
            let _ =
                crate::coq::alpha::CoqImporter.register_inductive_forms(&content, &mut registry);
        }
    }

    // PASS 2 — import each file with the shared registry, keeping per-file
    // fail-closed error isolation.
    let mut writer = ShardWriter::new();
    for path in &files {
        let display = path.display().to_string();
        let content = match std::fs::read_to_string(path) {
            Ok(c) => c,
            Err(e) => {
                stats.files_failed += 1;
                extend_reasons_capped(
                    &mut stats.file_failures,
                    &mut stats.file_failures_truncated,
                    [(display, format!("read failed: {e}"))],
                );
                continue;
            }
        };
        // `import_sexp_with_registry_and_standins` fails only if the top-level
        // s-expression stream does not parse — i.e. BEFORE any constant is
        // written — so a failed file never leaves partial declarations in
        // the shared writer. The salvage set (from the module's `.meta.json`
        // sidecar) profiles legacy dump-salvage `CoqAxiom` stand-ins
        // `SALVAGED_STAND_IN`; new dumps carry the inline marker as well.
        let salvaged_standins = salvaged_standin_names_for(path);
        match crate::coq::alpha::CoqImporter.import_sexp_with_registry_and_standins(
            &content,
            &registry,
            &salvaged_standins,
            &mut writer,
        ) {
            Ok(s) => {
                stats.files_processed += 1;
                stats.total_declarations += (s.translated + s.axiomatized) as usize;
                stats.translated += s.translated as usize;
                stats.axiomatized += s.axiomatized as usize;
                stats.skipped += s.skipped as usize;
                stats.value_translation_failed += s.value_translation_failed as usize;
                extend_reasons_capped(
                    &mut stats.skip_reasons,
                    &mut stats.skip_reasons_truncated,
                    s.skip_reasons,
                );
                extend_reasons_capped(
                    &mut stats.value_failure_reasons,
                    &mut stats.value_failure_reasons_truncated,
                    s.value_failure_reasons,
                );
            }
            Err(e) => {
                stats.files_failed += 1;
                extend_reasons_capped(
                    &mut stats.file_failures,
                    &mut stats.file_failures_truncated,
                    [(display, e.to_string())],
                );
            }
        }
    }

    if stats.total_declarations > 0 {
        if let Err(e) = std::fs::create_dir_all(shard_output_dir) {
            stats.shard_write_error = Some(format!("{}: {e}", shard_output_dir.display()));
            return stats;
        }
        let shard_path = shard_output_dir.join(shard_file_name);
        if let Err(e) = writer.write_to_file(&shard_path) {
            tracing::warn!("could not write shard {}: {e}", shard_path.display());
            stats.shard_write_error = Some(format!("{}: {e}", shard_path.display()));
        }
    }

    stats
}

/// Convert a directory of Coq SerAPI/CIC s-expression dumps (`.sexp`, with
/// top-level `(CoqConstant name type [value])` / `(CoqAxiom name type)` forms)
/// into one `.mathverse` shard via the richer [`crate::coq::alpha::CoqImporter`]
/// CIC-lowering path. This is the SerAPI counterpart to [`convert_coq_v_dir`]
/// (which parses `.v` surface syntax); both coexist since they scan different
/// extensions/directories. No-op when no `.sexp` files are present.
///
/// Thin legacy wrapper over [`convert_coq_sexp_dir_named`] with the historical
/// fixed shard name; files whose s-expression stream fails to parse are
/// counted in [`ConvertDirStats::errors`] (they were previously swallowed as
/// zero-declaration successes).
pub fn convert_coq_sexp_dir(dir: &Path, shard_output_dir: &Path) -> ConvertDirStats {
    let s = convert_coq_sexp_dir_named(dir, shard_output_dir, "coq_sexp.mathverse");
    ConvertDirStats {
        files_processed: s.files_processed,
        total_declarations: s.total_declarations,
        errors: s.files_failed + usize::from(s.shard_write_error.is_some()),
    }
}

/// Generic directory conversion: collect files, parse each, write one shard.
fn convert_generic(
    dir: &Path,
    shard_output_dir: &Path,
    extension: &str,
    shard_name: &str,
    parse_and_write: impl FnMut(&str, &str, &mut ShardWriter) -> usize,
) -> ConvertDirStats {
    convert_generic_exts(
        dir,
        shard_output_dir,
        &[extension],
        shard_name,
        parse_and_write,
    )
}

/// Like [`convert_generic`] but collects files matching any of `extensions`
/// into a single shard (e.g. F*'s `.fst` implementations and `.fsti`
/// interfaces).
fn convert_generic_exts(
    dir: &Path,
    shard_output_dir: &Path,
    extensions: &[&str],
    shard_name: &str,
    mut parse_and_write: impl FnMut(&str, &str, &mut ShardWriter) -> usize,
) -> ConvertDirStats {
    let mut stats = ConvertDirStats::default();
    let mut files = Vec::new();
    for ext in extensions {
        collect_files_recursive(dir, ext, &mut files);
    }
    files.sort();
    files.dedup();

    if files.is_empty() {
        return stats;
    }

    let mut shard_writer = ShardWriter::new();

    for path in &files {
        let filename = path.file_name().unwrap_or_default().to_string_lossy();
        match std::fs::read_to_string(path) {
            Ok(content) => {
                let n = parse_and_write(&content, &filename, &mut shard_writer);
                stats.total_declarations += n;
                stats.files_processed += 1;
            }
            Err(_) => stats.errors += 1,
        }
    }

    if stats.total_declarations > 0 {
        let _ = std::fs::create_dir_all(shard_output_dir);
        let shard_path = shard_output_dir.join(shard_name);
        if let Err(e) = shard_writer.write_to_file(&shard_path) {
            tracing::warn!("could not write shard {}: {e}", shard_path.display());
        }
    }

    stats
}

fn collect_files_recursive(dir: &Path, ext: &str, out: &mut Vec<PathBuf>) {
    if let Ok(rd) = std::fs::read_dir(dir) {
        for entry in rd.filter_map(|e| e.ok()) {
            let path = entry.path();
            if path.is_dir() {
                collect_files_recursive(&path, ext, out);
            } else if path.extension().is_some_and(|e| e == ext) {
                out.push(path);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A well-formed importer-dialect closure: `nat` + a translated identity
    /// definition + one genuine axiom. 3 inductive-family decls + 1 translated
    /// definition + 1 axiomatized constant = 5 declarations.
    const GOOD_SEXP: &str = r#"(CoqInductive nat 0 Set
  (Ctor O (Ind nat 0))
  (Ctor S (Prod n (Ind nat 0) (Ind nat 0))))
(CoqConstant idnat
  (Prod n (Ind nat 0) (Ind nat 0))
  (Lambda n (Ind nat 0) (Rel 0)))
(CoqAxiom classic (Sort Prop))"#;

    /// One value-bearing constant whose raw `Fix` value cannot be
    /// structuralized: the value is dropped LOUDLY (type-only axiomatized,
    /// counted in `value_translation_failed`), plus one unknown form that is
    /// skipped with a reason.
    const LOSSY_SEXP: &str = r#"(CoqConstant weird_fix (Sort Prop) (Fix ((f (Sort Prop) (Rel 0))) 0))
(CoqBogus whatever)"#;

    fn write_fixture(dir: &Path, name: &str, content: &str) {
        std::fs::write(dir.join(name), content).expect("write fixture file");
    }

    /// `convert_coq_sexp_dir_named` surfaces every loss channel: parsed files,
    /// unparsable files (counted, never silent), skipped forms, and dropped
    /// values — and still writes the shard for the successful declarations.
    #[test]
    fn test_convert_coq_sexp_dir_named_surfaces_all_loss_channels() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let src = tmp.path().join("src");
        let out = tmp.path().join("out");
        std::fs::create_dir_all(&src).expect("create src dir");
        write_fixture(&src, "a_good.sexp", GOOD_SEXP);
        write_fixture(&src, "b_lossy.sexp", LOSSY_SEXP);
        // Unbalanced parens: the top-level s-expression stream fails to parse.
        write_fixture(&src, "c_corrupt.sexp", "(CoqConstant broken (Sort Prop)");

        let stats = convert_coq_sexp_dir_named(&src, &out, "coq_test.mathverse");

        assert_eq!(stats.files_processed, 2, "good + lossy parse");
        assert_eq!(stats.files_failed, 1, "corrupt file must be COUNTED");
        assert_eq!(stats.file_failures.len(), 1);
        assert!(
            stats.file_failures[0].0.ends_with("c_corrupt.sexp"),
            "failure records the file: {:?}",
            stats.file_failures
        );
        // good: nat family (3) + idnat (1) + classic (1); lossy: weird_fix (1).
        assert_eq!(stats.total_declarations, 6);
        assert_eq!(stats.translated, 4, "nat family (3) + idnat");
        assert_eq!(stats.axiomatized, 2, "classic + value-dropped weird_fix");
        assert_eq!(stats.value_translation_failed, 1);
        assert_eq!(stats.value_failure_reasons.len(), 1);
        assert_eq!(stats.value_failure_reasons[0].0, "weird_fix");
        assert_eq!(stats.skipped, 1, "the unknown CoqBogus form");
        assert_eq!(stats.skip_reasons.len(), 1);
        assert!(!stats.skip_reasons_truncated);
        assert!(!stats.value_failure_reasons_truncated);
        assert!(!stats.file_failures_truncated);
        assert!(stats.shard_write_error.is_none());
        assert!(
            out.join("coq_test.mathverse").exists(),
            "shard written for the successful declarations"
        );
    }

    /// The sidecar-note extraction keeps exactly the notes that denote a KEPT
    /// type-only stand-in and drops the informational / superseded kinds.
    #[test]
    fn test_salvaged_standin_names_from_meta_filters_note_kinds() {
        let meta = serde_json::json!({
            "module": "m",
            "counts": {
                "notes": [
                    "a.one: value raw-Constr serialization crashed sertop; \
                     emitted statement-only axiom (type serialized)",
                    "a.two: MInd serialization crashed sertop; emitted \
                     statement-only axiom from the `Check` sort-arrow arity",
                    "a.three: value AND type raw serialization crashed sertop \
                     (Proj-laced type); emitted statement-only axiom parsed \
                     from the flagged `Check` pretty-print",
                    "a.four: reconstruction-from-parts failed (fail closed; \
                     the inline type-only stand-in, if any, is kept)",
                    "b.real: MInd serialization crashed sertop; reconstructed \
                     the REAL inductive from parts (3 `Print` ctor name(s), 1 \
                     params, ...) — kernel replay arbitrates at verify time",
                    "b.prim: PrimRecord — accessor bodies are Proj-valued and \
                     may not dump (sertop 8.20 Proj serialization limitation)",
                ]
            }
        })
        .to_string();
        let names = salvaged_standin_names_from_meta(&meta);
        for kept in ["a.one", "a.two", "a.three", "a.four"] {
            assert!(names.contains(kept), "{kept} must be extracted: {names:?}");
        }
        for dropped in ["b.real", "b.prim"] {
            assert!(
                !names.contains(dropped),
                "{dropped} must NOT be extracted: {names:?}"
            );
        }
        // Robustness: unparsable sidecar / missing notes → empty (fail-closed
        // toward MORE taint, never less).
        assert!(salvaged_standin_names_from_meta("not json").is_empty());
        assert!(salvaged_standin_names_from_meta("{}").is_empty());
    }

    /// End-to-end sidecar route: a legacy module whose `.meta.json` names a
    /// salvage stand-in gets that row profiled `SALVAGED_STAND_IN` in the
    /// written shard; a genuine axiom in the same file stays unmarked.
    #[test]
    fn test_convert_coq_sexp_dir_meta_sidecar_marks_standins() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let src = tmp.path().join("src");
        let out = tmp.path().join("out");
        std::fs::create_dir_all(&src).expect("create src dir");
        write_fixture(
            &src,
            "m.sexp",
            "(CoqAxiom legacy.standin (Sort Prop))\n\
             (CoqAxiom legacy.genuine (Sort Prop))\n",
        );
        write_fixture(
            &src,
            "m.meta.json",
            &serde_json::json!({
                "module": "m",
                "counts": {
                    "notes": [
                        "legacy.standin: value raw-Constr serialization crashed \
                         sertop; emitted statement-only axiom (type serialized)"
                    ]
                }
            })
            .to_string(),
        );

        let stats = convert_coq_sexp_dir_named(&src, &out, "coq_meta.mathverse");
        assert_eq!(stats.total_declarations, 2, "both axioms import");
        let reader = crate::shard::ShardReader::from_file(out.join("coq_meta.mathverse"))
            .expect("shard reads back");
        let profile_of = |name: &str| {
            reader
                .constants
                .iter()
                .find(|c| reader.strings[c.name_idx as usize] == name)
                .unwrap_or_else(|| panic!("{name} missing from shard"))
                .profile()
        };
        assert!(
            profile_of("legacy.standin").has(crate::types::AxiomProfile::SALVAGED_STAND_IN),
            "sidecar-named stand-in must carry the hint"
        );
        assert!(
            !profile_of("legacy.genuine").has(crate::types::AxiomProfile::SALVAGED_STAND_IN),
            "genuine axiom must stay unmarked"
        );
    }

    /// The legacy fixed-name wrapper maps the new stats down AND counts
    /// unparsable files as errors instead of swallowing them.
    #[test]
    fn test_convert_coq_sexp_dir_counts_corrupt_files_as_errors() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let src = tmp.path().join("src");
        let out = tmp.path().join("out");
        std::fs::create_dir_all(&src).expect("create src dir");
        write_fixture(&src, "good.sexp", GOOD_SEXP);
        write_fixture(&src, "corrupt.sexp", "(((");

        let stats = convert_coq_sexp_dir(&src, &out);
        assert_eq!(stats.files_processed, 1);
        assert_eq!(stats.errors, 1, "parse failure must count as an error");
        assert_eq!(stats.total_declarations, 5);
        assert!(out.join("coq_sexp.mathverse").exists());
    }

    /// CROSS-FILE inductive registry: file B's raw SerAPI `Case` matches on
    /// an inductive declared only in file A. The two-pass driver must
    /// register A's `(CoqInductive ...)` metadata before importing B, so B's
    /// value TRANSLATES (no `not in import session` drop) regardless of file
    /// order, and the merged shard kernel-verifies.
    #[test]
    fn test_convert_coq_sexp_dir_named_cross_file_case_translates() {
        use crate::library::MathverseLibrary;
        use crate::trust::policy::TrustPolicy;
        use crate::verify::incremental::verify_corpus_incremental;

        // File A: nat, declared alone. File B: `Definition my_pred (n:nat) :=
        // match n with O => O | S p => p end.` as a raw SerAPI Case on
        // Coq.Init.Datatypes.nat. Note the file names sort B BEFORE A, so the
        // test also proves order-independence of the registry pass.
        let file_a = r#"(CoqInductive Coq.Init.Datatypes.nat 0 Set
  (Ctor O (Ind Coq.Init.Datatypes.nat 0))
  (Ctor S (Prod n (Ind Coq.Init.Datatypes.nat 0) (Ind Coq.Init.Datatypes.nat 0))))"#;
        let file_b = r#"(CoqConstant SerTop.my_pred
  (Prod n (Ind Coq.Init.Datatypes.nat 0) (Ind Coq.Init.Datatypes.nat 0))
  (Lambda((binder_name(Name(Id n)))(binder_relevance Relevant))(Ind(((MutInd(KerName(MPfile(DirPath((Id Datatypes)(Id Init)(Id Coq))))(Id nat))())0)(Instance(()()))))(Case((ci_ind((MutInd(KerName(MPfile(DirPath((Id Datatypes)(Id Init)(Id Coq))))(Id nat))())0))(ci_npar 0)(ci_cstr_ndecls(0 1))(ci_cstr_nargs(0 1))(ci_pp_info((style RegularStyle))))(Instance(()()))()(((((binder_name(Name(Id n)))(binder_relevance Relevant)))(Ind(((MutInd(KerName(MPfile(DirPath((Id Datatypes)(Id Init)(Id Coq))))(Id nat))())0)(Instance(()())))))Relevant)NoInvert(Rel 1)((()(Construct((((MutInd(KerName(MPfile(DirPath((Id Datatypes)(Id Init)(Id Coq))))(Id nat))())0)1)(Instance(()())))))((((binder_name(Name(Id p)))(binder_relevance Relevant)))(Rel 1))))))"#;

        let tmp = tempfile::tempdir().expect("tempdir");
        let src = tmp.path().join("src");
        let out = tmp.path().join("out");
        std::fs::create_dir_all(&src).expect("create src dir");
        write_fixture(&src, "a_uses_nat.sexp", file_b); // sorts FIRST
        write_fixture(&src, "b_decls_nat.sexp", file_a); // sorts SECOND

        let stats = convert_coq_sexp_dir_named(&src, &out, "coq_cross.mathverse");
        assert_eq!(stats.files_processed, 2);
        assert_eq!(
            stats.value_translation_failed, 0,
            "the cross-file Case must translate: {:?}",
            stats.value_failure_reasons
        );
        // nat family (3 decls) + my_pred (1 translated definition).
        assert_eq!(stats.translated, 4);
        assert_eq!(stats.axiomatized, 0);

        // Golden-style kernel verification of the produced shard.
        let reader =
            crate::shard::ShardReader::from_file(out.join("coq_cross.mathverse")).expect("shard");
        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        lib.load_shard(&reader).expect("load shard");
        let prelude =
            clean_kernel::Environment::try_with_prelude().expect("kernel prelude environment");
        let report = verify_corpus_incremental(&lib, prelude);
        assert_eq!(report.failed, 0, "failures: {:?}", report.failures);
        assert_eq!(
            report.axiom_fallback, 0,
            "no value may be masked: {:?}",
            report.axiom_fallback_names
        );
        assert!(
            report
                .kernel_verified_names
                .contains(&"SerTop.my_pred".to_string()),
            "the cross-file match must kernel-verify, got {:?}",
            report.kernel_verified_names
        );
    }

    /// Reason lists are capped at [`COQ_REASON_LIST_CAP`] with the truncation
    /// flag raised; the COUNTS stay exact.
    #[test]
    fn test_convert_coq_sexp_dir_named_caps_reason_lists_loudly() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let src = tmp.path().join("src");
        let out = tmp.path().join("out");
        std::fs::create_dir_all(&src).expect("create src dir");
        let n = COQ_REASON_LIST_CAP + 5;
        let many_bogus = "(CoqBogus x)\n".repeat(n);
        write_fixture(&src, "bogus.sexp", &many_bogus);

        let stats = convert_coq_sexp_dir_named(&src, &out, "coq_cap.mathverse");
        assert_eq!(stats.skipped, n, "counts stay exact past the cap");
        assert_eq!(stats.skip_reasons.len(), COQ_REASON_LIST_CAP);
        assert!(stats.skip_reasons_truncated, "truncation is never silent");
        assert_eq!(stats.total_declarations, 0);
        assert!(
            !out.join("coq_cap.mathverse").exists(),
            "no shard when nothing was imported"
        );
    }
}
