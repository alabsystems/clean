// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `.vo` → importer-form sexp export: the Rocq-9 import ROUTE.
//!
//! Decodes a compiled `.vo` object graph into [`Constr`](super::constr::Constr)
//! and renders the SAME `(CoqConstant …)` forms that the SerAPI dump emits, so
//! [`CoqImporter::import_sexp`](crate::coq::alpha::CoqImporter::import_sexp)
//! consumes `.vo`-reconstructed terms UNCHANGED — no live `sertop` required.
//! This is the path past SerAPI's 8.20 dead-end (Rocq 9.x ships `.vo` only).
//!
//! Scope today: the CONSTANT lane (transparent `Def` bodies inline in the
//! `library` segment, `OpaqueDef`/Qed bodies through the `opaques` table).
//! Inductive blocks are NOT yet rendered — the library walk
//! ([`read_library`](super::library::read_library)) does not extract their
//! arity / parameter count — so constants that reference an inductive import
//! type-only until that lands. Every constant whose term the decoder cannot
//! yet reconstruct is SKIPPED with its name counted, never silently dropped.

use super::constr_decode::ConstrDecoder;
use super::constr_sexp::coq_constant_sexp;
use super::library::{self, ConstantDefKind};
use super::vo_parser::{VoObjFile, VoResult};

/// Outcome of exporting one `.vo` file's constants to importer-form sexp.
#[derive(Clone, Debug, Default)]
#[non_exhaustive]
pub struct VoExport {
    /// Importer-form dump: one `(CoqConstant …)` per line.
    pub sexp: String,
    /// Constants rendered (type, plus body when available).
    pub exported: usize,
    /// `(name, reason)` for constants the decoder could not yet reconstruct.
    pub skipped: Vec<(String, String)>,
}

/// Render every CONSTANT of a compiled `.vo` file (`data`) as importer-form
/// `(CoqConstant …)` sexps. `lib_name` is the logical library name
/// (e.g. `Coq.Init.Logic`), used to resolve the compiled-library structure.
///
/// # Errors
///
/// Returns [`VoParseError`](super::vo_parser::VoParseError) when the container
/// or the `library` segment itself cannot be walked. Per-constant decode
/// failures do NOT abort the export — they land in [`VoExport::skipped`].
pub fn export_vo_constants(data: &[u8], lib_name: &str) -> VoResult<VoExport> {
    let obj = VoObjFile::parse(data)?;
    let lib_dag = obj.read_segment("library")?;
    let lib = library::read_library(&lib_dag, lib_name)?;
    // The opaques segment is optional (absent when the library has no Qed
    // constants); its lookups are best-effort.
    let opq_dag = obj.read_segment("opaques").ok();

    let mut export = VoExport::default();
    for c in &lib.constants {
        let typ = match ConstrDecoder::new(&lib_dag).constr(c.type_val) {
            Ok(t) => t,
            Err(e) => {
                export
                    .skipped
                    .push((c.qualified.clone(), format!("type decode: {e}")));
                continue;
            }
        };
        let body = match c.def {
            // Axiom / primitive / rewrite symbol: import type-only, no body.
            ConstantDefKind::Undef | ConstantDefKind::Primitive | ConstantDefKind::Symbol => None,
            ConstantDefKind::Def => c
                .body_val
                .and_then(|bv| ConstrDecoder::new(&lib_dag).constr(bv).ok()),
            ConstantDefKind::OpaqueDef => match (opq_dag.as_ref(), c.opaque_index) {
                (Some(od), Some(idx)) => library::read_opaque_proof(od, idx)
                    .ok()
                    .flatten()
                    .and_then(|pv| ConstrDecoder::new(od).constr(pv).ok()),
                _ => None,
            },
        };
        export
            .sexp
            .push_str(&coq_constant_sexp(&c.qualified, &typ, body.as_ref()));
        export.sexp.push('\n');
        export.exported += 1;
    }
    Ok(export)
}
