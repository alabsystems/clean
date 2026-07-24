// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Coq `.vo` binary decoding: OCaml Marshal object graphs → kernel terms.
//!
//! This is the groundwork for the full-fidelity Rocq 9.x import route
//! (SerAPI ends at Coq 8.20): decode compiled `.vo` files directly into the
//! importer's sexp forms, with no `sertop` in the loop.
//!
//! Pipeline: [`marshal_parser`] decodes a segment's OCaml Marshal stream
//! into a shared DAG; [`vo_parser`] handles the `ObjFile` container (magic,
//! version, segment table); [`library`] navigates the `summary` / `library`
//! / `opaques` segment structures down to `constant_body`; [`constr_decode`]
//! turns kernel `Constr.t` values into [`constr::Constr`]; [`constr_sexp`]
//! serializes them in SerAPI-compatible sexp form. [`pipeline`] batches
//! whole directory trees with rayon.
//!
//! Layouts are taken from the Coq 8.20 sources (`lib/objFile.ml`,
//! `checker/analyze.ml`, `checker/values.ml`, `kernel/constr.ml`) and are
//! empirically validated against the local 8.20 stdlib `.vo` files plus the
//! SerAPI corpus dumps. The Marshal layer is OCaml-version-independent;
//! only the `Constr` tag layout needs revisiting for Rocq 9.x.

pub mod constr;
pub mod constr_decode;
pub mod constr_sexp;
pub mod export;
pub mod library;
pub mod marshal_parser;
pub(crate) mod marshal_reader;
pub mod pipeline;
pub mod vo_parser;

#[cfg(test)]
mod tests;
#[cfg(test)]
mod tests_pipeline;
