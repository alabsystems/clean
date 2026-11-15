// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Per-declaration elaboration timing, recorded on request for
//! `clean check --json`.
//!
//! WHY THIS EXISTS. Nothing in Clean measured where a `clean check` spent its
//! time. The five-file source-elab slice went from 1,283 s (2026-08-31) to
//! 3,941 s (2026-09-21) and no gate noticed; the performance audit
//! (`reports/lean4-replacement-audit-2026-09-24/performance.json`) needed
//! external `sample` snapshots to find that one `grind` fallback and one
//! `simp_rw` were most of two files. Lean has `-Dprofiler=true`; the check
//! report had nothing.
//!
//! WHY IT LIVES HERE AND NOT IN THE CLI. `clean check` iterates TOP-LEVEL
//! surface declarations, and a Mathlib file is mostly `section` / `namespace`
//! blocks, each elaborated inside ONE call to the elaborator. A timer around
//! that call measures a whole section. The block arms of
//! `elaborate_decl_and_register_inner_with_aux` recurse into the same function
//! once per member, so that function's entry is the one place every leaf
//! declaration passes through.
//!
//! WHAT A RECORD IS. One record per OUTERMOST non-container call: a
//! `section` / `namespace` block and a `set_option … in <decl>` wrapper never
//! record (their members do), and a call nested inside a recording one (a
//! desugaring that splits one declaration into several, the members of a
//! `mutual` block) is charged to the declaration the user wrote, never
//! double-counted. Wall time, including the kernel check of the declaration.
//!
//! OFF BY DEFAULT. Recording is armed per thread by
//! [`crate::begin_decl_timing`] and drained by [`crate::take_decl_timings`];
//! unarmed, a call costs one thread-local read. Nothing accumulates in a
//! long-lived process (the LSP, the server) that never asked.

use std::cell::{Cell, RefCell};
use std::time::{Duration, Instant};

use clean_parser::SurfaceDecl;

use crate::{DeclTiming, DeclTimingKind, FileContext};

thread_local! {
    static RECORDS: RefCell<Option<Vec<DeclTiming>>> = const { RefCell::new(None) };
    static LEAF_ACTIVE: Cell<bool> = const { Cell::new(false) };
}

/// `crate::begin_decl_timing`: arm recording on THIS thread, discarding
/// anything left from an earlier run.
pub(crate) fn begin() {
    RECORDS.with(|r| *r.borrow_mut() = Some(Vec::new()));
    LEAF_ACTIVE.with(|a| a.set(false));
}

/// `crate::take_decl_timings`: disarm recording on this thread and return the
/// records made since `begin`, in elaboration order.
#[must_use]
pub(crate) fn take() -> Vec<DeclTiming> {
    LEAF_ACTIVE.with(|a| a.set(false));
    RECORDS.with(|r| r.borrow_mut().take()).unwrap_or_default()
}

fn armed() -> bool {
    RECORDS.with(|r| r.borrow().is_some())
}

/// The declaration a wrapper stands for. `open X in <decl>` is elaborated
/// INLINE by the elaborator (`infer/elaborate_decl.rs`, the `Open` arm), never
/// by recursing through the registration entry, so the only record it gets is
/// its own -- and it must be the record of the declaration it wraps, not an
/// anonymous command the per-declaration report then drops.
fn timed_subject(decl: &SurfaceDecl) -> &SurfaceDecl {
    match decl {
        SurfaceDecl::Open {
            body: Some(inner), ..
        } => timed_subject(inner),
        _ => decl,
    }
}

/// A container is elaborated by recursing into its members, so it records
/// nothing itself (and refills no automation budget: its members do).
pub(crate) fn is_container(decl: &SurfaceDecl) -> bool {
    matches!(
        decl,
        SurfaceDecl::Section { .. }
            | SurfaceDecl::Namespace { .. }
            | SurfaceDecl::SetOption { body: Some(_), .. }
            // `#guard_msgs … in cmd` runs `cmd` through the registration
            // entry (`elaborate_decl_and_register_inner`), which times it.
            | SurfaceDecl::GuardMsgs { .. }
    )
}

fn kind_of(decl: &SurfaceDecl) -> DeclTimingKind {
    match decl {
        SurfaceDecl::Import { .. } => DeclTimingKind::Import,
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
        | SurfaceDecl::Mutual { .. }
        | SurfaceDecl::DerivingInstance { .. }
        | SurfaceDecl::RawDecl { .. } => DeclTimingKind::Declaration,
        _ => DeclTimingKind::Command,
    }
}

/// The namespace-qualified name the user would recognise, the same spelling
/// `failed_inner_leaf` reports a failing member under.
fn display_name(decl: &SurfaceDecl, file_ctx: Option<&FileContext>) -> String {
    if let SurfaceDecl::Mutual { decls, .. } = decl {
        let names: Vec<String> = decls
            .iter()
            .filter_map(|d| crate::preprocess_ext::decl_name(d).map(|n| n.to_string()))
            .collect();
        return format!("mutual({})", names.join(", "));
    }
    let Some(short) = crate::preprocess_ext::decl_name(decl) else {
        return "[anonymous]".to_owned();
    };
    match file_ctx.map(|fc| fc.namespace_state().current_namespace()) {
        Some(ns) if !ns.is_anon() => short
            .qualify_under(&clean_parser::SurfaceName::from_name(ns.clone()))
            .to_string(),
        _ => short.to_string(),
    }
}

/// Times one call of the elaborator's per-declaration entry; records on drop,
/// so every early `return` in that function is covered.
pub(crate) struct LeafTimer {
    pending: Option<(DeclTiming, Instant)>,
}

impl LeafTimer {
    pub(crate) fn start(decl: &SurfaceDecl, file_ctx: Option<&FileContext>) -> Self {
        if !armed() || is_container(decl) || LEAF_ACTIVE.with(Cell::get) {
            return Self { pending: None };
        }
        LEAF_ACTIVE.with(|a| a.set(true));
        let subject = timed_subject(decl);
        let record = DeclTiming {
            name: display_name(subject, file_ctx),
            kind: kind_of(subject),
            byte_start: subject.span().start,
            elapsed: Duration::ZERO,
            automation_work: 0,
        };
        Self {
            pending: Some((record, Instant::now())),
        }
    }
}

impl Drop for LeafTimer {
    fn drop(&mut self) {
        if let Some((mut record, started)) = self.pending.take() {
            record.elapsed = started.elapsed();
            // The automation budget is refilled at this same outermost entry
            // (`crate::decl_work_budget::LeafWorkScope`), so what it has spent
            // now is this declaration's work.
            record.automation_work = clean_auto::automation_work_used();
            LEAF_ACTIVE.with(|a| a.set(false));
            RECORDS.with(|r| {
                if let Some(v) = r.borrow_mut().as_mut() {
                    v.push(record);
                }
            });
        }
    }
}
