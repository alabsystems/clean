// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **The GLOBALS half of the interface check**: what `emitted_globals` READ
//! from the module-table preamble, compared against the tag table's `globals`
//! lane and against every `global_addr` the chain's bodies observed, and then
//! spliced into the core module as `(global k <agg>)` in canonical order.
//!
//! `interface.rs` owns the per-body checks (`check_body`) and the one entry
//! point `project`; this file owns the one MODULE-LEVEL check `project` runs
//! after the body loop. Reader B refuses a `global_addr` on every bare read;
//! `project` under a table with a `globals` lane is the single path that
//! reads one, and [`check_globals`] is what makes that path fail closed.

use std::collections::{BTreeMap, BTreeSet};

use super::core::Sx;
use super::emitted::ObservedTags;
use super::emitted_globals::Preamble;
use super::error::InterfaceError;
use super::tags::{GlobalPin, Tags};

impl Preamble {
    /// The `(global k <agg>)` entry for canonical `k`, from the ONE declaration
    /// that carries the pin's name — compared against the pin's linkage and
    /// resolved type on the way.
    ///
    /// # Errors
    /// [`InterfaceError::Mismatch`] with slot `global declaration` when no row
    /// declares the pinned name, `global linkage` or `global type` when the row
    /// disagrees with the pin.
    pub(super) fn entry_for(&self, k: u32, pin: &GlobalPin) -> Result<Sx, InterfaceError> {
        let decl = self
            .globals
            .iter()
            .find(|g| g.name == pin.name)
            .ok_or_else(|| InterfaceError::Mismatch {
                slot: "global declaration".into(),
                pinned: format!("global {k} `@{}`", pin.name),
                found: format!(
                    "no `global … @{} …` row in the module-table preamble (declared: {:?})",
                    pin.name,
                    self.globals
                        .iter()
                        .map(|g| g.name.as_str())
                        .collect::<Vec<_>>()
                ),
            })?;
        for (slot, found, pinned) in [
            ("global linkage", &decl.linkage, &pin.linkage),
            ("global type", &decl.ty, &pin.ty),
        ] {
            if found != pinned {
                return Err(InterfaceError::Mismatch {
                    slot: format!("{slot} (global {k} `@{}`)", pin.name),
                    pinned: pinned.clone(),
                    found: found.clone(),
                });
            }
        }
        Ok(Sx::tag(
            "global",
            vec![Sx::a(k.to_string()), decl.init.clone()],
        ))
    }

    /// The declared name that no pin claims, if any — a surplus row that would
    /// otherwise be dropped unread.
    pub(super) fn surplus<'a>(&'a self, pins: &BTreeMap<u32, GlobalPin>) -> Option<&'a str> {
        self.globals
            .iter()
            .map(|g| g.name.as_str())
            .find(|name| !pins.values().any(|p| p.name == *name))
    }
}

/// The module-level GLOBALS check: every `global_addr` any body read, the tag
/// table's `globals` lane and the module-table preamble must account for one
/// another exactly, and then the list is spliced in canonical order.
///
/// Four directions, each a refusal naming its slot:
///
/// * an id a body addressed that no row PINS — `Unpinned`, naming the
///   `@global.N` (an unpinned id interns above the lane in the reader, so it
///   cannot collide with a pinned canonical index; this is the only way an
///   observed global can fail to match its pin);
/// * a pinned global NO body addresses — `Unpinned`: a row nothing reaches is a
///   pin over nothing, exactly as a `funcs` row no call names would be;
/// * a pinned name with no preamble declaration, or a declaration whose
///   linkage or resolved type disagrees with the pin — `Mismatch` at slot
///   `global declaration` / `global linkage` / `global type`;
/// * a declaration no row pins — `Unpinned`, naming it, because a row the
///   reader dropped unread is the erasure this whole lane exists to refuse.
///
/// The union of observed canonicals is then dense `0..n` by construction: the
/// lane is dense (`tags::parse`), every pin is observed, and nothing observed
/// is unpinned.
///
/// Lives here, beside the pin comparison on [`Preamble`], rather than in
/// `interface.rs`, which `project`'s per-body checks already fill; `project`
/// calls it once, after every body is read.
pub(super) fn check_globals(
    bodies: &[ObservedTags],
    preamble: &Preamble,
    global_namespace: &BTreeMap<u32, u32>,
    tags: &Tags,
) -> Result<Vec<Sx>, InterfaceError> {
    let mut observed: BTreeSet<u32> = BTreeSet::new();
    for (i, body) in bodies.iter().enumerate() {
        for raw in &body.globals {
            let Some(canonical) = global_namespace.get(raw) else {
                return Err(InterfaceError::Unpinned(format!(
                    "body {i} addresses `@global.{raw}`, and no row of the chain's tag-table \
                     `globals` lane pins that crate id (pinned: {:?}). A global index no row \
                     names is a numeral standing for nothing — re-pin the table under review \
                     if the artifact was re-interned",
                    global_namespace.keys().collect::<Vec<_>>()
                )));
            };
            observed.insert(*canonical);
        }
    }
    let mut out = Vec::with_capacity(tags.globals.len());
    for (k, pin) in &tags.globals {
        if !observed.contains(k) {
            return Err(InterfaceError::Unpinned(format!(
                "a pinned global no body addresses: global {k} (`@{}`, `@global.{}`) is a row \
                 of the tag table's `globals` lane and no `global_addr` in any of the {} \
                 bod{} names it",
                pin.name,
                pin.crate_id,
                bodies.len(),
                if bodies.len() == 1 { "y" } else { "ies" }
            )));
        }
        out.push(preamble.entry_for(*k, pin)?);
    }
    if let Some(name) = preamble.surplus(&tags.globals) {
        return Err(InterfaceError::Unpinned(format!(
            "the module-table preamble declares `@{name}`, which no row of the tag table's \
             `globals` lane pins; a declaration the reader dropped unread would be an \
             erasure, so the surplus is refused by name"
        )));
    }
    Ok(out)
}
