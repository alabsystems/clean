// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **The AGGREGATE lanes of `project`: which crate `enum`/`struct` a body's
//! `enum.N` / `struct.N` denotes, compared instead of erased.**
//!
//! Until 2026-09-10 nothing here existed and nothing anywhere did this job.
//! `Reader::intern` hands out canonical aggregate indices by FIRST-SEEN order
//! within ONE body, counting from 0, with no reference to the tag table; the
//! `enums`/`structs` lanes carry a `crate_id`; and `project` related the two
//! nowhere — measured, `interface.rs` mentioned neither lane. That mattered
//! because the lane's crate id is what reaches the committed PROOF artifact:
//! `Tags::alias_defs` writes `def <alias> : IRTy := IRTy.enum_ ir_d<crate_id>`,
//! and this tree's `ir_lzc.defs.txt` line 1 is
//! `def ir_lzc_tlevel : IRTy := IRTy.enum_ ir_d2`. So the NUMERAL in the spec
//! came from the lane and the INDEX in the core came from the body, with
//! nothing checking they were about the same type.
//!
//! It was harmless on every chain minted so far, and harmless BY CONSTRUCTION
//! rather than by luck: each was assembled from ONE artifact, so first-seen
//! order within the module and the lane's order are the same walk. That
//! argument does not survive a module assembled from TWO artifacts with
//! independent type numbering, which is what the Phase-B five-body module is —
//! its crate bodies name `enum.2` while its sidecar bodies name `enum.0` and
//! `enum.1`, and all three would claim canonical 0.
//!
//! FOUR DIRECTIONS, each a refusal naming its slot, the same shape
//! [`super::interface_globals::check_globals`] takes one namespace over:
//!
//! * two bodies that disagree about what a canonical index denotes — a module
//!   cannot hold one `(enum k)` that means two crate types;
//! * an observed canonical index no row PINS — the mint would have to invent
//!   an alias, and `Tags::enum_alias` is already fail-closed, but refusing
//!   here names the body and the id rather than dying in the minter;
//! * a pinned row NOTHING in the module reaches — a pin over nothing, exactly
//!   as an unaddressed global is. "Reaches" is the UNION of instruction
//!   positions and INTERFACE positions, and that distinction is not a detail:
//!   `ir_hlb` pins `structs` canonical 0 (`ir_hlb_tself`, `struct.29`) and
//!   NEITHER of its two bodies names that id in an instruction — it appears
//!   only as the root's parameter type, `bb0(%0: struct.29)`, which reaches
//!   the lane through `Tags::canon_ty` instead. Measured: a first cut of this
//!   check that looked at instruction positions alone refused that committed
//!   chain, which is what running a new refusal against the whole corpus is
//!   for;
//! * an observed index whose raw id DISAGREES with the row's `crate_id` — the
//!   one this lane exists for, and the one the constructed pair in
//!   `crystal_a2_mint/blind_slots_aggregate.rs` demonstrates.

use std::collections::BTreeMap;

use super::emitted::ObservedTags;
use super::error::InterfaceError;
use super::tags::Tags;

/// Every `enum.N` / `struct.N` id a body reaches through its INTERFACE rather
/// than through an instruction — parameter and block-parameter types.
///
/// Read off the RAW interface (the ids the artifact printed), never the
/// canonicalized one: the canonical form has already been through the lane, so
/// asking it which ids were used would be asking the lane about itself.
fn interface_ids(body: &ObservedTags, lane: &str) -> Vec<u32> {
    let prefix = format!("{lane}.");
    let mut out = Vec::new();
    for p in body
        .interface
        .params
        .iter()
        .chain(body.interface.block_params.iter())
    {
        let mut rest = p.ty.as_str();
        while let Some(at) = rest.find(&prefix) {
            rest = &rest[at + prefix.len()..];
            let digits: String = rest.chars().take_while(char::is_ascii_digit).collect();
            if let Ok(id) = digits.parse::<u32>() {
                out.push(id);
            }
        }
    }
    out
}

/// One lane's name, its observation in each body, and its pins.
struct Lane<'a> {
    /// `enums` or `structs`, for the refusal text.
    name: &'a str,
    /// canonical index -> the raw id each body printed, per body.
    observed: Vec<&'a BTreeMap<u32, u32>>,
    /// canonical index -> (crate id, alias).
    pins: &'a BTreeMap<u32, (u32, String)>,
    /// Raw ids reached through an interface type rather than an instruction.
    interface_ids: Vec<u32>,
}

/// Compare both aggregate lanes across every body of the module.
///
/// # Errors
/// Returns [`InterfaceError`] on any of the four directions in the module
/// documentation above.
pub(super) fn check_aggregates(bodies: &[ObservedTags], tags: &Tags) -> Result<(), InterfaceError> {
    for lane in [
        Lane {
            name: "enum",
            observed: bodies.iter().map(|b| &b.enums).collect(),
            pins: &tags.enums,
            interface_ids: bodies
                .iter()
                .flat_map(|b| interface_ids(b, "enum"))
                .collect(),
        },
        Lane {
            name: "struct",
            observed: bodies.iter().map(|b| &b.structs).collect(),
            pins: &tags.structs,
            interface_ids: bodies
                .iter()
                .flat_map(|b| interface_ids(b, "struct"))
                .collect(),
        },
    ] {
        check_lane(&lane)?;
    }
    Ok(())
}

fn check_lane(lane: &Lane<'_>) -> Result<(), InterfaceError> {
    // 1. The bodies must agree with EACH OTHER first. Each interns from 0
    //    independently, so this is the direction that catches two artifacts
    //    merged into one module without their type tables being reconciled.
    let mut seen: BTreeMap<u32, (u32, usize)> = BTreeMap::new();
    for (i, body) in lane.observed.iter().enumerate() {
        for (canonical, raw) in body.iter() {
            let canonical = *canonical;
            match seen.get(&canonical) {
                Some((prev, j)) if prev != raw => {
                    return Err(InterfaceError::Mismatch {
                        slot: format!("{} {canonical}", lane.name),
                        pinned: format!("body {j} printed `{}.{prev}`", lane.name),
                        found: format!(
                            "body {i} printed `{}.{raw}` for the SAME canonical index — one \
                             module cannot hold one `({} {canonical})` that means two crate \
                             types. If these bodies came from different artifacts, their type \
                             tables have to be reconciled before they are one module",
                            lane.name, lane.name
                        ),
                    })
                }
                Some(_) => {}
                None => {
                    seen.insert(canonical, (*raw, i));
                }
            }
        }
    }

    // 2/4. Every observed index must be pinned, and pinned to the id the
    //      bodies actually printed.
    //
    //      Direction 4 — the id disagreeing with the row — is UNREACHABLE
    //      through `project` as of the aggregate namespace, and saying so is
    //      better than leaving it reading as a live guard. `project` pre-seeds
    //      the reader with the lane, so a pinned id resolves to ITS canonical
    //      index whoever names it and the two cannot differ; a body naming an
    //      id the lane does NOT pin interns above the lane and is caught by
    //      direction 2 instead. It is kept as an INVARIANT on the seeding
    //      rather than deleted: if it ever fires, the namespace and the lane
    //      have come apart, and that is worth a refusal rather than a wrong
    //      type in the proof.
    for (canonical, (raw, i)) in &seen {
        match lane.pins.get(canonical) {
            None => {
                let pinned: Vec<String> = lane
                    .pins
                    .iter()
                    .map(|(k, (id, alias))| format!("{k} -> `{}.{id}` (`{alias}`)", lane.name))
                    .collect();
                return Err(InterfaceError::Unpinned(format!(
                    "body {i} names `{}.{raw}`, which reader B interned at canonical index \
                     {canonical} because no row of the chain's tag-table `{}s` lane pins that \
                     crate id. The lane pins: [{}]. The lane's `crate_id` is what `alias_defs` \
                     writes into the committed spec, so an unpinned index is a type the proof \
                     would have to name without knowing which one it is — if this is a producer \
                     re-interning and not a different type, the fix is to move the pinned id to \
                     `{raw}`",
                    lane.name,
                    lane.name,
                    pinned.join(", ")
                )));
            }
            Some((pinned, alias)) if pinned != raw => {
                return Err(InterfaceError::Mismatch {
                    slot: format!("{} {canonical} (`{alias}`)", lane.name),
                    pinned: format!("`{}.{pinned}`", lane.name),
                    found: format!(
                        "body {i} printed `{}.{raw}`. `{alias}` is minted as \
                         `IRTy.{}_ ir_d{pinned}` whatever the body said, so this is the \
                         disagreement that would put the WRONG crate type into the proof",
                        lane.name, lane.name
                    ),
                })
            }
            Some(_) => {}
        }
    }

    // 3. A pinned row NOTHING in the module reaches is a pin over nothing.
    //    Reached = named in an instruction (the ids above) OR named in an
    //    interface type, which reaches the lane through `Tags::canon_ty`.
    let reached: std::collections::BTreeSet<u32> = seen
        .values()
        .map(|(raw, _)| *raw)
        .chain(lane.interface_ids.iter().copied())
        .collect();
    for (canonical, (raw, alias)) in lane.pins {
        if !reached.contains(raw) {
            return Err(InterfaceError::Unpinned(format!(
                "the chain's `{}s` lane pins canonical {canonical} (`{alias}`, `{}.{raw}`) and \
                 nothing in this module reaches it — not an instruction, not a parameter type. \
                 A row nothing reaches is a pin over nothing, exactly as an unaddressed global \
                 is, and `alias_defs` would still emit its definition into the spec",
                lane.name, lane.name
            )));
        }
    }
    Ok(())
}
