// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Clean-side parsing of the two WRITE instructions** — `IRInst.insertfield`
//! and `IRInst.store` — for the A1 comparator.
//!
//! Split out of `emitted_cfg_parse_clean.rs` at birth (2026-08-20): that file
//! was 460 lines against the 500-line convention when these lanes landed, and
//! the seam is the same one `emitted_cfg_parse_memory.rs` sits on for the
//! emitted side. The rule from the 2026-08-16 lane-completeness audit applies
//! unchanged: a slot this file cannot read must FAIL LOUDLY rather than parse
//! to nothing on both sides and compare equal.

use std::collections::BTreeMap;

use super::super::emitted_cfg_types::norm_clean_ty;

/// `ir_dN` / bare numeral -> N. The same reader `parse_clean` applies to every
/// operand slot: `trim_start_matches` rather than `strip_prefix`, so a field
/// index written as a bare `Nat` literal reads the same as one written through
/// the `ir_dK` numeral chain.
fn n(s: &str) -> Option<u32> {
    s.trim().trim_start_matches("ir_d").parse::<u32>().ok()
}

/// `IRInst.insertfield <ty> <agg> <k> <v>` — all four operands, and the ONE
/// result the node must bind.
///
/// The machine steps it to
/// `ir_bind_result s rs (ir_insert_field (ir_getd s a) k (ir_getd s v))`:
/// `a` and `v` are value reads, `k` selects the slot `ir_if_at` bounds-checks
/// and `ir_vals_set` rewrites — the semantic payload the lane exists for — and
/// `t` is discarded by Clean's step but printed by the artifact, which is the
/// same artifact-transcription reason `extract_tys` and `load_tys` are
/// compared. Arity and the result count are REFUSED rather than half-read: a
/// term with a fifth operand has a slot this parser does not read, and a node
/// that binds no result (or two) is not a transcription of a value producer
/// routed through `ir_bind_result`.
pub(super) fn clean_insertfield(
    id: u32,
    inst: &str,
    t: &[String],
    results: &[u32],
    aliases: &BTreeMap<String, String>,
    insertfields: &mut BTreeMap<u32, Vec<(u32, String, u32, u32, u32)>>,
) {
    assert_eq!(
        t.len(),
        5,
        "the registered insertfield carries {} operands ({inst}); `IRInst.insertfield : IRTy -> \
         Nat -> Nat -> Nat -> IRInst` has exactly four and this parser reads all four",
        t.len().saturating_sub(1)
    );
    assert_eq!(
        results.len(),
        1,
        "the registered insertfield binds {results:?} ({inst}); it is a value producer routed \
         through ir_bind_result and must bind exactly one result"
    );
    if let (Some(a), Some(k), Some(v)) = (
        t.get(2).and_then(|s| n(s)),
        t.get(3).and_then(|s| n(s)),
        t.get(4).and_then(|s| n(s)),
    ) {
        insertfields.entry(id).or_default().push((
            results[0],
            norm_clean_ty(t.get(1).map_or("", String::as_str), aliases),
            a,
            k,
            v,
        ));
    }
}

/// `IRInst.store <ty> <ptr> <val> <vol>` — pointer FIRST, the reverse of the
/// printed operand order (`store {ty} %{value}, ptr %{ptr}`), which is why the
/// lane both sides normalize into is `(POINTER, TYPE, value)` and this parser
/// reads the constructor slots positionally rather than mirroring the print.
///
/// The machine steps it to `ir_store_exec s (ir_getd s p) (ir_getd s v)` and
/// binds nothing, so a result on the node is REFUSED like `assert`'s. The
/// VOLATILE slot is read and then refused when `Bool.true`: the lane
/// deliberately carries no volatile slot (see `Cfg::stores`), the emitted
/// parser refuses the `volatile ` prefix symmetrically, and a slot refused on
/// both sides can never agree by both being dropped. An unreadable value there
/// is a panic for the same reason it is on `load` — it would compare equal to
/// nothing rather than to the artifact.
pub(super) fn clean_store(
    id: u32,
    inst: &str,
    t: &[String],
    results: &[u32],
    aliases: &BTreeMap<String, String>,
    stores: &mut BTreeMap<u32, Vec<(u32, String, u32)>>,
) {
    assert_eq!(
        t.len(),
        5,
        "the registered store carries {} operands ({inst}); `IRInst.store : IRTy -> Nat -> Nat \
         -> Bool -> IRInst` has exactly four and this parser reads all four",
        t.len().saturating_sub(1)
    );
    assert!(
        results.is_empty(),
        "the registered store BINDS a result ({results:?}) ({inst}); store is routed through \
         ir_store_exec and the machine advances past it without binding"
    );
    match t.get(4).map(String::as_str) {
        Some("Bool.false") => {}
        Some("Bool.true") => panic!(
            "the registered store is VOLATILE ({inst}), and the store lane has no slot for the \
             flag. The emitted parser refuses the `volatile ` prefix for the same reason; widen \
             the lane to carry it (as `load_tys` does) rather than dropping it on both sides."
        ),
        other => panic!(
            "the registered store's VOLATILE slot is {other:?}, which is neither Bool.true nor \
             Bool.false ({inst})."
        ),
    }
    if let (Some(p), Some(v)) = (t.get(2).and_then(|s| n(s)), t.get(3).and_then(|s| n(s))) {
        stores.entry(id).or_default().push((
            p,
            norm_clean_ty(t.get(1).map_or("", String::as_str), aliases),
            v,
        ));
    }
}
