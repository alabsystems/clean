// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Memory-instruction parsing for the emitted-side A1 comparator.

use std::collections::BTreeMap;

use super::{id_of, norm_emitted_ty};

/// Read a `load` — **every slot it prints**, and refuse the one slot Clean's
/// `IRInst.load` has no room for.
///
/// The printed form is
/// `[volatile ]load {ty}, ptr %{ptr}[, align {a}]` (`trust-ir/src/display.rs:672`);
/// the registered constructor is `IRInst.load : IRTy → Nat → Bool → IRInst`.
///
/// **Two defects the 2026-08-19 operand audit found here, both measured:**
///
/// * the pointer was taken with `t.last()`, which is the pointer only while
///   nothing follows it. On `load u8, ptr %0, align 8` the last token is `8`,
///   and `id_of("8")` is `Some(8)` — so the load would have been recorded as
///   reading `%8`, a binding that need not even exist, with nothing failing.
///   The pointer is now read from its own slot, positionally.
/// * the TYPE was never read at all, on either side. That is the slot the
///   flagship chain disagrees in.
///
/// `align` is REFUSED rather than dropped, because Clean's `load` has no
/// alignment operand: there is nothing for it to be compared against, and a
/// slot a parser cannot read must never parse to nothing on both sides and
/// compare equal. That is the same `?usize` rule `switch`'s block arguments and
/// `assert`'s extra operands are refused under.
pub(super) fn emitted_load(
    b: u32,
    r: u32,
    t: &[String],
    loads: &mut BTreeMap<u32, Vec<(u32, u32)>>,
    load_tys: &mut BTreeMap<u32, Vec<(u32, String, bool)>>,
) {
    let volatile = t.first().map(String::as_str) == Some("volatile");
    let i = usize::from(volatile);
    if t.get(i).map(String::as_str) != Some("load") {
        return;
    }
    assert_eq!(
        t.get(i + 2).map(String::as_str),
        Some("ptr"),
        "a `load`'s pointer operand is printed as `ptr %N` and this one is not: {t:?}"
    );
    assert_eq!(
        t.len(),
        i + 4,
        "a `load` carries {} tokens ({t:?}), and this parser reads exactly the type, the pointer \
         and the volatile flag. The extra slot is almost certainly `, align N`, which Clean's \
         `IRInst.load : IRTy -> Nat -> Bool -> IRInst` has NO operand for — so it cannot be \
         compared, and a slot that cannot be compared is refused here rather than dropped into \
         nothing on both sides. (It is also the slot that used to make `t.last()` return the \
         ALIGNMENT where the pointer was meant to be.)",
        t.len()
    );
    let Some(ptr) = t.get(i + 3).and_then(|s| id_of(s)) else {
        panic!("a `load`'s pointer operand is not an SSA id: {t:?}");
    };
    loads.entry(b).or_default().push((r, ptr));
    load_tys.entry(b).or_default().push((
        r,
        norm_emitted_ty(t.get(i + 1).map_or("", String::as_str)),
        volatile,
    ));
}

/// Read a `gep` — **every slot it prints**, and refuse anything it does not.
///
/// The printed form is `gep [inbounds ]{ty}, ptr %{base}, %{i0}[, %{i1}…]`
/// and the registered constructor is
/// `IRInst.gep : IRTy → Nat → IRList Nat → Bool → IRInst`. All four slots are
/// semantic input to `ir_gep_eval`, which offsets the base by `ir_sum_idx` of
/// the whole index list, so:
///
/// * the BASE decides which object is addressed;
/// * the INDEX LIST is summed, so keeping only the first index computes a
///   different address while binding the same SSA id — which is why the list is
///   read as a list;
/// * the TYPE is the element scale trust-ir's own semantics multiplies by;
/// * `inbounds` is the no-wrap licence, and it is a `Bool` field of the
///   registered constructor, so it has somewhere to be compared.
///
/// An index that is not an SSA id is a REFUSAL rather than a dropped slot: a
/// constant index would be a shape this parser cannot represent, and a slot
/// that cannot be compared must never parse to nothing on both sides.
pub(super) fn emitted_gep(
    b: u32,
    r: u32,
    t: &[String],
    geps: &mut BTreeMap<u32, Vec<(u32, String, u32, Vec<u32>, bool)>>,
) {
    let inbounds = t.get(1).map(String::as_str) == Some("inbounds");
    let i = 1 + usize::from(inbounds);
    assert_eq!(
        t.get(i + 1).map(String::as_str),
        Some("ptr"),
        "a `gep`'s base operand is printed as `ptr %N` and this one is not: {t:?}"
    );
    let Some(base) = t.get(i + 2).and_then(|s| id_of(s)) else {
        panic!("a `gep`'s base operand is not an SSA id: {t:?}");
    };
    assert!(
        t.len() > i + 3,
        "a `gep` with no index at all: {t:?}. `ir_sum_idx` of an empty list is zero, so such a \
         term would be a no-op offset that this parser must not invent."
    );
    let idxs: Vec<u32> = t[i + 3..]
        .iter()
        .map(|tok| {
            id_of(tok).unwrap_or_else(|| {
                panic!(
                    "a `gep` index is not an SSA id ({tok:?} in {t:?}); `IRInst.gep` takes an \
                     `IRList Nat` of SSA ids and there is nowhere to put anything else"
                )
            })
        })
        .collect();
    geps.entry(b).or_default().push((
        r,
        norm_emitted_ty(t.get(i).map_or("", String::as_str)),
        base,
        idxs,
        inbounds,
    ));
}
