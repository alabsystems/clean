// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **The `encodings` lane of a chain's tag table.**
//!
//! One row per aggregate whose BYTE IMAGE is not trust-ir's canonical layout —
//! a niche-encoded `Option` that stores its payload word directly, or a
//! pointer-wrapper struct whose only non-ZST field is the whole word. Without
//! them the machine reads a type under a layout the compiler did not emit,
//! which is a different program.
//!
//! Split out of `tags.rs` on 2026-09-10, when the wrapper constructor took
//! that file past the 1000-line paragon ratchet. The boundary is the natural
//! one: these types and this parser are the only part of the table that is
//! about LAYOUT rather than about naming.
//!
//! Every refusal here is falsified in `ir_mint/tests_encodings.rs`; read that
//! module's doc for what each one is for.

use super::error::CoreError;
use super::tags::Tags;

/// One derived encodings row — see [`Tags::encodings`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct EncPin {
    /// The CANONICAL aggregate index the row describes. `ir_enc_matches` keys
    /// on (KIND, id) — never on the id alone — so this number is read at
    /// `IRTy.enum_` for a niche row and at `IRTy.struct_` for a wrapper row,
    /// and the crystal's own table carries a `1` of each.
    pub canonical: u32,
    /// Which constructor, with the numbers only that constructor has.
    pub kind: EncKind,
    /// The payload type, in CORE syntax, as reader A emitted it.
    pub payload: String,
}

/// The two `IREnc` constructors, each carrying its own numbers. They are kept
/// apart rather than folded into three anonymous `Nat`s because the pair
/// (none, some) and the pair (slot, fields) obey different laws — `some` and
/// `none` must DIFFER, `slot` must be LESS THAN `fields` — and a shared shape
/// could not state either.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum EncKind {
    /// `IREnc.nicheptr k no so p`: a niche-encoded two-variant enum over a
    /// pointer payload. The zero word is variant `no`; any other word is
    /// variant `so` carrying the payload.
    Niche {
        none_variant: u32,
        some_variant: u32,
    },
    /// `IREnc.ptrwrap k i c p`: a `c`-field struct whose only non-ZST field is
    /// `i`, of the payload type. The whole word IS that field.
    Wrap { slot: u32, fields: u32 },
}

/// Parse the OPTIONAL `encodings` lane into `tags`.
///
/// Its absence means the canonical layout — which is what every chain before
/// Phase B measured, and why their tables parse unchanged.
///
/// # Errors
/// Returns `CoreError::Shape` for a malformed row; each refusal names the
/// clause it failed and why that clause exists.
pub(super) fn encodings_lane(v: &serde_json::Value, tags: &mut Tags) -> Result<(), CoreError> {
    // `encodings` is OPTIONAL and its absence means the canonical layout —
    // which is what every chain before Phase B measured, and why their tables
    // parse unchanged.
    if let Some(rows) = v.get("encodings") {
        let rows = rows
            .as_array()
            .ok_or_else(|| CoreError::Shape("`encodings` must be an array of rows".into()))?;
        for row in rows {
            let n = |field: &str| -> Result<u32, CoreError> {
                u32::try_from(
                    row.get(field)
                        .and_then(serde_json::Value::as_u64)
                        .ok_or_else(|| {
                            CoreError::Shape(format!("encodings row has no `{field}`"))
                        })?,
                )
                .map_err(|_| CoreError::Shape(format!("encodings `{field}` does not fit u32")))
            };
            let kind = row
                .get("kind")
                .and_then(serde_json::Value::as_str)
                .ok_or_else(|| CoreError::Shape("encodings row has no `kind`".into()))?;
            let kind = match kind {
                "nicheptr" => {
                    let none_variant = n("none_variant")?;
                    let some_variant = n("some_variant")?;
                    // `ir_niche_image` gives the zero word `no` and every other
                    // word `so`. If they were equal the row would claim one
                    // variant answers both, which no two-variant enum does.
                    if none_variant == some_variant {
                        return Err(CoreError::Shape(format!(
                            "encodings nicheptr row names variant {none_variant} as BOTH the zero \
                         word and the non-zero word; a niche row distinguishes two variants \
                         or it is not a niche row"
                        )));
                    }
                    EncKind::Niche {
                        none_variant,
                        some_variant,
                    }
                }
                "ptrwrap" => {
                    let slot = n("slot")?;
                    let fields = n("fields")?;
                    // `ir_spine_with_slot i c` prepends i ZSTs to `v ::
                    // (c - i - 1) ZSTs`, and `Nat.sub` TRUNCATES: at i >= c the
                    // spine is short rather than ill-formed, so the row would
                    // mint and mean something nobody derived. Refuse it here,
                    // where the reader can still say why.
                    if slot >= fields {
                        return Err(CoreError::Shape(format!(
                            "encodings ptrwrap row puts the payload at slot {slot} of a \
                         {fields}-field struct; `ir_spine_with_slot` truncates rather than \
                         faults, so a row out of range would mint a SHORT spine"
                        )));
                    }
                    EncKind::Wrap { slot, fields }
                }
                other => {
                    return Err(CoreError::Shape(format!(
                        "encodings `kind` is `{other}`; this reader mints `nicheptr` and \
                     `ptrwrap` rows, and a kind it cannot mint is refused rather than dropped"
                    )));
                }
            };
            let payload = row
                .get("payload")
                .and_then(serde_json::Value::as_str)
                .ok_or_else(|| CoreError::Shape("encodings row has no `payload`".into()))?
                .to_string();
            tags.encodings.push(EncPin {
                canonical: n("canonical")?,
                kind,
                payload,
            });
        }
        // `ir_enc_find` takes the FIRST matching row, so two rows at one KEY
        // would make the table's meaning depend on order. The key is (kind,
        // canonical) exactly as `ir_enc_matches` reads it: a niche row at 1 and
        // a wrapper row at 1 describe `enum.1` and `struct.1`, which are two
        // different types, and the crystal's own table carries both.
        let key = |e: &EncPin| (matches!(e.kind, EncKind::Wrap { .. }), e.canonical);
        let mut seen: Vec<(bool, u32)> = tags.encodings.iter().map(key).collect();
        seen.sort_unstable();
        let n = seen.len();
        seen.dedup();
        if seen.len() != n {
            return Err(CoreError::Shape(
                "two encodings rows share a (kind, canonical) key; `ir_enc_find` takes the first \
             match, so the table would mean whichever one came first"
                    .into(),
            ));
        }
    }
    Ok(())
}
