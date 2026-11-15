// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The kernel-held CANONICAL closure digests a native fold may match
//! (`native_fold_authority.rs`).
//!
//! `native_fold_canon.tsv` holds one row per (world, constant, digest). A
//! world is one construction the kernel vouches for:
//!
//! - `clean-*` — Clean's own builders (`with_prelude`, the import-mode
//!   prelude, the bare `Environment::new` + `init_nat` path), reviewed the same
//!   way. Minted and re-derived by `native_fold_authority_tests::
//!   test_clean_canonical_fold_digests_are_pinned`.
//! - `lean-<version>` — the definitions Lean's own `Init` ships, decoded from
//!   that toolchain's `.olean` files; the world is named by the toolchain
//!   version, so every row says which Lean it was minted from:
//!   - `lean-v4.30.0-rc2`, the workspace pin (and the mixed world
//!     `clean-import+lean-v4.30.0-rc2`): the rows the decoded `Init` mints
//!     whose review passes (`fold`) and the rows those need (`definition`).
//!     Minted and re-derived by `crates/clean-olean/tests/native_fold_canon_lean.rs`.
//!   - `lean-v4.8.0`, trust-ir's toolchain (Trust's bridge gate re-checks
//!     trust-ir's Lean 4.8.0 semantics through this kernel): only a REVIEWED
//!     list of digests no other world holds (the fourteen `reduce_nat` heads
//!     and the two fresh boundaries they rest on, `instDecidableAnd` and
//!     `Bool.decEq`). A Lean 4.8.0 closure whose digest another
//!     world pins is admitted by that world and not copied here; every other
//!     Lean 4.8.0 fold key stays unpinned and δ-unfolds. Minted and re-derived
//!     by `crates/clean-olean/tests/native_fold_canon_lean_v4_8_0.rs`, which
//!     holds the list and re-checks each reviewed fold against its own
//!     definition.
//!   - `lean-v4.35.0` and `lean-v4.36.0-rc2`: only `Nat.mod` and `Nat.xor`
//!     are reviewed as folds, with their complete required boundary closures
//!     recorded as definitions. The ordinary genuine `UInt.Basic` load and
//!     the reference/production review are re-derived by
//!     `crates/clean-olean/tests/native_fold_canon_recent_nat.rs`. In particular,
//!     a known recent `Decidable` boundary does not enable an unreviewed
//!     decider reducer. These rows do not qualify a whole recent Lean world.
//!
//! A digest is admitted for its NAME whichever world pinned it: the digest
//! covers the whole δ-closure, so two worlds that pin the same digest vouch for
//! the same definition. Nothing here is keyed on provenance.
//!
//! A digest here says "this exact δ-closure is a definition the kernel
//! knows". Every row carries a ROLE (fourth column,
//! `native_fold_authority::FoldRole`):
//!
//! - `fold` — the name's own rules (its registered reducer, its `reduce_nat` /
//!   `reduce_int` fold, the string-literal expansion) were REVIEWED against
//!   this closure and fire over it (`native_fold_review.rs`: the fold, the
//!   definition with the fold bypassed, and an independent computation agree
//!   on literal inputs that include edge cases);
//! - `definition` — the closure is known but its own rules were NOT exercised
//!   against it. Such a row may only be a BOUNDARY of a `fold` row's closure or
//!   a constant a `fold` reducer reads in its arguments; its own rules stay off
//!   and the term δ-unfolds;
//! - `refused` — as `definition`, but the review exercised its rules and they
//!   DISAGREE with it (Lean 4.30's `Nat.decEq`: the reducer's `isFalse` witness
//!   names a lemma Lean's `Init` does not declare). A `refused` row vetoes a
//!   `fold` row of the same digest in every world.
//!
//! A row missing the role column is dropped (fail-closed). Nothing else admits
//! a fold. Re-pin a world with `CLEAN_NATIVE_FOLD_REPIN=1` on its battery, and
//! say why in the commit: a re-pin is a claim that every new `fold` row still
//! computes what its definition does.

use std::collections::HashMap;
use std::sync::LazyLock;

use super::native_fold_authority::FoldDigest;
use crate::name::Name;

/// What a pinned digest vouches for (the module docs; `native_fold_authority`
/// reads it).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum FoldRole {
    /// The closure is known; it may be a boundary or a recognized argument,
    /// and the name's own rules stay off (nothing exercised them here).
    Definition,
    /// The name's own rules were reviewed against the closure and fire.
    Fold,
    /// The name's own rules were reviewed against the closure and DISAGREE
    /// with it. The closure may still be a boundary or a recognized argument;
    /// the rules stay off, and a `refused` row VETOES a `fold` row of the same
    /// digest in any world — the review's outcome can depend on what lies
    /// outside the closure (a boundary's own definition, the constants a
    /// reducer's witness names), so one world's measured disagreement outranks
    /// another world's agreement.
    Refused,
}

impl FoldRole {
    /// The spelling in `native_fold_canon.tsv`.
    #[must_use]
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Definition => "definition",
            Self::Fold => "fold",
            Self::Refused => "refused",
        }
    }

    /// Parse the table's spelling; anything else is `None` (the row drops).
    #[must_use]
    pub fn parse(s: &str) -> Option<Self> {
        match s {
            "definition" => Some(Self::Definition),
            "fold" => Some(Self::Fold),
            "refused" => Some(Self::Refused),
            _ => None,
        }
    }
}

/// The pinned rows, `world<TAB>name<TAB>hex<TAB>role` (see the module docs).
pub(crate) const CANONICAL_FOLD_TSV: &str = include_str!("native_fold_canon.tsv");

/// Constants a native reducer recognizes BY NAME in its arguments that are not
/// constructors: the typeclass instances the short-circuit reducers dispatch
/// on, and the definitions the literal-shaped reducers read through. A reducer
/// that matched `instHAddNatNatNat` by name would compute `Nat.add` for any
/// `instHAddNatNatNat` a user declared, so each of these is a fold key too
/// (`native_fold_authority::fold_key_universe`): present, it must be canonical
/// for any reducer that recognizes it to fire.
pub(crate) const RECOGNIZED_ARGUMENT_NAMES: &[&str] = &[
    // `BEq.beq` short-circuit (`native_reducers_beq_shortcircuit.rs`).
    "instBEqBool",
    "instBEqChar",
    "instBEqFin",
    "instBEqInt",
    "instBEqNat",
    "instBEqString",
    "instBEqUInt8",
    "instBEqUInt16",
    "instBEqUInt32",
    "instBEqUInt64",
    "instBEqUSize",
    // `HAdd.hAdd`/… short-circuit (`native_reducers_hetero_shortcircuit.rs`).
    "instHAddNat",
    "instHAddNatNatNat",
    "instHSubNatNatNat",
    "instHMulNatNatNat",
    "instHDivNat",
    "instHDivNatNatNat",
    "instHModNat",
    "instHModNatNatNat",
    "instHPowNatNatNat",
    "instHAppendString",
    "instHAppendStringStringString",
    "instHAppendOfAppend",
    "instAppendString",
    // `Ord.compare` (`native_reducers_init.rs`).
    "instOrdNat",
    // The numeral and character carriers every literal-shaped reducer reads
    // through (`native_reducers_uint.rs`, `_bitvec.rs`, `_char.rs`, and the
    // `String`/`BEq` reducers that read characters through `_char.rs`).
    "OfNat.ofNat",
    "instOfNatNat",
    "instOfNatBitVec",
    "UInt8.ofNat",
    "UInt16.ofNat",
    "UInt32.ofNat",
    "UInt64.ofNat",
    "BitVec.ofNat",
    "BitVec.ofNatLT",
    "Char.ofNat",
];

/// Which [`RECOGNIZED_ARGUMENT_NAMES`] each registered head's reducer
/// dispatches on. A head absent here recognizes only literals and
/// constructors, whose meaning the inductive registry fixes.
const RECOGNIZED_BY_HEAD: &[(&str, &[&str])] = &[
    (
        "BEq.beq",
        &[
            "instBEqBool",
            "instBEqChar",
            "instBEqFin",
            "instBEqInt",
            "instBEqNat",
            "instBEqString",
            "instBEqUInt8",
            "instBEqUInt16",
            "instBEqUInt32",
            "instBEqUInt64",
            "instBEqUSize",
        ],
    ),
    ("HAdd.hAdd", &["instHAddNat", "instHAddNatNatNat"]),
    ("HSub.hSub", &["instHSubNatNatNat"]),
    ("HMul.hMul", &["instHMulNatNatNat"]),
    ("HDiv.hDiv", &["instHDivNat", "instHDivNatNatNat"]),
    ("HMod.hMod", &["instHModNat", "instHModNatNatNat"]),
    ("HPow.hPow", &["instHPowNatNatNat"]),
    (
        "HAppend.hAppend",
        &[
            "instHAppendString",
            "instHAppendStringStringString",
            "instHAppendOfAppend",
            "instAppendString",
        ],
    ),
    ("Ord.compare", &["instOrdNat"]),
];

/// The carriers EVERY reducer may read a literal through (numerals via
/// `OfNat`, the fixed-width and `BitVec` constructors' `Nat` views, and
/// `Char.ofNat`). Applied to every head rather than per head: a reducer that
/// reads a character or a fixed-width value reaches these through shared
/// helpers (`char_code_point`, `get_uint_ctor_val`), so a per-head list would
/// have to track helper call graphs, and a missed edge would be unsound. The
/// cost of the coupling is completeness only, and only in an environment that
/// defines one of these names non-canonically.
const RECOGNIZED_BY_EVERY_HEAD: &[&str] = &[
    "OfNat.ofNat",
    "instOfNatNat",
    "instOfNatBitVec",
    "UInt8.ofNat",
    "UInt16.ofNat",
    "UInt32.ofNat",
    "UInt64.ofNat",
    "BitVec.ofNat",
    "BitVec.ofNatLT",
    "Char.ofNat",
];

/// The constants the reducer registered for `head` recognizes by name in its
/// arguments (see [`RECOGNIZED_ARGUMENT_NAMES`]).
pub(crate) fn recognized_argument_names(head: &Name) -> &'static [Name] {
    static EVERY: LazyLock<Vec<Name>> = LazyLock::new(|| {
        RECOGNIZED_BY_EVERY_HEAD
            .iter()
            .map(|n| Name::from_string(n))
            .collect()
    });
    static MAP: LazyLock<HashMap<Name, Vec<Name>>> = LazyLock::new(|| {
        RECOGNIZED_BY_HEAD
            .iter()
            .map(|(head, names)| {
                let mut all: Vec<Name> = names.iter().map(|n| Name::from_string(n)).collect();
                all.extend(EVERY.iter().cloned());
                (Name::from_string(head), all)
            })
            .collect()
    });
    MAP.get(head).map_or(EVERY.as_slice(), Vec::as_slice)
}

/// `name ↦ [(world, digest, role)]`, parsed once from [`CANONICAL_FOLD_TSV`].
pub(crate) fn canonical_digests(
) -> &'static HashMap<Name, Vec<(&'static str, FoldDigest, FoldRole)>> {
    type Table = HashMap<Name, Vec<(&'static str, FoldDigest, FoldRole)>>;
    static TABLE: LazyLock<Table> = LazyLock::new(|| {
        let mut table: Table = HashMap::new();
        for (world, name, digest, role) in parse_rows(CANONICAL_FOLD_TSV) {
            table
                .entry(Name::from_string(name))
                .or_default()
                .push((world, digest, role));
        }
        table
    });
    &TABLE
}

/// Every pinned row as `(world, name, hex, role)`, in file order (the pin
/// batteries compare against this and rewrite their own worlds' rows).
#[must_use]
pub fn canonical_fold_rows() -> Vec<(String, String, String, String)> {
    parse_rows(CANONICAL_FOLD_TSV)
        .map(|(world, name, digest, role)| {
            (
                world.to_string(),
                name.to_string(),
                digest.to_hex(),
                role.as_str().to_string(),
            )
        })
        .collect()
}

/// Parse `world<TAB>name<TAB>hex<TAB>role` rows; blank lines and `#` comments
/// are skipped, and a malformed row — a missing or unknown role included — is
/// dropped (it can only REMOVE an admission).
pub(crate) fn parse_rows(
    text: &'static str,
) -> impl Iterator<Item = (&'static str, &'static str, FoldDigest, FoldRole)> {
    text.lines().filter_map(|line| {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            return None;
        }
        let mut cols = line.split('\t');
        let (world, name, hex, role) = (cols.next()?, cols.next()?, cols.next()?, cols.next()?);
        if cols.next().is_some() {
            return None;
        }
        Some((world, name, parse_hex(hex)?, FoldRole::parse(role)?))
    })
}

fn parse_hex(hex: &str) -> Option<FoldDigest> {
    if hex.len() != 64 {
        return None;
    }
    let mut out = [0u8; 32];
    for (i, byte) in out.iter_mut().enumerate() {
        *byte = u8::from_str_radix(hex.get(2 * i..2 * i + 2)?, 16).ok()?;
    }
    Some(FoldDigest(out))
}

#[cfg(test)]
#[path = "native_fold_canon_tests.rs"]
mod tests;
