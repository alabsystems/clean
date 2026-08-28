// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Serde adapter for [`LevelVec`], replacing `smallvec`'s optional `serde`
//! feature.
//!
//! # Why this module exists
//!
//! `LevelVec` is `SmallVec<[Level; 2]>`, and it appears in exactly one
//! serde-derived position in the whole tree: the second field of
//! [`ExprKind::Const`](crate::expr::ExprKind::Const). That single field was the
//! only reason the workspace asked for `smallvec`'s `serde` feature — and that
//! feature is a `smallvec -> serde` **normal** dependency edge, which makes
//! `smallvec` one of the third-party packages that hold `serde` in Trust's
//! shipping closure. While `serde` is in that closure, every proof over a unit
//! that touches it is conditional on a compilation unit Trust does not own.
//!
//! Turning the feature off is therefore worth one attribute. This module is
//! that attribute's other half:
//!
//! ```text
//! Const(Name, #[serde(with = "crate::expr::level_vec_serde")] LevelVec),
//! ```
//!
//! Note what this does **not** buy: `smallvec` itself stays in the graph (it is
//! also required by `parking_lot_core` and `tracing-subscriber`, which do not
//! ask for `serde`). The unit count is unchanged; what is removed is one of the
//! edges keeping `serde` alive. Blocker removals and unit removals are separate
//! currencies and must be reported separately.
//!
//! # What correctness means here
//!
//! **Byte-identity with the incumbent, in both directions.** This is not a
//! preference — the encoding is *persisted*. `Environment::to_bincode`
//! (`env/serialization.rs`), the environment snapshots in `env/snapshot.rs`,
//! and the certificate archives in `cert/bundle.rs` all run
//! `bincode::serde::encode_to_vec(.., bincode::config::standard())` over values
//! that contain `ExprKind::Const`, and write the result to disk. `serde_json`
//! renders the same values into certificates and proof-search payloads.
//!
//! So a framing change here is not a compile error and not a test failure
//! somewhere nearby. It is an artifact written by yesterday's binary that today's
//! binary rejects — or, far worse, silently decodes as a *different* expression,
//! because bincode is not self-describing and a sequence and a fixed-arity tuple
//! of the same length have the same bytes. A kernel that reads back a different
//! `Const` than it wrote is a soundness problem, not an ergonomics problem.
//!
//! # How that is established
//!
//! The two impls can never be linked into one binary: whether `ExprKind` routes
//! through this module is a compile-time property of its derive. The evidence is
//! therefore layered, and the layers fail independently:
//!
//! 1. **Transcription, not reimplementation.** The bodies below are a
//!    line-for-line transcription of `smallvec 1.15.2`'s own impls
//!    (`smallvec-1.15.2/src/lib.rs:1937-1996`), quoted at each site. Every
//!    observable detail is mirrored, including the ones that only show up in
//!    error messages (`expecting` says exactly `"a sequence"`) and the
//!    `try_reserve` + `Error::custom` path that turns an allocation failure into
//!    a serde error rather than an abort.
//! 2. **A golden fixture minted by the incumbent** —
//!    `level_vec_serde_golden.json`, produced by a build in which `LevelVec`
//!    still used `smallvec`'s own impl. `tests::golden_*` assert all four
//!    directions per case: old JSON decodes under the new code, re-encodes
//!    byte-identically, old bincode bytes decode, and re-encode
//!    byte-identically. That is a differential across the implementation
//!    boundary in *time*, which is the only form available for the composed
//!    type. The fixture also carries a `kind_debug` field — a serde-independent
//!    rendering of each value — because the byte checks are round-trips and are
//!    therefore blind to a mistake made symmetrically in both directions; that
//!    hole was found by mutation, not by inspection, and
//!    `golden_decoded_values_match_a_serde_independent_oracle` closes it.
//! 3. **A live differential against the incumbent** — `smallvec` is retained as
//!    a `[dev-dependencies]` entry *with* the `serde` feature, so
//!    `tests::shim_bytes_match_the_incumbent_*` can encode the same `LevelVec`
//!    through both impls in one process and compare bytes. This is the check
//!    that keeps working when the fixture is regenerated.
//!
//! # Deviations from the incumbent
//!
//! **None are intended, and none are known.** If one is ever introduced
//! deliberately, it must be stated *here* and at the site, because a silent
//! difference in a serializer surfaces far from its cause.
//!
//! One asymmetry is worth naming even though it is not a deviation: this module
//! is written for `LevelVec` specifically, not for `SmallVec<A>` generically.
//! That is deliberate — a generic adapter would invite reuse on element types
//! whose encoding has not been differentially checked.

use serde::de::{Error as DeError, SeqAccess, Visitor};
use serde::ser::SerializeSeq;
use serde::{Deserializer, Serializer};
use std::fmt;

use super::LevelVec;
use crate::level::Level;

/// Serialize a [`LevelVec`] exactly as `smallvec`'s own `Serialize` impl does.
///
/// Transcribed from `smallvec-1.15.2/src/lib.rs:1939-1949`:
///
/// ```text
/// fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
///     let mut state = serializer.serialize_seq(Some(self.len()))?;
///     for item in self {
///         state.serialize_element(&item)?;
///     }
///     state.end()
/// }
/// ```
///
/// The length hint is `Some(len)`, not `None`: for a non-self-describing format
/// such as bincode that hint IS the length prefix, so passing `None` would
/// change the bytes.
pub(crate) fn serialize<S>(value: &LevelVec, serializer: S) -> Result<S::Ok, S::Error>
where
    S: Serializer,
{
    let mut state = serializer.serialize_seq(Some(value.len()))?;
    for item in value {
        // `&item` (a `&&Level`) mirrors the incumbent verbatim. `Serialize for
        // &T` forwards to `T`, so this is byte-identical to passing `item`;
        // the extra reference is kept only so the transcription is exact.
        state.serialize_element(&item)?;
    }
    state.end()
}

/// Deserialize a [`LevelVec`] exactly as `smallvec`'s own `Deserialize` impl
/// does.
///
/// Transcribed from `smallvec-1.15.2/src/lib.rs:1952-1996`: the entry point is
/// `deserializer.deserialize_seq(..)` with a visitor whose `expecting` message
/// is the literal `"a sequence"`.
pub(crate) fn deserialize<'de, D>(deserializer: D) -> Result<LevelVec, D::Error>
where
    D: Deserializer<'de>,
{
    deserializer.deserialize_seq(LevelVecVisitor)
}

struct LevelVecVisitor;

impl<'de> Visitor<'de> for LevelVecVisitor {
    type Value = LevelVec;

    fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        // The incumbent's exact wording. This string reaches users through
        // serde error messages on self-describing formats, so changing it is an
        // observable change even though it moves no bytes.
        formatter.write_str("a sequence")
    }

    fn visit_seq<B>(self, mut seq: B) -> Result<Self::Value, B::Error>
    where
        B: SeqAccess<'de>,
    {
        // Transcribed from `SmallVecVisitor::visit_seq`. `try_reserve` (not
        // `reserve`) is load-bearing: it turns an allocation failure into a
        // serde error instead of aborting the process, which matters when the
        // length prefix is attacker-influenced — exactly the case when reading
        // an `.olean`-adjacent artifact or a certificate archive off disk.
        let len = seq.size_hint().unwrap_or(0);
        let mut values = LevelVec::new();
        values.try_reserve(len).map_err(B::Error::custom)?;

        while let Some(value) = seq.next_element::<Level>()? {
            values.push(value);
        }

        Ok(values)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr::{Expr, ExprKind};
    use crate::name::Name;
    use serde::{Deserialize, Serialize};

    /// The fixture minted against the incumbent impl. See the module docs.
    const GOLDEN_JSON: &str = include_str!("level_vec_serde_golden.json");

    /// `#[serde(with = ...)]` routes through this module; a bare field uses
    /// whatever impl the element type provides — here, `smallvec`'s own, which
    /// the `[dev-dependencies]` entry keeps linkable. Two newtypes over the
    /// same value therefore give a same-process A/B of the two impls.
    #[derive(Serialize, Deserialize, PartialEq, Debug)]
    struct ViaShim(#[serde(with = "super")] LevelVec);

    #[derive(Serialize, Deserialize, PartialEq, Debug)]
    struct ViaIncumbent(LevelVec);

    fn bincode_cfg() -> bincode::config::Configuration {
        // The exact configuration every persisting call site uses.
        bincode::config::standard()
    }

    fn hex(bytes: &[u8]) -> String {
        bytes.iter().map(|b| format!("{b:02x}")).collect()
    }

    fn unhex(s: &str) -> Vec<u8> {
        assert!(
            s.len().is_multiple_of(2),
            "odd-length hex string in fixture: {s}"
        );
        (0..s.len())
            .step_by(2)
            .map(|i| u8::from_str_radix(&s[i..i + 2], 16).expect("fixture hex digit"))
            .collect()
    }

    /// A deterministic spread of `LevelVec` values. Lengths 0..=8 cross
    /// `SmallVec`'s inline/spilled boundary (inline capacity is 2), which is the
    /// only internal state change the container has.
    fn sample_level_vecs() -> Vec<LevelVec> {
        let u = Level::param(Name::from_string("u"));
        let v = Level::param(Name::from_string("v"));
        let shapes = [
            Level::zero(),
            Level::succ(Level::zero()),
            Level::succ(Level::succ(Level::zero())),
            u.clone(),
            v.clone(),
            Level::max(u.clone(), v.clone()),
            Level::imax(u.clone(), Level::zero()),
            Level::max(Level::succ(u.clone()), Level::imax(v.clone(), u.clone())),
        ];

        let mut out = Vec::new();
        for len in 0..=8usize {
            // Several distinct fillings per length, so a length-only bug and an
            // element-order bug are separately visible.
            for offset in 0..shapes.len() {
                let mut lv = LevelVec::new();
                for i in 0..len {
                    lv.push(shapes[(offset + i) % shapes.len()].clone());
                }
                out.push(lv);
            }
        }
        out
    }

    // ── Layer 3: live differential against the incumbent ─────────────────────

    #[test]
    fn shim_bytes_match_the_incumbent_under_bincode() {
        let cfg = bincode_cfg();
        let mut checked = 0usize;
        for lv in sample_level_vecs() {
            let shim = bincode::serde::encode_to_vec(ViaShim(lv.clone()), cfg)
                .expect("shim encodes under bincode");
            let incumbent = bincode::serde::encode_to_vec(ViaIncumbent(lv.clone()), cfg)
                .expect("incumbent encodes under bincode");
            assert_eq!(
                hex(&shim),
                hex(&incumbent),
                "bincode bytes diverge for LevelVec of len {}: {lv:?}",
                lv.len()
            );
            checked += 1;
        }
        assert_eq!(checked, 72, "sample set changed size unexpectedly");
    }

    #[test]
    fn shim_bytes_match_the_incumbent_under_serde_json() {
        for lv in sample_level_vecs() {
            let shim = serde_json::to_string(&ViaShim(lv.clone())).expect("shim -> json");
            let incumbent =
                serde_json::to_string(&ViaIncumbent(lv.clone())).expect("incumbent -> json");
            assert_eq!(
                shim,
                incumbent,
                "json diverges for LevelVec of len {}",
                lv.len()
            );
        }
    }

    /// The read direction, and specifically the CROSS direction: bytes written
    /// by one impl must decode through the other. A symmetric mistake made in
    /// both `serialize` and `deserialize` would pass a shim-only round-trip and
    /// fail here.
    #[test]
    fn each_impl_decodes_the_others_bytes() {
        let cfg = bincode_cfg();
        for lv in sample_level_vecs() {
            let from_incumbent = bincode::serde::encode_to_vec(ViaIncumbent(lv.clone()), cfg)
                .expect("incumbent encodes");
            let (decoded, _): (ViaShim, usize) =
                bincode::serde::decode_from_slice(&from_incumbent, cfg)
                    .expect("shim decodes incumbent bytes");
            assert_eq!(decoded.0, lv, "shim mis-decoded incumbent bytes");

            let from_shim =
                bincode::serde::encode_to_vec(ViaShim(lv.clone()), cfg).expect("shim encodes");
            let (decoded, _): (ViaIncumbent, usize) =
                bincode::serde::decode_from_slice(&from_shim, cfg)
                    .expect("incumbent decodes shim bytes");
            assert_eq!(decoded.0, lv, "incumbent mis-decoded shim bytes");
        }
    }

    // ── Layer 2: golden fixture minted by the incumbent ──────────────────────

    #[derive(Deserialize)]
    struct GoldenFile {
        cases: Vec<GoldenCase>,
    }

    #[derive(Deserialize)]
    struct GoldenCase {
        label: String,
        kind_json: String,
        kind_bincode_hex: String,
        expr_json: String,
        expr_bincode_hex: String,
        /// A serde-INDEPENDENT rendering of the value, minted by the incumbent
        /// build. See `golden_decoded_values_match_a_serde_independent_oracle`
        /// for why the byte checks alone are not enough.
        kind_debug: String,
    }

    fn golden() -> GoldenFile {
        serde_json::from_str(GOLDEN_JSON).expect("golden fixture parses")
    }

    /// Artifacts written before this change still load, and re-encode to the
    /// same bytes. Four assertions per case: JSON in, JSON out, bincode in,
    /// bincode out — for both `ExprKind` and the `Expr` that actually gets
    /// persisted.
    #[test]
    fn golden_artifacts_round_trip_byte_identically() {
        let cfg = bincode_cfg();
        let file = golden();
        assert_eq!(file.cases.len(), 8, "golden fixture case count changed");

        for case in &file.cases {
            let ctx = &case.label;

            let kind: ExprKind = serde_json::from_str(&case.kind_json)
                .unwrap_or_else(|e| panic!("{ctx}: golden kind_json no longer decodes: {e}"));
            assert_eq!(
                serde_json::to_string(&kind).expect("kind -> json"),
                case.kind_json,
                "{ctx}: ExprKind JSON re-encode is not byte-identical"
            );

            let want = unhex(&case.kind_bincode_hex);
            let (decoded, _): (ExprKind, usize) = bincode::serde::decode_from_slice(&want, cfg)
                .unwrap_or_else(|e| panic!("{ctx}: golden kind bincode no longer decodes: {e}"));
            assert_eq!(
                serde_json::to_string(&decoded).expect("decoded -> json"),
                case.kind_json,
                "{ctx}: ExprKind decoded from golden bincode is not the golden value"
            );
            assert_eq!(
                hex(&bincode::serde::encode_to_vec(&kind, cfg).expect("kind -> bincode")),
                case.kind_bincode_hex,
                "{ctx}: ExprKind bincode re-encode is not byte-identical"
            );

            let expr: Expr = serde_json::from_str(&case.expr_json)
                .unwrap_or_else(|e| panic!("{ctx}: golden expr_json no longer decodes: {e}"));
            assert_eq!(
                serde_json::to_string(&expr).expect("expr -> json"),
                case.expr_json,
                "{ctx}: Expr JSON re-encode is not byte-identical"
            );

            let want = unhex(&case.expr_bincode_hex);
            let (decoded, _): (Expr, usize) = bincode::serde::decode_from_slice(&want, cfg)
                .unwrap_or_else(|e| panic!("{ctx}: golden expr bincode no longer decodes: {e}"));
            assert_eq!(
                serde_json::to_string(&decoded).expect("decoded -> json"),
                case.expr_json,
                "{ctx}: Expr decoded from golden bincode is not the golden value"
            );
            assert_eq!(
                hex(&bincode::serde::encode_to_vec(&expr, cfg).expect("expr -> bincode")),
                case.expr_bincode_hex,
                "{ctx}: Expr bincode re-encode is not byte-identical"
            );
        }
    }

    /// **This test exists because a mutation got past the one above it.**
    ///
    /// `golden_artifacts_round_trip_byte_identically` asserts
    /// `encode(decode(bytes)) == bytes`. That is a ROUND-TRIP, so any mistake
    /// made symmetrically in `serialize` and `deserialize` cancels out and the
    /// check stays green. Measured: reversing the element order in BOTH
    /// directions left that test, and the shim's own round-trip test, passing.
    ///
    /// The fix is an oracle that does not go through serde at all. `Debug` is
    /// derived structurally on `ExprKind`/`Level`/`Name`, so comparing the
    /// decoded value's `Debug` rendering against the one the INCUMBENT build
    /// minted pins the value — element order included — independently of any
    /// encoder.
    #[test]
    fn golden_decoded_values_match_a_serde_independent_oracle() {
        let cfg = bincode_cfg();
        for case in &golden().cases {
            let ctx = &case.label;

            let from_json: ExprKind = serde_json::from_str(&case.kind_json)
                .unwrap_or_else(|e| panic!("{ctx}: golden kind_json no longer decodes: {e}"));
            assert_eq!(
                format!("{from_json:?}"),
                case.kind_debug,
                "{ctx}: value decoded from golden JSON is not the value the incumbent encoded"
            );

            let (from_bin, _): (ExprKind, usize) =
                bincode::serde::decode_from_slice(&unhex(&case.kind_bincode_hex), cfg)
                    .unwrap_or_else(|e| panic!("{ctx}: golden bincode no longer decodes: {e}"));
            assert_eq!(
                format!("{from_bin:?}"),
                case.kind_debug,
                "{ctx}: value decoded from golden bincode is not the value the incumbent encoded"
            );
        }
    }

    /// The fixture must actually exercise the spilled representation; a fixture
    /// that only ever held 0-2 levels would pass while an inline/heap-sensitive
    /// bug shipped.
    #[test]
    fn golden_fixture_covers_the_spilled_representation() {
        let file = golden();
        let labels: Vec<&str> = file.cases.iter().map(|c| c.label.as_str()).collect();
        for required in [
            "len0_empty",
            "len2_at_inline_cap",
            "len3_spilled",
            "len8_spilled",
        ] {
            assert!(
                labels.contains(&required),
                "golden fixture lost required case {required}; have {labels:?}"
            );
        }
    }

    // ── Shape checks that pin the framing itself ─────────────────────────────

    /// A sequence and a tuple encode to the same bincode bytes at a fixed
    /// length, so bincode alone cannot see a seq/tuple confusion. JSON can:
    /// a sequence renders as `[..]`.
    #[test]
    fn the_wire_shape_is_a_sequence() {
        let lv = LevelVec::from_vec(vec![Level::zero(), Level::succ(Level::zero())]);
        let json = serde_json::to_string(&ViaShim(lv)).expect("-> json");
        assert_eq!(json, r#"["Zero",{"Succ":"Zero"}]"#);
    }

    #[test]
    fn empty_and_spilled_lengths_round_trip_through_the_shim() {
        let cfg = bincode_cfg();
        for lv in sample_level_vecs() {
            let bytes = bincode::serde::encode_to_vec(ViaShim(lv.clone()), cfg).expect("encode");
            let (back, _): (ViaShim, usize) =
                bincode::serde::decode_from_slice(&bytes, cfg).expect("decode");
            assert_eq!(back.0, lv);
        }
    }
}
