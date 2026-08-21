// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Compile-time pin for the enum discriminants the crystal chains prove about.**
//!
//! # The hole this closes
//!
//! A crystal chain proves a theorem about the trust-ir `trustc` emits for one
//! shipped body. Several of those bodies are `match`es over a kernel enum, and
//! the emitted IR does not mention variant NAMES — it switches on the numeric
//! discriminant:
//!
//! ```text
//! mode::CleanMode::has_cubical_layer   switch %3 [ 2: bb1 3: bb2 default: bb3 ]
//! mode::CleanMode::from_source_system  switch %2 [ 0: bb1 … 9: bb10 11: bb11 default: bb12 ]
//! <ExprPathStep as Clone>::clone       switch %3 [ 0: bb1 … 9: bb10 default: bb11 ]
//! ```
//!
//! Clean's side of each proof encodes the *same* numbers — `clean_mode_tag`
//! maps `CleanModeR`'s six constructors to `ir_d0..ir_d5`. So the proof and the
//! artifact are joined at a numeric mapping that, before this module, appeared
//! in the source **nowhere at all**.
//!
//! Be precise about what was and was not guaranteed. The Rust Reference does
//! guarantee the *values*: an unspecified first discriminant is `0` and each
//! later one is the previous plus one, so `Cubical` was 2 **given the
//! declaration order**. What nothing guaranteed was the declaration order
//! itself. Reorder two variants of a default-repr enum — a refactor no reviewer
//! would blink at, and one that changes no behaviour of the Rust program — and
//! `Cubical` moves off 2 while `ir_h2_module`, `ir_fs_module`, the recorded
//! fixtures and every gate over them stay byte-identical. The chain would go on
//! reporting green while proving something false about the shipped body.
//!
//! # What is pinned, and by what
//!
//! Two mechanisms, deliberately different in kind:
//!
//! 1. **`#[repr(u8)]` + explicit `= N` on the enum itself** (`mode.rs`,
//!    `tc/expr_location.rs`). This is the primary fix and it is structural
//!    rather than assertive: with every discriminant written down, a REORDER no
//!    longer changes any number, and an INSERTION without a fresh number is a
//!    hard `rustc` error (E0081, duplicate discriminant) rather than a silent
//!    renumbering of everything below it. `#[repr(u8)]` additionally pins the
//!    tag ENCODING to the `u8` that the emitted `extractfield u8 %2, 0` reads,
//!    instead of leaving it to layout choice.
//!
//! 2. **The `const _: () = assert!(…)` block below.** The explicit values make
//!    a reorder harmless; they do not stop someone from *editing* a value. The
//!    asserts are the tripwire for that: they name each number once more, at a
//!    site whose doc comment says why it may not move, and they fail the build —
//!    not a test, the BUILD — if it does.
//!
//! `level::Level` is a chained enum too (`Level::is_zero`, `Level::kind_ord`;
//! `level_kind_tag` maps its five constructors to `ir_d0..ir_d4`) and is
//! deliberately NOT pinned here: it carries payloads, so `as u8` does not apply
//! and `#[repr(u8)]` would be a layout change to the kernel's hottest type.
//! Its declaration order is pinned instead by `data/crystal_enum_tag_pin.json`
//! and `scripts/check_enum_tag_pin.py`, which cover all four enums and also
//! cross-check the recorded artifacts. See the CRYSTAL TAG PIN comment in
//! `level/mod.rs` for why the repr flip is a separate, differentially-gated
//! change and not a thing to slip into this commit.
//!
//! # What this does NOT claim
//!
//! Nothing here says the emitted artifact is *currently* in agreement with the
//! registered module — that is link 2a's job, and `crystal_a1_lineage` owns it.
//! This module only makes the numeric mapping the two share impossible to move
//! by accident.

use crate::mode::{CleanMode, SourceSystem};
use crate::tc::expr_location::ExprPathStep;

// ---------------------------------------------------------------------------
// The pinned tables. Declaration order, and the discriminant each variant
// carries. `scripts/check_enum_tag_pin.py` re-derives both from the source of
// the enum itself and fails if either disagrees with these tables or with
// `data/crystal_enum_tag_pin.json`.
// ---------------------------------------------------------------------------

/// `mode::CleanMode` — variant name and pinned discriminant, declaration order.
///
/// Read by `crystal_mode_tags_match_the_pin` and by the manifest gate.
#[cfg(test)]
const CLEAN_MODE_TAGS: [(&str, u8); 6] = [
    ("Constructive", 0),
    ("Impredicative", 1),
    ("Cubical", 2),
    ("Directed", 3),
    ("Classical", 4),
    ("SetTheoretic", 5),
];

/// `mode::SourceSystem` — variant name and pinned discriminant, declaration order.
#[cfg(test)]
const SOURCE_SYSTEM_TAGS: [(&str, u8); 12] = [
    ("Lean4", 0),
    ("Coq", 1),
    ("Agda", 2),
    ("CubicalAgda", 3),
    ("IsabelleHOL", 4),
    ("HOLLight", 5),
    ("HOL4", 6),
    ("Mizar", 7),
    ("MetamathZFC", 8),
    ("MetamathSet", 9),
    ("PVS", 10),
    ("ACL2", 11),
];

/// `tc::expr_location::ExprPathStep` — variant name and pinned discriminant,
/// declaration order.
#[cfg(test)]
const EXPR_PATH_STEP_TAGS: [(&str, u8); 11] = [
    ("AppFn", 0),
    ("AppArg", 1),
    ("LamBody", 2),
    ("LamType", 3),
    ("PiDom", 4),
    ("PiBody", 5),
    ("LetType", 6),
    ("LetVal", 7),
    ("LetBody", 8),
    ("MDataExpr", 9),
    ("ProjExpr", 10),
];

// ---------------------------------------------------------------------------
// The tripwire. Editing a discriminant fails the BUILD, here, with this file's
// doc comment one scroll away.
// ---------------------------------------------------------------------------

const _: () = {
    assert!(CleanMode::Constructive as u8 == 0);
    assert!(CleanMode::Impredicative as u8 == 1);
    // 2 and 3 are the two arms `has_cubical_layer` switches on.
    assert!(CleanMode::Cubical as u8 == 2);
    assert!(CleanMode::Directed as u8 == 3);
    assert!(CleanMode::Classical as u8 == 4);
    assert!(CleanMode::SetTheoretic as u8 == 5);
};

const _: () = {
    assert!(SourceSystem::Lean4 as u8 == 0);
    assert!(SourceSystem::Coq as u8 == 1);
    assert!(SourceSystem::Agda as u8 == 2);
    assert!(SourceSystem::CubicalAgda as u8 == 3);
    assert!(SourceSystem::IsabelleHOL as u8 == 4);
    assert!(SourceSystem::HOLLight as u8 == 5);
    assert!(SourceSystem::HOL4 as u8 == 6);
    assert!(SourceSystem::Mizar as u8 == 7);
    assert!(SourceSystem::MetamathZFC as u8 == 8);
    assert!(SourceSystem::MetamathSet as u8 == 9);
    // `PVS` is the value the emitted `from_source_system` switch leaves to its
    // DEFAULT edge; `ACL2` is the explicit `11:` arm. Swapping them is exactly
    // the silent break this pin exists for.
    assert!(SourceSystem::PVS as u8 == 10);
    assert!(SourceSystem::ACL2 as u8 == 11);
};

const _: () = {
    assert!(ExprPathStep::AppFn as u8 == 0);
    assert!(ExprPathStep::AppArg as u8 == 1);
    assert!(ExprPathStep::LamBody as u8 == 2);
    assert!(ExprPathStep::LamType as u8 == 3);
    assert!(ExprPathStep::PiDom as u8 == 4);
    assert!(ExprPathStep::PiBody as u8 == 5);
    assert!(ExprPathStep::LetType as u8 == 6);
    assert!(ExprPathStep::LetVal as u8 == 7);
    assert!(ExprPathStep::LetBody as u8 == 8);
    assert!(ExprPathStep::MDataExpr as u8 == 9);
    // The value the emitted `clone` leaves to its DEFAULT edge.
    assert!(ExprPathStep::ProjExpr as u8 == 10);
};

// The emitted bodies read the tag as `extractfield u8`. A one-byte enum is what
// makes that reading right; `#[repr(u8)]` is what makes it guaranteed.
const _: () = {
    assert!(size_of::<CleanMode>() == 1);
    assert!(size_of::<SourceSystem>() == 1);
    assert!(size_of::<ExprPathStep>() == 1);
};

#[cfg(test)]
mod tests {
    use super::*;

    /// Every table entry names a real variant and carries its real tag.
    ///
    /// The `const _` blocks above already fail the build on a changed number.
    /// This adds the direction they cannot cover: that the TABLES — which the
    /// manifest gate reads — stay in step with the enum, including that they
    /// list every variant exactly once.
    #[test]
    fn test_crystal_mode_tags_match_the_enum() {
        let live = [
            (CleanMode::Constructive, "Constructive"),
            (CleanMode::Impredicative, "Impredicative"),
            (CleanMode::Cubical, "Cubical"),
            (CleanMode::Directed, "Directed"),
            (CleanMode::Classical, "Classical"),
            (CleanMode::SetTheoretic, "SetTheoretic"),
        ];
        assert_eq!(live.len(), CLEAN_MODE_TAGS.len());
        for (idx, (mode, name)) in live.iter().enumerate() {
            assert_eq!(mode.name(), *name, "name() disagrees with the pin table");
            assert_eq!(
                (*mode as u8),
                CLEAN_MODE_TAGS[idx].1,
                "{name}: live discriminant disagrees with the pin table"
            );
            assert_eq!(CLEAN_MODE_TAGS[idx].0, *name);
        }
    }

    /// The two arms the flagship chain's `switch` names, stated as themselves.
    ///
    /// `has_cubical_layer`'s emitted body is `switch [ 2: true 3: true default:
    /// false ]`. That is only the right compilation of
    /// `matches!(self, Cubical | Directed)` while 2 and 3 are exactly those two
    /// modes and nothing else.
    #[test]
    fn test_crystal_has_cubical_layer_switch_arms_are_cubical_and_directed() {
        for (name, tag) in CLEAN_MODE_TAGS {
            let mode = match name {
                "Constructive" => CleanMode::Constructive,
                "Impredicative" => CleanMode::Impredicative,
                "Cubical" => CleanMode::Cubical,
                "Directed" => CleanMode::Directed,
                "Classical" => CleanMode::Classical,
                "SetTheoretic" => CleanMode::SetTheoretic,
                other => panic!("unpinned CleanMode variant {other}"),
            };
            assert_eq!(
                mode.has_cubical_layer(),
                tag == 2 || tag == 3,
                "{name} (tag {tag}): the emitted switch's true-arms are 2 and 3"
            );
        }
    }

    /// `SourceSystem`'s tags, and the two the emitted switch treats specially.
    #[test]
    fn test_crystal_source_system_tags_match_the_enum() {
        let live = [
            (SourceSystem::Lean4, "Lean4"),
            (SourceSystem::Coq, "Coq"),
            (SourceSystem::Agda, "Agda"),
            (SourceSystem::CubicalAgda, "CubicalAgda"),
            (SourceSystem::IsabelleHOL, "IsabelleHOL"),
            (SourceSystem::HOLLight, "HOLLight"),
            (SourceSystem::HOL4, "HOL4"),
            (SourceSystem::Mizar, "Mizar"),
            (SourceSystem::MetamathZFC, "MetamathZFC"),
            (SourceSystem::MetamathSet, "MetamathSet"),
            (SourceSystem::PVS, "PVS"),
            (SourceSystem::ACL2, "ACL2"),
        ];
        assert_eq!(live.len(), SOURCE_SYSTEM_TAGS.len());
        for (idx, (system, name)) in live.iter().enumerate() {
            assert_eq!((*system as u8), SOURCE_SYSTEM_TAGS[idx].1, "{name}");
            assert_eq!(SOURCE_SYSTEM_TAGS[idx].0, *name);
        }
        // The emitted body routes 10 through the default edge and 11 through an
        // explicit arm; both land on `Classical`, which is why folding them is
        // sound TODAY and why swapping them would be silent.
        assert_eq!(
            CleanMode::from_source_system(SourceSystem::PVS),
            CleanMode::Classical
        );
        assert_eq!(
            CleanMode::from_source_system(SourceSystem::ACL2),
            CleanMode::Classical
        );
    }

    /// `ExprPathStep`'s tags, all eleven.
    #[test]
    fn test_crystal_expr_path_step_tags_match_the_enum() {
        let live = [
            (ExprPathStep::AppFn, "AppFn"),
            (ExprPathStep::AppArg, "AppArg"),
            (ExprPathStep::LamBody, "LamBody"),
            (ExprPathStep::LamType, "LamType"),
            (ExprPathStep::PiDom, "PiDom"),
            (ExprPathStep::PiBody, "PiBody"),
            (ExprPathStep::LetType, "LetType"),
            (ExprPathStep::LetVal, "LetVal"),
            (ExprPathStep::LetBody, "LetBody"),
            (ExprPathStep::MDataExpr, "MDataExpr"),
            (ExprPathStep::ProjExpr, "ProjExpr"),
        ];
        assert_eq!(live.len(), EXPR_PATH_STEP_TAGS.len());
        // `into_iter` rather than `iter`: `ExprPathStep` is not `Copy`, and an
        // `as u8` cast needs the value.
        for (idx, (step, name)) in live.into_iter().enumerate() {
            assert_eq!(step as u8, EXPR_PATH_STEP_TAGS[idx].1, "{name}");
            assert_eq!(EXPR_PATH_STEP_TAGS[idx].0, name);
        }
    }

    /// `#[repr(u8)]` must not have moved the SERDE wire, which is a different
    /// encoding with a different rule.
    ///
    /// serde's derived enum representation keys off the DECLARATION INDEX, not
    /// the discriminant: self-describing formats emit the variant NAME, compact
    /// ones emit the index. Neither reads the repr, so this change is wire-
    /// neutral — but only while discriminant == declaration index. If a future
    /// edit sets, say, `Cubical = 7`, the ABI tag and the serde index diverge
    /// and this test is where that shows up.
    #[test]
    fn test_crystal_serde_wire_is_unchanged_by_the_repr() {
        for (idx, (name, tag)) in CLEAN_MODE_TAGS.iter().enumerate() {
            assert_eq!(
                usize::from(*tag),
                idx,
                "{name}: discriminant must equal declaration index, or the ABI \
                 tag and serde's variant index have silently diverged"
            );
        }
        for (idx, (name, tag)) in SOURCE_SYSTEM_TAGS.iter().enumerate() {
            assert_eq!(usize::from(*tag), idx, "{name}");
        }
        for (idx, (name, tag)) in EXPR_PATH_STEP_TAGS.iter().enumerate() {
            assert_eq!(usize::from(*tag), idx, "{name}");
        }

        // And the JSON wire is by name, before and after.
        let json = serde_json::to_string(&CleanMode::Cubical).expect("serialize CleanMode");
        assert_eq!(json, "\"Cubical\"");
        let back: CleanMode = serde_json::from_str(&json).expect("deserialize CleanMode");
        assert_eq!(back, CleanMode::Cubical);

        let json = serde_json::to_string(&SourceSystem::ACL2).expect("serialize SourceSystem");
        assert_eq!(json, "\"ACL2\"");
        let back: SourceSystem = serde_json::from_str(&json).expect("deserialize SourceSystem");
        assert_eq!(back, SourceSystem::ACL2);
    }

    /// Round-trip through the compact format too, since `clean-kernel` carries
    /// a `bincode` dependency and a compact encoder is where a variant-index
    /// shift would do damage that a name-keyed JSON round-trip cannot see.
    #[test]
    fn test_crystal_bincode_round_trip_is_stable() {
        let cfg = bincode::config::standard();
        for (name, _) in CLEAN_MODE_TAGS {
            let mode = match name {
                "Constructive" => CleanMode::Constructive,
                "Impredicative" => CleanMode::Impredicative,
                "Cubical" => CleanMode::Cubical,
                "Directed" => CleanMode::Directed,
                "Classical" => CleanMode::Classical,
                "SetTheoretic" => CleanMode::SetTheoretic,
                other => panic!("unpinned CleanMode variant {other}"),
            };
            let bytes =
                bincode::serde::encode_to_vec(mode, cfg).expect("encode CleanMode with bincode");
            let (back, _): (CleanMode, usize) =
                bincode::serde::decode_from_slice(&bytes, cfg).expect("decode CleanMode");
            assert_eq!(back, mode, "{name} did not survive a bincode round trip");
        }
    }
}
