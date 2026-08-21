// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! clean Mode System
//!
//! The mode system enables clean to support multiple mathematical traditions
//! with proven-safe combinations. Each mode activates different axioms and
//! type-theoretic features.
//!
//! # Mode Compatibility
//!
//! Proofs from one mode can be imported into another if the source mode's
//! axioms are provable in (or axiomatized by) the target mode:
//!
//! - Constructive → All modes (most restrictive, works everywhere)
//! - Impredicative → Classical, SetTheoretic (proof irrelevance compatible)
//! - Cubical → Only itself (different equality/computation rules; no translation into non-cubical modes)
//! - Classical → SetTheoretic (SetTheoretic extends Classical)
//! - SetTheoretic → Only itself (strongest axioms)

use serde::{Deserialize, Serialize};

/// Logical mode controlling which axioms and features are available.
///
/// Different mathematical traditions have different logical foundations.
/// Rather than pick one, clean supports multiple modes with proven-safe
/// combinations.
///
/// # Discriminants are PINNED — do not renumber, do not reorder silently
///
/// `#[repr(u8)]` and the explicit `= N` values are load-bearing, not decoration.
/// The crystal chains for `CleanMode::has_cubical_layer` and
/// `CleanMode::from_source_system` prove theorems about the trust-ir that
/// `trustc` emits for these bodies, and that IR **switches on the numeric
/// discriminant**: `switch %3 [ 2: bb1 3: bb2 default: bb3 ]` for
/// `has_cubical_layer`, `const enum.13 { k }` for every arm of
/// `from_source_system`. Clean's side of the proof encodes the same numbers in
/// `clean_mode_tag` (`crates/clean-verify/src/spec/core_spec/eval_ir_mode.rs`).
///
/// Without explicit discriminants those numbers were rustc's choice for a
/// default-repr enum: the *values* were guaranteed to be 0.. in declaration
/// order by the language, but nothing stopped a future edit from REORDERING the
/// variants, which would silently move `Cubical` off 2 and make the registered
/// module a theorem about a body that is no longer shipped. `#[repr(u8)]`
/// additionally pins the tag ENCODING to the `u8` the emitted
/// `extractfield u8 %2, 0` reads.
///
/// The pin is enforced by `crate::crystal_tag_pin` (compile-time) and by
/// `scripts/check_enum_tag_pin.py` against `data/crystal_enum_tag_pin.json`,
/// which also cross-checks the recorded artifacts under
/// `crates/clean-verify/tests/fixtures/`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize, Default)]
#[repr(u8)]
pub enum CleanMode {
    /// Pure Martin-Löf Type Theory - no axioms, decidable type checking.
    /// Compatible with: All modes (most restrictive)
    ///
    /// This is the default mode and corresponds to Lean 4's core type theory.
    #[default]
    Constructive = 0,

    /// Calculus of Inductive Constructions - impredicative Prop, restricted large elimination.
    /// Compatible with: Constructive, Classical, SetTheoretic
    ///
    /// This mode adds:
    /// - Impredicative Prop (quantification over Prop stays in Prop)
    /// - SProp (strict propositions, always proof-irrelevant)
    /// - Restricted large elimination from Prop
    Impredicative = 1,

    /// Cubical Type Theory - Path types, hcomp, transp, Glue, univalence provable.
    /// Compatible with: Constructive only (NOT with Classical or Impredicative)
    ///
    /// This mode adds:
    /// - Interval type I with endpoints 0 and 1
    /// - Path types as primitive equality
    /// - Homogeneous composition (hcomp)
    /// - Transport along paths (transp)
    /// - Glue types for univalence
    ///
    /// WARNING: Cubical mode is ISOLATED - cannot import from or to Classical/Impredicative
    /// because it uses different equality/computation rules (Path/Glue/hcomp/transp) that are
    /// not available in the other modes. Note: univalence itself is compatible with classical
    /// axioms like LEM; the isolation here is a kernel/translation boundary.
    Cubical = 2,

    /// Directed / simplicial type theory (Riehl–Shulman) — **Rung 2** (frontier).
    /// Compatible with: Constructive only (isolated, like Cubical).
    ///
    /// This mode adds a **strict directed interval `𝟚`** (the 1-simplex `Δ¹`),
    /// kept cleanly SEPARATE from the symmetric cubical interval `I`:
    /// - `𝟚 : Type` with endpoints `0₂`/`1₂` and a bounded total order `≤`
    ///   (`0 ≤ x ≤ 1`). The order is **decidable on endpoints** — `0₂ ≤ 1₂`
    ///   holds, `1₂ ≤ 0₂` does NOT — so directedness (asymmetry) is real, not
    ///   collapsed to the invertible cubical `I`.
    /// - **Extension / hom types** `hom_A(x,y) := ⟨ 𝟚 → A | {0↦x, 1↦y} ⟩` — the
    ///   type of directed morphisms (1-cells) from `x` to `y`.
    ///
    /// The directed primitives are an **opt-in reserved-`Const` encoding**
    /// (`Dir.*`, registered by `register_directed_axioms`), NOT in the classical
    /// TCB and parsed/reduced only in their own module. They never touch the
    /// cubical `I`/`Glue` machinery, so the two foundations do not interfere.
    ///
    /// WARNING: Directed mode is ISOLATED (like Cubical) — different
    /// equality/computation rules; no translation into non-directed modes.
    ///
    /// This is **research, not settled engineering** (Riehl–Shulman simplicial TT
    /// has open metatheoretic questions); Segal/Rezk composition and ∞-Yoneda are
    /// roadmap, not yet built. See
    /// `docs/plans/RUNG2_DIRECTED_DESIGN.md`.
    Directed = 3,

    /// Classical logic - LEM, Choice as axioms.
    /// Compatible with: Constructive, Impredicative
    ///
    /// This mode adds:
    /// - Law of Excluded Middle (LEM): ∀ P, P ∨ ¬P
    /// - Axiom of Choice
    /// - Function extensionality
    /// - Propositional extensionality
    Classical = 4,

    /// ZFC set theory - sets as first-class, no dependent types required.
    /// Compatible with: Classical (inherits all classical axioms)
    ///
    /// This mode adds:
    /// - ZFC axioms (Extensionality, Pairing, Union, PowerSet, etc.)
    /// - Set membership as primitive
    /// - Set comprehension
    SetTheoretic = 5,
}

impl CleanMode {
    /// Check if proofs from `source` mode can be used in `target` mode.
    ///
    /// The import relation is transitive but not symmetric:
    /// - Constructive → Any (most general proofs)
    /// - Cubical is isolated (different kernel rules; no translation provided)
    /// - Classical hierarchy: Impredicative → Classical → SetTheoretic
    ///
    /// # Contract
    ///
    /// ENSURES: `can_import(Constructive, _) == true` (constructive works everywhere)
    /// ENSURES: `can_import(m, m) == true` for all modes (reflexive)
    /// ENSURES: `can_import(Cubical, m) == false` for m != Cubical (Cubical is isolated)
    ///
    /// # Examples
    ///
    /// ```
    /// use clean_kernel::mode::CleanMode;
    ///
    /// // Constructive proofs work everywhere
    /// assert!(CleanMode::can_import(CleanMode::Constructive, CleanMode::Classical));
    /// assert!(CleanMode::can_import(CleanMode::Constructive, CleanMode::Cubical));
    ///
    /// // Classical doesn't work in Constructive
    /// assert!(!CleanMode::can_import(CleanMode::Classical, CleanMode::Constructive));
    ///
    /// // Cubical is isolated
    /// assert!(!CleanMode::can_import(CleanMode::Cubical, CleanMode::Classical));
    /// assert!(!CleanMode::can_import(CleanMode::Classical, CleanMode::Cubical));
    /// ```
    #[must_use]
    pub fn can_import(source: CleanMode, target: CleanMode) -> bool {
        use CleanMode::*;
        match (source, target) {
            // Constructive proofs work everywhere
            (Constructive, _) => true,

            // Same mode always works
            (m1, m2) if m1 == m2 => true,

            // Impredicative works in Classical (both accept proof irrelevance)
            (Impredicative, Classical) => true,

            // Classical works in SetTheoretic (SetTheoretic extends Classical with ZFC axioms)
            (Classical, SetTheoretic) => true,
            (Impredicative, SetTheoretic) => true,

            // Cubical is isolated: different equality/computation rules (needs translation to cross)
            (Cubical, _) | (_, Cubical) => false,

            // Directed (Rung 2) is isolated, exactly like Cubical: the strict
            // interval `𝟚` and extension/hom types have no counterpart in the
            // non-directed modes. (Constructive → Directed and Directed →
            // Directed are already handled by the earlier arms.)
            (Directed, _) | (_, Directed) => false,

            // SetTheoretic only imports from Classical hierarchy
            (SetTheoretic, _) => false,

            // Default: not compatible
            _ => false,
        }
    }

    /// Get the default mode for a source system.
    ///
    /// When importing proofs from an external system, this determines
    /// which clean mode they will be checked in.
    ///
    /// # Contract
    ///
    /// ENSURES: Result is a valid CleanMode matching the source system's logic
    /// ENSURES: `from_source_system(Lean4) == Constructive`
    /// ENSURES: `from_source_system(CubicalAgda) == Cubical`
    #[must_use]
    pub fn from_source_system(system: SourceSystem) -> Self {
        use SourceSystem::*;
        match system {
            Lean4 => CleanMode::Constructive,
            Coq => CleanMode::Impredicative,
            Agda => CleanMode::Constructive,
            CubicalAgda => CleanMode::Cubical,
            IsabelleHOL | HOLLight | HOL4 => CleanMode::Classical,
            Mizar | MetamathZFC => CleanMode::SetTheoretic,
            MetamathSet | ACL2 => CleanMode::Classical,
            PVS => CleanMode::Classical,
        }
    }

    /// Get the axioms available in this mode.
    ///
    /// # Contract
    ///
    /// ENSURES: `Constructive.available_axioms().is_empty()`
    /// ENSURES: `Classical.available_axioms()` contains `LEM` and `Choice`
    /// ENSURES: `SetTheoretic.available_axioms()` contains all ZFC axioms
    #[must_use]
    pub fn available_axioms(&self) -> Vec<AxiomId> {
        use CleanMode::*;
        match self {
            Constructive => vec![
                // No logical axioms - pure MLTT
            ],

            Impredicative => vec![
                AxiomId::PropExt,    // Propositional extensionality
                AxiomId::ProofIrrel, // Proof irrelevance for Prop
            ],

            Cubical => vec![
                // Univalence is PROVABLE, not an axiom
                // But we expose it as a theorem
            ],

            Directed => vec![
                // No `AxiomId` logical axioms: the directed primitives (strict
                // interval `𝟚`, order `≤`, extension/hom types) are an opt-in
                // reserved-`Const` encoding (`Dir.*`), registered separately by
                // `register_directed_axioms` and NOT part of the classical TCB.
            ],

            Classical => vec![
                AxiomId::PropExt,
                AxiomId::ProofIrrel,
                AxiomId::LEM,    // Law of excluded middle
                AxiomId::Choice, // Axiom of choice
                AxiomId::FunExt, // Function extensionality
            ],

            SetTheoretic => vec![
                // All classical axioms plus ZFC
                AxiomId::PropExt,
                AxiomId::ProofIrrel,
                AxiomId::LEM,
                AxiomId::Choice,
                AxiomId::FunExt,
                AxiomId::ZFCExtensionality,
                AxiomId::ZFCPairing,
                AxiomId::ZFCUnion,
                AxiomId::ZFCPowerSet,
                AxiomId::ZFCInfinity,
                AxiomId::ZFCSeparation,
                AxiomId::ZFCReplacement,
                AxiomId::ZFCFoundation,
            ],
        }
    }

    /// Check if this mode allows large elimination from the given sort.
    ///
    /// Large elimination means eliminating from Prop to produce data (Type).
    /// This is restricted in Impredicative/Classical modes to prevent
    /// inconsistency.
    ///
    /// # Contract
    ///
    /// ENSURES: `Constructive.allows_large_elimination(_) == true`
    /// ENSURES: `Cubical.allows_large_elimination(_) == true`
    /// ENSURES: `Impredicative.allows_large_elimination(true) == false`
    /// ENSURES: `Classical.allows_large_elimination(true) == false`
    ///
    /// # Rules
    ///
    /// - Constructive: Always allowed
    /// - Impredicative/Classical: Only for singletons (Empty, Unit, Eq)
    /// - Cubical: Always allowed
    /// - SetTheoretic: Sets can eliminate freely
    #[must_use]
    pub fn allows_large_elimination(&self, from_prop: bool) -> bool {
        match self {
            CleanMode::Constructive => true,
            CleanMode::Impredicative | CleanMode::Classical => {
                // Only small elimination from Prop
                // Large elim only for singletons (handled separately)
                !from_prop
            }
            CleanMode::Cubical => true,
            // Directed builds on the fibrant (univalent) layer; large
            // elimination is unrestricted, as in Cubical/Constructive.
            CleanMode::Directed => true,
            CleanMode::SetTheoretic => true,
        }
    }

    /// Whether this mode includes the **cubical / HoTT-Kan layer** — `Path`,
    /// `PathP`, `hcomp`, `coe`, `transp`, `Glue`, and the `Sigma`-encoded
    /// `fiber`/`isContr`/`isEquiv` h-level library.
    ///
    /// This is the **2LTT bridge** (Riehl–Shulman simplicial HoTT): the directed
    /// layer sits *on top of* the fibrant cubical base, so `Directed` mode ALSO
    /// has the cubical machinery available. A directed type can then talk about
    /// contractibility (`isContr`) of its hom-composites — exactly what the Segal
    /// condition needs. The directed-specific `Dir.*` reductions (the strict
    /// interval `𝟚`, its order `≤`, the extension/hom types) stay Directed-only;
    /// this predicate only governs the *cubical* capability.
    ///
    /// # Contract
    ///
    /// ENSURES: `Cubical.has_cubical_layer() == true`
    /// ENSURES: `Directed.has_cubical_layer() == true` (the 2LTT bridge)
    /// ENSURES: `Constructive.has_cubical_layer() == false`
    #[must_use]
    pub fn has_cubical_layer(&self) -> bool {
        matches!(self, CleanMode::Cubical | CleanMode::Directed)
    }

    /// Get a human-readable name for this mode.
    ///
    /// # Contract
    ///
    /// ENSURES: Result is a non-empty static string
    /// ENSURES: Each mode returns a distinct name
    #[must_use]
    pub fn name(&self) -> &'static str {
        match self {
            CleanMode::Constructive => "Constructive",
            CleanMode::Impredicative => "Impredicative",
            CleanMode::Cubical => "Cubical",
            CleanMode::Directed => "Directed",
            CleanMode::Classical => "Classical",
            CleanMode::SetTheoretic => "SetTheoretic",
        }
    }
}

/// Source proof system for imported declarations.
///
/// # Discriminants are PINNED
///
/// See [`CleanMode`]. `CleanMode::from_source_system` is a registered crystal
/// chain; the emitted body switches on this enum's discriminant
/// (`switch %2 [ 0: bb1 … 9: bb10 11: bb11 default: bb12 ]`, with `10` — `PVS` —
/// deliberately folded into the default alongside `ACL2`'s explicit `11`).
/// Renumbering or reordering these variants changes which arm each system
/// reaches without changing one line of the registered module.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[repr(u8)]
pub enum SourceSystem {
    /// Lean 4
    Lean4 = 0,
    /// Coq proof assistant
    Coq = 1,
    /// Agda (standard)
    Agda = 2,
    /// Cubical Agda
    CubicalAgda = 3,
    /// Isabelle/HOL
    IsabelleHOL = 4,
    /// HOL Light
    HOLLight = 5,
    /// HOL4
    HOL4 = 6,
    /// Mizar
    Mizar = 7,
    /// Metamath with ZFC axioms
    MetamathZFC = 8,
    /// Metamath set.mm (classical logic)
    MetamathSet = 9,
    /// PVS
    PVS = 10,
    /// ACL2
    ACL2 = 11,
}

impl SourceSystem {
    /// Get a human-readable name for this system.
    ///
    /// # Contract
    ///
    /// ENSURES: Result is a non-empty static string
    /// ENSURES: Each system returns a distinct name
    #[must_use]
    pub fn name(&self) -> &'static str {
        match self {
            SourceSystem::Lean4 => "Lean 4",
            SourceSystem::Coq => "Coq",
            SourceSystem::Agda => "Agda",
            SourceSystem::CubicalAgda => "Cubical Agda",
            SourceSystem::IsabelleHOL => "Isabelle/HOL",
            SourceSystem::HOLLight => "HOL Light",
            SourceSystem::HOL4 => "HOL4",
            SourceSystem::Mizar => "Mizar",
            SourceSystem::MetamathZFC => "Metamath/ZFC",
            SourceSystem::MetamathSet => "Metamath/set.mm",
            SourceSystem::PVS => "PVS",
            SourceSystem::ACL2 => "ACL2",
        }
    }
}

/// Axiom identifiers for logical axioms in each mode.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum AxiomId {
    // ════════════════════════════════════════════════════════════════════
    // Logical axioms
    // ════════════════════════════════════════════════════════════════════
    /// Propositional extensionality: (P ↔ Q) → P = Q
    PropExt,
    /// Proof irrelevance: any two proofs of the same Prop are equal
    ProofIrrel,
    /// Law of Excluded Middle: ∀ P, P ∨ ¬P
    LEM,
    /// Axiom of Choice
    Choice,
    /// Function extensionality: (∀ x, f x = g x) → f = g
    FunExt,

    // ════════════════════════════════════════════════════════════════════
    // ZFC axioms
    // ════════════════════════════════════════════════════════════════════
    /// Extensionality: sets with same elements are equal
    ZFCExtensionality,
    /// Pairing: {a, b} exists
    ZFCPairing,
    /// Union: ⋃A exists
    ZFCUnion,
    /// Power Set: P(A) exists
    ZFCPowerSet,
    /// Infinity: ω exists
    ZFCInfinity,
    /// Separation: {x ∈ A | φ(x)} exists
    ZFCSeparation,
    /// Replacement: {F(x) | x ∈ A} exists
    ZFCReplacement,
    /// Foundation: every non-empty set has a ∈-minimal element
    ZFCFoundation,
    /// Choice (ZFC version): every family of non-empty sets has a choice function
    ZFCChoice,
}

impl AxiomId {
    /// Get a human-readable name for this axiom.
    ///
    /// # Contract
    ///
    /// ENSURES: Result is a non-empty static string
    /// ENSURES: Each axiom returns a distinct name
    #[must_use]
    pub fn name(&self) -> &'static str {
        match self {
            AxiomId::PropExt => "Propositional Extensionality",
            AxiomId::ProofIrrel => "Proof Irrelevance",
            AxiomId::LEM => "Law of Excluded Middle",
            AxiomId::Choice => "Axiom of Choice",
            AxiomId::FunExt => "Function Extensionality",
            AxiomId::ZFCExtensionality => "ZFC Extensionality",
            AxiomId::ZFCPairing => "ZFC Pairing",
            AxiomId::ZFCUnion => "ZFC Union",
            AxiomId::ZFCPowerSet => "ZFC Power Set",
            AxiomId::ZFCInfinity => "ZFC Infinity",
            AxiomId::ZFCSeparation => "ZFC Separation",
            AxiomId::ZFCReplacement => "ZFC Replacement",
            AxiomId::ZFCFoundation => "ZFC Foundation",
            AxiomId::ZFCChoice => "ZFC Choice",
        }
    }
}

impl std::fmt::Display for AxiomId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.name())
    }
}

impl std::fmt::Display for CleanMode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.name())
    }
}

/// Error when mode consistency is violated.
#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
pub enum ModeError {
    /// Attempted to use a feature not available in the current mode.
    #[error("Feature not available in {current} mode: {feature}")]
    FeatureNotAvailable {
        /// The current mode
        current: CleanMode,
        /// The feature that was attempted
        feature: String,
    },

    /// Attempted to import from an incompatible mode.
    #[error("Cannot import from {source_mode} mode into {target} mode")]
    IncompatibleImport {
        /// The source mode of the import
        source_mode: CleanMode,
        /// The target mode attempting to use the import
        target: CleanMode,
    },

    /// Attempted to use an axiom not available in the current mode.
    #[error("Axiom {axiom} not available in {mode} mode")]
    AxiomNotAvailable {
        /// The axiom that was attempted
        axiom: AxiomId,
        /// The current mode
        mode: CleanMode,
    },
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_constructive_imports_everywhere() {
        // Constructive proofs should work in all modes
        assert!(CleanMode::can_import(
            CleanMode::Constructive,
            CleanMode::Constructive
        ));
        assert!(CleanMode::can_import(
            CleanMode::Constructive,
            CleanMode::Impredicative
        ));
        assert!(CleanMode::can_import(
            CleanMode::Constructive,
            CleanMode::Cubical
        ));
        assert!(CleanMode::can_import(
            CleanMode::Constructive,
            CleanMode::Classical
        ));
        assert!(CleanMode::can_import(
            CleanMode::Constructive,
            CleanMode::SetTheoretic
        ));
    }

    #[test]
    fn test_cubical_isolated() {
        // Cubical mode is isolated - can't import from or to other non-constructive modes
        assert!(!CleanMode::can_import(
            CleanMode::Cubical,
            CleanMode::Impredicative
        ));
        assert!(!CleanMode::can_import(
            CleanMode::Cubical,
            CleanMode::Classical
        ));
        assert!(!CleanMode::can_import(
            CleanMode::Cubical,
            CleanMode::SetTheoretic
        ));

        assert!(!CleanMode::can_import(
            CleanMode::Impredicative,
            CleanMode::Cubical
        ));
        assert!(!CleanMode::can_import(
            CleanMode::Classical,
            CleanMode::Cubical
        ));
        assert!(!CleanMode::can_import(
            CleanMode::SetTheoretic,
            CleanMode::Cubical
        ));

        // But Constructive can import to Cubical
        assert!(CleanMode::can_import(
            CleanMode::Constructive,
            CleanMode::Cubical
        ));

        // And Cubical can import to itself
        assert!(CleanMode::can_import(
            CleanMode::Cubical,
            CleanMode::Cubical
        ));
    }

    #[test]
    fn test_directed_isolated() {
        // Directed mode (Rung 2) is isolated, like Cubical: no translation to or
        // from the non-directed modes.
        for other in [
            CleanMode::Impredicative,
            CleanMode::Cubical,
            CleanMode::Classical,
            CleanMode::SetTheoretic,
        ] {
            assert!(
                !CleanMode::can_import(CleanMode::Directed, other),
                "Directed should not import into {other:?}"
            );
            assert!(
                !CleanMode::can_import(other, CleanMode::Directed),
                "{other:?} should not import into Directed"
            );
        }
        // Constructive proofs still flow into Directed; Directed imports itself.
        assert!(CleanMode::can_import(
            CleanMode::Constructive,
            CleanMode::Directed
        ));
        assert!(CleanMode::can_import(
            CleanMode::Directed,
            CleanMode::Directed
        ));
        // Directed has no `AxiomId` logical axioms (its primitives are reserved
        // `Dir.*` consts), allows large elimination, and has a distinct name.
        assert!(CleanMode::Directed.available_axioms().is_empty());
        assert!(CleanMode::Directed.allows_large_elimination(true));
        assert_eq!(CleanMode::Directed.name(), "Directed");
    }

    #[test]
    fn test_classical_hierarchy() {
        // Impredicative → Classical → SetTheoretic
        assert!(CleanMode::can_import(
            CleanMode::Impredicative,
            CleanMode::Classical
        ));
        assert!(CleanMode::can_import(
            CleanMode::Classical,
            CleanMode::SetTheoretic
        ));
        assert!(CleanMode::can_import(
            CleanMode::Impredicative,
            CleanMode::SetTheoretic
        ));

        // But not the other way
        assert!(!CleanMode::can_import(
            CleanMode::Classical,
            CleanMode::Impredicative
        ));
        assert!(!CleanMode::can_import(
            CleanMode::SetTheoretic,
            CleanMode::Classical
        ));
        assert!(!CleanMode::can_import(
            CleanMode::SetTheoretic,
            CleanMode::Impredicative
        ));
    }

    #[test]
    fn test_classical_not_in_constructive() {
        // Classical axioms can't be used in constructive mode
        assert!(!CleanMode::can_import(
            CleanMode::Classical,
            CleanMode::Constructive
        ));
        assert!(!CleanMode::can_import(
            CleanMode::Impredicative,
            CleanMode::Constructive
        ));
    }

    #[test]
    fn test_source_system_modes() {
        // Test that source systems map to expected modes
        assert_eq!(
            CleanMode::from_source_system(SourceSystem::Lean4),
            CleanMode::Constructive
        );
        assert_eq!(
            CleanMode::from_source_system(SourceSystem::Coq),
            CleanMode::Impredicative
        );
        assert_eq!(
            CleanMode::from_source_system(SourceSystem::CubicalAgda),
            CleanMode::Cubical
        );
        assert_eq!(
            CleanMode::from_source_system(SourceSystem::IsabelleHOL),
            CleanMode::Classical
        );
        assert_eq!(
            CleanMode::from_source_system(SourceSystem::MetamathZFC),
            CleanMode::SetTheoretic
        );
    }

    #[test]
    fn test_available_axioms() {
        // Constructive has no axioms
        assert!(CleanMode::Constructive.available_axioms().is_empty());

        // Impredicative has PropExt and ProofIrrel
        let imp_axioms = CleanMode::Impredicative.available_axioms();
        assert!(imp_axioms.contains(&AxiomId::PropExt));
        assert!(imp_axioms.contains(&AxiomId::ProofIrrel));
        assert!(!imp_axioms.contains(&AxiomId::LEM));

        // Classical has LEM and Choice
        let class_axioms = CleanMode::Classical.available_axioms();
        assert!(class_axioms.contains(&AxiomId::LEM));
        assert!(class_axioms.contains(&AxiomId::Choice));

        // SetTheoretic has ZFC axioms
        let set_axioms = CleanMode::SetTheoretic.available_axioms();
        assert!(set_axioms.contains(&AxiomId::ZFCExtensionality));
        assert!(set_axioms.contains(&AxiomId::ZFCInfinity));
    }

    #[test]
    fn test_large_elimination() {
        // Constructive always allows large elimination
        assert!(CleanMode::Constructive.allows_large_elimination(false));
        assert!(CleanMode::Constructive.allows_large_elimination(true));

        // Impredicative restricts from Prop
        assert!(CleanMode::Impredicative.allows_large_elimination(false));
        assert!(!CleanMode::Impredicative.allows_large_elimination(true));

        // Same for Classical
        assert!(CleanMode::Classical.allows_large_elimination(false));
        assert!(!CleanMode::Classical.allows_large_elimination(true));

        // Cubical allows both
        assert!(CleanMode::Cubical.allows_large_elimination(false));
        assert!(CleanMode::Cubical.allows_large_elimination(true));

        // SetTheoretic allows both
        assert!(CleanMode::SetTheoretic.allows_large_elimination(false));
        assert!(CleanMode::SetTheoretic.allows_large_elimination(true));
    }

    #[test]
    fn test_reflexive_imports() {
        // Every mode can import from itself
        for mode in [
            CleanMode::Constructive,
            CleanMode::Impredicative,
            CleanMode::Cubical,
            CleanMode::Directed,
            CleanMode::Classical,
            CleanMode::SetTheoretic,
        ] {
            assert!(
                CleanMode::can_import(mode, mode),
                "{mode:?} should be able to import from itself"
            );
        }
    }

    #[test]
    fn test_default_mode() {
        // Default mode should be Constructive
        assert_eq!(CleanMode::default(), CleanMode::Constructive);
    }
}
