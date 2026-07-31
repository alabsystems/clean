// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bringing two existentially-hidden fuels to a common bound.
//!
//! Two places in the completeness capstone hold *two* independent "some fuel
//! works" witnesses and need one fuel that works for both: the two whnf legs at
//! the start, and the per-component acceptances at the end. Both are the same
//! move.
//!
//! ```text
//! whnf_fuel_pair            : WhnfFuelReaches a -> WhnfFuelReaches b -> WhnfFuelPair a b
//! def_eq_fuel_accepts_pair  : DefEqFuelAccepts x1 y1 -> DefEqFuelAccepts x2 y2
//!                               -> DefEqFuelAcceptsPair x1 y1 x2 y2
//! ```
//!
//! ## Addition, not maximum
//!
//! The obvious common bound is `max`, and the tree has no `nat_max` with the
//! accompanying `Le` facts — building them would be a small development of its
//! own. It also is not needed: `le_add_self_left : Le a (Nat.add a b)` and
//! `le_add_self_right : Le b (Nat.add a b)` are both already in tree
//! (`iota_core.rs:1686`, `expr_model_inst_ceiling.rs:333`), so **`n₁ + n₂` is a
//! perfectly good common bound** and both `Le` facts come for free.
//!
//! Monotonicity does the rest: `whnf_fuel_red_le` for the reduction side,
//! `def_eq_fuel_le` for the algorithm side. Fuel is a bound, not a measure —
//! nothing wants it tight.
//!
//! ## Why the bound cannot be passed in
//!
//! Each input witness hides its own fuel inside a constructor, so a caller
//! cannot name it, and a lemma of the form "…at fuel `m`, given `m` bounds the
//! hidden fuel" would be unusable. Hence the paired *witness* types: unpack
//! both, add, raise, repackage. The three-component case (`let_`) chains this
//! twice rather than needing a three-way variant.
//!
//! `DerivedProved`, empty axiom closures; the witnesses are census-neutral.

use crate::spec::error::SpecError;
use crate::spec::Specification;

impl Specification {
    /// Common-bound pairing for both fuel-carrying witnesses.
    pub(super) fn add_fuel_pairing(&mut self) -> Result<(), SpecError> {
        self.add_pair_witnesses()?;
        for (src, desc) in Self::fuel_pairing_decls() {
            self.add_recursive_def(&src, &desc)?;
        }
        Ok(())
    }

    /// The two paired-witness inductives.
    fn add_pair_witnesses(&mut self) -> Result<(), SpecError> {
        self.add_inductive(
            "inductive WhnfFuelPair (a : KExpr) (b : KExpr) : Type\n\
             | mk : forall (n : Nat) (ra : KExpr) (rb : KExpr), \
             Eq (OptionType KExpr) (whnf_fuel_red the_red_env n a) (OptionType.some KExpr ra) -> \
             Eq (OptionType KExpr) (whnf_fuel_red the_red_env n b) (OptionType.some KExpr rb) -> \
             WhnfFuelPair a b",
            "WhnfFuelPair a b: ONE fuel at which the executable whnf loop returns on both a and \
             b, with both results. The capstone reduces two terms and needs their loops to \
             terminate at a shared bound; carrying two separate fuels would make every later step \
             carry two. Census-neutral.",
        )?;
        self.add_inductive(
            "inductive DefEqFuelAcceptsPair (x1 : KExpr) (y1 : KExpr) (x2 : KExpr) \
             (y2 : KExpr) : Type\n\
             | mk : forall (n : Nat), \
             Eq Bool (def_eq_fuel the_red_env n x1 y1) Bool.true -> \
             Eq Bool (def_eq_fuel the_red_env n x2 y2) Bool.true -> \
             DefEqFuelAcceptsPair x1 y1 x2 y2",
            "DefEqFuelAcceptsPair x1 y1 x2 y2: ONE fuel at which the structural conversion \
             algorithm accepts both pairs. What the capstone needs to combine per-component \
             acceptances before rebuilding the composite, since def_eq_struct_intro_* wants every \
             component compared by the SAME comparator. Census-neutral.",
        )?;
        Ok(())
    }

    /// The two pairing terms, as `(source, description)`.
    ///
    /// Split out so the shape tests read the PROOF TERMS and nothing else. A
    /// file-text test here counted a lemma name that appeared only in a
    /// description, which is the third time that has happened in this program.
    fn fuel_pairing_decls() -> Vec<(String, String)> {
        vec![
            (
                "def whnf_fuel_pair (a : KExpr) (b : KExpr) (wa : WhnfFuelReaches a) \
                 (wb : WhnfFuelReaches b) : WhnfFuelPair a b := \
                 WhnfFuelReaches.rec a \
                 (fun (_x : WhnfFuelReaches a) => WhnfFuelPair a b) \
                 (fun (na : Nat) (ra : KExpr) \
                 (hra : Eq (OptionType KExpr) (whnf_fuel_red the_red_env na a) \
                 (OptionType.some KExpr ra)) => \
                 WhnfFuelReaches.rec b \
                 (fun (_y : WhnfFuelReaches b) => WhnfFuelPair a b) \
                 (fun (nb : Nat) (rb : KExpr) \
                 (hrb : Eq (OptionType KExpr) (whnf_fuel_red the_red_env nb b) \
                 (OptionType.some KExpr rb)) => \
                 WhnfFuelPair.mk a b (Nat.add na nb) ra rb \
                 (whnf_fuel_red_le the_red_env na (Nat.add na nb) \
                 (le_add_self_left na nb) a ra hra) \
                 (whnf_fuel_red_le the_red_env nb (Nat.add na nb) \
                 (le_add_self_right na nb) b rb hrb)) wb) wa"
                    .to_string(),
                "whnf_fuel_pair: two independent fuel witnesses yield ONE fuel that works for \
                 both. The bound is na + nb rather than the maximum: the tree has no nat_max with \
                 the accompanying order facts, while the two addition bounds are already present, \
                 so addition is free where the maximum would be a small development. Fuel is a \
                 bound, not a measure — nothing wants it tight. Both legs are then raised by \
                 whnf_fuel_red_le. The bound cannot be supplied by the caller, because each \
                 witness hides its own fuel inside a constructor; hence the paired witness type. \
                 DerivedProved, zero axiom_deps."
                    .to_string(),
            ),
            (
                "def def_eq_fuel_accepts_pair (x1 : KExpr) (y1 : KExpr) (x2 : KExpr) \
                 (y2 : KExpr) (w1 : DefEqFuelAccepts x1 y1) (w2 : DefEqFuelAccepts x2 y2) : \
                 DefEqFuelAcceptsPair x1 y1 x2 y2 := \
                 DefEqFuelAccepts.rec x1 y1 \
                 (fun (_a : DefEqFuelAccepts x1 y1) => DefEqFuelAcceptsPair x1 y1 x2 y2) \
                 (fun (n1 : Nat) (h1 : Eq Bool (def_eq_fuel the_red_env n1 x1 y1) Bool.true) => \
                 DefEqFuelAccepts.rec x2 y2 \
                 (fun (_b : DefEqFuelAccepts x2 y2) => DefEqFuelAcceptsPair x1 y1 x2 y2) \
                 (fun (n2 : Nat) (h2 : Eq Bool (def_eq_fuel the_red_env n2 x2 y2) Bool.true) => \
                 DefEqFuelAcceptsPair.mk x1 y1 x2 y2 (Nat.add n1 n2) \
                 (def_eq_fuel_le n1 (Nat.add n1 n2) (le_add_self_left n1 n2) x1 y1 h1) \
                 (def_eq_fuel_le n2 (Nat.add n1 n2) (le_add_self_right n1 n2) x2 y2 h2)) w2) w1"
                    .to_string(),
                "def_eq_fuel_accepts_pair: two independent acceptances yield ONE fuel that accepts \
                 both, by the same addition-as-bound trick, with def_eq_fuel_le doing the raising. \
                 This is what lets the completeness recursion's per-component results — which come \
                 back at unrelated fuels — be fed to def_eq_struct_intro_*, which compares every \
                 component with the same comparator. The three-component case (let_) chains this \
                 twice rather than needing a three-way variant. DerivedProved, zero axiom_deps."
                    .to_string(),
            ),
        ]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Collect just the generated proof terms — never the descriptions.
    ///
    /// The first version of this suite used `include_str!` and counted
    /// `le_add_self_left` across the whole file, which found THREE: two uses and
    /// one mention in a description explaining the choice. Prose is not a
    /// dependency. That is the third time in this program a file-text test has
    /// failed against its own commentary, so the rule is now standing: shape
    /// tests read generated strings, never source text.
    fn terms() -> Vec<String> {
        Specification::fuel_pairing_decls()
            .into_iter()
            .map(|(src, _desc)| src)
            .collect()
    }

    /// Both pairings must use ADDITION as the common bound, with the two
    /// matching `Le` facts. A `max`-based version would need arithmetic the tree
    /// does not have.
    #[test]
    fn test_pairings_use_addition_as_the_common_bound() {
        let joined = terms().join("\n");
        assert_eq!(
            joined.matches("le_add_self_left").count(),
            2,
            "each pairing needs the left Le fact"
        );
        assert_eq!(
            joined.matches("le_add_self_right").count(),
            2,
            "each pairing needs the right Le fact"
        );
        assert_eq!(
            joined.matches("nat_max").count(),
            0,
            "no nat_max: the tree has no Le facts for it, and addition is a perfectly good bound"
        );
    }

    /// Each pairing must raise BOTH sides. Raising only one would leave the
    /// witness carrying mismatched fuels while still typechecking at the
    /// constructor, since both fields mention the same `n`.
    #[test]
    fn test_pairings_raise_both_sides() {
        let joined = terms().join("\n");
        assert_eq!(
            joined.matches("whnf_fuel_red_le the_red_env").count(),
            2,
            "both whnf legs must be raised"
        );
        assert_eq!(
            joined.matches("def_eq_fuel_le n").count(),
            2,
            "both acceptances must be raised"
        );
    }

    /// The fuels are existentially hidden, so both witnesses must be UNPACKED by
    /// their recursors — a version taking the bound as a parameter would be
    /// unusable by callers who cannot name the hidden fuel.
    #[test]
    fn test_pairings_unpack_both_input_witnesses() {
        let joined = terms().join("\n");
        assert_eq!(joined.matches("WhnfFuelReaches.rec").count(), 2);
        assert_eq!(joined.matches("DefEqFuelAccepts.rec").count(), 2);
    }

    /// Paren balance across both terms.
    #[test]
    fn test_pairing_terms_parens_balanced() {
        for src in terms() {
            let mut depth: i64 = 0;
            for ch in src.chars() {
                match ch {
                    '(' => depth += 1,
                    ')' => depth -= 1,
                    _ => {}
                }
                assert!(depth >= 0, "close paren before its open in: {src}");
            }
            assert_eq!(depth, 0, "unbalanced: {src}");
        }
    }
}
