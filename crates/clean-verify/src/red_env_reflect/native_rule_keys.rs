// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel-native RULE KEYS: real names a modeled kernel-native conversion rule
//! of `KernelAcceptsTcIn` / `TypingTcIn` keys on, but that no reflected
//! `RecEnv` / `DefEnv` entry references.
//!
//! Quotient reduction (`Quot.lift f h (Quot.mk r a) ~> f a`, and `Quot.ind`) is
//! a kernel-native rule family: `Quot`, `Quot.mk`, `Quot.lift` and `Quot.ind`
//! are value-less builtins, not `RecursorVal` rules, so the reflected
//! foundation core never mentions them and the interning table had no tag for
//! them. The E4 rules key on the reflected name exactly as the deployed
//! `try_quot_reduction` keys on the kernel name.
//!
//! The native-Nat fold keys (E4d) are the same kind of name: `reduce_nat` folds
//! `Nat.mul` .. `Nat.ble` on literals, and the E4d lemmas state each fold as a
//! derived conversion over the head's canonical definition, which is reflected
//! at registration (`reflect_definition_value_text_at`) and needs the name tags.
//!
//! Each key is appended AFTER every other tag, in the declared order, and only
//! when absent, so no encountered name is renumbered. Reservation adds no
//! declaration, reduction rule or environment-validity theorem. Every key must
//! name a constant of the deployed default prelude (`Environment::with_prelude`),
//! so a mistyped key refuses emission instead of minting a tag for nothing.

use clean_kernel::{Environment, Name};

use super::ReflectError;

/// The reserved kernel-native rule keys, in tag-append order.
pub const RESERVED_NATIVE_RULE_KEYS: &[&str] = &[
    "Quot.mk",
    "Quot.lift",
    "Quot.ind",
    // E4d: the native-Nat fold keys (and the fuel cores their closures reach)
    // the foundation core does not reflect. `Nat.add` / `Nat.sub` / `Nat.pred`
    // are reflected definitions and keep their tags.
    "Nat.mul",
    "Nat.pow",
    "Nat.shiftLeft",
    "Nat.divCore",
    "Nat.div",
    "Nat.modCore",
    "Nat.mod",
    "Nat.beq",
    "Nat.ble",
    // E4d: the native-Int fold keys, the inductive and recursor their
    // definitions reduce through, and their closure members.
    "Int",
    "Int.ofNat",
    "Int.negSucc",
    "Int.rec",
    "Int.neg",
    "Int.negOfNat",
    "Int.subNatNat",
    "Int.add",
    "Int.sub",
    "Int.mul",
    // E4d: the bitwise fold keys and their closures (pairs and projections,
    // Bool connectives, the fuel fold).
    "Prod",
    "Prod.mk",
    "Prod.fst",
    "Prod.snd",
    "Bool.not",
    "Bool.or",
    "Bool.xor",
    "Nat.div2Pair",
    "Nat.div2",
    "Nat.div2Par",
    "Nat.iterDiv2",
    "Nat.toBoolPar",
    "Nat.testBit",
    "Nat.ofBool",
    "Nat.bitwiseAux",
    "Nat.bitwise",
    "Nat.land",
    "Nat.lor",
    "Nat.xor",
    "Nat.shiftRight",
    // E4 String literals: the heads `string_lit_to_constructor` builds, the
    // `String` constructor and recursor its derived branches reach, and every
    // constant the canonical `String.ofList` / `Char.ofNat` records (reflected
    // from the deployed default prelude for the admission fact) name.
    "String.ofList",
    "String.mk",
    "String.rec",
    "List",
    "List.nil",
    "List.cons",
    "Char",
    "Char.ofNat",
    "Char.ofNatAux",
    "Char.mk",
    "UInt32.ofBitVec",
    "BitVec.ofNatLT",
    "Nat.isValidChar",
    "Nat.decLt",
    "Nat.le_of_ble_eq_true",
    "LT.lt",
    "instLTNat",
    "OfNat.ofNat",
    "instOfNatNat",
    "HPow.hPow",
    "instHPow",
    "instPowNat",
    "instNatPowNat",
    "And",
    "Or",
    "Or.inl",
    "Not",
    "dite",
    "instDecidableOr",
    "instDecidableAnd",
    // E4n: registered native reducers whose folds the E4n lemmas derive
    // (`conv-native-reducers`): `Nat.blt` (a delta to `Nat.ble`) and `Int.toNat`
    // (an `Int.rec` to a `Nat` literal). Appended after every earlier stage, so
    // no encountered name is renumbered.
    "Nat.blt",
    "Int.toNat",
];

/// Refuse a key that names no constant of the deployed default prelude.
///
/// # Errors
/// Returns [`ReflectError::InvalidReflection`] naming the first absent key.
pub(super) fn check_keys_in_prelude(prelude: &Environment) -> Result<(), ReflectError> {
    check_named_keys_in_prelude(prelude, RESERVED_NATIVE_RULE_KEYS)
}

fn check_named_keys_in_prelude(prelude: &Environment, keys: &[&str]) -> Result<(), ReflectError> {
    for key in keys {
        if prelude.get_const(&Name::from_string(key)).is_none() {
            return Err(ReflectError::InvalidReflection {
                detail: format!(
                    "reserved native rule key {key:?} names no constant of the deployed default prelude"
                ),
            });
        }
    }
    Ok(())
}

/// Append every absent key after all existing tags, in declared order.
pub(super) fn append_native_rule_keys(interning: &mut Vec<(String, u64)>) {
    for key in RESERVED_NATIVE_RULE_KEYS {
        if !interning.iter().any(|(existing, _)| existing == key) {
            interning.push(((*key).to_string(), interning.len() as u64));
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn native_rule_keys_append_without_renumbering() {
        let mut interning = vec![
            ("Nat".to_string(), 0),
            ("Quot.lift".to_string(), 1),
            ("String".to_string(), 2),
        ];
        append_native_rule_keys(&mut interning);
        // The encountered names keep their tags; every other key appends in
        // declared order (derived from the list, which grows with each stage
        // that reserves keys: E4c Quot, E4d the native folds, E4 String).
        let mut expected = vec![
            ("Nat".to_string(), 0),
            ("Quot.lift".to_string(), 1),
            ("String".to_string(), 2),
        ];
        for key in RESERVED_NATIVE_RULE_KEYS {
            if !expected.iter().any(|(existing, _)| existing == key) {
                expected.push(((*key).to_string(), expected.len() as u64));
            }
        }
        assert_eq!(
            &interning[..5],
            &[
                ("Nat".to_string(), 0),
                ("Quot.lift".to_string(), 1),
                ("String".to_string(), 2),
                ("Quot.mk".to_string(), 3),
                ("Quot.ind".to_string(), 4),
            ],
            "an encountered key keeps its tag; absent keys append in declared order"
        );
        assert_eq!(
            interning, expected,
            "every absent key appends, in declared order"
        );
        let before = interning.clone();
        append_native_rule_keys(&mut interning);
        assert_eq!(interning, before, "appending is idempotent");
    }

    #[test]
    fn native_rule_keys_are_prelude_constants_and_a_typo_is_refused() {
        let prelude = Environment::with_prelude();
        check_keys_in_prelude(&prelude).expect("every reserved key is a prelude constant");
        let refused = check_named_keys_in_prelude(&prelude, &["Quot.mk", "Quot.lfit"])
            .expect_err("a key naming no prelude constant must refuse emission");
        assert!(
            refused.to_string().contains("Quot.lfit"),
            "the refusal names the absent key: {refused}"
        );
    }
}
