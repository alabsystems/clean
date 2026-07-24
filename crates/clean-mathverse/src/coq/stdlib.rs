// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Coq standard library type mappings for the Lean 5 Mathverse importer.
//!
//! Maps Coq qualified names (e.g. `Coq.Init.Datatypes.nat`) to their Lean 5
//! equivalents (e.g. `Nat`). Used by [`super::coq::CoqImporter`] to translate
//! Coq constants into the Lean 5 namespace during `.mathverse` shard construction.

use std::sync::LazyLock;

/// Mapping from a Coq qualified name to the Lean 5 equivalent.
#[derive(Clone, Debug)]
pub struct TypeMapping {
    pub coq_name: &'static str,
    pub clean_name_mapping: &'static str,
    pub category: MappingCategory,
}

/// Classification of a Coq-to-clean mapping entry.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MappingCategory {
    /// Basic type (nat, bool, unit, ...)
    BaseType,
    /// Type constructor (option, prod, sum, ...)
    TypeConstructor,
    /// Logical connective (and, or, not, exists, ...)
    LogicalConnective,
    /// Arithmetic operation (add, mul, sub, ...)
    Arithmetic,
    /// Comparison (le, lt, eq, ...)
    Comparison,
    /// Theorem / lemma
    Theorem,
    /// Data constructor (O, S, nil, cons, ...)
    Constructor,
}

/// The static mapping table from Coq stdlib names to Lean 5 names.
pub fn coq_clean_mappings() -> &'static [TypeMapping] {
    use MappingCategory::*;
    &[
        // --- Base types ---
        TypeMapping {
            coq_name: "Coq.Init.Datatypes.nat",
            clean_name_mapping: "Nat",
            category: BaseType,
        },
        TypeMapping {
            coq_name: "Coq.Init.Datatypes.bool",
            clean_name_mapping: "Bool",
            category: BaseType,
        },
        TypeMapping {
            coq_name: "Coq.Init.Datatypes.unit",
            clean_name_mapping: "Unit",
            category: BaseType,
        },
        TypeMapping {
            coq_name: "Coq.Init.Datatypes.Empty_set",
            clean_name_mapping: "Empty",
            category: BaseType,
        },
        TypeMapping {
            coq_name: "Coq.Numbers.BinNums.Z",
            clean_name_mapping: "Int",
            category: BaseType,
        },
        TypeMapping {
            coq_name: "Coq.Numbers.BinNums.positive",
            clean_name_mapping: "PosNum",
            category: BaseType,
        },
        TypeMapping {
            coq_name: "Coq.Strings.String.string",
            clean_name_mapping: "String",
            category: BaseType,
        },
        // --- Type constructors ---
        TypeMapping {
            coq_name: "Coq.Init.Datatypes.list",
            clean_name_mapping: "List",
            category: TypeConstructor,
        },
        TypeMapping {
            coq_name: "Coq.Init.Datatypes.option",
            clean_name_mapping: "Option",
            category: TypeConstructor,
        },
        TypeMapping {
            coq_name: "Coq.Init.Datatypes.prod",
            clean_name_mapping: "Prod",
            category: TypeConstructor,
        },
        TypeMapping {
            coq_name: "Coq.Init.Datatypes.sum",
            clean_name_mapping: "Sum",
            category: TypeConstructor,
        },
        TypeMapping {
            coq_name: "Coq.Init.Specif.sig",
            clean_name_mapping: "Subtype",
            category: TypeConstructor,
        },
        TypeMapping {
            coq_name: "Coq.Init.Specif.sigT",
            clean_name_mapping: "Sigma",
            category: TypeConstructor,
        },
        // --- Logical connectives ---
        TypeMapping {
            coq_name: "Coq.Init.Logic.True",
            clean_name_mapping: "True",
            category: LogicalConnective,
        },
        TypeMapping {
            coq_name: "Coq.Init.Logic.False",
            clean_name_mapping: "False",
            category: LogicalConnective,
        },
        TypeMapping {
            coq_name: "Coq.Init.Logic.and",
            clean_name_mapping: "And",
            category: LogicalConnective,
        },
        TypeMapping {
            coq_name: "Coq.Init.Logic.or",
            clean_name_mapping: "Or",
            category: LogicalConnective,
        },
        TypeMapping {
            coq_name: "Coq.Init.Logic.not",
            clean_name_mapping: "Not",
            category: LogicalConnective,
        },
        TypeMapping {
            coq_name: "Coq.Init.Logic.iff",
            clean_name_mapping: "Iff",
            category: LogicalConnective,
        },
        TypeMapping {
            coq_name: "Coq.Init.Logic.ex",
            clean_name_mapping: "Exists",
            category: LogicalConnective,
        },
        TypeMapping {
            coq_name: "Coq.Init.Logic.eq",
            clean_name_mapping: "Eq",
            category: LogicalConnective,
        },
        // --- Constructors ---
        TypeMapping {
            coq_name: "Coq.Init.Datatypes.O",
            clean_name_mapping: "Nat.zero",
            category: Constructor,
        },
        TypeMapping {
            coq_name: "Coq.Init.Datatypes.S",
            clean_name_mapping: "Nat.succ",
            category: Constructor,
        },
        TypeMapping {
            coq_name: "Coq.Init.Datatypes.true",
            clean_name_mapping: "Bool.true",
            category: Constructor,
        },
        TypeMapping {
            coq_name: "Coq.Init.Datatypes.false",
            clean_name_mapping: "Bool.false",
            category: Constructor,
        },
        TypeMapping {
            coq_name: "Coq.Init.Datatypes.nil",
            clean_name_mapping: "List.nil",
            category: Constructor,
        },
        TypeMapping {
            coq_name: "Coq.Init.Datatypes.cons",
            clean_name_mapping: "List.cons",
            category: Constructor,
        },
        TypeMapping {
            coq_name: "Coq.Init.Datatypes.Some",
            clean_name_mapping: "Option.some",
            category: Constructor,
        },
        TypeMapping {
            coq_name: "Coq.Init.Datatypes.None",
            clean_name_mapping: "Option.none",
            category: Constructor,
        },
        TypeMapping {
            coq_name: "Coq.Init.Datatypes.pair",
            clean_name_mapping: "Prod.mk",
            category: Constructor,
        },
        TypeMapping {
            coq_name: "Coq.Init.Datatypes.tt",
            clean_name_mapping: "Unit.unit",
            category: Constructor,
        },
        TypeMapping {
            coq_name: "Coq.Init.Logic.eq_refl",
            clean_name_mapping: "Eq.refl",
            category: Constructor,
        },
        TypeMapping {
            coq_name: "Coq.Init.Logic.conj",
            clean_name_mapping: "And.intro",
            category: Constructor,
        },
        TypeMapping {
            coq_name: "Coq.Init.Logic.or_introl",
            clean_name_mapping: "Or.inl",
            category: Constructor,
        },
        TypeMapping {
            coq_name: "Coq.Init.Logic.or_intror",
            clean_name_mapping: "Or.inr",
            category: Constructor,
        },
        // --- Arithmetic ---
        TypeMapping {
            coq_name: "Coq.Init.Nat.add",
            clean_name_mapping: "Nat.add",
            category: Arithmetic,
        },
        TypeMapping {
            coq_name: "Coq.Init.Nat.mul",
            clean_name_mapping: "Nat.mul",
            category: Arithmetic,
        },
        TypeMapping {
            coq_name: "Coq.Init.Nat.sub",
            clean_name_mapping: "Nat.sub",
            category: Arithmetic,
        },
        TypeMapping {
            coq_name: "Coq.Init.Peano.plus",
            clean_name_mapping: "Nat.add",
            category: Arithmetic,
        },
        TypeMapping {
            coq_name: "Coq.Init.Peano.mult",
            clean_name_mapping: "Nat.mul",
            category: Arithmetic,
        },
        TypeMapping {
            coq_name: "Coq.Arith.PeanoNat.Nat.add",
            clean_name_mapping: "Nat.add",
            category: Arithmetic,
        },
        TypeMapping {
            coq_name: "Coq.Arith.PeanoNat.Nat.mul",
            clean_name_mapping: "Nat.mul",
            category: Arithmetic,
        },
        // --- Comparisons ---
        TypeMapping {
            coq_name: "Coq.Init.Peano.le",
            clean_name_mapping: "Nat.le",
            category: Comparison,
        },
        TypeMapping {
            coq_name: "Coq.Init.Peano.lt",
            clean_name_mapping: "Nat.lt",
            category: Comparison,
        },
        TypeMapping {
            coq_name: "Coq.Arith.PeanoNat.Nat.le",
            clean_name_mapping: "Nat.le",
            category: Comparison,
        },
        TypeMapping {
            coq_name: "Coq.Arith.PeanoNat.Nat.lt",
            clean_name_mapping: "Nat.lt",
            category: Comparison,
        },
        TypeMapping {
            coq_name: "Coq.Init.Nat.eqb",
            clean_name_mapping: "Nat.beq",
            category: Comparison,
        },
        TypeMapping {
            coq_name: "Coq.Init.Nat.leb",
            clean_name_mapping: "Nat.ble",
            category: Comparison,
        },
        // --- List operations ---
        TypeMapping {
            coq_name: "Coq.Lists.List.map",
            clean_name_mapping: "List.map",
            category: Arithmetic,
        },
        TypeMapping {
            coq_name: "Coq.Lists.List.fold_left",
            clean_name_mapping: "List.foldl",
            category: Arithmetic,
        },
        TypeMapping {
            coq_name: "Coq.Lists.List.fold_right",
            clean_name_mapping: "List.foldr",
            category: Arithmetic,
        },
        TypeMapping {
            coq_name: "Coq.Lists.List.filter",
            clean_name_mapping: "List.filter",
            category: Arithmetic,
        },
        TypeMapping {
            coq_name: "Coq.Lists.List.length",
            clean_name_mapping: "List.length",
            category: Arithmetic,
        },
        TypeMapping {
            coq_name: "Coq.Lists.List.app",
            clean_name_mapping: "List.append",
            category: Arithmetic,
        },
        TypeMapping {
            coq_name: "Coq.Lists.List.rev",
            clean_name_mapping: "List.reverse",
            category: Arithmetic,
        },
        TypeMapping {
            coq_name: "Coq.Lists.List.nth",
            clean_name_mapping: "List.get",
            category: Arithmetic,
        },
        TypeMapping {
            coq_name: "Coq.Lists.List.In",
            clean_name_mapping: "List.Mem",
            category: LogicalConnective,
        },
        TypeMapping {
            coq_name: "Coq.Lists.List.forallb",
            clean_name_mapping: "List.all",
            category: Arithmetic,
        },
        TypeMapping {
            coq_name: "Coq.Lists.List.existsb",
            clean_name_mapping: "List.any",
            category: Arithmetic,
        },
        TypeMapping {
            coq_name: "Coq.Lists.List.flat_map",
            clean_name_mapping: "List.flatMap",
            category: Arithmetic,
        },
        TypeMapping {
            coq_name: "Coq.Lists.List.combine",
            clean_name_mapping: "List.zip",
            category: Arithmetic,
        },
        TypeMapping {
            coq_name: "Coq.Lists.List.split",
            clean_name_mapping: "List.unzip",
            category: Arithmetic,
        },
        TypeMapping {
            coq_name: "Coq.Lists.List.hd",
            clean_name_mapping: "List.head!",
            category: Arithmetic,
        },
        TypeMapping {
            coq_name: "Coq.Lists.List.tl",
            clean_name_mapping: "List.tail!",
            category: Arithmetic,
        },
        // --- Option operations ---
        TypeMapping {
            coq_name: "Coq.Init.Datatypes.option_map",
            clean_name_mapping: "Option.map",
            category: Arithmetic,
        },
        TypeMapping {
            coq_name: "Coq.Init.Datatypes.option_bind",
            clean_name_mapping: "Option.bind",
            category: Arithmetic,
        },
        // --- String and Ascii types ---
        TypeMapping {
            coq_name: "Coq.Strings.Ascii.ascii",
            clean_name_mapping: "Char",
            category: BaseType,
        },
        TypeMapping {
            coq_name: "Coq.Strings.String.EmptyString",
            clean_name_mapping: "String.empty",
            category: Constructor,
        },
        TypeMapping {
            coq_name: "Coq.Strings.String.String_",
            clean_name_mapping: "String.push",
            category: Constructor,
        },
        TypeMapping {
            coq_name: "Coq.Strings.String.append",
            clean_name_mapping: "String.append",
            category: Arithmetic,
        },
        TypeMapping {
            coq_name: "Coq.Strings.String.length",
            clean_name_mapping: "String.length",
            category: Arithmetic,
        },
        // --- Sigma types and dependent pairs ---
        TypeMapping {
            coq_name: "Coq.Init.Specif.existT",
            clean_name_mapping: "Sigma.mk",
            category: Constructor,
        },
        TypeMapping {
            coq_name: "Coq.Init.Specif.projT1",
            clean_name_mapping: "Sigma.fst",
            category: Arithmetic,
        },
        TypeMapping {
            coq_name: "Coq.Init.Specif.projT2",
            clean_name_mapping: "Sigma.snd",
            category: Arithmetic,
        },
        TypeMapping {
            coq_name: "Coq.Init.Specif.exist",
            clean_name_mapping: "Subtype.mk",
            category: Constructor,
        },
        TypeMapping {
            coq_name: "Coq.Init.Specif.proj1_sig",
            clean_name_mapping: "Subtype.val",
            category: Arithmetic,
        },
        // --- Vector types ---
        TypeMapping {
            coq_name: "Coq.Vectors.Vector.t",
            clean_name_mapping: "Vector",
            category: TypeConstructor,
        },
        TypeMapping {
            coq_name: "Coq.Vectors.Vector.map",
            clean_name_mapping: "Vector.map",
            category: Arithmetic,
        },
        TypeMapping {
            coq_name: "Coq.Vectors.Vector.nth",
            clean_name_mapping: "Vector.get",
            category: Arithmetic,
        },
        TypeMapping {
            coq_name: "Coq.Vectors.Vector.cons",
            clean_name_mapping: "Vector.cons",
            category: Constructor,
        },
        TypeMapping {
            coq_name: "Coq.Vectors.Vector.nil",
            clean_name_mapping: "Vector.nil",
            category: Constructor,
        },
        // --- Finite types ---
        TypeMapping {
            coq_name: "Coq.Vectors.Fin.t",
            clean_name_mapping: "Fin",
            category: TypeConstructor,
        },
        TypeMapping {
            coq_name: "Coq.Vectors.Fin.of_nat",
            clean_name_mapping: "Fin.ofNat",
            category: Arithmetic,
        },
        TypeMapping {
            coq_name: "Coq.Vectors.Fin.to_nat",
            clean_name_mapping: "Fin.val",
            category: Arithmetic,
        },
        // --- ZArith operations ---
        TypeMapping {
            coq_name: "Coq.ZArith.BinInt.Z.add",
            clean_name_mapping: "Int.add",
            category: Arithmetic,
        },
        TypeMapping {
            coq_name: "Coq.ZArith.BinInt.Z.mul",
            clean_name_mapping: "Int.mul",
            category: Arithmetic,
        },
        TypeMapping {
            coq_name: "Coq.ZArith.BinInt.Z.sub",
            clean_name_mapping: "Int.sub",
            category: Arithmetic,
        },
        TypeMapping {
            coq_name: "Coq.ZArith.BinInt.Z.div",
            clean_name_mapping: "Int.div",
            category: Arithmetic,
        },
        TypeMapping {
            coq_name: "Coq.ZArith.BinInt.Z.modulo",
            clean_name_mapping: "Int.mod",
            category: Arithmetic,
        },
        TypeMapping {
            coq_name: "Coq.ZArith.BinInt.Z.opp",
            clean_name_mapping: "Int.neg",
            category: Arithmetic,
        },
        TypeMapping {
            coq_name: "Coq.ZArith.BinInt.Z.abs",
            clean_name_mapping: "Int.natAbs",
            category: Arithmetic,
        },
        TypeMapping {
            coq_name: "Coq.ZArith.BinInt.Z.le",
            clean_name_mapping: "Int.le",
            category: Comparison,
        },
        TypeMapping {
            coq_name: "Coq.ZArith.BinInt.Z.lt",
            clean_name_mapping: "Int.lt",
            category: Comparison,
        },
        TypeMapping {
            coq_name: "Coq.ZArith.BinInt.Z.ge",
            clean_name_mapping: "Int.ge",
            category: Comparison,
        },
        TypeMapping {
            coq_name: "Coq.ZArith.BinInt.Z.gt",
            clean_name_mapping: "Int.gt",
            category: Comparison,
        },
        TypeMapping {
            coq_name: "Coq.ZArith.BinInt.Z.compare",
            clean_name_mapping: "Int.compare",
            category: Comparison,
        },
        TypeMapping {
            coq_name: "Coq.ZArith.BinInt.Z.max",
            clean_name_mapping: "Int.max",
            category: Arithmetic,
        },
        TypeMapping {
            coq_name: "Coq.ZArith.BinInt.Z.min",
            clean_name_mapping: "Int.min",
            category: Arithmetic,
        },
        TypeMapping {
            coq_name: "Coq.ZArith.BinInt.Z.pow",
            clean_name_mapping: "Int.pow",
            category: Arithmetic,
        },
        // --- QArith basics ---
        TypeMapping {
            coq_name: "Coq.QArith.QArith_base.Q",
            clean_name_mapping: "Mathverse.Coq.Rat",
            category: BaseType,
        },
        TypeMapping {
            coq_name: "Coq.QArith.QArith_base.Qplus",
            clean_name_mapping: "Mathverse.Coq.Rat.add",
            category: Arithmetic,
        },
        TypeMapping {
            coq_name: "Coq.QArith.QArith_base.Qmult",
            clean_name_mapping: "Mathverse.Coq.Rat.mul",
            category: Arithmetic,
        },
        TypeMapping {
            coq_name: "Coq.QArith.QArith_base.Qminus",
            clean_name_mapping: "Mathverse.Coq.Rat.sub",
            category: Arithmetic,
        },
        TypeMapping {
            coq_name: "Coq.QArith.QArith_base.Qinv",
            clean_name_mapping: "Mathverse.Coq.Rat.inv",
            category: Arithmetic,
        },
        TypeMapping {
            coq_name: "Coq.QArith.QArith_base.Qle",
            clean_name_mapping: "Mathverse.Coq.Rat.le",
            category: Comparison,
        },
        TypeMapping {
            coq_name: "Coq.QArith.QArith_base.Qlt",
            clean_name_mapping: "Mathverse.Coq.Rat.lt",
            category: Comparison,
        },
        TypeMapping {
            coq_name: "Coq.QArith.QArith_base.Qeq",
            clean_name_mapping: "Mathverse.Coq.Rat.eq",
            category: Comparison,
        },
        // --- Decidability ---
        TypeMapping {
            coq_name: "Coq.Logic.Decidable.decidable",
            clean_name_mapping: "Decidable",
            category: LogicalConnective,
        },
        TypeMapping {
            coq_name: "Coq.Classes.DecidableClass.Decidable",
            clean_name_mapping: "Decidable",
            category: LogicalConnective,
        },
        TypeMapping {
            coq_name: "Coq.Arith.EqNat.eq_nat_dec",
            clean_name_mapping: "Nat.decEq",
            category: Arithmetic,
        },
        // --- Key theorems ---
        TypeMapping {
            coq_name: "Coq.Arith.PeanoNat.Nat.add_comm",
            clean_name_mapping: "Nat.add_comm",
            category: Theorem,
        },
        TypeMapping {
            coq_name: "Coq.Arith.PeanoNat.Nat.add_assoc",
            clean_name_mapping: "Nat.add_assoc",
            category: Theorem,
        },
        TypeMapping {
            coq_name: "Coq.Arith.PeanoNat.Nat.mul_comm",
            clean_name_mapping: "Nat.mul_comm",
            category: Theorem,
        },
        TypeMapping {
            coq_name: "Coq.Arith.PeanoNat.Nat.mul_assoc",
            clean_name_mapping: "Nat.mul_assoc",
            category: Theorem,
        },
        TypeMapping {
            coq_name: "Coq.Arith.PeanoNat.Nat.add_0_r",
            clean_name_mapping: "Nat.add_zero",
            category: Theorem,
        },
        TypeMapping {
            coq_name: "Coq.Arith.PeanoNat.Nat.mul_0_r",
            clean_name_mapping: "Nat.mul_zero",
            category: Theorem,
        },
        TypeMapping {
            coq_name: "Coq.Arith.PeanoNat.Nat.mul_1_r",
            clean_name_mapping: "Nat.mul_one",
            category: Theorem,
        },
        TypeMapping {
            coq_name: "Coq.Arith.PeanoNat.Nat.add_sub_cancel",
            clean_name_mapping: "Nat.add_sub_cancel",
            category: Theorem,
        },
    ]
}

/// Fast bidirectional lookup between Coq and Lean 5 names.
pub struct CoqStdlibMap {
    coq_to_clean: hashbrown::HashMap<&'static str, &'static TypeMapping>,
    clean_to_coq: hashbrown::HashMap<&'static str, Vec<&'static TypeMapping>>,
}

impl CoqStdlibMap {
    /// Build lookup tables from [`coq_clean_mappings`].
    pub fn new() -> Self {
        let mappings = coq_clean_mappings();
        let mut coq_to_clean = hashbrown::HashMap::with_capacity(mappings.len());
        let mut clean_to_coq: hashbrown::HashMap<&'static str, Vec<&'static TypeMapping>> =
            hashbrown::HashMap::with_capacity(mappings.len());
        for m in mappings {
            coq_to_clean.insert(m.coq_name, m);
            clean_to_coq
                .entry(m.clean_name_mapping)
                .or_default()
                .push(m);
        }
        Self {
            coq_to_clean,
            clean_to_coq,
        }
    }

    /// Get the singleton instance (lazily initialized).
    pub fn global() -> &'static Self {
        static INSTANCE: LazyLock<CoqStdlibMap> = LazyLock::new(CoqStdlibMap::new);
        &INSTANCE
    }

    /// Translate a Coq qualified name to its Lean 5 equivalent.
    pub fn translate_name(&self, coq_name: &str) -> Option<&'static str> {
        self.coq_to_clean
            .get(coq_name)
            .map(|m| m.clean_name_mapping)
    }

    /// Reverse lookup: Lean 5 name to all matching Coq entries.
    ///
    /// Multiple Coq names may map to the same Lean 5 name (e.g. `Coq.Init.Nat.add`
    /// and `Coq.Arith.PeanoNat.Nat.add` both map to `Nat.add`).
    pub fn reverse_lookup(&self, clean_name_mapping: &str) -> Option<&[&'static TypeMapping]> {
        self.clean_to_coq
            .get(clean_name_mapping)
            .map(|v| v.as_slice())
    }

    /// Look up the mapping category for a Coq name.
    pub fn category(&self, coq_name: &str) -> Option<MappingCategory> {
        self.coq_to_clean.get(coq_name).map(|m| m.category)
    }

    /// Total number of mappings in the table.
    pub fn mapping_count(&self) -> usize {
        self.coq_to_clean.len()
    }

    /// Translate a Coq name, falling back to a mangled name if not in the table.
    pub fn translate_or_mangle(&self, coq_name: &str) -> String {
        match self.translate_name(coq_name) {
            Some(name) => name.to_owned(),
            None => mangle_coq_name(coq_name),
        }
    }
}

impl Default for CoqStdlibMap {
    fn default() -> Self {
        Self::new()
    }
}

/// Mangle a Coq qualified name into a Lean 5-compatible name.
///
/// Strips the `Coq.` prefix and places the result under the `Mathverse.Coq`
/// namespace, so unmapped constants are isolated from the native Lean 5 stdlib.
///
/// ```text
/// "Coq.Arith.PeanoNat.Nat.foo_bar" -> "Mathverse.Coq.Arith.PeanoNat.Nat.foo_bar"
/// "MyLib.Thing"                     -> "Mathverse.Coq.MyLib.Thing"
/// ```
pub fn mangle_coq_name(coq_name: &str) -> String {
    let stem = coq_name.strip_prefix("Coq.").unwrap_or(coq_name);
    format!("Mathverse.Coq.{stem}")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_each_category_has_entries() {
        let mappings = coq_clean_mappings();
        let categories = [
            MappingCategory::BaseType,
            MappingCategory::TypeConstructor,
            MappingCategory::LogicalConnective,
            MappingCategory::Arithmetic,
            MappingCategory::Comparison,
            MappingCategory::Theorem,
            MappingCategory::Constructor,
        ];
        for cat in &categories {
            let count = mappings.iter().filter(|m| m.category == *cat).count();
            assert!(count > 0, "category {cat:?} has no entries");
        }
    }

    #[test]
    fn test_translate_known_names() {
        let map = CoqStdlibMap::new();
        assert_eq!(map.translate_name("Coq.Init.Datatypes.nat"), Some("Nat"));
        assert_eq!(map.translate_name("Coq.Init.Datatypes.bool"), Some("Bool"));
        assert_eq!(map.translate_name("Coq.Init.Logic.eq"), Some("Eq"));
        assert_eq!(map.translate_name("Coq.Init.Datatypes.O"), Some("Nat.zero"));
        assert_eq!(map.translate_name("Coq.Init.Datatypes.S"), Some("Nat.succ"));
        assert_eq!(map.translate_name("Coq.Init.Nat.add"), Some("Nat.add"));
        assert_eq!(
            map.translate_name("Coq.Arith.PeanoNat.Nat.add_comm"),
            Some("Nat.add_comm")
        );
    }

    #[test]
    fn test_translate_unknown_returns_none() {
        let map = CoqStdlibMap::new();
        assert_eq!(map.translate_name("Coq.Nonexistent.thing"), None);
        assert_eq!(map.translate_name(""), None);
    }

    #[test]
    fn test_reverse_lookup() {
        let map = CoqStdlibMap::new();
        // Nat.add has multiple Coq sources
        let entries = map
            .reverse_lookup("Nat.add")
            .expect("Nat.add should have entries");
        assert!(
            entries.len() >= 3,
            "Nat.add mapped from Init.Nat, Init.Peano, and Arith.PeanoNat"
        );
        for e in entries {
            assert_eq!(e.clean_name_mapping, "Nat.add");
        }

        // Single-source mapping
        let entries = map.reverse_lookup("Nat").expect("Nat should have entries");
        assert_eq!(entries.len(), 1);
        assert_eq!(entries[0].coq_name, "Coq.Init.Datatypes.nat");
    }

    #[test]
    fn test_reverse_lookup_unknown() {
        let map = CoqStdlibMap::new();
        assert!(map.reverse_lookup("NonexistentType").is_none());
    }

    #[test]
    fn test_translate_or_mangle_mapped() {
        let map = CoqStdlibMap::new();
        assert_eq!(map.translate_or_mangle("Coq.Init.Datatypes.nat"), "Nat");
        assert_eq!(map.translate_or_mangle("Coq.Init.Logic.and"), "And");
    }

    #[test]
    fn test_translate_or_mangle_unmapped() {
        let map = CoqStdlibMap::new();
        assert_eq!(
            map.translate_or_mangle("Coq.Arith.PeanoNat.Nat.foo_bar"),
            "Mathverse.Coq.Arith.PeanoNat.Nat.foo_bar"
        );
        assert_eq!(
            map.translate_or_mangle("MyLib.Thing"),
            "Mathverse.Coq.MyLib.Thing"
        );
    }

    #[test]
    fn test_mangle_coq_name() {
        assert_eq!(
            mangle_coq_name("Coq.Arith.PeanoNat.Nat.foo_bar"),
            "Mathverse.Coq.Arith.PeanoNat.Nat.foo_bar"
        );
        assert_eq!(mangle_coq_name("MyLib.Thing"), "Mathverse.Coq.MyLib.Thing");
        assert_eq!(
            mangle_coq_name("Coq.Init.Datatypes.nat"),
            "Mathverse.Coq.Init.Datatypes.nat"
        );
    }

    #[test]
    fn test_mapping_count() {
        let map = CoqStdlibMap::new();
        let expected = coq_clean_mappings().len();
        assert_eq!(map.mapping_count(), expected);
        // Sanity: we have a substantial table
        assert!(
            expected >= 110,
            "expected at least 110 mappings, got {expected}"
        );
    }

    #[test]
    fn test_no_duplicate_coq_names() {
        let mappings = coq_clean_mappings();
        let mut seen = hashbrown::HashSet::new();
        for m in mappings {
            assert!(
                seen.insert(m.coq_name),
                "duplicate Coq name in mapping table: {}",
                m.coq_name
            );
        }
    }

    #[test]
    fn test_category_classification() {
        let map = CoqStdlibMap::new();
        assert_eq!(
            map.category("Coq.Init.Datatypes.nat"),
            Some(MappingCategory::BaseType)
        );
        assert_eq!(
            map.category("Coq.Init.Datatypes.list"),
            Some(MappingCategory::TypeConstructor)
        );
        assert_eq!(
            map.category("Coq.Init.Logic.and"),
            Some(MappingCategory::LogicalConnective)
        );
        assert_eq!(
            map.category("Coq.Init.Nat.add"),
            Some(MappingCategory::Arithmetic)
        );
        assert_eq!(
            map.category("Coq.Init.Peano.le"),
            Some(MappingCategory::Comparison)
        );
        assert_eq!(
            map.category("Coq.Arith.PeanoNat.Nat.add_comm"),
            Some(MappingCategory::Theorem)
        );
        assert_eq!(
            map.category("Coq.Init.Datatypes.O"),
            Some(MappingCategory::Constructor)
        );
        assert_eq!(map.category("Coq.Nonexistent"), None);
    }

    #[test]
    fn test_global_singleton() {
        let a = CoqStdlibMap::global();
        let b = CoqStdlibMap::global();
        assert_eq!(a.mapping_count(), b.mapping_count());
        // Both should point to the same static data
        assert!(std::ptr::eq(a, b));
    }

    #[test]
    fn test_translate_list_operations() {
        let map = CoqStdlibMap::new();
        assert_eq!(map.translate_name("Coq.Lists.List.map"), Some("List.map"));
        assert_eq!(
            map.translate_name("Coq.Lists.List.fold_left"),
            Some("List.foldl")
        );
        assert_eq!(
            map.translate_name("Coq.Lists.List.filter"),
            Some("List.filter")
        );
        assert_eq!(
            map.translate_name("Coq.Lists.List.length"),
            Some("List.length")
        );
        assert_eq!(
            map.translate_name("Coq.Lists.List.app"),
            Some("List.append")
        );
        assert_eq!(
            map.translate_name("Coq.Lists.List.rev"),
            Some("List.reverse")
        );
        assert_eq!(map.translate_name("Coq.Lists.List.nth"), Some("List.get"));
        assert_eq!(map.translate_name("Coq.Lists.List.In"), Some("List.Mem"));
        assert_eq!(
            map.translate_name("Coq.Lists.List.flat_map"),
            Some("List.flatMap")
        );
    }

    #[test]
    fn test_translate_option_operations() {
        let map = CoqStdlibMap::new();
        assert_eq!(
            map.translate_name("Coq.Init.Datatypes.option_map"),
            Some("Option.map")
        );
        assert_eq!(
            map.translate_name("Coq.Init.Datatypes.option_bind"),
            Some("Option.bind")
        );
    }

    #[test]
    fn test_translate_string_ascii() {
        let map = CoqStdlibMap::new();
        assert_eq!(map.translate_name("Coq.Strings.Ascii.ascii"), Some("Char"));
        assert_eq!(
            map.translate_name("Coq.Strings.String.EmptyString"),
            Some("String.empty")
        );
        assert_eq!(
            map.translate_name("Coq.Strings.String.append"),
            Some("String.append")
        );
    }

    #[test]
    fn test_translate_sigma_types() {
        let map = CoqStdlibMap::new();
        assert_eq!(
            map.translate_name("Coq.Init.Specif.existT"),
            Some("Sigma.mk")
        );
        assert_eq!(
            map.translate_name("Coq.Init.Specif.projT1"),
            Some("Sigma.fst")
        );
        assert_eq!(
            map.translate_name("Coq.Init.Specif.projT2"),
            Some("Sigma.snd")
        );
        assert_eq!(
            map.translate_name("Coq.Init.Specif.exist"),
            Some("Subtype.mk")
        );
        assert_eq!(
            map.translate_name("Coq.Init.Specif.proj1_sig"),
            Some("Subtype.val")
        );
    }

    #[test]
    fn test_translate_vector_types() {
        let map = CoqStdlibMap::new();
        assert_eq!(map.translate_name("Coq.Vectors.Vector.t"), Some("Vector"));
        assert_eq!(
            map.translate_name("Coq.Vectors.Vector.map"),
            Some("Vector.map")
        );
        assert_eq!(
            map.translate_name("Coq.Vectors.Vector.nth"),
            Some("Vector.get")
        );
    }

    #[test]
    fn test_translate_fin_types() {
        let map = CoqStdlibMap::new();
        assert_eq!(map.translate_name("Coq.Vectors.Fin.t"), Some("Fin"));
        assert_eq!(
            map.translate_name("Coq.Vectors.Fin.of_nat"),
            Some("Fin.ofNat")
        );
        assert_eq!(
            map.translate_name("Coq.Vectors.Fin.to_nat"),
            Some("Fin.val")
        );
    }

    #[test]
    fn test_translate_zarith_operations() {
        let map = CoqStdlibMap::new();
        assert_eq!(
            map.translate_name("Coq.ZArith.BinInt.Z.add"),
            Some("Int.add")
        );
        assert_eq!(
            map.translate_name("Coq.ZArith.BinInt.Z.mul"),
            Some("Int.mul")
        );
        assert_eq!(
            map.translate_name("Coq.ZArith.BinInt.Z.sub"),
            Some("Int.sub")
        );
        assert_eq!(
            map.translate_name("Coq.ZArith.BinInt.Z.div"),
            Some("Int.div")
        );
        assert_eq!(
            map.translate_name("Coq.ZArith.BinInt.Z.modulo"),
            Some("Int.mod")
        );
        assert_eq!(
            map.translate_name("Coq.ZArith.BinInt.Z.opp"),
            Some("Int.neg")
        );
        assert_eq!(
            map.translate_name("Coq.ZArith.BinInt.Z.abs"),
            Some("Int.natAbs")
        );
        assert_eq!(map.translate_name("Coq.ZArith.BinInt.Z.le"), Some("Int.le"));
        assert_eq!(map.translate_name("Coq.ZArith.BinInt.Z.lt"), Some("Int.lt"));
        assert_eq!(
            map.translate_name("Coq.ZArith.BinInt.Z.compare"),
            Some("Int.compare")
        );
        assert_eq!(
            map.translate_name("Coq.ZArith.BinInt.Z.pow"),
            Some("Int.pow")
        );
    }

    #[test]
    fn test_translate_qarith_basics() {
        let map = CoqStdlibMap::new();
        assert_eq!(
            map.translate_name("Coq.QArith.QArith_base.Q"),
            Some("Mathverse.Coq.Rat")
        );
        assert_eq!(
            map.translate_name("Coq.QArith.QArith_base.Qplus"),
            Some("Mathverse.Coq.Rat.add")
        );
        assert_eq!(
            map.translate_name("Coq.QArith.QArith_base.Qmult"),
            Some("Mathverse.Coq.Rat.mul")
        );
        assert_eq!(
            map.translate_name("Coq.QArith.QArith_base.Qle"),
            Some("Mathverse.Coq.Rat.le")
        );
    }

    #[test]
    fn test_translate_decidability() {
        let map = CoqStdlibMap::new();
        assert_eq!(
            map.translate_name("Coq.Logic.Decidable.decidable"),
            Some("Decidable")
        );
        assert_eq!(
            map.translate_name("Coq.Arith.EqNat.eq_nat_dec"),
            Some("Nat.decEq")
        );
    }

    #[test]
    fn test_zarith_category_classification() {
        let map = CoqStdlibMap::new();
        assert_eq!(
            map.category("Coq.ZArith.BinInt.Z.add"),
            Some(MappingCategory::Arithmetic)
        );
        assert_eq!(
            map.category("Coq.ZArith.BinInt.Z.le"),
            Some(MappingCategory::Comparison)
        );
    }

    #[test]
    fn test_list_in_is_logical_connective() {
        let map = CoqStdlibMap::new();
        assert_eq!(
            map.category("Coq.Lists.List.In"),
            Some(MappingCategory::LogicalConnective)
        );
    }
}
