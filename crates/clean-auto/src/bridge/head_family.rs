// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Centralized head-family classifier for SMT arithmetic and comparison operators.
//!
//! Lean 4 expresses arithmetic and comparison through multiple aliased heads:
//! typeclass forms (`HAdd.hAdd`, `LT.lt`), shorter typeclass forms (`Add.add`),
//! and direct sort-specific forms (`Int.add`, `Real.lt`). This module provides
//! a single lookup table that classifies any recognized head name into its
//! operator family and sort hint.
//!
//! # Consumers
//!
//! - `bridge::expr_classifier` — semantic classification of kernel expressions
//! - `bridge::ay_backend::proof_reconstruct::theory_lemma_lra` — additive child detection
//! - `clean_elab::tactic::smt::decide::recovery` — diagnostic classification
//!
//! Part of #2806: centralizes head-family tables that were previously duplicated
//! across these three layers.

use clean_kernel::name::Name;

use super::name_match::{name_eq_any, name_eq_str};

/// Arithmetic operator family.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum ArithFamily {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Neg,
}

/// Comparison operator family.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum CmpFamily {
    Lt,
    Le,
    Gt,
    Ge,
}

/// Sort hint from the constant name prefix.
///
/// Direct forms (e.g., `Int.add`, `Real.lt`) carry an inherent sort.
/// Typeclass forms (e.g., `HAdd.hAdd`, `LT.lt`) require sort resolution
/// from application arguments.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum SortHint {
    Nat,
    Int,
    Real,
    /// Typeclass form — sort must be determined from arguments.
    FromArgs,
}

/// Classified arithmetic head.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub struct ArithHead {
    pub family: ArithFamily,
    pub sort_hint: SortHint,
}

/// Classified comparison head.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub struct CmpHead {
    pub family: CmpFamily,
    pub sort_hint: SortHint,
}

/// Classify a dotted constant name as an arithmetic operator.
///
/// Returns `None` if the name is not a recognized arithmetic head.
#[must_use]
pub fn classify_arith_head(name: &str) -> Option<ArithHead> {
    use ArithFamily::*;
    use SortHint::*;

    let (family, sort) = match name {
        // Typeclass forms (sort from args)
        "HAdd.hAdd" | "Add.add" => (Add, FromArgs),
        "HSub.hSub" | "Sub.sub" => (Sub, FromArgs),
        "HMul.hMul" | "Mul.mul" => (Mul, FromArgs),
        "HDiv.hDiv" | "Div.div" => (Div, FromArgs),
        "HMod.hMod" | "Mod.mod" => (Mod, FromArgs),
        "Neg.neg" => (Neg, FromArgs),
        // Nat direct
        "Nat.add" => (Add, Nat),
        "Nat.sub" => (Sub, Nat),
        "Nat.mul" => (Mul, Nat),
        "Nat.div" => (Div, Nat),
        "Nat.mod" => (Mod, Nat),
        // Int direct
        "Int.add" => (Add, Int),
        "Int.sub" => (Sub, Int),
        "Int.mul" => (Mul, Int),
        "Int.div" => (Div, Int),
        "Int.mod" => (Mod, Int),
        "Int.neg" | "Int.negSucc" => (Neg, Int),
        // Real direct
        "Real.add" => (Add, Real),
        "Real.sub" => (Sub, Real),
        "Real.mul" => (Mul, Real),
        "Real.div" => (Div, Real),
        // Rat direct (Rat maps to SMT Real — dense ordered field)
        "Rat.add" => (Add, Real),
        "Rat.sub" => (Sub, Real),
        "Rat.mul" => (Mul, Real),
        "Rat.div" => (Div, Real),
        "Rat.neg" => (Neg, Real),
        _ => return None,
    };
    Some(ArithHead {
        family,
        sort_hint: sort,
    })
}

/// Classify a constant name as an arithmetic operator without allocating.
#[must_use]
pub(crate) fn classify_arith_head_name(name: &Name) -> Option<ArithHead> {
    use ArithFamily::*;
    use SortHint::*;

    let (family, sort) = if name_eq_any(name, &["HAdd.hAdd", "Add.add"]) {
        (Add, FromArgs)
    } else if name_eq_any(name, &["HSub.hSub", "Sub.sub"]) {
        (Sub, FromArgs)
    } else if name_eq_any(name, &["HMul.hMul", "Mul.mul"]) {
        (Mul, FromArgs)
    } else if name_eq_any(name, &["HDiv.hDiv", "Div.div"]) {
        (Div, FromArgs)
    } else if name_eq_any(name, &["HMod.hMod", "Mod.mod"]) {
        (Mod, FromArgs)
    } else if name_eq_str(name, "Neg.neg") {
        (Neg, FromArgs)
    } else if name_eq_str(name, "Nat.add") {
        (Add, Nat)
    } else if name_eq_str(name, "Nat.sub") {
        (Sub, Nat)
    } else if name_eq_str(name, "Nat.mul") {
        (Mul, Nat)
    } else if name_eq_str(name, "Nat.div") {
        (Div, Nat)
    } else if name_eq_str(name, "Nat.mod") {
        (Mod, Nat)
    } else if name_eq_str(name, "Int.add") {
        (Add, Int)
    } else if name_eq_str(name, "Int.sub") {
        (Sub, Int)
    } else if name_eq_str(name, "Int.mul") {
        (Mul, Int)
    } else if name_eq_str(name, "Int.div") {
        (Div, Int)
    } else if name_eq_str(name, "Int.mod") {
        (Mod, Int)
    } else if name_eq_any(name, &["Int.neg", "Int.negSucc"]) {
        (Neg, Int)
    } else if name_eq_str(name, "Real.add") {
        (Add, Real)
    } else if name_eq_str(name, "Real.sub") {
        (Sub, Real)
    } else if name_eq_str(name, "Real.mul") {
        (Mul, Real)
    } else if name_eq_str(name, "Real.div") {
        (Div, Real)
    // Rat direct (Rat maps to SMT Real — dense ordered field)
    } else if name_eq_str(name, "Rat.add") {
        (Add, Real)
    } else if name_eq_str(name, "Rat.sub") {
        (Sub, Real)
    } else if name_eq_str(name, "Rat.mul") {
        (Mul, Real)
    } else if name_eq_str(name, "Rat.div") {
        (Div, Real)
    } else if name_eq_str(name, "Rat.neg") {
        (Neg, Real)
    } else {
        return None;
    };

    Some(ArithHead {
        family,
        sort_hint: sort,
    })
}

/// Classify a dotted constant name as a comparison operator.
///
/// Returns `None` if the name is not a recognized comparison head.
#[must_use]
pub fn classify_cmp_head(name: &str) -> Option<CmpHead> {
    use CmpFamily::*;
    use SortHint::*;

    let (family, sort) = match name {
        // Typeclass forms (sort from args)
        "LT.lt" | "lt" => (Lt, FromArgs),
        "LE.le" | "le" => (Le, FromArgs),
        "GT.gt" | "gt" => (Gt, FromArgs),
        "GE.ge" | "ge" => (Ge, FromArgs),
        // Int direct
        "Int.lt" => (Lt, Int),
        "Int.le" => (Le, Int),
        "Int.gt" => (Gt, Int),
        "Int.ge" => (Ge, Int),
        // Nat direct
        "Nat.lt" => (Lt, Nat),
        "Nat.le" => (Le, Nat),
        "Nat.gt" => (Gt, Nat),
        "Nat.ge" => (Ge, Nat),
        // Real direct (Real.gt and Real.ge not yet present in Lean 4 stdlib)
        "Real.lt" => (Lt, Real),
        "Real.le" => (Le, Real),
        // Rat direct (Rat maps to SMT Real — dense ordered field)
        "Rat.lt" => (Lt, Real),
        "Rat.le" => (Le, Real),
        "Rat.gt" => (Gt, Real),
        "Rat.ge" => (Ge, Real),
        _ => return None,
    };
    Some(CmpHead {
        family,
        sort_hint: sort,
    })
}

/// Classify a constant name as a comparison operator without allocating.
#[must_use]
pub(crate) fn classify_cmp_head_name(name: &Name) -> Option<CmpHead> {
    use CmpFamily::*;
    use SortHint::*;

    let (family, sort) = if name_eq_any(name, &["LT.lt", "lt"]) {
        (Lt, FromArgs)
    } else if name_eq_any(name, &["LE.le", "le"]) {
        (Le, FromArgs)
    } else if name_eq_any(name, &["GT.gt", "gt"]) {
        (Gt, FromArgs)
    } else if name_eq_any(name, &["GE.ge", "ge"]) {
        (Ge, FromArgs)
    } else if name_eq_str(name, "Int.lt") {
        (Lt, Int)
    } else if name_eq_str(name, "Int.le") {
        (Le, Int)
    } else if name_eq_str(name, "Int.gt") {
        (Gt, Int)
    } else if name_eq_str(name, "Int.ge") {
        (Ge, Int)
    } else if name_eq_str(name, "Nat.lt") {
        (Lt, Nat)
    } else if name_eq_str(name, "Nat.le") {
        (Le, Nat)
    } else if name_eq_str(name, "Nat.gt") {
        (Gt, Nat)
    } else if name_eq_str(name, "Nat.ge") {
        (Ge, Nat)
    } else if name_eq_str(name, "Real.lt") {
        (Lt, Real)
    } else if name_eq_str(name, "Real.le") {
        (Le, Real)
    // Rat direct (Rat maps to SMT Real — dense ordered field)
    } else if name_eq_str(name, "Rat.lt") {
        (Lt, Real)
    } else if name_eq_str(name, "Rat.le") {
        (Le, Real)
    } else if name_eq_str(name, "Rat.gt") {
        (Gt, Real)
    } else if name_eq_str(name, "Rat.ge") {
        (Ge, Real)
    } else {
        return None;
    };

    Some(CmpHead {
        family,
        sort_hint: sort,
    })
}

/// Check if a dotted constant name is any recognized arithmetic or comparison head.
#[must_use]
pub fn is_arith_or_cmp_head(name: &str) -> bool {
    classify_arith_head(name).is_some() || classify_cmp_head(name).is_some()
}

/// Check if a constant name is any recognized arithmetic or comparison head.
#[cfg(test)]
#[must_use]
pub(crate) fn is_arith_or_cmp_head_name(name: &Name) -> bool {
    classify_arith_head_name(name).is_some() || classify_cmp_head_name(name).is_some()
}

impl SortHint {
    /// Return the sort name string for direct forms, or empty string for typeclass forms.
    ///
    /// This matches the existing `type_hint` convention in expr_classifier where
    /// `""` means "resolve from args" and `"Nat"`/`"Int"`/`"Real"` are direct.
    pub(crate) fn as_type_hint_str(&self) -> &'static str {
        match self {
            SortHint::Nat => "Nat",
            SortHint::Int => "Int",
            SortHint::Real => "Real",
            SortHint::FromArgs => "",
        }
    }
}

impl ArithHead {
    /// Whether this is a unary operator (Neg family).
    pub(crate) fn is_unary(&self) -> bool {
        matches!(self.family, ArithFamily::Neg)
    }
}

impl CmpFamily {
    /// Return the diagnostic tag string for this comparison family.
    pub fn as_tag(&self) -> &'static str {
        match self {
            CmpFamily::Lt => "lt",
            CmpFamily::Le => "le",
            CmpFamily::Gt => "gt",
            CmpFamily::Ge => "ge",
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::name::Name;

    #[test]
    fn test_arith_typeclass_forms() {
        let h = classify_arith_head("HAdd.hAdd").unwrap();
        assert_eq!(h.family, ArithFamily::Add);
        assert_eq!(h.sort_hint, SortHint::FromArgs);

        let h = classify_arith_head("Neg.neg").unwrap();
        assert_eq!(h.family, ArithFamily::Neg);
        assert!(h.is_unary());
    }

    #[test]
    fn test_arith_direct_forms() {
        let h = classify_arith_head("Int.add").unwrap();
        assert_eq!(h.family, ArithFamily::Add);
        assert_eq!(h.sort_hint, SortHint::Int);

        let h = classify_arith_head("Real.div").unwrap();
        assert_eq!(h.family, ArithFamily::Div);
        assert_eq!(h.sort_hint, SortHint::Real);

        let h = classify_arith_head("Int.negSucc").unwrap();
        assert_eq!(h.family, ArithFamily::Neg);
        assert_eq!(h.sort_hint, SortHint::Int);
    }

    #[test]
    fn test_cmp_typeclass_forms() {
        let h = classify_cmp_head("LT.lt").unwrap();
        assert_eq!(h.family, CmpFamily::Lt);
        assert_eq!(h.sort_hint, SortHint::FromArgs);

        let h = classify_cmp_head("ge").unwrap();
        assert_eq!(h.family, CmpFamily::Ge);
        assert_eq!(h.sort_hint, SortHint::FromArgs);
    }

    #[test]
    fn test_cmp_direct_forms() {
        let h = classify_cmp_head("Real.lt").unwrap();
        assert_eq!(h.family, CmpFamily::Lt);
        assert_eq!(h.sort_hint, SortHint::Real);

        let h = classify_cmp_head("Nat.ge").unwrap();
        assert_eq!(h.family, CmpFamily::Ge);
        assert_eq!(h.sort_hint, SortHint::Nat);
    }

    #[test]
    fn test_unknown_names_return_none() {
        assert!(classify_arith_head("Foo.bar").is_none());
        assert!(classify_cmp_head("And").is_none());
        assert!(!is_arith_or_cmp_head("Eq"));
    }

    #[test]
    fn test_is_arith_or_cmp_covers_all() {
        assert!(is_arith_or_cmp_head("HAdd.hAdd"));
        assert!(is_arith_or_cmp_head("Int.neg"));
        assert!(is_arith_or_cmp_head("LT.lt"));
        assert!(is_arith_or_cmp_head("Real.le"));
        assert!(!is_arith_or_cmp_head("Exists"));
    }

    #[test]
    fn test_sort_hint_as_type_hint_str() {
        assert_eq!(SortHint::Nat.as_type_hint_str(), "Nat");
        assert_eq!(SortHint::Int.as_type_hint_str(), "Int");
        assert_eq!(SortHint::Real.as_type_hint_str(), "Real");
        assert_eq!(SortHint::FromArgs.as_type_hint_str(), "");
    }

    #[test]
    fn test_name_based_arith_api_matches_string_api() {
        let name = Name::from_string("Int.negSucc");
        assert_eq!(
            classify_arith_head_name(&name),
            classify_arith_head("Int.negSucc")
        );
        assert!(is_arith_or_cmp_head_name(&name));
    }

    #[test]
    fn test_name_based_cmp_api_matches_string_api() {
        let name = Name::from_string("Real.le");
        assert_eq!(classify_cmp_head_name(&name), classify_cmp_head("Real.le"));
        assert!(is_arith_or_cmp_head_name(&name));
    }

    #[test]
    fn test_name_anon_rejects_all_classifications() {
        let anon = Name::anon();
        assert!(classify_arith_head_name(&anon).is_none());
        assert!(classify_cmp_head_name(&anon).is_none());
        assert!(!is_arith_or_cmp_head_name(&anon));
    }

    #[test]
    fn test_name_eq_str_rejects_partial_suffix_match() {
        // "hAdd" is a suffix of "HAdd.hAdd" — must NOT match
        let name = Name::from_string("HAdd.hAdd");
        assert!(classify_arith_head_name(&name).is_some()); // full match
        let suffix_only = Name::from_string("hAdd");
        assert!(classify_arith_head_name(&suffix_only).is_none()); // suffix != full
    }

    #[test]
    fn test_name_based_api_exhaustive_arith_parity() {
        // Every string-API recognized name must also be recognized by the Name-API.
        let arith_names = [
            "HAdd.hAdd",
            "Add.add",
            "HSub.hSub",
            "Sub.sub",
            "HMul.hMul",
            "Mul.mul",
            "HDiv.hDiv",
            "Div.div",
            "HMod.hMod",
            "Mod.mod",
            "Neg.neg",
            "Nat.add",
            "Nat.sub",
            "Nat.mul",
            "Nat.div",
            "Nat.mod",
            "Int.add",
            "Int.sub",
            "Int.mul",
            "Int.div",
            "Int.mod",
            "Int.neg",
            "Int.negSucc",
            "Real.add",
            "Real.sub",
            "Real.mul",
            "Real.div",
            "Rat.add",
            "Rat.sub",
            "Rat.mul",
            "Rat.div",
            "Rat.neg",
        ];
        for &s in &arith_names {
            let str_result = classify_arith_head(s);
            let name_result = classify_arith_head_name(&Name::from_string(s));
            assert_eq!(str_result, name_result, "string/Name parity failed for {s}");
        }
    }

    #[test]
    fn test_name_based_api_exhaustive_cmp_parity() {
        let cmp_names = [
            "LT.lt", "lt", "LE.le", "le", "GT.gt", "gt", "GE.ge", "ge", "Int.lt", "Int.le",
            "Int.gt", "Int.ge", "Nat.lt", "Nat.le", "Nat.gt", "Nat.ge", "Real.lt", "Real.le",
            "Rat.lt", "Rat.le", "Rat.gt", "Rat.ge",
        ];
        for &s in &cmp_names {
            let str_result = classify_cmp_head(s);
            let name_result = classify_cmp_head_name(&Name::from_string(s));
            assert_eq!(str_result, name_result, "string/Name parity failed for {s}");
        }
    }

    #[test]
    fn test_nat_sort_hint_on_all_nat_direct_forms() {
        // Verify all Nat direct forms carry SortHint::Nat
        for name in ["Nat.add", "Nat.sub", "Nat.mul", "Nat.div", "Nat.mod"] {
            let h = classify_arith_head(name).unwrap_or_else(|| panic!("{name} should classify"));
            assert_eq!(h.sort_hint, SortHint::Nat, "wrong sort hint for {name}");
        }
        for name in ["Nat.lt", "Nat.le", "Nat.gt", "Nat.ge"] {
            let h = classify_cmp_head(name).unwrap_or_else(|| panic!("{name} should classify"));
            assert_eq!(h.sort_hint, SortHint::Nat, "wrong sort hint for {name}");
        }
    }

    #[test]
    fn test_cmp_family_tag_round_trip() {
        assert_eq!(CmpFamily::Lt.as_tag(), "lt");
        assert_eq!(CmpFamily::Le.as_tag(), "le");
        assert_eq!(CmpFamily::Gt.as_tag(), "gt");
        assert_eq!(CmpFamily::Ge.as_tag(), "ge");
    }
}
