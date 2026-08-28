// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Comparison half of the centralized head-family classifier.
//!
//! The comparison tables (`LT.lt`/`Int.le`/`Rat.ge`/...) and their two
//! classifiers — the `&str` form and the allocation-free [`Name`] form — plus
//! the [`CmpFamily`] diagnostic tag live here; the arithmetic tables stay in
//! the parent module. Both halves are re-exported from `head_family`, so
//! `bridge::head_family::classify_cmp_head` remains the public path.

use clean_kernel::name::Name;

use crate::bridge::name_match::{name_eq_any, name_eq_str};

use super::SortHint;

/// Comparison operator family.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum CmpFamily {
    Lt,
    Le,
    Gt,
    Ge,
}

/// Classified comparison head.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub struct CmpHead {
    pub family: CmpFamily,
    pub sort_hint: SortHint,
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
