// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lean `Rat` <-> SMT `Real` mapping helpers.
//!
//! SMT-LIB's `Real` sort models a dense ordered field over the rationals, so
//! Lean's `Rat` lowers soundly to SMT `Real`. Kernel proof reconstruction still
//! needs to distinguish `Rat` from `Real` so it can select the correct Lean
//! lemmas (`Rat.*` vs `Real.*`). This module centralizes that bidirectional
//! mapping for lowering and proof reconstruction.

use std::collections::HashSet;

use ay::Sort;
use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprKind, FVarId};

use crate::arith_proof::ArithSort;

fn is_named_type(ty: &Expr, expected: &str) -> bool {
    let ty = ty.strip_mdata();
    match ty.kind() {
        ExprKind::Const(name, _) => name.to_string() == expected,
        ExprKind::App(_, _) => matches!(
            ty.get_app_fn().strip_mdata().kind(),
            ExprKind::Const(name, _) if name.to_string() == expected
        ),
        _ => false,
    }
}

/// Return `true` when the Lean type expression denotes `Rat`.
#[must_use]
pub(crate) fn is_rat_type(ty: &Expr) -> bool {
    is_named_type(ty, "Rat")
}

/// Return `true` when the Lean type expression denotes `Rat` or `Real`.
#[must_use]
pub(crate) fn is_rat_or_real_type(ty: &Expr) -> bool {
    is_rat_type(ty) || is_named_type(ty, "Real")
}

/// Prefer Lean `Rat` over SMT `Real` when selecting arithmetic reconstruction sorts.
#[must_use]
pub(crate) fn detect_rat_arith_sort(sort: &Sort, lean_ty: Option<&Expr>) -> ArithSort {
    if lean_ty.is_some_and(is_rat_type) {
        return ArithSort::Rat;
    }
    if sort.is_int() {
        ArithSort::Int
    } else if sort.is_real() {
        ArithSort::Real
    } else {
        // Callers use this helper on arithmetic paths; preserve the existing
        // Real default for any non-Int fallback.
        ArithSort::Real
    }
}

/// Build the kernel type expression for `Rat`.
pub(crate) fn mk_rat_type_expr() -> Expr {
    Expr::const_(Name::from_string("Rat"), vec![])
}

/// Tracks which SMT variables originated from Lean `Rat`-typed free variables.
#[derive(Debug, Clone, Default)]
#[non_exhaustive]
pub(crate) struct RatSmtMapping {
    pub(crate) rat_fvars: HashSet<FVarId>,
}

impl RatSmtMapping {
    pub(crate) fn register_rat_fvar(&mut self, fvar_id: FVarId) {
        self.rat_fvars.insert(fvar_id);
    }

    #[must_use]
    pub(crate) fn is_rat_fvar(&self, fvar_id: FVarId) -> bool {
        self.rat_fvars.contains(&fvar_id)
    }

    #[must_use]
    pub(crate) fn arith_sort_for_fvar(&self, fvar_id: FVarId, ay_sort: &Sort) -> ArithSort {
        if self.is_rat_fvar(fvar_id) {
            ArithSort::Rat
        } else {
            detect_rat_arith_sort(ay_sort, None)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{
        detect_rat_arith_sort, is_rat_or_real_type, is_rat_type, mk_rat_type_expr, RatSmtMapping,
    };
    use crate::arith_proof::ArithSort;
    use ay::Sort;
    use clean_kernel::name::Name;
    use clean_kernel::{Expr, FVarId};

    #[test]
    fn test_rat_smt_type_predicates_recognize_rat_and_real() {
        let rat = Expr::const_(Name::from_string("Rat"), vec![]);
        let real = Expr::const_(Name::from_string("Real"), vec![]);
        let rat_app = Expr::app(
            rat.clone(),
            Expr::const_(Name::from_string("dummy"), vec![]),
        );

        assert!(is_rat_type(&rat));
        assert!(is_rat_type(&rat_app));
        assert!(is_rat_or_real_type(&rat));
        assert!(is_rat_or_real_type(&real));
        assert!(!is_rat_type(&real));
    }

    #[test]
    fn test_rat_smt_detect_rat_arith_sort_prefers_lean_rat_type() {
        let rat = mk_rat_type_expr();

        assert_eq!(
            detect_rat_arith_sort(&Sort::Real, Some(&rat)),
            ArithSort::Rat
        );
        assert_eq!(detect_rat_arith_sort(&Sort::Int, None), ArithSort::Int);
        assert_eq!(detect_rat_arith_sort(&Sort::Real, None), ArithSort::Real);
    }

    #[test]
    fn test_rat_smt_mapping_prefers_registered_rat_fvars() {
        let mut mapping = RatSmtMapping::default();
        let rat_id = FVarId::new(10);
        let real_id = FVarId::new(11);

        mapping.register_rat_fvar(rat_id);

        assert!(mapping.is_rat_fvar(rat_id));
        assert!(!mapping.is_rat_fvar(real_id));
        assert_eq!(
            mapping.arith_sort_for_fvar(rat_id, &Sort::Real),
            ArithSort::Rat
        );
        assert_eq!(
            mapping.arith_sort_for_fvar(real_id, &Sort::Real),
            ArithSort::Real
        );
    }
}
