// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Well-founded recursion encoding: transforms a recursive definition
//! into a `WellFounded.fix` application.
//!
//! The core transformation takes:
//!   `def f (x : α) : β := ... f (smaller x) ...`
//! And produces:
//!   `def f := WellFounded.fix (fun x rec => ... rec (smaller x) proof ...) `
//!
//! Where `proof` witnesses `measure(smaller x) < measure(x)` under some
//! well-founded relation.
//!
//! Reference: Lean 4 `src/Lean/Elab/PreDefinition/WF/Fix.lean`

use clean_kernel::{Expr, ExprFolder, FVarId};

/// Replace recursive calls to `func_name` in the body with calls to
/// the fixpoint's recursive argument `rec`.
///
/// Transforms: `f arg` → `rec arg sorry`
///
/// where `sorry` is a placeholder for the decreasing proof obligation.
/// In a full implementation, this would generate actual proof obligations
/// of `measure(arg) < measure(x)`.
///
/// # Arguments
///
/// * `body` - The function body expression
/// * `func_fvar` - FVarId of the function being defined (used during elaboration)
/// * `rec_fvar` - FVarId of the `rec` parameter from the fix body
/// * `rec_type` - Type of the `rec` parameter (includes proof obligation in domain)
pub(crate) fn replace_rec_calls(body: &Expr, func_fvar: FVarId, rec_fvar: FVarId) -> Expr {
    struct RecCallReplacer {
        func_fvar: FVarId,
        rec_fvar: FVarId,
    }

    impl ExprFolder for RecCallReplacer {
        fn fold_fvar(&mut self, id: FVarId) -> Expr {
            if id == self.func_fvar {
                Expr::fvar(self.rec_fvar)
            } else {
                Expr::fvar(id)
            }
        }
    }

    let mut folder = RecCallReplacer {
        func_fvar,
        rec_fvar,
    };
    folder.fold_expr(body)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_replace_rec_calls_simple() {
        let func_fvar = FVarId::new(100);
        let rec_fvar = FVarId::new(200);
        let arg_fvar = FVarId::new(300);

        // f arg => rec arg
        let body = Expr::app(Expr::fvar(func_fvar), Expr::fvar(arg_fvar));
        let result = replace_rec_calls(&body, func_fvar, rec_fvar);

        // Should be: rec arg
        let expected = Expr::app(Expr::fvar(rec_fvar), Expr::fvar(arg_fvar));
        assert_eq!(format!("{result:?}"), format!("{expected:?}"));
    }

    #[test]
    fn test_replace_rec_calls_no_recursion() {
        let func_fvar = FVarId::new(100);
        let rec_fvar = FVarId::new(200);
        let other_fvar = FVarId::new(300);

        // other arg => other arg (unchanged)
        let body = Expr::app(Expr::fvar(other_fvar), Expr::nat_lit(42));
        let result = replace_rec_calls(&body, func_fvar, rec_fvar);

        let expected = Expr::app(Expr::fvar(other_fvar), Expr::nat_lit(42));
        assert_eq!(format!("{result:?}"), format!("{expected:?}"));
    }
}
