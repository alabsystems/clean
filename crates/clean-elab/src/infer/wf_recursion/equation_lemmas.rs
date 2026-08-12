// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Equation lemma generation for well-founded recursive definitions.
//!
//! After a recursive definition is compiled through `WellFounded.fix`, the
//! resulting definition unfolds differently from the user's original
//! recursive equations. Equation lemmas restore the expected rewriting
//! behaviour so that `simp` and `rw` can use the original equations.
//!
//! # Generated lemmas
//!
//! For a definition like:
//! ```lean
//! def f : Nat → Nat
//!   | 0 => 1
//!   | n + 1 => f n * 2
//! termination_by n => n
//! ```
//!
//! We generate:
//! - `f.eq_1 : f 0 = 1`
//! - `f.eq_2 : ∀ n, f (n + 1) = f n * 2`
//!
//! These lemmas are proved by `WellFounded.fix_eq` which states:
//!   `WellFounded.fix_eq : ∀ F x, fix F x = F x (fix F)`
//!
//! Reference: Lean 4 `src/Lean/Elab/PreDefinition/WF/Eqns.lean`

// Staged Lean4-parity scaffold with no caller yet (tests included): kept per the
// keep-and-annotate doctrine — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#![allow(dead_code)]
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, Level};

use super::ElabCtx;
use crate::ElabError;

/// A generated equation lemma.
#[derive(Debug, Clone)]
pub(crate) struct EquationLemma {
    /// Name of the lemma (e.g., `f.eq_1`).
    pub(crate) name: Name,
    /// Universe parameters for the lemma.
    pub(crate) universe_params: Vec<Name>,
    /// Type of the lemma (a propositional equality).
    pub(crate) ty: Expr,
    /// Proof term (typically using `WellFounded.fix_eq`).
    pub(crate) proof: Expr,
}

/// A single equation case extracted from the function body.
///
/// Represents one branch of the match/if-then-else that defines the
/// function's behaviour on a particular pattern.
#[derive(Debug, Clone)]
pub(crate) struct EquationCase {
    /// Pattern parameters (universally quantified variables in the lemma).
    /// E.g., for `| n + 1 => ...`, this would contain the binder for `n`.
    pub(crate) params: Vec<(String, Expr)>,
    /// The LHS argument expression (e.g., `0` or `Nat.succ n`).
    pub(crate) lhs_arg: Expr,
    /// The RHS expression (the branch body).
    pub(crate) rhs: Expr,
}

impl<'a> ElabCtx<'a> {
    /// Generate equation lemmas for a well-founded recursive definition.
    ///
    /// # Arguments
    ///
    /// * `func_name` - The fully qualified name of the defined function
    /// * `func_type` - The elaborated function type
    /// * `func_val` - The elaborated function value (WF.fix application)
    /// * `universe_params` - Universe parameters of the definition
    /// * `cases` - Equation cases extracted from the original definition
    ///
    /// # Returns
    ///
    /// A vector of equation lemmas, one per case.
    pub(crate) fn generate_equation_lemmas(
        &mut self,
        func_name: &Name,
        func_type: &Expr,
        func_val: &Expr,
        universe_params: &[Name],
        cases: &[EquationCase],
    ) -> Result<Vec<EquationLemma>, ElabError> {
        let mut lemmas = Vec::with_capacity(cases.len());

        for (i, case) in cases.iter().enumerate() {
            let lemma_name = Name::from_string(&format!("{}.eq_{}", func_name, i + 1,));

            let (lemma_ty, lemma_proof) =
                self.build_equation_lemma(func_name, func_type, func_val, universe_params, case)?;

            lemmas.push(EquationLemma {
                name: lemma_name,
                universe_params: universe_params.to_vec(),
                ty: lemma_ty,
                proof: lemma_proof,
            });
        }

        Ok(lemmas)
    }

    /// Build a single equation lemma: `f pattern_arg = rhs`.
    ///
    /// The lemma type is:
    ///   `∀ (params...), f (lhs_arg params) = rhs params`
    ///
    /// The proof uses `WellFounded.fix_eq` applied to the fixpoint body `F`
    /// and the argument, followed by definitional unfolding.
    fn build_equation_lemma(
        &mut self,
        func_name: &Name,
        func_type: &Expr,
        _func_val: &Expr,
        universe_params: &[Name],
        case: &EquationCase,
    ) -> Result<(Expr, Expr), ElabError> {
        // Build the function constant with universe params
        let func_levels: Vec<Level> = universe_params
            .iter()
            .map(|n| Level::param(n.clone()))
            .collect();
        let func_const = Expr::const_(func_name.clone(), func_levels);

        // LHS: f lhs_arg
        let lhs = Expr::app(func_const, case.lhs_arg.clone());

        // RHS: case.rhs
        let rhs = case.rhs.clone();

        // Build: @Eq ret_type lhs rhs
        let ret_type = self.extract_return_type(func_type, 1)?;
        let eq_type = build_eq_type(&ret_type, &lhs, &rhs);

        // Universally quantify over case parameters
        let mut lemma_ty = eq_type;
        for (name, ty) in case.params.iter().rev() {
            let fvar = self.push_local(name.clone(), ty.clone());
            let abstracted = lemma_ty.abstract_fvar(fvar);
            lemma_ty = Expr::pi(BinderInfo::Default, ty.clone(), abstracted);
            self.pop_local();
        }

        // Build proof using WellFounded.fix_eq
        // WellFounded.fix_eq : ∀ {α C rel wf} (F : ...) (x : α),
        //   WellFounded.fix wf F x = F x (WellFounded.fix wf F)
        //
        // For now, leave the proof as an unresolved metavariable. A full
        // implementation would instantiate fix_eq and apply congruence lemmas
        // for match/if branches; this path must not manufacture a sorry proof.
        let proof = self.fresh_meta(lemma_ty.clone());

        Ok((lemma_ty, proof))
    }
}

/// Build `@Eq α lhs rhs`.
pub(crate) fn build_eq_type(ty: &Expr, lhs: &Expr, rhs: &Expr) -> Expr {
    let eq = Expr::const_(
        Name::from_string("Eq"),
        vec![Level::param(Name::from_string("u"))],
    );
    Expr::apps(eq, [ty.clone(), lhs.clone(), rhs.clone()])
}

/// Build `@Eq.refl α a : @Eq α a a`.
pub(crate) fn build_eq_refl(ty: &Expr, val: &Expr) -> Expr {
    let refl = Expr::const_(
        Name::from_string("Eq.refl"),
        vec![Level::param(Name::from_string("u"))],
    );
    Expr::app(Expr::app(refl, ty.clone()), val.clone())
}

/// Extract equation cases from a match expression body.
///
/// Given a function body that is a `match` on the first argument,
/// extract each arm as an `EquationCase`.
///
/// This is a simplified extractor that handles:
/// - Direct match expressions
/// - If-then-else (desugared as match on Bool)
///
/// More complex patterns (nested matches, let bindings around matches)
/// require the full Lean 4 equation compiler, which is not yet implemented.
pub(crate) fn extract_equation_cases(_body: &Expr) -> Vec<EquationCase> {
    // For now, return an empty list — equation case extraction from
    // the elaborated expression tree is complex and requires matching
    // against the match compiler's output format.
    //
    // A full implementation would:
    // 1. Detect if body is a `Expr.mdata` with match metadata
    // 2. Extract the discriminant and branches
    // 3. For each branch, extract the pattern and body
    // 4. Build EquationCase for each
    //
    // This is deferred to a follow-up since the WF encoding itself
    // is the critical path; equation lemmas are a convenience feature.
    Vec::new()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_build_eq_type() {
        let nat = Expr::const_str("Nat");
        let zero = Expr::nat_lit(0);
        let one = Expr::nat_lit(1);

        let eq_ty = build_eq_type(&nat, &zero, &one);
        // Should be: @Eq Nat 0 1
        // Check it's an application chain
        match eq_ty.kind() {
            clean_kernel::ExprKind::App(_, _) => {} // good
            other => panic!("Expected App, got {:?}", other),
        }
    }

    #[test]
    fn test_build_eq_refl() {
        let nat = Expr::const_str("Nat");
        let zero = Expr::nat_lit(0);

        let refl = build_eq_refl(&nat, &zero);
        match refl.kind() {
            clean_kernel::ExprKind::App(_, _) => {} // good
            other => panic!("Expected App, got {:?}", other),
        }
    }

    #[test]
    fn test_extract_equation_cases_empty_for_now() {
        let body = Expr::const_str("some_body");
        let cases = extract_equation_cases(&body);
        assert!(
            cases.is_empty(),
            "Expected empty for unimplemented extractor"
        );
    }

    #[test]
    fn test_equation_lemma_name_format() {
        let func_name = Name::from_string("myFunc");
        let lemma_name = Name::from_string(&format!("{}.eq_1", func_name));
        assert_eq!(lemma_name, Name::from_string("myFunc.eq_1"));
    }
}
