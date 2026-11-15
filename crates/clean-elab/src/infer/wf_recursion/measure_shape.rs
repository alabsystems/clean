// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Is a `termination_by` measure a **SUM**?
//!
//! [`measure_params`] answers *which* parameters a measure mentions. This
//! module answers the other half of the phase-3 (2026-08-25) widening: once a
//! measure mentions MORE than one parameter, is it in the class the lowering
//! admits?
//!
//! # What the class is, and what it is not
//!
//! The course-of-values encoding in [`super::sum_measure`] is **uniform**: it
//! works for any `Nat`-valued measure over the parameters, because the fix
//! runs on the measure's VALUE and the parameters ride in the motive. So this
//! predicate is NOT a soundness boundary and not a limit of the encoding — it
//! is a deliberate scope limit on what the phase-3 increment TURNS ON, chosen
//! so the widening is one measurable class rather than "everything at once".
//!
//! The class is: **the measure's head is `Nat` addition** — `a + b`,
//! `a + b + 1`, `xs.length + ys.length`. That is exactly what a two-branch
//! subtractive Euclid needs, and it is the smallest widening that is useful.
//!
//! Per v7/D2 the boundary is a statement of where we are, never a design: a
//! measure outside it is refused by [`super::elab_wf_recursion_core`] with a
//! diagnostic that says sums ARE lowered and names restating-as-a-sum as an
//! option (v7/D3). Widening this predicate later is a one-line, strictly
//! additive change that turns on lowering code which already exists.
//!
//! # Two spellings, two levels
//!
//! * [`is_surface_nat_sum`] reads the SURFACE measure and feeds the ROUTING
//!   decision in `elab_decl_value` (which lowering is attempted). It carries
//!   no proof authority whatsoever.
//! * [`is_nat_sum`] reads the ELABORATED measure and feeds the LOWERING gate.
//!   It accepts both spellings the elaborator leaves behind for `+` — the raw
//!   `Nat.add`, and the `HAdd.hAdd` notation — for the same reason
//!   `decreasing::mod_numerator` does.
//!
//! [`measure_params`]: super::measure_params

use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprKind, FVarId};
use clean_parser::SurfaceExpr;

use super::ElabCtx;

/// Strip `MData` wrappers so a spine match sees the term itself.
fn strip_mdata(mut e: &Expr) -> &Expr {
    while let ExprKind::MData(_, inner) = e.kind() {
        e = inner;
    }
    e
}

/// The two summands of a `Nat` addition, in either spelling the elaborator
/// produces (`Nat.add a b`, or `@HAdd.hAdd α β γ inst a b`). `None` for any
/// other head, so a caller keyed on this never fires against a term it did not
/// recognise.
///
/// Only the HEAD is inspected. `a + b * c` is a sum (of `a` and `b * c`);
/// `a * b` is not. The summands are unconstrained because the encoding does
/// not constrain them — see the module docs for why this is a scope limit and
/// not a soundness one.
pub(super) fn split_nat_add(e: &Expr) -> Option<(Expr, Expr)> {
    let e = strip_mdata(e);
    let head = e.get_app_fn();
    let args = e.get_app_args();
    let ExprKind::Const(name, _) = strip_mdata(head).kind() else {
        return None;
    };
    if *name == Name::from_string("Nat.add") && args.len() == 2 {
        return Some((Expr::clone(args[0]), Expr::clone(args[1])));
    }
    if *name == Name::from_string("HAdd.hAdd") && args.len() == 6 {
        return Some((Expr::clone(args[4]), Expr::clone(args[5])));
    }
    None
}

/// Is `measure`'s head `Nat` addition? See [`split_nat_add`].
pub(super) fn is_nat_sum(measure: &Expr) -> bool {
    split_nat_add(measure).is_some()
}

/// Strip surface parentheses.
fn strip_parens(mut e: &SurfaceExpr) -> &SurfaceExpr {
    while let SurfaceExpr::Paren(_, inner) = e {
        e = inner;
    }
    e
}

/// The surface counterpart of [`is_nat_sum`]: `a + b` parses as
/// `App(Ident("HAdd.hAdd"), [a, b])` (`clean-parser`'s
/// `grammar::expr_operators`), so that is what routing keys on.
///
/// **Routing only — no proof authority.** A wrong answer here costs a
/// diagnostic. The lowering re-derives everything from the ELABORATED measure
/// ([`is_nat_sum`] plus `contains_fvar` over real `FVar`s), requires the
/// measure to be `Nat`-valued, and discharges or refuses every decreasing
/// obligation itself.
pub(crate) fn is_surface_nat_sum(measure: &SurfaceExpr) -> bool {
    match strip_parens(measure) {
        SurfaceExpr::App(_, f, args) => {
            args.len() == 2
                && matches!(strip_parens(f), SurfaceExpr::Ident(_, name) if name.name() == &Name::from_string("HAdd.hAdd"))
        }
        _ => false,
    }
}

impl ElabCtx<'_> {
    /// The measure evaluated at a call site's arguments:
    /// `measure[p₀ := a₀, …, pₙ₋₁ := aₙ₋₁]`, **simultaneously**.
    ///
    /// Simultaneity is load-bearing and is why this is not a fold of
    /// `subst_fvar`. A sequential substitution of `a + b` at the swapped
    /// arguments `(b, a)` produces `a + a`: the first step rewrites `a` to
    /// `b`, and the second then rewrites BOTH `b`s. Routing the parameters
    /// through fresh placeholders first makes the two phases disjoint, so the
    /// answer is `b + a`.
    ///
    /// A wrong measure here would be a wrong OBLIGATION — the one thing that
    /// must never be quietly wrong — so it is pinned by
    /// `tests::test_measure_at_swapped_arguments_is_simultaneous`.
    ///
    /// `args` is expected to cover every parameter (the caller checks the call
    /// spine's arity first). If it ever did not, the short parameters keep
    /// their placeholder `FVar`, which is in no local context — so the goal
    /// fails inference, no candidate is accepted, and the definition is
    /// refused. Fail-closed, not silently mis-substituted.
    pub(super) fn measure_at_args(
        &mut self,
        measure: &Expr,
        params: &[(FVarId, Expr)],
        args: &[Expr],
    ) -> Expr {
        let placeholders: Vec<FVarId> = params.iter().map(|_| self.fresh_fvar()).collect();
        let mut out = measure.clone();
        for ((param, _), placeholder) in params.iter().zip(&placeholders) {
            out = out.subst_fvar(*param, &Expr::fvar(*placeholder));
        }
        for (placeholder, arg) in placeholders.iter().zip(args) {
            out = out.subst_fvar(*placeholder, arg);
        }
        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_parser::parse_file;

    fn nat_add(x: Expr, y: Expr) -> Expr {
        Expr::apps(Expr::const_(Name::from_string("Nat.add"), vec![]), [x, y])
    }

    #[test]
    fn test_nat_add_spelling_is_a_sum() {
        assert!(is_nat_sum(&nat_add(Expr::nat_lit(1), Expr::nat_lit(2))));
    }

    #[test]
    fn test_hadd_notation_spelling_is_a_sum() {
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let hadd = Expr::apps(
            Expr::const_(Name::from_string("HAdd.hAdd"), vec![]),
            [
                nat.clone(),
                nat.clone(),
                nat,
                Expr::const_(Name::from_string("instHAdd"), vec![]),
                Expr::nat_lit(1),
                Expr::nat_lit(2),
            ],
        );
        assert!(is_nat_sum(&hadd));
    }

    #[test]
    fn test_a_product_is_not_a_sum() {
        let mul = Expr::apps(
            Expr::const_(Name::from_string("Nat.mul"), vec![]),
            [Expr::nat_lit(1), Expr::nat_lit(2)],
        );
        assert!(!is_nat_sum(&mul));
        assert!(!is_nat_sum(&Expr::nat_lit(5)));
    }

    /// A partially-applied `Nat.add` is NOT a measure — refuse it rather than
    /// let arity slip.
    #[test]
    fn test_a_partially_applied_add_is_not_a_sum() {
        let partial = Expr::app(
            Expr::const_(Name::from_string("Nat.add"), vec![]),
            Expr::nat_lit(1),
        );
        assert!(!is_nat_sum(&partial));
    }

    fn surface_measure(source: &str) -> SurfaceExpr {
        let decls = parse_file(source).expect("fixture should parse");
        let clean_parser::SurfaceDecl::Def { termination, .. } = &decls[0] else {
            panic!("fixture must be a `def`")
        };
        *termination
            .termination_by
            .as_ref()
            .and_then(|tb| tb.measure.clone())
            .expect("fixture must carry a `termination_by` measure")
    }

    const HEAD: &str = "def f (a b : Nat) : Nat := a\ntermination_by ";

    #[test]
    fn test_surface_sum_is_recognised_through_parens() {
        assert!(is_surface_nat_sum(&surface_measure(&format!(
            "{HEAD}a + b"
        ))));
        assert!(is_surface_nat_sum(&surface_measure(&format!(
            "{HEAD}(a + b)"
        ))));
        assert!(is_surface_nat_sum(&surface_measure(&format!(
            "{HEAD}a + b + 1"
        ))));
    }

    /// **THE SIMULTANEITY PIN.** `a + b` at the SWAPPED arguments `(b, a)` is
    /// `b + a`. A sequential `subst_fvar` fold answers `a + a` — a wrong
    /// obligation, silently. This is the one thing in the module that a
    /// reader cannot check by eye.
    #[test]
    fn test_measure_at_swapped_arguments_is_simultaneous() {
        let env = clean_kernel::Environment::with_prelude();
        let mut ctx = ElabCtx::new(&env);
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let (a, b) = (FVarId::new(9001), FVarId::new(9002));
        let measure = nat_add(Expr::fvar(a), Expr::fvar(b));
        let params = [(a, nat.clone()), (b, nat)];

        let swapped = ctx.measure_at_args(&measure, &params, &[Expr::fvar(b), Expr::fvar(a)]);
        assert_eq!(
            swapped,
            nat_add(Expr::fvar(b), Expr::fvar(a)),
            "a swap must produce `b + a`, not the sequential-substitution `a + a`"
        );

        // The ordinary, non-aliasing case still behaves.
        let sub = Expr::apps(
            Expr::const_(Name::from_string("Nat.sub"), vec![]),
            [Expr::fvar(a), Expr::fvar(b)],
        );
        let stepped = ctx.measure_at_args(&measure, &params, &[sub.clone(), Expr::fvar(b)]);
        assert_eq!(stepped, nat_add(sub, Expr::fvar(b)));
    }

    #[test]
    fn test_surface_non_sums_are_refused() {
        assert!(!is_surface_nat_sum(&surface_measure(&format!(
            "{HEAD}b - a"
        ))));
        assert!(!is_surface_nat_sum(&surface_measure(&format!(
            "{HEAD}a * b"
        ))));
        assert!(!is_surface_nat_sum(&surface_measure(&format!("{HEAD}b"))));
    }
}
