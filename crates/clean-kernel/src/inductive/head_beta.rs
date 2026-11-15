// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The `whnf` calls of Lean's inductive admission, restricted to β.
//!
//! Lean's nested-inductive elimination instantiates a container's
//! parameters with `instantiate_rev`, which performs no β step
//! (`inductive.cpp` `instantiate_pi_params`, `instantiate.cpp`, v4.30.0-rc2).
//! A dependent container parameter instantiated with a lambda therefore
//! leaves a redex in the auxiliary constructor's field: `Sigma.mk`'s
//! `snd : β fst` becomes `snd : (fun _ => Nat → SGS) fst`. Lean stores
//! that field unreduced (in the auxiliary block, so in the generated
//! recursors' minor premises and rule right-hand sides, and in the block's
//! `isReflexive`, which tests `is_pi` on the unreduced domain) and reads
//! through it only where it calls `whnf`:
//!
//! - `check_positivity` (`inductive.cpp:393-408`) whnfs the field, then
//!   every body of its Pi spine;
//! - `is_rec_argument` (`:383-390`) and the induction hypotheses of
//!   `mk_rec_infos` (`:650-656`) whnf the field type and each body of its
//!   Pi spine.
//!
//! These helpers are those `whnf` calls with β only. β ⊆ `whnf`, so a field
//! whose block occurrence appears only after a δ step is still refused, as
//! before (the deliberate divergence in `strict.rs`); every field Lean reads
//! through by β is read the same way here. Nothing else is reduced: Pi
//! domains and application arguments are left as written, as `whnf` leaves
//! them.

use crate::expr::{Expr, ExprKind};

/// Contractions one call may perform. A field reached from a container
/// carries one redex per dependent parameter it applies; the bound exists
/// only because `strict.rs` runs before the constructor types are
/// type-checked, so a crafted non-normalizing field must not loop. Running
/// out returns the term as it then stands, which the caller reads
/// syntactically: an occurrence it still hides is refused (fail-closed).
const HEAD_BETA_FUEL: u32 = 4096;

/// Contract head β-redexes, `(fun x => b) a as…` to `b[x := a] as…`, until
/// the head is no longer a lambda applied to an argument (Lean's
/// `head_beta`). Within [`HEAD_BETA_FUEL`] contractions; the identity on a
/// term whose head is not a redex.
pub(crate) fn head_beta(e: &Expr) -> Expr {
    let mut current = e.clone();
    for _ in 0..HEAD_BETA_FUEL {
        match contract_head(&current) {
            Some(next) => current = next,
            None => return current,
        }
    }
    current
}

/// One head contraction, `(fun x => b) a as…` to `b[x := a] as…`, or `None`
/// when the head is not a lambda applied to an argument.
fn contract_head(e: &Expr) -> Option<Expr> {
    if !matches!(e.kind, ExprKind::App(..)) {
        return None;
    }
    let ExprKind::Lam(_, _, body) = &e.get_app_fn().kind else {
        return None;
    };
    let args = e.get_app_args();
    let (first, rest) = args.split_first()?;
    let contracted = body.instantiate(first);
    Some(
        rest.iter()
            .fold(contracted, |f, a| Expr::app(f, (*a).clone())),
    )
}

/// [`head_beta`] at the head of `e` and of every body of its Pi spine,
/// leaving each Pi domain as written: the shape `is_rec_argument` and the
/// induction-hypothesis loop of Lean's `mk_rec_infos` walk (`t = whnf(t)`,
/// then `t = whnf(instantiate(binding_body(t), x))` while `is_pi(t)`). On a
/// field with no redex along that spine it is the identity.
pub(crate) fn head_beta_spine(e: &Expr) -> Expr {
    let mut domains = Vec::new();
    let mut current = head_beta(e);
    while let ExprKind::Pi(bi, domain, body) = &current.kind {
        domains.push((*bi, (**domain).clone()));
        current = head_beta(body);
    }
    domains
        .into_iter()
        .rev()
        .fold(current, |body, (bi, domain)| Expr::pi(bi, domain, body))
}

#[cfg(test)]
mod tests {
    use super::{head_beta, head_beta_spine};
    use crate::expr::{BinderInfo, Expr};
    use crate::level::Level;
    use crate::name::Name;

    fn c(s: &str) -> Expr {
        Expr::const_(Name::from_string(s), Vec::<Level>::new())
    }

    fn arrow(a: Expr, b: Expr) -> Expr {
        Expr::pi(BinderInfo::Default, a, b)
    }

    fn lam(ty: Expr, body: Expr) -> Expr {
        Expr::lam(BinderInfo::Default, ty, body)
    }

    /// `(fun _ => Nat → T) k` is `Nat → T`; the domain `Nat` and anything
    /// past the head are left alone.
    #[test]
    fn test_head_beta_const_map_redex_contracts_to_its_body() {
        let redex = Expr::app(lam(c("Nat"), arrow(c("Nat"), c("T"))), c("k"));
        assert_eq!(head_beta(&redex), arrow(c("Nat"), c("T")));
    }

    /// The bound variable is substituted: `(fun n => Fin n → T) k` is
    /// `Fin k → T`.
    #[test]
    fn test_head_beta_dependent_redex_substitutes_the_argument() {
        let body = arrow(Expr::app(c("Fin"), Expr::bvar(0)), c("T"));
        let redex = Expr::app(lam(c("Nat"), body), c("k"));
        assert_eq!(
            head_beta(&redex),
            arrow(Expr::app(c("Fin"), c("k")), c("T"))
        );
    }

    /// A term whose head is not a lambda is returned unchanged, including a
    /// redex that is only an ARGUMENT (Lean's `whnf` does not reach it).
    #[test]
    fn test_head_beta_leaves_a_non_redex_head_and_its_arguments() {
        let inner = Expr::app(lam(c("Nat"), c("T")), c("k"));
        let e = Expr::app(c("F"), inner);
        assert_eq!(head_beta(&e), e);
        assert_eq!(head_beta(&c("T")), c("T"));
    }

    /// Surplus arguments are re-applied: `(fun x => x) f a` is `f a`.
    #[test]
    fn test_head_beta_reapplies_surplus_arguments() {
        let id = lam(c("Nat"), Expr::bvar(0));
        let e = Expr::app(Expr::app(id, c("f")), c("a"));
        assert_eq!(head_beta(&e), Expr::app(c("f"), c("a")));
    }

    /// A non-normalizing head stops at the budget instead of looping.
    #[test]
    fn test_head_beta_non_normalizing_head_stops_at_the_budget() {
        let delta = lam(c("U"), Expr::app(Expr::bvar(0), Expr::bvar(0)));
        let omega = Expr::app(delta.clone(), delta);
        assert_eq!(head_beta(&omega), omega);
    }

    /// The spine view reduces each body of the rightmost Pi spine but no
    /// domain: `(fun _ => (fun _ => Nat) T → (fun _ => T) k) k` keeps the
    /// domain redex and contracts the body.
    #[test]
    fn test_head_beta_spine_reduces_bodies_not_domains() {
        let domain = Expr::app(lam(c("U"), c("Nat")), c("T"));
        let body = Expr::app(lam(c("U"), c("T")), c("k"));
        let field = Expr::app(lam(c("Nat"), arrow(domain.clone(), body)), c("k"));
        assert_eq!(head_beta_spine(&field), arrow(domain, c("T")));
    }
}
