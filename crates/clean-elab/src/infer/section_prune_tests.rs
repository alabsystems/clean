// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! [`super::prune_section_binders`] on hand-built telescopes. The end-to-end
//! behaviour (through `clean check`'s preprocess-then-elaborate loop) is pinned
//! in `tests_section_variable_inclusion.rs`.

use super::{prune_section_binders, PruneRule};
use clean_kernel::{BinderInfo, Expr, FVarId, Name};

fn c(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), Vec::new())
}

fn pi(info: BinderInfo, dom: Expr, body: Expr) -> Expr {
    Expr::pi(info, dom, body)
}

fn lam(info: BinderInfo, dom: Expr, body: Expr) -> Expr {
    Expr::lam(info, dom, body)
}

/// `{α : Type} {β : Type} (x : α) → α` / `fun {α} {β} (x : α) => x`, with `α`
/// and `β` the two section binders.
fn id_with_unused_beta() -> (Expr, Expr) {
    let ty = pi(
        BinderInfo::Implicit,
        Expr::type_(),
        pi(
            BinderInfo::Implicit,
            Expr::type_(),
            pi(BinderInfo::Default, Expr::bvar(1), Expr::bvar(2)),
        ),
    );
    let val = lam(
        BinderInfo::Implicit,
        Expr::type_(),
        lam(
            BinderInfo::Implicit,
            Expr::type_(),
            lam(BinderInfo::Default, Expr::bvar(1), Expr::bvar(0)),
        ),
    );
    (ty, val)
}

#[test]
fn test_prune_section_binders_used_rule_drops_an_unreferenced_binder() {
    let (ty, val) = id_with_unused_beta();
    let (ty, val, kept) =
        prune_section_binders(&ty, &val, 0, 2, &PruneRule::Used).expect("prunable");
    assert_eq!(kept, [true, false]);
    // `{α : Type} (x : α) → α`: `x`'s domain is now `BVar(0)`, the body `BVar(1)`.
    let want_ty = pi(
        BinderInfo::Implicit,
        Expr::type_(),
        pi(BinderInfo::Default, Expr::bvar(0), Expr::bvar(1)),
    );
    let want_val = lam(
        BinderInfo::Implicit,
        Expr::type_(),
        lam(BinderInfo::Default, Expr::bvar(0), Expr::bvar(0)),
    );
    assert_eq!(ty, want_ty);
    assert_eq!(val, want_val);
}

/// A binder only the VALUE mentions is kept: dropping it would leave a
/// dangling variable (Lean's `removeUnused` collects from values too).
#[test]
fn test_prune_section_binders_keeps_a_binder_only_the_value_uses() {
    // `(h : P) → Q` / `fun h => q h` — the value mentions `h`.
    let ty = pi(BinderInfo::Default, c("P"), c("Q"));
    let val = lam(
        BinderInfo::Default,
        c("P"),
        Expr::app(c("q"), Expr::bvar(0)),
    );
    let (_, _, kept) = prune_section_binders(&ty, &val, 0, 1, &PruneRule::Used).expect("prunable");
    assert_eq!(kept, [true]);
}

/// A binder the type of a KEPT binder mentions is kept (`addDependencies`),
/// even though nothing else does.
#[test]
fn test_prune_section_binders_keeps_what_a_kept_binder_type_needs() {
    // `{α : Type} (a : α) → Q` / `fun {α} a => q a`.
    let ty = pi(
        BinderInfo::Implicit,
        Expr::type_(),
        pi(BinderInfo::Default, Expr::bvar(0), c("Q")),
    );
    let val = lam(
        BinderInfo::Implicit,
        Expr::type_(),
        lam(
            BinderInfo::Default,
            Expr::bvar(0),
            Expr::app(c("q"), Expr::bvar(0)),
        ),
    );
    let (_, _, kept) = prune_section_binders(&ty, &val, 0, 2, &PruneRule::Used).expect("prunable");
    assert_eq!(kept, [true, true]);
}

/// The theorem rule keeps an `include`d binder the header never mentions, and
/// an instance-implicit binder whose type mentions only kept binders.
#[test]
fn test_prune_section_binders_header_rule_keeps_forced_and_instance_binders() {
    // `{α : Type} [inst : C α] {β : Type} (h : P) → Q`, section binders α,
    // inst, β, h; the proof is a constant. `h` is forced by `include`.
    let ty = pi(
        BinderInfo::Implicit,
        Expr::type_(),
        pi(
            BinderInfo::InstImplicit,
            Expr::app(c("C"), Expr::bvar(0)),
            pi(
                BinderInfo::Implicit,
                Expr::type_(),
                pi(
                    BinderInfo::Default,
                    c("P"),
                    Expr::app(c("Q"), Expr::bvar(3)),
                ),
            ),
        ),
    );
    let val = lam(
        BinderInfo::Implicit,
        Expr::type_(),
        lam(
            BinderInfo::InstImplicit,
            Expr::app(c("C"), Expr::bvar(0)),
            lam(
                BinderInfo::Implicit,
                Expr::type_(),
                lam(BinderInfo::Default, c("P"), c("proof")),
            ),
        ),
    );
    let rule = PruneRule::Header {
        forced: vec![false, false, false, true],
    };
    let (_, _, kept) = prune_section_binders(&ty, &val, 0, 4, &rule).expect("prunable");
    assert_eq!(
        kept,
        [true, true, false, true],
        "α (the statement), [C α] (instance over kept α), not β, h (included)"
    );
}

/// Binders outside the section prefix (the auto-bound implicits) are kept
/// and renumbered correctly.
#[test]
fn test_prune_section_binders_offset_keeps_outer_binders() {
    // `{γ : Type} {β : Type} (x : γ) → γ` with `γ` auto-bound (offset 1) and
    // `β` the single section binder.
    let ty = pi(
        BinderInfo::Implicit,
        Expr::type_(),
        pi(
            BinderInfo::Implicit,
            Expr::type_(),
            pi(BinderInfo::Default, Expr::bvar(1), Expr::bvar(2)),
        ),
    );
    let val = lam(
        BinderInfo::Implicit,
        Expr::type_(),
        lam(
            BinderInfo::Implicit,
            Expr::type_(),
            lam(BinderInfo::Default, Expr::bvar(1), Expr::bvar(0)),
        ),
    );
    let (ty, _, kept) = prune_section_binders(&ty, &val, 1, 1, &PruneRule::Used).expect("prunable");
    assert_eq!(kept, [false]);
    let want_ty = pi(
        BinderInfo::Implicit,
        Expr::type_(),
        pi(BinderInfo::Default, Expr::bvar(0), Expr::bvar(1)),
    );
    assert_eq!(ty, want_ty);
}

/// Anything the pruning cannot see through is left alone: a free variable
/// (or metavariable), or a telescope shorter than the request.
#[test]
fn test_prune_section_binders_refuses_free_variables_and_short_telescopes() {
    let (ty, _) = id_with_unused_beta();
    let with_fvar = lam(
        BinderInfo::Implicit,
        Expr::type_(),
        lam(
            BinderInfo::Implicit,
            Expr::type_(),
            Expr::fvar(FVarId::new(7)),
        ),
    );
    assert!(prune_section_binders(&ty, &with_fvar, 0, 2, &PruneRule::Used).is_none());
    let short = lam(BinderInfo::Implicit, Expr::type_(), Expr::bvar(0));
    assert!(prune_section_binders(&ty, &short, 0, 2, &PruneRule::Used).is_none());
}
