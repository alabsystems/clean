// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared equality proof term builders.
//!
//! Pure Expr-building free functions for `Eq.refl`, `Eq.symm`, `Eq.trans`,
//! `Eq.subst`, `congrArg`, and `congr`. Each caller provides the universe
//! level(s) via its preferred method (TypeChecker, heuristic, or pre-computed).
//!
//! Consolidates identical Expr construction from:
//! - `bridge/proof_terms.rs` (SmtBridge methods)
//! - `superposition_reconstruction/proof_helpers.rs`
//! - `ay_backend/proof_reconstruct/expr_builders.rs`

use clean_kernel::name::Name;
use clean_kernel::{Expr, Level};

/// Build `@Eq.refl.{u} α a : @Eq.{u} α a a`.
pub(crate) fn mk_eq_refl(u: &Level, ty: &Expr, val: &Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Eq.refl"), vec![u.clone()]),
            ty.clone(),
        ),
        val.clone(),
    )
}

/// Build `@Eq.symm.{u} α a b h : @Eq.{u} α b a`.
pub(crate) fn mk_eq_symm(u: &Level, ty: &Expr, a: &Expr, b: &Expr, h: &Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("Eq.symm"), vec![u.clone()]),
                    ty.clone(),
                ),
                a.clone(),
            ),
            b.clone(),
        ),
        h.clone(),
    )
}

/// Build `@Eq.trans.{u} α a b c h₁ h₂ : @Eq.{u} α a c`.
pub(crate) fn mk_eq_trans(
    u: &Level,
    ty: &Expr,
    a: &Expr,
    b: &Expr,
    c: &Expr,
    h1: &Expr,
    h2: &Expr,
) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::const_(Name::from_string("Eq.trans"), vec![u.clone()]),
                            ty.clone(),
                        ),
                        a.clone(),
                    ),
                    b.clone(),
                ),
                c.clone(),
            ),
            h1.clone(),
        ),
        h2.clone(),
    )
}

/// Build `@congrArg.{u, v} α β a₁ a₂ f h : f a₁ = f a₂`.
///
/// `congrArg : {α : Sort u} → {β : Sort v} → {a₁ a₂ : α} → (f : α → β) → a₁ = a₂ → f a₁ = f a₂`
pub(crate) fn mk_congr_arg(
    u: &Level,
    v: &Level,
    alpha: &Expr,
    beta: &Expr,
    a1: &Expr,
    a2: &Expr,
    f: &Expr,
    h: &Expr,
) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::const_(Name::from_string("congrArg"), vec![u.clone(), v.clone()]),
                            alpha.clone(),
                        ),
                        beta.clone(),
                    ),
                    a1.clone(),
                ),
                a2.clone(),
            ),
            f.clone(),
        ),
        h.clone(),
    )
}

/// Build `@Eq.subst.{u} α motive a b h m : motive b`.
///
/// Clean kernel signature (1 universe param, motive codomain fixed to Prop):
/// `Eq.subst : {α : Sort u} → {motive : α → Prop} → {a b : α} → a = b → motive a → motive b`
pub(crate) fn mk_eq_subst(
    u: &Level,
    ty: &Expr,
    motive: &Expr,
    a: &Expr,
    b: &Expr,
    h: &Expr,
    m: &Expr,
) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::const_(Name::from_string("Eq.subst"), vec![u.clone()]),
                            ty.clone(),
                        ),
                        motive.clone(),
                    ),
                    a.clone(),
                ),
                b.clone(),
            ),
            h.clone(),
        ),
        m.clone(),
    )
}

/// Build `@Eq.mp.{u} α β h a : β`.
///
/// `Eq.mp : {α β : Sort u} → (α = β) → α → β`
/// Forward transport: given `h : α = β` and `a : α`, produces a value of type `β`.
/// For propositional use (α, β : Prop), pass `u = Level::zero()`.
pub(crate) fn mk_eq_mp(u: &Level, alpha: &Expr, beta: &Expr, h: &Expr, a: &Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("Eq.mp"), vec![u.clone()]),
                    alpha.clone(),
                ),
                beta.clone(),
            ),
            h.clone(),
        ),
        a.clone(),
    )
}

/// Build `@Eq.mpr.{u} α β h b : α`.
///
/// `Eq.mpr : {α β : Sort u} → (α = β) → β → α`
/// Backward transport: given `h : α = β` and `b : β`, produces a value of type `α`.
/// For propositional use (α, β : Prop), pass `u = Level::zero()`.
pub(crate) fn mk_eq_mpr(u: &Level, alpha: &Expr, beta: &Expr, h: &Expr, b: &Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("Eq.mpr"), vec![u.clone()]),
                    alpha.clone(),
                ),
                beta.clone(),
            ),
            h.clone(),
        ),
        b.clone(),
    )
}

/// Build `@congr.{u, v} α β f₁ f₂ a₁ a₂ hf ha : f₁ a₁ = f₂ a₂`.
///
/// `congr : {α : Sort u} → {β : Sort v} → {f₁ f₂ : α → β} → {a₁ a₂ : α}
///          → f₁ = f₂ → a₁ = a₂ → f₁ a₁ = f₂ a₂`
pub(crate) fn mk_congr(
    u: &Level,
    v: &Level,
    alpha: &Expr,
    beta: &Expr,
    f1: &Expr,
    f2: &Expr,
    a1: &Expr,
    a2: &Expr,
    hf: &Expr,
    ha: &Expr,
) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::app(
                                Expr::app(
                                    Expr::const_(
                                        Name::from_string("congr"),
                                        vec![u.clone(), v.clone()],
                                    ),
                                    alpha.clone(),
                                ),
                                beta.clone(),
                            ),
                            f1.clone(),
                        ),
                        f2.clone(),
                    ),
                    a1.clone(),
                ),
                a2.clone(),
            ),
            hf.clone(),
        ),
        ha.clone(),
    )
}
