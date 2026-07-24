// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The **untrusted** boundary IR — the only thing that crosses into the kernel
//! (design §4.1). Parsers, `.olean` readers and cert producers emit this; it is
//! fully public and carries *no* invariants. The sole way to turn a [`RawExpr`]
//! into a trusted [`crate::Term`] is [`crate::Term::validate`], which re-checks
//! every property from scratch.
//!
//! Note the asymmetry with the trusted side: a `RawExpr::Const` *does* carry a
//! free `Vec<RawLevel>`, and a `RawExpr::Elim` *does* let the producer name an
//! inductive + levels — but neither can be turned into a `Term` except through
//! validation, where the level vector is checked against the declared arity
//! (for `Const`) or *discarded and re-derived* (for `Elim`). The producer can
//! ask; only the kernel decides.

use crate::bignat::BigNat;
use crate::name::Name;

/// Binder annotation, mirrored from the surface language. Soundness-inert.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Default)]
pub enum BinderInfo {
    /// `(x : T)`
    #[default]
    Default,
    /// `{x : T}`
    Implicit,
    /// `{{x : T}}`
    StrictImplicit,
    /// `[x : T]`
    InstImplicit,
}

/// Untrusted universe level syntax. `Param` is positional, as on the trusted
/// side, but here the index is unchecked until validation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RawLevel {
    /// `0`
    Zero,
    /// `l + 1`
    Succ(Box<RawLevel>),
    /// `max(l1, l2)`
    Max(Box<RawLevel>, Box<RawLevel>),
    /// `imax(l1, l2)`
    IMax(Box<RawLevel>, Box<RawLevel>),
    /// positional universe parameter (unchecked index)
    Param(u32),
}

/// Untrusted literal syntax.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RawLit {
    /// arbitrary-precision natural-number literal
    Nat(BigNat),
    /// string literal
    Str(String),
}

/// Untrusted term syntax. This is the boundary type (design §4.1).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RawExpr {
    /// de Bruijn bound variable.
    BVar(u32),
    /// `Sort l`.
    Sort(RawLevel),
    /// A constant reference with a producer-supplied level vector (checked
    /// against the declaration arity at validation).
    Const(Name, Vec<RawLevel>),
    /// An eliminator reference: the inductive name, the motive level, and the
    /// substitution for the inductive's own level params. At validation the full
    /// level vector is *derived* — the producer never authors it.
    Elim(Name, RawLevel, Vec<RawLevel>),
    /// Application `f a`.
    App(Box<RawExpr>, Box<RawExpr>),
    /// Lambda `λ (x : ty). body`.
    Lam(BinderInfo, Box<RawExpr>, Box<RawExpr>),
    /// Pi `(x : ty) → body`.
    Pi(BinderInfo, Box<RawExpr>, Box<RawExpr>),
    /// `let _ : ty := val; body`.
    Let(Box<RawExpr>, Box<RawExpr>, Box<RawExpr>),
    /// A literal.
    Lit(RawLit),
    /// Structure projection `e.i` of structure `name`.
    Proj(Name, u32, Box<RawExpr>),
}
