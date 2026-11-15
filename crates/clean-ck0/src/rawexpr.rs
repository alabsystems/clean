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
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
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
#[derive(Clone, Debug)]
pub enum RawExpr {
    /// An untrusted shared node; validation checks it at each binder depth.
    Shared(std::sync::Arc<RawExpr>),
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

/// Transform-local keys retain the source allocation, preventing address reuse.
#[cfg(feature = "export")]
pub(crate) type RawMemo =
    std::collections::HashMap<*const RawExpr, (std::sync::Arc<RawExpr>, std::sync::Arc<RawExpr>)>;

#[cfg(feature = "export")]
pub(crate) fn map_shared<E>(
    raw: &mut RawExpr,
    memo: &mut RawMemo,
    transform: impl FnOnce(&mut RawExpr, &mut RawMemo) -> Result<(), E>,
) -> Result<(), E> {
    let RawExpr::Shared(original) = raw else {
        return transform(raw, memo);
    };
    let id = std::ptr::from_ref(original.unshared());
    if let Some((_, image)) = memo.get(&id) {
        *raw = RawExpr::Shared(image.clone());
        return Ok(());
    }
    let original = original.clone();
    let mut image = original.unshared().clone();
    transform(&mut image, memo)?;
    let image = match image {
        RawExpr::Shared(node) => node,
        other => std::sync::Arc::new(other),
    };
    memo.insert(id, (original, image.clone()));
    *raw = RawExpr::Shared(image);
    Ok(())
}

impl RawExpr {
    pub(crate) fn unshared(&self) -> &Self {
        let mut node = self;
        while let Self::Shared(child) = node {
            node = child;
        }
        node
    }
}
impl PartialEq for RawExpr {
    fn eq(&self, other: &Self) -> bool {
        let mut stack = vec![(self, other)];
        let mut seen = std::collections::HashSet::new();
        while let Some((a, b)) = stack.pop() {
            let (a, b) = (a.unshared(), b.unshared());
            if std::ptr::eq(a, b) || !seen.insert((std::ptr::from_ref(a), std::ptr::from_ref(b))) {
                continue;
            }
            match (a, b) {
                (Self::BVar(a), Self::BVar(b)) if a == b => {}
                (Self::Sort(a), Self::Sort(b)) if a == b => {}
                (Self::Const(a, x), Self::Const(b, y)) if a == b && x == y => {}
                (Self::Elim(a, m, x), Self::Elim(b, n, y)) if a == b && m == n && x == y => {}
                (Self::Lit(a), Self::Lit(b)) if a == b => {}
                (Self::App(a, b), Self::App(c, d)) => {
                    stack.extend([(a.as_ref(), c.as_ref()), (b.as_ref(), d.as_ref())])
                }
                (Self::Pi(i, a, b), Self::Pi(j, c, d))
                | (Self::Lam(i, a, b), Self::Lam(j, c, d))
                    if i == j =>
                {
                    stack.extend([(a.as_ref(), c.as_ref()), (b.as_ref(), d.as_ref())])
                }
                (Self::Let(a, b, c), Self::Let(d, e, f)) => stack.extend([
                    (a.as_ref(), d.as_ref()),
                    (b.as_ref(), e.as_ref()),
                    (c.as_ref(), f.as_ref()),
                ]),
                (Self::Proj(n, i, a), Self::Proj(m, j, b)) if n == m && i == j => {
                    stack.push((a, b))
                }
                _ => return false,
            }
        }
        true
    }
}
impl Eq for RawExpr {}
