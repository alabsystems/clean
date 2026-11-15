// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Small term-building kit for the monad prelude (`data_monad_classes.rs`,
//! `data_monad_transformers.rs`).
//!
//! [`Tele`] is a binder telescope over temporary free variables: every
//! [`Tele::bind`] allocates a fresh variable, and [`Tele::pi`] / [`Tele::lam`]
//! close the whole telescope around a body — the same binder-safety
//! `EnvDeclBuilder` gives, with one shared id counter per root so a child
//! telescope opened INSIDE a body can never reuse an id its parent allocates
//! afterwards.
//!
//! [`MonadInst`] spells the operations of a monad through a `Monad m`
//! instance term exactly as Lean's elaborator does:
//! `@Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst)) α a`
//! and `@Bind.bind m (@Monad.toBind m inst) α β x f`.

use std::cell::Cell;
use std::rc::Rc;

use crate::expr::{BinderInfo, Expr, FVarId};
use crate::level::Level;
use crate::name::Name;

/// Base of the temporary free-variable ids; disjoint from both the type
/// checker's (counting up from 0) and `EnvDeclBuilder`'s (`0x8000…`).
const TELE_FVAR_BASE: u64 = 0x9000_0000_0000_0000;

/// A binder telescope over temporary free variables.
pub(crate) struct Tele {
    next: Rc<Cell<u64>>,
    binders: Vec<(FVarId, BinderInfo, Expr)>,
    root: bool,
}

impl Tele {
    /// A root telescope; its closed terms must mention no free variable.
    pub(crate) fn new() -> Self {
        Self {
            next: Rc::new(Cell::new(TELE_FVAR_BASE)),
            binders: Vec::new(),
            root: true,
        }
    }

    /// A telescope nested inside `parent`'s body. It shares the parent's id
    /// counter, and its closed terms may still mention the parent's
    /// variables.
    pub(crate) fn child(parent: &Tele) -> Self {
        Self {
            next: Rc::clone(&parent.next),
            binders: Vec::new(),
            root: false,
        }
    }

    /// Open a binder of type `ty`; the returned variable stands for it.
    pub(crate) fn bind(&mut self, bi: BinderInfo, ty: Expr) -> Expr {
        let id = FVarId::new(self.next.get());
        self.next.set(self.next.get() + 1);
        self.binders.push((id, bi, ty));
        Expr::fvar(id)
    }

    /// An explicit binder.
    pub(crate) fn arg(&mut self, ty: Expr) -> Expr {
        self.bind(BinderInfo::Default, ty)
    }

    /// An implicit binder.
    pub(crate) fn imp(&mut self, ty: Expr) -> Expr {
        self.bind(BinderInfo::Implicit, ty)
    }

    /// An instance-implicit binder.
    pub(crate) fn inst(&mut self, ty: Expr) -> Expr {
        self.bind(BinderInfo::InstImplicit, ty)
    }

    fn close(&self, body: Expr, pi: bool) -> Expr {
        let mut r = body;
        for (id, bi, ty) in self.binders.iter().rev() {
            let closed = r.abstract_fvar(*id);
            r = if pi {
                Expr::pi(*bi, ty.clone(), closed)
            } else {
                Expr::lam(*bi, ty.clone(), closed)
            };
        }
        if self.root {
            assert!(
                !r.has_fvar_quick(),
                "monad_term::Tele: a root telescope closed over a term that still \
                 mentions a free variable"
            );
        }
        r
    }

    /// `Π <telescope>, body`.
    pub(crate) fn pi(&self, body: Expr) -> Expr {
        self.close(body, true)
    }

    /// `λ <telescope>, body`.
    pub(crate) fn lam(&self, body: Expr) -> Expr {
        self.close(body, false)
    }
}

/// `c.{levels}`.
pub(crate) fn cst(name: &str, levels: &[Level]) -> Expr {
    Expr::const_(Name::from_string(name), levels.to_vec())
}

/// `Type l` (= `Sort (l+1)`).
pub(crate) fn type_at(l: &Level) -> Expr {
    Expr::sort(Level::succ(l.clone()))
}

/// `Type u → Type v`, the kind of a monad.
pub(crate) fn monad_kind(u: &Level, v: &Level) -> Expr {
    Expr::pi(BinderInfo::Default, type_at(u), type_at(v))
}

/// `Level::param(name)`.
pub(crate) fn lparam(name: &str) -> Level {
    Level::param(Name::from_string(name))
}

/// A monad `m : Type u → Type v` together with a `Monad m` instance term.
#[derive(Clone)]
pub(crate) struct MonadInst {
    pub(crate) u: Level,
    pub(crate) v: Level,
    pub(crate) m: Expr,
    pub(crate) inst: Expr,
}

impl MonadInst {
    fn uv(&self) -> [Level; 2] {
        [self.u.clone(), self.v.clone()]
    }

    /// `@Applicative.toPure m (@Monad.toApplicative m inst) : Pure m`.
    pub(crate) fn pure_inst(&self) -> Expr {
        let app = Expr::apps(
            cst("Monad.toApplicative", &self.uv()),
            [self.m.clone(), self.inst.clone()],
        );
        Expr::apps(cst("Applicative.toPure", &self.uv()), [self.m.clone(), app])
    }

    /// `@Monad.toBind m inst : Bind m`.
    pub(crate) fn bind_inst(&self) -> Expr {
        Expr::apps(
            cst("Monad.toBind", &self.uv()),
            [self.m.clone(), self.inst.clone()],
        )
    }

    /// `@Pure.pure m <pure inst> α a`.
    pub(crate) fn pure(&self, alpha: Expr, a: Expr) -> Expr {
        Expr::apps(
            cst("Pure.pure", &self.uv()),
            [self.m.clone(), self.pure_inst(), alpha, a],
        )
    }

    /// `@Bind.bind m <bind inst> α β x f`.
    pub(crate) fn bind(&self, alpha: Expr, beta: Expr, x: Expr, f: Expr) -> Expr {
        Expr::apps(
            cst("Bind.bind", &self.uv()),
            [self.m.clone(), self.bind_inst(), alpha, beta, x, f],
        )
    }

    /// `m α`.
    pub(crate) fn at(&self, alpha: Expr) -> Expr {
        Expr::app(self.m.clone(), alpha)
    }
}
