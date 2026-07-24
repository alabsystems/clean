// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Small helpers for emitting reducible definitions and theorems.

use super::{Declaration, EnvError, Environment, Expr, Name};

pub(super) fn reducible_def(
    name: &str,
    level_params: Vec<Name>,
    type_: Expr,
    value: Expr,
) -> Declaration {
    Declaration::Definition {
        name: Name::from_string(name),
        level_params,
        type_,
        value,
        is_reducible: true,
    }
}

pub(super) fn theorem(
    name: &str,
    level_params: Vec<Name>,
    type_: Expr,
    value: Expr,
) -> Declaration {
    Declaration::Theorem {
        name: Name::from_string(name),
        level_params,
        type_,
        value,
    }
}

pub(super) fn add_decl(env: &mut Environment, decl: Declaration) -> Result<(), EnvError> {
    let name = match &decl {
        Declaration::Definition { name, .. }
        | Declaration::Axiom { name, .. }
        | Declaration::Theorem { name, .. }
        | Declaration::Opaque { name, .. } => name,
    };
    // Idempotent on name. The kernel Eq surface (`init_eq`) is registered piece
    // by piece by the `core_eq` registrars; clean-verify's `Specification`
    // foundation surface registers its OWN `Eq` + `Eq.refl`/`symm`/`trans`/
    // `subst`/`cong` (without setting the kernel `eq_init` latch). When `init_eq`
    // then runs (e.g. via `init_rat`), the auxiliary registrars must ADD the
    // lemmas the foundation lacks (`congrArg`/`congrFun`/`congr`/`cast`/
    // `Eq.ndrec`/`Eq.mp`/…) while KEEPING the foundation's own already-present
    // decls — so we skip a decl whose name is already provided rather than
    // erroring `DuplicateName`. Sound by construction: the kernel re-type-checks
    // every downstream term, so a kept (foundation) decl that is incompatible
    // with what a later auxiliary needs surfaces as a type-check error in its
    // consumer, never as silent unsoundness. Used only by the `core_eq`
    // registrars.
    if env.get_const(name).is_some() {
        return Ok(());
    }
    env.add_decl(decl)
}

/// Apply a function expression to a sequence of arguments: `f a₁ a₂ … aₙ`.
pub(super) fn mk_apps(f: Expr, args: Vec<Expr>) -> Expr {
    args.into_iter().fold(f, Expr::app)
}
