// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared helpers for handwritten `init_*` routines.
//!
//! These helpers keep repeated declaration-registration patterns out of the
//! mixed overlay modules so those modules can focus on dependencies and type
//! construction.

use super::{Declaration, EnvError, Environment};
use crate::expr::Expr;
use crate::level::Level;
use crate::name::Name;

/// Shared universe parameter setup for handwritten `init_*` routines.
#[derive(Clone, Debug)]
pub(crate) struct InitLevelParam {
    pub(crate) name: Name,
    pub(crate) level: Level,
}

impl InitLevelParam {
    pub(crate) fn new(name: &str) -> Self {
        let name = Name::from_string(name);
        let level = Level::param(name.clone());
        Self { name, level }
    }

    pub(crate) fn sort(&self) -> Expr {
        Expr::sort(self.level.clone())
    }

    pub(crate) fn type_(&self) -> Expr {
        Expr::sort(Level::succ(self.level.clone()))
    }
}

pub(crate) fn prop_expr() -> Expr {
    Expr::sort(Level::zero())
}

pub(crate) fn type0_expr() -> Expr {
    Expr::sort(Level::succ(Level::zero()))
}

impl Environment {
    /// Register a batch of declarations emitted by an init template builder.
    pub(crate) fn add_init_decls<I>(&mut self, decls: I) -> Result<(), EnvError>
    where
        I: IntoIterator<Item = Declaration>,
    {
        for decl in decls {
            self.add_decl(decl)?;
        }
        Ok(())
    }

    /// Register a batch of axiom stubs that all share the same type.
    pub(crate) fn add_init_axioms(
        &mut self,
        names: &[&str],
        level_params: &[Name],
        type_: &Expr,
    ) -> Result<(), EnvError> {
        for name in names {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string(name),
                level_params: level_params.to_vec(),
                type_: type_.clone(),
            })?;
        }
        Ok(())
    }

    /// Register a batch of same-typed axiom stubs when they are not already present.
    pub(crate) fn add_init_axioms_if_absent(
        &mut self,
        names: &[&str],
        level_params: &[Name],
        type_: &Expr,
    ) -> Result<(), EnvError> {
        for name in names {
            self.add_init_axiom_if_absent(name, level_params, || type_.clone())?;
        }
        Ok(())
    }

    /// Lazily register an axiom stub only when the constant is absent.
    pub(crate) fn add_init_axiom_if_absent<F>(
        &mut self,
        name: &str,
        level_params: &[Name],
        mk_type: F,
    ) -> Result<bool, EnvError>
    where
        F: FnOnce() -> Expr,
    {
        let name = Name::from_string(name);
        if self.get_const(&name).is_some() {
            return Ok(false);
        }

        self.add_decl(Declaration::Axiom {
            name,
            level_params: level_params.to_vec(),
            type_: mk_type(),
        })?;
        Ok(true)
    }
}
