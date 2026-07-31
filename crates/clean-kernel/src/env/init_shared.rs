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
use crate::name::Name;

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
