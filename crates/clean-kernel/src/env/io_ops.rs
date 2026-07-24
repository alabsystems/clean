// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! IO operation axioms for the kernel environment.
//!
//! Registers axiomatic constants for standard Lean 4 IO operations so that
//! the evaluator/bridge can pattern-match on them at runtime. These are
//! opaque axioms — the kernel does not reduce them; the IO runtime executes
//! them.
//!
//! Requires [`Environment::init_io`] to have been called first (provides
//! `IO`, `IO.pure`, `IO.bind`).
//!
//! # Operations registered
//!
//! | Constant | Type |
//! |----------|------|
//! | `IO.println` | `String -> IO Unit` |
//! | `IO.print` | `String -> IO Unit` |
//! | `IO.eprintln` | `String -> IO Unit` |
//! | `IO.getLine` | `IO String` |
//! | `IO.FS.readFile` | `String -> IO String` |
//! | `IO.FS.writeFile` | `String -> String -> IO Unit` |
//! | `IO.getEnv` | `String -> IO String` |
//! | `IO.currentDir` | `IO String` |
//! | `IO.Process.exit` | `Nat -> IO Unit` |
//! | `IO.monoMsNow` | `IO Nat` |

use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize IO operation axioms. Idempotent.
    ///
    /// Registers constants for `IO.println`, `IO.print`, `IO.getLine`,
    /// `IO.FS.readFile`, `IO.FS.writeFile`, `IO.getEnv`, `IO.currentDir`,
    /// `IO.Process.exit`, `IO.monoMsNow`, and `IO.panic`.
    pub fn init_io_ops(&mut self) -> Result<(), EnvError> {
        if self.io_ops_init {
            return Ok(());
        }
        if !self.has_io() {
            self.init_io()?;
        }

        self.register_io_string_ops()?;
        self.register_io_misc_ops()?;

        self.io_ops_init = true;
        Ok(())
    }

    /// Check if IO operations have been initialized.
    pub fn has_io_ops(&self) -> bool {
        self.io_ops_init
    }

    /// Register IO ops that take/return String and Unit.
    fn register_io_string_ops(&mut self) -> Result<(), EnvError> {
        let io_const = Expr::const_(Name::from_string("IO"), vec![]);
        let string_ty = Expr::const_(Name::from_string("String"), vec![]);
        let unit_ty = Expr::const_(Name::from_string("Unit"), vec![]);

        let io_unit = Expr::app(io_const.clone(), unit_ty);
        let io_string = Expr::app(io_const, string_ty.clone());

        // String -> IO Unit
        let string_to_io_unit = Expr::pi(BinderInfo::Default, string_ty.clone(), io_unit.clone());
        // String -> IO String
        let string_to_io_string =
            Expr::pi(BinderInfo::Default, string_ty.clone(), io_string.clone());
        // String -> String -> IO Unit
        let string_string_to_io_unit = Expr::pi(
            BinderInfo::Default,
            string_ty.clone(),
            Expr::pi(BinderInfo::Default, string_ty, io_unit),
        );

        self.add_io_op_axiom("IO.println", string_to_io_unit.clone())?;
        self.add_io_op_axiom("IO.print", string_to_io_unit.clone())?;
        self.add_io_op_axiom("IO.eprintln", string_to_io_unit)?;
        self.add_io_op_axiom("IO.getLine", io_string.clone())?;
        self.add_io_op_axiom("IO.FS.readFile", string_to_io_string.clone())?;
        self.add_io_op_axiom("IO.FS.writeFile", string_string_to_io_unit)?;
        self.add_io_op_axiom("IO.getEnv", string_to_io_string)?;
        self.add_io_op_axiom("IO.currentDir", io_string)?;
        Ok(())
    }

    /// Register IO ops for Nat, process control, and IO.panic.
    fn register_io_misc_ops(&mut self) -> Result<(), EnvError> {
        let io_const = Expr::const_(Name::from_string("IO"), vec![]);
        let string_ty = Expr::const_(Name::from_string("String"), vec![]);
        let unit_ty = Expr::const_(Name::from_string("Unit"), vec![]);
        let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
        let type_0 = Expr::sort(Level::succ(Level::zero()));

        let io_unit = Expr::app(io_const.clone(), unit_ty);
        let io_nat = Expr::app(io_const.clone(), nat_ty.clone());
        let nat_to_io_unit = Expr::pi(BinderInfo::Default, nat_ty, io_unit);

        self.add_io_op_axiom("IO.Process.exit", nat_to_io_unit)?;
        self.add_io_op_axiom("IO.monoMsNow", io_nat)?;

        // IO.panic : {a : Type} -> String -> IO a
        let alpha = Expr::bvar(1);
        let io_alpha = Expr::app(io_const, alpha);
        let inner = Expr::pi(BinderInfo::Default, string_ty, io_alpha);
        let io_panic_type = Expr::pi(BinderInfo::Implicit, type_0, inner);
        self.add_io_op_axiom("IO.panic", io_panic_type)?;

        Ok(())
    }

    /// Helper: add an IO operation axiom with no universe parameters.
    fn add_io_op_axiom(&mut self, name: &str, type_: Expr) -> Result<(), EnvError> {
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_,
        })
    }
}
