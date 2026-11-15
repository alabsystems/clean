// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::{Interpreter, Module};
use std::sync::OnceLock;

#[derive(Clone, Copy, Debug)]
pub(super) enum ModulePreflight {
    Ready,
    UnsupportedAbi,
    InvalidStorage,
}

impl ModulePreflight {
    pub(super) fn inspect(module: &Module) -> Self {
        if module
            .func_types
            .iter()
            .any(|signature| signature.abi.is_some())
        {
            Self::UnsupportedAbi
        } else if module.first_storage_violation().is_some() {
            Self::InvalidStorage
        } else {
            Self::Ready
        }
    }
}

/// Lend interpreters sharing one lazy module-wide execution-policy preflight.
///
/// The immutable module borrow prevents safe mutation for this owner's entire
/// lifetime. Results are private to this exact borrow, never keyed by an address,
/// module name, function ID or global cache. Creating this owner performs no
/// validation or observed-work debit; ordinary execution initializes its policy
/// before executing any body or host callback. This is not full IR validation.
/// Explicit functions outside the module still receive their own body checks.
pub struct InterpreterModule<'module> {
    module: &'module Module,
    preflight: OnceLock<ModulePreflight>,
}

impl std::fmt::Debug for InterpreterModule<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("InterpreterModule")
            .field("module", &self.module.name)
            .field("preflight", &self.preflight.get())
            .finish()
    }
}

impl<'module> InterpreterModule<'module> {
    /// Retain one immutable module; validation stays lazy until execution.
    pub fn new(module: &'module Module) -> Self {
        Self {
            module,
            preflight: OnceLock::new(),
        }
    }

    /// Borrow an interpreter sharing this owner's complete module policy.
    /// Its ordinary options, host model, per-run fuel and memory remain local.
    pub fn interpreter(&self) -> Interpreter<'_> {
        let mut interpreter = Interpreter::with_module(self.module);
        interpreter.module_preflight = Some(&self.preflight);
        interpreter
    }
}
