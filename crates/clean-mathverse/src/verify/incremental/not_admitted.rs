// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The incremental replay's refusal of every use of a target it did not admit
//! while the environment still resolves the target's name (R142,
//! `docs/DECISIONS.md`).
//!
//! A target the kernel rejects is normally not in the environment, so a
//! dependent fails as an unknown constant. A target whose name the
//! environment held before it (an import's declaration, or the kernel's: every
//! refusal of `try_accept_seeded_duplicate`) is different: the name still
//! resolves, to a declaration that is not this module's, and a dependent was
//! checked against it and stamped. Measured 2026-10-24 on `ReplayShadowStub`
//! (pinned `leanchecker` rc 1 in both modes): `stamp-verified` default and
//! `--single-pass` rejected the module's `theorem sha_n`, whose value the
//! kernel refuses, and stamped its user `sh_u` over the import's `axiom sha_n`.
//! Lean's replay admits a declaration only after everything it uses; so a
//! dependent of such a target is refused by name and not added, and so is
//! every dependent of a refused one.

use std::collections::{HashMap, HashSet};

use clean_kernel::env::Environment;
use clean_kernel::name::Name;

/// The targets of one replay that were not admitted and whose uses must be
/// refused.
#[derive(Debug, Default)]
pub(super) struct NotAdmitted {
    names: HashSet<String>,
}

impl NotAdmitted {
    /// Record a target the replay did not admit (`KernelRejected`,
    /// `ReconstructFailed`) when `env` still holds a declaration of its name.
    pub(super) fn note_unadmitted(&mut self, env: &Environment, name: &str) {
        if env.get_const(&Name::from_string(name)).is_some() {
            self.names.insert(name.to_owned());
        }
    }

    /// The refusal of `name` when one of its direct dependencies was not
    /// admitted; `name` then joins them, so its own dependents are refused
    /// too (topological order makes the direct check transitive).
    pub(super) fn refuse_user(
        &mut self,
        name: &str,
        dep_graph: &HashMap<String, HashSet<String>>,
    ) -> Option<String> {
        if self.names.is_empty() {
            return None;
        }
        let mut refused: Vec<&String> = dep_graph
            .get(name)?
            .iter()
            .filter(|d| self.names.contains(d.as_str()))
            .collect();
        refused.sort_unstable();
        let dependency = refused.first()?;
        let message = format!(
            "replay order: `{name}` depends on `{dependency}`, which was not admitted (the \
             environment resolves the name to a declaration that is not this module's; Lean's \
             replay admits a constant only after everything it uses)"
        );
        self.names.insert(name.to_owned());
        Some(message)
    }
}
