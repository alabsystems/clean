// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The load of ONE module whose own declarations the caller replays, over
//! imports it trusts.

use super::{legacy_module_name, load_typed_module_with_deps_with_import_policy};
use crate::import::{ImportError, LoadSummary, OleanImportPolicy};
use clean_kernel::env::Environment;
use std::path::PathBuf;

/// [`super::load_module_with_deps_with_import_policy`], with `module`'s OWN
/// parts loaded under `OleanImportPolicy::with_module_replay_refusals` and
/// every import under `policy` itself.
///
/// For a caller that replays every declaration of `module` through the kernel
/// in Lean's order, refusing a self-dependent declaration, a use of one and a
/// redeclaration of an import's name itself, per declaration, and that trusts
/// the imports: the mathverse sharded worker. The loader's module-trust rules
/// would otherwise refuse the WHOLE import for such a declaration of `module`
/// (`ReplayForged3`'s `forged3_self := forged3_self`, `ReplayRedeclare`'s
/// `Nat.pred`), which pinned `leanchecker` refuses per declaration, in its
/// replay. Here the redeclaration is recorded in `module`'s
/// `LoadSummary::shadowed_declarations`, and the self-dependent declaration
/// registers as stored, for the replay to refuse by name.
///
/// Everything an IMPORT gets wrong still refuses the import: its own
/// self-dependent declaration (`ReplayCrossB`, whose import `ReplayCrossA`
/// holds `cross_forged := cross_forged`), a name it declares that another
/// import already declared, and a reference it made to a name none of its
/// imports declared, even when `module` declares that name. The imports are
/// only trusted, never replayed. That is stricter than `leanchecker
/// ReplayCrossB`, which trusts the import and exits 0, and it is deliberate:
/// per-module verdicts merged over a corpus with no cross-module pass would
/// otherwise count `cross_uses_forged : False` verified beside the refused
/// `cross_forged` it stands on.
///
/// # Errors
/// As [`super::load_module_with_deps_with_import_policy`].
pub fn load_module_with_deps_replaying_module(
    env: &mut Environment,
    module: &str,
    search_paths: &[PathBuf],
    policy: OleanImportPolicy,
) -> Result<Vec<LoadSummary>, ImportError> {
    load_typed_module_with_deps_with_import_policy(
        env,
        &legacy_module_name(module)?,
        search_paths,
        policy,
        policy.with_module_replay_refusals(),
    )
}
