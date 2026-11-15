// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! What Lean refuses before its replay starts, and a load that fails outright,
//! as refusal records that name the declaration.
//!
//! `leanchecker` refuses at two layers (`src/lean/LeanChecker.lean`,
//! v4.30.0-rc2). Its IMPORT (`finalizeImport`) refuses a closure in which two
//! modules declare one name, unless one restates the other (`subsumesInfo`):
//! `import M failed, environment already contains 'x' from N`. Its REPLAY
//! refuses a declaration the kernel does not admit. `leanchecker <M>` imports
//! only `M`'s imports and replays `M`'s constants, so a name `M` redeclares is
//! the replay's `already declared`; `leanchecker --fresh M` imports all of
//! `M`'s closure, `M` included, so the same name is the import's refusal.
//! Measured with the pinned binary on `ReplayForgedBoolDef` (`def bool_ax_b`
//! over `ReplayHonestBoolAx`'s `axiom bool_ax_b`): `leanchecker` refuses it in
//! the replay, `leanchecker --fresh` with `import ReplayForgedBoolDef failed,
//! environment already contains 'bool_ax_b' from ReplayHonestBoolAx`.

use crate::{ImportError, LoadSummary};

use super::{RefusalRecord, ReplayMode};

/// The base module of a loader part label (`M._server`, `M._private` → `M`).
fn base_module(label: &str) -> &str {
    label
        .strip_suffix("._server")
        .or_else(|| label.strip_suffix("._private"))
        .unwrap_or(label)
}

/// The duplicates Lean's IMPORT refuses, by name. The loader keeps the first
/// declaration of a name and records each later one Lean does not merge in
/// `LoadSummary::shadowed_declarations`, which omits the restatements Lean
/// accepts and, in this kernel-only load, includes a declaration other than a
/// theorem that would have filled another module's axiom
/// (`OleanImportPolicy::with_kernel_only`); it runs under
/// `OleanImportPolicy::with_replay_refusals`, so it never refuses the import
/// for one. Which modules Lean imports depends on the mode: with the imports
/// trusted, the modules not replayed; under `--fresh`, every module of the
/// closure, the replayed one included.
pub(super) fn import_merge_refusals(
    mode: ReplayMode,
    summaries: &[LoadSummary],
    replayed: &dyn Fn(&str) -> bool,
) -> Vec<RefusalRecord> {
    let mut refusals = Vec::new();
    for summary in summaries {
        let imported_by_lean = match mode {
            ReplayMode::ImportsTrusted => !summary.module_name.as_deref().is_some_and(replayed),
            ReplayMode::Fresh => true,
        };
        if !imported_by_lean {
            continue;
        }
        let module = base_module(summary.module_name.as_deref().unwrap_or("<unnamed module>"));
        for (name, held_by) in &summary.shadowed_declarations {
            refusals.push(RefusalRecord::refused(
                name.to_string(),
                format!(
                    "`{module}` declares it and it is already {held_by}: Lean's import refuses \
                     the closure before its replay (`finalizeImport`: import {module} failed, \
                     environment already contains '{name}')"
                ),
            ));
        }
    }
    refusals
}

/// A load that failed outright, as refusal records: one per declaration the
/// loader's error names, or one naming `module` when it names none (a missing
/// module, an unreadable file). Nothing of the closure was replayed, so the
/// record keeps the error too; these name what it was about.
pub(super) fn load_error_refusals(module: &str, error: &ImportError) -> Vec<RefusalRecord> {
    let named = error.declaration_names();
    let reason = format!("the .olean closure could not be loaded: {error}");
    if named.is_empty() {
        return vec![RefusalRecord::refused(module.to_owned(), reason)];
    }
    named
        .into_iter()
        .map(|constant| RefusalRecord::refused(constant.to_owned(), reason.clone()))
        .collect()
}
