// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! What `clean check` and `clean export-cert` may conclude about the imported
//! artifacts a file was checked against: is each one the build of its source?
//!
//! The imported-cone gate (`check_import_gate.rs`) re-admits every imported
//! declaration a credited declaration cites, so the cited closure is
//! well-typed. Well-typed is not faithful: a definition rewritten to another
//! well-typed value, or an elaborator table rewritten consistently, passes any
//! re-check, and the checked statement then means what the artifact says
//! (module-trust round 27, M2: `theorem : V0.v = 1 := rfl` over an artifact
//! whose `V0.v` is `1` while its source says `0`, `1 passed`). Only the source
//! can say what a module means, so:
//!
//! * an artifact in a Lake workspace's build directory next to its source,
//!   written by this builder, must be what `clean lake build` recorded
//!   building from that source (`ArtifactSourceBinding::Bound` in
//!   `clean_lake::artifact_binding`);
//!   otherwise the file is not checked against it at all (a refusal row);
//! * an artifact with no source to compare, or one another tool wrote, is
//!   DISCLOSED on the verdict: the statements checked against it hold of the
//!   artifact's definitions, which were not compared with any source.
//!
//! Toolchain modules are the checker's declared base and are not listed. A
//! module is one only when every `.olean` part it resolved to is byte-identical
//! to the pinned toolchain's, by the digest manifest this binary was built with
//! ([`clean_olean::toolchain_identity`]) — never because of where it sits or
//! what file names sit next to it (round 28: an empty `<lib>/Init/Prelude.olean`
//! used to exempt every module under `<lib>`).

//!
//! The decision itself is [`clean_lake::ImportAdmitter`]: one admission
//! authority, which `clean lake build` and `clean lake check-build` use for
//! every module they load that the workspace does not build itself
//! (module-trust round 31).

use std::collections::HashSet;

/// Per-run record of which loaded modules have been examined.
#[derive(Debug, Default)]
pub(crate) struct ImportBinding {
    admitter: clean_lake::ImportAdmitter,
    examined: HashSet<String>,
}

/// What [`ImportBinding::examine`] found among newly loaded modules.
pub(crate) type ImportBindingFindings = clean_lake::ImportAdmissionFindings;

impl ImportBinding {
    /// Examine every module `file_ctx` has loaded from an artifact that has
    /// not been examined yet this run.
    pub(crate) fn examine(&mut self, file_ctx: &clean_elab::FileContext) -> ImportBindingFindings {
        let fresh: Vec<String> = file_ctx
            .import_visited()
            .iter()
            .filter(|m| !self.examined.contains(*m))
            .cloned()
            .collect();
        if fresh.is_empty() {
            return ImportBindingFindings::default();
        }
        self.examined.extend(fresh.iter().cloned());
        // A file whose project's Lean world is refused loaded no artifact.
        let search_paths = file_ctx.effective_import_search_paths().unwrap_or_default();
        match file_ctx.declared_lean_world() {
            Ok(world) => self.admitter.examine_in_world(fresh, &search_paths, world),
            Err(error) => ImportBindingFindings {
                refusals: vec![error.to_string()],
                ..ImportBindingFindings::default()
            },
        }
    }
}

/// How many disclosure rows a text verdict prints before summarising the
/// rest as a count (every row is in the JSON report).
pub(crate) const DISCLOSURE_ROWS_SHOWN: usize = 20;

/// The heading the verdicts print above the disclosure rows.
pub(crate) const DISCLOSURE_HEADING: &str =
    "imported module(s) taken from artifacts that were not compared with any source: \
     statements checked against them hold of the definitions and elaborator metadata AS BUILT";

#[cfg(test)]
#[path = "import_binding_tests.rs"]
pub(crate) mod tests;
