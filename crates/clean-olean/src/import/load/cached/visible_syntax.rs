// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Visibility of exported parser registrations in Lean's module import graph.

use super::*;
use crate::import::exported_numeral_prefix::loaded_numeral_prefixes;
use crate::import::{ExportedNumeralPrefix, TypedImportFlags};

pub(super) type SyntaxVisitor<'a> =
    dyn FnMut(&Name, &[u8], Vec<ExportedNumeralPrefix>) -> Result<(), ImportError> + 'a;

pub(super) type LinkedSyntaxVisitor<'a> = dyn FnMut(
        &Name,
        &[u8],
        Vec<ExportedNumeralPrefix>,
        Arc<crate::ExportedTermProviders>,
    ) -> Result<(), ImportError>
    + 'a;

pub(super) struct SyntaxRequest<'a, 'v> {
    pub(super) capture_bootstrap_runtime: bool,
    pub(super) roots: &'a [(Name, bool)],
    pub(super) module_system: bool,
    pub(super) visit: &'a mut LinkedSyntaxVisitor<'v>,
}

/// The artifact ledger exposes display labels. Compute collisions across the entire
/// captured graph, including modules outside the handler's direct public meta imports.
pub(super) fn ambiguous_labels<'a>(names: impl Iterator<Item = &'a Name>) -> HashSet<String> {
    let mut seen = HashSet::new();
    let mut ambiguous = HashSet::new();
    for name in names {
        let label = name.to_string();
        if !seen.insert(label.clone()) {
            ambiguous.insert(label);
        }
    }
    ambiguous
}

impl SyntaxRequest<'_, '_> {
    pub(super) fn apply(
        &mut self,
        graph: &HashMap<Name, Arc<DirectModule>>,
        order: &[Name],
        ambiguous: &HashSet<String>,
    ) -> Result<(), ImportError> {
        let mut visible = HashMap::new();
        let mut pending = self.roots.to_vec();
        while let Some((name, all)) = pending.pop() {
            deadline::check()?;
            let all = all || !self.module_system;
            if let Some(&previous) = visible.get(&name) {
                if previous || !all {
                    continue;
                }
            }
            visible.insert(name.clone(), all);
            let bundle = graph
                .get(&name)
                .ok_or_else(|| ImportError::UnsupportedModule {
                    module: name.to_string(),
                    reason: "visible dependency absent from the captured graph".into(),
                })?;
            // The exported and private ModuleData parts can carry different imports.
            let part = if all && bundle.base.is_module {
                bundle
                    .private
                    .as_ref()
                    .ok_or_else(|| ImportError::UnsupportedModule {
                        module: name.to_string(),
                        reason: "import all requires the private module data".into(),
                    })?
            } else {
                &bundle.base
            };
            for import in &part.typed_imports {
                let TypedImportFlags::LeanV2 {
                    is_exported,
                    import_all,
                    ..
                } = import.flags
                else {
                    return Err(ImportError::UnsupportedModule {
                        module: name.to_string(),
                        reason: "stable term syntax requires Lean v2 import flags".into(),
                    });
                };
                if all || is_exported {
                    pending.push((import.module_name.clone(), all && import_all));
                }
            }
        }

        // Replay each module once, in the loader's dependency-first order. A second
        // path can strengthen visibility even when the first path was ordinary.
        for name in order.iter().filter(|name| visible.contains_key(*name)) {
            deadline::check()?;
            let bundle = graph
                .get(name)
                .ok_or_else(|| ImportError::UnsupportedModule {
                    module: name.to_string(),
                    reason: "visible module absent from the captured graph".into(),
                })?;
            let base = &bundle.base;
            let prefixes =
                loaded_numeral_prefixes(base).map_err(|source| ImportError::FileParse {
                    path: base
                        .source_olean
                        .clone()
                        .unwrap_or_else(|| PathBuf::from(name.to_string())),
                    source,
                })?;
            if !prefixes.is_empty() {
                let mut providers = crate::ExportedTermProviders::default();
                for edge in &base.typed_imports {
                    if !matches!(
                        edge.flags,
                        TypedImportFlags::LeanV2 {
                            is_exported: true,
                            is_meta: true,
                            ..
                        }
                    ) {
                        continue;
                    }
                    let Some(owner) = graph.get(&edge.module_name) else {
                        continue;
                    };
                    if let (Some(path), Some(capture)) =
                        (&owner.base.source_olean, &owner.base.captured_ir)
                    {
                        providers.insert(
                            edge.module_name.clone(),
                            path.clone(),
                            Arc::clone(capture),
                            ambiguous.contains(&edge.module_name.to_string()),
                        );
                    }
                }
                (self.visit)(name, &base.bytes, prefixes, Arc::new(providers))?;
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn exported_provider_labels_account_for_other_structural_graph_keys() {
        let nested = Name::anon().str("A").str("B");
        let quoted = Name::anon().str("A.B");
        assert_ne!(nested, quoted);
        assert_eq!(nested.to_string(), quoted.to_string());
        assert!(ambiguous_labels([&nested].into_iter()).is_empty());
        assert!(ambiguous_labels([&nested, &quoted].into_iter()).contains(&nested.to_string()));
    }
}
