// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact provenance and policy constituents, never whole-bundle validity.

use super::*;
use crate::request::{
    NativeDiagnosticsPolicy, NativeToolIdentity, NativeUnknownFieldPolicy,
    NativeVerificationBundle, NativeVerificationBundleError as E,
};
use crate::{ProofDigest, ProofDigestAlgorithm};
use std::collections::BTreeSet;

mod custody;
#[cfg(test)]
mod tests;
use custody::*;

#[derive(Default)]
struct Checking {
    errors: Vec<E>,
    pending: Option<E>,
    functions: FunctionRows,
    imports: ImportRows,
}

enum Component {
    Provenance,
    Serialization,
    Diagnostics,
}

impl NativeVerificationBundle {
    /// All ordinary provenance diagnostics, in their original order, under
    /// the supplied original session/site. Includes actual tool whitespace
    /// scans and function/import coverage. Empty diagnostics do not establish
    /// whole-bundle validity, dependency authentication or source authority.
    /// Successful diagnostic disposal remains the caller's responsibility.
    pub fn provenance_errors_observed<O: ExecutionObserver>(
        &self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Vec<E>> {
        component(self, Component::Provenance, session, site)
    }

    /// The ordinary serialization-policy diagnostics only, in original order.
    /// This neither serializes the bundle nor establishes whole-bundle validity.
    pub fn serialization_errors_observed<O: ExecutionObserver>(
        &self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Vec<E>> {
        component(self, Component::Serialization, session, site)
    }

    /// The ordinary bundle diagnostics-policy errors only, in original order.
    /// Successful result disposal remains in the caller's original scope.
    pub fn diagnostics_policy_errors_observed<O: ExecutionObserver>(
        &self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Vec<E>> {
        component(self, Component::Diagnostics, session, site)
    }
}

fn component<O: ExecutionObserver>(
    bundle: &NativeVerificationBundle,
    selected: Component,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<E>> {
    admit(session, site, 1, size_of::<Checking>())?;
    let mut state = Checking::default();
    let result = match selected {
        Component::Provenance => state.provenance(bundle, session, site),
        Component::Serialization => state.serialization(bundle, session, site),
        Component::Diagnostics => state.diagnostics(&bundle.diagnostics, session, site),
    };
    state.finish(result, session, site)
}

impl Checking {
    fn provenance<O: ExecutionObserver>(
        &mut self,
        bundle: &NativeVerificationBundle,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        let provenance = &bundle.provenance;
        admit(session, site, 1, 0)?;
        // Ordinary provenance checks empty, not whitespace-only, versions.
        if provenance.producer_version.is_empty() {
            self.error(
                || E::EmptyProvenanceField("provenance.producer_version"),
                session,
                site,
            )?;
        }
        admit(session, site, 1, size_of::<Option<ProofDigest>>())?;
        if let Some(source) = provenance.source_digest {
            admit(session, site, 32, 0)?;
            if source.is_zero() {
                self.error(
                    || E::EmptyDigest {
                        field: "provenance.source_digest",
                    },
                    session,
                    site,
                )?;
            }
            admit(session, site, 1, 0)?;
            if source.algorithm != ProofDigestAlgorithm::Sha256 {
                self.error(
                    || E::NonCryptographicDigest {
                        field: "provenance.source_digest",
                    },
                    session,
                    site,
                )?;
            }
            // source_digest is the existing fixed enum/32-byte identity match.
            admit(session, site, 66, size_of::<Option<ProofDigest>>())?;
            if let Some(input) = bundle.source_digest()
                && input != source
            {
                self.error(
                    || E::InputDigestMismatch {
                        field: "provenance.source_digest",
                        expected: input,
                        actual: source,
                    },
                    session,
                    site,
                )?;
            }
        }
        let mut index = 0;
        while index < provenance.toolchain.len() {
            admit(session, site, 1, 0)?;
            self.tool(&provenance.toolchain[index], session, site)?;
            index += 1;
        }
        self.languages(bundle, session, site)
    }

    fn tool<O: ExecutionObserver>(
        &mut self,
        tool: &NativeToolIdentity,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        if blank(&tool.name, session, site)? {
            self.error(
                || E::EmptyProvenanceField("provenance.toolchain"),
                session,
                site,
            )?;
        }
        admit(session, site, 1, 0)?;
        if let Some(version) = &tool.version
            && blank(version, session, site)?
        {
            self.error(
                || E::InvalidToolIdentityField {
                    field: "provenance.toolchain",
                    component: "version",
                },
                session,
                site,
            )?;
        }
        admit(session, site, 1, 0)?;
        if let Some(revision) = &tool.revision
            && blank(revision, session, site)?
        {
            self.error(
                || E::InvalidToolIdentityField {
                    field: "provenance.toolchain",
                    component: "revision",
                },
                session,
                site,
            )?;
        }
        admit(session, site, 1, size_of::<Option<ProofDigest>>())?;
        if let Some(digest) = tool.digest {
            admit(session, site, 32, 0)?;
            if digest.is_zero() {
                self.error(
                    || E::EmptyDigest {
                        field: "provenance.toolchain",
                    },
                    session,
                    site,
                )?;
            }
        }
        admit(session, site, 1, size_of::<Option<ProofDigest>>())?;
        if tool
            .digest
            .is_some_and(|digest| digest.algorithm != ProofDigestAlgorithm::Sha256)
        {
            self.error(
                || E::InvalidToolIdentityField {
                    field: "provenance.toolchain",
                    component: "digest.algorithm",
                },
                session,
                site,
            )?;
        }
        Ok(())
    }

    fn languages<O: ExecutionObserver>(
        &mut self,
        bundle: &NativeVerificationBundle,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        let provenance = &bundle.provenance;
        admit(
            session,
            site,
            observed_btree::population_work(provenance.source_languages.len())?,
            0,
        )?;
        if !provenance
            .source_languages
            .contains(&provenance.source_language)
        {
            self.begin(session, site)?;
            self.pending = Some(E::BundlePrimaryLanguageUncovered {
                primary: provenance.source_language,
                source_languages: BTreeSet::new(),
            });
            self.language_set(&provenance.source_languages, session, site)?;
            self.commit(session, site)?;
        }
        // Once returned, these owned rows belong to this caller's custody.
        self.functions = provenance.uncovered_functions_observed(&bundle.module, session, site)?;
        reverse(&mut self.functions, session, site)?;
        while !self.functions.is_empty() {
            self.begin(session, site)?;
            admit(
                session,
                site,
                1,
                size_of::<(Option<Producer>, Vec<FuncId>)>(),
            )?;
            if let Some((producer, functions)) = self.functions.pop() {
                self.pending = Some(E::BundleLanguageUncovered {
                    producer,
                    functions,
                    source_languages: BTreeSet::new(),
                });
            }
            self.language_set(&provenance.source_languages, session, site)?;
            self.commit(session, site)?;
        }
        self.imports = provenance.uncovered_imports_observed(&bundle.module, session, site)?;
        reverse(&mut self.imports, session, site)?;
        while !self.imports.is_empty() {
            self.begin(session, site)?;
            admit(
                session,
                site,
                1,
                size_of::<(ImportId, String, Option<Producer>)>(),
            )?;
            if let Some((import, name, producer)) = self.imports.pop() {
                self.pending = Some(E::BundleImportLanguageUncovered {
                    import,
                    name,
                    producer,
                    source_languages: BTreeSet::new(),
                });
            }
            self.language_set(&provenance.source_languages, session, site)?;
            self.commit(session, site)?;
        }
        Ok(())
    }

    fn serialization<O: ExecutionObserver>(
        &mut self,
        bundle: &NativeVerificationBundle,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        let policy = &bundle.serialization;
        admit(session, site, 1, 0)?;
        if policy.schema_version != NativeVerificationBundle::SCHEMA_VERSION {
            self.error(
                || E::UnsupportedSerializationSchemaVersion(policy.schema_version),
                session,
                site,
            )?;
        }
        admit(session, site, 1, 0)?;
        if !policy.canonical_order {
            self.error(
                || E::NonCanonicalSerialization("serialization.canonical_order"),
                session,
                site,
            )?;
        }
        admit(session, site, 1, 0)?;
        if !policy.sort_unordered_sets {
            self.error(
                || E::NonCanonicalSerialization("serialization.sort_unordered_sets"),
                session,
                site,
            )?;
        }
        admit(session, site, 1, 0)?;
        if !policy.messagepack_named_fields {
            self.error(
                || E::NonCanonicalSerialization("serialization.messagepack_named_fields"),
                session,
                site,
            )?;
        }
        admit(session, site, 1, 0)?;
        if policy.unknown_fields != NativeUnknownFieldPolicy::Reject {
            self.error(
                || E::NonCanonicalSerialization("serialization.unknown_fields"),
                session,
                site,
            )?;
        }
        Ok(())
    }

    fn diagnostics<O: ExecutionObserver>(
        &mut self,
        policy: &NativeDiagnosticsPolicy,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        admit(session, site, 1, 0)?;
        if !policy.include_source_spans {
            self.error(
                || E::InvalidBundleDiagnosticsPolicy {
                    field: "include_source_spans",
                },
                session,
                site,
            )?;
        }
        admit(session, site, 1, 0)?;
        if !policy.include_lineage {
            self.error(
                || E::InvalidBundleDiagnosticsPolicy {
                    field: "include_lineage",
                },
                session,
                site,
            )?;
        }
        admit(session, site, 2, 0)?;
        if policy.emit_counterexamples && policy.max_counterexamples == 0 {
            self.error(
                || E::InvalidBundleDiagnosticsPolicy {
                    field: "max_counterexamples",
                },
                session,
                site,
            )?;
        }
        Ok(())
    }
}
