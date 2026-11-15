// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! The complete structural lineage validator under the original session.
//! An empty diagnostic vector is structural validity, never proof closure.

use super::*;
use crate::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError, observed_btree,
};
use core::mem::size_of;
mod against;
mod cycles;
mod node;
#[cfg(test)]
mod original_tail_tests;
mod storage;
#[cfg(test)]
mod tests;
use storage::*;
type R<T = ()> = Result<T, ObservedValueError>;

#[derive(Clone, Copy, PartialEq, Eq)]
enum Mark {
    Visiting,
    Done,
}
#[derive(Clone, Copy)]
enum Frame {
    Enter(ProofLineageId),
    Next(ProofLineageId, usize),
}
#[derive(Default)]
struct Checking<'a> {
    nodes: BTreeMap<ProofLineageId, &'a ProofLineageNode>,
    roots: BTreeSet<ProofLineageId>,
    dependencies: BTreeSet<ProofLineageId>,
    obligations: BTreeSet<ProofId>,
    marks: BTreeMap<ProofLineageId, Mark>,
    certificates: Vec<(&'a ProofCertificate, ProofDigest)>,
    starts: Vec<ProofLineageId>,
    stack: Vec<Frame>,
    errors: Vec<ProofLineageError>,
    pending_error: Option<ProofLineageError>,
}

impl ProofLineageManifest {
    /// Return all errors from the existing `validate()` shape pass, in the
    /// same order, traversing the actual records, strings and dependency DFS
    /// under the caller's original session/site. This does not replay evidence,
    /// match module certificates, or issue any proof or source authority.
    /// Successful diagnostic disposal is the caller's responsibility.
    pub fn shape_errors_observed<O: ExecutionObserver>(
        &self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Vec<ProofLineageError>> {
        diagnostics(self, None, session, site)
    }

    /// Complete existing `validate_against` diagnostics, including actual
    /// evidence digest preimages and certificate/prover matching, under the
    /// same original session. This is structural correspondence, never replay.
    pub fn against_errors_observed<O: ExecutionObserver>(
        &self,
        obligations: &[ProofObligation],
        certificates: &[ProofCertificate],
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Vec<ProofLineageError>> {
        diagnostics(self, Some((obligations, certificates)), session, site)
    }
}

fn diagnostics<'a, O: ExecutionObserver>(
    manifest: &'a ProofLineageManifest,
    against: Option<(&[ProofObligation], &'a [ProofCertificate])>,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<ProofLineageError>> {
    admit(session, site, 1, size_of::<Checking<'_>>())?;
    let mut state = Checking::default();
    let result = state.shape(manifest, session, site).and_then(|()| {
        if let Some((obligations, certificates)) = against {
            state.against(manifest, obligations, certificates, session, site)?;
        }
        Ok(())
    });
    finish_diagnostics(&mut state, result, session, site)
}

fn finish_diagnostics<O: ExecutionObserver>(
    state: &mut Checking<'_>,
    result: R,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<ProofLineageError>> {
    state.retire_scratch(session, site);
    if let Err(error) = result {
        state.retire_errors(session, site);
        // Preserve the typed result held before cleanup. The later stop is
        // still recorded in the SAME original session and cannot overwrite it.
        return Err(error);
    }
    if session.first_refusal().is_some() {
        state.retire_errors(session, site);
        return Err(ObservedValueError::AdmissionRefused);
    }
    if session
        .admit(ExecutionProgress {
            phase: ExecutionPhase::Publication,
            site,
            work: 0,
            copy_bytes: 0,
        })
        .is_err()
    {
        state.retire_errors(session, site);
        return Err(ObservedValueError::AdmissionRefused);
    }
    Ok(core::mem::take(&mut state.errors))
}

impl<'a> Checking<'a> {
    fn shape<O: ExecutionObserver>(
        &mut self,
        manifest: &'a ProofLineageManifest,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        admit(session, site, 1, 0)?;
        if manifest.schema_version != ProofLineageManifest::SCHEMA_VERSION {
            self.error(
                ProofLineageError::UnsupportedSchemaVersion(manifest.schema_version),
                session,
                site,
            )?;
        }
        if manifest.nodes.is_empty() {
            self.error(ProofLineageError::EmptyManifest, session, site)?;
        }
        if manifest.roots.is_empty() {
            self.error(ProofLineageError::EmptyRoots, session, site)?;
        }
        for node in &manifest.nodes {
            admit(session, site, 1, 0)?;
            let duplicate = map_insert(&mut self.nodes, node.id, node, session, site)?.is_some();
            if duplicate {
                self.error(ProofLineageError::DuplicateNodeId(node.id), session, site)?;
            }
            self.node(node, session, site)?;
        }
        self.roots_and_dependencies(manifest, session, site)?;
        self.digest_links(manifest, session, site)?;
        self.cycles(session, site)
    }

    fn roots_and_dependencies<O: ExecutionObserver>(
        &mut self,
        manifest: &ProofLineageManifest,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        for root in &manifest.roots {
            admit(session, site, 1, 0)?;
            if !set_insert(&mut self.roots, *root, session, site)? {
                self.error(ProofLineageError::DuplicateRoot(*root), session, site)?;
            }
            lookup(self.nodes.len(), session, site)?;
            if !self.nodes.contains_key(root) {
                self.error(ProofLineageError::MissingRoot(*root), session, site)?;
            }
        }
        for node in &manifest.nodes {
            admit(session, site, 1, 0)?;
            for dependency in &node.depends_on {
                admit(session, site, 1, 0)?;
                if !set_insert(&mut self.dependencies, *dependency, session, site)? {
                    self.error(
                        ProofLineageError::DuplicateDependency {
                            node: node.id,
                            dependency: *dependency,
                        },
                        session,
                        site,
                    )?;
                }
                if *dependency == node.id {
                    self.error(ProofLineageError::Cycle { node: node.id }, session, site)?;
                }
                lookup(self.nodes.len(), session, site)?;
                if !self.nodes.contains_key(dependency) {
                    self.error(
                        ProofLineageError::MissingDependency {
                            node: node.id,
                            dependency: *dependency,
                        },
                        session,
                        site,
                    )?;
                }
            }
            retire_set(&mut self.dependencies, session, site);
            admit(session, site, 1, 0)?;
        }
        Ok(())
    }
    fn digest_links<O: ExecutionObserver>(
        &mut self,
        manifest: &ProofLineageManifest,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        for node in &manifest.nodes {
            admit(session, site, 1, 0)?;
            if node.transform.stage == ProofTransformStage::Composition {
                continue;
            }
            for dependency in &node.depends_on {
                lookup(self.nodes.len(), session, site)?;
                if let Some(previous) = self.nodes.get(dependency)
                    && previous.target_module != node.source_module
                {
                    self.error(
                        ProofLineageError::DependencyDigestMismatch {
                            node: node.id,
                            dependency: *dependency,
                            node_source: node.source_module,
                            dependency_target: previous.target_module,
                        },
                        session,
                        site,
                    )?;
                }
            }
        }
        Ok(())
    }
    fn error<O: ExecutionObserver>(
        &mut self,
        error: ProofLineageError,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        self.pending_error = Some(error);
        reserve(&mut self.errors, session, site)?;
        admit(session, site, 1, size_of::<ProofLineageError>())?;
        let Some(error) = self.pending_error.take() else {
            return Err(ObservedValueError::InvalidRange);
        };
        self.errors.push(error);
        Ok(())
    }
    fn retire_scratch<O: ExecutionObserver>(
        &mut self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) {
        retire_map(&mut self.nodes, session, site);
        retire_set(&mut self.roots, session, site);
        retire_set(&mut self.dependencies, session, site);
        retire_set(&mut self.obligations, session, site);
        retire_map(&mut self.marks, session, site);
        retire_value(core::mem::take(&mut self.certificates), session, site);
        retire_value(core::mem::take(&mut self.starts), session, site);
        retire_value(core::mem::take(&mut self.stack), session, site);
    }
    fn retire_errors<O: ExecutionObserver>(
        &mut self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) {
        retire_value(self.pending_error.take(), session, site);
        while !self.errors.is_empty() {
            session.retirement_poll(site);
            retire_value(self.errors.pop(), session, site);
        }
        retire_value(core::mem::take(&mut self.errors), session, site);
    }
}
