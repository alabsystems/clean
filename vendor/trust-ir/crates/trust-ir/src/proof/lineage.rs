// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Proof lineage: the versioned sidecar manifest ([`ProofLineageManifest`]) and
//! its building blocks — [`ProofLineageNode`], [`ProofLineageId`],
//! [`ProofTransform`] / [`ProofTransformStage`], [`ProofReplayIdentity`] — plus
//! the structural validators and [`ProofLineageError`].

use super::evidence::{
    ProofAuthorityRechecker, ProofCertificate, ProofCertificateRef, ProofDigest,
    ProofDigestAlgorithm, ProofEvidence, RejectingProofAuthorityRechecker, write_digest_stable,
    write_len_stable, write_str_stable, write_u8_stable, write_u32_stable,
};
use super::obligations::{ObligationKind, ProofFormula, ProofObligation, ProofStatus};
use crate::value::ProofId;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ProofLineageId(pub u32);

impl ProofLineageId {
    pub const fn new(index: u32) -> Self {
        Self(index)
    }

    pub const fn index(self) -> u32 {
        self.0
    }
}

impl core::fmt::Display for ProofLineageId {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// Coarse stage kind for a proof-producing transform.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum ProofTransformStage {
    Frontend,
    TrustIrLowering,
    TrustIrOptimization,
    SolverAdapter,
    Backend,
    Replay,
    Composition,
    Other,
}

/// Identity of the transform that produced a lineage node.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ProofTransform {
    pub stage: ProofTransformStage,
    pub name: String,
    pub producer: String,
    pub version: String,
}

impl ProofTransform {
    pub fn new(
        stage: ProofTransformStage,
        name: impl Into<String>,
        producer: impl Into<String>,
        version: impl Into<String>,
    ) -> Self {
        Self {
            stage,
            name: name.into(),
            producer: producer.into(),
            version: version.into(),
        }
    }
}

/// Formula schema that binds a translation-validation obligation to one exact
/// lineage transform edge. The payload is the canonical SHA-256 digest of the
/// edge's source semantics, target semantics, and full [`ProofTransform`]
/// identity.
pub const LINEAGE_TRANSFORM_BINDING_SCHEMA: &str = "trust-ir.ProofLineageTransformBinding@1";

/// Canonical authority-binding digest for a lineage transform edge.
///
/// Proof table identities are intentionally excluded: including obligation or
/// certificate references would make certificate construction circular. The
/// semantic edge itself is fully covered: both endpoint digests and every
/// transform identity field (`stage`, `name`, `producer`, `version`).
pub fn lineage_transform_binding_digest(
    transform: &ProofTransform,
    source_semantics: &ProofDigest,
    target_semantics: &ProofDigest,
) -> ProofDigest {
    let mut bytes = Vec::new();
    write_transform_stable(&mut bytes, transform);
    write_digest_stable(&mut bytes, source_semantics);
    write_digest_stable(&mut bytes, target_semantics);
    ProofDigest::sha256_domain("trust_ir.proof.lineage.transform_binding.v1", &bytes)
}

/// Canonical obligation formula for one exact lineage transform edge.
pub fn lineage_transform_binding_formula(
    transform: &ProofTransform,
    source_semantics: &ProofDigest,
    target_semantics: &ProofDigest,
) -> ProofFormula {
    ProofFormula::new(
        LINEAGE_TRANSFORM_BINDING_SCHEMA,
        lineage_transform_binding_digest(transform, source_semantics, target_semantics).to_string(),
    )
}

/// Replay identity for an independently repeatable verifier run.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ProofReplayIdentity {
    pub engine: String,
    pub invocation: String,
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
    pub transcript_digest: Option<ProofDigest>,
}

impl ProofReplayIdentity {
    pub fn new(engine: impl Into<String>, invocation: impl Into<String>) -> Self {
        Self {
            engine: engine.into(),
            invocation: invocation.into(),
            transcript_digest: None,
        }
    }

    pub fn with_transcript_digest(mut self, digest: ProofDigest) -> Self {
        self.transcript_digest = Some(digest);
        self
    }
}

/// One proof-producing transform in a composed proof DAG.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ProofLineageNode {
    pub id: ProofLineageId,
    pub transform: ProofTransform,
    pub source_module: ProofDigest,
    pub target_module: ProofDigest,
    pub obligations: Vec<ProofId>,
    pub certificates: Vec<ProofCertificateRef>,
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
    pub replay: Option<ProofReplayIdentity>,
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Vec::is_empty")
    )]
    pub depends_on: Vec<ProofLineageId>,
}

impl ProofLineageNode {
    pub fn new(
        id: ProofLineageId,
        transform: ProofTransform,
        source_module: ProofDigest,
        target_module: ProofDigest,
    ) -> Self {
        Self {
            id,
            transform,
            source_module,
            target_module,
            obligations: Vec::new(),
            certificates: Vec::new(),
            replay: None,
            depends_on: Vec::new(),
        }
    }

    pub fn stable_digest(&self) -> ProofDigest {
        let mut bytes = Vec::new();
        write_u32_stable(&mut bytes, self.id.index());
        write_transform_stable(&mut bytes, &self.transform);
        write_digest_stable(&mut bytes, &self.source_module);
        write_digest_stable(&mut bytes, &self.target_module);

        let mut obligations = self.obligations.clone();
        obligations.sort();
        write_len_stable(&mut bytes, obligations.len());
        for obligation in obligations {
            write_u32_stable(&mut bytes, obligation.index());
        }

        let mut certificates = self.certificates.clone();
        certificates.sort();
        write_len_stable(&mut bytes, certificates.len());
        for cert in certificates {
            write_certificate_ref_stable(&mut bytes, &cert);
        }

        match &self.replay {
            None => write_u8_stable(&mut bytes, 0),
            Some(replay) => {
                write_u8_stable(&mut bytes, 1);
                write_replay_stable(&mut bytes, replay);
            }
        }

        let mut depends_on = self.depends_on.clone();
        depends_on.sort();
        write_len_stable(&mut bytes, depends_on.len());
        for dep in depends_on {
            write_u32_stable(&mut bytes, dep.index());
        }

        ProofDigest::sha256_domain("trust_ir.proof.lineage.node.v2", &bytes)
    }

    /// Formula every obligation authorizing this rung must carry. Because a
    /// certificate's replay identity is in turn bound to its exact obligation,
    /// this prevents a proof for another transform or endpoint pair from being
    /// reused on this node.
    pub fn transform_binding_formula(&self) -> ProofFormula {
        lineage_transform_binding_formula(&self.transform, &self.source_module, &self.target_module)
    }
}

/// Versioned sidecar manifest for composed proof certificates.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ProofLineageManifest {
    pub schema_version: u32,
    pub nodes: Vec<ProofLineageNode>,
    pub roots: Vec<ProofLineageId>,
}

impl ProofLineageManifest {
    /// v2 requires SHA-256 for every module, certificate, and replay identity
    /// crossing the lineage boundary and uses checked u64 digest framing.
    /// Authority-aware closure additionally requires an exact
    /// `TranslationValidation` formula binding for every rung; this tightens
    /// acceptance without changing the sidecar's wire shape.
    pub const SCHEMA_VERSION: u32 = 2;

    pub fn new() -> Self {
        Self {
            schema_version: Self::SCHEMA_VERSION,
            nodes: Vec::new(),
            roots: Vec::new(),
        }
    }

    /// Append one pass to the lineage chain, owning the chaining bookkeeping
    /// [`validate`](Self::validate) enforces (roadmap:
    /// `proofchain-lineage-append`). The caller supplies *what* the pass did
    /// (transform, target digest, discharged obligations, certificates); this
    /// helper supplies the *chaining*: it allocates the next
    /// [`ProofLineageId`], sets `source_module` to the current tip's
    /// `target_module` (`base_module` — the digest of the module the chain
    /// starts from — for the first node on an empty chain, where it is the
    /// only use of that argument), sets `depends_on = [tip]`, and moves the
    /// tip root to the new node (the predecessor stays reachable via
    /// `depends_on`). Returns the new node's id.
    ///
    /// The helper does not weaken validation: `obligations` must be non-empty
    /// and every certificate's obligation bound, exactly as `validate`
    /// requires of hand-built nodes.
    pub fn append_pass(
        &mut self,
        transform: ProofTransform,
        base_module: ProofDigest,
        target_module: ProofDigest,
        obligations: Vec<ProofId>,
        certificates: Vec<ProofCertificateRef>,
    ) -> ProofLineageId {
        // Next id past every existing node, so appending to a hand-built
        // manifest cannot collide with its ids.
        let id = ProofLineageId::new(
            self.nodes
                .iter()
                .map(|node| node.id.index() + 1)
                .max()
                .unwrap_or(0),
        );
        let (source_module, depends_on) = if self.nodes.is_empty() {
            (base_module, Vec::new())
        } else {
            // The chain tip is the unique declared root; a hand-built
            // single-chain manifest whose nodes are not in push order still
            // resolves via the unique terminal node (a node no other node
            // depends on). Ambiguity (parallel chains / multiple terminals)
            // cannot be resolved silently — the digest auto-threading would
            // attest the pass ran on the wrong chain's module and validate()
            // could not detect it — so it panics instead.
            let tip_id = if self.roots.len() == 1 {
                self.roots[0]
            } else {
                let depended: BTreeSet<ProofLineageId> = self
                    .nodes
                    .iter()
                    .flat_map(|n| n.depends_on.iter().copied())
                    .collect();
                let mut terminals = self
                    .nodes
                    .iter()
                    .map(|n| n.id)
                    .filter(|id| !depended.contains(id));
                match (terminals.next(), terminals.next()) {
                    (Some(tip), None) => tip,
                    _ => panic!(
                        "append_pass: ambiguous chain tip (multiple roots / terminal \
                         nodes) — thread depends_on by hand for multi-chain manifests"
                    ),
                }
            };
            let tip = self
                .nodes
                .iter()
                .find(|n| n.id == tip_id)
                .unwrap_or_else(|| panic!("append_pass: root #{} names no node", tip_id.index()));
            (tip.target_module, vec![tip.id])
        };
        let mut node = ProofLineageNode::new(id, transform, source_module, target_module);
        node.obligations = obligations;
        node.certificates = certificates;
        node.depends_on = depends_on;
        // The new node is the tip: it replaces its predecessor among the
        // roots (an emitted-code rung is a root; its ancestors are reached by
        // walking depends_on).
        if let Some(prev) = node.depends_on.first().copied() {
            self.roots.retain(|root| *root != prev);
        }
        self.roots.push(id);
        self.nodes.push(node);
        id
    }

    pub fn validate(&self) -> Result<(), Vec<ProofLineageError>> {
        let mut errors = Vec::new();
        self.validate_shape(&mut errors);
        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors)
        }
    }

    pub fn validate_against(
        &self,
        obligations: &[ProofObligation],
        certificates: &[ProofCertificate],
    ) -> Result<(), Vec<ProofLineageError>> {
        let mut errors = Vec::new();
        self.validate_shape(&mut errors);

        let known_obligations: BTreeSet<ProofId> = obligations.iter().map(|o| o.id).collect();
        let known_certificates: Vec<ProofCertificateRef> = certificates
            .iter()
            .map(ProofCertificate::lineage_ref)
            .collect();

        for node in &self.nodes {
            for obligation in &node.obligations {
                if !known_obligations.contains(obligation) {
                    errors.push(ProofLineageError::UnknownObligation {
                        node: node.id,
                        obligation: *obligation,
                    });
                }
            }

            for cert in &node.certificates {
                if known_certificates.iter().any(|known| known == cert) {
                    continue;
                }

                if known_certificates
                    .iter()
                    .any(|known| known.obligation == cert.obligation && known.prover == cert.prover)
                {
                    errors.push(ProofLineageError::CertificateDigestMismatch {
                        node: node.id,
                        obligation: cert.obligation,
                        prover: cert.prover.clone(),
                    });
                } else {
                    errors.push(ProofLineageError::MissingCertificate {
                        node: node.id,
                        obligation: cert.obligation,
                        prover: cert.prover.clone(),
                    });
                }
            }
        }

        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors)
        }
    }

    /// The interpretation-B "completely proven" acceptance criterion
    /// (`lineage_is_closed`): a Module's proof-lineage chain is CLOSED iff every
    /// rung from the source digest to the emitted-code digest is present,
    /// `depends_on`-connected, and NONE is a faith-stamped (`Trusted`) rung.
    ///
    /// Concretely, walking the `depends_on` DAG backward from `roots`:
    ///
    /// 1. **Non-empty.** The manifest has at least one node and at least one
    ///    root ([`LineageGap::EmptyManifest`]).
    /// 2. **No dangling edges.** Every `depends_on` id resolves to a present
    ///    node ([`LineageGap::MissingDependency`]).
    /// 3. **Acyclic.** No node transitively depends on itself
    ///    ([`LineageGap::Cycle`]).
    /// 4. **Connected source -> emitted.** Every node in the manifest is
    ///    reachable from some root by following `depends_on`
    ///    ([`LineageGap::NotConnectedToSource`]). Roots are the emitted-code
    ///    rungs; following `depends_on` walks back to the source rung(s).
    /// 5. **No faith-stamped rung.** For every reachable node, each referenced
    ///    certificate must have strong status and be replayed by an explicit
    ///    [`ProofAuthorityRechecker`]. The structural-only entry point supplies
    ///    a rejecting capability, so opaque SMT/Lean/Kani strings, hashes, and
    ///    public `Discharged` / `Certified` labels are gaps rather than proof.
    ///
    /// Evidence and status do NOT live on the lineage node; the node carries
    /// only [`ProofCertificateRef`] identity tuples. The actual
    /// [`ProofCertificate`] (with its [`ProofEvidence`]) and the
    /// [`ProofObligation`] (with its [`ProofStatus`]) live on the module's
    /// tables, which is why both are passed in here.
    ///
    /// Returns `Ok(())` if the chain is closed, or `Err(gap)` describing the
    /// FIRST reason it is not — enabling an honest "interpretation B is not yet
    /// closed for this module" report.
    pub fn lineage_is_closed(
        &self,
        obligations: &[ProofObligation],
        certificates: &[ProofCertificate],
    ) -> Result<(), LineageGap> {
        self.lineage_is_closed_with_authority(
            obligations,
            certificates,
            &RejectingProofAuthorityRechecker,
        )
    }

    /// Authority-aware lineage closure. Structural-only callers should use
    /// [`Self::lineage_is_closed`], which deliberately supplies a rejecting
    /// capability and therefore cannot turn serialized labels/bytes into a
    /// closed proof chain.
    pub fn lineage_is_closed_with_authority(
        &self,
        obligations: &[ProofObligation],
        certificates: &[ProofCertificate],
        authority: &dyn ProofAuthorityRechecker,
    ) -> Result<(), LineageGap> {
        // (1) Non-empty: a chain with no rungs (or no emitted-code rung to walk
        // back from) proves nothing.
        if self.nodes.is_empty() || self.roots.is_empty() {
            return Err(LineageGap::EmptyManifest);
        }

        // Do not let a duplicate id collapse producer-selected nodes in the
        // map below. Other graph-shape errors retain their established,
        // specific LineageGap diagnostics during the walk.
        let mut unique_node_ids = BTreeSet::new();
        if let Some(duplicate) = self
            .nodes
            .iter()
            .map(|node| node.id)
            .find(|id| !unique_node_ids.insert(*id))
        {
            return Err(LineageGap::TrustedRung {
                node: duplicate,
                justification: format!(
                    "invalid lineage manifest: duplicate lineage node id {duplicate}"
                ),
            });
        }

        let nodes_by_id: BTreeMap<ProofLineageId, &ProofLineageNode> =
            self.nodes.iter().map(|node| (node.id, node)).collect();

        // (2,3,4) Walk the depends_on DAG backward from each root, collecting
        // reachable nodes. Dangling edges and cycles are reported as we go.
        let mut reachable: BTreeSet<ProofLineageId> = BTreeSet::new();
        let mut stack: Vec<(ProofLineageId, Vec<ProofLineageId>)> = Vec::new();
        for root in &self.roots {
            if !nodes_by_id.contains_key(root) {
                // A root that names no node cannot anchor the chain to an
                // emitted-code rung.
                return Err(LineageGap::NotConnectedToSource { node: *root });
            }
            if !reachable.insert(*root) {
                continue;
            }
            stack.push((*root, Vec::new()));
            while let Some((id, path)) = stack.pop() {
                let node = nodes_by_id[&id];
                for dep in &node.depends_on {
                    // (3) Acyclic: a dep already on the current path closes a loop.
                    if id == *dep || path.contains(dep) {
                        return Err(LineageGap::Cycle { node: *dep });
                    }
                    // (2) No dangling edges.
                    if !nodes_by_id.contains_key(dep) {
                        return Err(LineageGap::MissingDependency {
                            node: id,
                            missing: *dep,
                        });
                    }
                    if reachable.insert(*dep) {
                        let mut next = path.clone();
                        next.push(id);
                        stack.push((*dep, next));
                    }
                }
            }
        }

        // (4) Connected: every rung must be on the lineage from a root to the
        // source. A node no root depends on is a disconnected/orphan rung whose
        // proof contributes nothing to the emitted code.
        for node in &self.nodes {
            if !reachable.contains(&node.id) {
                return Err(LineageGap::NotConnectedToSource { node: node.id });
            }
        }

        // Closure is an authority boundary, not a caller-ordering convention.
        // Once the graph-specific diagnostics above have been preserved, run
        // the complete structural/table validator before evidence authority.
        // In particular, this enforces SHA-256-only lineage identities.
        if let Err(validation_errors) = self.validate_against(obligations, certificates) {
            let reason = validation_errors
                .first()
                .map(ToString::to_string)
                .unwrap_or_else(|| "unknown validation failure".to_string());
            return Err(LineageGap::TrustedRung {
                node: self.nodes[0].id,
                justification: format!("invalid lineage manifest: {reason}"),
            });
        }

        // A duplicated obligation id makes status/evidence resolution
        // ambiguous (`BTreeMap::collect` would otherwise silently keep one
        // producer-selected row). Reject before building the lookup table.
        let mut unique_obligations = BTreeSet::new();
        if let Some(duplicate) = obligations
            .iter()
            .map(|obligation| obligation.id)
            .find(|id| !unique_obligations.insert(*id))
        {
            return Err(LineageGap::TrustedRung {
                node: self.nodes[0].id,
                justification: format!(
                    "duplicate obligation id {duplicate} makes proof authority ambiguous"
                ),
            });
        }

        // Every claim carried by every rung needs a certificate reference.
        // Iterating only `node.certificates` made a certless rung pass the
        // authority loop vacuously, including under the rejecting default.
        for node in &self.nodes {
            if let Some(unbacked) = node.obligations.iter().find(|obligation| {
                !node
                    .certificates
                    .iter()
                    .any(|certificate| certificate.obligation == **obligation)
            }) {
                return Err(LineageGap::TrustedRung {
                    node: node.id,
                    justification: format!(
                        "obligation {unbacked} has no certificate reference on this rung"
                    ),
                });
            }
        }

        // (5) No faith-stamped rung. Index the module tables so we can resolve
        // each node's certificate references to real evidence/status.
        let obligations_by_id: BTreeMap<ProofId, &ProofObligation> = obligations
            .iter()
            .map(|obligation| (obligation.id, obligation))
            .collect();

        // A replayed proof authorizes a lineage EDGE only when the claim it
        // proves is itself an exact translation-validation binding for that
        // edge. An arbitrary Certified postcondition (or a TV proof minted for
        // different endpoint/transform fields) is genuine evidence for its own
        // claim but has no authority over this rung.
        for node in &self.nodes {
            let expected = node.transform_binding_formula();
            for obligation_id in &node.obligations {
                let Some(obligation) = obligations_by_id.get(obligation_id).copied() else {
                    return Err(LineageGap::TrustedRung {
                        node: node.id,
                        justification: format!(
                            "no obligation found for lineage binding {obligation_id}"
                        ),
                    });
                };
                if obligation.kind != ObligationKind::TranslationValidation {
                    return Err(LineageGap::TrustedRung {
                        node: node.id,
                        justification: format!(
                            "obligation {obligation_id} is not TranslationValidation"
                        ),
                    });
                }
                if obligation.formula.as_ref() != Some(&expected) {
                    return Err(LineageGap::TrustedRung {
                        node: node.id,
                        justification: format!(
                            "obligation {obligation_id} formula does not commit this source/target transform edge"
                        ),
                    });
                }
            }
        }

        for node in &self.nodes {
            for cert_ref in &node.certificates {
                // Resolve the referenced certificate to its actual evidence by
                // matching (obligation, prover, evidence_digest).
                let certificate: Option<&ProofCertificate> = certificates.iter().find(|c| {
                    c.obligation == cert_ref.obligation
                        && c.prover == cert_ref.prover
                        && c.evidence_digest() == cert_ref.evidence_digest
                });

                // A node referencing evidence that is not present in the module
                // table is an unbacked rung — treat as a faith gap rather than
                // silently passing.
                let Some(certificate) = certificate else {
                    return Err(LineageGap::TrustedRung {
                        node: node.id,
                        justification: format!(
                            "no certificate found for obligation {}/{} referenced by this rung",
                            cert_ref.obligation, cert_ref.prover
                        ),
                    });
                };
                let evidence = &certificate.evidence;

                // Evidence-side faith gap: an explicit "take this on faith" rung.
                if let ProofEvidence::Trusted(justification) = evidence {
                    return Err(LineageGap::TrustedRung {
                        node: node.id,
                        justification: justification.clone(),
                    });
                }

                // Status-side faith gap: a rung whose obligation is not actually
                // proven (Pending/Failed) or is taken on faith (Trusted).
                let Some(obligation) = obligations_by_id.get(&cert_ref.obligation).copied() else {
                    return Err(LineageGap::TrustedRung {
                        node: node.id,
                        justification: format!(
                            "no obligation found for certificate {}/{} referenced by this rung",
                            cert_ref.obligation, cert_ref.prover
                        ),
                    });
                };
                match obligation.status {
                    ProofStatus::Discharged | ProofStatus::Certified => {}
                    status
                    @ (ProofStatus::Trusted | ProofStatus::Failed | ProofStatus::Pending) => {
                        return Err(LineageGap::TrustedRung {
                            node: node.id,
                            justification: format!(
                                "obligation {} has non-proven status {status:?}",
                                cert_ref.obligation
                            ),
                        });
                    }
                }
                if !authority.replays_authority(obligation, certificate) {
                    return Err(LineageGap::TrustedRung {
                        node: node.id,
                        justification: format!(
                            "certificate {}/{} was not replayed by this validator; status and \
                             opaque evidence are not proof authority",
                            cert_ref.obligation, cert_ref.prover
                        ),
                    });
                }
            }
        }

        Ok(())
    }

    pub fn stable_digest(&self) -> ProofDigest {
        let mut bytes = Vec::new();
        write_u32_stable(&mut bytes, self.schema_version);

        let mut nodes = self.nodes.clone();
        nodes.sort_by_key(|node| node.id);
        write_len_stable(&mut bytes, nodes.len());
        for node in nodes {
            write_digest_stable(&mut bytes, &node.stable_digest());
        }

        let mut roots = self.roots.clone();
        roots.sort();
        write_len_stable(&mut bytes, roots.len());
        for root in roots {
            write_u32_stable(&mut bytes, root.index());
        }

        ProofDigest::sha256_domain("trust_ir.proof.lineage.manifest.v2", &bytes)
    }

    fn validate_shape(&self, errors: &mut Vec<ProofLineageError>) {
        if self.schema_version != Self::SCHEMA_VERSION {
            errors.push(ProofLineageError::UnsupportedSchemaVersion(
                self.schema_version,
            ));
        }
        if self.nodes.is_empty() {
            errors.push(ProofLineageError::EmptyManifest);
        }
        if self.roots.is_empty() {
            errors.push(ProofLineageError::EmptyRoots);
        }

        let mut node_ids = BTreeSet::new();
        let mut seen_ids = BTreeSet::new();
        for node in &self.nodes {
            if !node_ids.insert(node.id) {
                errors.push(ProofLineageError::DuplicateNodeId(node.id));
            }
            seen_ids.insert(node.id);
            validate_node_shape(node, errors);
        }

        let mut roots = BTreeSet::new();
        for root in &self.roots {
            if !roots.insert(*root) {
                errors.push(ProofLineageError::DuplicateRoot(*root));
            }
            if !seen_ids.contains(root) {
                errors.push(ProofLineageError::MissingRoot(*root));
            }
        }

        for node in &self.nodes {
            let mut deps = BTreeSet::new();
            for dep in &node.depends_on {
                if !deps.insert(*dep) {
                    errors.push(ProofLineageError::DuplicateDependency {
                        node: node.id,
                        dependency: *dep,
                    });
                }
                if *dep == node.id {
                    errors.push(ProofLineageError::Cycle { node: node.id });
                }
                if !seen_ids.contains(dep) {
                    errors.push(ProofLineageError::MissingDependency {
                        node: node.id,
                        dependency: *dep,
                    });
                }
            }
        }

        let target_by_node: BTreeMap<ProofLineageId, ProofDigest> = self
            .nodes
            .iter()
            .map(|node| (node.id, node.target_module))
            .collect();
        for node in &self.nodes {
            if node.transform.stage == ProofTransformStage::Composition {
                continue;
            }
            for dep in &node.depends_on {
                if let Some(dependency_target) = target_by_node.get(dep)
                    && *dependency_target != node.source_module
                {
                    errors.push(ProofLineageError::DependencyDigestMismatch {
                        node: node.id,
                        dependency: *dep,
                        node_source: node.source_module,
                        dependency_target: *dependency_target,
                    });
                }
            }
        }

        detect_cycles(&self.nodes, errors);
    }
}

impl Default for ProofLineageManifest {
    fn default() -> Self {
        Self::new()
    }
}

/// Module-level lineage-closure check — the CI entry point the Program CK1
/// docs name (`lineage_closed(module)`): is `module`'s proof lineage CLOSED
/// under `manifest`?
///
/// This is the thin binding of [`ProofLineageManifest::lineage_is_closed`] to
/// a [`crate::Module`]'s own proof tables (`proof_obligations` +
/// `proof_certificates`) — the tables where the evidence and statuses that the
/// manifest's [`ProofCertificateRef`]s reference actually live. The manifest
/// itself travels as a sidecar (`binary::serialize_proof_lineage` /
/// `deserialize_proof_lineage`, and `NativeVerificationBundle::lineage`), so
/// the pairing of "this module" with "this manifest" is the caller's claim;
/// this function checks that the claimed pair is closed.
///
/// Returns `Ok(())` iff every rung from source to emitted code is present,
/// connected, acyclic, and machine-backed — in particular, iff NO rung rests
/// on faith-stamped `ProofEvidence::Trusted` evidence (the zero-`Trusted`
/// flagship-lane gate; the same census
/// [`crate::Module::trusted_evidence_census`] reports). On failure, the
/// returned [`LineageGap`] names the FIRST gap.
pub fn lineage_closed(
    module: &crate::Module,
    manifest: &ProofLineageManifest,
) -> Result<(), LineageGap> {
    manifest.lineage_is_closed(&module.proof_obligations, &module.proof_certificates)
}

/// [`lineage_closed`] with an explicit evidence-replay capability.
pub fn lineage_closed_with_authority(
    module: &crate::Module,
    manifest: &ProofLineageManifest,
    authority: &dyn ProofAuthorityRechecker,
) -> Result<(), LineageGap> {
    manifest.lineage_is_closed_with_authority(
        &module.proof_obligations,
        &module.proof_certificates,
        authority,
    )
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProofLineageError {
    UnsupportedSchemaVersion(u32),
    EmptyManifest,
    EmptyRoots,
    DuplicateNodeId(ProofLineageId),
    EmptyTransformField {
        node: ProofLineageId,
        field: &'static str,
    },
    EmptyDigest {
        node: ProofLineageId,
        field: &'static str,
    },
    NonCryptographicDigest {
        node: ProofLineageId,
        field: &'static str,
    },
    MissingReplayIdentity(ProofLineageId),
    InvalidReplayIdentity {
        node: ProofLineageId,
        field: &'static str,
    },
    EmptyObligations(ProofLineageId),
    DuplicateObligation {
        node: ProofLineageId,
        obligation: ProofId,
    },
    CertificateObligationNotBound {
        node: ProofLineageId,
        obligation: ProofId,
    },
    DuplicateCertificate {
        node: ProofLineageId,
        obligation: ProofId,
        prover: String,
    },
    DuplicateCertificateIdentity {
        node: ProofLineageId,
        obligation: ProofId,
        prover: String,
    },
    MissingDependency {
        node: ProofLineageId,
        dependency: ProofLineageId,
    },
    DuplicateDependency {
        node: ProofLineageId,
        dependency: ProofLineageId,
    },
    DependencyDigestMismatch {
        node: ProofLineageId,
        dependency: ProofLineageId,
        node_source: ProofDigest,
        dependency_target: ProofDigest,
    },
    Cycle {
        node: ProofLineageId,
    },
    MissingRoot(ProofLineageId),
    DuplicateRoot(ProofLineageId),
    UnknownObligation {
        node: ProofLineageId,
        obligation: ProofId,
    },
    MissingCertificate {
        node: ProofLineageId,
        obligation: ProofId,
        prover: String,
    },
    CertificateDigestMismatch {
        node: ProofLineageId,
        obligation: ProofId,
        prover: String,
    },
}

impl core::fmt::Display for ProofLineageError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            ProofLineageError::UnsupportedSchemaVersion(version) => {
                write!(f, "unsupported proof lineage schema version {version}")
            }
            ProofLineageError::EmptyManifest => f.write_str("proof lineage manifest has no nodes"),
            ProofLineageError::EmptyRoots => f.write_str("proof lineage manifest has no roots"),
            ProofLineageError::DuplicateNodeId(id) => {
                write!(f, "duplicate proof lineage node {id}")
            }
            ProofLineageError::EmptyTransformField { node, field } => {
                write!(f, "proof lineage node {node} has empty transform {field}")
            }
            ProofLineageError::EmptyDigest { node, field } => {
                write!(f, "proof lineage node {node} has empty {field} digest")
            }
            ProofLineageError::NonCryptographicDigest { node, field } => write!(
                f,
                "proof lineage node {node} uses a non-cryptographic {field} digest"
            ),
            ProofLineageError::MissingReplayIdentity(node) => {
                write!(f, "proof lineage replay node {node} has no replay identity")
            }
            ProofLineageError::InvalidReplayIdentity { node, field } => {
                write!(
                    f,
                    "proof lineage node {node} has invalid replay identity field {field}"
                )
            }
            ProofLineageError::EmptyObligations(node) => {
                write!(f, "proof lineage node {node} binds no obligations")
            }
            ProofLineageError::DuplicateObligation { node, obligation } => {
                write!(
                    f,
                    "proof lineage node {node} repeats obligation {obligation}"
                )
            }
            ProofLineageError::CertificateObligationNotBound { node, obligation } => {
                write!(
                    f,
                    "proof lineage node {node} references certificate for unbound obligation {obligation}"
                )
            }
            ProofLineageError::DuplicateCertificate {
                node,
                obligation,
                prover,
            } => {
                write!(
                    f,
                    "proof lineage node {node} repeats certificate {obligation}/{prover}"
                )
            }
            ProofLineageError::DuplicateCertificateIdentity {
                node,
                obligation,
                prover,
            } => {
                write!(
                    f,
                    "proof lineage node {node} has multiple evidence digests for certificate {obligation}/{prover}"
                )
            }
            ProofLineageError::MissingDependency { node, dependency } => {
                write!(
                    f,
                    "proof lineage node {node} depends on missing node {dependency}"
                )
            }
            ProofLineageError::DuplicateDependency { node, dependency } => {
                write!(
                    f,
                    "proof lineage node {node} repeats dependency {dependency}"
                )
            }
            ProofLineageError::DependencyDigestMismatch {
                node,
                dependency,
                node_source,
                dependency_target,
            } => {
                write!(
                    f,
                    "proof lineage node {node} source digest {node_source} does not match dependency {dependency} target digest {dependency_target}"
                )
            }
            ProofLineageError::Cycle { node } => {
                write!(f, "proof lineage contains a cycle through node {node}")
            }
            ProofLineageError::MissingRoot(root) => {
                write!(f, "proof lineage root {root} is missing")
            }
            ProofLineageError::DuplicateRoot(root) => {
                write!(f, "proof lineage repeats root {root}")
            }
            ProofLineageError::UnknownObligation { node, obligation } => {
                write!(
                    f,
                    "proof lineage node {node} references unknown obligation {obligation}"
                )
            }
            ProofLineageError::MissingCertificate {
                node,
                obligation,
                prover,
            } => {
                write!(
                    f,
                    "proof lineage node {node} references missing certificate {obligation}/{prover}"
                )
            }
            ProofLineageError::CertificateDigestMismatch {
                node,
                obligation,
                prover,
            } => {
                write!(
                    f,
                    "proof lineage node {node} has stale certificate digest for {obligation}/{prover}"
                )
            }
        }
    }
}

impl std::error::Error for ProofLineageError {}

/// The FIRST reason a proof-lineage chain is not CLOSED in the
/// interpretation-B "completely proven" sense (see
/// [`ProofLineageManifest::lineage_is_closed`]).
///
/// A closed chain has every rung present, `depends_on`-connected from the
/// emitted-code rung(s) back to the source rung, with no faith-stamped
/// (`Trusted`) link. Each variant names exactly which of those conditions
/// failed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LineageGap {
    /// The manifest has no nodes or no roots — there is no chain to close.
    EmptyManifest,
    /// `node`'s `depends_on` names `missing`, which is not present in the
    /// manifest: a dangling edge leaves a hole in the chain.
    MissingDependency {
        node: ProofLineageId,
        missing: ProofLineageId,
    },
    /// The `depends_on` graph cycles through `node`; a cyclic "chain" never
    /// terminates at a genuine source rung.
    Cycle { node: ProofLineageId },
    /// `node` is not reachable from any root by following `depends_on`: it is
    /// an orphan rung disconnected from the emitted-code lineage (or a root
    /// that names no node).
    NotConnectedToSource { node: ProofLineageId },
    /// `node` is a faith-stamped rung: it references `Trusted` evidence (or an
    /// obligation whose status is not actually proven), so the chain rests on
    /// faith at this link rather than on machine-checkable proof.
    /// `justification` is the trusted reason / status detail.
    TrustedRung {
        node: ProofLineageId,
        justification: String,
    },
}

impl core::fmt::Display for LineageGap {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            LineageGap::EmptyManifest => {
                f.write_str("proof lineage is not closed: manifest has no rungs to walk")
            }
            LineageGap::MissingDependency { node, missing } => write!(
                f,
                "proof lineage is not closed: rung {node} depends on missing rung {missing}"
            ),
            LineageGap::Cycle { node } => write!(
                f,
                "proof lineage is not closed: dependency cycle through rung {node}"
            ),
            LineageGap::NotConnectedToSource { node } => write!(
                f,
                "proof lineage is not closed: rung {node} is not connected to the emitted-code lineage"
            ),
            LineageGap::TrustedRung {
                node,
                justification,
            } => write!(
                f,
                "proof lineage is not closed: rung {node} is faith-stamped (Trusted): {justification}"
            ),
        }
    }
}

impl std::error::Error for LineageGap {}

fn validate_node_shape(node: &ProofLineageNode, errors: &mut Vec<ProofLineageError>) {
    if node.transform.name.is_empty() {
        errors.push(ProofLineageError::EmptyTransformField {
            node: node.id,
            field: "name",
        });
    }
    if node.transform.producer.is_empty() {
        errors.push(ProofLineageError::EmptyTransformField {
            node: node.id,
            field: "producer",
        });
    }
    if node.transform.version.is_empty() {
        errors.push(ProofLineageError::EmptyTransformField {
            node: node.id,
            field: "version",
        });
    }
    if node.source_module.is_zero() {
        errors.push(ProofLineageError::EmptyDigest {
            node: node.id,
            field: "source_module",
        });
    }
    if node.source_module.algorithm != ProofDigestAlgorithm::Sha256 {
        errors.push(ProofLineageError::NonCryptographicDigest {
            node: node.id,
            field: "source_module",
        });
    }
    if node.target_module.is_zero() {
        errors.push(ProofLineageError::EmptyDigest {
            node: node.id,
            field: "target_module",
        });
    }
    if node.target_module.algorithm != ProofDigestAlgorithm::Sha256 {
        errors.push(ProofLineageError::NonCryptographicDigest {
            node: node.id,
            field: "target_module",
        });
    }
    if node.transform.stage == ProofTransformStage::Replay && node.replay.is_none() {
        errors.push(ProofLineageError::MissingReplayIdentity(node.id));
    }
    if let Some(replay) = &node.replay {
        validate_lineage_replay_identity(node.id, replay, errors);
    }
    if node.obligations.is_empty() {
        errors.push(ProofLineageError::EmptyObligations(node.id));
    }

    let mut obligations = BTreeSet::new();
    for obligation in &node.obligations {
        if !obligations.insert(*obligation) {
            errors.push(ProofLineageError::DuplicateObligation {
                node: node.id,
                obligation: *obligation,
            });
        }
    }

    let mut certificates = BTreeSet::new();
    let mut certificate_identities = BTreeSet::new();
    for cert in &node.certificates {
        if cert.evidence_digest.algorithm != ProofDigestAlgorithm::Sha256 {
            errors.push(ProofLineageError::NonCryptographicDigest {
                node: node.id,
                field: "certificate.evidence_digest",
            });
        }
        if !obligations.contains(&cert.obligation) {
            errors.push(ProofLineageError::CertificateObligationNotBound {
                node: node.id,
                obligation: cert.obligation,
            });
        }
        if !certificate_identities.insert((cert.obligation, cert.prover.clone())) {
            errors.push(ProofLineageError::DuplicateCertificateIdentity {
                node: node.id,
                obligation: cert.obligation,
                prover: cert.prover.clone(),
            });
        }
        if !certificates.insert(cert.clone()) {
            errors.push(ProofLineageError::DuplicateCertificate {
                node: node.id,
                obligation: cert.obligation,
                prover: cert.prover.clone(),
            });
        }
    }
}

fn validate_lineage_replay_identity(
    node: ProofLineageId,
    replay: &ProofReplayIdentity,
    errors: &mut Vec<ProofLineageError>,
) {
    if replay.engine.trim().is_empty() {
        errors.push(ProofLineageError::InvalidReplayIdentity {
            node,
            field: "engine",
        });
    }
    if replay.invocation.trim().is_empty() {
        errors.push(ProofLineageError::InvalidReplayIdentity {
            node,
            field: "invocation",
        });
    }
    if let Some(digest) = replay.transcript_digest {
        if digest.is_zero() {
            errors.push(ProofLineageError::InvalidReplayIdentity {
                node,
                field: "transcript_digest",
            });
        }
        if digest.algorithm != ProofDigestAlgorithm::Sha256 {
            errors.push(ProofLineageError::NonCryptographicDigest {
                node,
                field: "replay.transcript_digest",
            });
        }
    }
}

fn detect_cycles(nodes: &[ProofLineageNode], errors: &mut Vec<ProofLineageError>) {
    #[derive(Clone, Copy, PartialEq, Eq)]
    enum Mark {
        Visiting,
        Done,
    }

    fn visit(
        id: ProofLineageId,
        graph: &BTreeMap<ProofLineageId, Vec<ProofLineageId>>,
        marks: &mut BTreeMap<ProofLineageId, Mark>,
        errors: &mut Vec<ProofLineageError>,
    ) {
        match marks.get(&id).copied() {
            Some(Mark::Done) => return,
            Some(Mark::Visiting) => {
                errors.push(ProofLineageError::Cycle { node: id });
                return;
            }
            None => {}
        }

        marks.insert(id, Mark::Visiting);
        if let Some(deps) = graph.get(&id) {
            for dep in deps {
                if graph.contains_key(dep) {
                    visit(*dep, graph, marks, errors);
                }
            }
        }
        marks.insert(id, Mark::Done);
    }

    let graph: BTreeMap<ProofLineageId, Vec<ProofLineageId>> = nodes
        .iter()
        .map(|node| (node.id, node.depends_on.clone()))
        .collect();
    let mut marks = BTreeMap::new();
    for id in graph.keys().copied().collect::<Vec<_>>() {
        visit(id, &graph, &mut marks, errors);
    }
}

fn write_transform_stable(out: &mut Vec<u8>, transform: &ProofTransform) {
    write_u8_stable(
        out,
        match transform.stage {
            ProofTransformStage::Frontend => 0,
            ProofTransformStage::TrustIrLowering => 1,
            ProofTransformStage::TrustIrOptimization => 2,
            ProofTransformStage::SolverAdapter => 3,
            ProofTransformStage::Backend => 4,
            ProofTransformStage::Replay => 5,
            ProofTransformStage::Composition => 6,
            ProofTransformStage::Other => 7,
        },
    );
    write_str_stable(out, &transform.name);
    write_str_stable(out, &transform.producer);
    write_str_stable(out, &transform.version);
}

fn write_replay_stable(out: &mut Vec<u8>, replay: &ProofReplayIdentity) {
    write_str_stable(out, &replay.engine);
    write_str_stable(out, &replay.invocation);
    match &replay.transcript_digest {
        None => write_u8_stable(out, 0),
        Some(digest) => {
            write_u8_stable(out, 1);
            write_digest_stable(out, digest);
        }
    }
}

fn write_certificate_ref_stable(out: &mut Vec<u8>, cert: &ProofCertificateRef) {
    write_u32_stable(out, cert.obligation.index());
    write_str_stable(out, &cert.prover);
    write_digest_stable(out, &cert.evidence_digest);
}

#[cfg(test)]
mod closure_tests {
    use super::*;
    use crate::proof::evidence::{ProofCertificate, ProofEvidence};
    use crate::proof::obligations::{ObligationKind, ProofObligation, ProofStatus};

    struct TestSmtAuthority;

    impl ProofAuthorityRechecker for TestSmtAuthority {
        fn replays_authority(
            &self,
            obligation: &ProofObligation,
            certificate: &ProofCertificate,
        ) -> bool {
            certificate.obligation == obligation.id
                && matches!(certificate.evidence, ProofEvidence::SmtProof(_))
        }
    }

    fn digest(tag: &str) -> ProofDigest {
        ProofDigest::sha256_domain("trust_ir.test.lineage.digest.v2", tag.as_bytes())
    }

    fn transform(stage: ProofTransformStage, name: &str) -> ProofTransform {
        ProofTransform::new(stage, name, "trust-ir-test", "1.0.0")
    }

    /// A machine-backed certificate (SMT proof) for an obligation.
    fn smt_cert(obligation: ProofId) -> ProofCertificate {
        ProofCertificate {
            obligation,
            prover: "ay".into(),
            evidence: ProofEvidence::SmtProof(vec![0xde, 0xad, 0xbe, 0xef]),
        }
    }

    /// A faith-stamped certificate (manual audit) for an obligation.
    fn trusted_cert(obligation: ProofId) -> ProofCertificate {
        ProofCertificate {
            obligation,
            prover: "audit".into(),
            evidence: ProofEvidence::Trusted("hand-checked by reviewer".into()),
        }
    }

    fn discharged_obligation(id: ProofId, node: &ProofLineageNode) -> ProofObligation {
        ProofObligation::new(
            id,
            ObligationKind::TranslationValidation,
            ProofStatus::Discharged,
            "test obligation",
        )
        .with_formula(node.transform_binding_formula())
    }

    /// Build a realistic linear three-rung chain like `sign_with_lineage`:
    ///   rung 0 (Frontend, source)  -> rung 1 (TrustIrLowering) -> rung 2 (Backend, emitted)
    /// `cert_for` decides what evidence backs each rung's obligation.
    /// Returns (manifest, obligations, certificates).
    fn chain(
        cert_for: impl Fn(u32, ProofId) -> ProofCertificate,
    ) -> (
        ProofLineageManifest,
        Vec<ProofObligation>,
        Vec<ProofCertificate>,
    ) {
        let d_src = digest("source");
        let d_mid = digest("mid");
        let d_emitted = digest("emitted");

        let mut obligations = Vec::new();
        let mut certificates = Vec::new();
        let mut nodes = Vec::new();

        let stages = [
            (ProofTransformStage::Frontend, "frontend", d_src, d_mid),
            (
                ProofTransformStage::TrustIrLowering,
                "lowering",
                d_mid,
                d_emitted,
            ),
            (
                ProofTransformStage::Backend,
                "backend",
                d_emitted,
                d_emitted,
            ),
        ];

        for (i, (stage, name, source, target)) in stages.into_iter().enumerate() {
            let i = i as u32;
            let obligation = ProofId::new(i);
            let cert = cert_for(i, obligation);

            let cert_ref = cert.lineage_ref();
            certificates.push(cert);

            let mut node = ProofLineageNode::new(
                ProofLineageId::new(i),
                transform(stage, name),
                source,
                target,
            );
            node.obligations = vec![obligation];
            node.certificates = vec![cert_ref];
            if i > 0 {
                node.depends_on = vec![ProofLineageId::new(i - 1)];
            }
            obligations.push(discharged_obligation(obligation, &node));
            nodes.push(node);
        }

        let mut manifest = ProofLineageManifest::new();
        manifest.nodes = nodes;
        // The emitted-code rung (rung 2) is the root; walking depends_on goes
        // back to the source rung (rung 0).
        manifest.roots = vec![ProofLineageId::new(2)];

        (manifest, obligations, certificates)
    }

    #[test]
    fn fully_machine_backed_chain_is_closed() {
        let (manifest, obligations, certificates) = chain(|_, ob| smt_cert(ob));
        // Sanity: the chain is also structurally valid.
        assert_eq!(
            manifest.validate_against(&obligations, &certificates),
            Ok(())
        );
        assert!(matches!(
            manifest.lineage_is_closed(&obligations, &certificates),
            Err(LineageGap::TrustedRung { .. })
        ));
        assert_eq!(
            manifest.lineage_is_closed_with_authority(
                &obligations,
                &certificates,
                &TestSmtAuthority,
            ),
            Ok(())
        );
    }

    #[test]
    fn certified_contract_proof_cannot_authorize_transform_rung() {
        let (manifest, mut obligations, certificates) = chain(|_, ob| smt_cert(ob));
        // Keep the exact edge-binding formula and a replay-capable certificate;
        // only substitute an unrelated claim kind. The rung must fail closed.
        obligations[1].kind = ObligationKind::Postcondition;
        assert!(matches!(
            manifest.lineage_is_closed_with_authority(
                &obligations,
                &certificates,
                &TestSmtAuthority,
            ),
            Err(LineageGap::TrustedRung { justification, .. })
                if justification.contains("not TranslationValidation")
        ));
    }

    #[test]
    fn certificate_bound_to_another_transform_identity_cannot_be_reused() {
        let (mut manifest, obligations, certificates) = chain(|_, ob| smt_cert(ob));
        manifest.nodes[1].transform.name = "forged-lowering".to_string();
        assert!(matches!(
            manifest.lineage_is_closed_with_authority(
                &obligations,
                &certificates,
                &TestSmtAuthority,
            ),
            Err(LineageGap::TrustedRung { justification, .. })
                if justification.contains("formula does not commit")
        ));
    }

    #[test]
    fn one_trusted_rung_breaks_closure() {
        // Flip ONLY the middle rung (id 1) to Trusted evidence.
        let (manifest, obligations, certificates) = chain(|i, ob| {
            if i == 1 {
                trusted_cert(ob)
            } else {
                smt_cert(ob)
            }
        });
        match manifest.lineage_is_closed_with_authority(
            &obligations,
            &certificates,
            &TestSmtAuthority,
        ) {
            Err(LineageGap::TrustedRung {
                node,
                justification,
            }) => {
                assert_eq!(node, ProofLineageId::new(1));
                assert_eq!(justification, "hand-checked by reviewer");
            }
            other => panic!("expected TrustedRung gap, got {other:?}"),
        }
    }

    #[test]
    fn trusted_status_rung_breaks_closure() {
        // Machine evidence present, but the obligation's STATUS is not proven.
        let (manifest, mut obligations, certificates) = chain(|_, ob| smt_cert(ob));
        obligations[1].status = ProofStatus::Failed;
        match manifest.lineage_is_closed_with_authority(
            &obligations,
            &certificates,
            &TestSmtAuthority,
        ) {
            Err(LineageGap::TrustedRung { node, .. }) => {
                assert_eq!(node, ProofLineageId::new(1));
            }
            other => panic!("expected TrustedRung gap for failed status, got {other:?}"),
        }
    }

    #[test]
    fn dangling_dependency_breaks_closure() {
        let (mut manifest, obligations, certificates) = chain(|_, ob| smt_cert(ob));
        // Point the emitted rung at a nonexistent predecessor.
        manifest.nodes[2].depends_on = vec![ProofLineageId::new(99)];
        match manifest.lineage_is_closed(&obligations, &certificates) {
            Err(LineageGap::MissingDependency { node, missing }) => {
                assert_eq!(node, ProofLineageId::new(2));
                assert_eq!(missing, ProofLineageId::new(99));
            }
            other => panic!("expected MissingDependency gap, got {other:?}"),
        }
    }

    #[test]
    fn empty_manifest_is_not_closed() {
        let manifest = ProofLineageManifest::new();
        assert_eq!(
            manifest.lineage_is_closed(&[], &[]),
            Err(LineageGap::EmptyManifest)
        );
    }

    #[test]
    fn certless_rung_is_not_vacuously_closed() {
        let mut node = ProofLineageNode::new(
            ProofLineageId::new(0),
            transform(ProofTransformStage::Frontend, "frontend"),
            digest("source"),
            digest("target"),
        );
        let obligation = discharged_obligation(ProofId::new(0), &node);
        node.obligations.push(obligation.id);
        let manifest = ProofLineageManifest {
            schema_version: ProofLineageManifest::SCHEMA_VERSION,
            nodes: vec![node],
            roots: vec![ProofLineageId::new(0)],
        };

        assert!(matches!(
            manifest.lineage_is_closed(&[obligation], &[]),
            Err(LineageGap::TrustedRung { node, justification })
                if node == ProofLineageId::new(0)
                    && justification.contains("no certificate reference")
        ));
    }

    #[test]
    fn every_rung_obligation_requires_its_own_certificate_reference() {
        let (mut manifest, mut obligations, certificates) = chain(|_, ob| smt_cert(ob));
        let unbacked = ProofId::new(99);
        manifest.nodes[1].obligations.push(unbacked);
        obligations.push(discharged_obligation(unbacked, &manifest.nodes[1]));

        assert!(matches!(
            manifest.lineage_is_closed_with_authority(
                &obligations,
                &certificates,
                &TestSmtAuthority,
            ),
            Err(LineageGap::TrustedRung { node, justification })
                if node == ProofLineageId::new(1)
                    && justification.contains("obligation 99")
                    && justification.contains("no certificate reference")
        ));
    }

    #[test]
    fn closure_rejects_legacy_module_identity_without_separate_validate_call() {
        let (mut manifest, obligations, certificates) = chain(|_, ob| smt_cert(ob));
        manifest.nodes[0].source_module =
            ProofDigest::trust_ir_stable("legacy.lineage.source", b"source");

        assert!(matches!(
            manifest.lineage_is_closed_with_authority(
                &obligations,
                &certificates,
                &TestSmtAuthority,
            ),
            Err(LineageGap::TrustedRung { justification, .. })
                if justification.contains("invalid lineage manifest")
                    && justification.contains("non-cryptographic")
        ));
    }

    #[test]
    fn closure_rejects_duplicate_obligation_ids() {
        let (manifest, mut obligations, certificates) = chain(|_, ob| smt_cert(ob));
        obligations.push(obligations[0].clone());

        assert!(matches!(
            manifest.lineage_is_closed_with_authority(
                &obligations,
                &certificates,
                &TestSmtAuthority,
            ),
            Err(LineageGap::TrustedRung { justification, .. })
                if justification.contains("duplicate obligation id")
        ));
    }

    #[test]
    fn disconnected_rung_is_not_closed() {
        // Build the chain, but drop the depends_on edge from the emitted rung,
        // leaving rungs 0 and 1 unreachable from the root (rung 2).
        let (mut manifest, obligations, certificates) = chain(|_, ob| smt_cert(ob));
        manifest.nodes[2].depends_on = Vec::new();
        match manifest.lineage_is_closed(&obligations, &certificates) {
            Err(LineageGap::NotConnectedToSource { node }) => {
                // Rung 0 or 1 is now an orphan; either is a valid first report.
                assert!(node == ProofLineageId::new(0) || node == ProofLineageId::new(1));
            }
            other => panic!("expected NotConnectedToSource gap, got {other:?}"),
        }
    }
}

#[cfg(test)]
mod append_tests {
    use super::*;
    use crate::proof::evidence::{ProofCertificate, ProofEvidence};
    use crate::proof::obligations::{ObligationKind, ProofObligation, ProofStatus};

    struct TestSmtAuthority;

    impl ProofAuthorityRechecker for TestSmtAuthority {
        fn replays_authority(
            &self,
            obligation: &ProofObligation,
            certificate: &ProofCertificate,
        ) -> bool {
            certificate.obligation == obligation.id
                && matches!(certificate.evidence, ProofEvidence::SmtProof(_))
        }
    }

    fn digest(tag: &str) -> ProofDigest {
        ProofDigest::sha256_domain("trust_ir.test.lineage.append.v2", tag.as_bytes())
    }

    fn transform(stage: ProofTransformStage, name: &str) -> ProofTransform {
        ProofTransform::new(stage, name, "trust-ir-test", "1.0.0")
    }

    fn smt_cert(obligation: ProofId) -> ProofCertificate {
        ProofCertificate {
            obligation,
            prover: "ay".into(),
            evidence: ProofEvidence::SmtProof(vec![0xde, 0xad, 0xbe, 0xef]),
        }
    }

    fn discharged_obligation(id: ProofId, node: &ProofLineageNode) -> ProofObligation {
        ProofObligation::new(
            id,
            ObligationKind::TranslationValidation,
            ProofStatus::Discharged,
            "pass preserved semantics",
        )
        .with_formula(node.transform_binding_formula())
    }

    #[test]
    fn first_append_on_empty_chain_uses_base_digest() {
        let base = digest("base");
        let after = digest("after-pass-0");
        let mut manifest = ProofLineageManifest::new();
        let cert = smt_cert(ProofId::new(0));
        let id = manifest.append_pass(
            transform(ProofTransformStage::TrustIrOptimization, "const-fold"),
            base,
            after,
            vec![ProofId::new(0)],
            vec![cert.lineage_ref()],
        );
        assert_eq!(id, ProofLineageId::new(0));
        assert_eq!(manifest.nodes.len(), 1);
        assert_eq!(manifest.nodes[0].source_module, base);
        assert_eq!(manifest.nodes[0].target_module, after);
        assert!(manifest.nodes[0].depends_on.is_empty());
        assert_eq!(manifest.roots, vec![id]);
        assert_eq!(manifest.validate(), Ok(()));
    }

    #[test]
    fn three_appended_passes_chain_and_validate() {
        let base = digest("base");
        let digests = [digest("d1"), digest("d2"), digest("d3")];
        let passes = ["const-fold", "dce", "inline"];

        let mut manifest = ProofLineageManifest::new();
        let mut obligations = Vec::new();
        let mut certificates = Vec::new();
        for (i, (name, target)) in passes.iter().zip(digests).enumerate() {
            let obligation = ProofId::new(i as u32);
            let cert = smt_cert(obligation);
            let cert_ref = cert.lineage_ref();
            certificates.push(cert);
            let id = manifest.append_pass(
                transform(ProofTransformStage::TrustIrOptimization, name),
                base,
                target,
                vec![obligation],
                vec![cert_ref],
            );
            assert_eq!(id, ProofLineageId::new(i as u32));
            obligations.push(discharged_obligation(
                obligation,
                manifest.nodes.last().expect("just appended"),
            ));
        }

        // The helper threaded the digests: each source is the previous target
        // (the base for the first), each node depends on its predecessor, and
        // only the tip is a root.
        assert_eq!(manifest.nodes[0].source_module, base);
        assert_eq!(manifest.nodes[1].source_module, digests[0]);
        assert_eq!(manifest.nodes[2].source_module, digests[1]);
        assert_eq!(manifest.nodes[2].depends_on, vec![ProofLineageId::new(1)]);
        assert_eq!(manifest.roots, vec![ProofLineageId::new(2)]);

        // No hand-threading was needed for the checks the validator enforces.
        assert_eq!(manifest.validate(), Ok(()));
        assert_eq!(
            manifest.validate_against(&obligations, &certificates),
            Ok(())
        );
        assert_eq!(
            manifest.lineage_is_closed_with_authority(
                &obligations,
                &certificates,
                &TestSmtAuthority,
            ),
            Ok(())
        );
    }

    #[test]
    fn mis_threaded_chain_still_fails_validate() {
        // The helper eases construction only — a chain whose digests are
        // tampered after the fact must still be rejected.
        let base = digest("base");
        let mut manifest = ProofLineageManifest::new();
        for (i, target) in ["t0", "t1", "t2"].iter().enumerate() {
            let obligation = ProofId::new(i as u32);
            manifest.append_pass(
                transform(ProofTransformStage::TrustIrOptimization, "pass"),
                base,
                digest(target),
                vec![obligation],
                vec![smt_cert(obligation).lineage_ref()],
            );
        }
        manifest.nodes[1].source_module = digest("not-the-predecessor-target");
        let errors = manifest.validate().expect_err("mis-threaded chain");
        assert!(
            errors.iter().any(|e| matches!(
                e,
                ProofLineageError::DependencyDigestMismatch {
                    node,
                    dependency,
                    ..
                } if *node == ProofLineageId::new(1) && *dependency == ProofLineageId::new(0)
            )),
            "expected DependencyDigestMismatch: {errors:?}"
        );
    }

    #[test]
    fn append_pass_finds_tip_of_out_of_order_hand_built_chain() {
        // A hand-built single chain whose nodes are NOT in push order (the
        // tip was pushed first): append must chain onto the true tip (the
        // declared root / unique terminal node), not `nodes.last()`.
        let mut manifest = ProofLineageManifest::new();
        // tip: #1 (a <- b), pushed FIRST
        let mut tip = ProofLineageNode::new(
            ProofLineageId::new(1),
            transform(ProofTransformStage::TrustIrOptimization, "dce"),
            digest("a-out"),
            digest("b-out"),
        );
        tip.obligations = vec![ProofId::new(1)];
        tip.certificates = vec![smt_cert(ProofId::new(1)).lineage_ref()];
        tip.depends_on = vec![ProofLineageId::new(0)];
        manifest.nodes.push(tip);
        // ancestor: #0 (base -> a), pushed LAST
        let mut first = ProofLineageNode::new(
            ProofLineageId::new(0),
            transform(ProofTransformStage::TrustIrOptimization, "const-fold"),
            digest("base"),
            digest("a-out"),
        );
        first.obligations = vec![ProofId::new(0)];
        first.certificates = vec![smt_cert(ProofId::new(0)).lineage_ref()];
        manifest.nodes.push(first);
        manifest.roots = vec![ProofLineageId::new(1)];

        let id = manifest.append_pass(
            transform(ProofTransformStage::TrustIrOptimization, "inline"),
            digest("unused-base"),
            digest("c-out"),
            vec![ProofId::new(2)],
            vec![smt_cert(ProofId::new(2)).lineage_ref()],
        );
        let node = manifest.nodes.iter().find(|n| n.id == id).unwrap();
        // Chained onto the TIP (#1, target b-out), not nodes.last() (#0).
        assert_eq!(node.depends_on, vec![ProofLineageId::new(1)]);
        assert_eq!(node.source_module, digest("b-out"));
        assert_eq!(manifest.roots, vec![id]);
        assert_eq!(manifest.validate(), Ok(()));
    }

    #[test]
    #[should_panic(expected = "ambiguous chain tip")]
    fn append_pass_panics_on_parallel_chains() {
        // Two parallel chains (two roots / two terminal nodes): silently
        // picking one would attest the pass ran on the wrong chain's module
        // in a way validate() cannot detect, so append_pass refuses.
        let mut manifest = ProofLineageManifest::new();
        for (i, (src, tgt)) in [("base-a", "a-out"), ("base-b", "b-out")]
            .iter()
            .enumerate()
        {
            let mut node = ProofLineageNode::new(
                ProofLineageId::new(i as u32),
                transform(ProofTransformStage::TrustIrOptimization, "pass"),
                digest(src),
                digest(tgt),
            );
            node.obligations = vec![ProofId::new(i as u32)];
            node.certificates = vec![smt_cert(ProofId::new(i as u32)).lineage_ref()];
            manifest.nodes.push(node);
            manifest.roots.push(ProofLineageId::new(i as u32));
        }
        let _ = manifest.append_pass(
            transform(ProofTransformStage::TrustIrOptimization, "inline"),
            digest("unused"),
            digest("c-out"),
            vec![ProofId::new(2)],
            vec![smt_cert(ProofId::new(2)).lineage_ref()],
        );
    }
}
