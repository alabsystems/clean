// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
use crate::{ProofLineageNode, ProofTransform, ProofTransformStage};

impl NativeCompilerFacts {
    /// Serialize and hash the actual canonical fields under the caller's
    /// existing observation session. This grants no validation authority.
    pub fn stable_digest_observed<O: ExecutionObserver>(
        &self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> Result<ProofDigest> {
        digest(session, site, "trust_ir.native.compiler.facts.v5", |out| {
            write_compiler_facts(out, self)
        })
    }
}

impl NativeVerificationRequest {
    /// Canonical identity only; success does not validate a request.
    pub fn stable_digest_observed<O: ExecutionObserver>(
        &self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> Result<ProofDigest> {
        digest(
            session,
            site,
            "trust_ir.native.verification.request.v2",
            |out| write_native_request(out, self),
        )
    }
}

impl NativeEvidenceBundle {
    /// Canonical identity only; success does not authenticate evidence.
    pub fn stable_digest_observed<O: ExecutionObserver>(
        &self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> Result<ProofDigest> {
        digest(session, site, "trust_ir.native.evidence.bundle.v2", |out| {
            write_native_evidence_bundle(out, self)
        })
    }
}

impl NativeReplayAtom {
    /// Recompute the actual payload identity without accepting its stored digest.
    pub fn expected_payload_digest_observed<O: ExecutionObserver>(
        &self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> Result<ProofDigest> {
        digest(
            session,
            site,
            "trust_ir.native.replay.atom.payload.v2",
            |out| {
                write_replay_atom_kind(out, self.kind)?;
                write_proof_formula(out, &self.formula)
            },
        )
    }
}

impl ProofLineageNode {
    /// Canonical identity only, not lineage closure or certificate acceptance.
    pub fn stable_digest_observed<O: ExecutionObserver>(
        &self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> Result<ProofDigest> {
        digest(session, site, "trust_ir.proof.lineage.node.v2", |out| {
            write_u32(out, self.id.index())?;
            write_transform(out, &self.transform)?;
            write_digest(out, &self.source_module)?;
            write_digest(out, &self.target_module)?;
            write_proof_ids(out, &self.obligations)?;
            write_certificate_refs(out, &self.certificates)?;
            match &self.replay {
                None => write_u8(out, 0)?,
                Some(replay) => {
                    write_u8(out, 1)?;
                    write_lineage_replay(out, replay)?;
                }
            }
            write_lineage_ids(out, &self.depends_on)
        })
    }
}

impl ProofLineageManifest {
    /// Canonical identity only; no graph or proof validation is implied.
    pub fn stable_digest_observed<O: ExecutionObserver>(
        &self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> Result<ProofDigest> {
        digest(session, site, "trust_ir.proof.lineage.manifest.v2", |out| {
            write_u32(out, self.schema_version)?;
            write_sorted(
                &self.nodes,
                out,
                |a, b, out| {
                    out.poll()?;
                    Ok(a.id.cmp(&b.id))
                },
                |node, out| {
                    let child = node.stable_digest_observed(out.session, out.site)?;
                    write_digest(out, &child)
                },
            )?;
            write_lineage_ids(out, &self.roots)
        })
    }
}

impl NativeVerificationBundle {
    /// Traverse the complete existing bundle digest preimage. The embedded
    /// module is represented by its stored digest, exactly as in `stable_digest`;
    /// this API neither recomputes module wire identity nor validates authority.
    pub fn stable_digest_observed<O: ExecutionObserver>(
        &self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> Result<ProofDigest> {
        digest(
            session,
            site,
            "trust_ir.native.verification.bundle.v8",
            |out| {
                write_u32(out, self.schema_version)?;
                write_bundle_producer(out, self.producer)?;
                write_adapter_input(out, &self.input)?;
                write_bundle_provenance(out, &self.provenance)?;
                write_serialization_policy(out, &self.serialization)?;
                write_diagnostics_policy(out, &self.diagnostics)?;
                write_digest(out, &self.trust_ir_module_digest)?;
                let compiler = self
                    .compiler_facts
                    .stable_digest_observed(out.session, out.site)?;
                write_digest(out, &compiler)?;
                let lineage = self.lineage.stable_digest_observed(out.session, out.site)?;
                write_digest(out, &lineage)?;
                write_sorted(
                    &self.requests,
                    out,
                    |a, b, out| {
                        out.poll()?;
                        Ok((a.id(), native_request_variant_tag(a))
                            .cmp(&(b.id(), native_request_variant_tag(b))))
                    },
                    |request, out| {
                        let child = request.stable_digest_observed(out.session, out.site)?;
                        write_digest(out, &child)
                    },
                )?;
                write_sorted(
                    &self.evidence_bundles,
                    out,
                    |a, b, out| {
                        out.poll()?;
                        Ok((
                            a.request(),
                            native_evidence_bundle_variant_tag(a),
                            native_evidence_bundle_mode_tag(a),
                        )
                            .cmp(&(
                                b.request(),
                                native_evidence_bundle_variant_tag(b),
                                native_evidence_bundle_mode_tag(b),
                            )))
                    },
                    |evidence, out| {
                        let child = evidence.stable_digest_observed(out.session, out.site)?;
                        write_digest(out, &child)
                    },
                )
            },
        )
    }
}

fn write_transform<O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    transform: &ProofTransform,
) -> Result {
    write_u8(
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
    )?;
    write_str(out, &transform.name)?;
    write_str(out, &transform.producer)?;
    write_str(out, &transform.version)
}

fn write_lineage_replay<O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    replay: &ProofReplayIdentity,
) -> Result {
    write_str(out, &replay.engine)?;
    write_str(out, &replay.invocation)?;
    write_option_digest(out, replay.transcript_digest)
}
