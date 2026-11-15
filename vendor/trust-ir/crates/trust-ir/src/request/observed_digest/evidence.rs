// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Exact evidence identity bytes, never evidence replay or authority.
use super::*;
use crate::proof::{CertificateBinding, CleanCicKernelRecheck, ProofEvidence};
#[cfg(test)]
mod tests;

impl ProofCertificate {
    /// Hash the actual complete evidence preimage under the original session.
    /// Opaque theorem/island bytes remain identity data; none is replayed here.
    pub fn evidence_digest_observed<O: ExecutionObserver>(
        &self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> Result<ProofDigest> {
        digest(session, site, "trust_ir.proof.evidence.v2", |out| {
            write_evidence(out, &self.evidence)
        })
    }
    /// Exact ordinary certificate identity, with no validation/authority grant.
    pub fn stable_digest_observed<O: ExecutionObserver>(
        &self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> Result<ProofDigest> {
        let evidence = self.evidence_digest_observed(session, site)?;
        digest(session, site, "trust_ir.proof.certificate.v2", |out| {
            write_u32(out, self.obligation.index())?;
            write_str(out, &self.prover)?;
            write_digest(out, &evidence)
        })
    }
}
fn bytes<O: ExecutionObserver>(out: &mut Writer<'_, '_, O>, data: &[u8]) -> Result {
    write_len(out, data.len())?;
    out.append(data)
}
fn write_evidence<O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    evidence: &ProofEvidence,
) -> Result {
    out.poll()?;
    match evidence {
        ProofEvidence::SmtProof(data) => {
            write_u8(out, 0)?;
            bytes(out, data)?;
        }
        ProofEvidence::LeanProof(term) => {
            write_u8(out, 1)?;
            write_str(out, term)?;
        }
        ProofEvidence::KaniHarness(name) => {
            write_u8(out, 2)?;
            write_str(out, name)?;
        }
        ProofEvidence::GammaCrownBound {
            epsilon,
            verified_layers,
        } => {
            write_u8(out, 3)?;
            out.append(&epsilon.to_bits().to_le_bytes())?;
            write_u32(out, *verified_layers)?;
        }
        ProofEvidence::TranslationValidation {
            rule_name,
            smt_hash,
        } => {
            write_u8(out, 4)?;
            write_str(out, rule_name)?;
            out.append(smt_hash)?;
        }
        ProofEvidence::Trusted(reason) => {
            write_u8(out, 5)?;
            write_str(out, reason)?;
        }
        ProofEvidence::InheritedFromCallee {
            callee,
            obligation,
            external,
        } => {
            write_u8(out, if external.is_some() { 8 } else { 6 })?;
            write_u32(out, callee.index())?;
            write_u32(out, obligation.index())?;
            if let Some(external) = external {
                write_u32(out, external.module.index())?;
                write_str(out, &external.symbol)?;
                write_option_u32(out, external.obligation.map(|id| id.index()))?;
            }
        }
        ProofEvidence::CleanCic {
            term,
            context,
            lineage,
            kernel_recheck,
        } => {
            write_u8(out, 7)?;
            bytes(out, term)?;
            bytes(out, context)?;
            write_digest(out, lineage)?;
            match kernel_recheck {
                None => write_u8(out, 0)?,
                Some(recheck) => {
                    write_u8(out, 1)?;
                    write_recheck(out, recheck)?;
                }
            }
        }
    }
    Ok(())
}
fn write_recheck<O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    recheck: &CleanCicKernelRecheck,
) -> Result {
    write_str(out, &recheck.module)?;
    write_len(out, recheck.theorems.len())?;
    for name in &recheck.theorems {
        out.poll()?;
        write_str(out, name)?;
    }
    write_str(out, &recheck.anchor)?;
    write_len(out, recheck.allowed_axioms.len())?;
    for axiom in &recheck.allowed_axioms {
        out.poll()?;
        write_str(out, axiom)?;
    }
    // Deliberately no absent tail byte: preserve all old unbound preimages.
    if let Some(binding) = &recheck.binding {
        write_u8(out, 1)?;
        write_binding(out, binding)?;
    }
    Ok(())
}
fn write_binding<O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    binding: &CertificateBinding,
) -> Result {
    write_digest(out, &binding.environment_digest)?;
    write_digest(out, &binding.statement_digest)?;
    write_option_digest(out, binding.origin_module)?;
    match &binding.source {
        None => write_u8(out, 0)?,
        Some(source) => {
            write_u8(out, 1)?;
            write_str(out, &source.decl)?;
            write_digest(out, &source.closure_digest)?;
        }
    }
    write_len(out, binding.callees.len())?;
    for callee in &binding.callees {
        out.poll()?;
        write_str(out, callee)?;
    }
    // Deliberately no absent island byte: this was an additive optional tail.
    if let Some(island) = &binding.environment {
        write_u8(out, 1)?;
        bytes(out, &island.declarations)?;
        write_digest(out, &island.digest)?;
    }
    Ok(())
}
