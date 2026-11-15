// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The BOUND half of the TV minter ([`super`]): the bound entry point, the
//! inputs a bound certificate is populated from, and the license's evidence
//! oracle. The judgment, the payload and the license stamping stay in the
//! minter; this module only states what a bound certificate names.
//!
//! # Certificate binding (roadmap WS6.7(b), trust-ir WS1.12a)
//!
//! `certify_backend_translation_bound_in_environment` mints every certificate with a
//! `CertificateBinding`: the digest of the anchor environment the equation was
//! judged in, the digest of the statement the kernel checked, the source
//! declaration and its closure digest, and the name-sorted callee link
//! symbols — each of which trust-ir's re-checker recomputes and compares
//! (`CertificateBindingMismatch { field }` on any difference), except `source`,
//! which is a carrier until WS1.13. A binding that cannot be populated is a
//! SKIP, never a partial row. It is the shipping default
//! ([`crate::emit_trust_ir::TrustIrConfig::bind_certificates`]): the pinned
//! trust-ir carries a binding on the wire (the certificate-binding version,
//! v61), so a bound module is a `.tmbc` / `trustir-bin` artifact like any
//! other.
//!
//! # License evidence (roadmap WS6.7(b), trust-ir WS1.12(c))
//!
//! Every `Gated` body this minter licenses carries `GateEvidence { obligation,
//! body_digest }`: the `Certified` TV obligation it rests on, and
//! `Module::function_body_digest` of the body the kernel judged. trust-ir
//! re-checks both on every lane (`GatedEvidenceMismatch`: the row must be this
//! function's Certified TV row, and the digest must recompute), so a license
//! transplanted onto another function, or left on a body edited after the
//! mint, is refused. A body with no digest is SKIPPED — there is no `Gated`
//! without evidence on any path of this minter.

use super::*;

/// [`certify_backend_translation`], minting BOUND certificates (roadmap
/// WS6.7(b)): every certificate carries a [`CertificateBinding`] that names
///
/// * `environment_digest` — [`kernel_environment_digest`] of the anchor
///   environment the kernel judged the equation in
///   ([`tv_anchor_environment`], BEFORE the theorem is declared);
/// * `statement_digest` — [`clean_cic_statement_digest`] of the statement the
///   kernel checked;
/// * `source` — `source_of(name)`: the source declaration and the closure
///   digest (`clean_kernel::Environment::closure_digest`) of the environment
///   its comparand (`originals[name]`) was read from. It is asked ON DEMAND,
///   only for a decl the kernel has just certified, so no closure is digested
///   for a decl that is skipped or refused first; `None` means no identity was
///   supplied and `Some(Err)` names why it cannot be stated;
/// * `callees` — the name-sorted callee link symbols the statement quantifies
///   over; `origin_module = None` (minted in the module that carries it).
///
/// Its lineage is the symbol-keyed v8 form
/// ([`clean_cic_lineage_digest_v8`]), which folds the binding in and survives
/// id renumbering. A decl whose binding cannot be populated — no source
/// identity, an `Err` one, or a digest that cannot be stated — is still JUDGED
/// (a miscompile is REFUSED, exactly as on the unbound path) and then SKIPPED
/// with the reason: never a partial binding, never an unbound certificate on
/// this path, and never a `Gated` body without its certificate and evidence.
///
/// The shipping default ([`crate::emit_trust_ir::TrustIrConfig::bind_certificates`]):
/// the pinned trust-ir writes a binding in every format, the binary one at
/// its certificate-binding version (v61).
#[cfg(test)]
#[must_use]
pub(crate) fn certify_backend_translation_bound(
    module: &mut Module,
    originals: &[(String, Expr)],
    source_of: &dyn Fn(&str) -> Option<Result<SourceDefinitionRef, String>>,
) -> TvMintReport {
    certify_with(module, originals, Some(source_of), None)
}

/// Bound mint using the same original environment as its source identity.
pub(crate) fn certify_backend_translation_bound_in_environment(
    module: &mut Module,
    originals: &[(String, Expr)],
    source_of: &dyn Fn(&str) -> Option<Result<SourceDefinitionRef, String>>,
    environment: &Environment,
) -> TvMintReport {
    certify_with(module, originals, Some(source_of), Some(environment))
}

/// What a BOUND mint needs besides each decl's own statement: the source
/// identity of each decl, on demand, and the digest of the run's anchor
/// environment, taken at most once per run by the first certificate that
/// needs it.
pub(super) struct BindingInputs<'a> {
    pub(super) source_of: &'a dyn Fn(&str) -> Option<Result<SourceDefinitionRef, String>>,
    pub(super) environment_digest: &'a std::cell::OnceCell<Result<ProofDigest, String>>,
}

/// Populate a bound certificate's [`CertificateBinding`] for `name`, or name
/// why it cannot be: the source identity (asked of the caller now, for a decl
/// the kernel has certified), the statement digest taken before the judgment,
/// the run's anchor-environment digest (taken once, on first need), and the
/// name-sorted callee symbols. Any missing part is an `Err` — the decl is
/// SKIPPED, never bound partially.
pub(super) fn bound_binding(
    inputs: &BindingInputs<'_>,
    anchor: &Environment,
    name: &str,
    statement_digest: Result<ProofDigest, String>,
    callees: &[(String, usize)],
) -> Result<CertificateBinding, String> {
    let source = match (inputs.source_of)(name) {
        None => {
            return Err(
                "bound mint: no source-definition identity (declaration + closure digest) was \
                 supplied for this decl, so its certificate binding cannot be populated — never \
                 a partial binding"
                    .to_string(),
            )
        }
        Some(Err(reason)) => {
            return Err(format!(
                "bound mint: the source-definition identity cannot be stated (the closure \
                 digest: {reason}), so the certificate binding cannot be populated — never a \
                 partial binding"
            ))
        }
        Some(Ok(source)) => source,
    };
    let statement_digest = statement_digest.map_err(|reason| {
        format!("bound mint: the translation statement has no digest ({reason})")
    })?;
    let environment_digest = inputs
        .environment_digest
        .get_or_init(|| kernel_environment_digest(anchor))
        .clone()
        .map_err(|reason| {
            format!(
                "bound mint: the anchor environment has no digest ({reason}), so no certificate \
                 binding can be populated — fail-closed"
            )
        })?;
    let mut binding = CertificateBinding::new(environment_digest, statement_digest);
    binding.source = Some(source);
    binding.callees = callees.iter().map(|(callee, _)| callee.clone()).collect();
    Ok(binding)
}

/// TEST ORACLE: the license this minter stamps on `fid` once it certified it
/// — `Gated { clean-kernel-tv }` with the evidence re-derived from the module
/// as it stands (the one `Certified` TV obligation scoped to `fid`, and
/// `Module::function_body_digest` of its body). `None` when there is no such
/// single row or no digest. Tests compare a minted body's `body_gate` against
/// it, so a license whose evidence would not re-check never compares equal.
#[cfg(test)]
pub(crate) fn kernel_tv_gate(module: &Module, fid: FuncId) -> Option<BodyGate> {
    let mut rows = module.proof_obligations.iter().filter(|o| {
        o.function == Some(fid)
            && o.kind == ObligationKind::TranslationValidation
            && o.status == ProofStatus::Certified
    });
    let (Some(row), None) = (rows.next(), rows.next()) else {
        return None;
    };
    Some(BodyGate::Gated {
        authority: CLEAN_KERNEL_TV_AUTHORITY.to_string(),
        evidence: Some(GateEvidence {
            obligation: row.id,
            body_digest: module.function_body_digest(fid).ok()?,
        }),
    })
}
