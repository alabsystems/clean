// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

impl Scratch<'_> {
    pub(super) fn embedded<O: ExecutionObserver>(
        &self,
        bundle: &NativeVerificationBundle,
        work: &mut Work,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        for request in &bundle.requests {
            admit(session, site, 2, 0)?;
            let id = request.id();
            for obligation in request.obligations() {
                admit(session, site, 1, 0)?;
                self.embedded_one(bundle, id, *obligation, work, session, site)?;
            }
        }
        Ok(())
    }

    fn embedded_one<O: ExecutionObserver>(
        &self,
        bundle: &NativeVerificationBundle,
        request: NativeRequestId,
        obligation: ProofId,
        work: &mut Work,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        if !member(&self.mapped, &obligation, session, site)? {
            work.fixed_error(
                || E::MissingObligationSource {
                    request,
                    obligation,
                },
                session,
                site,
            )?;
        }
        let mut found = None;
        for candidate in &bundle.module.proof_obligations {
            admit(session, site, 1, 0)?;
            if candidate.id == obligation {
                found = Some(candidate);
                break;
            }
        }
        let Some(proof) = found else {
            return Ok(());
        };
        admit(session, site, 1, 0)?;
        let Some(embedded) = &proof.source else {
            return work.fixed_error(
                || E::MissingEmbeddedObligationSource {
                    request,
                    obligation,
                },
                session,
                site,
            );
        };
        for (field, value) in [
            ("source_id", embedded.source_id.as_str()),
            ("assertion_id", embedded.assertion_id.as_str()),
        ] {
            admit(session, site, 1, 0)?;
            if !text::identity(value, true, session, site)? {
                work.fixed_error(
                    || E::InvalidEmbeddedObligationSource {
                        request,
                        obligation,
                        field,
                    },
                    session,
                    site,
                )?;
            }
        }
        admit(session, site, 1, 0)?;
        if let Some(range) = embedded.range {
            embedded_range(bundle, request, obligation, range, work, session, site)?;
        }
        embedded_public(
            bundle,
            request,
            obligation,
            embedded.public.as_ref(),
            work,
            session,
            site,
        )
    }
}

fn embedded_public<O: ExecutionObserver>(
    bundle: &NativeVerificationBundle,
    request: NativeRequestId,
    obligation: ProofId,
    public: Option<&crate::proof::PublicObligationIdentity>,
    work: &mut Work,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R {
    admit(session, site, 1, 0)?;
    let Some(public) = public else {
        return work.fixed_error(
            || E::MissingEmbeddedPublicObligationIdentity {
                request,
                obligation,
            },
            session,
            site,
        );
    };
    if !text::public_id(&public.obligation_id, session, site)? {
        work.fixed_error(
            || E::InvalidEmbeddedObligationSource {
                request,
                obligation,
                field: "public.obligation_id",
            },
            session,
            site,
        )?;
    }
    admit(session, site, 1, 0)?;
    if public.semantic_digest.algorithm != ProofDigestAlgorithm::Sha256 {
        work.fixed_error(
            || E::InvalidEmbeddedObligationSource {
                request,
                obligation,
                field: "public.semantic_digest.algorithm",
            },
            session,
            site,
        )?;
    }
    admit(session, site, 32, 0)?;
    if public.semantic_digest.is_zero() {
        work.fixed_error(
            || E::InvalidEmbeddedObligationSource {
                request,
                obligation,
                field: "public.semantic_digest",
            },
            session,
            site,
        )?;
    }
    if let Some(sidecar) = source(bundle, obligation, session, site)?
        && !text_equal(
            &sidecar.public_obligation_id,
            &public.obligation_id,
            session,
            site,
        )?
    {
        work.public_mismatch(
            request,
            obligation,
            &sidecar.public_obligation_id,
            &public.obligation_id,
            session,
            site,
        )?;
    }
    Ok(())
}

fn source<'a, O: ExecutionObserver>(
    bundle: &'a NativeVerificationBundle,
    obligation: ProofId,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Option<&'a NativeObligationSource>> {
    for source in &bundle.compiler_facts.obligation_sources {
        admit(session, site, 1, 0)?;
        if source.obligation == obligation {
            return Ok(Some(source));
        }
    }
    Ok(None)
}

fn embedded_range<O: ExecutionObserver>(
    bundle: &NativeVerificationBundle,
    request: NativeRequestId,
    obligation: ProofId,
    range: crate::proof::ProofObligationSourceRange,
    work: &mut Work,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R {
    admit(session, site, 6, 0)?;
    if range.file as usize >= bundle.module.files.len() {
        work.fixed_error(
            || E::InvalidEmbeddedObligationSource {
                request,
                obligation,
                field: "range.file",
            },
            session,
            site,
        )?;
    }
    if range.start_line == 0 || range.end_line == 0 {
        work.fixed_error(
            || E::InvalidEmbeddedObligationSource {
                request,
                obligation,
                field: "range.line",
            },
            session,
            site,
        )?;
    }
    if (range.end_line, range.end_col) < (range.start_line, range.start_col) {
        work.fixed_error(
            || E::InvalidEmbeddedObligationSource {
                request,
                obligation,
                field: "range.order",
            },
            session,
            site,
        )?;
    }
    if let Some(sidecar) = source(bundle, obligation, session, site)? {
        admit(session, site, 1, 0)?;
        if let Some(expected) = sidecar.span {
            admit(session, site, 4, size_of::<SourceSpan>())?;
            let actual = SourceSpan {
                file: range.file,
                line: range.start_line,
                col: range.start_col,
            };
            if actual != expected {
                work.fixed_error(
                    || E::EmbeddedObligationSourceSpanMismatch {
                        request,
                        obligation,
                        expected,
                        actual,
                    },
                    session,
                    site,
                )?;
            }
        }
    }
    Ok(())
}
