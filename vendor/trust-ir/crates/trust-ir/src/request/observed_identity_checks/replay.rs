// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
impl State {
    pub(super) fn replay<O: ExecutionObserver>(
        &mut self,
        request: NativeRequestId,
        suite: Suite,
        p: &ProofReplayIdentity,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        self.normal(&p.engine, w)?;
        if w.blank(&p.engine)? {
            self.fixed(
                || E::InvalidReplayIdentity {
                    request,
                    field: "engine",
                },
                w,
            )?;
        }
        w.admit(2, size_of::<Option<&str>>() + size_of::<bool>())?;
        if let Some(family) = suite.canonical_family()
            && !self.canonical.is_empty()
            && !self.family(family, w)?
        {
            self.named(&p.engine, Kind::Replay(request, suite), w)?;
        }
        if w.blank(&p.invocation)? {
            self.fixed(
                || E::InvalidReplayIdentity {
                    request,
                    field: "invocation",
                },
                w,
            )?;
        }
        w.admit(40, size_of::<Option<crate::ProofDigest>>())?;
        match p.transcript_digest {
            Some(d) if d.is_zero() => self.fixed(
                || E::InvalidReplayIdentity {
                    request,
                    field: "transcript_digest",
                },
                w,
            )?,
            Some(d) if d.algorithm != ProofDigestAlgorithm::Sha256 => self.fixed(
                || E::InvalidReplayIdentity {
                    request,
                    field: "transcript_digest.algorithm",
                },
                w,
            )?,
            Some(_) => {}
            None => self.fixed(|| E::MissingReplayTranscriptDigest(request), w)?,
        }
        Ok(())
    }
}
