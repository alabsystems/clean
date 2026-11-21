// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Original direct check of an independently constructed concrete-byte equation.

use super::{
    expected_conjunction, BoolBodyRefusal, BoolPacket, BoolSubject, CheckedBoolOrigin,
    CheckedUnboundBoolMathematics,
};
use crate::{semr_model::SemrModelContext, ReferenceBase};
use clean_kernel::{EnvDigest, Environment};

/// The concrete reader authenticates the original seven model roots. Its
/// proof result is scoped to the literal bytes supplied in its subject.
pub struct UnboundBoolMathematicsContext {
    model: SemrModelContext,
}

const MODEL_ROOTS: [&str; 7] = [
    "SemR.runBlob",
    "SemR.Val",
    "SemR.Out",
    "SemR.DErr",
    "Bool.and",
    "Eq",
    "List",
];

impl UnboundBoolMathematicsContext {
    pub fn from_reference_base(base: ReferenceBase) -> Result<Self, BoolBodyRefusal> {
        let model = SemrModelContext::from_reference_base(
            base,
            &MODEL_ROOTS,
            &["SemR.BoolBody.checked_blob"],
        )?;
        Ok(Self { model })
    }

    pub fn digest(&self) -> EnvDigest {
        self.model.kernel().env_digest()
    }

    /// Independently FULL-replay the fixed source model under the unchanged
    /// reference policy, then compare exact complete reconstructed declarations,
    /// families, recursor rules and quotient records. Both sides undergo the
    /// same original admission policy; no caller mode or record is normalized.
    /// The checked fixed model is cached once per immutable context/batch, never
    /// replayed by `check` per function. Input digests are only cache identity
    /// after a genuine completion and exact comparison, not model authority.
    /// The Trust owner must still authenticate the fixed original source bytes.
    pub fn check_model_source(&self, original: &Environment) -> Result<(), BoolBodyRefusal> {
        self.model.check_model_source(original).map_err(Into::into)
    }

    /// Read-only kernel check of the exact universally quantified execution
    /// equation. Malformed bytes cannot obtain a useful vacuous decoder premise:
    /// the conclusion itself demands successful decode and the actual return.
    pub fn check(
        &self,
        expected: &BoolSubject,
        packet: &BoolPacket,
    ) -> Result<CheckedUnboundBoolMathematics, BoolBodyRefusal> {
        if expected.function != packet.subject.function
            || expected.module.bytes != packet.subject.module.bytes
            || packet.context != self.digest()
        {
            return Err(BoolBodyRefusal::SubjectMismatch);
        }
        let bytes = expected
            .module
            .concrete
            .get_or_init(|| crate::semr_model::bytes(expected.module.bytes()));
        let claim = expected_conjunction(bytes.clone(), expected.function);
        self.model
            .kernel()
            .check_closed_term(&claim, &packet.returned)
            .map_err(BoolBodyRefusal::Proof)?;
        Ok(CheckedUnboundBoolMathematics {
            subject: expected.clone(),
            context: self.digest(),
            claim,
            proof: packet.returned.clone(),
            origin: CheckedBoolOrigin::Direct,
        })
    }
}
