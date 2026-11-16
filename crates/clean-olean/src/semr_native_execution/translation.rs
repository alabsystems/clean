//! Exact original question and actual emitted VC, in the existing unbound model.
//! The VC's proposed JSON is untrusted data: its exact byte encoding, typed
//! decoding and total evaluation are premises checked inside the fixed goal.
use super::{
    bindings_quote, subject_arguments, NativeExecutionBinding, NativeExecutionRefusal,
    NativeExecutionSubject, MODEL_ROOTS,
};
use crate::semr_model::{bytes, c, SemrModelContext};
use crate::ReferenceBase;
use clean_kernel::{EnvDigest, Environment, Expr};
use std::sync::Arc;

/// The original typed request plus the actual emitted VC and its parameter places.
#[derive(Clone, Debug)]
pub struct NativeWpTranslationSubject {
    pub original: NativeExecutionSubject,
    pub vc_bytes: Arc<[u8]>,
    pub vc_bindings: Vec<NativeExecutionBinding>,
}

/// The syntax datum cannot select a proposition or model namespace. The fixed
/// proposition itself requires encoding to the independently expected VC bytes.
#[derive(Clone, Debug)]
pub struct NativeWpTranslationPacket {
    pub context: EnvDigest,
    pub proposed_vc: Expr,
    pub proof: Expr,
}

pub struct UnboundNativeWpTranslationContext {
    model: SemrModelContext,
}

impl UnboundNativeWpTranslationContext {
    pub fn from_reference_base(base: ReferenceBase) -> Result<Self, NativeExecutionRefusal> {
        const ROOTS: &[&str] = &[
            "SemRNativeUnsignedTranslation.originalWpTranslation",
            "SemRNativeUnsignedTranslation.TranslationCertificate",
            "SemRNativeExecutionClaim.originalExecution",
        ];
        Ok(Self {
            model: SemrModelContext::from_reference_base(base, ROOTS, MODEL_ROOTS)?,
        })
    }

    pub fn digest(&self) -> EnvDigest {
        self.model.kernel().env_digest()
    }

    pub fn check_model_source(&self, original: &Environment) -> Result<(), NativeExecutionRefusal> {
        self.model.check_model_source(original).map_err(Into::into)
    }

    /// Untrusted syntax for the fixed indexed certificate. Its only field is
    /// the existing exact semantic translation proof; indices are compared
    /// before unfolding that proposition on a wrong-question refusal.
    pub fn expected_goal(&self, expected: &NativeWpTranslationSubject, proposed_vc: &Expr) -> Expr {
        let mut arguments = subject_arguments(&expected.original).to_vec();
        arguments.extend([
            bytes(&expected.vc_bytes),
            proposed_vc.clone(),
            bindings_quote(&expected.vc_bindings),
        ]);
        Expr::apps(
            c("SemRNativeUnsignedTranslation.TranslationCertificate"),
            arguments,
        )
    }

    pub fn check(
        &self,
        expected: &NativeWpTranslationSubject,
        packet: &NativeWpTranslationPacket,
    ) -> Result<CheckedUnboundNativeWpTranslation, NativeExecutionRefusal> {
        if packet.context != self.digest() {
            return Err(NativeExecutionRefusal::ContextMismatch);
        }
        let claim = self.expected_goal(expected, &packet.proposed_vc);
        self.model
            .kernel()
            .check_closed_term(&claim, &packet.proof)
            .map_err(NativeExecutionRefusal::Proof)?;
        Ok(CheckedUnboundNativeWpTranslation {
            subject: expected.clone(),
            context: self.digest(),
            claim,
            proposed_vc: packet.proposed_vc.clone(),
            proof: packet.proof.clone(),
        })
    }
}

/// Checked conditional mathematics only. No Deserialize, grade, ABI or token conversion.
#[derive(Clone, Debug)]
pub struct CheckedUnboundNativeWpTranslation {
    subject: NativeWpTranslationSubject,
    context: EnvDigest,
    claim: Expr,
    proposed_vc: Expr,
    proof: Expr,
}

impl CheckedUnboundNativeWpTranslation {
    pub fn subject(&self) -> &NativeWpTranslationSubject {
        &self.subject
    }
    pub fn context(&self) -> EnvDigest {
        self.context
    }
    pub fn claim(&self) -> &Expr {
        &self.claim
    }
    pub fn proposed_vc(&self) -> &Expr {
        &self.proposed_vc
    }
    pub fn proof(&self) -> &Expr {
        &self.proof
    }
}
