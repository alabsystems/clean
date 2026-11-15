// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Unlicensed byte-subject mathematics in an independently FULL-rechecked SemR
//! context. This is a reader interface, not another Rust/IR evaluator.
//!
//! The caller must bind the supplied producer/context to the canonical SemR
//! source artifact. A kernel proves statements about definitions, not that an
//! arbitrary named context is the compiler's actual model. The exact checked
//! context digest is retained, and a packet cannot replace it. No TCX/source,
//! physical ABI/ISA, SourceNoUB, body-license or emission authority is created.
use crate::ReferenceBase;
use clean_kernel::{EnvDigest, Expr, Level, Name, ReferenceKernel, ReferenceRefusal};

/// Non-authoritative expected subject, derived by the actual IR/source owner.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ScalarSubject {
    pub module_bytes: Vec<u8>,
    pub literal: u64,
}

/// Untrusted original proof terms and their complete mathematical subject.
#[derive(Clone, Debug)]
pub struct ScalarPacket {
    pub context: EnvDigest,
    pub subject: ScalarSubject,
    pub decoded: Expr,
    pub returned: Expr,
    pub no_bad: Expr,
}

#[derive(Debug, thiserror::Error)]
pub enum ScalarRefusal {
    #[error("SemR context was not completely rechecked through the pinned reference entry")]
    IncompleteContext,
    #[error("SemR context lacks required checked declaration {0}")]
    MissingDeclaration(String),
    #[error("scalar packet differs from the independently supplied expected subject/context")]
    SubjectMismatch,
    #[error("this completed context lacks the generic canonical scalar profile")]
    ProfileContextRequired,
    #[error("{claim}: {reason}")]
    Proof {
        claim: &'static str,
        reason: ReferenceRefusal,
    },
}

/// FULL reference context retained from the existing closed-replay owner.
/// There is no unchecked environment constructor or mutable-kernel accessor.
pub struct ScalarContext {
    kernel: ReferenceKernel,
    namespace: &'static str,
}

/// Checked mathematics only; no conversion to any compiler grade/token exists.
#[derive(Clone, Debug)]
pub struct CheckedScalarMathematics {
    subject: ScalarSubject,
    context: EnvDigest,
    claims: [Expr; 3],
    proofs: [Expr; 3],
}
impl CheckedScalarMathematics {
    pub fn subject(&self) -> &ScalarSubject {
        &self.subject
    }
    pub fn context(&self) -> EnvDigest {
        self.context
    }
    pub fn claims(&self) -> &[Expr; 3] {
        &self.claims
    }
    pub fn proofs(&self) -> &[Expr; 3] {
        &self.proofs
    }
}

fn c(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}
fn list(bytes: &[u8]) -> Expr {
    bytes.iter().rev().fold(
        Expr::app(
            Expr::const_(Name::from_string("List.nil"), vec![Level::zero()]),
            c("Nat"),
        ),
        |tail, byte| {
            Expr::apps(
                Expr::const_(Name::from_string("List.cons"), vec![Level::zero()]),
                [c("Nat"), Expr::nat_lit(u64::from(*byte)), tail],
            )
        },
    )
}
impl ScalarContext {
    /// Consume a genuinely completed closed replay, including every dependency
    /// from EMPTY. A structural import, caller boolean or partial replay cannot
    /// construct this reader. Exact canonical-source association remains with
    /// the source/artifact owner, independently of this mathematical check.
    pub fn from_reference_base(base: ReferenceBase) -> Result<Self, ScalarRefusal> {
        Self::from_closed_base(
            base,
            "SemRU64AdditionConsumer",
            &[
                "Decodes",
                "Returns",
                "NoBad",
                "original_decoded",
                "original_returns",
                "original_no_bad",
            ],
        )
    }

    /// Completed generic canonical decoder/profile mathematics. The source
    /// artifact owner must still authenticate the actual fixed source cohort.
    /// This creates no source/ABI/grade or compiler admission capability.
    pub fn from_profile_reference_base(base: ReferenceBase) -> Result<Self, ScalarRefusal> {
        Self::from_closed_base(
            base,
            "SemRU64ScalarProfile",
            &[
                "Decodes",
                "Returns",
                "NoBad",
                "accepts",
                "classify_exact",
                "decoded_module",
                "decode_profile",
                "returns",
                "no_bad",
            ],
        )
    }

    fn from_closed_base(
        base: ReferenceBase,
        namespace: &'static str,
        required: &[&str],
    ) -> Result<Self, ScalarRefusal> {
        // The original PRIVATE completion seal precedes mutable diagnostics.
        let kernel = base
            .into_kernel()
            .map_err(|_| ScalarRefusal::IncompleteContext)?;
        for suffix in required {
            let name = format!("{namespace}.{suffix}");
            if kernel
                .environment()
                .get_const(&Name::from_string(&name))
                .is_none()
            {
                return Err(ScalarRefusal::MissingDeclaration(name));
            }
        }
        Ok(Self { kernel, namespace })
    }

    /// Construct ordinary untrusted proof DATA from actual expected bytes.
    /// The REAL decoder/profile must reduce under the kernel when checked;
    /// no host-side shape flag or successful-run equality is accepted.
    pub fn profile_packet(&self, expected: &ScalarSubject) -> Result<ScalarPacket, ScalarRefusal> {
        if self.namespace != "SemRU64ScalarProfile" {
            return Err(ScalarRefusal::ProfileContextRequired);
        }
        let bytes = list(&expected.module_bytes);
        let literal = Expr::nat_lit(expected.literal);
        let reflexivity = Expr::apps(
            Expr::const_(
                Name::from_string("Eq.refl"),
                vec![Level::succ(Level::zero())],
            ),
            [c("Bool"), c("Bool.true")],
        );
        let decoded = Expr::apps(
            c("SemRU64ScalarProfile.decode_profile"),
            [bytes.clone(), literal.clone(), reflexivity],
        );
        let returned = Expr::apps(
            c("SemRU64ScalarProfile.returns"),
            [bytes.clone(), literal.clone(), decoded.clone()],
        );
        let no_bad = Expr::apps(
            c("SemRU64ScalarProfile.no_bad"),
            [bytes, literal, decoded.clone()],
        );
        let packet = ScalarPacket {
            context: self.digest(),
            subject: expected.clone(),
            decoded,
            returned,
            no_bad,
        };
        Ok(packet)
    }

    pub fn digest(&self) -> EnvDigest {
        self.kernel.env_digest()
    }

    /// All three claims are reconstructed from expected bytes/literal. Decode
    /// success is mandatory alongside NoBad, preventing an invalid encoding's
    /// empty decode premise from becoming useful evidence. The packet supplies
    /// proof DATA only; it cannot choose claims or a different model context.
    pub fn check(
        &self,
        expected: &ScalarSubject,
        packet: &ScalarPacket,
    ) -> Result<CheckedScalarMathematics, ScalarRefusal> {
        if &packet.subject != expected
            || packet.context != self.digest()
            || expected.module_bytes.is_empty()
        {
            return Err(ScalarRefusal::SubjectMismatch);
        }
        let bytes = list(&expected.module_bytes);
        let with_literal = |kind: &str| {
            Expr::apps(
                c(&format!("{}.{kind}", self.namespace)),
                [bytes.clone(), Expr::nat_lit(expected.literal)],
            )
        };
        let claims = [
            with_literal("Decodes"),
            with_literal("Returns"),
            Expr::app(c(&format!("{}.NoBad", self.namespace)), bytes),
        ];
        let proofs = [
            packet.decoded.clone(),
            packet.returned.clone(),
            packet.no_bad.clone(),
        ];
        for ((claim, proof), label) in claims
            .iter()
            .zip(&proofs)
            .zip(["decode", "return", "no-bad"])
        {
            self.kernel
                .check_closed_term(claim, proof)
                .map_err(|reason| ScalarRefusal::Proof {
                    claim: label,
                    reason,
                })?;
        }
        Ok(CheckedScalarMathematics {
            subject: expected.clone(),
            context: self.digest(),
            claims,
            proofs,
        })
    }
}
