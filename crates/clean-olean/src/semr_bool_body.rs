// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Unbound mathematical checking of an exact byte-subject Boolean conjunction.
//!
//! This reader consumes a genuinely completed reference replay. It constructs
//! its own universal `SemR.runBlob` goal from actual expected bytes and FuncId;
//! a packet supplies proof data, never the goal or model selector. It does not
//! establish that the supplied model environment is canonical. The source owner
//! must bind the fixed original source cohort and compare its declarations via
//! [`UnboundBoolMathematicsContext::check_model_source`]. No Rust-source theorem,
//! producer grade, body license, physical ABI or emission permission is created.

use clean_kernel::{
    BinderInfo, EnvDigest, Environment, Expr, Level, Name, ReferenceKernel, ReferenceRefusal,
};
use std::collections::BTreeSet;
use std::sync::{Arc, OnceLock};

use crate::{reference_base_closed, ClosedRecheckOptions, ReferenceBase};

/// Shared ordinary input data. Quotation is built once per actual module, not
/// once per function. Private fields keep the byte slice and its quotation paired.
#[derive(Clone, Debug)]
pub struct BoolModuleSubject {
    bytes: Arc<[u8]>,
    quoted_bytes: Expr,
}

impl BoolModuleSubject {
    pub fn new(bytes: Arc<[u8]>) -> Result<Self, BoolBodyRefusal> {
        if bytes.is_empty() {
            return Err(BoolBodyRefusal::SubjectMismatch);
        }
        let quoted_bytes = list(
            c("Nat"),
            bytes.iter().map(|b| Expr::nat_lit(u64::from(*b))).collect(),
        );
        Ok(Self {
            bytes,
            quoted_bytes,
        })
    }

    pub fn bytes(&self) -> &[u8] {
        &self.bytes
    }
}

/// Independently expected mathematical subject; never proof authority.
#[derive(Clone, Debug)]
pub struct BoolSubject {
    pub module: Arc<BoolModuleSubject>,
    pub function: u32,
}

/// Untrusted proof data. Subject/context fields cannot replace the independent
/// expected input or the original kernel's check of the complete universal goal.
#[derive(Clone, Debug)]
pub struct BoolPacket {
    pub context: EnvDigest,
    pub subject: BoolSubject,
    pub returned: Expr,
}

#[derive(Debug, thiserror::Error)]
pub enum BoolBodyRefusal {
    #[error("Boolean model context lacks a genuinely completed reference replay")]
    IncompleteContext,
    #[error("Boolean model context lacks required declaration {0}")]
    MissingDeclaration(String),
    #[error("Boolean packet differs from the actual expected bytes/function/context")]
    SubjectMismatch,
    #[error("original source/model closure differs at {0}")]
    ModelSourceMismatch(String),
    #[error("cannot compare the complete original model closure: {0}")]
    ModelSourceClosure(String),
    #[error("exact universal Boolean runBlob goal was refused: {0}")]
    Proof(ReferenceRefusal),
}

/// Generic mathematical context only. There is no canonical-model constructor,
/// arbitrary model/goal namespace selector, or mutable-kernel accessor.
pub struct UnboundBoolMathematicsContext {
    kernel: ReferenceKernel,
    source_reference: OnceLock<CheckedSourceReference>,
}

// This completion and its immutable input identity are private. A hash is only
// a cache key AFTER a genuine full source replay and exact model comparison.
struct CheckedSourceReference {
    input: Vec<[u8; 32]>,
    _kernel: ReferenceKernel,
}

/// A checked equation in the retained, explicitly unbound model environment.
/// Private fields and no Deserialize/grade conversions prevent source promotion.
#[derive(Clone, Debug)]
pub struct CheckedUnboundBoolMathematics {
    subject: BoolSubject,
    context: EnvDigest,
    claim: Expr,
    proof: Expr,
}

impl CheckedUnboundBoolMathematics {
    pub fn subject(&self) -> &BoolSubject {
        &self.subject
    }
    pub fn context(&self) -> EnvDigest {
        self.context
    }
    pub fn claim(&self) -> &Expr {
        &self.claim
    }
    pub fn proof(&self) -> &Expr {
        &self.proof
    }
}

// These roots cover the fixed execution goal's complete declaration payloads.
// The source owner supplies a sealed accepted original-source environment, not
// caller-authored model labels or expected digest strings.
const MODEL_ROOTS: [&str; 7] = [
    "SemR.runBlob",
    "SemR.Val",
    "SemR.Out",
    "SemR.DErr",
    "Bool.and",
    "Eq",
    "List",
];

fn c(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn list(ty: Expr, values: Vec<Expr>) -> Expr {
    values.into_iter().rev().fold(
        Expr::app(
            Expr::const_(Name::from_string("List.nil"), vec![Level::zero()]),
            ty.clone(),
        ),
        |tail, value| {
            Expr::apps(
                Expr::const_(Name::from_string("List.cons"), vec![Level::zero()]),
                [ty.clone(), value, tail],
            )
        },
    )
}

fn expected_conjunction(subject: &BoolSubject) -> Expr {
    let a = Expr::bvar(2);
    let b = Expr::bvar(1);
    let depth = Expr::bvar(0);
    let input = list(
        c("SemR.Val"),
        vec![
            Expr::app(c("SemR.Val.bool"), a.clone()),
            Expr::app(c("SemR.Val.bool"), b.clone()),
        ],
    );
    let run = Expr::apps(
        c("SemR.runBlob"),
        [
            subject.module.quoted_bytes.clone(),
            Expr::nat_lit(u64::from(subject.function)),
            input,
            Expr::nat_lit(2),
            depth,
        ],
    );
    let returned = Expr::app(
        c("SemR.Out.ret"),
        list(
            c("SemR.Val"),
            vec![Expr::app(
                c("SemR.Val.bool"),
                Expr::apps(c("Bool.and"), [a, b]),
            )],
        ),
    );
    let result = Expr::apps(
        Expr::const_(
            Name::from_string("Except.ok"),
            vec![Level::zero(), Level::zero()],
        ),
        [c("SemR.DErr"), c("SemR.Out"), returned],
    );
    let result_ty = Expr::apps(
        Expr::const_(
            Name::from_string("Except"),
            vec![Level::zero(), Level::zero()],
        ),
        [c("SemR.DErr"), c("SemR.Out")],
    );
    let equation = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [result_ty, run, result],
    );
    Expr::pi(
        BinderInfo::Default,
        c("Bool"),
        Expr::pi(
            BinderInfo::Default,
            c("Bool"),
            Expr::pi(BinderInfo::Default, c("Nat"), equation),
        ),
    )
}

impl UnboundBoolMathematicsContext {
    pub fn from_reference_base(base: ReferenceBase) -> Result<Self, BoolBodyRefusal> {
        let kernel = base
            .into_kernel()
            .map_err(|_| BoolBodyRefusal::IncompleteContext)?;
        for root in MODEL_ROOTS {
            kernel
                .environment()
                .dependency_closure(&Name::from_string(root))
                .map_err(|_| BoolBodyRefusal::MissingDeclaration(root.into()))?;
        }
        let helper = "SemR.BoolBody.checked_blob";
        kernel
            .environment()
            .dependency_closure(&Name::from_string(helper))
            .map_err(|_| BoolBodyRefusal::MissingDeclaration(helper.into()))?;
        Ok(Self {
            kernel,
            source_reference: OnceLock::new(),
        })
    }

    pub fn digest(&self) -> EnvDigest {
        self.kernel.env_digest()
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
        let input = source_input(original)?;
        if let Some(cached) = self.source_reference.get() {
            return if cached.input == input {
                Ok(())
            } else {
                Err(BoolBodyRefusal::ModelSourceMismatch(
                    "fixed source batch changed".into(),
                ))
            };
        }
        let roots: BTreeSet<Name> = MODEL_ROOTS.into_iter().map(Name::from_string).collect();
        let base = reference_base_closed(original, &roots, &ClosedRecheckOptions::default())
            .map_err(|e| BoolBodyRefusal::ModelSourceClosure(e.to_string()))?;
        let source_kernel = base
            .into_kernel()
            .map_err(|report| BoolBodyRefusal::ModelSourceClosure(report.verdict_sentence()))?;
        let checked = self.kernel.environment();
        let source = source_kernel.environment();
        for root in MODEL_ROOTS {
            let name = Name::from_string(root);
            let left = checked
                .dependency_closure(&name)
                .map_err(|e| BoolBodyRefusal::ModelSourceClosure(e.to_string()))?;
            let right = source
                .dependency_closure(&name)
                .map_err(|e| BoolBodyRefusal::ModelSourceClosure(e.to_string()))?;
            if left != right {
                return Err(BoolBodyRefusal::ModelSourceMismatch(root.into()));
            }
            for member in left {
                if checked.get_const(&member) != source.get_const(&member)
                    || checked.get_inductive(&member) != source.get_inductive(&member)
                    || checked.get_constructor(&member) != source.get_constructor(&member)
                    || checked.get_recursor(&member) != source.get_recursor(&member)
                    || checked.get_quot(&member) != source.get_quot(&member)
                {
                    return Err(BoolBodyRefusal::ModelSourceMismatch(member.to_string()));
                }
            }
        }
        if source_input(original)? != input {
            return Err(BoolBodyRefusal::ModelSourceMismatch(
                "source changed during replay".into(),
            ));
        }
        let binding = CheckedSourceReference {
            input,
            _kernel: source_kernel,
        };
        match self.source_reference.set(binding) {
            Ok(()) => Ok(()),
            Err(binding)
                if self
                    .source_reference
                    .get()
                    .is_some_and(|source| source.input == binding.input) =>
            {
                Ok(())
            }
            Err(_) => Err(BoolBodyRefusal::ModelSourceMismatch(
                "fixed source batch changed".into(),
            )),
        }
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
        let claim = expected_conjunction(expected);
        self.kernel
            .check_closed_term(&claim, &packet.returned)
            .map_err(BoolBodyRefusal::Proof)?;
        Ok(CheckedUnboundBoolMathematics {
            subject: expected.clone(),
            context: self.digest(),
            claim,
            proof: packet.returned.clone(),
        })
    }
}

fn source_input(original: &Environment) -> Result<Vec<[u8; 32]>, BoolBodyRefusal> {
    MODEL_ROOTS
        .into_iter()
        .map(|root| {
            original
                .closure_digest(&Name::from_string(root))
                .map_err(|e| BoolBodyRefusal::ModelSourceClosure(e.to_string()))
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn edited_replay_diagnostics_cannot_create_a_model_context() {
        let env = Environment::for_lean_replay();
        let missing = Name::from_string("MissingBoolModelSubject");
        let mut base = reference_base_closed(
            &env,
            &BTreeSet::from([missing.clone()]),
            &ClosedRecheckOptions::default(),
        )
        .unwrap();
        assert!(!base.report.passed());
        base.report.refusals.clear();
        base.report.extension_bindings_pinned = true;
        base.entry_refusals.clear();
        base.admitted.insert(missing);
        assert!(base.report.passed());
        assert!(matches!(
            UnboundBoolMathematicsContext::from_reference_base(base),
            Err(BoolBodyRefusal::IncompleteContext)
        ));
    }
}
