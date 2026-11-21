// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Unbound mathematical checking of an exact byte-subject Boolean conjunction.
//!
//! This reader consumes a genuinely completed reference replay. It constructs
//! its own universal `SemR.runBlob` goal from actual expected bytes and FuncId;
//! a packet supplies proof data, never the goal or model selector. It does not
//! establish that the supplied model environment is canonical. The source owner
//! must bind the fixed original source cohort and compare its declarations via
//! [`PreparedBoolMathematicsContext::check_model_source`]. No Rust-source theorem,
//! producer grade, body license, physical ABI or emission permission is created.

use clean_kernel::{BinderInfo, EnvDigest, Environment, Expr, Level, Name, ReferenceRefusal};
use std::collections::{BTreeMap, BTreeSet};
use std::sync::{Arc, OnceLock};

use crate::semr_model::{c, list, CheckedSourceReference, SemrModelContext, SemrModelRefusal};
use crate::ReferenceBase;

mod byte_quote;
mod concrete;
mod minirust_call;
mod original_item;
pub use original_item::{OriginalBoolItemLocal, OriginalBoolItemSubject, ORIGINAL_BOOL_ITEM_ROOTS};
pub use minirust_call::MiniRustCallSubject;
use byte_quote::{ByteQuote, ByteQuotePlan};
pub use concrete::UnboundBoolMathematicsContext;

/// Shared ordinary input data. Private bytes are retained independently of any
/// proposed proof. Bounded quotations are checked once during context preparation.
#[derive(Clone, Debug)]
pub struct BoolModuleSubject {
    bytes: Arc<[u8]>,
    concrete: OnceLock<Expr>,
}

impl BoolModuleSubject {
    pub fn new(bytes: Arc<[u8]>) -> Result<Self, BoolBodyRefusal> {
        if bytes.is_empty() {
            return Err(BoolBodyRefusal::SubjectMismatch);
        }
        Ok(Self {
            bytes,
            concrete: OnceLock::new(),
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

/// A built-in Boolean operation observed by the source owner. This is input to
/// the independent goal builder and confers no source or proof authority.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BoolSourceOp {
    BitAnd,
    BitOr,
    BitXor,
}

impl BoolSourceOp {
    fn constant(self) -> &'static str {
        match self {
            Self::BitAnd => "Bool.and",
            Self::BitOr => "Bool.or",
            Self::BitXor => "Bool.xor",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BoolSourceParam {
    First,
    Second,
}

/// The operation and the two argument occurrences in source order. Repeated
/// parameters are representable and change the proposition that is checked.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BoolSourceRhs {
    op: BoolSourceOp,
    operands: [BoolSourceParam; 2],
}

impl BoolSourceRhs {
    pub fn new(op: BoolSourceOp, operands: [BoolSourceParam; 2]) -> Self {
        Self { op, operands }
    }

    fn term(self, a: &Expr, b: &Expr) -> Expr {
        let operands = self.operands.map(|param| match param {
            BoolSourceParam::First => a.clone(),
            BoolSourceParam::Second => b.clone(),
        });
        Expr::apps(c(self.op.constant()), operands)
    }
}

/// Untrusted proof data. Subject/context fields cannot replace the independent
/// expected input or the original kernel's check of the complete universal goal.
#[derive(Clone, Debug)]
pub struct BoolPacket {
    pub context: EnvDigest,
    pub subject: BoolSubject,
    pub returned: Expr,
}

/// Untrusted independent producer data. The reader checks every declaration,
/// chunk, terminal, link and full-root equation through the original kernel.
/// No field is an acceptance token or a native semantic assertion.
#[derive(Clone)]
pub struct BoolQuotationProposal {
    pub declarations: Vec<clean_kernel::Declaration>,
    pub chunks: Vec<Expr>,
    pub suffixes: Vec<Expr>,
    pub bytes: Expr,
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
    #[error("checked byte quotation name already exists: {0}")]
    QuotationNameCollision(String),
    #[error("the complete expected byte batch must be prepared exactly once before packets")]
    QuotationPreparation,
    #[error("the expected byte subject was not included in the frozen preparation batch")]
    UnpreparedSubject,
    #[error("independent quotation has malformed chunk/link data: {0}")]
    QuotationShape(String),
    #[error("one shared producer quotation is required per exact raw module")]
    DuplicateQuotationSubject,
    #[error("checked byte data declaration was refused: {0}")]
    Quotation(ReferenceRefusal),
    #[error("nominal opaque-input Boolean goal was refused: {0}")]
    NominalProof(ReferenceRefusal),
    #[error("this subject's proof preparation was refused: {0}")]
    PreparedProof(Arc<BoolBodyRefusal>),
    #[error("proof preparation changed the environment despite a refusal")]
    PreparationMutation,
    #[error("the proof preparation batch contains a repeated bytes/function subject")]
    DuplicateProofSubject,
    #[error("exact universal Boolean runBlob goal was refused: {0}")]
    Proof(ReferenceRefusal),
}

/// Generic mathematical context only. There is no canonical-model constructor,
/// arbitrary model/goal namespace selector, or mutable-kernel accessor.
pub struct PreparedBoolMathematicsContext {
    model: SemrModelContext,
    rhs_source_reference: OnceLock<CheckedSourceReference>,
    call_source_reference: OnceLock<CheckedSourceReference>,
    item_source_reference: OnceLock<CheckedSourceReference>,
    quotes: Option<BTreeMap<Arc<[u8]>, ByteQuote>>,
    proofs: Option<BTreeMap<(Arc<[u8]>, u32), Result<Expr, Arc<BoolBodyRefusal>>>>,
}

/// A checked equation in the retained, explicitly unbound model environment.
/// Private fields and no Deserialize/grade conversions prevent source promotion.
#[derive(Clone, Debug)]
pub struct CheckedUnboundBoolMathematics {
    origin: CheckedBoolOrigin,
    subject: BoolSubject,
    context: EnvDigest,
    claim: Expr,
    proof: Expr,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum CheckedBoolOrigin {
    Direct,
    PreparedRoot,
    SourceRhs,
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
const MODEL_ROOTS: [&str; 13] = [
    "SemR.runBlob",
    "SemR.Val",
    "SemR.Out",
    "SemR.DErr",
    "Bool.and",
    "Eq",
    "List",
    "SemR.DecodeCertificate.BoundBytes",
    "SemR.DecodeCertificate.from_bound",
    "SemR.DecodeCertificate.to_bound",
    "SemR.DecodeCertificate.suffix_exact",
    "SemR.DecodeCertificate.trans_exact",
    "SemR.DecodeCertificate.to_bound_from",
];

fn expected_conjunction(bytes: Expr, function: u32) -> Expr {
    expected_body(
        bytes,
        function,
        BoolSourceRhs::new(
            BoolSourceOp::BitAnd,
            [BoolSourceParam::First, BoolSourceParam::Second],
        ),
    )
}

fn run_bool(bytes: Expr, function: u32, a: Expr, b: Expr, depth: Expr) -> Expr {
    let input = list(
        c("SemR.Val"),
        vec![
            Expr::app(c("SemR.Val.bool"), a),
            Expr::app(c("SemR.Val.bool"), b),
        ],
    );
    Expr::apps(
        c("SemR.runBlob"),
        [
            bytes,
            Expr::nat_lit(u64::from(function)),
            input,
            Expr::nat_lit(2),
            depth,
        ],
    )
}

fn returned_bool(value: Expr) -> (Expr, Expr) {
    let returned = Expr::app(
        c("SemR.Out.ret"),
        list(
            c("SemR.Val"),
            vec![Expr::app(c("SemR.Val.bool"), value)],
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
    (result_ty, result)
}

fn return_equation(result_ty: Expr, run: Expr, result: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [result_ty, run, result],
    )
}

fn expected_body(bytes: Expr, function: u32, rhs: BoolSourceRhs) -> Expr {
    let a = Expr::bvar(2);
    let b = Expr::bvar(1);
    let (result_ty, result) = returned_bool(rhs.term(&a, &b));
    let run = run_bool(bytes.lift(3), function, a, b, Expr::bvar(0));
    let equation = return_equation(result_ty, run, result);
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

impl PreparedBoolMathematicsContext {
    pub fn from_reference_base(base: ReferenceBase) -> Result<Self, BoolBodyRefusal> {
        let model = SemrModelContext::from_reference_base(
            base,
            &MODEL_ROOTS,
            &["SemR.BoolBody.checked_blob"],
        )?;
        Ok(Self {
            model,
            rhs_source_reference: OnceLock::new(),
            call_source_reference: OnceLock::new(),
            item_source_reference: OnceLock::new(),
            quotes: None,
            proofs: None,
        })
    }

    /// Consume the model context to check the complete expected byte batch.
    /// All generated names are preflighted before any mutation. Equal byte
    /// slices share one quotation only within this preparation; a pre-existing
    /// generated name is never adopted. No packet may precede this extension.
    pub fn prepare_modules(
        mut self,
        modules: &[(Arc<BoolModuleSubject>, &BoolQuotationProposal)],
    ) -> Result<Self, BoolBodyRefusal> {
        if self.quotes.is_some() || modules.is_empty() {
            return Err(BoolBodyRefusal::QuotationPreparation);
        }
        let mut unique: BTreeMap<Arc<[u8]>, &BoolQuotationProposal> = BTreeMap::new();
        for (module, proposal) in modules {
            if let Some(previous) = unique.get(&module.bytes) {
                if !std::ptr::eq(*previous, *proposal) {
                    return Err(BoolBodyRefusal::DuplicateQuotationSubject);
                }
            } else {
                unique.insert(Arc::clone(&module.bytes), *proposal);
            }
        }
        let plans: Vec<_> = unique
            .iter()
            .map(|(bytes, proposal)| ByteQuotePlan::new(bytes, proposal))
            .collect::<Result<_, _>>()?;
        let mut names = BTreeSet::new();
        for plan in &plans {
            plan.preflight(self.model.kernel())?;
            for name in plan.names() {
                if !names.insert(name.clone()) {
                    return Err(BoolBodyRefusal::QuotationNameCollision(name.to_string()));
                }
            }
        }
        let mut quotes = BTreeMap::new();
        for ((bytes, _), plan) in unique.iter().zip(plans) {
            quotes.insert(Arc::clone(bytes), plan.admit(self.model.kernel_mut())?);
        }
        self.quotes = Some(quotes);
        Ok(self)
    }

    fn quote(&self, expected: &BoolModuleSubject) -> Result<&ByteQuote, BoolBodyRefusal> {
        self.quotes
            .as_ref()
            .and_then(|quotes| quotes.get(&expected.bytes))
            .ok_or(BoolBodyRefusal::UnpreparedSubject)
    }

    fn predicate(function: u32) -> Expr {
        Expr::lam(
            BinderInfo::Default,
            Expr::app(
                Expr::const_(Name::from_string("List"), vec![Level::zero()]),
                c("Nat"),
            ),
            expected_conjunction(Expr::bvar(0), function),
        )
    }

    /// Build an untrusted transport term from a proposed concrete proof.
    /// This does not evaluate the decoder or accept the proposal.
    pub fn bind_proposal(
        &self,
        expected: &BoolSubject,
        proposed: Expr,
    ) -> Result<Expr, BoolBodyRefusal> {
        let quote = self.quote(&expected.module)?;
        Ok(Expr::apps(
            c("SemR.DecodeCertificate.to_bound_from"),
            [
                quote.producer.clone(),
                quote.concrete.clone(),
                Self::predicate(expected.function),
                quote.equation.clone(),
                quote.input.clone(),
                proposed,
            ],
        ))
    }

    /// Check each proposed nominal theorem before the packet context is fixed.
    /// A body refusal remains attached to that exact subject; independent valid
    /// rows can still prepare. Any mutation accompanying a refusal invalidates
    /// the entire context. Successful declarations use the original entry only.
    pub fn prepare_proofs(
        mut self,
        proposals: &[(BoolSubject, Expr)],
    ) -> Result<Self, BoolBodyRefusal> {
        if self.proofs.is_some() || self.quotes.is_none() {
            return Err(BoolBodyRefusal::QuotationPreparation);
        }
        let mut subjects = BTreeSet::new();
        let mut names = BTreeSet::new();
        let mut plan = Vec::new();
        for (subject, proposed) in proposals {
            let quote = self.quote(&subject.module)?;
            let key = (Arc::clone(&subject.module.bytes), subject.function);
            if !subjects.insert(key.clone()) {
                return Err(BoolBodyRefusal::DuplicateProofSubject);
            }
            let name = Name::from_string(&format!(
                "TrustCheckedBytes.v1.h{}.n{}.proof_{}",
                blake3::hash(subject.module.bytes()).to_hex(),
                subject.module.bytes().len(),
                subject.function,
            ));
            let env = self.model.kernel().environment();
            if !names.insert(name.clone())
                || env.get_const(&name).is_some()
                || env.get_inductive(&name).is_some()
                || env.get_constructor(&name).is_some()
                || env.get_recursor(&name).is_some()
                || env.get_quot(&name).is_some()
            {
                return Err(BoolBodyRefusal::QuotationNameCollision(name.to_string()));
            }
            plan.push((
                key,
                name,
                expected_conjunction(quote.nominal.clone(), subject.function),
                proposed.clone(),
            ));
        }
        let mut proofs = BTreeMap::new();
        for (key, name, type_, value) in plan {
            let before = self.model.kernel().env_digest();
            let result = self
                .model
                .kernel_mut()
                .add_checked(clean_kernel::Declaration::Theorem {
                    name: name.clone(),
                    level_params: vec![],
                    type_,
                    value,
                });
            let result = match result {
                Ok(_) => Ok(Expr::const_(name, vec![])),
                Err(reason) => {
                    if self.model.kernel().env_digest() != before
                        || self.model.kernel().environment().get_const(&name).is_some()
                    {
                        return Err(BoolBodyRefusal::PreparationMutation);
                    }
                    Err(Arc::new(BoolBodyRefusal::NominalProof(reason)))
                }
            };
            proofs.insert(key, result);
        }
        self.proofs = Some(proofs);
        Ok(self)
    }

    /// Return ordinary proof syntax only for a successfully prepared subject.
    /// `check` still checks the nominal goal and the full concrete goal anew.
    pub fn prepared_proof(&self, expected: &BoolSubject) -> Result<Expr, BoolBodyRefusal> {
        match self
            .proofs
            .as_ref()
            .and_then(|proofs| proofs.get(&(Arc::clone(&expected.module.bytes), expected.function)))
        {
            Some(Ok(proof)) => Ok(proof.clone()),
            Some(Err(reason)) => Err(BoolBodyRefusal::PreparedProof(Arc::clone(reason))),
            None => Err(BoolBodyRefusal::UnpreparedSubject),
        }
    }

    /// Check a proposal directly against the original concrete-byte goal. This
    /// returns no result carrier and does not replace either check in `check`.
    /// In particular a nominal hostile-goal refusal cannot stand in for an
    /// actually executed concrete hostile-goal check.
    pub fn check_concrete_goal(
        &self,
        expected: &BoolSubject,
        proof: &Expr,
    ) -> Result<(), BoolBodyRefusal> {
        let quote = self.quote(&expected.module)?;
        let claim = expected_conjunction(quote.concrete.clone(), expected.function);
        self.model
            .kernel()
            .check_closed_term(&claim, proof)
            .map(|_| ())
            .map_err(BoolBodyRefusal::Proof)
    }

    /// Check the original decoder and interpreter return true at (true,false)
    /// on these concrete bytes, this function, fuel two and depth zero. This
    /// is one counterexample to universal conjunction, with no source grade.
    pub fn check_conjunction_counterexample(
        &self,
        expected: &BoolSubject,
    ) -> Result<(), BoolBodyRefusal> {
        let quote = self.quote(&expected.module)?;
        let run = run_bool(
            quote.concrete.clone(), expected.function, c("Bool.true"), c("Bool.false"),
            Expr::nat_lit(0u64),
        );
        let (result_ty, returned) = returned_bool(c("Bool.true"));
        let proof = Expr::apps(
            Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]),
            [result_ty.clone(), returned.clone()],
        );
        let goal = return_equation(result_ty, run, returned);
        self.model.kernel().check_closed_term(&goal, &proof)
            .map(|_| ())
            .map_err(BoolBodyRefusal::Proof)
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

    /// Authenticate the additional Bool operators against the same accepted
    /// original source environment. Legacy conjunction-only consumers retain
    /// their original declaration population.
    pub fn check_model_source_with_rhs(
        &self,
        original: &Environment,
    ) -> Result<(), BoolBodyRefusal> {
        self.check_model_source(original)?;
        self.model
            .check_source_roots(
                original,
                &["Bool.or", "Bool.xor"],
                &self.rhs_source_reference,
            )
            .map_err(Into::into)
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
        let quote = self.quote(&expected.module)?;
        let nominal_claim = expected_conjunction(quote.nominal.clone(), expected.function);
        self.model
            .kernel()
            .check_closed_term(&nominal_claim, &packet.returned)
            .map_err(BoolBodyRefusal::NominalProof)?;
        // Nominal acceptance supplies no result. Independently check the
        // transported theorem against the complete concrete-byte goal too.
        let claim = expected_conjunction(quote.concrete.clone(), expected.function);
        let proof = Expr::apps(
            c("SemR.DecodeCertificate.from_bound"),
            [
                quote.concrete.clone(),
                Self::predicate(expected.function),
                quote.input.clone(),
                packet.returned.clone(),
            ],
        );
        self.model
            .kernel()
            .check_closed_term(&claim, &proof)
            .map_err(BoolBodyRefusal::Proof)?;
        Ok(CheckedUnboundBoolMathematics {
            subject: expected.clone(),
            context: self.digest(),
            claim,
            proof,
            origin: CheckedBoolOrigin::PreparedRoot,
        })
    }

    /// Recheck the already transported concrete proof against the source
    /// owner's independently observed operator and argument occurrences. The
    /// returned claim still concerns the exact quoted SemR root invocation.
    pub fn check_source_rhs(
        &self,
        expected: &BoolSubject,
        checked: &CheckedUnboundBoolMathematics,
        rhs: BoolSourceRhs,
    ) -> Result<CheckedUnboundBoolMathematics, BoolBodyRefusal> {
        if checked.origin != CheckedBoolOrigin::PreparedRoot
            || checked.context != self.digest()
            || checked.subject.function != expected.function
            || checked.subject.module.bytes != expected.module.bytes
        {
            return Err(BoolBodyRefusal::SubjectMismatch);
        }
        if !self.model.source_is_checked()
            || (rhs.op != BoolSourceOp::BitAnd && self.rhs_source_reference.get().is_none())
        {
            return Err(BoolBodyRefusal::ModelSourceClosure(
                "source Boolean operator closure has not been checked".into(),
            ));
        }
        let quote = self.quote(&expected.module)?;
        let claim = expected_body(quote.concrete.clone(), expected.function, rhs);
        self.model
            .kernel()
            .check_closed_term(&claim, &checked.proof)
            .map_err(BoolBodyRefusal::Proof)?;
        Ok(CheckedUnboundBoolMathematics {
            subject: expected.clone(),
            context: self.digest(),
            claim,
            proof: checked.proof.clone(),
            origin: CheckedBoolOrigin::SourceRhs,
        })
    }
}

impl From<SemrModelRefusal> for BoolBodyRefusal {
    fn from(value: SemrModelRefusal) -> Self {
        match value {
            SemrModelRefusal::IncompleteContext => Self::IncompleteContext,
            SemrModelRefusal::MissingDeclaration(name) => Self::MissingDeclaration(name),
            SemrModelRefusal::ModelSourceMismatch(name) => Self::ModelSourceMismatch(name),
            SemrModelRefusal::ModelSourceClosure(reason) => Self::ModelSourceClosure(reason),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{reference_base_closed, ClosedRecheckOptions};

    #[test]
    fn source_rhs_instances_check_against_the_pinned_boolean_operators() {
        use clean_kernel::{KernelEnvError, KernelTypeError};
        let lib = crate::installed_lean_lib_path("leanprover/lean4:v4.30.0-rc2")
            .expect("the Boolean model's pinned Init library is required");
        let bytes = std::fs::read(lib.join("Init/Data/Bool.olean")).unwrap();
        let header = crate::OleanHeader::parse(&bytes).unwrap();
        assert_eq!(header.lean_version.as_deref(), Some("4.30.0-rc2"));
        assert!(header.matches_git_hash("3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc"));
        let mut env = Environment::for_lean_replay();
        crate::load_module_with_deps(&mut env, "Init.Data.Bool", &[lib]).unwrap();
        let roots = ["Eq.refl", "Bool.and", "Bool.or", "Bool.xor"]
            .map(Name::from_string)
            .into_iter()
            .collect();
        let kernel = reference_base_closed(&env, &roots, &ClosedRecheckOptions::default())
            .unwrap()
            .into_kernel()
            .expect("complete pinned Boolean reference replay");
        let boolean = |b| if b { c("Bool.true") } else { c("Bool.false") };
        let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
        let refl = Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        );
        for a in [false, true] {
            for b in [false, true] {
                let parameters = [(BoolSourceParam::First, a), (BoolSourceParam::Second, b)];
                for (left, x) in parameters {
                    for (right, y) in parameters {
                        for (op, expected) in [
                            (BoolSourceOp::BitAnd, x & y),
                            (BoolSourceOp::BitOr, x | y),
                            (BoolSourceOp::BitXor, x ^ y),
                        ] {
                            let rhs = BoolSourceRhs::new(op, [left, right])
                                .term(&boolean(a), &boolean(b));
                            let claim = Expr::apps(eq.clone(), [c("Bool"), rhs, boolean(expected)]);
                            let witness =
                                |value| Expr::apps(refl.clone(), [c("Bool"), boolean(value)]);
                            kernel
                                .check_closed_term(&claim, &witness(expected))
                                .unwrap();
                            assert!(matches!(
                                kernel.check_closed_term(&claim, &witness(!expected)),
                                Err(ReferenceRefusal::Kernel(KernelEnvError::TypeCheckFailed {
                                    source: KernelTypeError::TypeMismatch { .. },
                                    ..
                                }))
                            ));
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn source_rhs_changes_only_the_result_of_the_same_ordered_call() {
        let source_bytes = Expr::bvar(0);
        let val = |arg| Expr::app(c("SemR.Val.bool"), Expr::bvar(arg));
        let run = Expr::apps(
            c("SemR.runBlob"),
            [
                Expr::bvar(3),
                Expr::nat_lit(465),
                list(c("SemR.Val"), vec![val(2), val(1)]),
                Expr::nat_lit(2),
                Expr::bvar(0),
            ],
        );
        let params = [(BoolSourceParam::First, 2), (BoolSourceParam::Second, 1)];
        for (operation, name) in [
            (BoolSourceOp::BitAnd, "Bool.and"),
            (BoolSourceOp::BitOr, "Bool.or"),
            (BoolSourceOp::BitXor, "Bool.xor"),
        ] {
            for (left, l) in params {
                for (right, r) in params {
                    let claim = expected_body(
                        source_bytes.clone(),
                        465,
                        BoolSourceRhs::new(operation, [left, right]),
                    );
                    let mut equation = &claim;
                    for ty in ["Bool", "Bool", "Nat"] {
                        let clean_kernel::ExprKind::Pi(_, domain, body) = equation.kind() else {
                            panic!("missing universal binder");
                        };
                        assert_eq!(domain.as_ref(), &c(ty));
                        equation = body;
                    }
                    assert_eq!(
                        equation.get_app_fn(),
                        &Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())],)
                    );
                    let sides = equation.get_app_args();
                    assert_eq!(sides[1], &run);
                    let value = Expr::app(
                        c("SemR.Val.bool"),
                        Expr::apps(c(name), [Expr::bvar(l), Expr::bvar(r)]),
                    );
                    let output = Expr::app(c("SemR.Out.ret"), list(c("SemR.Val"), vec![value]));
                    assert_eq!(sides[2].get_app_args()[2], &output);
                }
            }
        }
    }

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
            PreparedBoolMathematicsContext::from_reference_base(base),
            Err(BoolBodyRefusal::IncompleteContext)
        ));
    }
}
