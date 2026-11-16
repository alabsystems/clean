// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Exact original-program/contract mathematics in an explicitly unbound model.
//!
//! The independent subject is ordinary data. The packet selects neither the
//! goal nor its namespace. A completed reference replay checks the fixed Lean
//! proposition, including its inhabited, complete typed input domain. Source
//! authentication, compiler grades, source ABI and emission authority remain
//! separate responsibilities of the source owner.
use crate::semr_model::{bytes, c, list, SemrModelContext};
use crate::{ReferenceBase, SemrModelRefusal};
use clean_kernel::{EnvDigest, Environment, Expr, Level, Name, ReferenceRefusal};
use std::sync::Arc;

mod translation;
pub use translation::{
    CheckedUnboundNativeWpTranslation, NativeWpTranslationPacket, NativeWpTranslationSubject,
    UnboundNativeWpTranslationContext,
};

/// Complete original serialized native module and its paired quotation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NativeExecutionModuleSubject {
    bytes: Arc<[u8]>,
    quoted_bytes: Expr,
}

impl NativeExecutionModuleSubject {
    pub fn new(original: Arc<[u8]>) -> Result<Self, NativeExecutionRefusal> {
        if original.is_empty() {
            return Err(NativeExecutionRefusal::EmptyModule);
        }
        Ok(Self {
            quoted_bytes: bytes(&original),
            bytes: original,
        })
    }

    pub fn bytes(&self) -> &[u8] {
        &self.bytes
    }
}

/// The two original payload vocabularies directly supported by the Lean codec.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NativeExecutionContractFormat {
    BooleanText,
    TypedJson,
}

impl NativeExecutionContractFormat {
    /// Exact outer schema selection; this never converts or rewrites a payload.
    pub fn from_schema(schema: &str) -> Result<Self, NativeExecutionRefusal> {
        match schema {
            "trust-wp.pure-expr.v1" => Ok(Self::BooleanText),
            "trust_wp.trust-formula.v1" | "trust-wp.trust-formula.v1" => Ok(Self::TypedJson),
            _ => Err(NativeExecutionRefusal::UnsupportedContractSchema(
                schema.into(),
            )),
        }
    }

    fn quote(self) -> Expr {
        c(match self {
            Self::BooleanText => "SemRNativeExecutionClaim.ContractFormat.booleanText",
            Self::TypedJson => "SemRNativeExecutionClaim.ContractFormat.typedJson",
        })
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NativeExecutionIntegerType {
    I8,
    I16,
    I32,
    I64,
    I128,
    Isize,
    U8,
    U16,
    U32,
    U64,
    U128,
    Usize,
}

impl NativeExecutionIntegerType {
    fn quote(self) -> Expr {
        c(match self {
            Self::I8 => "SemR.IntTy.i8",
            Self::I16 => "SemR.IntTy.i16",
            Self::I32 => "SemR.IntTy.i32",
            Self::I64 => "SemR.IntTy.i64",
            Self::I128 => "SemR.IntTy.i128",
            Self::Isize => "SemR.IntTy.isize",
            Self::U8 => "SemR.IntTy.u8",
            Self::U16 => "SemR.IntTy.u16",
            Self::U32 => "SemR.IntTy.u32",
            Self::U64 => "SemR.IntTy.u64",
            Self::U128 => "SemR.IntTy.u128",
            Self::Usize => "SemR.IntTy.usize",
        })
    }
}

/// Ordinary exact SemR type data, quoted without a caller-selected constant.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NativeExecutionType {
    Int(NativeExecutionIntegerType),
    Bool,
    Ptr,
    Unit,
    Never,
    Enum(u32),
    Struct(u32),
    Closure(u32),
    Storage {
        size: u64,
        align: u64,
    },
    Tensor {
        element: NativeExecutionIntegerType,
        rank: u64,
    },
}

impl NativeExecutionType {
    fn quote(self) -> Expr {
        match self {
            Self::Int(ty) => Expr::app(c("SemR.Ty.int"), ty.quote()),
            Self::Bool => c("SemR.Ty.bool"),
            Self::Ptr => c("SemR.Ty.ptr"),
            Self::Unit => c("SemR.Ty.unit"),
            Self::Never => c("SemR.Ty.never"),
            Self::Enum(id) => Expr::app(c("SemR.Ty.enum"), Expr::nat_lit(u64::from(id))),
            Self::Struct(id) => Expr::app(c("SemR.Ty.struct"), Expr::nat_lit(u64::from(id))),
            Self::Closure(id) => Expr::app(c("SemR.Ty.closure"), Expr::nat_lit(u64::from(id))),
            Self::Storage { size, align } => Expr::apps(
                c("SemR.Ty.storage"),
                [Expr::nat_lit(size), Expr::nat_lit(align)],
            ),
            Self::Tensor { element, rank } => {
                Expr::apps(c("SemR.Ty.tensor"), [element.quote(), Expr::nat_lit(rank)])
            }
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NativeExecutionPlace {
    Param(u32),
    Result(u32),
}

impl NativeExecutionPlace {
    fn quote(self) -> Expr {
        let (name, index) = match self {
            Self::Param(index) => ("SemRBooleanClaim.Place.param", index),
            Self::Result(index) => ("SemRBooleanClaim.Place.result", index),
        };
        Expr::app(c(name), Expr::nat_lit(u64::from(index)))
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NativeExecutionBinding {
    pub name: Vec<u8>,
    pub place: NativeExecutionPlace,
    pub ty: NativeExecutionType,
}

fn prod_type(first: Expr, second: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Prod"),
            vec![Level::zero(), Level::zero()],
        ),
        [first, second],
    )
}

fn pair(first_ty: Expr, second_ty: Expr, first: Expr, second: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Prod.mk"),
            vec![Level::zero(), Level::zero()],
        ),
        [first_ty, second_ty, first, second],
    )
}

fn bindings_quote(bindings: &[NativeExecutionBinding]) -> Expr {
    let name_ty = Expr::app(
        Expr::const_(Name::from_string("List"), vec![Level::zero()]),
        c("Nat"),
    );
    let place_ty = c("SemRBooleanClaim.Place");
    let ty = c("SemR.Ty");
    let tail_ty = prod_type(place_ty.clone(), ty.clone());
    list(
        prod_type(name_ty.clone(), tail_ty.clone()),
        bindings
            .iter()
            .map(|binding| {
                pair(
                    name_ty.clone(),
                    tail_ty.clone(),
                    bytes(&binding.name),
                    pair(
                        place_ty.clone(),
                        ty.clone(),
                        binding.place.quote(),
                        binding.ty.quote(),
                    ),
                )
            })
            .collect(),
    )
}

/// Independently expected data, derived from the complete original artifact by
/// its owner. This does not assert that the artifact is canonical or licensed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NativeExecutionSubject {
    pub module: Arc<NativeExecutionModuleSubject>,
    pub function: u32,
    pub codec_fuel: u64,
    pub contract_format: NativeExecutionContractFormat,
    pub contract_bytes: Arc<[u8]>,
    pub typed_bindings: Vec<NativeExecutionBinding>,
}

fn subject_arguments(expected: &NativeExecutionSubject) -> [Expr; 6] {
    [
        Expr::nat_lit(expected.codec_fuel),
        expected.module.quoted_bytes.clone(),
        Expr::nat_lit(u64::from(expected.function)),
        expected.contract_format.quote(),
        bytes(&expected.contract_bytes),
        bindings_quote(&expected.typed_bindings),
    ]
}

impl NativeExecutionSubject {
    /// Ordinary syntax for this exact original-byte goal; acceptance still
    /// requires a completed reference context and its closed-term check.
    pub fn expected_goal(&self) -> Expr {
        Expr::apps(
            c("SemRNativeExecutionClaim.originalExecution"),
            subject_arguments(self),
        )
    }
}

/// Untrusted proof data only. There is no caller proposition/model selector.
#[derive(Clone, Debug)]
pub struct NativeExecutionPacket {
    pub context: EnvDigest,
    pub proof: Expr,
}

#[derive(Debug, thiserror::Error)]
pub enum NativeExecutionRefusal {
    #[error("original module byte subject is empty")]
    EmptyModule,
    #[error("unsupported original contract schema {0}")]
    UnsupportedContractSchema(String),
    #[error(transparent)]
    Model(#[from] SemrModelRefusal),
    #[error("proof packet does not belong to the retained checked context")]
    ContextMismatch,
    #[error("exact original native execution goal was refused: {0}")]
    Proof(ReferenceRefusal),
}

pub struct UnboundNativeExecutionMathematicsContext {
    model: SemrModelContext,
}

const MODEL_ROOTS: &[&str] = &[
    "SemRNativeExecutionClaim.originalExecution",
    "SemRNativeExecutionClaim.originalContractHolds",
    "SemRNativeExecutionClaim.originalExecution_model_iff",
    "SemRNativeExecutionClaim.originalExecution_of_surjective",
    "SemRBooleanClaim.contractTypedEnv",
    "SemRBooleanClaim.checkedText",
    "SemRBooleanClaim.checkedTypedJson",
    "SemR.runBlob",
];

impl UnboundNativeExecutionMathematicsContext {
    /// Requires the existing private FULL-reference completion seal. The source
    /// owner separately authenticates original model source and artifact bytes.
    pub fn from_reference_base(base: ReferenceBase) -> Result<Self, NativeExecutionRefusal> {
        Ok(Self {
            model: SemrModelContext::from_reference_base(base, MODEL_ROOTS, &[])?,
        })
    }

    pub fn digest(&self) -> EnvDigest {
        self.model.kernel().env_digest()
    }

    /// Shared source comparison performs an actual completed reference replay
    /// and compares the complete fixed goal/codec/helper declaration closures.
    pub fn check_model_source(&self, original: &Environment) -> Result<(), NativeExecutionRefusal> {
        self.model.check_model_source(original).map_err(Into::into)
    }

    /// Ordinary quotation of the fixed Lean constant and every expected input.
    /// Returning syntax creates no acceptance; `check` always rebuilds it.
    pub fn expected_goal(&self, expected: &NativeExecutionSubject) -> Expr {
        expected.expected_goal()
    }

    pub fn check(
        &self,
        expected: &NativeExecutionSubject,
        packet: &NativeExecutionPacket,
    ) -> Result<CheckedUnboundNativeExecutionMathematics, NativeExecutionRefusal> {
        if packet.context != self.digest() {
            return Err(NativeExecutionRefusal::ContextMismatch);
        }
        let claim = self.expected_goal(expected);
        self.model
            .kernel()
            .check_closed_term(&claim, &packet.proof)
            .map_err(NativeExecutionRefusal::Proof)?;
        Ok(CheckedUnboundNativeExecutionMathematics {
            subject: expected.clone(),
            context: self.digest(),
            claim,
            proof: packet.proof.clone(),
        })
    }
}

/// Checked mathematics only: private fields, no Deserialize or grade/ABI/token
/// conversion. Its model environment remains explicitly unbound to source.
#[derive(Clone, Debug)]
pub struct CheckedUnboundNativeExecutionMathematics {
    subject: NativeExecutionSubject,
    context: EnvDigest,
    claim: Expr,
    proof: Expr,
}

impl CheckedUnboundNativeExecutionMathematics {
    pub fn subject(&self) -> &NativeExecutionSubject {
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{reference_base_closed, ClosedRecheckOptions};
    use std::collections::BTreeSet;

    #[test]
    fn native_context_requires_private_completion_and_direct_original_schema() {
        let missing = Name::from_string("MissingNativeExecutionModel");
        let mut base = reference_base_closed(
            &Environment::for_lean_replay(),
            &BTreeSet::from([missing.clone()]),
            &ClosedRecheckOptions::default(),
        )
        .unwrap();
        base.report.refusals.clear();
        base.report.extension_bindings_pinned = true;
        base.entry_refusals.clear();
        base.admitted.insert(missing);
        assert!(base.report.passed());
        assert!(matches!(
            UnboundNativeExecutionMathematicsContext::from_reference_base(base),
            Err(NativeExecutionRefusal::Model(
                SemrModelRefusal::IncompleteContext
            ))
        ));
        assert_eq!(
            NativeExecutionContractFormat::from_schema("trust-wp.pure-expr.v1").unwrap(),
            NativeExecutionContractFormat::BooleanText
        );
        assert_eq!(
            NativeExecutionContractFormat::from_schema("trust_wp.trust-formula.v1").unwrap(),
            NativeExecutionContractFormat::TypedJson
        );
        assert_eq!(
            NativeExecutionContractFormat::from_schema("trust-wp.trust-formula.v1").unwrap(),
            NativeExecutionContractFormat::TypedJson
        );
        assert!(matches!(
            NativeExecutionContractFormat::from_schema("trust-types.Formula@1"),
            Err(NativeExecutionRefusal::UnsupportedContractSchema(_))
        ));
    }
}
