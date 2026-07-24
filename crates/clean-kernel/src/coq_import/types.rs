// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Coq-side kernel IR used by the import scaffold.

use crate::expr::BinderInfo;
use serde::{Deserialize, Serialize};

/// Dotted Coq global or local name.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct CoqName {
    segments: Vec<String>,
}

impl CoqName {
    #[must_use]
    pub fn new(segments: Vec<String>) -> Self {
        Self { segments }
    }

    #[must_use]
    pub fn from_dotted(name: &str) -> Self {
        Self {
            segments: name
                .split('.')
                .filter(|segment| !segment.is_empty())
                .map(ToOwned::to_owned)
                .collect(),
        }
    }

    #[must_use]
    pub fn segments(&self) -> &[String] {
        &self.segments
    }

    #[must_use]
    pub fn as_dotted(&self) -> String {
        self.segments.join(".")
    }
}

/// Coq universe level expression.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum UniverseLevel {
    Zero,
    Succ(Box<UniverseLevel>),
    Max(Vec<UniverseLevel>),
    IMax(Box<UniverseLevel>, Box<UniverseLevel>),
    Param(String),
}

impl UniverseLevel {
    /// Build a numeric universe level as repeated `Succ`.
    #[must_use]
    pub fn from_index(index: u32) -> Self {
        let mut level = UniverseLevel::Zero;
        for _ in 0..index {
            level = UniverseLevel::Succ(Box::new(level));
        }
        level
    }
}

/// One universe instantiation on a global constant-like reference.
#[derive(Debug, Clone, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct UniverseInstance {
    pub levels: Vec<UniverseLevel>,
}

/// Coq sort.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum CoqSort {
    Prop,
    Set,
    Type(UniverseLevel),
}

/// Binder visibility/implicitness.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum CoqBinderKind {
    #[default]
    Default,
    Implicit,
    StrictImplicit,
    InstImplicit,
}

impl From<CoqBinderKind> for BinderInfo {
    fn from(value: CoqBinderKind) -> Self {
        match value {
            CoqBinderKind::Default => BinderInfo::Default,
            CoqBinderKind::Implicit => BinderInfo::Implicit,
            CoqBinderKind::StrictImplicit => BinderInfo::StrictImplicit,
            CoqBinderKind::InstImplicit => BinderInfo::InstImplicit,
        }
    }
}

/// Cast flavor.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum CastKind {
    Default,
    Vm,
    Native,
    Revert,
}

/// One Coq binder.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Binder {
    pub name: Option<String>,
    pub ty: Box<Constr>,
    pub info: CoqBinderKind,
}

impl Binder {
    #[must_use]
    pub fn explicit(name: impl Into<String>, ty: Constr) -> Self {
        Self {
            name: Some(name.into()),
            ty: Box::new(ty),
            info: CoqBinderKind::Default,
        }
    }

    #[must_use]
    pub fn anonymous(ty: Constr) -> Self {
        Self {
            name: None,
            ty: Box::new(ty),
            info: CoqBinderKind::Default,
        }
    }
}

/// Inductive reference.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct InductiveRef {
    pub name: CoqName,
    pub index: u32,
    pub universes: UniverseInstance,
}

/// Constructor reference.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct ConstructRef {
    pub inductive: CoqName,
    pub constructor_index: u32,
    pub constructor_name: Option<String>,
    pub universes: UniverseInstance,
}

/// Projection reference.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct ProjectionRef {
    pub inductive: CoqName,
    pub projection_index: u32,
    pub projection_name: Option<String>,
}

/// One case branch.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct CaseBranch {
    pub constructor: Option<ConstructRef>,
    pub binders: Vec<Binder>,
    pub body: Box<Constr>,
}

/// Case-analysis payload.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct CaseInfo {
    pub inductive: CoqName,
    pub universes: UniverseInstance,
    pub eliminator: Option<CoqName>,
    pub parameters: Vec<Constr>,
    pub indices: Vec<Constr>,
    pub motive: Box<Constr>,
    pub scrutinee: Box<Constr>,
    pub branches: Vec<CaseBranch>,
}

/// One mutually recursive body.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct FixBody {
    pub name: Option<String>,
    pub ty: Box<Constr>,
    pub body: Box<Constr>,
    pub recursive_arg: u32,
}

/// Fixpoint block.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct FixTerm {
    pub bodies: Vec<FixBody>,
    pub index: usize,
}

/// Co-fixpoint block.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct CoFixTerm {
    pub bodies: Vec<FixBody>,
    pub index: usize,
}

/// Coq kernel term (`Constr`).
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Constr {
    Rel(u32),
    Var(CoqName),
    Meta(u32),
    Evar {
        id: u32,
        args: Vec<Constr>,
    },
    Sort(CoqSort),
    Cast {
        term: Box<Constr>,
        kind: CastKind,
        ty: Box<Constr>,
    },
    Prod {
        binder: Binder,
        body: Box<Constr>,
    },
    Lambda {
        binder: Binder,
        body: Box<Constr>,
    },
    LetIn {
        name: Option<String>,
        type_: Box<Constr>,
        value: Box<Constr>,
        body: Box<Constr>,
    },
    App {
        func: Box<Constr>,
        args: Vec<Constr>,
    },
    Const {
        name: CoqName,
        universes: UniverseInstance,
    },
    Ind(InductiveRef),
    Construct(ConstructRef),
    Case(CaseInfo),
    Fix(FixTerm),
    CoFix(CoFixTerm),
    Proj {
        projection: ProjectionRef,
        term: Box<Constr>,
    },
}

impl Constr {
    #[must_use]
    pub fn rel(index: u32) -> Self {
        Self::Rel(index)
    }

    #[must_use]
    pub fn prop() -> Self {
        Self::Sort(CoqSort::Prop)
    }

    #[must_use]
    pub fn set() -> Self {
        Self::Sort(CoqSort::Set)
    }

    #[must_use]
    pub fn type0() -> Self {
        Self::Sort(CoqSort::Type(UniverseLevel::Zero))
    }

    #[must_use]
    pub fn app(func: Constr, args: Vec<Constr>) -> Self {
        Self::App {
            func: Box::new(func),
            args,
        }
    }

    #[must_use]
    pub fn const_(name: &str) -> Self {
        Self::Const {
            name: CoqName::from_dotted(name),
            universes: UniverseInstance::default(),
        }
    }
}

/// Coq constant declaration kind.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default, Serialize, Deserialize)]
pub enum ConstantDeclKind {
    Axiom,
    #[default]
    Definition,
    Theorem,
    Opaque,
}

/// One imported constant/theorem/axiom.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct ConstantDecl {
    pub kind: ConstantDeclKind,
    pub name: CoqName,
    pub universe_params: Vec<String>,
    pub type_: Constr,
    pub value: Option<Constr>,
}

/// One constructor inside an inductive body.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct ConstructorDecl {
    pub name: CoqName,
    pub type_: Constr,
}

/// One inductive family in a mutual block.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct InductiveBody {
    pub name: CoqName,
    pub type_: Constr,
    pub constructors: Vec<ConstructorDecl>,
}

/// Whether a declaration is inductive or coinductive.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default, Serialize, Deserialize)]
pub enum InductiveKind {
    #[default]
    Inductive,
    CoInductive,
}

/// One mutual inductive declaration block.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct MutualInductiveDecl {
    pub kind: InductiveKind,
    pub universe_params: Vec<String>,
    pub num_params: u32,
    pub params: Vec<Binder>,
    pub bodies: Vec<InductiveBody>,
}

/// One top-level declaration extracted from SerAPI output.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum GlobalDecl {
    Constant(ConstantDecl),
    Inductive(MutualInductiveDecl),
}
