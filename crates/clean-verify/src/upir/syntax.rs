// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Core UPIR syntax and proof metadata.

use crate::upir::{LeanTranslationError, UpirValidationError};
use clean_elab::ElabCtx;
use clean_kernel::{Environment, Expr};
use clean_parser::parse_expr;
use std::fmt;

/// Source provenance for imported proofs and terms.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum SourceSystem {
    Lean4,
    Clean,
    Coq,
    Agda,
    IsabelleHol,
    HolLight,
    Hol4,
    Metamath,
    Mizar,
    Other(String),
}

/// A qualified name represented segment-by-segment.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct UpirName {
    segments: Vec<String>,
}

impl UpirName {
    /// Create a name from explicit path segments.
    #[must_use]
    pub fn new(segments: Vec<String>) -> Self {
        Self { segments }
    }

    /// Create a name from a dotted path.
    #[must_use]
    pub fn from_dotted(name: &str) -> Self {
        Self {
            segments: name.split('.').map(ToOwned::to_owned).collect(),
        }
    }

    /// Borrow the underlying segments.
    #[must_use]
    pub fn segments(&self) -> &[String] {
        &self.segments
    }

    pub(crate) fn validate(&self) -> Result<(), UpirValidationError> {
        if self.segments.is_empty() {
            return Err(UpirValidationError::EmptyName {
                kind: "qualified name",
            });
        }
        if self.segments.iter().any(String::is_empty) {
            return Err(UpirValidationError::EmptyNameSegment);
        }
        Ok(())
    }
}

impl fmt::Display for UpirName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.segments.join("."))
    }
}

/// Universe level representation shared across source systems.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum UpirLevel {
    Zero,
    Succ(Box<UpirLevel>),
    Max(Box<UpirLevel>, Box<UpirLevel>),
    IMax(Box<UpirLevel>, Box<UpirLevel>),
    Param(String),
}

/// Sorts that can be represented in the Lean-compatible core.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum UpirSort {
    Prop,
    Type(UpirLevel),
    Foreign {
        source: SourceSystem,
        descriptor: String,
    },
}

/// Binder style preserved for round-trip and Lean rendering.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BinderStyle {
    Explicit,
    Implicit,
    StrictImplicit,
    InstanceImplicit,
}

/// One local binder.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct UpirBinder {
    pub name: Option<String>,
    pub style: BinderStyle,
}

impl UpirBinder {
    /// Explicit named binder.
    #[must_use]
    pub fn explicit(name: impl Into<String>) -> Self {
        Self {
            name: Some(name.into()),
            style: BinderStyle::Explicit,
        }
    }

    /// Anonymous explicit binder.
    #[must_use]
    pub fn anonymous() -> Self {
        Self {
            name: None,
            style: BinderStyle::Explicit,
        }
    }
}

/// Source-location annotation.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SourceLoc {
    pub file: String,
    pub line: u32,
    pub column: u32,
}

/// Literal values that can appear in imported proofs.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum UpirLiteral {
    Nat(u64),
    Bool(bool),
    String(String),
}

/// Foreign constructs that UPIR can preserve but Lean cannot directly render.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum UpirForeignExpr {
    CoqSet,
    CoqSProp,
    AgdaInterval,
    HolType {
        repr: String,
    },
    HolConst {
        name: UpirName,
        type_args: Vec<String>,
    },
    MetamathExpr {
        symbols: Vec<String>,
    },
    MizarTerm {
        repr: String,
    },
}

/// Pattern syntax for UPIR match arms.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum UpirPattern {
    Wildcard,
    Var(Option<String>),
    Literal(UpirLiteral),
    Ctor {
        name: UpirName,
        args: Vec<UpirPattern>,
    },
}

impl UpirPattern {
    pub(crate) fn bound_names(&self, out: &mut Vec<Option<String>>) {
        match self {
            Self::Wildcard | Self::Literal(_) => {}
            Self::Var(name) => out.push(name.clone()),
            Self::Ctor { args, .. } => {
                for arg in args {
                    arg.bound_names(out);
                }
            }
        }
    }
}

/// Match-expression style preserved from the source system.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum MatchStyle {
    Pattern,
    Eliminator,
}

/// One branch in a match expression.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct UpirMatchArm {
    pub pattern: UpirPattern,
    pub body: Box<UpirExpr>,
}

/// Projection target.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum UpirProjection {
    Index(u32),
    Field(String),
}

/// UPIR expression tree.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum UpirExpr {
    Var(u32),
    Sort(UpirSort),
    Const {
        name: UpirName,
        universes: Vec<UpirLevel>,
        source: SourceSystem,
    },
    App(Box<UpirExpr>, Box<UpirExpr>),
    Lambda {
        binder: UpirBinder,
        domain: Box<UpirExpr>,
        body: Box<UpirExpr>,
    },
    Pi {
        binder: UpirBinder,
        domain: Box<UpirExpr>,
        body: Box<UpirExpr>,
    },
    Let {
        binder: UpirBinder,
        type_: Box<UpirExpr>,
        value: Box<UpirExpr>,
        body: Box<UpirExpr>,
    },
    Match {
        scrutinee: Box<UpirExpr>,
        motive: Option<Box<UpirExpr>>,
        arms: Vec<UpirMatchArm>,
        style: MatchStyle,
    },
    Proj {
        expr: Box<UpirExpr>,
        projection: UpirProjection,
    },
    Annot {
        expr: Box<UpirExpr>,
        type_: Box<UpirExpr>,
    },
    Literal(UpirLiteral),
    SourceLoc {
        expr: Box<UpirExpr>,
        loc: SourceLoc,
    },
    Hole {
        id: u64,
        type_: Option<Box<UpirExpr>>,
    },
    Foreign(UpirForeignExpr),
}

impl UpirExpr {
    /// Construct a function application.
    #[must_use]
    pub fn app(func: Self, arg: Self) -> Self {
        Self::App(Box::new(func), Box::new(arg))
    }

    /// Render the expression as Lean source.
    ///
    /// # Errors
    /// Returns [`LeanTranslationError`] when the term cannot be rendered as Lean.
    pub fn to_lean_source(&self) -> Result<String, LeanTranslationError> {
        super::lean::render_expr(self)
    }

    /// Parse and elaborate the rendered Lean term in an environment.
    ///
    /// # Errors
    /// Returns [`LeanTranslationError`] when rendering, parsing, or elaboration fails.
    pub fn elaborate_in(&self, env: &Environment) -> Result<Expr, LeanTranslationError> {
        let source = self.to_lean_source()?;
        let surface = parse_expr(&source)
            .map_err(|err| LeanTranslationError::Parse(source.clone(), err.to_string()))?;
        let mut ctx = ElabCtx::new(env);
        ctx.elaborate(&surface)
            .map_err(|err| LeanTranslationError::Elab(source, err.to_string()))
    }

    /// Structural validation for a standalone term.
    ///
    /// # Errors
    /// Returns [`UpirValidationError`] if the expression is not structurally valid.
    pub fn validate(&self) -> Result<(), UpirValidationError> {
        super::validate::validate_expr(self, &[])
    }
}

/// A proof object ready for validation or translation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UpirProof {
    pub name: UpirName,
    pub source: SourceSystem,
    pub universe_params: Vec<String>,
    pub statement: Option<UpirExpr>,
    pub proof: UpirExpr,
}

impl UpirProof {
    /// Construct a new UPIR proof bundle.
    #[must_use]
    pub fn new(
        name: UpirName,
        source: SourceSystem,
        universe_params: Vec<String>,
        statement: Option<UpirExpr>,
        proof: UpirExpr,
    ) -> Self {
        Self {
            name,
            source,
            universe_params,
            statement,
            proof,
        }
    }

    /// Structural validation for the entire proof bundle.
    ///
    /// # Errors
    /// Returns [`UpirValidationError`] if the proof is not structurally valid.
    pub fn validate(&self) -> Result<(), UpirValidationError> {
        super::validate::validate_proof(self)
    }

    /// Render the proof term alone as Lean source.
    ///
    /// # Errors
    /// Returns [`LeanTranslationError`] when the proof term is not Lean-renderable.
    pub fn to_lean_term_source(&self) -> Result<String, LeanTranslationError> {
        self.validate().map_err(LeanTranslationError::Validation)?;
        self.proof.to_lean_source()
    }

    /// Render a Lean theorem declaration for the proof.
    ///
    /// # Errors
    /// Returns [`LeanTranslationError`] when validation fails or the proof cannot
    /// be rendered as a Lean theorem declaration.
    pub fn to_lean_declaration(&self) -> Result<String, LeanTranslationError> {
        self.validate().map_err(LeanTranslationError::Validation)?;
        let statement = self
            .statement
            .as_ref()
            .ok_or(LeanTranslationError::MissingStatement)?;
        let name = super::lean::render_global_name(&self.name)?;
        let universe_params = if self.universe_params.is_empty() {
            String::new()
        } else {
            format!(".{{{}}}", self.universe_params.join(", "))
        };
        let statement = statement.to_lean_source()?;
        let proof = self.proof.to_lean_source()?;
        Ok(format!(
            "theorem {name}{universe_params} : {statement} := {proof}"
        ))
    }
}
