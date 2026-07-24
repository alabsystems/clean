// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof state serialization for debugging, replay, and persistence.
//!
//! Provides a simplified, serializable representation of [`ProofState`], [`Goal`],
//! and [`Expr`] types. The serialized format is JSON-based, human-readable, and
//! versioned for forward compatibility.
//!
//! # Usage
//!
//! ```text
//! let serialized = serialize_proof_state(&proof_state);
//! let json = serialized.to_json()?;
//! let deserialized = SerializedProofState::from_json(&json)?;
//! assert_eq!(serialized, deserialized);
//! ```

use serde::{Deserialize, Serialize};

use super::core::{Goal, LocalDecl, ProofState};
use clean_kernel::expr::ExprKind;
use clean_kernel::{BinderInfo, Expr};

/// Current serialization format version.
const CURRENT_VERSION: u32 = 1;

// =============================================================================
// Error type
// =============================================================================

/// Errors that can occur during proof state serialization/deserialization.
#[derive(Debug, thiserror::Error)]
pub(crate) enum SerError {
    /// JSON serialization or deserialization failed.
    #[error("JSON serialization error: {0}")]
    Json(#[from] serde_json::Error),
    /// The deserialized format version does not match the current version.
    #[error("invalid format version: expected {expected}, got {got}")]
    VersionMismatch {
        /// The version this code expects.
        expected: u32,
        /// The version found in the serialized data.
        got: u32,
    },
}

// =============================================================================
// Serialized types
// =============================================================================

/// Serialized representation of a proof state.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub(crate) struct SerializedProofState {
    /// Active goals in the proof.
    pub goals: Vec<SerializedGoal>,
    /// Metavariable assignments: `(meta_name, assigned_expr)`.
    pub meta_assignments: Vec<(String, SerializedExpr)>,
    /// History of tactic applications (populated externally).
    pub tactic_history: Vec<TacticStep>,
    /// Format version for compatibility checking.
    pub version: u32,
}

/// Serialized representation of a single proof goal.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub(crate) struct SerializedGoal {
    /// Metavariable identifier (e.g., `"?m0"`).
    pub id: String,
    /// The target type to prove.
    pub target_type: SerializedExpr,
    /// Local declarations available as hypotheses.
    pub local_context: Vec<SerializedLocalDecl>,
    /// Whether this goal has been closed.
    pub is_closed: bool,
}

/// Serialized representation of a local declaration (hypothesis or let-binding).
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub(crate) struct SerializedLocalDecl {
    /// Display name.
    pub name: String,
    /// Type of the declaration.
    pub ty: SerializedExpr,
    /// Optional value for let-bindings.
    pub value: Option<SerializedExpr>,
    /// Binder info string: `"default"`, `"implicit"`, `"strict_implicit"`, `"inst_implicit"`.
    pub binder_info: String,
}

/// Simplified expression representation for serialization.
///
/// This is a lossy conversion from [`Expr`] / [`ExprKind`] that captures the
/// essential structure while being JSON-friendly. Complex or uncommon expression
/// kinds (cubical, ZFC, etc.) are represented as `Other(description)`.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub(crate) enum SerializedExpr {
    /// Bound variable (de Bruijn index).
    Var(usize),
    /// Sort (`"Prop"`, `"Type"`, `"Type 1"`, etc.).
    Sort(String),
    /// Constant with universe level names.
    Const(String, Vec<String>),
    /// Function application.
    App(Box<SerializedExpr>, Box<SerializedExpr>),
    /// Lambda abstraction: `(binder_info, domain_type, body)`.
    Lambda(String, Box<SerializedExpr>, Box<SerializedExpr>),
    /// Pi / forall type: `(binder_info, domain_type, codomain)`.
    Pi(String, Box<SerializedExpr>, Box<SerializedExpr>),
    /// Literal value as string.
    Lit(String),
    /// Metavariable reference.
    Meta(String),
    /// Free variable reference.
    FVar(String),
    /// Catch-all for complex or uncommon expression kinds.
    Other(String),
}

/// A recorded tactic application step.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub(crate) struct TacticStep {
    /// Name of the tactic that was applied.
    pub tactic_name: String,
    /// Arguments passed to the tactic.
    pub args: Vec<String>,
    /// Number of open goals before the tactic ran.
    pub goals_before: usize,
    /// Number of open goals after the tactic ran.
    pub goals_after: usize,
    /// Whether the tactic succeeded.
    pub success: bool,
}

// =============================================================================
// Serialization functions
// =============================================================================

/// Serialize a [`ProofState`] into its portable representation.
pub(crate) fn serialize_proof_state(state: &ProofState) -> SerializedProofState {
    let goals = state.goals().iter().map(serialize_goal).collect();

    let meta_assignments = state
        .metas()
        .iter()
        .filter_map(|(id, meta)| {
            meta.assignment.as_ref().map(|assigned| {
                let name = format!("?m{}", id.as_u64());
                (name, serialize_expr(assigned))
            })
        })
        .collect();

    SerializedProofState {
        goals,
        meta_assignments,
        tactic_history: Vec::new(),
        version: CURRENT_VERSION,
    }
}

/// Serialize a single [`Goal`].
pub(crate) fn serialize_goal(goal: &Goal) -> SerializedGoal {
    SerializedGoal {
        id: format!("?m{}", goal.meta_id.as_u64()),
        target_type: serialize_expr(&goal.target),
        local_context: goal.local_ctx.iter().map(serialize_local_decl).collect(),
        is_closed: false,
    }
}

/// Serialize an [`Expr`] into its simplified representation.
///
/// This is a lossy conversion: complex expression kinds (cubical, ZFC,
/// let-bindings) are collapsed into `Other(description)`. Metadata wrappers
/// are transparent.
pub(crate) fn serialize_expr(expr: &Expr) -> SerializedExpr {
    match expr.kind() {
        ExprKind::BVar(n) => SerializedExpr::Var(*n as usize),
        ExprKind::FVar(id) => SerializedExpr::FVar(format!("fvar_{}", id.as_u64())),
        ExprKind::Sort(level) => SerializedExpr::Sort(format!("{level}")),
        ExprKind::Const(name, levels) => SerializedExpr::Const(
            format!("{name}"),
            levels.iter().map(|l| format!("{l}")).collect(),
        ),
        ExprKind::App(f, a) => {
            SerializedExpr::App(Box::new(serialize_expr(f)), Box::new(serialize_expr(a)))
        }
        ExprKind::Lam(bd, ty, body) => SerializedExpr::Lambda(
            binder_info_str(bd.info),
            Box::new(serialize_expr(ty)),
            Box::new(serialize_expr(body)),
        ),
        ExprKind::Pi(bd, ty, body) => SerializedExpr::Pi(
            binder_info_str(bd.info),
            Box::new(serialize_expr(ty)),
            Box::new(serialize_expr(body)),
        ),
        ExprKind::Lit(literal) => SerializedExpr::Lit(format!("{literal:?}")),
        ExprKind::Let(name, _ty, _val, _body, _) => {
            SerializedExpr::Other(format!("let {name} : ... := ... in ..."))
        }
        ExprKind::Proj(name, idx, _inner) => SerializedExpr::Other(format!("{name}.{idx}")),
        ExprKind::MData(_, inner) => serialize_expr(inner),
        _ => SerializedExpr::Other("\u{ab}complex\u{bb}".to_owned()),
    }
}

/// Serialize a [`LocalDecl`] into its portable representation.
pub(crate) fn serialize_local_decl(decl: &LocalDecl) -> SerializedLocalDecl {
    SerializedLocalDecl {
        name: decl.name.clone(),
        ty: serialize_expr(&decl.ty),
        value: decl.value.as_ref().map(serialize_expr),
        binder_info: "default".to_owned(),
    }
}

/// Convert a [`BinderInfo`] to its string representation.
fn binder_info_str(info: BinderInfo) -> String {
    match info {
        BinderInfo::Default => "default".to_owned(),
        BinderInfo::Implicit => "implicit".to_owned(),
        BinderInfo::StrictImplicit => "strict_implicit".to_owned(),
        BinderInfo::InstImplicit => "inst_implicit".to_owned(),
    }
}

// =============================================================================
// SerializedProofState methods
// =============================================================================

impl SerializedProofState {
    /// Serialize this proof state to a pretty-printed JSON string.
    pub(crate) fn to_json(&self) -> Result<String, SerError> {
        serde_json::to_string_pretty(self).map_err(SerError::from)
    }

    /// Deserialize a proof state from a JSON string, checking format version.
    pub(crate) fn from_json(json: &str) -> Result<Self, SerError> {
        let state: Self = serde_json::from_str(json)?;
        if state.version != CURRENT_VERSION {
            return Err(SerError::VersionMismatch {
                expected: CURRENT_VERSION,
                got: state.version,
            });
        }
        Ok(state)
    }

    /// Return the number of goals in this serialized state.
    pub(crate) fn goal_count(&self) -> usize {
        self.goals.len()
    }

    /// Check whether the proof is solved (no open goals remain).
    pub(crate) fn is_solved(&self) -> bool {
        self.goals.is_empty() || self.goals.iter().all(|g| g.is_closed)
    }
}

// =============================================================================
// TacticStep methods
// =============================================================================

impl TacticStep {
    /// Create a new tactic step with the given name and default fields.
    pub(crate) fn new(name: &str) -> Self {
        Self {
            tactic_name: name.to_owned(),
            args: Vec::new(),
            goals_before: 0,
            goals_after: 0,
            success: false,
        }
    }
}

// =============================================================================
// SerializedExpr pretty printing
// =============================================================================

impl SerializedExpr {
    /// Produce a human-readable string representation of this expression.
    pub(crate) fn pretty_print(&self) -> String {
        match self {
            SerializedExpr::Var(n) => format!("#{n}"),
            SerializedExpr::Sort(s) => s.clone(),
            SerializedExpr::Const(name, levels) if levels.is_empty() => name.clone(),
            SerializedExpr::Const(name, levels) => {
                format!("{name}.{{{}}}", levels.join(", "))
            }
            SerializedExpr::App(f, a) => {
                format!("({} {})", f.pretty_print(), a.pretty_print())
            }
            SerializedExpr::Lambda(bi, ty, body) => {
                format!(
                    "fun ({bi} : {}) => {}",
                    ty.pretty_print(),
                    body.pretty_print()
                )
            }
            SerializedExpr::Pi(bi, ty, body) => {
                format!("({bi} : {}) -> {}", ty.pretty_print(), body.pretty_print())
            }
            SerializedExpr::Lit(s) => s.clone(),
            SerializedExpr::Meta(s) => s.clone(),
            SerializedExpr::FVar(s) => s.clone(),
            SerializedExpr::Other(s) => s.clone(),
        }
    }
}
