// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Simplified formal model of the clean kernel for bootstrap verification.
//!
//! Reuses [`KExpr`] and [`Level`] from [`crate::spec::core_spec::expr_model`]
//! (registered as `KExpr` and `Level` inductive types in the spec system) and
//! provides a standalone type inference and definitional equality checker
//! operating on these model types.
//!
//! This mirrors [`crate::bootstrap_checker::BootstrapChecker`] but operates on
//! the formal model types instead of the kernel's concrete `Expr`/`Level`,
//! bridging the gap between the Rust implementation and the Lean 4 formalization.

use std::collections::HashMap;

/// A kernel expression in the formal model.
///
/// Mirrors the `KExpr` inductive type from `spec/core_spec/expr_model.rs`:
/// ```text
/// inductive KExpr : Type
/// | sort : Nat -> KExpr
/// | bvar : Nat -> KExpr
/// | app : KExpr -> KExpr -> KExpr
/// | lam : KExpr -> KExpr -> KExpr
/// | pi : KExpr -> KExpr -> KExpr
/// | let_ : KExpr -> KExpr -> KExpr -> KExpr
/// | const : Name -> ListType Level -> KExpr
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum KernelExpr {
    /// Sort(n): the universe Sort n. Sort(0) = Prop.
    Sort(u32),
    /// Bound variable with de Bruijn index.
    BVar(u32),
    /// Application: `f a`.
    App(Box<KernelExpr>, Box<KernelExpr>),
    /// Lambda abstraction: `fun (x : ty) => body`.
    Lam(Box<KernelExpr>, Box<KernelExpr>),
    /// Dependent function type: `(x : ty) -> body`.
    Pi(Box<KernelExpr>, Box<KernelExpr>),
    /// Let binding: `let x : ty := val in body`.
    Let(Box<KernelExpr>, Box<KernelExpr>, Box<KernelExpr>),
    /// Named constant with universe level arguments.
    Const(String, Vec<KernelLevel>),
}

/// A universe level in the formal model.
///
/// Mirrors the `Level` inductive type from `spec/core_spec/expr_model.rs`:
/// ```text
/// inductive Level : Type
/// | zero : Level
/// | succ : Level -> Level
/// | max : Level -> Level -> Level
/// | imax : Level -> Level -> Level
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum KernelLevel {
    /// Universe level 0.
    Zero,
    /// Successor: `succ l`.
    Succ(Box<KernelLevel>),
    /// Maximum: `max l1 l2`.
    Max(Box<KernelLevel>, Box<KernelLevel>),
    /// Impredicative maximum: `imax l1 l2`.
    IMax(Box<KernelLevel>, Box<KernelLevel>),
}

/// An entry in the kernel environment: (type, optional definition value).
#[derive(Debug, Clone)]
struct EnvEntry {
    ty: KernelExpr,
    value: Option<KernelExpr>,
}

/// A simplified kernel environment mapping constant names to their types and values.
#[derive(Debug, Clone, Default)]
pub struct KernelEnv {
    entries: HashMap<String, EnvEntry>,
}

impl KernelEnv {
    /// Create an empty kernel environment.
    #[must_use]
    pub fn empty() -> Self {
        Self::default()
    }

    /// Add a constant with a type and optional definition body.
    pub fn add_const(&mut self, name: &str, ty: KernelExpr, value: Option<KernelExpr>) {
        self.entries
            .insert(name.to_string(), EnvEntry { ty, value });
    }

    /// Look up the type of a constant.
    #[must_use]
    pub fn get_type(&self, name: &str) -> Option<&KernelExpr> {
        self.entries.get(name).map(|e| &e.ty)
    }

    /// Look up the definition body of a constant (None for axioms/opaques).
    #[must_use]
    pub fn get_value(&self, name: &str) -> Option<&KernelExpr> {
        self.entries.get(name).and_then(|e| e.value.as_ref())
    }
}

/// Errors from model type inference.
#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
pub enum ModelError {
    /// Bound variable index out of range.
    #[error("unbound variable index {0} in context of depth {1}")]
    UnboundVariable(u32, usize),

    /// Expected a Sort type, got something else.
    #[error("expected Sort, got {0:?}")]
    ExpectedSort(KernelExpr),

    /// Expected a Pi (function) type for application.
    #[error("expected Pi type for function, got {0:?}")]
    ExpectedPi(KernelExpr),

    /// Type mismatch: an argument or let value does not match its expected type.
    #[error("type mismatch: expected {expected:?}, got {actual:?}")]
    TypeMismatch {
        expected: KernelExpr,
        actual: KernelExpr,
    },

    /// Unknown constant name.
    #[error("unknown constant: {0}")]
    UnknownConst(String),
}

/// Result of model type inference.
pub type TypeInferenceResult = Result<KernelExpr, ModelError>;

/// Infer the type of a `KernelExpr` in the given environment and local context.
///
/// The context is a stack of types for bound variables (index 0 is the
/// innermost binder). Implements the standard typing rules:
///
/// - **Sort**: `Sort n : Sort (n+1)`
/// - **BVar**: looked up from the context
/// - **Pi**: `(x : A) -> B : Sort (imax level(A) level(B))`
/// - **Lam**: `fun (x : A) => b : (x : A) -> infer(b)`
/// - **App**: `f a : B[a/x]` when `f : (x : A) -> B` and `a : A`
/// - **Let**: `let x : T := v in b : infer(b[v/x])`
/// - **Const**: looked up from the environment
pub fn model_infer_type(
    env: &KernelEnv,
    expr: &KernelExpr,
    ctx: &[KernelExpr],
) -> TypeInferenceResult {
    match expr {
        KernelExpr::Sort(n) => Ok(KernelExpr::Sort(n + 1)),

        KernelExpr::BVar(idx) => {
            let depth = ctx.len();
            let idx_usize = *idx as usize;
            if idx_usize >= depth {
                return Err(ModelError::UnboundVariable(*idx, depth));
            }
            // de Bruijn: index 0 is the most recent binder (last in ctx)
            let pos = depth - 1 - idx_usize;
            Ok(lift(&ctx[pos], (depth - pos) as u32))
        }

        KernelExpr::Pi(domain, codomain) => {
            let domain_ty = model_infer_type(env, domain, ctx)?;
            let domain_level = expect_sort(&domain_ty)?;

            let mut extended_ctx = ctx.to_vec();
            extended_ctx.push(*domain.clone());
            let codomain_ty = model_infer_type(env, codomain, &extended_ctx)?;
            let codomain_level = expect_sort(&codomain_ty)?;

            Ok(KernelExpr::Sort(imax_level(domain_level, codomain_level)))
        }

        KernelExpr::Lam(domain, body) => {
            let domain_ty = model_infer_type(env, domain, ctx)?;
            let _ = expect_sort(&domain_ty)?;

            let mut extended_ctx = ctx.to_vec();
            extended_ctx.push(*domain.clone());
            let body_ty = model_infer_type(env, body, &extended_ctx)?;

            Ok(KernelExpr::Pi(domain.clone(), Box::new(body_ty)))
        }

        KernelExpr::App(fun, arg) => {
            let fun_ty = model_infer_type(env, fun, ctx)?;
            let fun_ty_whnf = model_whnf(env, &fun_ty);
            let (domain, codomain) = expect_pi(&fun_ty_whnf)?;

            let arg_ty = model_infer_type(env, arg, ctx)?;
            if !model_is_def_eq(env, &arg_ty, domain) {
                return Err(ModelError::TypeMismatch {
                    expected: domain.clone(),
                    actual: arg_ty,
                });
            }

            Ok(instantiate(codomain, arg))
        }

        KernelExpr::Let(ty, val, body) => {
            // Check-mode let typing: the annotation must itself inhabit a
            // universe, and the value must have exactly that annotated type.
            // These are the premises reflected by KernelInfers.let_; merely
            // inferring both expressions independently would accept an
            // ill-typed annotated let and make the executable model diverge
            // from its claimed algorithmic-soundness relation.
            let annotation_ty = model_infer_type(env, ty, ctx)?;
            let annotation_ty_whnf = model_whnf(env, &annotation_ty);
            let _ = expect_sort(&annotation_ty_whnf)?;

            let val_ty = model_infer_type(env, val, ctx)?;
            if !model_is_def_eq(env, &val_ty, ty) {
                return Err(ModelError::TypeMismatch {
                    expected: *ty.clone(),
                    actual: val_ty,
                });
            }

            // Infer under the declared binder, then zeta-substitute the value
            // into the resulting dependent body type. This is the direct
            // de-Bruijn analogue of clean-kernel's check-mode Let arm.
            let mut extended_ctx = ctx.to_vec();
            extended_ctx.push(*ty.clone());
            let body_ty = model_infer_type(env, body, &extended_ctx)?;
            Ok(instantiate(&body_ty, val))
        }

        KernelExpr::Const(name, _levels) => env
            .get_type(name)
            .cloned()
            .ok_or_else(|| ModelError::UnknownConst(name.clone())),
    }
}

/// Check definitional equality of two model expressions.
///
/// Reduces both sides to WHNF and compares structurally. Supports:
/// - Reflexivity (syntactic equality after WHNF)
/// - Beta reduction (via WHNF)
/// - Delta reduction (constant unfolding via WHNF)
#[must_use]
pub fn model_is_def_eq(env: &KernelEnv, a: &KernelExpr, b: &KernelExpr) -> bool {
    let a_whnf = model_whnf(env, a);
    let b_whnf = model_whnf(env, b);
    def_eq_whnf(env, &a_whnf, &b_whnf)
}

// ── Internal helpers ────────────────────────────────────────────────────────

/// Extract the universe level number from a Sort, or return an error.
fn expect_sort(ty: &KernelExpr) -> Result<u32, ModelError> {
    match ty {
        KernelExpr::Sort(n) => Ok(*n),
        other => Err(ModelError::ExpectedSort(other.clone())),
    }
}

/// Extract (domain, codomain) from a Pi type, or return an error.
fn expect_pi(ty: &KernelExpr) -> Result<(&KernelExpr, &KernelExpr), ModelError> {
    match ty {
        KernelExpr::Pi(domain, codomain) => Ok((domain, codomain)),
        other => Err(ModelError::ExpectedPi(other.clone())),
    }
}

/// Compute the impredicative maximum of two concrete universe levels.
///
/// `imax a b = 0` when `b = 0` (Prop is impredicative), otherwise `max a b`.
fn imax_level(a: u32, b: u32) -> u32 {
    if b == 0 {
        0
    } else {
        a.max(b)
    }
}

/// Weak-head normal form reduction for model expressions.
///
/// Performs beta reduction (lambda application) and delta reduction
/// (constant unfolding) at the head position.
fn model_whnf(env: &KernelEnv, expr: &KernelExpr) -> KernelExpr {
    match expr {
        KernelExpr::App(fun, arg) => {
            let fun_whnf = model_whnf(env, fun);
            match &fun_whnf {
                KernelExpr::Lam(_, body) => model_whnf(env, &instantiate(body, arg)),
                _ => KernelExpr::App(Box::new(fun_whnf), arg.clone()),
            }
        }
        KernelExpr::Let(_, val, body) => model_whnf(env, &instantiate(body, val)),
        KernelExpr::Const(name, _) => {
            if let Some(value) = env.get_value(name) {
                model_whnf(env, value)
            } else {
                expr.clone()
            }
        }
        _ => expr.clone(),
    }
}

/// Structural equality after WHNF reduction.
fn def_eq_whnf(env: &KernelEnv, a: &KernelExpr, b: &KernelExpr) -> bool {
    match (a, b) {
        (KernelExpr::Sort(n1), KernelExpr::Sort(n2)) => n1 == n2,
        (KernelExpr::BVar(i), KernelExpr::BVar(j)) => i == j,
        (KernelExpr::App(f1, a1), KernelExpr::App(f2, a2)) => {
            model_is_def_eq(env, f1, f2) && model_is_def_eq(env, a1, a2)
        }
        (KernelExpr::Lam(ty1, b1), KernelExpr::Lam(ty2, b2))
        | (KernelExpr::Pi(ty1, b1), KernelExpr::Pi(ty2, b2)) => {
            model_is_def_eq(env, ty1, ty2) && model_is_def_eq(env, b1, b2)
        }
        (KernelExpr::Const(n1, ls1), KernelExpr::Const(n2, ls2)) => n1 == n2 && ls1 == ls2,
        _ => false,
    }
}

/// Lift (shift) bound variable indices >= `cutoff` by `amount`.
fn lift_at(expr: &KernelExpr, cutoff: u32, amount: u32) -> KernelExpr {
    match expr {
        KernelExpr::Sort(n) => KernelExpr::Sort(*n),
        KernelExpr::BVar(idx) => {
            if *idx >= cutoff {
                KernelExpr::BVar(idx + amount)
            } else {
                KernelExpr::BVar(*idx)
            }
        }
        KernelExpr::App(f, a) => KernelExpr::App(
            Box::new(lift_at(f, cutoff, amount)),
            Box::new(lift_at(a, cutoff, amount)),
        ),
        KernelExpr::Lam(ty, body) => KernelExpr::Lam(
            Box::new(lift_at(ty, cutoff, amount)),
            Box::new(lift_at(body, cutoff + 1, amount)),
        ),
        KernelExpr::Pi(ty, body) => KernelExpr::Pi(
            Box::new(lift_at(ty, cutoff, amount)),
            Box::new(lift_at(body, cutoff + 1, amount)),
        ),
        KernelExpr::Let(ty, val, body) => KernelExpr::Let(
            Box::new(lift_at(ty, cutoff, amount)),
            Box::new(lift_at(val, cutoff, amount)),
            Box::new(lift_at(body, cutoff + 1, amount)),
        ),
        KernelExpr::Const(name, levels) => KernelExpr::Const(name.clone(), levels.clone()),
    }
}

/// Lift all bound variables by `amount` (cutoff = 0).
fn lift(expr: &KernelExpr, amount: u32) -> KernelExpr {
    lift_at(expr, 0, amount)
}

/// Substitute `val` for `BVar(depth)`, adjusting indices under binders.
fn instantiate_at(body: &KernelExpr, val: &KernelExpr, depth: u32) -> KernelExpr {
    match body {
        KernelExpr::Sort(n) => KernelExpr::Sort(*n),
        KernelExpr::BVar(idx) => {
            if *idx < depth {
                KernelExpr::BVar(*idx)
            } else if *idx == depth {
                lift_at(val, 0, depth)
            } else {
                KernelExpr::BVar(idx - 1)
            }
        }
        KernelExpr::App(f, a) => KernelExpr::App(
            Box::new(instantiate_at(f, val, depth)),
            Box::new(instantiate_at(a, val, depth)),
        ),
        KernelExpr::Lam(ty, b) => KernelExpr::Lam(
            Box::new(instantiate_at(ty, val, depth)),
            Box::new(instantiate_at(b, val, depth + 1)),
        ),
        KernelExpr::Pi(ty, b) => KernelExpr::Pi(
            Box::new(instantiate_at(ty, val, depth)),
            Box::new(instantiate_at(b, val, depth + 1)),
        ),
        KernelExpr::Let(ty, v, b) => KernelExpr::Let(
            Box::new(instantiate_at(ty, val, depth)),
            Box::new(instantiate_at(v, val, depth)),
            Box::new(instantiate_at(b, val, depth + 1)),
        ),
        KernelExpr::Const(name, levels) => KernelExpr::Const(name.clone(), levels.clone()),
    }
}

/// Substitute `val` for `BVar(0)`.
fn instantiate(body: &KernelExpr, val: &KernelExpr) -> KernelExpr {
    instantiate_at(body, val, 0)
}
