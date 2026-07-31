// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Core types, error types, and expression/level operations for the micro-checker.

use std::collections::HashMap;
use std::sync::Arc;

use num_bigint::BigUint;

use crate::expr::stack_safe;

/// Minimal literal type for the micro-checker.
///
/// `Nat` carries an arbitrary-precision [`num_bigint::BigUint`] so the
/// env-aware native reducer (see `checker::whnf_impl`) can model the kernel's
/// arbitrary-precision Nat arithmetic faithfully — the AArch64 B-def corpus
/// reduces intermediates up to `2^128` (e.g. `Nat.mul` of two 64-bit values).
/// This `BigUint` is the micro-checker's OWN bignum: it is never the kernel's
/// `BigNat` and shares no arithmetic with the kernel reducer.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MicroLiteral {
    /// Natural number literal (arbitrary precision, the checker's own bignum).
    Nat(BigUint),
    /// String literal
    String(Arc<str>),
}

impl MicroLiteral {
    /// Construct a `Nat` literal from a `u64` (convenience for tests/small values).
    #[must_use]
    pub fn nat_u64(n: u64) -> MicroLiteral {
        MicroLiteral::Nat(BigUint::from(n))
    }
}

/// Minimal expression type for the micro-checker.
/// This is a simplified version of the main kernel's Expr.
pub enum MicroExpr {
    /// Bound variable (de Bruijn index)
    BVar(u32),
    /// Sort/Type at a level
    Sort(MicroLevel),
    /// Application
    App(Arc<MicroExpr>, Arc<MicroExpr>),
    /// Lambda abstraction: λ (x : A). b
    Lam(Arc<MicroExpr>, Arc<MicroExpr>),
    /// Pi/forall type: (x : A) → B
    Pi(Arc<MicroExpr>, Arc<MicroExpr>),
    /// Let binding: let x : A := v in b
    Let(Arc<MicroExpr>, Arc<MicroExpr>, Arc<MicroExpr>),
    /// Opaque constant (just a type, no definition)
    Opaque(Arc<MicroExpr>),
    /// Literal value (Nat or String)
    Lit(MicroLiteral),
    /// Structure projection: proj(idx, expr) extracts the idx-th field
    Proj(u32, Arc<MicroExpr>),
    /// Named constant reference, resolved against the micro-checker's
    /// read-only [`crate::micro::MicroEnv`] for its type (always) and, for
    /// `@[reducible]` definitions, its body (enabling DELTA unfolding).
    ///
    /// Universe levels are intentionally dropped: the env-aware diversity gate
    /// targets the monomorphic `:= rfl` B-def corpus, where every targeted
    /// constant is level-monomorphic. A polymorphic `Const` is reported
    /// [`MicroResult::Unsupported`] (fail-closed) — never silently accepted.
    Const(Arc<str>),
}

/// Outcome of an env-aware micro re-check.
///
/// `Unsupported` is the load-bearing third state: it means the micro-checker
/// hit a construct it cannot model (an unknown const, an irreducible def whose
/// body it cannot reach, a recursor outside the supported Nat/Bool set, a
/// polymorphic const, …). The diversity gate treats `Unsupported` as a HARD
/// FAILURE (fail-closed) so coverage is REPORTED, never laundered into a
/// silent skip.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MicroResult {
    /// The micro-checker verified the certificate and inferred this type.
    Verified(MicroExpr),
    /// The micro-checker rejected the certificate (genuine disagreement).
    Rejected(MicroError),
    /// The micro-checker cannot model some construct. Fail-closed: the gate
    /// must FAIL on this, not skip. The string names the unsupported construct.
    Unsupported(String),
}

/// Minimal universe level for the micro-checker.
pub enum MicroLevel {
    /// Level 0 (Prop)
    Zero,
    /// Successor: l + 1
    Succ(Arc<MicroLevel>),
    /// Maximum: max(l1, l2)
    Max(Arc<MicroLevel>, Arc<MicroLevel>),
    /// IMax: imax(l1, l2) - 0 if l2=0, else max(l1, l2)
    IMax(Arc<MicroLevel>, Arc<MicroLevel>),
}

impl Clone for MicroExpr {
    fn clone(&self) -> Self {
        stack_safe(|| match self {
            Self::BVar(idx) => Self::BVar(*idx),
            Self::Sort(level) => Self::Sort(level.clone()),
            Self::App(func, arg) => Self::App(func.clone(), arg.clone()),
            Self::Lam(ty, body) => Self::Lam(ty.clone(), body.clone()),
            Self::Pi(ty, body) => Self::Pi(ty.clone(), body.clone()),
            Self::Let(ty, value, body) => Self::Let(ty.clone(), value.clone(), body.clone()),
            Self::Opaque(ty) => Self::Opaque(ty.clone()),
            Self::Lit(lit) => Self::Lit(lit.clone()),
            Self::Proj(idx, expr) => Self::Proj(*idx, expr.clone()),
            Self::Const(name) => Self::Const(name.clone()),
        })
    }
}

impl PartialEq for MicroExpr {
    fn eq(&self, other: &Self) -> bool {
        stack_safe(|| match (self, other) {
            (Self::BVar(left), Self::BVar(right)) => left == right,
            (Self::Sort(left), Self::Sort(right)) => left == right,
            (Self::App(lf, la), Self::App(rf, ra))
            | (Self::Lam(lf, la), Self::Lam(rf, ra))
            | (Self::Pi(lf, la), Self::Pi(rf, ra)) => lf == rf && la == ra,
            (Self::Let(lt, lv, lb), Self::Let(rt, rv, rb)) => lt == rt && lv == rv && lb == rb,
            (Self::Opaque(left), Self::Opaque(right)) => left == right,
            (Self::Lit(left), Self::Lit(right)) => left == right,
            (Self::Proj(li, le), Self::Proj(ri, re)) => li == ri && le == re,
            (Self::Const(left), Self::Const(right)) => left == right,
            _ => false,
        })
    }
}

impl Eq for MicroExpr {}

// Diagnostics are deliberately bounded. Error formatting is itself reachable
// on adversarial rejection paths, so recursively printing the entire term
// would reintroduce an unguarded stack and output-amplification surface.
impl std::fmt::Debug for MicroExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::BVar(idx) => f.debug_tuple("BVar").field(idx).finish(),
            Self::Sort(level) => f.debug_tuple("Sort").field(level).finish(),
            Self::App(func, arg) => f
                .debug_tuple("App")
                .field(&MicroExprRule(func))
                .field(&MicroExprRule(arg))
                .finish(),
            Self::Lam(ty, body) => f
                .debug_tuple("Lam")
                .field(&MicroExprRule(ty))
                .field(&MicroExprRule(body))
                .finish(),
            Self::Pi(ty, body) => f
                .debug_tuple("Pi")
                .field(&MicroExprRule(ty))
                .field(&MicroExprRule(body))
                .finish(),
            Self::Let(ty, value, body) => f
                .debug_tuple("Let")
                .field(&MicroExprRule(ty))
                .field(&MicroExprRule(value))
                .field(&MicroExprRule(body))
                .finish(),
            Self::Opaque(ty) => f.debug_tuple("Opaque").field(&MicroExprRule(ty)).finish(),
            Self::Lit(lit) => f
                .debug_tuple("Lit")
                .field(&MicroLiteralSummary(lit))
                .finish(),
            Self::Proj(idx, expr) => f
                .debug_tuple("Proj")
                .field(idx)
                .field(&MicroExprRule(expr))
                .finish(),
            Self::Const(name) => f
                .debug_struct("Const")
                .field("len", &name.len())
                .field("prefix", &MicroBoundedStr(name))
                .finish(),
        }
    }
}

impl Drop for MicroExpr {
    fn drop(&mut self) {
        if !matches!(
            self,
            Self::Sort(_)
                | Self::App(_, _)
                | Self::Lam(_, _)
                | Self::Pi(_, _)
                | Self::Let(_, _, _)
                | Self::Opaque(_)
                | Self::Proj(_, _)
        ) || !micro_recursive_drop_needs_segment()
        {
            return;
        }

        let mut expr_children = Vec::with_capacity(3);
        let mut level_child = None;
        match self {
            Self::Sort(level) => {
                level_child = Some(std::mem::replace(level, MicroLevel::Zero));
            }
            Self::App(func, arg) | Self::Lam(func, arg) | Self::Pi(func, arg) => {
                expr_children.push(std::mem::replace(func, micro_expr_drop_leaf()));
                expr_children.push(std::mem::replace(arg, micro_expr_drop_leaf()));
            }
            Self::Let(ty, value, body) => {
                expr_children.push(std::mem::replace(ty, micro_expr_drop_leaf()));
                expr_children.push(std::mem::replace(value, micro_expr_drop_leaf()));
                expr_children.push(std::mem::replace(body, micro_expr_drop_leaf()));
            }
            Self::Opaque(ty) => {
                expr_children.push(std::mem::replace(ty, micro_expr_drop_leaf()));
            }
            Self::Proj(_, expr) => {
                expr_children.push(std::mem::replace(expr, micro_expr_drop_leaf()));
            }
            Self::BVar(_) | Self::Lit(_) | Self::Const(_) => {}
        }
        stack_safe(move || {
            drop(expr_children);
            drop(level_child);
        });
    }
}

impl Clone for MicroLevel {
    fn clone(&self) -> Self {
        stack_safe(|| match self {
            Self::Zero => Self::Zero,
            Self::Succ(level) => Self::Succ(level.clone()),
            Self::Max(left, right) => Self::Max(left.clone(), right.clone()),
            Self::IMax(left, right) => Self::IMax(left.clone(), right.clone()),
        })
    }
}

impl PartialEq for MicroLevel {
    fn eq(&self, other: &Self) -> bool {
        stack_safe(|| match (self, other) {
            (Self::Zero, Self::Zero) => true,
            (Self::Succ(left), Self::Succ(right)) => left == right,
            (Self::Max(ll, lr), Self::Max(rl, rr)) | (Self::IMax(ll, lr), Self::IMax(rl, rr)) => {
                ll == rl && lr == rr
            }
            _ => false,
        })
    }
}

impl Eq for MicroLevel {}

impl std::fmt::Debug for MicroLevel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Zero => f.write_str("Zero"),
            Self::Succ(child) => f.debug_tuple("Succ").field(&MicroLevelRule(child)).finish(),
            Self::Max(left, right) => f
                .debug_tuple("Max")
                .field(&MicroLevelRule(left))
                .field(&MicroLevelRule(right))
                .finish(),
            Self::IMax(left, right) => f
                .debug_tuple("IMax")
                .field(&MicroLevelRule(left))
                .field(&MicroLevelRule(right))
                .finish(),
        }
    }
}

impl Drop for MicroLevel {
    fn drop(&mut self) {
        if matches!(self, Self::Zero) || !micro_recursive_drop_needs_segment() {
            return;
        }

        let mut children = Vec::with_capacity(2);
        match self {
            Self::Succ(level) => {
                children.push(std::mem::replace(level, micro_level_drop_leaf()));
            }
            Self::Max(left, right) | Self::IMax(left, right) => {
                children.push(std::mem::replace(left, micro_level_drop_leaf()));
                children.push(std::mem::replace(right, micro_level_drop_leaf()));
            }
            Self::Zero => {}
        }
        stack_safe(move || drop(children));
    }
}

fn micro_expr_drop_leaf() -> Arc<MicroExpr> {
    static LEAF: std::sync::OnceLock<Arc<MicroExpr>> = std::sync::OnceLock::new();
    LEAF.get_or_init(|| Arc::new(MicroExpr::BVar(0))).clone()
}

fn micro_level_drop_leaf() -> Arc<MicroLevel> {
    static LEAF: std::sync::OnceLock<Arc<MicroLevel>> = std::sync::OnceLock::new();
    LEAF.get_or_init(|| Arc::new(MicroLevel::Zero)).clone()
}

fn micro_recursive_drop_needs_segment() -> bool {
    #[cfg(kani)]
    {
        false
    }
    #[cfg(not(kani))]
    {
        const DROP_RED_ZONE: usize = 256 * 1024;
        stacker::remaining_stack().is_none_or(|remaining| remaining < DROP_RED_ZONE)
    }
}

/// Minimal proof certificate for the micro-checker.
pub enum MicroCert {
    /// Sort(l) : Sort(succ(l))
    Sort {
        /// Universe level of the sort
        level: MicroLevel,
    },

    /// BVar with its type from context
    BVar {
        /// De Bruijn index
        idx: u32,
        /// Type of the bound variable
        ty: Box<MicroExpr>,
    },

    /// Opaque constant with its type
    Opaque {
        /// Type of the opaque constant
        ty: Box<MicroExpr>,
    },

    /// Named constant with its instantiated type (carried by the cert) and
    /// name (resolved against the read-only [`crate::micro::MicroEnv`] for
    /// cross-check). The micro-checker verifies that the cert-carried type is
    /// definitionally equal to the env's recorded type for `name`; if `name`
    /// is absent from the env it reports
    /// [`MicroResult::Unsupported`](crate::micro::MicroResult) (fail-closed).
    Const {
        /// Constant name (level-erased).
        name: Arc<str>,
        /// Instantiated type of the constant (from the kernel cert).
        ty: Box<MicroExpr>,
    },

    /// App: f a : B[a/x]
    App {
        /// Certificate for the function
        fn_cert: Box<MicroCert>,
        /// Certificate for the argument
        arg_cert: Box<MicroCert>,
        /// Resulting type after application
        result_ty: Box<MicroExpr>,
    },

    /// Lam: λ (x : A). b : (x : A) → B
    Lam {
        /// Certificate for argument type
        arg_ty_cert: Box<MicroCert>,
        /// Certificate for body
        body_cert: Box<MicroCert>,
        /// Resulting Pi type
        result_ty: Box<MicroExpr>,
    },

    /// Pi: (x : A) → B : Sort(imax(l1, l2))
    Pi {
        /// Certificate for argument type
        arg_ty_cert: Box<MicroCert>,
        /// Universe level of argument type
        arg_level: MicroLevel,
        /// Certificate for body type
        body_ty_cert: Box<MicroCert>,
        /// Universe level of body type
        body_level: MicroLevel,
    },

    /// Let: let x : A := v in b : B[v/x]
    Let {
        /// Certificate for the type annotation
        ty_cert: Box<MicroCert>,
        /// Certificate for the value
        val_cert: Box<MicroCert>,
        /// Certificate for the body
        body_cert: Box<MicroCert>,
        /// Resulting type
        result_ty: Box<MicroExpr>,
    },

    /// Lit: literal with its type
    Lit {
        /// The literal value
        lit: MicroLiteral,
        /// Type of the literal (provided externally; micro-checker has no environment)
        ty: Box<MicroExpr>,
    },

    /// Proj: structure projection with declared field type
    Proj {
        /// Field index in the structure
        idx: u32,
        /// Certificate for the expression being projected
        expr_cert: Box<MicroCert>,
        /// Type of the projected field (provided externally)
        field_ty: Box<MicroExpr>,
    },
}

impl Clone for MicroCert {
    fn clone(&self) -> Self {
        stack_safe(|| match self {
            Self::Sort { level } => Self::Sort {
                level: level.clone(),
            },
            Self::BVar { idx, ty } => Self::BVar {
                idx: *idx,
                ty: ty.clone(),
            },
            Self::Opaque { ty } => Self::Opaque { ty: ty.clone() },
            Self::Const { name, ty } => Self::Const {
                name: name.clone(),
                ty: ty.clone(),
            },
            Self::App {
                fn_cert,
                arg_cert,
                result_ty,
            } => Self::App {
                fn_cert: fn_cert.clone(),
                arg_cert: arg_cert.clone(),
                result_ty: result_ty.clone(),
            },
            Self::Lam {
                arg_ty_cert,
                body_cert,
                result_ty,
            } => Self::Lam {
                arg_ty_cert: arg_ty_cert.clone(),
                body_cert: body_cert.clone(),
                result_ty: result_ty.clone(),
            },
            Self::Pi {
                arg_ty_cert,
                arg_level,
                body_ty_cert,
                body_level,
            } => Self::Pi {
                arg_ty_cert: arg_ty_cert.clone(),
                arg_level: arg_level.clone(),
                body_ty_cert: body_ty_cert.clone(),
                body_level: body_level.clone(),
            },
            Self::Let {
                ty_cert,
                val_cert,
                body_cert,
                result_ty,
            } => Self::Let {
                ty_cert: ty_cert.clone(),
                val_cert: val_cert.clone(),
                body_cert: body_cert.clone(),
                result_ty: result_ty.clone(),
            },
            Self::Lit { lit, ty } => Self::Lit {
                lit: lit.clone(),
                ty: ty.clone(),
            },
            Self::Proj {
                idx,
                expr_cert,
                field_ty,
            } => Self::Proj {
                idx: *idx,
                expr_cert: expr_cert.clone(),
                field_ty: field_ty.clone(),
            },
        })
    }
}

impl PartialEq for MicroCert {
    fn eq(&self, other: &Self) -> bool {
        stack_safe(|| match (self, other) {
            (Self::Sort { level: left }, Self::Sort { level: right }) => left == right,
            (Self::BVar { idx: li, ty: lt }, Self::BVar { idx: ri, ty: rt }) => {
                li == ri && lt == rt
            }
            (Self::Opaque { ty: left }, Self::Opaque { ty: right }) => left == right,
            (Self::Const { name: ln, ty: lt }, Self::Const { name: rn, ty: rt }) => {
                ln == rn && lt == rt
            }
            (
                Self::App {
                    fn_cert: lf,
                    arg_cert: la,
                    result_ty: lr,
                },
                Self::App {
                    fn_cert: rf,
                    arg_cert: ra,
                    result_ty: rr,
                },
            ) => lf == rf && la == ra && lr == rr,
            (
                Self::Lam {
                    arg_ty_cert: la,
                    body_cert: lb,
                    result_ty: lr,
                },
                Self::Lam {
                    arg_ty_cert: ra,
                    body_cert: rb,
                    result_ty: rr,
                },
            ) => la == ra && lb == rb && lr == rr,
            (
                Self::Pi {
                    arg_ty_cert: lac,
                    arg_level: lal,
                    body_ty_cert: lbc,
                    body_level: lbl,
                },
                Self::Pi {
                    arg_ty_cert: rac,
                    arg_level: ral,
                    body_ty_cert: rbc,
                    body_level: rbl,
                },
            ) => lac == rac && lal == ral && lbc == rbc && lbl == rbl,
            (
                Self::Let {
                    ty_cert: lt,
                    val_cert: lv,
                    body_cert: lb,
                    result_ty: lr,
                },
                Self::Let {
                    ty_cert: rt,
                    val_cert: rv,
                    body_cert: rb,
                    result_ty: rr,
                },
            ) => lt == rt && lv == rv && lb == rb && lr == rr,
            (Self::Lit { lit: ll, ty: lt }, Self::Lit { lit: rl, ty: rt }) => ll == rl && lt == rt,
            (
                Self::Proj {
                    idx: li,
                    expr_cert: le,
                    field_ty: lf,
                },
                Self::Proj {
                    idx: ri,
                    expr_cert: re,
                    field_ty: rf,
                },
            ) => li == ri && le == re && lf == rf,
            _ => false,
        })
    }
}

impl std::fmt::Debug for MicroCert {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Sort { level } => f.debug_struct("Sort").field("level", level).finish(),
            Self::BVar { idx, ty } => f
                .debug_struct("BVar")
                .field("idx", idx)
                .field("ty", &MicroExprRule(ty))
                .finish(),
            Self::Opaque { ty } => f
                .debug_struct("Opaque")
                .field("ty", &MicroExprRule(ty))
                .finish(),
            Self::Const { name, ty } => f
                .debug_struct("Const")
                .field("name_len", &name.len())
                .field("name_prefix", &MicroBoundedStr(name))
                .field("ty", &MicroExprRule(ty))
                .finish(),
            Self::App {
                fn_cert,
                arg_cert,
                result_ty,
            } => f
                .debug_struct("App")
                .field("fn_cert", &MicroCertRule(fn_cert))
                .field("arg_cert", &MicroCertRule(arg_cert))
                .field("result_ty", &MicroExprRule(result_ty))
                .finish(),
            Self::Lam {
                arg_ty_cert,
                body_cert,
                result_ty,
            } => f
                .debug_struct("Lam")
                .field("arg_ty_cert", &MicroCertRule(arg_ty_cert))
                .field("body_cert", &MicroCertRule(body_cert))
                .field("result_ty", &MicroExprRule(result_ty))
                .finish(),
            Self::Pi {
                arg_ty_cert,
                arg_level,
                body_ty_cert,
                body_level,
            } => f
                .debug_struct("Pi")
                .field("arg_ty_cert", &MicroCertRule(arg_ty_cert))
                .field("arg_level", arg_level)
                .field("body_ty_cert", &MicroCertRule(body_ty_cert))
                .field("body_level", body_level)
                .finish(),
            Self::Let {
                ty_cert,
                val_cert,
                body_cert,
                result_ty,
            } => f
                .debug_struct("Let")
                .field("ty_cert", &MicroCertRule(ty_cert))
                .field("val_cert", &MicroCertRule(val_cert))
                .field("body_cert", &MicroCertRule(body_cert))
                .field("result_ty", &MicroExprRule(result_ty))
                .finish(),
            Self::Lit { lit, ty } => f
                .debug_struct("Lit")
                .field("lit", &MicroLiteralSummary(lit))
                .field("ty", &MicroExprRule(ty))
                .finish(),
            Self::Proj {
                idx,
                expr_cert,
                field_ty,
            } => f
                .debug_struct("Proj")
                .field("idx", idx)
                .field("expr_cert", &MicroCertRule(expr_cert))
                .field("field_ty", &MicroExprRule(field_ty))
                .finish(),
        }
    }
}

struct MicroExprRule<'a>(&'a MicroExpr);

impl std::fmt::Debug for MicroExprRule<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self.0 {
            MicroExpr::BVar(_) => "BVar",
            MicroExpr::Sort(_) => "Sort",
            MicroExpr::App(_, _) => "App",
            MicroExpr::Lam(_, _) => "Lam",
            MicroExpr::Pi(_, _) => "Pi",
            MicroExpr::Let(_, _, _) => "Let",
            MicroExpr::Opaque(_) => "Opaque",
            MicroExpr::Lit(_) => "Lit",
            MicroExpr::Proj(_, _) => "Proj",
            MicroExpr::Const(_) => "Const",
        })
    }
}

struct MicroLevelRule<'a>(&'a MicroLevel);

impl std::fmt::Debug for MicroLevelRule<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self.0 {
            MicroLevel::Zero => "Zero",
            MicroLevel::Succ(_) => "Succ",
            MicroLevel::Max(_, _) => "Max",
            MicroLevel::IMax(_, _) => "IMax",
        })
    }
}

struct MicroCertRule<'a>(&'a MicroCert);

impl std::fmt::Debug for MicroCertRule<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self.0 {
            MicroCert::Sort { .. } => "Sort",
            MicroCert::BVar { .. } => "BVar",
            MicroCert::Opaque { .. } => "Opaque",
            MicroCert::Const { .. } => "Const",
            MicroCert::App { .. } => "App",
            MicroCert::Lam { .. } => "Lam",
            MicroCert::Pi { .. } => "Pi",
            MicroCert::Let { .. } => "Let",
            MicroCert::Lit { .. } => "Lit",
            MicroCert::Proj { .. } => "Proj",
        })
    }
}

struct MicroLiteralSummary<'a>(&'a MicroLiteral);

impl std::fmt::Debug for MicroLiteralSummary<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.0 {
            MicroLiteral::Nat(value) => {
                let bits = value.bits();
                let mut digits = value.iter_u64_digits();
                let low = digits.next().unwrap_or(0);
                if bits <= 64 {
                    f.debug_tuple("Nat").field(&low).finish()
                } else {
                    let low_digits = [low, digits.next().unwrap_or(0)];
                    f.debug_struct("Nat")
                        .field("bits", &bits)
                        .field("low_u64_digits", &low_digits)
                        .finish()
                }
            }
            MicroLiteral::String(value) => f
                .debug_struct("String")
                .field("len", &value.len())
                .field("prefix", &MicroBoundedStr(value))
                .finish(),
        }
    }
}

struct MicroBoundedStr<'a>(&'a str);

impl std::fmt::Debug for MicroBoundedStr<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        const MAX_CHARS: usize = 32;
        let end = self
            .0
            .char_indices()
            .nth(MAX_CHARS)
            .map_or(self.0.len(), |(index, _)| index);
        std::fmt::Debug::fmt(&&self.0[..end], f)?;
        if end != self.0.len() {
            f.write_str("…")?;
        }
        Ok(())
    }
}

impl Drop for MicroCert {
    fn drop(&mut self) {
        if matches!(
            self,
            Self::Sort { .. }
                | Self::BVar { .. }
                | Self::Opaque { .. }
                | Self::Const { .. }
                | Self::Lit { .. }
        ) || !micro_recursive_drop_needs_segment()
        {
            return;
        }

        let cert_leaf = || {
            Box::new(MicroCert::Sort {
                level: MicroLevel::Zero,
            })
        };
        let mut cert_children = Vec::with_capacity(3);
        match self {
            Self::App {
                fn_cert, arg_cert, ..
            } => {
                cert_children.push(std::mem::replace(fn_cert, cert_leaf()));
                cert_children.push(std::mem::replace(arg_cert, cert_leaf()));
            }
            Self::Lam {
                arg_ty_cert,
                body_cert,
                ..
            } => {
                cert_children.push(std::mem::replace(arg_ty_cert, cert_leaf()));
                cert_children.push(std::mem::replace(body_cert, cert_leaf()));
            }
            Self::Pi {
                arg_ty_cert,
                body_ty_cert,
                ..
            } => {
                cert_children.push(std::mem::replace(arg_ty_cert, cert_leaf()));
                cert_children.push(std::mem::replace(body_ty_cert, cert_leaf()));
            }
            Self::Let {
                ty_cert,
                val_cert,
                body_cert,
                ..
            } => {
                cert_children.push(std::mem::replace(ty_cert, cert_leaf()));
                cert_children.push(std::mem::replace(val_cert, cert_leaf()));
                cert_children.push(std::mem::replace(body_cert, cert_leaf()));
            }
            Self::Proj { expr_cert, .. } => {
                cert_children.push(std::mem::replace(expr_cert, cert_leaf()));
            }
            Self::Sort { .. }
            | Self::BVar { .. }
            | Self::Opaque { .. }
            | Self::Const { .. }
            | Self::Lit { .. } => {}
        }
        stack_safe(move || drop(cert_children));
    }
}

/// Verification error
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum MicroError {
    /// Type mismatch
    #[error("type mismatch: expected {expected:?}, got {actual:?}")]
    TypeMismatch {
        /// Expected type
        expected: MicroExpr,
        /// Actual type found
        actual: MicroExpr,
    },
    /// Invalid de Bruijn index
    #[error("invalid bound variable: {0}")]
    InvalidBVar(u32),
    /// Expected a Sort
    #[error("expected Sort, got {0:?}")]
    ExpectedSort(MicroExpr),
    /// Expected a Pi type
    #[error("expected Pi, got {0:?}")]
    ExpectedPi(MicroExpr),
    /// Level mismatch
    #[error("level mismatch: expected {expected:?}, got {actual:?}")]
    LevelMismatch {
        /// Expected universe level
        expected: MicroLevel,
        /// Actual universe level found
        actual: MicroLevel,
    },
    /// Certificate/expression structure mismatch
    #[error("certificate/expression structure mismatch")]
    StructureMismatch,
    /// The micro-checker cannot model a construct (unknown const, unmodelable
    /// recursor, reduction fuel exhausted, …). This is the FAIL-CLOSED signal:
    /// the diversity gate must FAIL on it, never silently skip.
    #[error("unsupported by micro-checker (fail-closed): {0}")]
    Unsupported(String),
}

/// Error from cross-validation between the micro-checker and the main kernel.
///
/// Returned when the micro-checker disagrees with the main kernel's type
/// inference result. This indicates a potential soundness issue.
#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
pub enum CrossValidationError {
    /// Micro-checker inferred a different type than the main kernel
    #[error(
        "MICRO-CHECKER DISAGREEMENT: expr={expr}, main_type={main_type}, micro_type={micro_type}"
    )]
    Disagreement {
        /// The expression that was type-checked (debug representation)
        expr: String,
        /// Type inferred by the main kernel (debug representation)
        main_type: String,
        /// Type inferred by the micro-checker (debug representation)
        micro_type: String,
    },
    /// Micro-checker failed to verify the certificate
    #[error(
        "MICRO-CHECKER VERIFICATION FAILED: expr={expr}, main_type={main_type}, error={error}"
    )]
    VerificationFailed {
        /// The expression that was type-checked (debug representation)
        expr: String,
        /// Type inferred by the main kernel (debug representation)
        main_type: String,
        /// The underlying micro-checker error
        error: MicroError,
    },
}

// ============================================================================
// De Bruijn Index Arithmetic Helpers
// ============================================================================

/// Saturating addition for De Bruijn index arithmetic.
///
/// Returns `a + b`, saturating at `u32::MAX` on overflow instead of panicking.
/// Saturation is safe because MicroExpr BVar indices are bounded by construction.
fn checked_add_u32(a: u32, b: u32, _context: &'static str) -> u32 {
    a.saturating_add(b)
}

// ============================================================================
// Expression Operations
// ============================================================================

/// Pointer-identity memo for MicroExpr's substitution/lift engine.
///
/// Mirrors the main kernel's `FoldMemo` (`expr/subst.rs`, Track XX): the
/// micro-checker is a wholly separate, from-scratch substitution engine
/// (`micro/mod.rs`'s own header: "trades performance for simplicity… simple
/// WHNF… substitution with de Bruijn indices") that was not originally given
/// the same Arc-sharing-preservation treatment, even though `MicroExpr`'s own
/// children are `Arc`-wrapped exactly like the main kernel's `Expr` and are
/// subject to the identical match-lowering fan-out (a shared "fallback"
/// continuation duplicated into every `casesOn` minor as the SAME `Arc`).
/// A naive recursive `subst`/`lift` re-walks (and, unlike the main kernel's
/// `Option`-returning folder, unconditionally re-*allocates*) each shared
/// subtree once per occurrence, so distinct-node-linear DAGs blow up into
/// tree-exponential traversals here too.
///
/// SOUNDNESS: identical argument to `FoldMemo`. For a fixed `amount`
/// (`lift`) or fixed `val` (`subst`) — the only state held constant across
/// one top-level call — the result of lifting/substituting a given node at a
/// given `cutoff`/`depth` is a pure function of `(node-address, cutoff-or-
/// depth)`. A memo hit returns the exact `MicroExpr` the unmemoized recursion
/// would have produced — same output, byte-for-byte — only avoiding repeat
/// work on shared structure. Each memo is constructed fresh per top-level
/// `lift`/`subst` call (never persisted across calls), and every visited
/// node stays reachable (hence address-stable) for the duration of that call
/// via the same `Arc`-refcounting the main kernel's memo relies on.
#[derive(Default)]
struct MicroFoldMemo {
    /// `subst`: keyed on `(node pointer, depth)` — `val` is fixed per call.
    subst: HashMap<(usize, u32), MicroExpr>,
    /// `lift`: keyed on `(node pointer, cutoff)` — `amount` is fixed per call.
    lift: HashMap<(usize, u32), MicroExpr>,
}

impl MicroExpr {
    /// Lift all bound variables >= cutoff by amount
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid MicroExpr (no dangling indices beyond context)
    /// ENSURES: BVar(i) where i >= cutoff becomes BVar(i + amount)
    /// ENSURES: BVar(i) where i < cutoff remains unchanged
    /// ENSURES: Structurally identical to `self` except for lifted BVars
    #[must_use]
    pub fn lift(&self, cutoff: u32, amount: u32) -> MicroExpr {
        let mut memo = MicroFoldMemo::default();
        self.lift_recurse(cutoff, amount, &mut memo)
    }

    #[inline(always)]
    fn lift_recurse(&self, cutoff: u32, amount: u32, memo: &mut MicroFoldMemo) -> MicroExpr {
        stack_safe(|| self.lift_memo(cutoff, amount, memo))
    }

    /// Pointer-identity-memoized worker for [`Self::lift`]. See
    /// [`MicroFoldMemo`] for the soundness argument.
    fn lift_memo(&self, cutoff: u32, amount: u32, memo: &mut MicroFoldMemo) -> MicroExpr {
        let key = (self as *const MicroExpr as usize, cutoff);
        if let Some(cached) = memo.lift.get(&key) {
            return cached.clone();
        }
        let result = match self {
            MicroExpr::BVar(idx) => {
                if *idx >= cutoff {
                    MicroExpr::BVar(checked_add_u32(*idx, amount, "lift bvar index"))
                } else {
                    self.clone()
                }
            }
            MicroExpr::Sort(l) => MicroExpr::Sort(l.clone()),
            MicroExpr::App(f, a) => MicroExpr::App(
                Arc::new(f.lift_recurse(cutoff, amount, memo)),
                Arc::new(a.lift_recurse(cutoff, amount, memo)),
            ),
            MicroExpr::Lam(ty, body) => MicroExpr::Lam(
                Arc::new(ty.lift_recurse(cutoff, amount, memo)),
                Arc::new(body.lift_recurse(
                    checked_add_u32(cutoff, 1, "lift lam cutoff"),
                    amount,
                    memo,
                )),
            ),
            MicroExpr::Pi(ty, body) => MicroExpr::Pi(
                Arc::new(ty.lift_recurse(cutoff, amount, memo)),
                Arc::new(body.lift_recurse(
                    checked_add_u32(cutoff, 1, "lift pi cutoff"),
                    amount,
                    memo,
                )),
            ),
            MicroExpr::Let(ty, val, body) => MicroExpr::Let(
                Arc::new(ty.lift_recurse(cutoff, amount, memo)),
                Arc::new(val.lift_recurse(cutoff, amount, memo)),
                Arc::new(body.lift_recurse(
                    checked_add_u32(cutoff, 1, "lift let cutoff"),
                    amount,
                    memo,
                )),
            ),
            MicroExpr::Opaque(ty) => {
                MicroExpr::Opaque(Arc::new(ty.lift_recurse(cutoff, amount, memo)))
            }
            MicroExpr::Lit(_) => self.clone(),
            MicroExpr::Proj(idx, e) => {
                MicroExpr::Proj(*idx, Arc::new(e.lift_recurse(cutoff, amount, memo)))
            }
            // Constants are closed (no free BVars), so lifting is a no-op.
            MicroExpr::Const(_) => self.clone(),
        };
        memo.lift.insert(key, result.clone());
        result
    }

    /// Substitute `val` for BVar(0), adjusting indices appropriately
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid MicroExpr
    /// REQUIRES: `val` is a valid MicroExpr (no dangling BVars)
    /// ENSURES: BVar(0) is replaced by `val` (lifted appropriately)
    /// ENSURES: BVar(i) where i > 0 becomes BVar(i - 1)
    /// ENSURES: Result is a valid MicroExpr
    #[must_use]
    pub fn instantiate(&self, val: &MicroExpr) -> MicroExpr {
        self.subst(0, val)
    }

    /// Substitute `val` for BVar(depth), adjusting indices
    pub(crate) fn subst(&self, depth: u32, val: &MicroExpr) -> MicroExpr {
        let mut memo = MicroFoldMemo::default();
        self.subst_recurse(depth, val, &mut memo)
    }

    #[inline(always)]
    fn subst_recurse(&self, depth: u32, val: &MicroExpr, memo: &mut MicroFoldMemo) -> MicroExpr {
        stack_safe(|| self.subst_memo(depth, val, memo))
    }

    /// Pointer-identity-memoized worker for [`Self::subst`]. See
    /// [`MicroFoldMemo`] for the soundness argument.
    fn subst_memo(&self, depth: u32, val: &MicroExpr, memo: &mut MicroFoldMemo) -> MicroExpr {
        let key = (self as *const MicroExpr as usize, depth);
        if let Some(cached) = memo.subst.get(&key) {
            return cached.clone();
        }
        let result = match self {
            MicroExpr::BVar(idx) => {
                use std::cmp::Ordering;
                match idx.cmp(&depth) {
                    // val is fixed for this call, but the LIFT applied to it
                    // gets its own fresh memo (a separate top-level lift call)
                    // — identical to the un-memoized behavior, and to the main
                    // kernel's `Instantiator::fold_bvar_opt`.
                    Ordering::Equal => val.lift(0, depth),
                    Ordering::Greater => MicroExpr::BVar(idx - 1),
                    Ordering::Less => self.clone(),
                }
            }
            MicroExpr::Sort(l) => MicroExpr::Sort(l.clone()),
            MicroExpr::App(f, a) => MicroExpr::App(
                Arc::new(f.subst_recurse(depth, val, memo)),
                Arc::new(a.subst_recurse(depth, val, memo)),
            ),
            MicroExpr::Lam(ty, body) => MicroExpr::Lam(
                Arc::new(ty.subst_recurse(depth, val, memo)),
                Arc::new(body.subst_recurse(
                    checked_add_u32(depth, 1, "subst lam depth"),
                    val,
                    memo,
                )),
            ),
            MicroExpr::Pi(ty, body) => MicroExpr::Pi(
                Arc::new(ty.subst_recurse(depth, val, memo)),
                Arc::new(body.subst_recurse(
                    checked_add_u32(depth, 1, "subst pi depth"),
                    val,
                    memo,
                )),
            ),
            MicroExpr::Let(ty, v, body) => MicroExpr::Let(
                Arc::new(ty.subst_recurse(depth, val, memo)),
                Arc::new(v.subst_recurse(depth, val, memo)),
                Arc::new(body.subst_recurse(
                    checked_add_u32(depth, 1, "subst let depth"),
                    val,
                    memo,
                )),
            ),
            MicroExpr::Opaque(ty) => {
                MicroExpr::Opaque(Arc::new(ty.subst_recurse(depth, val, memo)))
            }
            MicroExpr::Lit(_) => self.clone(),
            MicroExpr::Proj(idx, e) => {
                MicroExpr::Proj(*idx, Arc::new(e.subst_recurse(depth, val, memo)))
            }
            // Constants are closed: substitution is a no-op.
            MicroExpr::Const(_) => self.clone(),
        };
        memo.subst.insert(key, result.clone());
        result
    }
}

impl MicroLevel {
    /// Create successor level
    ///
    /// # Contract
    ///
    /// REQUIRES: `l` is a valid MicroLevel
    /// ENSURES: Returns Succ(l), representing l + 1
    pub fn succ(l: MicroLevel) -> MicroLevel {
        MicroLevel::Succ(Arc::new(l))
    }

    /// Create max level, simplifying if possible
    ///
    /// # Contract
    ///
    /// REQUIRES: `l1` and `l2` are valid MicroLevels
    /// ENSURES: Result is semantically equivalent to max(l1, l2)
    /// ENSURES: Simplifies trivial cases: max(l, l) = l, max(0, l) = l
    pub fn max(l1: MicroLevel, l2: MicroLevel) -> MicroLevel {
        // Simplifications:
        // max(l, l) = l
        // max(0, l) = l
        // max(l, 0) = l
        if l1 == l2 {
            return l1;
        }
        if l1 == MicroLevel::Zero {
            return l2;
        }
        if l2 == MicroLevel::Zero {
            return l1;
        }
        // Check if one is definitely >= the other
        if MicroLevel::is_geq(&l1, &l2) {
            return l1;
        }
        if MicroLevel::is_geq(&l2, &l1) {
            return l2;
        }
        MicroLevel::Max(Arc::new(l1), Arc::new(l2))
    }

    /// Check if l1 >= l2 (conservative approximation).
    ///
    /// Normalizes both levels first to prevent exponential blowup on
    /// nested Max trees (see #1946).
    pub(crate) fn is_geq(l1: &MicroLevel, l2: &MicroLevel) -> bool {
        let n1 = l1.normalize();
        let n2 = l2.normalize();
        Self::is_geq_core(&n1, &n2)
    }

    /// Core is_geq on already-normalized levels.
    fn is_geq_core(l1: &MicroLevel, l2: &MicroLevel) -> bool {
        stack_safe(|| Self::is_geq_core_impl(l1, l2))
    }

    fn is_geq_core_impl(l1: &MicroLevel, l2: &MicroLevel) -> bool {
        // Same level
        if l1 == l2 {
            return true;
        }

        // Zero is the minimum
        if *l2 == MicroLevel::Zero {
            return true;
        }

        // succ^n(x) >= x for any n > 0
        let (base1, offset1) = MicroLevel::get_offset(l1);
        let (base2, offset2) = MicroLevel::get_offset(l2);

        if offset1 > 0 && *base1 == *l2 {
            return true;
        }

        // If same base, compare offsets
        if base1 == base2 {
            return offset1 >= offset2;
        }

        // max(a, b) >= l if a >= l or b >= l
        if let MicroLevel::Max(a, b) = l1 {
            if Self::is_geq_core(a, l2) || Self::is_geq_core(b, l2) {
                return true;
            }
        }

        // l >= max(a, b) if l >= a and l >= b
        if let MicroLevel::Max(a, b) = l2 {
            if Self::is_geq_core(l1, a) && Self::is_geq_core(l1, b) {
                return true;
            }
        }

        // l >= imax(a, b) iff l >= a && l >= b
        if let MicroLevel::IMax(a, b) = l2 {
            if Self::is_geq_core(l1, a) && Self::is_geq_core(l1, b) {
                return true;
            }
        }

        // imax(a, b) >= l iff b >= l
        if let MicroLevel::IMax(_, b) = l1 {
            return Self::is_geq_core(b, l2);
        }

        // Offset comparison with equal offsets
        if offset1 == offset2 && offset1 > 0 {
            return Self::is_geq_core(base1, base2);
        }

        false
    }

    /// Normalize a MicroLevel by flattening and deduplicating Max trees.
    ///
    /// Prevents exponential blowup in is_geq by ensuring Max trees are flat
    /// (no nested Max on either side) with deduplicated, sorted arguments.
    /// Analogous to Level::normalize_impl in level.rs.
    pub(crate) fn normalize(&self) -> MicroLevel {
        stack_safe(|| self.normalize_impl())
    }

    fn normalize_impl(&self) -> MicroLevel {
        let (base, outer_offset) = MicroLevel::get_offset(self);

        match base {
            MicroLevel::Zero => self.clone(),
            MicroLevel::Succ(_) => unreachable!("get_offset strips all Succ layers"),

            MicroLevel::IMax(l1, l2) => {
                let l1_norm = l1.normalize();
                let l2_norm = l2.normalize();
                let result = MicroLevel::imax(l1_norm, l2_norm);
                // If imax reduced to a Max, add offset then re-normalize
                // so that Succ distributes over Max.
                if matches!(result, MicroLevel::Max(_, _)) {
                    Self::add_offset(&result, outer_offset).normalize()
                } else {
                    Self::add_offset(&result, outer_offset)
                }
            }

            MicroLevel::Max(_, _) => {
                // Step 1: Flatten nested Max into a list of args
                let mut todo = Vec::new();
                Self::push_max_args(base, &mut todo);

                // Step 2: Normalize each arg, then re-flatten
                let mut args = Vec::new();
                for a in &todo {
                    let normed = a.normalize();
                    Self::push_max_args(&normed, &mut args);
                }

                // Step 3: Sort for canonical form
                args.sort_by(Self::norm_cmp);

                // Step 4: Deduplicate — keep largest offset per base
                let mut deduped: Vec<MicroLevel> = Vec::new();
                if !args.is_empty() {
                    deduped.push(args[0].clone());
                    let mut prev = MicroLevel::get_offset(&args[0]);
                    for arg in args.iter().skip(1) {
                        let curr = MicroLevel::get_offset(arg);
                        if prev.0 == curr.0 {
                            // Same base: keep larger offset
                            if curr.1 > prev.1 {
                                deduped.pop();
                                deduped.push(arg.clone());
                                prev = curr;
                            }
                        } else {
                            prev = curr;
                            deduped.push(arg.clone());
                        }
                    }
                }

                // Step 5: Reapply outer offset
                if outer_offset > 0 {
                    for a in &mut deduped {
                        *a = Self::add_offset(a, outer_offset);
                    }
                }

                // Step 6: Rebuild right-associated Max tree
                if deduped.is_empty() {
                    MicroLevel::Zero
                } else {
                    Self::mk_max_from_args(&deduped)
                }
            }
        }
    }

    /// Flatten a Max tree into its leaf arguments.
    fn push_max_args(l: &MicroLevel, buf: &mut Vec<MicroLevel>) {
        stack_safe(|| Self::push_max_args_impl(l, buf));
    }

    fn push_max_args_impl(l: &MicroLevel, buf: &mut Vec<MicroLevel>) {
        match l {
            MicroLevel::Max(a, b) => {
                Self::push_max_args(a, buf);
                Self::push_max_args(b, buf);
            }
            _ => buf.push(l.clone()),
        }
    }

    /// Rebuild a right-associated Max tree from a list of args.
    fn mk_max_from_args(args: &[MicroLevel]) -> MicroLevel {
        assert!(!args.is_empty());
        let mut result = args[args.len() - 1].clone();
        for i in (0..args.len() - 1).rev() {
            result = MicroLevel::Max(Arc::new(args[i].clone()), Arc::new(result));
        }
        result
    }

    /// Add n Succ layers to a level.
    fn add_offset(l: &MicroLevel, n: u32) -> MicroLevel {
        let mut result = l.clone();
        for _ in 0..n {
            result = MicroLevel::Succ(Arc::new(result));
        }
        result
    }

    /// Comparison function for normalized level ordering.
    /// Zero < IMax < Max, then by structural comparison.
    fn norm_cmp(a: &MicroLevel, b: &MicroLevel) -> std::cmp::Ordering {
        use std::cmp::Ordering;
        if a == b {
            return Ordering::Equal;
        }
        let (base_a, off_a) = MicroLevel::get_offset(a);
        let (base_b, off_b) = MicroLevel::get_offset(b);
        let kind_a = Self::kind_ord(base_a);
        let kind_b = Self::kind_ord(base_b);
        if kind_a != kind_b {
            return kind_a.cmp(&kind_b);
        }
        // Same kind: compare structurally, then by offset
        if base_a != base_b {
            return Self::structural_cmp(base_a, base_b);
        }
        off_a.cmp(&off_b)
    }

    /// Total, allocation-free structural ordering used by normalization.
    ///
    /// Keep this iterative: formatting a deeply nested level merely to obtain
    /// a tiebreaker reintroduced an unguarded recursive walk.
    fn structural_cmp(left: &MicroLevel, right: &MicroLevel) -> std::cmp::Ordering {
        use std::cmp::Ordering;

        let mut pending = vec![(left, right)];
        while let Some((lhs, rhs)) = pending.pop() {
            let tag = |level: &MicroLevel| match level {
                MicroLevel::Zero => 0_u8,
                MicroLevel::Succ(_) => 1,
                MicroLevel::IMax(_, _) => 2,
                MicroLevel::Max(_, _) => 3,
            };
            let tag_cmp = tag(lhs).cmp(&tag(rhs));
            if tag_cmp != Ordering::Equal {
                return tag_cmp;
            }
            match (lhs, rhs) {
                (MicroLevel::Zero, MicroLevel::Zero) => {}
                (MicroLevel::Succ(l), MicroLevel::Succ(r)) => pending.push((l, r)),
                (MicroLevel::Max(ll, lr), MicroLevel::Max(rl, rr))
                | (MicroLevel::IMax(ll, lr), MicroLevel::IMax(rl, rr)) => {
                    pending.push((lr, rr));
                    pending.push((ll, rl));
                }
                _ => unreachable!("equal level tags must have equal variants"),
            }
        }
        Ordering::Equal
    }

    /// Kind ordering for normalized level sorting.
    fn kind_ord(l: &MicroLevel) -> u8 {
        match l {
            MicroLevel::Zero => 0,
            MicroLevel::Succ(_) => 1,
            MicroLevel::IMax(_, _) => 2,
            MicroLevel::Max(_, _) => 3,
        }
    }

    /// Get the base level and offset (number of Succ applications)
    pub(crate) fn get_offset(l: &MicroLevel) -> (&MicroLevel, u32) {
        stack_safe(|| Self::get_offset_impl(l))
    }

    fn get_offset_impl(l: &MicroLevel) -> (&MicroLevel, u32) {
        match l {
            MicroLevel::Succ(inner) => {
                let (base, offset) = MicroLevel::get_offset(inner);
                (base, checked_add_u32(offset, 1, "level get_offset"))
            }
            _ => (l, 0),
        }
    }

    /// Create imax level, simplifying if possible
    ///
    /// imax(l1, l2) = 0 if l2 = 0, else max(l1, l2) if l2 is nonzero (Succ)
    ///
    /// # Contract
    ///
    /// REQUIRES: `l1` and `l2` are valid MicroLevels
    /// ENSURES: Returns Zero if l2 = Zero (proof irrelevance for Prop)
    /// ENSURES: Returns max(l1, l2) if l2 is definitely nonzero (Succ form)
    /// ENSURES: Returns IMax(l1, l2) otherwise (delayed evaluation)
    pub fn imax(l1: MicroLevel, l2: MicroLevel) -> MicroLevel {
        // imax(_, 0) = 0
        if l2 == MicroLevel::Zero {
            return MicroLevel::Zero;
        }
        // imax(l, succ(l')) = max(l, succ(l')) since succ(l') > 0
        if matches!(l2, MicroLevel::Succ(_)) {
            return MicroLevel::max(l1, l2);
        }
        // imax(0, l) = l (if l != 0, which we handled above)
        if l1 == MicroLevel::Zero {
            return l2;
        }
        // imax(l, l) = l
        if l1 == l2 {
            return l1;
        }
        MicroLevel::IMax(Arc::new(l1), Arc::new(l2))
    }

    /// Check if two levels are equal (uses derived PartialEq)
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` and `other` are valid MicroLevels
    /// ENSURES: Returns true iff levels are structurally identical
    /// ENSURES: Does NOT perform semantic equivalence (e.g., max(0, l) vs l)
    pub fn level_eq(&self, other: &MicroLevel) -> bool {
        self == other
    }
}

#[cfg(test)]
mod debruijn_ouroboros_tests {
    //! Faithfulness validation for the STEP C ouroboros instance: Trust's discharge
    //! proves a real arm of its OWN prover's kernel panic-free.
    //!
    //! `MicroExpr::subst`'s BVar arm decrements a de Bruijn index `idx - 1` (a u32
    //! subtraction that underflows/PANICS at idx == 0) under the guard `idx > depth`.
    //! In trust-mc, `soundness_oracle::build_debruijn_decrement` models exactly this arm
    //! as `f(idx, depth) = if idx > depth { idx - 1 } else { idx }` and
    //! `ouroboros_clean_kernel_debruijn_decrement_proven_safe` has Trust's own discharge
    //! PROVE it panic-free (SMT, all inputs).
    //!
    //! This test closes the fidelity gap by EXECUTION (so the trust-mc claim is about the
    //! REAL kernel code, not a hand-waved translation): it runs the actual `subst` over a
    //! grid INCLUDING idx == 0 and the u32 extremes, and asserts (a) it never panics, and
    //! (b) its decrement structure matches the model — `idx > depth` yields `BVar(idx-1)`,
    //! `idx < depth` is unchanged. Together: Trust proves a real, fidelity-validated arm of
    //! clean's kernel panic-free — the forward direction of the ouroboros.
    use super::{MicroExpr, MicroLevel};

    #[test]
    fn debruijn_decrement_model_matches_subst() {
        // `val` is a Sort (no bound variables), so the `idx == depth` arm's `val.lift`
        // performs no index arithmetic and cannot itself panic — isolating the property
        // under test to the `idx - 1` decrement.
        let val = MicroExpr::Sort(MicroLevel::Zero);
        let grid = [0u32, 1, 2, 3, 5, 17, 100, u32::MAX - 1, u32::MAX];
        for &idx in &grid {
            for &depth in &grid {
                // The REAL kernel function — must be TOTAL (never panic) for every input,
                // which is exactly what Trust's discharge proves of the model.
                let r = MicroExpr::BVar(idx).subst(depth, &val);
                if idx > depth {
                    assert_eq!(
                        r,
                        MicroExpr::BVar(idx - 1),
                        "subst BVar(Greater) must decrement to BVar(idx-1) at idx={idx}, depth={depth}"
                    );
                } else if idx < depth {
                    assert_eq!(
                        r,
                        MicroExpr::BVar(idx),
                        "subst BVar(Less) must be unchanged at idx={idx}, depth={depth}"
                    );
                }
                // idx == depth: r == val.lift(0, depth); only no-panic is required.
            }
        }
    }
}
