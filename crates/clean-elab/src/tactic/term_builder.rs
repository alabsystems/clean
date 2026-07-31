// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared term construction utilities for typeclass method applications.
// WIP: not yet wired into tactic dispatch — suppress dead_code until integration
//!
//! Eliminates the implicit-arg-omission bug class (#2078) by providing
//! correctly-arity'd builder functions for common typeclass methods.
//!
//! In Lean 4's kernel, all arguments are explicit — there are no "implicit"
//! arguments at the kernel level. The elaborator inserts them, but our tactic
//! code builds kernel terms directly and must supply every argument.
//!
//! # Reference signatures
//!
//! | Constant       | Total args | Pattern                              |
//! |----------------|-----------|--------------------------------------|
//! | `LE.le`        | 4         | `ty inst lhs rhs`                    |
//! | `HAdd.hAdd`    | 6         | `α β γ inst a b`                    |
//! | `Neg.neg`      | 3         | `ty inst a`                          |
//! | `OfNat.ofNat`  | 3         | `ty n inst`                          |

use super::ProofState;
use clean_kernel::Expr;

/// Build a homogeneous binary relation: `@Rel.rel ty inst lhs rhs`
///
/// For LE.le, LT.lt, GE.ge, GT.gt (4 args total).
///
/// REQUIRES: `rel_name` identifies a 4-arg comparison constant; `ty` is the type;
///   `inst` is the typeclass instance; `lhs`/`rhs` are operands.
/// ENSURES: Returns the fully-applied 4-arg expression `App(App(App(App(rel, ty), inst), lhs), rhs)`.
pub(crate) fn make_relation(
    rel_name: &str,
    ty: &Expr,
    inst: &Expr,
    lhs: &Expr,
    rhs: &Expr,
    state: &mut ProofState,
) -> Expr {
    let c = state.mk_const_str(rel_name);
    Expr::app(
        Expr::app(
            Expr::app(Expr::app(c, ty.clone()), inst.clone()),
            lhs.clone(),
        ),
        rhs.clone(),
    )
}

/// Build a heterogeneous binary operation: `@HOp.hOp α β γ inst a b`
///
/// For HAdd.hAdd, HMul.hMul, HPow.hPow, HSub.hSub, HDiv.hDiv (6 args).
///
/// REQUIRES: `op_name` identifies a 6-arg heterogeneous operator; `ty_a`/`ty_b`/`ty_c`
///   are the three type arguments; `inst` is the typeclass instance; `a`/`b` are operands.
/// ENSURES: Returns the fully-applied 6-arg expression.
pub(crate) fn make_hetero_binop(
    op_name: &str,
    ty_a: &Expr,
    ty_b: &Expr,
    ty_c: &Expr,
    inst: &Expr,
    a: &Expr,
    b: &Expr,
    state: &mut ProofState,
) -> Expr {
    let c = state.mk_const_str(op_name);
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(Expr::app(c, ty_a.clone()), ty_b.clone()),
                    ty_c.clone(),
                ),
                inst.clone(),
            ),
            a.clone(),
        ),
        b.clone(),
    )
}

/// Build a homogeneous binary operation (sugar for `make_hetero_binop` with α=β=γ).
///
/// REQUIRES: `op_name` identifies a 6-arg heterogeneous operator; all three type slots
///   are filled with `ty`.
/// ENSURES: Equivalent to `make_hetero_binop(op_name, ty, ty, ty, inst, a, b, state)`.
pub(crate) fn make_binop(
    op_name: &str,
    ty: &Expr,
    inst: &Expr,
    a: &Expr,
    b: &Expr,
    state: &mut ProofState,
) -> Expr {
    make_hetero_binop(op_name, ty, ty, ty, inst, a, b, state)
}

/// Build a unary operation: `@Op.op ty inst a`
///
/// For Neg.neg (3 args).
///
/// REQUIRES: `op_name` identifies a 3-arg unary operator; `ty` is the type;
///   `inst` is the typeclass instance; `a` is the operand.
/// ENSURES: Returns the fully-applied 3-arg expression `App(App(App(op, ty), inst), a)`.
pub(crate) fn make_unary_op(
    op_name: &str,
    ty: &Expr,
    inst: &Expr,
    a: &Expr,
    state: &mut ProofState,
) -> Expr {
    let c = state.mk_const_str(op_name);
    Expr::app(Expr::app(Expr::app(c, ty.clone()), inst.clone()), a.clone())
}

/// Build `@OfNat.ofNat ty n inst`
///
/// REQUIRES: `ty` is the target type; `n` is the numeric literal; `inst` is the
///   OfNat instance for that type and literal.
/// ENSURES: Returns the fully-applied 3-arg expression `App(App(App(OfNat.ofNat, ty), n), inst)`.
pub(crate) fn make_ofnat(ty: &Expr, n: &Expr, inst: &Expr, state: &mut ProofState) -> Expr {
    let c = state.mk_const_str("OfNat.ofNat");
    Expr::app(Expr::app(Expr::app(c, ty.clone()), n.clone()), inst.clone())
}

/// Create a fresh metavariable expression for an instance placeholder.
///
/// When the exact instance is not statically known, use this to create
/// a metavariable that the unifier can fill in later. The `class_app`
/// should be the fully-applied class type, e.g., `HAdd Nat Nat Nat`.
///
/// REQUIRES: `class_app` is a fully-applied typeclass type expression.
/// ENSURES: Returns an `FVar` expression whose ID encodes a fresh metavariable
///   registered in `state.metas` with the given class type.
pub(crate) fn fresh_inst_meta(class_app: Expr, state: &mut ProofState) -> Expr {
    let meta_id = state.fresh_meta(class_app);
    Expr::fvar(crate::MetaState::to_fvar(meta_id))
}

/// Build a class application expr for a homogeneous binary relation.
///
/// E.g., `LE Nat` for `LE.le` on `Nat`.
///
/// REQUIRES: `class_name` is a relation typeclass name (e.g., "LE", "LT").
/// ENSURES: Returns `App(Const(class_name), ty)` — a 1-arg class application.
pub(crate) fn class_app_relation(class_name: &str, ty: &Expr, state: &mut ProofState) -> Expr {
    let c = state.mk_const_str(class_name);
    Expr::app(c, ty.clone())
}

/// Build a class application expr for a homogeneous binary operation.
///
/// E.g., `HAdd Nat Nat Nat` for `HAdd.hAdd` on `Nat`.
///
/// REQUIRES: `class_name` is a heterogeneous op typeclass name (e.g., "HAdd", "HMul").
/// ENSURES: Returns `App(App(App(Const(class_name), ty), ty), ty)` — a 3-arg class application
///   with all type slots filled homogeneously.
pub(crate) fn class_app_binop(class_name: &str, ty: &Expr, state: &mut ProofState) -> Expr {
    let c = state.mk_const_str(class_name);
    Expr::app(Expr::app(Expr::app(c, ty.clone()), ty.clone()), ty.clone())
}
