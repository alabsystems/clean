// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Metaprogram *query* primitives and the kernel-`Expr` value channel for
//! term-elaborator bodies.
//!
//! # The problem this solves
//!
//! The constructor evaluator ([`super::meta_builtin`]) rewrites a
//! `MetaM`/`TermElabM` *builder* body (`mkApp`/`mkConst`/...) into an ordinary
//! `SurfaceExpr` and lets the normal pipeline elaborate it. That works because
//! every builder maps to a surface form. A *query* primitive is different: its
//! result is a kernel `Expr` *computed from the elaboration state* (e.g.
//! `inferType e` is the inferred type of `e`), and a type has no surface form to
//! rewrite back into. So a query cannot be handled by a pure `SurfaceExpr ->
//! SurfaceExpr` rewrite — its value must be carried as an already-elaborated
//! kernel `Expr`.
//!
//! # The value channel
//!
//! [`ElabCtx`](crate::infer::ElabCtx) carries a `meta_value_bindings` map
//! (`name -> Expr`). A term-elaborator body of the value-channel shape
//!
//! ```text
//! elab "tyOf" e:term : term => let t := inferType e; t
//! ```
//!
//! is interpreted statement-by-statement: `inferType e` is *evaluated* (elaborate
//! `e` through the normal pipeline, then infer its type), and the resulting
//! kernel `Expr` is bound to `t` in `meta_value_bindings`. When the remaining
//! body mentions `t`, [`elab_ident`](crate::infer::ElabCtx::elab_ident) consults
//! the map first and splices the stored `Expr` directly — no re-parse, no surface
//! round-trip. The binding is removed when the body finishes so it never leaks
//! into an unrelated elaboration.
//!
//! The terminal shape `elab "tyOf" e:term : term => inferType e` is the same
//! mechanism with no intervening `let`: the query value *is* the body result.
//!
//! # Recognized queries
//!
//! | Body call          | Value (kernel `Expr`)                                  |
//! |--------------------|--------------------------------------------------------|
//! | `inferType e`      | the inferred type of `e`                               |
//! | `Expr.inferType e` | (alias)                                                |
//! | `checkType e ty`   | `e` itself, iff `e : ty` (kernel-checked); else error  |
//! | `Expr.checkType e ty` | (alias)                                             |
//! | `whnf e`           | the weak-head normal form of `e` (meaning-preserving)  |
//! | `Expr.whnf e`      | (alias)                                                |
//!
//! `e` (and `ty`) are ordinary sub-terms, elaborated by the normal pipeline (and
//! may themselves mention an earlier value binding, which splices in via
//! `elab_ident`).
//!
//! # Soundness
//!
//! Every query *reads* from the kernel; none fabricates a term or closes a goal.
//!
//! - `inferType e`: the argument `e` is elaborated and kernel-checked by the
//!   normal `ElabCtx::elaborate` pipeline, and its type is produced by
//!   `ElabCtx::infer_type`, which delegates to the kernel type checker.
//! - `checkType e ty`: `e` and `ty` are elaborated by the normal pipeline; the
//!   inferred type of `e` is compared to `ty` via `ElabCtx::is_def_eq` (the kernel
//!   definitional-equality check). The (kernel-checked) `e` is returned *only* on a
//!   match; a mismatch fails honestly with [`ElabError::TypeMismatch`]. No term is
//!   accepted at a type it does not have.
//! - `whnf e`: `e` is elaborated and kernel-checked, then reduced by
//!   `ElabCtx::whnf` (the kernel weak-head reducer). Weak-head reduction is
//!   meaning-preserving — `is_def_eq(e, whnf e)` holds — so the returned `Expr` is
//!   the same value in normal form, still kernel-valid.
//!
//! An ill-typed or unresolvable argument fails with the ordinary elaboration
//! error. The value a query binds flows into a body that is itself elaborated and
//! kernel-checked by the normal pipeline; there is no kernel bypass and no new
//! axiom.

use super::ElabCtx;
use crate::error::ElabError;
use clean_kernel::Expr;
use clean_parser::{DoElem, SurfaceExpr};

/// Query head identifiers for the single-argument `inferType e` query. Its value
/// is the inferred type of `e` (a kernel `Expr` computed from elaboration state).
const QUERY_INFER_TYPE: &[&str] = &["inferType", "Expr.inferType"];

/// Query head identifiers for the single-argument `whnf e` query. Its value is the
/// weak-head normal form of `e` (a meaning-preserving reduction; see module docs).
const QUERY_WHNF: &[&str] = &["whnf", "Expr.whnf"];

/// Query head identifiers for the two-argument `checkType e ty` query. Its value
/// is `e` itself, returned only if `e : ty` kernel-checks (else an honest error).
const QUERY_CHECK_TYPE: &[&str] = &["checkType", "Expr.checkType"];

/// If `expr` is a recognized single-argument query call with one of the given
/// `heads` (`inferType e` / `whnf e`), return the (already-substituted) argument
/// sub-term. Returns `None` for any other shape so the caller falls through to the
/// constructor evaluator / normal path.
///
/// Recognizes both the bare head and the qualified `Expr.<head>` projection, with
/// exactly one positional argument (no named arguments).
fn as_unary_query_call<'e>(expr: &'e SurfaceExpr, heads: &[&str]) -> Option<&'e SurfaceExpr> {
    let SurfaceExpr::App(_, func, args) = expr else {
        return None;
    };
    if args.len() != 1 || args.iter().any(|a| a.name.is_some()) {
        return None;
    }
    let head = query_head_name(func)?;
    heads.contains(&head.as_str()).then(|| &args[0].expr)
}

/// If `expr` is `inferType e` (or the `Expr.inferType` alias), return `e`.
fn as_infer_type_call(expr: &SurfaceExpr) -> Option<&SurfaceExpr> {
    as_unary_query_call(expr, QUERY_INFER_TYPE)
}

/// If `expr` is `whnf e` (or the `Expr.whnf` alias), return `e`.
fn as_whnf_call(expr: &SurfaceExpr) -> Option<&SurfaceExpr> {
    as_unary_query_call(expr, QUERY_WHNF)
}

/// If `expr` is the two-argument `checkType e ty` query (or its `Expr.checkType`
/// alias), return the (already-substituted) `(e, ty)` argument sub-terms. Returns
/// `None` for any other shape (wrong head, wrong arity, or named arguments) so the
/// caller falls through to the constructor evaluator / normal path.
fn as_check_type_call(expr: &SurfaceExpr) -> Option<(&SurfaceExpr, &SurfaceExpr)> {
    let SurfaceExpr::App(_, func, args) = expr else {
        return None;
    };
    if args.len() != 2 || args.iter().any(|a| a.name.is_some()) {
        return None;
    }
    let head = query_head_name(func)?;
    QUERY_CHECK_TYPE
        .contains(&head.as_str())
        .then(|| (&args[0].expr, &args[1].expr))
}

/// Whether `expr` is any recognized query call (`inferType` / `whnf` / `checkType`
/// or their `Expr.*` aliases). Used to gate the value-channel evaluator.
fn is_query_call(expr: &SurfaceExpr) -> bool {
    as_infer_type_call(expr).is_some()
        || as_whnf_call(expr).is_some()
        || as_check_type_call(expr).is_some()
}

/// Extract the head identifier of a query call: a bare `Ident` (`inferType`) or
/// the qualified projection `Expr.inferType` rendered as the dotted string.
fn query_head_name(func: &SurfaceExpr) -> Option<String> {
    match func {
        SurfaceExpr::Ident(_, name) => Some(name.clone()),
        SurfaceExpr::Proj(_, base, clean_parser::Projection::Named(field)) => {
            let SurfaceExpr::Ident(_, base_name) = base.as_ref() else {
                return None;
            };
            Some(format!("{base_name}.{field}"))
        }
        _ => None,
    }
}

/// Whether a term-elaborator body is in the value-channel / query shape this
/// module interprets. Used to gate the (mutable, state-evaluating) path so an
/// ordinary body is left entirely to the existing pipeline.
///
/// Recognized shapes:
/// - a terminal query: `inferType e`, `whnf e`, or `checkType e ty`;
/// - a value-channel `do`-block whose statements are pure value lets binding a
///   query (`let t := inferType e`) followed by a terminal expression that uses
///   the bound value (`do let t := inferType e; checkType e t`).
#[must_use]
pub(super) fn is_meta_query_body(body: &SurfaceExpr) -> bool {
    if is_query_call(body) {
        return true;
    }
    matches!(body, SurfaceExpr::Do(_, elems) if do_block_binds_query(elems))
}

/// Whether a `do`-block contains at least one value-let binding a query
/// (`let x := inferType e` / `whnf e` / `checkType e ty`) — the value-channel
/// marker. Any block without one is not the value-channel shape and is left to the
/// normal pipeline.
fn do_block_binds_query(elems: &[DoElem]) -> bool {
    elems
        .iter()
        .any(|elem| matches!(elem, DoElem::Let(_, _, val) if is_query_call(val)))
}

impl<'a> ElabCtx<'a> {
    /// Evaluate a term-elaborator body in the value-channel / query shape,
    /// returning the resulting kernel `Expr`.
    ///
    /// Returns `None` if `body` is not a recognized meta-query shape, so the
    /// caller falls through to the constructor evaluator and the normal pipeline.
    /// On a recognized shape, returns `Some(Ok(expr))` with the elaborated,
    /// kernel-checkable result, or `Some(Err(..))` if a query argument fails to
    /// elaborate / type-infer (honest error — never a fabricated term).
    ///
    /// # Soundness
    ///
    /// Each query elaborates and kernel-checks its argument through the normal
    /// pipeline and reads its type from the kernel via [`ElabCtx::infer_type`].
    /// Bound values are spliced into later positions as already-elaborated kernel
    /// `Expr`s and the final body result is returned for the caller to use under
    /// the normal kernel check. No goal is closed and no term is accepted without
    /// the normal kernel path.
    pub(super) fn eval_meta_query_body(
        &mut self,
        body: &SurfaceExpr,
    ) -> Option<Result<Expr, ElabError>> {
        if !is_meta_query_body(body) {
            return None;
        }
        Some(self.eval_meta_query_body_inner(body))
    }

    /// Inner evaluation for a recognized meta-query body (`is_meta_query_body`
    /// already returned `true`).
    fn eval_meta_query_body_inner(&mut self, body: &SurfaceExpr) -> Result<Expr, ElabError> {
        // Terminal query: the body itself is `inferType e` / `whnf e` /
        // `checkType e ty`.
        if let Some(value) = self.eval_query_call(body)? {
            return Ok(value);
        }

        // Value-channel `do`-block: run pure value lets binding queries, then
        // elaborate the terminal expression with the bound values in scope. The
        // names introduced here are tracked so they can be removed afterwards,
        // keeping the value channel scoped to this body.
        let SurfaceExpr::Do(_, elems) = body else {
            // `is_meta_query_body` guarantees one of the two shapes; this is
            // defensive and fails honestly rather than fabricating a value.
            return Err(ElabError::Unsupported {
                feature: "metaprogram query body shape".to_owned(),
            });
        };

        let mut introduced: Vec<String> = Vec::new();
        let result = self.run_query_do_block(elems, &mut introduced);
        // Always unbind the names this body introduced, on success or failure, so
        // a value binding never leaks into a later, unrelated elaboration.
        for name in &introduced {
            self.meta_value_bindings.remove(name);
        }
        result
    }

    /// Interpret a value-channel `do`-block statement-by-statement.
    ///
    /// Supported statements:
    /// - `let x := inferType e` (also `whnf e` / `checkType e ty`) — evaluate the
    ///   query and bind `x -> Expr`;
    /// - `let x := <expr>` where `<expr>` is itself a meta-query body — evaluate
    ///   recursively and bind the value;
    /// - a terminal expression statement — if it is itself a query (e.g.
    ///   `checkType e t` referencing an earlier binding `t`), it is evaluated as a
    ///   query; otherwise it is elaborated by the normal path (with bound values in
    ///   scope) as the block's result.
    ///
    /// Any other statement defers honestly (`Unsupported`), never fabricating a
    /// value. Bound names are recorded in `introduced` for cleanup by the caller.
    fn run_query_do_block(
        &mut self,
        elems: &[DoElem],
        introduced: &mut Vec<String>,
    ) -> Result<Expr, ElabError> {
        let Some((last, prefix)) = elems.split_last() else {
            return Err(ElabError::Unsupported {
                feature: "empty metaprogram query do-block".to_owned(),
            });
        };
        for elem in prefix {
            match elem {
                DoElem::Let(_, binder, val) => {
                    let value = self.eval_query_value(val)?;
                    self.meta_value_bindings.insert(binder.name.clone(), value);
                    introduced.push(binder.name.clone());
                }
                _ => {
                    return Err(ElabError::Unsupported {
                        feature: "non-let statement in metaprogram query do-block".to_owned(),
                    });
                }
            }
        }
        // The terminal statement is the block's value. If it is itself a query
        // (possibly referencing an earlier binding, e.g. `checkType e t`), it is
        // evaluated as a query; otherwise it is an ordinary expression elaborated
        // by the normal path (with the bound values in scope via `elab_ident`).
        match last {
            DoElem::Expr(_, expr) => {
                if let Some(value) = self.eval_query_call(expr)? {
                    return Ok(value);
                }
                self.elaborate(expr)
            }
            DoElem::Let(_, binder, val) => {
                // A trailing `let` with no body has no result to return.
                let _ = (binder, val);
                Err(ElabError::Unsupported {
                    feature: "metaprogram query do-block ending in a binding".to_owned(),
                })
            }
            _ => Err(ElabError::Unsupported {
                feature: "unsupported terminal in metaprogram query do-block".to_owned(),
            }),
        }
    }

    /// Evaluate the right-hand side of a value-channel `let`: either a recognized
    /// query (`inferType e` / `whnf e` / `checkType e ty`) or a nested meta-query
    /// body. Returns the kernel `Expr` value to bind.
    fn eval_query_value(&mut self, val: &SurfaceExpr) -> Result<Expr, ElabError> {
        if let Some(value) = self.eval_query_call(val)? {
            return Ok(value);
        }
        if is_meta_query_body(val) {
            return self.eval_meta_query_body_inner(val);
        }
        Err(ElabError::Unsupported {
            feature: "metaprogram value-let RHS is not a recognized query".to_owned(),
        })
    }

    /// If `expr` is a recognized query call, evaluate it to its kernel `Expr`
    /// value and return `Some(value)`. Returns `Ok(None)` when `expr` is not a
    /// query call (so the caller can fall through), and `Err(..)` when a query was
    /// recognized but failed honestly (bad argument / type mismatch).
    fn eval_query_call(&mut self, expr: &SurfaceExpr) -> Result<Option<Expr>, ElabError> {
        if let Some(arg) = as_infer_type_call(expr) {
            return self.eval_infer_type_query(arg).map(Some);
        }
        if let Some(arg) = as_whnf_call(expr) {
            return self.eval_whnf_query(arg).map(Some);
        }
        if let Some((e, ty)) = as_check_type_call(expr) {
            return self.eval_check_type_query(e, ty).map(Some);
        }
        Ok(None)
    }

    /// Evaluate `inferType <arg>`: elaborate `<arg>` through the normal pipeline,
    /// then infer its type. The argument may reference an earlier value binding
    /// (spliced in via `elab_ident`).
    ///
    /// # Soundness
    ///
    /// `elaborate` kernel-checks `<arg>` exactly like any other term;
    /// `infer_type` reads the type from the kernel. An unresolvable or ill-typed
    /// argument fails honestly. No fabrication.
    fn eval_infer_type_query(&mut self, arg: &SurfaceExpr) -> Result<Expr, ElabError> {
        let elaborated = self.elaborate(arg)?;
        self.infer_type(&elaborated)
    }

    /// Evaluate `whnf <arg>`: elaborate `<arg>` through the normal pipeline, then
    /// weak-head-normalize the kernel-checked term. The argument may reference an
    /// earlier value binding (spliced in via `elab_ident`).
    ///
    /// # Soundness
    ///
    /// `elaborate` kernel-checks `<arg>`; [`ElabCtx::whnf`] is the kernel
    /// weak-head reducer, which is meaning-preserving (`is_def_eq(arg, whnf arg)`).
    /// The returned `Expr` is the same value in normal form — no fabrication, no
    /// change of meaning.
    fn eval_whnf_query(&mut self, arg: &SurfaceExpr) -> Result<Expr, ElabError> {
        let elaborated = self.elaborate(arg)?;
        Ok(self.whnf(&elaborated))
    }

    /// Evaluate `checkType <e> <ty>`: elaborate both `<e>` and `<ty>` through the
    /// normal pipeline, then verify `e : ty` against the kernel. On success return
    /// the kernel-checked term `e`; on mismatch fail honestly with
    /// [`ElabError::TypeMismatch`]. Either argument may reference an earlier value
    /// binding (spliced in via `elab_ident`).
    ///
    /// # Soundness
    ///
    /// Both arguments are elaborated and kernel-checked by the normal pipeline. The
    /// inferred type of `e` is compared to `ty` via [`ElabCtx::is_def_eq`], the
    /// kernel definitional-equality check. `e` is returned *only* when that check
    /// succeeds, so a term is never accepted at a type it does not have; otherwise
    /// the query errors. No goal is closed and nothing is fabricated.
    fn eval_check_type_query(
        &mut self,
        e: &SurfaceExpr,
        ty: &SurfaceExpr,
    ) -> Result<Expr, ElabError> {
        let elaborated = self.elaborate(e)?;
        let expected_ty = self.elaborate(ty)?;
        let actual_ty = self.infer_type(&elaborated)?;
        if self.is_def_eq(&actual_ty, &expected_ty) {
            Ok(elaborated)
        } else {
            Err(ElabError::TypeMismatch {
                expected: format!("{expected_ty:?}"),
                actual: format!("{actual_ty:?}"),
            })
        }
    }
}

#[cfg(test)]
use clean_parser::SurfaceArg;

/// Test-only constructor for a positional single-argument `App` query call with
/// the given head, kept here so the recognizer tests can build the surface shapes
/// without re-deriving them.
#[cfg(test)]
fn unary_query_call(head: &str, arg: SurfaceExpr) -> SurfaceExpr {
    SurfaceExpr::App(
        clean_parser::Span::dummy(),
        Box::new(SurfaceExpr::Ident(
            clean_parser::Span::dummy(),
            head.to_owned(),
        )),
        vec![SurfaceArg::positional(arg)],
    )
}

/// Test-only constructor for an `inferType <arg>` call.
#[cfg(test)]
pub(super) fn infer_type_call(arg: SurfaceExpr) -> SurfaceExpr {
    unary_query_call("inferType", arg)
}

/// Test-only constructor for a `whnf <arg>` call.
#[cfg(test)]
pub(super) fn whnf_call(arg: SurfaceExpr) -> SurfaceExpr {
    unary_query_call("whnf", arg)
}

/// Test-only constructor for a `checkType <e> <ty>` call.
#[cfg(test)]
pub(super) fn check_type_call(e: SurfaceExpr, ty: SurfaceExpr) -> SurfaceExpr {
    SurfaceExpr::App(
        clean_parser::Span::dummy(),
        Box::new(SurfaceExpr::Ident(
            clean_parser::Span::dummy(),
            "checkType".to_owned(),
        )),
        vec![SurfaceArg::positional(e), SurfaceArg::positional(ty)],
    )
}

#[cfg(test)]
#[path = "meta_query_tests.rs"]
mod tests;
