// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Certificate-generating type inference.
//!
//! Split into submodules by concern:
//! - `infer_core` — core CIC type inference (BVar, FVar, Sort, Const, App, Lam, Pi, Let, Lit, Proj, MData)
//! - `infer_modes` — mode-specific type inference (Cubical, ZFC, Impredicative)
//! - `infer_zfc` — ZFC set certificate generation
//! - `rebind` — FVar→BVar certificate conversion
//! - `abstract_fvar` — FVar abstraction in expressions

mod abstract_fvar;
mod infer_core;
mod infer_modes;
mod infer_zfc;
mod rebind;

pub(crate) use abstract_fvar::abstract_fvar_in_expr;
pub(crate) use rebind::convert_fvar_cert_to_bvar;

use std::sync::Arc;
use std::sync::LazyLock;

use crate::expr::{stack_safe, Expr};
use crate::name::Name;
use crate::tc::TypeChecker;
use crate::TypeError;

/// Pre-interned names for type inference (avoids repeated allocation).
static NAME_NAT: LazyLock<Name> = LazyLock::new(|| Name::from_string("Nat"));
static NAME_STRING: LazyLock<Name> = LazyLock::new(|| Name::from_string("String"));
static NAME_ZFC_SET: LazyLock<Name> = LazyLock::new(|| Name::from_string("ZFC.Set"));

impl<'env> TypeChecker<'env> {
    /// Infer the type of an expression with proof certificate generation.
    ///
    /// Returns both the inferred type and a proof certificate that can
    /// be independently verified to confirm the typing derivation.
    ///
    /// If a trace collector is set and enabled, emits a `TraceEntry::Infer`
    /// entry for the typing operation.
    ///
    /// # Contract
    ///
    /// REQUIRES: `e` contains no unbound `BVar` - all bound variables must be under binders
    /// REQUIRES: All `FVar` in `e` must be in scope (declared in the local context)
    /// REQUIRES: All `Const` in `e` must be in the environment
    ///
    /// ENSURES: On success, returns `(T, cert)` where `T` is the inferred type of `e`
    /// ENSURES: On success, the certificate `cert` can be independently verified to confirm `e : T`
    /// ENSURES: `cert.verify(env) == Ok(())` (certificate is valid)
    /// ENSURES: Type inference is deterministic - same `e` in same context yields same `(T, cert)`
    /// ENSURES: On error, returns appropriate `TypeError` variant identifying the issue
    pub fn infer_type_with_cert(
        &self,
        e: &Expr,
    ) -> Result<(Expr, crate::cert::ProofCert), TypeError> {
        // The returned certificate is retained by the caller (replayed /
        // serialized), so the shared-`Arc` memo must cache REAL certs, not the
        // discard-path placeholder. See `cert_retained` and
        // `infer_type_with_cert_arc`. RAII-restore on the way out.
        let prev_retained = self.cert_retained.replace(true);
        let result = stack_safe(|| self.infer_type_with_cert_impl(e));
        self.cert_retained.set(prev_retained);
        let result = result?;

        // Emit trace entry if tracing is enabled
        if self.tracing_enabled() {
            if let Some(collector) = &self.trace_collector {
                let expr_hash = crate::cert::trace::expr_hash(e);
                collector.record(crate::cert::TraceEntry::Infer {
                    expr_hash,
                    cert: result.1.clone(),
                });
            }
        }

        Ok(result)
    }

    /// Implementation of type inference with certificates (called via stacker::maybe_grow).
    ///
    /// Every recursive call goes through `stack_safe` to prevent stack overflow
    /// on deeply nested expressions (e.g., 8+ Pi levels with 6-deep App chains
    /// in homotopy topology types). See #1455.
    fn infer_type_with_cert_impl(
        &self,
        e: &Expr,
    ) -> Result<(Expr, crate::cert::ProofCert), TypeError> {
        // Track WW: bracket the WHOLE inference recursion so `infer_arc_memo`
        // persists across it (collapsing the shared-`Arc` DAG to linear work) and
        // is cleared exactly once when the outermost frame returns — at which
        // point the memoized `Arc` addresses become reusable and must not leak
        // into a later top-level inference call.
        let depth = self.infer_memo_depth.get();
        self.infer_memo_depth.set(depth + 1);
        let result = stack_safe(|| self.infer_type_with_cert_inner(e));
        self.infer_memo_depth.set(depth);
        if depth == 0 {
            self.infer_arc_memo.borrow_mut().clear();
        }
        result
    }

    /// Memoized inference over an `Arc`-shared sub-expression (Track WW).
    ///
    /// Identical result to `infer_type_with_cert_impl(arc)` but consults
    /// `infer_arc_memo` keyed on the `Arc<Expr>` node's STABLE address. Used for
    /// the recursive children of `App`, which are exactly the positions where
    /// match lowering's shared-`Arc` "fallback" duplicates compound, turning an
    /// `O(distinct nodes)` DAG into an `O(branching^depth)` tree walk. The pointee
    /// address is stable (an interned child, never a transient stack `Expr`) and
    /// we pin a clone of the `Arc` in the memo value so the address cannot be
    /// freed and reused while the entry lives. The memo is cleared by the
    /// outermost `infer_type_with_cert_impl` frame. See the `infer_arc_memo`
    /// soundness note in `tc/mod.rs`.
    pub(crate) fn infer_type_with_cert_arc(
        &self,
        arc: &Arc<Expr>,
    ) -> Result<(Expr, crate::cert::ProofCert), TypeError> {
        let infer_only = self.infer_only.get();
        let key = (Arc::as_ptr(arc) as usize, infer_only, self.ctx_len());
        if let Some((_pin, ty, cert)) = self.infer_arc_memo.borrow().get(&key) {
            return Ok((ty.clone(), cert.clone()));
        }
        let (ty, cert) = self.infer_type_with_cert_impl(arc.as_ref())?;
        // Cert-clone economy (Track WW): in `infer_only=true` (inference) mode the
        // certificate is ultimately discarded by the public `infer_type`
        // (`cross_validate_with_micro` runs only when `infer_only=false`). Storing
        // — and re-cloning on every DAG hit — the full structural cert there would
        // re-introduce the exponential it was built to avoid (the cert tree mirrors
        // the expanded term). So in inference mode we cache a cheap placeholder
        // cert; the freshly-computed `cert` is still returned to THIS caller intact,
        // only later memo HITS get the placeholder. In `check_type`
        // (`infer_only=false`) the real cert is cached and returned so the
        // micro-checker cross-validation remains exact.
        let cached_cert = if infer_only && !self.cert_retained.get() {
            crate::cert::ProofCert::Sort {
                level: crate::level::Level::zero(),
            }
        } else {
            cert.clone()
        };
        self.infer_arc_memo
            .borrow_mut()
            .insert(key, (arc.clone(), ty.clone(), cached_cert));
        Ok((ty, cert))
    }
}
