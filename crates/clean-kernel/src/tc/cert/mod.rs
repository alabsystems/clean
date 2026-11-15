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

#[cfg(test)]
mod abstract_fvar;
mod infer_core;
mod infer_modes;
mod infer_zfc;
mod rebind;

#[cfg(test)]
pub(crate) use abstract_fvar::abstract_fvar_in_expr;
pub(crate) use rebind::convert_fvar_cert_to_bvar;
pub(super) use rebind::RebindClosedMemo;

use std::sync::Arc;
use std::sync::LazyLock;

use crate::expr::{stack_safe, Expr};
use crate::name::Name;
use crate::tc::TypeChecker;
use crate::TypeError;

// Clear structural summaries on normal/error outer inference exits and initial
// unwinding. This does not repair the existing inference-depth/context state
// after a caught panic: checker reuse after unwinding is not supported here.
// The existing typing memo and context lifecycle are unchanged.
pub(super) struct ClearRebindMemo<'a>(pub(super) &'a std::cell::RefCell<RebindClosedMemo>);

impl Drop for ClearRebindMemo<'_> {
    fn drop(&mut self) {
        self.0.borrow_mut().clear();
    }
}

/// Pre-interned names for type inference (avoids repeated allocation).
static NAME_ZFC_SET: LazyLock<Name> = LazyLock::new(|| Name::from_string("ZFC.Set"));

impl<'env> TypeChecker<'env> {
    fn rebind_certificate_body(
        &self,
        cert: crate::cert::ProofCert,
        fvar_id: crate::expr::FVarId,
    ) -> crate::cert::ProofCert {
        rebind::convert_with_closed_memo(
            cert,
            fvar_id,
            0,
            &mut self.rebind_closed_memo.borrow_mut(),
            self.max_cache_entries,
        )
    }

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
        let _metered = self.begin_operation();
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

    /// [`Self::infer_type_with_cert`] in **full check mode** (`infer_only =
    /// false`): the certificate-path counterpart of `infer_type_full`, which
    /// runs whichever `infer_type` body the profile compiles.
    ///
    /// Check mode is where the App argument, Lam domain and Let type/value
    /// checks fire. Without this entry point an integration test can compare
    /// the release body against the certificate body only in infer-only mode,
    /// so the errors those checks raise (and the `ExprLocation` they carry)
    /// were never compared (`tests/release_infer_parity.rs`). Part of #3425.
    ///
    /// # Contract
    /// REQUIRES: as [`Self::infer_type_with_cert`].
    /// ENSURES: same result as [`Self::infer_type_with_cert`] with
    /// `infer_only = false`; `infer_only` is restored on return.
    pub fn infer_type_with_cert_full(
        &self,
        e: &Expr,
    ) -> Result<(Expr, crate::cert::ProofCert), TypeError> {
        let prev = self.infer_only.replace(false);
        let result = self.infer_type_with_cert(e);
        self.infer_only.set(prev);
        result
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
        // persists across it (reusing admitted shared-`Arc` keys) and
        // is cleared exactly once when the outermost frame returns — at which
        // point the memoized `Arc` addresses become reusable and must not leak
        // into a later top-level inference call.
        let depth = self.infer_memo_depth.get();
        let _clear_rebind = (depth == 0).then(|| ClearRebindMemo(&self.rebind_closed_memo));
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
    ///
    /// The returned Arc is installed directly in the parent certificate. Memo
    /// hits therefore preserve the certified node itself, not only descendants
    /// of a fresh shallow clone. The public Expr-root API still returns a value.
    pub(crate) fn infer_type_with_cert_arc(
        &self,
        arc: &Arc<Expr>,
    ) -> Result<(Expr, Arc<crate::cert::ProofCert>), TypeError> {
        let _metered = self.metered_scope();
        if self.sharing_replay.is_some() {
            return self
                .infer_type_with_cert_impl(arc.as_ref())
                .map(|(ty, cert)| (ty, Arc::new(cert)));
        }
        // Do not leave an entry outside the outer inference frame that owns
        // its lifetime. Normal App-child callers already have such a frame.
        if self.infer_memo_depth.get() == 0 {
            self.ensure_cache_theory();
            return self
                .infer_type_with_cert_impl(arc.as_ref())
                .map(|(ty, cert)| (ty, Arc::new(cert)));
        }
        let infer_only = self.infer_only.get();
        let needs_cert = !infer_only || self.cert_retained.get();
        let key = self.infer_arc_memo_key(arc);
        if let Some((_pin, ty, cert)) = self.infer_arc_memo.borrow().get(&key) {
            if let Some(cert) = cert {
                return Ok((ty.clone(), cert.clone()));
            }
            if !needs_cert {
                // Only the discard-only internal path may return a placeholder.
                // Public retained inference sets cert_retained before entering.
                return Ok((
                    ty.clone(),
                    Arc::new(crate::cert::ProofCert::Sort {
                        level: crate::level::Level::zero(),
                    }),
                ));
            }
        }
        let (ty, cert) = self.infer_type_with_cert_impl(arc.as_ref())?;
        let cert = Arc::new(cert);
        // A fast-inference re-entry can have cached only a type. Full checking
        // and retained inference must derive a REAL certificate and upgrade
        // that entry in either window, before considering any new-admission
        // rotation. No certificate is weakened or replaced by a placeholder.
        let mut memo = self.infer_arc_memo.borrow_mut();
        if let Some(entry) = memo.get_mut(&key) {
            if needs_cert {
                entry.1 = ty.clone();
                entry.2 = Some(cert.clone());
            }
        } else {
            memo.insert_if_absent_with(key, self.max_cache_entries, || {
                let cached_cert = needs_cert.then(|| cert.clone());
                (arc.clone(), ty.clone(), cached_cert)
            });
        }
        Ok((ty, cert))
    }
}
