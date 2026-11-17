// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Type inference for the clean kernel type checker.
//!
//! Contains:
//! - `infer_type` — public entry point (debug builds generate certificates)
//! - `infer_type_fast` / `_impl` / `_inner` — release-mode fast path
//! - `check_type` — verify an expression has a given type
//! - `infer_sort` — infer type and extract universe level
//! - `ctor_field_sort_levels` — constructor field universe check
//! - Type cache helpers (`try_get_cached_type`, `cache_type_result`)
//!
//! Mode-specific and projection inference are in sibling modules:
//! - `infer_cubical.rs` — cubical mode helpers (#2594)
//! - `infer_zfc.rs` — ZFC + impredicative mode helpers (#2594)
//! - `infer_proj.rs` — projection typing, batch cache, `is_prop` (#2594)

#[cfg(all(feature = "inference-stats", not(debug_assertions)))]
use super::reduction_stats::inference::{self as work_stats, ArcEvent, Operation};
use crate::expr::stack_safe;
use crate::expr::{Expr, ExprKind, FVarId};
use crate::level::Level;
use crate::name::Name;
#[cfg(not(debug_assertions))]
use crate::tc::expr_location::ExprPathStep;
use crate::tc::{TypeChecker, TypeError};
use std::sync::Arc;
use std::sync::LazyLock;

/// Pre-interned names for literal type inference (avoids repeated allocation).
static NAME_NAT: LazyLock<Name> = LazyLock::new(|| Name::from_string("Nat"));
static NAME_STRING: LazyLock<Name> = LazyLock::new(|| Name::from_string("String"));

static NAME_EAGER_REDUCE: LazyLock<Name> = LazyLock::new(|| Name::from_string("eagerReduce"));

/// The literal-inference computation shared by the release and certificate paths.
///
/// Keeping the real constructors in this function gives source extraction one
/// production body to attach to the literal typing specification. The input
/// payload is preserved by the caller; this computation selects its type without
/// consulting the environment. This factoring is not a refinement proof.
#[inline]
pub(super) fn infer_literal_type(lit: &crate::expr::Literal) -> Expr {
    match lit {
        crate::expr::Literal::Nat(_) => Expr::const_(NAME_NAT.clone(), vec![]),
        crate::expr::Literal::String(_) => Expr::const_(NAME_STRING.clone(), vec![]),
    }
}

/// Check if an expression is `eagerReduce _ _` (the constant applied to exactly 2 args).
///
/// Lean 4 reference: `type_checker.cpp:159-161`
/// ```cpp
/// bool is_eager_reduce(expr const & e) {
///     return is_const(get_app_fn(e), "eagerReduce") && get_app_num_args(e) == 2;
/// }
/// ```
#[inline]
pub(crate) fn is_eager_reduce(e: &Expr) -> bool {
    if e.get_app_num_args() != 2 {
        return false;
    }
    matches!(e.get_app_fn().kind(), ExprKind::Const(name, _) if *name == *NAME_EAGER_REDUCE)
}

impl<'env> TypeChecker<'env> {
    /// Close a let result identically in fast and certificate inference.
    /// Call only after the caller has checked the annotation/value premises
    /// required by its current inference mode and popped the temporary binder.
    pub(super) fn close_inferred_let_type(
        &self,
        let_name: &Name,
        ty: &Arc<Expr>,
        val: &Arc<Expr>,
        body_type: Expr,
        fvar_id: FVarId,
    ) -> Expr {
        // Retain a checked, well-scoped let in a dependent result type.
        // Eager substitution duplicates the value throughout that type
        // before enclosing binders abstract it again. The retained let
        // has exactly the same zeta normal form. Only full checking has
        // established the annotation/value premises required to reuse it.
        // Loose replacement terms retain the original substitution rule.
        if !self.infer_only.get()
            && !ty.has_loose_bvars_quick()
            && !val.has_loose_bvars_quick()
            && !body_type.has_loose_bvars_quick()
        {
            if !body_type.may_contain_fvar(fvar_id) {
                return body_type;
            }
            let abstracted = body_type.abstract_fvar(fvar_id);
            // The upper bound is conservative: do not retain an unused
            // declaration merely because a larger FVar was present.
            if !abstracted.has_loose_bvars_quick() {
                return body_type;
            }
            return Expr::from_kind(ExprKind::Let(
                let_name.clone(),
                ty.clone(),
                val.clone(),
                Arc::new(abstracted),
                false,
            ));
        }

        // Infer-only or loose inputs keep the existing zeta rule.
        #[cfg(all(feature = "inference-stats", not(debug_assertions)))]
        work_stats::record_operation(Operation::SubstLet);
        body_type.subst_fvar(fvar_id, val)
    }

    /// Return the domain/body of a Pi type while avoiding redundant WHNF calls.
    ///
    /// Projection inference often walks constructor telescopes that are already
    /// syntactic `Pi` chains after substitution. In that case, we can skip
    /// `whnf_impl` entirely and avoid O(n^2) WHNF traffic across `proj i` calls
    /// during structure eta expansion (#1516).
    pub(super) fn pi_domain_body_quick(&self, ty: &Expr) -> Option<(Expr, Expr)> {
        if let ExprKind::Pi(_, domain, body) = &ty.kind {
            return Some((domain.as_ref().clone(), body.as_ref().clone()));
        }

        let ty_whnf = self.whnf_impl(ty);
        match &ty_whnf.kind {
            ExprKind::Pi(_, domain, body) => Some((domain.as_ref().clone(), body.as_ref().clone())),
            _ => None,
        }
    }

    /// Infer the type of an expression
    ///
    /// In debug builds, this method also generates a typing certificate.
    ///
    /// In release builds, uses a fast path without certificate generation for performance.
    ///
    /// # Debug/release contract
    ///
    /// The typing logic is identical between the debug and release bodies in
    /// check mode (`infer_only = false`). In infer-only mode (`infer_only =
    /// true`, the default for `infer_type`) the debug body is STRICTLY
    /// STRICTER: the certificate-path traversal infers the App argument,
    /// the Lam domain, and the Let type/value unconditionally
    /// (`tc/cert/infer_core.rs` App/Lam/Let arms), while the release body
    /// guards each of those inferences behind `!infer_only`
    /// (`infer_type_fast_impl` App/Lam/Let arms). Debug can therefore `Err`
    /// on inputs where release `Ok`s; it never accepts more. The deployed
    /// behavior is the release body.
    ///
    /// # Contract
    ///
    /// REQUIRES: All FVars in `e` are defined in `self.ctx`
    /// REQUIRES: All Consts in `e` are defined in `self.env`
    /// REQUIRES: `e` has no dangling BVars (BVar indices beyond scope)
    ///
    /// ENSURES: On success, `result` is well-typed (`infer_type(result)` succeeds)
    /// ENSURES: On success, `is_def_eq(e, e)` holds (reflexivity)
    /// ENSURES: Deterministic - same input yields same output
    #[cfg(debug_assertions)]
    pub fn infer_type(&self, e: &Expr) -> Result<Expr, TypeError> {
        let _metered = self.begin_operation();
        self.tick_heartbeat()?;
        // Keep retained/replay/trace consumers on the original certificate
        // path, including plain inference nested inside a retained operation.
        // A configured collector may become enabled during the call.
        let ty = if self.cert_retained.get()
            || self.trace_collector.is_some()
            || self.sharing_replay.is_some()
        {
            self.infer_type_with_cert(e)?.0
        } else {
            self.infer_type_discard_cert(e)?
        };

        // Invariant (CIC): type of a type is always a Sort/SProp.
        // Check WHNF since result may not be syntactically a Sort.
        // Skip for terms containing free variables — FVars may originate from
        // elaborator-scope local contexts that are not available to the kernel
        // TypeChecker (e.g., CrossValidator passes elaborated exprs to a
        // standalone TC). Recursing into infer_type for such FVars can panic.
        //
        // Guard: skip when already inside this assert to prevent infinite
        // recursion (infer_type -> assert -> infer_type -> assert -> ...).
        // Part of #3285.
        debug_assert!(
            {
                if self.in_infer_type_assert.get() {
                    // Already inside the recursive check — skip to break cycle
                    true
                } else if ty.has_fvar_quick() || e.has_fvar_quick() {
                    // Cannot validate type-of-type when FVars are present
                    true
                } else {
                    self.in_infer_type_assert.set(true);
                    let result = match self.infer_type(&ty) {
                        Ok(t) => {
                            matches!(self.whnf(&t).kind(), ExprKind::Sort(_) | ExprKind::SProp)
                        }
                        // Any error in the recursive check (unknown FVar,
                        // heartbeat limit, missing constant in minimal env)
                        // is not an invariant violation — we simply cannot
                        // verify the invariant in this context.
                        Err(_) => true,
                    };
                    self.in_infer_type_assert.set(false);
                    result
                }
            },
            "invariant: infer_type result must be well-typed (type of type must be a Sort): \
             expr = {:?}, inferred type = {:?}",
            e,
            ty
        );

        // Invariant: inferred type must not introduce loose BVars that
        // weren't present in the input expression.
        debug_assert!(
            e.has_loose_bvars_quick() || !ty.has_loose_bvars_quick(),
            "invariant: infer_type produced type with escaping BVars for closed input: \
             expr = {:?}, type = {:?}",
            e,
            ty
        );

        Ok(ty)
    }

    /// Infer the type of an expression (release mode - fast path)
    ///
    /// Uses fast unchecked inference without certificate generation.
    ///
    /// # Debug/release contract
    ///
    /// Typing logic is identical to the debug body in check mode
    /// (`infer_only = false`). In infer-only mode (`infer_only = true`, the
    /// default for `infer_type`) this release body is STRICTLY MORE
    /// PERMISSIVE: it guards inference of the App argument, the Lam domain,
    /// and the Let type/value behind `!infer_only` (see the App/Lam/Let arms
    /// of `infer_type_fast_impl`), where the debug body infers all three
    /// unconditionally in the certificate-path traversal
    /// (`tc/cert/infer_core.rs`). Debug can `Err` where this body `Ok`s.
    /// This release body is the deployed behavior.
    ///
    /// # Contract
    ///
    /// REQUIRES: All FVars in `e` are defined in `self.ctx`
    /// REQUIRES: All Consts in `e` are defined in `self.env`
    /// REQUIRES: `e` has no dangling BVars (BVar indices beyond scope)
    ///
    /// ENSURES: On success, `result` is well-typed (`infer_type(result)` succeeds)
    /// ENSURES: On success, `is_def_eq(e, e)` holds (reflexivity)
    /// ENSURES: Deterministic - same input yields same output
    #[cfg(not(debug_assertions))]
    pub fn infer_type(&self, e: &Expr) -> Result<Expr, TypeError> {
        let _metered = self.begin_operation();
        self.tick_heartbeat()?;
        self.infer_type_fast(e)
    }

    /// Infer the type of an expression in infer-only mode.
    ///
    /// This is used by `is_def_eq` internals (proof irrelevance, eta expansion,
    /// structure eta, unit-like checks) that need to infer types but should NOT
    /// trigger recursive App/Let argument type checking.
    ///
    /// Lean 4 reference: all `infer_type` calls within `is_def_eq` use
    /// `infer_type_core(e, true)` — i.e., infer_only=true. Without this,
    /// when `check_type` sets `infer_only=false`, nested `infer_type` calls
    /// from within `is_def_eq` also do full App type checking, which triggers
    /// more `is_def_eq` calls, creating false TypeMismatch failures on valid
    /// expressions (e.g., `Lean.Syntax.brecOn_2.eq`).
    ///
    /// Part of #3134
    pub(super) fn infer_type_infer_only(&self, e: &Expr) -> Result<Expr, TypeError> {
        let prev = self.infer_only.get();
        self.infer_only.set(true);
        let result = self.infer_type(e);
        self.infer_only.set(prev);
        result
    }

    /// Fast type inference without certificate generation.
    ///
    /// This function implements the same typing logic as `infer_type_with_cert`
    /// in check mode (`infer_only = false`), without the overhead of generating
    /// proof certificates. Used in release mode for performance. In infer-only
    /// mode the two bodies are NOT identical: this one skips inferring the App
    /// argument, the Lam domain, and the Let type/value (each guarded behind
    /// `!infer_only` in the arms below), while `infer_type_with_cert` infers
    /// them unconditionally — so debug can `Err` where this body `Ok`s.
    ///
    /// When type caching is enabled and the local context is empty (closed term),
    /// results are cached for reuse on subsequent calls with the same expression.
    ///
    /// The typing rules are:
    /// - Sort(l) : Sort(succ(l))
    /// - FVar(id) : type_of(id) from context
    /// - Const(n, ls) : instantiate_type(n, ls) from environment
    /// - App(f, a) : B[a/x] when f : (x : A) → B and a : A
    /// - Lam(bi, A, b) : (x : A) → B when b : B
    /// - Pi(bi, A, B) : Sort(imax(l1, l2)) when A : Sort(l1), B : Sort(l2)
    /// - Let(A, v, b) : B[v/x] when v : A, b : B
    /// - Lit(n) : Nat or String
    #[cfg(not(debug_assertions))]
    fn infer_type_fast(&self, e: &Expr) -> Result<Expr, TypeError> {
        // Check cache first (only for closed terms - when local context is empty)
        let can_cache = self.ctx.borrow().is_empty();
        if can_cache {
            if let Some(cached_type) = self.try_get_cached_type(e) {
                return Ok(cached_type);
            }
        }

        // Compute type
        let result = stack_safe(|| self.infer_type_fast_impl(e))?;

        // Cache result for closed terms
        if can_cache {
            self.cache_type_result(e, &result);
        }

        Ok(result)
    }

    /// Try to get a cached type inference result.
    /// Returns `None` if caching is disabled or no cached result exists.
    #[cfg(not(debug_assertions))]
    fn try_get_cached_type(&self, e: &Expr) -> Option<Expr> {
        let mut cache_ref = self.type_cache.borrow_mut();
        if let Some(cache) = cache_ref.as_mut() {
            // Update env/mode hashes if environment or mode changed
            cache.set_env_hash(self.compute_env_hash());
            cache.set_mode_hash(self.compute_mode_hash());
            cache.get(e).cloned()
        } else {
            None
        }
    }

    /// Cache a type inference result.
    /// Does nothing if caching is disabled.
    #[cfg(not(debug_assertions))]
    fn cache_type_result(&self, e: &Expr, type_: &Expr) {
        let mut cache_ref = self.type_cache.borrow_mut();
        if let Some(cache) = cache_ref.as_mut() {
            cache.insert(e, type_.clone());
        }
    }

    /// Implementation of fast type inference (called via stacker::maybe_grow).
    ///
    /// Every recursive call goes through `stack_safe` to prevent stack overflow
    /// on deeply nested expressions. See #1455.
    #[cfg(not(debug_assertions))]
    pub(super) fn infer_type_fast_impl(&self, e: &Expr) -> Result<Expr, TypeError> {
        // Track WW: bracket the whole recursion so the Arc-identity infer memo
        // persists across it and is cleared once at the outermost frame. See the
        // `infer_arc_memo` soundness note in `tc/mod.rs`.
        let depth = self.infer_memo_depth.get();
        // Certificate inference can re-enter this shared inference frame.
        // Retire its structural summaries even when the outer owner is fast.
        let _clear_rebind =
            (depth == 0).then(|| super::cert::ClearRebindMemo(&self.rebind_closed_memo));
        self.infer_memo_depth.set(depth + 1);
        let result = stack_safe(|| self.infer_type_fast_inner(e));
        self.infer_memo_depth.set(depth);
        if depth == 0 {
            self.infer_arc_memo.borrow_mut().clear();
        }
        result
    }

    /// Memoized fast inference over an `Arc`-shared sub-expression (Track WW).
    ///
    /// Release-mode analogue of `infer_type_with_cert_arc`: keys on the `Arc<Expr>`
    /// node's stable address so the shared-`Arc` DAG produced by match lowering is
    /// inferred once per admitted distinct node while its entry lives. Fast
    /// inference needs only the type, so it can use either a type-only or certificate-bearing entry and
    /// stores no certificate of its own. Pins the `Arc` so its address cannot be
    /// reused while the entry lives. Two admission windows share the existing
    /// total cache limit; zero capacity disables admission, not inference.
    #[cfg(not(debug_assertions))]
    pub(super) fn infer_type_fast_arc(&self, arc: &Arc<Expr>) -> Result<Expr, TypeError> {
        if self.sharing_replay.is_some() {
            return self.infer_type_fast_impl(arc.as_ref());
        }
        // Child call sites already have an active inference frame. A direct
        // call must not insert an entry after its outer impl frame clears it.
        if self.infer_memo_depth.get() == 0 {
            #[cfg(feature = "inference-stats")]
            work_stats::record_arc(ArcEvent::NoFrame, self.infer_arc_memo.borrow().len());
            return self.infer_type_fast_impl(arc.as_ref());
        }
        let scoped_key = self.infer_arc_memo_key(arc);
        let independent_key = self.independent_infer_key(arc);
        let cached = {
            let memo = self.infer_arc_memo.borrow();
            independent_key
                .as_ref()
                .and_then(|key| memo.get(key))
                .or_else(|| memo.get(&scoped_key))
                .map(|(_, ty, _)| ty.clone())
        };
        if let Some(ty) = cached {
            #[cfg(feature = "inference-stats")]
            work_stats::record_arc(ArcEvent::Hit, self.infer_arc_memo.borrow().len());
            return Ok(ty);
        }
        #[cfg(feature = "inference-stats")]
        work_stats::record_arc(ArcEvent::Miss, self.infer_arc_memo.borrow().len());
        #[cfg(feature = "inference-stats")]
        work_stats::record_closed_input_miss(!arc.has_fvar_quick() && !arc.has_loose_bvars());
        let ty = self.infer_type_fast_impl(arc.as_ref());
        #[cfg(feature = "inference-stats")]
        if ty.is_err() {
            work_stats::record_arc(ArcEvent::InferenceError, self.infer_arc_memo.borrow().len());
        }
        let ty = ty?;
        let key = independent_key
            .filter(|_| self.independent_infer_admissible(arc, &ty))
            .unwrap_or(scoped_key);
        let mut memo = self.infer_arc_memo.borrow_mut();
        #[cfg(feature = "inference-stats")]
        let mut admitted = false;
        // A recursive inference may have supplied a real certificate in either
        // window; check for it before rotating or creating a type-only result.
        memo.insert_if_absent_with(key, self.max_cache_entries, || {
            let value = (arc.clone(), ty.clone(), None);
            #[cfg(feature = "inference-stats")]
            {
                admitted = true;
                // Only this vacant-entry closure creates a fast entry.
                // The shared memo insertion hook records its actual peak.
                work_stats::record_arc(ArcEvent::Admission, 0);
            }
            value
        });
        #[cfg(feature = "inference-stats")]
        if !admitted {
            work_stats::record_arc(
                if memo.get(&key).is_some() {
                    // A recursive certificate path may already have inserted it.
                    ArcEvent::RecursiveFill
                } else {
                    ArcEvent::CapacityRefusal
                },
                memo.len(),
            );
        }
        Ok(ty)
    }

    /// Inner implementation of fast type inference.
    #[cfg(not(debug_assertions))]
    fn infer_type_fast_inner(&self, e: &Expr) -> Result<Expr, TypeError> {
        #[cfg(feature = "inference-stats")]
        work_stats::record_visit(&e.kind, self.infer_memo_depth.get(), self.infer_only.get());
        match &e.kind {
            ExprKind::BVar(idx) => Err(TypeError::UnboundVariable(*idx)),
            ExprKind::FVar(id) => {
                let ty = self
                    .ctx
                    .borrow()
                    .get(*id)
                    .map(|d| d.type_.clone())
                    .ok_or(TypeError::UnknownFVar(*id))?;
                Ok(ty)
            }
            ExprKind::Sort(l) => {
                // Lean 4 parity: when infer_only=false, validate that all
                // Level::Param references in the sort's level are in the
                // declared level_params list.
                // Ref: type_checker.cpp:63-73 (check_level), :84-87 (Sort case)
                // Part of #3225.
                if !self.infer_only.get() {
                    self.check_level(l)?;
                }
                Ok(Expr::from_kind(ExprKind::Sort(Level::succ(l.clone()))))
            }
            ExprKind::Const(name, levels) => {
                #[cfg(feature = "debug-infer")]
                eprintln!(
                    "[infer_type] Const: name = {:?}, levels = {:?}",
                    name, levels
                );

                // Check level count before instantiation (#1277)
                let info = self
                    .env
                    .get_const(name)
                    .ok_or_else(|| TypeError::UnknownConst(name.clone()))?;
                if info.level_params.len() != levels.len() {
                    return Err(TypeError::LevelCountMismatch {
                        name: name.clone(),
                        expected: info.level_params.len(),
                        got: levels.len(),
                    });
                }

                // Lean 4 parity: when infer_only=false, check that the
                // constant is not unsafe or partial if those are disallowed.
                // Ref: type_checker.cpp:100-108 (infer_constant)
                // Part of #3226.
                if !self.infer_only.get() {
                    // Validate level params in constant's universe levels
                    for l in levels {
                        self.check_level(l)?;
                    }
                    // Check unsafe/partial safety
                    if !self.allow_unsafe && self.env.is_unsafe(name) {
                        return Err(TypeError::UnsafeDeclaration { name: name.clone() });
                    }
                    if !self.allow_partial && self.env.is_partial(name) {
                        return Err(TypeError::PartialDeclaration { name: name.clone() });
                    }
                }

                // `info` is in hand with a matching arity (checked above), so the
                // type is instantiated directly: no second `get_const` lookup on the
                // hot per-`Const` path. The theory picks the substitution: Clean's
                // collapsing `instantiate_level_params_direct` under `Extended`,
                // Lean's `instantiate_type_lparams` under the Lean theories, which
                // refuses an instantiation whose Lean answer depends on `.olean`
                // object sharing (`tc/level_profile.rs`, DECISIONS R150).
                let result: Result<Expr, TypeError> =
                    self.instantiate_levels_checked(name, &info.type_, &info.level_params, levels);

                #[cfg(feature = "debug-infer")]
                eprintln!("[infer_type] Const: instantiate_type result = {:?}", result);

                result
            }
            ExprKind::App(f, a) => {
                #[cfg(feature = "debug-infer")]
                eprintln!("[infer_type] App: f = {:?}, a = {:?}", f, a);

                self.expr_loc_push(ExprPathStep::AppFn);
                // Track WW: memoize on the Arc child's stable identity.
                let f_type = self.infer_type_fast_arc(f);
                self.expr_loc_pop();
                let f_type = f_type?;

                #[cfg(feature = "debug-infer")]
                eprintln!("[infer_type] App: f_type (pre-whnf) = {:?}", f_type);

                let f_type_whnf = self.whnf_impl(&f_type);

                #[cfg(feature = "debug-infer")]
                eprintln!("[infer_type] App: f_type_whnf = {:?}", f_type_whnf);

                match &f_type_whnf.kind {
                    ExprKind::Pi(_, expected_arg_type, result_type) => {
                        // Lean 4 parity: when infer_only=true (the default for
                        // infer_type), skip the argument type check entirely.
                        // Only check when infer_only=false (set by check_type).
                        // Ref: type_checker.cpp:163-196 (infer_app)
                        if !self.infer_only.get() {
                            // SOUNDNESS: infer the argument type in the CURRENT mode
                            // (infer_only stays false in check mode) so the argument's
                            // OWN sub-arguments are type-checked recursively. Forcing
                            // infer_only=true here skipped nested arg checks, which let an
                            // ill-typed coercion buried one application deep
                            // (`g (id False True.intro)`) be accepted as a proof of False.
                            self.expr_loc_push(ExprPathStep::AppArg);
                            let arg_type = self.infer_type_fast_arc(a);
                            self.expr_loc_pop();
                            let arg_type = arg_type?;

                            // Lean 4 parity: set eager_reduce when the argument is
                            // wrapped in `eagerReduce _ _`. This forces Nat arithmetic
                            // reduction and Bool.true reflection to proceed even with
                            // free variables present during the is_def_eq call.
                            // Ref: type_checker.cpp:168-176
                            let prev_eager = self.eager_reduce.get();
                            if is_eager_reduce(a) {
                                self.eager_reduce.set(true);
                            }
                            // Cumulative subtyping (`is_le`) at this ascription
                            // point: the argument's type must be a SUBTYPE of the
                            // expected domain. `is_le` == `is_def_eq` unless the
                            // Coq cumulative lane is enabled (Prop ≤ Set ≤ Type).
                            let eq = self.is_le(&arg_type, expected_arg_type);
                            self.eager_reduce.set(prev_eager);

                            if !eq {
                                // If heartbeat was exhausted during is_def_eq, the
                                // false result is not a real type mismatch — report
                                // HeartbeatExceeded instead of a misleading error
                                // with identical expected/inferred types. Part of #3134.
                                self.tick_heartbeat()?;
                                return Err(TypeError::TypeMismatch {
                                    expected: Box::new(expected_arg_type.as_ref().clone()),
                                    inferred: Box::new(arg_type),
                                    // At the argument, as the cert path. #3425.
                                    location: self.expr_loc_snapshot_at(ExprPathStep::AppArg),
                                });
                            }
                        }
                        #[cfg(feature = "inference-stats")]
                        work_stats::record_operation(Operation::InstantiateApp);
                        Ok(result_type.instantiate(a))
                    }
                    _ => {
                        // If heartbeat was exhausted during whnf, the type may
                        // not have reduced to a Pi — report HeartbeatExceeded
                        // instead of a misleading NotAFunction. Part of #3134.
                        self.tick_heartbeat()?;
                        #[cfg(feature = "debug-infer")]
                        eprintln!(
                            "[infer_type] NotAFunction ERROR: f = {:?}, f_type = {:?}, f_type_whnf = {:?}",
                            f, f_type, f_type_whnf
                        );
                        Err(TypeError::NotAFunction {
                            ty: Box::new(f_type),
                            location: self.expr_loc_snapshot_at(ExprPathStep::AppFn),
                        })
                    }
                }
            }
            ExprKind::Lam(bi, arg_type, body) => {
                // Lean 4 parity: when infer_only=true, skip the domain Sort
                // check. Lean 4's infer_lambda calls ensure_sort only when
                // infer_only=false (check mode). The domain type is still used
                // to extend the context, but its Sort-ness is not validated.
                // Ref: type_checker.cpp infer_lambda / ensure_sort_core
                // Part of #3223.
                if !self.infer_only.get() {
                    self.expr_loc_push(ExprPathStep::LamType);
                    let arg_sort = self.infer_type_fast_arc(arg_type);
                    self.expr_loc_pop();
                    let arg_sort = arg_sort?;
                    let arg_sort_whnf = self.whnf_impl(&arg_sort);
                    match &arg_sort_whnf.kind {
                        ExprKind::Sort(_) => {}
                        _ => {
                            return Err(TypeError::ExpectedSort {
                                ty: Box::new(arg_sort),
                                location: self.expr_loc_snapshot_at(ExprPathStep::LamType),
                            });
                        }
                    };
                }

                let fvar_id = self.ctx_push(Name::anon(), arg_type.as_ref().clone(), *bi);
                #[cfg(feature = "inference-stats")]
                work_stats::record_operation(Operation::OpenLam);
                let body_with_fvar = self.open_bvar(body, fvar_id);
                self.expr_loc_push(ExprPathStep::LamBody);
                let body_type = self.infer_type_fast_impl(&body_with_fvar);
                self.expr_loc_pop();
                // Pop BEFORE `?`: an Err must not leak the binder's FVar into
                // self.ctx (see infer_sort_inner below for the same ordering).
                self.ctx_pop();
                let body_type = body_type?;

                #[cfg(feature = "inference-stats")]
                work_stats::record_operation(Operation::AbstractLam);
                let body_type_abstract = body_type.abstract_fvar(fvar_id);
                Ok(Expr::from_kind(ExprKind::Pi(
                    *bi,
                    arg_type.clone(),
                    Arc::new(body_type_abstract),
                )))
            }
            ExprKind::Pi(bi, arg_type, body) => {
                self.expr_loc_push(ExprPathStep::PiDom);
                let arg_sort = self.infer_type_fast_arc(arg_type);
                self.expr_loc_pop();
                let arg_sort = arg_sort?;
                let arg_sort_whnf = self.whnf_impl(&arg_sort);
                let ExprKind::Sort(l1) = &arg_sort_whnf.kind else {
                    return Err(TypeError::ExpectedSort {
                        ty: Box::new(arg_sort),
                        location: self.expr_loc_snapshot_at(ExprPathStep::PiDom),
                    });
                };
                let l1 = l1.clone();

                let fvar_id = self.ctx_push(Name::anon(), arg_type.as_ref().clone(), *bi);
                #[cfg(feature = "inference-stats")]
                work_stats::record_operation(Operation::OpenPi);
                let body_with_fvar = self.open_bvar(body, fvar_id);
                self.expr_loc_push(ExprPathStep::PiBody);
                let body_sort = self.infer_type_fast_impl(&body_with_fvar);
                self.expr_loc_pop();
                // Pop BEFORE `?` so an Err leaves self.ctx unchanged.
                self.ctx_pop();
                let body_sort = body_sort?;

                let body_sort_whnf = self.whnf_impl(&body_sort);
                let ExprKind::Sort(l2) = &body_sort_whnf.kind else {
                    return Err(TypeError::ExpectedSort {
                        ty: Box::new(body_sort),
                        location: self.expr_loc_snapshot_at(ExprPathStep::PiBody),
                    });
                };
                let l2 = l2.clone();

                Ok(Expr::from_kind(ExprKind::Sort(self.level_imax(l1, l2))))
            }
            ExprKind::Let(let_name, ty, val, body, _) => {
                // Lean 4 parity: when infer_only=false, check that the type is
                // a sort and that the value has the declared type. When
                // infer_only=true, skip these checks (Lean 4's infer_let).
                // Ref: type_checker.cpp:198-221
                if !self.infer_only.get() {
                    self.expr_loc_push(ExprPathStep::LetType);
                    let ty_sort = self.infer_type_fast_arc(ty);
                    self.expr_loc_pop();
                    let ty_sort = ty_sort?;
                    let ty_sort_whnf = self.whnf_impl(&ty_sort);
                    match &ty_sort_whnf.kind {
                        ExprKind::Sort(_) => {}
                        _ => {
                            return Err(TypeError::ExpectedSort {
                                ty: Box::new(ty_sort),
                                location: self.expr_loc_snapshot_at(ExprPathStep::LetType),
                            });
                        }
                    }

                    // SOUNDNESS: infer the let value's type in the CURRENT mode
                    // (infer_only stays false in check mode) so the value's OWN nested
                    // arguments are type-checked — otherwise an ill-typed coercion in
                    // the let value (`let v:False := id False True.intro`) slips through.
                    // The is_def_eq below then confirms the value's type matches the
                    // annotation.
                    self.expr_loc_push(ExprPathStep::LetVal);
                    let val_type = self.infer_type_fast_arc(val);
                    self.expr_loc_pop();
                    let val_type = val_type?;
                    // Cumulative subtyping: the let value's type must be a subtype
                    // of the annotation. `is_le` == `is_def_eq` off the Coq lane.
                    if !self.is_le(&val_type, ty) {
                        // If heartbeat was exhausted during is_def_eq, the false
                        // result is not a real type mismatch — surface
                        // HeartbeatExceeded instead of a misleading TypeMismatch.
                        // Part of #3134 (same guard as the App-arg path).
                        self.tick_heartbeat()?;
                        return Err(TypeError::TypeMismatch {
                            expected: Box::new(ty.as_ref().clone()),
                            inferred: Box::new(val_type),
                            location: self.expr_loc_snapshot_at(ExprPathStep::LetVal),
                        });
                    }
                }

                let fvar_id =
                    self.ctx_push_let(let_name.clone(), ty.as_ref().clone(), val.as_ref().clone());
                #[cfg(feature = "inference-stats")]
                work_stats::record_operation(Operation::OpenLet);
                let body_with_fvar = self.open_bvar(body, fvar_id);
                self.expr_loc_push(ExprPathStep::LetBody);
                let body_type = self.infer_type_fast_impl(&body_with_fvar);
                self.expr_loc_pop();
                // Pop BEFORE `?` so an Err leaves self.ctx unchanged.
                self.ctx_pop();
                let body_type = body_type?;

                Ok(self.close_inferred_let_type(let_name, ty, val, body_type, fvar_id))
            }
            ExprKind::Lit(lit) => Ok(infer_literal_type(lit)),
            ExprKind::Proj(struct_name, idx, e) => {
                self.expr_loc_push(ExprPathStep::ProjExpr);
                let result = self.infer_proj_type(struct_name, *idx, e);
                self.expr_loc_pop();
                result
            }
            // MData is transparent - just infer the type of the inner expression
            ExprKind::MData(_, inner) => {
                self.expr_loc_push(ExprPathStep::MDataExpr);
                let result = self.infer_type_fast_arc(inner);
                self.expr_loc_pop();
                result
            }

            // Mode-specific extensions — delegated to infer_cubical.rs / infer_zfc.rs
            ExprKind::CubicalInterval => self.infer_cubical_interval(),
            ExprKind::CubicalI0 | ExprKind::CubicalI1 => self.infer_cubical_endpoint(),
            ExprKind::CubicalPath { ty, left, right } => self.infer_cubical_path(ty, left, right),
            ExprKind::CubicalPathLam { body } => self.infer_cubical_path_lam(body),
            ExprKind::CubicalPathApp { path, arg } => self.infer_cubical_path_app(path, arg),
            ExprKind::CubicalHComp { ty, phi, u, base } => {
                self.infer_cubical_hcomp(ty, phi, u, base)
            }
            ExprKind::CubicalTransp { ty, phi, base } => self.infer_cubical_transp(ty, phi, base),
            ExprKind::CubicalCoe { ty, r, s, base } => self.infer_cubical_coe(ty, r, s, base),
            ExprKind::ZFCSet(ref set_expr) => self.infer_zfc_set(set_expr),
            ExprKind::ZFCMem { element, set } => self.infer_zfc_mem(element, set),
            ExprKind::ZFCComprehension { domain, pred } => {
                self.infer_zfc_comprehension(domain, pred)
            }
            ExprKind::SProp => self.infer_sprop(),
            ExprKind::Squash(inner) => self.infer_squash(inner),
        }
    }

    /// Check that an expression has a given type.
    ///
    /// Unlike `infer_type()`, this performs full type checking at App and Let
    /// nodes (matching Lean 4's `check()` which passes `infer_only=false`).
    ///
    /// # Contract
    ///
    /// REQUIRES: All FVars in `e` and `expected` are defined in `self.ctx`
    /// REQUIRES: All Consts in `e` and `expected` are defined in `self.env`
    /// REQUIRES: `expected` is a well-formed type (infer_type succeeds on it)
    ///
    /// ENSURES: On success, `is_def_eq(infer_type(e), expected)` holds
    /// ENSURES: Deterministic - same inputs yield same output
    ///
    /// Lean 4 reference: `type_checker.cpp:308-311`
    /// ```text
    /// expr type_checker::check(expr const & e, names const & lps) {
    ///     return infer_type_core(e, false);  // infer_only=false
    /// }
    /// ```
    pub fn check_type(&self, e: &Expr, expected: &Expr) -> Result<(), TypeError> {
        let _metered = self.metered_scope();
        // Set infer_only=false for full checking (Lean 4's check() semantics).
        let prev = self.infer_only.get();
        self.infer_only.set(false);
        let result = self.infer_type(e);
        self.infer_only.set(prev);

        let inferred = result?;
        // Cumulative subtyping: the inferred type must be a subtype of the
        // expected type. `is_le` == `is_def_eq` unless the Coq cumulative lane is
        // enabled, so Lean-lane `check_type` is unchanged.
        if self.is_le(&inferred, expected) {
            Ok(())
        } else {
            // If heartbeat was exhausted during is_def_eq, whnf may have returned unreduced
            // terms, so the false result is a resource abort, not a real type mismatch —
            // surface HeartbeatExceeded instead of a misleading TypeMismatch. Part of #3134
            // (same guard as the App-arg path). A genuine type error with budget remaining
            // still returns TypeMismatch (tick_heartbeat is a no-op while budget remains),
            // so this never turns an ill-typed constant into a pass.
            self.tick_heartbeat()?;
            Err(TypeError::TypeMismatch {
                expected: Box::new(expected.clone()),
                inferred: Box::new(inferred),
                location: self.expr_loc_snapshot(),
            })
        }
    }

    /// Infer the type of `e` in **full check mode** (`infer_only = false`),
    /// returning the inferred type.
    ///
    /// This is the type-returning counterpart of [`Self::check_type`]: it runs
    /// the same `infer_only = false` path that Lean 4's `check()` and
    /// `Environment::add_decl` use — i.e. it validates App argument types and
    /// Lam/Pi domain sorts — but, unlike `check_type`, it does not take an
    /// `expected` type and instead surfaces the inferred type directly. A
    /// genuine type error (`NotAFunction`, `ExpectedSort`, App `TypeMismatch`,
    /// …) is returned as `Err`.
    ///
    /// Used by the model↔kernel fidelity gate (`clean-verify`
    /// `fidelity_gate`) so the always-checking micro-checker can be compared
    /// against the kernel apples-to-apples (the default `infer_type` runs the
    /// infer-only fast path, which deliberately skips those checks).
    ///
    /// # Contract
    /// REQUIRES: All FVars/Consts in `e` are defined in `self.ctx`/`self.env`.
    /// ENSURES: On `Ok(T)`, `e` type-checks (check mode) and `T` is its type.
    /// ENSURES: Deterministic — same input yields same output.
    pub fn infer_type_full(&self, e: &Expr) -> Result<Expr, TypeError> {
        let prev = self.infer_only.get();
        self.infer_only.set(false);
        let result = self.infer_type(e);
        self.infer_only.set(prev);
        result
    }

    /// Infer type and ensure it inhabits a sort-like universe, returning the
    /// corresponding universe level.
    ///
    /// Like `check_type`, this uses `infer_only=false` for full checking
    /// because it is a validation entry point used by `add_decl` and
    /// `add_inductive`. Matches Lean 4's `check()` semantics.
    ///
    /// `SProp` is treated as living at level zero for callers like
    /// `Environment::add_decl`, which need to validate proposition-like
    /// declaration types such as `Squash(Prop)`.
    pub fn infer_sort(&self, e: &Expr) -> Result<Level, TypeError> {
        let _metered = self.metered_scope();
        // Set infer_only=false for full checking (validation entry point).
        let prev = self.infer_only.get();
        self.infer_only.set(false);
        let result = stack_safe(|| self.infer_sort_inner(e, 0));
        self.infer_only.set(prev);
        result
    }

    /// Maximum recursion depth for `infer_sort_inner`'s Pi fallback.
    ///
    /// When `infer_type(e)` returns a Pi type (meaning `e` is a term with a function type),
    /// `infer_sort_inner` recursively processes the Pi domain and body to compute the sort
    /// level. This depth limit prevents runaway recursion on pathological or cyclic types.
    ///
    /// 64 is sufficient for all known nn_verify types (deepest observed: ~8
    /// levels for `compose_lipschitz` with higher-order function parameters).
    /// Part of #3304.
    const INFER_SORT_MAX_DEPTH: u32 = 64;

    /// Inner implementation of `infer_sort`, wrapped by `stack_safe` for stack
    /// overflow protection on deeply nested Pi types.
    ///
    /// The `depth` parameter bounds the Pi-unwinding recursion to prevent
    /// unbounded recursion on pathological types. When `infer_type(e)` returns
    /// a Pi, `infer_sort_inner` recursively extracts domain and body levels.
    /// For well-typed expressions this always terminates (each `infer_type`
    /// call reduces structural complexity), but the depth limit provides a
    /// clean error instead of heartbeat exhaustion. Part of #3304.
    fn infer_sort_inner(&self, e: &Expr, depth: u32) -> Result<Level, TypeError> {
        // Note: no tick_heartbeat() here — infer_type already decrements the heartbeat
        // counter. Adding a tick here would double-count and could exhaust the heartbeat
        // budget prematurely for complex types with many Pi domains (e.g., nn_verify
        // theorems). Part of #3304.
        let ty = self.infer_type(e)?;
        let ty_whnf = self.whnf(&ty);
        match &ty_whnf.kind {
            ExprKind::Sort(l) => Ok(l.clone()),
            ExprKind::SProp => Ok(Level::zero()),
            ExprKind::Pi(bd, arg_type, body) => {
                if depth >= Self::INFER_SORT_MAX_DEPTH {
                    // SOUNDNESS: if Pi-nesting exceeds the depth cap we CANNOT
                    // safely determine the universe. Returning Sort(0) (the old
                    // behavior) is unsound — it under-reports a potentially large
                    // universe as Prop, defeating the theorem-is-Prop gate and the
                    // per-field universe-consistency check (a Girard-paradox
                    // enabler). Hard-error instead. No legitimate type nests this
                    // deep; if one ever does, raise the cap rather than collapse.
                    return Err(TypeError::SortDepthExceeded { depth });
                }
                let arg_level = stack_safe(|| self.infer_sort_inner(arg_type, depth + 1))?;
                let fvar_id = self.ctx_push(Name::anon(), arg_type.as_ref().clone(), *bd);
                let body_with_fvar = self.open_bvar(body, fvar_id);
                let body_level_result =
                    stack_safe(|| self.infer_sort_inner(&body_with_fvar, depth + 1));
                self.ctx_pop();
                let body_level = body_level_result?;
                Ok(self.level_imax(arg_level, body_level))
            }
            _ => Err(TypeError::ExpectedSort {
                ty: Box::new(ty),
                location: self.expr_loc_snapshot(),
            }),
        }
    }

    /// Return the sort level of each non-parameter constructor field.
    ///
    /// Walks the Pi binders of `ctor_type`, skipping the first `num_params`
    /// (shared inductive parameters), and infers the sort of each remaining
    /// field's domain type. This matches Lean 4's per-field universe check
    /// in `check_constructors` (kernel/inductive.cpp).
    pub(crate) fn ctor_field_sort_levels(
        &self,
        ctor_type: &Expr,
        num_params: u32,
    ) -> Result<Vec<Level>, TypeError> {
        self.ctor_field_sorts_with(ctor_type, num_params, Self::infer_sort)
    }

    /// Infer-only [`Self::ctor_field_sort_levels`], as Lean's large-elimination
    /// analysis sorts fields (`ensure_type` = `infer_type_core(e, true)`). Native
    /// admission fully checks the constructor type first, so the modes agree
    /// there; an imported field's proof argument must not decide elimination.
    pub(crate) fn ctor_field_sort_levels_infer_only(
        &self,
        ctor_type: &Expr,
        num_params: u32,
    ) -> Result<Vec<Level>, TypeError> {
        self.ctor_field_sorts_with(ctor_type, num_params, |tc, e| {
            let prev = tc.infer_only.get();
            tc.infer_only.set(true);
            let result = stack_safe(|| tc.infer_sort_inner(e, 0));
            tc.infer_only.set(prev);
            result
        })
    }

    fn ctor_field_sorts_with(
        &self,
        ctor_type: &Expr,
        num_params: u32,
        sort_of: impl Fn(&Self, &Expr) -> Result<Level, TypeError>,
    ) -> Result<Vec<Level>, TypeError> {
        let mut current = ctor_type.clone();
        let mut depth = 0u32;
        let mut field_sorts = Vec::new();

        // Use break-with-value to ensure ctx_pop cleanup on all paths.
        let result = loop {
            match current.kind() {
                ExprKind::Pi(bd, domain, body) => {
                    if depth >= num_params {
                        match sort_of(self, domain) {
                            Ok(sort) => field_sorts.push(sort),
                            Err(e) => break Err(e),
                        }
                    }
                    let fvar_id = self.ctx_push(Name::anon(), domain.as_ref().clone(), *bd);
                    current = self.open_bvar(body, fvar_id);
                    depth += 1;
                }
                _ => break Ok(field_sorts),
            }
        };

        for _ in 0..depth {
            self.ctx_pop();
        }

        result
    }

    /// Validate that all `Level::Param` references in a level are in the
    /// declared `level_params` list.
    ///
    /// This is a no-op when `level_params` is `None` (the default), preserving
    /// backward compatibility for callers who don't set level params.
    ///
    /// Lean 4 reference: `type_checker.cpp:63-73` (`check_level`).
    /// Lean 4's `check_level` scans for `Level::Param` names not in `m_lparams`.
    ///
    /// Part of #3225.
    pub(super) fn check_level(&self, l: &Level) -> Result<(), TypeError> {
        let Some(ref allowed) = self.level_params else {
            return Ok(());
        };
        let mut level_stack = vec![l];
        while let Some(curr) = level_stack.pop() {
            match curr {
                Level::Zero => {}
                Level::Param(n) => {
                    if !allowed.contains(n) {
                        return Err(TypeError::UndefinedLevelParam { param: n.clone() });
                    }
                }
                Level::Succ(inner) => level_stack.push(inner),
                Level::Max(a, b) | Level::IMax(a, b) => {
                    level_stack.push(b);
                    level_stack.push(a);
                }
            }
        }
        Ok(())
    }
}
