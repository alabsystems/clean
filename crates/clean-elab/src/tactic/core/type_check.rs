// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! ProofState type checking and verification methods.
//!
//! Contains: type inference, definitional equality, WHNF, certificate
//! verification, and the TypeChecker cache.

use super::error::TacticError;
use super::{Goal, ProofState};
use crate::unify::MetaState;
use clean_kernel::cert::{CertError, CertVerifier, ProofCert};
use clean_kernel::level::Level;
use clean_kernel::name::Name;
use clean_kernel::{
    BinderInfo, EqProofBuilder, Expr, ExprKind, FVarId, LocalContext, TypeChecker, WhnfWithProof,
};

impl ProofState {
    /// Build a kernel LocalContext from a goal's local context.
    ///
    /// REQUIRES: `goal.local_ctx` contains valid local declarations.
    ///   `self.elab_locals` and `self.metas` are consistent with the current state.
    /// ENSURES: Returns a LocalContext containing all elaborator-scope locals,
    ///   goal-scope locals, and metavariable-as-FVar entries. Types are
    ///   instantiated through `self.metas`.
    pub(crate) fn build_local_ctx(&self, goal: &Goal) -> LocalContext {
        let push_decl = |ctx: &mut LocalContext, decl: &super::LocalDecl| {
            let name = Name::from_string(&decl.name);
            let ty = self.metas.instantiate(&decl.ty);
            if let Some(value) = &decl.value {
                ctx.push_let_with_id(decl.fvar, name, ty, self.metas.instantiate(value));
            } else {
                ctx.push_with_id(decl.fvar, name, ty, BinderInfo::Default);
            }
        };

        let mut ctx = LocalContext::new();
        // Add elaborator-scope locals first (#2212). These are theorem
        // parameters that exist in the enclosing ElabCtx but are not
        // tactic-created. They must be in the TypeChecker context so
        // proof terms referencing them can be type-checked.
        let mut seen = std::collections::HashSet::new();
        for decl in &self.elab_locals {
            seen.insert(decl.fvar);
            push_decl(&mut ctx, decl);
        }
        // #2529: After the bridge fix, goal.local_ctx also contains the
        // elab_locals entries. Skip duplicates by FVarId to avoid pushing
        // the same declaration twice into the kernel context.
        for decl in &goal.local_ctx {
            if seen.insert(decl.fvar) {
                push_decl(&mut ctx, decl);
            }
        }
        // Also add metavariables to context
        for (meta_id, meta) in self.metas.iter() {
            let name = Name::from_string(&format!("?m{}", meta_id.0));
            ctx.push_with_id(
                MetaState::to_fvar(meta_id),
                name,
                self.metas.instantiate(&meta.ty),
                BinderInfo::Implicit,
            );
            seen.insert(MetaState::to_fvar(meta_id));
        }

        // #38: thread sibling-subgoal binder FVars into the kernel context.
        //
        // Goal-transforming tactics (induction, cases, …) create subgoals whose
        // local contexts introduce fresh tactic binder FVars (e.g. the `succ`
        // case's `k`/`ih`). The recursor proof term abstracts those FVars in the
        // PROOF, but each subgoal's metavariable stores its TARGET type with the
        // raw binder FVar still free. When `close_goal`/`verify_tactic_proof` run
        // a strict (`infer_only=false`) check, the kernel pushes those meta types
        // into its LocalContext (above) and then compares them def-eq against the
        // recursor's expected minor-premise type — traversing an expr that
        // mentions a binder FVar which is NOT itself a context declaration. In
        // lenient (`infer_only=true`) mode that comparison is skipped, so the leak
        // is invisible; under the strict check it would otherwise reach the
        // kernel's out-of-context-FVar guard.
        //
        // The binder FVars in question are genuine, well-typed locals — they live
        // in the *sibling* subgoals' local contexts. Registering those decls makes
        // every meta type the strict check sees fully in-context, which is exactly
        // what makes the canonical induction proof type-check instead of tripping
        // the kernel guard. This is purely additive: it only ever pulls in decls
        // referenced by a meta type that are not already present.
        self.thread_sibling_ctx_fvars(&mut ctx, &mut seen);
        ctx
    }

    /// Register sibling-subgoal binder FVars referenced by metavariable types.
    ///
    /// Scans the current `ctx` for FVars that appear in already-registered
    /// declaration types but are not themselves declared, looks each one up in
    /// any goal's local context, and pushes its declaration. Repeats to a fixed
    /// point so that decls whose types reference further leaked FVars (e.g. an
    /// induction hypothesis whose type mentions the constructor field) are also
    /// brought into scope. Bounded by the total number of distinct local decls
    /// across all goals, so it always terminates.
    fn thread_sibling_ctx_fvars(
        &self,
        ctx: &mut LocalContext,
        seen: &mut std::collections::HashSet<FVarId>,
    ) {
        // Build a lookup of every local decl across all goals, keyed by FVarId.
        // Sibling subgoals hold the binder decls that leaked into meta types.
        let mut decl_index: std::collections::HashMap<FVarId, &super::LocalDecl> =
            std::collections::HashMap::new();
        for goal in &self.goals {
            for decl in &goal.local_ctx {
                decl_index.entry(decl.fvar).or_insert(decl);
            }
        }
        if decl_index.is_empty() {
            return;
        }

        // Fixed-point: repeatedly pull in any referenced-but-undeclared FVar.
        // The loop strictly grows `seen` each iteration (or stops), and is
        // bounded by `decl_index.len()`.
        let max_iters = decl_index.len() + 1;
        for _ in 0..max_iters {
            let missing: Vec<FVarId> = ctx
                .iter()
                .flat_map(|decl| crate::tactic::hypothesis::collect_fvars(&decl.type_))
                .filter(|fv| !seen.contains(fv) && decl_index.contains_key(fv))
                .collect();
            if missing.is_empty() {
                break;
            }
            let mut progressed = false;
            for fv in missing {
                if !seen.insert(fv) {
                    continue;
                }
                if let Some(decl) = decl_index.get(&fv) {
                    let name = Name::from_string(&decl.name);
                    let ty = self.metas.instantiate(&decl.ty);
                    if let Some(value) = &decl.value {
                        ctx.push_let_with_id(decl.fvar, name, ty, self.metas.instantiate(value));
                    } else {
                        ctx.push_with_id(decl.fvar, name, ty, BinderInfo::Default);
                    }
                    progressed = true;
                }
            }
            if !progressed {
                break;
            }
        }
    }

    /// Run an operation with a TypeChecker, reusing cached WHNF/def_eq/equiv
    /// state when the goal hasn't changed since the last call. The cache is
    /// keyed by `goal.meta_id`; switching goals invalidates all caches.
    ///
    /// REQUIRES: `goal` belongs to this proof state's current meta/environment context.
    /// ENSURES: `f` observes a `TypeChecker` built from `goal`'s instantiated local context.
    /// ENSURES: Cached checker state is reused only when the cache key matches `goal.meta_id`.
    /// ENSURES: Cache is updated with the post-call TypeChecker caches before returning.
    ///
    /// Part of #1671.
    fn with_tc<R>(&self, goal: &Goal, f: impl FnOnce(&TypeChecker<'_>) -> R) -> R {
        let ctx = self.build_local_ctx(goal);
        let cached = self.tc_cache.lock().expect("tc_cache poisoned").take();
        let tc = match cached {
            Some((mid, caches)) if mid == goal.meta_id => {
                TypeChecker::with_context_and_caches(&self.env, ctx, caches)
            }
            _ => TypeChecker::with_context(&self.env, ctx),
        };
        let result = f(&tc);
        *self.tc_cache.lock().expect("tc_cache poisoned") = Some((goal.meta_id, tc.take_caches()));
        result
    }

    /// Invalidate the TypeChecker cache (call after context-mutating tactics).
    ///
    /// ENSURES: Subsequent `with_tc` calls rebuild a fresh TypeChecker instead of reusing caches.
    ///
    /// Part of #1671.
    pub(crate) fn invalidate_tc_cache(&self) {
        *self.tc_cache.lock().expect("tc_cache poisoned") = None;
    }

    #[cfg(test)]
    pub(crate) fn has_tc_cache_for_test(&self) -> bool {
        self.tc_cache.lock().expect("tc_cache poisoned").is_some()
    }

    /// Strict (`infer_only=false`) typecheck of `expr` against `expected`
    /// within the goal's local context.
    ///
    /// Wave 98 (Gap 17): the default `infer_type` runs in
    /// `infer_only=true` mode, which skips App-argument and Let-body
    /// type checks. For validation entry points that must reject
    /// ill-typed rewrites (e.g. `validate_rewritten_goal`), this
    /// stricter variant routes through the kernel's `check_type` so
    /// argument-vs-domain mismatches are caught.
    ///
    /// REQUIRES: `expr` and `expected` are well-formed in `goal.local_ctx`.
    /// ENSURES: On Ok, the kernel accepts `expr : expected`.
    /// ENSURES: On Err(TypeCheckFailed), the kernel rejected the term.
    pub fn check_type_strict(
        &self,
        goal: &Goal,
        expr: &Expr,
        expected: &Expr,
    ) -> Result<(), TacticError> {
        let inst_expr = self.metas.instantiate(expr);
        let inst_expected = self.metas.instantiate(expected);
        self.with_tc(goal, |tc| {
            tc.check_type(&inst_expr, &inst_expected)
                .map_err(|e| TacticError::TypeCheckFailed(format!("{e:?}")))
        })
    }

    /// Strict (`infer_only=false`) type inference in the goal's context.
    ///
    /// Routes through the kernel's `infer_type_full`, which runs the same
    /// `infer_only=false` path that `Environment::add_decl` uses — validating
    /// App-argument types and Lam/Pi domain sorts. The default `infer_type`
    /// runs `infer_only=true`, which SKIPS those checks, so it accepts proof
    /// terms that `add_decl` would later reject (an ill-typed `Eq.trans`
    /// application, for example). `close_goal` and `verify_tactic_proof` use
    /// this variant so the tactic layer rejects exactly what the kernel
    /// rejects. Part of #38.
    ///
    /// REQUIRES: `expr` is a well-formed expression in the goal's local context.
    /// ENSURES: On Ok, returns the inferred type with metavariables instantiated,
    ///   and the kernel accepted `expr` in full-check mode.
    /// ENSURES: On Err(TypeCheckFailed), the kernel rejected the term under
    ///   full checking (App-arg mismatch, bad domain sort, …).
    pub fn infer_type_strict(&self, goal: &Goal, expr: &Expr) -> Result<Expr, TacticError> {
        let instantiated = self.metas.instantiate(expr);
        let is_lambda = matches!(instantiated.kind(), ExprKind::Lam(..));
        self.with_tc(goal, |tc| {
            let ty = tc
                .infer_type_full(&instantiated)
                .map_err(|e| TacticError::TypeCheckFailed(format!("{e:?}")))?;
            let ty = self.metas.instantiate(&ty);
            if is_lambda {
                self.fix_pi_leaked_fvars(goal, &ty)
            } else {
                Ok(ty)
            }
        })
    }

    /// Infer the type of an expression in the goal's context.
    ///
    /// REQUIRES: `expr` is a well-formed expression in the goal's local context.
    /// ENSURES: On Ok, returns the inferred type with metavariables instantiated.
    ///   For Lambda expressions, applies `fix_pi_leaked_fvars` to abstract
    ///   leaked tactic-context FVars back to BVars in the resulting Pi type.
    pub fn infer_type(&self, goal: &Goal, expr: &Expr) -> Result<Expr, TacticError> {
        let instantiated = self.metas.instantiate(expr);
        let is_lambda = matches!(instantiated.kind(), ExprKind::Lam(..));
        self.with_tc(goal, |tc| {
            let ty = tc
                .infer_type(&instantiated)
                .map_err(|e| TacticError::TypeCheckFailed(format!("{e:?}")))?;
            let ty = self.metas.instantiate(&ty);
            if is_lambda {
                self.fix_pi_leaked_fvars(goal, &ty)
            } else {
                Ok(ty)
            }
        })
    }

    /// Fix leaked FVars in Pi types returned from Lambda type inference.
    ///
    /// When the kernel's `infer_type` processes a Lambda whose body contains
    /// unresolved meta-FVars, it returns a Pi where the body has FVars from
    /// the tactic context (the meta's creation context) instead of BVars.
    /// The kernel correctly abstracts its OWN binder FVar, but the meta's
    /// type references a DIFFERENT FVar (the tactic's binder FVar), which
    /// leaks through.
    ///
    /// This post-processing step detects FVars in the Pi body that are not
    /// in the goal's local context and not meta-FVars, and abstracts them
    /// back to BVars. This produces a well-formed Pi that matches the goal
    /// target's BVar structure.
    ///
    /// REQUIRES: `expr` is a type inferred from a Lambda by the kernel.
    ///   `goal` has a valid local context covering all non-leaked FVars.
    /// ENSURES: On Ok, the returned Expr has no FVars from tactic-context
    ///   binders; leaked FVars are abstracted back to BVars with correct
    ///   de Bruijn indices. Non-Pi expressions pass through unchanged.
    ///   On Err, all leaked FVars appear in the Pi domain (dependent type
    ///   disambiguation failure) — reports error instead of silently leaking.
    ///
    /// Part of #2197.
    pub(crate) fn fix_pi_leaked_fvars(
        &self,
        goal: &Goal,
        expr: &Expr,
    ) -> Result<Expr, TacticError> {
        let ExprKind::Pi(bi, domain, body) = expr.kind() else {
            return Ok(expr.clone());
        };

        // Collect FVars in the body (operate on the ORIGINAL body, not a
        // recursively-fixed version). abstract_fvar traverses the full
        // expression tree with correct de Bruijn depth tracking, so
        // occurrences at any nesting depth get the correct BVar index.
        //
        // The previous inside-out approach (recurse into inner Pis first,
        // then abstract at outer level) corrupted de Bruijn indices: inner
        // recursion created BVar(0) at the inner level, and the outer
        // abstract_fvar didn't lift those BVars, producing e.g.
        // Pi(BVar(0), BVar(0)) instead of Pi(BVar(0), BVar(1)).
        let body_fvars = crate::tactic::hypothesis::collect_fvars(body);

        // Find leaked FVars: not in goal context, not in elaborator locals,
        // and not meta-FVars. These are tactic-context binder FVars that
        // should have been abstracted.
        let leaked: Vec<FVarId> = body_fvars
            .into_iter()
            .filter(|fv| {
                !goal.local_ctx.iter().any(|d| d.fvar == *fv)
                    && !self.elab_locals.iter().any(|d| d.fvar == *fv)
                    && MetaState::from_fvar(*fv).is_none()
            })
            .collect();

        if leaked.is_empty() {
            return Ok(expr.clone());
        }

        if leaked.len() == 1 {
            // Common case (single binder): abstract the one leaked FVar
            let body_abstracted = body.abstract_fvar(leaked[0]);
            return Ok(Expr::pi(*bi, domain.as_ref().clone(), body_abstracted));
        }

        // Multiple leaked FVars (nested binders): abstract the one NOT in
        // the Pi's domain, since the binder FVar can't appear in its own
        // domain (it's not yet in scope there).
        let domain_fvars = crate::tactic::hypothesis::collect_fvars(domain);
        if let Some(&fv) = leaked.iter().find(|fv| !domain_fvars.contains(*fv)) {
            let body_abstracted = body.abstract_fvar(fv);
            return Ok(Expr::pi(*bi, domain.as_ref().clone(), body_abstracted));
        }

        // Error: cannot determine which FVar to abstract. All leaked FVars
        // appear in the domain (dependent types where disambiguation fails).
        // Report the failure instead of silently returning a Pi with leaked
        // FVars, which causes confusing downstream TypeMismatch errors (#2227).
        Err(TacticError::TypeCheckFailed(format!(
            "fix_pi_leaked_fvars: {} leaked FVars in Pi body all appear in \
             domain — cannot disambiguate binder variable",
            leaked.len()
        )))
    }

    /// Check if two expressions are definitionally equal
    ///
    /// REQUIRES: `a` and `b` are meaningful in `goal`'s local context.
    /// ENSURES: Returns `true` iff the instantiated expressions are definitionally equal under the kernel checker.
    pub fn is_def_eq(&self, goal: &Goal, a: &Expr, b: &Expr) -> bool {
        let a_inst = self.metas.instantiate(a);
        let b_inst = self.metas.instantiate(b);
        self.with_tc(goal, |tc| tc.is_def_eq(&a_inst, &b_inst))
    }

    /// Check definitional equality at `withReducible` transparency (B15).
    ///
    /// Like [`ProofState::is_def_eq`] but the def-eq/WHNF path unfolds ONLY
    /// `@[reducible]` (abbreviation) constants — `Regular` (semireducible),
    /// `@[irreducible]`, and theorem heads stay folded. This is the transparency
    /// `simp` uses to decide whether a reflexivity goal `a = b` closes: a bare
    /// `def f := e` (semireducible) is opaque, so `f = e := by simp` does NOT
    /// close via the reflexivity closer (Lean: "simp made no progress"), while a
    /// genuinely reducible or already-simplified goal (`5 = 5`, `id 5 = 5`) still
    /// closes.
    ///
    /// A fresh TypeChecker is built (transparency=Reducible, honor on) rather
    /// than reusing the cached full-transparency checker, so this never pollutes
    /// the `with_tc` cache with a reducible verdict.
    ///
    /// ENSURES: `true` implies the standard (full-transparency) `is_def_eq`
    /// would also hold — a reducible-def-eq is a strict subset, so any proof it
    /// green-lights is still kernel-accepted at `close_goal`.
    pub fn is_def_eq_reducible(&self, goal: &Goal, a: &Expr, b: &Expr) -> bool {
        let a_inst = self.metas.instantiate(a);
        let b_inst = self.metas.instantiate(b);
        let ctx = self.build_local_ctx(goal);
        let mut tc = TypeChecker::with_context(&self.env, ctx);
        tc.set_transparency(clean_kernel::TransparencyMode::Reducible);
        tc.set_honor_reducibility(true);
        tc.is_def_eq(&a_inst, &b_inst)
    }

    /// Compute weak-head normal form
    ///
    /// REQUIRES: `expr` is well-formed in `goal`'s local context.
    /// ENSURES: Returns the WHNF of `expr` after metavariable instantiation.
    pub fn whnf(&self, goal: &Goal, expr: &Expr) -> Expr {
        self.with_tc(goal, |tc| tc.whnf(&self.metas.instantiate(expr)))
    }

    /// Normalize `expr` toward a spine normal form: weak-head reduce, then
    /// recursively normalize the function and argument of each application.
    ///
    /// Best-effort and bounded to a fixed recursion depth; subterms under binders
    /// are left in WHNF. This reduces argument-position redexes (the common case
    /// for a `reduce` tactic / `conv => reduce`) on top of the head reduction
    /// `whnf` already performs. The result is definitionally equal to `expr` by
    /// construction, so any caller that installs it via `replace_target_def_eq`
    /// is re-checked by the kernel — a bug here fails a tactic, never unsound.
    pub fn normalize(&self, goal: &Goal, expr: &Expr) -> Expr {
        // 256 levels comfortably covers realistic application spines while keeping
        // recursion depth bounded (no stack-overflow risk).
        self.normalize_depth(goal, expr, 256)
    }

    fn normalize_depth(&self, goal: &Goal, expr: &Expr, depth: usize) -> Expr {
        let e = self.whnf(goal, expr);
        if depth == 0 {
            return e;
        }
        if let ExprKind::App(f, a) = e.kind() {
            let nf = self.normalize_depth(goal, f, depth - 1);
            let na = self.normalize_depth(goal, a, depth - 1);
            Expr::app(nf, na)
        } else {
            e
        }
    }

    /// Try one kernel native-reduction step for `expr`.
    ///
    /// This uses the type checker's registered native reducer hook in the
    /// current goal context after metavariable instantiation.
    pub(crate) fn try_reduce_native(&self, goal: &Goal, expr: &Expr) -> Option<Expr> {
        let instantiated = self.metas.instantiate(expr);
        self.with_tc(goal, |tc| tc.try_reduce_native(&instantiated))
    }

    /// Compute WHNF with a proof term witnessing the reduction.
    ///
    /// Returns a `WhnfWithProof` containing the reduced expression and an
    /// optional proof of type `@Eq type_ expr result`.
    ///
    /// REQUIRES: `type_` is the type of `expr` in `goal`'s local context.
    /// REQUIRES: `u` is the universe level of `type_`.
    /// ENSURES: `result.result` is the WHNF of the instantiated `expr`.
    /// ENSURES: `result.proof`, when present, witnesses `@Eq type_ expr result.result`.
    ///
    /// Part of #685.
    pub fn whnf_with_proof(
        &self,
        goal: &Goal,
        expr: &Expr,
        type_: &Expr,
        u: Level,
    ) -> WhnfWithProof {
        let instantiated = self.metas.instantiate(expr);
        let type_inst = self.metas.instantiate(type_);
        self.with_tc(goal, |tc| tc.whnf_with_proof(&instantiated, &type_inst, u))
    }

    /// Prove `@Eq α a b` by reducing both sides to a common WHNF.
    ///
    /// Strategy:
    /// 1. Reduce `a` to `a'` with proof `ha : @Eq α a a'`
    /// 2. Reduce `b` to `b'` with proof `hb : @Eq α b b'`
    /// 3. If `a' == b'` (definitionally equal), construct:
    ///    `Eq.trans ha (Eq.symm hb) : @Eq α a b`
    ///
    /// REQUIRES: `alpha` is the type of both `lhs` and `rhs`. `u` is the
    ///   universe level of `alpha`. `goal` provides the local context.
    /// ENSURES: Returns Some(proof) where proof : `@Eq alpha lhs rhs` if
    ///   both sides reduce to a common WHNF. Returns None if they do not.
    ///   The proof is constructed via Eq.trans/Eq.symm/Eq.refl depending
    ///   on which sides needed reduction.
    ///
    /// Part of #685.
    pub fn prove_eq_by_reduction(
        &self,
        goal: &Goal,
        alpha: &Expr,
        lhs: &Expr,
        rhs: &Expr,
        u: Level,
    ) -> Option<Expr> {
        let lhs_result = self.whnf_with_proof(goal, lhs, alpha, u.clone());
        let rhs_result = self.whnf_with_proof(goal, rhs, alpha, u.clone());

        // Check if the reduced forms are definitionally equal
        if !self.is_def_eq(goal, &lhs_result.result, &rhs_result.result) {
            return None;
        }

        let alpha_inst = self.metas.instantiate(alpha);
        let lhs_inst = self.metas.instantiate(lhs);
        let rhs_inst = self.metas.instantiate(rhs);

        match (&lhs_result.proof, &rhs_result.proof) {
            // Both sides reduced: Eq.trans ha (Eq.symm hb)
            (Some(ha), Some(hb)) => {
                let hb_symm = EqProofBuilder::mk_eq_symm(
                    u.clone(),
                    alpha_inst.clone(),
                    rhs_inst,
                    rhs_result.result.clone(),
                    hb.clone(),
                );
                Some(EqProofBuilder::mk_eq_trans(
                    u,
                    alpha_inst,
                    lhs_inst,
                    lhs_result.result,
                    rhs_result.result,
                    ha.clone(),
                    hb_symm,
                ))
            }
            // Only lhs reduced, rhs is already the normal form: ha directly
            // (a reduces to b, so ha : @Eq α a a' and a' def= b)
            (Some(ha), None) => Some(ha.clone()),
            // Only rhs reduced: Eq.symm hb (b reduces to a)
            (None, Some(hb)) => Some(EqProofBuilder::mk_eq_symm(
                u,
                alpha_inst,
                rhs_inst,
                rhs_result.result,
                hb.clone(),
            )),
            // Neither reduced but they're def-eq: plain Eq.refl
            (None, None) => Some(EqProofBuilder::mk_eq_refl(u, alpha_inst, lhs_inst)),
        }
    }

    /// Create a certificate verifier with the goal's local context pre-registered.
    ///
    /// This enables verification of proof terms that contain free variables
    /// from the goal's hypotheses. The verifier is initialized with all locals
    /// and metavariables from the goal context.
    ///
    /// REQUIRES: `goal`'s local context is valid for the current environment.
    /// ENSURES: On Ok, the verifier has all goal locals and meta-as-fvar entries registered.
    /// ENSURES: On Err, no partially initialized verifier escapes this function.
    pub fn create_cert_verifier(&self, goal: &Goal) -> Result<CertVerifier<'_>, CertError> {
        let ctx = self.build_local_ctx(goal);
        let mut verifier = CertVerifier::with_mode(&self.env, self.env.mode());
        verifier.register_local_context(&ctx)?;
        Ok(verifier)
    }

    /// Infer the type of an expression with a proof certificate.
    ///
    /// This is the certified variant of `infer_type` - it returns both the
    /// inferred type and a proof certificate that can be independently verified.
    ///
    /// REQUIRES: `expr` is a well-formed expression in `goal`'s local context.
    /// ENSURES: On Ok, returns the inferred type after metavariable instantiation.
    /// ENSURES: On Ok, the certificate can be checked by a verifier built with `create_cert_verifier(goal)`.
    /// ENSURES: Applies the same leaked-FVar Pi fix as `infer_type` for lambda expressions.
    pub fn infer_type_with_cert(
        &self,
        goal: &Goal,
        expr: &Expr,
    ) -> Result<(Expr, ProofCert), TacticError> {
        let ctx = self.build_local_ctx(goal);
        let tc = TypeChecker::with_context_and_mode(&self.env, ctx, self.env.mode());
        let instantiated = self.metas.instantiate(expr);
        let is_lambda = matches!(instantiated.kind(), ExprKind::Lam(..));
        let (ty, cert) = tc
            .infer_type_with_cert(&instantiated)
            .map_err(|e| TacticError::TypeCheckFailed(format!("{e:?}")))?;
        let ty = self.metas.instantiate(&ty);
        // Apply same FVar leak fix as infer_type (#2197)
        let ty = if is_lambda {
            self.fix_pi_leaked_fvars(goal, &ty)?
        } else {
            ty
        };
        Ok((ty, cert))
    }

    /// Verify that a proof term has the expected type using certificates.
    ///
    /// This provides a double-check that the proof term is correct by:
    /// 1. Inferring its type with a certificate
    /// 2. Checking definitional equality with the goal target
    /// 3. Verifying the certificate independently
    ///
    /// # Contract
    ///
    /// REQUIRES: `goal` has a valid target type in the current environment
    /// REQUIRES: `proof` is a well-formed expression (no dangling BVars or unresolved metas)
    /// ENSURES: On Ok, the returned `ProofCert` certifies that `proof` inhabits `goal.target`
    /// ENSURES: On Err(TypeMismatch), inferred type is not definitionally equal to `goal.target`
    /// ENSURES: On Err(TypeCheckFailed), certificate verification failed independently
    pub fn verify_proof(&self, goal: &Goal, proof: &Expr) -> Result<ProofCert, TacticError> {
        let (inferred_ty, cert) = self.infer_type_with_cert(goal, proof)?;

        // Normalize inferred type through typeclass projections (same as
        // close_goal). Part of #2150.
        let inferred_ty = self.whnf(goal, &inferred_ty);

        // Check that inferred type matches goal target
        if !self.is_def_eq(goal, &inferred_ty, &goal.target) {
            return Err(TacticError::TypeMismatch {
                expected: format!("{:?}", goal.target),
                actual: format!("{inferred_ty:?}"),
            });
        }

        // Verify the certificate
        let mut verifier = self
            .create_cert_verifier(goal)
            .map_err(|e| TacticError::TypeCheckFailed(format!("CertVerifier error: {e:?}")))?;

        let _ = verifier.verify(&cert, proof).map_err(|e| {
            TacticError::TypeCheckFailed(format!("Certificate verification failed: {e:?}"))
        })?;

        Ok(cert)
    }
}
