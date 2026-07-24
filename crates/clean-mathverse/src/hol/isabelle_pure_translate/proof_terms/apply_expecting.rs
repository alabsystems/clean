// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `impl Ctx` bidirectional (expecting-driven) recovery: `apply_thm_expecting`,
//! `translate_eq_expecting`, and the `…_dict` reflexive-discharge gate
//! `dict_sides_registered`. Split out of the original `proof_terms` module
//! verbatim.

use super::super::super::isabelle_pure::{IsaProof, IsaTerm, IsaType};
use super::super::*;
use super::*;
use clean_kernel::expr::FVarId;
use clean_kernel::level::Level;
use clean_kernel::Expr;
use std::collections::BTreeMap;

/// Node cap on `expected` for the stage-3 Miller predicate solve
/// ([`Ctx::redex_premise_solve`]). The genuine `subst`-family discharge-chain
/// legs abstract a tiny leg conclusion (a single equation); a much larger
/// conclusion makes the solved `?P ↦ λz. expected[…]` a leg β-redex that is
/// pathologically expensive to kernel-reduce inside the root, so the solve
/// declines above this and falls back to the pre-stage-3 path. Generous enough
/// to cover every real discharge-chain conclusion, small enough to cut the rare
/// large-proposition root that blew up the reject tail.
const MILLER_EXPECTED_MAX_NODES: usize = 512;

/// Maximum stage-3 Miller predicate solves per root redex-lane translation (see
/// [`Ctx::redex_miller_solves`]). Generous enough for the genuine SHORT
/// discharge-chain flips (a handful of interior `subst` legs), small enough to
/// bound the pathological DEEP chain whose many-leg "almost-right" root candidate
/// is expensive for the kernel to refute.
const MILLER_MAX_SOLVES_PER_ROOT: usize = 16;

/// Node budget for the stage-4 CHEAP PRE-CHECK
/// ([`head_arity_compatible`]) that prunes an "almost-right" Miller candidate
/// before the pathologically-expensive kernel re-check. Small: a definite
/// head/arity clash surfaces within the first handful of spine nodes of the
/// predicted-vs-actual flex-premise proposition, so a shallow lockstep walk
/// catches the obvious mismatches while never touching the deep body a full
/// defeq would traverse. Over-budget positions are treated as compatible (the
/// kernel remains the arbiter).
const MILLER_PRECHECK_NODE_BUDGET: usize = 256;

impl Ctx {
    /// Embed a recorded instantiation-table OPERAND, bridging the
    /// **free-vs-schematic flavor gap** (the round-7 keying model): a
    /// derivation box spells its variables as unvarified `Free x` while the
    /// consumer's exported statement spells the SAME variable schematically
    /// (`?x.0`). An identity table entry (`(x,-1) ↦ Free x`) embedded verbatim
    /// would mint a SECOND param keyed `"x"` next to the statement's `"x.0"`,
    /// desynchronizing the operands (`expected …?x.0 got …x`). When the
    /// consumer already registered the schematic flavor, that param IS the
    /// variable the box means — use it; otherwise embed verbatim (a genuinely
    /// box-local free). The kernel re-checks the result either way.
    pub(crate) fn embed_table_operand(
        &mut self,
        tm: &IsaTerm,
        binders: &mut Vec<Binder>,
    ) -> Result<Expr, TranslateError> {
        if let IsaTerm::Free { n, .. } = tm {
            let skey = format!("{n}.0");
            if let Some((_, p)) = self.term_params.iter().find(|(k, _)| *k == skey) {
                return Ok(Expr::fvar(p.fvar));
            }
        }
        self.embed_term(tm, binders)
    }

    /// The registered type of a discovered param FVar (type / term / hypothesis
    /// param), or `None` for any other expression. Used by
    /// [`Self::apply_thm_expecting`] to solve type sentinels from a
    /// conclusion-pinned binder value's known type.
    pub(crate) fn clean_fvar_param_ty(&self, e: &Expr) -> Option<Expr> {
        use clean_kernel::expr::ExprKind;
        let ExprKind::FVar(id) = e.kind() else {
            return None;
        };
        self.type_params
            .iter()
            .chain(self.term_params.iter())
            .chain(self.hyp_params.iter())
            .find(|(_, p)| p.fvar == *id)
            .map(|(_, p)| p.ty.clone())
    }

    /// Like [`Self::apply_thm`] but recovers the implicit instantiations the
    /// Isabelle spine omits **bidirectionally**, by unifying the theorem's
    /// conclusion against the caller's `expected` proposition. This solves two
    /// kinds of implicit argument the forward [`Self::apply_thm`] cannot:
    ///
    /// - a **leading type binder that occurs only in the conclusion** (a *phantom*
    ///   schematic type, e.g. the let-body result type of `let_weak_cong`): no
    ///   supplied term argument constrains it, so the forward path filled it with
    ///   `any_in_scope_type`, collapsing it onto an existing type and shifting the
    ///   remaining term arguments onto the wrong binders;
    /// - an **implicit term binder the spine skips** (a higher-order operation the
    ///   surrounding equation determines, e.g. the `Let` combinator), which would
    ///   otherwise consume the next spine term argument and misalign the rest.
    ///
    /// We first peel the leading type binders and ALL remaining binders into fresh
    /// sentinels and unify the resulting bare conclusion against `expected` (a
    /// *pre-solution* pinning the conclusion-determined sentinels). Then we walk the
    /// telescope binder by binder, threading the spine: a binder is **explicit**
    /// (consumes the next matching spine argument) when its domain structurally
    /// matches that argument; otherwise it is **implicit** and filled from the
    /// pre-solution. When any otherwise-unfilled binder is left unsolved we fall
    /// back to the forward [`Self::apply_thm`], so this method never loses a case
    /// the forward path handled — it only adds the conclusion-driven recoveries.
    /// The kernel re-checks the result against `expected`, so a wrong recovery is
    /// rejected, never miscounted.
    pub(crate) fn apply_thm_expecting(
        &mut self,
        entry: &ClosureEntry,
        spine: &[SpineArg],
        expected: &Expr,
        closure: &Closure,
        binders: &mut Vec<Binder>,
    ) -> Result<Expr, TranslateError> {
        self.apply_thm_expecting_with_tables(entry, spine, expected, &[], closure, binders)
    }

    /// [`Self::apply_thm_expecting`] with the reference's recorded (generic)
    /// `tminst` table threaded as a LAST-RESORT fill source: a term binder that
    /// is neither conclusion-pinned, nor spine-matched, nor a `const:` op can
    /// still be pinned by its recorded IDENTITY table entry (`?x ↦ x` /
    /// `Free x ↦ itself`), which embeds to the consumer's own shared param —
    /// exact for the statement-shared box-internal frees (the round-7 keying
    /// model), and kernel-re-checked either way. Genuine (non-identity)
    /// instantiations never reach here (the caller routes those through
    /// [`Self::apply_thm_explicit`]).
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn apply_thm_expecting_with_tables(
        &mut self,
        entry: &ClosureEntry,
        spine: &[SpineArg],
        expected: &Expr,
        tminst: &[super::super::super::isabelle_pure::IsaTermInst],
        closure: &Closure,
        binders: &mut Vec<Binder>,
    ) -> Result<Expr, TranslateError> {
        match self
            .apply_thm_expecting_solved(entry, spine, expected, tminst, None, closure, binders)?
        {
            Some(e) => Ok(e),
            // A binder the expectation could not reconcile — defer to the
            // forward reconstruction, byte-identical to the historical inline
            // fallback this wrapper preserves.
            None => self.apply_thm(entry, spine, closure, binders),
        }
    }

    /// **Stage-3 premise-driven + Miller-pattern interior operand solve** for a
    /// `subst`/`ssubst`-family leg whose bare conclusion is FLEX-headed
    /// (`?P ?t …`). Isolated to the `bidir_redex` proof-β-redex sub-lane (the
    /// caller gates on `self.bidir_redex` + a flex-headed conclusion), so the
    /// stage-1 eq-tower gains stay byte-identical. Fills `presolution` in two
    /// passes and returns whether the flex predicate head was pinned (the caller
    /// declines the whole solved path — falling back to `apply_thm_explicit`
    /// exactly as the pre-stage-3 path did — when it was not):
    ///
    /// 1. **Premise-driven first-order.** Each proof-consuming premise binder
    ///    (those PAST the recorded term/op keys) consumes one proof spine
    ///    argument in order; unify its RIGID domain against the argument's
    ///    inferred proposition ([`Self::infer_proof_prop`]) to pin the
    ///    first-order operands — for `subst` the premise `?t = ?s` against
    ///    `PBound : (P = True)` pins `?t ↦ P`, `?s ↦ True`. A FLEX-headed premise
    ///    domain (`?P ?s`) is SKIPPED — first-order descent would mis-split the
    ///    predicate sentinel; the conclusion Miller solve owns it.
    /// 2. **Conclusion Miller-pattern.** With the first-order operands
    ///    substituted, the conclusion `?P ?t` becomes `?P x` with `x` a distinct
    ///    bound variable (`?t ↦ P`); the unique Miller solution
    ///    `?P ↦ λz. expected[x ↦ z]` ([`abstract_loose_bvar`]) is recorded. Only
    ///    the single-argument (`subst` predicate) fragment is solved; anything
    ///    outside it declines.
    ///
    /// The kernel re-checks the assembled application against `expected`, so a
    /// wrong HO solve is rejected — never miscounted.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn redex_premise_solve(
        &mut self,
        entry: &ClosureEntry,
        spine: &[SpineArg],
        expected: &Expr,
        binder_sentinels: &[FVarId],
        binder_doms: &[Expr],
        concl: &Expr,
        all_sentinels: &[FVarId],
        binders: &mut Vec<Binder>,
        presolution: &mut BTreeMap<FVarId, Expr>,
    ) -> Result<bool, TranslateError> {
        use clean_kernel::expr::ExprKind;
        use std::sync::atomic::Ordering::Relaxed;
        // --- 1. Premise-driven first-order solve. Along the way, record each
        // FLEX-headed premise's (post-presolution) operand list and the actual
        // proposition its supplied proof establishes — the cheap stage-4
        // pre-check cross-checks the Miller candidate against these.
        let proofs = proof_spine_args(spine);
        let mut pidx = 0usize;
        // (flex head, premise operand list, actual premise proposition).
        let mut flex_premises: Vec<(FVarId, Vec<Expr>, Expr)> = Vec::new();
        for (bi, _bfv) in binder_sentinels.iter().enumerate() {
            if bi < entry.term_param_keys.len() {
                // An implicit term / operation binder — never spine-supplied; its
                // value comes from a premise unification or the conclusion Miller.
                continue;
            }
            let Some(pr) = proofs.get(pidx) else { break };
            pidx += 1;
            let mut dom = binder_doms[bi].clone();
            for (fv, sol) in presolution.iter() {
                dom = dom.subst_fvar(*fv, sol);
            }
            // A flex-headed premise (`?P ?s`) is left for the conclusion Miller
            // solve — first-order descent here would mis-solve the predicate.
            if let Some((fh, fargs)) = app_head_sentinel(&dom, all_sentinels) {
                // Record it for the pre-check (best-effort: skip if the proof's
                // proposition is not statically derivable here).
                if let Some(actual) = self.infer_proof_prop(pr, binders)? {
                    flex_premises.push((fh, fargs, actual));
                }
                continue;
            }
            let Some(actual) = self.infer_proof_prop(pr, binders)? else {
                continue;
            };
            unify_sentinels(&dom, &actual, all_sentinels, presolution);
        }

        // --- 2. Conclusion Miller-pattern solve for the flex predicate head.
        let mut concl_s = concl.clone();
        for (fv, sol) in presolution.iter() {
            concl_s = concl_s.subst_fvar(*fv, sol);
        }
        let Some((head_fv, args)) = app_head_sentinel(&concl_s, all_sentinels) else {
            // No flex head remaining — the premise pass already pinned it (or the
            // caller mis-detected); treat as solved so the historical presolve
            // proceeds.
            return Ok(true);
        };
        if presolution.contains_key(&head_fv) {
            return Ok(true);
        }
        // Miller fragment: the predicate is applied to `n ∈ {1, 2}` arguments —
        // the single-`subst` predicate (`?P ?t`, stage 3) or the DOMINANT
        // two-argument shape (`?P a b`, stage 4; 446 measured legs vs 151 at
        // `n=1`). Decline `n = 0` or `n > 2`.
        let n = args.len();
        if n == 0 || n > 2 {
            return Ok(false);
        }
        // Each operand must be a DISTINCT pinned LEAF variable/param (a genuine
        // Miller pattern `?P a₀ … a_{n-1}` needs distinct arguments); a non-leaf
        // operand (`App`/`Lam`) is genuine higher-order beyond Miller — decline.
        let mut targets: Vec<AbsTarget> = Vec::with_capacity(n);
        for a in &args {
            match a.kind() {
                ExprKind::BVar(i) => targets.push(AbsTarget::Bvar(*i)),
                ExprKind::FVar(id) => targets.push(AbsTarget::Fvar(*id)),
                _ => return Ok(false),
            }
        }
        if targets
            .iter()
            .enumerate()
            .any(|(i, t)| targets[i + 1..].contains(t))
        {
            // Non-distinct operands (`?P a a`): the abstraction is ambiguous —
            // decline (the kernel would need genuine higher-order unification).
            return Ok(false);
        }
        // Bound the solved predicate's size: `?P ↦ λz̄. expected[ā↦z̄]` embeds a
        // COPY of `expected`, and a large one produces a leg β-redex nested in the
        // root proof that is pathologically expensive for the kernel to reduce (a
        // single such root measured at 60+ CPU-minutes). The genuine discharge-chain
        // legs abstract a tiny equation (`P = Q`), so cap `expected` and decline the
        // rare large-conclusion root, which then falls back to the pre-stage path
        // byte-identically — strictly additive.
        if !expr_within_size(expected, MILLER_EXPECTED_MAX_NODES) {
            return Ok(false);
        }
        // The abstracted variables' types are the first `n` DOMAINS of `?P`'s
        // (curried) function type.
        let Some(hbi) = binder_sentinels.iter().position(|f| *f == head_fv) else {
            return Ok(false);
        };
        let mut pty = binder_doms[hbi].clone();
        for (fv, sol) in presolution.iter() {
            pty = pty.subst_fvar(*fv, sol);
        }
        let mut doms: Vec<Expr> = Vec::with_capacity(n);
        let mut arrow = pty;
        for _ in 0..n {
            let Some((tau, rest)) = split_arrow(&arrow) else {
                return Ok(false);
            };
            doms.push(tau);
            arrow = rest;
        }

        // We now have a genuine Miller candidate shape; count it, then run the
        // CHEAP PRE-CHECK before the pathologically-expensive kernel re-check.
        MILLER_CANDIDATES.fetch_add(1, Relaxed);

        // **Cheap structural pre-check.** For every recorded flex premise sharing
        // this predicate head and arity, the candidate predicts
        // `?P b̄ = expected[ā ↦ b̄]` (β-reduction of `?P` applied to the premise's
        // operands `b̄`, computed here by positional substitution of the
        // conclusion operands `ā` — all FVar leaves — by the premise operands
        // without building the λ). A DEFINITE head/arity clash against the actual
        // premise proposition means the candidate is obviously wrong; decline it
        // now (a `head_arity_compatible` false), sparing the kernel the expensive
        // full-defeq refute. Conservative: it never rejects a merely-definitionally
        // different prediction, and declining reproduces the Miller-OFF baseline
        // for this leg, so it is 0-lost by construction.
        for (fh, fargs, actual) in &flex_premises {
            if *fh != head_fv || fargs.len() != n {
                continue;
            }
            let mut pred = expected.clone();
            let mut checkable = true;
            for (ca, fa) in args.iter().zip(fargs.iter()) {
                match ca.kind() {
                    ExprKind::FVar(id) => pred = pred.subst_fvar(*id, fa),
                    // A bvar conclusion operand is not statically substitutable
                    // here — skip the pre-check for this premise (measured: never
                    // occurs on the real population).
                    _ => {
                        checkable = false;
                        break;
                    }
                }
            }
            if !checkable {
                continue;
            }
            let mut budget = MILLER_PRECHECK_NODE_BUDGET;
            if !head_arity_compatible(&pred, actual, &mut budget) {
                MILLER_PRECHECK_REJECTS.fetch_add(1, Relaxed);
                return Ok(false);
            }
        }

        // Per-root Miller-solve cap: a DEEP discharge chain (many interior `subst`
        // legs) yields at most `MILLER_MAX_SOLVES_PER_ROOT` Miller-solved legs;
        // beyond that, decline so the root's remaining legs take the phantom-param
        // path, which the kernel type-errors EARLY — bounding the "almost-right
        // many-leg root" candidate that is pathologically expensive to reduce. The
        // genuine short discharge-chain flips need far fewer solves, so they are
        // untouched. Strictly additive: declining falls back to the pre-stage
        // path exactly as before.
        if self.redex_miller_solves >= MILLER_MAX_SOLVES_PER_ROOT {
            return Ok(false);
        }

        // **Miller solution `?P ↦ λz̄. expected[ā ↦ z̄]`.** The `n` operands are
        // distinct BOUND variables (strict Miller) or statement-schematic CTX
        // PARAMS (`FVar` — the Isabelle statement embeds each schematic `?x` as a
        // quantified ctx param, [`Ctx::term_param`]; measured: the whole
        // discharge-chain population). For `n = 1` keep the byte-identical stage-3
        // single-target abstraction; for `n = 2` abstract over BOTH pinned
        // operands simultaneously ([`abstract_loose_multi`]). FAITHFUL by
        // construction and by re-check: the abstracted operands are exactly the
        // args the flex head is applied to (never a param picked arbitrarily), and
        // the assembled application β-reduces `(λz̄. expected[ā↦z̄]) ā` back to
        // `expected`, which the kernel re-checks against the STORED statement — a
        // wrong solve is rejected, never miscounted (the ISA_S3_MILLER A/B 0-lost
        // diff is the empirical guard).
        let body = if n == 1 {
            match args[0].kind() {
                ExprKind::BVar(tgt) => abstract_loose_bvar(expected, *tgt, 0),
                ExprKind::FVar(fid) => abstract_loose_fvar(expected, *fid, 0),
                _ => return Ok(false),
            }
        } else {
            abstract_loose_multi(expected, &targets, 0)
        };
        let Some(body) = body else {
            return Ok(false);
        };
        self.redex_miller_solves += 1;
        // Wrap `body` in the `n` binders, OUTERMOST first: `λdoms[0]. … λdoms[n-1]. body`.
        let mut sol_p = body;
        for tau in doms.into_iter().rev() {
            sol_p = Expr::lam(clean_kernel::BinderInfo::Default, tau, sol_p);
        }
        MILLER_EMITTED.fetch_add(1, Relaxed);
        presolution.insert(head_fv, sol_p);
        Ok(true)
    }

    /// The SOLVED body of [`Self::apply_thm_expecting_with_tables`]: `Ok(None)`
    /// on the two bail points (an un-reconcilable binder / an unsolved leading
    /// type instantiation) instead of the internal forward-path fallback, so a
    /// caller that needs "fully expectation-pinned or nothing" (the
    /// binder-order round's namespace-crossed root lane,
    /// [`Ctx::try_root_sort_absp_expecting`]) can fall back to ITS OWN
    /// historical path instead of the forward reconstruction. The public
    /// wrapper above keeps every existing caller's behaviour byte-identical
    /// (`obj_isa: None` — the historical shared-opaque `const:` fill).
    ///
    /// `obj_isa: Some(fills)` (the root lane) threads the reference's leading
    /// object-type fills so an expectation-UNPINNED `const:` op binder takes
    /// the SAME flavor-aware fill the plain explicit path uses
    /// ([`Self::const_key_fill`] — re-embedding a registered constant at the
    /// use-site type under `instance_unfold`); with `None` such a binder takes
    /// the historical shared opaque param. Measured: without this, the lane's
    /// opaque fill regressed the `<c>_class.axioms` projection family (whose
    /// consumer statements spell the op in the `polyinst` flavor).
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn apply_thm_expecting_solved(
        &mut self,
        entry: &ClosureEntry,
        spine: &[SpineArg],
        expected: &Expr,
        tminst: &[super::super::super::isabelle_pure::IsaTermInst],
        obj_isa: Option<&[IsaType]>,
        closure: &Closure,
        binders: &mut Vec<Binder>,
    ) -> Result<Option<Expr>, TranslateError> {
        use clean_kernel::expr::ExprKind;
        // Index the (generic) table by both key spellings — `"{n}.{i}"` for a
        // schematic key and the plain `"n"` alias for a `-1` (free) key — the
        // same convention as [`Self::apply_thm_explicit`].
        let mut tminst_by_key: BTreeMap<String, &IsaTerm> = BTreeMap::new();
        for ti in tminst {
            tminst_by_key.insert(format!("{}.{}", ti.n, ti.i), &ti.t);
            if ti.i == -1 {
                tminst_by_key.entry(ti.n.clone()).or_insert(&ti.t);
            }
        }

        // **Speculative-solve param hygiene (F1 `equal_elim` free-var leak).**
        // The binder-threading loop below SIDE-EFFECT registers `const:` operation
        // params (and any proof-argument hyp/schematic params) into the shared ctx
        // param lists as it goes — but the solve can still DECLINE afterwards (an
        // un-reconcilable binder, or a leading TYPE sentinel the expectation never
        // pinned). A `const:` op binder minted BEFORE the sentinel-determining
        // premise carries the still-free type sentinel in its registered domain;
        // if we then decline and the caller falls back to the forward path, that
        // sentinel-typed param nonetheless persists in `ctx.term_params` and the
        // final param-abstraction loop pi-wraps its domain into the theorem
        // type+value — leaking `param_fvar(3, "thmE:<dep>:tyN")` as
        // `contains-free-var` (the F1 congruence-tower hub s280734/s280892: an
        // interior Set/Orderings congruence leg reached under the `equal_elim`
        // tower whose zproof reference omits the schematic type instantiation).
        // Snapshot the three ctx param lists at entry and restore them on EVERY
        // decline (`Ok(None)`) so a failed speculative solve leaves the shared
        // state byte-identical to entry; the successful (`Ok(Some)`) path keeps
        // its registrations (they are used by the assembled term, kernel-re-checked).
        // Gated on `bidir_tower` (the dedicated trailing escalation modes): every
        // historical mode stays byte-identical (no snapshot, no restore — the
        // declined-solve pollution is unchanged), and the fix only reshapes the
        // trailing eq-tower reconstruction where the F1 leak lives. The kernel
        // re-checks the assembled value either way, so hygiene can only turn a
        // leaking (rejecting) line cleaner — never miscount.
        let param_snap = self.bidir_tower.then(|| {
            (
                self.term_params.clone(),
                self.type_params.clone(),
                self.hyp_params.clone(),
            )
        });

        // --- Peel the leading object-`Type` binders into type sentinels.
        let mut type_sentinels: Vec<FVarId> = Vec::new();
        let mut tele = entry.ty.clone();
        while let ExprKind::Pi(_, dom, cod) = tele.kind() {
            if matches!(dom.kind(), ExprKind::Sort(level) if *level != Level::zero()) {
                let fv = param_fvar(
                    3,
                    &format!("thmE:{}:ty{}", entry.name, type_sentinels.len()),
                );
                type_sentinels.push(fv);
                tele = cod.instantiate(&Expr::fvar(fv));
            } else {
                break;
            }
        }

        // --- Pre-solve: peel EVERY remaining binder into a fresh sentinel, record
        // its (sentinel-parameterized) domain, and build the bare conclusion.
        // Unifying that conclusion against `expected` pins the conclusion-determined
        // sentinels (the phantom leading types and any implicit higher-order
        // operation binders the spine skips).
        let mut binder_sentinels: Vec<FVarId> = Vec::new();
        let mut binder_doms: Vec<Expr> = Vec::new();
        let mut concl = tele.clone();
        while let ExprKind::Pi(_, dom, cod) = concl.kind() {
            let fv = param_fvar(
                3,
                &format!("thmE:{}:b{}", entry.name, binder_sentinels.len()),
            );
            binder_sentinels.push(fv);
            binder_doms.push((**dom).clone());
            concl = cod.instantiate(&Expr::fvar(fv));
        }
        let mut all_sentinels: Vec<FVarId> = type_sentinels.clone();
        all_sentinels.extend(binder_sentinels.iter().copied());
        let mut presolution: BTreeMap<FVarId, Expr> = BTreeMap::new();
        // **Stage-3 higher-order (Miller-pattern) interior operand solve.** A
        // `subst`/`ssubst`-family leg's bare conclusion is FLEX-headed
        // (`?P ?t …` — an unsolved predicate sentinel applied to arguments),
        // which the strictly first-order `unify_sentinels` MIS-SPLITS (it would
        // solve `?P` to a partial application of the actual). Under the isolated
        // `bidir_redex` sub-lane only, and only for such flex-headed
        // conclusions, run the premise-driven + Miller-pattern solve
        // ([`Self::redex_premise_solve`]) FIRST — it pins the first-order
        // premise operands (`?t`/`?s`) from the proof arguments' inferred
        // propositions and Miller-solves the predicate `?P` from the conclusion
        // against `expected`. When it cannot pin the flex head, decline the
        // whole solved path (`Ok(None)`) so the caller falls back to
        // `apply_thm_explicit` EXACTLY as the pre-stage-3 (`bidir_redex == false`)
        // path did on this same shape — byte-identical fallback, so the lane is
        // strictly additive. A non-`bidir_redex` call, or a rigid-headed
        // conclusion, skips this block entirely and is byte-identical.
        if self.bidir_redex
            && s3_miller_enabled()
            && app_head_sentinel(&concl, &all_sentinels).is_some()
        {
            let solved = self.redex_premise_solve(
                entry,
                spine,
                expected,
                &binder_sentinels,
                &binder_doms,
                &concl,
                &all_sentinels,
                binders,
                &mut presolution,
            )?;
            if !solved {
                if let Some((t, ty, h)) = param_snap.as_ref() {
                    self.term_params = t.clone();
                    self.type_params = ty.clone();
                    self.hyp_params = h.clone();
                }
                return Ok(None);
            }
        }
        // Historical first-order conclusion presolve. `unify_sentinels` uses
        // `or_insert`, so it never overrides a premise-driven / Miller solution
        // above — it only fills the sentinels still unsolved. For a
        // non-`bidir_redex` (or rigid-conclusion) call `presolution` is empty
        // here, so this is byte-identical to the historical single call.
        unify_sentinels(&concl, expected, &all_sentinels, &mut presolution);

        // --- Type-sentinel pre-pass (the s110344 `contains-free-var` pin).
        // Resolve every leading TYPE sentinel from the KNOWN type of a
        // conclusion-pinned binder value, BEFORE the main loop mints any
        // `const:` operation param. The in-loop recovery below (the
        // `presolution.get(bfv)` arm at [`Self::clean_fvar_param_ty`]) already
        // does this unification — but only when its binder is REACHED, so a
        // `const:` op binder that PRECEDES the presolved binder determining the
        // object type (e.g. `class.preorder` at binder 0, whose `α` is only
        // pinned by the `less_eq` binder that follows) was minted with the
        // still-free type sentinel baked into its registered param type. That
        // sentinel-typed `const:` param then survives into the final quantified
        // Pi domain (`translate.rs`'s param-abstraction loop pi-wraps the param
        // TYPE verbatim; the local `solution` substitution only rewrites the
        // applied-arg EXPRESSIONS, never the already-registered `ctx.term_params`
        // type), leaking as `param_fvar(3, "thmE:<dep>:ty0")`.
        //
        // Hoisting the resolution makes the object type concrete before the
        // mint, so the `const:` key hashes and the param type coincide with the
        // consumer's own `'a.0`-typed occurrence. STRICTLY ADDITIVE:
        // `unify_sentinels` first-write-wins, pinning each sentinel to the exact
        // value the in-loop recovery would (only earlier); it inserts ONLY
        // type-sentinel keys (`&type_sentinels`), which are disjoint from the
        // binder-sentinel keys the threading tests read, so no binder decision
        // changes. A line whose op binders were already minted over a resolved
        // domain is unaffected, and a line that leaked here never
        // kernel-verified — so no previously-verified line is disturbed.
        if !type_sentinels.is_empty() {
            for (bi, bfv) in binder_sentinels.iter().enumerate() {
                let Some(sol) = presolution.get(bfv).cloned() else {
                    continue;
                };
                if let Some(ty) = self.clean_fvar_param_ty(&sol) {
                    unify_sentinels(&binder_doms[bi], &ty, &type_sentinels, &mut presolution);
                }
            }
        }

        // --- Thread the spine over the binders. `solution` accumulates the type
        // (and implicit-binder) instantiations; `applied_args` are the per-binder
        // argument values in telescope order. The Isabelle spine always supplies a
        // proof for every proof premise (a proof argument can never be omitted), so
        // a *proof* spine argument always fills the current binder explicitly. Only
        // a *term* binder can be implicit — the surrounding equation determines a
        // higher-order operation the spine skips — which we detect when the next
        // term argument's type does not structurally match the binder domain.
        let mut solution: BTreeMap<FVarId, Expr> = presolution.clone();
        let mut applied_args: Vec<Expr> = Vec::new();
        let mut idx = 0usize;
        let mut bailout = false;
        for (bi, bfv) in binder_sentinels.iter().enumerate() {
            // Domain with everything solved so far substituted in.
            let mut dom = binder_doms[bi].clone();
            for (fv, sol) in &solution {
                dom = dom.subst_fvar(*fv, sol);
            }
            // A binder whose recorded embedding key is `const:<n>` is an
            // **operation parameter** (a HOL constant this embedding abstracts —
            // class ops / locale predicates), NOT a schematic variable or a
            // premise: the spine never supplies it (a proof arg landing on it is
            // the classic sort-witness-into-op-slot misfill) and, when the
            // conclusion does not pin it, the consumer's own shared `const:` param
            // is the exact fill. The binder sentinels follow the type binders, so
            // sentinel `bi` corresponds to `term_param_keys[bi]` (premise binders
            // sit past the recorded keys). Stale metadata merely mis-guides a
            // fill the kernel then rejects — never miscounted.
            let const_key = entry
                .term_param_keys
                .get(bi)
                .filter(|k| k.starts_with("const:"));
            let explicit = match spine.get(idx) {
                // A proof arg fills the current binder — UNLESS the conclusion
                // unification already pinned this binder (a term/type binder the
                // expectation determines) or the binder is a RECORDED TERM
                // binder at all (`bi` within `term_param_keys` — an op param or
                // a schematic argument, never spine-supplied: a zproof generic
                // reference supplies its term binders through the (un-recorded)
                // instantiation / the shared params, never the spine, so its
                // proof args (sort witnesses, premises) must not be consumed by
                // a term binder). Premise binders sit PAST the recorded keys
                // (and a legacy entry records no keys), so they keep consuming
                // their proof args exactly as before.
                Some(SpineArg::Proof(_)) => {
                    !presolution.contains_key(bfv) && bi >= entry.term_param_keys.len()
                }
                Some(SpineArg::Term(t)) => {
                    let actual = self.infer_type(t, binders)?;
                    types_compatible(&dom, &actual, &type_sentinels)
                }
                None => false,
            };
            if explicit {
                match &spine[idx] {
                    SpineArg::Term(t) => {
                        let actual = self.infer_type(t, binders)?;
                        unify_sentinels(&dom, &actual, &type_sentinels, &mut solution);
                        applied_args.push(self.embed_term(t, binders)?);
                    }
                    SpineArg::Proof(pr) => {
                        applied_args
                            .push(self.translate_proof_expecting(pr, &dom, closure, binders)?);
                    }
                }
                idx += 1;
            } else if let Some(sol) = presolution.get(bfv).cloned() {
                // Implicit term binder: the conclusion pinned its value. When the
                // pinned value is a registered param FVar, its KNOWN type also
                // pins any type sentinels the binder domain mentions (e.g. the
                // object type `α` of a class-projection entry, which occurs in
                // the op binder domains but NOT in the conclusion — without this
                // the `all_type_solved` check below bailed to the forward path
                // and the spine premise witnesses landed on the op binders).
                if let Some(ty) = self.clean_fvar_param_ty(&sol) {
                    unify_sentinels(&binder_doms[bi], &ty, &type_sentinels, &mut solution);
                }
                applied_args.push(sol);
            } else if let Some(key) = const_key {
                // Un-presolved operation param: the consumer's shared `const:`
                // param of the same key (see [`Self::apply_thm_explicit`]'s
                // const-key fill). Record it in the solution so later binder
                // domains mentioning this sentinel instantiate correctly. Re-derive
                // the key from the INSTANTIATED domain `dom` (r16 type-suffix keying),
                // not the dependency's generically-hashed stored `key`, so the fill
                // coincides with the consumer's own occurrence of the operation.
                // With `obj_isa` threaded (the root lane), take the SAME
                // flavor-aware fill the plain explicit path uses; the
                // historical callers (`obj_isa: None`) keep the shared opaque
                // param byte-identically.
                let fill = match obj_isa {
                    Some(fills) => self.const_key_fill(key, dom.clone(), fills)?,
                    None => self.const_param(const_key_name(key).unwrap_or(key), dom.clone()),
                };
                solution.insert(*bfv, fill.clone());
                applied_args.push(fill);
            } else if let Some(isa_tm) = entry
                .term_param_keys
                .get(bi)
                .and_then(|k| tminst_by_key.get(k))
            {
                // Un-presolved schematic-arg binder with a recorded (identity)
                // table entry: embed it — the consumer's own shared param for a
                // statement-shared free/schematic (flavor-bridged; see
                // [`Self::embed_table_operand`]). Kernel-re-checked.
                let fill = self.embed_table_operand(isa_tm, binders)?;
                solution.insert(*bfv, fill.clone());
                applied_args.push(fill);
            } else {
                // Cannot reconcile this binder — defer to the forward path.
                bailout = true;
                break;
            }
        }

        if bailout || idx != spine.len() {
            if let Some((t, ty, h)) = param_snap.as_ref() {
                self.term_params = t.clone();
                self.type_params = ty.clone();
                self.hyp_params = h.clone();
            }
            return Ok(None);
        }

        // --- Assemble: head, leading type args, then the per-binder args (with the
        // accumulated solution substituted into any that still mention a sentinel).
        let mut head = Expr::const_str_levels(entry.name.as_str(), Vec::<Level>::new());
        let mut all_type_solved = true;
        for fv in &type_sentinels {
            match solution.get(fv) {
                Some(ty_arg) => head = Expr::app(head, ty_arg.clone()),
                None => {
                    all_type_solved = false;
                    break;
                }
            }
        }
        if !all_type_solved {
            // A leading type instantiation is still unknown even after the
            // conclusion unification — fall back rather than invent it. Restore the
            // param lists so the speculative binder-loop registrations (which may
            // carry the still-free type sentinel in a `const:` op domain) do not
            // pollute the caller's forward fallback.
            if let Some((t, ty, h)) = param_snap.as_ref() {
                self.term_params = t.clone();
                self.type_params = ty.clone();
                self.hyp_params = h.clone();
            }
            return Ok(None);
        }
        for a in applied_args {
            let mut a = a;
            for (fv, sol) in &solution {
                a = a.subst_fvar(*fv, sol);
            }
            head = Expr::app(head, a);
        }
        Ok(Some(head))
    }

    /// **Root lane for the prop/proof tvar-namespace crossing** (binder-order
    /// round): a theorem whose recorded proof is a chain of leading `AbsP`
    /// **implicit sort-hypothesis** discharges (`OFCLASS`/`type_class`
    /// constraints the statement does not spell) over a `Thm` reference whose
    /// `tyinst` is **generic** ([`insts_generic`] — an identity table). The
    /// corpus exports these `<c>_class.<m>_def` hub nodes with the PROP spelled
    /// in the theory-level (user) tvar namespace but the PROOF spelled in the
    /// dependency box's canonical namespace — for a multi-tvar method the two
    /// namespaces are CROSSED (`sum`'s hub names the element `'b`/monoid `'a`
    /// while its bridge box names them `'a`/`'b`), so filling the identity
    /// table verbatim ([`Ctx::apply_thm_explicit`], the plain path)
    /// instantiates the dependency at the SWAPPED types — the measured
    /// same-arity `Pi[k]→Eq got=Pi[k]→Eq` `method.<m> α β` vs `method.<m> β α`
    /// kernel reject on `sum_def`/`prod_def`/`insort_key_def`.
    ///
    /// A generic table records no actual instantiation — the real one is
    /// pinned only by the surrounding inference, which at the proof ROOT is
    /// the embedded statement itself. So: peel the unspelled sort-`AbsP`s into
    /// `ElidedSortHyp` slots (exactly the plain path's elision), then apply
    /// the dependency **fully expectation-pinned**
    /// ([`Self::apply_thm_expecting_solved`] against the embedded statement) —
    /// namespace-free by construction (the fills are solved from the
    /// consumer's own conclusion, never read from the crossed table).
    ///
    /// STRICTLY ADDITIVE: returns `None` — and restores every ctx param list,
    /// the premise queue, and the binder stack — unless the expectation pinned
    /// EVERY binder (the solved path); the caller then runs the historical
    /// plain translation byte-identically. When the namespaces coincide the
    /// solved fills equal the identity-table fills, so a previously-verifying
    /// node builds the same term. Gated on `zproof_mode` + `class_membership`
    /// + `root_lane` (the dedicated trailing escalation modes, which run only
    /// after every historical mode kernel-rejected — see [`Ctx::root_lane`]).
    /// The kernel re-checks the assembled value against the stored statement,
    /// so a wrong solve is rejected — never miscounted.
    pub(crate) fn try_root_sort_absp_expecting(
        &mut self,
        p: &IsaProof,
        expected: &Expr,
        closure: &Closure,
        binders: &mut Vec<Binder>,
    ) -> Option<Expr> {
        if !(self.zproof_mode && self.class_membership && self.root_lane) {
            return None;
        }
        // Peel the contiguous leading chain of UNSPELLED sort-hypothesis
        // `AbsP`s (at least one — a bare root is the existing
        // `root_expecting` lane's job).
        let mut hyps: Vec<&IsaTerm> = Vec::new();
        let mut cur = p;
        while let IsaProof::AbsP { h: Some(hyp), b } = cur {
            if self.stmt_premises.iter().any(|t| t == hyp) || !is_sort_hyp_term(hyp) {
                return None;
            }
            hyps.push(hyp);
            cur = b;
        }
        if hyps.is_empty() {
            return None;
        }
        // The peeled core must be a resolved `Thm`-headed spine whose tables
        // are generic (identity): a genuinely-instantiated reference is exact
        // under the plain explicit fill and keeps that path untouched.
        let (head, spine) = collect_spine(cur);
        let IsaProof::Thm {
            id, tyinst, tminst, ..
        } = head
        else {
            return None;
        };
        if !insts_generic(tyinst, tminst) {
            return None;
        }
        let entry = closure.get(id)?.clone();
        // The reference's leading object-type fills, keyed exactly as the
        // plain explicit path reads them (`type_param_keys` ↦ `tyinst`, with
        // the `-1`-index free alias) — threaded so an expectation-unpinned
        // `const:` op binder takes the SAME flavor-aware fill
        // ([`Self::const_key_fill`]) the plain path would have used. All keys
        // present or the lane declines (the plain explicit path would have
        // bailed on the missing key too).
        let mut tyinst_by_key: BTreeMap<String, &IsaType> = BTreeMap::new();
        for ti in tyinst {
            tyinst_by_key.insert(format!("{}.{}", ti.n, ti.i), &ti.ty);
            if ti.i == -1 {
                tyinst_by_key.entry(ti.n.clone()).or_insert(&ti.ty);
            }
        }
        let mut obj_isa_fills: Vec<IsaType> = Vec::with_capacity(entry.type_param_keys.len());
        for key in &entry.type_param_keys {
            obj_isa_fills.push((*tyinst_by_key.get(key)?).clone());
        }
        // Snapshot everything a failed attempt could have touched, so the
        // caller's plain-path retry starts from the pristine state.
        let snap_types = self.type_params.clone();
        let snap_terms = self.term_params.clone();
        let snap_hyps = self.hyp_params.clone();
        let snap_queue = self.premise_queue.clone();
        let snap_leading = self.leading_active;
        let depth0 = binders.len();
        let mut restore = |ctx: &mut Self, binders: &mut Vec<Binder>| {
            ctx.type_params = snap_types.clone();
            ctx.term_params = snap_terms.clone();
            ctx.hyp_params = snap_hyps.clone();
            ctx.premise_queue = snap_queue.clone();
            ctx.leading_active = snap_leading;
            binders.truncate(depth0);
        };
        // Push one `ElidedSortHyp` slot per peeled constraint (the plain
        // path's elision, verbatim), so the spine's `PBound` references
        // resolve to witnesses.
        for hyp in &hyps {
            match self.embed_term(hyp, binders) {
                Ok(dom) => binders.push(Binder {
                    kind: BKind::ElidedSortHyp,
                    ty: dom,
                }),
                Err(_) => {
                    restore(self, binders);
                    return None;
                }
            }
        }
        let attempt = self.apply_thm_expecting_solved(
            &entry,
            &spine,
            expected,
            tminst,
            Some(&obj_isa_fills),
            closure,
            binders,
        );
        match attempt {
            Ok(Some(e)) => {
                binders.truncate(depth0);
                Some(e)
            }
            Ok(None) | Err(_) => {
                restore(self, binders);
                None
            }
        }
    }

    /// **Root eq-tower via the ISABELLE-level channel** (bidir stage 1): the
    /// primary root routing of the `RootLane::BidirEqTower` lane for a recorded
    /// proof whose root — after peeling the leading *elided sort-hypothesis*
    /// `AbsP` chain — is a pure equational-tower node (`transitive`/`symmetric`/
    /// `combination`/`reflexive`/`equal_elim`) proving the statement equation
    /// `A ≡ B`. Unlike the clean-level [`Self::translate_eq_expecting_clean`]
    /// (which the `root_expecting` path already runs and which decomposes only
    /// clean `App` congruences), this drives the ISABELLE-level
    /// [`Self::translate_eq_expecting`] with the statement's own `A`/`B` operands
    /// — so a `Pure.combination` congruence over a `Pure.imp`/`Pure.eq`
    /// meta-connective (which embeds to a clean `Pi`/special form, NOT an `App`,
    /// and so is invisible to the clean-level congruence split) still decomposes
    /// at the `IsaTerm::App` level (`imp $ A $ B`), fixing the meta-logical
    /// congruence towers (`swap_prems_eq`-style implication rearrangements) the
    /// clean channel cannot reach.
    ///
    /// STRICTLY ADDITIVE: returns `None` — restoring every ctx param list, the
    /// premise queue, and the binder stack — unless the whole tower translated;
    /// the caller then runs the plain expecting/forward path byte-identically.
    /// Gated on `bidir_tower` (the dedicated trailing modes). The kernel
    /// re-checks the assembled value against the stored statement, so a wrong
    /// recovery is rejected — never miscounted.
    pub(crate) fn try_root_eq_tower_expecting(
        &mut self,
        p: &IsaProof,
        prop_isa: &IsaTerm,
        closure: &Closure,
        binders: &mut Vec<Binder>,
    ) -> Result<Option<Expr>, TranslateError> {
        if !self.bidir_tower {
            return Ok(None);
        }
        // Peel the leading elided-sort-hypothesis `AbsP` chain (a spelled premise
        // or a non-sort hypothesis means the statement is not the bare equation —
        // decline and let the plain path handle it).
        let mut hyps: Vec<&IsaTerm> = Vec::new();
        let mut cur = p;
        while let IsaProof::AbsP { h: Some(hyp), b } = cur {
            if self.stmt_premises.iter().any(|t| t == hyp) || !is_sort_hyp_term(hyp) {
                return Ok(None);
            }
            hyps.push(hyp);
            cur = b;
        }
        // The peeled core must be a pure equational-tower AXIOM head.
        let (head, _spine) = collect_spine(cur);
        let IsaProof::Axm { name, .. } = head else {
            return Ok(None);
        };
        if !matches!(
            name.as_str(),
            "Pure.transitive"
                | "HOL.trans"
                | "Pure.symmetric"
                | "HOL.sym"
                | "Pure.combination"
                | "Pure.reflexive"
                | "HOL.refl"
        ) {
            return Ok(None);
        }
        // The statement must be a bare (Trueprop/Pure.prop-stripped) equation
        // whose two sides drive the Isabelle-level operand recovery.
        let Some((a_isa, b_isa)) = pure_eq_parts(strip_prop_wrappers(prop_isa)) else {
            return Ok(None);
        };
        let (a_isa, b_isa) = (a_isa.clone(), b_isa.clone());
        // Snapshot everything a failed attempt could have touched.
        let snap_types = self.type_params.clone();
        let snap_terms = self.term_params.clone();
        let snap_hyps = self.hyp_params.clone();
        let snap_queue = self.premise_queue.clone();
        let snap_leading = self.leading_active;
        let depth0 = binders.len();
        let mut restore = |ctx: &mut Self, binders: &mut Vec<Binder>| {
            ctx.type_params = snap_types.clone();
            ctx.term_params = snap_terms.clone();
            ctx.hyp_params = snap_hyps.clone();
            ctx.premise_queue = snap_queue.clone();
            ctx.leading_active = snap_leading;
            binders.truncate(depth0);
        };
        // Push one `ElidedSortHyp` slot per peeled constraint (so the tower's
        // `PBound` references resolve to witnesses) — the sort hyps emit no clean
        // lambda, so the recovered tower value IS the whole proof term.
        for hyp in &hyps {
            match self.embed_term(hyp, binders) {
                Ok(dom) => binders.push(Binder {
                    kind: BKind::ElidedSortHyp,
                    ty: dom,
                }),
                Err(_) => {
                    restore(self, binders);
                    return Ok(None);
                }
            }
        }
        match self.translate_eq_expecting(cur, &a_isa, &b_isa, closure, binders) {
            Ok(Some(e)) => {
                binders.truncate(depth0);
                Ok(Some(e))
            }
            Ok(None) | Err(_) => {
                restore(self, binders);
                Ok(None)
            }
        }
    }

    /// **`equal_elim` under expectation** (bidir stage 1): translate a
    /// `Pure.equal_elim` node (`A ≡ B ⟹ A ⟹ B`) whose EXPECTED result `B` is
    /// known from the enclosing telescope — the keystone of the recursive
    /// expectation-propagation lane. The forward [`Ctx::bootstrap_axiom`]
    /// `equal_elim` handler reads the operands `A`/`B` from the recorded
    /// instantiation table, which the zproof export spells in the derivation
    /// box's namespace (`Free x` / a crossed schematic) — desynchronizing them
    /// from the consumer's statement (`?x.0`), the operand-desync the reject
    /// census decoded. Here the result `B` IS the caller's `expected` (the
    /// consumer's own statement namespace, exact by construction), and the
    /// left operand `A` is recovered from the equation premise's OWN inferred
    /// proposition ([`Self::infer_proof_prop`] — statement-keyed whenever its
    /// chain bottoms out in a `PBound`/`Hyp`), falling back to the recorded
    /// table operand ([`Self::embed_table_operand`], flavor-bridged) only when
    /// the premise proposition is not statically derivable. Both proof premises
    /// are then translated against their now-namespace-correct expectations
    /// (`heq : @Eq Prop A B`, `ha : A`).
    ///
    /// Scoped to the exact two-premise application (`A ≡ B ⟹ A ⟹ B` with no
    /// leftover `⋀`-elimination spine args): a node with leftover spine arguments
    /// (the connective `*_def_raw` elimination walk) declines here and keeps the
    /// forward handler byte-for-byte. Returns `Ok(None)` to decline (the caller
    /// falls back to the plain translation); the kernel re-checks the assembled
    /// `@Eq.mp A B heq ha` against the caller's expectation, so a wrong recovery
    /// is rejected — never miscounted.
    pub(crate) fn equal_elim_expecting(
        &mut self,
        spine: &[SpineArg],
        tminst: &[super::super::super::isabelle_pure::IsaTermInst],
        expected: &Expr,
        closure: &Closure,
        binders: &mut Vec<Binder>,
    ) -> Result<Option<Expr>, TranslateError> {
        // Exactly the two proof premises `heq`, `ha` and no leftover spine args
        // (a `⋀`-elimination term arg / an extra premise defers to the forward
        // walk, which handles the result-application cases).
        if spine.len() != 2 {
            return Ok(None);
        }
        let proof_spine = proof_spine_args(spine);
        let (Some(heq_p), Some(ha_p)) = (proof_spine.first().copied(), proof_spine.get(1).copied())
        else {
            return Ok(None);
        };
        // The result `B` is the caller's expectation — the consumer's own
        // statement namespace, exact by construction.
        let be = expected.clone();
        // Recover the left operand `A`: first from the equation premise's OWN
        // (statement-keyed) inferred proposition `@Eq Prop A B'`; otherwise from
        // the recorded (flavor-bridged) table operand `A`.
        let ae = match self.infer_proof_prop(heq_p, binders)? {
            Some(prop) => match eq_app_three(&prop) {
                Some((_, l, _, _)) => l,
                None => return Ok(None),
            },
            None => {
                // No derivable premise proposition — recover `A` from the
                // recorded table operand (flavor-bridged), declining if absent.
                let a_isa = tminst
                    .iter()
                    .find(|ti| ti.n == "A")
                    .or_else(|| tminst.first())
                    .map(|ti| &ti.t);
                match a_isa {
                    Some(a) => self.embed_table_operand(a, binders)?,
                    None => return Ok(None),
                }
            }
        };
        // `heq : @Eq Prop A B` and `ha : A`, both pinned by the recovered
        // (namespace-correct) operands.
        let heq_expected = eq_prop(ae.clone(), be.clone());
        let heq = self.translate_proof_expecting(heq_p, &heq_expected, closure, binders)?;
        let ha = self.translate_proof_expecting(ha_p, &ae, closure, binders)?;
        Ok(Some(Expr::apps(
            Expr::const_str_levels("Eq.mp", vec![Level::zero()]),
            [ae, be, heq, ha],
        )))
    }

    /// Bidirectional recovery for the base equational axioms whose conclusion is a
    /// **known Isabelle equation** `A ≡ B` — the `(a, b)` term operands carried by
    /// the enclosing `Pure.equal_elim` (or a parent `combination`). In the
    /// connective `*_def_raw` discharge proofs the raw export frequently drops
    /// these axioms' own term operands (`% NONE` → `Bound{-1}` sentinels), so the
    /// local [`Self::bootstrap_axiom`] cannot infer their types. Here the operands
    /// are recovered from the expected `A`/`B` *Isabelle* terms directly — at the
    /// Isabelle level, so the connective fold/unfold matches the kernel's
    /// β-reduction:
    ///
    /// - `Pure.combination` (`f x ≡ g y`): `A = f $ x`, `B = g $ y` at the Isa
    ///   level, so the operands are `A`/`B`'s function/argument split; each
    ///   sub-proof is recovered with its own expected equation (`f ≡ g`, `x ≡ y`).
    /// - `Pure.symmetric` (`A ≡ B` from `B ≡ A`): recurse with the flipped pair.
    /// - `Pure.reflexive` (`A ≡ A`): `@Eq.refl` once the operand is pinned by `A`.
    ///
    /// Returns `Ok(None)` (caller falls back to plain translation) when `pr` is not
    /// one of these heads or the shape does not decompose. The kernel re-checks the
    /// built term, so a wrong recovery is rejected — never miscounted.
    pub(crate) fn translate_eq_expecting(
        &mut self,
        pr: &IsaProof,
        a: &IsaTerm,
        b: &IsaTerm,
        closure: &Closure,
        binders: &mut Vec<Binder>,
    ) -> Result<Option<Expr>, TranslateError> {
        Ok(self
            .translate_eq_expecting_ops(pr, a, b, closure, binders)?
            .map(|(h, _)| h))
    }

    /// A congruence leg's translation with its **actual concluded operands**
    /// when they deviate from the caller's syntactic split (`Some((l, r))`), or
    /// `None` when the historical split-driven assembly applies byte-for-byte.
    ///
    /// Why operands must flow back: a recorded leg can prove
    /// `min ≡ (λa b. If (le a b) a b)` (its own exact conclusion — the
    /// dictionary-unfold lambda) while the syntactic App-split of the caller's
    /// β-NORMAL expected equation spells the partial application
    /// `If α (le a b)` at that position — a genuinely DIFFERENT function (the
    /// split fixes the outer `a`/`b` in the condition; the lambda binds them).
    /// Assembling `congr` with the split operands then mismatches the leg's
    /// real type (the s125868/s126068 `expected=Eq got=Eq` family). When a leg
    /// reports its actual operands, the parent assembles `congr` WITH them; the
    /// re-composed conclusion `f x ≡ g y` is β-defeq to the caller's
    /// expectation once fully applied, which the kernel re-checks — a wrong
    /// recovery is rejected, never miscounted.
    #[allow(clippy::type_complexity)]
    pub(crate) fn translate_eq_expecting_ops(
        &mut self,
        pr: &IsaProof,
        a: &IsaTerm,
        b: &IsaTerm,
        closure: &Closure,
        binders: &mut Vec<Binder>,
    ) -> Result<Option<(Expr, Option<(Expr, Expr)>)>, TranslateError> {
        let (head, spine) = collect_spine(pr);
        let IsaProof::Axm { name, tyinst, .. } = head else {
            return Ok(None);
        };
        // Strip the `Pure.prop`/`Trueprop` identity wrappers off the operands,
        // remembering whether anything was actually stripped: a WRAPPED operand
        // pair means the recorded chain may sit one congruence level ABOVE the
        // stripped equation (its outermost `combination` rewrites under the
        // `Trueprop` coercion the embedding erases — see the delegation below).
        let (a_raw, b_raw) = (a, b);
        let a = strip_prop_wrappers(a);
        let b = strip_prop_wrappers(b);
        let wrapped = !std::ptr::eq(a_raw, a) || !std::ptr::eq(b_raw, b);
        match name.as_str() {
            // `f ≡ g ⟹ x ≡ y ⟹ f x ≡ g y`, conclusion `A ≡ B` with `A = f $ x`,
            // `B = g $ y`. Decompose the *Isabelle* applications so each operand is
            // re-embedded faithfully (the connective head stays consistent with the
            // kernel's β/defeq, fixing the fold/unfold mismatch).
            "Pure.combination" => {
                // **Wrapper-level (Trueprop-coercion) congruence.** When the
                // expected operands arrived `Trueprop`-wrapped (`A ≡ B` =
                // `Trueprop X ≡ Trueprop Y`) and this combination's recorded
                // function type is the `bool ⇒ prop` COERCION, the node concludes
                // the WRAPPED equation: its function leg is the vacuous
                // `Trueprop ≡ Trueprop` reflexivity and its ARGUMENT leg proves
                // exactly the stripped `X ≡ Y`. The embedding erases `Trueprop`
                // (`embed(Trueprop X) = embed(X)`), so the faithful translation of
                // the whole node IS the argument leg's — decomposing the stripped
                // `X`/`Y` against THIS node instead desynchronizes every inner
                // pairing by one congruence level (the junk-leaf `expected=FVar`
                // rejects). Delegate; on failure fall through to the plain
                // decomposition (kernel re-checks either way).
                if wrapped && combination_at_prop_coercion(tyinst) {
                    let proof_spine = proof_spine_args(&spine);
                    if let Some(p2) = proof_spine.get(1) {
                        if let Ok(Some(h)) = self.translate_eq_expecting(p2, a, b, closure, binders)
                        {
                            return Ok(Some((h, None)));
                        }
                        let alpha = self.infer_type(a, binders)?;
                        let ae = self.embed_term(a, binders)?;
                        let be = self.embed_term(b, binders)?;
                        let expected = mk_eq_expr(alpha, ae, be);
                        if let Ok(h) =
                            self.translate_proof_expecting(p2, &expected, closure, binders)
                        {
                            return Ok(Some((h, None)));
                        }
                    }
                }
                let (IsaTerm::App { f, a: x }, IsaTerm::App { f: g, a: y }) = (a, b) else {
                    return Ok(None);
                };
                let f_ty = self.infer_type(f, binders)?;
                let Some((dom, cod)) = split_arrow(&f_ty) else {
                    return Ok(None);
                };
                let fe = self.embed_term(f, binders)?;
                let ge = self.embed_term(g, binders)?;
                let xe = self.embed_term(x, binders)?;
                let ye = self.embed_term(y, binders)?;
                let proof_spine = proof_spine_args(&spine);
                let (Some(p1), Some(p2)) = (proof_spine.first(), proof_spine.get(1)) else {
                    return Ok(None);
                };
                // Sub-proofs: `f ≡ g` and `x ≡ y`, recovered with their operands.
                // A leg the Isabelle-level channel does not decompose (a `Thm`
                // reference, …) still has a KNOWN expected equation — but its OWN
                // recorded conclusion is preferred when derivable
                // ([`Self::infer_thm_prop`] — a genuine-table reference), because
                // the syntactic split of a β-normal expectation can spell a
                // different (non-defeq) partial application than the leg actually
                // proves (see [`Self::translate_eq_expecting_ops`]). Otherwise the
                // split expectation is threaded through the bidirectional
                // clean-typed channel exactly as before.
                let (h1, ops1) = match self
                    .translate_eq_expecting_ops(p1, f, g, closure, binders)?
                {
                    Some((h, ops)) => (h, ops),
                    None => match self.thm_leg_own_eq(p1, closure, binders)? {
                        Some((h, l, r)) => (h, Some((l, r))),
                        None => {
                            let expected = mk_eq_expr(
                                Expr::arrow(dom.clone(), cod.clone()),
                                fe.clone(),
                                ge.clone(),
                            );
                            (
                                self.translate_proof_expecting(p1, &expected, closure, binders)?,
                                None,
                            )
                        }
                    },
                };
                // When the FUNCTION leg deviated (its actual conclusion is a
                // lambda the expected β-normal `r` had already reduced away),
                // the syntactic split of `r` mis-assigns the ARGUMENT pairing:
                // e.g. `max a b ≡ If (le a b) b a` splits its argument level as
                // `(a, b)` while the recorded leg is the reflexivity `a ≡ a`
                // (the derivation applies both sides of the lambda rewrite to
                // the SAME variable). Re-pair the argument leg as `(x, x)` from
                // the LEFT operand; the re-composed conclusion `f x ≡ g_e x` is
                // β-defeq to the caller's expectation once fully applied, which
                // the kernel re-checks. The non-deviating path is byte-identical.
                let (h2, ops2) = if ops1.is_some() {
                    match self.translate_eq_expecting_ops(p2, x, x, closure, binders)? {
                        Some((h, ops)) => (h, ops.or_else(|| Some((xe.clone(), xe.clone())))),
                        None => match self.thm_leg_own_eq(p2, closure, binders)? {
                            Some((h, l, r)) => (h, Some((l, r))),
                            None => {
                                let expected = mk_eq_expr(dom.clone(), xe.clone(), xe.clone());
                                (
                                    self.translate_proof_expecting(
                                        p2, &expected, closure, binders,
                                    )?,
                                    Some((xe.clone(), xe.clone())),
                                )
                            }
                        },
                    }
                } else {
                    match self.translate_eq_expecting_ops(p2, x, y, closure, binders)? {
                        Some((h, ops)) => (h, ops),
                        None => match self.thm_leg_own_eq(p2, closure, binders)? {
                            Some((h, l, r)) => (h, Some((l, r))),
                            None => {
                                let expected = mk_eq_expr(dom.clone(), xe.clone(), ye.clone());
                                (
                                    self.translate_proof_expecting(
                                        p2, &expected, closure, binders,
                                    )?,
                                    None,
                                )
                            }
                        },
                    }
                };
                // Assemble with each leg's ACTUAL operands where they deviate;
                // report the re-composed conclusion upward only then (the
                // historical split assembly stays byte-for-byte otherwise).
                let deviated = ops1.is_some() || ops2.is_some();
                let (f_e, g_e) = ops1.unwrap_or((fe, ge));
                let (x_e, y_e) = ops2.unwrap_or((xe, ye));
                let proof = Expr::apps(
                    Expr::const_str_levels("congr", vec![obj_level(), obj_level()]),
                    [
                        dom,
                        cod,
                        f_e.clone(),
                        g_e.clone(),
                        x_e.clone(),
                        y_e.clone(),
                        h1,
                        h2,
                    ],
                );
                let ops = deviated.then(|| (Expr::app(f_e, x_e), Expr::app(g_e, y_e)));
                Ok(Some((proof, ops)))
            }
            // `B ≡ A ⟹ A ≡ B`: the sub-proof proves the flipped equation.
            "Pure.symmetric" | "HOL.sym" => {
                let alpha = self.infer_type(a, binders)?;
                let ae = self.embed_term(a, binders)?;
                let be = self.embed_term(b, binders)?;
                let proof_spine = proof_spine_args(&spine);
                let Some(p) = proof_spine.first() else {
                    return Ok(None);
                };
                let (h, inner_ops) =
                    match self.translate_eq_expecting_ops(p, b, a, closure, binders)? {
                        Some((h, ops)) => (h, ops),
                        None => match self.thm_leg_own_eq(p, closure, binders)? {
                            Some((h, l, r)) => (h, Some((l, r))),
                            None => {
                                let expected = mk_eq_expr(alpha.clone(), be.clone(), ae.clone());
                                (
                                    self.translate_proof_expecting(p, &expected, closure, binders)?,
                                    None,
                                )
                            }
                        },
                    };
                // Flip the leg's ACTUAL operands when it deviated from the split
                // (see [`Self::translate_eq_expecting_ops`]); byte-identical
                // assembly otherwise.
                if let Some((li, ri)) = inner_ops {
                    let sym = Expr::apps(
                        Expr::const_str_levels("Eq.symm", vec![obj_level()]),
                        [alpha, li.clone(), ri.clone(), h],
                    );
                    return Ok(Some((sym, Some((ri, li)))));
                }
                Ok(Some((
                    Expr::apps(
                        Expr::const_str_levels("Eq.symm", vec![obj_level()]),
                        [alpha, be, ae, h],
                    ),
                    None,
                )))
            }
            // `a ≡ m ⟹ m ≡ b ⟹ a ≡ b` — transitivity. The expectation pins the
            // endpoints `a`/`b`, but NOT the midpoint `m`, which a generic
            // (identity-`tminst`) zproof reference records nowhere. Recover it
            // from a leg whose proposition is recorded or derivable:
            //  - a bare recorded hypothesis leg carries its full Isabelle
            //    proposition (split it as an equation → the ISA midpoint, letting
            //    the other leg recurse through this same exact channel);
            //  - otherwise a leg with a statically derivable embedded proposition
            //    ([`Self::infer_proof_prop`]) yields the clean midpoint, and both
            //    legs are translated against their now-known expected equations.
            // Returns `Ok(None)` when no midpoint is recoverable (the caller falls
            // back). The kernel re-checks the assembled `Eq.trans`, so a wrong
            // recovery is rejected — never miscounted.
            "Pure.transitive" | "HOL.trans" => {
                let proof_spine = proof_spine_args(&spine);
                let (Some(p1), Some(p2)) = (proof_spine.first(), proof_spine.get(1)) else {
                    return Ok(None);
                };
                let alpha = self.infer_type(a, binders)?;
                let ae = self.embed_term(a, binders)?;
                let be = self.embed_term(b, binders)?;
                // ISA-level midpoint from a bare recorded-hypothesis leg.
                let isa_mid = |p: &IsaProof, want_lhs: bool| -> Option<IsaTerm> {
                    let IsaProof::Hyp { p: hp } = p else {
                        return None;
                    };
                    let (l, r) = pure_eq_parts(strip_prop_wrappers(hp))?;
                    Some(if want_lhs { l.clone() } else { r.clone() })
                };
                if let Some(m_isa) = isa_mid(p1, false) {
                    let me = self.embed_term(&m_isa, binders)?;
                    let h1 = self.translate_proof(p1, closure, binders)?;
                    let h2 = match self.translate_eq_expecting(p2, &m_isa, b, closure, binders)? {
                        Some(h) => h,
                        None => {
                            let expected = mk_eq_expr(alpha.clone(), me.clone(), be.clone());
                            self.translate_proof_expecting(p2, &expected, closure, binders)?
                        }
                    };
                    return Ok(Some((
                        Expr::apps(
                            Expr::const_str_levels("Eq.trans", vec![obj_level()]),
                            [alpha, ae, me, be, h1, h2],
                        ),
                        None,
                    )));
                }
                if let Some(m_isa) = isa_mid(p2, true) {
                    let me = self.embed_term(&m_isa, binders)?;
                    let h1 = match self.translate_eq_expecting(p1, a, &m_isa, closure, binders)? {
                        Some(h) => h,
                        None => {
                            let expected = mk_eq_expr(alpha.clone(), ae.clone(), me.clone());
                            self.translate_proof_expecting(p1, &expected, closure, binders)?
                        }
                    };
                    let h2 = self.translate_proof(p2, closure, binders)?;
                    return Ok(Some((
                        Expr::apps(
                            Expr::const_str_levels("Eq.trans", vec![obj_level()]),
                            [alpha, ae, me, be, h1, h2],
                        ),
                        None,
                    )));
                }
                // Clean-level midpoint from a leg with a derivable proposition.
                let mut mid: Option<Expr> = None;
                if let Some(prop) = self.infer_proof_prop(p1, binders)? {
                    mid = eq_app_three(&prop).map(|(_, _, r, _)| r);
                }
                if mid.is_none() {
                    if let Some(prop) = self.infer_proof_prop(p2, binders)? {
                        mid = eq_app_three(&prop).map(|(_, l, _, _)| l);
                    }
                }
                // **`Thm`-leg midpoint recovery** (bidir stage 1) — the
                // Isabelle-level twin of the recovery in
                // [`Self::translate_eq_expecting_clean`]: a genuinely-instantiated
                // `Thm` leg's conclusion resolves from the closure
                // ([`Self::infer_thm_prop`]), which `infer_proof_prop` cannot reach.
                // Gated on `bidir_tower` so historical modes stay byte-identical;
                // kernel-re-checked.
                if mid.is_none() && self.bidir_tower {
                    if let Some(prop) = self.infer_thm_prop(p1, closure, binders)? {
                        mid = eq_app_three(&prop).map(|(_, _, r, _)| r);
                    }
                }
                if mid.is_none() && self.bidir_tower {
                    if let Some(prop) = self.infer_thm_prop(p2, closure, binders)? {
                        mid = eq_app_three(&prop).map(|(_, l, _, _)| l);
                    }
                }
                let Some(me) = mid else {
                    return Ok(None);
                };
                let h1 = {
                    let expected = mk_eq_expr(alpha.clone(), ae.clone(), me.clone());
                    self.translate_proof_expecting(p1, &expected, closure, binders)?
                };
                let h2 = {
                    let expected = mk_eq_expr(alpha.clone(), me.clone(), be.clone());
                    self.translate_proof_expecting(p2, &expected, closure, binders)?
                };
                Ok(Some((
                    Expr::apps(
                        Expr::const_str_levels("Eq.trans", vec![obj_level()]),
                        [alpha, ae, me, be, h1, h2],
                    ),
                    None,
                )))
            }
            // `A ≡ A` reflexivity, pinned by the expected operand `A`.
            "Pure.reflexive" | "HOL.refl" | "Pure.prop_def" => {
                let alpha = self.infer_type(a, binders)?;
                let ae = self.embed_term(a, binders)?;
                Ok(Some((
                    Expr::apps(
                        Expr::const_str_levels("Eq.refl", vec![obj_level()]),
                        [alpha, ae],
                    ),
                    None,
                )))
            }
            // A **dictionary-unfolding axiom** `c_class.method ≡ c.method op₁ … opₙ`
            // for a *registered* overloaded method. Under the method def-const
            // embedding (see [`MethodDefInfo`]) the overloaded `c_class.method`
            // (one of `a`/`b`) δ-unfolds to its dictionary form `c.method ops` (the
            // other side), so both expected operands embed to definitionally-equal
            // clean terms — the equation is genuinely reflexive. We prove it by
            // `@Eq.refl α (embed a)`; the kernel accepts ONLY when `embed a` and
            // `embed b` are defeq (a wrong registration is rejected, never
            // miscounted). The class operation arguments embed identically on both
            // sides, so the reflexivity holds for the whole congruence chain.
            _ if name.ends_with("_dict") && self.dict_sides_registered(a, b) => {
                let alpha = self.infer_type(a, binders)?;
                let ae = self.embed_term(a, binders)?;
                Ok(Some((
                    Expr::apps(
                        Expr::const_str_levels("Eq.refl", vec![obj_level()]),
                        [alpha, ae],
                    ),
                    None,
                )))
            }
            _ => Ok(None),
        }
    }

    /// A `Thm`-headed congruence leg translated against its **own derivable
    /// conclusion** ([`Ctx::infer_thm_prop`]) when that conclusion is a
    /// saturated equation — returning the proof together with the leg's actual
    /// operands `(l, r)` for the parent's `congr` assembly. `Ok(None)` when the
    /// leg's own proposition is not derivable / not an equation, or its
    /// translation fails — the caller keeps the historical split-expectation
    /// path byte-for-byte. The kernel re-checks the assembled parent, so a
    /// wrong derivation is rejected — never miscounted.
    fn thm_leg_own_eq(
        &mut self,
        pr: &IsaProof,
        closure: &Closure,
        binders: &mut Vec<Binder>,
    ) -> Result<Option<(Expr, Expr, Expr)>, TranslateError> {
        let Some(prop) = self.infer_thm_prop(pr, closure, binders)? else {
            return Ok(None);
        };
        let Some((_, l, r, _)) = eq_app_three(&prop) else {
            return Ok(None);
        };
        match self.translate_proof_expecting(pr, &prop, closure, binders) {
            Ok(h) => Ok(Some((h, l, r))),
            Err(_) => Ok(None),
        }
    }

    /// **Clean-level** bidirectional recovery for an `Axm`-headed equation chain
    /// whose expected proposition is a known embedded equation `@Eq α l r` — the
    /// counterpart of [`Self::translate_eq_expecting`] for call sites where only
    /// the CLEAN expectation is available (a referenced theorem's instantiated
    /// premise domain, e.g. `apply_thm_explicit`'s premise walk). The zproof
    /// export leaves these nested `combination`/`reflexive`/`symmetric`/
    /// `transitive` references GENERIC (identity `tminst` — no term operands),
    /// but their `tyinst` types ARE recorded, so together with the expected
    /// clean equation every operand is determined:
    ///
    /// - `Pure.combination` (`f x ≡ g y`): `l`/`r` split as clean `App`s; the
    ///   function type comes from the recorded `tyinst` (`'a` = the function's
    ///   type, `'b` = the result type, as the export records them); each
    ///   sub-proof recurses with its own expected equation.
    /// - `Pure.reflexive`: `@Eq.refl α l` (the kernel accepts iff `l ≡ r` defeq).
    /// - `Pure.symmetric`: recurse with the flipped equation.
    /// - `Pure.transitive`: the midpoint is recovered from a leg with a
    ///   statically derivable proposition ([`Self::infer_proof_prop`]).
    /// - a `Thm`-headed leg falls to [`Self::translate_proof_expecting`] with the
    ///   built expected equation (solving a generic reference bidirectionally);
    ///   a `Hyp`/`PBound` leg translates directly.
    ///
    /// Returns `Ok(None)` when the shape does not decompose (caller falls back).
    /// The kernel re-checks the assembled term, so a wrong recovery is rejected —
    /// never miscounted.
    pub(crate) fn translate_eq_expecting_clean(
        &mut self,
        pr: &IsaProof,
        alpha: &Expr,
        l: &Expr,
        r: &Expr,
        closure: &Closure,
        binders: &mut Vec<Binder>,
    ) -> Result<Option<Expr>, TranslateError> {
        use clean_kernel::expr::ExprKind;
        // A leg with a directly-translatable identity: a recorded hypothesis or a
        // proof-binder reference.
        if matches!(pr, IsaProof::Hyp { .. } | IsaProof::Bound { .. }) {
            return Ok(Some(self.translate_proof(pr, closure, binders)?));
        }
        let (head, spine) = collect_spine(pr);
        let IsaProof::Axm { name, tyinst, .. } = head else {
            // A referenced theorem (or other head): solve it against the built
            // expected equation through the bidirectional Thm channel.
            return Ok(Some(self.translate_proof_expecting(
                pr,
                &mk_eq_expr(alpha.clone(), l.clone(), r.clone()),
                closure,
                binders,
            )?));
        };
        match name.as_str() {
            "Pure.reflexive" | "HOL.refl" | "Pure.prop_def" => Ok(Some(Expr::apps(
                Expr::const_str_levels("Eq.refl", vec![obj_level()]),
                [alpha.clone(), l.clone()],
            ))),
            "Pure.symmetric" | "HOL.sym" => {
                let proof_spine = proof_spine_args(&spine);
                let Some(p) = proof_spine.first() else {
                    return Ok(None);
                };
                let Some(h) =
                    self.translate_eq_expecting_clean(p, alpha, r, l, closure, binders)?
                else {
                    return Ok(None);
                };
                Ok(Some(Expr::apps(
                    Expr::const_str_levels("Eq.symm", vec![obj_level()]),
                    [alpha.clone(), r.clone(), l.clone(), h],
                )))
            }
            "Pure.combination" => {
                // **Wrapper-level (Trueprop-coercion) congruence** — the clean-level
                // counterpart of the delegation in [`Self::translate_eq_expecting`].
                // A clean expectation `@Eq α l r` is ALWAYS coercion-free (the
                // embedding erases `Trueprop`), so a combination whose recorded
                // function type is the `bool ⇒ prop` coercion sits one congruence
                // level above it: its argument leg proves exactly the expected
                // equation. Delegate; on failure fall through to the plain
                // decomposition (kernel re-checks either way).
                if combination_at_prop_coercion(tyinst) {
                    let proof_spine = proof_spine_args(&spine);
                    if let Some(p2) = proof_spine.get(1) {
                        if let Ok(Some(h)) =
                            self.translate_eq_expecting_clean(p2, alpha, l, r, closure, binders)
                        {
                            return Ok(Some(h));
                        }
                    }
                }
                let (ExprKind::App(fe, xe), ExprKind::App(ge, ye)) = (l.kind(), r.kind()) else {
                    return Ok(None);
                };
                // The recorded types: `'a` = the function's type, `'b` = the
                // result type (matching the export's combination instantiation).
                let fun_isa = tyinst
                    .iter()
                    .find(|ti| ti.n == "'a")
                    .or_else(|| tyinst.first());
                let Some(fun_isa) = fun_isa else {
                    return Ok(None);
                };
                let fun_ty = self.embed_type(&fun_isa.ty)?;
                let Some((dom, _cod)) = split_arrow(&fun_ty) else {
                    return Ok(None);
                };
                let cod_ty = match tyinst
                    .iter()
                    .find(|ti| ti.n == "'b")
                    .or_else(|| tyinst.get(1))
                {
                    Some(ti) => self.embed_type(&ti.ty)?,
                    None => alpha.clone(),
                };
                let proof_spine = proof_spine_args(&spine);
                let (Some(p1), Some(p2)) = (proof_spine.first(), proof_spine.get(1)) else {
                    return Ok(None);
                };
                let (fe, xe, ge, ye) = (
                    (**fe).clone(),
                    (**xe).clone(),
                    (**ge).clone(),
                    (**ye).clone(),
                );
                let Some(h1) =
                    self.translate_eq_expecting_clean(p1, &fun_ty, &fe, &ge, closure, binders)?
                else {
                    return Ok(None);
                };
                let Some(h2) =
                    self.translate_eq_expecting_clean(p2, &dom, &xe, &ye, closure, binders)?
                else {
                    return Ok(None);
                };
                Ok(Some(Expr::apps(
                    Expr::const_str_levels("congr", vec![obj_level(), obj_level()]),
                    [dom, cod_ty, fe, ge, xe, ye, h1, h2],
                )))
            }
            "Pure.transitive" | "HOL.trans" => {
                let proof_spine = proof_spine_args(&spine);
                let (Some(p1), Some(p2)) = (proof_spine.first(), proof_spine.get(1)) else {
                    return Ok(None);
                };
                let mut mid: Option<Expr> = None;
                if let Some(prop) = self.infer_proof_prop(p1, binders)? {
                    mid = eq_app_three(&prop).map(|(_, _, y, _)| y);
                }
                if mid.is_none() {
                    if let Some(prop) = self.infer_proof_prop(p2, binders)? {
                        mid = eq_app_three(&prop).map(|(_, x, _, _)| x);
                    }
                }
                // **`Thm`-leg midpoint recovery** (bidir stage 1): the midpoint
                // `m` of `L ≡ m ⟹ m ≡ R ⟹ L ≡ R` is recorded nowhere on a
                // GENERIC (identity-`tminst`) outer `transitive` node, and
                // [`Self::infer_proof_prop`] derives it only from a `Bound`/`Hyp`/
                // `Axm`-headed leg — NOT from a `Thm` reference. But a nested
                // equational tower's legs are overwhelmingly genuinely-instantiated
                // `Thm` references (`method.<m>_def` / congruence lemmas) whose
                // conclusion IS resolvable from the closure ([`Self::infer_thm_prop`],
                // which specializes the stored type by the leg's OWN recorded — and
                // here namespace-consistent — tables). Recover the midpoint from
                // either leg's `Thm` conclusion. Gated on `bidir_tower` so every
                // historical mode (and the `root_expecting` path) stays
                // byte-identical; the recovered midpoint only pins the two legs'
                // expected equations, which the kernel re-checks — a wrong midpoint
                // is rejected, never miscounted. This is the keystone that lets the
                // whole `transitive` tower resolve (each leg recurses through this
                // same channel).
                if mid.is_none() && self.bidir_tower {
                    if let Some(prop) = self.infer_thm_prop(p1, closure, binders)? {
                        mid = eq_app_three(&prop).map(|(_, _, y, _)| y);
                    }
                }
                if mid.is_none() && self.bidir_tower {
                    if let Some(prop) = self.infer_thm_prop(p2, closure, binders)? {
                        mid = eq_app_three(&prop).map(|(_, x, _, _)| x);
                    }
                }
                let Some(me) = mid else {
                    return Ok(None);
                };
                let Some(h1) =
                    self.translate_eq_expecting_clean(p1, alpha, l, &me, closure, binders)?
                else {
                    return Ok(None);
                };
                let Some(h2) =
                    self.translate_eq_expecting_clean(p2, alpha, &me, r, closure, binders)?
                else {
                    return Ok(None);
                };
                Ok(Some(Expr::apps(
                    Expr::const_str_levels("Eq.trans", vec![obj_level()]),
                    [alpha.clone(), l.clone(), me, r.clone(), h1, h2],
                )))
            }
            _ => Ok(None),
        }
    }

    /// Whether `p` is a pure **equational-glue chain** — every leaf is one of the
    /// Pure equality-congruence axioms (`combination`/`symmetric`/`reflexive`/
    /// `transitive`/`abstract_rule` and their HOL aliases) or a **registered**
    /// overloaded-method `…_dict` dictionary axiom — setting `found` when at least
    /// one such `…_dict` leaf is present. Such a chain only ever rewrites by the
    /// dictionary unfolding (plus congruence plumbing), so its conclusion's two
    /// sides embed to **definitionally equal** clean terms under the active
    /// `method_unfold` embedding — the whole chain collapses to one `Eq.refl`
    /// (see [`Self::dict_glue_refl`]). Any other node kind (a `Thm` reference, a
    /// `Hyp`, a `Bound`, an oracle, a non-glue axiom) makes this return `false`,
    /// so a chain with real (non-defeq) rewriting content is never collapsed.
    fn dict_glue_walk(&self, p: &IsaProof, found: &mut bool) -> bool {
        match p {
            IsaProof::Axm { name, .. } => {
                if matches!(
                    name.as_str(),
                    "Pure.combination"
                        | "Pure.symmetric"
                        | "Pure.reflexive"
                        | "Pure.transitive"
                        | "Pure.abstract_rule"
                        | "HOL.refl"
                        | "HOL.sym"
                        | "HOL.trans"
                ) {
                    true
                } else if name.ends_with("_dict")
                    && self
                        .method_registry
                        .contains_key(name.trim_end_matches("_dict"))
                {
                    *found = true;
                    true
                } else {
                    false
                }
            }
            IsaProof::AppP { f, a } => {
                self.dict_glue_walk(f, found) && self.dict_glue_walk(a, found)
            }
            IsaProof::AppT { f, .. } => self.dict_glue_walk(f, found),
            IsaProof::Abst { b, .. } | IsaProof::AbsP { b, .. } => self.dict_glue_walk(b, found),
            _ => false,
        }
    }

    /// **Dictionary-glue collapse**: when a proof argument whose expected clean
    /// proposition is a saturated equation `@Eq α L R` fails to translate, and the
    /// recorded proof is a pure equational-glue chain whose only rewriting leaves
    /// are **registered** `…_dict` dictionary axioms ([`Self::dict_glue_walk`]),
    /// prove the expectation by `@Eq.refl α L`.
    ///
    /// Under the active `method_unfold` embedding a registered overloaded method
    /// embeds to its dictionary def-const, which δ-unfolds to exactly the
    /// dictionary form — so the two sides of every equation such a chain derives
    /// are **definitionally equal** clean terms, and `Eq.refl` on the expected LHS
    /// is a genuine proof of the expected (distinct-operand, faithful) equation.
    /// The kernel re-checks the result against the consumer's exact expectation,
    /// so a chain whose sides do NOT coincide definitionally is rejected — never
    /// miscounted. This recovers the `…_dict` consumers whose glue chain sits in a
    /// position the Isabelle-level operand recovery ([`Self::translate_eq_expecting`])
    /// cannot reach: inside a `PThm` premise argument (the referenced theorem's
    /// telescope supplies only the *clean* expectation) and under the extra
    /// `Trueprop` congruence layer of an `equal_elim` equation premise (the zproof
    /// export records only generic schematic `tminst` on the inner glue leaves, so
    /// the forward translation cannot reconstruct the operands). Returns `None`
    /// (caller keeps its honest translate error) when the expectation is not a
    /// saturated `Eq`, the chain has non-glue content, no registered `…_dict` leaf
    /// is present, or method unfolding is not active (strictly additive: modes
    /// that verified before behave identically).
    pub(crate) fn dict_glue_refl(&self, pr: &IsaProof, expected: &Expr) -> Option<Expr> {
        use clean_kernel::expr::ExprKind;
        if !self.method_unfold {
            return None;
        }
        // `expected` must be a saturated `@Eq α L R` application.
        let ExprKind::App(f1, _rhs) = expected.kind() else {
            return None;
        };
        let ExprKind::App(f2, lhs) = f1.kind() else {
            return None;
        };
        let ExprKind::App(eq_head, alpha) = f2.kind() else {
            return None;
        };
        let ExprKind::Const(n, levels) = eq_head.kind() else {
            return None;
        };
        if *n != clean_kernel::name::Name::from_string("Eq") {
            return None;
        }
        let mut found = false;
        if !self.dict_glue_walk(pr, &mut found) || !found {
            return None;
        }
        Some(Expr::apps(
            Expr::const_str_levels("Eq.refl", levels.clone()),
            [(**alpha).clone(), (**lhs).clone()],
        ))
    }

    /// Whether the clean expectation `expected` is a saturated `@Eq α L R`
    /// application (the shape the dictionary-glue recovery acts on).
    fn expected_is_eq(expected: &Expr) -> bool {
        use clean_kernel::expr::ExprKind;
        let ExprKind::App(f1, _rhs) = expected.kind() else {
            return false;
        };
        let ExprKind::App(f2, _lhs) = f1.kind() else {
            return false;
        };
        let ExprKind::App(eq_head, _alpha) = f2.kind() else {
            return false;
        };
        matches!(eq_head.kind(), clean_kernel::expr::ExprKind::Const(n, _)
            if *n == clean_kernel::name::Name::from_string("Eq"))
    }

    /// **Dictionary-glue recovery** for a failed proof argument with a known clean
    /// equation expectation `@Eq α L R` — the fallback entrypoint
    /// [`Self::translate_proof_expecting`] runs after the forward translation
    /// errors. Two shapes are recovered, both kernel-re-checked:
    ///
    /// 1. the whole proof is dictionary glue ([`Self::dict_glue_refl`]) →
    ///    `@Eq.refl α L`;
    /// 2. the proof is `Pure.transitive p₁ p₂` where ONE leg is dictionary glue:
    ///    that leg proves `L ≡ M` (resp. `M ≡ R`) whose sides embed to
    ///    **definitionally equal** clean terms under `method_unfold`, so the
    ///    OTHER leg — which proves `M ≡ R` (resp. `L ≡ M`) — is already a proof
    ///    of the full expectation up to defeq. We translate that other leg with
    ///    the SAME `@Eq α L R` expectation (recursing through this very recovery,
    ///    so nested `transitive(glue, PThm(… transitive(glue, …)))` towers
    ///    resolve), and return it directly.
    ///
    /// Returns `Ok(None)` when the expectation is not a saturated `Eq`, method
    /// unfolding is inactive, or the proof matches neither shape — the caller
    /// keeps its honest translate error. A recovered term the kernel rejects is
    /// rejected against the consumer's exact expectation — never miscounted.
    pub(crate) fn dict_glue_recover(
        &mut self,
        pr: &IsaProof,
        expected: &Expr,
        closure: &Closure,
        binders: &mut Vec<Binder>,
    ) -> Result<Option<Expr>, TranslateError> {
        if !self.method_unfold || !Self::expected_is_eq(expected) {
            return Ok(None);
        }
        if let Some(p) = self.dict_glue_refl(pr, expected) {
            return Ok(Some(p));
        }
        // `Pure.transitive` with one dictionary-glue leg: skip the (defeq) glue
        // leg and translate the other leg against the same expectation.
        let (head, spine) = collect_spine(pr);
        let IsaProof::Axm { name, .. } = head else {
            return Ok(None);
        };
        if name != "Pure.transitive" && name != "HOL.trans" {
            return Ok(None);
        }
        let pargs = proof_spine_args(&spine);
        let (Some(p1), Some(p2)) = (pargs.first().copied(), pargs.get(1).copied()) else {
            return Ok(None);
        };
        let mut found = false;
        if self.dict_glue_walk(p1, &mut found) && found {
            return self
                .translate_proof_expecting(p2, expected, closure, binders)
                .map(Some);
        }
        let mut found = false;
        if self.dict_glue_walk(p2, &mut found) && found {
            return self
                .translate_proof_expecting(p1, expected, closure, binders)
                .map(Some);
        }
        Ok(None)
    }

    /// Whether a `…_dict` axiom's two expected sides are the overloaded method and
    /// its dictionary form for a **registered** method — i.e. one side is a bare
    /// overloaded method `Const` in [`Self::method_registry`]. Gates the reflexive
    /// `…_dict` discharge so an unregistered method's `…_dict` still falls through
    /// (and is reported as `unmapped-axiom`, not silently mis-verified).
    pub(crate) fn dict_sides_registered(&self, a: &IsaTerm, b: &IsaTerm) -> bool {
        // Only fire in the unfolding pass: the reflexive discharge needs the
        // overloaded method to actually δ-unfold to its dictionary form (which only
        // happens when `embed_method_use` is active).
        if !self.method_unfold {
            return false;
        }
        let is_reg_method = |t: &IsaTerm| matches!(t, IsaTerm::Const { n, .. } if self.method_registry.contains_key(n));
        // One side is the overloaded method head; the other its dictionary form.
        let head_is_reg = |t: &IsaTerm| {
            let (h, _) = term_app_spine(t);
            is_reg_method(h)
        };
        head_is_reg(a) || head_is_reg(b)
    }
}
