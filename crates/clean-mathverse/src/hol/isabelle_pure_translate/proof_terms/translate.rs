// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `impl Ctx` proof-walking: `translate_proof`, the proof-level redex
//! β-reducer, and the bidirectional `translate_proof_expecting`. Split out of
//! the original single-file `proof_terms` module verbatim.

use super::super::super::isabelle_pure::IsaProof;
use super::super::*;
use super::*;
use clean_kernel::{BinderInfo, Expr};

impl Ctx {
    /// The witness a `PBound` reference to an **elided implicit
    /// sort-hypothesis** slot resolves to, given the slot's embedded membership
    /// proposition: `True.intro` for the vacuous `True` (an unregistered /
    /// erased class), or a quantified `∀(h : c_class α ops)` **hypothesis
    /// param** for a registered structured class — the honest explicit form of
    /// Isabelle's implicit sort constraint (exactly what Isabelle's own
    /// `unconstrainT` does at export time). Keyed by the embedded proposition,
    /// so every reference to the same constraint shares one binder; the final
    /// quantification wrap pi-binds it on both the stored type and the value,
    /// keeping them in lockstep. The kernel re-checks the result.
    pub(crate) fn sort_hyp_witness(&mut self, prop: &Expr) -> Expr {
        if *prop == Expr::const_str("True") {
            Expr::const_str("True.intro")
        } else {
            self.hyp_param(&format!("implicit-sort:{prop:?}"), prop.clone())
        }
    }

    /// Translate a proof term to a clean proof `Expr`. `closure` resolves PThm
    /// serials to already-verified clean constant names.
    pub(crate) fn translate_proof(
        &mut self,
        p: &IsaProof,
        closure: &Closure,
        binders: &mut Vec<Binder>,
    ) -> Result<Expr, TranslateError> {
        // Env-gated runaway guard: every recursive proof-node visit consumes one
        // unit of the per-LINE budget (`ISA_TRANSLATE_NODE_BUDGET`; unset =
        // unlimited, zero-cost default). The counter is thread-local and reset
        // per line by the driver, so the five escalating modes SHARE one
        // budget — a pathological recorded proof (multi-hundred-MB congruence
        // tower with superlinear reconstruction) fails FAST as an honest
        // bounded reject instead of grinding the corpus replay on one line.
        if let Some(budget) = bump_translate_steps() {
            return Err(TranslateError::BudgetExceeded(budget));
        }
        match p {
            // A free hypothesis used directly → its quantified proof var.
            IsaProof::Hyp { p: hp } => {
                let prop_ty = self.embed_term(hp, binders)?;
                let key = format!("{hp:?}");
                return Ok(self.hyp_param(&key, prop_ty));
            }
            // `AbsP(h:A, body)` discharges A: clean `fun (h:A) => body`.
            //
            // The raw proof body omits the hypothesis term for *every* AbsP
            // (`h: None`). We recover it from the statement: the discharged
            // premises appear, outermost-first, as the leading `Pure.imp`
            // chain of `thm.prop` (collected into `self.premise_queue` up front).
            // The i-th enclosing AbsP corresponds to the i-th premise, so we pop
            // the front premise here. When the export *did* record `h: Some(hyp)`
            // we use that explicit term but still advance the cursor so the
            // statement/proof premise ordering stays aligned. The kernel re-checks
            // the result, so a mis-recovery is rejected, never miscounted.
            IsaProof::AbsP { h, b } => {
                // **Implicit sort-hypothesis elision** (fully-typed `zproof`
                // proofs, `Real`-membership pass only): an `AbsP` whose EXPLICIT
                // hypothesis is a sort-constraint membership (`OFCLASS('a, c)` /
                // `type_class TYPE('a)`) that the statement does NOT spell
                // (Isabelle attaches it to the type variable's sort — it is not
                // the front leading premise) is TRANSPARENT: no clean lambda is
                // emitted (an emitted `λ(_:True)` would add a premise the
                // embedded statement lacks — the `expected=Pi[N]->Sort got=True`
                // intro_of_class reject family), and any `PBound` reference to
                // it becomes the membership WITNESS ([`Ctx::sort_hyp_witness`]):
                // `True.intro` for a vacuous/unregistered membership, or a
                // quantified `∀(h : c_class α ops)` hypothesis param for a
                // REGISTERED structured class — the honest explicit form of
                // Isabelle's sort constraint (the `…_class.axioms` projections,
                // whose statements assume `'a::c` implicitly). Gated on
                // `zproof_mode` (legacy proofs byte-identical) and
                // `class_membership` (the `Erase` passes byte-identical, so the
                // escalation ordering is preserved). The kernel re-checks the
                // result, so a wrong elision is rejected — never miscounted.
                if self.zproof_mode && self.class_membership {
                    if let Some(hyp) = h.as_ref() {
                        // Spelled ANYWHERE in the statement's leading premise
                        // chain ⇒ keep the lambda (a root redex clears
                        // `leading_active`, so the queue front alone cannot
                        // decide spelled-ness off the leading spine).
                        let spelled = self.stmt_premises.iter().any(|t| t == hyp);
                        if !spelled && is_sort_hyp_term(hyp) {
                            let dom = self.embed_term(hyp, binders)?;
                            binders.push(Binder {
                                kind: BKind::ElidedSortHyp,
                                ty: dom,
                            });
                            let body = self.translate_proof(b, closure, binders);
                            binders.pop();
                            return body;
                        }
                    }
                }
                // On the leading spine, a bare `AbsP` consumes the matching front
                // leading binder, which must be a `Pure.imp` premise
                // (`LeadingBinder::Hyp`). Off the leading spine the queue is not
                // touched (it tracks only the statement's outermost chain).
                let recovered = if self.leading_active {
                    match self.premise_queue.front() {
                        Some(LeadingBinder::Hyp(_)) => {
                            if let Some(LeadingBinder::Hyp(t)) = self.premise_queue.pop_front() {
                                Some(t)
                            } else {
                                None
                            }
                        }
                        _ => None,
                    }
                } else {
                    None
                };
                let hyp = match (h.as_ref(), recovered.as_ref()) {
                    (Some(hyp), _) => hyp,
                    (None, Some(prem)) => prem,
                    (None, None) => {
                        return Err(TranslateError::Unsupported("AbsP without hypothesis"))
                    }
                };
                let dom = self.embed_term(hyp, binders)?;
                binders.push(Binder {
                    kind: BKind::Proof,
                    ty: dom.clone(),
                });
                let body = self.translate_proof(b, closure, binders);
                binders.pop();
                return Ok(Expr::lam(BinderInfo::Default, dom, body?));
            }
            // `Abst(x:T, body)` (⋀-intro): clean `fun (x:T) => body`.
            //
            // The raw export omits the bound-variable type (`ty: None`). On the
            // leading spine, a bare `Abst` corresponds to a leading
            // `Pure.all (λx:T. _)` / `⋀x:T.` binder in the statement, so we
            // recover `T` from the front of the leading-binder queue (mirroring
            // the `AbsP { h: None }` recovery). The kernel re-checks the result,
            // so a wrong recovery is rejected.
            IsaProof::Abst { ty, b } => {
                let recovered = if self.leading_active {
                    match self.premise_queue.front() {
                        Some(LeadingBinder::AllTy(_)) => {
                            if let Some(LeadingBinder::AllTy(t)) = self.premise_queue.pop_front() {
                                Some(t)
                            } else {
                                None
                            }
                        }
                        _ => None,
                    }
                } else {
                    None
                };
                let dom = match (ty, recovered.as_ref()) {
                    (Some(t), _) => self.embed_type(t)?,
                    (None, Some(t)) => self.embed_type(t)?,
                    (None, None) => return Err(TranslateError::Unsupported("Abst without type")),
                };
                binders.push(Binder {
                    kind: BKind::ProofTerm,
                    ty: dom.clone(),
                });
                let body = self.translate_proof(b, closure, binders);
                binders.pop();
                return Ok(Expr::lam(BinderInfo::Default, dom, body?));
            }
            // `PBound i` → clean bvar over the proof-binder context (or the
            // membership witness for an elided sort-hypothesis slot).
            IsaProof::Bound { i } => {
                return match proof_bvar_slot(binders, *i as usize) {
                    Some(PboundSlot::Bvar(d)) => Ok(Expr::bvar(d)),
                    Some(PboundSlot::Elided(prop)) => Ok(self.sort_hyp_witness(&prop)),
                    None => Err(TranslateError::Unsupported("loose PBound")),
                };
            }
            // Sort witness → the proof of the vacuous `True` sort constraint.
            IsaProof::OfClass { .. } => return Ok(Expr::const_str("True.intro")),
            _ => {}
        }

        // Past the leading binder chain: this node is an application or leaf, so
        // we have left the outermost spine. Subsequent binders (redex arguments,
        // bare proof arguments) recover their omitted types locally, never from
        // the leading-binder queue.
        self.leading_active = false;

        let (head, spine) = collect_spine(p);
        match head {
            // Fully-typed (`zproof`) Pure/HOL base axioms carry their schematic
            // term/type arguments in the explicit `tyinst`/`tminst` tables, NOT on
            // the proof spine (the legacy export applied them as `% t` spine args).
            // Forward both tables so each handler can recover the term/type arg it
            // needs from the table when the spine omits it (legacy JSON has empty
            // tables, so the existing spine-based path is unchanged).
            IsaProof::Axm {
                name,
                tyinst,
                tminst,
            } => self.bootstrap_axiom(name, &spine, tyinst, tminst, closure, binders),
            IsaProof::Thm {
                id, tyinst, tminst, ..
            } => {
                let entry = closure
                    .get(id)
                    .ok_or(TranslateError::UnresolvedThm(*id))?
                    .clone();
                // Fully-typed (`zproof`) reference: when an explicit `tyinst`/
                // `tminst` table is present, specialize the referenced theorem's
                // leading type/term instantiations DIRECTLY (exact, no spine-driven
                // reconstruction). Legacy references carry empty tables, so this is
                // skipped and the implicit `apply_thm` path runs unchanged.
                if !tyinst.is_empty() || !tminst.is_empty() {
                    if let Some(e) =
                        self.apply_thm_explicit(&entry, tyinst, tminst, &spine, closure, binders)?
                    {
                        return Ok(e);
                    }
                }
                self.apply_thm(&entry, &spine, closure, binders)
            }
            IsaProof::Min | IsaProof::Oracle { .. } | IsaProof::Nop | IsaProof::Other => {
                Err(TranslateError::Hole("MinProof/oracle/nop"))
            }
            // A structural binder applied to args — a proof-level redex
            // `(⋀x. body) % t` / `(λh. body) %% q`. β-reduce at the IsaProof level
            // (eliminating the typeless binders) and/or recover each binder's
            // omitted type from its argument; clean re-checks the result.
            IsaProof::AbsP { .. } | IsaProof::Abst { .. } | IsaProof::Bound { .. } => {
                self.translate_redex(head, &spine, closure, binders)
            }
            _ => Err(TranslateError::Unsupported("proof head not yet supported")),
        }
    }

    /// Translate a proof-level redex `(binder…) arg…` — a chain of structural
    /// binders (`Abst`/`AbsP`) applied to spine arguments. The raw export omits
    /// each binder's type, but a redex pairs each leading binder with the argument
    /// it is applied to, which recovers the omitted type **locally**:
    ///
    /// - an `Abst { ty: None }` applied to a *term* arg `% t` is `fun (x:T) => …`
    ///   with `T = infer_type(t)` (the de Bruijn `Bound` occurrences of `x` in the
    ///   body resolve against this `ProofTerm` binder);
    /// - an `AbsP { h: None }` applied to a *proof* arg `%% q` is `fun (h:A) => …`
    ///   with `A` recovered from `q`'s proposition when statically derivable
    ///   ([`Self::proof_prop`]); otherwise from the leading-binder queue.
    ///
    /// Binders beyond the spine (a partial redex) fall back to the normal
    /// binder translation (queue-based recovery), and any spine arguments beyond
    /// the binders are applied verbatim. The kernel β-reduces and re-checks the
    /// whole term, so a wrong type recovery is rejected, never miscounted.
    pub(crate) fn translate_redex(
        &mut self,
        head: &IsaProof,
        spine: &[SpineArg],
        closure: &Closure,
        binders: &mut Vec<Binder>,
    ) -> Result<Expr, TranslateError> {
        // First, β-reduce as many leading (binder, arg) pairs as match at the
        // IsaProof level: substituting the argument into the body eliminates the
        // binder — and crucially its *missing* type annotation — without needing
        // to recover it. We reduce the contiguous prefix of binders paired with a
        // matching-kind argument, then translate the reduced proof applied to any
        // leftover arguments. This is soundness-neutral (the kernel performs the
        // same reduction), so it is preferred over type recovery when applicable.
        {
            let mut cur = head.clone();
            let mut reduced = 0usize;
            while reduced < spine.len() {
                match beta_step(&cur, &spine[reduced]) {
                    Some(next) => {
                        cur = next;
                        reduced += 1;
                    }
                    None => break,
                }
                // A β-step whose substitution exhausted the per-line budget
                // latched the poison flag and returned a partial (discarded)
                // tree — reject the line now instead of translating garbage or
                // grinding further quadratic clones.
                if let Some(budget) = subst_poison_budget() {
                    return Err(TranslateError::BudgetExceeded(budget));
                }
            }
            if reduced > 0 {
                // Translate the reduced body, then apply the remaining args.
                let mut e = self.translate_proof(&cur, closure, binders)?;
                for arg in &spine[reduced..] {
                    e = match arg {
                        SpineArg::Term(t) => Expr::app(e, self.embed_term(t, binders)?),
                        SpineArg::Proof(pr) => {
                            Expr::app(e, self.translate_proof(pr, closure, binders)?)
                        }
                    };
                }
                return Ok(e);
            }
        }

        // Peel the leading binders that are paired with a spine argument, pushing
        // each recovered binder onto the de Bruijn context (so the body's `Bound`
        // / `PBound` occurrences resolve) and recording its clean type. We then
        // build the nested lambda and apply the FULL spine — i.e. reconstruct the
        // redex `(λ…λ. body) arg₀ arg₁ …` verbatim, which the kernel β-reduces
        // and re-checks. The arguments are used *both* to recover the omitted
        // binder types *and* (still) as the application operands.
        let mut layers: Vec<Expr> = Vec::new();
        let mut pushed = 0usize;
        let mut cur = head;
        let mut idx = 0usize;
        let result = loop {
            match cur {
                IsaProof::Abst { ty, b } if idx < spine.len() => {
                    let SpineArg::Term(t) = &spine[idx] else {
                        break self.translate_proof(cur, closure, binders);
                    };
                    let dom = match ty {
                        Some(t) => self.embed_type(t)?,
                        None => self.infer_type(t, binders)?,
                    };
                    binders.push(Binder {
                        kind: BKind::ProofTerm,
                        ty: dom.clone(),
                    });
                    pushed += 1;
                    layers.push(dom);
                    idx += 1;
                    cur = b;
                }
                IsaProof::AbsP { h, b } if idx < spine.len() => {
                    let SpineArg::Proof(q) = &spine[idx] else {
                        break self.translate_proof(cur, closure, binders);
                    };
                    let dom = match h {
                        Some(hyp) => Some(self.embed_term(hyp, binders)?),
                        None => self.proof_prop(q, binders)?,
                    };
                    let Some(dom) = dom else {
                        // Could not recover the hypothesis type locally; fall back
                        // to translating the remaining binder+body as a unit, then
                        // applying the spine below (the original redex behavior).
                        break self.translate_proof(cur, closure, binders);
                    };
                    binders.push(Binder {
                        kind: BKind::Proof,
                        ty: dom.clone(),
                    });
                    pushed += 1;
                    layers.push(dom);
                    idx += 1;
                    cur = b;
                }
                _ => break self.translate_proof(cur, closure, binders),
            }
        };
        // Unwind the binder context regardless of success.
        for _ in 0..pushed {
            binders.pop();
        }
        let mut body = result?;
        // Re-wrap the recovered binders (innermost recovered = last in `layers`).
        for dom in layers.into_iter().rev() {
            body = Expr::lam(BinderInfo::Default, dom, body);
        }
        // Apply the FULL spine: the consumed args drive the recovered β-redex,
        // and any remaining args apply verbatim. (When a binder fell back above,
        // its arg is among these and is applied to the translated binder+body.)
        for arg in spine {
            body = match arg {
                SpineArg::Term(t) => Expr::app(body, self.embed_term(t, binders)?),
                SpineArg::Proof(pr) => Expr::app(body, self.translate_proof(pr, closure, binders)?),
            };
        }
        Ok(body)
    }

    /// Translate a proof argument whose **expected proposition** (`expected`) is
    /// known from the enclosing application's telescope. When the argument is a
    /// raw structural binder whose type the export omits — `AbsP { h: None }`
    /// (discharging `A ⟹ B`) or `Abst { ty: None }` (a `⋀x:T.` binder) — and
    /// `expected` is the matching `Pi` type, we recover the binder's domain from
    /// `expected` and recurse into the body with the (instantiated) codomain as
    /// the new expectation. This is the bidirectional analogue of the leading
    /// queue/redex recovery, used at argument positions where the proof body
    /// alone does not pin the binder type. Any other shape falls back to the
    /// plain [`Self::translate_proof`]. The kernel re-checks the result, so a
    /// wrong recovery is rejected, never miscounted.
    pub(crate) fn translate_proof_expecting(
        &mut self,
        pr: &IsaProof,
        expected: &Expr,
        closure: &Closure,
        binders: &mut Vec<Binder>,
    ) -> Result<Expr, TranslateError> {
        // Shares the per-LINE node budget with [`Self::translate_proof`]: the
        // bidirectional expecting channels recurse through their own inner
        // dispatch, so an uncounted tower here would evade the runaway guard.
        if let Some(budget) = bump_translate_steps() {
            return Err(TranslateError::BudgetExceeded(budget));
        }
        match self.translate_proof_expecting_inner(pr, expected, closure, binders) {
            Ok(e) => Ok(e),
            Err(e) => {
                // **Dictionary-glue recovery** (see [`Self::dict_glue_recover`]): a
                // failed argument whose expectation is a saturated `@Eq α L R` and
                // whose recorded proof is an equational-glue chain over registered
                // `…_dict` dictionary axioms (or a `Pure.transitive` with one such
                // glue leg) proves the expectation by `@Eq.refl α L` / the other
                // leg — genuine under the `method_unfold` embedding (the glue's
                // two sides are definitionally equal), kernel-re-checked against
                // the consumer's exact expectation. Attempted only AFTER the
                // forward translation fails (strictly additive), and only for
                // dict-bearing glue (any other failure keeps its honest error).
                match self.dict_glue_recover(pr, expected, closure, binders)? {
                    Some(p) => Ok(p),
                    None => Err(e),
                }
            }
        }
    }

    /// The forward body of [`Self::translate_proof_expecting`] (the shape-directed
    /// binder/reference recovery), split out so the dictionary-glue collapse can
    /// run as a fallback around every recursion level.
    fn translate_proof_expecting_inner(
        &mut self,
        pr: &IsaProof,
        expected: &Expr,
        closure: &Closure,
        binders: &mut Vec<Binder>,
    ) -> Result<Expr, TranslateError> {
        use clean_kernel::expr::ExprKind;
        match pr {
            IsaProof::AbsP { h, b } => {
                let ExprKind::Pi(_, edom, ecod) = expected.kind() else {
                    // Falls back to the plain translation, whose implicit
                    // sort-hypothesis elision arm handles an `AbsP` discharging
                    // a constraint the (non-Pi) expectation does not spell.
                    return self.translate_proof(pr, closure, binders);
                };
                // **Implicit sort-hypothesis elision**, expecting-side: the
                // recorded `AbsP` discharges a sort-constraint hypothesis
                // (`OFCLASS`/`type_class`) that the expected proposition does
                // NOT spell — its Pi domain is neither `True` nor a
                // class-membership def-const application. Emitting the lambda
                // would insert a premise the expectation lacks, so the binder
                // is elided (an `ElidedSortHyp` slot; `PBound` references
                // become the membership witness) and the body is translated
                // against the SAME expectation. Gated exactly like the
                // plain-side arm (`zproof_mode` + `class_membership`);
                // kernel-re-checked.
                if self.zproof_mode && self.class_membership {
                    if let Some(hyp) = h.as_ref() {
                        let spelled = self.stmt_premises.iter().any(|t| t == hyp);
                        if !spelled
                            && is_sort_hyp_term(hyp)
                            && !expected_dom_spells_sort_premise(edom)
                        {
                            let dom = self.embed_term(hyp, binders)?;
                            binders.push(Binder {
                                kind: BKind::ElidedSortHyp,
                                ty: dom,
                            });
                            let body =
                                self.translate_proof_expecting(b, expected, closure, binders);
                            binders.pop();
                            return body;
                        }
                    }
                }
                let dom = match h {
                    Some(hyp) => self.embed_term(hyp, binders)?,
                    None => (**edom).clone(),
                };
                binders.push(Binder {
                    kind: BKind::Proof,
                    ty: dom.clone(),
                });
                // The codomain may reference the binder; instantiate it with the
                // binder's fvar-free bvar(0) view via a fresh body expectation.
                let ecod = (**ecod).clone();
                let body = self.translate_proof_expecting(b, &ecod, closure, binders);
                binders.pop();
                Ok(Expr::lam(BinderInfo::Default, dom, body?))
            }
            IsaProof::Abst { ty, b } => {
                let ExprKind::Pi(_, edom, ecod) = expected.kind() else {
                    return self.translate_proof(pr, closure, binders);
                };
                let dom = match ty {
                    Some(t) => self.embed_type(t)?,
                    None => (**edom).clone(),
                };
                binders.push(Binder {
                    kind: BKind::ProofTerm,
                    ty: dom.clone(),
                });
                let ecod = (**ecod).clone();
                let body = self.translate_proof_expecting(b, &ecod, closure, binders);
                binders.pop();
                Ok(Expr::lam(BinderInfo::Default, dom, body?))
            }
            // A PThm reference — bare or applied to a spine — whose implicit leading
            // *type* instantiations (and any class-def operation binders the spine
            // leaves unfilled) are recovered bidirectionally by unifying the
            // theorem's partially-applied CONCLUSION against the caller's `expected`
            // type. An Isabelle Pure proof spine never records the schematic *type*
            // arguments, and when a leading type variable occurs only in the
            // conclusion (a *phantom* binder, e.g. the let-body result type of
            // `let_weak_cong`) no supplied term argument constrains it — only the
            // expectation does. Routing every applied PThm through
            // [`Self::apply_thm_expecting_with_tables`] solves such phantoms (the buggy
            // `any_in_scope_type` fallback collapsed them onto an existing type).
            // The method falls back to the plain [`Self::apply_thm`] when the
            // expectation does not solve every otherwise-unfilled binder, so no
            // previously-handled reference loses its translation; the kernel
            // re-checks the result against `expected`, so a wrong recovery is
            // rejected — never miscounted.
            // **Mode-seam sort-witness coercion** (dict-impl round): a `PBound`
            // supplied where the expectation (a referenced dependency's stored
            // premise) is the vacuous `True`, but the slot resolves to an ELIDED
            // implicit sort hypothesis — whose witness in a `Real`-membership
            // pass is the real class-membership hypothesis param
            // (`∀(h : c_class α ops)`), structurally NOT `True`. The membership-
            // mode matrix stores each dependency in the FIRST mode the kernel
            // accepts, so a dependency whose spelled `OFCLASS ⟹` premise
            // verified under `Erase` expects `True` while a `Real`-mode consumer
            // holds the real membership — the historical
            // `expected=True got=isabelle.def.<c>_class` reject wall on every
            // `<c>_class.<m>_def` hub (the G2 dict-impl regression class). A
            // premise of `True` is proof-irrelevant: `True.intro` is ALWAYS the
            // canonical inhabitant, so supply it instead of the mismatched
            // witness. Scoped to elided sort-hyp slots (never a real proof
            // binder), and the kernel re-checks the assembled application — a
            // wrong coercion is rejected, never miscounted.
            IsaProof::Bound { i } if *expected == Expr::const_str("True") => {
                match proof_bvar_slot(binders, *i as usize) {
                    Some(PboundSlot::Elided(_)) => Ok(Expr::const_str("True.intro")),
                    // A REAL (spelled) proof binder whose recorded domain is NOT
                    // `True` — e.g. the consumer's own `class.complete_lattice
                    // ops ⟹` locale-predicate hypothesis passed where the
                    // dependency stores the vacuous `True` (the dependency was
                    // accepted via a reflexivity arm that discharges every
                    // leading premise as `True →`, so it PROVES the stronger
                    // premise-free statement). Supplying the mismatched binder
                    // is a guaranteed kernel reject; `True.intro` is the
                    // canonical inhabitant of the expected `True`. When the
                    // binder's own domain IS `True`, keep the bvar reference —
                    // byte-identical to the historical translation.
                    Some(PboundSlot::Bvar(d)) => {
                        let dom_is_true = proof_bvar_ty(binders, *i as usize)
                            .is_some_and(|ty| ty == Expr::const_str("True"));
                        if dom_is_true {
                            Ok(Expr::bvar(d))
                        } else {
                            Ok(Expr::const_str("True.intro"))
                        }
                    }
                    None => self.translate_proof(pr, closure, binders),
                }
            }
            // **Membership-witness re-spelling** (binder-order round): a
            // `PBound` resolving to an ELIDED implicit sort-hypothesis slot,
            // supplied where the dependency's stored premise domain is a
            // *class-membership proposition* (`isabelle.def.<Thy>.<c>_class α
            // ops…`). The slot's own embedding spells the SAME constraint in
            // THIS node's proof-namespace tvars — which the corpus's
            // `<c>_class.<m>_def` hub exports CROSS against the statement
            // namespace on multi-tvar methods, so the slot-keyed witness
            // (`Ctx::sort_hyp_witness` on the slot's prop, the plain-path
            // behaviour) mismatches the dependency's expected premise. The
            // constraint IS the dependency's premise (Isabelle discharged it
            // with exactly this sort hypothesis), so mint the quantified
            // witness at the *expected* proposition — the honest explicit
            // form of the implicit sort constraint, spelled the one way the
            // dependency can consume. When the namespaces coincide the two
            // spellings are equal and the minted param is byte-identical to
            // the historical one. Scoped to membership-shaped expectations
            // with no loose bvars (a quantified hypothesis type must be
            // closed); everything else keeps the plain translation. Gated on
            // [`Ctx::root_lane`] (the dedicated trailing escalation modes) so
            // every historical mode stays byte-identical — the minted witness
            // can be WRONG where the slot-keyed one was right (the measured
            // `<c>_class.axioms` former-KV regression when this arm ran inside
            // the shared `Real` modes). The kernel re-checks the assembled
            // application — never miscounted.
            IsaProof::Bound { i } => {
                if self.root_lane
                    && !expected.has_loose_bvars_quick()
                    && expected_dom_spells_sort_premise(expected)
                {
                    if let Some(PboundSlot::Elided(_)) = proof_bvar_slot(binders, *i as usize) {
                        return Ok(self.sort_hyp_witness(expected));
                    }
                }
                self.translate_proof(pr, closure, binders)
            }
            IsaProof::Thm { .. } | IsaProof::AppP { .. } | IsaProof::AppT { .. } => {
                // **Proof β-redex under expectation** (bidir stage 2): a
                // `(λh:H. b) arg` proof application whose FUNCTION is an
                // explicit-hypothesis `AbsP`. Applying discharges the hypothesis
                // `h`, so the redex proves the SAME conclusion as `b`; thread the
                // caller's `expected` STRAIGHT INTO `b` (with `h : H` in scope) and
                // translate the argument against the discharged hypothesis type
                // `H`. Emitting the redex — instead of plain-translating it, which
                // loses the expectation and lets the interior `Thm` legs
                // manufacture phantom operands from their generic tables (the
                // `expected=Sort got=FVar` reject the census decoded on the
                // let-style discharge chains, e.g. the swap/iff twins) — carries
                // the statement expectation down to those legs so each solves its
                // operands from the expected proposition. The kernel β-reduces and
                // re-checks against `expected`, so a wrong recovery is rejected —
                // never miscounted. Gated on `bidir_tower` (the dedicated trailing
                // modes); declines (falls through to the spine handling) for any
                // non-redex `AppP`/`AppT` or an omitted (`None`) hypothesis, whose
                // domain the result expectation cannot pin.
                if self.bidir_tower {
                    if let IsaProof::AppP { f, a } = pr {
                        if let IsaProof::AbsP { h: Some(hyp), b } = &**f {
                            let dom = self.embed_term(hyp, binders)?;
                            binders.push(Binder {
                                kind: BKind::Proof,
                                ty: dom.clone(),
                            });
                            let body =
                                self.translate_proof_expecting(b, expected, closure, binders);
                            binders.pop();
                            let body = body?;
                            let arg = self.translate_proof_expecting(a, &dom, closure, binders)?;
                            return Ok(Expr::app(Expr::lam(BinderInfo::Default, dom, body), arg));
                        }
                    }
                }
                let (head, spine) = collect_spine(pr);
                let IsaProof::Thm {
                    id, tyinst, tminst, ..
                } = head
                else {
                    // An `Axm`-headed chain whose spine head is a GENERIC
                    // (identity-`tminst`) zproof reference and whose expected
                    // proposition is a known embedded equation `@Eq α l r`: the
                    // recorded tables carry no term operands, so reconstruct the
                    // chain bidirectionally at the CLEAN level from the expected
                    // equation ([`Self::translate_eq_expecting_clean`] — the
                    // `combination`/`reflexive`/`symmetric`/`transitive` chains
                    // referenced inside a specialized theorem's premises). Any
                    // failure falls back to the plain translation unchanged; the
                    // kernel re-checks both.
                    if spine_head_generic_inst(pr) {
                        if let Some((alpha, l, r, _)) = eq_app_three(expected) {
                            if let Ok(Some(e)) = self
                                .translate_eq_expecting_clean(pr, &alpha, &l, &r, closure, binders)
                            {
                                return Ok(e);
                            }
                        }
                    }
                    // **`equal_elim` under expectation** (bidir stage 1): an
                    // interior `Pure.equal_elim` node (`A ≡ B ⟹ A ⟹ B`) whose
                    // expected result `B` is the caller's `expected`. Pin the
                    // result by the expectation (statement namespace) and recover
                    // the left operand from the equation premise's own
                    // proposition — instead of the forward handler's recorded
                    // (crossed-namespace) table read that desyncs the operands.
                    // Gated on `bidir_tower` so historical modes stay
                    // byte-identical; declines (falls to the forward handler) on
                    // any shape it does not pin. See [`Ctx::equal_elim_expecting`].
                    if self.bidir_tower {
                        if let IsaProof::Axm { name, tminst, .. } = head {
                            if name == "Pure.equal_elim" {
                                if let Some(e) = self.equal_elim_expecting(
                                    &spine, tminst, expected, closure, binders,
                                )? {
                                    return Ok(e);
                                }
                            }
                        }
                    }
                    return self.translate_proof(pr, closure, binders);
                };
                let entry = closure
                    .get(id)
                    .ok_or(TranslateError::UnresolvedThm(*id))?
                    .clone();
                // Prefer the fully-typed explicit-instantiation specialization
                // (exact), then the bidirectional expecting-driven reconstruction,
                // then the forward implicit path. Legacy references (empty tables)
                // skip straight to the expecting path, unchanged.
                //
                // EXCEPTION: a reference whose tables leave the term operands
                // **generic** ([`insts_generic`] — an identity `tminst`, possibly
                // under genuinely-instantiated types) records no actual witnesses —
                // Isabelle left the reference schematic, and the real instantiation
                // is pinned only by the surrounding inference (here: the caller's
                // `expected` proposition). Filling the generic entries verbatim
                // manufactures fresh unconstrained parameters (`?x.0 ↦ param x.0`)
                // that the kernel then rejects, so route these through the
                // bidirectional `apply_thm_expecting_with_tables` instead, which solves the
                // binders by unifying the referenced conclusion against `expected`.
                // When the consumer genuinely shares the schematic (a real identity
                // use), the expectation is stated over those same shared params, so
                // the unification pins the identical instantiation — conservative
                // either way, and the kernel re-checks the result.
                // **Expectation-first Thm-leg operand pinning** (bidir stage 1):
                // inside the equational-tower lane a `Thm` LEG reached under a
                // fully-pinned equational expectation (`combination`/`transitive`/
                // `symmetric`/`equal_elim` operand) must take its operands from the
                // EXPECTED type, not from its recorded (box-namespace) `tyinst`/
                // `tminst` tables — a genuinely-instantiated leg's recorded operands
                // are spelled in the derivation box's namespace and desync against
                // the consumer statement (`Eq FVar got=Eq Prop <concrete>` — the
                // reject census signature). Try the fully-pinned solve FIRST
                // ([`Self::apply_thm_expecting_solved`], which declines to `None`
                // unless the expectation solves EVERY binder); only if it declines
                // do we run the historical explicit-then-forward order below. Gated
                // on `bidir_tower` so every historical mode (and the `root_expecting`
                // path) stays byte-identical; the kernel re-checks the assembled
                // application against `expected`, so a wrong solve is rejected —
                // never miscounted.
                if self.bidir_tower {
                    if let Some(e) = self.apply_thm_expecting_solved(
                        &entry, &spine, expected, tminst, None, closure, binders,
                    )? {
                        return Ok(e);
                    }
                }
                if (!tyinst.is_empty() || !tminst.is_empty()) && !insts_generic(tyinst, tminst) {
                    if let Some(e) =
                        self.apply_thm_explicit(&entry, tyinst, tminst, &spine, closure, binders)?
                    {
                        return Ok(e);
                    }
                }
                self.apply_thm_expecting_with_tables(
                    &entry, &spine, expected, tminst, closure, binders,
                )
            }
            // **OfClass→membership superclass projection**: an `IsaProof::OfClass`
            // sort-witness leaf reached under a class-membership expectation (the
            // `apply_thm_explicit`/`apply_thm_expecting_with_tables` premise-argument path threads
            // the referenced telescope's ground binder domain here as `expected`). The
            // fall-through ([`Self::translate_proof`]) mints the vacuous `True.intro`
            // — correct only where `expected` IS `True`. Under a `Real`-membership
            // expectation the kernel demands the actual `c_class α ops` membership,
            // which is projectable from an in-scope SUBCLASS membership hypothesis via
            // `And.left`/`And.right` (`conjunctionD1`/`D2`): e.g. `order_class α le lt`
            // δ-unfolds to `And (preorder_class α le lt) …`, so the
            // `ofclass[preorder,'a]` super-leg is the `And.left` of the in-scope
            // `order_class` premise — the residual `expected=<c>_class got=True`
            // blocker of the `contains-free-var` Orderings family (s110344, s163466,
            // s164374, …). Gated (in [`Ctx::project_ofclass_membership`]) on `expected`
            // being a non-`True` registered class membership AND an in-scope proof
            // hypothesis projecting it: a `True`-expectation OfClass keeps `True.intro`
            // byte-identical, and a real-membership `True.intro` was ALWAYS a
            // guaranteed kernel reject (`True : True` where `<c>_class` is demanded),
            // so the arm can only turn a rejecting line into an accepting one —
            // strictly additive, never pre-empting a verified line. The kernel
            // re-checks `proof : expected`, so a wrong projection is rejected — never
            // miscounted. Falls through to `True.intro` when no in-scope hypothesis
            // projects it.
            IsaProof::OfClass { .. } => {
                if let Some(p) = self.project_ofclass_membership(expected, binders) {
                    return Ok(p);
                }
                self.translate_proof(pr, closure, binders)
            }
            _ => self.translate_proof(pr, closure, binders),
        }
    }
}
