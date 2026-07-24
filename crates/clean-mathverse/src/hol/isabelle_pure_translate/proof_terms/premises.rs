// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `impl Ctx` statement-level derivations: `prove_from_premises[_inner]` (the
//! premise-identity / conclusion-reflexivity / subst / connective-elim / def-unfold
//! arms) and `prove_classical_rule`. Split out of the original `proof_terms`
//! module's second `impl Ctx` block verbatim.

use super::super::super::isabelle_pure::IsaTerm;
use super::super::*;
use super::*;
use clean_kernel::expr::FVarId;
use clean_kernel::{BinderInfo, Expr};

impl Ctx {
    /// Best-effort proof of an implication chain `A₁ ⟹ … ⟹ Aₙ ⟹ C` whose raw
    /// proof body discharges internal (non-statement) hypotheses we cannot
    /// recover, BUT whose conclusion is provable *directly from the discharged
    /// premises* without using the omitted body. Two cases, both kernel-checked:
    ///
    /// - **premise-identity**: the conclusion `C` embeds identically to one of
    ///   the premises `Aᵢ` (e.g. `(False ≡ HOL.False) ⟹ (False ≡ ∀P.P)`, where
    ///   `HOL.False` and `∀P.P` have the *same* embedding) → `fun a₁ … aₙ => aᵢ`.
    /// - **conclusion-reflexivity**: the conclusion embeds to a syntactically
    ///   reflexive `@Eq α t t` → `fun a₁ … aₙ => @Eq.refl α t`.
    ///
    /// Returns `None` when neither case applies (so the caller keeps the original
    /// error). The kernel re-checks the built term against the embedded statement
    /// type, so a wrong guess is rejected — never miscounted.
    pub(crate) fn prove_from_premises(
        &mut self,
        prop: &IsaTerm,
    ) -> Result<Option<Expr>, TranslateError> {
        self.prove_from_premises_inner(prop, true)
    }

    /// As [`Self::prove_from_premises`] but, when `allow_def_unfold` is `false`,
    /// only the **pure** structural arms (premise-identity, conclusion-reflexivity)
    /// are attempted — the definitional-unfold arm (which is a heuristic that
    /// prefers the recorded proof when it translates) is skipped. Used by the
    /// before-`translate_proof` short-circuit ([`prove_from_premises_first`]).
    pub(crate) fn prove_from_premises_inner(
        &mut self,
        prop: &IsaTerm,
        allow_def_unfold: bool,
    ) -> Result<Option<Expr>, TranslateError> {
        // Peel the leading premises and the final conclusion, embedding each
        // under the accumulating premise binder context (premises are `Prop`s,
        // bound by `Proof` binders).
        let mut premise_terms: Vec<&IsaTerm> = Vec::new();
        let mut cur = prop;
        while let Some((lhs, rhs)) = split_pure_imp(cur) {
            premise_terms.push(lhs);
            cur = rhs;
        }
        if premise_terms.is_empty() {
            return Ok(None);
        }
        let conclusion = strip_prop_wrappers(cur);

        let mut binders: Vec<Binder> = Vec::new();
        let mut premise_tys: Vec<Expr> = Vec::new();
        for p in &premise_terms {
            let ty = self.embed_term(p, &mut binders)?;
            binders.push(Binder {
                kind: BKind::Proof,
                ty: ty.clone(),
            });
            premise_tys.push(ty);
        }
        let concl_e = self.embed_term(conclusion, &mut binders)?;

        // Body under the n premise binders (innermost premise = bvar 0).
        let n = premise_tys.len();
        let body = if let Some(pos) = premise_tys.iter().position(|t| *t == concl_e) {
            // premise-identity: the (n-1-pos)-th de Bruijn index from the top.
            Expr::bvar((n - 1 - pos) as u32)
        } else if let Some((alpha, t)) = reflexive_eq_parts(&concl_e) {
            // conclusion-reflexivity.
            Expr::apps(
                Expr::const_str_levels("Eq.refl", vec![obj_level()]),
                [alpha, t],
            )
        } else if let Some(d) = subst_elim_body(&premise_tys, &concl_e, n) {
            // substitution / equality-elimination: the conclusion `motive b`
            // follows from a `motive a` premise and an equation premise relating
            // `a` and `b` (either direction), by `@Eq.subst`. This is the shape of
            // HOL's `subst`/`iffD1`/`iffD2`/`eqTrueE`-style derived rules — proved
            // here directly from the discharged premises regardless of how Isabelle
            // recorded the (intricate, def-raw) proof. The kernel re-checks the
            // `Eq.subst` against the embedded statement, so a wrong match is
            // rejected — never miscounted.
            d
        } else if let Some(d) = connective_elim_body(&premise_tys, &concl_e, n) {
            // connective elimination via the impredicative encoding: a premise
            // `conj P Q` / `disj P Q` (registered as a defeq-unfolding `Definition`,
            // `conj P Q ≡ ∀C.(P→Q→C)→C`, `disj P Q ≡ ∀C.(P→C)→(B→C)→C`) is itself a
            // generalized eliminator, so HOL's `conjunct1`/`conjunct2`/`conjE`/
            // `disjE` follow by *applying* the encoded hypothesis to the goal `R`
            // and the case proofs. Proved directly from the discharged premises;
            // the kernel re-checks (unfolding the connective definition by defeq).
            d
        } else if allow_def_unfold {
            if let Some(d) = premise_instantiation_body(&premise_tys, &concl_e, n) {
                // **Premise instantiation / application** (keystone round):
                // the conclusion follows from a premise by APPLYING it —
                // universal instantiation (`(∀y. P y) ⟹ P x`: the `HOL.All`
                // premise embeds as a clean `Pi`, so `h x` proves `P x`, with
                // `x` recovered by a ONE-HOLE first-order match of the premise
                // codomain against the conclusion) and modus ponens
                // (`(A → B) ⟹ A ⟹ B`: `h h_A`), chained through
                // non-dependent steps. The shape of the anonymous Pure
                // meta-wrappers (`spec`/`mp`-style) the class package routes
                // essentially every HOL proof through — the s73744 keystone
                // the cascade-weight analyzer measured blocking 88 % of all
                // rejects. FALLBACK-ONLY (this `allow_def_unfold` region is
                // never reached by the pre-translate short-circuit), so
                // previously-verified lines are structurally untouched; the
                // kernel re-checks the application, so a wrong recovery is
                // rejected — never miscounted.
                d
            } else if let Some(budget) = super::super::premise_budget_exhausted() {
                // The premise-instantiation search hit its deterministic step
                // budget ([`PREMISE_STEP_BUDGET_DEFAULT`] / `ISA_PREMISE_STEP_BUDGET`)
                // — a pathological, effectively-unbounded premise shape (the
                // v3.2-grand 5-hour single-line spin). Reject the line HONESTLY and
                // fast under a distinct `premise-budget-cut` bucket rather than
                // spinning; the recorded proof already failed to reach this
                // fallback, so no KV line is affected. Mirrors the translate-node
                // budget's [`TranslateError::BudgetExceeded`] cut.
                return Err(TranslateError::PremiseBudgetExceeded(budget));
            } else if let Some(d) = def_unfold_body(&premise_tys, &concl_e, n) {
                // definitional unfolding via the single eq premise `c ≡ HOL.c`.
                d
            } else {
                return Ok(None);
            }
        } else {
            return Ok(None);
        };

        // Wrap the body in the premise lambdas (outermost premise binds first).
        let mut e = body;
        for ty in premise_tys.into_iter().rev() {
            e = Expr::lam(BinderInfo::Default, ty, e);
        }
        Ok(Some(e))
    }

    /// **Membership-introduction seam** (seam-matrix round): a statement-level,
    /// premise-driven proof of a theorem whose conclusion is the **real class
    /// membership** `c_class α ops` of a *registered* structured class — the
    /// `c_class.intro_of_class` / class-arity family. In the `Real`-membership
    /// pass the conclusion embeds (via [`Ctx::embed_class_membership`]) to the
    /// class def-const applied to the object type and the operations
    /// (`isabelle.def.<c_class> α extra… op₁…opₙ`), whereas the recorded proof —
    /// a leading sort-`AbsP` chain over an arity `Thm` whose own stored
    /// conclusion was accepted under `Erase` — reconstructs to the vacuous
    /// `True`, the dominant `expected=Pi[k]->isabelle.def.<c>_class got=Pi[k]->
    /// True` reject wall (every `<c>.intro_of_class`).
    ///
    /// The class def-const δ-unfolds to the class **body** `B` — a
    /// `Pure.conjunction` (`→ And`) / `HOL.type_class` (`→ True`) tree of exactly
    /// the memberships/axioms the intro discharges as its `⟹` premises. So we
    /// β-reduce the registered [`ClassDefInfo::def_value`] at the conclusion's
    /// use-site arguments to that concrete `B` (β-reduction is pure — no kernel
    /// environment needed) and assemble a witness structurally:
    ///   - a `True` conjunct → `True.intro`;
    ///   - an `And P Q` node → `And.intro P Q ⟨P⟩ ⟨Q⟩`;
    ///   - a leaf that equals one of the discharged premises → that premise's
    ///     bound proof variable.
    /// Any leaf that is none of these makes the whole build decline (`Ok(None)`,
    /// caller keeps its honest error) — strictly additive: attempted only on the
    /// post-`translate_proof` fallback path (the recorded proof already failed),
    /// so no previously-verifying translation changes. Every conjunct is a
    /// genuine, distinct proposition (the class's real axioms — never a `B = B`
    /// tautology), and the kernel re-checks the assembled term against the stored
    /// membership statement (δ-unfolding the def-const), so a wrong assembly is
    /// rejected — never miscounted. Foundational closure (`And.intro`/`True.intro`
    /// only).
    pub(crate) fn prove_class_membership_intro(
        &mut self,
        prop: &IsaTerm,
    ) -> Result<Option<Expr>, TranslateError> {
        use clean_kernel::expr::ExprKind;
        // Only the `Real`-membership pass embeds the conclusion to the def-const;
        // under `Erase` it is `True` and the ordinary arms already discharge it.
        if !self.class_membership {
            return Ok(None);
        }
        // Peel the leading `⟹` premises and embed each under an accumulating
        // proof-binder context (premises are `Prop`s), exactly as
        // [`Self::prove_from_premises_inner`] does.
        let mut premise_terms: Vec<&IsaTerm> = Vec::new();
        let mut cur = prop;
        while let Some((lhs, rhs)) = split_pure_imp(cur) {
            premise_terms.push(lhs);
            cur = rhs;
        }
        if premise_terms.is_empty() {
            return Ok(None);
        }
        let conclusion = strip_prop_wrappers(cur);

        let mut binders: Vec<Binder> = Vec::new();
        let mut premise_tys: Vec<Expr> = Vec::new();
        for p in &premise_terms {
            let ty = self.embed_term(p, &mut binders)?;
            binders.push(Binder {
                kind: BKind::Proof,
                ty: ty.clone(),
            });
            premise_tys.push(ty);
        }
        let concl_e = self.embed_term(conclusion, &mut binders)?;

        // The conclusion must be a registered class membership: a def-const
        // application `isabelle.def.<c_class> α extra… op₁…opₙ` whose head names a
        // class in the registry.
        let head = concl_e.get_app_fn();
        let clean_kernel::expr::ExprKind::Const(def_name, _) = head.kind() else {
            return Ok(None);
        };
        let def_name = def_name.to_string();
        let Some(info) = self
            .class_registry
            .values()
            .find(|i| i.def_name == def_name)
            .cloned()
        else {
            return Ok(None);
        };
        let args: Vec<Expr> = concl_e.get_app_args().into_iter().cloned().collect();

        // β-reduce the class definition's value at the use-site arguments to the
        // concrete class body `B`. A binder/argument-count surprise (stale
        // metadata) declines rather than mis-builds.
        let mut body = info.def_value.clone();
        for arg in &args {
            let clean_kernel::expr::ExprKind::Lam(_, _, b) = body.kind() else {
                return Ok(None);
            };
            body = b.instantiate(arg);
        }

        // Assemble the membership witness from the body's `And`/`True`/premise
        // structure. Two escalating builders, both strictly additive (kernel
        // re-checks the assembled term against the stored membership statement):
        //
        // 1. the **local** builder ([`build_membership_witness`]) — `True →
        //    True.intro`, `And → And.intro`, and a leaf equal to a discharged
        //    premise → that premise var. Pass-independent (no `instance_unfold`).
        // 2. the **locale-bridge** builder ([`build_membership_intro_rec`],
        //    unfold pass only) — the seam this round closes: a `c_class.
        //    intro_of_class` discharges a *single* locale-predicate premise
        //    `class.C ops` (never per-superclass `OFCLASS` premises), while the
        //    class body `B` is a conjunction of superclass **memberships**
        //    (`isabelle.def.<S>_class α ops`) plus the class's own axioms
        //    predicate (`isabelle.polyinst.class.<C>_axioms α ops`). The two
        //    spellings never leaf-match, so builder 1 declines. Builder 2 threads
        //    the locale premise: a superclass-membership conjunct is expanded
        //    structurally (β-reducing that superclass's own def value and
        //    recursing — bottoming out at base memberships `→ True.intro`), and
        //    an axioms/locale conjunct is EXTRACTED from the locale premise by the
        //    r10 impredicative-`conj_def` projection ([`Ctx::extract_conjunct`]),
        //    which δ-unfolds the premise's `polyinst.class.<C>` def-const and
        //    selects the matching conjunct. Every conjunct stays a genuine, real
        //    proposition; the kernel re-checks the whole assembly (δ-unfolding
        //    both the membership def-const and the locale def-const), so a wrong
        //    thread is rejected — never miscounted.
        let n = premise_tys.len();
        let witness = if let Some(w) = Self::build_membership_witness(&body, &premise_tys, n) {
            w
        } else if self.instance_unfold {
            // Collect the discharged premises that are registered locale
            // predicates (`class.C ops`) — the projection sources. Each carries
            // its ISA argument spine (for the conjunct specialization) and its
            // bound proof variable (`bvar(n-1-idx)`, mirroring the premise-lambda
            // wrap below).
            let mut locale_prems: Vec<(String, Vec<IsaTerm>, Expr)> = Vec::new();
            for (idx, pt) in premise_terms.iter().enumerate() {
                let (phead, pargs) = term_app_spine(strip_prop_wrappers(pt));
                if let IsaTerm::Const { n: c_name, .. } = phead {
                    if self.poly_inst_registry.contains_key(c_name) {
                        let pargs_owned: Vec<IsaTerm> = pargs.iter().map(|&a| a.clone()).collect();
                        locale_prems.push((
                            c_name.clone(),
                            pargs_owned,
                            Expr::bvar((n - 1 - idx) as u32),
                        ));
                    }
                }
            }
            match self.build_membership_intro_rec(
                &body,
                &premise_tys,
                n,
                &locale_prems,
                &mut binders,
                0,
            )? {
                Some(w) => w,
                None => return Ok(None),
            }
        } else {
            return Ok(None);
        };

        // Wrap in the premise lambdas (outermost premise binds first).
        let mut e = witness;
        for ty in premise_tys.into_iter().rev() {
            e = Expr::lam(BinderInfo::Default, ty, e);
        }
        Ok(Some(e))
    }

    /// Build a proof of the (β-reduced) class body `body` from the `n` discharged
    /// premise types (innermost premise = de Bruijn 0), by structural recursion:
    /// `True → True.intro`, `And P Q → And.intro P Q ⟨P⟩ ⟨Q⟩`, and a leaf equal to
    /// premise `i` → its bound proof variable `bvar(n-1-i)`. Returns `None` for a
    /// leaf that is none of these (the caller then declines the whole
    /// membership-intro build — never a partial/unsound witness). See
    /// [`Ctx::prove_class_membership_intro`].
    fn build_membership_witness(body: &Expr, premise_tys: &[Expr], n: usize) -> Option<Expr> {
        use clean_kernel::expr::ExprKind;
        // A premise-matching leaf (checked first so a premise whose own type is
        // `True`/`And`-shaped is still discharged by its hypothesis, not rebuilt).
        if let Some(pos) = premise_tys.iter().position(|t| t == body) {
            return Some(Expr::bvar((n - 1 - pos) as u32));
        }
        // Vacuous `True` conjunct.
        if *body == Expr::const_str("True") {
            return Some(Expr::const_str("True.intro"));
        }
        // `And P Q` node (`App(App(Const "And", P), Q)`).
        if let clean_kernel::expr::ExprKind::App(app_a, q) = body.kind() {
            if let clean_kernel::expr::ExprKind::App(and_head, p) = app_a.kind() {
                if matches!(and_head.kind(), clean_kernel::expr::ExprKind::Const(n2, _) if *n2 == clean_kernel::name::Name::from_string("And"))
                {
                    let hp = Self::build_membership_witness(p, premise_tys, n)?;
                    let hq = Self::build_membership_witness(q, premise_tys, n)?;
                    return Some(Expr::apps(
                        Expr::const_str("And.intro"),
                        [(**p).clone(), (**q).clone(), hp, hq],
                    ));
                }
            }
        }
        None
    }

    /// The **locale-bridge** membership builder (unfold pass, [`Ctx::
    /// prove_class_membership_intro`] builder 2): assemble a proof of the
    /// (β-reduced, current-pass-embedded) class body `body` by threading the
    /// registered locale-predicate premises `locale_prems` (`class.C ops`), whose
    /// def-const δ-unfolds to the conjunction of the class's superclass locales +
    /// axioms predicate. Structural recursion:
    ///   - a leaf equal to a discharged premise → that premise var;
    ///   - `True` → `True.intro`;
    ///   - `And P Q` → `And.intro P Q ⟨P⟩ ⟨Q⟩` (recurse both);
    ///   - a **superclass membership** leaf `isabelle.def.<S>_class α ops` (head
    ///     names a registered class) → β-reduce that superclass's own `def_value`
    ///     at the leaf's arguments to its concrete body `B_S` and recurse — the
    ///     proof of `B_S` is a proof of the membership by δ (base sorts bottom out
    ///     at `True.intro`);
    ///   - any other leaf (an axioms / locale-predicate conjunct) → PROJECT it from
    ///     a locale premise via [`Self::project_locale_leaf`] (the full-tree
    ///     impredicative-`conj_def` projection, which descends left-nested
    ///     `HOL.conj` sub-trees) then [`Self::extract_conjunct`] (the r10
    ///     projection with schematic-instance discharge): both descend the
    ///     premise's δ-unfolded conjunction and select the conjunct equal to the
    ///     leaf.
    /// Returns `None` if any leaf cannot be discharged (the caller declines — never
    /// a partial witness). `depth` guards against a pathological superclass
    /// re-expansion. FAITHFUL: distinct real conjuncts, `And.intro`/`True.intro`/
    /// impredicative-`conj_def` closure (foundational); the kernel re-checks the
    /// whole assembly, so a wrong thread is rejected — never miscounted.
    fn build_membership_intro_rec(
        &mut self,
        body: &Expr,
        premise_tys: &[Expr],
        n: usize,
        locale_prems: &[(String, Vec<IsaTerm>, Expr)],
        binders: &mut Vec<Binder>,
        depth: usize,
    ) -> Result<Option<Expr>, TranslateError> {
        use clean_kernel::expr::ExprKind;
        if depth > 64 {
            return Ok(None);
        }
        // A premise-matching leaf (checked first so a premise whose own type is
        // `True`/`And`/membership-shaped is discharged by its hypothesis).
        if let Some(pos) = premise_tys.iter().position(|t| t == body) {
            return Ok(Some(Expr::bvar((n - 1 - pos) as u32)));
        }
        // Vacuous `True` conjunct.
        if *body == Expr::const_str("True") {
            return Ok(Some(Expr::const_str("True.intro")));
        }
        // `And P Q` node → recurse both, `And.intro`.
        if let clean_kernel::expr::ExprKind::App(app_a, q) = body.kind() {
            if let clean_kernel::expr::ExprKind::App(and_head, p) = app_a.kind() {
                if matches!(and_head.kind(), clean_kernel::expr::ExprKind::Const(nm, _) if *nm == clean_kernel::name::Name::from_string("And"))
                {
                    let Some(hp) = self.build_membership_intro_rec(
                        p,
                        premise_tys,
                        n,
                        locale_prems,
                        binders,
                        depth,
                    )?
                    else {
                        return Ok(None);
                    };
                    let Some(hq) = self.build_membership_intro_rec(
                        q,
                        premise_tys,
                        n,
                        locale_prems,
                        binders,
                        depth,
                    )?
                    else {
                        return Ok(None);
                    };
                    return Ok(Some(Expr::apps(
                        Expr::const_str("And.intro"),
                        [(**p).clone(), (**q).clone(), hp, hq],
                    )));
                }
            }
        }
        // A **superclass membership** leaf `isabelle.def.<S>_class α ops`: expand
        // it structurally by β-reducing that class's own def value at the leaf's
        // arguments (the proof of the expanded body IS a proof of the membership,
        // by δ). This bridges the body's membership spelling to the locale premise
        // without a per-superclass hypothesis.
        let head = body.get_app_fn();
        if let clean_kernel::expr::ExprKind::Const(dn, _) = head.kind() {
            let dn = dn.to_string();
            if let Some(info) = self
                .class_registry
                .values()
                .find(|i| i.def_name == dn)
                .cloned()
            {
                let sub_args: Vec<Expr> = body.get_app_args().into_iter().cloned().collect();
                let mut sub_body = info.def_value.clone();
                for arg in &sub_args {
                    let clean_kernel::expr::ExprKind::Lam(_, _, b) = sub_body.kind() else {
                        return Ok(None);
                    };
                    sub_body = b.instantiate(arg);
                }
                return self.build_membership_intro_rec(
                    &sub_body,
                    premise_tys,
                    n,
                    locale_prems,
                    binders,
                    depth + 1,
                );
            }
        }
        // Any other leaf (an axioms / locale-predicate conjunct): extract it from a
        // locale premise. First the FULL-TREE projector ([`Self::project_locale_leaf`],
        // which descends left-nested `HOL.conj` sub-trees the flat conjunct list
        // leaves opaque), then the r10 [`Self::extract_conjunct`] (which adds the
        // schematic-instance discharge). The kernel re-checks either extraction
        // (δ-unfolding the premise def-const), so a wrong source rejects.
        for (lname, largs, h) in locale_prems {
            if let Some(p) = self.project_locale_leaf(lname, largs, h.clone(), body, binders, 0)? {
                return Ok(Some(p));
            }
            if let Some(p) = self.extract_conjunct(lname, largs, h.clone(), body, binders)? {
                return Ok(Some(p));
            }
        }
        Ok(None)
    }

    /// Full-tree impredicative-`conj_def` projection from a locale-predicate
    /// hypothesis `h : class.<c_name> pargs` to a `target` leaf. The registered
    /// `conjuncts` are the RIGHT-spine-flattened leaves of the def body, so
    /// `class.<c_name>` δ-unfolds to `conj_def(c₀, conj_def(c₁, … cₙ))`; we build
    /// the `And.left`/`And.right` selector chain to each `cₖ` and, for that `cₖ`,
    /// descend via [`Self::descend_conj_node`]. Unlike [`Self::extract_conjunct`]
    /// this reaches leaves behind a **left-nested** `HOL.conj` conjunct
    /// (`(A∧B)∧(C∧D)`, the ring-tower shape `flatten_hol_conjuncts` leaves as an
    /// opaque leaf). Fallback-only (a wrong descent is kernel-rejected, never
    /// displaces a KV). `depth` guards the mutual recursion.
    fn project_locale_leaf(
        &mut self,
        c_name: &str,
        pargs: &[IsaTerm],
        h: Expr,
        target: &Expr,
        binders: &mut Vec<Binder>,
        depth: usize,
    ) -> Result<Option<Expr>, TranslateError> {
        if depth > 96 {
            return Ok(None);
        }
        let Some(info) = self.poly_inst_registry.get(c_name).cloned() else {
            return Ok(None);
        };
        if info.conjuncts.is_empty() || info.arg_vars.len() != pargs.len() {
            return Ok(None);
        }
        let subst: Vec<((String, i64), IsaTerm)> = info
            .arg_vars
            .iter()
            .cloned()
            .zip(pargs.iter().cloned())
            .collect();
        let isa_conjs: Vec<IsaTerm> = info
            .conjuncts
            .iter()
            .map(|cj| subst_isa_vars(cj, &subst))
            .collect();
        let mut conjs: Vec<Expr> = Vec::with_capacity(isa_conjs.len());
        for cj in &isa_conjs {
            conjs.push(self.embed_term(cj, binders)?);
        }
        let n = conjs.len() - 1;
        let mut rest = vec![conjs[n].clone(); conjs.len()];
        for i in (0..n).rev() {
            rest[i] = conj_def(conjs[i].clone(), rest[i + 1].clone());
        }
        for k in 0..conjs.len() {
            let mut hk = h.clone();
            for (j, cj) in conjs.iter().enumerate().take(k) {
                hk = and_right(cj.clone(), rest[j + 1].clone(), hk);
            }
            let proof_k = if k < n {
                and_left(conjs[k].clone(), rest[k + 1].clone(), hk)
            } else {
                hk
            };
            if let Some(p) = self.descend_conj_node(
                &isa_conjs[k],
                &conjs[k],
                proof_k,
                target,
                binders,
                depth + 1,
            )? {
                return Ok(Some(p));
            }
        }
        Ok(None)
    }

    /// Reach `target` from a proof `h : clean_node` (ISA node `isa_node`): a
    /// direct match, a raw `HOL.conj L R` node (split by `And.left`/`And.right`
    /// and recurse both operands — this is what descends the left-nested tree),
    /// or a registered locale predicate (→ [`Self::project_locale_leaf`]).
    /// Returns `None` when `target` is not a leaf of the node's sub-tree.
    fn descend_conj_node(
        &mut self,
        isa_node: &IsaTerm,
        clean_node: &Expr,
        h: Expr,
        target: &Expr,
        binders: &mut Vec<Binder>,
        depth: usize,
    ) -> Result<Option<Expr>, TranslateError> {
        if depth > 96 {
            return Ok(None);
        }
        if clean_node == target {
            return Ok(Some(h));
        }
        let stripped = strip_prop_wrappers(isa_node);
        // Raw `HOL.conj L R` node → `And.left`/`And.right` into both operands.
        if let IsaTerm::App { f, a: r } = stripped {
            if let IsaTerm::App { f: hd, a: l } = f.as_ref() {
                if matches!(hd.as_ref(), IsaTerm::Const { n, .. } if n == "HOL.conj") {
                    let l_e = self.embed_term(l, binders)?;
                    let r_e = self.embed_term(r, binders)?;
                    let p_l = and_left(l_e.clone(), r_e.clone(), h.clone());
                    if let Some(p) =
                        self.descend_conj_node(l, &l_e, p_l, target, binders, depth + 1)?
                    {
                        return Ok(Some(p));
                    }
                    let p_r = and_right(l_e, r_e.clone(), h);
                    if let Some(p) =
                        self.descend_conj_node(r, &r_e, p_r, target, binders, depth + 1)?
                    {
                        return Ok(Some(p));
                    }
                    return Ok(None);
                }
            }
        }
        // Registered locale-predicate node → descend its own conjuncts.
        let (head, args) = term_app_spine(stripped);
        if let IsaTerm::Const { n: sub_name, .. } = head {
            if self.poly_inst_registry.contains_key(sub_name) {
                let args_owned: Vec<IsaTerm> = args.iter().map(|&a| a.clone()).collect();
                let sub_name = sub_name.clone();
                return self.project_locale_leaf(
                    &sub_name,
                    &args_owned,
                    h,
                    target,
                    binders,
                    depth + 1,
                );
            }
        }
        Ok(None)
    }

    /// Statement-level proof of a HOL **classical-reasoning** rule
    /// (`ccontr` / `classical` / `swap` / `eqTrueI`): peel the premise chain,
    /// embed each premise and the conclusion under the accumulating premise binder
    /// context, then hand the embedded shapes to [`classical_rule_proof`], which
    /// builds the proof via `Classical.em` + `propext` (foundational closure)
    /// instead of the intricate recorded def-raw proof. Returns `None` if the
    /// statement is not one of the recognized classical shapes. The kernel
    /// re-checks the produced term against the embedded statement, so a wrong match
    /// is rejected — never miscounted.
    pub(crate) fn prove_classical_rule(
        &mut self,
        prop: &IsaTerm,
    ) -> Result<Option<Expr>, TranslateError> {
        let mut premise_terms: Vec<&IsaTerm> = Vec::new();
        let mut cur = prop;
        while let Some((lhs, rhs)) = split_pure_imp(cur) {
            premise_terms.push(lhs);
            cur = rhs;
        }
        if premise_terms.is_empty() {
            return Ok(None);
        }
        let conclusion = strip_prop_wrappers(cur);

        let mut binders: Vec<Binder> = Vec::new();
        let mut premise_tys: Vec<Expr> = Vec::new();
        for p in &premise_terms {
            let ty = self.embed_term(p, &mut binders)?;
            binders.push(Binder {
                kind: BKind::Proof,
                ty: ty.clone(),
            });
            premise_tys.push(ty);
        }
        let concl_e = self.embed_term(conclusion, &mut binders)?;
        if let Some(p) = classical_rule_proof(&premise_tys, &concl_e) {
            return Ok(Some(p));
        }
        // Existential introduction (`exI`), whose conclusion embeds (via
        // `ex_encoding`) to the impredicative `∀Q. (∀y. p y → Q) → Q` — a shape
        // `classical_rule_proof` does not recognize (it targets `Eq`/`Not`
        // conclusions). Discharged directly from a witnessing premise `p wit`.
        Ok(ex_intro_proof(&premise_tys, &concl_e))
    }
}

/// If `concl` is exactly [`ex_encoding`]`(α, p)` — the impredicative existential
/// `∀(Q:Prop). (∀(y:α). p y → Q) → Q` — return `(p, inner)` where `inner` is the
/// case-hypothesis type `∀(y:α). p y → Q` (the domain of the outer arm, expressed
/// under the single leading `Q:Prop` binder). Recovers the candidate `(α, p)` by
/// structural descent and CONFIRMS the guess by rebuilding `ex_encoding(α, p)` and
/// requiring byte-equality, so a non-`Ex` conclusion never matches.
fn match_ex_encoding(concl: &Expr) -> Option<(Expr, Expr)> {
    use clean_kernel::expr::ExprKind;
    // concl = ∀(Q:Prop). arm
    let ExprKind::Pi(_, dom_q, arm) = concl.kind() else {
        return None;
    };
    if **dom_q != Expr::prop() {
        return None;
    }
    // arm = inner → Q   (Q is `BVar(1)` from arm's codomain)
    let ExprKind::Pi(_, inner, arm_cod) = arm.kind() else {
        return None;
    };
    if **arm_cod != Expr::bvar(1) {
        return None;
    }
    // inner = ∀(y:α). inner_body
    let ExprKind::Pi(_, alpha, inner_body) = inner.kind() else {
        return None;
    };
    // inner_body = (p y) → Q   (Q is `BVar(2)`; `p y = App(p, BVar(0))`)
    let ExprKind::Pi(_, px, inner_cod) = inner_body.kind() else {
        return None;
    };
    if **inner_cod != Expr::bvar(2) {
        return None;
    }
    let ExprKind::App(p, y) = px.kind() else {
        return None;
    };
    if **y != Expr::bvar(0) {
        return None;
    }
    let alpha = (**alpha).clone();
    let p = (**p).clone();
    // Confirm by reconstruction (handles all de Bruijn bookkeeping in one shot).
    if ex_encoding(&alpha, &p) != *concl {
        return None;
    }
    Some((p, (**inner).clone()))
}

/// **Existential introduction** (`exI`: `⟦sort; P x⟧ ⟹ ∃y. P y`) discharged
/// directly from the embedded statement, bypassing the recorded proof (whose
/// `equal_elim` tower leaks a schematic and rejects). The conclusion embeds via
/// [`ex_encoding`] to the impredicative `∀(Q:Prop). (∀(y:α). p y → Q) → Q`; given
/// a premise `p wit` (the witnessing hypothesis), the proof is the pure lambda
///
/// ```text
/// λ(Q:Prop)(k:∀(y:α). p y → Q). k wit hwit
/// ```
///
/// — no axioms. The conclusion is recognized by [`match_ex_encoding`] (a
/// reconstruct-and-compare, so a non-`Ex` conclusion never matches); the witness
/// is recovered from the LAST application premise `App(_, wit)` and
/// SELF-VERIFIED (`p wit ≡β premise`) before committing, so a mismatched witness
/// returns `None` and the recorded proof is kept — regression-safe. Restricted to
/// a closed witness / predicate / premise (the `exI` schema's `P`/`x` are leading
/// schematics → fvars, so this always holds on the target family) which keeps the
/// de Bruijn bookkeeping trivial and the self-check scope-valid. The kernel
/// re-checks the built term against the embedded statement, so a wrong match is
/// rejected — never miscounted. Foundational (pure λ), faithful, strictly
/// additive (reached only where `classical_rule_proof` returns `None`).
fn ex_intro_proof(premise_tys: &[Expr], concl_e: &Expr) -> Option<Expr> {
    use clean_kernel::expr::ExprKind;
    let (p, inner_ty) = match_ex_encoding(concl_e)?;
    if p.has_loose_bvars() {
        return None;
    }
    let n = premise_tys.len();
    // Premise-proof fvar handles (abstracted + wrapped exactly as in
    // `classical_rule_proof`: premise `i` binds to the `i`-th enclosing lambda).
    let prem_fvar = |pos: usize| FVarId::new(0xE10_1000 + pos as u64);
    // Scan premises last-first for a witnessing hypothesis `App(_, wit)` whose
    // predicate reduces to `p` (self-verifying witness recovery).
    for pos in (0..n).rev() {
        let prem = &premise_tys[pos];
        let ExprKind::App(_, wit) = prem.kind() else {
            continue;
        };
        if prem.has_loose_bvars() || wit.has_loose_bvars() {
            continue;
        }
        // `p wit ≡β premise`? (Both closed → the comparison is scope-valid.)
        if beta_normal(&Expr::app(p.clone(), (**wit).clone())) != beta_normal(prem) {
            continue;
        }
        // Body under `[Q, k]`: `k wit hwit`. `wit`/`hwit` are closed, so no
        // lifting is needed; `inner_ty` is already expressed under the leading
        // `Q:Prop` binder, matching the `λ(k:inner_ty)` slot.
        let applied = Expr::app(
            Expr::app(Expr::bvar(0), (**wit).clone()),
            Expr::fvar(prem_fvar(pos)),
        );
        let lam_k = Expr::lam(BinderInfo::Default, inner_ty, applied);
        let mut body = Expr::lam(BinderInfo::Default, Expr::prop(), lam_k);
        // Abstract every premise fvar (innermost-first), then wrap in the premise
        // lambdas (outermost = premise 0), so `prem_fvar(i)` binds correctly.
        for i in 0..n {
            body = body.abstract_fvar(prem_fvar(i));
        }
        for ty in premise_tys.iter().rev() {
            body = Expr::lam(BinderInfo::Default, ty.clone(), body);
        }
        return Some(body);
    }
    None
}

/// [`Ctx::prove_from_premises_inner`]'s **premise-instantiation** arm
/// (quantifier-trio generalization): prove the embedded conclusion from the
/// discharged premises by *applying* them — universal instantiation
/// (`spec`/`allE`/`bspec`), modus ponens (`mp`), and the impredicative
/// existential eliminator (`exE`), chained through non-dependent steps.
///
/// Three shapes the class package routes essentially every HOL proof through,
/// unified by one recursive prover [`prove_goal`]/[`drive_premise`]:
///   - **`allE`** `(∀x. P x) ⟹ (P a ⟹ R) ⟹ R`: the eliminator premise
///     `P a ⟹ R` is driven by discharging its domain `P a` from the `∀`
///     premise (`P a` recovered by a one-hole match of `P`'s codomain), i.e.
///     `h₂ (h₁ a)`.
///   - **`exE`** `(∃x. P x) ⟹ (⋀x. P x ⟹ R) ⟹ R`: the existential premise
///     embeds (via `ex_encoding`) to a genuine `∀(C:Prop). (∀x. P x → C) → C`,
///     so instantiating `C := R` and discharging the case premise gives `h₁ R h₂`.
///   - **`bspec`** `(∀x∈A. P x) ⟹ a ∈ A ⟹ P a`: the `Set.Ball` premise embeds
///     to the β-redex `(λA P. ∀x. A x → P x) A P`, so [`beta_normal`]
///     exposes the `Pi`, `x := a` is recovered by matching, and the membership
///     domain `a ∈ A` is discharged by the second premise.
///
/// All indices are de Bruijn under the `n` premise proof-binders (premise `i` =
/// `BVar(n-1-i)`); embedded schematics are ctx params, so premise types and the
/// conclusion share one closed scope. The kernel re-checks the built term
/// against the embedded statement (β/δ-unfolding as needed), so a wrong
/// recovery is rejected — never miscounted. Foundational (no axioms), faithful,
/// and fallback-only (this region is never reached by the pre-translate
/// short-circuit), so previously-verified lines are structurally untouched.
fn premise_instantiation_body(premise_tys: &[Expr], concl: &Expr, n: usize) -> Option<Expr> {
    // Arm the per-attempt deterministic step budget: the walk below is an
    // exponential premise-application search whose nominal `fuel` does NOT bound
    // a pathological premise shape (the v3.2-grand 5-hour single-line spin). Reset
    // here so the budget covers exactly THIS attempt; every `prove_goal`/
    // `drive_premise` invocation bumps it, and on exhaustion the whole search
    // unwinds to `None` with [`super::super::PREMISE_POISON`] latched — the
    // enclosing `prove_from_premises_inner` turns that into an honest
    // `premise-budget-cut` reject.
    super::super::reset_premise_steps();
    let goal = beta_normal(concl);
    prove_goal(premise_tys, &goal, n, 6)
}

/// Prove `goal` (β-head-normalized) from the `n` discharged premises: a premise
/// whose (β-normalized) type equals `goal` directly, else some premise's
/// application spine [`drive_premise`]d to `goal`. `fuel` bounds the search.
fn prove_goal(premise_tys: &[Expr], goal: &Expr, n: usize, fuel: usize) -> Option<Expr> {
    if fuel == 0 {
        return None;
    }
    // Deterministic step budget (see [`premise_instantiation_body`]): one step per
    // search node. On exhaustion the whole walk unwinds cheaply.
    if !super::super::bump_premise_steps() {
        return None;
    }
    if let Some(pos) = premise_tys.iter().position(|t| beta_normal(t) == *goal) {
        return Some(Expr::bvar((n - 1 - pos) as u32));
    }
    for (i, pty) in premise_tys.iter().enumerate() {
        let head = Expr::bvar((n - 1 - i) as u32);
        if let Some(b) = drive_premise(&beta_normal(pty), goal, head, premise_tys, n, fuel) {
            return Some(b);
        }
    }
    None
}

/// Drive `acc : cur_ty` (β-head-normalized) toward `goal` by applications:
///   - `cur_ty == goal` → `acc` (done);
///   - `cur_ty = Pi(dom, cod)` with `cod` mentioning the bound variable
///     (**universal instantiation**): recover the object argument `x` by a
///     one-hole match of `cod`'s arrow-stripped tail against `goal`, then
///     continue on `cod[x]`;
///   - `cur_ty = Pi(dom, cod)` non-dependent (**modus ponens**): discharge the
///     domain by [`prove_goal`] and continue on `cod`.
/// `fuel` bounds the chain.
fn drive_premise(
    cur_ty: &Expr,
    goal: &Expr,
    acc: Expr,
    premise_tys: &[Expr],
    n: usize,
    fuel: usize,
) -> Option<Expr> {
    if fuel == 0 {
        return None;
    }
    // Deterministic step budget (see [`premise_instantiation_body`]): one step per
    // search node. On exhaustion the whole walk unwinds cheaply.
    if !super::super::bump_premise_steps() {
        return None;
    }
    if *cur_ty == *goal {
        return Some(acc);
    }
    let clean_kernel::expr::ExprKind::Pi(_, dom, cod) = cur_ty.kind() else {
        return None;
    };
    if mentions_bvar(cod, 0) {
        // Universal instantiation. Strip `cod`'s leading (β-normalized) `Pi`s to
        // its tail; the universal variable, `BVar(0)` in `cod`, is `BVar(d)` in
        // the tail after `d` strips. Recover its value by a one-hole match of the
        // tail against `goal` (guarded on a closed goal so the solution — a
        // subterm of `goal` — is expressible in the outer scope). Then continue
        // on `cod[x]`, whose leading arrows are discharged by the mp step.
        if goal.has_loose_bvars() {
            return None;
        }
        let mut tail = beta_normal(cod);
        let mut d: u32 = 0;
        loop {
            let next = match tail.kind() {
                clean_kernel::expr::ExprKind::Pi(_, _, pcod) => Some(beta_normal(pcod)),
                _ => None,
            };
            match next {
                Some(t) => {
                    tail = t;
                    d += 1;
                }
                None => break,
            }
        }
        let x = match_one_hole(&tail, goal, d)?;
        let next_ty = beta_normal(&cod.instantiate(&x));
        return drive_premise(&next_ty, goal, Expr::app(acc, x), premise_tys, n, fuel - 1);
    }
    // Non-dependent step (modus ponens): prove the domain from the premises.
    let arg = prove_goal(premise_tys, &beta_normal(dom), n, fuel - 1)?;
    let next_ty = beta_normal(&cod.instantiate(&arg));
    drive_premise(
        &next_ty,
        goal,
        Expr::app(acc, arg),
        premise_tys,
        n,
        fuel - 1,
    )
}

/// β-head-normalize `e`: repeatedly reduce the head redex
/// `(λx. body) arg rest…` → `body[arg] rest…`. Terminates on well-typed terms
/// (each step removes one application layer).
fn beta_head_normal(e: &Expr) -> Expr {
    let mut cur = e.clone();
    loop {
        let head_is_lam = matches!(
            cur.get_app_fn().kind(),
            clean_kernel::expr::ExprKind::Lam(..)
        );
        if !head_is_lam {
            return cur;
        }
        let clean_kernel::expr::ExprKind::Lam(_, _, body) = cur.get_app_fn().kind() else {
            return cur;
        };
        let args: Vec<Expr> = cur.get_app_args().into_iter().cloned().collect();
        let Some((first, rest)) = args.split_first() else {
            return cur;
        };
        let reduced = body.instantiate(first);
        cur = Expr::apps(reduced, rest.iter().cloned());
    }
}

/// Full **β-normal form** of `e`: head-normalize, then recurse into the
/// resulting binder/spine structure. Terminates on well-typed terms. Used so
/// the prover compares premise and goal shapes up to β — the quantifier
/// encodings leave *nested* redexes (`ex_encoding` builds `∀x. p x → C` where
/// the predicate `p = λy. P y`, so `p x` is a redex the case premise's plain
/// `∀x. P x → C` does not have; `Set.Ball`'s `(λA P. ∀x. A x → P x) A P` leaves
/// `P x` similarly), which head-normalization alone would miss.
fn beta_normal(e: &Expr) -> Expr {
    use clean_kernel::expr::ExprKind;
    let h = beta_head_normal(e);
    match h.kind() {
        ExprKind::Pi(bi, d, c) => Expr::pi(*bi, beta_normal(d), beta_normal(c)),
        ExprKind::Lam(bi, d, c) => Expr::lam(*bi, beta_normal(d), beta_normal(c)),
        ExprKind::App(_, _) => {
            let f = beta_normal(h.get_app_fn());
            let args = h.get_app_args().into_iter().map(beta_normal);
            Expr::apps(f, args)
        }
        _ => h,
    }
}

/// Structural one-hole first-order match: `pat` (under `delta` binders, hole =
/// `BVar(delta)`) against `target`; returns the hole's solution when the rest
/// matches exactly and every hole occurrence agrees. Solutions containing
/// pattern-local bound variables are rejected (not expressible outside).
fn match_one_hole(pat: &Expr, target: &Expr, delta: u32) -> Option<Expr> {
    let mut solution: Option<Expr> = None;
    fn go(pat: &Expr, target: &Expr, delta: u32, sol: &mut Option<Expr>) -> bool {
        if let clean_kernel::expr::ExprKind::BVar(i) = pat.kind() {
            if *i == delta {
                // The hole: the candidate must be closed w.r.t. pattern-local
                // binders (no bvars below `delta` levels of target nesting —
                // target subterms here may only reference binders INSIDE the
                // matched region, which correspond one-to-one with pattern
                // binders below `delta`).
                if mentions_bvar_below(target, delta) {
                    return false;
                }
                return match sol {
                    Some(s) => s == target,
                    None => {
                        *sol = Some(target.clone());
                        true
                    }
                };
            }
        }
        match (pat.kind(), target.kind()) {
            (
                clean_kernel::expr::ExprKind::App(pf, pa),
                clean_kernel::expr::ExprKind::App(tf, ta),
            ) => go(pf, tf, delta, sol) && go(pa, ta, delta, sol),
            (
                clean_kernel::expr::ExprKind::Lam(_, pd, pb),
                clean_kernel::expr::ExprKind::Lam(_, td, tb),
            )
            | (
                clean_kernel::expr::ExprKind::Pi(_, pd, pb),
                clean_kernel::expr::ExprKind::Pi(_, td, tb),
            ) => go(pd, td, delta, sol) && go(pb, tb, delta + 1, sol),
            _ => pat == target,
        }
    }
    if go(pat, target, delta, &mut solution) {
        solution
    } else {
        None
    }
}

/// Whether `e` mentions the loose bound variable `idx` (de Bruijn, adjusted
/// under binders).
fn mentions_bvar(e: &Expr, idx: u32) -> bool {
    match e.kind() {
        clean_kernel::expr::ExprKind::BVar(i) => *i == idx,
        clean_kernel::expr::ExprKind::App(f, a) => mentions_bvar(f, idx) || mentions_bvar(a, idx),
        clean_kernel::expr::ExprKind::Lam(_, d, b) | clean_kernel::expr::ExprKind::Pi(_, d, b) => {
            mentions_bvar(d, idx) || mentions_bvar(b, idx + 1)
        }
        _ => false,
    }
}

/// Whether `e` mentions ANY loose bound variable below `limit`.
fn mentions_bvar_below(e: &Expr, limit: u32) -> bool {
    fn go(e: &Expr, limit: u32) -> bool {
        match e.kind() {
            clean_kernel::expr::ExprKind::BVar(i) => *i < limit,
            clean_kernel::expr::ExprKind::App(f, a) => go(f, limit) || go(a, limit),
            clean_kernel::expr::ExprKind::Lam(_, d, b)
            | clean_kernel::expr::ExprKind::Pi(_, d, b) => go(d, limit) || go(b, limit + 1),
            _ => false,
        }
    }
    if limit == 0 {
        return false;
    }
    go(e, limit)
}
