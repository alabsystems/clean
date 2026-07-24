// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `impl Ctx` theorem application: `proof_prop` / `infer_proof_prop` (best-effort
//! proposition inference), `apply_thm` (the implicit type-instantiation recovery),
//! `apply_thm_explicit` (the fully-typed `tyinst`-driven specialization), and the
//! `any_in_scope_type` phantom-fill helper. Split out of the original
//! `proof_terms` module verbatim (plus the additive explicit-instantiation path).

use super::super::super::isabelle_pure::{IsaProof, IsaTermInst, IsaTypeInst};
use super::super::*;
use super::*;
use clean_kernel::expr::FVarId;
use clean_kernel::level::Level;
use clean_kernel::Expr;
use std::collections::BTreeMap;

impl Ctx {
    /// Best-effort proposition that a proof *argument* establishes, used to
    /// recover the hypothesis type of an `AbsP { h: None }` applied to it in a
    /// redex. Returns `None` (not an error) when the proposition is not statically
    /// derivable here, so the caller can fall back. Currently handles the `Hyp`
    /// case (the proof is a bare hypothesis whose proposition is recorded).
    pub(crate) fn proof_prop(
        &mut self,
        q: &IsaProof,
        binders: &mut Vec<Binder>,
    ) -> Result<Option<Expr>, TranslateError> {
        match q {
            IsaProof::Hyp { p } => Ok(Some(self.embed_term(p, binders)?)),
            _ => self.infer_proof_prop(q, binders),
        }
    }

    /// Best-effort embedded **proposition** that a proof term establishes — the
    /// proof-level analogue of [`Self::infer_type`]. Used to recover the omitted
    /// hypothesis type of a redex `AbsP { h: None }` whose argument is not a bare
    /// `Hyp`. Returns `Ok(None)` (not an error) when the proposition is not
    /// statically derivable, so the caller falls back. The kernel re-checks the
    /// final term, so a wrong inference is rejected, never miscounted.
    ///
    /// Covered shapes (the ones that arise in the equal-elim / symmetry discharge
    /// redexes): a `PBound` (→ its proof binder's proposition), and the base
    /// equational axioms applied to their term spine
    /// (`reflexive`/`symmetric`/`transitive`/`combination`/`equal_elim`), whose
    /// conclusion is read off the spine's term arguments.
    pub(crate) fn infer_proof_prop(
        &mut self,
        q: &IsaProof,
        binders: &mut Vec<Binder>,
    ) -> Result<Option<Expr>, TranslateError> {
        if let IsaProof::Bound { i } = q {
            return Ok(proof_bvar_ty(binders, *i as usize));
        }
        if let IsaProof::Hyp { p } = q {
            return Ok(Some(self.embed_term(p, binders)?));
        }
        let (head, spine) = collect_spine(q);
        // A `PBound`/`Hyp`-headed APPLICATION spine (`PB2 %% PB0 % t …`): the
        // head's proposition is statically known (the proof binder's recorded
        // type / the hypothesis term — statement-keyed by construction), and each
        // spine argument peels one `Pi`: a *term* argument instantiates the
        // binder with its embedding, a *proof* argument discharges a premise
        // (proof-irrelevant in this embedding — the codomain never mentions the
        // proof bvar, so instantiating with a placeholder is exact). Any shape
        // surprise returns `None` (the caller falls back); the kernel re-checks
        // whatever is built from the derived proposition, so a wrong derivation
        // is rejected — never miscounted.
        match head {
            IsaProof::Bound { i } => {
                let Some(base) = proof_bvar_ty(binders, *i as usize) else {
                    return Ok(None);
                };
                return self.peel_prop_spine(base, &spine, binders);
            }
            IsaProof::Hyp { p } => {
                let base = self.embed_term(p, binders)?;
                return self.peel_prop_spine(base, &spine, binders);
            }
            _ => {}
        }
        let IsaProof::Axm { name, .. } = head else {
            return Ok(None);
        };
        let terms = spine_terms(&spine);
        // Build `@Eq u α a b` from already-embedded operands.
        let mk_eq = |alpha: Expr, a: Expr, b: Expr| {
            Expr::apps(
                Expr::const_str_levels("Eq", vec![obj_level()]),
                [alpha, a, b],
            )
        };
        match name.as_str() {
            // `t ≡ t`
            "Pure.reflexive" | "HOL.refl" | "Pure.prop_def" => {
                let Some(t) = terms.first() else {
                    return Ok(None);
                };
                // The witness term may be omitted (`% NONE` → `Bound{-1}`
                // sentinel); recover nothing rather than erroring.
                let (Ok(alpha), Ok(te)) =
                    (self.infer_type(t, binders), self.embed_term(t, binders))
                else {
                    return Ok(None);
                };
                Ok(Some(mk_eq(alpha, te.clone(), te)))
            }
            // `a ≡ b ⟹ b ≡ a` proves `b ≡ a`
            "Pure.symmetric" | "HOL.sym" => match (terms.first(), terms.get(1)) {
                (Some(a), Some(b)) => {
                    let alpha = self.infer_type(a, binders)?;
                    let ae = self.embed_term(a, binders)?;
                    let be = self.embed_term(b, binders)?;
                    Ok(Some(mk_eq(alpha, be, ae)))
                }
                _ => {
                    // zproof: no spine terms (the reference's `tminst` carries only
                    // the generic box-internal `Free`s) — derive the single proof
                    // premise's own proposition and FLIP it. Statement-keyed
                    // whenever the premise chain bottoms out in `PBound`/`Hyp`.
                    let ps = proof_spine_args(&spine);
                    let Some(pr) = ps.first() else {
                        return Ok(None);
                    };
                    let Some(prop) = self.infer_proof_prop(pr, binders)? else {
                        return Ok(None);
                    };
                    let Some((alpha, l, r, _)) = eq_app_three(&prop) else {
                        return Ok(None);
                    };
                    Ok(Some(mk_eq(alpha, r, l)))
                }
            },
            // proves `a ≡ c`
            "Pure.transitive" | "HOL.trans" => match (terms.first(), terms.get(2)) {
                (Some(a), Some(c)) => {
                    let alpha = self.infer_type(a, binders)?;
                    let ae = self.embed_term(a, binders)?;
                    let ce = self.embed_term(c, binders)?;
                    Ok(Some(mk_eq(alpha, ae, ce)))
                }
                _ => {
                    // zproof (no spine terms): compose the endpoints of the two
                    // premises' own derived propositions.
                    let ps = proof_spine_args(&spine);
                    let (Some(p1), Some(p2)) = (ps.first(), ps.get(1)) else {
                        return Ok(None);
                    };
                    let Some(prop1) = self.infer_proof_prop(p1, binders)? else {
                        return Ok(None);
                    };
                    let Some(prop2) = self.infer_proof_prop(p2, binders)? else {
                        return Ok(None);
                    };
                    let (Some((alpha, ae, _, _)), Some((_, _, ce, _))) =
                        (eq_app_three(&prop1), eq_app_three(&prop2))
                    else {
                        return Ok(None);
                    };
                    Ok(Some(mk_eq(alpha, ae, ce)))
                }
            },
            // `f ≡ g ⟹ x ≡ y ⟹ f x ≡ g y` proves `f x ≡ g y`
            "Pure.combination" => match (terms.first(), terms.get(1), terms.get(2), terms.get(3)) {
                (Some(f), Some(g), Some(x), Some(y)) => {
                    let f_ty = self.infer_type(f, binders)?;
                    let Some((_, cod)) = split_arrow(&f_ty) else {
                        return Ok(None);
                    };
                    let fe = self.embed_term(f, binders)?;
                    let ge = self.embed_term(g, binders)?;
                    let xe = self.embed_term(x, binders)?;
                    let ye = self.embed_term(y, binders)?;
                    Ok(Some(mk_eq(cod, Expr::app(fe, xe), Expr::app(ge, ye))))
                }
                _ => {
                    // zproof (no spine terms): apply the two premises' own derived
                    // equations pointwise (`f x ≡ g y` from `f ≡ g` and `x ≡ y`).
                    let ps = proof_spine_args(&spine);
                    let (Some(p1), Some(p2)) = (ps.first(), ps.get(1)) else {
                        return Ok(None);
                    };
                    let Some(prop1) = self.infer_proof_prop(p1, binders)? else {
                        return Ok(None);
                    };
                    let Some(prop2) = self.infer_proof_prop(p2, binders)? else {
                        return Ok(None);
                    };
                    let (Some((fun_ty, fe, ge, _)), Some((_, xe, ye, _))) =
                        (eq_app_three(&prop1), eq_app_three(&prop2))
                    else {
                        return Ok(None);
                    };
                    let Some((_, cod)) = split_arrow(&fun_ty) else {
                        return Ok(None);
                    };
                    Ok(Some(mk_eq(cod, Expr::app(fe, xe), Expr::app(ge, ye))))
                }
            },
            // `A ≡ B ⟹ A ⟹ B` proves `B` (the 2nd term arg).
            "Pure.equal_elim" => match terms.get(1) {
                Some(b) => Ok(Some(self.embed_term(b, binders)?)),
                None => Ok(None),
            },
            _ => Ok(None),
        }
    }

    /// Peel one `Pi` off `base` per spine argument (the [`Self::infer_proof_prop`]
    /// application walk): a *term* argument instantiates the binder with its
    /// embedding; a *proof* argument discharges a premise binder, whose codomain
    /// never mentions the proof bvar in this proof-irrelevant embedding, so it is
    /// instantiated with an inert placeholder. Returns `Ok(None)` when `base`
    /// runs out of `Pi`s before the spine is consumed (shape surprise — caller
    /// falls back). Diagnostics-only inference: the kernel re-checks anything
    /// built from the result.
    fn peel_prop_spine(
        &mut self,
        base: Expr,
        spine: &[SpineArg],
        binders: &mut Vec<Binder>,
    ) -> Result<Option<Expr>, TranslateError> {
        use clean_kernel::expr::ExprKind;
        let mut cur = base;
        for arg in spine {
            let ExprKind::Pi(_, _, cod) = cur.kind() else {
                return Ok(None);
            };
            let cod = (**cod).clone();
            cur = match arg {
                // A term argument the embedder cannot handle (e.g. the legacy
                // `% NONE` `Bound{-1}` sentinel) makes the proposition
                // underivable — report `None` (fall back), never an error.
                SpineArg::Term(t) => match self.embed_term(t, binders) {
                    Ok(te) => cod.instantiate(&te),
                    Err(_) => return Ok(None),
                },
                // Proof-irrelevant premise: the codomain cannot mention the
                // discharged proof, so any well-formed placeholder is exact.
                SpineArg::Proof(_) => cod.instantiate(&Expr::const_str("True.intro")),
            };
        }
        Ok(Some(cur))
    }

    /// Best-effort embedded **proposition** of a `Thm`-headed spine carrying a
    /// GENUINE (non-generic, non-empty) explicit instantiation table — the
    /// type-level counterpart of [`Self::apply_thm_explicit`]: fill the
    /// referenced entry's leading type/term binders from `tyinst`/`tminst` by
    /// recorded key, then peel one premise `Pi` per spine argument
    /// ([`Self::peel_prop_spine`]). Used by the bidirectional equation channels
    /// to read a congruence leg's OWN conclusion: the recorded chain may prove
    /// `min ≡ (λa b. If (le a b) a b)` where the syntactic split of the
    /// β-NORMAL expected equation spells the partial `If α (le a b)` — two
    /// genuinely different functions, so a split-driven expectation
    /// desynchronizes the congruence assembly (the s125868 `expected=Eq got=Eq`
    /// reject). Returns `Ok(None)` whenever anything is missing (legacy/empty
    /// or generic tables, unresolved dep, stale metadata) — callers keep the
    /// split path byte-for-byte. Diagnostics-grade: the kernel re-checks
    /// whatever is assembled from the derived proposition.
    pub(crate) fn infer_thm_prop(
        &mut self,
        q: &IsaProof,
        closure: &Closure,
        binders: &mut Vec<Binder>,
    ) -> Result<Option<Expr>, TranslateError> {
        use clean_kernel::expr::ExprKind;
        let (head, spine) = collect_spine(q);
        let IsaProof::Thm {
            id, tyinst, tminst, ..
        } = head
        else {
            return Ok(None);
        };
        // zproof-only: legacy (empty) and generic (identity) tables record no
        // operand information, so the leg's own conclusion is not derivable.
        if (tyinst.is_empty() && tminst.is_empty()) || insts_generic(tyinst, tminst) {
            return Ok(None);
        }
        let Some(entry) = closure.get(id) else {
            return Ok(None);
        };
        let entry = entry.clone();
        if entry.type_param_keys.is_empty() && entry.term_param_keys.is_empty() {
            return Ok(None);
        }
        let tyinst_by_key: BTreeMap<String, &super::super::super::isabelle_pure::IsaType> = tyinst
            .iter()
            .map(|ti| (format!("{}.{}", ti.n, ti.i), &ti.ty))
            .collect();
        let tminst_by_key: BTreeMap<String, &super::super::super::isabelle_pure::IsaTerm> = tminst
            .iter()
            .map(|ti| (format!("{}.{}", ti.n, ti.i), &ti.t))
            .collect();
        let mut tele = entry.ty.clone();
        for key in &entry.type_param_keys {
            let ExprKind::Pi(_, dom, cod) = tele.kind() else {
                return Ok(None);
            };
            if !matches!(dom.kind(), ExprKind::Sort(level) if *level != Level::zero()) {
                return Ok(None);
            }
            let Some(isa_ty) = tyinst_by_key.get(key) else {
                return Ok(None);
            };
            let arg = self.embed_type(isa_ty)?;
            tele = cod.instantiate(&arg);
        }
        for key in &entry.term_param_keys {
            let ExprKind::Pi(_, _, cod) = tele.kind() else {
                return Ok(None);
            };
            let Some(isa_tm) = tminst_by_key.get(key) else {
                return Ok(None);
            };
            let arg = self.embed_term(isa_tm, binders)?;
            tele = cod.instantiate(&arg);
        }
        self.peel_prop_spine(tele, &spine, binders)
    }

    /// Apply an already-verified clean theorem (a resolved `PThm`) to the
    /// Isabelle proof spine, **reconstructing the implicit leading type
    /// instantiations** the spine omits.
    ///
    /// A Pure proof term records a polymorphic theorem's *term* and *proof*
    /// arguments (including sort-constraint witnesses, as `PClass`/proof
    /// arguments) in its application spine, but it never records the schematic
    /// **type** instantiation. The closed clean theorem, however, makes each
    /// schematic type variable an explicit leading `∀(T : Type)` binder (an
    /// object-`Type` at `Sort (n+1)`, distinct from a `Prop` premise at
    /// `Sort 0`, which the spine *does* supply). In this embedding every such
    /// type binder is a contiguous prefix of the telescope (type params bind
    /// outermost).
    ///
    /// We instantiate each leading type binder with a fresh sentinel free
    /// variable, then walk the remaining binders consuming spine arguments in
    /// order. For each consumed **term** argument we unify its embedded type
    /// against the (sentinel-parameterized) binder domain, solving the sentinels
    /// — i.e. recovering the type instantiation from the term arguments exactly
    /// as Isabelle's type inference would. Finally the head is applied to the
    /// solved type arguments, then to the spine arguments (terms embedded, proof
    /// arguments — `Prop` premises, `True` sort witnesses, hypotheses —
    /// translated); clean β/η-checks the result.
    pub(crate) fn apply_thm(
        &mut self,
        entry: &ClosureEntry,
        spine: &[SpineArg],
        closure: &Closure,
        binders: &mut Vec<Binder>,
    ) -> Result<Expr, TranslateError> {
        use clean_kernel::expr::ExprKind;

        // Peel the contiguous leading object-`Type` binders, replacing each with
        // a fresh sentinel fvar so the remaining telescope is sentinel-indexed.
        let mut sentinels: Vec<FVarId> = Vec::new();
        let mut tele = entry.ty.clone();
        while let ExprKind::Pi(_, dom, cod) = tele.kind() {
            if matches!(dom.kind(), ExprKind::Sort(level) if *level != Level::zero()) {
                let fv = param_fvar(3, &format!("thm:{}:ty{}", entry.name, sentinels.len()));
                sentinels.push(fv);
                tele = cod.instantiate(&Expr::fvar(fv));
            } else {
                break;
            }
        }

        // Solution map for the sentinels, solved by unifying each term arg's
        // embedded type against its (sentinel-parameterized) binder domain.
        let mut solution: BTreeMap<FVarId, Expr> = BTreeMap::new();
        let mut applied_args: Vec<Expr> = Vec::new();
        let mut idx = 0usize;
        while let ExprKind::Pi(_, dom, cod) = tele.kind() {
            let (dom, cod) = ((**dom).clone(), (**cod).clone());
            let arg = match spine.get(idx) {
                Some(SpineArg::Term(t)) => {
                    idx += 1;
                    let actual = self.infer_type(t, binders)?;
                    unify_sentinels(&dom, &actual, &sentinels, &mut solution);
                    self.embed_term(t, binders)?
                }
                Some(SpineArg::Proof(pr)) => {
                    idx += 1;
                    // The binder `dom` IS the expected proposition of this proof
                    // argument. When the argument is a raw `AbsP { h: None }` /
                    // `Abst { ty: None }` chain (whose omitted binder types the
                    // raw export drops), recover them from `dom`'s Pi telescope —
                    // substituting any sentinels already solved. The kernel
                    // re-checks, so a wrong recovery is rejected.
                    let mut expected = dom.clone();
                    for (fv, sol) in &solution {
                        expected = expected.subst_fvar(*fv, sol);
                    }
                    self.translate_proof_expecting(pr, &expected, closure, binders)?
                }
                None => break, // telescope longer than spine: partial application
            };
            tele = cod.instantiate(&arg);
            applied_args.push(arg);
        }

        // A sentinel left unsolved means the spine carried no term argument
        // constraining that type variable — it is *phantom*, occurring only in
        // discharged sort constraints / the conclusion of an arity-style fact
        // (e.g. `OFCLASS('a) ⟹ … ⟹ True`). Such a binder may be instantiated at
        // any in-scope type without changing the proof, so we fall back to a
        // type that is in scope in the enclosing theorem (a registered `Type`
        // parameter), or `PUnit` as a last resort. This keeps the result closed.
        let phantom_fill = self.any_in_scope_type();
        let mut head = Expr::const_str_levels(entry.name.as_str(), Vec::<Level>::new());
        for fv in &sentinels {
            let ty_arg = solution
                .get(fv)
                .cloned()
                .unwrap_or_else(|| phantom_fill.clone());
            head = Expr::app(head, ty_arg);
        }
        // Apply the consumed binder arguments, substituting solved sentinels into
        // any proof argument that still mentions them (term args are already in
        // sentinel-free embedded form).
        for a in applied_args {
            let mut a = a;
            for (fv, sol) in &solution {
                a = a.subst_fvar(*fv, sol);
            }
            head = Expr::app(head, a);
        }
        // Any spine arguments beyond the telescope apply verbatim — EXCEPT a
        // leftover sort witness (`PClass`/`OfClass`, or a `PBound` resolving to
        // an ELIDED implicit sort-hypothesis slot): the referenced entry's
        // verified telescope carries no binder for it (the sort constraint was
        // erased / never materialized in the mode that verified the entry), so
        // applying its vacuous witness translation to the already-saturated
        // head is always ill-typed (`NotAFunction @Eq …`). The constraint is
        // vacuous in this embedding — drop it; the kernel re-checks the result.
        for arg in &spine[idx..] {
            head = match arg {
                arg if is_leftover_sort_witness(arg, binders) => head,
                SpineArg::Term(t) => Expr::app(head, self.embed_term(t, binders)?),
                SpineArg::Proof(pr) => Expr::app(head, self.translate_proof(pr, closure, binders)?),
            };
        }
        Ok(head)
    }

    /// Apply a resolved `PThm` using the fully-typed (`zproof`) export's **explicit
    /// `tyinst`/`tminst` tables** to specialize the referenced theorem DIRECTLY,
    /// instead of reconstructing the leading type instantiations from the term
    /// spine ([`Self::apply_thm`]'s sentinel / `any_in_scope_type` machinery).
    ///
    /// In the closed clean theorem the referenced theorem's schematic variables
    /// become leading binders, in this order: each schematic **type** variable is a
    /// leading `∀(T:Type)` binder, then each schematic **term** variable is a
    /// `∀(x:T)` binder, then the Pure premises (`OFCLASS` sort witnesses, `⟹`
    /// hypotheses) are `Prop` binders. The closure entry records the embedding keys
    /// of the type binders ([`ClosureEntry::type_param_keys`]) and term binders
    /// ([`ClosureEntry::term_param_keys`]) in order. The fully-typed reference
    /// carries:
    /// - `tyinst`: each schematic type var `(n, i)` → the concrete type, keyed as
    ///   `embed_type` registers a type param (`"{n}.{i}"`);
    /// - `tminst`: each schematic term var `(n, i)` → the concrete term, keyed as
    ///   `term_param` registers a term param (the base name `n`).
    ///
    /// We therefore fill each leading type binder from `tyinst` (by key) and each
    /// term binder from `tminst` (by key) — an **exact** specialization. A bare
    /// schematic instantiation supplies its type/term arguments through these
    /// tables, NOT through the proof spine; the spine carries only the remaining
    /// premise witnesses (sort/hyp proofs), which fill the `Prop` binders in order.
    ///
    /// Returns `Ok(None)` — the caller falls back to [`Self::apply_thm`] — whenever
    /// the metadata needed for an exact fill is missing or inconsistent: a legacy
    /// entry recorded no keys; a leading type/term binder's key has no matching
    /// table entry (e.g. a phantom type variable the conclusion/sort constraints
    /// determine, which the implicit `any_in_scope_type` path handles); or the
    /// recorded key count disagrees with the peeled binders. The kernel re-checks
    /// the assembled term, so a wrong instantiation is rejected — never miscounted.
    pub(crate) fn apply_thm_explicit(
        &mut self,
        entry: &ClosureEntry,
        tyinst: &[IsaTypeInst],
        tminst: &[IsaTermInst],
        spine: &[SpineArg],
        closure: &Closure,
        binders: &mut Vec<Binder>,
    ) -> Result<Option<Expr>, TranslateError> {
        use clean_kernel::expr::ExprKind;

        // No recorded keys → cannot map the instantiation tables to binder
        // positions exactly. Defer to the implicit reconstruction path.
        if entry.type_param_keys.is_empty() && entry.term_param_keys.is_empty() {
            return Ok(None);
        }

        // Index `tyinst` and `tminst` by the SAME key the embedder registers the
        // corresponding schematic param under: a `TVar { n, i }` type and a
        // `Var { n, i }` term both register as `"{n}.{i}"` (see `embed_type`'s
        // `TVar` arm and `embed_term`'s `Var` arm). So both tables are keyed by
        // `"{n}.{i}"`, matching the recorded `type_param_keys`/`term_param_keys`.
        //
        // FREE-key alias (the round-7 keying model): `Pure/zterm.ML` encodes a
        // referenced statement's own FREE variable as index `-1` (`ZVar (x, ~1)`
        // = `Free x`, `ZTVar (a, ~1)` = `TFree a`), while the embedder keys a
        // `Free { n }` param as plain `"n"` (and a `TFree { n }` as `"'n"` — the
        // name already carries the tick). A dependency whose statement is
        // spelled over box-internal frees therefore records binder keys
        // WITHOUT the `.-1` suffix; alias each `-1`-indexed table entry under
        // the plain name so the exact fill finds it (an explicit `"{n}.-1"`
        // entry, if the embedder ever produced one, still wins).
        let mut tyinst_by_key: BTreeMap<String, &IsaType> = BTreeMap::new();
        for ti in tyinst {
            tyinst_by_key.insert(format!("{}.{}", ti.n, ti.i), &ti.ty);
            if ti.i == -1 {
                tyinst_by_key.entry(ti.n.clone()).or_insert(&ti.ty);
            }
        }
        let mut tminst_by_key: BTreeMap<String, &IsaTerm> = BTreeMap::new();
        for ti in tminst {
            tminst_by_key.insert(format!("{}.{}", ti.n, ti.i), &ti.t);
            if ti.i == -1 {
                tminst_by_key.entry(ti.n.clone()).or_insert(&ti.t);
            }
        }

        let mut tele = entry.ty.clone();
        let mut head_args: Vec<Expr> = Vec::new();

        // The object-type fills' Isabelle types, in binder order — the use-site
        // object types for re-embedding a registered locale predicate /
        // poly-inst operation in the consumer's own flavor (see the `const:`
        // fill below). Multi-entry since the G1 lift admits multi-tvar
        // registrations (positional: the dependency's leading type binders
        // correspond to the registration's first-occurrence tvar order).
        let mut obj_isa_fills: Vec<IsaType> = Vec::new();

        // (1) Leading object-`Type` binders → fill from `tyinst` by recorded key.
        for key in &entry.type_param_keys {
            let ExprKind::Pi(_, dom, cod) = tele.kind() else {
                return Ok(None); // fewer binders than recorded keys: metadata stale
            };
            // Must actually be an object-`Type` binder (`Sort n>0`).
            if !matches!(dom.kind(), ExprKind::Sort(level) if *level != Level::zero()) {
                return Ok(None);
            }
            // A key with no `tyinst` entry is a phantom the conclusion/sort
            // constraints determine; defer to the implicit `any_in_scope_type` path.
            let Some(isa_ty) = tyinst_by_key.get(key) else {
                return Ok(None);
            };
            obj_isa_fills.push((*isa_ty).clone());
            let arg = self.embed_type(isa_ty)?;
            tele = cod.instantiate(&arg);
            head_args.push(arg);
        }

        // (2) Schematic-term-variable binders → fill from `tminst` by recorded key.
        for key in &entry.term_param_keys {
            let ExprKind::Pi(_, dom, cod) = tele.kind() else {
                return Ok(None);
            };
            let arg = match tminst_by_key.get(key) {
                // Flavor-bridged: a bare `Free x` operand prefers the consumer's
                // schematic `x.0` param when registered (the round-7 keying
                // model; see [`Self::embed_table_operand`]).
                Some(isa_tm) => self.embed_table_operand(isa_tm, binders)?,
                // A `const:<n>`-keyed binder is an **embedding-introduced
                // OPERATION parameter** — a HOL *constant* (a class operation /
                // locale predicate like `Orderings.class.preorder`, `less_eq`)
                // this embedding abstracts as a shared `const:` param — NOT a
                // schematic variable of the referenced statement, so the
                // reference's `tminst` can never carry an entry for it (the
                // class-def / class-projection reference family: identity
                // `tyinst`, EMPTY `tminst`, telescope `Pi[3..]` over the ops).
                // The exact fill is THIS consumer's own shared param of the
                // same key: both sides re-embed the same global constant under
                // the same `const:<n>` key, so the dependency's op binder and
                // every occurrence in the consumer's statement coincide. The
                // binder's domain (already instantiated with the earlier type
                // fills) types the param; the kernel re-checks the assembled
                // term, so a wrong fill is rejected — never miscounted.
                // A recorded `tminst` can only ever carry SCHEMATIC-variable
                // keys, so a missing `const:` key is never "not yet supplied" —
                // it is structurally unfillable from the table and the shared
                // param is the one exact fill (the class-chain references:
                // identity `tyinst`, `tminst` empty or identity over the
                // schematic args, telescope over the ops).
                None if key.starts_with("const:") => {
                    let dom = (**dom).clone();
                    self.const_key_fill(key, dom, &obj_isa_fills)?
                }
                None => return Ok(None),
            };
            tele = cod.instantiate(&arg);
            head_args.push(arg);
        }

        // (3) Remaining binders are the Pure premises (sort witnesses / hypotheses)
        // — these the proof spine supplies, in order, exactly as `apply_thm` does
        // (the type/term arguments are already fixed, so the domains are ground).
        let mut idx = 0usize;
        while let ExprKind::Pi(_, dom, cod) = tele.kind() {
            let (dom, cod) = ((**dom).clone(), (**cod).clone());
            let arg = match spine.get(idx) {
                Some(SpineArg::Term(t)) => {
                    idx += 1;
                    self.embed_term(t, binders)?
                }
                Some(SpineArg::Proof(pr)) => {
                    idx += 1;
                    // The (now ground) binder domain IS the expected proposition of
                    // this proof argument; recover an omitted-type raw binder from it.
                    self.translate_proof_expecting(pr, &dom, closure, binders)?
                }
                None => break, // telescope longer than spine: partial application
            };
            tele = cod.instantiate(&arg);
            head_args.push(arg);
        }

        // Assemble: head applied to the type args, term args, and consumed premise
        // args, then any spine arguments beyond the telescope (applied verbatim —
        // except a leftover sort witness (`OfClass` / elided-slot `PBound`), which
        // has no binder in the verified telescope and would over-apply the
        // saturated head; see [`Self::apply_thm`]).
        let mut head = Expr::const_str_levels(entry.name.as_str(), Vec::<Level>::new());
        for a in head_args {
            head = Expr::app(head, a);
        }
        for arg in &spine[idx..] {
            head = match arg {
                arg if is_leftover_sort_witness(arg, binders) => head,
                SpineArg::Term(t) => Expr::app(head, self.embed_term(t, binders)?),
                SpineArg::Proof(pr) => Expr::app(head, self.translate_proof(pr, closure, binders)?),
            };
        }
        Ok(Some(head))
    }

    /// Fill for a dependency's `const:<n>`-keyed operation binder: the
    /// **consumer's own embedding of the constant `n`**, so the applied
    /// dependency's premises/conclusion carry the SAME flavor as every
    /// occurrence in the consumer's statement and hypotheses.
    ///
    /// The shared opaque `term_param(key, dom)` is exact whenever the
    /// consumer's own embedding of `n` is opaque — but under an Unfold-mode
    /// pass a constant in the poly-inst registry (a locale predicate
    /// `Thy.class.c`, a polymorphic instance operation) embeds as its
    /// `isabelle.polyinst.<n>` def-const application. A dependency STORED by an
    /// Opaque-mode acceptance still quantifies the operation as a `const:`
    /// binder; filling it with the opaque shared param then produces
    /// `FVar(le,lt)` premises structurally irreconcilable with the consumer's
    /// `polyinst.<n>(α,…)` hypotheses (the cross-line
    /// `expected=FVar got=polyinst.class.<c>` intro_of_class family, round 9).
    /// So when the consumer's dispatch WOULD unfold `n` (same gate as
    /// `embed_const_term`: `instance_unfold` + registered), re-embed `n` at the
    /// use-site type — the registered type with the object tvars instantiated
    /// POSITIONALLY to this application's leading recorded type fills (the
    /// dependency quantifies the registration's tvars in the same
    /// first-occurrence order for the class-chain/def families this path
    /// serves; a single tvar reproduces the historical first-fill behaviour)
    /// — through the full dispatch. Falls back to the shared opaque param when
    /// the object types are unavailable or the re-embed declines. The kernel
    /// re-checks the assembled term either way, so a wrong fill is rejected —
    /// never miscounted.
    pub(crate) fn const_key_fill(
        &mut self,
        key: &str,
        dom: Expr,
        obj_isa: &[IsaType],
    ) -> Result<Expr, TranslateError> {
        let name = const_key_name(key).unwrap_or(key);
        if self.instance_unfold {
            if let Some(info) = self.poly_inst_registry.get(name).cloned() {
                // A G4 instance-link ALIAS entry records no tvars/ops — its
                // `fn_ty` is the link's own (generic) instance type, so the
                // positional re-instantiation below would re-embed the constant
                // at the WRONG (uninstantiated) type. Keep alias-named op
                // binders on the historical shared-opaque-param path; the
                // kernel re-checks the assembled term either way.
                if info.alias_of.is_none() && info.obj_tvars.len() <= obj_isa.len() {
                    let subs: Vec<((String, i64), IsaType)> = info
                        .obj_tvars
                        .iter()
                        .cloned()
                        .zip(obj_isa.iter().cloned())
                        .collect();
                    let use_ty = subst_tvars(&info.fn_ty, &subs);
                    if let Ok(e) = self.embed_const_term(&IsaTerm::Const {
                        n: name.to_string(),
                        t: use_ty,
                    }) {
                        return Ok(e);
                    }
                }
            }
        }
        // Re-derive the shared param key from this application's INSTANTIATED binder
        // domain `dom` (via `const_param`), NOT from the dependency's stored key
        // `key` — which was hashed at the dependency's own (generic `'a`) op type and
        // no longer coincides with the CONSUMER's occurrence of the operation at the
        // instantiated type under the r16 type-suffix keying. `const_param(name, dom)`
        // mints exactly `const:name#hash(dom)`, the SAME key the consumer's statement
        // occurrence of `name` at this instantiation produces (by the embed/subst
        // homomorphism `dom = embed(op_ty)['a := fill]`), so the filled op binder
        // coincides with the consumer's hypotheses — restoring the instantiation-
        // independence the name-only keying gave for FREE. The kernel re-checks the
        // assembled term, so a wrong fill is rejected — never miscounted.
        Ok(self.const_param(name, dom))
    }

    /// A clean `Type` that is in scope in the proof currently being built — the
    /// first registered object-type parameter (`∀(T:Type)`), or universe-0
    /// `PUnit` if none is registered yet. Used to instantiate *phantom* type
    /// arguments of referenced theorems (type variables the proof spine never
    /// constrains, as in arity facts whose conclusion is `True`).
    pub(crate) fn any_in_scope_type(&self) -> Expr {
        match self.type_params.first() {
            Some((_, p)) => Expr::fvar(p.fvar),
            None => Expr::const_str_levels("PUnit", vec![obj_level()]),
        }
    }
}
