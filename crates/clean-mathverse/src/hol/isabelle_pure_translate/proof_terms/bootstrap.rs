// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `impl Ctx::bootstrap_axiom`: the Pure/HOL base-axiom → clean-proof mapping
//! (reflexivity, symmetry, transitivity, the Pure meta-connectives, `equal_elim`/
//! `equal_intr`, the HOL classical/funext axioms, …). Split out of the original
//! `proof_terms` module verbatim.

use super::super::super::isabelle_pure::{IsaTerm, IsaTermInst, IsaType, IsaTypeInst};
use super::super::*;
use super::*;
use clean_kernel::level::Level;
use clean_kernel::{BinderInfo, Expr};
use std::collections::BTreeMap;

impl Ctx {
    /// Map a Pure/HOL base axiom (with its spine of term/proof args) to a clean
    /// proof `Expr`. Each mapping is a real clean proof reducible to the three
    /// foundational axioms (often to *none*).
    ///
    /// `tyinst`/`tminst` are the fully-typed (`zproof`) export's explicit schematic
    /// type/term instantiation tables: in that export a base axiom's term/type
    /// arguments are supplied through these tables (keyed by the axiom's schematic
    /// variable name, e.g. `Pure.reflexive`'s `?x`), NOT applied as `% t` spine
    /// args the way the legacy export did. Each handler that needs a schematic term
    /// arg therefore looks it up positionally on the spine first and falls back to
    /// the `tminst` table by schematic name. Legacy JSON carries empty tables, so
    /// the spine-based path is preserved exactly. The kernel re-checks every
    /// assembled term, so a wrong instantiation is rejected, never miscounted.
    pub(crate) fn bootstrap_axiom(
        &mut self,
        name: &str,
        spine: &[SpineArg],
        tyinst: &[IsaTypeInst],
        tminst: &[IsaTermInst],
        closure: &Closure,
        binders: &mut Vec<Binder>,
    ) -> Result<Expr, TranslateError> {
        // Most base-axiom arms recover their object types from the spine terms;
        // the generic registered-constant `_def_raw`/`_def` leaf arm (G7) uses
        // `tyinst` directly to instantiate the registered constant's HOL type.
        let terms = spine_terms(spine);
        // Index `tminst` by the axiom's schematic-variable NAME (`x`, `A`, `f`, …),
        // matching the fixed schematic names each Pure/HOL base axiom binds. These
        // names are unique within a single axiom's statement, so name keying is
        // unambiguous (unlike `apply_thm_explicit`'s `"{n}.{i}"` closure-binder
        // keying, the base axioms have no recorded binder-key metadata). Empty for
        // legacy JSON, leaving every `tminst_term` lookup `None` → spine path only.
        let tminst_by_name: BTreeMap<&str, &IsaTerm> =
            tminst.iter().map(|ti| (ti.n.as_str(), &ti.t)).collect();
        // Resolve a base axiom's `idx`-th schematic **term** argument (named `sch`
        // in the axiom's statement): prefer the positional spine term (legacy
        // shape), else the `tminst` table entry under the schematic name, else the
        // `idx`-th `tminst` entry positionally. The named lookup is the primary
        // `zproof` path (keyed exactly as the schematic var, like
        // `apply_thm_explicit`); the positional `tminst` fallback covers axioms
        // whose schematic names vary across aliases (e.g. the `reflexive`/`prop_def`
        // group, `?x` vs `?A`) — Isabelle records `tminst` in statement order, so
        // the `idx`-th entry IS the `idx`-th schematic argument. All three agree on
        // every well-formed export; the kernel re-checks, so a mismatch is rejected.
        let term_arg = |idx: usize, sch: &str| -> Option<&IsaTerm> {
            terms
                .get(idx)
                .copied()
                .or_else(|| tminst_by_name.get(sch).copied())
                .or_else(|| tminst.get(idx).map(|ti| &ti.t))
        };
        match name {
            // reflexivity: `?t ≡ ?t`  →  `@Eq.refl u α t`. `Pure.prop_def`
            // (`Pure.prop A ≡ A`) is reflexivity after the identity embedding.
            "HOL.refl" | "Pure.reflexive" | "Pure.prop_def" => {
                let t =
                    term_arg(0, "x").ok_or(TranslateError::Unsupported("refl without term arg"))?;
                let alpha = self.infer_type(t, binders)?;
                let te = self.embed_term(t, binders)?;
                Ok(Expr::apps(
                    Expr::const_str_levels("Eq.refl", vec![obj_level()]),
                    [alpha, te],
                ))
            }
            // symmetry: `a ≡ b ⟹ b ≡ a`  →  `@Eq.symm u α a b h`
            "Pure.symmetric" | "HOL.sym" => {
                let a =
                    term_arg(0, "x").ok_or(TranslateError::Unsupported("symm missing term a"))?;
                let b =
                    term_arg(1, "y").ok_or(TranslateError::Unsupported("symm missing term b"))?;
                // **Operand-keying recovery** (same contract as the `equal_elim`
                // arm above): zproof-recorded operands that mention box-internal
                // `Free`s (`Free x` vs the statement's `?x.0` — distinct embed
                // keys) can never match the premise's proposition; recover the
                // premise equation `a ≡ b` from the premise itself
                // ([`Self::infer_proof_prop`] — statement-keyed by construction)
                // and translate the premise against it. Legacy (empty-`tminst`)
                // and `Free`-free operands keep the historical path byte-for-byte.
                if !tminst.is_empty() && (term_contains_free(a) || term_contains_free(b)) {
                    if let Some(pr) = proof_spine_args(spine).first() {
                        if let Some(prop) = self.infer_proof_prop(pr, binders)? {
                            if let Some((alpha, l, r, _)) = eq_app_three(&prop) {
                                let h =
                                    self.translate_proof_expecting(pr, &prop, closure, binders)?;
                                return Ok(Expr::apps(
                                    Expr::const_str_levels("Eq.symm", vec![obj_level()]),
                                    [alpha, l, r, h],
                                ));
                            }
                        }
                    }
                }
                let alpha = self.infer_type(a, binders)?;
                let ae = self.embed_term(a, binders)?;
                let be = self.embed_term(b, binders)?;
                // The sub-proof establishes the flipped equation `b ≡ a`. When it is
                // a bare `…_dict` axiom (a dictionary unfolding of a registered
                // overloaded method, exported with no statement), route it through
                // the expected-equation channel with the now-known sides `(b, a)` so
                // it discharges reflexively; otherwise translate it directly.
                let h = match self.first_proof_arg_expecting(spine, b, a, closure, binders)? {
                    Some(h) => h,
                    None => self.first_proof_arg(spine, closure, binders)?,
                };
                Ok(Expr::apps(
                    Expr::const_str_levels("Eq.symm", vec![obj_level()]),
                    [alpha, ae, be, h],
                ))
            }
            // transitivity: `a ≡ b ⟹ b ≡ c ⟹ a ≡ c`  →  `@Eq.trans u α a b c h1 h2`
            "Pure.transitive" | "HOL.trans" => {
                let a = term_arg(0, "x").ok_or(TranslateError::Unsupported("trans missing a"))?;
                let b = term_arg(1, "y").ok_or(TranslateError::Unsupported("trans missing b"))?;
                let c = term_arg(2, "z").ok_or(TranslateError::Unsupported("trans missing c"))?;
                // **Operand-keying recovery** (same contract as `equal_elim`):
                // `Free`-mentioning zproof operands are box-internal names that can
                // never match the premises; recover the endpoints and midpoint from
                // the two premises' own propositions instead.
                if !tminst.is_empty()
                    && (term_contains_free(a) || term_contains_free(b) || term_contains_free(c))
                {
                    let ps = proof_spine_args(spine);
                    if let (Some(p1), Some(p2)) = (ps.first(), ps.get(1)) {
                        let prop1 = self.infer_proof_prop(p1, binders)?;
                        let prop2 = self.infer_proof_prop(p2, binders)?;
                        if let (Some(prop1), Some(prop2)) = (prop1, prop2) {
                            if let (Some((alpha, ae, me, _)), Some((_, _, ce, _))) =
                                (eq_app_three(&prop1), eq_app_three(&prop2))
                            {
                                let h1 =
                                    self.translate_proof_expecting(p1, &prop1, closure, binders)?;
                                let h2 =
                                    self.translate_proof_expecting(p2, &prop2, closure, binders)?;
                                return Ok(Expr::apps(
                                    Expr::const_str_levels("Eq.trans", vec![obj_level()]),
                                    [alpha, ae, me, ce, h1, h2],
                                ));
                            }
                        }
                    }
                }
                let alpha = self.infer_type(a, binders)?;
                let ae = self.embed_term(a, binders)?;
                let be = self.embed_term(b, binders)?;
                let ce = self.embed_term(c, binders)?;
                let proofs = self.proof_args(spine, closure, binders)?;
                let h1 = proofs
                    .first()
                    .cloned()
                    .ok_or(TranslateError::Unsupported("trans missing proof a≡b"))?;
                let h2 = proofs
                    .get(1)
                    .cloned()
                    .ok_or(TranslateError::Unsupported("trans missing proof b≡c"))?;
                Ok(Expr::apps(
                    Expr::const_str_levels("Eq.trans", vec![obj_level()]),
                    [alpha, ae, be, ce, h1, h2],
                ))
            }
            // Pure meta-conjunction elimination/introduction, matching clean's
            // `And` eliminators/constructor (we embed `Pure.conjunction` → `And`):
            //   conjunctionD1 : `A &&& B ⟹ A`  →  `@And.left A B h`
            //   conjunctionD2 : `A &&& B ⟹ B`  →  `@And.right A B h`
            //   conjunctionI  : `A ⟹ B ⟹ A &&& B`  →  `@And.intro A B hA hB`
            // The spine carries the two conjuncts `A`, `B` as term args (both
            // `prop`), then the witness proof(s). These drive the structured
            // type-class `.super`/`.axioms`/`.intro` projections.
            "Pure.conjunctionD1" | "Pure.conjunctionD2" => {
                let a = term_arg(0, "A")
                    .ok_or(TranslateError::Unsupported("conjunctionD missing A"))?;
                let b = term_arg(1, "B")
                    .ok_or(TranslateError::Unsupported("conjunctionD missing B"))?;
                let ae = self.embed_term(a, binders)?;
                let be = self.embed_term(b, binders)?;
                let head = if name == "Pure.conjunctionD1" {
                    "And.left"
                } else {
                    "And.right"
                };
                let base = Expr::apps(Expr::const_str(head), [ae, be]);
                self.apply_proof_args(base, spine, closure, binders)
            }
            "Pure.conjunctionI" => {
                let a = term_arg(0, "A")
                    .ok_or(TranslateError::Unsupported("conjunctionI missing A"))?;
                let b = term_arg(1, "B")
                    .ok_or(TranslateError::Unsupported("conjunctionI missing B"))?;
                let ae = self.embed_term(a, binders)?;
                let be = self.embed_term(b, binders)?;
                let base = Expr::apps(Expr::const_str("And.intro"), [ae, be]);
                self.apply_proof_args(base, spine, closure, binders)
            }
            // congruence: `f ≡ g ⟹ x ≡ y ⟹ f x ≡ g y`  →  `@congr α β f g x y h₁ h₂`
            "Pure.combination" => {
                let f =
                    term_arg(0, "f").ok_or(TranslateError::Unsupported("combination missing f"))?;
                let g =
                    term_arg(1, "g").ok_or(TranslateError::Unsupported("combination missing g"))?;
                let x =
                    term_arg(2, "x").ok_or(TranslateError::Unsupported("combination missing x"))?;
                let y =
                    term_arg(3, "y").ok_or(TranslateError::Unsupported("combination missing y"))?;
                // **Operand-keying recovery** (same contract as `equal_elim`):
                // `Free`-mentioning zproof operands are box-internal names that can
                // never match the premises; recover `f ≡ g` / `x ≡ y` from the two
                // premises' own propositions instead.
                if !tminst.is_empty()
                    && (term_contains_free(f)
                        || term_contains_free(g)
                        || term_contains_free(x)
                        || term_contains_free(y))
                {
                    let ps = proof_spine_args(spine);
                    if let (Some(p1), Some(p2)) = (ps.first(), ps.get(1)) {
                        let prop1 = self.infer_proof_prop(p1, binders)?;
                        let prop2 = self.infer_proof_prop(p2, binders)?;
                        if let (Some(prop1), Some(prop2)) = (prop1, prop2) {
                            if let (Some((fun_ty, fe, ge, _)), Some((_, xe, ye, _))) =
                                (eq_app_three(&prop1), eq_app_three(&prop2))
                            {
                                if let Some((dom, cod)) = split_arrow(&fun_ty) {
                                    let h1 = self
                                        .translate_proof_expecting(p1, &prop1, closure, binders)?;
                                    let h2 = self
                                        .translate_proof_expecting(p2, &prop2, closure, binders)?;
                                    return Ok(Expr::apps(
                                        Expr::const_str_levels(
                                            "congr",
                                            vec![obj_level(), obj_level()],
                                        ),
                                        [dom, cod, fe, ge, xe, ye, h1, h2],
                                    ));
                                }
                            }
                        }
                    }
                }
                // f : α → β; recover α, β from f's embedded function type.
                let f_ty = self.infer_type(f, binders)?;
                let (dom, cod) = split_arrow(&f_ty)
                    .ok_or(TranslateError::Unsupported("combination f not a function"))?;
                let fe = self.embed_term(f, binders)?;
                let ge = self.embed_term(g, binders)?;
                let xe = self.embed_term(x, binders)?;
                let ye = self.embed_term(y, binders)?;
                let proofs = self.proof_args(spine, closure, binders)?;
                let h1 = proofs
                    .first()
                    .cloned()
                    .ok_or(TranslateError::Unsupported("combination missing f≡g"))?;
                let h2 = proofs
                    .get(1)
                    .cloned()
                    .ok_or(TranslateError::Unsupported("combination missing x≡y"))?;
                Ok(Expr::apps(
                    Expr::const_str_levels("congr", vec![obj_level(), obj_level()]),
                    [dom, cod, fe, ge, xe, ye, h1, h2],
                ))
            }
            // `A ≡ B ⟹ A ⟹ B`  →  `@Eq.mp A B h a` (A,B : Prop, so level 0). In the
            // `zproof` shape the propositions `A`/`B` are in `tminst` (`?A`/`?B`) and
            // only the `heq`/`ha` *proof* premises remain on the spine.
            "Pure.equal_elim" => {
                // **Spine-shape-aware operand read (zproof).** In the fully-typed
                // export the axiom's schematic operands `A`/`B` live in `tminst`
                // and NEVER on the spine — a spine TERM argument on an
                // `equal_elim` chain is a `⋀`-ELIMINATION applied to the RESULT
                // `B` (e.g. the `Pure.conjunction_def` elimination spines
                // `equal_elim cd hyp $t C-inst $ minor`, s622/s634). The
                // positional `term_arg(0)` read let that `$t` C-instantiation
                // term SHADOW the real recorded `A` operand (and the
                // instantiation itself was then never applied). Read the
                // operands by the recorded instantiation KEYS against the
                // axiom's parameter telescope (`A`, `B` — falling back to the
                // statement-order positional table entries for alias spellings),
                // and apply every leftover spine argument to the result below.
                // Legacy nodes (empty `tminst` — operands genuinely on the term
                // spine) keep the positional read byte-for-byte.
                let zproof_spine =
                    !tminst.is_empty() && spine.iter().any(|s| matches!(s, SpineArg::Term(_)));
                let (a, b) = if zproof_spine {
                    let a = tminst_by_name
                        .get("A")
                        .copied()
                        .or_else(|| tminst.first().map(|ti| &ti.t))
                        .ok_or(TranslateError::Unsupported("equal_elim missing A"))?;
                    let b = tminst_by_name
                        .get("B")
                        .copied()
                        .or_else(|| tminst.get(1).map(|ti| &ti.t))
                        .ok_or(TranslateError::Unsupported("equal_elim missing B"))?;
                    (a, b)
                } else {
                    (
                        term_arg(0, "A")
                            .ok_or(TranslateError::Unsupported("equal_elim missing A"))?,
                        term_arg(1, "B")
                            .ok_or(TranslateError::Unsupported("equal_elim missing B"))?,
                    )
                };
                // **Operand-keying recovery.** The zproof export records a
                // derivation box's internal variables as unvarified `Free`s
                // (`Free phi`) while the statement — and the recorded `AbsP`
                // hypotheses recovered from it — carry the varified schematics
                // (`?phi.0`). The two embed under DIFFERENT parameter keys
                // (`phi` vs `phi.0`), so `tminst` operands that mention a `Free`
                // can NEVER match the premises' propositions and the assembled
                // `Eq.mp A B …` mismatches (`expected=FVar got=FVar`). When the
                // recorded operands carry such box-internal `Free`s, recover the
                // equation `A ≡ B` from the FIRST proof premise's own proposition
                // instead ([`Self::infer_proof_prop`] — a `PBound`/`Hyp`(-headed
                // application) whose binder type came from the statement, so it is
                // statement-keyed by construction). Genuinely-recorded operands
                // (no `Free`s) keep the historical `tminst` path byte-for-byte;
                // the kernel re-checks either way, so a wrong recovery is
                // rejected — never miscounted. Recovery ALSO avoids embedding the
                // `Free`-carrying operands (embedding them would register phantom
                // quantified parameters that leak into the theorem's closed type).
                // Gated on a non-empty `tminst` (a fully-typed zproof reference —
                // legacy references carry empty tables and keep the historical
                // spine-operand path byte-for-byte).
                let free_operands =
                    !tminst.is_empty() && (term_contains_free(a) || term_contains_free(b));
                let premise_eq = if free_operands {
                    match proof_spine_args(spine).first() {
                        Some(pr) => self
                            .infer_proof_prop(pr, binders)?
                            .and_then(|prop| eq_app_three(&prop).map(|(_, l, r, _)| (l, r))),
                        None => None,
                    }
                } else {
                    None
                };
                let recovered = premise_eq.is_some();
                let (ae, be) = match premise_eq {
                    Some((l, r)) => (l, r),
                    None => (self.embed_term(a, binders)?, self.embed_term(b, binders)?),
                };
                // The two proof arguments have known expected propositions:
                //   heq : @Eq Prop A B   (the equation A ≡ B)
                //   ha  : A              (the minor premise)
                // Pass these so raw `AbsP { h: None }` / `Abst { ty: None }`
                // arguments (which the bootstrap discharge redexes use) recover
                // their omitted binder types from the expectation.
                let heq_expected = eq_prop(ae.clone(), be.clone());
                let proof_spine = proof_spine_args(spine);
                let heq = match proof_spine.first() {
                    Some(pr) => {
                        // A sub-proof whose spine head carries a **non-empty,
                        // fully-GENERIC (identity) instantiation table**
                        // ([`spine_head_generic_inst`]) records no actual operands —
                        // the zproof export left the nested `combination`/
                        // `reflexive`/`symmetric` reference schematic (`?f ↦ f`,
                        // `?x ↦ x`), so the local (tminst-driven) channel would
                        // "succeed" with fresh generic parameters in place of the
                        // real operands and the kernel rejects the assembled term
                        // (the dominant `expected=fun/Eq got=Eq @ AbsP` reject
                        // clusters). For exactly that shape, recover the operands
                        // bidirectionally FIRST from this `equal_elim`'s own
                        // recorded `A`/`B` (exact by construction). Legacy
                        // references (empty tables, operands on the term spine) and
                        // genuinely-instantiated references keep the historical
                        // order: the local/clean-typed channel first, the
                        // Isabelle-level bidirectional recovery only on failure.
                        // The kernel re-checks both — a wrong recovery is rejected,
                        // never miscounted.
                        if recovered {
                            // The recorded `A`/`B` carried box-internal `Free`s
                            // (unusable as expected operands) and the equation was
                            // recovered from this premise's own proposition — the
                            // Isabelle-level channel (which re-embeds the recorded
                            // terms) would re-introduce the phantom parameters, so
                            // translate against the recovered CLEAN expectation.
                            self.translate_proof_expecting(pr, &heq_expected, closure, binders)?
                        } else if spine_head_generic_inst(pr) {
                            match self
                                .translate_eq_expecting(pr, a, b, closure, binders)
                                .unwrap_or(None)
                            {
                                Some(h) => h,
                                None => self.translate_proof_expecting(
                                    pr,
                                    &heq_expected,
                                    closure,
                                    binders,
                                )?,
                            }
                        } else {
                            match self.translate_proof_expecting(
                                pr,
                                &heq_expected,
                                closure,
                                binders,
                            ) {
                                Ok(h) => h,
                                Err(first_err) => {
                                    match self.translate_eq_expecting(pr, a, b, closure, binders)? {
                                        Some(h) => h,
                                        None => return Err(first_err),
                                    }
                                }
                            }
                        }
                    }
                    None => return Err(TranslateError::Unsupported("equal_elim missing A≡B")),
                };
                let ha = match proof_spine.get(1) {
                    Some(pr) => self.translate_proof_expecting(pr, &ae, closure, binders)?,
                    None => return Err(TranslateError::Unsupported("equal_elim missing A")),
                };
                let be_is_fn = matches!(be.kind(), clean_kernel::expr::ExprKind::Pi(..));
                // On the operand-recovery path the ISA `b` carries the box-internal
                // `Free`s (unusable for the leftover-premise antecedent below); keep
                // the recovered clean `be`'s own Pi domain instead.
                let recovered_ante = match (recovered, be.kind()) {
                    (true, clean_kernel::expr::ExprKind::Pi(_, dom, _)) => Some((**dom).clone()),
                    _ => None,
                };
                // The clean result proposition `B`, kept for the spine-shape-aware
                // leftover walk below (only needed on the zproof-spine shape).
                let b_clean = zproof_spine.then(|| be.clone());
                let result = Expr::apps(
                    Expr::const_str_levels("Eq.mp", vec![Level::zero()]),
                    [ae, be, heq, ha],
                );
                // **Spine-shape-aware leftover application (zproof).** On the
                // zproof-with-spine-terms shape ([`zproof_spine`] — operands read
                // from `tminst` above), EVERY spine argument after the two
                // consumed proof premises applies to the RESULT `B`, in original
                // spine order: a TERM argument is a `⋀`-elimination (instantiate
                // `B`'s `Pi` with its embedding — the previously-shadowing `$t`
                // C-instantiation), a PROOF argument discharges the next premise
                // (translated against `B`'s current `Pi` domain, which types raw
                // `AbsP{h:None}`/`Abst{ty:None}` binders). The kernel re-checks
                // the applied result, so a wrong walk is rejected — never
                // miscounted. The legacy/no-spine-term paths below are untouched.
                if let Some(cur) = b_clean {
                    let mut cur_ty = cur;
                    let mut e = result;
                    let mut proofs_seen = 0usize;
                    let mut start = spine.len();
                    for (i, arg) in spine.iter().enumerate() {
                        if matches!(arg, SpineArg::Proof(_)) {
                            proofs_seen += 1;
                            if proofs_seen == 2 {
                                start = i + 1;
                                break;
                            }
                        }
                    }
                    for arg in &spine[start..] {
                        match arg {
                            SpineArg::Term(t) => {
                                let te = self.embed_term(t, binders)?;
                                let next = match cur_ty.kind() {
                                    clean_kernel::expr::ExprKind::Pi(_, _, cod) => {
                                        Some(cod.instantiate(&te))
                                    }
                                    _ => None,
                                };
                                if let Some(n) = next {
                                    cur_ty = n;
                                }
                                e = Expr::app(e, te);
                            }
                            SpineArg::Proof(pr) => {
                                let pi_parts = match cur_ty.kind() {
                                    clean_kernel::expr::ExprKind::Pi(_, dom, cod) => {
                                        Some(((**dom).clone(), (**cod).clone()))
                                    }
                                    _ => None,
                                };
                                let arg_e = match pi_parts {
                                    Some((dom, cod)) => {
                                        let h = self.translate_proof_expecting(
                                            pr, &dom, closure, binders,
                                        )?;
                                        // Proof-irrelevant premise: the codomain never
                                        // mentions the discharged proof binder.
                                        cur_ty = cod.instantiate(&Expr::const_str("True.intro"));
                                        h
                                    }
                                    None => self.translate_proof(pr, closure, binders)?,
                                };
                                e = Expr::app(e, arg_e);
                            }
                        }
                    }
                    return Ok(e);
                }
                // `equal_elim` consumes exactly two proof premises (`heq`, `ha`);
                // any FURTHER proof args on the spine apply to the RESULT `B` when
                // `B` is itself a function type. This arises in the connective
                // `*_def_raw` proofs, where `B` is an implication
                // `(P→Q→enc) → (P→Q→conj)` and the proof supplies its premise with
                // one more `%% h` after the `equal_elim`. Dropping those leftover
                // args left a spurious leading premise on the inferred type — the
                // conjI/disjI/conjunct/disjE `TypeMismatch`. We only fold a leftover
                // when `B` (the embedded result proposition) is a `Pi`, so an
                // `equal_elim` whose `B` is atomic is left untouched. The kernel
                // re-checks the applied result, so a wrong arg is rejected.
                let mut e = result;
                if be_is_fn {
                    // Fold exactly one leftover premise (each `*_def_raw` supplies
                    // one). The kernel re-checks the applied result regardless.
                    //
                    // When the leftover sub-proof's spine head is a **generic**
                    // (non-empty identity-table) zproof reference
                    // ([`spine_head_generic_inst`]), its actual instantiation is
                    // recorded nowhere on the node — it is pinned only by its
                    // expected proposition, which is `B`'s antecedent (carried
                    // exactly by this `equal_elim`'s own recorded `B` term). Thread
                    // it: an equation-shaped antecedent routes the sub-proof through
                    // the exact bidirectional [`Self::translate_eq_expecting`]
                    // channel, any other shape through
                    // [`Self::translate_proof_expecting`] (e.g. a `?x ≡ ?x`
                    // reflexivity theorem referenced with the identity table, whose
                    // required instance is the antecedent's own operand). Legacy /
                    // genuinely-instantiated sub-proofs keep the historical plain
                    // translation. The kernel re-checks the applied result either
                    // way — a wrong recovery is rejected, never miscounted.
                    if let Some(pr) = proof_spine.get(2) {
                        // On the operand-recovery path the ISA `b` carries the
                        // box-internal `Free`s (unusable); the antecedent is the
                        // recovered clean `be`'s own Pi domain (captured above).
                        if recovered {
                            let arg = match &recovered_ante {
                                Some(dom) => {
                                    self.translate_proof_expecting(pr, dom, closure, binders)?
                                }
                                None => self.translate_proof(pr, closure, binders)?,
                            };
                            return Ok(Expr::app(e, arg));
                        }
                        let ante = if spine_head_generic_inst(pr) {
                            split_pure_imp(b).map(|(ante, _)| ante)
                        } else {
                            None
                        };
                        let exact = match ante.and_then(|ante| pure_eq_parts(ante)) {
                            Some((l, r)) => self
                                .translate_eq_expecting(pr, l, r, closure, binders)
                                .unwrap_or(None),
                            None => None,
                        };
                        let arg = match exact {
                            Some(h) => h,
                            None => match ante {
                                Some(ante) => {
                                    let ante_e = self.embed_term(ante, binders)?;
                                    self.translate_proof_expecting(pr, &ante_e, closure, binders)?
                                }
                                None => self.translate_proof(pr, closure, binders)?,
                            },
                        };
                        e = Expr::app(e, arg);
                    }
                }
                Ok(e)
            }
            // `(A ⟹ B) ⟹ (B ⟹ A) ⟹ A ≡ B`  →  `@propext A B hAB hBA` (uses
            // the foundational `propext` axiom).
            "Pure.equal_intr" => {
                // The operand propositions `A`/`B` are recovered PREFERENTIALLY from
                // the type of the first proof argument `hab : A ⟹ B` (its embedded
                // proposition is the arrow `Pi A B`), NOT from the `tminst` `A`/`B`
                // terms. Reason: in a compound (hereditary-Harrop) instance —
                // `equal_intr_rule`, where `hab`/`hba` are the enclosing `AbsP`
                // hypotheses recovered from the STATEMENT's leading `⋀`/`⟹` chain —
                // the statement carries the operands as schematic `?phi`/`?psi`
                // (embed key `phi.0`), while the proof's `tminst` carries them as
                // *free* `phi`/`psi` (embed key `phi`). Those are DISTINCT quantified
                // params, so embedding `tminst`'s `A`/`B` yields a `propext A B (…)`
                // whose `Iff.intro A B` domain `A → B` (over the free params) does
                // not match `hab`'s type `phi.0 → psi.0` (over the schematic params)
                // — the kernel rejects `Pi FVar(phi) …` vs `Pi FVar(phi.0) …`.
                // Reading `A`/`B` off `hab`'s own proposition keeps the `propext`
                // operands definitionally identical to the hypothesis domains by
                // construction, for any keying. Falls back to the `tminst`-embedded
                // operands when the first proof's proposition is not a statically
                // recoverable arrow (the atomic-operand shape the legacy path
                // handled). The kernel re-checks either way.
                let proof_spine = proof_spine_args(spine);
                let hab_pr = proof_spine
                    .first()
                    .ok_or(TranslateError::Unsupported("equal_intr missing A⟹B"))?;
                let hba_pr = proof_spine.get(1).copied();
                let from_hab = self
                    .infer_proof_prop(hab_pr, binders)?
                    .and_then(|prop| split_arrow(&prop));
                // Second recovery channel (zproof): both legs are `AbsP` binders
                // whose discharged hypotheses ARE the operands — `hab : A ⟹ B`
                // discharges `A`, `hba : B ⟹ A` discharges `B` — and the zproof
                // export RECORDS those hypothesis terms (statement-keyed
                // schematics), while the node's own `tminst` carries the
                // box-internal `Free`-named copies (`Free phi` vs the statement's
                // `?phi.0` — distinct embedding keys, the `Pi[N]->FVar` /
                // variable-identity mismatch family). Reading the operands off the
                // recorded hypotheses keeps them definitionally identical to the
                // legs' own binder domains for any keying. Legacy legs record no
                // hypothesis (`h: None`), so this channel is zproof-only.
                let from_hyps = match (from_hab.is_some(), hab_pr, hba_pr) {
                    (
                        false,
                        IsaProof::AbsP { h: Some(a_hyp), .. },
                        Some(IsaProof::AbsP { h: Some(b_hyp), .. }),
                    ) => Some((
                        self.embed_term(a_hyp, binders)?,
                        self.embed_term(b_hyp, binders)?,
                    )),
                    _ => None,
                };
                let hyp_recovered = from_hyps.is_some();
                let (ae, be) = match from_hab.or(from_hyps) {
                    Some((dom, cod)) => (dom, cod),
                    None => {
                        // Legacy / atomic-operand fallback: embed the `tminst` (or
                        // spine) `A`/`B` terms directly. Sound when `A`/`B` are the
                        // same params the hypotheses use (the non-compound case).
                        let a = term_arg(0, "A")
                            .ok_or(TranslateError::Unsupported("equal_intr missing A"))?;
                        let b = term_arg(1, "B")
                            .ok_or(TranslateError::Unsupported("equal_intr missing B"))?;
                        let ae = self.embed_term(a, binders)?;
                        let be = self.embed_term(b, binders)?;
                        (ae, be)
                    }
                };
                // On the recorded-hypothesis recovery the legs' expected
                // propositions are known exactly (`hab : A ⟹ B`, `hba : B ⟹ A`),
                // and their bodies may contain raw `Abst { ty: None }` binders only
                // the expectation can type (the hereditary-Harrop `⋀`-crossing
                // shapes) — translate them bidirectionally. Every other case keeps
                // the historical plain translation byte-for-byte.
                let (hab, hba) = if hyp_recovered {
                    let hba_pr =
                        hba_pr.ok_or(TranslateError::Unsupported("equal_intr missing B⟹A"))?;
                    let hab = self.translate_proof_expecting(
                        hab_pr,
                        &Expr::arrow(ae.clone(), be.clone()),
                        closure,
                        binders,
                    )?;
                    let hba = self.translate_proof_expecting(
                        hba_pr,
                        &Expr::arrow(be.clone(), ae.clone()),
                        closure,
                        binders,
                    )?;
                    (hab, hba)
                } else {
                    let proofs = self.proof_args(spine, closure, binders)?;
                    let hab = proofs
                        .first()
                        .cloned()
                        .ok_or(TranslateError::Unsupported("equal_intr missing A⟹B"))?;
                    let hba = proofs
                        .get(1)
                        .cloned()
                        .ok_or(TranslateError::Unsupported("equal_intr missing B⟹A"))?;
                    (hab, hba)
                };
                Ok(propext_iff(ae, be, hab, hba))
            }
            // `(A ⟹ B) ⟹ (A ⟶ B)` — ⟹ and ⟶ both embed to clean arrow, so impI
            // is the identity `fun (h : A→B) => h`. Built closed, then any spine
            // proof args are applied (clean β-reduces the redex).
            "HOL.impI" => {
                let a = terms
                    .first()
                    .ok_or(TranslateError::Unsupported("impI missing A"))?;
                let b = terms
                    .get(1)
                    .ok_or(TranslateError::Unsupported("impI missing B"))?;
                let dom = Expr::arrow(self.embed_term(a, binders)?, self.embed_term(b, binders)?);
                let base = Expr::lam(BinderInfo::Default, dom, Expr::bvar(0));
                self.apply_proof_args(base, spine, closure, binders)
            }
            // `(A ⟶ B) ⟹ A ⟹ B`  →  `fun (h:A→B)(a:A) => h a`, then apply spine.
            "HOL.mp" => {
                let a = terms
                    .first()
                    .ok_or(TranslateError::Unsupported("mp missing A"))?;
                let b = terms
                    .get(1)
                    .ok_or(TranslateError::Unsupported("mp missing B"))?;
                let ae = self.embed_term(a, binders)?;
                let be = self.embed_term(b, binders)?;
                let inner = Expr::lam(
                    BinderInfo::Default,
                    ae.lift(1),
                    Expr::app(Expr::bvar(1), Expr::bvar(0)),
                );
                let base = Expr::lam(BinderInfo::Default, Expr::arrow(ae, be), inner);
                self.apply_proof_args(base, spine, closure, binders)
            }
            // `s = t ⟹ P s ⟹ P t` — built closed as
            // `fun (heq : @Eq α s t) (hps : P s) => @Eq.subst α P s t heq hps`,
            // then any spine proof args are applied (β-reduces). schematic term
            // order is s, t, P.
            "HOL.subst" => {
                // PAxm spine applies terms in order [t, s, P] (verified against
                // the real proof tree), so s = terms[1], t = terms[0].
                let t = terms
                    .first()
                    .ok_or(TranslateError::Unsupported("subst missing t"))?;
                let s = terms
                    .get(1)
                    .ok_or(TranslateError::Unsupported("subst missing s"))?;
                let p = terms
                    .get(2)
                    .ok_or(TranslateError::Unsupported("subst missing motive"))?;
                let alpha = self.infer_type(s, binders)?;
                let se = self.embed_term(s, binders)?;
                let te = self.embed_term(t, binders)?;
                let motive = self.embed_term(p, binders)?;
                // HOL.subst is polymorphic over `'a::type`, so its premises are
                // [sort-constraint (→ True), heq : s=t, hps : P s] in that order.
                // Discharge all three; clean β-reduces the applied spine args
                // ([True.intro, heq, hps]).
                // binder0 c:True; binder1 heq:@Eq α s t (+1); binder2 hps:P s (+2).
                let heq_ty = Expr::apps(
                    Expr::const_str_levels("Eq", vec![obj_level()]),
                    [alpha.clone(), se.clone(), te.clone()],
                )
                .lift(1);
                let hps_ty = Expr::app(motive.clone(), se.clone()).lift(2);
                // body under 3 binders: term args +3, heq = bvar1, hps = bvar0.
                let body = Expr::apps(
                    Expr::const_str_levels("Eq.subst", vec![obj_level()]),
                    [
                        alpha.lift(3),
                        motive.lift(3),
                        se.lift(3),
                        te.lift(3),
                        Expr::bvar(1),
                        Expr::bvar(0),
                    ],
                );
                let base = Expr::lam(
                    BinderInfo::Default,
                    Expr::const_str("True"),
                    Expr::lam(
                        BinderInfo::Default,
                        heq_ty,
                        Expr::lam(BinderInfo::Default, hps_ty, body),
                    ),
                );
                self.apply_proof_args(base, spine, closure, binders)
            }
            // `(⋀x. f x = g x) ⟹ f = g`. Like subst it carries a leading sort
            // constraint, so build `fun (c:True) (h : ∀x, f x = g x) =>
            // @funext α (fun _=>β) f g h` and apply the spine ([True.intro, h]).
            // spine term order is [f, g].
            // `OFCLASS('a,type) ⟹ OFCLASS('b,type) ⟹ (⋀x. f x = g x) ⟹ f = g`.
            // The two sort constraints are discharged by enclosing `True` lambdas
            // (and their spine witnesses dropped); the funext hypothesis stays a
            // premise, so ext's residual proof is
            // `fun (h : ∀x. f x = g x) => @funext α (fun _=>β) f g h`.
            "HOL.ext" => {
                let f = terms
                    .first()
                    .ok_or(TranslateError::Unsupported("ext missing f"))?;
                let g = terms
                    .get(1)
                    .ok_or(TranslateError::Unsupported("ext missing g"))?;
                let f_ty = self.infer_type(f, binders)?;
                let (dom, cod) = split_arrow(&f_ty)
                    .ok_or(TranslateError::Unsupported("ext f not a function"))?;
                let fe = self.embed_term(f, binders)?;
                let ge = self.embed_term(g, binders)?;
                // H = ∀(x:α). @Eq β (f x) (g x)
                let h_ty = Expr::pi(
                    BinderInfo::Default,
                    dom.clone(),
                    Expr::apps(
                        Expr::const_str_levels("Eq", vec![obj_level()]),
                        [
                            cod.clone().lift(1),
                            Expr::app(fe.clone().lift(1), Expr::bvar(0)),
                            Expr::app(ge.clone().lift(1), Expr::bvar(0)),
                        ],
                    ),
                );
                // body under the h binder (depth 1): @funext α (fun _=>β) f g h
                let beta = Expr::lam(BinderInfo::Default, dom.clone().lift(1), cod.lift(2));
                let body = Expr::apps(
                    Expr::const_str_levels("funext", vec![obj_level(), obj_level()]),
                    [dom.lift(1), beta, fe.lift(1), ge.lift(1), Expr::bvar(0)],
                );
                Ok(Expr::lam(BinderInfo::Default, h_ty, body))
            }
            // `(⋀x. f x ≡ g x) ⟹ (λx. f x) ≡ (λx. g x)` — Pure's β-extensionality
            // rule. The conclusion `(λx.f x) ≡ (λx.g x)` is `f ≡ g` by eta, so this
            // is exactly `funext` over f, g. Unlike `HOL.ext` it carries NO leading
            // sort constraint: the spine is `axm % f % g %% (⋀x. f x ≡ g x)`, so the
            // pointwise-equality proof is supplied directly on the spine (the
            // `Abst x. …` argument translates to a clean `fun (x:α) => _` of type
            // `∀x, f x = g x`). We build `@funext α (fun _=>β) f g h` directly.
            // spine term order is [f, g].
            "Pure.abstract_rule" => {
                let f = term_arg(0, "f")
                    .ok_or(TranslateError::Unsupported("abstract_rule missing f"))?;
                let g = term_arg(1, "g")
                    .ok_or(TranslateError::Unsupported("abstract_rule missing g"))?;
                // f : α → β; recover α, β from f's embedded function type.
                let f_ty = self.infer_type(f, binders)?;
                let (dom, cod) = split_arrow(&f_ty).ok_or(TranslateError::Unsupported(
                    "abstract_rule f not a function",
                ))?;
                let fe = self.embed_term(f, binders)?;
                let ge = self.embed_term(g, binders)?;
                // The `⋀x. f x ≡ g x` sub-proof translates to `fun (x:α) => _`,
                // i.e. a clean `h : ∀x, f x = g x` — exactly funext's hypothesis.
                let h = self.first_proof_arg(spine, closure, binders)?;
                // funext's β is the constant family `fun (_:α) => β`.
                let beta = Expr::lam(BinderInfo::Default, dom.clone(), cod.lift(1));
                Ok(Expr::apps(
                    Expr::const_str_levels("funext", vec![obj_level(), obj_level()]),
                    [dom, beta, fe, ge, h],
                ))
            }
            // Classical excluded middle, HOL form. The schematic `?P : bool`
            // (spine `terms[0]`) embeds to a `Prop`, and `HOL.True_or_False`'s
            // statement is the disj-encoding
            //   `∀C. ((P = True_enc) → C) → ((P = False_enc) → C) → C`,
            // where `True_enc = (λx:Prop.x) = (λx:Prop.x)` and
            // `False_enc = ∀Q:Prop. Q` are the `connective_encoding`s. We prove
            // it by case-splitting `Classical.em P : Or P (P → False)` with
            // `Or.rec` (motive `fun _ => C`):
            //   - P holds (`hp`):  `f (propext P True_enc (λ_. Eq.refl (λx.x)) (λ_. hp))`
            //   - ¬P holds (`hnp`): `g (propext P False_enc (λhp. False.elim (hnp hp)) (λhf. hf P))`
            // Closure ⊆ {propext, Classical.choice (via Classical.em), Quot.sound}.
            "HOL.True_or_False" => {
                let p_tm = terms
                    .first()
                    .ok_or(TranslateError::Unsupported("True_or_False missing P"))?;
                let p = self.embed_term(p_tm, binders)?;
                let true_enc = connective_encoding("HOL.True")
                    .ok_or(TranslateError::Unsupported("True encoding missing"))?;
                let false_enc = connective_encoding("HOL.False")
                    .ok_or(TranslateError::Unsupported("False encoding missing"))?;
                Ok(true_or_false_proof(&p, &true_enc, &false_enc))
            }
            // `bool :: type` — bare class fact, statement embeds to `True`.
            "HOL.arity_type_bool" => Ok(Expr::const_str("True.intro")),
            // `fun :: (type, type) type` — conditional arity
            // `OFCLASS('a) ⟹ OFCLASS('b) ⟹ OFCLASS('a⇒'b)` = `True → True → True`,
            // so `fun (_:True) (_:True) => True.intro`.
            "HOL.fun_arity" => Ok(Expr::lam(
                BinderInfo::Default,
                Expr::const_str("True"),
                Expr::lam(
                    BinderInfo::Default,
                    Expr::const_str("True"),
                    Expr::const_str("True.intro"),
                ),
            )),
            // Pure's meta-conjunction **definition** axiom, referenced as a leaf
            // inside a consumer proof (an `equal_elim`/`Eq.mp` minor premise, …):
            //   `Pure.conjunction A B ≡ (⋀C. (A⟹B⟹C)⟹C)`.
            // Under `Pure.conjunction → And`, `Pure.all → Π`, `Pure.imp → →` its
            // statement embeds to `@Eq Prop (And A B) E`, `E = ∀C.(A→B→C)→C` the
            // impredicative encoding. `And` is inductive, NOT defeq to `E`, so we
            // prove the genuine equality via `propext` of the constructive `And ↔ E`
            // isomorphism (foundational: `And.{intro,left,right}` + `propext`) — the
            // SAME proof [`prove_pure_conjunction_def`] builds for the def node. The
            // `A`/`B` conjuncts (both `prop`) come from the leaf's `tminst`/spine;
            // `E` is built from the embedded `A`/`B`. The kernel re-checks the result
            // against the consuming proof's expectation, so a wrong shape is rejected.
            "Pure.conjunction_def" => {
                let a = term_arg(0, "A")
                    .ok_or(TranslateError::Unsupported("conjunction_def missing A"))?;
                let b = term_arg(1, "B")
                    .ok_or(TranslateError::Unsupported("conjunction_def missing B"))?;
                let ae = self.embed_term(a, binders)?;
                let be = self.embed_term(b, binders)?;
                let and_ab = Expr::apps(Expr::const_str("And"), [ae.clone(), be.clone()]);
                // E = ∀(C:Prop). (A → B → C) → C.
                let e = prop_pi(0x1_7e10, |c| {
                    Expr::arrow(
                        Expr::arrow(ae.clone(), Expr::arrow(be.clone(), c.clone())),
                        c,
                    )
                });
                // Reuse the def-node bridge over the embedded `@Eq Prop (And A B) E`.
                let stated = Expr::apps(
                    Expr::const_str_levels("Eq", vec![obj_level()]),
                    [Expr::prop(), and_ab, e],
                );
                prove_pure_conjunction_def(name, &stated)
                    .ok_or(TranslateError::Unsupported("conjunction_def bridge shape"))
            }
            // Pure's `term` judgement-marker **definition** axiom, referenced as a
            // leaf:  `Pure.term x ≡ (⋀A. A ⟹ A)` (`Pure.term_def`). `Pure.term`
            // embeds (via [`Ctx::embed_const_term`]) to its def-const `λ_. ∀A. A → A`,
            // so the statement is `@Eq Prop (Pure.term-defconst α x) R` whose two
            // sides δβ-reduce to the SAME `∀A. A → A`. We prove the genuine (faithful,
            // distinct-operand) equation by `Eq.refl Prop (embed lhs)`, which the
            // kernel accepts iff `embed lhs` δβ-reduces to `embed rhs` — so a
            // non-reducible statement is rejected, never miscounted. The LHS is
            // rebuilt as an `IsaTerm` (`Pure.term x`) from the leaf's argument.
            "Pure.term_def" => {
                let arg =
                    term_arg(0, "x").ok_or(TranslateError::Unsupported("term_def missing arg"))?;
                // The argument's HOL type carries the marker's domain `'a`.
                let arg_ty = match arg {
                    IsaTerm::Const { t, .. } | IsaTerm::Free { t, .. } | IsaTerm::Var { t, .. } => {
                        t.clone()
                    }
                    _ => return Err(TranslateError::Unsupported("term_def arg has no type")),
                };
                let marker_ty = IsaType::Type {
                    n: "fun".to_string(),
                    a: vec![
                        arg_ty,
                        IsaType::Type {
                            n: "prop".to_string(),
                            a: vec![],
                        },
                    ],
                };
                let lhs_tm = IsaTerm::App {
                    f: Box::new(IsaTerm::Const {
                        n: "Pure.term".to_string(),
                        t: marker_ty,
                    }),
                    a: Box::new(arg.clone()),
                };
                let lhs = self.embed_term(&lhs_tm, binders)?;
                Ok(Expr::apps(
                    Expr::const_str_levels("Eq.refl", vec![Level::zero()]),
                    [Expr::prop(), lhs],
                ))
            }
            // Pure's `sort_constraint` **definition** axiom, referenced as a leaf:
            //   `Pure.sort_constraint TYPE('a) ≡ Pure.term TYPE('a)`.
            // The LHS `Pure.sort_constraint …` is a sort constraint ([`is_class_app`])
            // erased to the vacuous `True`; the RHS `Pure.term TYPE('a)` embeds (via
            // the `Pure.term` def-const) to a term δβ-equal to `∀A. A → A`. `True` is
            // NOT defeq to that, so we prove the genuine `True = R` equality via the
            // dedicated `propext` bridge [`prove_sort_constraint_def`] over the
            // embedded `@Eq Prop True R` (foundational: `propext` + `True.intro`). The
            // RHS `R` is rebuilt from the leaf's `TYPE('a)` argument (a `Pure.type`
            // term of type `itself('a)`). Kernel-re-checked against the consumer's
            // expectation, so a wrong shape is rejected — never miscounted.
            "Pure.sort_constraint_def" => {
                // The argument is `TYPE('a)` (`Pure.type : itself('a)`). In the
                // `zproof` shape `'a` is supplied through `tyinst` (NOT as a `tminst`
                // term), so reconstruct the `Pure.type` term of type `itself('a)`
                // from the leaf's `tyinst` entry; the legacy path (a `tminst`/spine
                // `Pure.type` term) is used when present.
                let arg: IsaTerm = match term_arg(0, "x") {
                    Some(t) => t.clone(),
                    None => {
                        let obj_ty = tyinst.first().map(|ti| ti.ty.clone()).ok_or(
                            TranslateError::Unsupported("sort_constraint_def missing 'a tyinst"),
                        )?;
                        IsaTerm::Const {
                            n: "Pure.type".to_string(),
                            t: IsaType::Type {
                                n: "itself".to_string(),
                                a: vec![obj_ty],
                            },
                        }
                    }
                };
                let arg_ty = match &arg {
                    IsaTerm::Const { t, .. } | IsaTerm::Free { t, .. } | IsaTerm::Var { t, .. } => {
                        t.clone()
                    }
                    _ => {
                        return Err(TranslateError::Unsupported(
                            "sort_constraint_def arg has no type",
                        ))
                    }
                };
                // Embed the RHS `Pure.term TYPE('a)` through the def-const routing.
                let rhs_tm = IsaTerm::App {
                    f: Box::new(IsaTerm::Const {
                        n: "Pure.term".to_string(),
                        t: IsaType::Type {
                            n: "fun".to_string(),
                            a: vec![
                                arg_ty,
                                IsaType::Type {
                                    n: "prop".to_string(),
                                    a: vec![],
                                },
                            ],
                        },
                    }),
                    a: Box::new(arg.clone()),
                };
                let rhs = self.embed_term(&rhs_tm, binders)?;
                // The stored/expected equation is `@Eq Prop True R`.
                let stated = Expr::apps(
                    Expr::const_str_levels("Eq", vec![obj_level()]),
                    [Expr::prop(), Expr::const_str("True"), rhs],
                );
                prove_sort_constraint_def(name, &stated).ok_or(TranslateError::Unsupported(
                    "sort_constraint_def bridge shape",
                ))
            }
            // Point-free HOL logical **definition** axioms, referenced as a leaf
            // inside a consumer proof: `HOL.All_def_raw`/`Ex_def_raw`/`Uniq_def_raw`/
            // `Ex1_def_raw`/`Let_def_raw`/`induct_forall_def_raw`/
            // `induct_equal_def_raw`/`NO_MATCH_def_raw`, each stating
            // `C ≡ (λargs. body)`. The leaf carries only its object type(s) in
            // `tyinst`; [`Ctx::prove_pointfree_def_raw_leaf`] reconstructs the full
            // point-free equation from those types and proves it via the SAME path
            // the point-free theorem arm uses (def-const reflexivity for
            // `Ex/Uniq/Ex1/Let/induct_*/NO_MATCH`, a `funext`/`propext` bridge for
            // `All`). The kernel re-checks the result against the consuming proof's
            // expectation, so a wrong shape is rejected — never miscounted.
            "HOL.All_def_raw"
            | "HOL.Ex_def_raw"
            | "HOL.Uniq_def_raw"
            | "HOL.Ex1_def_raw"
            | "HOL.Let_def_raw"
            | "HOL.induct_forall_def_raw"
            | "HOL.induct_equal_def_raw"
            | "HOL.NO_MATCH_def_raw" => {
                // The primary object type `'a` is the first `tyinst` entry; the
                // secondary (`Let`'s value type / `NO_MATCH`'s second arg) is the
                // next entry when present, else `'a`.
                let alpha =
                    tyinst
                        .first()
                        .map(|ti| ti.ty.clone())
                        .ok_or(TranslateError::Unsupported(
                            "pointfree def-raw leaf missing 'a",
                        ))?;
                let beta = tyinst
                    .get(1)
                    .map(|ti| ti.ty.clone())
                    .unwrap_or(alpha.clone());
                match self.prove_pointfree_def_raw_leaf(name, &alpha, &beta, binders)? {
                    Some(p) => Ok(p),
                    None => Err(TranslateError::UnmappedAxiom(name.to_string())),
                }
            }
            // The `HOL.ATP` first-order connective aliases (round-9), referenced
            // as a `…_def_raw` leaf: `fFalse ≡ False`, `fNot ≡ λP. ¬P`,
            // `fconj ≡ λP Q. P ∧ Q`, `fAll ≡ λP. All P`, `fequal ≡ λx y. x = y`,
            // `fComp ≡ λP x. ¬ P x`, `fChoice ≡ Eps`, … Reconstructed and proved
            // exactly like the point-free HOL leaves above (each alias's
            // def-const δβ-unfolds to the aliased connective's own embedding, so
            // the equation is reflexive; see `pointfree_defs.rs`). The
            // monomorphic aliases (`fFalse`/`fTrue`/`fNot`/`fconj`/`fdisj`/
            // `fimplies` are `bool`-only) carry no `tyinst` — their object type
            // defaults to `bool` (unused by the reconstruction); the polymorphic
            // ones carry `'a` as the sole entry.
            "ATP.fFalse_def_raw"
            | "ATP.fTrue_def_raw"
            | "ATP.fNot_def_raw"
            | "ATP.fconj_def_raw"
            | "ATP.fdisj_def_raw"
            | "ATP.fimplies_def_raw"
            | "ATP.fAll_def_raw"
            | "ATP.fEx_def_raw"
            | "ATP.fequal_def_raw"
            | "ATP.fComp_def_raw"
            | "ATP.fChoice_def_raw" => {
                let alpha = tyinst
                    .first()
                    .map(|ti| ti.ty.clone())
                    .unwrap_or(IsaType::Type {
                        n: "HOL.bool".to_string(),
                        a: Vec::new(),
                    });
                match self.prove_pointfree_def_raw_leaf(name, &alpha, &alpha, binders)? {
                    Some(p) => Ok(p),
                    None => Err(TranslateError::UnmappedAxiom(name.to_string())),
                }
            }
            // HOL's `the_eq_trivial` (`(THE x. x = a) = a`), referenced as a leaf
            // inside a consumer proof. The leaf's schematic point `?a` is the spine /
            // `tminst` term argument named `a`; its object type `α` is `a`'s type. We
            // build the same kernel proof the top-level arm uses
            // ([`prove_the_eq_trivial_core`] — `Subtype.property` of the guard-subtype
            // choice, applied to `∃y. y = a`), whose LHS is the routed epsilon
            // `isabelle.def.HOL.The α (Nonempty.intro α a) (λx. x = a)` — matching the
            // consumer's own `instance_unfold`-routed embedding of `THE x. x = a`. The
            // kernel re-checks the proof against the consumer's expectation, so a wrong
            // reconstruction is rejected — never miscounted. Foundational closure
            // (`Classical.choice`/`propext`/`Quot.sound`).
            "HOL.the_eq_trivial" => {
                let a_tm = term_arg(0, "a").ok_or(TranslateError::Unsupported(
                    "the_eq_trivial leaf missing point `a`",
                ))?;
                let alpha = self.infer_type(a_tm, binders)?;
                let a = self.embed_term(a_tm, binders)?;
                Ok(prove_the_eq_trivial_core(&alpha, &a))
            }
            // Point-free order-extremum **definition** axioms, referenced as a leaf:
            // `Least/Greatest ≡ λle P. THE x. P x ∧ (∀y. P y → x ≼ y)`. The leaf
            // carries the object type `'a` in `tyinst`; the bare `Least`/`Greatest`
            // embeds to its `@isabelle.def.<C> α hne` def-const (η/δ-unfolding to that
            // `λle P. THE …`), so the equation is reflexive (`Eq.refl`). See
            // [`Ctx::prove_extremum_def_raw_leaf`].
            n if n.ends_with("_def_raw") && is_order_extremum(n.trim_end_matches("_def_raw")) => {
                let base = n.trim_end_matches("_def_raw");
                let alpha =
                    tyinst
                        .first()
                        .map(|ti| ti.ty.clone())
                        .ok_or(TranslateError::Unsupported(
                            "extremum def-raw leaf missing 'a",
                        ))?;
                self.prove_extremum_def_raw_leaf(base, &alpha)
            }
            // GENERAL **arity facts** `T :: (type, …) type` — Isabelle records, for
            // every type constructor `T`, an axiom `…arity_type_T` whose statement
            // (after the per-argument `OFCLASS('aᵢ, type) ⟹` sort premises) is the
            // base-sort membership `OFCLASS(T …, type)`. Under the CIC embedding
            // `HOL.type_class TYPE(…)` is the vacuous `True` (every clean type
            // inhabits the universal sort) — see `embed_class_membership` — so the
            // whole statement embeds to `True → … → True`. Each leading `OFCLASS`
            // premise is already discharged by an enclosing `fun (_:True) =>` (the
            // `AbsP` leading arm in `translate_proof`), so the residual axiom body is
            // exactly the conclusion `True`, proved by `True.intro` — identical to
            // the hand-written `HOL.arity_type_bool` / `HOL.fun_arity` arms above,
            // generalised to ALL constructors (`Nat.nat`, `Nat.ind`,
            // `Product_Type.unit`, `Product_Type.prod`, `Set.set`, `Sum_Type.sum`,
            // …). Conservative + KV-preserving: `True.intro` is axiom-free, and the
            // kernel re-checks `True.intro : True` against the embedded statement, so
            // a mis-shaped arity (whose statement did NOT embed to `True`) is rejected
            // — never miscounted. The marker `.arity_type_` is Isabelle's stable name
            // for exactly these constructor-arity records.
            n if n.contains(".arity_type_") => Ok(Expr::const_str("True.intro")),
            // GENERIC registered-constant point-free definitional leaf (G7): a
            // `…_def_raw` / `…_def` axiom, referenced as a LEAF inside a consumer
            // proof, whose bare constant `C` is registered as a poly-inst clean
            // `Definition` (`register_poly_inst_def` — the r17/G1/G3 family:
            // `Code_Numeral`/`Int`/`Num` ground towers, the 2-tvar BNF/relation
            // combinators, `Sum_Type.Plus`, …). The hand-listed HOL/ATP/extremum
            // `_def_raw` arms above prove exactly this shape for a FIXED constant
            // set; this arm generalises them to ANY registered constant. The bare
            // `C` embeds (via the poly-inst registry) to
            // `@isabelle.polyinst.<c> α op₁ … opₘ`, whose δ/η-unfold IS the
            // registered point-free body — so the definitional equation
            // `C ≡ (λargs. body)` is GENUINELY reflexive (`Eq.refl`), never a
            // tautology (the consumer's stored proposition keeps the real
            // `C ≡ body` shape and the kernel accepts the reflexive proof ONLY
            // when `embed C` δ-reduces to `embed body`). The object types are the
            // leaf's `tyinst`; the equation's operand type is `C`'s full
            // instantiated HOL type. The kernel re-checks the produced term
            // against the consuming proof's expectation, so a wrong reconstruction
            // (or a non-reflexive `_def`) is rejected — never miscounted; and the
            // arm fires ONLY on `_def`/`_def_raw` names that fall through every
            // earlier arm (all currently `UnmappedAxiom` rejects), returning
            // `UnmappedAxiom` unchanged for any non-registered base, so it is
            // strictly additive. Foundational closure follows from the registered
            // `Definition`'s (kernel-accepted, foundational-only) body. Instance
            // ALIAS entries (`alias_of.is_some()`) are skipped — their LINK axiom
            // is a different (`method ≡ impl`) reflexive shape.
            n if n.ends_with("_def_raw") || n.ends_with("_def") => {
                let base = registered_poly_inst_leaf_base(n);
                match self.poly_inst_registry.get(base).cloned() {
                    Some(info) if info.alias_of.is_none() => {
                        // The constant's instantiated HOL type: substitute the
                        // leaf's `tyinst` into the registered (schematic) `fn_ty`.
                        // Empty `tyinst` (legacy export) leaves it schematic — the
                        // tvars then embed as type params, exactly as the
                        // standalone `_def` arm handles them.
                        let inst_ty = subst_isa_tyinst(&info.fn_ty, tyinst);
                        match self.embed_poly_inst_use(base, &inst_ty)? {
                            Some(embed_c) => {
                                let eq_ty = self.embed_type(&inst_ty)?;
                                Ok(Expr::apps(
                                    Expr::const_str_levels("Eq.refl", vec![obj_level()]),
                                    [eq_ty, embed_c],
                                ))
                            }
                            None => Err(TranslateError::UnmappedAxiom(name.to_string())),
                        }
                    }
                    _ => Err(TranslateError::UnmappedAxiom(name.to_string())),
                }
            }
            other => Err(TranslateError::UnmappedAxiom(other.to_string())),
        }
    }
}

/// Recover the bare constant name of a point-free definitional leaf axiom
/// `<C>_def_raw` / `<C>_def` (G7) by stripping the definitional suffix, so the
/// base can be looked up in the poly-inst registry. `_def_raw` is tried first
/// (`<C>_def_raw` also ends with `_def`); a name with neither suffix is
/// returned unchanged (the caller's guard restricts entry to the two shapes).
fn registered_poly_inst_leaf_base(name: &str) -> &str {
    name.strip_suffix("_def_raw")
        .or_else(|| name.strip_suffix("_def"))
        .unwrap_or(name)
}

/// Substitute a leaf reference's schematic **type**-instantiation table into a
/// registered constant's schematic HOL type: replace every `TVar { n, i }` that
/// appears in `tyinst` with its concrete `ty`, recursively. An empty table
/// (legacy export) is the identity, leaving the type schematic (its tvars then
/// embed as type params). Used by the G7 generic `_def_raw` leaf arm to
/// instantiate the registered `fn_ty` at the consumer's use types before
/// embedding the bare constant.
fn subst_isa_tyinst(ty: &IsaType, tyinst: &[IsaTypeInst]) -> IsaType {
    match ty {
        IsaType::TVar { n, i } => tyinst
            .iter()
            .find(|ti| ti.n == *n && ti.i == *i)
            .map(|ti| ti.ty.clone())
            .unwrap_or_else(|| ty.clone()),
        IsaType::TFree { .. } => ty.clone(),
        IsaType::Type { n, a } => IsaType::Type {
            n: n.clone(),
            a: a.iter().map(|t| subst_isa_tyinst(t, tyinst)).collect(),
        },
    }
}
