// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `Ctx::embed_term` — the HOL term embedder's top-level dispatch (non-`Const`
//! shapes). `Const`-headed terms delegate to `embed_const_term` (see
//! `embed_const`/`embed_const2`). Moved verbatim from the original single-file
//! `isabelle_pure_translate` module; behaviour is byte-identical.

use clean_kernel::{BinderInfo, Expr};

use super::super::isabelle_pure::IsaTerm;
use super::*;

impl Ctx {
    /// Embed a HOL term to a clean `Expr`. `binders` is the stack of local
    /// `Abs` binder clean-types (innermost last) for de Bruijn resolution.
    pub(crate) fn embed_term(
        &mut self,
        tm: &IsaTerm,
        binders: &mut Vec<Binder>,
    ) -> Result<Expr, TranslateError> {
        match tm {
            // Identity coercions in this embedding: Trueprop (bool→prop) and
            // Pure.prop (the `PROP P ≡ P` protect wrapper).
            IsaTerm::App { f, a }
                if is_const(f, "HOL.Trueprop")
                    || is_const(f, "Trueprop")
                    || is_const(f, "Pure.prop") =>
            {
                self.embed_term(a, binders)
            }
            // Sort-membership constraints (`OFCLASS('a, c_class)` = `c_class _`).
            // For a **base** sort whose class predicate carries no axioms
            // (`HOL.type_class`, or a `c_class` not registered as structured) this
            // is vacuous in the CIC embedding (every type inhabits the universal
            // sort) → the trivially-true `True`, paired with `PClass`/structural
            // witnesses translating to `True.intro`. For a **structured** class
            // registered in [`Self::class_registry`] (genuine axioms — e.g.
            // `semigroup_add`'s associativity) it is the REAL membership
            // proposition `c_class α ops` (the registered def-const applied to the
            // object type and the class operations), so the class axioms stay
            // honest hypotheses rather than being erased. The kernel δ-unfolds the
            // def-const to the axiom conjunction, re-checking the consuming proof.
            IsaTerm::App { f, .. } if is_class_app(f) => self.embed_class_membership(tm),
            // Pure universal `⋀x:T. P x` = `Pure.all (λx. P)` → clean `Pi (x:T) P`.
            IsaTerm::App { f, a } if is_const(f, "Pure.all") || is_const(f, "Pure.all_def") => {
                if let IsaTerm::Abs { t, b, .. } = a.as_ref() {
                    let dom = self.embed_type(t)?;
                    binders.push(Binder {
                        kind: BKind::Term,
                        ty: dom.clone(),
                    });
                    let body = self.embed_term(b, binders);
                    binders.pop();
                    return Ok(Expr::pi(BinderInfo::Default, dom, body?));
                }
                Err(TranslateError::Unsupported("Pure.all without lambda"))
            }
            // HOL universal `∀x:T. P x` = `HOL.All (λx:T. P)` → clean `Pi (x:T) P`.
            // The faithful Prop-level encoding of HOL's binder quantifier: it makes
            // the connective `_def` theorems (which spell `conj`/`disj`/`False` via
            // `HOL.All`) reflexivity under the embedding, since e.g.
            //   `HOL.All (λR. (P→Q→R)→R)` ≡ `∀R. (P→Q→R)→R` = the `conj` encoding.
            // Honest over an arbitrary object type T (clean `Pi` quantifies any
            // sort); the kernel re-checks the resulting term either way.
            IsaTerm::App { f, a } if is_const(f, "HOL.All") => {
                if let IsaTerm::Abs { t, b, .. } = a.as_ref() {
                    let dom = self.embed_type(t)?;
                    binders.push(Binder {
                        kind: BKind::Term,
                        ty: dom.clone(),
                    });
                    let body = self.embed_term(b, binders);
                    binders.pop();
                    return Ok(Expr::pi(BinderInfo::Default, dom, body?));
                }
                // `HOL.All` applied to a non-lambda predicate `P` (a bare variable,
                // as in `All_def` itself): η-expand to `∀(x:α). P x` so the binder
                // quantifier is still the faithful clean `Pi`. The domain `α` is the
                // operand type of `HOL.All`'s own type `(α ⇒ bool) ⇒ bool`. This
                // keeps `HOL.All P` and `HOL.All (λx. body)` embedding *uniformly*
                // to a clean `Pi`, which is what the `All_def` bridge proof targets.
                if let IsaTerm::Const { t, .. } = f.as_ref() {
                    if let Some(pred_ty) = eq_operand_type(t) {
                        if let Some(dom_ty) = eq_operand_type(pred_ty) {
                            let dom = self.embed_type(dom_ty)?;
                            // `P` is closed w.r.t. the new binder; lift its embedding
                            // over the fresh `x:α` binder and apply it to `bvar 0`.
                            let pe = self.embed_term(a, binders)?;
                            let body = Expr::app(pe.lift(1), Expr::bvar(0));
                            return Ok(Expr::pi(BinderInfo::Default, dom, body));
                        }
                    }
                }
                // Could not read the predicate's domain type — fall through to a
                // plain application of the abstracted `All` constant. The kernel
                // still re-checks the result.
                self.embed_app(f, a, binders)
            }
            // HOL existential `∃x:α. P x` = `HOL.Ex P` → the faithful semantic
            // encoding `∀(Q:Prop). (∀(x:α). P x → Q) → Q`. This makes `Ex_def`
            // (`Ex P ≡ ∀Q. (∀x. P x ⟶ Q) ⟶ Q`) reflexivity under the embedding —
            // its RHS already spells exactly this `∀Q.…` form (via `HOL.All`/
            // `HOL.implies`), so both sides coincide. Works for a lambda or a bare
            // predicate `P` alike; the kernel re-checks the result.
            IsaTerm::App { f, a } if is_const(f, "HOL.Ex") => {
                if let IsaTerm::Const { t, .. } = f.as_ref() {
                    if let Some(pred_ty) = eq_operand_type(t) {
                        if let Some(dom_ty) = eq_operand_type(pred_ty) {
                            let dom = self.embed_type(dom_ty)?;
                            let pe = self.embed_term(a, binders)?;
                            return Ok(ex_encoding(&dom, &pe));
                        }
                    }
                }
                self.embed_app(f, a, binders)
            }
            // HOL definite description `THE x. P x` = `HOL.The P` → clean's classical
            // epsilon `isabelle.def.HOL.The α (Nonempty.intro α w) (embed P)`, where
            // `w : α` is a nonemptiness witness (HOL types are always nonempty, but
            // clean's `Classical.choice` needs the witness explicitly — see
            // [`super::hilbert`]). The witness is recovered from the predicate when it
            // is a **singleton** `λx. x = a` (`the_eq_trivial`; witness `a`), which is
            // the only shape whose `The` value the def-axioms pin down. Gated on
            // `instance_unfold` (escalating final pass → strictly additive: bare /
            // earlier-pass occurrences keep the opaque `const:HOL.The` param). When no
            // witness is available the arm falls through to the opaque embedding, so a
            // `The`-using node is never regressed. The kernel re-checks the result, so
            // a wrong witness/predicate is rejected — never miscounted.
            IsaTerm::App { f, a: pred } if self.instance_unfold && is_const(f, "HOL.The") => {
                if let Some(e) = self.embed_hol_the(f, pred, binders)? {
                    return Ok(e);
                }
                self.embed_app(f, pred, binders)
            }
            // `Set.Collect P` (`('a ⇒ bool) ⇒ 'a set`) — the predicate→set
            // coercion. Under the `'a set = 'a → Prop` model a set IS its
            // membership predicate, so `Collect` is the **identity**: `Collect P`
            // embeds to `embed(P)`. This makes the set-lattice instance defs
            // reflexive (their RHS is `Collect (<op on the 'a⇒bool instance>)`,
            // which then coincides with the LHS `op` on the unified `'a set` /
            // `'a ⇒ bool` clean type).
            IsaTerm::App { f, a } if is_const(f, "Set.Collect") => self.embed_term(a, binders),
            // `Set.member x S` (`'a ⇒ 'a set ⇒ bool`) — set membership `x ∈ S`.
            // Under the predicate model `S : 'a → Prop`, so `x ∈ S` is just the
            // application `S x`. (The export curries it as `App(App(member,x),S)`.)
            IsaTerm::App { f, a: set_arg } if is_member_app(f) => {
                if let IsaTerm::App { a: elem, .. } = f.as_ref() {
                    let s = self.embed_term(set_arg, binders)?;
                    let x = self.embed_term(elem, binders)?;
                    return Ok(Expr::app(s, x));
                }
                Err(TranslateError::Unsupported("Set.member malformed spine"))
            }
            // Pure implication `A ⟹ B` → clean `Pi (_:A) B` (B embedded under the
            // hypothesis binder so its bvars stay correct — no manual lift).
            IsaTerm::App { f, a: rhs } => {
                // A **fully-applied `HOL.If` with a literal `HOL.True`/`HOL.False`
                // condition** — `if True then x else y` / `if False then x else y`.
                // HOL's `if_True`/`if_False` simp lemmas state these denote the THEN
                // / ELSE branch outright, so we embed directly to that branch's
                // image (`embed x` / `embed y`) instead of routing through the
                // polymorphic `isabelle.def.HOL.If` def-const (whose `Decidable`
                // witness is built via `Classical.choice`/`Or.rec` and therefore
                // never ι-reduces, even for a literal condition — the clean `ite`
                // reducer only fires on a saturated `Decidable.isTrue`/`isFalse`
                // constructor). This is strictly cleaner and more reducible: a
                // literal-condition `if` collapses to its branch with NO classical
                // machinery in the closure, and Classical is kept only for
                // genuinely-abstract `Prop` conditions (the def-const path).
                // FAITHFUL: `embed_term` maps both a `…_def` body's `if True then x
                // …` and any use-site's same spelling through this one branch, so
                // the two sides stay definitionally identical (the kernel-checked
                // `Eq.refl` still holds); and the result is exactly the branch HOL
                // itself proves equal. The kernel re-checks the embedded branch, so
                // a mis-typed branch is rejected — never miscounted. Gated on
                // `instance_unfold` (the escalating final pass) to stay strictly
                // additive with the existing `HOL.If` def-const arm; bare /
                // earlier-pass occurrences are unchanged.
                if self.instance_unfold {
                    if let Some(branch) = if_literal_branch(f.as_ref(), rhs.as_ref()) {
                        return self.embed_term(branch, binders);
                    }
                }
                if let IsaTerm::App { f: impf, a: lhs } = f.as_ref() {
                    if is_const(impf, "Pure.imp") || is_const(impf, "HOL.implies") {
                        let dom = self.embed_term(lhs, binders)?;
                        binders.push(Binder {
                            kind: BKind::Proof,
                            ty: dom.clone(),
                        });
                        let cod = self.embed_term(rhs, binders);
                        binders.pop();
                        return Ok(Expr::pi(BinderInfo::Default, dom, cod?));
                    }
                    // Pure meta-conjunction `A &&& B` (`Pure.conjunction A B`,
                    // both `prop`) → clean `And A B`. This is the body shape of a
                    // structured `c_class_def` axiom (`super(α) &&& Trueprop(class
                    // axioms)`). `And.left`/`And.right` (the clean eliminators)
                    // mirror Pure's `conjunctionD1`/`conjunctionD2`, so the
                    // class's `.super`/`.axioms` projections translate directly.
                    if is_const(impf, "Pure.conjunction") {
                        let ae = self.embed_term(lhs, binders)?;
                        let be = self.embed_term(rhs, binders)?;
                        return Ok(Expr::apps(Expr::const_str("And"), [ae, be]));
                    }
                }
                self.embed_app(f, rhs, binders)
            }
            IsaTerm::Free { n, t } => {
                let ty = self.embed_type(t)?;
                // A `Free` may be a box-internal spelling of the statement's
                // varified `?n.0` — see [`Ctx::term_param_free`] (aliasing
                // active only while the recorded proof value is translated).
                Ok(self.term_param_free(n, ty))
            }
            IsaTerm::Var { n, i, t } => {
                let ty = self.embed_type(t)?;
                Ok(self.term_param(&format!("{n}.{i}"), ty))
            }
            IsaTerm::Bound { i } => {
                // Pure term `Bound` counts only term binders; map to the clean
                // bvar that counts all binders.
                match term_bvar(binders, *i as usize) {
                    Some((k, _)) => Ok(Expr::bvar(k)),
                    None => Err(TranslateError::Unsupported("loose Bound in term")),
                }
            }
            IsaTerm::Abs { t, b, .. } => {
                let dom = self.embed_type(t)?;
                binders.push(Binder {
                    kind: BKind::Term,
                    ty: dom.clone(),
                });
                let body = self.embed_term(b, binders);
                binders.pop();
                Ok(Expr::lam(BinderInfo::Default, dom, body?))
            }
            // All `Const`-headed terms dispatch through the dedicated
            // const embedder (split out for file size; arm order preserved).
            IsaTerm::Const { .. } => self.embed_const_term(tm),
        }
    }
}
