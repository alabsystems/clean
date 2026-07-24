// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Term/type/proof shape predicates and accessors for the Isabelle Pure
//! definitional-axiom translator (`is_const`, `strip_prop_wrappers`,
//! `split_pure_imp`, `def_axiom_body`, `pure_eq_parts`, …). Moved verbatim from
//! the original single-file `def_axioms` module; behaviour is byte-identical.

use super::super::super::isabelle_pure::{IsaProof, IsaProvenTheorem, IsaTerm, IsaType};
use super::super::*;
pub(crate) fn is_const(tm: &IsaTerm, name: &str) -> bool {
    matches!(tm, IsaTerm::Const { n, .. } if n == name)
}

/// For a fully-applied HOL if-then-else whose *outermost* application is
/// `App { f, a: else_branch }` (so `f` is the partial spine `HOL.If cond then`),
/// return the branch the `if` denotes **when the condition is the literal
/// `HOL.True` or `HOL.False`** — `if True then x else y = x`, `if False … = y`
/// (HOL's `if_True`/`if_False`). Returns `None` for any other condition (an
/// abstract `Prop`, a `Bound`, an equality test, …), in which case the caller
/// routes the `if` through the polymorphic `isabelle.def.HOL.If` def-const.
///
/// The spine HOL exports is `(((HOL.If $ cond) $ then) $ else)`, i.e.
/// `App { f: App { f: App { HOL.If, cond }, then }, else }`. The element type need
/// not be inspected — the branch IS the denotation, already at the right type.
pub(crate) fn if_literal_branch<'a>(
    f: &'a IsaTerm,
    else_branch: &'a IsaTerm,
) -> Option<&'a IsaTerm> {
    // f = ((HOL.If $ cond) $ then)
    let IsaTerm::App {
        f: f2,
        a: then_branch,
    } = f
    else {
        return None;
    };
    // f2 = (HOL.If $ cond)
    let IsaTerm::App { f: head, a: cond } = f2.as_ref() else {
        return None;
    };
    if !is_const(head.as_ref(), "HOL.If") {
        return None;
    }
    if is_const(cond.as_ref(), "HOL.True") {
        Some(then_branch.as_ref())
    } else if is_const(cond.as_ref(), "HOL.False") {
        Some(else_branch)
    } else {
        None
    }
}

/// Whether `tm` is the partial application `Set.member x` (the first operand of
/// the curried `Set.member x S` membership). Used by [`Ctx::embed_term`] to embed
/// `x ∈ S` as the application `S x` under the `'a set = 'a → Prop` model.
pub(crate) fn is_member_app(tm: &IsaTerm) -> bool {
    matches!(tm, IsaTerm::App { f, .. } if is_const(f, "Set.member"))
}

/// Peel the `Pure.prop` / `Trueprop` identity wrappers from a statement term.
pub(crate) fn strip_prop_wrappers(tm: &IsaTerm) -> &IsaTerm {
    let mut cur = tm;
    while let IsaTerm::App { f, a } = cur {
        if is_const(f, "Pure.prop") || is_const(f, "HOL.Trueprop") || is_const(f, "Trueprop") {
            cur = a;
        } else {
            break;
        }
    }
    cur
}

/// If `tm` is a Pure implication `A ⟹ B` (`App(App(Const "Pure.imp", A), B)`,
/// modulo `Pure.prop`/`Trueprop` wrappers), return `(A, B)`.
pub(crate) fn split_pure_imp(tm: &IsaTerm) -> Option<(&IsaTerm, &IsaTerm)> {
    if let IsaTerm::App { f, a: rhs } = strip_prop_wrappers(tm) {
        if let IsaTerm::App { f: impf, a: lhs } = f.as_ref() {
            if is_const(impf, "Pure.imp") {
                return Some((lhs, rhs));
            }
        }
    }
    None
}

/// Peel any leading `Pure.imp` premises off a statement and return its final
/// conclusion (after `Pure.prop`/`Trueprop` stripping). HOL's `All_def`/`Ex_def`
/// carry a single leading `type_class`/sort-constraint premise, which the bridge
/// discharges by an enclosing `True`-binder lambda; the recognizers below match
/// against this conclusion.
pub(crate) fn strip_leading_imps(tm: &IsaTerm) -> &IsaTerm {
    let mut cur = strip_prop_wrappers(tm);
    while let Some((_, rhs)) = split_pure_imp(cur) {
        cur = strip_prop_wrappers(rhs);
    }
    cur
}

/// Whether `prem` is a **sort-constraint premise** — a class-membership
/// `OFCLASS('a, c)` / `HOL.type_class TYPE('a)` (`App(Const c_class, Pure.type)`)
/// or a `Pure.sort_constraint …` head — which embeds to the vacuous `True` (see
/// [`super::super::Ctx::embed_class_membership`]). Used by
/// [`eq_under_sort_premises`] to confirm that an equation's leading premises are
/// *only* erasable sort constraints, so the equation can be discharged
/// reflexively once those `True` premises are taken as enclosing
/// `fun (_:True) =>` lambdas.
pub(crate) fn is_sort_premise(prem: &IsaTerm) -> bool {
    let head = match strip_prop_wrappers(prem) {
        IsaTerm::App { f, .. } => f.as_ref(),
        _ => return false,
    };
    matches!(head, IsaTerm::Const { n, .. }
        if n == "HOL.type_class" || n.ends_with("_class") || n == "Pure.sort_constraint")
}

/// If a statement is a chain of leading **sort-constraint premises** ending in an
/// equation — `OFCLASS('a₁,c₁) ⟹ … ⟹ OFCLASS('aₙ,cₙ) ⟹ (eq lhs rhs)` (each
/// premise a [`is_sort_premise`], the conclusion a `Pure.eq`/`HOL.eq`/`=` after
/// `Trueprop` stripping) — return `(n-premises, eq-const-type, lhs, rhs)`.
///
/// This is the leading-sort-premise generalisation of [`super::super::eq_statement_lhs`]:
/// the latter sees through `Trueprop` but NOT through a leading `Pure.imp` sort
/// constraint, so an equation gated by `OFCLASS('a, type) ⟹` (e.g. HOL's
/// `Set.Collect_mem_eq` — `Collect (λx. x ∈ A) = A` — whose recorded proof is a
/// bare unmapped `…_mem_eq` axm) never reached the `Eq.refl` fallback. Each sort
/// premise embeds to the vacuous `True`, so the residual goal is the bare equation;
/// when its `lhs` is **definitionally equal** to its `rhs` under the embedding
/// (`Collect`/`member` are identity/application, so `Collect (λx. member x A)`
/// β-η-reduces to `A`), it is provable by `Eq.refl α (embed lhs)` wrapped in `n`
/// `fun (_:True) =>` lambdas. The stored proposition keeps the REAL `lhs = rhs`
/// shape (two DISTINCT operands — faithful, not a `B = B` tautology), and the
/// kernel accepts the `Eq.refl` ONLY when `lhs ≡ rhs` definitionally, rejecting a
/// genuinely-different equation — never miscounted. Requires `n ≥ 1` (a 0-premise
/// equation is already handled by the plain [`super::super::eq_statement_lhs`] arm,
/// so this never shadows it).
pub(crate) fn eq_under_sort_premises(
    tm: &IsaTerm,
) -> Option<(usize, &IsaType, &IsaTerm, &IsaTerm)> {
    let mut cur = strip_prop_wrappers(tm);
    let mut n = 0usize;
    while let Some((prem, rhs)) = split_pure_imp(cur) {
        if !is_sort_premise(prem) {
            return None;
        }
        n += 1;
        cur = strip_prop_wrappers(rhs);
    }
    if n == 0 {
        return None;
    }
    // The conclusion (sort premises peeled) must be an equation `eq lhs rhs`.
    // `eq_statement_lhs` reads the operand type off the `eq` constant and the LHS
    // (seeing through any residual `Trueprop`); `pure_eq_parts` decomposes the same
    // (wrapper-stripping) equation to recover the RHS for the faithful stored type.
    let (eq_ty, lhs) = eq_statement_lhs(cur)?;
    let (_lhs2, rhs) = pure_eq_parts(cur)?;
    Some((n, eq_ty, lhs, rhs))
}

/// If `tm`'s conclusion is HOL's raw `All_def` equation
/// `(HOL.All P) ≡ (P = (λx:α. HOL.True))`, return the predicate `P`. The bridge
/// [`all_def_bridge_proof`] proves the embedded form of this statement; the
/// predicate `P` (a schematic `Var`/`Free`) is embedded as a term parameter and
/// its domain `α` recovered from its type. `Ex_def` is recognized analogously by
/// [`ex_def_predicate`].
pub(crate) fn all_def_predicate(tm: &IsaTerm) -> Option<&IsaTerm> {
    // conclusion: Pure.eq (HOL.All P) (HOL.eq P (λx. HOL.True))
    let (lhs, rhs) = pure_eq_parts(strip_leading_imps(tm))?;
    // lhs = HOL.All P
    let IsaTerm::App { f: allf, a: p_lhs } = lhs else {
        return None;
    };
    if !is_const(allf, "HOL.All") {
        return None;
    }
    // rhs = (HOL.eq P) (λx. HOL.True)  — confirm the eq-trick body is `HOL.True`.
    let (rl, rr) = hol_eq_parts(rhs)?;
    // P must match on both sides (cheap structural check via Debug equality).
    if format!("{p_lhs:?}") != format!("{rl:?}") {
        return None;
    }
    if let IsaTerm::Abs { b, .. } = rr {
        if is_const(b, "HOL.True") {
            return Some(p_lhs);
        }
    }
    None
}

/// If `tm`'s conclusion is HOL's raw `Ex_def` equation
/// `(HOL.Ex P) ≡ (∀Q. (∀x. P x ⟶ Q) ⟶ Q)`, return the predicate `P`. The RHS is
/// already the faithful semantic encoding `HOL.All (λQ. HOL.All(λx. P x ⟶ Q) ⟶ Q)`,
/// so under this embedding it is `Ex`'s definition; the bridge discharges the
/// sort-constraint premise and proves the equation by `Eq.refl` once both sides
/// embed identically (`HOL.Ex P` η-expands to the same `∀Q.…` form).
pub(crate) fn ex_def_predicate(tm: &IsaTerm) -> Option<&IsaTerm> {
    let (lhs, rhs) = pure_eq_parts(strip_leading_imps(tm))?;
    // LHS must be `HOL.Ex P`.
    let IsaTerm::App { f: exf, a: p_lhs } = lhs else {
        return None;
    };
    if !is_const(exf, "HOL.Ex") {
        return None;
    }
    // RHS must be the genuine `Ex_def` semantic encoding
    // `HOL.All (λQ. (HOL.All (λx. P x ⟶ Q)) ⟶ Q)`, over the SAME predicate `P`.
    // WITHOUT this check the arm fired on *any* `HOL.Ex P = R` equation — e.g. an
    // existential-congruence lemma `(∃x. P x) = (∃x. Q x)` — and "proved" it by the
    // reflexive `Eq.refl (Ex P)`, which the kernel then rejects (`Ex P ≠ Ex Q`),
    // wasting the theorem as a `kernel-reject`. Restricting the arm to the real
    // `Ex_def` shape lets such lemmas fall through to their recorded proof instead.
    if is_ex_def_encoding(rhs, p_lhs) {
        Some(p_lhs)
    } else {
        None
    }
}

/// Whether `rhs` is the faithful `Ex_def` right-hand encoding
/// `HOL.All (λQ. (HOL.All (λx. P x ⟶ Q)) ⟶ Q)` over the predicate `p` (the `P`
/// applied to the inner bound `x`). The two Pure de Bruijn levels are `Q = Bound 1`
/// (the outer `∀Q`) inside the inner `∀x` body, and `Q = Bound 0` as the outer
/// implication's consequent. `p` is matched by structural (Debug) equality — the
/// same cheap check `all_def_predicate` uses for its predicate.
fn is_ex_def_encoding(rhs: &IsaTerm, p: &IsaTerm) -> bool {
    // rhs = HOL.All (Abs Q. body)
    let IsaTerm::App { f: allf, a: outer } = rhs else {
        return false;
    };
    if !is_const(allf, "HOL.All") {
        return false;
    }
    let IsaTerm::Abs { b: outer_body, .. } = outer.as_ref() else {
        return false;
    };
    // outer_body = HOL.implies (HOL.All (Abs x. inner_body)) (Bound 0)
    let Some((ante, conseq)) = hol_implies_parts(outer_body) else {
        return false;
    };
    if !matches!(conseq, IsaTerm::Bound { i: 0 }) {
        return false;
    }
    // ante = HOL.All (Abs x. inner_body)
    let IsaTerm::App { f: allf2, a: inner } = ante else {
        return false;
    };
    if !is_const(allf2, "HOL.All") {
        return false;
    }
    let IsaTerm::Abs { b: inner_body, .. } = inner.as_ref() else {
        return false;
    };
    // inner_body = HOL.implies (P x) (Bound 1)   (Bound 1 = the outer Q)
    let Some((px, q)) = hol_implies_parts(inner_body) else {
        return false;
    };
    if !matches!(q, IsaTerm::Bound { i: 1 }) {
        return false;
    }
    // `P x`: the predicate applied to the inner bound var. Confirm the applied head
    // is the SAME predicate `p` the LHS `HOL.Ex P` carries.
    let IsaTerm::App { f: p_applied, .. } = px else {
        return false;
    };
    format!("{:?}", p_applied.as_ref()) == format!("{p:?}")
}

/// Decompose a HOL implication `HOL.implies a b` into `(a, b)`.
fn hol_implies_parts(tm: &IsaTerm) -> Option<(&IsaTerm, &IsaTerm)> {
    if let IsaTerm::App { f, a: rhs } = tm {
        if let IsaTerm::App { f: impf, a: lhs } = f.as_ref() {
            if is_const(impf, "HOL.implies") {
                return Some((lhs, rhs));
            }
        }
    }
    None
}

/// If `thm` is a **definitional axiom** — a Pure `…_def` axiom asserting a
/// constant equals its definition — return the `Pure.eq` operand type and the
/// RHS body term `B`.
///
/// Isabelle records every defined constant `c` (type classes, locales, the
/// `class.κ`/`κ_class` predicates, function abbreviations, …) with a
/// *definitional* Pure axiom `…c_def`. Its statement, after stripping leading
/// `OFCLASS`/sort-constraint premises (`HOL.type_class TYPE('a) ⟹ …`,
/// embedded to vacuous `True`), is a `Pure.eq` whose LHS applies the defined
/// constant `c` to its parameters/operations and whose RHS spells the body `B`:
///
/// - `…κ_class_def`: `κ_class TYPE('a) ≡ B` (trivial `type_class` body for a base
///   class, or `Pure.conjunction (super TYPE('a)) (Trueprop (class.κ ops))` for a
///   structured class);
/// - `…class.κ_def` / `…κ_axioms_def`: `class.κ ops ≡ (∀…. <axiom>)`;
/// - other `…c_def`: `c args ≡ B`.
///
/// The recorded proof is a bare `PAxm` (possibly applied to the operations via
/// `%`, and/or under leading sort premises), carrying no logical content beyond
/// the equation. Under the HOL-in-CIC embedding the LHS `c args` denotes
/// *exactly* its body `B` (that is what the axiom asserts), so the faithful
/// embedded statement is the reflexive equation `@Eq α (embed B) (embed B)`,
/// proved by `Eq.refl`. [`translate_theorem`] uses this to discharge the
/// definitional axiom directly instead of hitting `bootstrap_axiom`'s unmapped
/// fallthrough.
///
/// Detection is deliberately tight: the proof's head must be a bare `Axm` whose
/// name ends with `_def`, **and** the statement (sans leading sort premises) must
/// be a `Pure.eq` whose LHS head is a `Const`. The kernel re-checks the produced
/// `@Eq α B B` against the stored type, so a mis-detection cannot be miscounted.
pub(crate) fn def_axiom_body(thm: &IsaProvenTheorem) -> Option<(&IsaType, &IsaTerm)> {
    // The proof's head (peeling any term/proof applications and leading binders)
    // must be the bare `…_def` axiom leaf.
    if !proof_head_is_def_axiom(&thm.proof) {
        return None;
    }
    // Statement (after the leading `OFCLASS ⟹ …` premises): `Pure.eq (c args) B`.
    let (lhs, rhs) = pure_eq_parts(strip_leading_imps(&thm.prop))?;
    // The `Pure.eq` constant's operand type carries `α` (`α ⇒ α ⇒ prop`).
    let eq_ty = pure_eq_operand_ty(strip_leading_imps(&thm.prop))?;
    // LHS head must be a defined constant `c` (applied to zero or more args).
    head_const(lhs)?;
    Some((eq_ty, rhs))
}

/// A **set-instance definitional axiom** — a `…_set_def`/`…_set_inst.…_def`
/// equation `op_set ≡ Collect(<the same class op on the `'a ⇒ bool` instance>)`
/// (`bot_set_def`, `inf_set_def`, `less_eq_set_def`, `Inf_set_def`, …). Unlike
/// [`def_axiom_body`] this is keyed by STATEMENT SHAPE (not the recorded-proof
/// head), because these nodes' recorded proofs are intricate `…_set_inst.…_def_raw`
/// unfolding chains that reference export-absent / unmapped raw axioms. Under the
/// faithful `'a set = 'a → Prop` model (see `embed_type`) the LHS `op_set` and the
/// RHS `Collect(op_fun …)` embed to the *same* clean term (`Set.set['a]` and
/// `'a ⇒ bool` unify; `Collect`/`member` are identity/application), so the
/// equation is genuinely reflexive — provable by `Eq.refl(lhs)`, which the kernel
/// accepts **iff** the two sides are definitionally equal. A non-set or
/// non-reflexive `_def` is rejected by the kernel, so this can never miscount.
///
/// Returns `(operand-type, lhs-term, rhs-term)`. Detection requires: the
/// statement (sans leading `OFCLASS ⟹` sort premises) is a `Pure.eq`/`HOL.eq`
/// whose operand type is `Set.set['a]` (a set-valued equation) OR whose
/// LHS/RHS mention `Set.member`/`Set.Collect` (a `bool`-valued set relation such
/// as `less_eq_set`/`less_set`), and whose LHS head is a `Const`.
pub(crate) fn set_instance_def_body(
    thm: &IsaProvenTheorem,
) -> Option<(&IsaType, &IsaTerm, &IsaTerm)> {
    // GUARD: only a genuine *definitional* axiom (the recorded proof bottoms out
    // at a `…_def` / `…_def_raw` `PAxm` leaf). This excludes ordinary set theorems
    // (e.g. `A ∪ B = B ∪ A`) whose proofs are real derivations — so the reflexive
    // shortcut never *steals* a node the recorded-proof path could verify; it only
    // intercepts the definitional nodes (whose `…_set_inst.…_def_raw` leaves are
    // otherwise unmapped). The detector below additionally requires the equation to
    // be set-shaped, so non-set defs still flow to [`def_axiom_body`].
    if !proof_contains_def_axiom(&thm.proof) {
        return None;
    }
    let concl = strip_leading_imps(&thm.prop);
    let (lhs, rhs) = pure_eq_parts(concl)?;
    let eq_ty = pure_eq_operand_ty(concl)?;
    head_const(lhs)?;
    // Either the equation is over a `Set.set[..]` value, or it relates set
    // expressions (LHS/RHS reference `Set.member`/`Set.Collect`). Both shapes are
    // exactly the set-lattice instance definitions.
    let set_valued = matches!(eq_ty, IsaType::Type { n, a } if n == "Set.set" && a.len() == 1);
    if set_valued || mentions_set_op(lhs) || mentions_set_op(rhs) {
        Some((eq_ty, lhs, rhs))
    } else {
        None
    }
}

/// Whether a term syntactically mentions the set membership / comprehension
/// coercions `Set.member` or `Set.Collect` (the markers of a set expression under
/// the predicate model).
pub(crate) fn mentions_set_op(tm: &IsaTerm) -> bool {
    match tm {
        IsaTerm::Const { n, .. } => n == "Set.member" || n == "Set.Collect",
        IsaTerm::App { f, a } => mentions_set_op(f) || mentions_set_op(a),
        IsaTerm::Abs { b, .. } => mentions_set_op(b),
        _ => false,
    }
}

/// Whether a proof's head leaf (after peeling term/proof applications and leading
/// abstractions) is a bare `…_def` axiom — the recorded proof of a definitional
/// axiom.
pub(crate) fn proof_head_is_def_axiom(p: &IsaProof) -> bool {
    match p {
        IsaProof::Axm { name, .. } => name.ends_with("_def"),
        IsaProof::AppP { f, .. }
        | IsaProof::AppT { f, .. }
        | IsaProof::AbsP { b: f, .. }
        | IsaProof::Abst { b: f, .. } => proof_head_is_def_axiom(f),
        _ => false,
    }
}

/// Whether a proof's head leaf (after peeling term/proof applications and leading
/// abstractions) is a bare `…_dict` axiom — the recorded proof of an overloaded
/// method's dictionary axiom `c_class.method ≡ c.method op₁ … opₙ`.
pub(crate) fn proof_head_is_dict_axiom(p: &IsaProof) -> bool {
    match p {
        IsaProof::Axm { name, .. } => name.ends_with("_dict"),
        IsaProof::AppP { f, .. }
        | IsaProof::AppT { f, .. }
        | IsaProof::AbsP { b: f, .. }
        | IsaProof::Abst { b: f, .. } => proof_head_is_dict_axiom(f),
        _ => false,
    }
}

/// If `thm` is a **method dictionary axiom** — a standalone `…_dict` axiom whose
/// statement is `c_class.method ≡ c.method op₁ … opₙ` (an overloaded class method
/// equated with its dictionary form) — return the `Pure.eq` operand type and the
/// RHS dictionary term `c.method ops`.
///
/// Isabelle exports the dictionary axiom of some overloaded methods
/// (`Orderings.ord_class.max`/`min`/`Least`, …) as a *named top-level theorem*
/// whose recorded proof is the bare `…_dict` `PAxm` and whose `prop`, after
/// stripping any leading `OFCLASS`/sort premises, is a `Pure.eq` applying the
/// method (a bare `Const`) on the left and its dictionary form `c.method ops` on
/// the right. When the method is registered ([`register_method_defs`] recovers it
/// from this very statement via [`super::super::dict_equation_from_prop`]), the
/// LHS `c_class.method` embeds to its dictionary def-const, which δ-unfolds to
/// exactly the RHS `c.method ops` embedding — so the equation is GENUINELY
/// reflexive (LHS δ-reduces to RHS) and provable by `Eq.refl α (embed lhs)`.
/// [`translate_theorem`] uses this to discharge the `…_dict` axiom directly
/// instead of hitting `bootstrap_axiom`'s unmapped fallthrough.
///
/// Detection mirrors [`def_axiom_body`] but keys on the `…_dict` proof-head suffix
/// (rather than `…_def`) and additionally requires the LHS head to be an
/// **overloaded method** const — so it never fires on a non-dictionary node. The
/// kernel re-checks the produced `Eq.refl α lhs : @Eq α lhs rhs`, accepting only
/// when `embed lhs` δ-reduces to `embed rhs` (i.e. the method is registered), so a
/// mis-detection or an unregistered method is kernel-rejected — never miscounted.
pub(crate) fn dict_axiom_body(thm: &IsaProvenTheorem) -> Option<(&IsaType, &IsaTerm)> {
    if !proof_head_is_dict_axiom(&thm.proof) {
        return None;
    }
    let (lhs, rhs) = pure_eq_parts(strip_leading_imps(&thm.prop))?;
    let eq_ty = pure_eq_operand_ty(strip_leading_imps(&thm.prop))?;
    // LHS must be a bare overloaded method const `c_class.method`.
    match lhs {
        IsaTerm::Const { n, .. } if is_overloaded_method_const(n) => {}
        _ => return None,
    }
    Some((eq_ty, rhs))
}

/// Whether a proof tree *contains* a definitional axiom leaf — a `…_def` **or**
/// `…_def_raw` `PAxm` anywhere in the tree. The `…_set_inst.…_def_raw`
/// instance-definition proofs are intricate `equal_elim`/`combination` unfolding
/// chains (so the `_def_raw` leaf is NOT the peeled head), but the leaf is always
/// present somewhere — its appearance marks the node as a genuine definitional
/// axiom that [`set_instance_def_body`] may discharge reflexively. This excludes
/// ordinary set theorems (whose proofs reference no `_def`/`_def_raw` leaf), so the
/// reflexive shortcut never steals a node the recorded-proof path could verify.
pub(crate) fn proof_contains_def_axiom(p: &IsaProof) -> bool {
    match p {
        IsaProof::Axm { name, .. } => name.ends_with("_def") || name.ends_with("_def_raw"),
        IsaProof::AppP { f, a } => proof_contains_def_axiom(f) || proof_contains_def_axiom(a),
        IsaProof::AppT { f, .. } | IsaProof::AbsP { b: f, .. } | IsaProof::Abst { b: f, .. } => {
            proof_contains_def_axiom(f)
        }
        _ => false,
    }
}

/// The head `Const` name of a (possibly applied) term, peeling the application
/// spine; `None` if the head is not a constant.
pub(crate) fn head_const(tm: &IsaTerm) -> Option<&str> {
    match tm {
        IsaTerm::Const { n, .. } => Some(n),
        IsaTerm::App { f, .. } => head_const(f),
        _ => None,
    }
}

/// The operand type `α` of a `Pure.eq`/`HOL.eq` application (`α ⇒ α ⇒ _`),
/// stripping `Pure.prop`/`Trueprop` wrappers — the type the reflexive `@Eq` and
/// its `Eq.refl` proof take.
pub(crate) fn pure_eq_operand_ty(tm: &IsaTerm) -> Option<&IsaType> {
    if let IsaTerm::App { f, .. } = strip_prop_wrappers(tm) {
        if let IsaTerm::App { f: eqf, .. } = f.as_ref() {
            if let IsaTerm::Const { n, t } = eqf.as_ref() {
                if n == "Pure.eq" || n == "HOL.eq" || n == "=" {
                    return eq_operand_type(t);
                }
            }
        }
    }
    None
}

/// Decompose a `Pure.eq lhs rhs` (`≡`) application, stripping `Pure.prop`/
/// `Trueprop` wrappers, into `(lhs, rhs)`.
pub(crate) fn pure_eq_parts(tm: &IsaTerm) -> Option<(&IsaTerm, &IsaTerm)> {
    if let IsaTerm::App { f, a: rhs } = strip_prop_wrappers(tm) {
        if let IsaTerm::App { f: eqf, a: lhs } = f.as_ref() {
            if is_const(eqf, "Pure.eq") || is_const(eqf, "HOL.eq") || is_const(eqf, "=") {
                return Some((lhs, rhs));
            }
        }
    }
    None
}

/// Decompose a HOL `=` (`HOL.eq lhs rhs`) application into `(lhs, rhs)` (no
/// wrapper stripping — used for the inner eq-trick of `All_def`).
pub(crate) fn hol_eq_parts(tm: &IsaTerm) -> Option<(&IsaTerm, &IsaTerm)> {
    if let IsaTerm::App { f, a: rhs } = tm {
        if let IsaTerm::App { f: eqf, a: lhs } = f.as_ref() {
            if is_const(eqf, "HOL.eq") || is_const(eqf, "=") || is_const(eqf, "Pure.eq") {
                return Some((lhs, rhs));
            }
        }
    }
    None
}

/// Collect the ordered **leading binders** of a statement
/// `⋀x:T. A₁ ⟹ A₂ ⟹ … ⟹ C` (peeling `Pure.prop`/`Trueprop` wrappers between
/// them), in outermost-first order. Each leading `Pure.imp` premise yields a
/// [`LeadingBinder::Hyp`] (recovering a raw `AbsP { h: None }`'s hypothesis) and
/// each leading `Pure.all`/`⋀` universal binder yields a
/// [`LeadingBinder::AllTy`] (recovering a raw `Abst { ty: None }`'s bound-var
/// type). The proof's outermost binders mirror this chain in the same order, so
/// the i-th enclosing proof binder consumes the i-th queue entry. Stops at the
/// first non-binder node (the conclusion).
pub(crate) fn leading_premises(prop: &IsaTerm) -> std::collections::VecDeque<LeadingBinder> {
    let mut out = std::collections::VecDeque::new();
    let mut cur = strip_prop_wrappers(prop);
    loop {
        cur = strip_prop_wrappers(cur);
        if let Some((lhs, rhs)) = split_pure_imp(cur) {
            out.push_back(LeadingBinder::Hyp(lhs.clone()));
            cur = rhs;
            continue;
        }
        if let Some((ty, body)) = split_pure_all(cur) {
            out.push_back(LeadingBinder::AllTy(ty.clone()));
            cur = body;
            continue;
        }
        break;
    }
    out
}

/// If `tm` is a Pure universal `⋀x:T. P` (`App(Const "Pure.all", Abs(_, T, P))`,
/// modulo `Pure.prop`/`Trueprop` wrappers), return `(T, P)` — the bound-variable
/// type and the body. Used to recover the bound type of a raw `Abst { ty: None }`
/// from the statement's leading `Pure.all` chain.
pub(crate) fn split_pure_all(tm: &IsaTerm) -> Option<(&IsaType, &IsaTerm)> {
    if let IsaTerm::App { f, a } = strip_prop_wrappers(tm) {
        if is_const(f, "Pure.all") || is_const(f, "Pure.all_def") {
            if let IsaTerm::Abs { t, b, .. } = a.as_ref() {
                return Some((t, b));
            }
        }
    }
    None
}
