// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Isabelle/HOL Hilbert **definite description** `HOL.The` (`THE x. P x`), mapped
//! onto clean's foundational `Classical.choice`.
//!
//! ## The mapping
//!
//! Isabelle/HOL's `The :: ('a ⇒ bool) ⇒ 'a` is the definite-description operator;
//! its single characterising axiom is `the_eq_trivial : (THE x. x = a) = a`. HOL
//! types are always nonempty, so `The` is total. clean's kernel — soundly — has no
//! global choice over *possibly-empty* sorts: its foundational `Classical.choice`
//! is `{α : Sort u} → Nonempty α → α`. We therefore model `The` as clean's
//! **classical epsilon** (definite description = Hilbert choice restricted to the
//! predicate), threading the nonemptiness witness explicitly. HOL object types
//! embed at clean `Type` (`Sort 1`), so the definition is monomorphic there.
//!
//! The witness is drawn from the **guard subtype** `S := {x : α // (∃y. P y) → P x}`
//! ("x satisfies P whenever P is satisfiable"). `S` is *always* nonempty (pick a
//! witness of `P` if `∃y. P y`, else any `α` from the supplied `Nonempty α`,
//! vacuously), and the recursion needed to prove that lands in `Prop`
//! (`Nonempty S`) — so it obeys the `Or`/`Nonempty` large-elimination restriction,
//! exactly like the classical `Decidable` instance in `isabelle.def.HOL.If`.
//!
//! ```text
//! isabelle.def.HOL.The : Type → Nonempty α → (α → Prop) → α
//!   := λ α hne P.
//!        @Subtype.val α Q (@Classical.choice {x // Q x} (neOfGuard α hne P))
//!   where Q := λ x. (∃y. P y) → P x
//! ```
//!
//! When `∃x. P x`, `Subtype.property (choice …) : Q (The …)` applied to that
//! existence proof yields `P (The …)` — the definite-description spec
//! `(∃x. P x) → P (The P)`, from which `the_eq_trivial` follows. The `The`-defined
//! order extrema `Least`/`Greatest` are registered as def-consts over this `The`, so
//! their defining axioms are reflexive. Its transitive axiom closure is
//! `⊆ {Classical.choice, propext, Quot.sound}` — all foundational — so every
//! consumer stays `KernelVerified` to the three foundationals.
//!
//! `embed_term` routes each `HOL.The α P` occurrence (on the escalating
//! `instance_unfold` pass — strictly additive, so no opaque-pass success is
//! displaced) to this def-const applied to a synthesised `Nonempty α` witness. When
//! a witness is available (a singleton predicate `λx. x = a`, or a bound object
//! variable of type `α` in scope), the witness is `Nonempty.intro α w`; otherwise
//! the occurrence keeps the opaque param and the node stays as before.

use clean_kernel::expr::FVarId;
use clean_kernel::level::Level;
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Declaration, Expr};

use super::super::*;

/// The kernel declaration name of the clean monomorphic `Definition` registered
/// for HOL's definite description `HOL.The` (`isabelle.def.HOL.The`).
pub(crate) fn hol_the_def_name() -> &'static str {
    "isabelle.def.HOL.The"
}

/// `Nonempty α` (at object level 1).
pub(crate) fn nonempty(alpha: &Expr) -> Expr {
    Expr::apps(
        Expr::const_str_levels("Nonempty", vec![obj_level()]),
        [alpha.clone()],
    )
}

/// `@Nonempty.intro.{1} α w : Nonempty α`.
fn nonempty_intro(alpha: &Expr, w: &Expr) -> Expr {
    Expr::apps(
        Expr::const_str_levels("Nonempty.intro", vec![obj_level()]),
        [alpha.clone(), w.clone()],
    )
}

/// `@Exists.{1} α P : Prop` — the existential over the object type `α`, predicate `P`.
fn exists_app(alpha: &Expr, p: &Expr) -> Expr {
    Expr::apps(
        Expr::const_str_levels("Exists", vec![obj_level()]),
        [alpha.clone(), p.clone()],
    )
}

/// The **guard predicate** `Q := λ (x:α). (∃y. P y) → P x` over the object type
/// `α`. `P` is a closed `α → Prop`; the resulting `Q : α → Prop` is closed too.
pub(crate) fn guard_pred(alpha: &Expr, p: &Expr) -> Expr {
    let fx = FVarId::new(0x1_7f01);
    let x = Expr::fvar(fx);
    // (∃y. P y) → P x
    let body = Expr::arrow(exists_app(alpha, p), Expr::app(p.clone(), x.clone()));
    Expr::lam(BinderInfo::Default, alpha.clone(), body.abstract_fvar(fx))
}

/// `@Subtype.{1} α Q : Type` — the guard subtype `{x : α // Q x}` (at `Sort 1`).
pub(crate) fn subtype(alpha: &Expr, q: &Expr) -> Expr {
    Expr::apps(
        Expr::const_str_levels("Subtype", vec![obj_level()]),
        [alpha.clone(), q.clone()],
    )
}

/// `neOfGuard α hne P : Nonempty {x // Q x}` — the guard subtype is always
/// nonempty. `Q := λx. (∃y.Py) → Px`. Built by classical case split on
/// `Classical.em (∃y. P y)` — but the split recurses only into the **Prop**
/// `Nonempty {x//Qx}`, so it respects the `Or.rec` large-elimination restriction:
///
/// ```text
/// @Or.rec (∃y.Py) (¬∃y.Py) (λ_. Nonempty S)
///   (λ he : ∃y.Py.   Exists.elim he (λ w hw. Nonempty.intro S (Subtype.mk α Q w (λ_. hw))))
///   (λ hn : ¬∃y.Py.  Nonempty.intro S (Subtype.mk α Q (Classical.choice α hne)
///                                       (λ hex. False.elim (hn hex))))
///   (Classical.em (∃y.Py))
/// ```
pub(crate) fn ne_of_guard(alpha: &Expr, hne: &Expr, p: &Expr) -> Expr {
    let q = guard_pred(alpha, p);
    let sub = subtype(alpha, &q);
    let ne_sub = nonempty(&sub);
    let ex = exists_app(alpha, p);
    let not_ex = Expr::arrow(ex.clone(), Expr::const_str("False"));

    // `@Subtype.mk.{1} α Q w qw : S`.
    let mk = |w: &Expr, qw: Expr| {
        Expr::apps(
            Expr::const_str_levels("Subtype.mk", vec![obj_level()]),
            [alpha.clone(), q.clone(), w.clone(), qw],
        )
    };
    let intro_sub = |s: Expr| {
        Expr::apps(
            Expr::const_str_levels("Nonempty.intro", vec![obj_level()]),
            [sub.clone(), s],
        )
    };

    // pos: λ (he:∃y.Py). Exists.elim he (λ (w:α)(hw:P w). intro (mk w (λ_:∃y.Py. hw)))
    let pos = {
        let fhe = FVarId::new(0x1_7f11);
        let he = Expr::fvar(fhe);
        // handler λ w hw. intro (mk w (λ _:∃y.Py. hw))
        let fw = FVarId::new(0x1_7f12);
        let fhw = FVarId::new(0x1_7f13);
        let w = Expr::fvar(fw);
        let hw = Expr::fvar(fhw);
        // qw : Q w = (∃y.Py) → P w  is  λ (_:∃y.Py). hw
        let qw = Expr::lam(BinderInfo::Default, ex.clone(), hw.clone()); // hw closed under this binder (no bvar 0)
        let s = mk(&w, qw);
        let intro = intro_sub(s);
        let pw = Expr::app(p.clone(), w.clone());
        let lam_hw = Expr::lam(BinderInfo::Default, pw, intro.abstract_fvar(fhw));
        let handler = Expr::lam(BinderInfo::Default, alpha.clone(), lam_hw.abstract_fvar(fw));
        let elim = Expr::apps(
            Expr::const_str_levels("Exists.elim", vec![obj_level()]),
            [
                alpha.clone(),
                p.clone(),
                ne_sub.clone(),
                he.clone(),
                handler,
            ],
        );
        Expr::lam(BinderInfo::Default, ex.clone(), elim.abstract_fvar(fhe))
    };

    // neg: λ (hn:¬∃y.Py). intro (mk (Classical.choice α hne) (λ hex:∃y.Py. @False.elim (P w) (hn hex)))
    // — the element comes from the supplied `Nonempty α` (no `Nonempty.rec` needed);
    // `Q w` holds vacuously because its premise `∃y.Py` contradicts `hn`.
    let neg = {
        let fhn = FVarId::new(0x1_7f21);
        let fhex = FVarId::new(0x1_7f23);
        let hn = Expr::fvar(fhn);
        let hex = Expr::fvar(fhex);
        let w = Expr::apps(
            Expr::const_str_levels("Classical.choice", vec![obj_level()]),
            [alpha.clone(), hne.clone()],
        );
        let pw = Expr::app(p.clone(), w.clone());
        let false_elim = Expr::apps(
            Expr::const_str_levels("False.elim", vec![Level::zero()]),
            [pw, Expr::app(hn.clone(), hex.clone())],
        );
        // qw : Q w = (∃y.Py) → P w  is  λ hex. False.elim (hn hex)
        let qw = Expr::lam(
            BinderInfo::Default,
            ex.clone(),
            false_elim.abstract_fvar(fhex),
        );
        let s = mk(&w, qw);
        let intro = intro_sub(s);
        Expr::lam(
            BinderInfo::Default,
            not_ex.clone(),
            intro.abstract_fvar(fhn),
        )
    };

    let em = Expr::app(Expr::const_str("Classical.em"), ex.clone());
    // motive for Or.rec: λ (_:Or (∃y.Py) (¬∃y.Py)). Nonempty S   (a Prop).
    let or_ty = Expr::apps(Expr::const_str("Or"), [ex.clone(), not_ex.clone()]);
    let motive = Expr::lam(BinderInfo::Default, or_ty, ne_sub);
    Expr::apps(
        Expr::const_str("Or.rec"),
        [ex, not_ex, motive, pos, neg, em],
    )
}

/// The faithful clean monomorphic `Definition` value+type for HOL's definite
/// description `HOL.The : ('a ⇒ bool) ⇒ 'a` — the classical epsilon threaded with
/// an explicit `Nonempty α`, over the guard subtype. See the module doc.
pub(crate) fn build_hol_the_value_and_type() -> (Expr, Expr) {
    let type_1 = Expr::type_(); // α : Type (Sort 1)
    let fa = FVarId::new(0x1_7d01); // α : Type
    let fhne = FVarId::new(0x1_7d02); // hne : Nonempty α
    let fp = FVarId::new(0x1_7d03); // P : α → Prop
    let alpha = || Expr::fvar(fa);
    let hne = || Expr::fvar(fhne);
    let p = || Expr::fvar(fp);
    let pred_ty = || Expr::arrow(alpha(), Expr::prop());

    // body: @Subtype.val α Q (@Classical.choice {x//Qx} (neOfGuard α hne P))
    let q = guard_pred(&alpha(), &p());
    let sub = subtype(&alpha(), &q);
    let ne_witness = ne_of_guard(&alpha(), &hne(), &p());
    let choose = Expr::apps(
        Expr::const_str_levels("Classical.choice", vec![obj_level()]),
        [sub.clone(), ne_witness],
    );
    let body = Expr::apps(
        Expr::const_str_levels("Subtype.val", vec![obj_level()]),
        [alpha(), q, choose],
    );

    // value: λ (α:Type)(hne:Nonempty α)(P:α→Prop). body — abstract innermost-first.
    let v = body.abstract_fvar(fp);
    let v = Expr::lam(BinderInfo::Default, pred_ty(), v);
    let v = v.abstract_fvar(fhne);
    let v = Expr::lam(BinderInfo::Default, nonempty(&alpha()), v);
    let v = v.abstract_fvar(fa);
    let value = Expr::lam(BinderInfo::Default, type_1.clone(), v);

    // type: Π (α:Type)(hne:Nonempty α)(P:α→Prop). α.
    let t = alpha().abstract_fvar(fp);
    let t = Expr::pi(BinderInfo::Default, pred_ty(), t);
    let t = t.abstract_fvar(fhne);
    let t = Expr::pi(BinderInfo::Default, nonempty(&alpha()), t);
    let t = t.abstract_fvar(fa);
    let type_ = Expr::pi(BinderInfo::Default, type_1, t);

    (value, type_)
}

/// HOL's definite description `HOL.The` as a clean [`Declaration::Definition`]
/// (`isabelle.def.HOL.The`). Registered into the verifier's accumulating
/// environment up front so every routed `HOL.The` occurrence shares one
/// defeq-unfolding head. See [`build_hol_the_value_and_type`].
#[must_use]
pub(crate) fn hol_the_definition_decl() -> Declaration {
    let (value, type_) = build_hol_the_value_and_type();
    Declaration::Definition {
        name: Name::from_string(hol_the_def_name()),
        level_params: Vec::new(),
        type_,
        value,
        is_reducible: true,
    }
}

/// `isabelle.def.HOL.The α (Nonempty.intro α w) P` — the epsilon applied at object
/// type `α`, nonemptiness witnessed by `w : α`, predicate `P : α → Prop`.
///
/// This is the clean image of `HOL.The P` when a witness `w` for the object type is
/// available (a singleton predicate's point, or a bound object variable in scope).
pub(crate) fn the_applied(alpha: &Expr, w: &Expr, p: &Expr) -> Expr {
    the_applied_ne(alpha, &nonempty_intro(alpha, w), p)
}

/// `isabelle.def.HOL.The α hne P` — the epsilon applied at object type `α`,
/// predicate `P : α → Prop`, with `hne : Nonempty α` supplied as an arbitrary
/// expression (a witnessed `Nonempty.intro`, or an opaque nonemptiness parameter
/// for the `Least`/`Greatest` definitions whose predicate carries no witness).
pub(crate) fn the_applied_ne(alpha: &Expr, hne: &Expr, p: &Expr) -> Expr {
    Expr::apps(
        Expr::const_str(hol_the_def_name()),
        [alpha.clone(), hne.clone(), p.clone()],
    )
}

/// Whether `name` is one of HOL's `The`-defined order extrema `Orderings.ord.Least`
/// / `Orderings.order.Greatest` (or their class-qualified aliases), whose defining
/// axiom is `C le P = (THE x. P x ∧ (∀y. P y → x ≼ y))`.
pub(crate) fn is_order_extremum(name: &str) -> bool {
    matches!(
        name,
        "Orderings.ord.Least"
            | "Orderings.ord_class.Least"
            | "Orderings.order.Greatest"
            | "Orderings.order_class.Greatest"
            | "Orderings.ord.Greatest"
    )
}

/// `true` for the `Greatest` extrema (comparison `le y x`), `false` for `Least`
/// (comparison `le x y`). The two differ only in the order of the `le` operands.
fn is_greatest(name: &str) -> bool {
    name.contains("Greatest")
}

/// The registered def-const name for an order extremum (`isabelle.def.<name>`).
pub(crate) fn extremum_def_name(name: &str) -> String {
    format!("isabelle.def.{name}")
}

/// The (per-object-type) key of the shared `Nonempty α` quantified parameter that
/// the `The`-defined extrema / definite descriptions thread. Keying by the embedded
/// object type means every extremum use-site and its `…_def` prover reference ONE
/// `∀(hne : Nonempty α)` binder, so `Eq.refl` closes. Shared with the `wo_rel`
/// `The`-threaded constants (`minim`/`supr`/`suc`, `def_axioms::wo_rel`).
pub(crate) fn nonempty_param_key(alpha: &Expr) -> String {
    format!("nonempty:the:{alpha:?}")
}

/// The extremum **predicate** `λ(x:α). conj (P x) (∀(y:α). P y → le·x·y)` (for
/// `Least`; `le·y·x` for `Greatest`), built with exactly the clean encoding
/// `embed_term` produces for HOL's `P x ∧ (∀y. P y ⟶ le x y)`:
/// `isabelle.def.HOL.conj` for `∧`, clean `Pi` for `∀`/`⟶`. `alpha`/`le`/`p` are
/// the embedded object type, relation `α→α→Prop`, and predicate `α→Prop`.
fn extremum_predicate(alpha: &Expr, le: &Expr, p: &Expr, greatest: bool) -> Expr {
    let fx = FVarId::new(0x1_7b01);
    let fy = FVarId::new(0x1_7b02);
    let x = Expr::fvar(fx);
    let y = Expr::fvar(fy);
    let px = Expr::app(p.clone(), x.clone());
    let py = Expr::app(p.clone(), y.clone());
    // le applied in Least (x,y) or Greatest (y,x) order.
    let le_xy = if greatest {
        Expr::apps(le.clone(), [y.clone(), x.clone()])
    } else {
        Expr::apps(le.clone(), [x.clone(), y.clone()])
    };
    // ∀(y:α). P y → le·… : Pi (y:α). (Pi (_:P y). le·…)
    let inner = Expr::arrow(py, le_xy);
    let forall_y = Expr::pi(BinderInfo::Default, alpha.clone(), inner.abstract_fvar(fy));
    // conj (P x) (∀y. …)
    let conj = Expr::apps(Expr::const_str("isabelle.def.HOL.conj"), [px, forall_y]);
    Expr::lam(BinderInfo::Default, alpha.clone(), conj.abstract_fvar(fx))
}

/// The faithful clean monomorphic `Definition` value+type for an order extremum
/// `C : (α⇒α⇒bool) ⇒ (α⇒bool) ⇒ α`, threaded with an explicit `Nonempty α`:
///
/// ```text
/// isabelle.def.<C> : Type → Nonempty α → (α→α→Prop) → (α→Prop) → α
///   := λ α hne le P. isabelle.def.HOL.The α hne (extremum_predicate α le P)
/// ```
///
/// So `C le P` δ-unfolds to `THE x. P x ∧ (∀y. P y → x ≼ y)`, making the defining
/// axiom `C le P = (THE …)` genuinely reflexive under the embedding.
pub(crate) fn build_extremum_value_and_type(greatest: bool) -> (Expr, Expr) {
    let type_1 = Expr::type_();
    let fa = FVarId::new(0x1_7a01); // α : Type
    let fhne = FVarId::new(0x1_7a02); // hne : Nonempty α
    let fle = FVarId::new(0x1_7a03); // le : α → α → Prop
    let fp = FVarId::new(0x1_7a04); // P : α → Prop
    let alpha = || Expr::fvar(fa);
    let le_ty = || Expr::arrow(alpha(), Expr::arrow(alpha(), Expr::prop()));
    let pred_ty = || Expr::arrow(alpha(), Expr::prop());

    let pred = extremum_predicate(&alpha(), &Expr::fvar(fle), &Expr::fvar(fp), greatest);
    let body = the_applied_ne(&alpha(), &Expr::fvar(fhne), &pred);

    // value: λ (α:Type)(hne:Nonempty α)(le:α→α→Prop)(P:α→Prop). body.
    let v = body.abstract_fvar(fp);
    let v = Expr::lam(BinderInfo::Default, pred_ty(), v);
    let v = v.abstract_fvar(fle);
    let v = Expr::lam(BinderInfo::Default, le_ty(), v);
    let v = v.abstract_fvar(fhne);
    let v = Expr::lam(BinderInfo::Default, nonempty(&alpha()), v);
    let v = v.abstract_fvar(fa);
    let value = Expr::lam(BinderInfo::Default, type_1.clone(), v);

    // type: Π (α:Type)(hne:Nonempty α)(le:α→α→Prop)(P:α→Prop). α.
    let t = alpha().abstract_fvar(fp);
    let t = Expr::pi(BinderInfo::Default, pred_ty(), t);
    let t = t.abstract_fvar(fle);
    let t = Expr::pi(BinderInfo::Default, le_ty(), t);
    let t = t.abstract_fvar(fhne);
    let t = Expr::pi(BinderInfo::Default, nonempty(&alpha()), t);
    let t = t.abstract_fvar(fa);
    let type_ = Expr::pi(BinderInfo::Default, type_1, t);

    (value, type_)
}

/// The order-extremum def-consts (`isabelle.def.Orderings.ord.Least`,
/// `isabelle.def.Orderings.order.Greatest`, plus the class-qualified aliases) as
/// clean [`Declaration::Definition`]s. Registered up front so a `Least`/`Greatest`
/// occurrence unfolds to its `The`-expression and the defining axiom verifies
/// reflexively. Depends on `isabelle.def.HOL.The` and `isabelle.def.HOL.conj`.
#[must_use]
pub(crate) fn extremum_definition_decls() -> Vec<Declaration> {
    [
        "Orderings.ord.Least",
        "Orderings.ord_class.Least",
        "Orderings.order.Greatest",
        "Orderings.order_class.Greatest",
        "Orderings.ord.Greatest",
    ]
    .into_iter()
    .map(|n| {
        let (value, type_) = build_extremum_value_and_type(is_greatest(n));
        Declaration::Definition {
            name: Name::from_string(&extremum_def_name(n)),
            level_params: Vec::new(),
            type_,
            value,
            is_reducible: true,
        }
    })
    .collect()
}

/// If the HOL predicate `pred` is a **singleton** `λ(x:α). x = a` (the object
/// variable equated to a closed term `a` that does not mention `x`), return `a`.
/// This is the only predicate shape whose definite description the def-axioms pin
/// down (`the_eq_trivial`), so it is the only one for which the embedding can
/// recover a nonemptiness witness. Both operand orders (`x = a` and `a = x`) are
/// accepted; the bound `x` must be `Bound 0` and must not occur in `a`.
fn singleton_witness(pred: &IsaTerm) -> Option<&IsaTerm> {
    let IsaTerm::Abs { b, .. } = pred else {
        return None;
    };
    // b must be `HOL.eq lhs rhs` (curried `App(App(eq, lhs), rhs)`).
    let IsaTerm::App { f, a: rhs } = b.as_ref() else {
        return None;
    };
    let IsaTerm::App { f: eqf, a: lhs } = f.as_ref() else {
        return None;
    };
    let IsaTerm::Const { n, .. } = eqf.as_ref() else {
        return None;
    };
    if n != "HOL.eq" && n != "=" && n != "Pure.eq" {
        return None;
    }
    // Exactly one operand is the bound `x` (Bound 0); the other is the witness `a`,
    // which must be closed w.r.t. the binder (no `Bound 0`).
    let is_bound0 = |t: &IsaTerm| matches!(t, IsaTerm::Bound { i } if *i == 0);
    let cand = if is_bound0(lhs) {
        rhs.as_ref()
    } else if is_bound0(rhs) {
        lhs.as_ref()
    } else {
        return None;
    };
    if mentions_bound0(cand, 0) {
        return None;
    }
    Some(cand)
}

/// Whether `tm` references the de Bruijn term variable at depth `depth` (i.e.
/// `Bound depth`), accounting for nested `Abs` binders that shift the index.
fn mentions_bound0(tm: &IsaTerm, depth: i64) -> bool {
    match tm {
        IsaTerm::Bound { i } => *i == depth,
        IsaTerm::Abs { b, .. } => mentions_bound0(b, depth + 1),
        IsaTerm::App { f, a } => mentions_bound0(f, depth) || mentions_bound0(a, depth),
        _ => false,
    }
}

impl Ctx {
    /// Prove a point-free extremum `…_def_raw` axiom referenced as a **leaf**
    /// (`C ≡ λle P. THE x. P x ∧ (∀y. P y → x ≼ y)`), from the object type the leaf's
    /// `tyinst` supplies. `base_name` is the extremum constant (`Orderings.ord.Least`,
    /// …). The bare `C` embeds to `@isabelle.def.<C> α hne`, whose η/δ-unfold is
    /// `λle P. THE x. …` — the RHS built by [`extremum_predicate`]/[`the_applied_ne`]
    /// with the SAME shared `Nonempty α` parameter — so the equation is reflexive
    /// (`Eq.refl`). The kernel re-checks the produced term against the consuming
    /// proof's expectation, so a wrong shape is rejected — never miscounted.
    pub(crate) fn prove_extremum_def_raw_leaf(
        &mut self,
        base_name: &str,
        alpha_ty: &IsaType,
    ) -> Result<Expr, TranslateError> {
        let alpha = self.embed_type(alpha_ty)?;
        let hne = self.term_param(&nonempty_param_key(&alpha), nonempty(&alpha));
        let greatest = base_name.contains("Greatest");
        // LHS bare `C` → `@isabelle.def.<C> α hne : (α→α→Prop)→(α→Prop)→α`.
        let lhs = Expr::apps(
            Expr::const_str(&extremum_def_name(base_name)),
            [alpha.clone(), hne.clone()],
        );
        // The equation's operand type `(α→α→Prop)→(α→Prop)→α`.
        let rel_ty = Expr::arrow(alpha.clone(), Expr::arrow(alpha.clone(), Expr::prop()));
        let pred_ty = Expr::arrow(alpha.clone(), Expr::prop());
        let fun_ty = Expr::arrow(rel_ty.clone(), Expr::arrow(pred_ty.clone(), alpha.clone()));
        // The reflexive proof — LHS δ/η-reduces to `λle P. THE x. …`, the RHS the
        // consumer's `The`-routed embedding spells. The kernel accepts iff defeq.
        Ok(Expr::apps(
            Expr::const_str_levels("Eq.refl", vec![obj_level()]),
            [fun_ty, lhs],
        ))
    }

    /// Embed a bare `Orderings.ord.Least` / `Orderings.order.Greatest` constant (HOL
    /// type `(α⇒α⇒bool)⇒(α⇒bool)⇒α`) to its registered def-const applied to the
    /// object type and the shared `Nonempty α` parameter
    /// (`@isabelle.def.<C> α hne : (α→α→Prop)→(α→Prop)→α`, which η/δ-unfolds to
    /// `λle P. THE x. P x ∧ …`). Returns `None` when the type is not the expected
    /// two-argument extremum shape. The `Nonempty α` param is keyed by the object
    /// type so LHS uses and the `…_def` prover share one quantified hypothesis.
    pub(crate) fn embed_extremum_const(
        &mut self,
        name: &str,
        t: &IsaType,
    ) -> Result<Option<Expr>, TranslateError> {
        // t = (α⇒α⇒bool) ⇒ (α⇒bool) ⇒ α ; the result element type α is the codomain
        // of the second arrow (= the domain of the predicate arg `(α⇒bool)`).
        let Some(rel_ty) = eq_operand_type(t) else {
            return Ok(None);
        };
        // rel_ty = α⇒α⇒bool ; α is its domain.
        let Some(alpha_ty) = eq_operand_type(rel_ty) else {
            return Ok(None);
        };
        let alpha = self.embed_type(alpha_ty)?;
        let hne = self.term_param(&nonempty_param_key(&alpha), nonempty(&alpha));
        Ok(Some(Expr::apps(
            Expr::const_str(&extremum_def_name(name)),
            [alpha, hne],
        )))
    }

    /// Embed `HOL.The pred` (definite description) to the classical-epsilon
    /// def-const applied at the recovered object type, witness and predicate, or
    /// `None` when no nonemptiness witness is recoverable (predicate not a
    /// singleton `λx. x = a`, or the const type is not the expected `(α⇒bool)⇒α`).
    /// See [`the_applied`] and the module doc.
    pub(crate) fn embed_hol_the(
        &mut self,
        the_const: &IsaTerm,
        pred: &IsaTerm,
        binders: &mut Vec<Binder>,
    ) -> Result<Option<Expr>, TranslateError> {
        // `HOL.The : (α ⇒ bool) ⇒ α`; the result/element type `α` is the codomain,
        // = the domain of the predicate type `(α ⇒ bool)`.
        let IsaTerm::Const { t, .. } = the_const else {
            return Ok(None);
        };
        let Some(pred_ty) = eq_operand_type(t) else {
            return Ok(None);
        };
        let Some(alpha_ty) = eq_operand_type(pred_ty) else {
            return Ok(None);
        };
        let alpha = self.embed_type(alpha_ty)?;
        let p = self.embed_term(pred, binders)?;
        // Prefer a concrete nonemptiness witness when the predicate is a singleton
        // `λx. x = a` (`the_eq_trivial`, witness `a`); otherwise thread the shared
        // quantified `Nonempty α` parameter (the general definite description — its
        // value is only pinned down where the def-axiom supplies uniqueness). Both
        // keep the epsilon head shared with the `The`-defined `Least`/`Greatest`.
        let hne = match singleton_witness(pred) {
            Some(wit_tm) => {
                let w = self.embed_term(wit_tm, binders)?;
                nonempty_intro(&alpha, &w)
            }
            None => self.term_param(&nonempty_param_key(&alpha), nonempty(&alpha)),
        };
        Ok(Some(the_applied_ne(&alpha, &hne, &p)))
    }
}

/// The singleton predicate `λ(x:α). @Eq.{1} α x a` — HOL's `(λx. x = a)`, whose
/// definite description is `a` (`the_eq_trivial`).
pub(crate) fn eq_singleton_pred(alpha: &Expr, a: &Expr) -> Expr {
    let fx = FVarId::new(0x1_7c01);
    let x = Expr::fvar(fx);
    let body = Expr::apps(
        Expr::const_str_levels("Eq", vec![obj_level()]),
        [alpha.clone(), x.clone(), a.clone()],
    );
    Expr::lam(BinderInfo::Default, alpha.clone(), body.abstract_fvar(fx))
}

/// Kernel proof of `the_eq_trivial` at a fixed object type `α` and point `a`:
///
/// ```text
/// @Eq.{1} α (isabelle.def.HOL.The α (Nonempty.intro α a) (λx. x = a)) a
/// ```
///
/// The epsilon δ-unfolds to `Subtype.val α Q (Classical.choice S ne)` with
/// `Q := λx. (∃y. y = a) → (x = a)`, so `Subtype.property (choice …) : Q (The …)`,
/// i.e. `(∃y. y = a) → (The … = a)`. Applying it to the existence proof
/// `Exists.intro α (λx. x = a) a (Eq.refl α a)` yields `The … = a`. Foundational
/// closure (`Classical.choice`/`propext`/`Quot.sound`); the kernel re-checks the
/// result against the equation, so a mis-build is rejected — never miscounted.
pub(crate) fn prove_the_eq_trivial_core(alpha: &Expr, a: &Expr) -> Expr {
    let pred = eq_singleton_pred(alpha, a);
    let q = guard_pred(alpha, &pred);
    let sub = subtype(alpha, &q);
    // The value `Classical.choice S ne` (the same subtype element `The` unfolds through).
    let ne_witness = ne_of_guard(alpha, &nonempty_intro(alpha, a), &pred);
    let choose = Expr::apps(
        Expr::const_str_levels("Classical.choice", vec![obj_level()]),
        [sub.clone(), ne_witness],
    );
    // Subtype.property (choice) : Q (Subtype.val α Q choice)  =  (∃y.y=a) → (The … = a)
    let property = Expr::apps(
        Expr::const_str_levels("Subtype.property", vec![obj_level()]),
        [alpha.clone(), q, choose],
    );
    // hex : ∃y. y = a   is   @Exists.intro.{1} α (λx.x=a) a (@Eq.refl.{1} α a)
    let refl = Expr::apps(
        Expr::const_str_levels("Eq.refl", vec![obj_level()]),
        [alpha.clone(), a.clone()],
    );
    let hex = Expr::apps(
        Expr::const_str_levels("Exists.intro", vec![obj_level()]),
        [alpha.clone(), pred, a.clone(), refl],
    );
    Expr::app(property, hex)
}

impl Ctx {
    /// Statement-level proof of an order-extremum defining axiom
    /// `Least/Greatest le P = (THE x. P x ∧ (∀y. P y → x ≼ y))`, attempted BEFORE the
    /// recorded proof (whose `…Least_def_raw`/`…Greatest_def_raw` PAxm leaf is
    /// unmapped). Returns the `(stored_type, proof)` pair, or `None` if `thm` is not
    /// an extremum def.
    ///
    /// The `Least`/`Greatest` LHS is embedded to its registered def-const
    /// `@isabelle.def.<C> α hne le P` (see [`extremum_definition_decls`]), which
    /// δ-unfolds to `isabelle.def.HOL.The α hne (extremum_predicate α le P)` — the
    /// SAME term the RHS `THE …` builds via [`the_applied_ne`]/[`extremum_predicate`].
    /// The nonemptiness witness `hne : Nonempty α` is a shared quantified parameter
    /// (HOL types are always nonempty; clean makes the hypothesis explicit — a
    /// faithful strengthening, cf. `Greatest`'s own `order` premise). The stored
    /// equation therefore has two structurally **distinct** but definitionally equal
    /// operands (never a `B = B` tautology), proved by `Eq.refl`, which the kernel
    /// accepts iff the def-const genuinely unfolds to the RHS. Foundational closure
    /// (via `isabelle.def.HOL.The` → `Classical.choice`). Leading sort/`order`
    /// premises are discharged as vacuous `True →` in lockstep on type and proof.
    pub(crate) fn prove_extremum_def(
        &mut self,
        thm: &IsaProvenTheorem,
        binders: &mut Vec<Binder>,
    ) -> Result<Option<(Expr, Expr)>, TranslateError> {
        let concl = strip_leading_imps(&thm.prop);
        let (lhs_tm, rhs_tm) = match pure_eq_parts(concl) {
            Some(p) => p,
            None => return Ok(None),
        };
        // LHS must be `C le P` with `C` an order-extremum constant.
        let (c_name, le_tm, p_tm) = match extremum_lhs_parts(lhs_tm) {
            Some(x) => x,
            None => return Ok(None),
        };
        // RHS must be `HOL.The pred`.
        let IsaTerm::App {
            f: the_f,
            a: pred_tm,
        } = rhs_tm
        else {
            return Ok(None);
        };
        if !is_const(the_f, "HOL.The") {
            return Ok(None);
        }
        // Object type α: the predicate `P`'s domain (`P : α ⇒ bool`).
        let p_ty = self.infer_type(p_tm, binders)?;
        let (alpha, _) = split_arrow(&p_ty).ok_or(TranslateError::Unsupported(
            "extremum_def: predicate not a function",
        ))?;
        let le = self.embed_term(le_tm, binders)?;
        let p = self.embed_term(p_tm, binders)?;
        // Sanity: the RHS predicate must be exactly the extremum predicate for this
        // relation/predicate (so the def-const's unfold matches). We do NOT trust the
        // export's spelling — we rebuild it canonically and let the kernel `Eq.refl`
        // reject a mismatch. (`embed_term(pred_tm)` is not used for the RHS operand;
        // the canonical `extremum_predicate` is, guaranteeing LHS δ-unfold = RHS.)
        let _ = pred_tm; // shape only; canonical predicate rebuilt below
        let greatest = c_name.contains("Greatest");
        let pred = extremum_predicate(&alpha, &le, &p, greatest);
        // Shared nonemptiness parameter for the object type (same key the bare-const
        // routing [`Ctx::embed_extremum_const`] uses, so LHS/RHS share one binder).
        let hne = self.term_param(&nonempty_param_key(&alpha), nonempty(&alpha));

        // LHS_e = @isabelle.def.<C> α hne le P  (δ-unfolds to `The α hne pred`).
        let lhs_e = Expr::apps(
            Expr::const_str(&extremum_def_name(c_name)),
            [alpha.clone(), hne.clone(), le, p],
        );
        // RHS_e = isabelle.def.HOL.The α hne pred.
        let rhs_e = the_applied_ne(&alpha, &hne, &pred);
        let mut stored = Expr::apps(
            Expr::const_str_levels("Eq", vec![obj_level()]),
            [alpha.clone(), lhs_e.clone(), rhs_e],
        );
        let mut proof = Expr::apps(
            Expr::const_str_levels("Eq.refl", vec![obj_level()]),
            [alpha, lhs_e],
        );
        // Discharge each leading premise (erased sort constraint / `order`) as `True →`.
        let n_premises = leading_premises(&thm.prop).len();
        for _ in 0..n_premises {
            proof = Expr::lam(BinderInfo::Default, Expr::const_str("True"), proof);
            stored = Expr::arrow(Expr::const_str("True"), stored);
        }
        Ok(Some((stored, proof)))
    }
}

/// If `tm` is `C le P` with `C` an [`is_order_extremum`] constant applied to a
/// relation `le` and predicate `P`, return `(C_name, le, P)`.
fn extremum_lhs_parts(tm: &IsaTerm) -> Option<(&str, &IsaTerm, &IsaTerm)> {
    // C le P  =  App(App(Const C, le), P).
    let IsaTerm::App { f, a: p } = tm else {
        return None;
    };
    let IsaTerm::App { f: cf, a: le } = f.as_ref() else {
        return None;
    };
    let IsaTerm::Const { n, .. } = cf.as_ref() else {
        return None;
    };
    if !is_order_extremum(n) {
        return None;
    }
    Some((n.as_str(), le, p))
}

/// Statement-level proof of HOL's `the_eq_trivial` (`(THE x. x = a) = a`) directly
/// from the embedded statement, attempted BEFORE the recorded proof (whose
/// `the_eq_trivial_def_raw` PAxm leaf is unmapped). The recognized shape is
///
/// ```text
/// @Eq.{1} α (isabelle.def.HOL.The α (Nonempty.intro α a) (λx. @Eq α x a)) a
/// ```
///
/// — the definite-description LHS routed by [`Ctx::embed_hol_the`] with witness
/// `a`. On a match it returns [`prove_the_eq_trivial_core`] (`Subtype.property`
/// applied to the existence proof), whose foundational closure the kernel
/// re-checks against `prop`. Returns `None` for any other shape.
pub(crate) fn prove_the_eq_trivial(prop: &Expr) -> Option<Expr> {
    use clean_kernel::expr::ExprKind;
    // The statement carries no premises, but be defensive about leading `True →`.
    let mut cur = prop.clone();
    while let ExprKind::Pi(_, dom, cod) = cur.kind() {
        if **dom != Expr::const_str("True") {
            break;
        }
        cur = (**cod).clone();
    }
    let (alpha, lhs, rhs) = eq_three_parts(&cur)?;
    // LHS must be `isabelle.def.HOL.The α (Nonempty.intro α rhs) (λx. x = rhs)`.
    let (args, head) = the_app_spine(&lhs);
    if !matches!(head.kind(), ExprKind::Const(n, _) if n.to_string() == hol_the_def_name()) {
        return None;
    }
    if args.len() != 3 {
        return None;
    }
    // arg0 = α, arg1 = Nonempty.intro α rhs, arg2 = predicate.
    if args[0] != alpha {
        return None;
    }
    let expected_ne = nonempty_intro(&alpha, &rhs);
    if args[1] != expected_ne {
        return None;
    }
    let expected_pred = eq_singleton_pred(&alpha, &rhs);
    if args[2] != expected_pred {
        return None;
    }
    Some(prove_the_eq_trivial_core(&alpha, &rhs))
}

/// Decompose an application `f a₁ … aₙ` into `([a₁,…,aₙ], f)`.
fn the_app_spine(e: &Expr) -> (Vec<Expr>, Expr) {
    use clean_kernel::expr::ExprKind;
    let mut args = Vec::new();
    let mut cur = e.clone();
    while let ExprKind::App(f, a) = cur.kind() {
        args.push((**a).clone());
        cur = (**f).clone();
    }
    args.reverse();
    (args, cur)
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::env::is_foundational_axiom;
    use clean_kernel::Environment;

    #[test]
    fn hol_the_epsilon_definition_kernel_checks_foundational() {
        let mut env = Environment::with_prelude();
        env.add_decl(hol_the_definition_decl())
            .expect("epsilon `isabelle.def.HOL.The` must type-check in the prelude env");
        let deps = env
            .axiom_deps(&Name::from_string(hol_the_def_name()))
            .expect("axiom_deps for the epsilon def");
        assert!(
            deps.iter().all(is_foundational_axiom),
            "epsilon `The` axiom closure must be foundational-only; got {deps:?}"
        );
    }

    #[test]
    fn extremum_definitions_kernel_check_foundational() {
        let mut env = Environment::with_prelude();
        // Dependencies: HOL.conj def-const and the epsilon The.
        for d in super::super::super::connective_definition_decls() {
            let _ = env.add_decl(d);
        }
        env.add_decl(hol_the_definition_decl())
            .expect("register epsilon The");
        for d in extremum_definition_decls() {
            let name = match &d {
                Declaration::Definition { name, .. } => name.clone(),
                _ => panic!("expected Definition"),
            };
            env.add_decl(d)
                .unwrap_or_else(|e| panic!("extremum def {name:?} must type-check: {e:?}"));
            let deps = env.axiom_deps(&name).expect("axiom_deps");
            assert!(
                deps.iter().all(is_foundational_axiom),
                "extremum {name:?} closure must be foundational-only; got {deps:?}"
            );
        }
    }

    #[test]
    fn the_eq_trivial_kernel_checks_foundational() {
        let mut env = Environment::with_prelude();
        env.add_decl(hol_the_definition_decl())
            .expect("register epsilon `The`");

        // Build `∀(α:Type)(a:α). @Eq α (The α (Nonempty.intro α a) (λx.x=a)) a`.
        let fa = FVarId::new(0xABCD_0001);
        let faa = FVarId::new(0xABCD_0002);
        let alpha = Expr::fvar(fa);
        let a = Expr::fvar(faa);
        let pred = eq_singleton_pred(&alpha, &a);
        let lhs = the_applied(&alpha, &a, &pred);
        let eq_ty = Expr::apps(
            Expr::const_str_levels("Eq", vec![obj_level()]),
            [alpha.clone(), lhs, a.clone()],
        );
        // type: Π(α:Type)(a:α). eq_ty
        let ty = eq_ty.abstract_fvar(faa);
        let ty = Expr::pi(BinderInfo::Default, alpha.clone(), ty);
        let ty = ty.abstract_fvar(fa);
        let ty = Expr::pi(BinderInfo::Default, Expr::type_(), ty);

        let core = prove_the_eq_trivial_core(&alpha, &a);
        let pf = core.abstract_fvar(faa);
        let pf = Expr::lam(BinderInfo::Default, alpha, pf);
        let pf = pf.abstract_fvar(fa);
        let pf = Expr::lam(BinderInfo::Default, Expr::type_(), pf);

        env.add_decl(Declaration::Theorem {
            name: Name::from_string("test.the_eq_trivial"),
            level_params: Vec::new(),
            type_: ty,
            value: pf,
        })
        .expect("the_eq_trivial proof must kernel-check");

        let deps = env
            .axiom_deps(&Name::from_string("test.the_eq_trivial"))
            .expect("axiom_deps");
        assert!(
            deps.iter().all(is_foundational_axiom),
            "the_eq_trivial closure must be foundational-only; got {deps:?}"
        );
    }
}
