// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Set / complete-lattice predicate encodings for the Isabelle Pure
//! translator (`Set.Ball`/`Bex`/`Pow`/`image`, lattice `Inf`/`Sup`, and the
//! shared `ex_encoding`/`curry2`). Moved verbatim from the original
//! single-file `connectives` module; behaviour is byte-identical.

use std::collections::BTreeMap;

use clean_kernel::expr::FVarId;
use clean_kernel::level::Level;
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Declaration, Environment, Expr};

use super::super::super::isabelle_pure::{IsaProof, IsaProvenTheorem, IsaTerm, IsaType};
use super::super::*;

/// The faithful semantic encoding of HOL's existential `HOL.Ex P` over an object
/// type `alpha` with predicate `p : alpha → Prop`:
///
/// ```text
/// ∀(Q : Prop). (∀(x : alpha). p x → Q) → Q
/// ```
///
/// Built with fresh `FVarId`s + `abstract_fvar` (no manual de Bruijn). `alpha`
/// and `p` are arbitrary closed clean terms; the kernel re-checks any use.
pub(crate) fn ex_encoding(alpha: &Expr, p: &Expr) -> Expr {
    const FQ: u64 = 0xE10_0001; // Q : Prop
    const FX: u64 = 0xE10_0002; // x : alpha
    let q = Expr::fvar(FVarId::new(FQ));
    // inner : ∀(x:alpha). p x → Q
    let inner = {
        let x = Expr::fvar(FVarId::new(FX));
        let px = Expr::app(p.clone(), x.clone());
        let body = Expr::arrow(px, q.clone());
        Expr::pi(
            BinderInfo::Default,
            alpha.clone(),
            body.abstract_fvar(FVarId::new(FX)),
        )
    };
    // (inner) → Q
    let arm = Expr::arrow(inner, q.clone());
    // ∀(Q:Prop). arm
    Expr::pi(
        BinderInfo::Default,
        Expr::prop(),
        arm.abstract_fvar(FVarId::new(FQ)),
    )
}

/// The faithful **predicate encoding** of a HOL `Set`/`Complete_Lattices` set
/// operation, as a *bare* (un-applied) clean lambda, under the `'a set = 'a → Prop`
/// model (see [`Ctx::embed_type`]). Returns `None` for a name we do not encode.
///
/// Each lambda is β-η-equal to exactly what the operation's own HOL
/// `…_def`/`…_set_def` axiom spells on the right (which embeds via the
/// already-handled `Set.Collect`/`Set.member`/`HOL.All`/`HOL.Ex`/`HOL.conj`/
/// `HOL.implies`/`HOL.eq` arms), so the definitional axiom becomes genuinely
/// reflexive — provable by `Eq.refl(lhs)`, which the kernel accepts **iff** the
/// LHS `op args` δ/β-reduces to the embedded RHS. A wrong encoding therefore
/// kernel-rejects and can never be miscounted; this is faithful (not a `B=B`
/// tautology) precisely because the stored proposition keeps the real
/// `op args = RHS` shape and the proof is sound only when the two genuinely
/// coincide.
///
/// Sub-operations the encoding does not itself model (e.g. the set-instance
/// `≤` in `Pow`) are embedded *consistently* — the same abstract `const:…`
/// parameter appears on both sides, so the equation still coincides. The object
/// element type `α` (and, for `image`, the codomain `β`) are read from the
/// constant's HOL type.
///
/// - `Set.Ball` (`'a set ⇒ ('a⇒bool) ⇒ bool`):
///   `λ(A:α→Prop)(P:α→Prop). ∀(x:α). A x → P x`.
/// - `Set.Bex` (`'a set ⇒ ('a⇒bool) ⇒ bool`):
///   `λ(A:α→Prop)(P:α→Prop). ∃(x:α). A x ∧ P x` (impredicative `∃`/`∧` encoding).
/// - `Set.Pow` (`'a set ⇒ 'a set set`):
///   `λ(A:α→Prop)(B:α→Prop). (B ≤ A)` — `≤` the (abstract) set-instance order.
/// - `Set.image` (`('a⇒'b) ⇒ 'a set ⇒ 'b set`):
///   `λ(f:α→β)(A:α→Prop)(y:β). ∃(x:α). A x ∧ @Eq β y (f x)`.
pub(crate) fn set_op_encoding(
    ctx: &mut Ctx,
    n: &str,
    t: &IsaType,
) -> Result<Option<Expr>, TranslateError> {
    // Element type `α` of a `'a set = 'a→Prop`-domained operation: read the first
    // argument of the constant's curried HOL type and pull `'a` from a
    // `Set.set['a]` or a function domain `'a ⇒ _`.
    pub(crate) fn set_dom(ctx: &mut Ctx, ty: &IsaType) -> Option<Expr> {
        let first = eq_operand_type(ty)?;
        match first {
            IsaType::Type { n, a } if n == "Set.set" && a.len() == 1 => ctx.embed_type(&a[0]).ok(),
            // `Set.image`'s first argument is the function `'a ⇒ 'b`; α is its domain.
            IsaType::Type { n, a } if n == "fun" && a.len() == 2 => ctx.embed_type(&a[0]).ok(),
            _ => None,
        }
    }
    match n {
        // λ(A:α→Prop)(P:α→Prop). ∀(x:α). A x → P x
        "Set.Ball" => Ok(set_dom(ctx, t).map(|alpha| ball_encoding(&alpha))),
        // λ(A:α→Prop)(P:α→Prop). ∃(x:α). A x ∧ P x
        "Set.Bex" => Ok(set_dom(ctx, t).map(|alpha| bex_encoding(&alpha))),
        // λ(A:α→Prop)(B:α→Prop). (B ≤ A) — `≤` the abstract set-instance order,
        // referenced as the same `const:…less_eq` param the RHS uses (keeping
        // both sides of `Pow_def` coincident). HOL type `'a set ⇒ 'a set set`.
        "Set.Pow" => {
            let Some(alpha) = set_dom(ctx, t) else {
                return Ok(None);
            };
            let set_ty = Expr::arrow(alpha, Expr::prop());
            // less_eq : (α→Prop) → (α→Prop) → Prop  (the set-instance `⊆`).
            let leq_ty = Expr::arrow(set_ty.clone(), Expr::arrow(set_ty.clone(), Expr::prop()));
            let leq = ctx.const_param("Orderings.ord_class.less_eq", leq_ty);
            Ok(Some(pow_encoding(&set_ty, &leq)))
        }
        // `insert a A ≡ {x. x = a ∨ x ∈ A}` — HOL's `insert_compr`. Under the
        // `'a set = 'a → Prop` model the RHS `Collect (λx. x = a ∨ member x A)`
        // embeds to `λx. (@Eq α x a) ∨ (A x)` (`Collect` is identity, `member` is
        // application, `HOL.disj`/`HOL.eq` embed to the `isabelle.def.HOL.disj`
        // def-const / object-level `@Eq`). Encoding `Set.insert` to exactly that
        // makes `insert_compr` (`insert a A = Collect …`) reflexive — the LHS
        // `insert a A` β-reduces to precisely the embedded RHS. HOL type
        // `'a ⇒ 'a set ⇒ 'a set`; α is its first operand type.
        "Set.insert" => {
            let Some(elem_ty) = eq_operand_type(t) else {
                return Ok(None);
            };
            let alpha = ctx.embed_type(elem_ty)?;
            Ok(Some(insert_encoding(&alpha)))
        }
        // λ(f:α→β)(A:α→Prop)(y:β). ∃(x:α). A x ∧ @Eq β y (f x)
        "Set.image" => {
            // α from the function domain; β from its codomain.
            let Some(alpha) = set_dom(ctx, t) else {
                return Ok(None);
            };
            let beta = match eq_operand_type(t) {
                Some(IsaType::Type { n, a }) if n == "fun" && a.len() == 2 => {
                    ctx.embed_type(&a[1])?
                }
                _ => return Ok(None),
            };
            Ok(Some(image_encoding(&alpha, &beta)))
        }
        // The complete-lattice `Inf`/`Sup` on the **set** instance
        // (`'a set set ⇒ 'a set`). HOL defines these compositionally, NOT by the
        // direct `∀S∈𝒮. …` form — `Inf_set 𝒮 = {x | Inf_bool {x∈S | S∈𝒮}}`
        // (`Inf_set_def`: `Inf 𝒮 = Collect(λx. Inf (image (λS. x∈S) 𝒮))`). To make
        // that equation reflexive we mirror the composition exactly, leaving the
        // inner `bool`-instance `Inf`/`Sup` and `Set.image` abstract-but-shared with
        // the RHS: the bool instance maps to its own instance-distinct `const:…@bool`
        // parameter (see below), so the same parameter appears on both sides of the
        // `_def` and the two coincide. The `'a set set ⇒ 'a set` shape is detected by
        // the result type being a `Set.set[…]`.
        "Complete_Lattices.Inf_class.Inf" | "Complete_Lattices.Sup_class.Sup"
            if lattice_result_is_set(t) =>
        {
            // α: the element type of the *result* set `'a set` (codomain).
            let Some(alpha) = lattice_result_elem(ctx, t) else {
                return Ok(None);
            };
            // The inner `bool`-instance operation, as an instance-distinct param
            // `(Prop→Prop) → Prop` keyed so it cannot collide with the set instance.
            let bool_op_ty = Expr::arrow(Expr::arrow(Expr::prop(), Expr::prop()), Expr::prop());
            let bool_op = ctx.term_param(&format!("const:{n}@bool"), bool_op_ty);
            Ok(Some(lattice_set_encoding(&alpha, &bool_op)))
        }
        // The `bool`-instance `Inf`/`Sup` (`bool set ⇒ bool`, i.e.
        // `(Prop→Prop)→Prop`) — kept abstract but under an **instance-distinct**
        // name so it never conflates with the set instance (same Isabelle const
        // name, different clean type). The set-instance encoding above references
        // exactly this parameter, so `Inf_set_def`/`Sup_set_def` stay coincident.
        "Complete_Lattices.Inf_class.Inf" | "Complete_Lattices.Sup_class.Sup"
            if lattice_result_is_bool(t) =>
        {
            let ty = ctx.embed_type(t)?;
            Ok(Some(ctx.term_param(&format!("const:{n}@bool"), ty)))
        }
        _ => Ok(None),
    }
}

/// Whether a complete-lattice `Inf`/`Sup` constant's HOL type `'a set set ⇒ 'a set`
/// is the **set** instance — its result (codomain) is a `Set.set[…]`.
pub(crate) fn lattice_result_is_set(t: &IsaType) -> bool {
    matches!(lattice_result_ty(t), Some(IsaType::Type { n, a }) if n == "Set.set" && a.len() == 1)
}

/// Whether a complete-lattice `Inf`/`Sup` constant is the **bool** instance — its
/// result (codomain) is `bool`.
pub(crate) fn lattice_result_is_bool(t: &IsaType) -> bool {
    matches!(lattice_result_ty(t), Some(IsaType::Type { n, .. }) if n == "HOL.bool" || n == "bool")
}

/// The result (codomain) type of an `Inf`/`Sup` constant `_ set ⇒ _`.
pub(crate) fn lattice_result_ty(t: &IsaType) -> Option<&IsaType> {
    match t {
        IsaType::Type { n, a } if n == "fun" && a.len() == 2 => Some(&a[1]),
        _ => None,
    }
}

/// The element type `α` of the **result** set `'a set` of a set-instance
/// `Inf`/`Sup` (`'a set set ⇒ 'a set`).
pub(crate) fn lattice_result_elem(ctx: &mut Ctx, t: &IsaType) -> Option<Expr> {
    match lattice_result_ty(t)? {
        IsaType::Type { n, a } if n == "Set.set" && a.len() == 1 => ctx.embed_type(&a[0]).ok(),
        _ => None,
    }
}

/// `λ(𝒮:(α→Prop)→Prop)(x:α). bool_op (image (λ(S:α→Prop). S x) 𝒮)` — the
/// compositional set-instance `Inf`/`Sup` encoding, mirroring HOL's
/// `Inf_set_def`/`Sup_set_def` exactly. `bool_op` is the (abstract, instance-
/// distinct) `bool`-instance `Inf`/`Sup` shared with the RHS; the `image` is the
/// faithful [`image_encoding`] (`(α→Prop) → Prop`), so both sides of the `_def`
/// coincide and the equation is reflexive.
pub(crate) fn lattice_set_encoding(alpha: &Expr, bool_op: &Expr) -> Expr {
    const FS: u64 = 0x1f5_0001; // 𝒮 : (α→Prop)→Prop
    const FX: u64 = 0x1f5_0002; // x : α
    const FSET: u64 = 0x1f5_0003; // S : α→Prop  (the inner-set binder of `λS. S x`)
    let set_ty = Expr::arrow(alpha.clone(), Expr::prop()); // 'a set = α→Prop
    let setset_ty = Expr::arrow(set_ty.clone(), Expr::prop()); // 'a set set
    let scr = Expr::fvar(FVarId::new(FS));
    let x = Expr::fvar(FVarId::new(FX));
    // membership-probe function  λ(S:α→Prop). S x  : (α→Prop) → Prop
    let probe = {
        let s = Expr::fvar(FVarId::new(FSET));
        let sx = Expr::app(s, x.clone());
        Expr::lam(
            BinderInfo::Default,
            set_ty.clone(),
            sx.abstract_fvar(FVarId::new(FSET)),
        )
    };
    // image (λS. S x) 𝒮  : bool set = Prop→Prop   (image over `(α→Prop)`, into Prop)
    let img = Expr::apps(image_encoding(&set_ty, &Expr::prop()), [probe, scr.clone()]);
    // bool_op (image …) : Prop
    let body = Expr::app(bool_op.clone(), img);
    // λ(x:α). body
    let xfun = Expr::lam(
        BinderInfo::Default,
        alpha.clone(),
        body.abstract_fvar(FVarId::new(FX)),
    );
    // λ(𝒮:'a set set). xfun
    Expr::lam(
        BinderInfo::Default,
        setset_ty,
        xfun.abstract_fvar(FVarId::new(FS)),
    )
}

/// `λ(A:α→Prop)(P:α→Prop). ∀(x:α). A x → P x` — the bounded-universal encoding
/// of `Set.Ball`. Built with fresh fvars + `abstract_fvar` (no manual de Bruijn).
pub(crate) fn ball_encoding(alpha: &Expr) -> Expr {
    const FA: u64 = 0x5e7_0001; // A : α→Prop
    const FP: u64 = 0x5e7_0002; // P : α→Prop
    const FX: u64 = 0x5e7_0003; // x : α
    let set_ty = Expr::arrow(alpha.clone(), Expr::prop());
    let a = Expr::fvar(FVarId::new(FA));
    let p = Expr::fvar(FVarId::new(FP));
    // ∀(x:α). A x → P x
    let body = {
        let x = Expr::fvar(FVarId::new(FX));
        let ax = Expr::app(a.clone(), x.clone());
        let px = Expr::app(p.clone(), x);
        Expr::pi(
            BinderInfo::Default,
            alpha.clone(),
            Expr::arrow(ax, px).abstract_fvar(FVarId::new(FX)),
        )
    };
    curry2(&set_ty, &set_ty, body, FA, FP)
}

/// `λ(A:α→Prop)(P:α→Prop). ∃(x:α). A x ∧ P x` — the bounded-existential encoding
/// of `Set.Bex`, reusing the impredicative `∃` ([`ex_encoding`]) and `∧`
/// ([`connective_def_name`] `HOL.conj`) so it coincides with the RHS embedding.
pub(crate) fn bex_encoding(alpha: &Expr) -> Expr {
    const FA: u64 = 0x5e8_0001; // A : α→Prop
    const FP: u64 = 0x5e8_0002; // P : α→Prop
    const FX: u64 = 0x5e8_0003; // x : α
    let set_ty = Expr::arrow(alpha.clone(), Expr::prop());
    let a = Expr::fvar(FVarId::new(FA));
    let p = Expr::fvar(FVarId::new(FP));
    // predicate λ(x:α). A x ∧ P x   (using the registered `conj` def-const).
    let pred = {
        let x = Expr::fvar(FVarId::new(FX));
        let ax = Expr::app(a.clone(), x.clone());
        let px = Expr::app(p.clone(), x);
        let conj = Expr::apps(conj_def_const(), [ax, px]);
        Expr::lam(
            BinderInfo::Default,
            alpha.clone(),
            conj.abstract_fvar(FVarId::new(FX)),
        )
    };
    let body = ex_encoding(alpha, &pred);
    curry2(&set_ty, &set_ty, body, FA, FP)
}

/// `λ(A:α→Prop)(B:α→Prop). (less_eq B A)` — the `Set.Pow` encoding (the powerset
/// `{B | B ⊆ A}` as a membership predicate), with `less_eq` the abstract
/// set-instance order shared with the RHS.
pub(crate) fn pow_encoding(set_ty: &Expr, less_eq: &Expr) -> Expr {
    const FA: u64 = 0x509_0001; // A : α→Prop
    const FB: u64 = 0x509_0002; // B : α→Prop
    let a = Expr::fvar(FVarId::new(FA));
    let b = Expr::fvar(FVarId::new(FB));
    // less_eq B A
    let body = Expr::apps(less_eq.clone(), [b, a]);
    curry2(set_ty, set_ty, body, FA, FB)
}

/// `λ(f:α→β)(A:α→Prop)(y:β). ∃(x:α). A x ∧ @Eq β y (f x)` — the `Set.image`
/// encoding. Reuses [`ex_encoding`] / the `HOL.conj` def-const / the object-level
/// `@Eq` so it coincides with the RHS embedding `Collect(λy. Bex A (λx. y = f x))`.
pub(crate) fn image_encoding(alpha: &Expr, beta: &Expr) -> Expr {
    const FF: u64 = 0x10a_0001; // f : α→β
    const FA: u64 = 0x10a_0002; // A : α→Prop
    const FY: u64 = 0x10a_0003; // y : β
    const FX: u64 = 0x10a_0004; // x : α
    let fun_ty = Expr::arrow(alpha.clone(), beta.clone());
    let set_ty = Expr::arrow(alpha.clone(), Expr::prop());
    let f = Expr::fvar(FVarId::new(FF));
    let a = Expr::fvar(FVarId::new(FA));
    let y = Expr::fvar(FVarId::new(FY));
    // predicate λ(x:α). A x ∧ @Eq β y (f x)
    let pred = {
        let x = Expr::fvar(FVarId::new(FX));
        let ax = Expr::app(a.clone(), x.clone());
        let fx = Expr::app(f.clone(), x);
        let eq = Expr::apps(
            Expr::const_str_levels("Eq", vec![obj_level()]),
            [beta.clone(), y.clone(), fx],
        );
        let conj = Expr::apps(conj_def_const(), [ax, eq]);
        Expr::lam(
            BinderInfo::Default,
            alpha.clone(),
            conj.abstract_fvar(FVarId::new(FX)),
        )
    };
    // λ(y:β). ∃(x:α). A x ∧ y = f x
    let yfun = Expr::lam(
        BinderInfo::Default,
        beta.clone(),
        ex_encoding(alpha, &pred).abstract_fvar(FVarId::new(FY)),
    );
    // λ(f:α→β)(A:α→Prop). yfun
    let inner = Expr::lam(
        BinderInfo::Default,
        set_ty,
        yfun.abstract_fvar(FVarId::new(FA)),
    );
    Expr::lam(
        BinderInfo::Default,
        fun_ty,
        inner.abstract_fvar(FVarId::new(FF)),
    )
}

/// `λ(a:α)(A:α→Prop)(x:α). (@Eq α x a) ∨ (A x)` — the `Set.insert` encoding under
/// the `'a set = 'a → Prop` model. Mirrors HOL's `insert_compr`
/// (`insert a A = {x. x = a ∨ x ∈ A}`): the disjunction uses the SAME
/// `isabelle.def.HOL.disj` def-const the RHS `HOL.disj` embeds to, and the
/// equality the object-level `@Eq α`, so `insert a A` β-reduces to exactly the
/// embedded RHS `Collect (λx. x = a ∨ member x A)` and the `insert_compr` equation
/// is reflexive. The kernel re-checks the `Eq.refl`, so a wrong encoding rejects.
pub(crate) fn insert_encoding(alpha: &Expr) -> Expr {
    const FA: u64 = 0x125_0001; // a : α  (the inserted element)
    const FSET: u64 = 0x125_0002; // A : α→Prop  (the base set)
    const FX: u64 = 0x125_0003; // x : α  (the membership probe)
    let set_ty = Expr::arrow(alpha.clone(), Expr::prop());
    let a = Expr::fvar(FVarId::new(FA));
    let set = Expr::fvar(FVarId::new(FSET));
    // λ(x:α). (@Eq α x a) ∨ (A x)
    let xfun = {
        let x = Expr::fvar(FVarId::new(FX));
        let eq = Expr::apps(
            Expr::const_str_levels("Eq", vec![obj_level()]),
            [alpha.clone(), x.clone(), a.clone()],
        );
        let mem = Expr::app(set.clone(), x);
        let disj = Expr::apps(disj_def_const(), [eq, mem]);
        Expr::lam(
            BinderInfo::Default,
            alpha.clone(),
            disj.abstract_fvar(FVarId::new(FX)),
        )
    };
    // λ(a:α)(A:α→Prop). xfun
    let inner = Expr::lam(
        BinderInfo::Default,
        set_ty,
        xfun.abstract_fvar(FVarId::new(FSET)),
    );
    Expr::lam(
        BinderInfo::Default,
        alpha.clone(),
        inner.abstract_fvar(FVarId::new(FA)),
    )
}

/// `λ(p:t0)(q:t1). body[p,q]` — close `body` over two fresh fvars `p0`/`p1` in
/// order, producing the curried lambda. Used by the set-op encodings.
pub(crate) fn curry2(t0: &Expr, t1: &Expr, body: Expr, p0: u64, p1: u64) -> Expr {
    let inner = Expr::lam(
        BinderInfo::Default,
        t1.clone(),
        body.abstract_fvar(FVarId::new(p1)),
    );
    Expr::lam(
        BinderInfo::Default,
        t0.clone(),
        inner.abstract_fvar(FVarId::new(p0)),
    )
}
