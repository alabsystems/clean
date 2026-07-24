// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Pointwise / type-constructor **instance-operation** encodings for the Isabelle
//! Pure translator: the faithful semantic lambdas that make the
//! `…_fun_inst.…_fun_def` (pointwise lattice/order ops on `'a ⇒ 'b`),
//! `equal_itself_def` (executable equality on `itself`), and `ord.max`/`min`
//! (if-then-else order methods) definitional equations *reflexive*. Split out of
//! `sets.rs` to keep each file under the size limit; the shared `curry2`/
//! `image_encoding`/`ex_encoding` helpers stay in `sets.rs` and are used here via
//! the `connectives` re-export.

use clean_kernel::expr::FVarId;
use clean_kernel::{BinderInfo, Expr};

use super::super::super::isabelle_pure::{IsaProvenTheorem, IsaTerm, IsaType};
use super::super::*;

/// The faithful **pointwise-lift encoding** of an overloaded lattice/order class
/// operation `c_class.op` **at a function instance** `'a ⇒ 'b` — the semantic
/// lambda HOL's `…_fun_inst.…_fun_def` axiom spells on the right:
///
/// ```text
/// (f ⊓ g)  ≡  λx. (f x) ⊓ (g x)      (sup / inf / minus : binary, pointwise app)
/// (- f)    ≡  λx. - (f x)             (uminus / abs      : unary,  pointwise app)
/// ⊥        ≡  λx. ⊥                   (bot / top         : nullary constant)
/// (f ≤ g)  ≡  ∀x. (f x) ≤ (g x)       (less_eq           : binary relation)
/// ```
///
/// The inner element-instance operation (the `⊓`/`-`/`⊥`/`≤` **on `'b`**) is
/// referenced as the SAME abstract `const:<op>` parameter the operation's RHS
/// embeds it to (keyed by name only, at the *element* type `β`), so both sides of
/// the `…_fun_def` equation contain the identical fvar and the equation is
/// **genuinely reflexive** — provable by `Eq.refl(lhs)`, which the kernel accepts
/// **iff** the pointwise LHS β-reduces to the embedded RHS. This is faithful (not a
/// `B = B` tautology): the stored proposition keeps the real
/// `op@fun args = (pointwise body)` shape, and the proof is sound only because the
/// two genuinely coincide. A wrong encoding therefore kernel-rejects and can never
/// be miscounted.
///
/// Fires **only** when the operation's *first operand type* is a syntactic `fun`
/// arrow `'a ⇒ 'b` (the function instance), so it never intercepts the element
/// instance (`op@'b`, operand a bare `TVar`), a ground instance (handled by the
/// instance-op registry), or a set instance (operand `Set.set[..]`, handled by
/// [`set_op_encoding`]). Returns `None` for any other name/type so the caller
/// falls through to the opaque-parameter embedding.
pub(crate) fn pointwise_fun_instance_op(
    ctx: &mut Ctx,
    n: &str,
    t: &IsaType,
) -> Result<Option<Expr>, TranslateError> {
    // A RAW function-instance implementation constant `<M>.<c>_fun_inst.<c>_fun`
    // (`Lattices.sup_fun_inst.sup_fun`, …) IS Isabelle's `instance …` definition of
    // the class op on `'a ⇒ 'b` — DEFINITIONALLY the same pointwise lambda the class
    // op `<c>_class.<c>` at the function instance denotes. So it embeds to the SAME
    // encoding: rewrite the impl name to its element class op and continue. This
    // makes the `<c>_class.<c> ≡ <c>_fun` instance-registration equation reflexive
    // (both sides are the identical pointwise lambda), on top of the pointwise
    // `<c>_class.<c> ≡ λf g x. …` equation. Faithful: the kernel re-checks the
    // resulting `Eq.refl`, so a wrong mapping is rejected — never miscounted.
    if let Some(class_op) = fun_impl_const_class_op(n) {
        return pointwise_fun_instance_op(ctx, class_op, t);
    }
    // HOL's executable equality `equal_class.equal @ (τ ⇒ τ ⇒ bool)` at the
    // `itself` / `Sum_Type.sum` / `Product_Type.prod` instances IS propositional
    // equality on `τ` — each instance's raw definition literally spells `(=)`
    // (`equal_itself_def` / `Sum_Type.equal_sum_def_raw` /
    // `Product_Type.equal_prod_def_raw`: `equal x y ≡ (x = y)`). Encode it as
    // `λ(x:τ)(y:τ). @Eq τ x y` — the SAME clean term the RHS `HOL.eq x y` embeds
    // to (`embed_app`'s `@Eq` spine), so the definitional equation is reflexive.
    // Scoped to exactly these instances (whose raw def IS `=`) to stay
    // conservative; other `equal` instances (e.g. `Set.set`, whose raw def is the
    // NON-definitional `A ⊆ B ∧ B ⊆ A`) keep the opaque param. The kernel
    // re-checks the `Eq.refl`, so a mis-encoding is rejected.
    if n == "HOL.equal_class.equal" {
        if let Some(IsaType::Type { n: dom_head, .. }) = eq_operand_type(t) {
            if matches!(
                dom_head.as_str(),
                "itself" | "Sum_Type.sum" | "Product_Type.prod"
            ) {
                let Some(elem_ty) = eq_operand_type(t) else {
                    return Ok(None);
                };
                let tau = ctx.embed_type(elem_ty)?;
                return Ok(Some(equal_encoding(&tau)));
            }
        }
        return Ok(None);
    }
    // HOL's `nat` lattice instance DEFINES `inf`/`sup` at `nat` as the order
    // methods `min`/`max` (`Nat.inf_nat_def_raw`: `inf_nat ≡ min`,
    // `Nat.sup_nat_def_raw`: `sup_nat ≡ max` — with the registration equations
    // `inf ≡ inf_nat` / `sup ≡ sup_nat` composing to `inf ≡ min` / `sup ≡ max`).
    // So the class op at the ground `nat` instance embeds to the SAME clean term
    // `Orderings.ord_class.min`/`max` at that type embeds to (re-dispatched
    // through the ordinary `Const` path, honouring the active `method_unfold`
    // flag identically to a direct `min`/`max` occurrence). This makes the whole
    // `inf_nat`/`sup_nat` def family (`…_inst.…_def`, `…_def_raw`, the composed
    // `inf ≡ min` node, and the named HOL-eq `inf_nat_def`) genuinely reflexive.
    // Faithful: the identification is Isabelle's own definition of `inf@nat`; the
    // kernel re-checks every resulting `Eq.refl`, so a wrong collapse is rejected
    // — never miscounted. Non-`nat` instances fall through unchanged (the
    // function-instance pointwise arms below, or the opaque param).
    if matches!(n, "Lattices.inf_class.inf" | "Lattices.sup_class.sup") {
        if let Some(IsaType::Type { n: op0, a: op0a }) = eq_operand_type(t) {
            if op0 == "Nat.nat" && op0a.is_empty() {
                let target = if n == "Lattices.inf_class.inf" {
                    "Orderings.ord_class.min"
                } else {
                    "Orderings.ord_class.max"
                };
                return ctx.embed_element_op(target, t).map(Some);
            }
        }
    }
    // HOL's order-class methods `Orderings.ord.max`/`min` are plain polymorphic
    // functions that take the order relation `≤` as an EXPLICIT argument (not an
    // overloaded `_class.` method), defined via if-then-else:
    // `max le a b ≡ if le a b then b else a`, `min le a b ≡ if le a b then a else b`.
    // Encode the bare constant `ord.max`/`min : (α→α→bool)→α→α→α` as the semantic
    // lambda `λ(le)(a)(b). (@If α) (le a b) X Y`, routing the `if` through the SAME
    // `isabelle.def.HOL.If` def-const the RHS uses (so both sides coincide). Applied
    // to `?le ?a ?b` it β-reduces to exactly the embedded RHS, so the `…_def`
    // equation is reflexive. The relation `le` is the innermost bound binder (the
    // consumer's own `?le` fills it), so no element operation is threaded.
    if n == "Orderings.ord.max" || n == "Orderings.ord.min" {
        // t = (α→α→bool) → α → α → α ; read α off the relation's domain.
        let Some(rel_ty) = eq_operand_type(t) else {
            return Ok(None);
        };
        let Some(elem_ty) = eq_operand_type(rel_ty) else {
            return Ok(None);
        };
        let alpha = ctx.embed_type(elem_ty)?;
        let max_first = n == "Orderings.ord.max"; // max: then=b else=a ; min: then=a else=b
        return Ok(Some(ord_minmax_encoding(&alpha, max_first)));
    }
    // A HOL `fun` arrow type constructor `d ⇒ r`.
    let arrow = |d: &IsaType, r: &IsaType| IsaType::Type {
        n: "fun".to_string(),
        a: vec![d.clone(), r.clone()],
    };
    let bool_ty = IsaType::Type {
        n: "HOL.bool".to_string(),
        a: Vec::new(),
    };
    // The complete-lattice `Inf`/`Sup` at the **function instance**
    // (`(('a⇒'b) set) ⇒ ('a⇒'b)`) — HOL's `Inf_fun_def`/`Sup_fun_def`:
    //   `Inf A ≡ (λx. Inf ((λf. f x) ` A))`
    // (the pointwise lift through `Set.image`). Encode the class op as the
    // semantic lambda `λ(A:(α→β)→Prop)(x:α). op_β (image (λf. f x) A)`, where
    // `image` is the SAME [`image_encoding`] the RHS's `Set.image` embeds to and
    // `op_β` is the element-instance `Inf`/`Sup` at `'b` embedded through the SAME
    // dispatch the RHS's inner occurrence uses (an opaque `const:` param at a
    // `TVar` element; the set/bool encodings at those instances) — so both sides
    // of the `…_def` equation coincide and it is genuinely reflexive. Fires only
    // when the operand is a set OF FUNCTIONS, so the set instance
    // (`'a set set ⇒ 'a set`, [`set_op_encoding`]) and bool instance are never
    // intercepted.
    if matches!(
        n,
        "Complete_Lattices.Inf_class.Inf" | "Complete_Lattices.Sup_class.Sup"
    ) {
        if let Some(IsaType::Type { n: op0, a: op0a }) = eq_operand_type(t) {
            if op0 == "Set.set" && op0a.len() == 1 {
                if let IsaType::Type { n: f_head, a: fa } = &op0a[0] {
                    if f_head == "fun" && fa.len() == 2 {
                        let alpha = ctx.embed_type(&fa[0])?;
                        let beta = ctx.embed_type(&fa[1])?;
                        let set_b = IsaType::Type {
                            n: "Set.set".to_string(),
                            a: vec![fa[1].clone()],
                        };
                        let elem_op_ty = arrow(&set_b, &fa[1]);
                        let op = ctx.embed_element_op(n, &elem_op_ty)?;
                        return Ok(Some(lattice_fun_encoding(&alpha, &beta, &op)));
                    }
                }
            }
        }
        return Ok(None);
    }
    // NULLARY constant: the constant's OWN type IS the function instance `'a ⇒ 'b`
    // (`bot : 'a ⇒ 'b`), so read `'a`/`'b` off `t` directly. `⊥@fun ≡ λx. ⊥@'b`.
    if matches!(
        n,
        "Orderings.bot_class.bot"
            | "Orderings.top_class.top"
            | "Groups.zero_class.zero"
            | "Groups.one_class.one"
    ) {
        let Some((dom_isa, cod_isa)) = fun_split(t) else {
            return Ok(None);
        };
        let alpha = ctx.embed_type(dom_isa)?;
        let c = ctx.embed_element_op(n, cod_isa)?;
        return Ok(Some(pointwise_const(&alpha, &c)));
    }
    // APPLIED ops: the constant's FIRST operand type is the function instance
    // `'a ⇒ 'b` (`sup : ('a⇒'b) ⇒ …`), so read `'a`/`'b` off that operand.
    let Some(IsaType::Type {
        n: op0_head,
        a: op0_args,
    }) = eq_operand_type(t)
    else {
        return Ok(None);
    };
    if op0_head != "fun" || op0_args.len() != 2 {
        return Ok(None);
    }
    let elem_isa = op0_args[1].clone(); // 'b  (codomain; the element instance type)
    let alpha = ctx.embed_type(&op0_args[0])?; // α  (domain of the function)
    let beta = ctx.embed_type(&op0_args[1])?; // β  (codomain; the element type)
    let fun_ty = Expr::arrow(alpha.clone(), beta.clone()); // 'a ⇒ 'b
    match n {
        // Binary pointwise app: (f ⊓ g) ≡ λx. op_β (f x) (g x).
        "Lattices.sup_class.sup"
        | "Lattices.inf_class.inf"
        | "Groups.minus_class.minus"
        | "Groups.plus_class.plus"
        | "Groups.times_class.times" => {
            // Element op `op@('b⇒'b⇒'b)`, embedded through the SAME dispatch the RHS
            // occurrence uses (opaque `const:` param, or method/instance def-const under
            // the active unfold flags) — so the two coincide in every pass.
            let elem_op_ty = arrow(&elem_isa, &arrow(&elem_isa, &elem_isa));
            let op = ctx.embed_element_op(n, &elem_op_ty)?;
            Ok(Some(pointwise_binary(&fun_ty, &alpha, &op)))
        }
        // Unary pointwise app: (- f) ≡ λx. op_β (f x).
        "Groups.uminus_class.uminus" | "Groups.abs_class.abs" => {
            let elem_op_ty = arrow(&elem_isa, &elem_isa);
            let op = ctx.embed_element_op(n, &elem_op_ty)?;
            Ok(Some(pointwise_unary(&fun_ty, &alpha, &op)))
        }
        // Non-strict order `(f ≤ g) ≡ ∀x. (f x) ≤ (g x)` — the pointwise universal
        // lift (`le_fun_def`). `op` is the element `≤@'b`.
        "Orderings.ord_class.less_eq" => {
            let elem_op_ty = arrow(&elem_isa, &arrow(&elem_isa, &bool_ty));
            let op = ctx.embed_element_op(n, &elem_op_ty)?;
            Ok(Some(pointwise_relation(&fun_ty, &alpha, &op)))
        }
        // Strict order `(f < g) ≡ (f ≤ g) ∧ ¬ (g ≤ f)` on the function instance
        // (`less_fun_def`) — the RHS uses the **function-instance** `≤` (itself the
        // pointwise `∀x. …`), NOT the element `<`. So encode `<@fun` as
        // `λf g. conj (∀x. le (f x) (g x)) (Not (∀x. le (g x) (f x)))`, where `le` is
        // the element `≤@'b` and `conj`/`Not` are the SAME connective def-consts the
        // RHS embeds to — so the whole equation is reflexive.
        "Orderings.ord_class.less" => {
            let elem_le_ty = arrow(&elem_isa, &arrow(&elem_isa, &bool_ty));
            let le = ctx.embed_element_op("Orderings.ord_class.less_eq", &elem_le_ty)?;
            Ok(Some(pointwise_strict_less(&fun_ty, &alpha, &le)))
        }
        _ => Ok(None),
    }
}

/// Map a RAW function-instance implementation constant name
/// `<M>.<c>_fun_inst.<c>_fun` to the **element class operation** it lifts pointwise
/// (`Lattices.sup_fun_inst.sup_fun` → `Lattices.sup_class.sup`), or `None` for a
/// name that is not one of the pointwise-liftable instance impls. Each impl is
/// definitionally the same body its element class op's function-instance encoding
/// produces (pointwise lift for `sup`/`inf`/`minus`/`uminus`/`bot`/`top`/`less_eq`;
/// the strict-from-nonstrict encoding for `less`), so the `<c>_class.<c> ≡ <c>_fun`
/// instance-registration equation is reflexive.
pub(crate) fn fun_impl_const_class_op(n: &str) -> Option<&'static str> {
    Some(match n {
        "Lattices.sup_fun_inst.sup_fun" => "Lattices.sup_class.sup",
        "Lattices.inf_fun_inst.inf_fun" => "Lattices.inf_class.inf",
        "Lattices.minus_fun_inst.minus_fun" => "Groups.minus_class.minus",
        "Lattices.uminus_fun_inst.uminus_fun" => "Groups.uminus_class.uminus",
        "Orderings.bot_fun_inst.bot_fun" => "Orderings.bot_class.bot",
        "Orderings.top_fun_inst.top_fun" => "Orderings.top_class.top",
        "Orderings.ord_fun_inst.less_eq_fun" => "Orderings.ord_class.less_eq",
        "Orderings.ord_fun_inst.less_fun" => "Orderings.ord_class.less",
        "Complete_Lattices.Inf_fun_inst.Inf_fun" => "Complete_Lattices.Inf_class.Inf",
        "Complete_Lattices.Sup_fun_inst.Sup_fun" => "Complete_Lattices.Sup_class.Sup",
        _ => return None,
    })
}

/// Map a RAW **bool-instance** implementation constant name
/// `<M>.<c>_bool_inst.<c>_bool` to the **class operation** it implements
/// (`Boolean_Algebras.sup_bool_inst.sup_bool` → `Lattices.sup_class.sup`), or
/// `None` for a name that is not one of the recognized bool-instance impls.
///
/// Isabelle registers each class operation's `bool` instance with a definitional
/// axiom `<c>_class.<c> ≡ <c>_bool_inst.<c>_bool` (the `boolean_algebra`/order
/// instantiation of `bool`). In clean's overloading model the impl const IS the
/// class op at `bool` — the two denote the identical element — so the impl name
/// embeds to the SAME opaque `const:<c>_class.<c>` parameter the class op embeds
/// to, making the registration equation genuinely reflexive
/// (`const:<c>_class.<c> = const:<c>_class.<c>`, provable by `Eq.refl`). This is
/// the ground-type analogue of [`fun_impl_const_class_op`] (which does the same
/// for the `'a ⇒ 'b` function instance). Applied only under the final
/// `instance_unfold` escalating pass (strictly additive — an earlier opaque pass
/// keeps the two params distinct), and the kernel re-checks the resulting
/// `Eq.refl`, so a wrong mapping is rejected — never miscounted.
pub(crate) fn bool_impl_const_class_op(n: &str) -> Option<&'static str> {
    Some(match n {
        "Boolean_Algebras.sup_bool_inst.sup_bool" => "Lattices.sup_class.sup",
        "Boolean_Algebras.inf_bool_inst.inf_bool" => "Lattices.inf_class.inf",
        "Boolean_Algebras.minus_bool_inst.minus_bool" => "Groups.minus_class.minus",
        "Boolean_Algebras.uminus_bool_inst.uminus_bool" => "Groups.uminus_class.uminus",
        "Orderings.bot_bool_inst.bot_bool" => "Orderings.bot_class.bot",
        "Orderings.top_bool_inst.top_bool" => "Orderings.top_class.top",
        "Orderings.ord_bool_inst.less_eq_bool" => "Orderings.ord_class.less_eq",
        "Orderings.ord_bool_inst.less_bool" => "Orderings.ord_class.less",
        _ => return None,
    })
}

/// Map a RAW **ground/type-constructor instance** implementation constant name
/// `<M>.<c>_<T>_inst.<c>_<T>` to the **class operation** it implements
/// (`Nat.inf_nat_inst.inf_nat` → `Lattices.inf_class.inf`,
/// `Product_Type.equal_prod_inst.equal_prod` → `HOL.equal_class.equal`, …), or
/// `None` for a name that is not one of the recognized instance impls.
///
/// Isabelle registers each instance with a definitional axiom
/// `<c>_class.<c> ≡ <c>_<T>_inst.<c>_<T>` (the overloading link). In clean's
/// overloading model the impl const IS the class op at that instance — the two
/// denote the identical element — so the impl name embeds through the SAME
/// `Const` dispatch the class op uses at the same type (the direct `0::nat ↦
/// Nat.zero` mapping, the `inf@nat ↦ min` collapse, the `equal@sum/prod ↦ @Eq`
/// encoding, or the shared opaque `const:<c>_class.<c>` param), making the
/// registration equation genuinely reflexive. This is the non-`bool` ground
/// analogue of [`bool_impl_const_class_op`] (same dispatch arm, same
/// `instance_unfold` gating — strictly additive), covering the one-off instance
/// `_def` axioms the 20-theory corpus exports standalone. The kernel re-checks
/// every resulting `Eq.refl`, so a wrong mapping is rejected — never miscounted.
pub(crate) fn ground_impl_const_class_op(n: &str) -> Option<&'static str> {
    Some(match n {
        "Nat.inf_nat_inst.inf_nat" => "Lattices.inf_class.inf",
        "Nat.sup_nat_inst.sup_nat" => "Lattices.sup_class.sup",
        "Nat.zero_nat_inst.zero_nat" => "Groups.zero_class.zero",
        "Set.equal_set_inst.equal_set" => "HOL.equal_class.equal",
        "Sum_Type.equal_sum_inst.equal_sum" => "HOL.equal_class.equal",
        "Product_Type.equal_prod_inst.equal_prod" => "HOL.equal_class.equal",
        _ => return None,
    })
}

/// Whether an overloaded operation `(n, t)` is one [`pointwise_fun_instance_op`]
/// encodes at this instance type — i.e. a lattice/order class op at a function
/// instance (`sup`/`inf`/`minus`/`uminus`/`bot`/`top`/`less_eq`/`less`/…, first
/// operand a `fun` arrow), `equal_class.equal` at the `itself` instance, or the
/// `ord.max`/`min` if-then-else order methods. Used to SCOPE the reflexive
/// definitional-axiom proof arm to exactly these instance defs (so it never
/// re-proves unrelated `_def` equations by reflexivity, which would perturb the
/// shared closure). Keyed on the *statement shape* — the LHS head constant and its
/// instance type — mirroring the encoder's own name/type dispatch.
pub(crate) fn is_pointwise_instance_op_head(n: &str, t: &IsaType) -> bool {
    // A raw impl const lifts to its element class op (same instance type), so it is
    // recognized exactly when its class op is.
    if let Some(class_op) = fun_impl_const_class_op(n) {
        return is_pointwise_instance_op_head(class_op, t);
    }
    // Likewise a raw ground-instance impl const (`Nat.inf_nat_inst.inf_nat`, …) —
    // recognized exactly when its class op is at the same instance type.
    if let Some(class_op) = ground_impl_const_class_op(n) {
        return is_pointwise_instance_op_head(class_op, t);
    }
    // `inf`/`sup` at the ground `nat` instance — the `min`/`max` collapse (exactly
    // the encoder's `Nat.nat` operand gate). Checked before the generic applied-op
    // arm below (whose gate requires a `fun`-arrow operand).
    if matches!(n, "Lattices.inf_class.inf" | "Lattices.sup_class.sup")
        && matches!(
            eq_operand_type(t),
            Some(IsaType::Type { n: h, a }) if h == "Nat.nat" && a.is_empty()
        )
    {
        return true;
    }
    match n {
        // `equal` at the instances whose raw definition IS `(=)` — `itself`,
        // `Sum_Type.sum`, `Product_Type.prod` (exactly the encoder's gate).
        "HOL.equal_class.equal" => {
            matches!(
                eq_operand_type(t),
                Some(IsaType::Type { n: h, .. })
                    if matches!(h.as_str(), "itself" | "Sum_Type.sum" | "Product_Type.prod")
            )
        }
        // `ord.max`/`min`: the relation-taking order methods (no instance-type gate;
        // the encoder reads α off the relation domain).
        "Orderings.ord.max" | "Orderings.ord.min" => true,
        // Nullary constants at a FUNCTION instance — the constant's OWN type is the
        // instance `'a ⇒ 'b` (`bot : 'a ⇒ 'b`), so `t` itself must be a `fun` arrow.
        "Orderings.bot_class.bot"
        | "Orderings.top_class.top"
        | "Groups.zero_class.zero"
        | "Groups.one_class.one" => {
            matches!(t, IsaType::Type { n: h, a } if h == "fun" && a.len() == 2)
        }
        // The APPLIED pointwise lattice/order class ops, at a FUNCTION instance (first
        // operand a `fun` arrow) — exactly the encoder's `fun`-gated branch.
        "Lattices.sup_class.sup"
        | "Lattices.inf_class.inf"
        | "Groups.minus_class.minus"
        | "Groups.plus_class.plus"
        | "Groups.times_class.times"
        | "Groups.uminus_class.uminus"
        | "Groups.abs_class.abs"
        | "Orderings.ord_class.less_eq"
        | "Orderings.ord_class.less" => {
            matches!(eq_operand_type(t), Some(IsaType::Type { n: h, a }) if h == "fun" && a.len() == 2)
        }
        // The complete-lattice `Inf`/`Sup` at a FUNCTION instance — the operand is
        // a set OF FUNCTIONS `('a⇒'b) set` (exactly the encoder's gate), so the
        // set instance (`'a set set`) and bool instance are never intercepted.
        "Complete_Lattices.Inf_class.Inf" | "Complete_Lattices.Sup_class.Sup" => {
            matches!(
                eq_operand_type(t),
                Some(IsaType::Type { n: h, a })
                    if h == "Set.set"
                        && a.len() == 1
                        && matches!(&a[0], IsaType::Type { n: f, a: fa } if f == "fun" && fa.len() == 2)
            )
        }
        _ => false,
    }
}

/// Whether `thm`'s conclusion (after stripping leading sort/`Pure.imp` premises) is
/// a **pointwise / type-constructor instance-operation definition** —
/// `Pure.eq (op@instance args) rhs` whose LHS head `op@instance` is one
/// [`pointwise_fun_instance_op`] encodes ([`is_pointwise_instance_op_head`]). These
/// are the `…_fun_inst.…_fun_def`, `equal_itself_def`, and `ord.max`/`min` `_def`
/// axioms whose recorded proof bottoms out in an unmapped `…_def`/`…_def_raw` PAxm
/// leaf; the LHS now embeds to the faithful pointwise/if-lambda that β-reduces to
/// the embedded RHS, so the whole equation is reflexive. Scopes the reflexive proof
/// arm to exactly these defs.
pub(crate) fn is_pointwise_instance_def(thm: &IsaProvenTheorem) -> bool {
    let concl = strip_leading_imps(&thm.prop);
    let Some((lhs, _rhs)) = pure_eq_parts(concl) else {
        return false;
    };
    // Peel the LHS application spine to the head constant `op` and its type.
    let (head, _args) = term_app_spine(lhs);
    matches!(head, IsaTerm::Const { n, t } if is_pointwise_instance_op_head(n, t))
}

impl Ctx {
    /// Embed the **element-instance** occurrence of an overloaded operation `n` at
    /// element-operation type `elem_op_ty` (`'b⇒'b⇒'b`, `'b`, …) — the SAME clean
    /// term the pointwise `_fun_def` RHS's inner occurrence produces, so both sides
    /// of the equation coincide. Routes through the ordinary `Const` dispatch
    /// ([`Self::embed_term`]) so it honours the active `method_unfold` /
    /// `instance_unfold` flags identically to the RHS (opaque `const:` param when
    /// neither fires, dictionary/instance def-const when they do). The kernel
    /// re-checks the resulting `Eq.refl`, so a mismatch is rejected — never miscounted.
    pub(crate) fn embed_element_op(
        &mut self,
        n: &str,
        elem_op_ty: &IsaType,
    ) -> Result<Expr, TranslateError> {
        let mut binders: Vec<Binder> = Vec::new();
        self.embed_term(
            &IsaTerm::Const {
                n: n.to_string(),
                t: elem_op_ty.clone(),
            },
            &mut binders,
        )
    }
}

/// `λ(le:α→α→Prop)(a:α)(b:α). (@isabelle.def.HOL.If.{u} α) (le a b) X Y` — the
/// `Orderings.ord.max`/`min` encoding. `X`/`Y` are `(b, a)` for `max`
/// (`max_first = true`) and `(a, b)` for `min`. The `if` head is the SAME
/// `isabelle.def.HOL.If` def-const the RHS `HOL.If (le a b) X Y` embeds to, so the
/// `…_def` equation is reflexive. `u` is `α`'s universe (matching `embed_hol_if`).
pub(crate) fn ord_minmax_encoding(alpha: &Expr, max_first: bool) -> Expr {
    const FLE: u64 = 0xf0f_0001; // le : α→α→Prop
    const FA: u64 = 0xf0f_0002; // a : α
    const FB: u64 = 0xf0f_0003; // b : α
    let le = Expr::fvar(FVarId::new(FLE));
    let a = Expr::fvar(FVarId::new(FA));
    let b = Expr::fvar(FVarId::new(FB));
    let cond = Expr::apps(le, [a.clone(), b.clone()]); // le a b : Prop
    let (then_br, else_br) = if max_first {
        (b.clone(), a.clone())
    } else {
        (a.clone(), b.clone())
    };
    let u = type_universe_level(alpha);
    // (@isabelle.def.HOL.If.{u} α) cond then else
    let if_head = Expr::app(
        Expr::const_str_levels(hol_if_def_name(), vec![u]),
        alpha.clone(),
    );
    let body = Expr::apps(if_head, [cond, then_br, else_br]);
    // λ(le)(a)(b). body — abstract innermost-first (b, a, le).
    let rel_ty = Expr::arrow(alpha.clone(), Expr::arrow(alpha.clone(), Expr::prop()));
    let lam_b = Expr::lam(
        BinderInfo::Default,
        alpha.clone(),
        body.abstract_fvar(FVarId::new(FB)),
    );
    let lam_ab = Expr::lam(
        BinderInfo::Default,
        alpha.clone(),
        lam_b.abstract_fvar(FVarId::new(FA)),
    );
    Expr::lam(
        BinderInfo::Default,
        rel_ty,
        lam_ab.abstract_fvar(FVarId::new(FLE)),
    )
}

/// `λ(x:τ)(y:τ). @Eq τ x y` — the executable-equality encoding (HOL's `equal`
/// class op IS propositional `=`), matching how the RHS `HOL.eq x y` embeds.
pub(crate) fn equal_encoding(tau: &Expr) -> Expr {
    const FX: u64 = 0xf0e_0001; // x : τ
    const FY: u64 = 0xf0e_0002; // y : τ
    let x = Expr::fvar(FVarId::new(FX));
    let y = Expr::fvar(FVarId::new(FY));
    let body = Expr::apps(
        Expr::const_str_levels("Eq", vec![obj_level()]),
        [tau.clone(), x, y],
    );
    curry2(tau, tau, body, FX, FY)
}

/// `λ(f:α→β)(g:α→β)(x:α). op (f x) (g x)` — the binary pointwise lift.
pub(crate) fn pointwise_binary(fun_ty: &Expr, alpha: &Expr, op: &Expr) -> Expr {
    const FF: u64 = 0xf0a_0001; // f : α→β
    const FG: u64 = 0xf0a_0002; // g : α→β
    const FX: u64 = 0xf0a_0003; // x : α
    let f = Expr::fvar(FVarId::new(FF));
    let g = Expr::fvar(FVarId::new(FG));
    let inner = {
        let x = Expr::fvar(FVarId::new(FX));
        let fx = Expr::app(f.clone(), x.clone());
        let gx = Expr::app(g.clone(), x);
        let body = Expr::apps(op.clone(), [fx, gx]);
        Expr::lam(
            BinderInfo::Default,
            alpha.clone(),
            body.abstract_fvar(FVarId::new(FX)),
        )
    };
    curry2(fun_ty, fun_ty, inner, FF, FG)
}

/// `λ(f:α→β)(x:α). op (f x)` — the unary pointwise lift.
pub(crate) fn pointwise_unary(fun_ty: &Expr, alpha: &Expr, op: &Expr) -> Expr {
    const FF: u64 = 0xf0b_0001; // f : α→β
    const FX: u64 = 0xf0b_0002; // x : α
    let f = Expr::fvar(FVarId::new(FF));
    let inner = {
        let x = Expr::fvar(FVarId::new(FX));
        let fx = Expr::app(f.clone(), x);
        let body = Expr::app(op.clone(), fx);
        Expr::lam(
            BinderInfo::Default,
            alpha.clone(),
            body.abstract_fvar(FVarId::new(FX)),
        )
    };
    Expr::lam(
        BinderInfo::Default,
        fun_ty.clone(),
        inner.abstract_fvar(FVarId::new(FF)),
    )
}

/// `λ(x:α). c` — the nullary-constant pointwise lift (`⊥`/`⊤`/`0`/`1` on a
/// function instance is the constant function returning the element-instance
/// constant `c`).
pub(crate) fn pointwise_const(alpha: &Expr, c: &Expr) -> Expr {
    const FX: u64 = 0xf0c_0001; // x : α
                                // `c` is closed w.r.t. `x`, so abstracting a fresh (unused) `x` fvar yields the
                                // constant function `λx. c`.
    Expr::lam(
        BinderInfo::Default,
        alpha.clone(),
        c.clone().abstract_fvar(FVarId::new(FX)),
    )
}

/// `λ(f:α→β)(g:α→β). ∀(x:α). op (f x) (g x)` — the binary-relation pointwise lift
/// (`≤` on a function instance is the universally-quantified pointwise order). The
/// `∀` is built as clean `Pi`, matching how the RHS `HOL.All (λx. …)` embeds.
pub(crate) fn pointwise_relation(fun_ty: &Expr, alpha: &Expr, op: &Expr) -> Expr {
    const FF: u64 = 0xf0d_0001; // f : α→β
    const FG: u64 = 0xf0d_0002; // g : α→β
    const FX: u64 = 0xf0d_0003; // x : α
    let f = Expr::fvar(FVarId::new(FF));
    let g = Expr::fvar(FVarId::new(FG));
    let forall = {
        let x = Expr::fvar(FVarId::new(FX));
        let fx = Expr::app(f.clone(), x.clone());
        let gx = Expr::app(g.clone(), x);
        let body = Expr::apps(op.clone(), [fx, gx]);
        Expr::pi(
            BinderInfo::Default,
            alpha.clone(),
            body.abstract_fvar(FVarId::new(FX)),
        )
    };
    curry2(fun_ty, fun_ty, forall, FF, FG)
}

/// `λ(f:α→β)(g:α→β). conj (∀x. le (f x) (g x)) (Not (∀x. le (g x) (f x)))` — the
/// **strict** order on a function instance (`less_fun_def`:
/// `(f < g) ≡ (f ≤ g) ∧ ¬ (g ≤ f)`, where `≤` is itself the pointwise universal
/// order). `le` is the element `≤@'b`; `conj`/`Not` are the SAME
/// `isabelle.def.HOL.{conj,Not}` def-consts the RHS embeds to, so the equation is
/// reflexive.
pub(crate) fn pointwise_strict_less(fun_ty: &Expr, alpha: &Expr, le: &Expr) -> Expr {
    const FF: u64 = 0xf10_0001; // f : α→β
    const FG: u64 = 0xf10_0002; // g : α→β
    const FX: u64 = 0xf10_0003; // x : α
    let f = Expr::fvar(FVarId::new(FF));
    let g = Expr::fvar(FVarId::new(FG));
    // `∀x. le (p x) (q x)` for the two orderings `(f,g)` and `(g,f)`.
    let forall_le = |p: &Expr, q: &Expr| {
        let x = Expr::fvar(FVarId::new(FX));
        let px = Expr::app(p.clone(), x.clone());
        let qx = Expr::app(q.clone(), x);
        let body = Expr::apps(le.clone(), [px, qx]);
        Expr::pi(
            BinderInfo::Default,
            alpha.clone(),
            body.abstract_fvar(FVarId::new(FX)),
        )
    };
    let le_fg = forall_le(&f, &g);
    let not_le_gf = Expr::app(not_def_const(), forall_le(&g, &f));
    let body = Expr::apps(conj_def_const(), [le_fg, not_le_gf]);
    curry2(fun_ty, fun_ty, body, FF, FG)
}

/// The registered `HOL.Not` definition const (`isabelle.def.HOL.Not`), as a clean
/// `Expr` — mirrors [`conj_def_const`] so a `¬` an instance encoding builds shares
/// the same defeq-unfolding head as every other `HOL.Not` occurrence.
pub(crate) fn not_def_const() -> Expr {
    Expr::const_str(connective_def_name("HOL.Not").unwrap_or("isabelle.def.HOL.Not"))
}

/// `λ(A:(α→β)→Prop)(x:α). op (image (λ(f:α→β). f x) A)` — the complete-lattice
/// `Inf`/`Sup` at the **function instance**, mirroring HOL's
/// `Inf_fun_def`/`Sup_fun_def` exactly. `op` is the element-instance `Inf`/`Sup`
/// at `'b` (embedded through the shared dispatch, so it coincides with the RHS's
/// inner occurrence); the `image` is the faithful [`image_encoding`] over the
/// function type `α→β` into `β` — the SAME encoding the RHS's `Set.image` embeds
/// to — so both sides of the `…_def` equation coincide and it is reflexive.
pub(crate) fn lattice_fun_encoding(alpha: &Expr, beta: &Expr, op: &Expr) -> Expr {
    const FS: u64 = 0xf11_0001; // A : (α→β) → Prop  (the set of functions)
    const FX: u64 = 0xf11_0002; // x : α
    const FF: u64 = 0xf11_0003; // f : α→β  (the probe binder of `λf. f x`)
    let fun_ty = Expr::arrow(alpha.clone(), beta.clone()); // 'a ⇒ 'b
    let set_ty = Expr::arrow(fun_ty.clone(), Expr::prop()); // ('a⇒'b) set
    let a = Expr::fvar(FVarId::new(FS));
    let x = Expr::fvar(FVarId::new(FX));
    // probe: λ(f:α→β). f x  : (α→β) → β
    let probe = {
        let f = Expr::fvar(FVarId::new(FF));
        let fx = Expr::app(f, x.clone());
        Expr::lam(
            BinderInfo::Default,
            fun_ty.clone(),
            fx.abstract_fvar(FVarId::new(FF)),
        )
    };
    // image (λf. f x) A : β set = β→Prop  (image over `α→β`, into `β`).
    let img = Expr::apps(image_encoding(&fun_ty, beta), [probe, a.clone()]);
    // op (image …) : β
    let body = Expr::app(op.clone(), img);
    // λ(x:α). body
    let xfun = Expr::lam(
        BinderInfo::Default,
        alpha.clone(),
        body.abstract_fvar(FVarId::new(FX)),
    );
    // λ(A:('a⇒'b) set). xfun
    Expr::lam(
        BinderInfo::Default,
        set_ty,
        xfun.abstract_fvar(FVarId::new(FS)),
    )
}
