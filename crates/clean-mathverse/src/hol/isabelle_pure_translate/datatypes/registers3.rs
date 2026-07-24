// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **G4 — the `_inst.` method@constructor registration shape** (the design gate
//! table row G4 of `designs/2026-07-07-isabelle-100pct-industrial-import.md`).
//!
//! Isabelle's `instantiation K :: (…) c` target compiles each method definition
//! to TWO primitives the corpus exports:
//!
//! 1. the **overloading LINK** axiom `<c>_class.<m> @ τ ≡ <impl> @ τ`, where
//!    `<impl>` is the freshly-minted instance-implementation constant
//!    `<Thy>.<m>_<K>_inst.<m>_<K>` and `τ` is the method's type at the instance
//!    (`Enum.enum_class.enum @ (α⇒β) list ≡ Enum.enum_fun_inst.enum_fun`);
//! 2. the user-level **body equation** `<c>_class.<m> @ τ = <body>`
//!    (`Enum.enum_fun_def : enum = map … (n_lists (size enum) enum)`).
//!
//! Both fell BETWEEN the two existing registries: the ground instance-op
//! registry demands a fully-GROUND `τ` ([`is_ground_type`]), while the poly-inst
//! registry demands a plain (non-method) LHS head. This module supplies the
//! third shape:
//!
//! - [`register_inst_link`] records `<impl> → <method>` **alias** entries from
//!   the link axioms (the registry-driven generalisation of the hand lists
//!   [`fun_impl_const_class_op`] / [`bool_impl_const_class_op`] /
//!   [`ground_impl_const_class_op`]): a use-site re-embeds the impl as the
//!   method at the occurrence type, so the link equation becomes genuinely
//!   reflexive — whatever the method's embedding at that instance is (opaque
//!   `const:` param, ground/dict def-const, or the G4 def-const below).
//! - [`register_method_inst_def`] registers the body equation as a clean
//!   polymorphic `Definition` keyed **(method, instance shape)**
//!   ([`method_inst_registry_key`]) with the instantiation tvars as leading
//!   binders — sharing [`build_poly_inst_definition`]'s exact embedding /
//!   partition / abstraction discipline (G3 strict typed keys included). A
//!   use-site `method @ τ'` whose type unifies with the registered instance
//!   type unfolds to the def-const ([`Ctx::find_method_inst`]).
//!
//! Every registration is kernel-re-checked (`add_decl`) and every use-site
//! result is kernel-re-checked against the consumer's expectation, so a wrong
//! registration can only reject — never falsely verify.

use clean_kernel::Declaration;

use super::super::super::isabelle_pure::{IsaProvenTheorem, IsaTerm, IsaType};
use super::super::*;

/// If `thm` is an **instance overloading LINK** — a definitional axiom whose
/// conclusion is `Pure.eq (Const method τ) (Const impl τ)` with `method` an
/// overloaded `_class.` operation, `impl` a bare `…_inst.…` instance
/// implementation constant, and the two carried types identical — return
/// `(method, impl, τ)`. This is the exact statement Isabelle's `instantiation`
/// target records for every instance method (`HOL.equal_itself_inst.
/// equal_itself : equal_class.equal ≡ equal_itself_inst.equal_itself`, …); its
/// recorded proof is the bare `…_inst.…_def` axiom leaf, so the
/// [`proof_contains_def_axiom`] guard scopes detection to genuine links.
pub(crate) fn inst_link_axiom(thm: &IsaProvenTheorem) -> Option<(&str, &str, &IsaType)> {
    if !proof_contains_def_axiom(&thm.proof) {
        return None;
    }
    let concl = strip_leading_imps(&thm.prop);
    let (lhs, rhs) = pure_eq_parts(concl)?;
    let IsaTerm::Const { n: method, t: mt } = lhs else {
        return None;
    };
    let IsaTerm::Const { n: impl_c, t: it } = rhs else {
        return None;
    };
    if !is_overloaded_method_const(method) || is_overloaded_method_const(impl_c) {
        return None;
    }
    // The Isabelle instance-implementation naming convention — the mangled
    // `<Thy>.<m>_<K>_inst.<m>_<K>` constants minted by the `instantiation`
    // target. Ordinary constants never carry the `_inst.` infix.
    if !impl_c.contains("_inst.") {
        return None;
    }
    // Both sides must be the SAME instance type (the overloading link relates
    // the method to the impl at exactly the declared instance).
    if mt != it {
        return None;
    }
    Some((method, impl_c, mt))
}

/// Register the **`impl → method` ALIAS** an instance overloading LINK records
/// (see [`inst_link_axiom`]), as a [`PolyInstRegistry`] entry keyed by the impl
/// constant's name with [`PolyInstInfo::alias_of`]`= Some(method)`. No kernel
/// `Definition` is minted — a use-site simply re-embeds the impl as the method
/// at the occurrence type through the full `Const` dispatch, so the two denote
/// one head in every escalation mode and the link axiom verifies by a
/// kernel-re-checked `Eq.refl`.
///
/// Declines (keeping the historical path byte-identical) when the impl:
/// - is already registered (idempotent snapshot resume),
/// - has a HAND mapping ([`fun_impl_const_class_op`] /
///   [`bool_impl_const_class_op`] / [`ground_impl_const_class_op`]) or any
///   canonical encoding ([`has_canonical_encoding`] or a non-opaque probe —
///   the G2 shadow-guard rule),
/// - is the dictionary implementation of a registered method (the r9 dict lane
///   owns it; aliasing it would make `embed_method_use`'s impl re-embedding
///   recurse through the method head).
#[must_use]
pub(crate) fn register_inst_link(
    thm: &IsaProvenTheorem,
    registry: &PolyInstRegistry,
    methods: &MethodRegistry,
) -> Option<(String, PolyInstInfo)> {
    let (method, impl_c, ty) = inst_link_axiom(thm)?;
    if registry.contains_key(impl_c) {
        return None;
    }
    if fun_impl_const_class_op(impl_c).is_some()
        || bool_impl_const_class_op(impl_c).is_some()
        || ground_impl_const_class_op(impl_c).is_some()
        || has_canonical_encoding(impl_c)
    {
        return None;
    }
    if methods.values().any(|m| m.impl_const.0 == impl_c) {
        return None;
    }
    // Shadow probe (G2 rule): only an impl that embeds to exactly one opaque
    // `const:` param may be re-routed — anything else already has a canonical
    // arm somewhere, and aliasing would split its occurrences across two heads.
    if !probe_embeds_opaque(impl_c, ty) {
        return None;
    }
    Some((
        impl_c.to_string(),
        PolyInstInfo {
            // Marker only — an alias entry never declares a kernel constant.
            def_name: format!("isabelle.instlink.{impl_c}"),
            fn_ty: ty.clone(),
            obj_tvars: Vec::new(),
            extra_type_consts: Vec::new(),
            ops: Vec::new(),
            arg_vars: Vec::new(),
            conjuncts: Vec::new(),
            alias_of: Some(method.to_string()),
        },
    ))
}

/// If `thm` is a **method-at-constructor instance definition** — a definitional
/// axiom (named `…_def`/`…_def_raw`, or whose recorded proof bottoms out in one)
/// whose LHS is an overloaded `_class.` method applied to schematic argument
/// variables at a NON-ground instance type carrying only schematic tvars —
/// return `(method, method-type, object-tvars, schematic-arg-names, rhs)`.
/// The exact complement of [`poly_inst_def_axiom`]'s overloaded-method decline
/// (and of [`instance_op_def_axiom`]'s ground-type demand): this is the G4 gap.
#[allow(clippy::type_complexity)]
pub(crate) fn method_inst_def_axiom(
    thm: &IsaProvenTheorem,
) -> Option<(
    &str,
    &IsaType,
    Vec<(String, i64)>,
    Vec<(String, i64)>,
    &IsaTerm,
)> {
    let name_is_def = thm.name.ends_with("_def") || thm.name.ends_with("_def_raw");
    if !name_is_def && !proof_contains_def_axiom(&thm.proof) {
        return None;
    }
    let concl = strip_leading_imps(&thm.prop);
    let (lhs, rhs) = pure_eq_parts(concl)?;
    let (head, args) = term_app_spine(lhs);
    let IsaTerm::Const { n, t } = head else {
        return None;
    };
    // The G4 shape: an overloaded METHOD head (poly-inst declines these) at a
    // NON-ground type (the ground instance-op registry owns the ground ones).
    if !is_overloaded_method_const(n) || is_ground_type(t) {
        return None;
    }
    // Every distinct schematic tvar in first-occurrence order; a fixed `TFree`
    // declines (same rule as every other registry). Non-ground + no `TFree`
    // implies at least one tvar, but keep the emptiness check explicit.
    let obj_tvars = method_obj_tvars(t)?;
    if obj_tvars.is_empty() {
        return None;
    }
    // Each LHS argument must be a schematic `Var` (the η-expanded formal).
    let mut arg_vars: Vec<(String, i64)> = Vec::new();
    for a in &args {
        let IsaTerm::Var { n: vn, i: vi, .. } = a else {
            return None;
        };
        arg_vars.push((vn.clone(), *vi));
    }
    // A bare-`Const` RHS is an overloading LINK (`method ≡ impl`) or a pure
    // renaming — NOT a body definition. The alias lane ([`register_inst_link`])
    // owns links; registering one here would mint the degenerate
    // `instk.<m>@<K> := λα op. op` whose sole op is the impl const, and the
    // impl's alias re-embeds the method at the same type — an unfold CYCLE
    // (alias → method → instk → op → alias → …, the mini-slice stack
    // overflow). Decline: there is nothing to unfold in a link.
    if matches!(rhs, IsaTerm::Const { .. }) {
        return None;
    }
    Some((n, t, obj_tvars, arg_vars, rhs))
}

/// Register the **method-at-constructor instance definition** a body equation
/// defines (see [`method_inst_def_axiom`]), as a clean polymorphic `Definition`
/// `isabelle.instk.<method>@<shape> := λ(α₁…αₖ)(ops…)(args…). <embed body>`
/// under the composite registry key [`method_inst_registry_key`] — the G4
/// third registration shape. Shares [`build_poly_inst_definition`] with the
/// poly-inst lane (identical embedding / close-or-skip partition / G3 strict
/// typed op keys / binder ordering), so a wrong body can only fail to close or
/// kernel-reject — never mis-register.
///
/// `anchors` is the set of `(method, instance shape-key)` pairs recorded by
/// the batch's overloading LINK axioms ([`register_inst_link`]): a body
/// equation registers ONLY at an instance Isabelle itself declared (this is
/// what keeps the lane away from generic method equations and arbitrary
/// method-headed rewrites — registration is anchored in the instantiation
/// target's own primitive, not in a name heuristic).
#[must_use]
#[allow(clippy::implicit_hasher)]
pub fn register_method_inst_def(
    thm: &IsaProvenTheorem,
    registry: &PolyInstRegistry,
    methods: &MethodRegistry,
    instance_ops: &InstanceOpRegistry,
    list_fns: &ListFnRegistry,
    alt_heads: &std::collections::BTreeSet<String>,
    anchors: &std::collections::BTreeSet<(String, String)>,
) -> Option<(String, Declaration, PolyInstInfo)> {
    let (method, fn_ty, obj_tvars, arg_vars, rhs) = method_inst_def_axiom(thm)?;
    let shape = isa_shape_key(fn_ty);
    // Anchor: only instances the corpus's own LINK axioms declared register.
    if !anchors.contains(&(method.to_string(), shape.clone())) {
        return None;
    }
    let key = method_inst_registry_key(method, &shape);
    if registry.contains_key(&key) {
        return None;
    }
    // The G2 widening guards, scoped exactly as in the poly-inst lane (only
    // method-free bodies are subject to the alt-def / dict-impl declines; a
    // method-mentioning body is the historical registration class there — and
    // the overwhelmingly common shape here, since an instance body usually
    // recurses through the element instances of its own method).
    if !tm_mentions_overloaded_method(rhs) {
        if alt_heads.contains(method) {
            return None;
        }
        if methods.values().any(|m| m.impl_const.0 == method) {
            return None;
        }
    }
    // Shadow probe (G2 rule) AT THE INSTANCE TYPE: a method whose occurrence at
    // this instance already has a canonical hand encoding — the pointwise
    // function-instance lattice/order lambdas, `equal@itself/sum/prod`,
    // `inf/sup@nat`, the set-lattice arms — embeds non-opaquely and must NOT be
    // shadowed by a registration (its `_def` already verifies through that
    // arm). Other instances of the same method probe opaque and register.
    if !probe_embeds_opaque(method, fn_ty) {
        return None;
    }
    let def_name = method_inst_def_name(method, &shape);
    let (decl, info) = build_poly_inst_definition(
        method,
        fn_ty,
        obj_tvars,
        arg_vars,
        rhs,
        instance_ops,
        list_fns,
        def_name,
    )?;
    // CYCLE GUARD: a body whose op binders include (a) an `_inst.` impl
    // ALIASED back to this same method, or (b) this method itself at THIS SAME
    // instance shape, would unfold circularly at every use-site (op supply →
    // alias/method → this def-const → op supply → …). Genuine recursion in an
    // instance body goes through a recursor, never through the raw
    // impl/method head, so declining is safe — the `_def` node keeps its
    // recorded-proof path.
    for (op_name, op_ty) in &info.ops {
        if registry
            .get(op_name)
            .is_some_and(|e| e.alias_of.as_deref() == Some(method))
        {
            return None;
        }
        if op_name == method && isa_shape_key(op_ty) == shape {
            return None;
        }
    }
    Some((key, decl, info))
}
