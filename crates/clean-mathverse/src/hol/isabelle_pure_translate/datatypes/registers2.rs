// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Plain-polymorphic list-function definition-axiom detection and registration:
//! `list_fn_def_axiom`, `ty_mentions`, `tm_mentions_type`, `tm_mentions_const`,
//! `register_list_fn_def`. Moved verbatim from the original single-file
//! `datatypes` module; behaviour is byte-identical.

use std::collections::BTreeMap;

use clean_kernel::expr::FVarId;
use clean_kernel::level::Level;
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Declaration, Environment, Expr};

use super::super::super::isabelle_pure::{IsaProof, IsaProvenTheorem, IsaTerm, IsaType};
use super::super::*;

/// If `thm` is a **plain polymorphic list-function definition** — a `Pure.eq`
/// definitional axiom whose LHS is a bare function constant `c` (zero args)
/// parameterised by **one or more** object type variables `'a`, `'b`, …, and
/// whose body (or function type) references the `'a list` datatype — return
/// `(fn-name, fn-type, object-tvars, rhs-body)`.
///
/// These are exported as the recursive list-function `…_def` axioms
/// (`List.append_def`, `List.rev_def`, `List.list.map_def`, `List.foldr_def`,
/// `List.foldl_def`, `List.zip_def`, `List.those_def`, …) whose statement, after
/// stripping the leading `OFCLASS('a, type_class) ⟹` sort premises (one per type
/// variable), is `c = (λ…. List.list.rec_list / case_list … )`. Their recorded
/// proof is a `Pure.transitive` unfolding chain bottoming out in the `…_def`
/// PAxm leaf — so detection is by **statement shape** (like
/// [`instance_op_def_axiom`]), guarded by `proof_contains_def_axiom` so the
/// shortcut never steals an ordinary list theorem with a real derivation. The
/// `'a list` mention keeps the lever scoped to genuine element-polymorphic list
/// functions; the type-variable count is now **unbounded** (was exactly one),
/// unlocking the two-variable `map`/`foldr`/`foldl`/`zip`/`those`.
pub(crate) fn list_fn_def_axiom(
    thm: &IsaProvenTheorem,
) -> Option<(&str, &IsaType, Vec<(String, i64)>, &IsaTerm)> {
    let concl = strip_leading_imps(&thm.prop);
    let (lhs, rhs) = pure_eq_parts(concl)?;
    // The LHS must be the *bare* function constant (zero args).
    let IsaTerm::Const { n, t } = lhs else {
        return None;
    };
    // The BNF LFP-package datatype **size** functions
    // (`Basic_BNF_LFPs.sum.size_sum`, `Basic_BNF_LFPs.prod.size_prod`) are exactly
    // this plain-polymorphic structural-recursion shape — a closed
    // `case_sum`/`case_prod` fold into `nat` over the element sizes
    // (`λf fa. case_sum (λx. f x + Suc 0) (λx. fa x + Suc 0)`) — but two of this
    // function's gates decline them: (a) their recorded proof reaches the
    // `…_def_raw` leaf INDIRECTLY through a `thm` node (not an inline `PAxm`), so
    // `proof_contains_def_axiom` is false, and (b) `size_sum`'s body names the sum
    // type as `Sum_Type.sum`, which the scoping list does not enumerate. They are
    // admitted by their EXACT constant name (specific enough that no other theorem
    // can match), bypassing both gates. The close-or-skip guard in
    // [`register_list_fn_def`] (any leftover term param → skip) and the kernel
    // `add_decl` re-check keep the registration faithful: if a constituent op
    // (`Groups.plus_class.plus@nat`) is unregistered so the body cannot close, the
    // registration is simply skipped, never mis-registered.
    let is_size_ctor = matches!(
        n.as_str(),
        "Basic_BNF_LFPs.sum.size_sum" | "Basic_BNF_LFPs.prod.size_prod"
    );
    if !is_size_ctor && !proof_contains_def_axiom(&thm.proof) {
        return None;
    }
    // One or more object type variables `'a`, `'b`, … parameterise the function
    // (in canonical first-occurrence order). No fixed (`TFree`) type may appear.
    let tvs = all_tvars(t)?;
    // Scope to **clean-mappable** datatype/combinator functions: the function type
    // or its body must mention one of the datatypes whose recursor/case the
    // translator maps to a clean prelude eliminator (`List.rec`/`Option.rec`/
    // `Nat.rec`/`Num.rec`/`Sum.rec`/`Prod.rec`) **or** one of the function
    // combinators it δ-unfolds (`Fun.comp`/`Fun.id`). This keeps the lever from
    // perturbing arbitrary unrelated polymorphic defs (which would not close anyway)
    // while admitting the genuinely-closing non-list functions whose bodies are pure
    // recursor/combinator folds — e.g. `Nat.compow` (`funpow`, `f^^n ≡ rec_nat id
    // (λ_ g. f ∘ g) n`), which threads only `rec_nat`/`Fun.comp`/`Fun.id`. The
    // close-or-skip guard (any leftover term param → reject) + the kernel `add_decl`
    // re-check keep every registration faithful regardless of the broadened scope.
    if !is_size_ctor {
        let mentions = |name: &str| ty_mentions(t, name) || tm_mentions_type(rhs, name);
        let scoped = mentions("List.list")
            || mentions("Option.option")
            || mentions("Sum.sum")
            || mentions("Product_Type.prod")
            || mentions("Num.num")
            || tm_mentions_const(rhs, "Nat.old.nat.rec_nat")
            || tm_mentions_const(rhs, "Fun.comp")
            || tm_mentions_const(rhs, "Fun.id");
        if !scoped {
            return None;
        }
    }
    Some((n, t, tvs, rhs))
}

/// Whether a HOL type syntactically mentions a type constructor named `name`.
pub(crate) fn ty_mentions(ty: &IsaType, name: &str) -> bool {
    match ty {
        IsaType::Type { n, a } => n == name || a.iter().any(|t| ty_mentions(t, name)),
        _ => false,
    }
}

/// Whether a HOL term syntactically mentions a type constructor named `name`
/// anywhere in the types it carries (constant types, abstraction binder types).
pub(crate) fn tm_mentions_type(tm: &IsaTerm, name: &str) -> bool {
    match tm {
        IsaTerm::Const { t, .. } => ty_mentions(t, name),
        IsaTerm::App { f, a } => tm_mentions_type(f, name) || tm_mentions_type(a, name),
        IsaTerm::Abs { t, b, .. } => ty_mentions(t, name) || tm_mentions_type(b, name),
        _ => false,
    }
}

/// Whether a HOL term syntactically mentions a `Const` named `name` anywhere.
/// Used to scope the list-function registry to bodies that are pure folds over a
/// clean-mapped recursor/combinator (`rec_nat`, `Fun.comp`, `Fun.id`) even when the
/// function's type names no list/option datatype (e.g. `Nat.compow`/`funpow`).
pub(crate) fn tm_mentions_const(tm: &IsaTerm, name: &str) -> bool {
    match tm {
        IsaTerm::Const { n, .. } => n == name,
        IsaTerm::App { f, a } => tm_mentions_const(f, name) || tm_mentions_const(a, name),
        IsaTerm::Abs { b, .. } => tm_mentions_const(b, name),
        _ => false,
    }
}

/// Register the **plain polymorphic list function** a `List.*_def` axiom defines,
/// as a clean polymorphic `Definition`
/// `isabelle.listfn.<c> := λ(α₁:Type)…(αₙ:Type). <embed RHS>`.
///
/// The body is embedded in a fresh [`Ctx`] with `instance_unfold` active (so
/// nested already-registered list functions / nat-base constructors resolve to
/// their def-consts), discovering the object type variables `'a`, `'b`, … as the
/// `Type` parameters `α₁, …, αₙ` — abstracted as the leading binders, **in the
/// order [`Ctx::embed_type`] first discovers them in the body**. The definition
/// is closed *modulo* those `αᵢ`: any *term* param (an unmapped non-type constant
/// survived) or a type-param count that disagrees with the function's own type
/// variables means the body did not close polymorphically, so registration is
/// skipped — the `…_def` stays unmapped exactly as before, never mis-registered.
///
/// Returns the registry key (the function-constant name), the clean `Definition`,
/// and its [`ListFnInfo`], or `None`. The driver registers these in **serial (=
/// dependency) order** so a base function (`append`) is registered before a
/// recursive function (`rev`, which uses `append`) that mentions it. Generalized
/// from one type variable to N — unlocking `map`/`foldr`/`foldl`/`zip`/`those`.
///
/// The already-built `instance_ops` and `methods` registries are threaded in so a
/// list function whose body uses a **ground-type arithmetic operation**
/// (`List.count_list`'s body counts in `nat` via `Groups.plus_class.plus@nat` /
/// `zero@nat` / `one@nat`) or an overloaded method closes — those op occurrences
/// re-embed to their already-registered instance/method def-consts instead of
/// surviving as a free `const:` param that would block closure. The driver
/// registers instance ops *before* list functions (serial order also puts a nat
/// `…_def` before a list `…_def` that uses it), so the registry is fully populated
/// here. Faithfulness is unchanged: the body still embeds to a closed term that the
/// kernel re-checks via `add_decl`, and a wrong embedding is rejected.
#[must_use]
pub(crate) fn register_list_fn_def(
    thm: &IsaProvenTheorem,
    registry: &ListFnRegistry,
    instance_ops: &InstanceOpRegistry,
    methods: &MethodRegistry,
) -> Option<(String, Declaration, ListFnInfo)> {
    let (fn_name, fn_ty, tvs, rhs) = list_fn_def_axiom(thm)?;
    if registry.contains_key(fn_name) {
        return None;
    }
    // Embed the RHS with instance-unfold AND the current list-fn registry, so a
    // recursive function whose body mentions an earlier-registered list function
    // (and the `rec_list`/`case_list`/constructor mappings) re-embeds those closed.
    // The instance-op and method registries are threaded in too, so a list function
    // whose body uses ground nat/int arithmetic (or an overloaded method) closes.
    let mut ctx = Ctx {
        instance_op_registry: instance_ops.clone(),
        instance_unfold: true,
        method_registry: methods.clone(),
        method_unfold: true,
        list_fn_registry: registry.clone(),
        ..Default::default()
    };
    let mut binders: Vec<Binder> = Vec::new();
    let value_core = ctx.embed_term(rhs, &mut binders).ok()?;
    // The body must close to exactly the object type vars `α₁…αₙ` and NOTHING
    // else: no leftover term param (unmapped constant) and exactly one type param
    // per object type variable. Anything else → not a faithful closed
    // polymorphic body.
    if !ctx.term_params.is_empty() || ctx.type_params.len() != tvs.len() {
        return None;
    }
    // Re-embed the function's HOL type in the SAME ctx so the SAME `αᵢ` fvars are
    // used; the leading binders are then abstracted identically over value+type.
    // (Re-embedding the type cannot introduce a NEW type variable: `fn_ty`'s
    // variables are exactly `tvs` and the body already discovered `tvs.len()` of
    // them, so `type_params` is unchanged — but re-checking keeps it robust.)
    let fn_clean_ty = ctx.embed_type(fn_ty).ok()?;
    if ctx.type_params.len() != tvs.len() {
        return None;
    }
    // The canonical binder order is the type-param *discovery* order (which is the
    // same first-occurrence walk `all_tvars` used on the function type). Record the
    // object type variables in THAT order so a use-site solves and applies them in
    // lockstep with the abstraction.
    let mut obj_tvars: Vec<(String, i64)> = Vec::with_capacity(tvs.len());
    for (key, _) in &ctx.type_params {
        // `embed_type`'s `TVar` arm keys a schematic var as `"{n}.{i}"`; recover
        // the matching `(name, index)` from the function's own type-variable set.
        let tv = tvs
            .iter()
            .find(|(n, i)| *key == format!("{n}.{i}"))?
            .clone();
        obj_tvars.push(tv);
    }
    // Abstract every `αᵢ` as a leading `λ(αᵢ:Type).` / `Π(αᵢ:Type).` binder, in
    // forward (discovery) order — iterate the params in reverse so the FIRST
    // discovered binder ends up OUTERMOST (matching `obj_tvars`/use-site order).
    let mut value = value_core;
    let mut def_type = fn_clean_ty;
    for (_key, p) in ctx.type_params.iter().rev() {
        value = Expr::lam(
            BinderInfo::Default,
            Expr::type_(),
            value.abstract_fvar(p.fvar),
        );
        def_type = Expr::pi(
            BinderInfo::Default,
            Expr::type_(),
            def_type.abstract_fvar(p.fvar),
        );
    }
    let def_name = list_fn_def_name(fn_name);
    let decl = Declaration::Definition {
        name: Name::from_string(&def_name),
        level_params: Vec::new(),
        type_: def_type,
        value,
        is_reducible: true,
    };
    Some((
        fn_name.to_string(),
        decl,
        ListFnInfo {
            def_name,
            fn_ty: fn_ty.clone(),
            // The object type variables (from `list_fn_def_axiom`), recorded in the
            // canonical abstraction order so a use-site can solve `'aᵢ := Tᵢ` by
            // matching `fn_ty` against the instantiated use type and supply the
            // solutions as leading type arguments in this exact order.
            obj_tvars,
        },
    ))
}
