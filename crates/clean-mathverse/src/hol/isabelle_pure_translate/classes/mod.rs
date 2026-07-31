// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Type-class & method machinery: `ClassRegistry`/`MethodRegistry`, class-definition
//! building, the dictionary-equation scanner, polymorphic-instance registration and
//! the type-variable matching helpers.
//!
//! Part of the [`super`] Pure proof-term → clean kernel translator; split
//! out of the original single-file module purely for readability — the code is
//! moved verbatim, the behaviour is byte-identical.

use std::collections::BTreeMap;

use clean_kernel::level::Level;
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Declaration, Environment, Expr};

use super::super::isabelle_pure::{IsaProof, IsaProvenTheorem, IsaTerm, IsaType};
use super::*;
mod dicts;
mod projection;

pub(crate) use dicts::*;
pub(crate) use projection::{and_left, and_right, conj_def, subst_isa_vars};

/// A registered **structured type class** — a class whose `…c_class_def`
/// definitional axiom carries genuine axioms (e.g. `semigroup_add`'s
/// associativity), as opposed to a *base* sort whose body is the trivial
/// `HOL.type_class`. Built from the `…c_class_def` axiom by
/// [`build_class_def`] and registered as a clean polymorphic `Definition`
/// `isabelle.def.<c_class> := λ(α:Type)(op₁ … opₙ). ⟨embed body⟩`. Its presence
/// in the [`ClassRegistry`] is what turns an `OFCLASS('a, c_class)` premise from
/// the vacuous `True` into the **real membership proposition** `c_class α ops`,
/// keeping the class axioms as honest hypotheses (the type-class-as-hypothesis
/// model — see the module-level header).
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct ClassDefInfo {
    /// Kernel declaration name of the registered clean `Definition`
    /// (`isabelle.def.<c_class>`).
    pub(crate) def_name: String,
    /// The class operations, in the fixed order the definition abstracts them —
    /// each an `(operation-constant-name, its HOL type)`. An `OFCLASS` premise /
    /// membership use re-embeds these (in the consumer's own context) and
    /// applies the def-const to `α` (then any [`Self::extra_type_consts`]) then to
    /// each op, so every occurrence of the class predicate shares one head and one
    /// argument order.
    pub(crate) ops: Vec<(String, IsaType)>,
    /// Names of the **extra fixed ground type constructors** the body references
    /// beyond the object type `α` (e.g. `Nat.nat` for `euclidean_size : 'a ⇒
    /// nat`, `Set.set` for `Inf : 'a set ⇒ 'a`). `embed_type` abstracts each such
    /// type as its own leading `Π(_:Type)` binder of the registered definition, so
    /// a consumer's membership use must supply them — in this order, immediately
    /// after `α` and before the operations — re-embedding each as the same global
    /// `type_param(name)` so the def-const application is fully saturated. (For a
    /// single-`α` class this is empty and membership is `def α op₁ … opₙ` as
    /// before.)
    pub(crate) extra_type_consts: Vec<String>,
    /// The registered `Definition`'s **closed value** `λ(α)(extra…)(op₁…opₙ). B`
    /// (identical to the `Declaration::Definition` `value`). Retained so a
    /// membership-**introduction** consumer (`c_class.intro_of_class`) can build
    /// a faithful witness of `c_class α ops` by β-reducing this value at the
    /// use-site arguments to the concrete class body `B` (a
    /// `Pure.conjunction`/`type_class` tree of the very premises the intro
    /// discharges) and assembling `And.intro`/`True.intro` from those premises —
    /// see [`Ctx::prove_class_membership_intro`]. Pure data (no free FVars — the
    /// binders are all bound), so it serializes into the snapshot alongside the
    /// rest of the entry.
    pub(crate) def_value: Expr,
}

/// Registry of structured type classes registered so far in the closure replay
/// (`c_class` constant name → its [`ClassDefInfo`]). Threaded read-only through
/// [`translate_theorem`] so `embed_term` can model `OFCLASS('a, c_class)` as the
/// real membership proposition for any class already registered.
pub type ClassRegistry = BTreeMap<String, ClassDefInfo>;

/// A registered **overloaded class method** — the operational analogue of
/// [`ClassDefInfo`]. Every Isabelle type-class operation `c_class.method`
/// (`numeral`, `of_nat`, `power`, `dvd`, `sum`, …) carries a `…_dict` axiom whose
/// statement is the *dictionary unfolding*
/// `c_class.method ≡ c.method op₁ … opₙ`, where `c.method` is the dictionary form
/// of the operation (the bare overloaded constant taking the class operations
/// explicitly) and `op₁ … opₙ` are the class's operations (themselves overloaded
/// methods such as `one`, `plus`, `less_eq`). The `…_dict` axiom is NOT exported
/// as a standalone node — it only appears as a bare `PAxm` leaf inside consumer
/// proofs, fed (via `Pure.symmetric`) into a congruence chain that rewrites every
/// `c_class.method` occurrence to its dictionary form. So the dictionary equation
/// is recovered by scanning proofs for the `symmetric % LHS % RHS %% …_dict`
/// spine (see [`scan_method_dicts`]).
///
/// Registering `c_class.method` as the clean polymorphic `Definition`
/// `isabelle.method.<c_class.method> := λ(α:Type)(impl)(op₁ … opₙ). impl op₁ … opₙ`
/// (where `impl` is the dictionary-form recursor `c.method`) makes the `…_dict`
/// equation *genuinely reflexive*: under the embedding `c_class.method` δ-unfolds
/// to `impl op₁ … opₙ`, which is exactly the embedded RHS. The dictionary axiom
/// is then dischargeable by `Eq.refl`, kernel-accepted **iff** the two sides are
/// definitionally equal — never a tautology (the method side is the operational
/// twin of the predicate side's [`ClassDefInfo`] crack).
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct MethodDefInfo {
    /// Kernel declaration name of the registered clean `Definition`
    /// (`isabelle.method.<c_class.method>`).
    pub(crate) def_name: String,
    /// The overloaded method's own HOL type as seen at registration (e.g.
    /// `num ⇒ 'a`). Unified against a use-site's instantiated method type to solve
    /// the object type variables (see [`Self::obj_tvars`]), which are then
    /// substituted into [`Self::impl_const`]/[`Self::ops`] so they re-embed at the
    /// use-site's concrete instantiation.
    pub(crate) method_ty: IsaType,
    /// The object type variables of the method (each the `(name, index)` of a
    /// `TVar` of [`Self::method_ty`], in first-occurrence order), recorded at
    /// registration. The clean `Definition` abstracts them as the leading
    /// `(αᵢ : Type)` binders in this order. Usually the single class variable
    /// `'a`; the big-operator methods (`sum : ('b⇒'a)⇒'b set⇒'a`, `insort_key`,
    /// `horner_sum`, …) also carry the element/key variable, and the
    /// function-package ground methods (`or_num : num⇒num⇒num`) carry none.
    pub(crate) obj_tvars: Vec<(String, i64)>,
    /// The dictionary-form implementation constant (`c.method`, the RHS head of
    /// the `…_dict` equation) and its HOL type (referencing [`Self::obj_tvar`]).
    /// A consumer applying the method def-const supplies this as the first
    /// non-type argument.
    pub(crate) impl_const: (String, IsaType),
    /// The class operations the dictionary form is applied to (`op₁ … opₙ`), in
    /// order — each `(operation-constant-name, its HOL type referencing
    /// `obj_tvar`)`. A consumer applies the def-const to `α`, then `impl`, then
    /// each of these (re-embedded in its own context as the same global
    /// `const:<n>` param at the use-site instantiation), so every occurrence
    /// shares one head and argument order.
    pub(crate) ops: Vec<(String, IsaType)>,
    /// Names of the **extra fixed ground type constructors** the method body /
    /// type references beyond the object type `α` (e.g. `Num.num` for
    /// `numeral : num ⇒ 'a`, `Nat.nat` for `of_nat : nat ⇒ 'a`). `embed_type`
    /// abstracts each such base type as its own leading `Π(_:Type)` binder of the
    /// registered definition (otherwise the definition's value/type would contain
    /// a free `type_param` FVar → kernel `ContainsFreeVar`). A consumer's method
    /// use supplies them — in this order, immediately after `α` and before
    /// `impl`/operations — re-embedding each as the same global `type_param(name)`.
    pub(crate) extra_type_consts: Vec<String>,
}

/// Registry of overloaded class methods registered so far (`c_class.method`
/// constant name → its [`MethodDefInfo`]). Threaded read-only through
/// [`translate_theorem`] so `embed_term` rewrites every overloaded method
/// occurrence to its dictionary def-const and the `…_dict` axiom verifies
/// reflexively.
pub type MethodRegistry = BTreeMap<String, MethodDefInfo>;

/// The kernel declaration name of the clean `Definition` registered for an
/// overloaded class method `c_class.method` (`isabelle.method.<c_class.method>`).
pub(crate) fn method_def_name(method_const: &str) -> String {
    format!("isabelle.method.{method_const}")
}

/// The universe `Level` that an **embedded clean type** `ty` inhabits — the `u`
/// such that `ty : Sort u`. Used to pick the universe parameter of a HOL
/// constant-motive recursor (`Nat.rec`/`Num.rec`): the motive is `λ_. α`, so its
/// type is `_ → typeof(α)` and the recursor's `motive : _ → Sort u` constrains
/// `u` to be exactly `type_universe_level(α)`.
///
/// Computed structurally over the shapes [`Ctx::embed_type`] produces, applying
/// the CIC sorting rules — crucially the **Prop-impredicative** `imax` for
/// function/forall types (`A → Prop : Prop`, but `A → bool` where `bool ↦ Prop`
/// is the *result type* so `Nat → Prop : Sort 1`). Concretely:
///   • `Sort l`            inhabits `Sort (l+1)`           → `succ l`
///     (so `Prop = Sort 0 : Sort 1`, not `Sort 0` — the bug this fixes: a bare
///      `α = bool ↦ Prop` recursor result lives in `Sort 1`, not `Sort 0`);
///   • `Pi (_:A). B`       inhabits `Sort (imax (lvl A) (lvl B))`;
///   • an object-type `Const` (`Nat`/`Num`/`Int`/…) lives in `Type = Sort 1`.
/// Anything else defaults to `Sort 1` (the object-type universe), a safe
/// over-approximation the kernel re-checks (a wrong level simply rejects, never
/// miscounts).
pub(crate) fn type_universe_level(ty: &Expr) -> Level {
    use clean_kernel::expr::ExprKind;
    match ty.kind() {
        ExprKind::Sort(l) => Level::succ(l.clone()),
        ExprKind::Pi(_, a, b) => Level::imax(type_universe_level(a), type_universe_level(b)),
        _ => Level::succ(Level::zero()),
    }
}

/// The kernel declaration name of the clean `Definition` registered for a class
/// constant `c_class` (`isabelle.def.<c_class>`).
pub(crate) fn class_def_name(class_const: &str) -> String {
    format!("isabelle.def.{class_const}")
}

/// If `thm` is a **type-class definitional axiom** `…c_class_def` of the canonical
/// shape `c_class (TYPE('a)) ≡ B` — proof a bare `…_class_def` `PAxm` and
/// statement a `Pure.eq` whose LHS is a single class predicate `c_class` applied
/// to one `Pure.type` argument — return `(class_const_name, body B)`.
///
/// This is the registration trigger for the type-class-as-hypothesis model:
/// [`build_class_def`] turns `B` into a closed polymorphic clean `Definition`
/// `isabelle.def.<c_class> := λ(α:Type)(ops…). ⟨embed B⟩`, after which
/// `OFCLASS('a, c_class)` premises in *consumer* proofs embed to the real
/// membership proposition `c_class α ops` (via [`Ctx::embed_class_membership`])
/// rather than the vacuous `True`.
/// If `thm` is a registrable structured type-class definitional axiom, build the
/// clean polymorphic `Definition` for its class predicate and the
/// [`ClassDefInfo`] describing how consumers apply it. Returns the class constant
/// name (the [`ClassRegistry`] key), the `Declaration` to `add_decl` into the
/// accumulating environment, and the info. Used by the closure-replay driver
/// (`super::isabelle_pure_verify`) to register classes in dependency order before
/// translating consumers. Returns `None` when `thm` is not a class-def or its
/// body does not embed.
#[must_use]
pub(crate) fn register_class_def(
    thm: &IsaProvenTheorem,
    registry: &ClassRegistry,
) -> Option<(String, Declaration, ClassDefInfo)> {
    let (class_name, type_var, body) = class_def_axiom(thm)?;
    let class_name = class_name.to_string();
    let (decl, info) = build_class_def(&class_name, type_var, body, registry)?;
    Some((class_name, decl, info))
}

/// Scan a theorem's recorded proof for **overloaded-method dictionary axioms**
/// (`c_class.method ≡ c.method op₁ … opₙ`) and return, for each method not yet in
/// `registry`, its `(method_name, Declaration, MethodDefInfo)`.
///
/// The `…_dict` axiom is exported only as a bare `PAxm` argument to
/// `Pure.symmetric` (whose two `%` term arguments are the equation's sides — see
/// [`MethodDefInfo`]), so the dictionary equation is recovered by scanning for
/// that spine and the clean polymorphic `Definition` for `c_class.method` is built
/// from it ([`build_method_def`]). The driver registers these (idempotently) in a
/// pre-pass over the corpus before translating consumers, so every occurrence of
/// the overloaded method embeds to its dictionary def-const and the `…_dict` axiom
/// verifies reflexively. Returns an empty `Vec` for proofs that reference no new
/// method dictionary. The kernel re-checks each `Definition`, so a malformed
/// dictionary model is rejected by `add_decl`, never registered wrong.
#[must_use]
pub(crate) fn register_method_defs(
    thm: &IsaProvenTheorem,
    registry: &MethodRegistry,
) -> Vec<(String, Declaration, MethodDefInfo)> {
    let mut eqs = Vec::new();
    scan_method_dicts(&thm.proof, &mut eqs);
    // zproof (v3.2) encoding: the `…_dict` unfolding is not a `Pure.symmetric`
    // term-application spine (the scan above finds nothing there) but the `A`/`B`
    // schematic operands of the enclosing `Pure.equal_elim` axiom. Recover those
    // dictionary equations by diffing the two goal sides ([`scan_method_dicts_zproof`]).
    scan_method_dicts_zproof(&thm.proof, &mut eqs);
    // Some overloaded methods (`Orderings.ord_class.max`/`min`/`Least`) export
    // their dictionary axiom as a STANDALONE named theorem whose `prop` IS the
    // dictionary equation `c_class.method ≡ c.method ops` and whose recorded proof
    // is the bare `…_dict` `PAxm` (not the `Pure.symmetric`-spine form the scanner
    // above recovers). Recover the equation from the statement itself so these
    // methods register too. Gated on the theorem being a `…_dict`-named node so it
    // never mis-fires on an ordinary equation whose LHS happens to be a method.
    if thm.name.ends_with("_dict") {
        if let Some(eq) = dict_equation_from_prop(&thm.prop) {
            eqs.push(eq);
        }
    }
    let mut out = Vec::new();
    let mut seen: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
    for eq in &eqs {
        if registry.contains_key(&eq.method_name) || !seen.insert(eq.method_name.clone()) {
            continue;
        }
        if let Some((decl, info)) = build_method_def(eq) {
            out.push((eq.method_name.clone(), decl, info));
        }
    }
    out
}

/// The **superclass** class-predicate constant names referenced in a structured
/// `…c_class_def` axiom's body (the `super_class TYPE('a)` membership conjuncts,
/// e.g. `ab_semigroup_add_class`'s body references `semigroup_add_class`). Used
/// by the closure-replay driver to register class definitions in
/// superclass-first order: a class whose body re-embeds a superclass's
/// operations can only be built faithfully once that superclass is already in
/// the [`ClassRegistry`] (otherwise the superclass membership erases to `True`
/// and the inherited operations cannot be typed). Returns the class's own name
/// alongside the list, or `None` when `thm` is not a class-def axiom.
#[must_use]
pub(crate) fn class_def_superclasses(thm: &IsaProvenTheorem) -> Option<(String, Vec<String>)> {
    let (class_name, _type_var, body) = class_def_axiom(thm)?;
    let mut supers = Vec::new();
    collect_class_app_consts(body, class_name, &mut supers);
    Some((class_name.to_string(), supers))
}

/// Collect every `_class`-suffixed predicate constant applied to a `Pure.type`
/// argument inside `tm` (a class-membership use), excluding the class being
/// defined itself. These are the superclass dependencies of a `_class_def` body.
pub(crate) fn collect_class_app_consts(tm: &IsaTerm, self_name: &str, out: &mut Vec<String>) {
    match tm {
        IsaTerm::App { f, a } => {
            if let IsaTerm::Const { n, .. } = f.as_ref() {
                if n.ends_with("_class") && n != self_name && is_class_app(f) {
                    // Confirm the argument is a `Pure.type : itself('a)` (a
                    // genuine membership), not an arbitrary application.
                    if class_type_arg(a).is_some() && !out.iter().any(|s| s == n) {
                        out.push(n.clone());
                    }
                }
            }
            collect_class_app_consts(f, self_name, out);
            collect_class_app_consts(a, self_name, out);
        }
        IsaTerm::Abs { b, .. } => collect_class_app_consts(b, self_name, out),
        _ => {}
    }
}

/// Whether a theorem's CONCLUSION (after stripping the leading `⟹` premises)
/// is a class-membership proposition `OFCLASS('a, c_class)` of a **registered
/// structured class** — the `intro_of_class` / class-arity chain shape. The
/// escalating verifier runs the `Real`-membership passes FIRST for these nodes:
/// their faithful stored type ends in the real membership `c_class α ops`
/// (which downstream membership consumers need), whereas the historical
/// `Erase`-first order would store the vacuous `… → True` restatement whenever
/// the erased translation happens to type-check, poisoning every consumer that
/// needs the real conclusion. Strictly verdict-additive: the erase passes still
/// run afterwards, so any node only verifiable under erasure keeps verifying.
#[must_use]
pub fn concludes_registered_class_membership(
    thm: &IsaProvenTheorem,
    registry: &ClassRegistry,
) -> bool {
    let concl = strip_leading_imps(&thm.prop);
    let IsaTerm::App { f, a } = concl else {
        return false;
    };
    let IsaTerm::Const { n, .. } = f.as_ref() else {
        return false;
    };
    n.ends_with("_class") && class_type_arg(a).is_some() && registry.contains_key(n)
}

pub(crate) fn class_def_axiom(thm: &IsaProvenTheorem) -> Option<(&str, &IsaType, &IsaTerm)> {
    if !proof_head_is_class_def_axiom(&thm.proof) {
        return None;
    }
    // No leading `OFCLASS ⟹ …` premises on the class-def itself.
    let (lhs, rhs) = pure_eq_parts(&thm.prop)?;
    // LHS must be exactly `c_class (TYPE('a))` — one class-predicate const applied
    // to a single `Pure.type` argument of `itself('a)` type.
    let IsaTerm::App { f, a } = lhs else {
        return None;
    };
    let IsaTerm::Const { n: class_name, .. } = f.as_ref() else {
        return None;
    };
    if !class_name.ends_with("_class") {
        return None;
    }
    let type_var = class_type_arg(a)?; // the class's object type `'a`
    Some((class_name, type_var, rhs))
}

/// Whether a proof's head leaf is a bare `…_class_def` axiom.
pub(crate) fn proof_head_is_class_def_axiom(p: &IsaProof) -> bool {
    match p {
        IsaProof::Axm { name, .. } => name.ends_with("_class_def"),
        IsaProof::AppP { f, .. }
        | IsaProof::AppT { f, .. }
        | IsaProof::AbsP { b: f, .. }
        | IsaProof::Abst { b: f, .. } => proof_head_is_class_def_axiom(f),
        _ => false,
    }
}

/// Build the clean polymorphic `Definition` for a type-class predicate from its
/// `…c_class_def` body `B` (`c_class (TYPE('a)) ≡ B`).
///
/// `B` is embedded in a **fresh** [`Ctx`] (with the already-registered classes in
/// scope so nested superclass predicates `super (TYPE('a))` resolve to their
/// def-consts), discovering the object type `α` and the class **operations** as
/// free parameters. We abstract `α` outermost and the operations next, yielding a
/// closed value `λ(α:Type)(op₁…opₙ). embed(B) : Π(α:Type)(op₁…opₙ). Prop`. The
/// returned [`ClassDefInfo`] records the operation order so consumers apply the
/// def-const identically. Returns `None` if `B` does not embed (kept honest — the
/// driver then simply does not register the class, and consumers fall back to the
/// `True` erasure).
pub(crate) fn build_class_def(
    class_name: &str,
    type_var: &IsaType,
    body: &IsaTerm,
    registry: &ClassRegistry,
) -> Option<(Declaration, ClassDefInfo)> {
    let mut ctx = Ctx {
        class_registry: registry.clone(),
        class_membership: true,
        ..Default::default()
    };
    // Force-register the class's object type `α` FIRST, so it is always the
    // OUTERMOST binder of the registered definition — even for a *base* class
    // whose body (`HOL.type_class _` → `True`) never mentions it. The class
    // predicate's HOL type is `itself('a) ⇒ prop`, so it is intrinsically
    // parameterised by `'a`; a consumer's `OFCLASS('a, c_class)` premise applies
    // the def-const to `α` unconditionally, so the binder must be present.
    let _ = ctx.embed_type(type_var).ok()?;
    // The object type `α` is the first (and, for a single-`α` class, only) type
    // param; record its key so the extra ground-type params can be separated out.
    let alpha_key = ctx.type_params.first().map(|(k, _)| k.clone());
    let mut binders: Vec<Binder> = Vec::new();
    let value_core = ctx.embed_term(body, &mut binders).ok()?;
    // The HOL types of every operation referenced in the body, for the
    // `ClassDefInfo` consumers re-embed from. The class's own body supplies the
    // operations of *this* class and the `class.…_axioms` predicate; the
    // operations introduced by a **structured superclass** membership
    // (`super_class TYPE('a)` re-embeds the superclass's own `ops`) are not
    // syntactically present in `body`, so their HOL types are pulled from the
    // already-registered superclass [`ClassDefInfo`]s in `registry`. This is what
    // makes a superclass-chained class (e.g. `ab_semigroup_add` over
    // `semigroup_add`) register: its term params include the inherited
    // `class.semigroup_add`/`plus`, whose types live in the superclass entry.
    let mut op_types = collect_op_types(body);
    for info in registry.values() {
        for (op_name, op_ty) in &info.ops {
            op_types
                .entry(op_name.clone())
                .or_insert_with(|| op_ty.clone());
        }
    }
    // The body must be over `Prop` (a class predicate's body is a proposition).
    // Abstract the discovered parameters: operations (term params) innermost,
    // the object type(s) outermost — mirroring `translate_theorem`'s final wrap.
    // Record each operation under its constant name (strip the `const:` key
    // prefix), in first-seen order, so consumers apply the def-const identically.
    let mut value = value_core;
    let mut def_type = Expr::prop();
    let mut ops: Vec<(String, IsaType)> = Vec::new();
    for (key, p) in ctx.term_params.iter().rev() {
        value = Expr::lam(
            BinderInfo::Default,
            p.ty.clone(),
            value.abstract_fvar(p.fvar),
        );
        def_type = Expr::pi(
            BinderInfo::Default,
            p.ty.clone(),
            def_type.abstract_fvar(p.fvar),
        );
        let op_name = const_key_name(key).unwrap_or(key).to_string();
        // Every term param of a class-def body is an operation `const:<n>`; its
        // HOL type must be recoverable from the body (else we cannot let a
        // consumer re-embed it coherently → do not register the class).
        let op_ty = op_types.get(&op_name)?.clone();
        ops.push((op_name, op_ty));
    }
    ops.reverse();
    // The extra fixed ground-type params (every type param past the first `α`),
    // in the order the definition abstracts them, so a consumer's membership use
    // supplies them right after `α` and before the operations. For a single-`α`
    // class this stays empty.
    let extra_type_consts: Vec<String> = ctx
        .type_params
        .iter()
        .map(|(k, _)| k.clone())
        .filter(|k| Some(k) != alpha_key.as_ref())
        .collect();
    for (_key, p) in ctx.type_params.iter().rev() {
        value = Expr::lam(
            BinderInfo::Default,
            p.ty.clone(),
            value.abstract_fvar(p.fvar),
        );
        def_type = Expr::pi(
            BinderInfo::Default,
            p.ty.clone(),
            def_type.abstract_fvar(p.fvar),
        );
    }
    let def_name = class_def_name(class_name);
    let def_value = value.clone();
    let decl = Declaration::Definition {
        name: Name::from_string(&def_name),
        level_params: Vec::new(),
        type_: def_type,
        value,
        is_reducible: true,
    };
    Some((
        decl,
        ClassDefInfo {
            def_name,
            ops,
            extra_type_consts,
            def_value,
        },
    ))
}

/// Collect the HOL type of every constant operation referenced in a class-def
/// body (`Const`/`Var` heads that are not structural/connective), keyed by name.
/// Used by [`build_class_def`] to record each abstracted operation's faithful
/// HOL type for re-embedding in consumers.
pub(crate) fn collect_op_types(tm: &IsaTerm) -> BTreeMap<String, IsaType> {
    pub(crate) fn go(tm: &IsaTerm, out: &mut BTreeMap<String, IsaType>) {
        match tm {
            // Only genuine operations get abstracted as term params (the same
            // constants `embed_term`'s generic `Const` arm turns into
            // `const:<n>` params). Structural/connective heads embed to clean
            // operators and are never term params.
            IsaTerm::Const { n, t } if is_op_const(n) => {
                out.entry(n.clone()).or_insert_with(|| t.clone());
            }
            IsaTerm::App { f, a } => {
                go(f, out);
                go(a, out);
            }
            IsaTerm::Abs { b, .. } => go(b, out),
            _ => {}
        }
    }
    let mut out = BTreeMap::new();
    go(tm, &mut out);
    out
}

/// Whether a constant name is a class **operation** (abstracted as a `const:<n>`
/// term param by `embed_term`), as opposed to a structural/connective head that
/// embeds to a clean operator. Mirrors the negative space of `embed_term`'s
/// special-cased `Const` arms.
pub(crate) fn is_op_const(n: &str) -> bool {
    !(is_class_op_structural(n)
        || n.ends_with("_class")
        || n == "Pure.sort_constraint"
        || connective_def_name(n).is_some())
}

/// Structural/connective constant heads that `embed_term` rewrites to a clean
/// operator (never a `const:` term param).
pub(crate) fn is_class_op_structural(n: &str) -> bool {
    matches!(
        n,
        "HOL.Trueprop"
            | "Trueprop"
            | "Pure.prop"
            | "Pure.all"
            | "Pure.all_def"
            | "HOL.All"
            | "HOL.Ex"
            | "Pure.imp"
            | "HOL.implies"
            | "Pure.conjunction"
            | "HOL.type_class"
            | "Pure.eq"
            | "HOL.eq"
            | "="
    )
}
