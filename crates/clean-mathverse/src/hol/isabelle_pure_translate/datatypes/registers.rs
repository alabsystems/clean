// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Instance-operation and polymorphic-instance definition-axiom detection and
//! registration: `instance_op_def_axiom`, `register_instance_op_def`,
//! `poly_inst_def_axiom`, `register_poly_inst_def`. Moved from the
//! original single-file `datatypes` module.

use std::collections::BTreeMap;

use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Declaration, Expr};

use super::super::super::isabelle_pure::{IsaProvenTheorem, IsaTerm, IsaType};
use super::super::*;

/// If `thm` is a **monomorphic ground-type instance-operation definition** —
/// a `Pure.eq`/`HOL.eq` definitional axiom whose LHS is an overloaded class
/// operation (`Groups.plus_class.plus`, `Groups.times_class.times`, …)
/// instantiated at a closed ground type (no `TVar`/`TFree`) — return
/// `(method-name, ground-operand-type, rhs-body)`.
///
/// These are exported as the recursive-arithmetic `…_nat_def` / `…_num_def`
/// axioms (`Nat.plus_nat_def`, `Nat.times_nat_def`, …) whose recorded proof is an
/// intricate `Pure.transitive` unfolding chain bottoming out in unmapped
/// `…_inst.…_def` raw leaves — so detection is by **statement shape**
/// (like [`set_instance_def_body`]), not the recorded-proof head (which is not a
/// bare `_def`). A `proof_contains_def_axiom` guard restricts the shortcut to
/// genuine definitional nodes (whose `_def`/`_def_raw` leaf is present somewhere),
/// never an ordinary nat-arithmetic theorem with a real derivation.
pub(crate) fn instance_op_def_axiom(thm: &IsaProvenTheorem) -> Option<(&str, &IsaType, &IsaTerm)> {
    if !proof_contains_def_axiom(&thm.proof) {
        return None;
    }
    let concl = strip_leading_imps(&thm.prop);
    let (lhs, rhs) = pure_eq_parts(concl)?;
    let eq_ty = pure_eq_operand_ty(concl)?;
    // The LHS must be the *bare* overloaded class operation (zero args) at a
    // closed ground type — the instance-operation definition shape.
    let IsaTerm::Const { n, t } = lhs else {
        return None;
    };
    if !is_overloaded_method_const(n) || !is_ground_type(t) {
        return None;
    }
    Some((n, eq_ty, rhs))
}

/// Register the **monomorphic ground-type instance operation** a `…_nat_def` /
/// `…_num_def` axiom defines, as a clean `Definition`
/// `isabelle.inst.<c>@<ground-type-key> := <embed RHS>`.
///
/// The operation type is fully ground, so the definition is *closed* and
/// *monomorphic* — no type variable or class operation to abstract (unlike the
/// polymorphic [`build_method_def`]). The body embeds with `instance_unfold`
/// active over the *current* registry, so a recursive op whose body mentions an
/// earlier-registered instance op (e.g. `times`'s body mentions `plus` and the
/// `0::nat` base) re-embeds those to their def-consts / direct mappings and the
/// value closes. If the body fails to embed to a *closed* term (e.g. it mentions a
/// constant that has no clean image and survives as a `const:` param — the value
/// would then contain a free FVar → kernel `ContainsFreeVar`), registration is
/// skipped: the `…_def` axiom stays unmapped exactly as before, never
/// mis-registered.
///
/// Returns the registry key `(method-name, ground-type-key)`, the clean
/// `Definition`, and its [`InstanceOpInfo`], or `None` when `thm` is not an
/// instance-op def axiom or its body does not close. The driver registers these in
/// **serial (= dependency) order** so a base op is in the registry before a
/// recursive op that uses it.
#[must_use]
pub(crate) fn register_instance_op_def(
    thm: &IsaProvenTheorem,
    registry: &InstanceOpRegistry,
) -> Option<((String, String), Declaration, InstanceOpInfo)> {
    let (method_name, eq_ty, rhs) = instance_op_def_axiom(thm)?;
    let type_key = isa_ground_type_key(eq_ty);
    let key = (method_name.to_string(), type_key.clone());
    if registry.contains_key(&key) {
        return None;
    }
    // Embed the RHS with instance-unfold over the current registry, so nested
    // already-registered ops (and the nat base constructors) resolve to closed
    // def-consts / constructors rather than free params.
    let mut ctx = Ctx {
        instance_op_registry: registry.clone(),
        instance_unfold: true,
        ..Default::default()
    };
    let mut binders: Vec<Binder> = Vec::new();
    let value = ctx.embed_term(rhs, &mut binders).ok()?;
    // The definition's type is the embedded ground operand type. Ground ⇒ no
    // type params discovered; any term param means the body did NOT close (an
    // unmapped const survived), so reject — the kernel would otherwise see a free
    // FVar (`ContainsFreeVar`). Keeping registration honest: only genuinely closed
    // bodies are stored.
    if !ctx.type_params.is_empty() || !ctx.term_params.is_empty() {
        return None;
    }
    let def_type = ctx.embed_type(eq_ty).ok()?;
    let def_name = instance_op_def_name(method_name, &type_key);
    let decl = Declaration::Definition {
        name: Name::from_string(&def_name),
        level_params: Vec::new(),
        type_: def_type,
        value,
        is_reducible: true,
    };
    Some((key, decl, InstanceOpInfo { def_name }))
}

/// If `thm` is a **polymorphic instance-operation definition** — a `Pure.eq`/`HOL.eq`
/// definitional axiom whose LHS is a *bare polymorphic constant* `c` applied to
/// schematic argument variables `?arg₁ … ?argₖ` (the η-expanded function form), where
/// `c` carries **any number** of object type variables (k ≥ 0, discovered by
/// [`method_obj_tvars`] in first-occurrence order — the G1 gate-lift; the historical
/// `sole_tvar` gate declined every multi-tvar definitional constant: `rel_prod` has
/// 4, `Sum_Type.Plus`/`csum`/`cexp` 2, `Enum.enum_*` 2, …) and is **not** itself an
/// overloaded `_class.` method (those go through [`build_method_def`]) — return
/// `(fn-name, fn-type, object-tvars, schematic-arg-names, rhs-body)`.
///
/// The canonical example is `Int.power_int` (`power_int ?x ?n ≡ if 0 ≤ ?n then …`),
/// whose body uses the overloaded class operations `power`/`inverse`/`uminus`/`zero`/
/// `less_eq` over `'a`. Detection is by **statement shape** (like
/// [`instance_op_def_axiom`]), guarded by `proof_contains_def_axiom` so the shortcut
/// never steals an ordinary theorem with a real derivation. The body need NOT
/// reference an overloaded class operation (the G2 gate-lift): plain-body
/// definitional constants and plain (non-type-class) locale predicates register
/// too — the `list_fn`/`instance_op` registries still win at embed-time for the
/// constants they cover (their arms dispatch first), and
/// [`has_canonical_encoding`] excludes every hand-encoded constant.
#[allow(clippy::type_complexity)]
pub(crate) fn poly_inst_def_axiom(
    thm: &IsaProvenTheorem,
) -> Option<(
    &str,
    &IsaType,
    Vec<(String, i64)>,
    Vec<(String, i64)>,
    &IsaTerm,
)> {
    // A genuine definitional axiom is named `…_def` / `…_def_raw` (Isabelle's
    // convention) OR its recorded proof bottoms out in such a `_def`/`_def_raw` PAxm
    // leaf. The expanded export proves a `_def` reflexively (a `Pure.reflexive` leaf,
    // NOT a `_def_raw` PAxm), so the name marker is the reliable signal; the raw
    // export keeps the `_def_raw` leaf. Either marker scopes the shortcut to real
    // definitions — and the kernel's `Eq.refl` still rejects any non-reflexive case,
    // so a wrong detection never miscounts.
    let name_is_def = thm.name.ends_with("_def") || thm.name.ends_with("_def_raw");
    if !name_is_def && !proof_contains_def_axiom(&thm.proof) {
        return None;
    }
    let concl = strip_leading_imps(&thm.prop);
    let (lhs, rhs) = pure_eq_parts(concl)?;
    // The LHS is the constant `c` applied to schematic argument variables: peel the
    // application spine to the head const and the (Var) arguments.
    let (head, args) = term_app_spine(lhs);
    let IsaTerm::Const { n, t } = head else {
        return None;
    };
    // `c` must NOT be an overloaded method (dictionary path) and must carry exactly
    // ONE object type variable (no fixed `TFree`).
    if is_overloaded_method_const(n) {
        return None;
    }
    // `c` must NOT be a constant the embedder already maps to a **canonical
    // semantic encoding** (`Set.insert` → the `insert_compr` disjunction lambda,
    // `Set.Ball`/`Bex`/`Pow`/`image`, `HOL.If`/`HOL.The`, `Fun.comp`/`id`, the
    // `Fun.*` combinator def-consts, the point-free logical constants, the
    // connective def-consts, the order extrema). Registering one as a poly-inst
    // def-const would SHADOW its canonical encoding at every use-site
    // ([`Ctx::embed_const_term2`] consults the poly-inst registry BEFORE the
    // encoding arms), splitting occurrences across two irreconcilable heads —
    // e.g. `Set.insert_def` (`insert ?a ?B = sup {x. x=a} ?B`, whose `sup`
    // mention trips the overloaded-method scope) used to re-register
    // `Set.insert`, which then broke `finite_def` (its `lfp` body embeds
    // `Set.insert` via the canonical encoding) and every `insert_compr`-style
    // consumer. Excluded here so every occurrence stays on the ONE canonical
    // head; the shadowing `_def` itself is honestly rejected unless another arm
    // proves it.
    if has_canonical_encoding(n) {
        return None;
    }
    // G1 (lifted): EVERY distinct object tvar in first-occurrence order (k ≥ 0,
    // no fixed `TFree`) — the same discovery the r9 dictionary machinery
    // ([`build_method_def`]) and the r12+ `bnf_cardinal` opaque framework use.
    let obj_tvars = method_obj_tvars(t)?;
    // Each LHS argument must be a schematic `Var` (the η-expanded formal parameter).
    let mut arg_vars: Vec<(String, i64)> = Vec::new();
    for a in &args {
        let IsaTerm::Var { n: vn, i: vi, .. } = a else {
            return None;
        };
        arg_vars.push((vn.clone(), *vi));
    }
    // G2 (lifted): the body may — but need NOT — mention an overloaded class
    // operation. The historical gate required a method mention (or a `.class.`
    // locale-predicate name), which declined (a) every **plain-body** definitional
    // constant (`Fun_Def.pair_leq`-style pure-logic bodies over the formal
    // arguments) and (b) every **plain locale predicate** (`Orderings.
    // {partial_preordering,preordering,ordering}`, `Finite_Set.folding_on`,
    // `Lattices_Big.semilattice_set`, `Groups_Big.comm_monoid_set` — Isabelle
    // locales that are NOT type classes, so their mangled names carry no
    // `.class.`). The plain locales gate the entire `Finite_Set.fold → card →
    // sum/prod` big-operator tower. Registration is safe for any closing body:
    // the `register_poly_inst_def` close-or-skip partition still rejects a body
    // that does not close, [`has_canonical_encoding`] still excludes every
    // constant with a canonical hand encoding (the shadow guard), and the kernel
    // re-checks the `Definition` and every consumer — a wrong registration is
    // rejected, never miscounted.
    Some((n, t, obj_tvars, arg_vars, rhs))
}

/// If `thm` is an **alternative-form definitional equation** — a theorem named
/// `…_alt_def` whose conclusion is a `Pure.eq`/`HOL.eq` with a `Const`-headed
/// LHS — return that LHS head constant's name.
///
/// An `_alt_def` records a PROVED equivalent reformulation of a constant's
/// real definition (`left_total_alt_def : left_total R ⟷ ((=) ≤ R OO R⁻¹)`),
/// derived by a rewriting chain from the `_def` axiom. Registering the head as
/// a poly-inst def-const makes the recorded chain reconstruct to the
/// **tautology** `Eq(lhs, lhs)` (every midpoint occurrence δ-unfolds to the
/// def body, collapsing the `Pure.transitive` legs) while the stored statement
/// keeps the REAL `Eq(lhs, alt-body)` — a kernel reject on a previously-KV
/// node (the r18/G2 `Transfer.*_alt_def` / `Zorn.Chains_alt_def` regression
/// class; re-deriving the chain under unfolding is the r10-congruence root-B
/// problem). [`register_poly_insts`] therefore pre-scans the batch and
/// DECLINES registration for every `_alt_def` head.
#[must_use]
pub fn alt_def_head(thm: &IsaProvenTheorem) -> Option<&str> {
    if !thm.name.ends_with("_alt_def") {
        return None;
    }
    let concl = strip_leading_imps(&thm.prop);
    let (lhs, _rhs) = pure_eq_parts(concl)?;
    let (head, _args) = term_app_spine(lhs);
    match head {
        IsaTerm::Const { n, .. } => Some(n),
        _ => None,
    }
}

/// Whether a constant is an Isabelle **locale predicate** for a type class —
/// the mangled `Thy.class.c` / `Thy.class.c_axioms` names (`Orderings.class.order`,
/// `Groups.class.monoid_add_axioms`, …). These are ordinary `bool`-valued
/// predicate constants (NOT the `…_class : itself('a) ⇒ prop` sort predicates and
/// NOT the overloaded `…_class.method` operations).
pub(crate) fn is_locale_predicate_const(n: &str) -> bool {
    n.contains(".class.")
}

/// Whether the embedder maps constant `n` to a **canonical semantic encoding**
/// (a set-op/`Fun.*`/point-free/connective/extremum/`If`/`The`/`comp`/`id`
/// lambda or def-const) rather than an opaque parameter. Such a constant must
/// never be re-registered under a *second* def-const head (poly-inst registry),
/// or its occurrences split across two irreconcilable embeddings. See the
/// guard in [`poly_inst_def_axiom`].
pub(crate) fn has_canonical_encoding(n: &str) -> bool {
    matches!(
        n,
        // The core logical constants: encoded at the APPLICATION level (the
        // quantifier/implication/equality arms of `embed_term`/`embed_use`),
        // so the bare-`Const` shadow PROBE in [`register_poly_inst_def`]
        // cannot see their canonical arms — excluded by name. Registering one
        // (`HOL.All_def` is a real corpus axiom) would split applied
        // occurrences (canonical Pi/Eq encodings) from bare occurrences
        // (poly-inst def-const) across two irreconcilable heads.
        "HOL.All"
            | "HOL.Ex"
            | "Pure.all"
            | "Pure.imp"
            | "HOL.implies"
            | "HOL.eq"
            | "Pure.eq"
            | "HOL.Trueprop"
            | "Pure.prop"
            | "Pure.conjunction"
            | "Set.Collect"
            | "Set.member"
            | "Set.Ball"
            | "Set.Bex"
            | "Set.Pow"
            | "Set.insert"
            | "Set.image"
            | "Complete_Lattices.Inf_class.Inf"
            | "Complete_Lattices.Sup_class.Sup"
            | "HOL.If"
            | "HOL.The"
            | "Fun.comp"
            | "Fun.id"
            // The hand-modeled BNF/list combinators of `embed_const.rs` (the
            // r13 list-BNF model: `map` via `List.rec` image, the initial-algebra
            // `ctor_list`/`ctor_fold_list`, the pre-datatype `map_pre_list`, and
            // the `map_sum`/`map_prod`/`map_option`/`map_fun` functorial maps).
            // All are ≥2-tvar, so the historical `sole_tvar` gate excluded them
            // implicitly; under the G1 multi-tvar lift they must be excluded
            // EXPLICITLY or their `_def` registration would shadow the hand
            // encoding at every use-site (the `ctor_fold_list_def` r17
            // regression — the same incident class as `Set.insert_def`).
            | "List.list.map"
            | "List.list.ctor_list"
            | "List.list.ctor_fold_list"
            | "List.pre_list.list.map_pre_list"
            | "Sum_Type.map_sum"
            | "Product_Type.map_prod"
            | "Option.map_option"
            | "Fun.map_fun"
    ) || fun_def_const_name(n).is_some()
        || bnf_def_const_name(n).is_some()
        || bnf_opaque_def_const_name(n).is_some()
        || wo_the_def_const_name(n).is_some()
        || pointfree_const_def_name(n).is_some()
        || connective_def_name(n).is_some()
        || is_order_extremum(n)
}

/// Register the **polymorphic instance operation** a `_def` axiom defines as a clean
/// polymorphic `Definition`
/// `isabelle.polyinst.<c> := λ(α:Type)(extra-types…)(op₁ … opₘ)(arg₁ … argₖ). <embed body>`.
///
/// The body is embedded in a fresh [`Ctx`] with `instance_unfold` active (so nested
/// already-mapped datatype recursors / Int-quotient bridges resolve) but **without**
/// `method_unfold` (so the overloaded class operations stay as opaque `const:<op>`
/// term params — exactly the form a consumer re-embeds them in, keeping the equation
/// reflexive across use-sites). The discovered parameters are partitioned:
///   • type params → `α` (the object type) plus any **extra ground type constructors**
///     (`Int.int`, …), abstracted as leading `Π(_:Type)` binders;
///   • term params whose key is `const:<op>` → the class **operations**, abstracted
///     after the types (consumer-supplied);
///   • term params keyed by a schematic argument name (`x.0`, `n.0`, …) → the
///     η-expanded **formal arguments**, abstracted innermost (the consumer's own
///     application fills them).
///
/// If the body fails to close to exactly that partition (an unexpected free param
/// survives — e.g. an unmapped non-method constant), registration is skipped and the
/// `_def` axiom stays unmapped exactly as before. The kernel re-checks the
/// `Definition` via `add_decl`, so a malformed body is rejected, never mis-registered.
/// Returns the registry key (the constant name), the `Definition`, and its
/// [`PolyInstInfo`], or `None`.
#[must_use]
pub fn register_poly_inst_def(
    thm: &IsaProvenTheorem,
    registry: &PolyInstRegistry,
) -> Option<(String, Declaration, PolyInstInfo)> {
    // Guard-free form (single-theorem callers, e.g. the faithfulness gate):
    // no method/instance/list registries and no `_alt_def` pre-scan — exactly
    // the driver behaviour on a corpus containing only the candidate line.
    register_poly_inst_def_guarded(
        thm,
        registry,
        &MethodRegistry::new(),
        &InstanceOpRegistry::new(),
        &ListFnRegistry::new(),
        &std::collections::BTreeSet::new(),
    )
}

/// The driver form of [`register_poly_inst_def`], threading the G2 guard
/// context: the method registry (dict-impl guard), the instance-op + list-fn
/// registries (registration-flavor alignment), and the batch's
/// `_alt_def`-head decline set (see [`alt_def_head`]).
#[must_use]
pub fn register_poly_inst_def_guarded(
    thm: &IsaProvenTheorem,
    registry: &PolyInstRegistry,
    methods: &MethodRegistry,
    instance_ops: &InstanceOpRegistry,
    list_fns: &ListFnRegistry,
    alt_heads: &std::collections::BTreeSet<String>,
) -> Option<(String, Declaration, PolyInstInfo)> {
    let (fn_name, fn_ty, obj_tvars, arg_vars, rhs) = poly_inst_def_axiom(thm)?;
    if registry.contains_key(fn_name) {
        return None;
    }
    // The two G2-WIDENING guards below apply ONLY to the class this round
    // NEWLY admits — bodies with NO overloaded-method mention. A constant whose
    // body mentions an overloaded method registered under the historical gate
    // for many rounds with none of the breakage below (`Zorn.chains`,
    // `Set_Interval.ord.atLeastAtMost`, `Int.ring_1.Ints`, … — declining those
    // would LOSE their baseline-KV `_def` nodes, measured −11 on the BNF
    // slice), so the historical class keeps registering unconditionally:
    // the widening is strictly additive on the registration set by
    // construction.
    if !tm_mentions_overloaded_method(rhs) {
        // ALT-DEF GUARD (G2 supporting fix): a constant with a recorded
        // alternative-form equation in the batch (`left_total` with
        // `left_total_alt_def`) — see [`alt_def_head`] for why registration
        // turns the previously-verified `_alt_def` node into a kernel reject.
        // `Nat.compow` (the `overloading` dispatcher behind `_ ^^ _`) is the
        // same rewriting-chain-consumer shape without the naming convention:
        // registering it makes the `Transitive_Closure.relpow_def`/
        // `relpowp_def` primrec nodes (whose recorded proofs rewrite through
        // the dispatcher) reconstruct to the collapsed tautology —
        // hand-declined pending the congruence-lane (r10 root-B)
        // reconstruction. `relpow`/`relpowp` themselves stay declined for the
        // same chain.
        if alt_heads.contains(fn_name)
            || matches!(
                fn_name,
                "Nat.compow" | "Transitive_Closure.relpow" | "Transitive_Closure.relpowp"
            )
        {
            return None;
        }
        // DICT-IMPL GUARD — WIDENED to TWO-object-tvar impls (binder-order
        // round). History: G2 declined EVERY dictionary implementation of a
        // registered overloaded method (naively poly-registering the impl
        // made every `<c>_class.<m>_def` hub kernel-reject); the dict-impl
        // round closed the membership-mode seam (`True` premise ⇒
        // `True.intro` coercion) and re-admitted SINGLE-object-tvar impls;
        // multi-tvar impls (`comm_monoid_add.sum`, `comm_monoid_mult.prod`,
        // `linorder.insort_key` — `('b⇒'a)⇒'b set⇒'a` method shapes) stayed
        // declined for the same-arity `Pi[k]→Eq got=Pi[k]→Eq` operand-order
        // mismatch on their hubs. The binder-order round root-caused THAT
        // wall: the hub exports spell the PROP in the theory-level tvar
        // namespace but the recorded PROOF in the dependency box's canonical
        // namespace — crossed for a multi-tvar method — and the proof's
        // identity `tyinst` was filled verbatim (`apply_thm_explicit`),
        // instantiating the bridge at the swapped types. Fixed
        // namespace-free by the root expectation lane
        // ([`Ctx::try_root_sort_absp_expecting`]: a generic identity-table
        // reference under implicit sort `AbsP`s is pinned by the embedded
        // statement, never by the crossed table) plus the membership-witness
        // re-spelling in the expecting `PBound` arm, both on the dedicated
        // trailing `RootLane::On` escalation modes. With those seams closed
        // the 2-tvar impls register and the whole family verifies
        // (impl defs + premise-spelled bridges + hubs — `sum_def`/`prod_def`/
        // `insort_key_def`, measured on the mini4 hub slice: +12 KV, 0 lost).
        // The registration itself is close-or-skip + kernel-re-checked, so a
        // shape this lift newly admits that does NOT close is skipped or
        // rejected — never miscounted. GROUND (zero-object-tvar) impls stay
        // DECLINED (the ground lanes `instance_op`/`method_inst` own those
        // shapes), and THREE-plus-tvar impls stay DECLINED: registering them
        // changes how their method spells at every use-site in the Unfold
        // modes, and the measured family-slice effect was NEGATIVE — the
        // `old.sum.case`/`old.prod.case` (3-tvar case-combinator) former-KV
        // consumers flipped to the same-arity `Pi[k]→FVar` operand-order
        // kernel-reject (the crossed-namespace wall again, one arity up).
        // Aligning the ≥3-tvar binder-order matrix is the honest remaining
        // blocker (follow-up).
        if methods
            .values()
            .any(|m| m.impl_const.0 == fn_name && !matches!(m.obj_tvars.len(), 1 | 2))
        {
            return None;
        }
    }
    // GENERIC SHADOW GUARD (G2 supporting fix): a constant the embedder maps to
    // a canonical encoding ANYWHERE — a hand arm (`Nat.Suc` → `Nat.succ`,
    // `Product_Type.Pair`/`case_prod`, `Sum_Type.Inl`/`Inr`, the Int-quotient
    // `Abs_Integ`/`Rep_Integ` bridges), a logical-constant encoding
    // (`Pure.prop`, `Pure.conjunction`, `HOL.All`/`Ex`), or any future arm —
    // must never ALSO register as a poly-inst def-const: the registry arm
    // dispatches before the encoding arms, so the `_def` registration would
    // shadow the canonical encoding at every use-site and split occurrences
    // across two irreconcilable heads (the `Set.insert_def` /
    // `ctor_fold_list_def` incident class). [`has_canonical_encoding`] lists
    // the historically-known cases; this PROBE is the closed-form rule: embed
    // the bare `Const` in a fresh Unfold ctx — a constant with NO canonical
    // encoding embeds to exactly one opaque `const:`-keyed term param (a bare
    // `FVar`); anything else (a mapped kernel `Const`, a lambda encoding, an
    // applied def-const) proves a canonical arm exists → decline, keeping every
    // occurrence on the one canonical head. Probed under the G1-lifted
    // multi-tvar rule the registries themselves use, so the verdict matches the
    // use-site dispatch exactly.
    if !probe_embeds_opaque(fn_name, fn_ty) {
        return None;
    }
    let def_name = poly_inst_def_name(fn_name);
    let (decl, info) = build_poly_inst_definition(
        fn_name,
        fn_ty,
        obj_tvars,
        arg_vars,
        rhs,
        instance_ops,
        list_fns,
        def_name,
    )?;
    Some((fn_name.to_string(), decl, info))
}

/// The G2 generic shadow PROBE, shared by [`register_poly_inst_def_guarded`]
/// and the G4 [`register_method_inst_def`]: embed the bare `Const` in a fresh
/// Unfold ctx — a constant with NO canonical encoding embeds to exactly one
/// opaque `const:`-keyed term param (a bare `FVar`); anything else (a mapped
/// kernel `Const`, a lambda encoding, an applied def-const) proves a canonical
/// arm exists, so the caller must DECLINE registration to keep every occurrence
/// on the one canonical head (the `Set.insert_def` / `ctor_fold_list_def`
/// incident class). Probed under the G1-lifted multi-tvar rule the registries
/// themselves use, so the verdict matches the use-site dispatch exactly.
pub(crate) fn probe_embeds_opaque(fn_name: &str, fn_ty: &IsaType) -> bool {
    let mut probe = Ctx {
        instance_unfold: true,
        ..Default::default()
    };
    let mut pb: Vec<Binder> = Vec::new();
    let probe_tm = IsaTerm::Const {
        n: fn_name.to_string(),
        t: fn_ty.clone(),
    };
    match probe.embed_term(&probe_tm, &mut pb) {
        Ok(e) => {
            matches!(e.kind(), clean_kernel::expr::ExprKind::FVar(_))
                && probe.term_params.len() == 1
        }
        Err(_) => false,
    }
}

/// The shared registration BODY BUILDER: embed a definitional axiom's RHS,
/// partition the discovered params (object tvars / extra ground type
/// constructors / `const:`-keyed class operations / schematic formal
/// arguments), and abstract them into a closed polymorphic kernel `Definition`
/// named `def_name`, plus the [`PolyInstInfo`] a use-site needs to re-apply it.
/// Extracted verbatim from [`register_poly_inst_def_guarded`] (behaviour
/// byte-identical) so the G4 [`register_method_inst_def`] (an overloaded METHOD
/// head at a type-constructor instance — the third registration shape) shares
/// the exact embedding/partition/abstraction discipline, including the G3
/// strict typed-key rule. Returns `None` when the body does not close to the
/// expected shape (the `_def` axiom then stays on its recorded-proof path,
/// never mis-registered).
///
/// REGISTRATION-FLAVOR ALIGNMENT (G2 supporting fix): the body embeds in a
/// ctx carrying the CANONICAL-ENCODING registries a consumer's Unfold-pass
/// ctx carries (ground instance ops + list functions), so a body subterm
/// with a canonical registry encoding is BAKED IN exactly as every use-site
/// re-embeds it. The historical `..Default::default()` ctx had these EMPTY:
/// a body mentioning a registry-covered constant baked in the OPAQUE flavor
/// while the `_def` line's own translation embeds the registry def-const —
/// the reflexive `@Eq` then kernel-rejects and every consumer inherits the
/// split (the r18/G2 `relpow_def` regression class). The POLY registry is
/// deliberately NOT threaded: a nested registered poly const stays an opaque
/// `const:` OP BINDER whose fill is the consumer's own (unfolded) embedding
/// — the flavor is threaded through the application, not baked — and
/// threading it would mint synthesized-type op keys the G3 strict typed-key
/// rule correctly declines (measured: −166 registrations, cardinal + every
/// nested `.class.` predicate). Overloaded METHODS likewise stay opaque op
/// params by design (no `method_unfold`).
#[allow(clippy::too_many_arguments)]
pub(crate) fn build_poly_inst_definition(
    fn_name: &str,
    fn_ty: &IsaType,
    obj_tvars: Vec<(String, i64)>,
    arg_vars: Vec<(String, i64)>,
    rhs: &IsaTerm,
    instance_ops: &InstanceOpRegistry,
    list_fns: &ListFnRegistry,
    def_name: String,
) -> Option<(Declaration, PolyInstInfo)> {
    let mut ctx = Ctx {
        instance_unfold: true,
        instance_op_registry: instance_ops.clone(),
        list_fn_registry: list_fns.clone(),
        ..Default::default()
    };
    // Force-register the object types FIRST (in first-occurrence order) so they
    // are the OUTERMOST type binders — a consumer applies the def-const to them
    // first, in the same order — then embed the body.
    for tv in &obj_tvars {
        let _ = ctx.tvar_param(tv);
    }
    let alpha_keys: std::collections::BTreeSet<String> =
        obj_tvars.iter().map(|(n, i)| format!("{n}.{i}")).collect();
    let mut binders: Vec<Binder> = Vec::new();
    let mut value = ctx.embed_term(rhs, &mut binders).ok()?;
    // Re-embed the constant's HOL type in the SAME ctx so the SAME `αᵢ` fvars are
    // used.
    let mut def_type = ctx.embed_type(fn_ty).ok()?;
    // G3 (lifted): recover each `const:`-keyed op param's HOL type from the
    // SPECIFIC body occurrence that MINTED it. The r16 `const_param_key` keys an
    // opaque constant by (name, embedded-type hash), so a body that uses ONE
    // polymorphic operation at TWO type instantiations (`csum`'s two `Field`s,
    // `rel_prod`'s two `rel`s) discovers two DISTINCT params — and each needs
    // ITS OWN occurrence type recorded, not the first-by-name occurrence
    // [`poly_inst_op_isa_ty`] returns (which made the two use-site supplies
    // coincide and kernel-reject; r16 therefore declined such bodies outright).
    // Re-derive the exact key of every body `Const` occurrence by embedding its
    // carried type in the SAME ctx (idempotent for anything the body pass
    // already embedded) and map key → occurrence type, first occurrence wins
    // (same key ⇒ structurally identical embedded type).
    let op_ty_by_key: BTreeMap<String, IsaType> = {
        let n_type_params = ctx.type_params.len();
        let mut occs: Vec<(&str, &IsaType)> = Vec::new();
        collect_const_occurrences(rhs, &mut occs);
        let mut map = BTreeMap::new();
        for (cn, ct) in occs {
            if let Ok(ty_e) = ctx.embed_type(ct) {
                map.entry(const_param_key(cn, &ty_e))
                    .or_insert_with(|| ct.clone());
            }
        }
        // Undo any type-param registration performed only for key recovery: a
        // MATCHED occurrence's type was already fully embedded by the body pass
        // (that is what minted the param key), so truncation never drops a
        // binder the definition needs.
        ctx.type_params.truncate(n_type_params);
        map
    };
    // Partition the discovered term params into class operations (`const:<op>`) and
    // schematic formal arguments (the LHS `?arg` names). Any OTHER term param means
    // the body did not close to the expected shape — reject.
    let arg_keys: std::collections::BTreeSet<String> =
        arg_vars.iter().map(|(n, i)| format!("{n}.{i}")).collect();
    let mut ops: Vec<(String, IsaType)> = Vec::new();
    let mut op_params: Vec<Param> = Vec::new();
    let mut arg_param_by_key: std::collections::BTreeMap<String, Param> =
        std::collections::BTreeMap::new();
    for (key, p) in &ctx.term_params {
        if let Some(op) = const_key_name(key) {
            // A class operation: record (name, HOL type) for the consumer to
            // re-supply — the type of the EXACT body occurrence that minted this
            // (typed) key, so one op at two instantiations records each type
            // (the G3 lift). A key with NO literal-occurrence match was minted
            // at a SYNTHESIZED type (inside a pointwise-lift expansion or a
            // nested registered-combinator re-embed): a use-site could then only
            // re-supply it at a WRONG type — the historical name-based
            // first-occurrence fallback is provably wrong here, since every
            // literal occurrence's key IS in the map, so a miss means this param
            // is not any literal occurrence — so DECLINE registration and the
            // `_def` node keeps its recorded-proof path exactly as before (the
            // r17 POS/NEG/ctor_fold regression class).
            let op_ty = op_ty_by_key.get(key).cloned()?;
            ops.push((op.to_string(), op_ty));
            op_params.push(p.clone());
        } else if arg_keys.contains(key) {
            arg_param_by_key.insert(key.clone(), p.clone());
        } else {
            // An unexpected free term param (an unmapped non-method constant or a free
            // var that is not a formal argument) — the body did not close. Reject.
            return None;
        }
    }
    // NOTE (r17, G3 lift): a body that uses the SAME operation at TWO embedded
    // types is now REGISTERED — the two `const:<op>#<h₁>`/`const:<op>#<h₂>`
    // params each carry their own occurrence type in [`ops`] (via
    // `op_ty_by_key`), so a use-site re-embeds each at its correct
    // instantiation and the two supplies stay distinct. The r16 decline that
    // stood here (needed while `poly_inst_op_isa_ty` recovered only the
    // first-by-name occurrence type) is superseded.
    //
    // Order the schematic-argument params in the LHS application order (= the
    // constant's `fn_ty` arrow order), NOT the body's discovery order (the body may
    // mention `?n` before `?x`). This is essential: the def-const's residual argument
    // arrows must match `def_type = embed(fn_ty)` exactly, so the kernel accepts
    // `value : type`.
    let mut arg_params: Vec<Param> = Vec::with_capacity(arg_vars.len());
    for (n, i) in &arg_vars {
        let key = format!("{n}.{i}");
        arg_params.push(arg_param_by_key.remove(&key)?);
    }
    // Every schematic argument must have been discovered as a param (and no extra).
    if arg_params.len() != arg_vars.len() || !arg_param_by_key.is_empty() {
        return None;
    }
    // Abstract innermost-first: schematic args, then operations, then extra type
    // params, then `α` (outermost). `def_type` is the constant's type, which already
    // includes the argument arrows; abstracting the arg params over the VALUE (a
    // closed body) η-expands it to `λargs. body`, matching `def_type`'s arrows.
    for p in arg_params.iter().rev() {
        value = Expr::lam(
            BinderInfo::Default,
            p.ty.clone(),
            value.abstract_fvar(p.fvar),
        );
    }
    for p in op_params.iter().rev() {
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
    // Extra ground type constructors (every type param past the object `αᵢ`s).
    let extra_type_consts: Vec<String> = ctx
        .type_params
        .iter()
        .map(|(k, _)| k.clone())
        .filter(|k| !alpha_keys.contains(k))
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
    let decl = Declaration::Definition {
        name: Name::from_string(&def_name),
        level_params: Vec::new(),
        type_: def_type,
        value,
        is_reducible: true,
    };
    // For a PREDICATE-shaped definition — a type-class locale predicate
    // (`Thy.class.c`), a PLAIN locale predicate (`Orderings.ordering`,
    // `Finite_Set.folding_on`, `Groups_Big.comm_monoid_set` — no `.class.` in
    // the mangled name; the G2 conjunct-recording extension), or any other
    // `bool`-resulting definitional constant — record the flattened conjuncts
    // so the `C args ⟹ conjunctᵢ` projection and `conjuncts ⟹ C args`
    // construction nodes can discharge definitionally (the premise/conclusion's
    // def-const δ-unfolds to this conjunction; see `Ctx::prove_locale_projection`
    // / `prove_locale_construction`). A single-element list for a
    // non-conjunction predicate body — the "projection" is then the plain
    // definitional unfolding of the predicate, equally kernel-checked. Empty
    // for a non-predicate definition — the discharges never fire.
    let conjuncts =
        if is_locale_predicate_const(fn_name) || fn_result_is_bool(fn_ty, arg_vars.len()) {
            flatten_hol_conjuncts(rhs)
        } else {
            Vec::new()
        };
    Some((
        decl,
        PolyInstInfo {
            def_name,
            fn_ty: fn_ty.clone(),
            obj_tvars,
            extra_type_consts,
            ops,
            arg_vars,
            conjuncts,
            alias_of: None,
        },
    ))
}

/// Collect every `Const` occurrence `(name, carried HOL type)` in a HOL term,
/// depth-first, application function before argument (the embedder's traversal
/// order). Used by [`register_poly_inst_def`]'s G3 typed-key recovery to map each
/// `const:<n>#<hash>` op param to the type of the exact occurrence that minted it.
fn collect_const_occurrences<'t>(tm: &'t IsaTerm, out: &mut Vec<(&'t str, &'t IsaType)>) {
    match tm {
        IsaTerm::Const { n, t } => out.push((n, t)),
        IsaTerm::App { f, a } => {
            collect_const_occurrences(f, out);
            collect_const_occurrences(a, out);
        }
        IsaTerm::Abs { b, .. } => collect_const_occurrences(b, out),
        _ => {}
    }
}

/// Whether a HOL term mentions any overloaded class method constant
/// ([`is_overloaded_method_const`]) anywhere in its structure. Under the G2
/// gate-lift this no longer GATES registration — it SCOPES the widening
/// guards in [`register_poly_inst_def_guarded`]: a method-mentioning body is
/// the historical (pre-G2) registration class and registers unconditionally;
/// only the newly-admitted method-free class is subject to the alt-def and
/// dict-impl declines.
pub(crate) fn tm_mentions_overloaded_method(tm: &IsaTerm) -> bool {
    match tm {
        IsaTerm::Const { n, .. } => is_overloaded_method_const(n),
        IsaTerm::App { f, a } => {
            tm_mentions_overloaded_method(f) || tm_mentions_overloaded_method(a)
        }
        IsaTerm::Abs { b, .. } => tm_mentions_overloaded_method(b),
        _ => false,
    }
}

/// Whether a definitional constant's HOL type is **predicate-shaped**: peeling
/// the `nargs` leading `fun` arrows of its LHS application leaves `HOL.bool`.
/// This is the shape of every locale predicate — type-class (`Thy.class.c`) or
/// plain (`Orderings.ordering`, `Finite_Set.folding_on`) — and is what gates the
/// G2 conjunct recording in [`register_poly_inst_def`]: only a `bool`-resulting
/// constant can head the `C args ⟹ conjunctᵢ` projection / construction nodes.
fn fn_result_is_bool(fn_ty: &IsaType, nargs: usize) -> bool {
    let mut cur = fn_ty;
    for _ in 0..nargs {
        match cur {
            IsaType::Type { n, a } if n == "fun" && a.len() == 2 => cur = &a[1],
            _ => return false,
        }
    }
    matches!(cur, IsaType::Type { n, a } if (n == "HOL.bool" || n == "bool") && a.is_empty())
}

/// Flatten a **right-associated `HOL.conj` chain** into its leaf conjuncts, in
/// left-to-right order (`conj A (conj B C)` → `[A, B, C]`). A non-conjunction is
/// a single-element list (`[tm]`). Peels ONLY the RIGHT spine — the left operand
/// of each `HOL.conj` is taken as a leaf — matching the way a structured
/// type-class locale-predicate definition is spelled (`class.semiring ≡
/// class.ab_semigroup_add ∧ (class.semigroup_mult ∧ class.semiring_axioms)`), which
/// is exactly the nesting the impredicative `conj_def` projection descends. A body
/// whose left operand is itself a conjunction (not the class-predicate shape) simply
/// yields that operand as an opaque leaf — the projection match then fails to find
/// its target and the discharge declines (kernel never sees a wrong term).
pub(crate) fn flatten_hol_conjuncts(tm: &IsaTerm) -> Vec<IsaTerm> {
    if let IsaTerm::App { f, a: right } = tm {
        if let IsaTerm::App { f: head, a: left } = f.as_ref() {
            if matches!(head.as_ref(), IsaTerm::Const { n, .. } if n == "HOL.conj") {
                let mut out = vec![(**left).clone()];
                out.extend(flatten_hol_conjuncts(right));
                return out;
            }
        }
    }
    vec![tm.clone()]
}
