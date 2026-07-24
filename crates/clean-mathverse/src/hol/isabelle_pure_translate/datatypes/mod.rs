// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Datatype embedding: Nat/Num/List/Option/Sum/Prod/Int recursors, constructors,
//! `case`/`rec` mappings, the BNF combinators, and the core `embed_term` dispatch,
//! plus the instance-op / poly-inst / list-fn definition registries.
//!
//! Part of the [`super`] Pure proof-term → clean kernel translator; split
//! out of the original single-file module purely for readability — the code is
//! moved verbatim, the behaviour is byte-identical.

use std::collections::BTreeMap;

use clean_kernel::expr::FVarId;
use clean_kernel::level::Level;
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Declaration, Environment, Expr};

use super::super::isabelle_pure::{IsaProof, IsaProvenTheorem, IsaTerm, IsaType};
use super::*;

/// A registered **monomorphic instance operation** — the *ground-type* analogue
/// of [`MethodDefInfo`]. The recursive arithmetic definitions on the concrete
/// datatypes `Nat.nat` / `Num.num` (`Nat.plus_nat_def`, `Nat.times_nat_def`,
/// `Nat.One_nat_def`, `Num.times_num_def`, …) are exported as `Pure.eq`
/// definitional axioms whose LHS is an overloaded class operation **instantiated
/// at a closed ground type** (`Groups.plus_class.plus : nat ⇒ nat ⇒ nat`,
/// `Groups.one_class.one : nat`) and whose RHS is a closed `rec_nat`/`rec_num`
/// fold (which, now that `Nat.nat`/`Num.num` map to real clean inductives and
/// `rec_nat`/`rec_num` map to the kernel recursors, embeds to a closed
/// monomorphic clean term).
///
/// Because the LHS type is fully ground (no type variable), there is nothing to
/// generalise — the operation is genuinely monomorphic. Registering it as the
/// clean `Definition`
/// `isabelle.inst.<c_class.method>@<ground-type-key> := <embed RHS>`
/// makes the `…_def` axiom *genuinely reflexive*: `embed(LHS)` δ-unfolds to the
/// registered body (`embed RHS`), so the definitional equation is dischargeable
/// by `Eq.refl`, kernel-accepted **iff** the two sides are definitionally equal —
/// never a tautology. Downstream nat/num-arithmetic theorems that use the same
/// operation at the same ground type unfold consistently (they embed the *same*
/// def-const), so they stay sound and faithful.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct InstanceOpInfo {
    /// Kernel declaration name of the registered clean `Definition`
    /// (`isabelle.inst.<c_class.method>@<ground-type-key>`).
    pub(crate) def_name: String,
}

/// Registry of monomorphic ground-type instance operations registered so far,
/// keyed by `(overloaded-method-constant-name, ground-type-key)` — the
/// [`isa_ground_type_key`] of the operation's instantiated HOL type. Threaded
/// read-only through [`translate_theorem`] so `embed_term` rewrites every
/// occurrence of a registered instance operation (at the matching ground type)
/// to its def-const, making the recursive arithmetic `…_def` axioms reflexive
/// and keeping every nat/num use-site consistent.
pub type InstanceOpRegistry = BTreeMap<(String, String), InstanceOpInfo>;

/// A registered **polymorphic instance operation** — the type-class-method-using
/// generalisation of the ground [`InstanceOpInfo`]. Some HOL constants are defined
/// by a `_def` axiom whose LHS is a *bare polymorphic* constant `c : τ['a]` (one
/// object type variable `'a`, NOT an overloaded `_class.` method itself, so neither
/// the ground [`register_instance_op_def`] nor the dictionary [`build_method_def`]
/// fires) and whose body uses **overloaded class operations over `'a`**
/// (`Power.power_class.power`, `Fields.inverse_class.inverse`, `Orderings.ord_class.less_eq`,
/// …). The canonical example is `Int.power_int`:
/// ```text
/// power_int ?x ?n ≡ if 0 ≤ ?n then ?x ^ nat ?n else inverse ?x ^ nat (- ?n)
/// ```
/// (exported η-expanded with schematic argument variables `?x : 'a`, `?n : int`).
///
/// Such a body does not close as a *ground* instance op (`'a` is free) nor as a
/// *list function* (it has leftover overloaded-method `const:` params, not just the
/// element type). The faithful image abstracts BOTH the object type `α` AND each
/// distinct overloaded class operation the body references, plus the η-expanded
/// schematic argument variables, as binders of a clean polymorphic `Definition`
/// `isabelle.polyinst.<c> := λ(α:Type)(op₁ … opₘ)(arg₁ … argₖ). <embed body>`.
/// A consumer applies the def-const to `α` then each operation (re-embedded at the
/// use-site instantiation as the same global `const:<op>` param — the identical
/// keying [`embed_method_use`]/[`embed_class_membership`] use), leaving the argument
/// binders as the function's residual arrows (the consumer's own application fills
/// them). So `embed(c)` δ-unfolds to the registered body and the `_def` axiom is
/// **genuinely reflexive** (kernel-accepted by `Eq.refl` iff the two sides are
/// definitionally equal — never a `B=B` tautology). Gated on `instance_unfold` and
/// the close-or-skip / kernel `add_decl` guards, so strictly additive.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct PolyInstInfo {
    /// Kernel declaration name of the registered clean `Definition`
    /// (`isabelle.polyinst.<c>`).
    pub(crate) def_name: String,
    /// The constant's own HOL type as seen at registration (referencing the object
    /// type variables). Unified against a use-site's instantiated type to solve
    /// every `'aᵢ := Tᵢ`, each then embedded as a leading def-const type argument.
    pub(crate) fn_ty: IsaType,
    /// The object type variables of the constant — every distinct `TVar` of
    /// `fn_ty`, in first-occurrence order ([`method_obj_tvars`]; k ≥ 0, empty for
    /// a ground constant — the G1 lift over the historical sole-`TVar` gate). The
    /// clean `Definition` abstracts each as a leading `(αᵢ : Type)` binder, in
    /// this order.
    pub(crate) obj_tvars: Vec<(String, i64)>,
    /// Names of the **extra fixed ground type constructors** the body/type references
    /// beyond the object type `α` (e.g. `Int.int` for `power_int`'s `int` argument).
    /// `embed_type` abstracts each such base type as its own leading `Π(_:Type)`
    /// binder; a consumer supplies them right after `α`, before the operations.
    pub(crate) extra_type_consts: Vec<String>,
    /// The overloaded class operations the body references (`(operation-constant-name,
    /// the HOL type of the EXACT body occurrence that minted its typed `const:` key —
    /// the G3 lift, so one op at two type instantiations records BOTH types)`), in
    /// the abstraction order. A consumer applies the def-const to each (re-embedded
    /// at the use-site instantiation as the same global `const:<n>#<hash>` param),
    /// so every occurrence shares one head and argument order.
    pub(crate) ops: Vec<(String, IsaType)>,
    /// The constant's **formal argument** schematic variables (`(name, index)`), in
    /// the LHS application order (`class.semiring ?plus ?times` → `[(plus,i),(times,j)]`).
    /// Used by the locale-predicate PROJECTION discharge to substitute these formals
    /// with a use-site's actual operands before matching / embedding the body's
    /// conjuncts.
    pub(crate) arg_vars: Vec<(String, i64)>,
    /// For a **locale predicate** (`Thy.class.c`) whose body is a right-associated
    /// `HOL.conj` chain (`class.order ≡ class.preorder ∧ class.order_axioms`,
    /// `class.semiring ≡ class.ab_semigroup_add ∧ (class.semigroup_mult ∧
    /// class.semiring_axioms)`), the FLATTENED list of conjuncts (each a HOL term
    /// over [`Self::arg_vars`] and the ops). Empty for a non-conjunction body. This
    /// is what lets the `class.C args ⟹ class.subpredᵢ subargs` locale-predicate
    /// projection nodes discharge DEFINITIONALLY — the premise's def-const δ-unfolds
    /// to this conjunction, so the conclusion is the i-th conjunct, extracted by the
    /// impredicative `conj_def` projection (see `Ctx::prove_locale_projection`)
    /// rather than the recorded `atomize_conj`+`Pure.combination` congruence chain
    /// (which the deeper 3-way nestings do not reconstruct).
    pub(crate) conjuncts: Vec<IsaTerm>,
    /// **G4 (instance-link ALIAS entry):** `Some(method)` when this registry entry
    /// records an Isabelle instance-implementation constant
    /// (`Enum.enum_fun_inst.enum_fun`, `Filter.ord_filter_inst.less_eq_filter`, …)
    /// registered from its overloading LINK axiom
    /// `<c>_class.<m> @ τ ≡ <impl> @ τ` (see `inst_link_axiom`). The impl const IS
    /// the class operation at that instance — the two denote the identical element
    /// — so a use-site re-embeds the impl as the METHOD at the occurrence type
    /// through the full `Const` dispatch (the registry-driven generalisation of the
    /// hand lists `fun_impl_const_class_op` / `bool_impl_const_class_op` /
    /// `ground_impl_const_class_op`). An alias entry mints NO kernel `Definition`
    /// (`def_name` is a marker, never a real declaration) and records no
    /// tvars/ops/args/conjuncts, so every other registry consumer (projection,
    /// conjunct extraction, `const_key_fill`) declines it naturally. `None` for
    /// every ordinary poly-inst / method-inst registration. Defaults to `None` on
    /// deserialization of a pre-G4 snapshot record.
    #[serde(default)]
    pub(crate) alias_of: Option<String>,
}

/// Registry of polymorphic instance operations registered so far (`c` constant name
/// → its [`PolyInstInfo`]). Threaded read-only through [`translate_theorem`] so
/// `embed_term` rewrites every occurrence of a registered polymorphic instance op to
/// its def-const applied to the use-site object type and operations, making the
/// `_def` axiom reflexive and keeping every use-site consistent.
pub type PolyInstRegistry = BTreeMap<String, PolyInstInfo>;

/// The kernel declaration name of the clean `Definition` registered for a
/// polymorphic instance operation `c` (`isabelle.polyinst.<c>`).
pub(crate) fn poly_inst_def_name(fn_const: &str) -> String {
    format!("isabelle.polyinst.{fn_const}")
}

/// The kernel declaration name of the clean `Definition` registered for a
/// monomorphic ground-type instance operation `c_class.method` at ground type
/// key `k` (`isabelle.inst.<c_class.method>@<k>`).
pub(crate) fn instance_op_def_name(method_const: &str, type_key: &str) -> String {
    format!("isabelle.inst.{method_const}@{type_key}")
}

/// **G4:** the [`PolyInstRegistry`] key of a **method-at-constructor instance
/// definition** — an overloaded method `m` defined at a type-constructor
/// instance whose canonical shape key is `k` ([`isa_shape_key`]). The `\t`
/// separator cannot occur in an Isabelle constant name, so a composite key can
/// never collide with (or be found by) a plain constant-name lookup — every
/// existing name-keyed registry consumer is untouched by construction. Lookup
/// is by [`Ctx::find_method_inst`], which range-scans the `"{m}\t"` prefix and
/// unifies each candidate's registered type against the use-site type.
pub(crate) fn method_inst_registry_key(method_const: &str, shape_key: &str) -> String {
    format!("{method_const}\t{shape_key}")
}

/// **G4:** the kernel declaration name of the clean `Definition` registered for
/// an overloaded method `m` at the type-constructor instance with shape key `k`
/// (`isabelle.instk.<m>@<k>`).
pub(crate) fn method_inst_def_name(method_const: &str, shape_key: &str) -> String {
    format!("isabelle.instk.{method_const}@{shape_key}")
}

/// A stable, canonical shape key for a HOL type **modulo schematic-variable
/// renaming**: the same pre-order constructor serialisation as
/// [`isa_ground_type_key`], with every `TVar` replaced by its first-occurrence
/// index (`?0`, `?1`, …). Two exports of one instance type that differ only in
/// tvar spelling (`'a`/`'b` vs `'aa`/`'ba`) therefore produce the SAME key —
/// the G4 registries key an instance by (method, this shape), so the LINK
/// axiom's recorded instance type anchors the body `_def`'s registration
/// regardless of variable naming. `TFree`s keep their names (a fixed type
/// variable is not schematic and never unifies at a use-site anyway).
pub(crate) fn isa_shape_key(ty: &IsaType) -> String {
    fn go(ty: &IsaType, s: &mut String, seen: &mut Vec<(String, i64)>) {
        match ty {
            IsaType::Type { n, a } => {
                s.push_str(n);
                if !a.is_empty() {
                    s.push('<');
                    for (i, t) in a.iter().enumerate() {
                        if i != 0 {
                            s.push(',');
                        }
                        go(t, s, seen);
                    }
                    s.push('>');
                }
            }
            IsaType::TVar { n, i } => {
                let idx = match seen.iter().position(|(sn, si)| sn == n && si == i) {
                    Some(k) => k,
                    None => {
                        seen.push((n.clone(), *i));
                        seen.len() - 1
                    }
                };
                s.push('?');
                s.push_str(&idx.to_string());
            }
            IsaType::TFree { n } => {
                s.push('\'');
                s.push_str(n);
            }
        }
    }
    let mut s = String::new();
    let mut seen: Vec<(String, i64)> = Vec::new();
    go(ty, &mut s, &mut seen);
    s
}

/// A registered **plain polymorphic list (datatype) function** — the
/// element-polymorphic analogue of [`InstanceOpInfo`]. HOL's recursive list
/// functions (`List.append`, `List.rev`, `List.map`, `List.length`, …) are
/// exported as `Pure.eq` definitional axioms (`List.append_def`, `List.rev_def`,
/// `List.list.map_def`, …) of the shape
/// `OFCLASS('a, type_class) ⟹ c = (λ…. List.list.rec_list … )` — a *plain*
/// recursive function over `'a list` parameterised **only** by the element type
/// `'a` (no class dictionary, unlike [`MethodDefInfo`]; and polymorphic, unlike
/// the ground [`InstanceOpInfo`]). Now that `List.list 'a` maps to clean's
/// `List 'a` and `List.list.rec_list`/`case_list` to wrappers over `List.rec`,
/// the body embeds to a closed term modulo the single type parameter `α`.
///
/// Registering it as the clean polymorphic `Definition`
/// `isabelle.listfn.<c> := λ(α : Type). <embed RHS>`
/// (with `α` the sole leading binder) makes the `…_def` axiom **genuinely
/// reflexive**: `embed(c)` at a use-site element type `T` δ-unfolds to the
/// registered body specialised at `T`, so the definitional equation is
/// dischargeable by `Eq.refl`, kernel-accepted **iff** the two sides are
/// definitionally equal — never a tautology. Downstream list lemmas that use the
/// same function unfold consistently (they embed the *same* def-const applied to
/// their own element type), so they stay sound and faithful.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct ListFnInfo {
    /// Kernel declaration name of the registered clean `Definition`
    /// (`isabelle.listfn.<c>`).
    pub(crate) def_name: String,
    /// The function's own HOL type as seen at registration (referencing the
    /// object type variables `'a`, `'b`, …). Unified against a use-site's
    /// instantiated type to solve each `'aᵢ := Tᵢ`, which are then embedded and
    /// supplied as the def-const's leading type arguments (in `obj_tvars` order)
    /// so the function re-embeds at the use-site element types.
    pub(crate) fn_ty: IsaType,
    /// The object (element) type variables `'a`, `'b`, … of the list function —
    /// the `(name, index)` of each schematic `TVar` the body is parameterised by,
    /// in the **canonical order** the clean `Definition` abstracts them (the same
    /// first-occurrence order [`Ctx::embed_type`] discovers them into
    /// `type_params`). The `Definition` abstracts them as the leading
    /// `λ(α₁:Type)…(αₙ:Type)` binders; a use-site solves and applies them in this
    /// order. (Single-element for `append`/`rev`/`map₁`/…; two-element for
    /// `map`/`foldr`/`foldl`/`zip`/`those`.)
    pub(crate) obj_tvars: Vec<(String, i64)>,
}

/// Registry of plain polymorphic list-datatype functions registered so far
/// (function-constant name → its [`ListFnInfo`]). Threaded read-only through
/// [`translate_theorem`] so `embed_term` rewrites every occurrence of a
/// registered list function to its def-const applied to the use-site element
/// type, making the recursive list-function `…_def` axioms reflexive and keeping
/// every list use-site consistent.
pub type ListFnRegistry = BTreeMap<String, ListFnInfo>;

/// The kernel declaration name of the clean `Definition` registered for a plain
/// polymorphic list function `c` (`isabelle.listfn.<c>`).
pub(crate) fn list_fn_def_name(fn_const: &str) -> String {
    format!("isabelle.listfn.{fn_const}")
}

/// Whether a HOL type is **fully ground** — built only from concrete `Type`
/// constructors, with no `TVar` (schematic) and no `TFree` (fixed) type variable
/// anywhere. The recursive-arithmetic instance-operation definitions are exactly
/// the ones whose LHS operation is instantiated at such a closed type (e.g.
/// `nat ⇒ nat ⇒ nat`), so they are genuinely monomorphic and need no
/// polymorphic-definition machinery.
pub(crate) fn is_ground_type(ty: &IsaType) -> bool {
    match ty {
        IsaType::TVar { .. } | IsaType::TFree { .. } => false,
        IsaType::Type { a, .. } => a.iter().all(is_ground_type),
    }
}

/// A stable, collision-free string key for a **ground** HOL type, used as the
/// per-instance suffix of an [`InstanceOpInfo`]'s def-const name and as the
/// registry key. A pre-order serialisation of the type's constructor names and
/// arities; only ever called on [`is_ground_type`] types (no variables to
/// represent), so the key is a total function of the type.
pub(crate) fn isa_ground_type_key(ty: &IsaType) -> String {
    let mut s = String::new();
    pub(crate) fn go(ty: &IsaType, s: &mut String) {
        match ty {
            IsaType::Type { n, a } => {
                s.push_str(n);
                if !a.is_empty() {
                    s.push('<');
                    for (i, t) in a.iter().enumerate() {
                        if i != 0 {
                            s.push(',');
                        }
                        go(t, s);
                    }
                    s.push('>');
                }
            }
            // Unreachable for ground types; kept total for safety.
            IsaType::TVar { n, i } => {
                s.push('?');
                s.push_str(n);
                s.push('.');
                s.push_str(&i.to_string());
            }
            IsaType::TFree { n } => {
                s.push('\'');
                s.push_str(n);
            }
        }
    }
    go(ty, &mut s);
    s
}

mod bnf;
mod bnf2;
mod embed_use;
mod int_prod_sum;
mod list;
mod nat_num;
mod registers;
mod registers2;
mod registers3;

pub use registers::*;
pub use registers2::*;
pub use registers3::*;
