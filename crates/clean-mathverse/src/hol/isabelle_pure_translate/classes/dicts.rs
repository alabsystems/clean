// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Overloaded class-method dictionary-equation scanning and the type-variable
//! matching helpers for the Isabelle Pure translator (`DictEquation`,
//! `scan_method_dicts`, `dict_equation_from_symmetric`, `build_method_def`,
//! `term_app_spine`, `is_overloaded_method_const`, `subst_tvar`, `match_tvar`,
//! `sole_tvar`, `all_tvars`). Moved verbatim from the original single-file
//! `classes` module; behaviour is byte-identical.

use std::collections::BTreeMap;

use clean_kernel::expr::FVarId;
use clean_kernel::level::Level;
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Declaration, Environment, Expr};

use super::super::super::isabelle_pure::{IsaProof, IsaProvenTheorem, IsaTerm, IsaType};
use super::super::*;

/// One recovered **dictionary equation** for an overloaded class method, scanned
/// from a `Pure.symmetric % LHS % RHS %% …_dict` spine in a consumer proof (the
/// `…_dict` axiom is never a standalone node). `LHS` is the overloaded method
/// `c_class.method` (with its instantiated HOL type), `RHS` is the dictionary
/// form `c.method op₁ … opₙ`. See [`MethodDefInfo`].
#[derive(Clone, Debug)]
pub(crate) struct DictEquation {
    /// The overloaded method constant `c_class.method`.
    pub(crate) method_name: String,
    /// Its instantiated HOL type at the use-site (e.g. `num ⇒ 'a`).
    pub(crate) method_ty: IsaType,
    /// The dictionary-form implementation constant `c.method` (RHS head) + type.
    pub(crate) impl_const: (String, IsaType),
    /// The class operations the dictionary form is applied to, each `(name, type)`.
    pub(crate) ops: Vec<(String, IsaType)>,
}

/// Scan a proof tree for every `Pure.symmetric % LHS % RHS %% …_dict` spine and
/// return the recovered [`DictEquation`]s. The `…_dict` axiom unfolds an
/// overloaded class method to its dictionary form; it is exported only as a bare
/// `PAxm` *argument* to `Pure.symmetric` (whose two `%` term arguments ARE the
/// two sides of the equation), never standalone — so we recover the equation from
/// the enclosing `symmetric` spine. Used by the closure-replay driver's
/// method-registration pre-pass.
pub(crate) fn scan_method_dicts(proof: &IsaProof, out: &mut Vec<DictEquation>) {
    if let IsaProof::AppP { f, a } = proof {
        if let IsaProof::Axm { name, .. } = a.as_ref() {
            if name.ends_with("_dict") {
                if let Some(eq) = dict_equation_from_symmetric(f) {
                    out.push(eq);
                }
            }
        }
    }
    // Recurse into every sub-proof.
    match proof {
        IsaProof::AppP { f, a } => {
            scan_method_dicts(f, out);
            scan_method_dicts(a, out);
        }
        IsaProof::AppT { f, .. } | IsaProof::AbsP { b: f, .. } | IsaProof::Abst { b: f, .. } => {
            scan_method_dicts(f, out);
        }
        _ => {}
    }
}

/// The **dictionary-form implementation constant** name for an overloaded method
/// `<Theory>.<c>_class.<method>`: collapse the `_class.` class-marker segment to a
/// bare `.` (`Num.numeral_class.numeral` → `Num.numeral.numeral`,
/// `Power.power_class.power` → `Power.power.power`,
/// `Nat.semiring_1_class.of_nat` → `Nat.semiring_1.of_nat`,
/// `Rings.dvd_class.dvd` → `Rings.dvd.dvd`). This is Isabelle's stable naming
/// convention for the class→dictionary translation: the method's dictionary
/// implementation lives at the same theory/name path with the `_class` marker
/// dropped. Only the FIRST `_class.` (the class segment — the same one
/// [`is_overloaded_method_const`] keys on) is collapsed.
pub(crate) fn dict_impl_name(method: &str) -> String {
    method.replacen("_class.", ".", 1)
}

/// Scan a proof for **zproof-encoding** overloaded-method dictionary rewrites and
/// recover their [`DictEquation`]s, complementing the legacy-spine
/// [`scan_method_dicts`].
///
/// In the fully-typed (`zproof` / v3.2) export the `…_dict` unfolding is NOT an
/// explicit `Pure.symmetric % LHS % RHS` term-application spine — the
/// `Pure.symmetric` axiom carries its schematic operands in its `tminst` table
/// (as the derivation box's internal `Free` placeholders, not the equation sides),
/// so [`dict_equation_from_symmetric`] recovers nothing. The dictionary rewrite's
/// two goals are instead carried by the enclosing `Pure.equal_elim` axiom's `A`/`B`
/// schematic term arguments (its `tminst`): `A` is the dictionary-form goal, `B`
/// the overloaded-method-form goal (the theorem's own statement). We recover every
/// method dictionary equation by structurally diffing those two sides
/// ([`dict_equations_from_rewrite`]). Gated on the proof actually referencing a
/// `…_dict` axiom, so the `A`/`B` term diff runs only on genuine dictionary
/// consumers (never on an ordinary congruence's `equal_elim`).
pub(crate) fn scan_method_dicts_zproof(proof: &IsaProof, out: &mut Vec<DictEquation>) {
    let mut pairs: Vec<(&IsaTerm, &IsaTerm)> = Vec::new();
    let mut saw_dict = false;
    collect_equal_elim_pairs(proof, &mut pairs, &mut saw_dict);
    if !saw_dict {
        return;
    }
    for (a, b) in pairs {
        dict_equations_from_rewrite(a, b, out);
    }
}

/// Single-walk helper for [`scan_method_dicts_zproof`]: collect every
/// `Pure.equal_elim` axiom's `A`/`B` schematic term-argument pair (from its
/// `tminst`) and note whether any `…_dict` axiom leaf is present in the proof.
fn collect_equal_elim_pairs<'a>(
    proof: &'a IsaProof,
    pairs: &mut Vec<(&'a IsaTerm, &'a IsaTerm)>,
    saw_dict: &mut bool,
) {
    if let IsaProof::Axm { name, tminst, .. } = proof {
        if name.ends_with("_dict") {
            *saw_dict = true;
        } else if name == "Pure.equal_elim" {
            let a = tminst.iter().find(|e| e.n == "A").map(|e| &e.t);
            let b = tminst.iter().find(|e| e.n == "B").map(|e| &e.t);
            if let (Some(a), Some(b)) = (a, b) {
                pairs.push((a, b));
            }
        }
    }
    match proof {
        IsaProof::AppP { f, a } => {
            collect_equal_elim_pairs(f, pairs, saw_dict);
            collect_equal_elim_pairs(a, pairs, saw_dict);
        }
        IsaProof::AppT { f, .. } | IsaProof::AbsP { b: f, .. } | IsaProof::Abst { b: f, .. } => {
            collect_equal_elim_pairs(f, pairs, saw_dict);
        }
        _ => {}
    }
}

/// Diff a dictionary rewrite's two sides (`A`/`B` of a `Pure.equal_elim`, in
/// either order) to recover the [`DictEquation`]s it unfolds.
///
/// The two terms are structurally identical except at the rewrite sites, where one
/// side is a saturated overloaded-method application `c_class.method arg₁ … argₖ`
/// and the other is the parallel dictionary-form application
/// `c.method op₁ … opₙ arg₁ … argₖ` — the implementation constant `c.method`
/// ([`dict_impl_name`] of the method) applied to the class operations `op₁ … opₙ`
/// ahead of the method's own `k` arguments. We walk both terms in parallel; at each
/// rewrite site we emit `DictEquation { method_name, method_ty, impl_const, ops }`
/// (each `opᵢ` must be a bare `Const` — a compound operation is not a dictionary
/// op, so that site is skipped) and recurse on the trailing argument pairs; away
/// from a rewrite site we recurse structurally into the aligned children (equal-
/// arity applications, or a shared `Abs` binder body). Orientation-agnostic: either
/// side may hold the method / dictionary form. The recovered equation feeds
/// [`build_method_def`], and the kernel re-checks the registered `Definition`, so a
/// spurious recovery is rejected by `add_decl`, never registered wrong.
pub(crate) fn dict_equations_from_rewrite(x: &IsaTerm, y: &IsaTerm, out: &mut Vec<DictEquation>) {
    let (hx, ax) = term_app_spine(x);
    let (hy, ay) = term_app_spine(y);
    // A rewrite site: one side's head is an overloaded method `Const`, the other's
    // is that method's dictionary implementation `Const`. Try both orientations.
    for (mh, margs, ih, iargs) in [(hx, &ax, hy, &ay), (hy, &ay, hx, &ax)] {
        let (IsaTerm::Const { n: mname, t: mty }, IsaTerm::Const { n: iname, t: ity }) = (mh, ih)
        else {
            continue;
        };
        if !is_overloaded_method_const(mname)
            || *iname != dict_impl_name(mname)
            || iargs.len() < margs.len()
        {
            continue;
        }
        let n = iargs.len() - margs.len();
        let ops: Option<Vec<(String, IsaType)>> = iargs[..n]
            .iter()
            .map(|&op| match op {
                IsaTerm::Const { n, t } => Some((n.clone(), t.clone())),
                _ => None,
            })
            .collect();
        let Some(ops) = ops else {
            continue;
        };
        out.push(DictEquation {
            method_name: mname.clone(),
            method_ty: mty.clone(),
            impl_const: (iname.clone(), ity.clone()),
            ops,
        });
        // Recurse on the trailing (method arg, dictionary arg) pairs — the method's
        // own arguments may themselves carry a nested dictionary rewrite.
        for i in 0..margs.len() {
            dict_equations_from_rewrite(margs[i], iargs[n + i], out);
        }
        return;
    }
    // Not a rewrite site — recurse structurally into aligned subterms.
    if !ax.is_empty() && ax.len() == ay.len() {
        for (a, b) in ax.iter().zip(ay.iter()) {
            dict_equations_from_rewrite(a, b, out);
        }
    } else if let (IsaTerm::Abs { b: bx, .. }, IsaTerm::Abs { b: by, .. }) = (x, y) {
        dict_equations_from_rewrite(bx, by, out);
    }
}

/// Given the function side `f` of a `…_dict`-consuming `Pure.symmetric % LHS % RHS`
/// application, extract the dictionary equation. The spine is
/// `Pure.symmetric % LHS % RHS` (two `%` term arguments); `LHS` is the overloaded
/// method constant, `RHS` is `c.method op₁ … opₙ` (the dictionary form applied to
/// the class operations).
pub(crate) fn dict_equation_from_symmetric(f: &IsaProof) -> Option<DictEquation> {
    let (head, spine) = collect_spine(f);
    let IsaProof::Axm { name, .. } = head else {
        return None;
    };
    if name != "Pure.symmetric" && name != "HOL.sym" {
        return None;
    }
    let terms = spine_terms(&spine);
    let lhs = terms.first()?;
    let rhs = terms.get(1)?;
    // LHS: the overloaded method `c_class.method` (a bare `Const`).
    let IsaTerm::Const {
        n: method_name,
        t: method_ty,
    } = lhs
    else {
        return None;
    };
    if !is_overloaded_method_const(method_name) {
        return None;
    }
    // RHS: `c.method op₁ … opₙ` — peel the application spine to the dictionary
    // head and its operation arguments (each a `Const`).
    let (rhs_head, rhs_args) = term_app_spine(rhs);
    let IsaTerm::Const {
        n: impl_name,
        t: impl_ty,
    } = rhs_head
    else {
        return None;
    };
    let mut ops = Vec::new();
    for arg in rhs_args {
        let IsaTerm::Const { n, t } = arg else {
            return None;
        };
        ops.push((n.clone(), t.clone()));
    }
    Some(DictEquation {
        method_name: method_name.clone(),
        method_ty: (*method_ty).clone(),
        impl_const: (impl_name.clone(), (*impl_ty).clone()),
        ops,
    })
}

/// Extract a [`DictEquation`] directly from a **standalone `…_dict` axiom's own
/// statement** `Pure.eq (c_class.method) (c.method op₁ … opₙ)`.
///
/// Some overloaded methods (`Orderings.ord_class.max`/`min`/`Least`, …) export
/// their dictionary axiom as a *named top-level theorem* whose `prop` IS the
/// dictionary equation and whose recorded proof is the bare `…_dict` `PAxm` — as
/// opposed to the more common form recovered by [`dict_equation_from_symmetric`]
/// (where the `…_dict` axiom appears only inside a `Pure.symmetric` spine of a
/// *consumer* proof). The statement shape is identical to that spine's two `%`
/// term arguments, so we recover the same `DictEquation`: `Pure.eq`'s LHS is the
/// overloaded method `c_class.method`, its RHS is `c.method op₁ … opₙ` (each `opᵢ`
/// a `Const`). Returns `None` when the statement is not a `Pure.eq` of that shape
/// (e.g. the RHS is not a saturated application of a dictionary-form const to
/// bare-`Const` operations), so a non-dictionary `…_dict`-named node is left
/// unregistered exactly as before.
pub(crate) fn dict_equation_from_prop(prop: &IsaTerm) -> Option<DictEquation> {
    let (lhs, rhs) = pure_eq_parts(strip_leading_imps(prop))?;
    // LHS: the overloaded method `c_class.method` (a bare `Const`).
    let IsaTerm::Const {
        n: method_name,
        t: method_ty,
    } = lhs
    else {
        return None;
    };
    if !is_overloaded_method_const(method_name) {
        return None;
    }
    // RHS: `c.method op₁ … opₙ` — peel to the dictionary head + operation args.
    // `n = 0` (a bare `c_class.method ≡ c.method`, e.g. `of_nat_aux_dict`, whose
    // class context contributes no dictionary operations) is a legitimate
    // degenerate dictionary equation: the method def-const is then
    // `λ(α)(impl). impl`, which δ-unfolds to the bare impl const exactly as the
    // RHS embeds it. Safe here because this recovery only runs for `…_dict`-named
    // nodes ([`register_method_defs`]'s gate), so it never fires on an ordinary
    // equation; the kernel re-checks the registered `Definition` either way.
    let (rhs_head, rhs_args) = term_app_spine(rhs);
    let IsaTerm::Const {
        n: impl_name,
        t: impl_ty,
    } = rhs_head
    else {
        return None;
    };
    let mut ops = Vec::new();
    for arg in rhs_args {
        let IsaTerm::Const { n, t } = arg else {
            return None;
        };
        ops.push((n.clone(), t.clone()));
    }
    Some(DictEquation {
        method_name: method_name.clone(),
        method_ty: (*method_ty).clone(),
        impl_const: (impl_name.clone(), (*impl_ty).clone()),
        ops,
    })
}

/// Whether a constant name is an **overloaded class method** — a `…_class.<op>`
/// constant (the `_class`-suffixed *module* segment marks a class operation, as
/// in `Num.numeral_class.numeral`, `Groups.plus_class.plus`), as opposed to the
/// class *predicate* `…_class` itself or a structural/connective head.
pub(crate) fn is_overloaded_method_const(n: &str) -> bool {
    // A method is `<prefix>_class.<rest>`: the `_class` segment is followed by a
    // `.` and a non-empty method name. The bare predicate `…_class` has no
    // trailing `.rest`.
    if let Some(idx) = n.find("_class.") {
        // Exclude the class-def predicate forms and structural heads.
        let rest = &n[idx + "_class.".len()..];
        !rest.is_empty() && !is_class_op_structural(n) && connective_def_name(n).is_none()
    } else {
        false
    }
}

/// Peel a term's application spine into its head and the argument list (in
/// left-to-right order). `f a₁ … aₙ` → `(f, [a₁, …, aₙ])`.
pub(crate) fn term_app_spine(tm: &IsaTerm) -> (&IsaTerm, Vec<&IsaTerm>) {
    let mut args = Vec::new();
    let mut cur = tm;
    while let IsaTerm::App { f, a } = cur {
        args.push(a.as_ref());
        cur = f.as_ref();
    }
    args.reverse();
    (cur, args)
}

/// Build the clean polymorphic `Definition` for an overloaded class method from a
/// recovered [`DictEquation`] `c_class.method ≡ c.method op₁ … opₙ`.
///
/// The method's object type variables are every distinct `TVar` of its HOL type,
/// in first-occurrence order, each abstracted as a leading `(αᵢ : Type)` binder
/// (round-9: the big-operator methods carry TWO — `Groups_Big.…sum :
/// ('b⇒'a)⇒'b set⇒'a` quantifies the element type `'b` alongside the class type
/// `'a` — and the function-package methods carry NONE — `or_num : num⇒num⇒num`
/// is fully ground). The dictionary recursor `impl` and each operation `opᵢ` are
/// abstracted (in that order) as term binders, with each `'aᵢ` rewritten to its
/// binder `αᵢ` inside their types. The value is `impl op₁ … opₙ`:
///
/// `isabelle.method.<c> := λ(α₁…αₖ:Type)(impl:Timpl)(op₁:τ₁)…(opₙ:τₙ). impl op₁ … opₙ`.
///
/// Returns the [`Declaration`] and the [`MethodDefInfo`] consumers re-embed from,
/// or `None` when the equation does not yield a closed, well-formed definition
/// (e.g. a fixed `TFree` in the method type, or an operation type the embedder
/// rejects — the driver then simply does not register the method and the `…_dict`
/// axiom stays unmapped). The kernel re-checks `value : type`, so a malformed
/// definition is rejected, never registered wrong.
pub(crate) fn build_method_def(eq: &DictEquation) -> Option<(Declaration, MethodDefInfo)> {
    // The object type variables: every distinct `TVar` of the method's HOL type
    // (first-occurrence order; empty for a ground method).
    let obj_tvars = method_obj_tvars(&eq.method_ty)?;
    let mut ctx = Ctx::default();
    // Force-register the object types FIRST so they are the OUTERMOST type
    // binders in canonical order (matches `build_class_def`; a consumer applies
    // the def-const to the solved `αᵢ` first, in this same order).
    for tv in &obj_tvars {
        let _ = ctx.tvar_param(tv);
    }
    let tvar_keys: Vec<String> = obj_tvars
        .iter()
        .map(|tv| format!("{}.{}", tv.0, tv.1))
        .collect();
    // The method's residual result type `c.method op… : method_ty` — embed it
    // first so all GROUND type constructors it carries (`Num.num`, `Nat.nat`, …)
    // are discovered as type params and abstracted (otherwise they survive as free
    // `type_param` FVars → kernel `ContainsFreeVar`).
    let mut def_type = ctx.embed_type(&eq.method_ty).ok()?;
    // Build the body term `impl op₁ … opₙ` and embed it. The impl const and each
    // op const become `const:<n>` term params (and their types contribute any
    // further ground type params, again discovered into `ctx.type_params`).
    let impl_tm = IsaTerm::Const {
        n: eq.impl_const.0.clone(),
        t: eq.impl_const.1.clone(),
    };
    let mut body_tm = impl_tm;
    for (n, t) in &eq.ops {
        body_tm = IsaTerm::App {
            f: Box::new(body_tm),
            a: Box::new(IsaTerm::Const {
                n: n.clone(),
                t: t.clone(),
            }),
        };
    }
    let mut binders: Vec<Binder> = Vec::new();
    let mut value = ctx.embed_term(&body_tm, &mut binders).ok()?;
    // Abstract the discovered parameters: term params (impl, ops) innermost, then
    // the type params outermost — mirroring `build_class_def`'s final wrap.
    for (_key, p) in ctx.term_params.iter().rev() {
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
    // The extra fixed ground-type params (every type param past the object
    // `αᵢ`s), in the order the definition abstracts them, so a consumer supplies
    // them right after the `αᵢ`s and before `impl`/operations.
    let extra_type_consts: Vec<String> = ctx
        .type_params
        .iter()
        .map(|(k, _)| k.clone())
        .filter(|k| !tvar_keys.contains(k))
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
    let def_name = method_def_name(&eq.method_name);
    let decl = Declaration::Definition {
        name: Name::from_string(&def_name),
        level_params: Vec::new(),
        type_: def_type,
        value,
        is_reducible: true,
    };
    Some((
        decl,
        MethodDefInfo {
            def_name,
            method_ty: eq.method_ty.clone(),
            obj_tvars,
            impl_const: eq.impl_const.clone(),
            ops: eq.ops.clone(),
            extra_type_consts,
        },
    ))
}

/// Every distinct `TVar` of an overloaded method's HOL type, in
/// **first-occurrence order** — the canonical order [`build_method_def`]
/// abstracts the leading `(αᵢ : Type)` binders and [`Ctx::embed_method_use`]
/// applies the solved instantiations. Empty for a fully **ground** method
/// (`or_num : num ⇒ num ⇒ num` — the function-package methods of a class whose
/// operations the method does not mention). `None` when any **fixed** type
/// variable (`TFree`) is present: a polymorphic def-const cannot abstract a
/// fixed type, so the method is left unregistered exactly as before.
pub(crate) fn method_obj_tvars(ty: &IsaType) -> Option<Vec<(String, i64)>> {
    fn go(ty: &IsaType, found: &mut Vec<(String, i64)>, ok: &mut bool) {
        match ty {
            IsaType::TVar { n, i } => {
                if !found.iter().any(|(fn_, fi)| fn_ == n && *fi == *i) {
                    found.push((n.clone(), *i));
                }
            }
            IsaType::TFree { .. } => *ok = false,
            IsaType::Type { a, .. } => {
                for t in a {
                    go(t, found, ok);
                }
            }
        }
    }
    let mut found = Vec::new();
    let mut ok = true;
    go(ty, &mut found, &mut ok);
    ok.then_some(found)
}

/// **Simultaneously** substitute the type variables of `subs` in `ty` (each
/// `((name, index), replacement)` pair applied in one pass — never sequentially,
/// so a swap instantiation `'b ↦ 'a, 'a ↦ 'b` cannot capture the just-inserted
/// occurrences). The multi-tvar generalization of [`subst_tvar`], used to
/// instantiate a [`MethodDefInfo`]'s stored impl/operation types at a use-site's
/// solved object types.
pub(crate) fn subst_tvars(ty: &IsaType, subs: &[((String, i64), IsaType)]) -> IsaType {
    match ty {
        IsaType::TVar { n, i } => subs
            .iter()
            .find(|((sn, si), _)| sn == n && *si == *i)
            .map_or_else(|| ty.clone(), |(_, repl)| repl.clone()),
        IsaType::TFree { .. } => ty.clone(),
        IsaType::Type { n, a } => IsaType::Type {
            n: n.clone(),
            a: a.iter().map(|t| subst_tvars(t, subs)).collect(),
        },
    }
}

/// Solve **all** the object type variables `tvs` simultaneously by matching a
/// stored HOL type `pat` against a use-site instantiated type `inst`. Returns the
/// solved instantiations in `tvs` order, or `None` on a structural mismatch, an
/// inconsistent double solution, or a `tv` that never occurs in `pat`.
///
/// The multi-tvar generalization of [`match_tvar`]: that helper matches ONE
/// variable at a time and demands every *other* `TVar` of `pat` match an
/// identically-named `TVar` in `inst` — which fails the moment a second object
/// variable is genuinely instantiated (`sum : ('b⇒'a)⇒'b set⇒'a` used at
/// `('b⇒nat)⇒'b set⇒nat`). Here every listed variable binds (consistently), and
/// only non-listed `TVar`s (none, when `tvs` covers the pattern) must match
/// verbatim.
pub(crate) fn match_tvars(
    pat: &IsaType,
    inst: &IsaType,
    tvs: &[(String, i64)],
) -> Option<Vec<((String, i64), IsaType)>> {
    fn go(
        pat: &IsaType,
        inst: &IsaType,
        tvs: &[(String, i64)],
        sol: &mut BTreeMap<(String, i64), IsaType>,
    ) -> bool {
        match pat {
            IsaType::TVar { n, i } if tvs.iter().any(|(tn, ti)| tn == n && *ti == *i) => {
                let key = (n.clone(), *i);
                match sol.get(&key) {
                    Some(prev) => prev == inst,
                    None => {
                        sol.insert(key, inst.clone());
                        true
                    }
                }
            }
            IsaType::TVar { n, i } => {
                matches!(inst, IsaType::TVar { n: m, i: j } if m == n && j == i)
            }
            IsaType::TFree { n } => matches!(inst, IsaType::TFree { n: m } if m == n),
            IsaType::Type { n, a } => match inst {
                IsaType::Type { n: m, a: b } if m == n && a.len() == b.len() => {
                    a.iter().zip(b).all(|(p, q)| go(p, q, tvs, sol))
                }
                _ => false,
            },
        }
    }
    let mut sol = BTreeMap::new();
    if !go(pat, inst, tvs, &mut sol) {
        return None;
    }
    tvs.iter()
        .map(|tv| sol.get(tv).map(|t| (tv.clone(), t.clone())))
        .collect()
}

/// Substitute every occurrence of the type variable `tv` in `ty` with `repl`.
/// Used to instantiate a [`MethodDefInfo`]'s stored operation types (which
/// reference the object `TVar`) at a use-site's concrete object type.
pub(crate) fn subst_tvar(ty: &IsaType, tv: &(String, i64), repl: &IsaType) -> IsaType {
    match ty {
        IsaType::TVar { n, i } if *n == tv.0 && *i == tv.1 => repl.clone(),
        IsaType::TVar { .. } | IsaType::TFree { .. } => ty.clone(),
        IsaType::Type { n, a } => IsaType::Type {
            n: n.clone(),
            a: a.iter().map(|t| subst_tvar(t, tv, repl)).collect(),
        },
    }
}

/// Solve the object type variable `tv` by matching a stored (`'a`-carrying) HOL
/// type `pat` against a use-site instantiated type `inst`. Returns the type `'a`
/// was instantiated to, or `None` on a structural mismatch. (A first-order
/// one-variable match — every occurrence of `tv` in `pat` must map to the same
/// `inst` sub-type.)
pub(crate) fn match_tvar(pat: &IsaType, inst: &IsaType, tv: &(String, i64)) -> Option<IsaType> {
    let mut sol: Option<IsaType> = None;
    pub(crate) fn go(
        pat: &IsaType,
        inst: &IsaType,
        tv: &(String, i64),
        sol: &mut Option<IsaType>,
    ) -> bool {
        match pat {
            IsaType::TVar { n, i } if *n == tv.0 && *i == tv.1 => match sol {
                Some(prev) => prev == inst,
                None => {
                    *sol = Some(inst.clone());
                    true
                }
            },
            IsaType::TVar { n, i } => {
                matches!(inst, IsaType::TVar { n: m, i: j } if m == n && j == i)
            }
            IsaType::TFree { n } => matches!(inst, IsaType::TFree { n: m } if m == n),
            IsaType::Type { n, a } => match inst {
                IsaType::Type { n: m, a: b } if m == n && a.len() == b.len() => {
                    a.iter().zip(b).all(|(p, q)| go(p, q, tv, sol))
                }
                _ => false,
            },
        }
    }
    if go(pat, inst, tv, &mut sol) {
        sol
    } else {
        None
    }
}

/// The single `TVar` `(name, index)` appearing in a HOL type, or `None` if there
/// is not exactly one distinct type variable (the object type of an overloaded
/// method is always its sole type variable).
pub(crate) fn sole_tvar(ty: &IsaType) -> Option<(String, i64)> {
    let mut found: Option<(String, i64)> = None;
    pub(crate) fn go(ty: &IsaType, found: &mut Option<(String, i64)>, ok: &mut bool) {
        match ty {
            IsaType::TVar { n, i } => match found {
                Some((fn_, fi)) if fn_ == n && *fi == *i => {}
                Some(_) => *ok = false,
                None => *found = Some((n.clone(), *i)),
            },
            IsaType::TFree { .. } => *ok = false,
            IsaType::Type { a, .. } => {
                for t in a {
                    go(t, found, ok);
                }
            }
        }
    }
    let mut ok = true;
    go(ty, &mut found, &mut ok);
    if ok {
        found
    } else {
        None
    }
}

/// Every distinct `TVar` `(name, index)` appearing in a HOL type, in
/// **first-occurrence (canonical) order**, or `None` if there is **no** type
/// variable at all or any **fixed** type variable (`TFree`) is present.
///
/// This generalizes [`sole_tvar`] to the multi-type-variable list functions
/// (`map : ('a⇒'b)⇒'a list⇒'b list`, `foldr/foldl : ('b⇒'a⇒'b)⇒'b⇒'a list⇒'b`,
/// `zip : 'a list⇒'b list⇒('a×'b) list`, `those : 'a option list⇒'a list option`).
/// The order is the order in which a left-to-right walk of the function's HOL
/// type first encounters each variable — the SAME order in which
/// [`Ctx::embed_type`] discovers the `TVar`s into `type_params`, so the
/// registered `Definition`'s leading `λ(α₁:Type)…(αₙ:Type)` binders and the
/// use-site type-argument application stay aligned. (`TFree` would be a *fixed*
/// (non-schematic) type, which a polymorphic def-const cannot abstract — so the
/// lever is scoped out for safety, exactly as the single-`TVar` path was.)
pub(crate) fn all_tvars(ty: &IsaType) -> Option<Vec<(String, i64)>> {
    let mut found: Vec<(String, i64)> = Vec::new();
    pub(crate) fn go(ty: &IsaType, found: &mut Vec<(String, i64)>, ok: &mut bool) {
        match ty {
            IsaType::TVar { n, i } => {
                if !found.iter().any(|(fn_, fi)| fn_ == n && *fi == *i) {
                    found.push((n.clone(), *i));
                }
            }
            IsaType::TFree { .. } => *ok = false,
            IsaType::Type { a, .. } => {
                for t in a {
                    go(t, found, ok);
                }
            }
        }
    }
    let mut ok = true;
    go(ty, &mut found, &mut ok);
    if ok && !found.is_empty() {
        Some(found)
    } else {
        None
    }
}
