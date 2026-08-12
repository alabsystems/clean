// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended derive handlers with advanced strategies, validation, and custom registration.
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#![cfg_attr(not(test), allow(dead_code))]
use crate::derive::{DeriveError, DeriveHandler};
use crate::derive_ext_handlers2::{
    project_struct_field, resolve_field_instance, single_ctor_struct, CtorInfo2, DerivedDecl2,
    ExtDeriveHandler2,
};
use crate::derive_handlers::{
    lookup_constructors, mk_bool, mk_nat, wrap_param_lambdas, wrap_param_pis,
};
use clean_kernel::{
    BinderInfo, ConstructorVal, Declaration, Environment, Expr, ExprKind, InductiveVal, Level, Name,
};
use std::collections::{HashMap, HashSet};
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
#[non_exhaustive]
pub(crate) enum DeriveDiagnosticSeverity {
    #[default]
    Error,
    Warning,
    Info,
    Hint,
}
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub(crate) struct DeriveDiagnostic {
    pub(crate) severity: DeriveDiagnosticSeverity,
    pub(crate) class_name: String,
    pub(crate) message: String,
    pub(crate) suggestions: Vec<String>,
}
impl DeriveDiagnostic {
    #[must_use]
    pub(crate) fn new(
        severity: DeriveDiagnosticSeverity,
        class_name: &str,
        message: impl Into<String>,
        suggestions: Vec<String>,
    ) -> Self {
        Self {
            severity,
            class_name: class_name.to_owned(),
            message: message.into(),
            suggestions,
        }
    }
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct PreconditionSpec {
    allow_reflexive: bool,
    allow_recursive: bool,
    min_ctors: usize,
    max_ctors: Option<usize>,
    require_nullary_ctors: bool,
    require_single_field_wrapper: bool,
    max_fields_per_ctor: Option<usize>,
}
impl PreconditionSpec {
    #[must_use]
    fn for_class(class_name: &str) -> Self {
        match class_name {
            "Fintype" => Self {
                allow_reflexive: false,
                allow_recursive: false,
                min_ctors: 1,
                max_ctors: Some(512),
                require_nullary_ctors: true,
                require_single_field_wrapper: false,
                max_fields_per_ctor: Some(0),
            },
            "Countable" => Self {
                allow_reflexive: false,
                allow_recursive: false,
                min_ctors: 1,
                max_ctors: Some(1024),
                require_nullary_ctors: false,
                require_single_field_wrapper: false,
                max_fields_per_ctor: Some(16),
            },
            "ToExpr" => Self {
                allow_reflexive: false,
                allow_recursive: false,
                min_ctors: 1,
                max_ctors: Some(256),
                require_nullary_ctors: false,
                require_single_field_wrapper: false,
                max_fields_per_ctor: Some(16),
            },
            "OfScientific" => Self {
                allow_reflexive: false,
                allow_recursive: false,
                min_ctors: 1,
                max_ctors: Some(1),
                require_nullary_ctors: false,
                require_single_field_wrapper: true,
                max_fields_per_ctor: Some(1),
            },
            _ => Self {
                allow_reflexive: false,
                allow_recursive: false,
                min_ctors: 1,
                max_ctors: None,
                require_nullary_ctors: false,
                require_single_field_wrapper: false,
                max_fields_per_ctor: None,
            },
        }
    }
}
pub(crate) struct DerivePreconditionChecker;
impl DerivePreconditionChecker {
    #[must_use]
    pub(crate) fn diagnostics(
        class_name: &str,
        type_name: &Name,
        _type_expr: &Expr,
        ctors: &[CtorInfo2],
    ) -> Vec<DeriveDiagnostic> {
        let spec = PreconditionSpec::for_class(class_name);
        let mut out = Vec::new();
        if ctors.len() < spec.min_ctors {
            out.push(Self::diag(
                DeriveDiagnosticSeverity::Error,
                class_name,
                format!(
                    "`{type_name}` must have at least {} constructor(s)",
                    spec.min_ctors
                ),
            ));
        }
        if let Some(max_ctors) = spec.max_ctors {
            if ctors.len() > max_ctors {
                out.push(Self::diag(
                    DeriveDiagnosticSeverity::Error,
                    class_name,
                    format!("`{type_name}` exceeds the supported constructor count of {max_ctors}"),
                ));
            }
        }
        if !spec.allow_recursive && ctors.iter().any(|ctor| ctor.is_recursive) {
            out.push(Self::diag(
                DeriveDiagnosticSeverity::Error,
                class_name,
                format!("recursive constructors are not supported for `{type_name}`"),
            ));
        }
        if !spec.allow_reflexive
            && ctors
                .iter()
                .any(|ctor| has_direct_self_field(type_name, ctor))
        {
            out.push(Self::diag(
                DeriveDiagnosticSeverity::Error,
                class_name,
                format!("reflexive fields are not supported for `{type_name}`"),
            ));
        }
        if spec.require_nullary_ctors && ctors.iter().any(|ctor| !ctor.fields.is_empty()) {
            out.push(Self::diag(
                DeriveDiagnosticSeverity::Error,
                class_name,
                format!("`{type_name}` must be an enum-like inductive with nullary constructors"),
            ));
        }
        if spec.require_single_field_wrapper
            && ctors.first().is_none_or(|ctor| ctor.fields.len() != 1)
        {
            out.push(Self::diag(
                DeriveDiagnosticSeverity::Error,
                class_name,
                format!("`{type_name}` must be a single-constructor, single-field wrapper"),
            ));
        }
        if let Some(max_fields) = spec.max_fields_per_ctor {
            if ctors.iter().any(|ctor| ctor.fields.len() > max_fields) {
                out.push(Self::diag(
                    DeriveDiagnosticSeverity::Error,
                    class_name,
                    format!("constructors of `{type_name}` exceed the supported field count of {max_fields}"),
                ));
            }
        }
        if class_name == "Fintype" && ctors.len() > 64 {
            out.push(Self::diag(
                DeriveDiagnosticSeverity::Warning,
                class_name,
                format!(
                    "`{type_name}` has many constructors; generated enumeration may be unwieldy"
                ),
            ));
        }
        if class_name == "ToExpr" && ctors.len() > 32 {
            out.push(Self::diag(
                DeriveDiagnosticSeverity::Info,
                class_name,
                format!("`{type_name}` may benefit from a hand-written `ToExpr` encoder"),
            ));
        }
        out
    }

    pub(crate) fn check(
        class_name: &str,
        type_name: &Name,
        type_expr: &Expr,
        ctors: &[CtorInfo2],
    ) -> Result<(), DeriveError> {
        if let Some(diag) = Self::diagnostics(class_name, type_name, type_expr, ctors)
            .into_iter()
            .find(|diag| diag.severity == DeriveDiagnosticSeverity::Error)
        {
            return Err(DeriveError::Unsupported {
                class_name: diag.class_name,
                ind_name: type_name.to_string(),
                reason: diag.message,
            });
        }
        Ok(())
    }

    #[must_use]
    fn diag(
        severity: DeriveDiagnosticSeverity,
        class_name: &str,
        message: String,
    ) -> DeriveDiagnostic {
        DeriveDiagnostic::new(
            severity,
            class_name,
            message,
            manual_suggestions(class_name),
        )
    }
}
#[must_use]
fn inst_name(class_name: &str, type_name: &Name) -> Name {
    Name::from_string(&format!("inst{class_name}{type_name}"))
}
fn mk_applied_type(type_name: &Name, num_params: u32) -> Expr {
    let base = Expr::const_(type_name.clone(), vec![]);
    if num_params == 0 {
        return base;
    }
    Expr::apps(
        base,
        (0..num_params).rev().map(Expr::bvar).collect::<Vec<_>>(),
    )
}
fn mk_inst_ty(type_name: &Name, class_name: &str, num_params: u32) -> Expr {
    Expr::app(
        Expr::const_str(class_name),
        mk_applied_type(type_name, num_params),
    )
}
fn wrap_params(value: Expr, type_: Expr, num_params: u32) -> (Expr, Expr) {
    (
        wrap_param_lambdas(value, num_params),
        wrap_param_pis(type_, num_params),
    )
}
#[must_use]
fn mk_inst_decl(
    inst_class_name: &str,
    type_class_name: &str,
    type_name: &Name,
    num_params: u32,
    value: Expr,
) -> DerivedDecl2 {
    let (value, type_) = wrap_params(
        value,
        mk_inst_ty(type_name, type_class_name, num_params),
        num_params,
    );
    DerivedDecl2 {
        name: inst_name(inst_class_name, type_name),
        type_,
        value,
        is_instance: true,
    }
}
#[must_use]
fn manual_suggestions(class_name: &str) -> Vec<String> {
    match class_name {
        "Fintype" => {
            vec!["Define an explicit finite carrier and membership proof by hand.".to_owned()]
        }
        "Countable" => vec!["Provide manual encode/decode functions to and from `Nat`.".to_owned()],
        "ToExpr" => {
            vec!["Encode each constructor explicitly using `Lean.Expr` builders.".to_owned()]
        }
        "OfScientific" => {
            vec!["Define a wrapper-specific `ofScientific` conversion manually.".to_owned()]
        }
        _ => vec![format!(
            "Implement `{class_name}` manually for this inductive."
        )],
    }
}
fn has_direct_self_field(type_name: &Name, ctor: &CtorInfo2) -> bool {
    ctor.fields
        .iter()
        .any(|(_, ty)| head_const_name(ty).is_some_and(|head| head == type_name))
}
fn head_const_name(expr: &Expr) -> Option<&Name> {
    match expr.kind() {
        ExprKind::Const(name, _) => Some(name),
        ExprKind::App(fun, _) => head_const_name(fun),
        _ => None,
    }
}
pub(crate) struct DeriveFintype;
impl ExtDeriveHandler2 for DeriveFintype {
    fn class_name(&self) -> &str {
        "Fintype"
    }

    fn derive(
        &self,
        _env: &Environment,
        tn: &Name,
        te: &Expr,
        ctors: &[CtorInfo2],
        np: u32,
        _lp: &[Name],
    ) -> Result<Vec<DerivedDecl2>, DeriveError> {
        // Shape gate: `Fintype` only admits a nullary enum (≥1 constructor, all
        // arity 0, no type parameters, non-recursive). This errors (no sorry,
        // no panic) for ctor-with-fields / recursive / parametric / infinite
        // shapes — exactly the PreconditionSpec for "Fintype".
        DerivePreconditionChecker::check(self.class_name(), tn, te, ctors)?;

        // Build the GENUINE instance: a real `Finset` carrier plus a real
        // completeness proof, kernel-checkable and sorry-free. The deriver
        // ERRORS rather than ever emitting a sorry-backed `Fintype`.
        let value =
            fintype_nullary_enum_value(tn, ctors).ok_or_else(|| DeriveError::Unsupported {
                class_name: self.class_name().to_owned(),
                ind_name: tn.to_string(),
                reason: "Fintype can only be derived for a nullary enum (all \
                         constructors arity 0, no type parameters, non-recursive); \
                         this shape is unsupported"
                    .to_owned(),
            })?;
        Ok(vec![mk_inst_decl("Fintype", "Fintype", tn, np, value)])
    }
}

/// Build the genuine, sorry-free `Fintype E` instance value for a nullary enum
/// `E` (constructors `c₀ … c_{n-1}`, all arity 0, `np == 0`, non-recursive):
///
/// ```text
/// @Fintype.mk E
///   (elems    : Finset E)
///   (complete : ∀ (a : E), Finset.Mem a elems)
/// ```
///
/// where:
/// - `elems = Finset.cons c₀ (… (Finset.cons c_{n-1} Finset.empty h_{n-1}) …) h₀`.
///   Each `hᵢ : ¬ Finset.Mem cᵢ restᵢ` def-eq-reduces (through `Subtype.val` and
///   the `Multiset`/`List` quotient) to `¬ List.Mem cᵢ [c_{i+1}, …]`, which is
///   discharged by nesting `List.not_mem_cons_iff.mpr ⟨cᵢ ≠ cⱼ, …⟩` down to
///   `List.not_mem_nil`. Each distinctness `cᵢ ≠ cⱼ` is `fun h => E.noConfusion h`
///   (the type's own no-confusion principle); no domain axiom is used.
/// - `complete = fun a => @E.rec.{0} (fun a => Finset.Mem a elems) m₀ … m_{n-1} a`
///   eliminating into `Prop`, where each minor `mᵢ : Finset.Mem cᵢ elems` is a
///   `Finset.mem_cons_self` / `Finset.mem_cons_of_mem` chain.
///
/// Returns `None` for any shape outside the nullary-enum set, so the caller
/// turns that into a hard derive error (never a sorry-backed instance).
fn fintype_nullary_enum_value(tn: &Name, ctors: &[CtorInfo2]) -> Option<Expr> {
    if ctors.is_empty() || ctors.iter().any(|c| !c.fields.is_empty() || c.is_recursive) {
        return None;
    }

    let lvl0 = Level::zero();
    let lvl1 = Level::succ(Level::zero());
    let ind_ty = Expr::const_(tn.clone(), vec![]); // E : Type 0 = Sort 1

    // Level-less / level-0 constants (E lives in Type 0).
    let finset_empty = Expr::app(
        Expr::const_(Name::from_string("Finset.empty"), vec![lvl0.clone()]),
        ind_ty.clone(),
    );
    let finset_cons = Expr::const_(Name::from_string("Finset.cons"), vec![lvl0.clone()]);
    let finset_mem = Expr::const_(Name::from_string("Finset.Mem"), vec![lvl0.clone()]);
    let _mem_empty = Expr::const_(Name::from_string("Finset.mem_empty"), vec![lvl0.clone()]);
    let mem_self = Expr::const_(
        Name::from_string("Finset.mem_cons_self"),
        vec![lvl0.clone()],
    );
    let mem_of_mem = Expr::const_(
        Name::from_string("Finset.mem_cons_of_mem"),
        vec![lvl0.clone()],
    );
    let list_cons = Expr::const_(Name::from_string("List.cons"), vec![lvl0.clone()]);
    let list_nil = Expr::app(
        Expr::const_(Name::from_string("List.nil"), vec![lvl0.clone()]),
        ind_ty.clone(),
    );
    let list_mem = Expr::const_(Name::from_string("List.Mem"), vec![lvl0.clone()]);
    let not_mem_cons_iff = Expr::const_(
        Name::from_string("List.not_mem_cons_iff"),
        vec![lvl0.clone()],
    );
    let not_mem_nil = Expr::const_(Name::from_string("List.not_mem_nil"), vec![lvl0.clone()]);
    let no_conf = Expr::const_(
        Name::from_string(&format!("{tn}.noConfusion")),
        vec![lvl0.clone()],
    );
    let eq_c = Expr::const_(Name::from_string("Eq"), vec![lvl1.clone()]);
    let not_c = Expr::const_str("Not");
    let and_c = Expr::const_str("And");
    let and_intro = Expr::const_str("And.intro");
    let iff_mpr = Expr::const_str("Iff.mpr");
    let false_c = Expr::const_str("False");

    let ctor_const = |c: &CtorInfo2| Expr::const_(c.name.clone(), vec![]);
    let fmem = |x: Expr, f: Expr| Expr::apps(finset_mem.clone(), [ind_ty.clone(), x, f]);
    let lmem = |x: Expr, l: Expr| Expr::apps(list_mem.clone(), [ind_ty.clone(), x, l]);
    let lcons = |h: Expr, t: Expr| Expr::apps(list_cons.clone(), [ind_ty.clone(), h, t]);
    let fcons =
        |a: Expr, f: Expr, h: Expr| Expr::apps(finset_cons.clone(), [ind_ty.clone(), a, f, h]);
    let not = |p: Expr| Expr::app(not_c.clone(), p);
    let and_ = |p: Expr, q: Expr| Expr::apps(and_c.clone(), [p, q]);
    let eq_e = |l: Expr, r: Expr| Expr::apps(eq_c.clone(), [ind_ty.clone(), l, r]);
    // ne a b : ¬(a = b)  =  fun (h : a = b) => @E.noConfusion.{0} False a b h
    let ne = |a: Expr, b: Expr| {
        let body = Expr::apps(
            no_conf.clone(),
            [false_c.clone(), a.clone(), b.clone(), Expr::bvar(0)],
        );
        Expr::lam(BinderInfo::Default, eq_e(a, b), body)
    };

    // The underlying list of the suffix `rest_i = [c_{i+1}, …, c_{n-1}]`.
    let suffix_list = |start: usize| -> Expr {
        let mut acc = list_nil.clone();
        for c in ctors[start..].iter().rev() {
            acc = lcons(ctor_const(c), acc);
        }
        acc
    };

    // not_mem_suffix(i, start): ¬ List.Mem cᵢ [c_start, …, c_{n-1}].
    // Recursion over the suffix using `List.not_mem_cons_iff.mpr ⟨ne, inner⟩`,
    // bottoming out at `List.not_mem_nil cᵢ`.
    fn build_not_mem_list(
        i: usize,
        start: usize,
        ctors: &[CtorInfo2],
        ctor_const: &dyn Fn(&CtorInfo2) -> Expr,
        suffix_list: &dyn Fn(usize) -> Expr,
        lmem: &dyn Fn(Expr, Expr) -> Expr,
        not: &dyn Fn(Expr) -> Expr,
        and_: &dyn Fn(Expr, Expr) -> Expr,
        ne: &dyn Fn(Expr, Expr) -> Expr,
        eq_e: &dyn Fn(Expr, Expr) -> Expr,
        ind_ty: &Expr,
        not_mem_cons_iff: &Expr,
        not_mem_nil: &Expr,
        iff_mpr: &Expr,
        and_intro: &Expr,
        lcons: &dyn Fn(Expr, Expr) -> Expr,
    ) -> Expr {
        let ci = ctor_const(&ctors[i]);
        if start >= ctors.len() {
            // ¬ List.Mem cᵢ []  =  @List.not_mem_nil E cᵢ
            return Expr::apps(not_mem_nil.clone(), [ind_ty.clone(), ci]);
        }
        let cj = ctor_const(&ctors[start]);
        let tail = suffix_list(start + 1);
        // ne_ij : ¬(cᵢ = cⱼ)
        let ne_ij = ne(ci.clone(), cj.clone());
        let ne_ty = not(eq_e(ci.clone(), cj.clone()));
        // inner : ¬ List.Mem cᵢ tail
        let inner = build_not_mem_list(
            i,
            start + 1,
            ctors,
            ctor_const,
            suffix_list,
            lmem,
            not,
            and_,
            ne,
            eq_e,
            ind_ty,
            not_mem_cons_iff,
            not_mem_nil,
            iff_mpr,
            and_intro,
            lcons,
        );
        let inner_ty = not(lmem(ci.clone(), tail.clone()));
        // conj : (¬(cᵢ=cⱼ)) ∧ (¬ List.Mem cᵢ tail)
        let conj = Expr::apps(
            and_intro.clone(),
            [ne_ty.clone(), inner_ty.clone(), ne_ij, inner],
        );
        // iff : ¬ Mem cᵢ (cⱼ::tail) ↔ (¬(cᵢ=cⱼ) ∧ ¬Mem cᵢ tail)
        let iff_t = Expr::apps(
            not_mem_cons_iff.clone(),
            [ind_ty.clone(), ci.clone(), cj.clone(), tail.clone()],
        );
        let lhs = not(lmem(ci, lcons(cj, tail)));
        let rhs = and_(ne_ty, inner_ty);
        // Iff.mpr lhs rhs iff_t conj : ¬ Mem cᵢ (cⱼ::tail)
        Expr::apps(iff_mpr.clone(), [lhs, rhs, iff_t, conj])
    }

    // Build the `elems` cons-chain right-to-left, recording each suffix Finset
    // and the `¬mem` proof used to extend it (needed by the completeness minors).
    // `finsets[k]` = the Finset of constructors `c_k … c_{n-1}`.
    let n = ctors.len();
    let mut finsets: Vec<Expr> = vec![finset_empty.clone(); n + 1];
    let _hproofs: Vec<Expr> = Vec::with_capacity(n); // hproofs[i] used to cons cᵢ onto finsets[i+1]
                                                     // placeholder fill; we build from the back.
    finsets[n] = finset_empty.clone();
    // Build h proofs and finsets going from i = n-1 down to 0.
    let mut h_by_index: Vec<Option<Expr>> = vec![None; n];
    for i in (0..n).rev() {
        let ci = ctor_const(&ctors[i]);
        // hᵢ : ¬ Finset.Mem cᵢ finsets[i+1]  (def-eq ¬ List.Mem cᵢ [c_{i+1}…])
        let h_i = build_not_mem_list(
            i,
            i + 1,
            ctors,
            &ctor_const,
            &suffix_list,
            &lmem,
            &not,
            &and_,
            &ne,
            &eq_e,
            &ind_ty,
            &not_mem_cons_iff,
            &not_mem_nil,
            &iff_mpr,
            &and_intro,
            &lcons,
        );
        finsets[i] = fcons(ci, finsets[i + 1].clone(), h_i.clone());
        h_by_index[i] = Some(h_i);
    }
    let elems = finsets[0].clone();

    // complete = fun (a : E) => @E.rec.{0} (fun a => Finset.Mem a elems) m₀ … m_{n-1} a
    // Minor mᵢ : Finset.Mem cᵢ elems.
    // elems = cons c₀ (cons c₁ … finsets[1]) h₀, so:
    //   m₀ = mem_cons_self c₀ finsets[1] h₀
    //   mᵢ = mem_cons_of_mem cᵢ c₀ finsets[1] h₀ ( mem_cons_of_mem cᵢ c₁ finsets[2] h₁ ( … (mem_cons_self cᵢ finsets[i+1] hᵢ)))
    // i.e. peel `i` outer conses with mem_cons_of_mem, then mem_cons_self at depth i.
    let mut minors: Vec<Expr> = Vec::with_capacity(n);
    for i in 0..n {
        let ci = ctor_const(&ctors[i]);
        // base: cᵢ ∈ finsets[i] via mem_cons_self (finsets[i] = cons cᵢ finsets[i+1] hᵢ)
        let h_i = h_by_index[i].clone()?;
        let mut acc = Expr::apps(
            mem_self.clone(),
            [ind_ty.clone(), ci.clone(), finsets[i + 1].clone(), h_i],
        );
        // climb outward: for k = i-1 down to 0, cᵢ ∈ finsets[k] = cons c_k finsets[k+1] h_k
        for k in (0..i).rev() {
            let ck = ctor_const(&ctors[k]);
            let h_k = h_by_index[k].clone()?;
            acc = Expr::apps(
                mem_of_mem.clone(),
                [
                    ind_ty.clone(),
                    ci.clone(),
                    ck,
                    finsets[k + 1].clone(),
                    h_k,
                    acc,
                ],
            );
        }
        minors.push(acc);
    }

    // motive : fun (a : E) => Finset.Mem a elems  (eliminating into Prop = Sort 0)
    let motive = Expr::lam(
        BinderInfo::Default,
        ind_ty.clone(),
        fmem(Expr::bvar(0), elems.clone()),
    );
    let rec_const = Expr::const_(Name::from_string(&format!("{tn}.rec")), vec![lvl0.clone()]);
    let mut rec_app = Expr::app(rec_const, motive);
    for m in &minors {
        rec_app = Expr::app(rec_app, m.clone());
    }
    // major premise = the lambda-bound `a` (bvar 0).
    rec_app = Expr::app(rec_app, Expr::bvar(0));
    let complete = Expr::lam(BinderInfo::Default, ind_ty.clone(), rec_app);

    // @Fintype.mk.{0} E elems complete : Fintype E
    let fintype_mk = Expr::const_(Name::from_string("Fintype.mk"), vec![lvl0.clone()]);
    Some(Expr::apps(fintype_mk, [ind_ty, elems, complete]))
}
pub(crate) struct DeriveCountable;
impl ExtDeriveHandler2 for DeriveCountable {
    fn class_name(&self) -> &str {
        "Countable"
    }

    fn derive(
        &self,
        _env: &Environment,
        tn: &Name,
        te: &Expr,
        ctors: &[CtorInfo2],
        np: u32,
        _lp: &[Name],
    ) -> Result<Vec<DerivedDecl2>, DeriveError> {
        DerivePreconditionChecker::check(self.class_name(), tn, te, ctors)?;

        // Try to synthesize a genuine, sorry-free `Countable` instance for the
        // single-constructor `Nat`-wrapper shape (`W.mk : Nat → W`, no type
        // parameters). The encode-to-`Nat` injection is the field projection
        // `W.mk n ↦ n`, built from the wrapper recursor. Every other shape
        // fails with an explicit unsupported-shape error.
        let Some(value) = countable_nat_wrapper_value(tn, ctors, np) else {
            return Err(DeriveError::Unsupported {
                class_name: "Countable".to_owned(),
                ind_name: tn.to_string(),
                reason: "only a monomorphic single-field Nat wrapper has a complete \
                         Countable construction"
                    .to_owned(),
            });
        };
        Ok(vec![mk_inst_decl("Countable", "Countable", tn, np, value)])
    }
}

/// Try to build a sorry-free `Countable` instance value for a single-field
/// `Nat`-wrapper inductive.
///
/// The countability witness Clean's derive handler produces is the
/// encode-to-`Nat` injection (the *data* witnessing countability), modelled by
/// the class
///
/// ```text
/// class Countable (α : Type u) where
///   encode : α → Nat
/// ```
///
/// For a single-constructor wrapper `W.mk : Nat → W` with no type parameters,
/// the encode is the field projection `W.mk n ↦ n`, built from the wrapper
/// recursor at motive universe `1` (`Nat : Type = Sort 1`) with the constant
/// motive `fun _ => Nat` and the identity minor premise `fun (n : Nat) => n`:
///
/// ```text
/// @Countable.mk W (fun (w : W) => @W.rec.{1} (fun _ => Nat) (fun (n : Nat) => n) w)
/// ```
///
/// This is a closed, kernel-checkable term that introduces no
/// `sorryAx`/axioms.
///
/// Returns `None` for shapes outside this supported set (parametric inductives,
/// multi-constructor enums, or wrappers whose single field is not exactly
/// `Nat`), so the caller reports a typed unsupported-shape error. Restricting to a
/// `Nat` field keeps the encode unambiguously the identity: a non-`Nat` field
/// would need a `Countable`/encode instance for the field type, which is not
/// resolvable structurally here. The real Lean `Countable` is `Prop`-valued and
/// additionally demands an injectivity *proof*; that obligation is not
/// constructively dischargeable here, so we deliberately model only the
/// encode-data witness we can fully kernel-check and reject every other shape.
fn countable_nat_wrapper_value(tn: &Name, ctors: &[CtorInfo2], np: u32) -> Option<Expr> {
    if np != 0 || ctors.len() != 1 {
        return None;
    }
    let ctor = ctors.first()?;
    if ctor.is_recursive || ctor.fields.len() != 1 {
        return None;
    }
    let (_field_name, field_ty) = ctor.fields.first()?;
    // Only a `Nat`-typed field has a canonical encode (the identity) that needs
    // no `Countable` instance for the field type.
    if head_const_name(field_ty).is_none_or(|head| head.to_string() != "Nat") {
        return None;
    }

    let wrapper_ty = Expr::const_(tn.clone(), vec![]);

    // motive: fun (_ : W) => Nat  (a constant function into `Nat`).
    let motive = Expr::lam(BinderInfo::Default, wrapper_ty.clone(), mk_nat());

    // Minor premise for `W.mk : Nat → W`: fun (n : Nat) => n  (the identity,
    // i.e. the field projection). `n` is the single bound binder, so `bvar 0`.
    let minor = Expr::lam(BinderInfo::Default, mk_nat(), Expr::bvar(0));

    // @W.rec.{1} motive minor w. `Nat : Type = Sort 1`, so the motive eliminates
    // into `Sort 1`.
    let rec_const = Expr::const_(
        Name::from_string(&format!("{tn}.rec")),
        vec![Level::succ(Level::zero())],
    );
    // The major premise is the lambda-bound argument `w` (bvar 0).
    let rec_app = Expr::apps(rec_const, [motive, minor, Expr::bvar(0)]);
    let encode_fn = Expr::lam(BinderInfo::Default, wrapper_ty.clone(), rec_app);

    // @Countable.mk W encode. The `α` binder is implicit; the kernel accepts it
    // positionally, so we supply `W` explicitly (mirroring `DeriveOfScientific`
    // / `DeriveToExpr` / `DeriveHashable2`).
    Some(Expr::apps(
        Expr::const_str("Countable.mk"),
        [wrapper_ty, encode_fn],
    ))
}
pub(crate) struct DeriveToExpr;
impl ExtDeriveHandler2 for DeriveToExpr {
    fn class_name(&self) -> &str {
        "ToExpr"
    }

    fn derive(
        &self,
        env: &Environment,
        tn: &Name,
        te: &Expr,
        ctors: &[CtorInfo2],
        np: u32,
        _lp: &[Name],
    ) -> Result<Vec<DerivedDecl2>, DeriveError> {
        DerivePreconditionChecker::check(self.class_name(), tn, te, ctors)?;

        // Single-ctor struct shape (1 ctor, np == 0, >= 1 field, non-recursive):
        // reflect `C f0 .. fn` as the applied constant
        // `mkAppN (Lean.Expr.const ``C []) #[toExpr f0, .., toExpr fn]`, resolving
        // each field type's own `Lean.ToExpr` instance from the environment.
        // Closed and kernel-checkable; no proof obligation. If any field instance
        // is unresolvable the helper returns `None` and we fall through to the
        // nullary-enum path or a typed error below.
        if let Some(value) = to_expr_struct_value(env, tn, ctors, np) {
            return Ok(vec![mk_inst_decl("ToExpr", "Lean.ToExpr", tn, np, value)]);
        }

        // Try to synthesize a genuine, sorry-free `Lean.ToExpr` instance for the
        // nullary-enum shape (>= 1 constructors, every constructor of arity 0,
        // no type parameters). Every other shape fails closed.
        match to_expr_nullary_enum_value(tn, ctors, np) {
            Some(value) => Ok(vec![mk_inst_decl("ToExpr", "Lean.ToExpr", tn, np, value)]),
            None => Err(DeriveError::Unsupported {
                class_name: "ToExpr".to_owned(),
                ind_name: tn.to_string(),
                reason: "no closed structural ToExpr construction is available for this shape"
                    .to_owned(),
            }),
        }
    }
}

/// Reflect a kernel [`Name`] into the `Lean.Name` term that names it.
///
/// Mirrors `Name::from_string`'s component split: numeric components become
/// `Lean.Name.num`, every other component becomes `Lean.Name.str`, rooted at
/// `Lean.Name.anonymous`. The result is a closed term (no bound variables, no
/// `sorry`), suitable as the `declName` argument of `Lean.Expr.const`.
fn reflect_lean_name(name: &Name) -> Expr {
    let rendered = name.to_string();
    let mut acc = Expr::const_str("Lean.Name.anonymous");
    for part in rendered.split('.') {
        acc = if let Ok(n) = part.parse::<u64>() {
            Expr::apps(Expr::const_str("Lean.Name.num"), [acc, Expr::nat_lit(n)])
        } else {
            Expr::apps(Expr::const_str("Lean.Name.str"), [acc, Expr::str_lit(part)])
        };
    }
    acc
}

/// Build the reflected `Lean.Expr` value naming a nullary constructor or the
/// enum type itself: `@Lean.Expr.const <reflected-name> (@List.nil Lean.Level)`.
fn reflect_expr_const(name: &Name) -> Expr {
    let empty_levels = Expr::app(
        Expr::const_str_levels("List.nil", vec![Level::zero()]),
        Expr::const_str("Lean.Level"),
    );
    Expr::apps(
        Expr::const_str("Lean.Expr.const"),
        [reflect_lean_name(name), empty_levels],
    )
}

/// Try to build a sorry-free `Lean.ToExpr` instance value for the nullary-enum
/// shape.
///
/// The real Lean class is
///
/// ```text
/// class ToExpr (α : Type u) where
///   toExpr     : α → Lean.Expr
///   toTypeExpr : Lean.Expr
/// ```
///
/// For an inductive `E` with constructors `c₁ … cₙ`, all of arity 0 and no type
/// parameters, `toExpr` maps each constructor `cᵢ` to the reflected
/// `Lean.Expr.const ``cᵢ []`, and `toTypeExpr` is `Lean.Expr.const ``E []`:
///
/// ```text
/// @Lean.ToExpr.mk E
///   (fun (x : E) => @E.rec.{1} (fun _ => Lean.Expr) <c₁-expr> … <cₙ-expr> x)
///   (Lean.Expr.const ``E [])
/// ```
///
/// The match is the inductive recursor `E.rec` instantiated at motive universe
/// `1` (`Lean.Expr : Type`), with the constant motive `fun _ => Lean.Expr` and
/// one minor premise per constructor. This is a closed, kernel-checkable term
/// that introduces no `sorryAx`/axioms.
///
/// Returns `None` for shapes outside this supported set (parametric inductives,
/// zero constructors, or any constructor with fields), so the caller reports a
/// typed `Unsupported` error without generating a declaration.
fn to_expr_nullary_enum_value(tn: &Name, ctors: &[CtorInfo2], np: u32) -> Option<Expr> {
    if np != 0 || ctors.is_empty() {
        return None;
    }
    if ctors.iter().any(|c| !c.fields.is_empty() || c.is_recursive) {
        return None;
    }

    // motive: fun (_ : E) => Lean.Expr  (a constant function into `Lean.Expr`).
    let ind_ty = Expr::const_(tn.clone(), vec![]);
    let motive = Expr::lam(
        BinderInfo::Default,
        ind_ty.clone(),
        Expr::const_str("Lean.Expr"),
    );

    // @E.rec.{1} motive <minor c₁> … <minor cₙ> applied to the bound major `x`.
    // `Lean.Expr : Type = Sort 1`, so the motive eliminates into `Sort 1`.
    let rec_const = Expr::const_(
        Name::from_string(&format!("{tn}.rec")),
        vec![Level::succ(Level::zero())],
    );
    let mut rec_app = Expr::app(rec_const, motive);
    for ctor in ctors {
        rec_app = Expr::app(rec_app, reflect_expr_const(&ctor.name));
    }
    // The major premise is the lambda-bound argument `x` (bvar 0).
    rec_app = Expr::app(rec_app, Expr::bvar(0));

    let to_expr_fn = Expr::lam(BinderInfo::Default, ind_ty.clone(), rec_app);
    let to_type_expr = reflect_expr_const(tn);

    // @Lean.ToExpr.mk E toExpr toTypeExpr. The `α` binder is implicit; the
    // kernel accepts it positionally, so we supply `E` explicitly (mirroring
    // `DeriveOfScientific`/`DeriveHashable2`).
    Some(Expr::apps(
        Expr::const_str("Lean.ToExpr.mk"),
        [ind_ty, to_expr_fn, to_type_expr],
    ))
}

/// Try to build a sorry-free `Lean.ToExpr` instance value for the single-ctor
/// struct shape (1 constructor, `np == 0`, `>= 1` field, non-recursive).
///
/// The real Lean class carries `toExpr : α → Lean.Expr` and
/// `toTypeExpr : Lean.Expr`. For a struct `S` with the sole constructor
/// `C : F0 → … → F_{n-1} → S`, `toExpr` reflects an applied constructor:
///
/// ```text
/// @Lean.ToExpr.mk S
///   (fun (x : S) =>
///      Lean.Expr.app (… Lean.Expr.app (Lean.Expr.const ``C [])
///        (@Lean.ToExpr.toExpr F0 inst0 x.0) …)
///        (@Lean.ToExpr.toExpr F_{n-1} inst_{n-1} x.{n-1}))
///   (Lean.Expr.const ``S [])
/// ```
///
/// This is the `mkAppN (.const ``C []) #[toExpr f0, …, toExpr fn]` form spelled
/// out via the left-nested `Lean.Expr.app` constructor (the reflected
/// application node), avoiding any dependency on a `Lean.mkAppN` helper that is
/// not an in-tree kernel constant. Each `x.i` is the struct recursor projection
/// (see [`project_struct_field`]) and `insti` is the field type's own
/// `Lean.ToExpr` instance resolved from `env`, applied through the
/// `Lean.ToExpr.toExpr` projection accessor. Every field type must resolve a
/// monomorphic in-tree `Lean.ToExpr` instance; otherwise this returns `None` and
/// the caller fails closed with `Unsupported`. The whole term is closed and
/// kernel-checkable (only the struct's recursor, the reflected `Lean.Expr`
/// constructors, and the field instances' `toExpr` projections).
fn to_expr_struct_value(
    env: &Environment,
    tn: &Name,
    ctors: &[CtorInfo2],
    np: u32,
) -> Option<Expr> {
    let ctor = single_ctor_struct(ctors, np)?;
    // The struct lives in `Type 0 = Sort 1`; its data fields also live in
    // `Sort 1`, so the projecting recursor eliminates into `Sort 1`.
    let motive_level = Level::succ(Level::zero());
    let ind_ty = Expr::const_(tn.clone(), vec![]);

    // Resolve every field's Lean.ToExpr instance up front; bail to the fallback
    // if any field type lacks a resolvable monomorphic instance.
    let mut field_insts = Vec::with_capacity(ctor.fields.len());
    for (_fname, fty) in &ctor.fields {
        field_insts.push(resolve_field_instance(env, "Lean.ToExpr", fty)?);
    }

    // toExpr := fun (x : S) => mkAppN (.const ``C []) #[toExpr x.0, …]. The single
    // lambda binds `x = bvar 0`; reflected application nests left via
    // `Lean.Expr.app`, seeded with the reflected constructor constant.
    let lean_expr_app = Expr::const_str("Lean.Expr.app");
    let mut body = reflect_expr_const(&ctor.name);
    for (idx, (_fname, fty)) in ctor.fields.iter().enumerate() {
        let x_field =
            project_struct_field(tn, idx, fty, &ctor.fields, Expr::bvar(0), &motive_level);
        // @Lean.ToExpr.toExpr Fi insti x.i : Lean.Expr (the projection accessor;
        // the supported field types live in `Type 0`, so no levels are supplied).
        let reflected_field = Expr::apps(
            Expr::const_str("Lean.ToExpr.toExpr"),
            [fty.clone(), field_insts[idx].clone(), x_field],
        );
        body = Expr::apps(lean_expr_app.clone(), [body, reflected_field]);
    }

    let to_expr_fn = Expr::lam(BinderInfo::Default, ind_ty.clone(), body);
    let to_type_expr = reflect_expr_const(tn);

    // @Lean.ToExpr.mk S toExpr toTypeExpr. The `α` binder is implicit; supply it
    // explicitly (mirroring the nullary-enum branch).
    Some(Expr::apps(
        Expr::const_str("Lean.ToExpr.mk"),
        [ind_ty, to_expr_fn, to_type_expr],
    ))
}
pub(crate) struct DeriveOfScientific;
impl ExtDeriveHandler2 for DeriveOfScientific {
    fn class_name(&self) -> &str {
        "OfScientific"
    }

    fn derive(
        &self,
        _env: &Environment,
        tn: &Name,
        te: &Expr,
        ctors: &[CtorInfo2],
        np: u32,
        _lp: &[Name],
    ) -> Result<Vec<DerivedDecl2>, DeriveError> {
        DerivePreconditionChecker::check(self.class_name(), tn, te, ctors)?;

        // The precondition guarantees a single-constructor, single-field
        // wrapper. Try to synthesize a genuine, sorry-free `OfScientific`
        // instance for the shapes we can kernel-check.
        let Some(value) = of_scientific_value(tn, ctors, np) else {
            return Err(DeriveError::Unsupported {
                class_name: "OfScientific".to_owned(),
                ind_name: tn.to_string(),
                reason: "only a monomorphic single-field Nat wrapper has a complete \
                         OfScientific construction"
                    .to_owned(),
            });
        };

        Ok(vec![mk_inst_decl(
            "OfScientific",
            "OfScientific",
            tn,
            np,
            value,
        )])
    }
}

/// Try to build a sorry-free `OfScientific` instance value for a single-field
/// wrapper.
///
/// The real Lean class is
///
/// ```text
/// class OfScientific (α : Type u) where
///   ofScientific : (mantissa : Nat) → (exponentSign : Bool) → (decimalExponent : Nat) → α
/// ```
///
/// For a single-constructor, single-field wrapper `Ctor : Nat → Wrapper` with
/// no type parameters, the mantissa is already a canonical `Nat`, so
///
/// ```text
/// OfScientific.mk (fun (mantissa : Nat) (s : Bool) (exp : Nat) => Ctor mantissa)
/// ```
///
/// is a closed, kernel-checkable term that introduces no `sorryAx`/axioms.
///
/// Returns `None` for shapes outside this supported set (parametric wrappers,
/// or wrappers whose field type is not exactly `Nat`), so the caller fails
/// closed with `Unsupported`. Restricting to `np == 0` and a `Nat` field
/// keeps the de Bruijn indices and the field value unambiguously sound: for a
/// non-`Nat` field we would need an `OfScientific` instance for the field type,
/// which is not resolvable structurally here.
fn of_scientific_value(tn: &Name, ctors: &[CtorInfo2], np: u32) -> Option<Expr> {
    if np != 0 {
        return None;
    }
    let ctor = ctors.first()?;
    if ctor.fields.len() != 1 {
        return None;
    }
    let (_field_name, field_ty) = ctor.fields.first()?;
    // Only `Nat`-typed fields have a canonical value constructible from the
    // mantissa alone.
    if head_const_name(field_ty).is_none_or(|head| head.to_string() != "Nat") {
        return None;
    }
    // Lambda nesting: fun (mantissa : Nat) (s : Bool) (exp : Nat) => Ctor mantissa
    // mantissa is the outermost of three binders, so it is `bvar(2)` in the body.
    let ctor_expr = Expr::const_(ctor.name.clone(), vec![]);
    let body = Expr::app(ctor_expr, Expr::bvar(2));
    let lambda = Expr::lam(
        BinderInfo::Default,
        mk_nat(),
        Expr::lam(
            BinderInfo::Default,
            mk_bool(),
            Expr::lam(BinderInfo::Default, mk_nat(), body),
        ),
    );
    // `OfScientific.mk : {α : Type} → (Nat → Bool → Nat → α) → OfScientific α`.
    // The `α` binder is implicit, but the kernel accepts it positionally, so we
    // supply the wrapper type explicitly (mirroring `DeriveHashable2`).
    let wrapper_ty = Expr::const_(tn.clone(), vec![]);
    Some(Expr::apps(
        Expr::const_str("OfScientific.mk"),
        [wrapper_ty, lambda],
    ))
}

// ---------------------------------------------------------------------------
// ExtDeriveHandler2 -> DeriveHandler adapter (sound, sorry-rejecting bridge)
// ---------------------------------------------------------------------------

/// Extract the field `(name, type)` list of a constructor.
///
/// Walks the `num_params` leading pi binders (the inductive's parameters) and
/// then collects the next `num_fields` pi domains as the constructor's data
/// fields, synthesizing positional names `field0 … field{n-1}` (the batch-2
/// handlers key off field *types*, not names). Field types are returned as the
/// raw constructor-type domains; for the monomorphic, parameter-free shapes the
/// registered handlers accept (`np == 0`), these are closed `Const` terms such
/// as `Nat`.
fn ctor_fields(
    class_name: &str,
    ind: &InductiveVal,
    ctor: &ConstructorVal,
) -> Result<Vec<(Name, Expr)>, DeriveError> {
    let mut current = &ctor.type_;
    for idx in 0..ctor.num_params {
        match current.kind() {
            ExprKind::Pi(_, _, body) => current = body.as_ref(),
            _ => {
                return Err(DeriveError::Unsupported {
                    class_name: class_name.to_owned(),
                    ind_name: ind.name.to_string(),
                    reason: format!(
                        "constructor `{}` telescope ended before declared parameter {idx} of {}",
                        ctor.name, ctor.num_params
                    ),
                });
            }
        }
    }
    let mut fields = Vec::with_capacity(ctor.num_fields as usize);
    for idx in 0..ctor.num_fields {
        match current.kind() {
            ExprKind::Pi(_, domain, body) => {
                fields.push((
                    Name::from_string(&format!("field{idx}")),
                    (**domain).clone(),
                ));
                current = body.as_ref();
            }
            _ => {
                return Err(DeriveError::Unsupported {
                    class_name: class_name.to_owned(),
                    ind_name: ind.name.to_string(),
                    reason: format!(
                        "constructor `{}` telescope ended before declared field {idx} of {}",
                        ctor.name, ctor.num_fields
                    ),
                });
            }
        }
    }
    Ok(fields)
}

/// Build the [`CtorInfo2`] list for an inductive from its environment entry.
///
/// Each constructor's fields are extracted via [`ctor_fields`]; a constructor is
/// flagged recursive when any of its field-type heads is the inductive itself
/// (so the precondition checkers — which reject recursive constructors for all
/// four batch-2 classes — see the same shape the dedicated tests assert).
fn build_ctor_infos(
    class_name: &str,
    ind: &InductiveVal,
    env: &Environment,
) -> Result<Vec<CtorInfo2>, DeriveError> {
    let ctors = lookup_constructors(ind, env)?;
    ctors
        .iter()
        .map(|ctor| {
            let fields = ctor_fields(class_name, ind, ctor)?;
            let is_recursive = fields
                .iter()
                .any(|(_, ty)| head_const_name(ty).is_some_and(|head| head == &ind.name));
            Ok(CtorInfo2 {
                name: ctor.name.clone(),
                fields,
                is_recursive,
            })
        })
        .collect()
}

/// Adapter that exposes an [`ExtDeriveHandler2`] through the canonical
/// [`DeriveHandler`] interface used by [`crate::derive::DeriveRegistry`].
///
/// The adapter routes every batch-2 result through the same central automatic
/// derive admission gate used by the frontend and canonical registry. Batch
/// handlers report unsupported shapes directly; the gate remains defense in
/// depth for custom/composed handlers. Genuine, closed instances pass through
/// and are kernel-checked by `run_derive`.
pub(crate) struct ExtDeriveHandler2Adapter {
    inner: Box<dyn ExtDeriveHandler2>,
}

impl ExtDeriveHandler2Adapter {
    #[must_use]
    pub(crate) fn new(inner: Box<dyn ExtDeriveHandler2>) -> Self {
        Self { inner }
    }
}

impl DeriveHandler for ExtDeriveHandler2Adapter {
    fn class_name(&self) -> &str {
        self.inner.class_name()
    }

    fn derive(
        &self,
        ind: &InductiveVal,
        env: &Environment,
    ) -> Result<Vec<Declaration>, DeriveError> {
        let ctors = build_ctor_infos(self.inner.class_name(), ind, env)?;
        let derived = self.inner.derive(
            env,
            &ind.name,
            &ind.type_,
            &ctors,
            ind.num_params,
            &ind.level_params,
        )?;

        let mut decls = Vec::with_capacity(derived.len());
        for DerivedDecl2 {
            name, type_, value, ..
        } in derived
        {
            crate::derive::admit_generated_instance(
                env,
                self.inner.class_name(),
                &ind.name.to_string(),
                &name,
                &type_,
                &value,
            )?;
            decls.push(Declaration::Definition {
                name,
                level_params: ind.level_params.clone(),
                type_,
                value,
                is_reducible: true,
            });
        }
        Ok(decls)
    }
}

pub(crate) struct ComposedDeriveHandler {
    class_name: String,
    handlers: Vec<Box<dyn ExtDeriveHandler2>>,
}
impl ComposedDeriveHandler {
    #[must_use]
    pub(crate) fn new(class_name: &str, handlers: Vec<Box<dyn ExtDeriveHandler2>>) -> Self {
        Self {
            class_name: class_name.to_owned(),
            handlers,
        }
    }
}
impl ExtDeriveHandler2 for ComposedDeriveHandler {
    fn class_name(&self) -> &str {
        &self.class_name
    }

    fn derive(
        &self,
        env: &Environment,
        tn: &Name,
        te: &Expr,
        ctors: &[CtorInfo2],
        np: u32,
        lp: &[Name],
    ) -> Result<Vec<DerivedDecl2>, DeriveError> {
        let mut out = Vec::new();
        for handler in &self.handlers {
            out.extend(handler.derive(env, tn, te, ctors, np, lp)?);
        }
        Ok(out)
    }
}
impl std::fmt::Debug for ComposedDeriveHandler {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let names: Vec<&str> = self
            .handlers
            .iter()
            .map(|handler| handler.class_name())
            .collect();
        f.debug_struct("ComposedDeriveHandler")
            .field("class_name", &self.class_name)
            .field("handlers", &names)
            .finish()
    }
}
struct RegisteredHandler {
    priority: u32,
    handler: Box<dyn ExtDeriveHandler2>,
}
pub(crate) struct ExtendedDeriveRegistry {
    handlers: HashMap<String, Vec<RegisteredHandler>>,
    dependencies: HashMap<String, Vec<Name>>,
}
impl ExtendedDeriveRegistry {
    #[must_use]
    pub(crate) fn new() -> Self {
        Self {
            handlers: HashMap::new(),
            dependencies: HashMap::new(),
        }
    }

    pub(crate) fn register(
        &mut self,
        priority: u32,
        dependencies: &[Name],
        handler: Box<dyn ExtDeriveHandler2>,
    ) {
        let class_name = handler.class_name().to_owned();
        let entries = self.handlers.entry(class_name.clone()).or_default();
        let pos = entries
            .iter()
            .position(|entry| entry.priority < priority)
            .unwrap_or(entries.len());
        entries.insert(pos, RegisteredHandler { priority, handler });
        let deps = self.dependencies.entry(class_name).or_default();
        for dependency in dependencies {
            if !deps.contains(dependency) {
                deps.push(dependency.clone());
            }
        }
    }

    #[must_use]
    pub(crate) fn has_handler(&self, class_name: &str) -> bool {
        self.handlers
            .get(class_name)
            .is_some_and(|entries| !entries.is_empty())
    }

    #[must_use]
    pub(crate) fn registered_classes(&self) -> Vec<&str> {
        self.handlers.keys().map(String::as_str).collect()
    }

    #[must_use]
    pub(crate) fn dependencies_for(&self, class_name: &str) -> Vec<Name> {
        self.dependencies
            .get(class_name)
            .cloned()
            .unwrap_or_default()
    }

    #[must_use]
    pub(crate) fn default_registry() -> Self {
        let mut reg = Self::new();
        reg.register(100, &[], Box::new(DeriveFintype));
        reg.register(
            100,
            &[Name::from_string("Fintype")],
            Box::new(DeriveCountable),
        );
        reg.register(100, &[], Box::new(DeriveToExpr));
        reg.register(100, &[], Box::new(DeriveOfScientific));
        reg
    }

    pub(crate) fn derive_all(
        &self,
        env: &Environment,
        type_name: &Name,
        type_expr: &Expr,
        ctors: &[CtorInfo2],
        classes: &[Name],
        num_params: u32,
        level_params: &[Name],
    ) -> Result<Vec<DerivedDecl2>, DeriveError> {
        let ordered = self.order_classes(classes)?;
        let mut out = Vec::new();
        for class in ordered {
            let class_name = class.to_string();
            let entries = self
                .handlers
                .get(&class_name)
                .ok_or_else(|| DeriveError::NoHandler(class_name.clone()))?;
            let mut last_err = None;
            for entry in entries {
                match entry.handler.derive(
                    env,
                    type_name,
                    type_expr,
                    ctors,
                    num_params,
                    level_params,
                ) {
                    Ok(decls) => {
                        out.extend(decls);
                        last_err = None;
                        break;
                    }
                    Err(err) => last_err = Some(err),
                }
            }
            if let Some(err) = last_err {
                return Err(err);
            }
        }
        Ok(out)
    }

    fn order_classes(&self, classes: &[Name]) -> Result<Vec<Name>, DeriveError> {
        let mut ordered = Vec::new();
        let mut visiting = HashSet::new();
        let mut visited = HashSet::new();
        for class in classes {
            self.visit_class(class, &mut visiting, &mut visited, &mut ordered)?;
        }
        Ok(ordered)
    }

    fn visit_class(
        &self,
        class: &Name,
        visiting: &mut HashSet<String>,
        visited: &mut HashSet<String>,
        ordered: &mut Vec<Name>,
    ) -> Result<(), DeriveError> {
        let class_name = class.to_string();
        if visited.contains(&class_name) {
            return Ok(());
        }
        if !visiting.insert(class_name.clone()) {
            return Err(DeriveError::Unsupported {
                class_name,
                ind_name: "<derive dependency graph>".to_owned(),
                reason: "cyclic derive dependency detected".to_owned(),
            });
        }
        for dep in self
            .dependencies
            .get(&class.to_string())
            .cloned()
            .unwrap_or_default()
        {
            self.visit_class(&dep, visiting, visited, ordered)?;
        }
        visiting.remove(&class.to_string());
        visited.insert(class.to_string());
        ordered.push(class.clone());
        Ok(())
    }
}
impl Default for ExtendedDeriveRegistry {
    fn default() -> Self {
        Self::default_registry()
    }
}
impl std::fmt::Debug for ExtendedDeriveRegistry {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ExtendedDeriveRegistry")
            .field("handlers", &self.handlers.keys().collect::<Vec<_>>())
            .field("dependencies", &self.dependencies)
            .finish()
    }
}
