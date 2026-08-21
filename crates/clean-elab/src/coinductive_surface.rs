// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The `coinductive` predicate surface (#191, rank 1 of the coinduction
//! ladder): a Lean 4.25-style `coinductive` **Prop-valued** declaration
//! lowered to the impredicative greatest-fixpoint encoding Clean's kernel
//! already checks — no kernel cofix, no new `ExprKind`, no new reduction
//! rule, **zero new axioms**.
//!
//! ```text
//! coinductive Bisim : Str → Str → Prop
//! | step : shd s = shd t → Bisim (stl s) (stl t) → Bisim s t
//! ```
//!
//! generates, and kernel-checks, exactly the shapes the hand-written
//! `data/graduation/clean-coind/proof/Coind.lean` core pins:
//!
//! ```text
//! Bisim.F      : (Str → Str → Prop) → Str → Str → Prop   one-step functor
//! Bisim        : Str → Str → Prop                        gfp = ⋃ post-fixpoints
//! Bisim.coind  : Park coinduction — every post-fixpoint is below the gfp
//! Bisim.F_mono : monotonicity of the generated functor
//! Bisim.unfold : the gfp is a post-fixpoint (the destructor)
//! Bisim.fold   : the gfp is a pre-fixpoint (needs monotonicity)
//! Bisim.step   : the declared constructor, proved through `fold`
//! ```
//!
//! The fixpoint is the standard impredicative union of post-fixpoints
//! (`Coind.lean`'s `gfpRel`) at the declaration's own index telescope:
//!
//! ```text
//! P v⃗ := ∃ R, (∀ v⃗, R v⃗ → P.F R v⃗) ∧ R v⃗
//! ```
//!
//! No induction principle is generated, and none exists: `P` is a `def`, not
//! an inductive type, so there is no `P.rec` to misuse.
//!
//! # v1 envelope (everything outside it REJECTS LOUDLY)
//!
//! A narrow envelope is the point. A `coinductive` declaration must never
//! quietly acquire least-fixpoint meaning, so every shape this module does
//! not fully understand is an [`ElabError::Unsupported`] naming the offending
//! clause — never a best-effort lowering:
//!
//! * result sort `Prop`, reached through a NON-dependent arrow telescope of
//!   arity ≥ 1 (`P : T₁ → … → Tₙ → Prop`);
//! * no declaration parameters, no universe parameters, no `deriving`, no
//!   modifiers;
//! * exactly ONE constructor. A multi-constructor functor is a disjunction —
//!   a named build item, not something to approximate silently;
//! * that constructor's type is an ARROW chain `Prem₁ → … → Premⱼ → P v⃗`
//!   (j ≥ 1) whose target arguments `v⃗` are DISTINCT identifiers — the
//!   destructor-style one-step rule. Compound targets need the
//!   `∃`-plus-index-equation lowering (build item);
//! * each premise is either a fully-applied recursive occurrence `P e⃗`
//!   (arity n, positional, arguments free of `P`) or a premise not mentioning
//!   `P` at all — so recursive occurrences are strictly positive by
//!   construction and the generated `F_mono` proof is always available;
//! * each premise is applicative (identifiers, applications, arrows,
//!   binders); `match` / `do` / tactic premises reject;
//! * every free variable of a premise is a target variable or an existing
//!   constant. This clause is load-bearing: a stray free name would be
//!   silently AUTO-BOUND as an implicit parameter of the generated functor,
//!   changing what the declaration means.
//!
//! [`lower`] is pure — it returns surface declarations. The caller elaborates
//! them through the ordinary parse→elaborate→kernel-check path, so every
//! generated definition and theorem is kernel-re-checked exactly like
//! hand-written source.

use crate::ElabError;
use clean_kernel::{Environment, Name};
use clean_parser::{
    DeclModifiers, Span, SurfaceArg, SurfaceBinder, SurfaceBinderInfo, SurfaceCtor, SurfaceDecl,
    SurfaceExpr, TerminationHints, UniverseExpr,
};

/// Companion suffixes this lowering mints under the declaration's name.
/// A constructor may not claim one of them.
const RESERVED_SUFFIXES: [&str; 5] = ["F", "coind", "F_mono", "unfold", "fold"];

/// Generated binder names, all carrying the `coind` marker so they cannot
/// collide with a target variable (those are checked to be plain identifiers
/// drawn from the user's constructor).
const REL_R: &str = "R_coind";
const REL_S: &str = "S_coind";
const HYP_POST: &str = "hpost_coind";
const HYP_LE: &str = "hle_coind";
const HYP_H: &str = "h_coind";
const HYP_HR: &str = "hR_coind";

fn unsupported(msg: impl Into<String>) -> ElabError {
    ElabError::Unsupported {
        feature: msg.into(),
    }
}

// ── surface-term builders ────────────────────────────────────────────────

fn ident(name: &str) -> SurfaceExpr {
    SurfaceExpr::Ident(Span::dummy(), name.to_string())
}

/// Application that FLATTENS a nested head: `app(app(f, [a]), [b])` is
/// `f a b`, the shape a parsed application would have had.
fn app(head: SurfaceExpr, args: Vec<SurfaceExpr>) -> SurfaceExpr {
    if args.is_empty() {
        return head;
    }
    let new_args = args.into_iter().map(SurfaceArg::positional);
    match head {
        SurfaceExpr::App(span, h, mut existing) => {
            existing.extend(new_args);
            SurfaceExpr::App(span, h, existing)
        }
        other => SurfaceExpr::App(Span::dummy(), Box::new(other), new_args.collect()),
    }
}

fn napp(name: &str, args: Vec<SurfaceExpr>) -> SurfaceExpr {
    app(ident(name), args)
}

fn arrow(a: SurfaceExpr, b: SurfaceExpr) -> SurfaceExpr {
    SurfaceExpr::Arrow(Span::dummy(), Box::new(a), Box::new(b))
}

fn prop() -> SurfaceExpr {
    SurfaceExpr::Universe(Span::dummy(), UniverseExpr::Prop)
}

fn binder(name: &str, ty: SurfaceExpr, info: SurfaceBinderInfo) -> SurfaceBinder {
    SurfaceBinder::new(name, Some(ty), info)
}

/// `fun n₁ n₂ … => body` with untyped binders (solved from the expected type).
fn lam(names: &[&str], body: SurfaceExpr) -> SurfaceExpr {
    if names.is_empty() {
        return body;
    }
    SurfaceExpr::Lambda(
        Span::dummy(),
        names
            .iter()
            .map(|n| SurfaceBinder::new(*n, None, SurfaceBinderInfo::Explicit))
            .collect(),
        Box::new(body),
    )
}

fn and(a: SurfaceExpr, b: SurfaceExpr) -> SurfaceExpr {
    napp("And", vec![a, b])
}

/// Right-nested combination of a non-empty list (`p₁ ∘ (p₂ ∘ (… ∘ pⱼ))`).
fn right_nest(
    mut parts: Vec<SurfaceExpr>,
    f: impl Fn(SurfaceExpr, SurfaceExpr) -> SurfaceExpr,
) -> SurfaceExpr {
    let last = parts.pop().unwrap_or_else(prop);
    parts.into_iter().rev().fold(last, |acc, p| f(p, acc))
}

fn mk_def(
    name: String,
    binders: Vec<SurfaceBinder>,
    ty: SurfaceExpr,
    val: SurfaceExpr,
) -> SurfaceDecl {
    SurfaceDecl::Def {
        span: Span::dummy(),
        name,
        universe_params: Vec::new(),
        binders,
        ty: Some(Box::new(ty)),
        val: Box::new(val),
        attrs: Vec::new(),
        termination: TerminationHints::default(),
        modifiers: DeclModifiers::default(),
        where_decls: Vec::new(),
    }
}

fn mk_theorem(
    name: String,
    binders: Vec<SurfaceBinder>,
    ty: SurfaceExpr,
    proof: SurfaceExpr,
) -> SurfaceDecl {
    SurfaceDecl::Theorem {
        span: Span::dummy(),
        name,
        universe_params: Vec::new(),
        binders,
        ty: Box::new(ty),
        proof: Box::new(proof),
        attrs: Vec::new(),
        termination: TerminationHints::default(),
        modifiers: DeclModifiers::default(),
        where_decls: Vec::new(),
    }
}

fn strip_parens(expr: &SurfaceExpr) -> &SurfaceExpr {
    match expr {
        SurfaceExpr::Paren(_, e) => strip_parens(e),
        _ => expr,
    }
}

/// A short label for a surface form this module refuses to analyse, so the
/// reject names the offending construct instead of dumping a debug tree.
fn variant_label(expr: &SurfaceExpr) -> &'static str {
    match expr {
        SurfaceExpr::Match(..) => "match",
        SurfaceExpr::Do(..) => "do",
        SurfaceExpr::ByTactic(..) => "by",
        SurfaceExpr::CalcBlock(..) => "calc",
        SurfaceExpr::If(..) | SurfaceExpr::IfLet(..) | SurfaceExpr::IfDecidable(..) => "if",
        SurfaceExpr::Let(..) | SurfaceExpr::LetRec(..) | SurfaceExpr::LetPattern(..) => "let",
        SurfaceExpr::PatternMatchLambda(..) => "fun | …",
        SurfaceExpr::SyntaxQuote(..) => "syntax quotation",
        SurfaceExpr::SyntheticSorry(..) => "sorry",
        _ => "unsupported term",
    }
}

// ── shape analysis ───────────────────────────────────────────────────────

/// One premise of the single constructor.
enum Premise {
    /// A fully-applied recursive occurrence `P e⃗` (arity n).
    Rec(Vec<SurfaceExpr>),
    /// A premise that does not mention `P` at all.
    Plain(SurfaceExpr),
}

struct Shape {
    /// Fully-qualified declaration name.
    qname: String,
    /// Constructor short name.
    ctor: String,
    /// Index telescope types, in order.
    idx_tys: Vec<SurfaceExpr>,
    /// Target variable names of the constructor, in order (distinct).
    vars: Vec<String>,
    premises: Vec<Premise>,
}

/// Flatten a non-dependent arrow chain, returning `(antecedents, head)`.
/// A `Pi` anywhere in the spine yields `None`: v1 rejects dependent
/// telescopes rather than mis-lowering them.
fn flatten_arrows(expr: &SurfaceExpr) -> Option<(Vec<&SurfaceExpr>, &SurfaceExpr)> {
    let mut parts = Vec::new();
    let mut cur = strip_parens(expr);
    loop {
        match cur {
            SurfaceExpr::Arrow(_, a, b) => {
                parts.push(strip_parens(a));
                cur = strip_parens(b);
            }
            SurfaceExpr::Pi(..) => return None,
            _ => return Some((parts, cur)),
        }
    }
}

/// Does `expr` mention `name` as an identifier (exactly, or as the prefix of
/// a dotted name)? Binder scoping is deliberately IGNORED — a shadowed
/// occurrence still trips the check, which errs toward rejection.
fn mentions(expr: &SurfaceExpr, name: &str) -> bool {
    let mut bound: Vec<&str> = Vec::new();
    let mut fvs: Vec<&str> = Vec::new();
    if all_idents(expr, &mut bound, &mut fvs).is_err() {
        // A form this module cannot analyse is treated as possibly mentioning
        // the name; the caller rejects either way.
        return true;
    }
    let dotted = format!("{name}.");
    fvs.iter().any(|id| *id == name || id.starts_with(&dotted))
}

/// Collect the FREE identifiers of `expr`, honouring lambda/Pi binder scope.
///
/// Returns `Err(label)` for a surface form this module refuses to analyse.
fn all_idents<'a>(
    expr: &'a SurfaceExpr,
    bound: &mut Vec<&'a str>,
    out: &mut Vec<&'a str>,
) -> Result<(), &'static str> {
    match expr {
        SurfaceExpr::Ident(_, id) => {
            let id = id.as_str();
            if !bound.contains(&id) && !out.contains(&id) {
                out.push(id);
            }
        }
        SurfaceExpr::Lit(..) | SurfaceExpr::Universe(..) | SurfaceExpr::Hole(..) => {}
        SurfaceExpr::App(_, h, args) => {
            all_idents(h, bound, out)?;
            for a in args {
                all_idents(&a.expr, bound, out)?;
            }
        }
        SurfaceExpr::Arrow(_, a, b) => {
            all_idents(a, bound, out)?;
            all_idents(b, bound, out)?;
        }
        SurfaceExpr::Lambda(_, bs, body) | SurfaceExpr::Pi(_, bs, body) => {
            let depth = bound.len();
            for b in bs {
                if let Some(t) = &b.ty {
                    all_idents(t, bound, out)?;
                }
                bound.push(b.name.as_str());
            }
            all_idents(body, bound, out)?;
            bound.truncate(depth);
        }
        SurfaceExpr::Paren(_, e)
        | SurfaceExpr::Explicit(_, e)
        | SurfaceExpr::OutParam(_, e)
        | SurfaceExpr::SemiOutParam(_, e)
        | SurfaceExpr::Proj(_, e, _)
        | SurfaceExpr::NamedArg(_, _, e)
        | SurfaceExpr::UniverseInst(_, e, _) => all_idents(e, bound, out)?,
        SurfaceExpr::Ascription(_, e, t) => {
            all_idents(e, bound, out)?;
            all_idents(t, bound, out)?;
        }
        other => return Err(variant_label(other)),
    }
    Ok(())
}

/// Is `id` already a constant of `env`? Used only to tell "constant" from
/// "stray free variable"; an unknown name rejects rather than being
/// auto-bound into the generated functor's signature.
fn known_constant(env: &Environment, id: &str) -> bool {
    env.get_const(&Name::from_string(id)).is_some()
}

/// `short v₁ … vₙ` with `n == arity` distinct positional identifier args.
fn target_vars(target: &SurfaceExpr, short: &str, arity: usize) -> Option<Vec<String>> {
    let SurfaceExpr::App(_, head, args) = strip_parens(target) else {
        return None;
    };
    if !matches!(strip_parens(head), SurfaceExpr::Ident(_, id) if id == short) {
        return None;
    }
    if args.len() != arity {
        return None;
    }
    let mut vars: Vec<String> = Vec::with_capacity(arity);
    for a in args {
        if a.name.is_some() {
            return None;
        }
        let SurfaceExpr::Ident(_, id) = strip_parens(&a.expr) else {
            return None;
        };
        if id == short || vars.iter().any(|v| v == id) {
            return None;
        }
        vars.push(id.clone());
    }
    Some(vars)
}

fn classify_premise(p: &SurfaceExpr, short: &str, arity: usize) -> Option<Premise> {
    if let SurfaceExpr::App(_, head, args) = strip_parens(p) {
        if matches!(strip_parens(head), SurfaceExpr::Ident(_, id) if id == short) {
            if args.len() != arity || args.iter().any(|a| a.name.is_some()) {
                return None;
            }
            if args.iter().any(|a| mentions(&a.expr, short)) {
                return None;
            }
            return Some(Premise::Rec(args.iter().map(|a| a.expr.clone()).collect()));
        }
    }
    if mentions(p, short) {
        return None;
    }
    Some(Premise::Plain(p.clone()))
}

#[allow(clippy::too_many_arguments)]
fn validate(
    qname: &str,
    short: &str,
    env: &Environment,
    universe_params: &[String],
    binders: &[SurfaceBinder],
    ty: &SurfaceExpr,
    ctors: &[SurfaceCtor],
    deriving: &[String],
    modifiers: &DeclModifiers,
) -> Result<Shape, ElabError> {
    let what = format!("coinductive declaration `{qname}`");
    if !universe_params.is_empty() {
        return Err(unsupported(format!(
            "{what}: universe-polymorphic coinductive predicates are not \
             supported in v1 — the greatest-fixpoint lowering is Prop-valued \
             and monomorphic for now"
        )));
    }
    if !binders.is_empty() {
        return Err(unsupported(format!(
            "{what}: declaration parameters are not supported in v1 — write \
             them as leading indices (`{short} : Param → … → Prop`)"
        )));
    }
    if !deriving.is_empty() {
        return Err(unsupported(format!(
            "{what}: `deriving {}` has no meaning for a Prop-valued greatest \
             fixpoint; this is a deliberate loud reject",
            deriving.join(", ")
        )));
    }
    if !modifiers.is_default() {
        return Err(unsupported(format!(
            "{what}: declaration modifiers (private/partial/noncomputable/…) \
             are not supported in v1"
        )));
    }

    // ── the index telescope ────────────────────────────────────────────
    let Some((idx_tys, sort)) = flatten_arrows(ty) else {
        return Err(unsupported(format!(
            "{what}: a DEPENDENT index telescope `(x : A) → …` is not \
             supported in v1; use a non-dependent arrow telescope"
        )));
    };
    if !matches!(sort, SurfaceExpr::Universe(_, UniverseExpr::Prop)) {
        return Err(unsupported(format!(
            "{what}: the result sort must be `Prop` — v1 lowers coinductive \
             PREDICATES to a greatest fixpoint over complete lattices; \
             Type-valued codata is the separate `codata` command"
        )));
    }
    if idx_tys.is_empty() {
        return Err(unsupported(format!(
            "{what}: a coinductive predicate needs at least one index \
             (`{short} : T → … → Prop`)"
        )));
    }
    let arity = idx_tys.len();

    // ── the single constructor ─────────────────────────────────────────
    let [ctor] = ctors else {
        return Err(unsupported(format!(
            "{what}: v1 supports exactly ONE constructor (the one-step \
             functor); {} were declared — a multi-constructor functor is a \
             DISJUNCTIVE one-step relation, which is a build item, not \
             something to approximate silently",
            ctors.len()
        )));
    };
    if RESERVED_SUFFIXES.contains(&ctor.name.as_str()) {
        return Err(unsupported(format!(
            "{what}: constructor name `{}` collides with the generated \
             companion `{qname}.{}`",
            ctor.name, ctor.name
        )));
    }

    let Some((prem_exprs, target)) = flatten_arrows(&ctor.ty) else {
        return Err(unsupported(format!(
            "{what}: constructor `{}` uses binders (`(x : T) → …`); v1 \
             requires a plain arrow chain of premises",
            ctor.name
        )));
    };
    if prem_exprs.is_empty() {
        return Err(unsupported(format!(
            "{what}: constructor `{}` has no premises, so the one-step \
             functor would be constantly true and `{qname}` would hold of \
             everything; v1 rejects that rather than mint it",
            ctor.name
        )));
    }

    let vars = target_vars(target, short, arity).ok_or_else(|| {
        unsupported(format!(
            "{what}: constructor `{}` must conclude in `{short} v₁ … v{arity}` \
             with DISTINCT variable arguments (the destructor-style one-step \
             rule); a compound target needs the index-equation lowering, \
             which is a build item",
            ctor.name
        ))
    })?;

    // ── premises ───────────────────────────────────────────────────────
    let mut premises = Vec::with_capacity(prem_exprs.len());
    for p in &prem_exprs {
        let analysed = classify_premise(p, short, arity).ok_or_else(|| {
            unsupported(format!(
                "{what}: every premise of `{}` must be either a FULLY-APPLIED \
                 recursive occurrence `{short} e₁ … e{arity}` (arguments free \
                 of `{short}`) or a premise that does not mention `{short}` at \
                 all; a nested, negative or partially-applied occurrence is \
                 refused because its positivity is not established here",
                ctor.name
            ))
        })?;
        premises.push(analysed);
    }

    // Every free variable of a premise must be a target variable or an
    // existing constant. A stray name would otherwise be AUTO-BOUND as an
    // implicit parameter of the generated functor, silently changing what
    // the declaration means.
    for p in &prem_exprs {
        let mut bound: Vec<&str> = Vec::new();
        let mut fvs: Vec<&str> = Vec::new();
        all_idents(p, &mut bound, &mut fvs).map_err(|label| {
            unsupported(format!(
                "{what}: a premise of `{}` uses the non-applicative surface \
                 form `{label}`; v1 premises must be built from identifiers, \
                 applications, arrows and binders",
                ctor.name
            ))
        })?;
        for fv in fvs {
            if fv == short || vars.iter().any(|v| v == fv) || known_constant(env, fv) {
                continue;
            }
            return Err(unsupported(format!(
                "{what}: a premise of `{}` mentions `{fv}`, which is neither a \
                 target variable nor a known constant. v1 refuses to auto-bind \
                 it: an implicit parameter silently inserted into the generated \
                 one-step functor would change what `{qname}` means",
                ctor.name
            )));
        }
    }

    Ok(Shape {
        qname: qname.to_string(),
        ctor: ctor.name.clone(),
        idx_tys: idx_tys.into_iter().cloned().collect(),
        vars,
        premises,
    })
}

// ── generation ───────────────────────────────────────────────────────────

impl Shape {
    /// `T₁ → … → Tₙ → Prop` — the type of a candidate relation.
    fn rel_ty(&self) -> SurfaceExpr {
        self.idx_tys
            .iter()
            .rev()
            .fold(prop(), |acc, t| arrow(t.clone(), acc))
    }

    /// `(v₁ : T₁) … (vₙ : Tₙ)` binders at the requested binder info.
    fn idx_binders(&self, info: SurfaceBinderInfo) -> Vec<SurfaceBinder> {
        self.vars
            .iter()
            .zip(&self.idx_tys)
            .map(|(v, t)| binder(v, t.clone(), info))
            .collect()
    }

    fn var_args(&self) -> Vec<SurfaceExpr> {
        self.vars.iter().map(|v| ident(v)).collect()
    }

    /// `head v₁ … vₙ`.
    fn applied(&self, head: SurfaceExpr) -> SurfaceExpr {
        app(head, self.var_args())
    }

    /// `∀ (v₁ : T₁) … (vₙ : Tₙ), body`.
    fn forall_vars(&self, body: SurfaceExpr) -> SurfaceExpr {
        SurfaceExpr::Pi(
            Span::dummy(),
            self.idx_binders(SurfaceBinderInfo::Explicit),
            Box::new(body),
        )
    }

    /// The one-step functor body with `rel` standing for the recursive
    /// occurrences: `Prem₁' ∧ … ∧ Premⱼ'`.
    fn functor_body(&self, rel: &str) -> SurfaceExpr {
        right_nest(
            self.premises
                .iter()
                .map(|p| match p {
                    Premise::Rec(args) => napp(rel, args.clone()),
                    Premise::Plain(e) => e.clone(),
                })
                .collect(),
            and,
        )
    }

    /// The declared premises, with recursive occurrences spelled at the
    /// generated (fully-qualified) predicate name.
    fn declared_premises(&self) -> Vec<SurfaceExpr> {
        self.premises
            .iter()
            .map(|p| match p {
                Premise::Rec(args) => napp(&self.qname, args.clone()),
                Premise::Plain(e) => e.clone(),
            })
            .collect()
    }

    fn f_name(&self) -> String {
        format!("{}.F", self.qname)
    }
    fn coind_name(&self) -> String {
        format!("{}.coind", self.qname)
    }
    fn mono_name(&self) -> String {
        format!("{}.F_mono", self.qname)
    }
    fn unfold_name(&self) -> String {
        format!("{}.unfold", self.qname)
    }
    fn fold_name(&self) -> String {
        format!("{}.fold", self.qname)
    }
}

/// The accessor for the `i`-th conjunct of a right-nested `j`-conjunction
/// proof `h`: `And.left (And.right (… h))`, and plain `h` when `j == 1`.
fn conjunct(h: SurfaceExpr, i: usize, j: usize) -> SurfaceExpr {
    let mut acc = h;
    for _ in 0..i {
        acc = napp("And.right", vec![acc]);
    }
    if i + 1 < j {
        acc = napp("And.left", vec![acc]);
    }
    acc
}

/// Validate a `coinductive` declaration against the v1 envelope and return
/// the surface declarations it lowers to, in dependency order.
///
/// # Errors
///
/// [`ElabError::Unsupported`] — naming the declaration and the precise
/// envelope clause — for every shape outside the v1 envelope documented on
/// this module. Nothing is generated in that case.
#[allow(clippy::too_many_arguments)]
pub(crate) fn lower(
    qname: &str,
    short: &str,
    env: &Environment,
    universe_params: &[String],
    binders: &[SurfaceBinder],
    ty: &SurfaceExpr,
    ctors: &[SurfaceCtor],
    deriving: &[String],
    modifiers: &DeclModifiers,
) -> Result<Vec<SurfaceDecl>, ElabError> {
    let shape = validate(
        qname,
        short,
        env,
        universe_params,
        binders,
        ty,
        ctors,
        deriving,
        modifiers,
    )?;
    Ok(generate(&shape))
}

fn generate(s: &Shape) -> Vec<SurfaceDecl> {
    let j = s.premises.len();
    let rel_ty = s.rel_ty();
    let gfp = || ident(&s.qname);
    // `fun v⃗ h_coind => …` — the shared binder row of every generated proof.
    let lam_names: Vec<&str> = s
        .vars
        .iter()
        .map(String::as_str)
        .chain(std::iter::once(HYP_H))
        .collect();

    // ── 1. the one-step functor ────────────────────────────────────────
    // def P.F (R : T⃗ → Prop) (v⃗ : T⃗) : Prop := Prem₁[P:=R] ∧ … ∧ Premⱼ[P:=R]
    let mut f_binders = vec![binder(REL_R, rel_ty.clone(), SurfaceBinderInfo::Explicit)];
    f_binders.extend(s.idx_binders(SurfaceBinderInfo::Explicit));
    let f_def = mk_def(s.f_name(), f_binders, prop(), s.functor_body(REL_R));

    // `∀ v⃗, rel v⃗ → P.F rel v⃗` — "rel is a post-fixpoint of the functor".
    let post_of = |rel: SurfaceExpr| {
        s.forall_vars(arrow(
            s.applied(rel.clone()),
            s.applied(napp(&s.f_name(), vec![rel])),
        ))
    };

    // ── 2. the greatest fixpoint ───────────────────────────────────────
    // def P (v⃗ : T⃗) : Prop := ∃ R, (∀ v⃗, R v⃗ → P.F R v⃗) ∧ R v⃗
    let gfp_def = mk_def(
        s.qname.clone(),
        s.idx_binders(SurfaceBinderInfo::Explicit),
        prop(),
        napp(
            "Exists",
            vec![SurfaceExpr::Lambda(
                Span::dummy(),
                vec![binder(REL_R, rel_ty.clone(), SurfaceBinderInfo::Explicit)],
                Box::new(and(post_of(ident(REL_R)), s.applied(ident(REL_R)))),
            )],
        ),
    );

    // ── 3. Park coinduction ────────────────────────────────────────────
    // theorem P.coind (R) (post : ∀ v⃗, R v⃗ → P.F R v⃗) : ∀ v⃗, R v⃗ → P v⃗ :=
    //   fun v⃗ h => Exists.intro R (And.intro post h)
    let coind_thm = mk_theorem(
        s.coind_name(),
        vec![
            binder(REL_R, rel_ty.clone(), SurfaceBinderInfo::Explicit),
            binder(HYP_POST, post_of(ident(REL_R)), SurfaceBinderInfo::Explicit),
        ],
        s.forall_vars(arrow(s.applied(ident(REL_R)), s.applied(gfp()))),
        lam(
            &lam_names,
            napp(
                "Exists.intro",
                vec![
                    ident(REL_R),
                    napp("And.intro", vec![ident(HYP_POST), ident(HYP_H)]),
                ],
            ),
        ),
    );

    // ── 4. monotonicity of the generated functor ───────────────────────
    // theorem P.F_mono (R) (S) (hle : ∀ v⃗, R v⃗ → S v⃗)
    //     : ∀ v⃗, P.F R v⃗ → P.F S v⃗ :=
    //   fun v⃗ h => ⟨…, hle e⃗ h.right…, …⟩
    //
    // Sound by construction: every recursive premise is a POSITIVE,
    // fully-applied occurrence (the envelope enforces it), so mapping each
    // through `hle` and rebuilding the conjunction is a proof.
    let mono_val = lam(
        &lam_names,
        right_nest(
            s.premises
                .iter()
                .enumerate()
                .map(|(i, p)| {
                    let acc = conjunct(ident(HYP_H), i, j);
                    match p {
                        Premise::Rec(args) => {
                            let mut a = args.clone();
                            a.push(acc);
                            napp(HYP_LE, a)
                        }
                        Premise::Plain(_) => acc,
                    }
                })
                .collect(),
            |a, b| napp("And.intro", vec![a, b]),
        ),
    );
    let mono_thm = mk_theorem(
        s.mono_name(),
        vec![
            binder(REL_R, rel_ty.clone(), SurfaceBinderInfo::Explicit),
            binder(REL_S, rel_ty.clone(), SurfaceBinderInfo::Explicit),
            binder(
                HYP_LE,
                s.forall_vars(arrow(s.applied(ident(REL_R)), s.applied(ident(REL_S)))),
                SurfaceBinderInfo::Explicit,
            ),
        ],
        s.forall_vars(arrow(
            s.applied(napp(&s.f_name(), vec![ident(REL_R)])),
            s.applied(napp(&s.f_name(), vec![ident(REL_S)])),
        )),
        mono_val,
    );

    // ── 5. the gfp is a post-fixpoint (the destructor) ─────────────────
    // theorem P.unfold : ∀ v⃗, P v⃗ → P.F P v⃗ :=
    //   fun v⃗ h => Exists.elim h (fun R hR =>
    //     P.F_mono R P (P.coind R hR.left) v⃗ (hR.left v⃗ hR.right))
    let post_hyp = napp("And.left", vec![ident(HYP_HR)]);
    let carrier_hyp = napp("And.right", vec![ident(HYP_HR)]);
    let mut mono_args = vec![
        ident(REL_R),
        gfp(),
        napp(&s.coind_name(), vec![ident(REL_R), post_hyp.clone()]),
    ];
    mono_args.extend(s.var_args());
    mono_args.push(app(
        post_hyp,
        s.var_args().into_iter().chain([carrier_hyp]).collect(),
    ));
    let unfold_thm = mk_theorem(
        s.unfold_name(),
        Vec::new(),
        s.forall_vars(arrow(
            s.applied(gfp()),
            s.applied(napp(&s.f_name(), vec![gfp()])),
        )),
        lam(
            &lam_names,
            napp(
                "Exists.elim",
                vec![
                    ident(HYP_H),
                    lam(&[REL_R, HYP_HR], napp(&s.mono_name(), mono_args)),
                ],
            ),
        ),
    );

    // ── 6. the gfp is a pre-fixpoint ───────────────────────────────────
    // theorem P.fold : ∀ v⃗, P.F P v⃗ → P v⃗ :=
    //   P.coind (P.F P) (fun v⃗ h => P.F_mono P (P.F P) P.unfold v⃗ h)
    let f_gfp = || napp(&s.f_name(), vec![gfp()]);
    let mut fold_mono_args = vec![gfp(), f_gfp(), ident(&s.unfold_name())];
    fold_mono_args.extend(s.var_args());
    fold_mono_args.push(ident(HYP_H));
    let fold_thm = mk_theorem(
        s.fold_name(),
        Vec::new(),
        s.forall_vars(arrow(s.applied(f_gfp()), s.applied(gfp()))),
        napp(
            &s.coind_name(),
            vec![
                f_gfp(),
                lam(&lam_names, napp(&s.mono_name(), fold_mono_args)),
            ],
        ),
    );

    // ── 7. the declared constructor ────────────────────────────────────
    // theorem P.c {v⃗ : T⃗} : Prem₁ → … → Premⱼ → P v⃗ :=
    //   fun h₁ … hⱼ => P.fold v⃗ ⟨h₁, …, hⱼ⟩
    let hyp_names: Vec<String> = (0..j).map(|i| format!("hprem_coind{i}")).collect();
    let ctor_ty = s
        .declared_premises()
        .into_iter()
        .rev()
        .fold(s.applied(gfp()), |acc, p| arrow(p, acc));
    let packed = right_nest(hyp_names.iter().map(|h| ident(h)).collect(), |a, b| {
        napp("And.intro", vec![a, b])
    });
    let hyp_refs: Vec<&str> = hyp_names.iter().map(String::as_str).collect();
    let ctor_thm = mk_theorem(
        format!("{}.{}", s.qname, s.ctor),
        s.idx_binders(SurfaceBinderInfo::Implicit),
        ctor_ty,
        lam(
            &hyp_refs,
            app(
                ident(&s.fold_name()),
                s.var_args().into_iter().chain([packed]).collect(),
            ),
        ),
    );

    vec![
        f_def, gfp_def, coind_thm, mono_thm, unfold_thm, fold_thm, ctor_thm,
    ]
}
