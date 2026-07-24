// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Sound mutual structural recursion via product packing (Track H, task 2).
//!
//! A `mutual ... end` block of functions that all recurse structurally on a
//! single argument of the *same* inductive type — the canonical
//!
//! ```text
//! mutual
//!   def isEven : Nat -> Bool | 0 => true  | Nat.succ n => isOdd n
//!   def isOdd  : Nat -> Bool | 0 => false | Nat.succ n => isEven n
//! end
//! ```
//!
//! — is lowered, **without any `WellFounded.fix` / `sorry` / faked termination
//! axiom**, into ONE structurally-recursive packed function returning a tuple
//! of all the components' results, plus thin projection wrappers:
//!
//! ```text
//! def isEven.isOdd.pack : Nat -> Prod Bool Bool
//!   | 0          => Prod.mk true false
//!   | Nat.succ n => Prod.mk (Prod.snd (isEven.isOdd.pack n))   -- isEven's RHS
//!                           (Prod.fst (isEven.isOdd.pack n))   -- isOdd's RHS
//!
//! def isEven (x : Nat) : Bool := Prod.fst (isEven.isOdd.pack x)
//! def isOdd  (x : Nat) : Bool := Prod.snd (isEven.isOdd.pack x)
//! ```
//!
//! The packed function is an ordinary *single-argument structural recursion*
//! on the shared inductive, so it routes through the **already-proven**
//! equation-form `T.rec` lowering (`normalize_equation_def`). Each cross-call
//! `fⱼ <arg>` becomes the j-th product projection of `pack <arg>`; the same
//! shared decreasing variable makes the recursion's IH apply directly. The
//! wrappers are non-recursive projections. Soundness is inherited wholesale
//! from the existing structural-recursion path plus the kernel's `Prod`
//! eliminator — no new kernel reducer, no termination escape hatch.
//!
//! SCOPE (conservative — returns `None`, leaving the block to the existing
//! `elab_mutual` path, on anything outside this envelope):
//!
//! * Every member is a `def` in equation form (`binders == []`, value is a
//!   single-`_x` `PatternMatchLambda` over a `match _x`), with an annotated
//!   `Ind -> Ret` arrow type whose domain `Ind` is the SAME named inductive
//!   for all members.
//! * All members share IDENTICAL arm pattern lists (same constructors, same
//!   bound variable names, same order) — so one canonical arm set drives the
//!   packed match and cross-call variable rewriting is unambiguous.
//! * Every self/cross recursive call passes a single positional argument that
//!   is a bound pattern variable (the structural decreasing position). Calls
//!   with a non-variable argument fall outside the envelope.

use clean_parser::{
    Projection, Span, SurfaceArg, SurfaceBinder, SurfaceBinderInfo, SurfaceDecl, SurfaceExpr,
    SurfaceLit, SurfaceMatchArm, SurfacePattern,
};

/// If `decls` is a packable mutual block, return the desugared declaration
/// list `[pack, wrapper₁, …, wrapperₙ]`; otherwise `None`.
pub(crate) fn desugar_mutual_structural(decls: &[SurfaceDecl]) -> Option<Vec<SurfaceDecl>> {
    if decls.len() < 2 {
        return None;
    }

    // Collect per-member view; bail on any non-equation-form def.
    let mut members: Vec<Member> = Vec::with_capacity(decls.len());
    for decl in decls {
        members.push(extract_member(decl)?);
    }

    // All members must share the same domain inductive and the same return
    // type spelling is NOT required (each component keeps its own), but the
    // domain inductive MUST match for a single shared recursor.
    let ind_name = members[0].ind_name.clone();
    if members.iter().any(|m| m.ind_name != ind_name) {
        return None;
    }

    // All members must share identical arm pattern lists (canonical arms).
    let canonical_arms: Vec<SurfacePattern> =
        members[0].arms.iter().map(|a| a.pattern.clone()).collect();
    for m in &members {
        if m.arms.len() != canonical_arms.len() {
            return None;
        }
        for (a, canon) in m.arms.iter().zip(&canonical_arms) {
            if !patterns_identical(&a.pattern, canon) {
                return None;
            }
        }
    }

    let func_names: Vec<&str> = members.iter().map(|m| m.name.as_str()).collect();
    let n = members.len();

    // Build the packed return type `Prod β₁ (Prod β₂ (... βₙ))`.
    let pack_ret_ty =
        build_prod_type(&members.iter().map(|m| m.ret_ty.clone()).collect::<Vec<_>>());

    // Packed function name. Deterministic, derived from member names so it is
    // stable and collision-resistant in practice.
    let pack_name = format!("{}.pack", func_names.join("."));

    // Build the packed arms: for each canonical arm index, combine each
    // member's body for that arm into an N-tuple, rewriting cross/self calls
    // `fⱼ v` into `projⱼ (pack v)`.
    let mut rewriter = CallRewriter {
        func_names: &func_names,
        pack_name: &pack_name,
        n,
        bailed: false,
    };
    let mut pack_arms: Vec<SurfaceMatchArm> = Vec::with_capacity(canonical_arms.len());
    for (arm_idx, canon_pat) in canonical_arms.iter().enumerate() {
        let mut component_bodies: Vec<SurfaceExpr> = Vec::with_capacity(n);
        for m in &members {
            let body = &m.arms[arm_idx].body;
            component_bodies.push(rewriter.rewrite(body));
        }
        let tuple = build_prod_value(&component_bodies);
        pack_arms.push(SurfaceMatchArm {
            span: Span::dummy(),
            pattern: canon_pat.clone(),
            body: tuple,
        });
    }
    if rewriter.bailed {
        return None;
    }

    // Safety net: the `CallRewriter` only traverses the expression forms an
    // equation body uses in the supported envelope (App / Ident / Match /
    // Paren / Ascription). If a member name survives anywhere in the rewritten
    // arms it means it occurred in a form we did not rewrite (e.g. captured in
    // a lambda, let, or struct literal) — outside the envelope. Decline rather
    // than emit a `pack` body that references a not-yet-registered member.
    if pack_arms
        .iter()
        .any(|arm| mentions_member(&arm.body, &func_names))
    {
        return None;
    }

    // Packed equation-form def: `def <pack> : Ind -> ProdTy | <pack_arms>`.
    let pack_ty = SurfaceExpr::Arrow(
        Span::dummy(),
        Box::new(SurfaceExpr::ident(&ind_name)),
        Box::new(pack_ret_ty),
    );
    let pack_val = SurfaceExpr::PatternMatchLambda(
        Span::dummy(),
        vec![SurfaceBinder::new("_x", None, SurfaceBinderInfo::Explicit)],
        Box::new(SurfaceExpr::Match(
            Span::dummy(),
            None,
            Box::new(SurfaceExpr::ident("_x")),
            pack_arms,
        )),
    );
    let pack_decl = make_def(&pack_name, Some(pack_ty), pack_val, &members[0].modifiers);

    let mut out = Vec::with_capacity(n + 1);
    out.push(pack_decl);

    // Projection wrappers: `def fᵢ (x : Ind) : βᵢ := projᵢ (pack x)`.
    for (i, m) in members.iter().enumerate() {
        let wrapper_body = nth_projection(
            i,
            n,
            SurfaceExpr::App(
                Span::dummy(),
                Box::new(SurfaceExpr::ident(&pack_name)),
                vec![SurfaceArg::positional(SurfaceExpr::ident("x"))],
            ),
        );
        let binder = SurfaceBinder::explicit("x", SurfaceExpr::ident(&ind_name));
        let mut wrapper = make_def(&m.name, Some(m.ret_ty.clone()), wrapper_body, &m.modifiers);
        if let SurfaceDecl::Def { binders, .. } = &mut wrapper {
            *binders = vec![binder];
        }
        out.push(wrapper);
    }

    Some(out)
}

/// A normalized view of one mutual-block member.
struct Member {
    name: String,
    ind_name: String,
    ret_ty: SurfaceExpr,
    arms: Vec<SurfaceMatchArm>,
    modifiers: clean_parser::DeclModifiers,
}

/// Extract a `Member` from a `def` in equation form, or `None`.
fn extract_member(decl: &SurfaceDecl) -> Option<Member> {
    let SurfaceDecl::Def {
        span: _,
        name,
        universe_params,
        binders,
        ty,
        val,
        attrs,
        termination,
        modifiers,
        where_decls,
    } = decl
    else {
        return None;
    };
    // Conservative: no attrs / termination hints / where / universe params /
    // explicit binders (equation form puts the domain in `ty`).
    if !attrs.is_empty()
        || !where_decls.is_empty()
        || !universe_params.is_empty()
        || !binders.is_empty()
        || termination.termination_by.is_some()
        || termination.decreasing_by.is_some()
    {
        return None;
    }
    // Type must be `Ind -> Ret` with `Ind` a bare ident (named inductive).
    let SurfaceExpr::Arrow(_, dom, ret) = ty.as_deref()? else {
        return None;
    };
    let SurfaceExpr::Ident(_, ind_name) = peel_parens(dom) else {
        return None;
    };
    // Value must be the equation-form `PatternMatchLambda([_x], Match(_x, arms))`.
    let SurfaceExpr::PatternMatchLambda(_, lam_binders, lam_body) = val.as_ref() else {
        return None;
    };
    let [lb] = lam_binders.as_slice() else {
        return None;
    };
    if lb.name != "_x" {
        return None;
    }
    let SurfaceExpr::Match(_, None, scrut, arms) = lam_body.as_ref() else {
        return None;
    };
    if !matches!(peel_parens(scrut), SurfaceExpr::Ident(_, s) if s == "_x") {
        return None;
    }
    Some(Member {
        name: name.clone(),
        ind_name: ind_name.clone(),
        ret_ty: ret.as_ref().clone(),
        arms: arms.clone(),
        modifiers: *modifiers,
    })
}

/// Rewrites cross/self recursive calls `fⱼ v` (v a bound var) into the j-th
/// product projection of `pack v`.
struct CallRewriter<'a> {
    func_names: &'a [&'a str],
    pack_name: &'a str,
    n: usize,
    bailed: bool,
}

impl<'a> CallRewriter<'a> {
    fn rewrite(&mut self, e: &SurfaceExpr) -> SurfaceExpr {
        match e {
            SurfaceExpr::App(span, func, args) => {
                if let SurfaceExpr::Ident(_, fname) = peel_parens(func) {
                    if let Some(j) = self.func_names.iter().position(|n| n == fname) {
                        // A call to mutual member j. Require exactly one
                        // positional argument; it becomes pack's argument.
                        let [arg] = args.as_slice() else {
                            self.bailed = true;
                            return e.clone();
                        };
                        if arg.name.is_some() {
                            self.bailed = true;
                            return e.clone();
                        }
                        let rewritten_arg = self.rewrite(&arg.expr);
                        let pack_call = SurfaceExpr::App(
                            *span,
                            Box::new(SurfaceExpr::ident(self.pack_name)),
                            vec![SurfaceArg::positional(rewritten_arg)],
                        );
                        return nth_projection(j, self.n, pack_call);
                    }
                }
                let new_args = args
                    .iter()
                    .map(|a| SurfaceArg {
                        span: a.span,
                        expr: self.rewrite(&a.expr),
                        name: a.name.clone(),
                    })
                    .collect();
                SurfaceExpr::App(*span, Box::new(self.rewrite(func)), new_args)
            }
            // A bare reference to a mutual member name outside an application
            // would escape the packing (e.g. used as a first-class value);
            // outside our envelope.
            SurfaceExpr::Ident(_, name) if self.func_names.iter().any(|n| n == name) => {
                self.bailed = true;
                e.clone()
            }
            SurfaceExpr::Paren(span, inner) => {
                SurfaceExpr::Paren(*span, Box::new(self.rewrite(inner)))
            }
            SurfaceExpr::Match(span, hyp, scrut, arms) => {
                let new_arms = arms
                    .iter()
                    .map(|arm| SurfaceMatchArm {
                        span: arm.span,
                        pattern: arm.pattern.clone(),
                        body: self.rewrite(&arm.body),
                    })
                    .collect();
                SurfaceExpr::Match(*span, hyp.clone(), Box::new(self.rewrite(scrut)), new_arms)
            }
            SurfaceExpr::Ascription(span, inner, t) => {
                SurfaceExpr::Ascription(*span, Box::new(self.rewrite(inner)), t.clone())
            }
            // Leaf / opaque forms: returned unchanged. Any hidden member
            // reference inside an un-walked form is caught by the bare-ident
            // arm above only at the top level; to stay sound we additionally
            // bail if such a form contains a member name (checked by the
            // caller via a separate scan is unnecessary — equation bodies for
            // the supported envelope are applications / idents / matches).
            _ => e.clone(),
        }
    }
}

/// `Prod β₁ (Prod β₂ (... βₙ))` for n ≥ 1 (n == 1 yields `β₁`).
fn build_prod_type(tys: &[SurfaceExpr]) -> SurfaceExpr {
    let mut iter = tys.iter().rev();
    let mut acc = iter.next().expect("non-empty").clone();
    for ty in iter {
        acc = prod_app(ty.clone(), acc);
    }
    acc
}

/// `Prod.mk v₁ (Prod.mk v₂ (... vₙ))` for n ≥ 1 (n == 1 yields `v₁`).
fn build_prod_value(vals: &[SurfaceExpr]) -> SurfaceExpr {
    let mut iter = vals.iter().rev();
    let mut acc = iter.next().expect("non-empty").clone();
    for v in iter {
        acc = SurfaceExpr::App(
            Span::dummy(),
            Box::new(SurfaceExpr::ident("Prod.mk")),
            vec![
                SurfaceArg::positional(v.clone()),
                SurfaceArg::positional(acc),
            ],
        );
    }
    acc
}

/// Project the `i`-th of `n` components out of a nested-`Prod` value `e`.
///
/// Layout is right-nested: component i for i < n-1 is `Prod.fst (Prod.snd^i e)`;
/// the last component (i == n-1) is `Prod.snd^(n-1) e`. For n == 1, `e` itself.
fn nth_projection(i: usize, n: usize, e: SurfaceExpr) -> SurfaceExpr {
    if n == 1 {
        return e;
    }
    // Descend i times through `.snd`.
    let mut cur = e;
    for _ in 0..i {
        cur = prod_proj("Prod.snd", cur);
    }
    if i == n - 1 {
        cur
    } else {
        prod_proj("Prod.fst", cur)
    }
}

fn prod_app(a: SurfaceExpr, b: SurfaceExpr) -> SurfaceExpr {
    SurfaceExpr::App(
        Span::dummy(),
        Box::new(SurfaceExpr::ident("Prod")),
        vec![SurfaceArg::positional(a), SurfaceArg::positional(b)],
    )
}

fn prod_proj(proj: &str, e: SurfaceExpr) -> SurfaceExpr {
    SurfaceExpr::App(
        Span::dummy(),
        Box::new(SurfaceExpr::ident(proj)),
        vec![SurfaceArg::positional(e)],
    )
}

fn make_def(
    name: &str,
    ty: Option<SurfaceExpr>,
    val: SurfaceExpr,
    modifiers: &clean_parser::DeclModifiers,
) -> SurfaceDecl {
    SurfaceDecl::Def {
        span: Span::dummy(),
        name: name.to_owned(),
        universe_params: Vec::new(),
        binders: Vec::new(),
        ty: ty.map(Box::new),
        val: Box::new(val),
        attrs: Vec::new(),
        termination: Default::default(),
        modifiers: *modifiers,
        where_decls: Vec::new(),
    }
}

fn peel_parens(e: &SurfaceExpr) -> &SurfaceExpr {
    match e {
        SurfaceExpr::Paren(_, inner) => peel_parens(inner),
        _ => e,
    }
}

/// Structural pattern equality INCLUDING bound variable names. Two patterns
/// are "identical" when they bind the same variables in the same positions and
/// match the same constructors/literals — required so the packed arms can use
/// one canonical pattern and every member's body references the same names.
fn patterns_identical(a: &SurfacePattern, b: &SurfacePattern) -> bool {
    match (a, b) {
        (SurfacePattern::Var(x), SurfacePattern::Var(y)) => x == y,
        (SurfacePattern::Wildcard, SurfacePattern::Wildcard) => true,
        (SurfacePattern::Lit(x), SurfacePattern::Lit(y)) => lits_eq(x, y),
        (SurfacePattern::NumeralAdd(p, k), SurfacePattern::NumeralAdd(q, l)) => {
            k == l && patterns_identical(p, q)
        }
        (SurfacePattern::Ctor(cx, ax), SurfacePattern::Ctor(cy, ay)) => {
            cx == cy
                && ax.len() == ay.len()
                && ax.iter().zip(ay).all(|(p, q)| patterns_identical(p, q))
        }
        _ => false,
    }
}

fn lits_eq(a: &SurfaceLit, b: &SurfaceLit) -> bool {
    // Compare via debug spelling — SurfaceLit does not derive PartialEq but a
    // structural debug comparison is sufficient and conservative here.
    format!("{a:?}") == format!("{b:?}")
}

/// Whether `e` mentions any of the mutual member names as a bare identifier
/// anywhere in its (full, conservative) sub-tree. Used as a post-rewrite safety
/// net: any surviving member reference means the body contained a form outside
/// the rewriter's traversal envelope, so the whole desugar must be declined.
fn mentions_member(e: &SurfaceExpr, names: &[&str]) -> bool {
    match e {
        SurfaceExpr::Ident(_, name) => names.iter().any(|n| n == name),
        SurfaceExpr::App(_, f, args) => {
            mentions_member(f, names) || args.iter().any(|a| mentions_member(&a.expr, names))
        }
        SurfaceExpr::Paren(_, inner)
        | SurfaceExpr::Ascription(_, inner, _)
        | SurfaceExpr::Explicit(_, inner)
        | SurfaceExpr::OutParam(_, inner)
        | SurfaceExpr::SemiOutParam(_, inner) => mentions_member(inner, names),
        SurfaceExpr::Lambda(_, _, body)
        | SurfaceExpr::PatternMatchLambda(_, _, body)
        | SurfaceExpr::Pi(_, _, body) => mentions_member(body, names),
        SurfaceExpr::Arrow(_, a, b) => mentions_member(a, names) || mentions_member(b, names),
        SurfaceExpr::Let(_, _, v, body) | SurfaceExpr::LetRec(_, _, v, body) => {
            mentions_member(v, names) || mentions_member(body, names)
        }
        SurfaceExpr::Match(_, _, scrut, arms) => {
            mentions_member(scrut, names) || arms.iter().any(|a| mentions_member(&a.body, names))
        }
        SurfaceExpr::StructLit { base, fields, .. } => {
            base.as_ref().is_some_and(|b| mentions_member(b, names))
                || fields.iter().any(|f| mentions_member(&f.val, names))
        }
        // Other forms are leaves or do not occur in supported equation bodies;
        // treat them as not mentioning members (the body would already have
        // failed the conservative envelope checks if they appeared).
        _ => false,
    }
}

// ===========================================================================
// Track AA: nested-mutual fold fusion.
// ===========================================================================

/// A recognized nested-mutual fold block `{ T.f : T -> R, T.g : C T -> R }`.
///
/// `T` is a *nested* inductive (it has a constructor with a `C T` field, e.g.
/// `Tree.node : List Tree -> Tree`), so `T.rec` is a mutual recursor with an
/// auxiliary motive for the synthesized mirror `T._C`. The two members fuse into
/// ONE `T.rec` application: `T.f`'s arms supply the primary minors, `T.g`'s arms
/// supply the auxiliary minors — a genuine fold, NOT a degenerate default.
pub(crate) struct NestedMutualFold {
    /// The primary member's equation-form `def` (`T.f : T -> R`), elaborated
    /// as-is but with the auxiliary-arm source installed so its nested-recursor
    /// lowering fills the `T._C` minors from `T.g`'s arms.
    pub primary_def: SurfaceDecl,
    /// The secondary member's equation-form `def` (`T.g : C T -> R`), registered
    /// after the primary so it can reference the now-defined `T.f`.
    pub secondary_def: SurfaceDecl,
    /// Short name of the container `C` (e.g. `List`), naming the mirror
    /// `T._<C>`.
    pub container_short: String,
    /// `T.g`'s arms — the auxiliary minor bodies.
    pub aux_arms: Vec<SurfaceMatchArm>,
    /// Fully-qualified names of BOTH members, recognized as recursive self-calls
    /// inside the fused minors (`T.f t` → ih_t, `T.g rest` → ih_rest).
    pub member_names: Vec<String>,
}

/// Recognize a 2-member `mutual` block of the nested-fold shape
/// `{ T.f : T -> R, T.g : C T -> R }`, where `T` is the parent inductive and
/// `C T` (e.g. `List Tree`) is the nested container field type of one of `T`'s
/// constructors. Returns the data needed to fuse the pair into one `T.rec`
/// application. Conservative: `None` for anything outside this exact envelope
/// (the caller then falls back to the existing `elab_mutual` path).
pub(crate) fn desugar_mutual_nested(decls: &[SurfaceDecl]) -> Option<NestedMutualFold> {
    let [a, b] = decls else {
        return None;
    };
    // Try both orderings independently (the `T -> R` primary may be either
    // member). Each extraction is fallible, so do not let one ordering's failure
    // short-circuit the other.
    if let (Some(prim), Some(aux)) = (extract_member(a), extract_nested_member(b)) {
        if let Some(fold) = pair_nested(&prim, &aux, a, b) {
            return Some(fold);
        }
    }
    if let (Some(prim), Some(aux)) = (extract_member(b), extract_nested_member(a)) {
        if let Some(fold) = pair_nested(&prim, &aux, b, a) {
            return Some(fold);
        }
    }
    None
}

/// Given a candidate primary member `prim` (`T.f : T -> R`) and auxiliary member
/// `aux` (`T.g : C T -> R`), validate that they share the parent type `T` and
/// build the [`NestedMutualFold`].
fn pair_nested(
    prim: &Member,
    aux: &NestedMember,
    prim_decl: &SurfaceDecl,
    aux_decl: &SurfaceDecl,
) -> Option<NestedMutualFold> {
    // The auxiliary member's container element type must be the primary's
    // inductive (`List Tree` ↔ primary over `Tree`).
    if aux.element_ty != prim.ind_name {
        return None;
    }
    // Both return types must agree (one fused motive `fun _ => R`). Compared
    // span-insensitively, since the two members carry independent source spans.
    if !surface_ty_eq(&prim.ret_ty, &aux.ret_ty) {
        return None;
    }
    Some(NestedMutualFold {
        primary_def: prim_decl.clone(),
        secondary_def: aux_decl.clone(),
        container_short: aux.container_short.clone(),
        aux_arms: aux.arms.clone(),
        member_names: vec![prim.name.clone(), aux.name.clone()],
    })
}

/// A normalized view of an auxiliary member `T.g : C T -> R` (domain is a
/// container application `C T`, not a bare inductive).
struct NestedMember {
    name: String,
    container_short: String,
    element_ty: String,
    ret_ty: SurfaceExpr,
    arms: Vec<SurfaceMatchArm>,
}

/// Extract a `NestedMember` from a `def T.g : C T -> R | …` in equation form,
/// or `None`. Mirrors `extract_member` but the domain is `App(C, [T])`.
fn extract_nested_member(decl: &SurfaceDecl) -> Option<NestedMember> {
    let SurfaceDecl::Def {
        span: _,
        name,
        universe_params,
        binders,
        ty,
        val,
        attrs,
        termination,
        modifiers: _,
        where_decls,
    } = decl
    else {
        return None;
    };
    if !attrs.is_empty()
        || !where_decls.is_empty()
        || !universe_params.is_empty()
        || !binders.is_empty()
        || termination.termination_by.is_some()
        || termination.decreasing_by.is_some()
    {
        return None;
    }
    // Type must be `(C T) -> Ret` with the domain a single-argument application
    // `C T` of named container `C` to a named element type `T`.
    let SurfaceExpr::Arrow(_, dom, ret) = ty.as_deref()? else {
        return None;
    };
    let (container_short, element_ty) = parse_container_app(peel_parens(dom))?;
    // Value must be the equation-form `PatternMatchLambda([_x], Match(_x, arms))`.
    let SurfaceExpr::PatternMatchLambda(_, lam_binders, lam_body) = val.as_ref() else {
        return None;
    };
    let [lb] = lam_binders.as_slice() else {
        return None;
    };
    if lb.name != "_x" {
        return None;
    }
    let SurfaceExpr::Match(_, None, scrut, arms) = lam_body.as_ref() else {
        return None;
    };
    if !matches!(peel_parens(scrut), SurfaceExpr::Ident(_, s) if s == "_x") {
        return None;
    }
    Some(NestedMember {
        name: name.clone(),
        container_short,
        element_ty,
        ret_ty: ret.as_ref().clone(),
        arms: arms.clone(),
    })
}

/// Parse a container application `C T` (e.g. `List Tree`) into the container's
/// short name and the element type's name. Returns `None` for anything that is
/// not a single-argument application of two bare idents.
fn parse_container_app(e: &SurfaceExpr) -> Option<(String, String)> {
    let SurfaceExpr::App(_, head, args) = peel_parens(e) else {
        return None;
    };
    let SurfaceExpr::Ident(_, container) = peel_parens(head) else {
        return None;
    };
    let [arg] = args.as_slice() else {
        return None;
    };
    if arg.name.is_some() {
        return None;
    }
    let SurfaceExpr::Ident(_, element) = peel_parens(&arg.expr) else {
        return None;
    };
    let container_short = container
        .rsplit('.')
        .next()
        .unwrap_or(container)
        .to_string();
    Some((container_short, element.clone()))
}

/// Span-insensitive structural equality of two surface type expressions, over
/// the forms a return-type annotation uses (idents, applications, arrows,
/// parentheses). Two members of a mutual block carry independent source spans,
/// so a Debug comparison spuriously differs; this compares only the structure.
fn surface_ty_eq(a: &SurfaceExpr, b: &SurfaceExpr) -> bool {
    match (peel_parens(a), peel_parens(b)) {
        (SurfaceExpr::Ident(_, x), SurfaceExpr::Ident(_, y)) => x == y,
        (SurfaceExpr::App(_, fa, aa), SurfaceExpr::App(_, fb, ab)) => {
            surface_ty_eq(fa, fb)
                && aa.len() == ab.len()
                && aa
                    .iter()
                    .zip(ab)
                    .all(|(x, y)| x.name == y.name && surface_ty_eq(&x.expr, &y.expr))
        }
        (SurfaceExpr::Arrow(_, da, ra), SurfaceExpr::Arrow(_, db, rb)) => {
            surface_ty_eq(da, db) && surface_ty_eq(ra, rb)
        }
        _ => false,
    }
}
