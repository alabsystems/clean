// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Recursion-through-projection desugaring (Track H, task 1).
//!
//! A recursive method may match on a *projection* of its decreasing binder
//! rather than on the binder itself, and reconstruct a wrapper around the
//! strictly-smaller sub-component for the recursive call:
//!
//! ```text
//! structure Box where
//!   data : Lst
//!
//! def Box.len (b : Box) : Nat :=
//!   match b.data with
//!   | Lst.nil      => 0
//!   | Lst.cons _ t => Nat.succ (Box.len { data := t })
//! ```
//!
//! This is *not* structural recursion on `Box` (a non-recursive single-field
//! struct): `Box.rec` performs only one level of case analysis, and the
//! recursive call passes a freshly-built `{ data := t }`, not a sub-term of
//! `b`. The recursion is genuinely structural on the **projected field**
//! `b.data : Lst`. The existing structural-recursion lowering only fires when
//! the match scrutinee *is* the decreasing binder (`is_match_on_decreasing_arg`)
//! and the recursive call passes a bound pattern variable at the decreasing
//! position, so the def above never installs a `RecursiveDefContext` and the
//! self-name `Box.len` is left unresolved (`UnknownIdent`).
//!
//! This module is a **purely syntactic pre-pass** that rewrites the def into an
//! auxiliary equation-form def recursing structurally on the projected field,
//! plus a thin wrapper:
//!
//! ```text
//! def Box.len.go : Lst -> Nat
//!   | Lst.nil      => 0
//!   | Lst.cons _ t => Nat.succ (Box.len.go t)
//!
//! def Box.len (b : Box) : Nat := Box.len.go b.data
//! ```
//!
//! The auxiliary def routes through the *already-proven* equation-form
//! structural `.rec` lowering (`normalize_equation_def` + `T.rec`). No new
//! kernel reducer, no faked termination, no `sorry`: soundness is inherited
//! wholesale from the existing single-argument structural-recursion path that
//! `Box.len.go` reuses verbatim.
//!
//! SCOPE (conservative — bails to `None`, leaving the original def untouched,
//! on anything outside this envelope):
//!
//! * Exactly one explicit value parameter `b : S`.
//! * Body (after peeling redundant parens) is `match b.<field> with <arms>`,
//!   i.e. the scrutinee is a *named-field projection of the sole binder*.
//! * The projected field's inductive type is recoverable from the arm
//!   constructor patterns (a non-parameterized inductive head such as `Lst` or
//!   `Nat`) — this becomes the auxiliary binder's type, so the projected field's
//!   declared type need not be consulted.
//! * Every self-recursive call `F <arg>` passes, at the single argument
//!   position, a single-field struct literal `{ <field> := X }` (no `with`
//!   base, exactly the projected field assigned) — the wrapper rebuild shape.
//!   Each such call is rewritten to `F.go X`.

use clean_parser::{
    Projection, Span, SurfaceArg, SurfaceBinder, SurfaceBinderInfo, SurfaceDecl, SurfaceExpr,
    SurfaceMatchArm, SurfacePattern,
};

/// If `decl` is a recursion-through-projection `def`, return the desugared
/// `[aux, wrapper]` declaration pair; otherwise return `None`.
///
/// The returned decls are intended to be elaborated and registered in order
/// (aux first, then wrapper) so the wrapper can reference the aux.
pub(crate) fn desugar_projection_recursion(decl: &SurfaceDecl) -> Option<Vec<SurfaceDecl>> {
    let SurfaceDecl::Def {
        span,
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

    // Conservative gating: no attributes / termination hints / where-clauses /
    // universe params. Those interact with elaboration in ways this purely
    // syntactic split does not model, so we decline rather than risk changing
    // behaviour for them.
    if !attrs.is_empty()
        || !where_decls.is_empty()
        || !universe_params.is_empty()
        || termination.termination_by.is_some()
        || termination.decreasing_by.is_some()
    {
        return None;
    }

    // Exactly one explicit value parameter `b : S`.
    let [binder] = binders.as_slice() else {
        return None;
    };
    if binder.info != SurfaceBinderInfo::Explicit {
        return None;
    }
    let binder_name = binder.name.as_str();

    // Body must be `match b.<field> with <arms>` (peel redundant parens).
    let body = peel_parens(val);
    let SurfaceExpr::Match(_, None, scrutinee, arms) = body else {
        return None;
    };
    let (scrut_binder, field) = match_projection_of(scrutinee)?;
    if scrut_binder != binder_name {
        return None;
    }

    // Recover the projected field's inductive type name from the arm
    // constructor patterns. All structural arms must agree on the same head.
    let ind_name = inductive_from_arms(arms)?;

    // The function's self-name. For a namespaced def the name is the fully
    // dotted string (e.g. "Box.len"); recursive calls appear either as that
    // ident or as a `Proj` spelling of the same dotted path.
    let self_name = name.as_str();
    let aux_name = format!("{self_name}.go");

    // Rewrite every recursive call `F { <field> := X }` -> `F.go X` across all
    // arm bodies. If ANY recursive call is present but does not match the
    // rebuild shape, bail (the def is outside our sound envelope).
    let mut rewriter = CallRewriter {
        self_name,
        field: &field,
        aux_name: &aux_name,
        saw_unhandled_rec_call: false,
        saw_handled_rec_call: false,
    };
    let mut new_arms = Vec::with_capacity(arms.len());
    for arm in arms {
        let new_body = rewriter.rewrite(&arm.body);
        new_arms.push(SurfaceMatchArm {
            span: arm.span,
            pattern: arm.pattern.clone(),
            body: new_body,
        });
    }
    if rewriter.saw_unhandled_rec_call {
        return None;
    }

    // Must actually be recursive (otherwise this is a plain projection match the
    // existing non-recursive path already handles — don't disturb it).
    if !rewriter.saw_handled_rec_call {
        return None;
    }

    // Auxiliary equation-form def: `def F.go : Ind -> Ret | <arms'>`.
    // The return type is the original def's return type annotation. We require
    // it to be present so the aux's arrow type is fully determined (the
    // equation-form normalizer needs an annotated arrow to peel the domain).
    let ret_ty = ty.as_deref()?;
    let aux_ty = SurfaceExpr::Arrow(
        Span::dummy(),
        Box::new(SurfaceExpr::ident(&ind_name)),
        Box::new(ret_ty.clone()),
    );
    // Equation-form value: a single-`_x` pattern-match lambda over the arms,
    // exactly the shape the def parser emits for `def F.go : A -> B | ...`,
    // which `normalize_equation_def` recognizes and lowers via `Ind.rec`.
    let aux_val = SurfaceExpr::PatternMatchLambda(
        Span::dummy(),
        vec![SurfaceBinder::new("_x", None, SurfaceBinderInfo::Explicit)],
        Box::new(SurfaceExpr::Match(
            Span::dummy(),
            None,
            Box::new(SurfaceExpr::ident("_x")),
            new_arms,
        )),
    );
    let aux_decl = SurfaceDecl::Def {
        span: *span,
        name: aux_name.clone(),
        universe_params: Vec::new(),
        binders: Vec::new(),
        ty: Some(Box::new(aux_ty)),
        val: Box::new(aux_val),
        attrs: Vec::new(),
        termination: Default::default(),
        modifiers: *modifiers,
        where_decls: Vec::new(),
    };

    // Wrapper def: `def F (b : S) : Ret := F.go b.<field>`.
    let wrapper_body = SurfaceExpr::App(
        Span::dummy(),
        Box::new(SurfaceExpr::ident(&aux_name)),
        vec![SurfaceArg::positional(SurfaceExpr::Proj(
            Span::dummy(),
            Box::new(SurfaceExpr::ident(binder_name)),
            Projection::Named(field.clone()),
        ))],
    );
    let wrapper_decl = SurfaceDecl::Def {
        span: *span,
        name: name.clone(),
        universe_params: universe_params.clone(),
        binders: binders.clone(),
        ty: ty.clone(),
        val: Box::new(wrapper_body),
        attrs: attrs.clone(),
        termination: Default::default(),
        modifiers: *modifiers,
        where_decls: Vec::new(),
    };

    Some(vec![aux_decl, wrapper_decl])
}

/// Peel redundant `Paren` / `Ascription` wrappers that do not change identity.
fn peel_parens(e: &SurfaceExpr) -> &SurfaceExpr {
    match e {
        SurfaceExpr::Paren(_, inner) => peel_parens(inner),
        _ => e,
    }
}

/// Recognize `<ident>.<named-field>` and return `(binder_name, field_name)`.
fn match_projection_of(e: &SurfaceExpr) -> Option<(&str, String)> {
    match peel_parens(e) {
        SurfaceExpr::Proj(_, base, Projection::Named(field)) => {
            if let SurfaceExpr::Ident(_, name) = peel_parens(base) {
                Some((name.as_str(), field.clone()))
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Recover the inductive type name shared by all constructor-pattern arms.
///
/// Constructor patterns are spelled either as `Ctor("Ind.ctor", _)` or, for
/// nullary constructors, as `Var("Ind.ctor")` (the parser keeps a dotted,
/// argument-less constructor as a `Var`). The inductive head is the dotted
/// prefix. All structural arms must agree; wildcard / plain-variable arms are
/// permitted (they impose no constraint). Returns `None` if no constructor
/// pattern is present or the heads disagree.
fn inductive_from_arms(arms: &[SurfaceMatchArm]) -> Option<String> {
    let mut ind: Option<String> = None;
    for arm in arms {
        let ctor_name = match &arm.pattern {
            SurfacePattern::Ctor(name, _) => Some(name.as_str()),
            SurfacePattern::Var(name) if name.contains('.') => Some(name.as_str()),
            _ => None,
        };
        if let Some(ctor_name) = ctor_name {
            let head = ctor_name.rsplit_once('.').map(|(h, _)| h)?;
            match &ind {
                None => ind = Some(head.to_owned()),
                Some(existing) if existing == head => {}
                Some(_) => return None, // disagreeing heads
            }
        }
    }
    ind
}

/// Rewrites recursive calls `F { field := X }` into `F.go X` within arm bodies.
struct CallRewriter<'a> {
    self_name: &'a str,
    field: &'a str,
    aux_name: &'a str,
    /// Set when a recursive call to `self_name` was found that does NOT match
    /// the `{ field := X }` rebuild shape — signals "outside the sound
    /// envelope", and the caller bails.
    saw_unhandled_rec_call: bool,
    /// Set when at least one recursive call WAS rewritten.
    saw_handled_rec_call: bool,
}

impl<'a> CallRewriter<'a> {
    fn rewrite(&mut self, e: &SurfaceExpr) -> SurfaceExpr {
        match e {
            SurfaceExpr::App(span, func, args) => {
                // Is this a self-recursive call?
                if self.is_self_ref(peel_parens(func)) {
                    if let Some(inner) = self.rebuild_arg(args) {
                        self.saw_handled_rec_call = true;
                        return SurfaceExpr::App(
                            *span,
                            Box::new(SurfaceExpr::ident(self.aux_name)),
                            vec![SurfaceArg::positional(self.rewrite(&inner))],
                        );
                    }
                    // A recursive call that is NOT the rebuild shape: outside
                    // our envelope.
                    self.saw_unhandled_rec_call = true;
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
            // A bare self-name reference that is not applied to the rebuild
            // shape escapes the wrapper — outside our envelope.
            SurfaceExpr::Ident(_, name) if name == self.self_name => {
                self.saw_unhandled_rec_call = true;
                e.clone()
            }
            SurfaceExpr::Proj(_, _, _) if self.is_self_ref(e) => {
                self.saw_unhandled_rec_call = true;
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
            // Other compound forms: recurse structurally only where a recursive
            // call could plausibly hide. To stay conservative we treat any
            // self-reference encountered in an un-handled position (above) as
            // "unhandled". Leaf/opaque forms are returned unchanged.
            _ => e.clone(),
        }
    }

    /// Whether `func` names the function being defined (ident or dotted Proj).
    fn is_self_ref(&self, func: &SurfaceExpr) -> bool {
        match func {
            SurfaceExpr::Ident(_, name) => name == self.self_name,
            SurfaceExpr::Proj(_, _, _) => {
                qualified_name_from_proj(func).as_deref() == Some(self.self_name)
            }
            SurfaceExpr::Paren(_, inner) => self.is_self_ref(inner),
            _ => false,
        }
    }

    /// If `args` is exactly one positional `{ <field> := X }` struct literal
    /// (no `with` base, the sole field being the projected one), return `X`.
    fn rebuild_arg(&self, args: &[SurfaceArg]) -> Option<SurfaceExpr> {
        let [arg] = args else {
            return None;
        };
        if arg.name.is_some() {
            return None;
        }
        let SurfaceExpr::StructLit { base, fields, .. } = peel_parens(&arg.expr) else {
            return None;
        };
        if base.is_some() {
            return None;
        }
        let [field_assign] = fields.as_slice() else {
            return None;
        };
        if field_assign.name != self.field {
            return None;
        }
        Some(field_assign.val.clone())
    }
}

/// Collect a dotted qualified name from a `Proj` spine, e.g.
/// `Proj(Ident("Box"), Named("len"))` -> `"Box.len"`. Returns `None` for
/// indexed projections or non-ident bases.
fn qualified_name_from_proj(e: &SurfaceExpr) -> Option<String> {
    match e {
        SurfaceExpr::Ident(_, name) => Some(name.clone()),
        SurfaceExpr::Proj(_, base, Projection::Named(field)) => {
            let base_name = qualified_name_from_proj(base)?;
            Some(format!("{base_name}.{field}"))
        }
        SurfaceExpr::Paren(_, inner) => qualified_name_from_proj(inner),
        _ => None,
    }
}
