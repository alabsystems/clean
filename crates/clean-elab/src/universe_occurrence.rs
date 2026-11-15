// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Which file-declared universe names a declaration actually USES.
//!
//! Lean's rule for `universe u v w`: the command puts the names in scope; a
//! declaration's level parameters are the universe names that OCCUR in it
//! (`collectLevelParams` over the elaborated header and value, plus the used
//! section variables' types). `universe u v` followed by
//! `class MyLE (α : Type u)` is `MyLE.{u}` — `v` is not a parameter.
//!
//! Clean's `preprocess` used to merge EVERY declared universe into EVERY
//! declaration, so that class became `MyLE.{u, v}`. Measured 2026-09-10 with
//! passing controls (`universe u` alone; `Type*`): a later
//! `def useIt (α : Type u) [MyLE α] (a b : α) : Prop := MyLE.le a b` died at
//! the kernel with `Type mismatch: expected MyLE fvar#4, got MyLE fvar#4` —
//! the binder's `MyLE.{u, ?v₁}` and the body's `MyLE.{u, ?v₂}` carry two
//! level metavariables nothing can ever constrain, because the parameter
//! occurs nowhere. Two of the five pinned source-elab files declare unused
//! universes at file scope (`Mathlib/Logic/Function/Basic.lean`:
//! `universe u v w x`; `Mathlib/Logic/Unique.lean`: `universe u v w`, with
//! `structure Unique (α : Sort u)` — every `[Unique α]` binder in that file
//! took the defect).
//!
//! # Fail-closed direction
//!
//! The walk is SYNTACTIC and returns `None` when it meets a construct it does
//! not model (a tactic block, a `do` block, a `calc`, an interpolated string,
//! a syntax quotation). The caller then keeps the old, over-inclusive merge
//! for that one declaration — the behaviour every declaration had before this
//! module, so no declaration can lose a universe it uses. The one deliberate
//! exception is a structure FIELD DEFAULT written as a tactic block
//! (`lt_iff_le_not_ge := by intros; rfl`, Lean's `autoParam`): it contributes
//! nothing and does not poison the walk, because a proof of the field's type
//! cannot need a universe the field's type does not name.

use clean_parser::{
    LevelExpr, QAntiquotContent, SurfaceBinder, SurfaceDecl, SurfaceExpr, SurfacePattern,
    UniverseExpr,
};
use std::collections::HashSet;

/// Universe names occurring in the declaration's own syntax plus in the
/// binders it will be registered with (its own and the section variables
/// prepended to it). `None` when the walk could not see everything.
#[must_use]
pub(crate) fn used_universe_names(
    decl: &SurfaceDecl,
    binders: &[SurfaceBinder],
) -> Option<HashSet<String>> {
    let mut w = Walk {
        names: HashSet::new(),
        complete: true,
    };
    for b in binders {
        w.binder(b);
    }
    match decl {
        SurfaceDecl::Def {
            binders,
            ty,
            val,
            where_decls,
            ..
        } => {
            w.binders(binders);
            w.opt(ty.as_deref());
            w.expr(val);
            for wd in where_decls {
                w.binders(&wd.binders);
                w.opt(wd.ret_ty.as_deref());
                w.expr(&wd.body);
            }
        }
        SurfaceDecl::Theorem {
            binders,
            ty,
            proof,
            where_decls,
            ..
        } => {
            w.binders(binders);
            w.expr(ty);
            w.expr(proof);
            for wd in where_decls {
                w.binders(&wd.binders);
                w.opt(wd.ret_ty.as_deref());
                w.expr(&wd.body);
            }
        }
        SurfaceDecl::Axiom { binders, ty, .. } => {
            w.binders(binders);
            w.expr(ty);
        }
        SurfaceDecl::Opaque {
            binders, ty, val, ..
        } => {
            w.binders(binders);
            w.expr(ty);
            w.opt(val.as_deref());
        }
        SurfaceDecl::Inductive {
            binders, ty, ctors, ..
        }
        | SurfaceDecl::Coinductive {
            binders, ty, ctors, ..
        } => {
            w.binders(binders);
            w.expr(ty);
            for c in ctors {
                w.expr(&c.ty);
            }
        }
        SurfaceDecl::Structure {
            binders,
            extends,
            ty,
            fields,
            ..
        }
        | SurfaceDecl::Class {
            binders,
            extends,
            ty,
            fields,
            ..
        } => {
            w.binders(binders);
            for e in extends {
                w.expr(e);
            }
            w.opt(ty.as_deref());
            for f in fields {
                w.expr(&f.ty);
                if let Some(d) = &f.default {
                    w.field_default(d);
                }
            }
        }
        SurfaceDecl::Instance {
            binders,
            class_type,
            fields,
            ..
        } => {
            w.binders(binders);
            w.expr(class_type);
            for f in fields {
                w.expr(&f.val);
            }
        }
        // Not a declaration this analysis has a rule for: say so rather than
        // report an empty (and therefore universe-dropping) answer.
        _ => w.complete = false,
    }
    w.complete.then_some(w.names)
}

struct Walk {
    names: HashSet<String>,
    complete: bool,
}

impl Walk {
    fn level(&mut self, l: &LevelExpr) {
        match l {
            LevelExpr::Lit(_) => {}
            LevelExpr::Param(n) => {
                self.names.insert(n.to_string());
            }
            LevelExpr::Succ(a) => self.level(a),
            LevelExpr::Max(a, b) | LevelExpr::IMax(a, b) => {
                self.level(a);
                self.level(b);
            }
            LevelExpr::Antiquot(_) => self.complete = false,
        }
    }

    fn binders(&mut self, bs: &[SurfaceBinder]) {
        for b in bs {
            self.binder(b);
        }
    }

    fn binder(&mut self, b: &SurfaceBinder) {
        self.opt(b.ty.as_deref());
        self.opt(b.default.as_deref());
    }

    fn opt(&mut self, e: Option<&SurfaceExpr>) {
        if let Some(e) = e {
            self.expr(e);
        }
    }

    /// A field default: a tactic block here is blind, not poisoning (see the
    /// module doc); anything else is walked like any expression.
    fn field_default(&mut self, e: &SurfaceExpr) {
        if !matches!(e, SurfaceExpr::ByTactic(..)) {
            self.expr(e);
        }
    }

    fn pattern(&mut self, p: &SurfacePattern) {
        match p {
            SurfacePattern::Var(_)
            | SurfacePattern::Wildcard
            | SurfacePattern::Lit(_)
            | SurfacePattern::Ellipsis => {}
            SurfacePattern::Ctor(_, ps) => {
                for p in ps {
                    self.pattern(p);
                }
            }
            SurfacePattern::Inaccessible(e) | SurfacePattern::QPattern(e) => self.expr(e),
            SurfacePattern::NumeralAdd(p, _) | SurfacePattern::As(_, p) => self.pattern(p),
            SurfacePattern::Or(a, b) => {
                self.pattern(a);
                self.pattern(b);
            }
            SurfacePattern::StructInst { fields, ty, .. } => {
                for (_, pat) in fields {
                    self.pattern(pat);
                }
                if let Some(ty) = ty {
                    self.expr(ty);
                }
            }
        }
    }

    fn expr(&mut self, e: &SurfaceExpr) {
        match e {
            SurfaceExpr::Ident(..)
            | SurfaceExpr::SyntheticSorry(_)
            | SurfaceExpr::Lit(..)
            | SurfaceExpr::Hole(_)
            | SurfaceExpr::NamedHole(..) => {}
            SurfaceExpr::Universe(_, u) => match u {
                UniverseExpr::Prop
                | UniverseExpr::Type
                | UniverseExpr::TypeImplicit
                | UniverseExpr::SortImplicit
                | UniverseExpr::SortStar => {}
                UniverseExpr::TypeLevel(l) | UniverseExpr::Sort(l) => self.level(l),
            },
            SurfaceExpr::App(_, f, args) => {
                self.expr(f);
                for a in args {
                    self.expr(&a.expr);
                }
            }
            SurfaceExpr::Lambda(_, bs, body)
            | SurfaceExpr::PatternMatchLambda(_, bs, body)
            | SurfaceExpr::Pi(_, bs, body) => {
                self.binders(bs);
                self.expr(body);
            }
            SurfaceExpr::Arrow(_, a, b) | SurfaceExpr::Ascription(_, a, b) => {
                self.expr(a);
                self.expr(b);
            }
            SurfaceExpr::Let(_, b, v, body)
            | SurfaceExpr::Have(_, b, v, body)
            | SurfaceExpr::LetRec(_, b, v, body) => {
                self.binder(b);
                self.expr(v);
                self.expr(body);
            }
            SurfaceExpr::LetPattern(_, p, a, b, c) | SurfaceExpr::IfLet(_, p, a, b, c) => {
                self.pattern(p);
                self.expr(a);
                self.expr(b);
                self.expr(c);
            }
            SurfaceExpr::Paren(_, e)
            | SurfaceExpr::Explicit(_, e)
            | SurfaceExpr::OutParam(_, e)
            | SurfaceExpr::SemiOutParam(_, e)
            | SurfaceExpr::LiftMethod(_, e)
            | SurfaceExpr::NamedArg(_, _, e)
            | SurfaceExpr::Proj(_, e, _) => self.expr(e),
            SurfaceExpr::If(_, a, b, c) | SurfaceExpr::IfDecidable(_, _, a, b, c) => {
                self.expr(a);
                self.expr(b);
                self.expr(c);
            }
            SurfaceExpr::Match(_, _, d, arms) => {
                self.expr(d);
                for arm in arms {
                    self.pattern(&arm.pattern);
                    self.expr(&arm.body);
                }
            }
            SurfaceExpr::UniverseInst(_, e, levels) => {
                self.expr(e);
                for l in levels {
                    self.level(l);
                }
            }
            SurfaceExpr::QQuotation {
                inner, type_annot, ..
            } => {
                self.expr(inner);
                self.opt(type_annot.as_deref());
            }
            SurfaceExpr::QAntiquot { content, .. } => match content {
                QAntiquotContent::Simple(_) | QAntiquotContent::Splice { .. } => {}
                QAntiquotContent::Expr(e) => self.expr(e),
                QAntiquotContent::Typed { ty, .. } => self.expr(ty),
            },
            SurfaceExpr::StructLit {
                struct_type,
                base,
                fields,
                ..
            } => {
                self.opt(struct_type.as_deref());
                self.opt(base.as_deref());
                for f in fields {
                    self.expr(&f.val);
                }
            }
            SurfaceExpr::OpenIn { body, .. } => self.expr(body),
            // Opaque to this walk: a universe could hide inside, so the caller
            // must fall back to the over-inclusive merge.
            SurfaceExpr::ByTactic(..)
            | SurfaceExpr::CalcBlock(..)
            | SurfaceExpr::Do(..)
            | SurfaceExpr::InterpolatedStr { .. }
            | SurfaceExpr::SyntaxQuote(..) => self.complete = false,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_parser::parse_file;

    fn first_decl(src: &str) -> SurfaceDecl {
        parse_file(src)
            .expect("parses")
            .into_iter()
            .next()
            .expect("one declaration")
    }

    fn names(src: &str) -> Option<Vec<String>> {
        let d = first_decl(src);
        used_universe_names(&d, &[]).map(|s| {
            let mut v: Vec<String> = s.into_iter().collect();
            v.sort();
            v
        })
    }

    #[test]
    fn a_class_over_type_u_uses_exactly_u() {
        assert_eq!(
            names("class MyLE (α : Type u) where\n  le : α → α → Prop\n"),
            Some(vec!["u".to_string()])
        );
    }

    #[test]
    fn a_def_names_the_universes_of_its_binders_type_and_body() {
        assert_eq!(
            names("def f (α : Type u) : Type v := PUnit.{v+1}\n"),
            Some(vec!["u".to_string(), "v".to_string()])
        );
    }

    #[test]
    fn a_tactic_proof_is_opaque_so_the_caller_falls_back() {
        assert_eq!(
            names("theorem t (α : Type u) (a : α) : a = a := by rfl\n"),
            None
        );
    }

    #[test]
    fn a_tactic_field_default_is_blind_not_poisoning() {
        assert_eq!(
            names(
                "class Pre (α : Type u) extends LE α where\n  \
                 le_refl : ∀ a : α, a ≤ a := by intros; rfl\n"
            ),
            Some(vec!["u".to_string()])
        );
    }

    #[test]
    fn prepended_section_binders_count() {
        let d = first_decl("def g (a : α) : α := a\n");
        let sect = parse_file("variable {α : Type w}\n").expect("parses");
        let SurfaceDecl::Variable { binders, .. } = &sect[0] else {
            panic!("variable command")
        };
        let got = used_universe_names(&d, binders).expect("complete");
        assert_eq!(got, HashSet::from(["w".to_string()]));
    }

    #[test]
    fn max_and_succ_levels_are_walked() {
        assert_eq!(
            names("def h (α : Sort (max u (v+1))) : Sort (imax u w) := α\n"),
            Some(vec!["u".to_string(), "v".to_string(), "w".to_string()])
        );
    }
}
