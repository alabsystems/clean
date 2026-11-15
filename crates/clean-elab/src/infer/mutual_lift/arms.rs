// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Named equation lemmas `f.eq_N` of a lifted DEFINITION member (design §5.5
//! item 2, brick B3), the names `rw [Pred.denote.eq_4]` uses.
//!
//! Lean 4.8 reserves `f.eq_N` for every `N` (`j8_reserved.lean`) and numbers
//! them by SOURCE ARM. For an equation-form member (`def f (bs) : … | p₁, …,
//! pₙ => body | …`), arm `N` that no earlier arm overlaps yields
//!
//! ```text
//!   f.eq_N : ∀ bs (pattern variables), f bs p₁ … pₙ = body
//! ```
//!
//! built as SURFACE syntax and elaborated with the block's forward locals in
//! scope (so `body` is the arm body elaborated exactly as pass 2 elaborates
//! it, the patterns read as terms), then the locals replaced by the member
//! constants. The proof is `fun … => Eq.refl lhs`; it is registered through
//! the kernel's checked `add_decl` AFTER the members (`CtxAttributes::apply`),
//! and a lemma the kernel refuses is simply not minted — the name stays an
//! unknown identifier, never a wrong theorem.
//!
//! Not minted, by design (pinned): an arm an earlier arm may overlap (Lean
//! states it with hypotheses, `p19.lean`), an arm with an or-, as-, literal-
//! sum or structure pattern, a term-mode `match`, and `f.eq_def`.

use clean_kernel::{Expr, ExprKind, Name};
use clean_parser::{
    Span, SurfaceArg, SurfaceBinder, SurfaceBinderInfo, SurfaceDecl, SurfaceExpr, SurfaceName,
    SurfacePattern,
};

use super::{replace_forward_locals, PreDef};
use crate::infer::ElabCtx;

/// An equation lemma waiting for its members to register.
#[derive(Debug, Clone)]
pub(crate) struct PendingEqLemma {
    /// `f.eq_N`.
    pub name: Name,
    /// Its universe parameters.
    pub universe_params: Vec<Name>,
    /// `∀ xs, f … = body`, closed.
    pub ty: Expr,
    /// `fun xs => Eq.refl (f …)`.
    pub proof: Expr,
}

/// A pattern's head shape, for the overlap test.
enum Shape {
    Any,
    Ctor(String, Vec<Shape>),
    Lit(String),
}

fn is_tuple_ctor(name: &SurfaceName) -> bool {
    *name == SurfaceName::generated_path("Prod.mk")
        || *name == SurfaceName::generated_path("PProd.mk")
}

/// Columns the parser folded into a right-nested `Prod.mk` pattern.
fn tuple_arity(pattern: &SurfacePattern) -> usize {
    match pattern {
        SurfacePattern::Ctor(name, fields) if is_tuple_ctor(name) && fields.len() == 2 => {
            1 + tuple_arity(&fields[1])
        }
        _ => 1,
    }
}

fn peel(pattern: &SurfacePattern, arity: usize) -> Vec<&SurfacePattern> {
    let mut out = Vec::with_capacity(arity);
    let mut cur = pattern;
    while out.len() + 1 < arity {
        match cur {
            SurfacePattern::Ctor(name, fields) if is_tuple_ctor(name) && fields.len() == 2 => {
                out.push(&fields[0]);
                cur = &fields[1];
            }
            _ => break,
        }
    }
    out.push(cur);
    out
}

/// Whether some value could match both shapes (conservative: `true` unless
/// two different constructors or literals meet).
fn may_overlap(a: &Shape, b: &Shape) -> bool {
    match (a, b) {
        (Shape::Ctor(x, xs), Shape::Ctor(y, ys)) => {
            x == y && (xs.len() != ys.len() || xs.iter().zip(ys).all(|(p, q)| may_overlap(p, q)))
        }
        (Shape::Lit(x), Shape::Lit(y)) => x == y,
        _ => true,
    }
}

fn last(name: &SurfaceName) -> String {
    name.last_component().to_string()
}

fn ident(name: SurfaceName) -> SurfaceExpr {
    SurfaceExpr::Ident(Span::dummy(), name)
}

fn app(head: SurfaceExpr, args: Vec<SurfaceExpr>) -> SurfaceExpr {
    if args.is_empty() {
        return head;
    }
    SurfaceExpr::App(
        Span::dummy(),
        Box::new(head),
        args.into_iter().map(SurfaceArg::positional).collect(),
    )
}

/// The arms of an equation-form value: `fun _x => match _x with arms`.
fn equation_arms(val: &SurfaceExpr) -> Option<&[clean_parser::SurfaceMatchArm]> {
    let SurfaceExpr::PatternMatchLambda(_, binders, inner) = val else {
        return None;
    };
    let SurfaceExpr::Match(_, None, scrutinee, arms) = inner.as_ref() else {
        return None;
    };
    let lambda = SurfaceName::pattern_lambda_binder();
    let scrutinee_ok = matches!(scrutinee.as_ref(), SurfaceExpr::Ident(_, n) if *n == lambda);
    (binders.len() == 1 && binders[0].name == lambda && scrutinee_ok).then_some(arms.as_slice())
}

fn mentions_sorry(expr: &Expr) -> bool {
    match expr.kind() {
        ExprKind::Const(name, _) => name.to_string().contains("sorry"),
        ExprKind::App(f, a) => mentions_sorry(f) || mentions_sorry(a),
        ExprKind::Lam(_, t, b) | ExprKind::Pi(_, t, b) => mentions_sorry(t) || mentions_sorry(b),
        ExprKind::Let(_, t, v, b, _) => mentions_sorry(t) || mentions_sorry(v) || mentions_sorry(b),
        ExprKind::Proj(_, _, e) | ExprKind::MData(_, e) => mentions_sorry(e),
        _ => false,
    }
}

/// `∀ xs, @Eq.{u} T lhs rhs` ↦ `fun xs => @Eq.refl.{u} T lhs`, when `lhs` is
/// an application of `member`.
fn refl_proof(ty: &Expr, member: &Name) -> Option<Expr> {
    match ty.kind() {
        ExprKind::Pi(bd, dom, body) => Some(Expr::lam(
            *bd,
            dom.as_ref().clone(),
            refl_proof(body, member)?,
        )),
        _ => {
            let ExprKind::Const(eq, levels) = ty.get_app_fn().kind() else {
                return None;
            };
            let args = ty.get_app_args();
            if eq.to_string() != "Eq" || args.len() != 3 {
                return None;
            }
            let head_ok =
                matches!(args[1].get_app_fn().kind(), ExprKind::Const(f, _) if f == member);
            head_ok.then(|| {
                Expr::apps(
                    Expr::const_str_levels("Eq.refl", levels.to_vec()),
                    [args[0].clone(), args[1].clone()],
                )
            })
        }
    }
}

impl ElabCtx<'_> {
    /// Queue `f.eq_N` for every lifted definition member of the block whose
    /// value is in equation form. `defs` carry the members' final universe
    /// parameters; `lifted` names the members the lift compiled.
    pub(in crate::infer) fn queue_arm_equations(
        &mut self,
        decls: &[SurfaceDecl],
        defs: &[PreDef],
        lifted: &[Name],
    ) {
        let members = decls
            .iter()
            .filter(|d| matches!(d, SurfaceDecl::Def { .. } | SurfaceDecl::Theorem { .. }));
        for (decl, def) in members.zip(defs) {
            if def.is_theorem || !lifted.contains(&def.name) {
                continue;
            }
            let SurfaceDecl::Def {
                name,
                universe_params,
                binders,
                val,
                ..
            } = decl
            else {
                continue;
            };
            let Some(arms) = equation_arms(val) else {
                continue;
            };
            let Some(arity) = arms.iter().map(|a| tuple_arity(&a.pattern)).min() else {
                continue;
            };
            let mut explicit: Vec<SurfaceExpr> = Vec::new();
            let mut nameable = true;
            for b in binders {
                if b.info == SurfaceBinderInfo::Explicit {
                    nameable &= !b.name.is_anonymous() && b.name.component_text() != Some("_");
                    explicit.push(ident(b.name.clone()));
                }
            }
            if !nameable {
                continue;
            }
            self.set_decl_universe_params(universe_params);
            let shapes: Vec<Option<Vec<Shape>>> = arms
                .iter()
                .map(|arm| {
                    peel(&arm.pattern, arity)
                        .into_iter()
                        .map(|p| self.pattern_shape(p))
                        .collect()
                })
                .collect();
            for (k, arm) in arms.iter().enumerate() {
                let Some(cols) = shapes[k].as_ref() else {
                    continue;
                };
                let overlapped = shapes[..k].iter().any(|earlier| match earlier {
                    Some(prev) => prev.iter().zip(cols).all(|(p, q)| may_overlap(p, q)),
                    None => true,
                });
                if overlapped {
                    continue;
                }
                // Lean's binder order: the definition's binders, then the
                // columns matched by a variable, then the pattern variables
                // of the constructor columns (`Q.denote.eq_3 : ∀ (k x : Nat)
                // (cs : List Q), …` for `| .conj cs, v => …`).
                let mut col_binders = Vec::new();
                let mut pat_binders = Vec::new();
                let mut fresh = 0u64;
                let mut terms = Vec::with_capacity(arity);
                for (col, p) in peel(&arm.pattern, arity).into_iter().enumerate() {
                    let target = if matches!(cols[col], Shape::Any) {
                        &mut col_binders
                    } else {
                        &mut pat_binders
                    };
                    match self.pattern_term(p, target, &mut fresh) {
                        Some(term) => terms.push(term),
                        None => break,
                    }
                }
                if terms.len() != arity {
                    continue;
                }
                col_binders.extend(pat_binders);
                let pat_binders = col_binders;
                let lhs = app(
                    ident(name.clone()),
                    explicit.iter().cloned().chain(terms).collect(),
                );
                let eq = app(
                    ident(SurfaceName::global_path("Eq")),
                    vec![lhs, arm.body.clone()],
                );
                let all_binders: Vec<SurfaceBinder> =
                    binders.iter().cloned().chain(pat_binders).collect();
                let statement = if all_binders.is_empty() {
                    eq
                } else {
                    SurfaceExpr::Pi(Span::dummy(), all_binders, Box::new(eq))
                };
                let lemma = def.name.clone().str(format!("eq_{}", k + 1));
                if let Some(pending) = self.arm_lemma(&statement, defs, def, lemma) {
                    self.mutual_eq_lemmas.push(pending);
                }
            }
        }
    }

    fn arm_lemma(
        &mut self,
        statement: &SurfaceExpr,
        defs: &[PreDef],
        def: &PreDef,
        name: Name,
    ) -> Option<PendingEqLemma> {
        // The statement is elaborated for its own sake: nothing it leaves
        // behind (locals, auto-bound implicits, postponed instance problems)
        // may reach the block's declarations.
        let depth = self.locals.len();
        let autos = self.auto_implicit_count();
        let postponed = self.postponed_open_carrier_instances.len();
        let pure_obligations = self.do_pure_obligations.len();
        let elaborated = self.elaborate(statement);
        let leaked = self.auto_implicit_count() > autos;
        if leaked {
            let _ = self.take_auto_implicits_since(autos);
        }
        let unsolved = self.postponed_open_carrier_instances.len() > postponed;
        self.postponed_open_carrier_instances.truncate(postponed);
        self.do_pure_obligations.truncate(pure_obligations);
        self.locals.truncate(depth);
        if unsolved {
            return None;
        }
        let ty = elaborated.ok()?;
        if leaked {
            return None;
        }
        let ty = self.metas.instantiate(&ty);
        let ty = self.metas.instantiate_levels(&ty);
        if ty.has_expr_mvar_quick() {
            return None;
        }
        let ty = self.metas.canonicalize_levels_in_expr(&ty);
        let ty = replace_forward_locals(defs, &ty);
        if ty.has_fvar_quick() || mentions_sorry(&ty) {
            return None;
        }
        let proof = refl_proof(&ty, &def.name)?;
        let mut universe_params = Vec::new();
        crate::infer::elab_decl_value::collect_def_level_params(&ty, &mut universe_params);
        Some(PendingEqLemma {
            name,
            universe_params,
            ty,
            proof,
        })
    }

    /// The overlap shape of a column pattern; `None` for a pattern this module
    /// does not state (the arm is then not minted).
    fn pattern_shape(&mut self, pattern: &SurfacePattern) -> Option<Shape> {
        Some(match pattern {
            SurfacePattern::Wildcard => Shape::Any,
            SurfacePattern::Var(name) if name.is_relative_constructor() => {
                Shape::Ctor(last(name), Vec::new())
            }
            SurfacePattern::Var(name) => match self.bare_pattern_name_is_constructor(name)? {
                true => Shape::Ctor(last(name), Vec::new()),
                false => Shape::Any,
            },
            SurfacePattern::Ctor(name, args) => Shape::Ctor(
                last(name),
                args.iter()
                    .map(|a| self.pattern_shape(a))
                    .collect::<Option<Vec<_>>>()?,
            ),
            SurfacePattern::Lit(lit) => Shape::Lit(format!("{lit:?}")),
            _ => return None,
        })
    }

    /// A column pattern read as a term, its variables appended to `binders`.
    fn pattern_term(
        &mut self,
        pattern: &SurfacePattern,
        binders: &mut Vec<SurfaceBinder>,
        fresh: &mut u64,
    ) -> Option<SurfaceExpr> {
        fn bind(binders: &mut Vec<SurfaceBinder>, name: SurfaceName) -> SurfaceExpr {
            binders.push(SurfaceBinder::new_typed(
                name.clone(),
                None,
                SurfaceBinderInfo::Explicit,
            ));
            ident(name)
        }
        Some(match pattern {
            SurfacePattern::Wildcard => {
                let name = SurfaceName::unspellable("x✝", *fresh);
                *fresh += 1;
                bind(binders, name)
            }
            SurfacePattern::Var(name) if name.is_relative_constructor() => ident(name.clone()),
            SurfacePattern::Var(name) => match self.bare_pattern_name_is_constructor(name)? {
                true => ident(name.clone()),
                false => bind(binders, name.clone()),
            },
            SurfacePattern::Ctor(name, args) => {
                let mut terms = Vec::with_capacity(args.len());
                for arg in args {
                    terms.push(self.pattern_term(arg, binders, fresh)?);
                }
                app(ident(name.clone()), terms)
            }
            SurfacePattern::Lit(lit) => SurfaceExpr::Lit(Span::dummy(), lit.clone()),
            _ => return None,
        })
    }

    /// The equation lemmas queued so far (drained).
    pub(crate) fn take_mutual_eq_lemmas(&mut self) -> Vec<PendingEqLemma> {
        std::mem::take(&mut self.mutual_eq_lemmas)
    }
}
