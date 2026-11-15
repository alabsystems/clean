// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! A structural-recursion lowering is faithful only when its recursor
//! computes the WHOLE definition.
//!
//! Clean lowers structural recursion at the `match` on the decreasing
//! argument: that match becomes `T.rec motive minors major gen…`, and a
//! recursive call on a constructor field becomes the minor's induction
//! hypothesis. An induction hypothesis is the RECURSOR's value at the smaller
//! argument — the value of that one match, re-run with the call's arguments.
//! It is the value of the DEFINITION at those arguments only if evaluating the
//! definition there reaches the same match and returns its value unchanged.
//! Lean 4.8.0 never has this problem: `Structural` wraps the whole body in
//! `T.brecOn`, so the recursion re-runs everything.
//!
//! Measured on db37ea99b, base 3f45fb7c6 and e3f696689 alike (Lean 4.8.0
//! refusing each restatement):
//!
//! * `def f (n : Nat) : Nat := 1 + match n with | 0 => 0 | Nat.succ m => f m`
//!   — the `1 +` is outside the recursor, so every level after the first lost
//!   it: `f 2 = 1` by `rfl` (Lean: `3`);
//! * `def c (a b : Nat) := match a with | 0 => 5 | Nat.succ x => match b with |
//!   0 => 1 | Nat.succ y => c 0 y + 100` — the case split on `a`, which the
//!   call changes to `0`, is outside the recursor, so the recursion never took
//!   its `0 => 5` branch: `c 1 2 = 201` (Lean: `105`).
//!
//! `check_recursive_minors_closed` (the S1 check) refuses a recursor whose
//! minors READ a value computed from the changing arguments; neither case
//! above reads one. This module checks the other half: after the definition
//! body is elaborated, every recorded recursion site must be the value of the
//! whole body, reached only through
//!
//! * `let` bodies (a `let` changes no control; a minor that reads a `let` that
//!   depends on a changing argument is refused by the S1 check), and
//! * the branches of a case split (`T.casesOn`, `ite`, `dite`, `cond`) whose
//!   discriminant depends on no argument that a recursive call changes — the
//!   recursion then takes the same branch at every level.
//!
//! Anything else around a site — an application, a `fun`, a `let` value, a
//! case split on a changing argument — refuses the definition, loudly and
//! with the shape named. The check reads the elaborated term, so notation,
//! macros and desugarings cannot hide a context from it.

use super::ElabCtx;
use crate::unify::MetaState;
use crate::ElabError;
use clean_kernel::name::{Name, NameInner};
use clean_kernel::{BinderInfo, Expr, ExprKind, FVarId, RecursorArgOrder, TypeChecker};
use clean_parser::SurfaceName;
use std::collections::HashSet;

/// One `.rec` application the structural lowering emitted for a `match` on
/// the decreasing argument (`elab_match_with_scrutinee_hyp_inner`).
#[derive(Debug, Clone)]
pub(super) struct StructuralRecSite {
    /// The definition being lowered.
    pub(super) func: SurfaceName,
    /// The decreasing parameter, as written.
    pub(super) major_name: SurfaceName,
    /// The recursor constant heading the application.
    pub(super) eliminator: Name,
    /// Position of the major premise in the application's arguments.
    pub(super) major_index: usize,
    /// The major premise: exactly the decreasing parameter's local.
    pub(super) major: FVarId,
    /// The parameters recursive calls may change: the major, the generalized
    /// parameters and the recursor-index parameters.
    pub(super) changing: Vec<FVarId>,
}

/// Why a site is not the value of the whole definition.
type Violation = String;

struct SiteWalker<'s> {
    env: &'s clean_kernel::Environment,
    sites: &'s [StructuralRecSite],
    changing: HashSet<FVarId>,
    /// Is this closed term, whose one site is `site`, definitionally that
    /// site (`Id.run (pure site)`)? See `ElabCtx::is_identity_around_site`.
    identity: &'s dyn Fn(&Expr, &Expr) -> bool,
}

/// Argument layout of an eliminator application used as a case split:
/// which arguments choose nothing (parameters, motives), which choose the
/// branch (indices and the major premise), and where the branches (minor
/// premises, with the number of binders each opens) sit. Arguments from
/// `extra_start` on are applied to the chosen branch.
struct SplitLayout {
    passive: std::ops::Range<usize>,
    control: std::ops::Range<usize>,
    branches: Vec<(usize, usize)>,
    extra_start: usize,
}

impl SiteWalker<'_> {
    fn is_site(&self, e: &Expr) -> bool {
        let ExprKind::Const(head, _) = e.get_app_fn().kind() else {
            return false;
        };
        let args = e.get_app_args();
        self.sites.iter().any(|site| {
            &site.eliminator == head
                && args.get(site.major_index).is_some_and(
                    |arg| matches!(arg.kind(), ExprKind::FVar(id) if *id == site.major),
                )
        })
    }

    fn contains_site(&self, e: &Expr) -> bool {
        crate::stack_safe(|| {
            if self.is_site(e) {
                return true;
            }
            match e.kind() {
                ExprKind::App(f, a) => self.contains_site(f) || self.contains_site(a),
                ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                    self.contains_site(ty) || self.contains_site(body)
                }
                ExprKind::Let(_, ty, val, body, _) => {
                    self.contains_site(ty) || self.contains_site(val) || self.contains_site(body)
                }
                ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) => {
                    self.contains_site(inner)
                }
                ExprKind::BVar(_)
                | ExprKind::FVar(_)
                | ExprKind::Sort(_)
                | ExprKind::Const(..)
                | ExprKind::Lit(_) => false,
                // No structural lowering emits these; if one ever wraps a
                // site, it is not a context this check can judge.
                _ => true,
            }
        })
    }

    /// Does `e` depend on an argument recursive calls change? `bound` holds
    /// that verdict for each enclosing context binder, innermost last; `depth`
    /// counts the binders entered inside `e` itself. An unassigned
    /// metavariable counts as dependent.
    fn depends(&self, e: &Expr, bound: &[bool], depth: u32) -> bool {
        crate::stack_safe(|| match e.kind() {
            ExprKind::BVar(i) => {
                if *i < depth {
                    return false;
                }
                let outer = (*i - depth) as usize;
                bound
                    .len()
                    .checked_sub(1 + outer)
                    .is_none_or(|slot| bound[slot])
            }
            ExprKind::FVar(id) => self.changing.contains(id) || MetaState::from_fvar(*id).is_some(),
            ExprKind::Sort(_) | ExprKind::Const(..) | ExprKind::Lit(_) => false,
            ExprKind::App(f, a) => self.depends(f, bound, depth) || self.depends(a, bound, depth),
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                self.depends(ty, bound, depth) || self.depends(body, bound, depth + 1)
            }
            ExprKind::Let(_, ty, val, body, _) => {
                self.depends(ty, bound, depth)
                    || self.depends(val, bound, depth)
                    || self.depends(body, bound, depth + 1)
            }
            ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) => {
                self.depends(inner, bound, depth)
            }
            _ => true,
        })
    }

    /// The layout of `head` as a case split: `T.casesOn` (motive, indices,
    /// major, then minors) or a `T.rec` that is not a recursion site (minors,
    /// then indices and major; each minor also binds the induction hypotheses
    /// of its recursive fields, which are computed from the major alone).
    fn split_layout(&self, head: &Name) -> Option<SplitLayout> {
        let NameInner::Str(prefix, last) = head.inner() else {
            return None;
        };
        let (params, motives, indices, minor_binders, major_after_motive) =
            match (last.as_ref(), self.env.get_recursor(head)) {
                ("casesOn" | "rec", Some(rec)) => (
                    rec.num_params as usize,
                    rec.num_motives as usize,
                    rec.num_indices as usize,
                    rec.rules
                        .iter()
                        .map(|rule| {
                            rule.num_fields as usize
                                + if last.as_ref() == "rec" {
                                    rule.recursive_fields.iter().filter(|r| **r).count()
                                } else {
                                    0
                                }
                        })
                        .collect::<Vec<_>>(),
                    matches!(rec.arg_order, RecursorArgOrder::MajorAfterMotive),
                ),
                // An imported `casesOn` is a plain definition with Lean's
                // layout: one motive, then indices and major, then minors.
                ("casesOn", None) => {
                    let ind = self.env.get_inductive(prefix)?;
                    let fields = ind
                        .constructor_names
                        .iter()
                        .map(|c| self.env.get_constructor(c).map(|c| c.num_fields as usize))
                        .collect::<Option<Vec<_>>>()?;
                    (
                        ind.num_params as usize,
                        1,
                        ind.num_indices as usize,
                        fields,
                        true,
                    )
                }
                _ => return None,
            };
        let passive = 0..params + motives;
        let minors = minor_binders.len();
        let (control, minors_start) = if major_after_motive {
            let control = passive.end..passive.end + indices + 1;
            let minors_start = control.end;
            (control, minors_start)
        } else {
            let minors_start = passive.end;
            (
                minors_start + minors..minors_start + minors + indices + 1,
                minors_start,
            )
        };
        let branches = minor_binders
            .into_iter()
            .enumerate()
            .map(|(k, binders)| (minors_start + k, binders))
            .collect();
        Some(SplitLayout {
            extra_start: control.end.max(minors_start + minors),
            passive,
            control,
            branches,
        })
    }

    /// The site occurrences in `e` (stopping after two).
    fn single_site<'e>(&self, e: &'e Expr, out: &mut Vec<&'e Expr>) {
        if out.len() > 1 {
            return;
        }
        if self.is_site(e) {
            out.push(e);
            return;
        }
        match e.kind() {
            ExprKind::App(f, a) => {
                self.single_site(f, out);
                self.single_site(a, out);
            }
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                self.single_site(ty, out);
                self.single_site(body, out);
            }
            ExprKind::Let(_, ty, val, body, _) => {
                self.single_site(ty, out);
                self.single_site(val, out);
                self.single_site(body, out);
            }
            ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) => {
                self.single_site(inner, out);
            }
            _ => {}
        }
    }

    /// A context the walker cannot read may still be the identity on its
    /// site: `Id.run (pure (match n with …))` IS the match. Accept `e` when it
    /// is closed, holds exactly one site, and the kernel finds `e` with that
    /// site replaced by a fresh variable definitionally equal to the variable;
    /// otherwise refuse with `shape`.
    fn identity_or(&self, e: &Expr, shape: String) -> Result<(), Violation> {
        let mut found = Vec::new();
        self.single_site(e, &mut found);
        match found.as_slice() {
            [site]
                if !e.has_loose_bvars() && !site.has_loose_bvars() && (self.identity)(e, site) =>
            {
                Ok(())
            }
            _ => Err(shape),
        }
    }

    /// `e` is in tail position of the definition body.
    fn tail(&self, e: &Expr, bound: &mut Vec<bool>) -> Result<(), Violation> {
        crate::stack_safe(|| {
            if !self.contains_site(e) || self.is_site(e) {
                return Ok(());
            }
            match e.kind() {
                ExprKind::MData(_, inner) => self.tail(inner, bound),
                ExprKind::Let(name, ty, val, body, _) => {
                    if self.contains_site(ty) || self.contains_site(val) {
                        return Err(format!("inside the value of `let {name}`"));
                    }
                    let dependent = self.depends(ty, bound, 0) || self.depends(val, bound, 0);
                    bound.push(dependent);
                    let result = self.tail(body, bound);
                    bound.pop();
                    result
                }
                ExprKind::App(..) => self.tail_app(e, bound),
                ExprKind::Lam(..) => Err("inside a `fun`".to_string()),
                _ => Err("inside a term that is not the definition's value".to_string()),
            }
        })
    }

    fn tail_app(&self, e: &Expr, bound: &mut Vec<bool>) -> Result<(), Violation> {
        let head = e.get_app_fn();
        let args: Vec<Expr> = e.get_app_args().into_iter().cloned().collect();
        // A beta-redex (`cond` elaborates to one) is its reduct.
        if let ExprKind::Lam(_, _, body) = head.kind() {
            let reduct = Expr::apps(body.instantiate(&args[0]), args[1..].iter().cloned());
            return self.tail(&reduct, bound);
        }
        let ExprKind::Const(name, _) = head.kind() else {
            return self.identity_or(e, "inside an application of a local function".to_string());
        };
        // Each shape: (arguments that choose nothing, arguments that choose
        // the branch, branches with their field-binder counts, trailing
        // arguments the branches take).
        let (passive, control, branches, extra): (&[Expr], &[Expr], Vec<(&Expr, usize)>, &[Expr]) =
            match (name.to_string().as_str(), args.len()) {
                // `@ite α c inst t e`: the instance decides the branch.
                ("ite", 5) => (
                    &args[..1],
                    &args[1..3],
                    vec![(&args[3], 0), (&args[4], 0)],
                    &[],
                ),
                // `@dite α c inst (fun h => t) (fun h => e)`
                ("dite", 5) => (
                    &args[..1],
                    &args[1..3],
                    vec![(&args[3], 1), (&args[4], 1)],
                    &[],
                ),
                // `@cond α b t e`
                ("cond", 4) => (
                    &args[..1],
                    &args[1..2],
                    vec![(&args[2], 0), (&args[3], 0)],
                    &[],
                ),
                _ => {
                    let Some(layout) = self.split_layout(name) else {
                        return self.identity_or(e, format!("inside an application of `{name}`"));
                    };
                    if args.len() < layout.extra_start {
                        return Err(format!("inside a partial application of `{name}`"));
                    }
                    let branches = layout
                        .branches
                        .iter()
                        .map(|&(at, binders)| (&args[at], binders))
                        .collect();
                    (
                        &args[layout.passive.clone()],
                        &args[layout.control.clone()],
                        branches,
                        &args[layout.extra_start..],
                    )
                }
            };
        if passive
            .iter()
            .chain(control)
            .chain(extra)
            .any(|a| self.contains_site(a))
        {
            return Err(format!(
                "inside an argument of `{name}` that is not a branch"
            ));
        }
        if control.iter().any(|d| self.depends(d, bound, 0)) {
            return Err(format!(
                "under a case split (`{name}`) on a value that a recursive call changes"
            ));
        }
        // A branch's binders after its fields take the trailing arguments; such
        // a binder is dependent when any trailing argument is.
        let extra_dependent = extra.iter().any(|arg| self.depends(arg, bound, 0));
        for (branch, fields) in branches {
            let mut body = branch.clone();
            let mut pushed = 0;
            while pushed < fields + extra.len() {
                let ExprKind::Lam(_, _, inner) = body.kind() else {
                    break;
                };
                let inner = inner.as_ref().clone();
                bound.push(pushed >= fields && extra_dependent);
                pushed += 1;
                body = inner;
            }
            let result = if pushed < fields + extra.len() {
                if self.contains_site(&body) {
                    Err(format!(
                        "inside a branch of `{name}` that is not a `fun` over its fields"
                    ))
                } else {
                    Ok(())
                }
            } else {
                self.tail(&body, bound)
            };
            for _ in 0..pushed {
                bound.pop();
            }
            result?;
        }
        Ok(())
    }
}

/// `e` with every occurrence of `target` replaced by `with`; `None` when a
/// form this does not rebuild holds an occurrence.
fn replace_subterm(e: &Expr, target: &Expr, with: &Expr) -> Option<Expr> {
    if e == target {
        return Some(with.clone());
    }
    let r = |x: &Expr| replace_subterm(x, target, with).map(std::sync::Arc::new);
    crate::stack_safe(|| {
        Some(match e.kind() {
            ExprKind::App(f, a) => Expr::from_kind(ExprKind::App(r(f)?, r(a)?)),
            ExprKind::Lam(b, ty, body) => Expr::from_kind(ExprKind::Lam(*b, r(ty)?, r(body)?)),
            ExprKind::Pi(b, ty, body) => Expr::from_kind(ExprKind::Pi(*b, r(ty)?, r(body)?)),
            ExprKind::Let(n, ty, val, body, nd) => {
                Expr::from_kind(ExprKind::Let(n.clone(), r(ty)?, r(val)?, r(body)?, *nd))
            }
            ExprKind::Proj(n, i, inner) => {
                Expr::from_kind(ExprKind::Proj(n.clone(), *i, r(inner)?))
            }
            ExprKind::MData(m, inner) => Expr::from_kind(ExprKind::MData(m.clone(), r(inner)?)),
            ExprKind::BVar(_)
            | ExprKind::FVar(_)
            | ExprKind::Sort(_)
            | ExprKind::Const(..)
            | ExprKind::Lit(_) => e.clone(),
            _ => return None,
        })
    })
}

impl ElabCtx<'_> {
    /// Is `term` — a closed context around its one recursion site `site` —
    /// definitionally equal to that site? Decided by the kernel on `term` with
    /// the site replaced by a fresh variable `witness` of the site's type: if
    /// `C[x] ≡ x` for a variable, then `C[site] ≡ site`, so the definition's
    /// value IS the recursor's and the induction hypotheses stand for it.
    fn is_identity_around_site(&self, term: &Expr, site: &Expr, witness: FVarId) -> bool {
        let checker = TypeChecker::with_context(self.env, self.build_local_ctx());
        let Ok(site_ty) = checker.infer_type(site) else {
            return false;
        };
        let mut ctx = self.build_local_ctx();
        ctx.push_with_id(
            witness,
            Name::from_string("_recursion_site"),
            site_ty,
            BinderInfo::Default,
        );
        let checker = TypeChecker::with_context(self.env, ctx);
        let x = Expr::fvar(witness);
        match replace_subterm(term, site, &x) {
            Some(abstracted) => checker.is_def_eq(&abstracted, &x),
            None => false,
        }
    }

    /// Record a structural `.rec` lowering (see [`StructuralRecSite`]).
    pub(super) fn record_structural_rec_site(&mut self, site: StructuralRecSite) {
        self.structural_rec_sites.push(site);
    }

    /// How many sites are recorded; a definition body checks the sites it
    /// recorded after this mark.
    pub(super) fn structural_rec_site_mark(&self) -> usize {
        self.structural_rec_sites.len()
    }

    /// Refuse a structurally recursive definition whose recursor does not
    /// compute its whole body (see the module documentation). `body` is the
    /// elaborated definition value with the parameters still free; the sites
    /// recorded since `mark` are checked and forgotten.
    pub(super) fn check_structural_recursion_sites(
        &mut self,
        body: &Expr,
        mark: usize,
    ) -> Result<(), ElabError> {
        if self.structural_rec_sites.len() <= mark {
            return Ok(());
        }
        let sites = self.structural_rec_sites.split_off(mark);
        let body = self.metas.instantiate_levels(&self.metas.instantiate(body));
        let witness = self.fresh_fvar();
        let identity = |term: &Expr, site: &Expr| self.is_identity_around_site(term, site, witness);
        let walker = SiteWalker {
            env: self.env,
            sites: &sites,
            changing: sites
                .iter()
                .flat_map(|site| site.changing.iter().copied())
                .collect(),
            identity: &identity,
        };
        match walker.tail(&body, &mut Vec::new()) {
            Ok(()) => Ok(()),
            Err(shape) => {
                let site = &sites[0];
                Err(ElabError::Unsupported {
                    feature: format!(
                        "structural recursion in `{func}`: the `match` on the decreasing argument `{major}` is {shape}, not the value of the whole definition. Its recursor computes that `match` alone, so an induction hypothesis would stand for the value of the `match` at the smaller argument rather than for `{func}` there, and the lowered term would compute a different function than the source (`def f (n : Nat) : Nat := 1 + match n with | 0 => 0 | n+1 => f n` would give `f 2 = 1`; Lean 4.8.0 gives 3). Lean compiles this form through `brecOn` over the whole body; Clean's recursor lowering admits it only when the `match` on `{major}` is the definition's value, reached through `let`s and through case splits on values every recursive call passes unchanged. Restate `{func}` with the `match` on `{major}` outermost",
                        func = site.func,
                        major = site.major_name,
                    ),
                })
            }
        }
    }
}
