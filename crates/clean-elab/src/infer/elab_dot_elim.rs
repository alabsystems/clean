// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Generalized field notation on a recursor-family head whose motive is
//! EXPLICIT (`x.casesOn` with `x : Empty`, `h.rec` with `h : False`).
//!
//! A type with no constructors has no minor premise, so its eliminators take
//! the motive explicitly: `@Empty.casesOn : (motive : Empty → Sort u) →
//! (t : Empty) → motive t`. Lean's `addLValArg` (`Lean/Elab/App.lean`) passes
//! the receiver as `t`, and `elabAppArgs.elabAsElim?` then decides the route:
//! when no positional argument other than `_` and no named argument supplies
//! the motive, the application is elaborated as an ELIMINATOR, which needs the
//! expected type ("failed to elaborate eliminator, expected type is not
//! available") and builds the motive by abstracting the discriminant out of it
//! (`ElabElim.finalize`, `mkMotive`). Clean's `apply_dot_receiver` instead
//! re-bound the explicit motive as a lambda, `fun motive => Empty.casesOn
//! motive x`, which Lean never produces.
//!
//! What is modelled, and nothing more:
//!
//! * The term must be a bare `x.f` (an identifier receiver, no arguments)
//!   ascribed a WRITTEN type with no metavariable, `(x.f : T)`, or the whole
//!   body of a definition whose declared result `T` has none
//!   (`def d (x : E) : T := x.f`, from `elab_def_body`): Lean elaborates
//!   `x.f` against `T` there whatever the context holds. The ascription is
//!   also the shape the parser gives `let g (a : A) : T := x.f`. No other
//!   expected type is trusted. The ambient `current_expected_type` keeps
//!   whatever an enclosing site left there (a tactic block's goal, say, under
//!   a tactic `let`, where Lean passes no expected type at all), and a type
//!   DERIVED from it (an `if` branch, a `let` body, an ascription `_` filled
//!   from the context) inherits that staleness. The site is recorded with the
//!   written type ([`DotElimState::arm_expected`], from `elab_ascription` and
//!   `elab_def_body`) and matched by `elab_proj` against the term it elaborates, which must
//!   still have that type as its expected type.
//! * The head is `T.casesOn`, `T.rec` or `T.recOn` for an inductive with one
//!   motive, no indices and no minor premises, so its type is `{params} →
//!   (motive) → (t : T params) → motive t`.
//! * The receiver is a local variable without a value, and the expected type,
//!   once the receiver is abstracted, mentions no free variable and no
//!   metavariable. Then the motive `fun t => C[t]` is closed and type-correct
//!   exactly when `C[x]` is, so Lean's "motive is not type correct" cannot
//!   arise, and `kabstract` of a variable is abstraction of that variable.
//! * `rec`/`recOn` only at a proposition or in a `noncomputable def`: Lean
//!   compiles any other definition, and whether its code generator accepts a
//!   recursor depends on the head (`x.rec : Nat` compiles, `x.recOn : Nat`
//!   does not) in ways `clean check` does not model.
//!
//! Everything else that reaches an explicit motive this way is refused by
//! name, except an application whose first argument is a positional motive
//! other than `_` with no named arguments, which Lean elaborates as an
//! ordinary application and the lambda path reproduces up to β.

use super::*;
use clean_parser::Span;

/// A bare field-notation site `x.f`, identified by the receiver identifier as
/// written (spelling and span) and the field.
#[derive(Debug, Clone, PartialEq, Eq)]
struct DotSite {
    base: SurfaceName,
    base_span: Span,
    field: SurfaceName,
}

/// What follows a field-notation head inside an application.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum DotHeadArgs {
    /// The first argument is positional and not `_`, and there are no named
    /// arguments and no `..`: Lean takes it as the motive and uses the
    /// ordinary application elaborator.
    PositionalMotive,
    /// Anything else (`_` first, a named argument, `..`).
    Other,
}

/// How the field-notation term being elaborated was reached.
#[derive(Debug, Clone)]
enum DotElimRoute {
    /// Ascribed this written type, with no arguments following.
    Expected(Expr),
    /// The head of an application with these arguments.
    Applied(DotHeadArgs),
    /// Neither: Clean cannot show which expected type Lean would pass.
    Unannounced,
}

#[derive(Debug, Clone)]
struct DotElimFrame {
    route: DotElimRoute,
    /// The elaborated receiver, once known; the frame applies only to a head
    /// applied to exactly this receiver.
    receiver: Option<Expr>,
}

/// Scoped state of this module. Every field is saved and restored by the
/// function that sets it, on success and on error alike.
#[derive(Debug, Clone, Default)]
pub(super) struct DotElimState {
    expected: Option<(DotSite, Expr)>,
    app_head: Option<(DotSite, DotHeadArgs)>,
    frame: Option<DotElimFrame>,
    /// The enclosing declaration is `noncomputable`: no code is generated for
    /// it, so a recursor at data is not the code generator's to refuse.
    uncompiled: bool,
}

/// Saved state handed back to the `restore_*` functions.
pub(super) struct SavedExpected(Option<(DotSite, Expr)>);
pub(super) struct SavedAppHead(Option<(DotSite, DotHeadArgs)>);
pub(super) struct SavedFrame {
    expected: Option<(DotSite, Expr)>,
    app_head: Option<(DotSite, DotHeadArgs)>,
    frame: Option<DotElimFrame>,
}

/// The eliminator heads this module recognizes, by last component.
const ELIM_FIELDS: &[&str] = &["casesOn", "rec", "recOn", "brecOn", "binductionOn"];

fn dot_site_of(base: &SurfaceExpr, proj: &Projection) -> Option<DotSite> {
    let (SurfaceExpr::Ident(span, name), Projection::Named(field)) = (base, proj) else {
        return None;
    };
    let last = field.name().last_component()?;
    if !ELIM_FIELDS.contains(&last.as_str()) {
        return None;
    }
    Some(DotSite {
        base: name.clone(),
        base_span: *span,
        field: field.clone(),
    })
}

fn dot_site_of_surface(surface: &SurfaceExpr) -> Option<DotSite> {
    match ElabCtx::unwrap_surface_parens(surface) {
        SurfaceExpr::Proj(_, base, proj) => dot_site_of(base, proj),
        _ => None,
    }
}

/// Which recursor-family head `name` is, relative to the namespace `T`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ElimHead {
    CasesOn,
    Rec,
    RecOn,
    /// `brecOn` / `binductionOn`: never modelled here.
    Other,
}

fn elim_head(name: &Name, type_name: &Name) -> Option<ElimHead> {
    [
        ("casesOn", ElimHead::CasesOn),
        ("rec", ElimHead::Rec),
        ("recOn", ElimHead::RecOn),
        ("brecOn", ElimHead::Other),
        ("binductionOn", ElimHead::Other),
    ]
    .into_iter()
    .find(|(suffix, _)| Name::append(type_name, suffix) == *name)
    .map(|(_, head)| head)
}

fn refuse(head: &Name, why: &str) -> ElabError {
    ElabError::Unsupported {
        feature: format!("field notation on eliminator `{head}` with an explicit motive: {why}"),
    }
}

impl DotElimState {
    /// Record that `surface` is elaborated against the written, metavariable-
    /// free type `expected` (`None`: no such type). Returns the state to
    /// restore once that elaboration ends.
    pub(super) fn arm_expected(
        &mut self,
        surface: &SurfaceExpr,
        expected: Option<&Expr>,
    ) -> SavedExpected {
        let armed = expected.and_then(|ty| dot_site_of_surface(surface).map(|s| (s, ty.clone())));
        SavedExpected(std::mem::replace(&mut self.expected, armed))
    }

    pub(super) fn restore_expected(&mut self, saved: SavedExpected) {
        self.expected = saved.0;
    }

    /// Record that `func` is elaborated as the head of an application with
    /// `args`. An unparenthesized `x.f` only: Lean elaborates a parenthesized
    /// head `(x.f) a` as a term of its own, with no expected type.
    pub(super) fn arm_app_head(&mut self, func: &SurfaceExpr, args: &[SurfaceArg]) -> SavedAppHead {
        let armed = match func {
            SurfaceExpr::Proj(_, base, proj) => dot_site_of(base, proj).map(|site| {
                let positional_motive = args.first().is_some_and(|first| {
                    first.name.is_none() && !matches!(first.expr, SurfaceExpr::Hole(_))
                }) && args.iter().all(|a| a.name.is_none());
                let shape = if positional_motive {
                    DotHeadArgs::PositionalMotive
                } else {
                    DotHeadArgs::Other
                };
                (site, shape)
            }),
            _ => None,
        };
        SavedAppHead(std::mem::replace(&mut self.app_head, armed))
    }

    pub(super) fn restore_app_head(&mut self, saved: SavedAppHead) {
        self.app_head = saved.0;
    }

    /// Enter the body of a declaration that is (`true`) or is not compiled.
    /// Returns the flag to restore once that body ends.
    pub(super) fn enter_uncompiled(&mut self, uncompiled: bool) -> bool {
        std::mem::replace(&mut self.uncompiled, uncompiled)
    }

    pub(super) fn restore_uncompiled(&mut self, saved: bool) {
        self.uncompiled = saved;
    }

    pub(super) fn restore_frame(&mut self, saved: SavedFrame) {
        self.expected = saved.expected;
        self.app_head = saved.app_head;
        self.frame = saved.frame;
    }

    /// The elaborated receiver of the current `elab_proj` frame.
    pub(super) fn set_frame_receiver(&mut self, receiver: &Expr) {
        if let Some(frame) = self.frame.as_mut() {
            frame.receiver = Some(receiver.clone());
        }
    }
}

impl<'a> ElabCtx<'a> {
    /// Open the frame for `elab_proj(base, proj)`: decide how this term was
    /// reached, and hide the armed sites from the receiver's elaboration.
    pub(super) fn open_dot_elim_frame(
        &mut self,
        base: &SurfaceExpr,
        proj: &Projection,
    ) -> SavedFrame {
        let site = dot_site_of(base, proj);
        let state = &mut self.dot_elim;
        let expected = state.expected.take();
        let app_head = state.app_head.take();
        let route = match &site {
            None => DotElimRoute::Unannounced,
            Some(site) => {
                let handed = expected.as_ref().filter(|(armed, ty)| {
                    armed == site && self.current_expected_type.as_ref() == Some(ty)
                });
                if let Some((_, ty)) = handed {
                    DotElimRoute::Expected(ty.clone())
                } else if let Some((_, args)) = app_head.as_ref().filter(|(s, _)| s == site) {
                    DotElimRoute::Applied(*args)
                } else {
                    DotElimRoute::Unannounced
                }
            }
        };
        let frame = self.dot_elim.frame.replace(DotElimFrame {
            route,
            receiver: None,
        });
        SavedFrame {
            expected,
            app_head,
            frame,
        }
    }

    /// Recursor helpers imported as ordinary definitions retain their family's
    /// motive/major-premise application semantics.
    pub(super) fn is_dot_recursor_family_member(&self, name: &Name, namespace: &Name) -> bool {
        self.env.get_recursor(name).is_some()
            || (elim_head(name, namespace).is_some()
                && self
                    .env
                    .get_recursor(&Name::append(namespace, "rec"))
                    .is_some())
    }

    /// Field notation on a recursor-family head with an explicit motive, from
    /// `apply_dot_receiver`. `None` when the head is not one (or `@` is in
    /// force, where Lean uses the ordinary elaborator), or when the ordinary
    /// lambda path is faithful (a positional motive follows); otherwise the
    /// eliminator's elaboration or a refusal by name.
    pub(super) fn dot_explicit_motive_eliminator(
        &mut self,
        fn_expr: &Expr,
        fn_type: &Expr,
        receiver: &Expr,
        receiver_ty: &Expr,
        type_name: &Name,
    ) -> Option<Result<Expr, ElabError>> {
        if self.explicit_mode {
            return None;
        }
        let ExprKind::Const(head_name, _) = fn_expr.kind() else {
            return None;
        };
        let head = elim_head(head_name, type_name)?;
        let rec_val = self
            .env
            .get_recursor(&Name::append(type_name, "rec"))
            .cloned()?;
        if !self.motive_binder_is_explicit(fn_type, rec_val.num_params) {
            return None;
        }
        let route = match &self.dot_elim.frame {
            Some(frame) if frame.receiver.as_ref() == Some(receiver) => frame.route.clone(),
            _ => DotElimRoute::Unannounced,
        };
        match route {
            DotElimRoute::Applied(DotHeadArgs::PositionalMotive) => None,
            DotElimRoute::Applied(DotHeadArgs::Other) => Some(Err(refuse(
                head_name,
                "only a positional motive other than `_` may follow it",
            ))),
            DotElimRoute::Unannounced => Some(Err(refuse(
                head_name,
                "Lean elaborates it as an eliminator, which needs the expected type, and \
                 none was handed to this term",
            ))),
            DotElimRoute::Expected(expected) => Some(self.elab_dot_eliminator(
                head,
                &rec_val,
                fn_expr.clone(),
                fn_type,
                receiver,
                receiver_ty,
                &expected,
            )),
        }
    }

    /// Is the binder after `num_params` leading binders of `fn_type` an
    /// explicit one (the motive of a recursor-family head)?
    pub(super) fn motive_binder_is_explicit(&self, fn_type: &Expr, num_params: u32) -> bool {
        let mut ty = self.whnf(fn_type);
        for _ in 0..num_params {
            let ExprKind::Pi(_, _, body) = ty.kind() else {
                return false;
            };
            // The parameters only feed later binder types; a placeholder
            // instantiation keeps the telescope closed for the walk.
            ty = self.whnf(&body.instantiate(&Expr::sort(Level::zero())));
        }
        matches!(ty.kind(), ExprKind::Pi(bi, _, _) if bi.info == BinderInfo::Default)
    }

    /// `ElabElim.main` + `finalize` on the modelled slice (module docs).
    #[allow(clippy::too_many_arguments)]
    fn elab_dot_eliminator(
        &mut self,
        head: ElimHead,
        rec_val: &clean_kernel::RecursorVal,
        fn_expr: Expr,
        fn_type: &Expr,
        receiver: &Expr,
        receiver_ty: &Expr,
        expected: &Expr,
    ) -> Result<Expr, ElabError> {
        let ExprKind::Const(head_name, _) = fn_expr.kind() else {
            return Err(ElabError::Unsupported {
                feature: "field notation on an eliminator whose head is not a constant".into(),
            });
        };
        let head_name = head_name.clone();
        if head == ElimHead::Other {
            return Err(refuse(
                &head_name,
                "only `casesOn`, `rec` and `recOn` are modelled",
            ));
        }
        if rec_val.num_indices != 0 || rec_val.num_motives != 1 || rec_val.num_minors != 0 {
            return Err(refuse(
                &head_name,
                "only an inductive with no indices and no constructors is modelled",
            ));
        }
        let receiver_id = match receiver.kind() {
            ExprKind::FVar(id)
                if MetaState::from_fvar(*id).is_none()
                    && !self.locals.let_values().contains_key(id) =>
            {
                *id
            }
            _ => {
                return Err(refuse(
                    &head_name,
                    "only a local variable without a value is modelled as the receiver",
                ))
            }
        };
        let expected = self
            .metas
            .instantiate_levels(&self.metas.instantiate(expected));
        if expected.has_expr_mvar_quick() || Self::has_unassigned_meta_fvar(&expected) {
            return Err(refuse(
                &head_name,
                "the expected type is not known yet (Lean postpones it)",
            ));
        }
        // Clean's universe metavariables are non-rigid `Level::Param`s; Lean
        // fails on one it cannot settle ("failed to infer universe levels").
        if self.mentions_flexible_level(&expected) {
            return Err(refuse(
                &head_name,
                "the expected type's universe levels are not known yet",
            ));
        }
        // Lean introduces an implicit lambda for a leading `{x}`/`[x]` binder
        // before it elaborates the term; that is not modelled here.
        if matches!(expected.kind(), ExprKind::Pi(bi, _, _) if bi.info != BinderInfo::Default) {
            return Err(refuse(
                &head_name,
                "an expected type with a leading implicit binder is not modelled",
            ));
        }
        let motive_body = expected.abstract_fvar(receiver_id);
        if motive_body.has_fvar_quick() {
            return Err(refuse(
                &head_name,
                "the expected type mentions a local other than the receiver",
            ));
        }
        let expected_sort = self.infer_type(&expected)?;
        let ExprKind::Sort(level) = self.whnf(&expected_sort).kind().clone() else {
            return Err(refuse(&head_name, "the expected type is not a type"));
        };
        let receiver_ty = self.metas.instantiate(receiver_ty);

        // Parameters: implicit binders, solved from the receiver's type.
        let mut result = fn_expr;
        let mut ty = self.whnf(fn_type);
        let mut param_metas = Vec::new();
        for _ in 0..rec_val.num_params {
            let ExprKind::Pi(bi, dom, body) = ty.kind() else {
                return Err(refuse(&head_name, "unexpected eliminator type"));
            };
            if bi.info == BinderInfo::Default {
                return Err(refuse(&head_name, "an explicit parameter is not modelled"));
            }
            let meta = self.fresh_meta(self.metas.instantiate(dom));
            param_metas.push(meta.clone());
            result = Expr::app(result, meta.clone());
            ty = self.whnf(&self.metas.instantiate(&body.instantiate(&meta)));
        }
        // `(motive : T params → Sort u) → (t : T params) → motive t`.
        let (motive_ty, after_motive) = match ty.kind() {
            ExprKind::Pi(bi, dom, body) if bi.info == BinderInfo::Default => {
                ((**dom).clone(), (**body).clone())
            }
            _ => return Err(refuse(&head_name, "unexpected eliminator type")),
        };
        let (major_ty, target) = match after_motive.kind() {
            ExprKind::Pi(bi, dom, body) if bi.info == BinderInfo::Default => {
                ((**dom).clone(), (**body).clone())
            }
            _ => return Err(refuse(&head_name, "unexpected eliminator type")),
        };
        let target_is_motive_of_major = matches!(target.kind(), ExprKind::App(f, a)
            if matches!(f.kind(), ExprKind::BVar(1)) && matches!(a.kind(), ExprKind::BVar(0)));
        if !target_is_motive_of_major || major_ty.has_loose_bvars() {
            return Err(refuse(&head_name, "unexpected eliminator type"));
        }
        if !self.try_unify(&major_ty, &receiver_ty) {
            return Err(refuse(
                &head_name,
                "the receiver's type does not fit the major premise",
            ));
        }
        let motive = Expr::lam(BinderInfo::Default, receiver_ty.clone(), motive_body);
        let motive_val_ty = Expr::pi(BinderInfo::Default, receiver_ty, Expr::sort(level.clone()));
        if !self.try_unify(&motive_ty, &motive_val_ty) {
            return Err(refuse(&head_name, "the motive does not fit the eliminator"));
        }
        if matches!(head, ElimHead::Rec | ElimHead::RecOn) && !self.dot_elim.uncompiled {
            let level = self.metas.instantiate_level(&level);
            if !level.is_zero() {
                return Err(refuse(
                    &head_name,
                    "a recursor is modelled only at a proposition; Lean's code generator \
                     decides the rest",
                ));
            }
        }
        let result = Expr::apps(result, [motive, receiver.clone()]);
        let result = self.metas.instantiate(&result);
        let result = self.metas.instantiate_levels(&result);
        if Self::has_unassigned_meta_fvar(&result) || self.mentions_flexible_level(&result) {
            return Err(refuse(
                &head_name,
                "the eliminator's parameters are not determined",
            ));
        }
        Ok(result)
    }

    /// Does `e` mention a universe parameter that is not a rigid declared one
    /// (Clean's encoding of a universe metavariable)? Call on a term whose
    /// levels are instantiated.
    fn mentions_flexible_level(&self, e: &Expr) -> bool {
        fn level_flexible(metas: &MetaState, l: &Level) -> bool {
            match l {
                Level::Zero => false,
                Level::Param(name) => !metas.is_rigid_level_param(name),
                Level::Succ(l) => level_flexible(metas, l),
                Level::Max(a, b) | Level::IMax(a, b) => {
                    level_flexible(metas, a) || level_flexible(metas, b)
                }
            }
        }
        if !e.has_level_param_quick() && !e.has_level_mvar_quick() {
            return false;
        }
        match e.kind() {
            ExprKind::Sort(l) => level_flexible(&self.metas, l),
            ExprKind::Const(_, levels) => levels.iter().any(|l| level_flexible(&self.metas, l)),
            ExprKind::App(f, a) => {
                self.mentions_flexible_level(f) || self.mentions_flexible_level(a)
            }
            ExprKind::Lam(_, t, b) | ExprKind::Pi(_, t, b) => {
                self.mentions_flexible_level(t) || self.mentions_flexible_level(b)
            }
            ExprKind::Let(_, t, v, b, _) => {
                self.mentions_flexible_level(t)
                    || self.mentions_flexible_level(v)
                    || self.mentions_flexible_level(b)
            }
            ExprKind::Proj(_, _, x) | ExprKind::MData(_, x) => self.mentions_flexible_level(x),
            ExprKind::BVar(_) | ExprKind::FVar(_) | ExprKind::Lit(_) => false,
            // Extension forms: answer conservatively.
            _ => true,
        }
    }

    /// Does `e` mention an unassigned metavariable (encoded as an `FVar`)?
    /// Call on an instantiated term.
    fn has_unassigned_meta_fvar(e: &Expr) -> bool {
        if !e.has_fvar_quick() {
            return false;
        }
        match e.kind() {
            ExprKind::FVar(id) => MetaState::from_fvar(*id).is_some(),
            ExprKind::App(f, a) => {
                Self::has_unassigned_meta_fvar(f) || Self::has_unassigned_meta_fvar(a)
            }
            ExprKind::Lam(_, t, b) | ExprKind::Pi(_, t, b) => {
                Self::has_unassigned_meta_fvar(t) || Self::has_unassigned_meta_fvar(b)
            }
            ExprKind::Let(_, t, v, b, _) => {
                Self::has_unassigned_meta_fvar(t)
                    || Self::has_unassigned_meta_fvar(v)
                    || Self::has_unassigned_meta_fvar(b)
            }
            ExprKind::Proj(_, _, x) | ExprKind::MData(_, x) => Self::has_unassigned_meta_fvar(x),
            ExprKind::BVar(_) | ExprKind::Sort(_) | ExprKind::Const(..) | ExprKind::Lit(_) => false,
            // Extension forms: answer conservatively.
            _ => true,
        }
    }
}

#[cfg(test)]
#[path = "elab_dot_elim_tests.rs"]
mod tests;
