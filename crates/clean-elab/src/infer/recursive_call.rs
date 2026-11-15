// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Structural recursive calls retain and check the original argument telescope.
//!
//! A recursive hypothesis generalizes movable parameters on either side of the
//! major argument. Parameters needed by the major's type stay recursor-fixed;
//! their supplied arguments must still be elaborated, checked, and equal to the
//! fixed originals before the application can be replaced by an IH.

use super::{ArgsFollow, ElabCtx, RecursiveDefContext, RecursiveParam};
use crate::unify::MetaState;
use crate::ElabError;
use clean_kernel::{BinderInfo, Expr, ExprKind, ExprVisitor, FVarId, TypeChecker};
use clean_parser::{SurfaceArg, SurfaceExpr, SurfaceName};
use std::collections::HashSet;

/// Sets `found` when any of `targets` occurs free.
struct FVarSetFinder<'t> {
    targets: &'t HashSet<FVarId>,
    found: &'t mut bool,
}

impl ExprVisitor for FVarSetFinder<'_> {
    type Result = ();
    fn combine(&self, _a: (), _b: ()) {}
    fn visit_fvar(&mut self, id: FVarId) {
        if self.targets.contains(&id) {
            *self.found = true;
        }
    }
}

impl RecursiveDefContext {
    pub(super) fn decreasing_binder_index(&self) -> Option<usize> {
        self.parameters
            .iter()
            .enumerate()
            .filter(|(_, p)| !p.captured_section && p.binder_info == BinderInfo::Default)
            .nth(self.decreasing_arg_pos)
            .map(|(index, _)| index)
    }
}

/// Simultaneous substitution, not sequential FVar replacement: an actual
/// argument may itself mention another original parameter.
fn instantiate_parameters(ty: &Expr, params: &[RecursiveParam], args: &[Expr]) -> Expr {
    let mut result = ty.clone();
    for param in params.iter().take(args.len()) {
        result = result.abstract_fvar(param.fvar);
    }
    for arg in args.iter().rev() {
        result = result.instantiate(arg);
    }
    result
}

impl ElabCtx<'_> {
    /// Complete the original declaration telescope before entering its body.
    /// The final declaration wrapper consumes this same ordered auto-implicit
    /// packet. Local `let rec` helpers run in term scope and must not acquire
    /// the enclosing declaration's implicit parameters as their own arguments.
    pub(super) fn capture_recursive_auto_implicit_parameters(&mut self) -> Result<(), ElabError> {
        if self.in_term_body || self.recursive_def_ctx.is_none() {
            return Ok(());
        }
        let packet = self.snapshot_auto_implicits_since(0);
        let Some(ctx) = self.recursive_def_ctx.as_ref() else {
            return Ok(());
        };
        // Identity, not spelling: a written binder may shadow an auto name.
        // Reconstruct the written telescope on repeated calls without
        // duplicating its auto packet.
        let auto_fvars: HashSet<_> = packet.iter().map(|(_, id, _)| *id).collect();
        let written: Vec<_> = ctx
            .parameters
            .iter()
            .filter(|parameter| !auto_fvars.contains(&parameter.fvar))
            .cloned()
            .collect();
        let sections = written.iter().take_while(|p| p.captured_section).count();
        if written[sections..].iter().any(|p| p.captured_section) {
            return Err(ElabError::InternalInvariant(
                "recursive declaration has a nonleading section parameter".to_string(),
            ));
        }
        let mut used = HashSet::new();
        for parameter in &written[..sections] {
            used.extend(crate::tactic::hypothesis::collect_fvars(
                &self.metas.instantiate(&parameter.type_),
            ));
        }
        let captured = Self::section_auto_prefix_count(&packet, used);
        let autos: Vec<_> = packet
            .into_iter()
            .enumerate()
            .map(|(index, (name, fvar, type_))| RecursiveParam {
                name,
                binder_info: BinderInfo::Implicit,
                captured_section: index < captured,
                fvar,
                type_,
            })
            .collect();
        let mut parameters = Vec::with_capacity(autos.len() + written.len());
        parameters.extend(autos[..captured].iter().cloned());
        parameters.extend(written[..sections].iter().cloned());
        parameters.extend(autos[captured..].iter().cloned());
        parameters.extend(written[sections..].iter().cloned());
        if let Some(ctx) = self.recursive_def_ctx.as_mut() {
            ctx.parameters = parameters;
        }
        Ok(())
    }

    pub(super) fn generalize_recursive_parameters(
        &mut self,
        major_ty: &Expr,
    ) -> Result<Vec<(FVarId, BinderInfo, Expr)>, ElabError> {
        let Some(ctx) = self.recursive_def_ctx.as_ref() else {
            return Ok(Vec::new());
        };
        let major = ctx
            .decreasing_binder_index()
            .ok_or(ElabError::CannotInfer)?;
        let parameters = ctx.parameters.clone();
        let major_ty = self.metas.instantiate(major_ty);
        let major_args = major_ty.get_app_args();
        let num_params = match major_ty.get_app_fn().kind() {
            ExprKind::Const(name, _) => self
                .env
                .get_inductive(name)
                .map(|ind| ind.num_params as usize),
            _ => None,
        };
        let index_params: Vec<_> = (0..major)
            .filter(|&index| {
                !parameters[index].captured_section
                    && num_params.is_some_and(|count| {
                        major_args.iter().skip(count).any(|arg| {
                    matches!(arg.kind(), ExprKind::FVar(id) if *id == parameters[index].fvar)
                })
                    })
            })
            .collect();
        let mut dependencies = vec![major_ty.clone()];
        let mut fixed: Vec<_> = parameters.iter().map(|p| p.captured_section).collect();
        // Binder domains refer only to earlier binders, so one reverse pass
        // computes the transitive prefix dependency closure.
        for index in (0..major).rev() {
            let param = &parameters[index];
            if fixed[index]
                || dependencies
                    .iter()
                    .any(|ty| ty.abstract_fvar(param.fvar).has_loose_bvar(0))
            {
                fixed[index] = true;
                dependencies.push(self.metas.instantiate(&param.type_));
            }
        }
        let indices: Vec<_> = (0..parameters.len())
            .filter(|&index| index != major && !fixed[index])
            .collect();
        let result = indices
            .iter()
            .map(|&index| {
                let p = &parameters[index];
                (
                    p.fvar,
                    p.binder_info,
                    self.metas
                        .instantiate_levels(&self.metas.instantiate(&p.type_)),
                )
            })
            .collect();
        if let Some(ctx) = &mut self.recursive_def_ctx {
            ctx.generalized_params = indices;
            ctx.index_params = index_params;
        }
        Ok(result)
    }

    /// The parameters whose value can differ between the levels of the
    /// current recursive match: the major, the recursor-index parameters, and
    /// every generalized parameter some recursive call passed a value other
    /// than itself (`recursive_changed_params`, recorded by
    /// `try_elab_recursive_call`). A generalized parameter every call passes
    /// back unchanged has its original value at every level. A parameter that
    /// is neither generalized nor an index is checked equal to the original at
    /// every call.
    pub(super) fn recursive_changing_params(&self) -> Vec<FVarId> {
        let Some(ctx) = self.recursive_def_ctx.as_ref() else {
            return Vec::new();
        };
        let Some(major) = ctx.decreasing_binder_index() else {
            return Vec::new();
        };
        ctx.parameters
            .iter()
            .enumerate()
            .filter(|(index, param)| {
                *index == major
                    || ctx.index_params.contains(index)
                    || (ctx.generalized_params.contains(index)
                        && self.recursive_changed_params.contains(&param.fvar))
            })
            .map(|(_, param)| param.fvar)
            .collect()
    }

    /// The free variables a `.rec` minor premise must not mention.
    ///
    /// `T.rec` computes the whole recursive function from the match site
    /// DOWNWARD: an induction hypothesis stands for the minors re-run at a
    /// structurally smaller major, with the generalized parameters bound to
    /// the recursive call's arguments. Everything the minors read from
    /// OUTSIDE the match is not re-run — it keeps the value it had for the
    /// ORIGINAL arguments. That is only sound for values that do not depend on
    /// those arguments. Measured 2026-09-25 (Lean 4.8.0 disagreeing each time):
    ///
    /// * `def h (b : Nat) : Nat := let q := b; match b with | succ y => h y + q
    ///   | zero => q` — the IH reused `q := b`, so `h 2 = 6` was provable by
    ///   `rfl` (Lean: `h 2 = 3`);
    /// * `def c (a b : Nat) := match a with | zero => b + 10 | succ x => match
    ///   b with | succ y => c 0 y + 100 | zero => x` — recursion on `b` sits
    ///   inside the case split on `a`, so the IH reused the outer `x` and
    ///   ignored the call's `0`: `c 1 2 = 200` (Lean: `111`).
    ///
    /// Forbidden: the ORIGINAL major and index parameters, every generalized
    /// parameter some recursive call changes (the minors must see them only
    /// through the motive; see `recursive_changing_params`), and every local
    /// bound after the recursive parameters that may depend on one of them. A
    /// generalized parameter every call passes back unchanged keeps its
    /// original value at every level, so it is not forbidden: `let z := k + 1;
    /// match n with | 0 => z | m+1 => g k m + z` computes Lean's value. A `let`
    /// (or term `have`) is judged by its type and raw stored value,
    /// transitively. Any other local bound after the parameters (a pattern
    /// variable of an enclosing match, a `fun` binder) has no recorded
    /// provenance — a pattern variable's type does not mention the scrutinee
    /// it was cut from — so it is treated as dependent. Locals bound before
    /// the first parameter cannot depend on it.
    pub(super) fn recursive_minor_forbidden_fvars(&self) -> HashSet<FVarId> {
        let mut forbidden = HashSet::new();
        let Some(ctx) = self.recursive_def_ctx.as_ref() else {
            return forbidden;
        };
        if ctx.decreasing_binder_index().is_none() {
            return forbidden;
        }
        let params: HashSet<FVarId> = ctx.parameters.iter().map(|p| p.fvar).collect();
        // A generalized parameter that every recursive call passes back
        // unchanged has its original value at every level, so a value computed
        // from it outside the match is the same at every level too.
        forbidden.extend(self.recursive_changing_params());
        let mentions_forbidden = |expr: &Expr, forbidden: &HashSet<FVarId>| {
            let expr = self.metas.instantiate(expr);
            let mut found = false;
            if expr.has_fvar_quick() {
                let mut finder = FVarSetFinder {
                    targets: forbidden,
                    found: &mut found,
                };
                finder.visit_expr(&expr);
            }
            found
        };
        let mut after_params = false;
        for (_, fvar, ty) in self.locals.iter() {
            if params.contains(fvar) {
                after_params = true;
                continue;
            }
            if !after_params {
                continue;
            }
            let value = self.locals.let_value(*fvar);
            let dependent = match value {
                Some(value) => {
                    mentions_forbidden(ty, &forbidden) || mentions_forbidden(value, &forbidden)
                }
                None => true,
            };
            if dependent {
                forbidden.insert(*fvar);
            }
        }
        forbidden
    }

    /// Refuse a `.rec` lowering whose minors (or motive) read a value computed
    /// from the ORIGINAL recursive arguments; see
    /// `recursive_minor_forbidden_fvars`.
    pub(super) fn check_recursive_minors_closed(
        &self,
        forbidden: &HashSet<FVarId>,
        motive_and_minors: &[Expr],
    ) -> Result<(), ElabError> {
        if forbidden.is_empty() {
            return Ok(());
        }
        let mut found = false;
        for expr in motive_and_minors {
            let expr = self.metas.instantiate(expr);
            if expr.has_fvar_quick() {
                let mut finder = FVarSetFinder {
                    targets: forbidden,
                    found: &mut found,
                };
                finder.visit_expr(&expr);
            }
            if found {
                break;
            }
        }
        if !found {
            return Ok(());
        }
        let func = self
            .recursive_def_ctx
            .as_ref()
            .map_or_else(String::new, |ctx| ctx.func_name.to_string());
        let names: Vec<String> = self
            .locals
            .iter()
            .filter(|(_, fvar, _)| forbidden.contains(fvar))
            .filter(|(_, fvar, _)| {
                motive_and_minors.iter().any(|expr| {
                    let expr = self.metas.instantiate(expr);
                    let single: HashSet<FVarId> = std::iter::once(*fvar).collect();
                    let mut hit = false;
                    let mut finder = FVarSetFinder {
                        targets: &single,
                        found: &mut hit,
                    };
                    finder.visit_expr(&expr);
                    hit
                })
            })
            .map(|(name, _, _)| format!("`{name}`"))
            .collect();
        Err(ElabError::Unsupported {
            feature: format!(
                "structural recursion in `{func}`: a match alternative on the decreasing argument reads {}, bound outside that match from the recursive parameters. An induction hypothesis re-runs only the match alternatives, so it would reuse that outer value at every recursive call and compute a different function than the source. Match on the decreasing argument before any other case split or binding that depends on the parameters",
                if names.is_empty() {
                    "a recursive parameter's original value".to_string()
                } else {
                    names.join(", ")
                }
            ),
        })
    }

    pub(super) fn try_elab_recursive_call(
        &mut self,
        func: &SurfaceExpr,
        args: &[SurfaceArg],
    ) -> Result<Option<Expr>, ElabError> {
        let Some(mut ctx) = self.recursive_def_ctx.clone() else {
            return Ok(None);
        };
        let spelling = match Self::unwrap_surface_parens(func) {
            SurfaceExpr::Ident(_, name) => (!name.is_anonymous()
                && !name.is_relative_constructor()
                && self.lookup_local(name).is_none())
            .then(|| name.clone()),
            SurfaceExpr::Proj(_, base, proj) => Self::try_collect_qualified_name(base, proj)
                .filter(|name| {
                    name.split_first().is_some_and(|(leading, rest)| {
                        self.namespace_projection_name(&leading, &rest).is_some()
                    })
                }),
            _ => None,
        };
        // Named arguments remain on the ordinary named-application path.
        let Some(spelling) = spelling else {
            return Ok(None);
        };
        if args.is_empty() || args.iter().any(|arg| arg.name.is_some()) {
            return Ok(None);
        }
        // The bare self name is a reserved recursive binder, unless a local
        // shadows it. Qualified names follow the ordinary namespace lookup,
        // with the pending declarations visible at their canonical names.
        let call_name = if spelling.parent().is_anonymous() && spelling == ctx.short_name() {
            ctx.func_name.clone()
        } else {
            let pending: Vec<_> = std::iter::once(&ctx.func_name)
                .chain(ctx.sibling_names.iter())
                .map(|name| name.name().clone())
                .collect();
            let Some(resolved) = self.resolve_qualified_chain_with_pending(&spelling, &pending)
            else {
                return Ok(None);
            };
            if !pending.contains(&resolved) {
                return Ok(None);
            }
            SurfaceName::from_name(resolved)
        };
        let major = ctx
            .decreasing_binder_index()
            .ok_or(ElabError::CannotInfer)?;
        let call_major = if self.explicit_mode {
            ctx.parameters[..major]
                .iter()
                .filter(|p| !p.captured_section)
                .count()
        } else {
            ctx.decreasing_arg_pos
        };
        let param = ctx.decreasing_arg_name.clone();
        let Some(arg) = args.get(call_major) else {
            self.recursive_call_miss = Some(format!(
                "structural recursion on `{param}`, but a recursive call passes no argument \
                 for `{param}`"
            ));
            return Ok(None);
        };
        // The decreasing argument may be a direct field or an application of
        // a strictly positive function field. Collect only unnamed index args;
        // the field's actual telescope and the IH below validate every index.
        let mut field_head = Self::unwrap_surface_parens(&arg.expr);
        let mut field_arguments = Vec::new();
        while let SurfaceExpr::App(_, function, arguments) = field_head {
            if arguments.iter().any(|argument| argument.name.is_some()) {
                return Ok(None);
            }
            field_arguments.splice(0..0, arguments.iter().cloned());
            field_head = Self::unwrap_surface_parens(function);
        }
        let not_a_field = format!(
            "structural recursion on `{param}`, but a recursive call passes {} for \
             `{param}` — not a variable bound to a constructor field of `{param}`; \
             recursion on such an argument needs a `termination_by` measure",
            if matches!(Self::unwrap_surface_parens(&arg.expr), SurfaceExpr::Lit(..)) {
                "a literal"
            } else {
                "a compound expression"
            }
        );
        let SurfaceExpr::Ident(_, name) = field_head else {
            self.recursive_call_miss = Some(not_a_field);
            return Ok(None);
        };
        // An application is a function-valued field applied to indices only
        // when its head is a local; `n + 1` (`HAdd.hAdd n 1`) is a compound
        // expression, not a reference to the global `HAdd.hAdd`.
        if !field_arguments.is_empty() && self.lookup_local(name).is_none() {
            self.recursive_call_miss = Some(not_a_field);
            return Ok(None);
        }
        let Some((mut field, _)) = self.lookup_local(name) else {
            self.recursive_call_miss = Some(format!(
                "structural recursion on `{param}`, but a recursive call passes `{name}` for \
                 `{param}`, which is not a local variable"
            ));
            return Ok(None);
        };
        // A pattern variable the equation compiler re-binds from a freshly
        // named constructor field (`let y := y._f0`, see
        // `compile_pattern_matrix`'s `reserved`) is a `let` whose value IS the
        // field: follow such pure aliases to the field that owns the IH. The
        // kernel check below still requires the supplied major to be
        // definitionally the field.
        let mut major_aliases = vec![field];
        while !ctx.ih_map.contains_key(&field) {
            let next = match self.locals.reduction_value(field) {
                Some(value) => match self.metas.instantiate(value).kind() {
                    ExprKind::FVar(next) if MetaState::from_fvar(*next).is_none() => *next,
                    _ => break,
                },
                None => break,
            };
            if major_aliases.contains(&next) {
                break;
            }
            field = next;
            major_aliases.push(next);
        }
        let Some(&ih) = ctx.ih_map.get(&field) else {
            self.recursive_call_miss = Some(if ctx.ih_map.is_empty() {
                format!(
                    "structural recursion on `{param}`, but a recursive call is not inside a \
                     `match` on `{param}`, so no constructor field of `{param}` is in scope"
                )
            } else if !field_arguments.is_empty() {
                not_a_field
            } else {
                format!(
                    "structural recursion on `{param}`, but a recursive call passes `{name}` for \
                     `{param}`, which is not a recursive constructor field that the `match` on \
                     `{param}` binds — a deeper sub-term is course-of-values recursion (Lean \
                     compiles it through `brecOn`, which Clean's recursor lowering does not \
                     emit) and any other value needs a `termination_by` measure"
                )
            });
            return Ok(None);
        };

        // The existing fused nested-fold envelope has one explicit major per
        // member, but its sibling major has a DIFFERENT declared domain. Use
        // the exact annotation captured before arm scope, never the argument's
        // own inferred type as a purported source contract.
        let primary = call_name == ctx.func_name;
        let sibling_result = if primary {
            None
        } else {
            let (_, signature) = ctx
                .sibling_types
                .iter()
                .find(|(name, _)| name == &call_name)
                .ok_or_else(|| {
                    ElabError::InternalInvariant(
                        "recursive sibling call lost its declared type".into(),
                    )
                })?;
            let signature = self.whnf(signature);
            let ExprKind::Pi(binder, domain, codomain) = signature.kind() else {
                return Err(ElabError::InternalInvariant(
                    "nested-fold member must have an explicit major".into(),
                ));
            };
            if binder.info != BinderInfo::Default
                || major != 0
                || ctx.parameters.len() != 1
                || !ctx.generalized_params.is_empty()
            {
                return Err(ElabError::InternalInvariant(
                    "nested-fold member escaped its single-major envelope".into(),
                ));
            }
            ctx.parameters[0].type_ = domain.as_ref().clone();
            Some(codomain.as_ref().clone())
        };

        let mut actuals = Vec::new();
        let mut defaults = Vec::new();
        let mut next = 0;
        for (index, param) in ctx.parameters.iter().enumerate() {
            let domain = instantiate_parameters(&param.type_, &ctx.parameters, &actuals);
            let domain = self
                .metas
                .instantiate_levels(&self.metas.instantiate(&domain));
            let actual = if param.captured_section {
                Expr::fvar(param.fvar)
            } else if self.explicit_mode || param.binder_info == BinderInfo::Default {
                let Some(arg) = args.get(next) else {
                    break; // Preserve partial application of trailing parameters.
                };
                next += 1;
                let expr =
                    self.elaborate_arg_with_expected_type(&arg.expr, Some(domain.clone()))?;
                self.coerce_to_expected_type(&expr, &domain)?
            } else if ctx.generalized_params.contains(&index) || ctx.index_params.contains(&index) {
                // Infer changed implicit parameters from later explicit args.
                // Preserve the old local argument only when no constraint
                // determines it (e.g. an otherwise unused implicit instance).
                let meta = self.fresh_meta(domain);
                defaults.push((index, meta.clone(), Expr::fvar(param.fvar)));
                meta
            } else {
                Expr::fvar(param.fvar)
            };
            actuals.push(actual);
        }
        let mut structural_child = Expr::fvar(field);
        let mut result = Expr::fvar(ih);
        for argument in &field_arguments {
            let field_type = self.infer_type(&structural_child)?;
            let field_type = self.whnf(&field_type);
            let ExprKind::Pi(binder, domain, _) = field_type.kind() else {
                return Err(ElabError::CannotInfer);
            };
            if binder.info != BinderInfo::Default {
                return Err(ElabError::Unsupported {
                    feature: "implicit indices of a function-valued recursive field".into(),
                });
            }
            let value = self
                .elaborate_arg_with_expected_type(&argument.expr, Some(domain.as_ref().clone()))?;
            let value = self.coerce_to_expected_type(&value, domain)?;
            structural_child = Expr::app(structural_child, value.clone());
            result = Expr::app(result, value);
        }
        for &index in &ctx.generalized_params {
            if let Some(actual) = actuals.get(index) {
                result = Expr::app(result, actual.clone());
            }
        }
        if let Some(codomain) = sibling_result {
            let actual_major = actuals.get(major).ok_or(ElabError::CannotInfer)?;
            let expected = codomain.instantiate(actual_major);
            let actual = self.infer_type(&result)?;
            if !self.is_def_eq(&actual, &expected) {
                return Err(ElabError::TypeMismatch {
                    expected: expected.to_string(),
                    actual: actual.to_string(),
                });
            }
        }
        // A recursive function may itself return a function. Arguments beyond
        // its declaration binders are ordinary checked applications, not junk
        // to discard after rewriting the recursive head.
        let mut pending_instances = Vec::new();
        for arg in &args[next..] {
            let ty = self.infer_type(&result)?;
            // `arg` is the explicit argument that follows this implicit run.
            let (applied, ty, pending) =
                self.insert_implicit_args_deferring_instances(result, &ty, ArgsFollow::Yes);
            result = applied;
            pending_instances.extend(pending);
            let ExprKind::Pi(_, domain, _) = ty.kind() else {
                return Err(ElabError::TypeMismatch {
                    expected: "a function for the remaining recursive-call argument".to_string(),
                    actual: ty.to_string(),
                });
            };
            let value =
                self.elaborate_arg_with_expected_type(&arg.expr, Some(domain.as_ref().clone()))?;
            let value = self.coerce_to_expected_type(&value, domain)?;
            result = Expr::app(result, value);
        }
        for (index, meta, default) in defaults {
            let unresolved = self.metas.instantiate(&meta);
            if let ExprKind::FVar(id) = unresolved.kind() {
                if let Some(id) = MetaState::from_fvar(*id) {
                    let param = &ctx.parameters[index];
                    let value = if param.binder_info == BinderInfo::InstImplicit {
                        let goal = instantiate_parameters(
                            &param.type_,
                            &ctx.parameters,
                            &actuals[..index],
                        );
                        let goal = self
                            .metas
                            .instantiate_levels(&self.metas.instantiate(&goal));
                        self.resolve_instance(&goal).unwrap_or(default)
                    } else {
                        default
                    };
                    if !self.metas.assign(id, value) {
                        return Err(ElabError::CannotInfer);
                    }
                }
            }
        }
        for actual in &mut actuals {
            *actual = self
                .metas
                .instantiate_levels(&self.metas.instantiate(actual));
        }
        // Record every generalized parameter this call passes a value other
        // than itself — or does not pass at all (a partial application leaves
        // it to whatever the IH is later applied to). The recursion-site check
        // (`recursion_site`) treats only such parameters as varying between
        // levels.
        for &index in &ctx.generalized_params {
            let param = &ctx.parameters[index];
            let unchanged = actuals.get(index).is_some_and(
                |actual| matches!(actual.kind(), ExprKind::FVar(id) if *id == param.fvar),
            );
            if !unchanged {
                self.recursive_changed_params.insert(param.fvar);
            }
        }

        // An erased argument would otherwise evade the final kernel check of
        // the generated IH application. Check EVERY original supplied argument
        // with the kernel, including the major and recursor-fixed prefixes.
        let checker = TypeChecker::with_context(self.env, self.build_local_ctx());
        for (index, actual) in actuals.iter().enumerate() {
            let param = &ctx.parameters[index];
            let domain = instantiate_parameters(&param.type_, &ctx.parameters, &actuals[..index]);
            let domain = self
                .metas
                .instantiate_levels(&self.metas.instantiate(&domain));
            checker
                .check_type(actual, &domain)
                .map_err(|error| ElabError::TypeMismatch {
                    expected: format!("recursive parameter {} : {domain}", param.name),
                    actual: error.to_string(),
                })?;
            // A `let` alias of the field is the field: the enclosing `let`
            // expression binds it to exactly that value.
            let is_major_alias = field_arguments.is_empty()
                && matches!(actual.kind(), ExprKind::FVar(id) if major_aliases.contains(id));
            if index == major && !is_major_alias && !checker.is_def_eq(actual, &structural_child) {
                // Elaboration may insert a coercion. An IH for this field does
                // not justify replacing recursion on a different, coerced value.
                return Err(ElabError::TypeMismatch {
                    expected: "the structural child associated with this induction hypothesis"
                        .to_string(),
                    actual: actual.to_string(),
                });
            }
            if index != major
                && !ctx.generalized_params.contains(&index)
                && !ctx.index_params.contains(&index)
                && !checker.is_def_eq(actual, &Expr::fvar(param.fvar))
            {
                return Err(ElabError::TypeMismatch {
                    expected: format!("fixed recursive parameter {}", param.name),
                    actual: actual.to_string(),
                });
            }
        }
        if !self.resolve_deferred_instances(&pending_instances) {
            return Err(ElabError::CannotInfer);
        }
        Ok(Some(
            self.metas
                .instantiate_levels(&self.metas.instantiate(&result)),
        ))
    }
}

#[cfg(test)]
#[path = "recursive_call_auto_implicit_tests.rs"]
mod auto_implicit_tests;
