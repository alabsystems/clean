// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lean v4.30 HETEROGENEOUS noConfusionType/noConfusion generation for
//! PARAMETERIZED (`num_params > 0`) inductive types.
//!
//! Design: `designs/2026-07-03-noconfusion-ctoridx-convention.md` (§3, §5/N1).
//! Ground truth: `lean` 4.30.0-rc2 `#print` probes and upstream
//! `src/lean/Lean/Meta/Constructions/NoConfusion.lean` (`mkNoConfusionType`,
//! `mkNoConfusionCtorArg`, `mkNoConfusionCoreImp`, `mkEqNDRecTelescope`).
//!
//! For `inductive T (p₁ : A₁) … (pₙ : Aₙ) : Sort ℓ` this emits:
//!
//! ```text
//! T.noConfusionType.{u, us} :
//!   Sort u → {p₁ : A₁} → … → {pₙ : Aₙ} → T p… →
//!            {p₁' : A₁} → … → {pₙ' : Aₙ[p'/p]} → T p'… → Sort u
//! T.noConfusion.{u, us} :
//!   {P : Sort u} → {p…} → {t : T p…} → {p'…} → {t' : T p'…} →
//!     (p₁ ~ p₁') → … → (pₙ ~ pₙ') → HEq t t' → T.noConfusionType P p… t p'… t'
//! ```
//!
//! where `pᵢ ~ pᵢ'` is `Eq` iff `Aᵢ` mentions no earlier param, else `HEq`
//! (Sigma: `α = α'`, `β ≍ β'`), and the diagonal field chain in
//! `noConfusionType` uses `HEq` for every field whose type mentions a param
//! or an earlier field, `Eq` only for fully-concrete fields (`mkEqHEq` at
//! abstract primed params, NoConfusion.lean:30-46). Prop-valued fields are
//! skipped (unchanged rule).
//!
//! `noConfusion`'s value is an `Eq.ndrec` telescope substituting each param
//! equality outermost-first (`eq_of_heq` for `HEq` hypotheses, exactly as in
//! the printed `Sigma.noConfusion`), then transporting the diagonal `casesOn`
//! core along `eq_of_heq h_t`. Each telescope step re-generalizes the whole
//! remaining primed group (later primed params, `t'`, later premises, the
//! major `HEq`) — a uniform superset of upstream's `substEq`-driven minimal
//! revert; the types are identical, only the (never-type-compared) value
//! spelling differs.
//!
//! `num_params = 0` types NEVER route here: the classic builder in
//! `inductive_no_confusion.rs` is byte-for-byte what v4.30 produces for them
//! (the two schemes coincide — design §1.2), and keeping that path untouched
//! is what guarantees the 0-param invariance gate (design §6/A6).

use crate::expr::{BinderInfo, Expr, ExprKind, FVarId};
use crate::inductive::{InductiveDecl, InductiveType};
use crate::level::Level;
use crate::name::Name;
use crate::tc::{LocalContext, TypeChecker};

use super::decl_builder::EnvDeclBuilder;
use super::inductive_fixed_indices::{fresh_univ_name, ind_const_with_levels};
use super::types::EnvError;
use super::Environment;

/// A binder opened as a builder FVar: its id, the `Expr::fvar` reference, and
/// its (instantiated, fvar-referencing) type.
#[derive(Clone)]
struct OpenedLocal {
    id: FVarId,
    var: Expr,
    ty: Expr,
}

/// Per-constructor generation data (primary type only).
struct HeteroCtor {
    /// The constructor's full Pi type (params + fields).
    type_: Expr,
    /// Universe level of each field's type (`Sort l`); `l = 0` ⇒ Prop field,
    /// skipped in the equality chain.
    sort_levels: Vec<Level>,
    /// v4.30 `mkEqHEq` decision per field: `true` ⇒ `HEq` (field type
    /// mentions a param or an earlier field), `false` ⇒ `Eq` (fully concrete).
    uses_heq: Vec<bool>,
}

/// Shared per-inductive generation data.
struct HeteroInfo {
    result_univ_name: Name,
    level_params: Vec<Name>,
    /// Sort level `s_k` of each param type (`A_k : Sort s_k`).
    param_sorts: Vec<Level>,
    /// `true` ⇒ `A_k` mentions an earlier param ⇒ `HEq` premise.
    param_deps: Vec<bool>,
    /// Level `ℓ` with `T p… : Sort ℓ` — the major `HEq` / `Eq.ndrec` level.
    ind_sort_level: Level,
    cases_on_name: Name,
    ctors: Vec<HeteroCtor>,
}

/// The current `Eq.ndrec` telescope state: the not-yet-substituted primed
/// group (`p'ᵢ..p'ₙ`, `t'`, premises `hᵢ..hₙ`, major `h_t`), rebound afresh at
/// each step with the substituted param replaced.
#[derive(Clone)]
struct EqTelescopeGroup {
    primed: Vec<OpenedLocal>,
    tp: OpenedLocal,
    hs: Vec<OpenedLocal>,
    ht: OpenedLocal,
}

/// Read-only context for `noConfusion` value construction.
struct HeteroNcCx<'a> {
    env: &'a Environment,
    decl: &'a InductiveDecl,
    ind_name: &'a Name,
    info: &'a HeteroInfo,
    us: &'a [Name],
    p_var: &'a Expr,
    xs1: &'a [OpenedLocal],
    t_var: &'a Expr,
    t_ty: &'a Expr,
    nct_const: &'a Expr,
}

fn eq_app(level: &Level, ty: &Expr, a: &Expr, b: &Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![level.clone()]),
        [ty.clone(), a.clone(), b.clone()],
    )
}

fn heq_app(level: &Level, ty_a: &Expr, a: &Expr, ty_b: &Expr, b: &Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("HEq"), vec![level.clone()]),
        [ty_a.clone(), a.clone(), ty_b.clone(), b.clone()],
    )
}

fn eq_of_heq_app(level: &Level, ty: &Expr, a: &Expr, b: &Expr, h: &Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("eq_of_heq"), vec![level.clone()]),
        [ty.clone(), a.clone(), b.clone(), h.clone()],
    )
}

/// Does `e` reference any of the `limit` innermost enclosing binders of the
/// telescope it was taken from? (`BVar(x)` with `x - depth < limit`.)
///
/// With `limit = field_idx + num_params` on a constructor field type this is
/// the v4.30 `mkEqHEq` structural rule: the a-side and b-side types are
/// syntactically different (⇒ `HEq`) exactly when the field type mentions a
/// param or an earlier field. With `num_params = 0` it degenerates to the
/// classic earlier-fields-only rule.
fn mentions_bound_below(e: &Expr, limit: usize, depth: u32) -> bool {
    match &e.kind {
        ExprKind::BVar(idx) => *idx >= depth && ((*idx - depth) as usize) < limit,
        ExprKind::App(f, a) => {
            mentions_bound_below(f, limit, depth) || mentions_bound_below(a, limit, depth)
        }
        ExprKind::Pi(_, domain, body) | ExprKind::Lam(_, domain, body) => {
            mentions_bound_below(domain, limit, depth)
                || mentions_bound_below(body, limit, depth + 1)
        }
        ExprKind::Let(_, ty, val, body, _) => {
            mentions_bound_below(ty, limit, depth)
                || mentions_bound_below(val, limit, depth)
                || mentions_bound_below(body, limit, depth + 1)
        }
        ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) | ExprKind::Squash(inner) => {
            mentions_bound_below(inner, limit, depth)
        }
        _ => false,
    }
}

/// The v4.30 heterogeneous `noConfusion(Type)` of a parameterized inductive
/// references `HEq`/`HEq.refl`/`eq_of_heq` in its per-dependent-param and
/// per-major premises. In the real prelude these are always registered
/// (`init_heq` runs immediately after `init_eq` in `init_prelude_core`), but
/// some minimal / domain-specific environments (e.g. the `add_decl` audit
/// harnesses that seed only `init_eq` + a single domain) build parameterized
/// structures without HEq. Generating a `noConfusion` that references an absent
/// constant would store a decl that fails to type-check downstream — so, as
/// with the existing "skip noConfusion on error rather than fail add_inductive"
/// discipline, we signal a skip here. In any environment where HEq IS present
/// the generation proceeds unchanged.
fn require_heq(env: &Environment) -> Result<(), EnvError> {
    for dep in ["HEq", "HEq.refl", "eq_of_heq"] {
        let name = Name::from_string(dep);
        if env.get_const(&name).is_none() {
            return Err(EnvError::MissingRequiredDeclaration {
                init: "noConfusion (v4.30 heterogeneous)",
                decl: name,
            });
        }
    }
    Ok(())
}

/// Open the first `n` Pi binders of `ty` as fresh builder locals,
/// instantiating as we go. Errors if `ty` has fewer than `n` binders.
fn open_binders(
    b: &mut EnvDeclBuilder,
    ty: &Expr,
    n: usize,
    who: &Name,
) -> Result<(Vec<OpenedLocal>, Expr), EnvError> {
    let mut out = Vec::with_capacity(n);
    let mut cur = ty.clone();
    for _ in 0..n {
        let ExprKind::Pi(_, domain, body) = &cur.kind else {
            return Err(EnvError::UnknownInductive(who.clone()));
        };
        let dom = (**domain).clone();
        let (id, var) = b.fresh_local(dom.clone());
        cur = body.instantiate(&var);
        out.push(OpenedLocal { id, var, ty: dom });
    }
    Ok((out, cur))
}

/// Open a constructor's FIELD binders (after instantiating its params with
/// `params`) as fresh builder locals.
fn open_ctor_fields(
    b: &mut EnvDeclBuilder,
    ctor_type: &Expr,
    params: &[Expr],
    who: &Name,
) -> Result<Vec<OpenedLocal>, EnvError> {
    let mut cur = ctor_type.clone();
    for p in params {
        let ExprKind::Pi(_, _, body) = &cur.kind else {
            return Err(EnvError::UnknownInductive(who.clone()));
        };
        cur = body.instantiate(p);
    }
    let mut out = Vec::new();
    while let ExprKind::Pi(_, domain, body) = &cur.kind {
        let dom = (**domain).clone();
        let (id, var) = b.fresh_local(dom.clone());
        cur = body.instantiate(&var);
        out.push(OpenedLocal { id, var, ty: dom });
    }
    Ok(out)
}

impl Environment {
    /// Collect the shared generation data for the heterogeneous builders.
    ///
    /// Fails (⇒ callers skip the twin pair, as for any generation failure) on:
    /// - indexed inductives (`InductiveCodomainNotSort` from the codomain
    ///   walk — the generator's scope is params-only, unchanged);
    /// - param types whose sort cannot be inferred (no fallback for PARAM
    ///   sorts: a guessed level would produce an ill-typed premise;
    ///   fail closed instead).
    fn hetero_info(
        &self,
        ind_name: &Name,
        decl: &InductiveDecl,
        ind_type: &InductiveType,
        fallback_level: Option<&Level>,
    ) -> Result<HeteroInfo, EnvError> {
        let num_params = decl.num_params;
        let n = num_params as usize;

        // Universe parameter for the result type — freshen to avoid collision.
        let result_univ_name = fresh_univ_name(&decl.level_params);
        let mut level_params = vec![result_univ_name.clone()];
        level_params.extend(decl.level_params.clone());

        // Param dependency flags: RAW (uninstantiated) walk, where `A_k`
        // still sees earlier params as BVar(0..k-1). (The instantiated walk
        // below replaces them with FVars, which would make every param look
        // independent.)
        let mut param_deps = Vec::with_capacity(n);
        {
            let mut cur = &ind_type.type_;
            for k in 0..n {
                let ExprKind::Pi(_, domain, body) = &cur.kind else {
                    return Err(EnvError::InductiveCodomainNotSort {
                        name: ind_name.clone(),
                        num_params,
                    });
                };
                param_deps.push(mentions_bound_below(domain, k, 0));
                cur = body;
            }
        }

        // Param sorts and the inductive's result sort — instantiated walk.
        let mut param_sorts = Vec::with_capacity(n);
        let mut ctx = LocalContext::new();
        let mut cur = ind_type.type_.clone();
        for _ in 0..n {
            let ExprKind::Pi(bi, domain, body) = &cur.kind else {
                return Err(EnvError::InductiveCodomainNotSort {
                    name: ind_name.clone(),
                    num_params,
                });
            };
            let tc = TypeChecker::with_context_and_mode(self, ctx.clone(), self.mode());
            let sort = tc
                .infer_sort(domain)
                .map_err(|e| EnvError::TypeCheckFailed {
                    name: ind_name.clone(),
                    source: e,
                })?;
            param_sorts.push(sort);
            let fvar_id = ctx.push(Name::anon(), (**domain).clone(), *bi);
            cur = body.instantiate(&Expr::fvar(fvar_id));
        }
        // Indexed inductives never reach a Sort here — the params-only scope
        // check and the result-sort extraction are the same walk.
        let ExprKind::Sort(ind_sort_level) = &cur.kind else {
            return Err(EnvError::InductiveCodomainNotSort {
                name: ind_name.clone(),
                num_params,
            });
        };
        let ind_sort_level = ind_sort_level.clone();

        // Per-ctor field data (primary type).
        let mut ctors = Vec::with_capacity(ind_type.constructors.len());
        for ctor in &ind_type.constructors {
            let sort_levels = if let Some(fb) = fallback_level {
                self.compute_ctor_field_sort_levels_with_fallback(
                    &ctor.type_,
                    num_params,
                    &ctor.name,
                    fb,
                )?
            } else {
                self.compute_ctor_field_sort_levels(&ctor.type_, num_params, &ctor.name)?
            };
            let field_tys = self.get_constructor_field_types(&ctor.type_, num_params);
            let uses_heq = field_tys
                .iter()
                .enumerate()
                .map(|(j, fty)| mentions_bound_below(fty, j + n, 0))
                .collect();
            ctors.push(HeteroCtor {
                type_: ctor.type_.clone(),
                sort_levels,
                uses_heq,
            });
        }

        let cases_on_name = Name::from_string(&format!("{ind_name}.casesOn"));
        Ok(HeteroInfo {
            result_univ_name,
            level_params,
            param_sorts,
            param_deps,
            ind_sort_level,
            cases_on_name,
            ctors,
        })
    }

    /// Build the v4.30 heterogeneous `T.noConfusionType` (type + value).
    /// See the module docs for the emitted shape. `num_params > 0` only.
    pub(super) fn build_no_confusion_type_hetero(
        &self,
        ind_name: &Name,
        decl: &InductiveDecl,
        fallback_level: Option<&Level>,
    ) -> Result<(Expr, Expr, Vec<Name>), EnvError> {
        require_heq(self)?;
        let ind_type = decl
            .types
            .iter()
            .find(|t| &t.name == ind_name)
            .ok_or_else(|| EnvError::UnknownInductive(ind_name.clone()))?;
        let info = self.hetero_info(ind_name, decl, ind_type, fallback_level)?;
        let n = decl.num_params as usize;
        debug_assert!(n > 0, "0-param types use the classic builder");

        let result_univ = Level::param(info.result_univ_name.clone());
        let sort_u = Expr::from_kind(ExprKind::Sort(result_univ.clone()));
        let ind_const = ind_const_with_levels(ind_name, &decl.level_params);

        let mut b = EnvDeclBuilder::new();
        // Binder layout (v4.30, P-first): P | p… | t | p'… | t'.
        let (p_id, p_var) = b.fresh_local(sort_u.clone());
        let (xs1, _) = open_binders(&mut b, &ind_type.type_, n, ind_name)?;
        let t_ty = Expr::apps(ind_const.clone(), xs1.iter().map(|l| l.var.clone()));
        let (t_id, t_var) = b.fresh_local(t_ty.clone());
        let (xs2, _) = open_binders(&mut b, &ind_type.type_, n, ind_name)?;
        let tp_ty = Expr::apps(ind_const.clone(), xs2.iter().map(|l| l.var.clone()));
        let (tp_id, tp_var) = b.fresh_local(tp_ty.clone());

        // --- TYPE ---
        // Sort u → {p…} → T p… → {p'…} → T p'… → Sort u
        let mut ty = sort_u.clone();
        ty = b.mk_pi(tp_id, BinderInfo::Default, tp_ty.clone(), ty);
        for l in xs2.iter().rev() {
            ty = b.mk_pi(l.id, BinderInfo::Implicit, l.ty.clone(), ty);
        }
        ty = b.mk_pi(t_id, BinderInfo::Default, t_ty.clone(), ty);
        for l in xs1.iter().rev() {
            ty = b.mk_pi(l.id, BinderInfo::Implicit, l.ty.clone(), ty);
        }
        ty = b.mk_pi(p_id, BinderInfo::Default, sort_u.clone(), ty);
        let no_conf_type_ty = b.finish(ty);

        // --- VALUE ---
        // fun P {p…} t {p'…} t' =>
        //   T.casesOn.{u+1, us} p… (fun _ : T p… => Sort u) t
        //     (fun a-fields => T.casesOn p'… (fun _ : T p'… => Sort u) t'
        //        (fun b-fields => <cell>) …) …
        // Diagonal cell = (eq₁ → … → e_k → P) → P with the mkEqHEq field rule;
        // off-diagonal = P. The registered recursor telescope supplies every
        // mutual/restored-companion motive and minor; unreachable premises get
        // exact-telescope `PUnit.{u}` padding. The outer casesOn runs at
        // unprimed params, the inner at primed params.
        let mut cases_levels: Vec<Level> = vec![Level::succ(result_univ.clone())];
        cases_levels.extend(decl.level_params.iter().map(|p| Level::param(p.clone())));
        let punit_u = Expr::const_(Name::from_string("PUnit"), vec![result_univ.clone()]);

        let xs1_vars: Vec<Expr> = xs1.iter().map(|l| l.var.clone()).collect();
        let xs2_vars: Vec<Expr> = xs2.iter().map(|l| l.var.clone()).collect();

        let mut own_outer_alts: Vec<Expr> = Vec::with_capacity(info.ctors.len());
        for (i, ctor_i) in info.ctors.iter().enumerate() {
            // a-side fields at UNPRIMED params.
            let fs1 = open_ctor_fields(&mut b, &ctor_i.type_, &xs1_vars, ind_name)?;

            // Inner casesOn on t' at PRIMED params.
            let mut own_inner_alts: Vec<Expr> = Vec::with_capacity(info.ctors.len());
            for (j, ctor_j) in info.ctors.iter().enumerate() {
                // b-side fields at PRIMED params.
                let fs2 = open_ctor_fields(&mut b, &ctor_j.type_, &xs2_vars, ind_name)?;
                let cell = if i == j {
                    // Diagonal: (e₁ → … → e_k → P) → P. a-side at unprimed
                    // params/fields, b-side at primed — the mkEqHEq rule.
                    let mut chain = p_var.clone();
                    for (f_idx, (fa, fb)) in fs1.iter().zip(fs2.iter()).enumerate().rev() {
                        let l = &ctor_i.sort_levels[f_idx];
                        if l.is_zero() {
                            continue; // Prop field — proof irrelevance
                        }
                        let e = if ctor_i.uses_heq[f_idx] {
                            heq_app(l, &fa.ty, &fa.var, &fb.ty, &fb.var)
                        } else {
                            eq_app(l, &fa.ty, &fa.var, &fb.var)
                        };
                        chain = Expr::pi(BinderInfo::Default, e, chain);
                    }
                    Expr::pi(BinderInfo::Default, chain, p_var.clone())
                } else {
                    p_var.clone()
                };
                let mut alt2 = cell;
                for f in fs2.iter().rev() {
                    alt2 = b.mk_lam(f.id, BinderInfo::Default, f.ty.clone(), alt2);
                }
                own_inner_alts.push(alt2);
            }

            let inner_motive = Expr::lam(BinderInfo::Default, tp_ty.clone(), sort_u.clone());
            let inner = self.apply_cases_on_with_restored_padding(
                decl,
                ind_name,
                &info.cases_on_name,
                &cases_levels,
                &xs2_vars,
                &inner_motive,
                &own_inner_alts,
                &tp_var,
                &sort_u,
                &punit_u,
            )?;

            let mut alt = inner;
            for f in fs1.iter().rev() {
                alt = b.mk_lam(f.id, BinderInfo::Default, f.ty.clone(), alt);
            }
            own_outer_alts.push(alt);
        }

        let outer_motive = Expr::lam(BinderInfo::Default, t_ty.clone(), sort_u.clone());
        let body = self.apply_cases_on_with_restored_padding(
            decl,
            ind_name,
            &info.cases_on_name,
            &cases_levels,
            &xs1_vars,
            &outer_motive,
            &own_outer_alts,
            &t_var,
            &sort_u,
            &punit_u,
        )?;

        let mut value = body;
        value = b.mk_lam(tp_id, BinderInfo::Default, tp_ty, value);
        for l in xs2.iter().rev() {
            value = b.mk_lam(l.id, BinderInfo::Implicit, l.ty.clone(), value);
        }
        value = b.mk_lam(t_id, BinderInfo::Default, t_ty, value);
        for l in xs1.iter().rev() {
            value = b.mk_lam(l.id, BinderInfo::Implicit, l.ty.clone(), value);
        }
        value = b.mk_lam(p_id, BinderInfo::Default, sort_u, value);
        let value = b.finish(value);

        Ok((no_conf_type_ty, value, info.level_params))
    }

    /// Build the v4.30 heterogeneous `T.noConfusion` (type + value).
    /// See the module docs for the emitted shape. `num_params > 0` only.
    pub(super) fn build_no_confusion_hetero(
        &self,
        ind_name: &Name,
        decl: &InductiveDecl,
        fallback_level: Option<&Level>,
    ) -> Result<(Expr, Expr, Vec<Name>), EnvError> {
        require_heq(self)?;
        let ind_type = decl
            .types
            .iter()
            .find(|t| &t.name == ind_name)
            .ok_or_else(|| EnvError::UnknownInductive(ind_name.clone()))?;
        let info = self.hetero_info(ind_name, decl, ind_type, fallback_level)?;
        let n = decl.num_params as usize;
        debug_assert!(n > 0, "0-param types use the classic builder");

        let result_univ = Level::param(info.result_univ_name.clone());
        let sort_u = Expr::from_kind(ExprKind::Sort(result_univ.clone()));
        let ind_const = ind_const_with_levels(ind_name, &decl.level_params);
        let mut nct_levels = vec![result_univ.clone()];
        nct_levels.extend(decl.level_params.iter().map(|p| Level::param(p.clone())));
        let nct_const = Expr::const_(
            Name::from_string(&format!("{ind_name}.noConfusionType")),
            nct_levels,
        );

        let mut b = EnvDeclBuilder::new();
        // Binder layout: {P} {p…} {t} {p'…} {t'} (h₁)…(hₙ) (h_t).
        let (p_id, p_var) = b.fresh_local(sort_u.clone());
        let (xs1, _) = open_binders(&mut b, &ind_type.type_, n, ind_name)?;
        let t_ty = Expr::apps(ind_const.clone(), xs1.iter().map(|l| l.var.clone()));
        let (t_id, t_var) = b.fresh_local(t_ty.clone());
        let (xs2, _) = open_binders(&mut b, &ind_type.type_, n, ind_name)?;
        let tp_ty = Expr::apps(ind_const.clone(), xs2.iter().map(|l| l.var.clone()));
        let (tp_id, tp_var) = b.fresh_local(tp_ty.clone());

        // Param premises: `Eq A_k p_k p_k'` for independent params,
        // `HEq (A_k at p) p_k (A_k at p') p_k'` for dependent ones.
        let mut hs: Vec<OpenedLocal> = Vec::with_capacity(n);
        for k in 0..n {
            let hty = if info.param_deps[k] {
                heq_app(
                    &info.param_sorts[k],
                    &xs1[k].ty,
                    &xs1[k].var,
                    &xs2[k].ty,
                    &xs2[k].var,
                )
            } else {
                eq_app(&info.param_sorts[k], &xs1[k].ty, &xs1[k].var, &xs2[k].var)
            };
            let (id, var) = b.fresh_local(hty.clone());
            hs.push(OpenedLocal { id, var, ty: hty });
        }
        // Major premise: `t ≍ t'` (heterogeneous — `t : T p…`, `t' : T p'…`).
        let ht_ty = heq_app(&info.ind_sort_level, &t_ty, &t_var, &tp_ty, &tp_var);
        let (ht_id, ht_var) = b.fresh_local(ht_ty.clone());

        let mut result = nct_const.clone();
        result = Expr::app(result, p_var.clone());
        for l in &xs1 {
            result = Expr::app(result, l.var.clone());
        }
        result = Expr::app(result, t_var.clone());
        for l in &xs2 {
            result = Expr::app(result, l.var.clone());
        }
        result = Expr::app(result, tp_var.clone());

        // --- TYPE ---
        let mut ty = result;
        ty = b.mk_pi(ht_id, BinderInfo::Default, ht_ty.clone(), ty);
        for h in hs.iter().rev() {
            ty = b.mk_pi(h.id, BinderInfo::Default, h.ty.clone(), ty);
        }
        ty = b.mk_pi(tp_id, BinderInfo::Implicit, tp_ty.clone(), ty);
        for l in xs2.iter().rev() {
            ty = b.mk_pi(l.id, BinderInfo::Implicit, l.ty.clone(), ty);
        }
        ty = b.mk_pi(t_id, BinderInfo::Implicit, t_ty.clone(), ty);
        for l in xs1.iter().rev() {
            ty = b.mk_pi(l.id, BinderInfo::Implicit, l.ty.clone(), ty);
        }
        ty = b.mk_pi(p_id, BinderInfo::Implicit, sort_u.clone(), ty);
        let no_conf_ty = b.finish(ty);

        // --- VALUE ---
        let cx = HeteroNcCx {
            env: self,
            decl,
            ind_name,
            info: &info,
            us: &decl.level_params,
            p_var: &p_var,
            xs1: &xs1,
            t_var: &t_var,
            t_ty: &t_ty,
            nct_const: &nct_const,
        };
        let group = EqTelescopeGroup {
            primed: xs2.clone(),
            tp: OpenedLocal {
                id: tp_id,
                var: tp_var,
                ty: tp_ty.clone(),
            },
            hs: hs.clone(),
            ht: OpenedLocal {
                id: ht_id,
                var: ht_var,
                ty: ht_ty.clone(),
            },
        };
        let body = Self::hetero_noconf_telescope(&mut b, &cx, 0, group)?;

        let mut value = body;
        value = b.mk_lam(ht_id, BinderInfo::Default, ht_ty, value);
        for h in hs.iter().rev() {
            value = b.mk_lam(h.id, BinderInfo::Default, h.ty.clone(), value);
        }
        value = b.mk_lam(tp_id, BinderInfo::Implicit, tp_ty, value);
        for l in xs2.iter().rev() {
            value = b.mk_lam(l.id, BinderInfo::Implicit, l.ty.clone(), value);
        }
        value = b.mk_lam(t_id, BinderInfo::Implicit, t_ty, value);
        for l in xs1.iter().rev() {
            value = b.mk_lam(l.id, BinderInfo::Implicit, l.ty.clone(), value);
        }
        value = b.mk_lam(p_id, BinderInfo::Implicit, sort_u, value);
        let value = b.finish(value);

        Ok((no_conf_ty, value, info.level_params))
    }

    /// One step of the `Eq.ndrec` telescope (design §3): at step `i < n`,
    /// eliminate the param-`i` equality, re-generalizing the remaining primed
    /// group; at step `n`, transport the diagonal `casesOn` core along
    /// `eq_of_heq h_t`.
    fn hetero_noconf_telescope(
        b: &mut EnvDeclBuilder,
        cx: &HeteroNcCx<'_>,
        i: usize,
        group: EqTelescopeGroup,
    ) -> Result<Expr, EnvError> {
        let info = cx.info;
        let n = info.param_sorts.len();
        let result_univ = Level::param(info.result_univ_name.clone());

        if i == n {
            // Major step:
            //   @Eq.ndrec.{u, ℓ} (T p…) t (fun y => NCT P p… t p… y)
            //     <diagonal casesOn core> t' (eq_of_heq h_t)
            let motive = {
                let (y_id, y_var) = b.fresh_local(cx.t_ty.clone());
                let mut cod = cx.nct_const.clone();
                cod = Expr::app(cod, cx.p_var.clone());
                for l in cx.xs1 {
                    cod = Expr::app(cod, l.var.clone());
                }
                cod = Expr::app(cod, cx.t_var.clone());
                for l in cx.xs1 {
                    cod = Expr::app(cod, l.var.clone());
                }
                cod = Expr::app(cod, y_var);
                b.mk_lam(y_id, BinderInfo::Default, cx.t_ty.clone(), cod)
            };
            let core = Self::hetero_diagonal_core(b, cx)?;
            // At this point every earlier param equality has been substituted,
            // so h_t is a HOMOGENEOUS HEq over `T p…` — eq_of_heq applies.
            let proof = eq_of_heq_app(
                &info.ind_sort_level,
                cx.t_ty,
                cx.t_var,
                &group.tp.var,
                &group.ht.var,
            );
            let ndrec = Expr::const_(
                Name::from_string("Eq.ndrec"),
                vec![result_univ, info.ind_sort_level.clone()],
            );
            return Ok(Expr::apps(
                ndrec,
                [
                    cx.t_ty.clone(),
                    cx.t_var.clone(),
                    motive,
                    core,
                    group.tp.var.clone(),
                    proof,
                ],
            ));
        }

        let s_i = &info.param_sorts[i];
        let a_dom = cx.xs1[i].ty.clone();
        let pp0 = group.primed[0].clone();
        let h0 = group.hs[0].clone();
        // For a dependent param the hypothesis has been rebound to a
        // homogeneous HEq (earlier params already substituted) — convert with
        // eq_of_heq, as in the printed Sigma.noConfusion.
        let proof = if info.param_deps[i] {
            eq_of_heq_app(s_i, &a_dom, &cx.xs1[i].var, &pp0.var, &h0.var)
        } else {
            h0.var.clone()
        };

        // Motive: fun x : A_i => Π <rebound group [p'_i := x]>. NCT P p… t
        //   (p_{<i}, x, p'_{>i}) t'
        let (x_id, x_var) = b.fresh_local(a_dom.clone());
        let m_group = Self::rebind_group(b, &group, &pp0, &x_var);
        let motive = {
            let mut cod = cx.nct_const.clone();
            cod = Expr::app(cod, cx.p_var.clone());
            for l in cx.xs1 {
                cod = Expr::app(cod, l.var.clone());
            }
            cod = Expr::app(cod, cx.t_var.clone());
            for l in cx.xs1.iter().take(i) {
                cod = Expr::app(cod, l.var.clone());
            }
            cod = Expr::app(cod, x_var.clone());
            for p in &m_group.primed {
                cod = Expr::app(cod, p.var.clone());
            }
            cod = Expr::app(cod, m_group.tp.var.clone());
            let mut mo = cod;
            mo = b.mk_pi(
                m_group.ht.id,
                BinderInfo::Default,
                m_group.ht.ty.clone(),
                mo,
            );
            for h in m_group.hs.iter().rev() {
                mo = b.mk_pi(h.id, BinderInfo::Default, h.ty.clone(), mo);
            }
            mo = b.mk_pi(
                m_group.tp.id,
                BinderInfo::Implicit,
                m_group.tp.ty.clone(),
                mo,
            );
            for p in m_group.primed.iter().rev() {
                mo = b.mk_pi(p.id, BinderInfo::Implicit, p.ty.clone(), mo);
            }
            b.mk_lam(x_id, BinderInfo::Default, a_dom.clone(), mo)
        };

        // Motive universe: the sort of the rebound-group Pi telescope, folded
        // exactly the way the type checker computes Pi sorts (innermost-out
        // `Level::imax`), so the levels agree syntactically.
        let mut u2 = result_univ;
        u2 = Level::imax(Level::zero(), u2); // h_t : Prop
        for _ in (i + 1)..n {
            u2 = Level::imax(Level::zero(), u2); // h_j : Prop
        }
        u2 = Level::imax(info.ind_sort_level.clone(), u2); // t' : Sort ℓ
        for j in ((i + 1)..n).rev() {
            u2 = Level::imax(info.param_sorts[j].clone(), u2); // p'_j : Sort s_j
        }

        // Base: fun <rebound group [p'_i := p_i]> => <step i+1>
        let b_group = Self::rebind_group(b, &group, &pp0, &cx.xs1[i].var);
        let inner = Self::hetero_noconf_telescope(b, cx, i + 1, b_group.clone())?;
        let base = {
            let mut e = inner;
            e = b.mk_lam(b_group.ht.id, BinderInfo::Default, b_group.ht.ty.clone(), e);
            for h in b_group.hs.iter().rev() {
                e = b.mk_lam(h.id, BinderInfo::Default, h.ty.clone(), e);
            }
            e = b.mk_lam(
                b_group.tp.id,
                BinderInfo::Implicit,
                b_group.tp.ty.clone(),
                e,
            );
            for p in b_group.primed.iter().rev() {
                e = b.mk_lam(p.id, BinderInfo::Implicit, p.ty.clone(), e);
            }
            e
        };

        let ndrec = Expr::const_(Name::from_string("Eq.ndrec"), vec![u2, s_i.clone()]);
        let mut e = Expr::apps(
            ndrec,
            [
                a_dom,
                cx.xs1[i].var.clone(),
                motive,
                base,
                pp0.var.clone(),
                proof,
            ],
        );
        for p in &group.primed[1..] {
            e = Expr::app(e, p.var.clone());
        }
        e = Expr::app(e, group.tp.var.clone());
        for h in &group.hs[1..] {
            e = Expr::app(e, h.var.clone());
        }
        e = Expr::app(e, group.ht.var.clone());
        Ok(e)
    }

    /// Rebind the tail of the telescope group (`primed[1..]`, `t'`,
    /// `hs[1..]`, `h_t`) with `replaced` (the group's head primed param)
    /// substituted by `replacement`, threading the substitution through the
    /// freshly created locals.
    fn rebind_group(
        b: &mut EnvDeclBuilder,
        group: &EqTelescopeGroup,
        replaced: &OpenedLocal,
        replacement: &Expr,
    ) -> EqTelescopeGroup {
        let mut subst: Vec<(FVarId, Expr)> = vec![(replaced.id, replacement.clone())];
        let apply = |ty: &Expr, subst: &[(FVarId, Expr)]| -> Expr {
            let mut r = ty.clone();
            for (id, rep) in subst {
                r = r.abstract_fvar(*id).instantiate(rep);
            }
            r
        };

        let mut primed = Vec::with_capacity(group.primed.len().saturating_sub(1));
        for p in &group.primed[1..] {
            let ty = apply(&p.ty, &subst);
            let (id, var) = b.fresh_local(ty.clone());
            subst.push((p.id, var.clone()));
            primed.push(OpenedLocal { id, var, ty });
        }
        let tp = {
            let ty = apply(&group.tp.ty, &subst);
            let (id, var) = b.fresh_local(ty.clone());
            subst.push((group.tp.id, var.clone()));
            OpenedLocal { id, var, ty }
        };
        let mut hs = Vec::with_capacity(group.hs.len().saturating_sub(1));
        for h in &group.hs[1..] {
            let ty = apply(&h.ty, &subst);
            let (id, var) = b.fresh_local(ty.clone());
            subst.push((h.id, var.clone()));
            hs.push(OpenedLocal { id, var, ty });
        }
        let ht = {
            let ty = apply(&group.ht.ty, &subst);
            let (id, var) = b.fresh_local(ty.clone());
            OpenedLocal { id, var, ty }
        };
        EqTelescopeGroup { primed, tp, hs, ht }
    }

    /// The diagonal `casesOn` core:
    ///   `T.casesOn.{u, us} p… (fun x => NCT P p… x p… x) t
    ///      (fun f… k => k (·.refl f₁) …) …`
    /// with `Eq.refl`/`HEq.refl` matching the diagonal chain's Eq/HEq choices
    /// (both sides at UNPRIMED params — homogeneous on the diagonal).
    fn hetero_diagonal_core(b: &mut EnvDeclBuilder, cx: &HeteroNcCx<'_>) -> Result<Expr, EnvError> {
        let info = cx.info;
        let result_univ = Level::param(info.result_univ_name.clone());
        let mut cases_levels = vec![result_univ.clone()];
        cases_levels.extend(cx.us.iter().map(|p| Level::param(p.clone())));
        let cmotive = {
            let (x_id, x_var) = b.fresh_local(cx.t_ty.clone());
            let mut cod = cx.nct_const.clone();
            cod = Expr::app(cod, cx.p_var.clone());
            for l in cx.xs1 {
                cod = Expr::app(cod, l.var.clone());
            }
            cod = Expr::app(cod, x_var.clone());
            for l in cx.xs1 {
                cod = Expr::app(cod, l.var.clone());
            }
            cod = Expr::app(cod, x_var);
            b.mk_lam(x_id, BinderInfo::Default, cx.t_ty.clone(), cod)
        };
        let xs1_vars: Vec<Expr> = cx.xs1.iter().map(|l| l.var.clone()).collect();
        let mut minors = Vec::with_capacity(info.ctors.len());
        for c in &info.ctors {
            let fs = open_ctor_fields(b, &c.type_, &xs1_vars, &info.cases_on_name)?;
            let minor = if fs.is_empty() {
                // fun (k : P) => k
                let (kk_id, kk_var) = b.fresh_local(cx.p_var.clone());
                b.mk_lam(kk_id, BinderInfo::Default, cx.p_var.clone(), kk_var)
            } else {
                let mut chain = cx.p_var.clone();
                for (j, f) in fs.iter().enumerate().rev() {
                    let l = &c.sort_levels[j];
                    if l.is_zero() {
                        continue;
                    }
                    let eqx = if c.uses_heq[j] {
                        heq_app(l, &f.ty, &f.var, &f.ty, &f.var)
                    } else {
                        eq_app(l, &f.ty, &f.var, &f.var)
                    };
                    chain = Expr::pi(BinderInfo::Default, eqx, chain);
                }
                let (kk_id, kk_var) = b.fresh_local(chain.clone());
                let mut body = kk_var;
                for (j, f) in fs.iter().enumerate() {
                    let l = &c.sort_levels[j];
                    if l.is_zero() {
                        continue;
                    }
                    let refl = if c.uses_heq[j] {
                        Expr::apps(
                            Expr::const_(Name::from_string("HEq.refl"), vec![l.clone()]),
                            [f.ty.clone(), f.var.clone()],
                        )
                    } else {
                        Expr::apps(
                            Expr::const_(Name::from_string("Eq.refl"), vec![l.clone()]),
                            [f.ty.clone(), f.var.clone()],
                        )
                    };
                    body = Expr::app(body, refl);
                }
                let mut m = b.mk_lam(kk_id, BinderInfo::Default, chain, body);
                for f in fs.iter().rev() {
                    m = b.mk_lam(f.id, BinderInfo::Default, f.ty.clone(), m);
                }
                m
            };
            minors.push(minor);
        }

        let punit_u = Expr::const_(Name::from_string("PUnit"), vec![result_univ.clone()]);
        let punit_unit_u = Expr::const_(Name::from_string("PUnit.unit"), vec![result_univ]);
        let params: Vec<Expr> = cx.xs1.iter().map(|l| l.var.clone()).collect();
        cx.env.apply_cases_on_with_restored_padding(
            cx.decl,
            cx.ind_name,
            &info.cases_on_name,
            &cases_levels,
            &params,
            &cmotive,
            &minors,
            cx.t_var,
            &punit_u,
            &punit_unit_u,
        )
    }
}
