// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Target-row analysis for the `coinductive` lowering (Brick 3 of
//! `designs/2026-08-25-rank1-full-gfp-lowering.md`): classify each target
//! position of a constructor's conclusion `P a₁ … aₙ` as either an
//! index-SUBSTITUTED variable (the position becomes the shared index binder
//! itself — no equation, the v1 minimization) or an index EQUATION
//! `aᵢ = vᵢ` (written target on the LEFT, the pinned orientation). The
//! α-rename helper [`rename_free`] also lives here. See the parent module
//! for the full envelope.

use super::{
    known_constant, mentions, strip_parens, unsupported, variant_label, ElabError, Environment,
};
use clean_parser::{SurfaceArg, SurfaceBinder, SurfaceExpr};

/// The classification of one target position of a constructor's conclusion.
pub(super) enum TargetPos {
    /// A bare variable that becomes the shared index binder for this
    /// position: the FIRST bare occurrence of a fresh variable, or the only
    /// bare occurrence of a declared binder whose declared type is beyond
    /// doubt the index type (see [`classify_target`]). No equation is
    /// minted — the v1/Brick-1 byte-stability minimization.
    Subst { var: String },
    /// Every other position: the disjunct carries the index equation
    /// `written = vᵢ` (written target on the LEFT — the pinned
    /// orientation), and the intro theorem closes it with
    /// `Eq.refl written` at the instantiated target.
    Equate { written: SurfaceExpr },
}

/// Does `expr` contain a hole (`_` / `?name`) anywhere this module can see?
/// A hole in a target argument would elaborate to an arbitrarily-solved
/// metavariable inside the generated functor, silently changing what the
/// declaration means — refused. Surface forms outside the applicative
/// fragment return `false` here; the free-identifier sweep refuses them
/// separately, so nothing containing them is ever lowered.
fn contains_hole(expr: &SurfaceExpr) -> bool {
    match expr {
        SurfaceExpr::Hole(..) | SurfaceExpr::NamedHole(..) => true,
        SurfaceExpr::App(_, h, args) => {
            contains_hole(h) || args.iter().any(|a| contains_hole(&a.expr))
        }
        SurfaceExpr::Arrow(_, a, b) => contains_hole(a) || contains_hole(b),
        SurfaceExpr::Lambda(_, bs, body) | SurfaceExpr::Pi(_, bs, body) => {
            bs.iter()
                .any(|b| b.ty.as_deref().is_some_and(contains_hole))
                || contains_hole(body)
        }
        SurfaceExpr::Paren(_, e)
        | SurfaceExpr::Explicit(_, e)
        | SurfaceExpr::OutParam(_, e)
        | SurfaceExpr::SemiOutParam(_, e)
        | SurfaceExpr::Proj(_, e, _)
        | SurfaceExpr::NamedArg(_, _, e)
        | SurfaceExpr::UniverseInst(_, e, _) => contains_hole(e),
        SurfaceExpr::Ascription(_, e, t) => contains_hole(e) || contains_hole(t),
        _ => false,
    }
}

/// Span-insensitive structural equality over the applicative surface
/// fragment. Used ONLY to decide whether a declared binder's type is beyond
/// doubt the index type (the substitution minimization); a `false` answer
/// degrades to the general ∃-plus-equation form, which is sound for every
/// shape, so conservative `false` on anything unrecognized is safe.
fn surface_eq(a: &SurfaceExpr, b: &SurfaceExpr) -> bool {
    match (strip_parens(a), strip_parens(b)) {
        (SurfaceExpr::Ident(_, x), SurfaceExpr::Ident(_, y)) => x == y,
        (SurfaceExpr::Lit(_, x), SurfaceExpr::Lit(_, y)) => x == y,
        (SurfaceExpr::App(_, hx, xs), SurfaceExpr::App(_, hy, ys)) => {
            surface_eq(hx, hy)
                && xs.len() == ys.len()
                && xs
                    .iter()
                    .zip(ys)
                    .all(|(x, y)| x.name == y.name && surface_eq(&x.expr, &y.expr))
        }
        (SurfaceExpr::Arrow(_, ax, bx), SurfaceExpr::Arrow(_, ay, by)) => {
            surface_eq(ax, ay) && surface_eq(bx, by)
        }
        _ => false,
    }
}

/// Classify every target position of constructor `ctor_name`'s conclusion.
///
/// `target` must be the fully-applied `short p⃗ a₁ … a_arity` conclusion —
/// the declaration-parameter row first, EXACTLY as declared
/// ([`super::params::check_param_row`]; a varied parameter position, or a
/// bare parameter name in an INDEX position, refuses by name) — then each
/// index position becomes [`TargetPos::Subst`] or [`TargetPos::Equate`]
/// under the documented rules:
///
/// * a bare FRESH variable (not a declared binder, not a registered
///   constant, not the predicate) substitutes at its FIRST bare occurrence
///   and equates at every later one (`P x x` is admitted: `x` binds the
///   first index, the second carries `x = v₂`);
/// * a bare DECLARED BINDER substitutes when it is the constructor's only
///   bare occurrence of that binder AND its declared type is structurally
///   the index type with constant-only free names (beyond doubt the same
///   type in every context); otherwise it stays ∃-bound and the position
///   equates — sound either way, so no refusal rides on this boundary;
/// * a bare REGISTERED CONSTANT refuses: v1 read such a name as a fresh
///   index variable shadowing the constant, and the constant reading is
///   what `inductive` means — rather than silently pick either, the
///   ambiguity is refused (write `(c : T)` to force the constant reading);
/// * anything else (literals, applications, ascriptions, …) equates,
///   provided it is hole-free and does not mention the predicate.
pub(super) fn classify_target(
    target: &SurfaceExpr,
    short: &str,
    arity: usize,
    ctor_name: &str,
    what: &str,
    binders: &[SurfaceBinder],
    idx_tys: &[&SurfaceExpr],
    params: &[String],
    env: &Environment,
) -> Result<Vec<TargetPos>, ElabError> {
    let shape_err = || {
        let spelled = if params.is_empty() {
            format!("`{short} a₁ … a{arity}` with exactly {arity} positional target argument(s)")
        } else {
            format!(
                "`{short} {} a₁ … a{arity}` — the declaration-parameter row \
                 exactly as declared, then exactly {arity} positional target \
                 argument(s)",
                params.join(" ")
            )
        };
        unsupported(format!(
            "{what}: constructor `{ctor_name}` must conclude in {spelled} — arbitrary \
             applicative terms over declared binders and registered constants are \
             allowed as index arguments, but the head and arity must be the declared \
             predicate's"
        ))
    };
    let SurfaceExpr::App(_, head, all_args) = strip_parens(target) else {
        return Err(shape_err());
    };
    if !matches!(strip_parens(head), SurfaceExpr::Ident(_, id) if id == short) {
        return Err(shape_err());
    }
    if all_args.len() != params.len() + arity
        || all_args.iter().any(|a: &SurfaceArg| a.name.is_some())
    {
        return Err(shape_err());
    }
    // The declaration-parameter row must be applied first, EXACTLY as
    // declared (the mirror of the kernel's strict inductive check 3): a
    // constructor "varying" a parameter position is declaring an INDEX and
    // refuses by name.
    super::params::check_param_row(all_args, params, short)
        .map_err(|reason| unsupported(format!("{what}: constructor `{ctor_name}`: {reason}")))?;
    let args = &all_args[params.len()..];

    // Bare-position occurrence counts drive the substitution/equation split.
    let bare_name = |a: &SurfaceArg| match strip_parens(&a.expr) {
        SurfaceExpr::Ident(_, id) => Some(id.clone()),
        _ => None,
    };
    let bares: Vec<Option<String>> = args.iter().map(bare_name).collect();

    let mut positions = Vec::with_capacity(arity);
    for (i, arg) in args.iter().enumerate() {
        let arg = strip_parens(&arg.expr);
        if contains_hole(arg) {
            return Err(unsupported(format!(
                "{what}: a target argument of constructor `{ctor_name}` contains a \
                 hole `_`; every index the constructor concludes at must be written \
                 out — a hole would elaborate to an arbitrarily-solved metavariable \
                 inside the generated one-step functor"
            )));
        }
        {
            let mut bound: Vec<&str> = Vec::new();
            let mut fvs: Vec<&str> = Vec::new();
            super::all_idents(arg, &mut bound, &mut fvs).map_err(|label| {
                unsupported(format!(
                    "{what}: a target argument of constructor `{ctor_name}` uses \
                     the non-applicative surface form `{label}`; target arguments \
                     must be built from identifiers, applications, arrows and \
                     binders"
                ))
            })?;
        }
        if mentions(arg, short) {
            return Err(unsupported(format!(
                "{what}: a target argument of constructor `{ctor_name}` mentions \
                 `{short}` — a nested occurrence of the predicate in its own index \
                 is refused"
            )));
        }
        let Some(id) = &bares[i] else {
            positions.push(TargetPos::Equate {
                written: arg.clone(),
            });
            continue;
        };
        if id.contains("_coind") {
            return Err(unsupported(format!(
                "{what}: constructor `{ctor_name}` uses the target variable `{id}`, \
                 which carries the `_coind` marker reserved for generated binder \
                 names — it could be captured inside the generated proofs"
            )));
        }
        if params.iter().any(|p| p == id) {
            return Err(unsupported(format!(
                "{what}: target argument {} of constructor `{ctor_name}` is the bare \
                 declaration parameter `{id}` in an INDEX position — ambiguous \
                 between a fresh index variable (which would shadow the parameter) \
                 and the parameter's value; write it ascribed (`({id} : T)`) to \
                 equate the index to the parameter, or rename the variable",
                i + 1
            )));
        }
        let first_bare = bares[..i].iter().flatten().all(|b| b != id);
        if let Some(b) = binders.iter().find(|b| b.name == *id) {
            let once_bare = first_bare && bares[i + 1..].iter().flatten().all(|b| b != id);
            let ty_is_index = b
                .ty
                .as_deref()
                .is_some_and(|ty| surface_eq(ty, idx_tys[i]) && type_fvs_all_constants(ty, env));
            positions.push(if once_bare && ty_is_index {
                TargetPos::Subst { var: id.clone() }
            } else {
                TargetPos::Equate {
                    written: arg.clone(),
                }
            });
        } else if known_constant(env, id) {
            return Err(unsupported(format!(
                "{what}: target argument {} of constructor `{ctor_name}` is the bare \
                 identifier `{id}`, which is a registered constant — ambiguous between \
                 a fresh index variable (which would shadow it) and the constant \
                 itself; write the constant reading with an ascription `({id} : T)` \
                 or rename the variable",
                i + 1
            )));
        } else {
            positions.push(if first_bare {
                TargetPos::Subst { var: id.clone() }
            } else {
                TargetPos::Equate {
                    written: arg.clone(),
                }
            });
        }
    }

    // Every free variable of an EQUATED target argument must be an
    // index-substituted variable of this target, a declared binder, or a
    // registered constant — the same auto-bind hazard as premises, at the
    // index position. This is where a compound target over an UNDECLARED
    // variable (`Bad (stl s) t` with no `(s : Str)` binder) refuses: a
    // fresh variable is only bindable by substituting at a bare position.
    let subst_names: Vec<&str> = positions
        .iter()
        .filter_map(|p| match p {
            TargetPos::Subst { var } => Some(var.as_str()),
            TargetPos::Equate { .. } => None,
        })
        .collect();
    for pos in &positions {
        let TargetPos::Equate { written } = pos else {
            continue;
        };
        let mut bound: Vec<&str> = Vec::new();
        let mut fvs: Vec<&str> = Vec::new();
        // Vetted applicative above; an error here is unreachable.
        let _ = super::all_idents(written, &mut bound, &mut fvs);
        for fv in fvs {
            if subst_names.contains(&fv)
                || binders.iter().any(|b| b.name == fv)
                || params.iter().any(|p| p == fv)
                || known_constant(env, fv)
            {
                continue;
            }
            return Err(unsupported(format!(
                "{what}: a target argument of constructor `{ctor_name}` mentions \
                 `{fv}`, which is neither an index-substituted target variable, a \
                 declared binder of this constructor, nor a known constant; \
                 refusing to auto-bind it into the generated one-step functor — \
                 declare it as a constructor binder to ∃-bind it"
            )));
        }
    }
    Ok(positions)
}

/// Are all free identifiers of `ty` registered constants? Required for the
/// declared-binder substitution minimization: a binder type mentioning a
/// constructor-local name could change meaning under the shared index row.
fn type_fvs_all_constants(ty: &SurfaceExpr, env: &Environment) -> bool {
    let mut bound: Vec<&str> = Vec::new();
    let mut fvs: Vec<&str> = Vec::new();
    if super::all_idents(ty, &mut bound, &mut fvs).is_err() {
        return false;
    }
    fvs.iter().all(|fv| known_constant(env, fv))
}

/// Simultaneously rename the FREE identifiers of `expr` (`map` is source →
/// destination; the sources are one constructor's index-substituted target
/// variables and the destinations the shared index row, so each side is
/// pairwise distinct).
///
/// Capture-honoring and FAIL-CLOSED: any shape whose meaning under the
/// rename is not beyond doubt returns `Err` naming the offense, which the
/// caller turns into a loud [`ElabError::Unsupported`]. Refused shapes:
///
/// * an inner binder named after a rename source or destination — the
///   premise SHADOWS a variable being renamed; refusing errs toward
///   rejection instead of attempting scope-split treatment (v1 tolerated
///   such shadowing, but only under the identity rename, which still runs
///   rename-free — see `validate`);
/// * a free occurrence of a destination name that is not itself a source —
///   there it denotes a constant (`validate` has already vetted every free
///   name), and the shared index binder would CAPTURE it;
/// * a binder carrying a default value, and every surface form outside the
///   applicative fragment `all_idents` accepts.
pub(super) fn rename_free(
    expr: &SurfaceExpr,
    map: &[(String, String)],
) -> Result<SurfaceExpr, String> {
    let sub = |e: &SurfaceExpr| rename_free(e, map);
    match expr {
        SurfaceExpr::Ident(sp, id) => {
            if let Some((_, dst)) = map.iter().find(|(src, _)| src == id) {
                return Ok(SurfaceExpr::Ident(*sp, dst.clone()));
            }
            if map.iter().any(|(_, dst)| dst == id) {
                return Err(format!(
                    "it mentions `{id}`, which is not one of this constructor's \
                     target variables but IS a shared index-row name — under the \
                     shared binder row that occurrence would be captured"
                ));
            }
            Ok(expr.clone())
        }
        SurfaceExpr::Lit(..) | SurfaceExpr::Universe(..) | SurfaceExpr::Hole(..) => {
            Ok(expr.clone())
        }
        SurfaceExpr::App(sp, h, args) => {
            let new_args = args
                .iter()
                .map(|a| {
                    Ok(SurfaceArg {
                        span: a.span,
                        expr: sub(&a.expr)?,
                        name: a.name.clone(),
                    })
                })
                .collect::<Result<Vec<_>, String>>()?;
            Ok(SurfaceExpr::App(*sp, Box::new(sub(h)?), new_args))
        }
        SurfaceExpr::Arrow(sp, a, b) => Ok(SurfaceExpr::Arrow(
            *sp,
            Box::new(sub(a)?),
            Box::new(sub(b)?),
        )),
        SurfaceExpr::Lambda(sp, bs, body) | SurfaceExpr::Pi(sp, bs, body) => {
            let mut new_bs = Vec::with_capacity(bs.len());
            for b in bs {
                if map
                    .iter()
                    .any(|(src, dst)| *src == b.name || *dst == b.name)
                {
                    return Err(format!(
                        "it binds `{}`, shadowing a variable of the α-rename onto \
                         the shared index row",
                        b.name
                    ));
                }
                if b.default.is_some() {
                    return Err(format!(
                        "its binder `{}` carries a default value, which this \
                         rename does not analyse",
                        b.name
                    ));
                }
                new_bs.push(SurfaceBinder {
                    span: b.span,
                    name: b.name.clone(),
                    ty: match &b.ty {
                        Some(t) => Some(Box::new(sub(t)?)),
                        None => None,
                    },
                    default: None,
                    info: b.info,
                });
            }
            let new_body = Box::new(sub(body)?);
            Ok(if matches!(expr, SurfaceExpr::Lambda(..)) {
                SurfaceExpr::Lambda(*sp, new_bs, new_body)
            } else {
                SurfaceExpr::Pi(*sp, new_bs, new_body)
            })
        }
        SurfaceExpr::Paren(sp, e) => Ok(SurfaceExpr::Paren(*sp, Box::new(sub(e)?))),
        SurfaceExpr::Explicit(sp, e) => Ok(SurfaceExpr::Explicit(*sp, Box::new(sub(e)?))),
        SurfaceExpr::OutParam(sp, e) => Ok(SurfaceExpr::OutParam(*sp, Box::new(sub(e)?))),
        SurfaceExpr::SemiOutParam(sp, e) => Ok(SurfaceExpr::SemiOutParam(*sp, Box::new(sub(e)?))),
        SurfaceExpr::Proj(sp, e, p) => Ok(SurfaceExpr::Proj(*sp, Box::new(sub(e)?), p.clone())),
        SurfaceExpr::NamedArg(sp, n, e) => {
            Ok(SurfaceExpr::NamedArg(*sp, n.clone(), Box::new(sub(e)?)))
        }
        SurfaceExpr::UniverseInst(sp, e, us) => Ok(SurfaceExpr::UniverseInst(
            *sp,
            Box::new(sub(e)?),
            us.clone(),
        )),
        SurfaceExpr::Ascription(sp, e, t) => Ok(SurfaceExpr::Ascription(
            *sp,
            Box::new(sub(e)?),
            Box::new(sub(t)?),
        )),
        other => Err(format!(
            "it uses the non-applicative surface form `{}`",
            variant_label(other)
        )),
    }
}
