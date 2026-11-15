// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! VARIANT codata — brick VC-1 of
//! `designs/2026-08-28-variant-codata-surface.md`.
//!
//! ```text
//! codata ITr (E : Type) (R : Type) (Ans : E → Type) where
//!   | Ret : R → ITr E R Ans
//!   | Tau : ITr E R Ans → ITr E R Ans
//!   | Vis : (e : E) → (Ans e → ITr E R Ans) → ITr E R Ans
//! ```
//!
//! The rank-1 `codata` command is a RECORD envelope — observation fields
//! plus a trailing block of recursive fields — so its position family is
//! constant in the shape (`codata_cmd.rs:763` passes `fun _ _ => …`). A
//! variant's positions DEPEND on which constructor was chosen, which is
//! why rank 9's ITree carrier is hand-expanded
//! (`data/graduation/clean-mtype/proof/ITreeEco.lean:754-855`) instead of
//! declared. This module is the lane that closes that seam.
//!
//! **This module decides what is ALLOWED.** Every envelope violation gets
//! its own named [`ElabError::Unsupported`] (VC-1), and the telescope of
//! each surviving constructor is classified into [`CtorArg`]s. What it
//! BECOMES is [`crate::codata_variant_plan`] (VC-2) — `Pₖ`, `Qₖ`, the
//! projection path of every payload, every binder name — and
//! [`crate::codata_variant_generate`] (VC-3) turns that plan into
//! declarations and registers them through a candidate clone. Neither this
//! module nor the plan consults an environment.
//!
//! [`validate_variant`] takes no `&mut Environment`, so the refusing path
//! cannot touch the environment even by accident; the accepting path's
//! transactionality is the record lane's candidate-clone rollback
//! (`codata_cmd.rs:567`/`:580`), reused verbatim.

use crate::codata_cmd::GlobalPath;
use crate::codata_cmd::{is_self_at_params, mentions, strip_parens};
use crate::codata_variant_plan::{
    gen_names, nest_right, resolve_ctor, VariantCtorPlan, VariantShape,
};
use crate::{ElabError, RegisteredElabResult};
use clean_parser::{
    DeclModifiers, SurfaceBinder, SurfaceBinderInfo, SurfaceCtor, SurfaceExpr, SurfaceName,
    UniverseExpr,
};

/// The single `ElabError` mint point for this lane (the
/// `coinductive_surface.rs:297-301` discipline).
pub(crate) fn unsupported(msg: impl Into<String>) -> ElabError {
    ElabError::Unsupported {
        feature: msg.into(),
    }
}

/// The one accepted `deriving` handle: the coinductive companion tier (VC-6).
pub(crate) const DERIVE_COIND: &str = "Coind";

/// Names the generator will mint under `T.` — a constructor may not take
/// one. Kept in one place so VC-3 cannot drift from VC-1's refusal.
const RESERVED_COMPANIONS: &[&str] = &[
    "shapeF",
    "posF",
    "tgtF",
    "head",
    "child",
    "mk",
    "mkStep",
    "Step",
    "corec",
    "corecStep",
    "head_corec",
    "child_corec",
    // VC-6 (`deriving Coind`). Reserved unconditionally, not only when the
    // tier is requested: whether a name is legal must not depend on a
    // modifier, or adding `deriving Coind` to a working declaration could
    // break it.
    "cast",
    "ExtQ",
    "ExtQ_hhead",
    "ExtQ_of_eq",
    "ext_unwrap",
    "ch_cast_irrel",
    "ext",
    // VC-6b, the case tower. `cases` is the sharp one: a constructor named
    // `cases` would both collide with the tower's own `T.cases` and generate
    // `T.cases_cases`. That is caught downstream by `check_names_distinct`,
    // but a VC-1 refusal names the problem where the user can see it.
    "CasesP",
    "sumCases",
    "cases",
];

/// One argument of a variant constructor, classified by how the carrier
/// occurs in it. The raw classification; [`ArgPlan`] is what the generator
/// consumes.
#[derive(Debug)]
pub(crate) enum CtorArg<'a> {
    /// Type does not mention the carrier: contributes to the constructor's
    /// shape payload `Pₖ`.
    Payload {
        name: Option<&'a SurfaceName>,
        ty: &'a SurfaceExpr,
    },
    /// Exactly `T p⃗`: one child, position `PUnit.{1}`.
    Child { name: Option<&'a SurfaceName> },
    /// `D → T p⃗`: a `D`-indexed family of children, position `D`.
    ChildFamily {
        name: Option<&'a SurfaceName>,
        domain: &'a SurfaceExpr,
    },
}

/// Elaborate a variant-bodied `codata`: validate the whole envelope (this
/// function's `env` is untouched by [`validate_variant`], which takes
/// none), then register the generated family through a candidate clone so
/// a failure anywhere leaves `env` byte-identical.
#[allow(clippy::too_many_arguments)]
pub(crate) fn elab_variant_codata(
    env: &mut clean_kernel::Environment,
    name: &SurfaceName,
    universe_params: &[SurfaceName],
    binders: &[SurfaceBinder],
    ty: &Option<Box<SurfaceExpr>>,
    ctors: &[SurfaceCtor],
    deriving: &[SurfaceName],
    modifiers: &DeclModifiers,
) -> Result<RegisteredElabResult, ElabError> {
    let shape = validate_variant(
        name,
        universe_params,
        binders,
        ty,
        ctors,
        deriving,
        modifiers,
    )?;
    crate::codata_variant_generate::register(env, &shape)
}

/// The whole VC1 envelope, in one fail-closed pass.
#[allow(clippy::too_many_arguments)]
pub(crate) fn validate_variant<'a>(
    name: &'a SurfaceName,
    universe_params: &'a [SurfaceName],
    binders: &'a [SurfaceBinder],
    ty: &Option<Box<SurfaceExpr>>,
    ctors: &'a [SurfaceCtor],
    deriving: &[SurfaceName],
    modifiers: &DeclModifiers,
) -> Result<VariantShape<'a>, ElabError> {
    // `Coind` is the ONE accepted deriving handle: it asks for the coinductive
    // companion tier (VC-6). Everything else stays a loud reject.
    let coind = SurfaceName::generated_path(DERIVE_COIND);
    let derive_coind = deriving.iter().any(|d| d == &coind);
    if let Some(other) = deriving.iter().find(|d| *d != &coind) {
        return Err(unsupported(format!(
            "variant codata `{name}`: deriving {other} is rejected — BEq/DecidableEq/Repr \
             have no sound derivation for M-encoded codata (potentially infinite \
             values); this is a deliberate loud reject, not an omission. The only \
             accepted handle is `deriving {DERIVE_COIND}` (extensionality + eta laws)"
        )));
    }
    if !modifiers.is_default() {
        return Err(unsupported(format!(
            "variant codata `{name}`: declaration modifiers \
             (private/partial/noncomputable/…) are not supported"
        )));
    }
    // ONE universe parameter, mirroring the record lane (`codata_cmd.rs`
    // `validate`). The seed library is already the two-universe `.{u, v}`
    // sibling and this lane instantiates it at `v := u`, so a single
    // parameter is what the lowering can spell.
    let poly: Option<&SurfaceName> = match universe_params {
        [] => None,
        [u] => Some(u),
        _ => {
            return Err(unsupported(format!(
                "variant codata `{name}`: at most ONE universe parameter is \
                 supported (`codata {name}.{{u}}`), got {}",
                universe_params.len()
            )))
        }
    };
    check_result_sort(name, ty)?;
    for b in binders {
        if b.info != SurfaceBinderInfo::Explicit || b.ty.is_none() || b.default.is_some() {
            return Err(unsupported(format!(
                "variant codata `{name}`: parameters must be simple explicit \
                 binders `(x : T)`"
            )));
        }
    }
    if ctors.is_empty() {
        return Err(unsupported(format!(
            "variant codata `{name}`: at least one constructor is required — an \
             empty variant would make the shape functor uninhabited and `{name}` \
             the empty type; refusing to mint it"
        )));
    }
    let mut seen: Vec<&SurfaceName> = Vec::new();
    for c in ctors {
        if seen.contains(&&c.name) {
            return Err(unsupported(format!(
                "variant codata `{name}`: constructor `{}` is declared more than \
                 once — the generated companions would collide",
                c.name
            )));
        }
        seen.push(&c.name);
        if RESERVED_COMPANIONS
            .iter()
            .any(|reserved| c.name == SurfaceName::generated_path(reserved))
        {
            return Err(unsupported(format!(
                "variant codata `{name}`: constructor `{}` collides with the \
                 generated companion `{name}.{}`",
                c.name, c.name
            )));
        }
    }

    let param_names: Vec<&SurfaceName> = binders.iter().map(|b| &b.name).collect();
    // Sequential, not `map`: each constructor's ALTERNATE binder names are
    // minted fresh against every name the earlier constructors already
    // claim, so `T.Cⱼ x⃗ = T.Cₖ y⃗ → False` can bind both telescopes at once.
    let mut plans: Vec<VariantCtorPlan<'a>> = Vec::with_capacity(ctors.len());
    let mut occupied: Vec<SurfaceName> = Vec::new();
    for c in ctors {
        let plan = validate_ctor(poly, name, &param_names, c, &occupied)?;
        occupied.extend(plan.occupied_names());
        plans.push(plan);
    }

    // ANTI-VACUITY: a "codata" whose every constructor is a leaf has no
    // recursive positions at all. Its M-type carrier is isomorphic to a
    // finite sum — i.e. an ordinary `inductive` dressed up as a
    // coinductive one. The record lane refuses the same degeneracy
    // ("a codata with no recursive field is just a record",
    // codata_cmd.rs:368-374).
    if !plans.iter().any(VariantCtorPlan::has_child) {
        return Err(unsupported(format!(
            "variant codata `{name}`: no constructor has a recursive argument, so \
             the carrier would have no infinite values at all — that is an \
             `inductive`, not a codata; refusing to mint it"
        )));
    }

    let shape_ty = nest_right(
        GlobalPath("Sum"),
        plans.iter().map(|c| c.payload_ty.clone()).collect(),
    )
    .ok_or_else(|| unsupported(format!("variant codata `{name}`: no constructors")))?;
    let gen_names = gen_names(binders, &plans);
    Ok(VariantShape {
        name,
        binders,
        ctors: plans,
        shape_ty,
        gen_names,
        poly,
        derive_coind,
    })
}

/// `codata T where` / `codata T : Type where` only. A Pi-headed sort is
/// the INDEXED form, which gets its own message because the record lane
/// supports it and a user may reasonably expect the variant lane to.
fn check_result_sort(name: &SurfaceName, ty: &Option<Box<SurfaceExpr>>) -> Result<(), ElabError> {
    let Some(t) = ty else { return Ok(()) };
    let t = strip_parens(t);
    if matches!(t, SurfaceExpr::Pi(..) | SurfaceExpr::Arrow(..)) {
        return Err(unsupported(format!(
            "variant codata `{name}`: an INDEXED variant codata \
             (`codata {name} : I → Type where | …`) is outside the VC1 envelope \
             (designs/2026-08-28-variant-codata-surface.md §5)"
        )));
    }
    if !matches!(t, SurfaceExpr::Universe(_, UniverseExpr::Type)) {
        return Err(unsupported(format!(
            "variant codata `{name}`: the result sort must be `Type` — Prop-valued \
             coinduction is the separate `coinductive` command, and `Type u` needs \
             the universe-polymorphic lane"
        )));
    }
    Ok(())
}

/// Flatten one constructor's telescope and classify every argument.
fn validate_ctor<'a>(
    poly: Option<&SurfaceName>,
    name: &SurfaceName,
    param_names: &[&SurfaceName],
    ctor: &'a SurfaceCtor,
    occupied: &[SurfaceName],
) -> Result<VariantCtorPlan<'a>, ElabError> {
    let cname = &ctor.name;
    let (arg_tys, ret) = flatten_telescope(&ctor.ty, name, cname)?;
    if !is_self_at_params(ret, name, param_names, poly) {
        return Err(unsupported(format!(
            "variant codata `{name}`: constructor `{cname}` must return `{name}` \
             applied to exactly its declared parameters, by name"
        )));
    }

    let mut args: Vec<CtorArg<'a>> = Vec::new();
    let mut payload_names: Vec<&'a SurfaceName> = Vec::new();
    let mut child_names: Vec<&'a SurfaceName> = Vec::new();
    for (binder_name, arg_ty) in arg_tys {
        let classified = classify_arg(poly, name, param_names, cname, binder_name, arg_ty)?;
        // A child argument's DOMAIN may mention earlier payload binders
        // (that is exactly `Vis : (e : E) → (Ans e → T) → T`); nothing may
        // mention an earlier CHILD binder, and a payload type may not
        // mention an earlier payload binder (that needs a `Sigma`, not the
        // `PProd` tower VC1 builds). A bare `T p⃗` child has no type to
        // scan at all.
        let scan = match &classified {
            CtorArg::Payload { ty, .. } => Some((*ty, true)),
            CtorArg::Child { .. } => None,
            CtorArg::ChildFamily { domain, .. } => Some((*domain, false)),
        };
        if let Some((scan_ty, forbid_payload_refs)) = scan {
            for earlier in &child_names {
                if mentions(scan_ty, earlier) {
                    return Err(unsupported(format!(
                        "variant codata `{name}`: constructor `{cname}` has an \
                         argument whose type mentions the earlier RECURSIVE \
                         argument `{earlier}` — a recursive argument is a child of \
                         the node, not a value its siblings' types may depend on"
                    )));
                }
            }
            if forbid_payload_refs {
                for earlier in &payload_names {
                    if mentions(scan_ty, earlier) {
                        return Err(unsupported(format!(
                            "variant codata `{name}`: constructor `{cname}` has a \
                             non-recursive argument whose type mentions the earlier \
                             non-recursive argument `{earlier}` — a DEPENDENT \
                             payload telescope needs a `Sigma` shape and is outside \
                             the VC1 envelope \
                             (designs/2026-08-28-variant-codata-surface.md §5)"
                        )));
                    }
                }
            }
        }
        let (bound, is_child) = match &classified {
            CtorArg::Payload { name, .. } => (*name, false),
            CtorArg::Child { name } => (*name, true),
            CtorArg::ChildFamily { name, .. } => (*name, true),
        };
        if let Some(n) = bound {
            if param_names.contains(&n) {
                return Err(unsupported(format!(
                    "variant codata `{name}`: constructor `{cname}` binds `{n}`, \
                     which SHADOWS the parameter `{n}` — the generated \
                     declarations take the parameters as leading binders, so a \
                     constructor argument may not reuse a parameter name"
                )));
            }
            if payload_names.contains(&n) || child_names.contains(&n) {
                return Err(unsupported(format!(
                    "variant codata `{name}`: constructor `{cname}` binds `{n}` \
                     twice — argument names must be distinct so payload \
                     references resolve unambiguously"
                )));
            }
            if is_child {
                child_names.push(n);
            } else {
                payload_names.push(n);
            }
        }
        args.push(classified);
    }

    resolve_ctor(poly, name, param_names, cname, args, occupied)
}

/// Split a constructor type into `(argument binder name, argument type)`
/// pairs plus the return type, flattening both `Pi` and `Arrow`.
fn flatten_telescope<'a>(
    ty: &'a SurfaceExpr,
    name: &SurfaceName,
    cname: &SurfaceName,
) -> Result<
    (
        Vec<(Option<&'a SurfaceName>, &'a SurfaceExpr)>,
        &'a SurfaceExpr,
    ),
    ElabError,
> {
    let mut args: Vec<(Option<&'a SurfaceName>, &'a SurfaceExpr)> = Vec::new();
    let mut cur = strip_parens(ty);
    loop {
        match cur {
            SurfaceExpr::Pi(_, bs, body) => {
                for b in bs {
                    if b.info != SurfaceBinderInfo::Explicit {
                        return Err(unsupported(format!(
                            "variant codata `{name}`: constructor `{cname}` uses an \
                             implicit/instance binder `{}` — VC1 constructors take \
                             explicit arguments only",
                            b.name
                        )));
                    }
                    if b.default.is_some() {
                        return Err(unsupported(format!(
                            "variant codata `{name}`: constructor `{cname}` binder \
                             `{}` carries a default value",
                            b.name
                        )));
                    }
                    let Some(bty) = &b.ty else {
                        return Err(unsupported(format!(
                            "variant codata `{name}`: constructor `{cname}` binder \
                             `{}` has no type ascription",
                            b.name
                        )));
                    };
                    args.push((Some(&b.name), bty));
                }
                cur = strip_parens(body);
            }
            SurfaceExpr::Arrow(_, a, b) => {
                args.push((None, strip_parens(a)));
                cur = strip_parens(b);
            }
            _ => return Ok((args, cur)),
        }
    }
}

/// Classify one constructor argument. Everything that is neither a
/// carrier-free payload nor one of the two admitted child forms is a
/// nested or negative occurrence and is refused by name.
fn classify_arg<'a>(
    poly: Option<&SurfaceName>,
    name: &SurfaceName,
    param_names: &[&SurfaceName],
    cname: &SurfaceName,
    binder_name: Option<&'a SurfaceName>,
    arg_ty: &'a SurfaceExpr,
) -> Result<CtorArg<'a>, ElabError> {
    if !mentions(arg_ty, name) {
        return Ok(CtorArg::Payload {
            name: binder_name,
            ty: arg_ty,
        });
    }
    if is_self_at_params(arg_ty, name, param_names, poly) {
        return Ok(CtorArg::Child { name: binder_name });
    }
    // `D → T p⃗` (or the one-binder Pi spelling of it).
    let fam = match strip_parens(arg_ty) {
        SurfaceExpr::Arrow(_, d, body) => Some((strip_parens(d), strip_parens(body))),
        SurfaceExpr::Pi(_, bs, body) if bs.len() == 1 => bs[0]
            .ty
            .as_ref()
            .map(|d| (strip_parens(d), strip_parens(body))),
        _ => None,
    };
    if let Some((domain, body)) = fam {
        if is_self_at_params(body, name, param_names, poly) && !mentions(domain, name) {
            return Ok(CtorArg::ChildFamily {
                name: binder_name,
                domain,
            });
        }
    }
    Err(unsupported(format!(
        "variant codata `{name}`: constructor `{cname}` has an argument in which \
         `{name}` occurs neither as `{name}` at its own parameters nor as \
         `D → {name}` with `D` free of `{name}` — nested, negative and \
         parameter-varying occurrences are outside the VC1 envelope \
         (designs/2026-08-28-variant-codata-surface.md §5)"
    )))
}
