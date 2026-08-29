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
//! **VC-1 validates fully and generates NOTHING.** Every envelope
//! violation gets its own named [`ElabError::Unsupported`]; a declaration
//! that passes the whole envelope is *still* refused, by
//! [`NOT_YET_IMPLEMENTED`], because the lowering (VC-3) is not built. That
//! ordering is deliberate: the thing worth preventing first is a silent
//! wrong lowering, and the second-worst outcome is the MEASURED status quo
//! — a variant `codata` body parsing as zero fields and reporting
//! "codata needs at least one observation field … got 0 field(s)" while
//! the `|` clauses fall out to top-level parse recovery.
//!
//! Nothing here touches the environment. The function takes no
//! `&mut Environment` at all, so "a partial family never lands" is a
//! property of the signature rather than of a rollback that has to be got
//! right. VC-3 introduces the candidate-clone registration used by the
//! record lane (`codata_cmd.rs:567`/`:580`).

use crate::codata_cmd::{is_self_at_params, mentions, strip_parens};
use crate::{ElabError, RegisteredElabResult};
use clean_parser::{
    DeclModifiers, SurfaceBinder, SurfaceBinderInfo, SurfaceCtor, SurfaceExpr, UniverseExpr,
};

/// The single `ElabError` mint point for this lane (the
/// `coinductive_surface.rs:297-301` discipline).
fn unsupported(msg: impl Into<String>) -> ElabError {
    ElabError::Unsupported {
        feature: msg.into(),
    }
}

/// The terminal refusal for an in-envelope variant codata.
///
/// Deliberately distinct from every envelope refusal so a caller can tell
/// "your declaration is malformed" from "your declaration is fine and the
/// lowering is not built yet" — and it echoes back the shape it just
/// validated, so the author can see that the classification agreed with
/// what they wrote before VC-3 exists to act on it.
fn not_yet_implemented(shape: &VariantShape<'_>) -> ElabError {
    let ctors: Vec<&str> = shape.ctors.iter().map(|c| c.name).collect();
    unsupported(format!(
        "variant codata `{}` ({} parameter(s), {} constructor(s): {}) parses and \
         validates against the VC1 envelope, but its M-type lowering is not \
         implemented yet (brick VC-3 of \
         designs/2026-08-28-variant-codata-surface.md); refusing rather than \
         registering a partial family",
        shape.name,
        shape.binders.len(),
        ctors.len(),
        ctors.join(", ")
    ))
}

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
];

/// One argument of a variant constructor, classified by how the carrier
/// occurs in it.
#[derive(Debug)]
pub(crate) enum CtorArg<'a> {
    /// Type does not mention the carrier: contributes to the constructor's
    /// shape payload `Pₖ`.
    Payload {
        name: Option<&'a str>,
        ty: &'a SurfaceExpr,
    },
    /// Exactly `T p⃗`: one child, position `PUnit.{1}`.
    Child { name: Option<&'a str> },
    /// `D → T p⃗`: a `D`-indexed family of children, position `D`.
    ChildFamily {
        name: Option<&'a str>,
        domain: &'a SurfaceExpr,
    },
}

/// A validated variant constructor.
#[derive(Debug)]
pub(crate) struct VariantCtorPlan<'a> {
    pub(crate) name: &'a str,
    pub(crate) args: Vec<CtorArg<'a>>,
}

impl VariantCtorPlan<'_> {
    /// Does this constructor have at least one recursive position?
    fn has_child(&self) -> bool {
        self.args
            .iter()
            .any(|a| matches!(a, CtorArg::Child { .. } | CtorArg::ChildFamily { .. }))
    }
}

/// A validated variant codata declaration. VC-2 turns this into the
/// `Pₖ`/`Qₖ`/projection plan; VC-1 only proves it exists.
#[derive(Debug)]
pub(crate) struct VariantShape<'a> {
    pub(crate) name: &'a str,
    pub(crate) binders: &'a [SurfaceBinder],
    pub(crate) ctors: Vec<VariantCtorPlan<'a>>,
}

/// Elaborate a variant-bodied `codata`. In VC-1 this ALWAYS returns
/// `Err`: either a specific envelope refusal or [`not_yet_implemented`].
pub(crate) fn elab_variant_codata(
    name: &str,
    universe_params: &[String],
    binders: &[SurfaceBinder],
    ty: &Option<Box<SurfaceExpr>>,
    ctors: &[SurfaceCtor],
    deriving: &[String],
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
    Err(not_yet_implemented(&shape))
}

/// The whole VC1 envelope, in one fail-closed pass.
#[allow(clippy::too_many_arguments)]
pub(crate) fn validate_variant<'a>(
    name: &'a str,
    universe_params: &[String],
    binders: &'a [SurfaceBinder],
    ty: &Option<Box<SurfaceExpr>>,
    ctors: &'a [SurfaceCtor],
    deriving: &[String],
    modifiers: &DeclModifiers,
) -> Result<VariantShape<'a>, ElabError> {
    if !deriving.is_empty() {
        return Err(unsupported(format!(
            "variant codata `{name}`: deriving {} is rejected — BEq/DecidableEq/Repr \
             have no sound derivation for M-encoded codata (potentially infinite \
             values); this is a deliberate loud reject, not an omission",
            deriving.join(", ")
        )));
    }
    if !modifiers.is_default() {
        return Err(unsupported(format!(
            "variant codata `{name}`: declaration modifiers \
             (private/partial/noncomputable/…) are not supported"
        )));
    }
    if !universe_params.is_empty() {
        return Err(unsupported(format!(
            "variant codata `{name}`: universe-polymorphic variant codata \
             (`codata {name}.{{u}}`) is outside the VC1 envelope — VC1 is \
             monomorphic `Type` (designs/2026-08-28-variant-codata-surface.md §5)"
        )));
    }
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
    let mut seen: Vec<&str> = Vec::new();
    for c in ctors {
        if seen.contains(&c.name.as_str()) {
            return Err(unsupported(format!(
                "variant codata `{name}`: constructor `{}` is declared more than \
                 once — the generated companions would collide",
                c.name
            )));
        }
        seen.push(&c.name);
        if RESERVED_COMPANIONS.contains(&c.name.as_str()) {
            return Err(unsupported(format!(
                "variant codata `{name}`: constructor `{}` collides with the \
                 generated companion `{name}.{}`",
                c.name, c.name
            )));
        }
    }

    let param_names: Vec<&str> = binders.iter().map(|b| b.name.as_str()).collect();
    let plans = ctors
        .iter()
        .map(|c| validate_ctor(name, &param_names, c))
        .collect::<Result<Vec<_>, _>>()?;

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

    Ok(VariantShape {
        name,
        binders,
        ctors: plans,
    })
}

/// `codata T where` / `codata T : Type where` only. A Pi-headed sort is
/// the INDEXED form, which gets its own message because the record lane
/// supports it and a user may reasonably expect the variant lane to.
fn check_result_sort(name: &str, ty: &Option<Box<SurfaceExpr>>) -> Result<(), ElabError> {
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
    name: &str,
    param_names: &[&str],
    ctor: &'a SurfaceCtor,
) -> Result<VariantCtorPlan<'a>, ElabError> {
    let cname = ctor.name.as_str();
    let (arg_tys, ret) = flatten_telescope(&ctor.ty, name, cname)?;
    if !is_self_at_params(ret, name, param_names) {
        return Err(unsupported(format!(
            "variant codata `{name}`: constructor `{cname}` must return `{name}` \
             applied to exactly its declared parameters, by name"
        )));
    }

    let mut args: Vec<CtorArg<'a>> = Vec::new();
    let mut payload_names: Vec<&'a str> = Vec::new();
    let mut child_names: Vec<&'a str> = Vec::new();
    for (binder_name, arg_ty) in arg_tys {
        let classified = classify_arg(name, param_names, cname, binder_name, arg_ty)?;
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
            if is_child {
                child_names.push(n);
            } else {
                payload_names.push(n);
            }
        }
        args.push(classified);
    }

    Ok(VariantCtorPlan { name: cname, args })
}

/// Split a constructor type into `(argument binder name, argument type)`
/// pairs plus the return type, flattening both `Pi` and `Arrow`.
fn flatten_telescope<'a>(
    ty: &'a SurfaceExpr,
    name: &str,
    cname: &str,
) -> Result<(Vec<(Option<&'a str>, &'a SurfaceExpr)>, &'a SurfaceExpr), ElabError> {
    let mut args: Vec<(Option<&'a str>, &'a SurfaceExpr)> = Vec::new();
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
                    args.push((Some(b.name.as_str()), bty));
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
    name: &str,
    param_names: &[&str],
    cname: &str,
    binder_name: Option<&'a str>,
    arg_ty: &'a SurfaceExpr,
) -> Result<CtorArg<'a>, ElabError> {
    if !mentions(arg_ty, name) {
        return Ok(CtorArg::Payload {
            name: binder_name,
            ty: arg_ty,
        });
    }
    if is_self_at_params(arg_ty, name, param_names) {
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
        if is_self_at_params(body, name, param_names) && !mentions(domain, name) {
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
