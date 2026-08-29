// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! VARIANT codata discrimination and injectivity — brick VC-5 of
//! `designs/2026-08-28-variant-codata-surface.md`.
//!
//! [`crate::codata_variant_generate`] emits the family and how it COMPUTES;
//! this module emits what tells its constructors APART. Everything here is
//! ordinary term-mode: no coinduction, no `iM_coind`, nothing that needs the
//! seed cut moved (design §1c). Every proof goes through the `rfl` head law
//! the definitional tier already emitted, so this module never reasons about
//! the M-type encoding at all — it reasons about `Sum`.
//!
//! Three families, for a codata with constructors `C₀ … Cₙ₋₁`:
//!
//! | generated | shape | how |
//! |---|---|---|
//! | `T.isCₖ` | `T.shapeF ps PUnit.unit → Prop` | the tag tower, `True` at `k` |
//! | `T.Cⱼ_ne_Cₖ` (j < k) | `T.Cⱼ x⃗ = T.Cₖ y⃗ → False` | `Eq.rec` on `T.isCⱼ` |
//! | `T.out_Cₖ` / `T.Cₖ_inj` | payload retraction / `Pₖ` equation | `congrArg` |
//!
//! **Why the discriminator is a `Prop` classifier and not a tag numeral.**
//! `T.isCⱼ ps tagⱼ` reduces to `True` and `T.isCⱼ ps tagₖ` to `False`
//! DEFINITIONALLY, so `Eq.rec` transports `True.intro` straight to `False`
//! with no arithmetic and no `noConfusion` — the recipe rank 9 arrived at by
//! hand (`data/graduation/clean-mtype/proof/ITreeEco.lean:3027-3063`).
//!
//! **What is deliberately NOT here.** Child injectivity
//! (`T.Tau x = T.Tau y → x = y`) is not a `congrArg`: `Codata.IMchild m b`
//! binds `b` at `B i (IMhead m)`, so the position's TYPE moves with the value
//! being congruenced, and the retraction needs the equation-carrying `Sum.rec`
//! tower of `ITreeEco.lean:3075+`. That is past the range the design cites for
//! this brick, and stating it would cost a probe cycle per shape.

use crate::codata_cmd::{arrow, at_app, ident, lam, mk_def, mk_theorem, plain_app};
use crate::codata_variant_generate::{
    binder, ctor_binders, ctor_call, eq, lam_one, lam_typed, tag_tower,
};
use crate::codata_variant_plan::{projection_path, ArgPlan, VariantCtorPlan, VariantShape};
use clean_parser::{Span, SurfaceBinder, SurfaceDecl, SurfaceExpr, UniverseExpr};

/// `Prop`, as a sort rather than an identifier lookup.
fn prop_universe() -> SurfaceExpr {
    SurfaceExpr::Universe(Span::dummy(), UniverseExpr::Prop)
}

/// One side of a two-sided statement: a constructor's telescope under a
/// chosen naming, plus the call and the shape tag those binders build.
///
/// `T.Cⱼ x⃗ = T.Cₖ y⃗ → False` and `T.Cₖ x⃗ = T.Cₖ y⃗ → x⃗ = y⃗` both put two
/// telescopes in ONE binder list, so the second must not shadow the first.
/// That is what `PayloadPlan::alt_name` is for, and why a family child's
/// domain has to be re-spelled: `T.Vis_inj` needs `k₀ : Ans e₀ → T`, not
/// `Ans e → T`. Left unhandled, `T.Ret_inj` for `| Ret : (r : R) → T` would
/// bind `r` twice and degrade to the vacuous `r = r`.
struct CtorSide {
    binders: Vec<SurfaceBinder>,
    call: SurfaceExpr,
    tag: SurfaceExpr,
    payload_value: SurfaceExpr,
}

/// Build one side. `alt = false` uses the primary binder names, `alt = true`
/// the alternates.
fn ctor_side(
    shape: &VariantShape<'_>,
    k: usize,
    ctor: &VariantCtorPlan<'_>,
    params: &[SurfaceExpr],
    self_ty: &SurfaceExpr,
    alt: bool,
) -> CtorSide {
    if !alt {
        return CtorSide {
            binders: ctor_binders(ctor, self_ty),
            call: ctor_call(shape.name, ctor, params),
            tag: shape.tag(k, ctor.payload_value()),
            payload_value: ctor.payload_value(),
        };
    }
    let binders = ctor
        .args
        .iter()
        .map(|a| match a {
            ArgPlan::Payload(p) => binder(&p.alt_name, p.ty.clone()),
            ArgPlan::Child(c) => binder(
                &c.alt_name,
                match &c.family {
                    Some(f) => arrow(f.in_alt.clone(), self_ty.clone()),
                    None => self_ty.clone(),
                },
            ),
        })
        .collect();
    let mut call_args = params.to_vec();
    call_args.extend(ctor.args.iter().map(|a| ident(a.alt_name())));
    CtorSide {
        binders,
        call: plain_app(&format!("{}.{}", shape.name, ctor.name), call_args),
        tag: shape.tag(k, ctor.alt_payload_value()),
        payload_value: ctor.alt_payload_value(),
    }
}

/// `T.head_Cₖ ps args…` under the primary or alternate naming — the `rfl`
/// head law the definitional tier emitted, applied to one side's binders.
fn head_law_call(
    name: &str,
    ctor: &VariantCtorPlan<'_>,
    params: &[SurfaceExpr],
    alt: bool,
) -> SurfaceExpr {
    let mut args = params.to_vec();
    args.extend(
        ctor.args
            .iter()
            .map(|a| ident(if alt { a.alt_name() } else { a.arg_name() })),
    );
    plain_app(&format!("{name}.head_{}", ctor.name), args)
}

/// VC-5's whole output, in dependency order: the classifiers, the
/// disjointness matrix, then the retractions and injectivity.
///
/// With ONE constructor there is nothing to discriminate — no pair exists and
/// every classifier would be the constant `True` — so the discrimination half
/// is skipped. Injectivity is still emitted: a one-constructor variant IS the
/// record encoding (design §3), and `T.step x⃗ = T.step y⃗ → x⃗ = y⃗` is exactly
/// as meaningful there.
pub(crate) fn generate(shape: &VariantShape<'_>) -> Vec<SurfaceDecl> {
    let name = shape.name;
    let g = &shape.gen_names;
    let binders: Vec<SurfaceBinder> = shape.binders.to_vec();
    let params: Vec<SurfaceExpr> = shape.binders.iter().map(|b| ident(&b.name)).collect();
    let self_ty = plain_app(name, params.clone());
    let n = shape.ctors.len();
    // The shape functor at the single index: the argument type of every
    // classifier and retraction, and the type both sides of a head equation
    // live at.
    let head_ty = {
        let mut args = params.clone();
        args.push(ident("PUnit.unit"));
        plain_app(&format!("{name}.shapeF"), args)
    };
    let head_call = |x: SurfaceExpr| {
        let mut args = params.clone();
        args.push(x);
        plain_app(&format!("{name}.head"), args)
    };
    // A tag tower scrutinises `scruts[0]`, so a declaration whose BODY is a
    // tag tower binds its argument under that name.
    let scrut = g.scruts[0].as_str();

    let mut out: Vec<SurfaceDecl> = Vec::new();
    if n >= 2 {
        // def T.isCₖ (ps) (s0 : T.shapeF ps PUnit.unit) : Prop
        for (k, ctor) in shape.ctors.iter().enumerate() {
            out.push(mk_def(
                format!("{name}.is{}", ctor.name),
                {
                    let mut bs = binders.clone();
                    bs.push(binder(scrut, head_ty.clone()));
                    bs
                },
                prop_universe(),
                tag_tower(
                    shape,
                    &lam(&["_"], prop_universe()),
                    &|i, _| lam(&["_"], ident(if i == k { "True" } else { "False" })),
                    0,
                ),
            ));
        }
        // theorem T.Cⱼ_ne_Cₖ (ps) (x⃗) (y⃗) (h : T.Cⱼ ps x⃗ = T.Cₖ ps y⃗) : False
        for j in 0..n {
            for k in (j + 1)..n {
                out.push(disjointness(
                    shape, j, k, &params, &self_ty, &head_ty, &head_call, scrut,
                ));
            }
        }
    }

    out.extend(injectivity_tier(
        shape, &params, &self_ty, &head_ty, &head_call, scrut,
    ));
    out
}

/// `T.Cⱼ x⃗ = T.Cₖ y⃗ → False`, for `j < k`.
#[allow(clippy::too_many_arguments)]
fn disjointness(
    shape: &VariantShape<'_>,
    j: usize,
    k: usize,
    params: &[SurfaceExpr],
    self_ty: &SurfaceExpr,
    head_ty: &SurfaceExpr,
    head_call: &dyn Fn(SurfaceExpr) -> SurfaceExpr,
    scrut: &str,
) -> SurfaceDecl {
    let name = shape.name;
    let g = &shape.gen_names;
    let cj = &shape.ctors[j];
    let ck = &shape.ctors[k];
    let left = ctor_side(shape, j, cj, params, self_ty, false);
    let right = ctor_side(shape, k, ck, params, self_ty, true);
    // The two heads are equal because the two values are: read the `rfl` head
    // law off each side and splice them onto `congrArg`.
    let heads_eq = plain_app(
        "Eq.trans",
        vec![
            plain_app("Eq.symm", vec![head_law_call(name, cj, params, false)]),
            plain_app(
                "Eq.trans",
                vec![
                    plain_app(
                        "congrArg",
                        vec![
                            lam_typed(
                                &g.value_arg,
                                self_ty.clone(),
                                head_call(ident(&g.value_arg)),
                            ),
                            ident(&g.eq_arg),
                        ],
                    ),
                    head_law_call(name, ck, params, true),
                ],
            ),
        ],
    );
    let motive = lam(&[scrut, "_"], {
        let mut args = params.to_vec();
        args.push(ident(scrut));
        plain_app(&format!("{name}.is{}", cj.name), args)
    });
    mk_theorem(
        format!("{name}.{}_ne_{}", cj.name, ck.name),
        {
            let mut bs = shape.binders.to_vec();
            bs.extend(left.binders);
            bs.extend(right.binders);
            bs.push(binder(&g.eq_arg, eq(left.call, right.call)));
            bs
        },
        ident("False"),
        // `T.isCⱼ ps tagⱼ` IS `True` and `T.isCⱼ ps tagₖ` IS `False`,
        // definitionally, so transporting `True.intro` along the head equation
        // lands exactly on the goal.
        at_app(
            "Eq.rec",
            vec![
                head_ty.clone(),
                left.tag,
                motive,
                ident("True.intro"),
                right.tag,
                heads_eq,
            ],
        ),
    )
}

/// The payload retraction and injectivity of every constructor that HAS a
/// payload.
///
/// `T.out_Cₖ ps d` is total on the shape — every branch but `k`'s returns the
/// default — so `congrArg (fun z => T.out_Cₖ ps d (T.head ps z))` turns
/// `T.Cₖ x⃗ = T.Cₖ y⃗` into `Pₖ`'s equation with no case analysis at all. The
/// default is taken to be the LEFT side's own payload, which always exists, so
/// no inhabitant of `Pₖ` has to be conjured.
fn injectivity_tier(
    shape: &VariantShape<'_>,
    params: &[SurfaceExpr],
    self_ty: &SurfaceExpr,
    head_ty: &SurfaceExpr,
    head_call: &dyn Fn(SurfaceExpr) -> SurfaceExpr,
    scrut: &str,
) -> Vec<SurfaceDecl> {
    let name = shape.name;
    let g = &shape.gen_names;
    let n = shape.ctors.len();
    let mut out: Vec<SurfaceDecl> = Vec::new();

    for (k, ctor) in shape.ctors.iter().enumerate() {
        let m = ctor.payload_count();
        if m == 0 {
            continue;
        }
        let out_name = format!("{name}.out_{}", ctor.name);
        let inj_name = format!("{name}.{}_inj", ctor.name);
        let left = ctor_side(shape, k, ctor, params, self_ty, false);
        let right = ctor_side(shape, k, ctor, params, self_ty, true);

        // def T.out_Cₖ (ps) (d : Pₖ) (s0 : T.shapeF ps PUnit.unit) : Pₖ
        //
        // With one constructor there is no tag to dispatch on: the shape IS
        // `P₀`, so the retraction is the identity and the default is unused.
        let body = if n == 1 {
            ident(scrut)
        } else {
            tag_tower(
                shape,
                &lam(&["_"], ctor.payload_ty.clone()),
                &|i, _| {
                    if i == k {
                        lam_one(&g.shape_arg, ident(&g.shape_arg))
                    } else {
                        lam(&["_"], ident(&g.default_arg))
                    }
                },
                0,
            )
        };
        out.push(mk_def(
            out_name.clone(),
            {
                let mut bs = shape.binders.to_vec();
                bs.push(binder(&g.default_arg, ctor.payload_ty.clone()));
                bs.push(binder(scrut, head_ty.clone()));
                bs
            },
            ctor.payload_ty.clone(),
            body,
        ));

        // theorem T.Cₖ_inj (ps) (x⃗) (y⃗) (h : T.Cₖ ps x⃗ = T.Cₖ ps y⃗) :
        //   <Pₖ of x⃗> = <Pₖ of y⃗>
        let inj_binders: Vec<SurfaceBinder> = {
            let mut bs = shape.binders.to_vec();
            bs.extend(left.binders.iter().cloned());
            bs.extend(right.binders.iter().cloned());
            bs.push(binder(&g.eq_arg, eq(left.call.clone(), right.call.clone())));
            bs
        };
        out.push(mk_theorem(
            inj_name.clone(),
            inj_binders.clone(),
            eq(left.payload_value.clone(), right.payload_value.clone()),
            plain_app(
                "congrArg",
                vec![
                    lam_typed(&g.value_arg, self_ty.clone(), {
                        let mut args = params.to_vec();
                        args.push(left.payload_value.clone());
                        args.push(head_call(ident(&g.value_arg)));
                        plain_app(&out_name, args)
                    }),
                    ident(&g.eq_arg),
                ],
            ),
        ));

        // With several payloads `Pₖ` is a `PProd` tower, so the equation above
        // is about the PACKED value. Project it apart, one theorem per
        // payload, so the useful spelling exists without the caller having to
        // know the packing order.
        if m < 2 {
            continue;
        }
        let inj_call = {
            let mut args = params.to_vec();
            args.extend(ctor.args.iter().map(|a| ident(a.arg_name())));
            args.extend(ctor.args.iter().map(|a| ident(a.alt_name())));
            args.push(ident(&g.eq_arg));
            plain_app(&inj_name, args)
        };
        for (i, p) in ctor.payloads().enumerate() {
            out.push(mk_theorem(
                format!("{inj_name}_{i}"),
                inj_binders.clone(),
                eq(ident(&p.arg_name), ident(&p.alt_name)),
                plain_app(
                    "congrArg",
                    vec![
                        lam_typed(
                            &g.shape_arg,
                            ctor.payload_ty.clone(),
                            projection_path(&g.shape_arg, i, m),
                        ),
                        inj_call.clone(),
                    ],
                ),
            ));
        }
    }

    out
}
