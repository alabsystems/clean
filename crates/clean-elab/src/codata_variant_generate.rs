// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! VARIANT codata generation — bricks VC-3 and VC-4 of
//! `designs/2026-08-28-variant-codata-surface.md`.
//!
//! Turns the pure [`VariantShape`] plan of [`crate::codata_variant`] into
//! the definitional tier (VC-3: container `shapeF`/`posF`/`tgtF`, carrier,
//! `mkStep`, the constructors, `head`, and the `rfl` computation laws) and
//! the corecursor tier (VC-4: `Step`, the per-constructor step builders,
//! `corec`, and the `rfl` laws that make a corecursion compute). What tells
//! the constructors APART is [`crate::codata_variant_companions`] (VC-5).
//!
//! The target is not invented here. `data/variant_codata/itree_target.lean`
//! is the hand-written, kernel-checked lowering of the four-constructor
//! ITree — covering all four position shapes (`PEmpty.{1}`, `PUnit.{1}`, a
//! payload-DEPENDENT `Ans e`, and a k-fold `Sum`) — and
//! `codata_variant_generate_tests::test_generated_family_matches_the_hand_written_target`
//! asserts that what this module emits elaborates to the SAME kernel terms.
//!
//! It strictly generalizes the record lane: with one constructor,
//! `shapeF` is the bare `PProd` label and `posF` is constant in the shape,
//! which is exactly `codata_cmd::generate`'s encoding.
//!
//! Registration is transactional in the record lane's idiom
//! (`codata_cmd.rs:567`/`:580`): every generated declaration goes through
//! the ordinary `elaborate_decl_and_register` pipeline into a CLONE, and
//! the clone replaces `env` only after the last one kernel-checks. A
//! partial family can therefore never land, and neither can the
//! `mark_codata_carrier` provenance mark.

use crate::codata_cmd::{
    arrow, at_app, ident, lam, mk_def, mk_theorem, pi, plain_app, punit_ty, type_universe,
};
use crate::codata_seed::ensure_codata_seeds;
use crate::codata_variant_plan::{
    inject_sum, pempty_ty, ArgPlan, ChildPlan, GenNames, VariantCtorPlan, VariantShape,
};
use crate::{ElabError, ElabResult, RegisteredElabResult};
use clean_kernel::Environment;
use clean_parser::{
    Projection, Span, SurfaceArg, SurfaceBinder, SurfaceBinderInfo, SurfaceDecl, SurfaceExpr,
};

fn unsupported(msg: impl Into<String>) -> ElabError {
    ElabError::Unsupported {
        feature: msg.into(),
    }
}

/// Generate, kernel-check and register the whole family — all-or-nothing.
pub(crate) fn register(
    env: &mut Environment,
    shape: &VariantShape<'_>,
) -> Result<RegisteredElabResult, ElabError> {
    let name = shape.name;
    let mut decls = generate(shape);
    if shape.derive_coind {
        decls.extend(crate::codata_variant_coind::generate(shape)?);
    }
    check_names_distinct(name, &decls)?;
    let mut candidate = env.clone();
    // The coinductive tier needs the coinduction seed SECTION on top of the
    // core; a codata that did not ask for it pays neither the declarations
    // nor the check time.
    if shape.derive_coind {
        crate::codata_seed::ensure_codata_coind_seeds(&mut candidate)?;
    } else {
        ensure_codata_seeds(&mut candidate)?;
    }
    for (i, generated) in decls.into_iter().enumerate() {
        crate::elaborate_decl_and_register(&mut candidate, &generated).map_err(|e| {
            unsupported(format!(
                "variant codata `{name}`: generated declaration {i} failed to \
                 elaborate/kernel-check (env left untouched): {e:?}"
            ))
        })?;
    }
    // Carrier provenance, on the CANDIDATE only — same as the record lane
    // (`codata_cmd.rs:547`/`:579`), so a family that failed leaves no mark.
    candidate.mark_codata_carrier(clean_kernel::Name::from_string(name));
    *env = candidate;
    Ok(RegisteredElabResult {
        result: ElabResult::Skipped,
        warning: None,
        hole_contexts: Vec::new(),
    })
}

/// The name of a generated declaration. `generate` emits only `def`s and
/// `theorem`s, so anything else is a bug in this module rather than in the
/// user's source — it is reported as an unnamed slot rather than silently
/// skipped by the collision check below.
fn decl_name(decl: &SurfaceDecl) -> Option<&str> {
    match decl {
        SurfaceDecl::Def { name, .. } | SurfaceDecl::Theorem { name, .. } => Some(name),
        _ => None,
    }
}

/// Refuse a family whose generated names are not all distinct.
///
/// `codata_variant::RESERVED_COMPANIONS` catches a constructor that
/// takes a FIXED companion name (`corec`, `head`, …), but the companions are
/// also derived FROM the constructor names, so a collision can be minted by a
/// pair: `| Ret | head_Ret` generates `T.head_Ret` twice — once as the second
/// constructor, once as the first's head law. Registering the second would be
/// a raw duplicate-declaration failure out of the kernel; this turns it into a
/// named refusal that says which name and nothing has been touched.
fn check_names_distinct(name: &str, decls: &[SurfaceDecl]) -> Result<(), ElabError> {
    let mut seen: Vec<&str> = Vec::with_capacity(decls.len());
    for decl in decls {
        let Some(n) = decl_name(decl) else {
            return Err(unsupported(format!(
                "variant codata `{name}`: the generator produced a declaration \
                 form that is neither a `def` nor a `theorem`"
            )));
        };
        if seen.contains(&n) {
            return Err(unsupported(format!(
                "variant codata `{name}`: two generated declarations would both \
                 be called `{n}` — a constructor name collides with a companion \
                 derived from another constructor's name; rename one of them"
            )));
        }
        seen.push(n);
    }
    Ok(())
}

/// `Eq lhs rhs` — the law statements, spelled exactly as the record lane
/// spells them (`codata_cmd.rs:1108`).
pub(crate) fn eq(lhs: SurfaceExpr, rhs: SurfaceExpr) -> SurfaceExpr {
    SurfaceExpr::App(
        Span::dummy(),
        Box::new(ident("Eq")),
        vec![SurfaceArg::positional(lhs), SurfaceArg::positional(rhs)],
    )
}

pub(crate) fn binder(name: &str, ty: SurfaceExpr) -> SurfaceBinder {
    SurfaceBinder::new(name, Some(ty), SurfaceBinderInfo::Explicit)
}

/// `fun <names> => body`, binding by string (the [`lam`] helper takes
/// `&[&str]`, which a `Vec<String>` cannot be coerced to).
pub(crate) fn lam_one(name: &str, body: SurfaceExpr) -> SurfaceExpr {
    SurfaceExpr::Lambda(
        Span::dummy(),
        vec![SurfaceBinder::new(name, None, SurfaceBinderInfo::Explicit)],
        Box::new(body),
    )
}

/// `fun (name : ty) => body` — an ASCRIBED one-binder lambda. Needed
/// wherever the lambda is the motive-ish argument of `congrArg`, which
/// cannot infer the domain from the equation alone.
pub(crate) fn lam_typed(name: &str, ty: SurfaceExpr, body: SurfaceExpr) -> SurfaceExpr {
    SurfaceExpr::Lambda(Span::dummy(), vec![binder(name, ty)], Box::new(body))
}

/// `head args…` where `head` is an arbitrary expression, not a name.
pub(crate) fn app(head: SurfaceExpr, args: Vec<SurfaceExpr>) -> SurfaceExpr {
    if args.is_empty() {
        return head;
    }
    SurfaceExpr::App(
        Span::dummy(),
        Box::new(head),
        args.into_iter().map(SurfaceArg::positional).collect(),
    )
}

/// `e.1` / `e.2` — the `Sigma` projections a `Codata.isigmaStep` value is
/// consumed through.
pub(crate) fn proj(e: SurfaceExpr, index: u32) -> SurfaceExpr {
    SurfaceExpr::Proj(Span::dummy(), Box::new(e), Projection::Index(index))
}

/// Right-nested `Sum` over a slice (bare element for one part). Only ever
/// called on a non-empty slice; an empty one is the caller's `PEmpty.{1}`
/// case, handled before the call.
pub(crate) fn nest_sum(parts: &[SurfaceExpr]) -> SurfaceExpr {
    match parts {
        [only] => only.clone(),
        [first, rest @ ..] => plain_app("Sum", vec![first.clone(), nest_sum(rest)]),
        [] => pempty_ty(),
    }
}

/// The whole definitional tier, in dependency order.
pub(crate) fn generate(shape: &VariantShape<'_>) -> Vec<SurfaceDecl> {
    let name = shape.name;
    let g = &shape.gen_names;
    let binders: Vec<SurfaceBinder> = shape.binders.to_vec();
    let params: Vec<SurfaceExpr> = shape.binders.iter().map(|b| ident(&b.name)).collect();

    let shape_f = format!("{name}.shapeF");
    let pos_f = format!("{name}.posF");
    let tgt_f = format!("{name}.tgtF");
    let mk_step = format!("{name}.mkStep");
    let head = format!("{name}.head");
    let container = |f: &str| plain_app(f, params.clone());
    let self_ty = plain_app(name, params.clone());
    let at_params = |f: &str, extra: Vec<SurfaceExpr>| {
        let mut args = params.clone();
        args.extend(extra);
        plain_app(f, args)
    };
    // The IMIntl family at this container, partially applied (3 args) —
    // the shape of every `Codata.*` argument slot that wants the family
    // rather than a value.
    let im_family = || {
        plain_app(
            "Codata.IMIntl",
            vec![container(&shape_f), container(&pos_f), container(&tgt_f)],
        )
    };
    let container_args = || {
        vec![
            punit_ty(),
            container(&shape_f),
            container(&pos_f),
            container(&tgt_f),
            ident("PUnit.unit"),
        ]
    };

    let mut out: Vec<SurfaceDecl> = Vec::new();

    // def T.shapeF (ps) : PUnit.{1} → Type := fun _ => Sum P₁ (Sum P₂ …)
    out.push(mk_def(
        shape_f.clone(),
        binders.clone(),
        arrow(punit_ty(), type_universe()),
        lam(&["_"], shape.shape_ty.clone()),
    ));

    // def T.posF (ps) : (i : PUnit.{1}) → T.shapeF ps i → Type :=
    //   fun _ s => <the Sum.rec tag tower dispatching to Qₖ>
    out.push(mk_def(
        pos_f.clone(),
        binders.clone(),
        pi(
            "i",
            punit_ty(),
            arrow(at_params(&shape_f, vec![ident("i")]), type_universe()),
        ),
        pos_body(shape, g),
    ));

    // def T.tgtF (ps) : (i : PUnit.{1}) → (a : T.shapeF ps i) →
    //   T.posF ps i a → PUnit.{1} := fun _ _ _ => PUnit.unit
    out.push(mk_def(
        tgt_f.clone(),
        binders.clone(),
        pi(
            "i",
            punit_ty(),
            pi(
                &g.shape_arg,
                at_params(&shape_f, vec![ident("i")]),
                arrow(
                    at_params(&pos_f, vec![ident("i"), ident(&g.shape_arg)]),
                    punit_ty(),
                ),
            ),
        ),
        lam(&["_", "_", "_"], ident("PUnit.unit")),
    ));

    // def T (ps) : Type := @Codata.IMIntl PUnit.{1} … PUnit.unit
    out.push(mk_def(
        name.to_string(),
        binders.clone(),
        type_universe(),
        at_app("Codata.IMIntl", container_args()),
    ));

    // def T.mkStep (ps) (a : T.shapeF ps PUnit.unit)
    //     (f : (b : T.posF ps PUnit.unit a) →
    //          Codata.IMIntl … (T.tgtF ps PUnit.unit a b)) :
    //     Codata.isigmaStep … PUnit.unit := Sigma.mk a f
    out.push(mk_def(
        mk_step.clone(),
        {
            let mut bs = binders.clone();
            bs.push(binder(
                &g.shape_arg,
                at_params(&shape_f, vec![ident("PUnit.unit")]),
            ));
            bs.push(binder(
                &g.child_arg,
                pi(
                    &g.pos_arg,
                    at_params(&pos_f, vec![ident("PUnit.unit"), ident(&g.shape_arg)]),
                    plain_app(
                        "Codata.IMIntl",
                        vec![
                            container(&shape_f),
                            container(&pos_f),
                            container(&tgt_f),
                            at_params(
                                &tgt_f,
                                vec![ident("PUnit.unit"), ident(&g.shape_arg), ident(&g.pos_arg)],
                            ),
                        ],
                    ),
                ),
            ));
            bs
        },
        plain_app(
            "Codata.isigmaStep",
            vec![
                container(&shape_f),
                container(&pos_f),
                container(&tgt_f),
                im_family(),
                ident("PUnit.unit"),
            ],
        ),
        plain_app("Sigma.mk", vec![ident(&g.shape_arg), ident(&g.child_arg)]),
    ));

    // def T.Cₖ (ps) (args…) : T ps :=
    //   @Codata.IMmk … (T.mkStep ps <tagₖ> <child dispatch>)
    for (k, ctor) in shape.ctors.iter().enumerate() {
        out.push(mk_def(
            format!("{name}.{}", ctor.name),
            {
                let mut bs = binders.clone();
                bs.extend(ctor_binders(ctor, &self_ty));
                bs
            },
            self_ty.clone(),
            at_app("Codata.IMmk", {
                let mut args = container_args();
                args.push(at_params(
                    &mk_step,
                    vec![
                        shape.tag(k, ctor.payload_value()),
                        child_dispatch(ctor, &self_ty, g),
                    ],
                ));
                args
            }),
        ));
    }

    // def T.head (ps) (x : T ps) : T.shapeF ps PUnit.unit := @Codata.IMhead …
    out.push(mk_def(
        head.clone(),
        {
            let mut bs = binders.clone();
            bs.push(binder(&g.value_arg, self_ty.clone()));
            bs
        },
        at_params(&shape_f, vec![ident("PUnit.unit")]),
        at_app("Codata.IMhead", {
            let mut args = container_args();
            args.push(ident(&g.value_arg));
            args
        }),
    ));

    // theorem T.head_Cₖ (ps) (args…) : T.head ps (T.Cₖ ps args…) = tagₖ := rfl
    for (k, ctor) in shape.ctors.iter().enumerate() {
        out.push(mk_theorem(
            format!("{name}.head_{}", ctor.name),
            {
                let mut bs = binders.clone();
                bs.extend(ctor_binders(ctor, &self_ty));
                bs
            },
            eq(
                at_params(&head, vec![ctor_call(name, ctor, &params)]),
                shape.tag(k, ctor.payload_value()),
            ),
            ident("rfl"),
        ));
        out.extend(child_laws(shape, k, ctor, &self_ty, &params));
    }

    out.extend(corecursor_tier(shape));
    out.extend(crate::codata_variant_companions::generate(shape));
    out
}

/// VC-4 — the corecursor tier.
///
/// `T.corec` is `Codata.ucorec` at this container: a coalgebra
/// `g : (j : PUnit.{1}) → S → T.Step ps S j` and an initial state produce a
/// carrier value. `T.Step` names `Codata.isigmaStep … (Codata.uFam S)` so the
/// coalgebra's type is spelled in the codata's own vocabulary rather than the
/// seed's, and the per-constructor `T.step_Cₖ` are the CONSTRUCTORS with the
/// carrier replaced by the state — same tag, same child dispatch, over
/// `Codata.umkStep` instead of `Codata.IMmk ∘ T.mkStep`. That is why they can
/// reuse [`ctor_binders`] and [`child_dispatch`] verbatim at a different
/// target type.
///
/// The state universe is fixed: at `u = v = 0` the seed's
/// `{S : Type (max u v)}` is `Type`, so `S` is an ordinary `Type` binder and
/// the VC1 monomorphic envelope needs no level algebra here.
fn corecursor_tier(shape: &VariantShape<'_>) -> Vec<SurfaceDecl> {
    let name = shape.name;
    let g = &shape.gen_names;
    let binders: Vec<SurfaceBinder> = shape.binders.to_vec();
    let params: Vec<SurfaceExpr> = shape.binders.iter().map(|b| ident(&b.name)).collect();

    let shape_f = format!("{name}.shapeF");
    let pos_f = format!("{name}.posF");
    let tgt_f = format!("{name}.tgtF");
    let step = format!("{name}.Step");
    let corec = format!("{name}.corec");
    let head = format!("{name}.head");
    let container = |f: &str| plain_app(f, params.clone());
    let self_ty = plain_app(name, params.clone());
    let state_ty = ident(&g.state_arg);
    let at_params = |f: &str, extra: Vec<SurfaceExpr>| {
        let mut args = params.clone();
        args.extend(extra);
        plain_app(f, args)
    };

    // (S : Type) and (j : PUnit.{1}) — every declaration in this tier takes
    // both, right after the codata's own parameters.
    let state_binder = binder(&g.state_arg, type_universe());
    let index_binder = binder(&g.index_arg, punit_ty());
    let step_at = |j: SurfaceExpr| at_params(&step, vec![state_ty.clone(), j]);
    // (j : PUnit.{1}) → S → T.Step ps S j
    let coalg_ty = pi(
        &g.index_arg,
        punit_ty(),
        arrow(state_ty.clone(), step_at(ident(&g.index_arg))),
    );
    let corec_binders = || {
        let mut bs = binders.clone();
        bs.push(state_binder.clone());
        bs.push(binder(&g.coalg_arg, coalg_ty.clone()));
        bs.push(binder(&g.init_arg, state_ty.clone()));
        bs
    };
    // T.corec ps S g <state>
    let corec_call =
        |state: SurfaceExpr| at_params(&corec, vec![state_ty.clone(), ident(&g.coalg_arg), state]);
    // (g PUnit.unit s) — the one step the coalgebra takes from the initial
    // state, which is what every corec law is stated against.
    let one_step = || plain_app(&g.coalg_arg, vec![ident("PUnit.unit"), ident(&g.init_arg)]);

    let mut out: Vec<SurfaceDecl> = Vec::new();

    // def T.Step (ps) (S : Type) (j : PUnit.{1}) : Type :=
    //   Codata.isigmaStep (T.shapeF ps) (T.posF ps) (T.tgtF ps) (Codata.uFam S) j
    out.push(mk_def(
        step.clone(),
        {
            let mut bs = binders.clone();
            bs.push(state_binder.clone());
            bs.push(index_binder.clone());
            bs
        },
        type_universe(),
        plain_app(
            "Codata.isigmaStep",
            vec![
                container(&shape_f),
                container(&pos_f),
                container(&tgt_f),
                plain_app("Codata.uFam", vec![state_ty.clone()]),
                ident(&g.index_arg),
            ],
        ),
    ));

    // def T.step_Cₖ (ps) (S : Type) (j : PUnit.{1}) (args… at S) : T.Step ps S j
    for (k, ctor) in shape.ctors.iter().enumerate() {
        out.push(mk_def(
            format!("{name}.step_{}", ctor.name),
            {
                let mut bs = binders.clone();
                bs.push(state_binder.clone());
                bs.push(index_binder.clone());
                bs.extend(ctor_binders(ctor, &state_ty));
                bs
            },
            step_at(ident(&g.index_arg)),
            at_app(
                "Codata.umkStep",
                vec![
                    container(&shape_f),
                    container(&pos_f),
                    container(&tgt_f),
                    state_ty.clone(),
                    ident(&g.index_arg),
                    shape.tag(k, ctor.payload_value()),
                    child_dispatch(ctor, &state_ty, g),
                ],
            ),
        ));
    }

    // def T.corec (ps) (S : Type) (g : …) (s : S) : T ps := @Codata.ucorec …
    out.push(mk_def(
        corec.clone(),
        corec_binders(),
        self_ty.clone(),
        at_app(
            "Codata.ucorec",
            vec![
                container(&shape_f),
                container(&pos_f),
                container(&tgt_f),
                state_ty.clone(),
                ident(&g.coalg_arg),
                ident(&g.init_arg),
            ],
        ),
    ));

    // theorem T.head_corec … : T.head ps (T.corec ps S g s) = (g PUnit.unit s).1 := rfl
    out.push(mk_theorem(
        format!("{name}.head_corec"),
        corec_binders(),
        eq(
            at_params(&head, vec![corec_call(ident(&g.init_arg))]),
            proj(one_step(), 1),
        ),
        ident("rfl"),
    ));

    // theorem T.child_corec … (b : T.posF ps PUnit.unit (T.head ps (T.corec …))) :
    //   IMchild … (T.corec ps S g s) b = T.corec ps S g ((g PUnit.unit s).2 b) := rfl
    //
    // The position binder is spelled at the HEAD of the corecursion rather
    // than at `(g PUnit.unit s).1` — the two are definitionally equal, and
    // the head spelling is the one a caller can write down without unfolding
    // `T.corec`.
    out.push(mk_theorem(
        format!("{name}.child_corec"),
        {
            let mut bs = corec_binders();
            bs.push(binder(
                &g.pos_arg,
                at_params(
                    &pos_f,
                    vec![
                        ident("PUnit.unit"),
                        at_params(&head, vec![corec_call(ident(&g.init_arg))]),
                    ],
                ),
            ));
            bs
        },
        eq(
            at_app(
                "Codata.IMchild",
                vec![
                    punit_ty(),
                    container(&shape_f),
                    container(&pos_f),
                    container(&tgt_f),
                    ident("PUnit.unit"),
                    corec_call(ident(&g.init_arg)),
                    ident(&g.pos_arg),
                ],
            ),
            corec_call(app(proj(one_step(), 2), vec![ident(&g.pos_arg)])),
        ),
        ident("rfl"),
    ));

    // The per-constructor step laws: what `T.step_Cₖ` PUTS in the two slots
    // `T.head_corec`/`T.child_corec` read back out. Together they make a
    // concrete corecursion compute by `rfl` at the surface, without the
    // caller ever naming `Codata.isigmaStep`.
    for (k, ctor) in shape.ctors.iter().enumerate() {
        let step_call = || {
            let mut args = params.clone();
            args.extend([state_ty.clone(), ident(&g.index_arg)]);
            args.extend(ctor.args.iter().map(|a| ident(a.arg_name())));
            plain_app(&format!("{name}.step_{}", ctor.name), args)
        };
        let step_binders = || {
            let mut bs = binders.clone();
            bs.push(state_binder.clone());
            bs.push(index_binder.clone());
            bs.extend(ctor_binders(ctor, &state_ty));
            bs
        };
        out.push(mk_theorem(
            format!("{name}.head_step_{}", ctor.name),
            step_binders(),
            eq(proj(step_call(), 1), shape.tag(k, ctor.payload_value())),
            ident("rfl"),
        ));
        out.extend(step_child_laws(shape, k, ctor, &step_call, &step_binders));
    }

    out
}

/// The `rfl` child laws of one STEP builder: `(T.step_Cₖ …).2 <pos> = <that
/// child state>`. The same case split as [`child_laws`] — one child quantifies
/// over the whole position type, several name their own injection, none get a
/// law when there are no children.
fn step_child_laws(
    shape: &VariantShape<'_>,
    k: usize,
    ctor: &VariantCtorPlan<'_>,
    step_call: &dyn Fn() -> SurfaceExpr,
    step_binders: &dyn Fn() -> Vec<SurfaceBinder>,
) -> Vec<SurfaceDecl> {
    let name = shape.name;
    let g = &shape.gen_names;
    let params: Vec<SurfaceExpr> = shape.binders.iter().map(|b| ident(&b.name)).collect();
    let children: Vec<&ChildPlan<'_>> = ctor.children().collect();
    let m = children.len();
    let law = |extra: Vec<SurfaceBinder>, law_name: String, pos: SurfaceExpr, rhs: SurfaceExpr| {
        let mut bs = step_binders();
        bs.extend(extra);
        mk_theorem(
            law_name,
            bs,
            eq(app(proj(step_call(), 2), vec![pos]), rhs),
            ident("rfl"),
        )
    };
    let child_value = |c: &ChildPlan<'_>, pos: SurfaceExpr| match &c.family {
        Some(_) => plain_app(&c.arg_name, vec![pos]),
        None => ident(&c.arg_name),
    };
    match children.as_slice() {
        [] => Vec::new(),
        [only] => {
            let pos_ty = match &only.family {
                Some(f) => f.source.clone(),
                None => {
                    let mut args = params.clone();
                    args.extend([ident(&g.index_arg), shape.tag(k, ctor.payload_value())]);
                    plain_app(&format!("{name}.posF"), args)
                }
            };
            vec![law(
                vec![binder(&g.pos_arg, pos_ty)],
                format!("{name}.child_step_{}", ctor.name),
                ident(&g.pos_arg),
                child_value(only, ident(&g.pos_arg)),
            )]
        }
        _ => children
            .iter()
            .enumerate()
            .map(|(i, c)| {
                let (extra, point) = match &c.family {
                    Some(f) => (
                        vec![binder(&g.pos_arg, f.source.clone())],
                        ident(&g.pos_arg),
                    ),
                    None => (Vec::new(), ident("PUnit.unit")),
                };
                law(
                    extra,
                    format!("{name}.child_step_{}_{i}", ctor.name),
                    inject_sum(i, m, point.clone()),
                    child_value(c, point),
                )
            })
            .collect(),
    }
}

/// The generated constructor's binder list (parameters excluded).
pub(crate) fn ctor_binders(
    ctor: &VariantCtorPlan<'_>,
    self_ty: &SurfaceExpr,
) -> Vec<SurfaceBinder> {
    ctor.args
        .iter()
        .map(|a| match a {
            ArgPlan::Payload(p) => binder(&p.arg_name, p.ty.clone()),
            ArgPlan::Child(c) => binder(
                &c.arg_name,
                match &c.family {
                    Some(f) => arrow(f.source.clone(), self_ty.clone()),
                    None => self_ty.clone(),
                },
            ),
        })
        .collect()
}

/// `T.Cₖ ps args…`
pub(crate) fn ctor_call(
    name: &str,
    ctor: &VariantCtorPlan<'_>,
    params: &[SurfaceExpr],
) -> SurfaceExpr {
    let mut args = params.to_vec();
    args.extend(ctor.args.iter().map(|a| ident(a.arg_name())));
    plain_app(&format!("{name}.{}", ctor.name), args)
}

/// `posF`'s body: `fun _ s => …`.
///
/// With ONE constructor there is no tag to dispatch on and the body is
/// `Q₁` directly — the record lane's `fun _ _ => pos_ty(m)` whenever `Q₁`
/// happens not to mention the shape, which for a record it never does.
fn pos_body(shape: &VariantShape<'_>, g: &GenNames) -> SurfaceExpr {
    let n = shape.ctors.len();
    if n == 1 {
        let ctor = &shape.ctors[0];
        return SurfaceExpr::Lambda(
            Span::dummy(),
            vec![
                SurfaceBinder::new("_", None, SurfaceBinderInfo::Explicit),
                SurfaceBinder::new(&ctor.shape_var, None, SurfaceBinderInfo::Explicit),
            ],
            Box::new(ctor.pos_ty_in_shape.clone()),
        );
    }
    SurfaceExpr::Lambda(
        Span::dummy(),
        vec![
            SurfaceBinder::new("_", None, SurfaceBinderInfo::Explicit),
            SurfaceBinder::new(&g.scruts[0], None, SurfaceBinderInfo::Explicit),
        ],
        Box::new(tag_tower(
            shape,
            &lam(&["_"], type_universe()),
            &|_, c| lam_one(&c.shape_var, c.pos_ty_in_shape.clone()),
            0,
        )),
    )
}

/// The `Sum.rec` tower over the constructor TAG, from constructor `idx` on,
/// scrutinising `g.scruts[idx]`.
///
/// `motive` is the eliminator's motive and `branch(k, ctor)` the VALUE of
/// constructor `k`'s branch — a function of that constructor's payload. Three
/// generated families are this same tower under three motives: `posF`'s
/// position dispatch (`Type`, VC-3), the per-constructor head classifiers
/// (`Prop`, VC-5) and the payload retractions (`Pₖ`, VC-5). Keeping one
/// spelling means a tag-numbering change cannot desynchronise them.
pub(crate) fn tag_tower(
    shape: &VariantShape<'_>,
    motive: &SurfaceExpr,
    branch: &dyn Fn(usize, &VariantCtorPlan<'_>) -> SurfaceExpr,
    idx: usize,
) -> SurfaceExpr {
    let g = &shape.gen_names;
    let n = shape.ctors.len();
    let rest_ty = nest_sum(
        &shape.ctors[idx + 1..]
            .iter()
            .map(|c| c.payload_ty.clone())
            .collect::<Vec<_>>(),
    );
    let rest_branch = if idx + 2 == n {
        branch(idx + 1, &shape.ctors[idx + 1])
    } else {
        lam_one(
            &g.scruts[idx + 1],
            tag_tower(shape, motive, branch, idx + 1),
        )
    };
    at_app(
        "Sum.rec",
        vec![
            shape.ctors[idx].payload_ty.clone(),
            rest_ty,
            motive.clone(),
            branch(idx, &shape.ctors[idx]),
            rest_branch,
            ident(&g.scruts[idx]),
        ],
    )
}

/// The constructor's child function: `(b : Qₖ) → T ps`, dispatching each
/// position to the argument that owns it.
fn child_dispatch(ctor: &VariantCtorPlan<'_>, self_ty: &SurfaceExpr, g: &GenNames) -> SurfaceExpr {
    let children: Vec<&ChildPlan<'_>> = ctor.children().collect();
    // A branch VALUE for one child: a bare child ignores the position, a
    // family child IS the function from it.
    let branch = |c: &ChildPlan<'_>| match &c.family {
        Some(_) => ident(&c.arg_name),
        None => lam(&["_"], ident(&c.arg_name)),
    };
    match children.as_slice() {
        // No children: the position type is `PEmpty.{1}`, so the function
        // is the empty eliminator. (`Ret`.)
        [] => lam_one(
            &g.pos_arg,
            at_app(
                "PEmpty.rec",
                vec![lam(&["_"], self_ty.clone()), ident(&g.pos_arg)],
            ),
        ),
        [only] => branch(only),
        _ => lam_one(
            &g.pos_arg,
            child_tower(&children, self_ty, g, 0, ident(&g.pos_arg)),
        ),
    }
}

/// `Sum.rec` over the child positions, from child `idx` on.
fn child_tower(
    children: &[&ChildPlan<'_>],
    self_ty: &SurfaceExpr,
    g: &GenNames,
    idx: usize,
    scrut: SurfaceExpr,
) -> SurfaceExpr {
    let m = children.len();
    let branch = |c: &ChildPlan<'_>| match &c.family {
        Some(_) => ident(&c.arg_name),
        None => lam(&["_"], ident(&c.arg_name)),
    };
    let rest_ty = nest_sum(
        &children[idx + 1..]
            .iter()
            .map(|c| c.domain_in_args())
            .collect::<Vec<_>>(),
    );
    let rest_branch = if idx + 2 == m {
        branch(children[idx + 1])
    } else {
        lam_one(
            &g.scruts[idx + 1],
            child_tower(children, self_ty, g, idx + 1, ident(&g.scruts[idx + 1])),
        )
    };
    at_app(
        "Sum.rec",
        vec![
            children[idx].domain_in_args(),
            rest_ty,
            lam(&["_"], self_ty.clone()),
            branch(children[idx]),
            rest_branch,
            scrut,
        ],
    )
}

/// The `rfl` child laws of one constructor: `IMchild … (T.Cₖ …) <pos> =
/// <that child>`.
///
/// With exactly one child the position type is the child's own domain, so
/// the law can quantify over ALL of it (`∀ b, child … b = k b`) — the
/// stronger statement, and the one `data/variant_codata/itree_target.lean`
/// records for `Tau` and `Vis`. With several children each law names its
/// own injection instead, because the value genuinely differs per position.
fn child_laws(
    shape: &VariantShape<'_>,
    k: usize,
    ctor: &VariantCtorPlan<'_>,
    self_ty: &SurfaceExpr,
    params: &[SurfaceExpr],
) -> Vec<SurfaceDecl> {
    let name = shape.name;
    let g = &shape.gen_names;
    let children: Vec<&ChildPlan<'_>> = ctor.children().collect();
    let m = children.len();
    let im_child = |extra_binders: Vec<SurfaceBinder>,
                    law_name: String,
                    pos: SurfaceExpr,
                    rhs: SurfaceExpr| {
        let mut bs = shape.binders.to_vec();
        bs.extend(ctor_binders(ctor, self_ty));
        bs.extend(extra_binders);
        mk_theorem(
            law_name,
            bs,
            eq(
                at_app("Codata.IMchild", {
                    let mut args = vec![
                        punit_ty(),
                        plain_app(&format!("{name}.shapeF"), params.to_vec()),
                        plain_app(&format!("{name}.posF"), params.to_vec()),
                        plain_app(&format!("{name}.tgtF"), params.to_vec()),
                        ident("PUnit.unit"),
                    ];
                    args.push(ctor_call(name, ctor, params));
                    args.push(pos);
                    args
                }),
                rhs,
            ),
            ident("rfl"),
        )
    };
    let child_value = |c: &ChildPlan<'_>, pos: SurfaceExpr| match &c.family {
        Some(_) => plain_app(&c.arg_name, vec![pos]),
        None => ident(&c.arg_name),
    };
    match children.as_slice() {
        [] => Vec::new(),
        [only] => {
            // The position type: the family's own domain when there is one,
            // else `posF ps PUnit.unit tagₖ` — which reduces to `PUnit.{1}`
            // but says WHERE the position came from.
            let pos_ty = match &only.family {
                Some(f) => f.source.clone(),
                None => {
                    let mut args = params.to_vec();
                    args.extend([ident("PUnit.unit"), shape.tag(k, ctor.payload_value())]);
                    plain_app(&format!("{name}.posF"), args)
                }
            };
            vec![im_child(
                vec![binder(&g.pos_arg, pos_ty)],
                format!("{name}.child_{}", ctor.name),
                ident(&g.pos_arg),
                child_value(only, ident(&g.pos_arg)),
            )]
        }
        _ => children
            .iter()
            .enumerate()
            .map(|(i, c)| {
                let (extra, point) = match &c.family {
                    Some(f) => (
                        vec![binder(&g.pos_arg, f.source.clone())],
                        ident(&g.pos_arg),
                    ),
                    None => (Vec::new(), ident("PUnit.unit")),
                };
                let pos = inject_sum(i, m, point.clone());
                im_child(
                    extra,
                    format!("{name}.child_{}_{i}", ctor.name),
                    pos,
                    child_value(c, point),
                )
            })
            .collect(),
    }
}
