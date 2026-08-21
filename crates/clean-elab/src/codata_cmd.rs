// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The `codata` command (R3.2 of `designs/2026-08-06-indexed-m-codata.md`):
//! Rocq-style Type-level codata as an observation record, elaborated to the
//! indexed-container M-type encoding — no kernel cofix, no new `ExprKind`,
//! no new reduction rule, zero new axioms.
//!
//! ```text
//! codata Stream (A : Type) where
//!   head : A
//!   tail : Stream A
//! ```
//!
//! generates (all through the ordinary parse→elaborate→kernel-check path,
//! against the lazy `Codata.*` seed library — see [`crate::codata_seed`]):
//!
//! ```text
//! Stream.shapeF/posF/tgtF   the I := Unit container of the record
//! Stream                    Codata.IMIntl … Unit.unit
//! Stream.head               Codata.IMhead (the observation)
//! Stream.tail               Codata.IMchild (the step)
//! Stream.corecStep/corec    Codata.ucorec (the corecursor)
//! Stream.head_corec         rfl computation law
//! Stream.tail_corec         rfl computation law
//! ```
//!
//! Every generated shape is pinned by the hand-elaborated probe battery in
//! the graduation lane (the `@`-explicit spellings and the `uFam`/`umkStep`
//! wrappers are load-bearing — see the battery lessons in
//! `data/graduation/clean-mtype/proof/MTypeIndexed.lean`).
//!
//! **Envelope (loud rejects, extend-don't-descope):** one or more
//! non-recursive observation fields followed by exactly one recursive
//! field (last) at the same instantiation — multi-observation labels are
//! right-nested `PProd`s with projection-chain accessors.
//!
//! CORRECTED 2026-08-14: this used to say "branching (multiple recursive
//! fields) is a named build item", i.e. unsupported. MEASURED FALSE — a
//! two-recursive-field codata elaborates and COMPUTES:
//!
//! ```lean
//! codata BTree2 : Type where
//!   label : Nat
//!   left  : BTree2
//!   right : BTree2
//! codef mkT2 (n : Nat) : BTree2 where
//!   label := n
//!   left  := mkT2 (n + 1)
//!   right := mkT2 (n + 2)
//! theorem t2 : BTree2.label (mkT2 5) = 5 := rfl   -- passes
//! ```
//!
//! A doc that understates the envelope is not harmless: it sends the next
//! author to build something that already works. Simple explicit
//! `(x : T)` parameters; no universe parameters (U2 lane); no `deriving`
//! (BEq/DecidableEq/Repr on M-encoded codata must reject loudly per the
//! design); no modifiers.

use crate::codata_seed::ensure_codata_seeds;
use crate::{ElabError, ElabResult, RegisteredElabResult};
use clean_kernel::Environment;
use clean_parser::{
    DeclModifiers, LevelExpr, Projection, Span, SurfaceArg, SurfaceBinder, SurfaceBinderInfo,
    SurfaceDecl, SurfaceExpr, SurfaceField, TerminationHints, UniverseExpr,
};

fn unsupported(msg: impl Into<String>) -> ElabError {
    ElabError::Unsupported {
        feature: msg.into(),
    }
}

/// `PUnit.{1}` with the level PINNED. Generated monomorphic code mentions
/// the index/tag unit type MANY times (tag towers, motives, binders); a
/// bare `PUnit` mints an independent fresh level meta per mention, and in
/// nested `Sum.rec` dependent-motive positions some stay unconstrained —
/// the 3-member Σ-tag tower failed exactly there once the seeds went
/// polymorphic. Pinning `.{1}` (= Lean `Unit`) makes generated code
/// byte-deterministic again; ctor VALUES (`PUnit.unit`) stay bare and
/// solve from these pinned types.
fn punit_ty() -> SurfaceExpr {
    SurfaceExpr::UniverseInst(
        Span::dummy(),
        Box::new(ident("PUnit")),
        vec![LevelExpr::Lit(1)],
    )
}

/// `Type` or `Type u` — the result-sort/state-sort for generated code,
/// polymorphic when the codata declares `.{u}` (U2 rung 7 part 2).
fn type_u(poly: Option<&str>) -> SurfaceExpr {
    match poly {
        Some(u) => SurfaceExpr::Universe(
            Span::dummy(),
            UniverseExpr::TypeLevel(Box::new(LevelExpr::Param(u.to_string()))),
        ),
        None => type_universe(),
    }
}

/// `PUnit.{1}` (mono) or `PUnit.{u+1}` (polymorphic): the container
/// index/tag unit at the level matching `Type`/`Type u` families.
fn punit_ty_p(poly: Option<&str>) -> SurfaceExpr {
    match poly {
        Some(u) => SurfaceExpr::UniverseInst(
            Span::dummy(),
            Box::new(ident("PUnit")),
            vec![LevelExpr::Succ(Box::new(LevelExpr::Param(u.to_string())))],
        ),
        None => punit_ty(),
    }
}

/// Stamp the declared universe params onto a generated def/theorem.
fn set_uparams(mut decl: SurfaceDecl, poly: Option<&str>) -> SurfaceDecl {
    if let Some(u) = poly {
        match &mut decl {
            SurfaceDecl::Def {
                universe_params, ..
            }
            | SurfaceDecl::Theorem {
                universe_params, ..
            } => *universe_params = vec![u.to_string()],
            _ => {}
        }
    }
    decl
}

fn ident(name: &str) -> SurfaceExpr {
    SurfaceExpr::Ident(Span::dummy(), name.to_string())
}

/// `@name args…` — Explicit-marked head, positional args.
fn at_app(name: &str, args: Vec<SurfaceExpr>) -> SurfaceExpr {
    let head = SurfaceExpr::Explicit(Span::dummy(), Box::new(ident(name)));
    if args.is_empty() {
        return head;
    }
    SurfaceExpr::App(
        Span::dummy(),
        Box::new(head),
        args.into_iter().map(SurfaceArg::positional).collect(),
    )
}

/// `name args…` — plain application (no @).
fn plain_app(name: &str, args: Vec<SurfaceExpr>) -> SurfaceExpr {
    if args.is_empty() {
        return ident(name);
    }
    SurfaceExpr::App(
        Span::dummy(),
        Box::new(ident(name)),
        args.into_iter().map(SurfaceArg::positional).collect(),
    )
}

/// `fun b1 b2 … => body` with untyped binders.
fn lam(names: &[&str], body: SurfaceExpr) -> SurfaceExpr {
    SurfaceExpr::Lambda(
        Span::dummy(),
        names
            .iter()
            .map(|n| SurfaceBinder::new(*n, None, SurfaceBinderInfo::Explicit))
            .collect(),
        Box::new(body),
    )
}

/// `(name : ty) → body` (dependent) — a one-binder Pi.
fn pi(name: &str, ty: SurfaceExpr, body: SurfaceExpr) -> SurfaceExpr {
    SurfaceExpr::Pi(
        Span::dummy(),
        vec![SurfaceBinder::new(
            name,
            Some(ty),
            SurfaceBinderInfo::Explicit,
        )],
        Box::new(body),
    )
}

/// `a → b` (non-dependent arrow).
fn arrow(a: SurfaceExpr, b: SurfaceExpr) -> SurfaceExpr {
    SurfaceExpr::Arrow(Span::dummy(), Box::new(a), Box::new(b))
}

fn type_universe() -> SurfaceExpr {
    SurfaceExpr::Universe(Span::dummy(), UniverseExpr::Type)
}

fn mk_def(
    name: String,
    binders: Vec<SurfaceBinder>,
    ty: SurfaceExpr,
    val: SurfaceExpr,
) -> SurfaceDecl {
    SurfaceDecl::Def {
        span: Span::dummy(),
        name,
        universe_params: Vec::new(),
        binders,
        ty: Some(Box::new(ty)),
        val: Box::new(val),
        attrs: Vec::new(),
        termination: TerminationHints::default(),
        modifiers: DeclModifiers::default(),
        where_decls: Vec::new(),
    }
}

fn mk_theorem(
    name: String,
    binders: Vec<SurfaceBinder>,
    ty: SurfaceExpr,
    proof: SurfaceExpr,
) -> SurfaceDecl {
    SurfaceDecl::Theorem {
        span: Span::dummy(),
        name,
        universe_params: Vec::new(),
        binders,
        ty: Box::new(ty),
        proof: Box::new(proof),
        attrs: Vec::new(),
        termination: TerminationHints::default(),
        modifiers: DeclModifiers::default(),
        where_decls: Vec::new(),
    }
}

/// Does `expr` mention the identifier `name` (exactly, or as a dotted
/// prefix `name.…`)? Conservative surface walk for self-reference checks.
fn mentions(expr: &SurfaceExpr, name: &str) -> bool {
    let mut found = false;
    walk(expr, &mut |e| {
        if let SurfaceExpr::Ident(_, id) = e {
            if id == name || id.starts_with(&format!("{name}.")) {
                found = true;
            }
        }
    });
    found
}

fn walk(expr: &SurfaceExpr, f: &mut impl FnMut(&SurfaceExpr)) {
    f(expr);
    match expr {
        SurfaceExpr::App(_, h, args) => {
            walk(h, f);
            for a in args {
                walk(&a.expr, f);
            }
        }
        SurfaceExpr::Lambda(_, bs, b)
        | SurfaceExpr::PatternMatchLambda(_, bs, b)
        | SurfaceExpr::Pi(_, bs, b) => {
            for binder in bs {
                if let Some(t) = &binder.ty {
                    walk(t, f);
                }
            }
            walk(b, f);
        }
        SurfaceExpr::Arrow(_, a, b) => {
            walk(a, f);
            walk(b, f);
        }
        SurfaceExpr::Paren(_, e)
        | SurfaceExpr::Explicit(_, e)
        | SurfaceExpr::OutParam(_, e)
        | SurfaceExpr::SemiOutParam(_, e) => walk(e, f),
        SurfaceExpr::Ascription(_, e, t) => {
            walk(e, f);
            walk(t, f);
        }
        _ => {}
    }
}

/// The validated shape of a `codata` declaration: N observations, then
/// M trailing recursive step fields.
struct CodataShape<'a> {
    name: &'a str,
    /// The single declared universe parameter, when polymorphic (v1: ≤1).
    poly: Option<&'a str>,
    binders: &'a [SurfaceBinder],
    obs: Vec<(&'a str, &'a SurfaceExpr)>,
    steps: Vec<&'a str>,
}

fn validate<'a>(
    name: &'a str,
    universe_params: &'a [String],
    binders: &'a [SurfaceBinder],
    ty: &Option<Box<SurfaceExpr>>,
    fields: &'a [SurfaceField],
    deriving: &[String],
    modifiers: &DeclModifiers,
) -> Result<CodataShape<'a>, ElabError> {
    let poly = match universe_params {
        [] => None,
        [u] => Some(u.as_str()),
        _ => {
            return Err(unsupported(
                "codata: at most ONE universe parameter is supported in v1 \
                 (`codata C.{u} …`); multi-parameter polymorphic codata is a \
                 later lane",
            ))
        }
    };
    if !deriving.is_empty() {
        return Err(unsupported(format!(
            "codata: deriving {} is rejected — BEq/DecidableEq/Repr have no \
             sound derivation for M-encoded codata (potentially infinite \
             values); this is a deliberate loud reject, not an omission",
            deriving.join(", ")
        )));
    }
    if !modifiers.is_default() {
        return Err(unsupported(
            "codata: declaration modifiers (private/partial/noncomputable/…) \
             are not supported yet",
        ));
    }
    if let Some(t) = ty {
        let sort_ok = match t.as_ref() {
            SurfaceExpr::Universe(_, UniverseExpr::Type) => true,
            SurfaceExpr::Universe(_, UniverseExpr::TypeLevel(l)) => {
                matches!((l.as_ref(), poly), (LevelExpr::Param(n), Some(u)) if n == u)
            }
            _ => false,
        };
        if !sort_ok {
            return Err(unsupported(
                "codata: the result sort must be `Type` (or `Type u` matching \
                 the declared universe parameter); Prop-valued codata is a \
                 separate lane",
            ));
        }
    }
    for b in binders {
        if b.info != SurfaceBinderInfo::Explicit || b.ty.is_none() || b.default.is_some() {
            return Err(unsupported(
                "codata: parameters must be simple explicit binders `(x : T)` \
                 in v1",
            ));
        }
    }
    if fields.len() < 2 {
        return Err(unsupported(format!(
            "codata needs at least one observation field followed by at \
             least one recursive step field; got {} field(s)",
            fields.len()
        )));
    }
    // Split at the trailing block of recursive fields (each exactly the
    // codata type at its own parameters).
    let expected_args: Vec<&str> = binders.iter().map(|b| b.name.as_str()).collect();
    let mut split = fields.len();
    while split > 0 && is_self_at_params(&fields[split - 1].ty, name, &expected_args) {
        split -= 1;
    }
    let (obs_fields, step_fields) = fields.split_at(split);
    if step_fields.is_empty() {
        return Err(unsupported(
            "codata: the final field must be recursive (the codata type at \
             its own parameters) — a codata with no recursive field is just \
             a record",
        ));
    }
    if obs_fields.is_empty() {
        return Err(unsupported(
            "codata needs at least one observation field before the \
             recursive fields",
        ));
    }
    for obs in obs_fields {
        if mentions(&obs.ty, name) {
            return Err(unsupported(format!(
                "codata: observation field `{}` must be non-recursive (it \
                 mentions `{name}`) — recursive fields must form the TRAILING \
                 block, each exactly `{name}` at its own parameters",
                obs.name
            )));
        }
    }
    let mut seen: Vec<&str> = Vec::new();
    for f in fields {
        if seen.contains(&f.name.as_str()) {
            return Err(unsupported("codata: field names must be distinct"));
        }
        seen.push(&f.name);
        for reserved in [
            "shapeF",
            "posF",
            "tgtF",
            "corecStep",
            "corec",
            "mk",
            "mkStep",
        ] {
            if f.name == reserved {
                return Err(unsupported(format!(
                    "codata: field name `{reserved}` collides with a generated \
                     companion definition"
                )));
            }
        }
    }
    Ok(CodataShape {
        name,
        poly,
        binders,
        obs: obs_fields
            .iter()
            .map(|f| (f.name.as_str(), &f.ty))
            .collect(),
        steps: step_fields.iter().map(|f| f.name.as_str()).collect(),
    })
}

/// Is `expr` exactly `head p1 … pk` (modulo parens) with the given
/// identifier arguments in order?
fn is_self_at_params(expr: &SurfaceExpr, head: &str, params: &[&str]) -> bool {
    let expr = strip_parens(expr);
    if params.is_empty() {
        return matches!(expr, SurfaceExpr::Ident(_, id) if id == head);
    }
    let SurfaceExpr::App(_, h, args) = expr else {
        return false;
    };
    if !matches!(strip_parens(h), SurfaceExpr::Ident(_, id) if id == head) {
        return false;
    }
    if args.len() != params.len() {
        return false;
    }
    args.iter().zip(params).all(|(a, p)| {
        a.name.is_none() && matches!(strip_parens(&a.expr), SurfaceExpr::Ident(_, id) if id == p)
    })
}

fn strip_parens(expr: &SurfaceExpr) -> &SurfaceExpr {
    match expr {
        SurfaceExpr::Paren(_, e) => strip_parens(e),
        _ => expr,
    }
}

/// Elaborate a `codata` declaration: seed the `Codata.*` library on first
/// use, then generate and kernel-check the container, the type, the
/// observation/step accessors, the corecursor, and the `rfl` computation
/// laws. Transactional: a failure anywhere leaves `env` untouched.
pub(crate) fn elab_codata_decl(
    env: &mut Environment,
    decl: &SurfaceDecl,
) -> Result<RegisteredElabResult, ElabError> {
    let SurfaceDecl::Codata {
        name,
        universe_params,
        binders,
        ty,
        fields,
        deriving,
        modifiers,
        ..
    } = decl
    else {
        return Err(unsupported("elab_codata_decl: not a codata declaration"));
    };
    // Indexed form: `codata C : (n : I) → Type where …` — the
    // source-index answer (the container index IS the user's index).
    if let Some(t) = ty {
        // Collect the index telescope, flattening nested Pis
        // (`(r : Nat) → (c : Nat) → Type` may parse as nested one-binder
        // Pis).
        let mut flat_binders: Vec<SurfaceBinder> = Vec::new();
        let mut body = strip_parens(t);
        while let SurfaceExpr::Pi(_, pib, pibody) = body {
            flat_binders.extend(pib.iter().cloned());
            body = strip_parens(pibody);
        }
        let body_is_type_sort = match body {
            SurfaceExpr::Universe(_, UniverseExpr::Type) => true,
            SurfaceExpr::Universe(_, UniverseExpr::TypeLevel(l)) => matches!(
                (l.as_ref(), universe_params.as_slice()),
                (LevelExpr::Param(n), [u]) if n == u
            ),
            _ => false,
        };
        if !flat_binders.is_empty() && body_is_type_sort {
            {
                let ishape = validate_indexed(
                    name,
                    universe_params,
                    binders,
                    &flat_binders,
                    fields,
                    deriving,
                    modifiers,
                )?;
                let mut candidate = env.clone();
                ensure_codata_seeds(&mut candidate)?;
                let gen_decls = if ishape.idx_binders.len() > 1 {
                    generate_multi_indexed(&ishape)
                } else {
                    generate_indexed(&ishape)
                };
                for (i, generated) in gen_decls.into_iter().enumerate() {
                    crate::elaborate_decl_and_register(&mut candidate, &generated).map_err(
                        |e| {
                            unsupported(format!(
                                "indexed codata `{name}`: generated declaration {i} \
                                 failed to elaborate/kernel-check (env left \
                                 untouched): {e:?}"
                            ))
                        },
                    )?;
                }
                // Mark the carrier as GENERATED by this command, so
                // recognition can require provenance rather than accepting any
                // type that merely owns a `<C>.corec`. Into the candidate, so a
                // codata whose generated declarations failed leaves no mark.
                candidate.mark_codata_carrier(clean_kernel::Name::from_string(name));
                *env = candidate;
                return Ok(RegisteredElabResult {
                    result: ElabResult::Skipped,
                    warning: None,
                    hole_contexts: Vec::new(),
                });
            }
        }
    }
    let shape = validate(
        name,
        universe_params,
        binders,
        ty,
        fields,
        deriving,
        modifiers,
    )?;

    let mut candidate = env.clone();
    ensure_codata_seeds(&mut candidate)?;

    for (i, generated) in generate(&shape).into_iter().enumerate() {
        crate::elaborate_decl_and_register(&mut candidate, &generated).map_err(|e| {
            unsupported(format!(
                "codata `{name}`: generated declaration {i} failed to \
                 elaborate/kernel-check (env left untouched): {e:?}"
            ))
        })?;
    }
    // Same carrier provenance mark as the indexed lane above.
    candidate.mark_codata_carrier(clean_kernel::Name::from_string(name));
    *env = candidate;
    Ok(RegisteredElabResult {
        result: ElabResult::Skipped,
        warning: None,
        hole_contexts: Vec::new(),
    })
}

/// Build the generated declarations, mirroring the hand-validated probe
/// battery byte-for-shape (`@`-explicit heads throughout). For k
/// observations the label is the right-nested `PProd` of their types
/// (bare type when k = 1), and each accessor is a projection chain off
/// `Codata.IMhead`.
fn generate(shape: &CodataShape<'_>) -> Vec<SurfaceDecl> {
    let CodataShape {
        name,
        poly,
        binders,
        obs,
        steps,
    } = shape;
    let poly = *poly;
    let params: Vec<SurfaceExpr> = binders.iter().map(|b| ident(&b.name)).collect();
    let explicit_binders: Vec<SurfaceBinder> = binders.to_vec();
    let implicit_binders: Vec<SurfaceBinder> = binders
        .iter()
        .map(|b| {
            let mut ib = b.clone();
            ib.info = SurfaceBinderInfo::Implicit;
            ib
        })
        .collect();

    let shape_f = format!("{name}.shapeF");
    let pos_f = format!("{name}.posF");
    let tgt_f = format!("{name}.tgtF");
    let container = |f: &str| plain_app(f, params.clone());
    let self_ty = plain_app(name, params.clone());
    let corec_step = format!("{name}.corecStep");
    let corec = format!("{name}.corec");

    // The label type: right-nested PProd of the observation types.
    let label_ty = obs
        .iter()
        .rev()
        .map(|(_, t)| (*t).clone())
        .reduce(|acc, t| plain_app("PProd", vec![t, acc]))
        .expect("validate guarantees at least one observation");
    // The packed label from per-observation values.
    fn pack(vals: &[SurfaceExpr]) -> SurfaceExpr {
        match vals {
            [only] => only.clone(),
            [first, rest @ ..] => plain_app("PProd.mk", vec![first.clone(), pack(rest)]),
            [] => unreachable!("validate guarantees at least one observation"),
        }
    }
    // The position type for m recursive fields: Unit for one, a
    // right-nested Sum of Units for more.
    fn pos_ty(m: usize, poly: Option<&str>) -> SurfaceExpr {
        if m == 1 {
            punit_ty_p(poly)
        } else {
            plain_app("Sum", vec![punit_ty_p(poly), pos_ty(m - 1, poly)])
        }
    }
    // The i-th position point out of m.
    fn pos_point(i: usize, m: usize) -> SurfaceExpr {
        if m == 1 {
            ident("PUnit.unit")
        } else if i == 0 {
            plain_app("Sum.inl", vec![ident("PUnit.unit")])
        } else {
            plain_app("Sum.inr", vec![pos_point(i - 1, m - 1)])
        }
    }
    // The coalgebra child function over the position type: selects the
    // i-th step function's next state.
    fn child_fn(step_apps: &[SurfaceExpr], poly: Option<&str>) -> SurfaceExpr {
        match step_apps {
            [only] => lam(&["_"], only.clone()),
            [first, rest @ ..] => {
                let inner = match rest {
                    [only] => lam(&["_"], only.clone()),
                    _ => child_fn(rest, poly),
                };
                SurfaceExpr::Lambda(
                    Span::dummy(),
                    vec![SurfaceBinder::new("b", None, SurfaceBinderInfo::Explicit)],
                    Box::new(SurfaceExpr::App(
                        Span::dummy(),
                        Box::new(SurfaceExpr::Explicit(
                            Span::dummy(),
                            Box::new(ident("Sum.rec")),
                        )),
                        vec![
                            SurfaceArg::positional(punit_ty_p(poly)),
                            SurfaceArg::positional(pos_ty(rest.len(), poly)),
                            SurfaceArg::positional(lam(&["_"], ident("S"))),
                            SurfaceArg::positional(lam(&["_"], first.clone())),
                            SurfaceArg::positional(inner),
                            SurfaceArg::positional(ident("b")),
                        ],
                    )),
                )
            }
            [] => unreachable!("validate guarantees at least one recursive field"),
        }
    }

    // Projection chain selecting observation i out of k.
    fn select(base: SurfaceExpr, i: usize, k: usize) -> SurfaceExpr {
        let mut e = base;
        for _ in 0..i {
            e = SurfaceExpr::Proj(Span::dummy(), Box::new(e), Projection::Index(2));
        }
        if i + 1 < k {
            e = SurfaceExpr::Proj(Span::dummy(), Box::new(e), Projection::Index(1));
        }
        e
    }

    let s_binder = SurfaceBinder::new("S", Some(type_u(poly)), SurfaceBinderInfo::Implicit);
    let obs_f_names: Vec<String> = obs.iter().map(|(n, _)| format!("{n}F")).collect();
    let step_f_names: Vec<String> = steps.iter().map(|n| format!("{n}F")).collect();
    let mut corec_fn_binders: Vec<SurfaceBinder> = obs
        .iter()
        .zip(&obs_f_names)
        .map(|((_, t), fname)| {
            SurfaceBinder::new(
                fname.as_str(),
                Some(arrow(ident("S"), (*t).clone())),
                SurfaceBinderInfo::Explicit,
            )
        })
        .collect();
    for step_f in &step_f_names {
        corec_fn_binders.push(SurfaceBinder::new(
            step_f.as_str(),
            Some(arrow(ident("S"), ident("S"))),
            SurfaceBinderInfo::Explicit,
        ));
    }

    // @C.corec <ps> S obsF… stepF <extra> — reused by the law statements.
    let corec_call = |extra: SurfaceExpr| {
        let mut args = params.clone();
        args.push(ident("S"));
        args.extend(obs_f_names.iter().map(|n| ident(n)));
        args.extend(step_f_names.iter().map(|n| ident(n)));
        args.push(extra);
        at_app(&corec, args)
    };
    let head_call = |x: SurfaceExpr| {
        at_app(
            "Codata.IMhead",
            vec![
                punit_ty_p(poly),
                container(&shape_f),
                container(&pos_f),
                container(&tgt_f),
                ident("PUnit.unit"),
                x,
            ],
        )
    };

    let mut out = vec![
        // def C.shapeF (ps) : Unit → Type := fun _ => <label>
        mk_def(
            shape_f.clone(),
            explicit_binders.clone(),
            arrow(punit_ty_p(poly), type_u(poly)),
            lam(&["_"], label_ty),
        ),
        // def C.posF (ps) : (i : Unit) → C.shapeF ps i → Type := fun _ _ => Unit
        mk_def(
            pos_f.clone(),
            explicit_binders.clone(),
            pi("i", punit_ty_p(poly), {
                let mut args = params.clone();
                args.push(ident("i"));
                arrow(plain_app(&shape_f, args), type_u(poly))
            }),
            lam(&["_", "_"], pos_ty(steps.len(), poly)),
        ),
        // def C.tgtF (ps) :
        //   (i : Unit) → (a : C.shapeF ps i) → C.posF ps i a → Unit :=
        //   fun _ _ _ => Unit.unit
        mk_def(
            tgt_f.clone(),
            explicit_binders.clone(),
            pi("i", punit_ty_p(poly), {
                let mut shape_args = params.clone();
                shape_args.push(ident("i"));
                pi("a", plain_app(&shape_f, shape_args), {
                    let mut pos_args = params.clone();
                    pos_args.extend([ident("i"), ident("a")]);
                    arrow(plain_app(&pos_f, pos_args), punit_ty_p(poly))
                })
            }),
            lam(&["_", "_", "_"], ident("PUnit.unit")),
        ),
        // def C (ps) : Type := @Codata.IMIntl Unit … Unit.unit
        mk_def(
            (*name).to_string(),
            explicit_binders.clone(),
            type_u(poly),
            at_app(
                "Codata.IMIntl",
                vec![
                    punit_ty_p(poly),
                    container(&shape_f),
                    container(&pos_f),
                    container(&tgt_f),
                    ident("PUnit.unit"),
                ],
            ),
        ),
    ];

    // Observation accessors: def C.obs_i {ps} (x : C ps) : T_i := <proj chain>
    let k = obs.len();
    for (i, (obs_name, obs_ty)) in obs.iter().enumerate() {
        out.push(mk_def(
            format!("{name}.{obs_name}"),
            {
                let mut bs = implicit_binders.clone();
                bs.push(SurfaceBinder::new(
                    "x",
                    Some(self_ty.clone()),
                    SurfaceBinderInfo::Explicit,
                ));
                bs
            },
            (*obs_ty).clone(),
            select(head_call(ident("x")), i, k),
        ));
    }

    // Recursive accessors: def C.step_i {ps} (x : C ps) : C ps :=
    //   @Codata.IMchild … x <point_i>
    let m = steps.len();
    for (i, step_name) in steps.iter().enumerate() {
        out.push(mk_def(
            format!("{name}.{step_name}"),
            {
                let mut bs = implicit_binders.clone();
                bs.push(SurfaceBinder::new(
                    "x",
                    Some(self_ty.clone()),
                    SurfaceBinderInfo::Explicit,
                ));
                bs
            },
            self_ty.clone(),
            at_app(
                "Codata.IMchild",
                vec![
                    punit_ty_p(poly),
                    container(&shape_f),
                    container(&pos_f),
                    container(&tgt_f),
                    ident("PUnit.unit"),
                    ident("x"),
                    pos_point(i, m),
                ],
            ),
        ));
    }

    // def C.corecStep {ps} {S} (obsF…) (stepF) : (j : Unit) → S → isigmaStep …
    let packed_label = pack(
        &obs_f_names
            .iter()
            .map(|n| plain_app(n, vec![ident("st")]))
            .collect::<Vec<_>>(),
    );
    out.push(mk_def(
        corec_step.clone(),
        {
            let mut bs = implicit_binders.clone();
            bs.push(s_binder.clone());
            bs.extend(corec_fn_binders.clone());
            bs
        },
        pi(
            "j",
            punit_ty_p(poly),
            arrow(
                ident("S"),
                at_app(
                    "Codata.isigmaStep",
                    vec![
                        punit_ty_p(poly),
                        container(&shape_f),
                        container(&pos_f),
                        container(&tgt_f),
                        plain_app("Codata.uFam", vec![ident("S")]),
                        ident("j"),
                    ],
                ),
            ),
        ),
        lam(
            &["j", "st"],
            at_app(
                "Codata.umkStep",
                vec![
                    container(&shape_f),
                    container(&pos_f),
                    container(&tgt_f),
                    ident("S"),
                    ident("j"),
                    packed_label,
                    child_fn(
                        &step_f_names
                            .iter()
                            .map(|n| plain_app(n, vec![ident("st")]))
                            .collect::<Vec<_>>(),
                        poly,
                    ),
                ],
            ),
        ),
    ));

    // def C.corec {ps} {S} (obsF…) (stepF) (s : S) : C ps := @Codata.ucorec …
    out.push(mk_def(
        corec.clone(),
        {
            let mut bs = implicit_binders.clone();
            bs.push(s_binder.clone());
            bs.extend(corec_fn_binders.clone());
            bs.push(SurfaceBinder::new(
                "s",
                Some(ident("S")),
                SurfaceBinderInfo::Explicit,
            ));
            bs
        },
        self_ty.clone(),
        at_app("Codata.ucorec", {
            let mut step_args = params.clone();
            step_args.push(ident("S"));
            step_args.extend(obs_f_names.iter().map(|n| ident(n)));
            step_args.extend(step_f_names.iter().map(|n| ident(n)));
            vec![
                container(&shape_f),
                container(&pos_f),
                container(&tgt_f),
                ident("S"),
                at_app(&corec_step, step_args),
                ident("s"),
            ]
        }),
    ));

    // The CONSTRUCTOR: C.mk (one arg per field) — finite one-layer
    // construction via Codata.IMmk, giving finite-prefix-then-corecurse
    // (depth-1 guardedness) at the term level. Per-field laws are rfl.
    let mk_step_name = format!("{name}.mkStep");
    let unit_self = |extra: Vec<SurfaceExpr>| -> SurfaceExpr {
        let mut args = params.clone();
        args.extend(extra);
        plain_app(&shape_f, args)
    };
    out.push(mk_def(
        mk_step_name.clone(),
        {
            let mut bs = implicit_binders.clone();
            bs.extend([
                SurfaceBinder::new(
                    "a",
                    Some(unit_self(vec![ident("PUnit.unit")])),
                    SurfaceBinderInfo::Explicit,
                ),
                SurfaceBinder::new(
                    "f",
                    Some(SurfaceExpr::Pi(
                        Span::dummy(),
                        vec![SurfaceBinder::new(
                            "b",
                            Some({
                                let mut args = params.clone();
                                args.extend([ident("PUnit.unit"), ident("a")]);
                                plain_app(&pos_f, args)
                            }),
                            SurfaceBinderInfo::Explicit,
                        )],
                        Box::new(plain_app("Codata.IMIntl", {
                            let mut args =
                                vec![container(&shape_f), container(&pos_f), container(&tgt_f)];
                            args.push({
                                let mut targs = params.clone();
                                targs.extend([ident("PUnit.unit"), ident("a"), ident("b")]);
                                plain_app(&tgt_f, targs)
                            });
                            args
                        })),
                    )),
                    SurfaceBinderInfo::Explicit,
                ),
            ]);
            bs
        },
        plain_app(
            "Codata.isigmaStep",
            vec![
                container(&shape_f),
                container(&pos_f),
                container(&tgt_f),
                plain_app(
                    "Codata.IMIntl",
                    vec![container(&shape_f), container(&pos_f), container(&tgt_f)],
                ),
                ident("PUnit.unit"),
            ],
        ),
        plain_app("Sigma.mk", vec![ident("a"), ident("f")]),
    ));
    // Field-value binders for mk.
    let mut mk_binders = implicit_binders.clone();
    for (obs_name, obs_ty) in obs.iter() {
        mk_binders.push(SurfaceBinder::new(
            format!("{obs_name}V").as_str(),
            Some((*obs_ty).clone()),
            SurfaceBinderInfo::Explicit,
        ));
    }
    for step_name in steps.iter() {
        mk_binders.push(SurfaceBinder::new(
            format!("{step_name}V").as_str(),
            Some(self_ty.clone()),
            SurfaceBinderInfo::Explicit,
        ));
    }
    let mk_label = pack(
        &obs.iter()
            .map(|(n, _)| ident(&format!("{n}V")))
            .collect::<Vec<_>>(),
    );
    let mk_children: Vec<SurfaceExpr> = steps.iter().map(|n| ident(&format!("{n}V"))).collect();
    let mk_child_fn = if mk_children.len() == 1 {
        lam(&["_"], mk_children[0].clone())
    } else {
        let im_at = {
            let shape_f = shape_f.clone();
            let pos_f = pos_f.clone();
            let tgt_f = tgt_f.clone();
            let pe = params.clone();
            let label = mk_label.clone();
            move |bpos: SurfaceExpr| -> SurfaceExpr {
                let mut targs = pe.clone();
                targs.extend([ident("PUnit.unit"), label.clone(), bpos]);
                plain_app(
                    "Codata.IMIntl",
                    vec![
                        plain_app(&shape_f, pe.clone()),
                        plain_app(&pos_f, pe.clone()),
                        plain_app(&tgt_f, pe.clone()),
                        plain_app(&tgt_f, targs),
                    ],
                )
            }
        };
        let _ = &im_at;
        // Sum.rec chain selecting the children (dependent motive over the
        // constant-Unit target family reduces per branch).
        SurfaceExpr::Lambda(
            Span::dummy(),
            vec![SurfaceBinder::new("b", None, SurfaceBinderInfo::Explicit)],
            Box::new(mut_state_chain_p(
                &mk_children,
                0,
                &plain_app(
                    "Codata.IMIntl",
                    vec![container(&shape_f), container(&pos_f), container(&tgt_f)],
                ),
                &{
                    let tgt_f = tgt_f.clone();
                    let pe = params.clone();
                    let label = mk_label.clone();
                    move |bpos: SurfaceExpr| -> SurfaceExpr {
                        let mut targs = pe.clone();
                        targs.extend([ident("PUnit.unit"), label.clone(), bpos]);
                        plain_app(&tgt_f, targs)
                    }
                },
                ident("b"),
                None,
            )),
        )
    };
    out.push(mk_def(
        format!("{name}.mk"),
        mk_binders.clone(),
        self_ty.clone(),
        at_app("Codata.IMmk", {
            let mut args = vec![
                punit_ty_p(poly),
                container(&shape_f),
                container(&pos_f),
                container(&tgt_f),
                ident("PUnit.unit"),
            ];
            let mut mkargs = params.clone();
            mkargs.extend([mk_label.clone(), mk_child_fn]);
            args.push(at_app(&mk_step_name, mkargs));
            args
        }),
    ));
    // Per-field mk laws: accessor of mk = the supplied value, rfl.
    let mk_call = {
        let mut args = params.clone();
        args.extend(
            obs.iter()
                .map(|(n, _)| ident(&format!("{n}V")))
                .chain(steps.iter().map(|n| ident(&format!("{n}V")))),
        );
        at_app(&format!("{name}.mk"), args)
    };
    for field_name in obs.iter().map(|(n, _)| *n).chain(steps.iter().copied()) {
        let full = format!("{name}.{field_name}");
        let mut acc_args = params.clone();
        acc_args.push(mk_call.clone());
        out.push(mk_theorem(
            format!("{full}_mk"),
            mk_binders.clone(),
            SurfaceExpr::App(
                Span::dummy(),
                Box::new(ident("Eq")),
                vec![
                    SurfaceArg::positional(at_app(&full, acc_args)),
                    SurfaceArg::positional(ident(&format!("{field_name}V"))),
                ],
            ),
            ident("rfl"),
        ));
    }

    // Per-observation law: @C.obs_i ps (corec-call s) = obsF_i s := rfl
    let law_binders = || {
        let mut bs = implicit_binders.clone();
        bs.push(s_binder.clone());
        bs.extend(corec_fn_binders.clone());
        bs.push(SurfaceBinder::new(
            "s",
            Some(ident("S")),
            SurfaceBinderInfo::Explicit,
        ));
        bs
    };
    for ((obs_name, _), fname) in obs.iter().zip(&obs_f_names) {
        let obs_full = format!("{name}.{obs_name}");
        let mut obs_args = params.clone();
        obs_args.push(corec_call(ident("s")));
        out.push(mk_theorem(
            format!("{obs_full}_corec"),
            law_binders(),
            SurfaceExpr::App(
                Span::dummy(),
                Box::new(ident("Eq")),
                vec![
                    SurfaceArg::positional(at_app(&obs_full, obs_args)),
                    SurfaceArg::positional(plain_app(fname, vec![ident("s")])),
                ],
            ),
            ident("rfl"),
        ));
    }

    // Per-recursive-field law:
    //   @C.step_i ps (corec-call s) = corec-call (step_iF s) := rfl
    for (step_name, fname) in steps.iter().zip(&step_f_names) {
        let step_full = format!("{name}.{step_name}");
        let mut step_args = params.clone();
        step_args.push(corec_call(ident("s")));
        out.push(mk_theorem(
            format!("{step_full}_corec"),
            law_binders(),
            SurfaceExpr::App(
                Span::dummy(),
                Box::new(ident("Eq")),
                vec![
                    SurfaceArg::positional(at_app(&step_full, step_args)),
                    SurfaceArg::positional(corec_call(plain_app(fname, vec![ident("s")]))),
                ],
            ),
            ident("rfl"),
        ));
    }

    out.into_iter().map(|d| set_uparams(d, poly)).collect()
}

/// Elaborate a `codef` declaration (copattern definition into a codata
/// type): each clause observes one field of the result; recursive clauses
/// are syntactic self-calls (the productivity guarantee — one full
/// observation layer per corecursive step). Compiles to the codata's
/// generated corecursor and goes through the ordinary kernel-checked
/// pipeline. Deeper guardedness (self-calls under constructors) is a
/// named build item.
pub(crate) fn elab_codef_decl(
    env: &mut Environment,
    decl: &SurfaceDecl,
) -> Result<RegisteredElabResult, ElabError> {
    let SurfaceDecl::Codef {
        name,
        binders,
        ty,
        clauses,
        modifiers,
        ..
    } = decl
    else {
        return Err(unsupported("elab_codef_decl: not a codef declaration"));
    };
    if !modifiers.is_default() {
        return Err(unsupported(
            "codef: declaration modifiers are not supported yet",
        ));
    }
    for b in binders.iter() {
        if b.info != SurfaceBinderInfo::Explicit || b.ty.is_none() || b.default.is_some() {
            return Err(unsupported(
                "codef: binders must be simple explicit `(x : T)`",
            ));
        }
    }

    // The result type must be a codata type: head constant C with a
    // generated `C.corec` whose parameter names are recorded.
    let (head_name, type_args) = {
        let mut t = strip_parens(ty);
        let mut args: Vec<SurfaceExpr> = Vec::new();
        if let SurfaceExpr::App(_, h, a) = t {
            for arg in a {
                if arg.name.is_some() {
                    return Err(unsupported(
                        "codef: named arguments in the result type are not \
                         supported",
                    ));
                }
                args.push(arg.expr.clone());
            }
            t = strip_parens(h);
        }
        let SurfaceExpr::Ident(_, c) = t else {
            return Err(unsupported(
                "codef: the result type must be a codata type (a constant, \
                 possibly applied to parameters)",
            ));
        };
        (c.clone(), args)
    };
    let corec_name = format!("{head_name}.corec");
    let corec_const = clean_kernel::Name::from_string(&corec_name);
    if env.get_const(&corec_const).is_none() {
        return Err(unsupported(format!(
            "codef: `{head_name}` is not a codata type — `{corec_name}` does \
             not exist (declare it with the `codata` command first)"
        )));
    }
    let param_names = env.get_param_names(&corec_const).ok_or_else(|| {
        unsupported(format!(
            "codef: no parameter names recorded for `{corec_name}`"
        ))
    })?;
    let param_infos = env.get_param_binder_infos(&corec_const).ok_or_else(|| {
        unsupported(format!(
            "codef: no binder kinds recorded for `{corec_name}`"
        ))
    })?;
    // The clause slots are the EXPLICIT corec parameters except the final
    // state argument.
    let mut slots: Vec<String> = param_names
        .iter()
        .zip(param_infos.iter())
        .filter(|(_, i)| matches!(i, clean_kernel::BinderInfo::Default))
        .map(|(n, _)| n.clone())
        .collect();
    if slots.is_empty() {
        return Err(unsupported(format!(
            "codef: `{corec_name}` has no explicit parameters — not a \
             command-generated corecursor"
        )));
    }
    slots.pop(); // the trailing state argument
                 // An INDEXED corecursor has one more trailing explicit parameter — the
                 // index — which is the only generated explicit slot not `F`-suffixed.
    let indexed = slots.last().is_some_and(|sl| !sl.ends_with('F'));
    if indexed {
        slots.pop();
    }

    // For an indexed codef the FIRST binder is the index (it must be the
    // final argument of the result type); the optional second binder is
    // the corecursion state.
    let (idx_binder, state) = if indexed {
        let Some(ib) = binders.first() else {
            return Err(unsupported(format!(
                "codef into the indexed codata `{head_name}` needs the index \
                 as its first binder (matching the result type's index)"
            )));
        };
        if binders.len() > 2 {
            return Err(unsupported(
                "indexed codef v1 supports the index binder plus at most one \
                 state binder; pack richer state into one argument",
            ));
        }
        match type_args.last() {
            Some(SurfaceExpr::Ident(_, id)) if *id == ib.name => {}
            _ => {
                return Err(unsupported(format!(
                    "indexed codef: the result type's index must be exactly \
                     the first binder `{}`",
                    ib.name
                )));
            }
        }
        (Some(ib), binders.get(1))
    } else {
        if binders.len() > 1 {
            return Err(unsupported(
                "codef v1 supports zero or one explicit binder (the \
                 corecursion state); pack richer state into one argument",
            ));
        }
        (None, binders.first())
    };

    // mk-GUARDED corecursive clause (one constructor layer around the
    // self-call): compile via the Bool-flag buffered state. v1: plain
    // (non-indexed) codef into a single-recursive-field codata.
    if !indexed {
        if let Some(generated) = compile_guarded_codef(
            name, binders, ty, clauses, &slots, &head_name, &type_args, state,
        )? {
            let mut candidate = env.clone();
            crate::elaborate_decl_and_register(&mut candidate, &generated).map_err(|e| {
                unsupported(format!(
                    "codef `{name}` (mk-guarded): the generated corecursor \
                     application failed to elaborate/kernel-check (env left \
                     untouched): {e:?}"
                ))
            })?;
            *env = candidate;
            return Ok(RegisteredElabResult {
                result: ElabResult::Skipped,
                warning: None,
                hole_contexts: Vec::new(),
            });
        }
    }

    // Map each slot `<field>F` to its clause, building the per-slot lambda.
    let state_name = state.map_or("_", |b| b.name.as_str());
    let mut slot_lambdas: Vec<SurfaceExpr> = Vec::new();
    let mut used: Vec<&str> = Vec::new();
    // (field, index the author wrote) for each indexed self-call, checked below.
    let mut idx_checks: Vec<(String, SurfaceExpr)> = Vec::new();
    for slot in &slots {
        let field = slot.strip_suffix('F').unwrap_or(slot);
        let Some((_, value)) = clauses.iter().find(|(n, _)| n == field) else {
            return Err(unsupported(format!(
                "codef: missing clause for observation `{field}` of \
                 `{head_name}`"
            )));
        };
        used.push(field);
        // A syntactic self-call is a corecursive step: the lambda returns
        // the NEW STATE. Anything else is an observation value and must
        // not mention the function being defined (productivity).
        let body = match self_call_arg(value, name, indexed) {
            Some(call) => {
                if let Some(written) = call.index {
                    idx_checks.push((field.to_string(), written));
                }
                call.state
            }
            None => {
                if mentions(value, name) {
                    return Err(unsupported(format!(
                        "codef: clause `{field}` mentions `{name}` but is not \
                         a plain self-call — corecursive clauses must be \
                         exactly `{name} <next-state>` (deeper guardedness is \
                         a named build item)"
                    )));
                }
                value.clone()
            }
        };
        let mut lam_binders = Vec::new();
        if let Some(ib) = idx_binder {
            lam_binders.push(SurfaceBinder::new(
                ib.name.as_str(),
                ib.ty.as_deref().cloned(),
                SurfaceBinderInfo::Explicit,
            ));
        }
        lam_binders.push(SurfaceBinder::new(
            state_name,
            state.and_then(|b| b.ty.as_deref().cloned()),
            SurfaceBinderInfo::Explicit,
        ));
        slot_lambdas.push(SurfaceExpr::Lambda(
            Span::dummy(),
            lam_binders,
            Box::new(body),
        ));
    }
    for (n, _) in clauses {
        if !used.contains(&n.as_str()) {
            return Err(unsupported(format!(
                "codef: `{n}` is not an observation of `{head_name}` \
                 (expected: {})",
                used.join(", ")
            )));
        }
    }

    // The state type and initial state.
    let state_ty = state
        .and_then(|b| b.ty.as_deref().cloned())
        .unwrap_or_else(punit_ty);
    let init_state = state.map_or_else(|| ident("PUnit.unit"), |b| ident(&b.name));

    // INDEX-FIDELITY GUARD.
    //
    // The corecursor forces every child to the codata FIELD's target index, so
    // the index written in a self-call is not consumed. Until this guard, a
    // self-call that wrote a DIFFERENT index was silently accepted and meant
    // something the author did not write:
    //
    //   codata IS3 : (n : Nat) → Type where
    //     val : Nat
    //     next : IS3 (Nat.succ n)
    //
    //   codef tr (n : Nat) : IS3 n where
    //     val := n
    //     next := tr n                       -- target demands `Nat.succ n`
    //
    // `IS3.val (IS3.next (tr 4))` reduced to 5 — the target's move — while the
    // author's own `tr n` would give 4. The ERRONEOUS program was the one that
    // compiled. The kernel cannot catch it on its own: it only would if the
    // state type mentioned the index, which it need not.
    //
    // The check needs the field's target index, and `C.<field>`'s result type
    // already IS `C <params> <target>`. So "written ≡ target" is exactly "does
    // `C.<field> x` typecheck at `C <params> <written>`" — decided by DEFEQ,
    // not by syntax, so `tr (n + 1)` against a `Nat.succ n` target stays
    // accepted. Probe in a THROWAWAY clone before anything is registered, so a
    // rejection leaves `env` untouched.
    for (field, written) in &idx_checks {
        // A HAND-WRITTEN carrier can present an indexed-looking `.corec`
        // without the generated step accessors. There is then no `C.<field>`
        // whose result type carries a target index, and probing would reject a
        // previously-accepted codef while blaming the wrong thing (an
        // `UnknownIdent` for `C.<field>`, reported as an index mismatch). This
        // guard owns index fidelity only; carrier impersonation is checked
        // elsewhere. Nothing to compare against, so skip.
        let accessor = format!("{head_name}.{field}");
        if env
            .get_const(&clean_kernel::Name::from_string(&accessor))
            .is_none()
        {
            continue;
        }
        let mut probe_args = type_args.clone();
        probe_args.pop(); // the result type's own index
        probe_args.push(written.clone());
        let mut probe_binders = binders.to_vec();
        probe_binders.push(SurfaceBinder::new(
            "_idxProbeSelf",
            Some((**ty).clone()),
            SurfaceBinderInfo::Explicit,
        ));
        let probe = mk_def(
            format!("{name}._indexProbe_{field}"),
            probe_binders,
            plain_app(&head_name, probe_args),
            plain_app(&accessor, vec![ident("_idxProbeSelf")]),
        );
        let mut probe_env = env.clone();
        crate::elaborate_decl_and_register(&mut probe_env, &probe).map_err(|e| {
            unsupported(format!(
                "codef `{name}`: clause `{field}` corecurses at an index that is not \
                 the one `{accessor}` moves to. The written index is \
                 DISCARDED (the codata field's target governs the move), so this \
                 would compile as a different program than the one written: {e:?}"
            ))
        })?;
    }

    // def <name> (idx?) (state?) : <ty> :=
    //   @C.corec <params> <S> <lams…> (<idx>) <init>
    let mut corec_args = type_args;
    let idx_arg = if indexed { corec_args.pop() } else { None };
    if let Some(ib) = idx_binder {
        // Indexed state family: S := fun <idx> => <state-ty> (the state
        // type may mention the index).
        corec_args.push(lam1(&ib.name, state_ty));
    } else {
        corec_args.push(state_ty);
    }
    corec_args.extend(slot_lambdas);
    if let Some(ia) = idx_arg {
        corec_args.push(ia);
    }
    corec_args.push(init_state);
    let generated = mk_def(
        name.clone(),
        binders.to_vec(),
        (**ty).clone(),
        at_app(&corec_name, corec_args),
    );

    let mut candidate = env.clone();
    crate::elaborate_decl_and_register(&mut candidate, &generated).map_err(|e| {
        unsupported(format!(
            "codef `{name}`: the generated corecursor application failed to \
             elaborate/kernel-check (env left untouched): {e:?}"
        ))
    })?;
    // Record that WE generated this constant, for the rank-7 direct-lazy
    // lowering (B2). Minted into `candidate`, so a codef whose generated body
    // failed to kernel-check above leaves behind no origin either.
    //
    // This is a HINT and authorizes nothing: a consumer must re-resolve
    // `corec` and structurally replay the canonical body against a freshly
    // re-derived expectation before acting on it. It exists so recognition
    // never has to guess from a name — `C.corec` is user-derivable, and
    // matching on it would be a soundness hole wearing metadata's clothes.
    candidate.set_codata_origin(
        clean_kernel::Name::from_string(name),
        clean_kernel::CodataOrigin {
            lane: if indexed {
                clean_kernel::CodataLane::Indexed
            } else {
                clean_kernel::CodataLane::Plain
            },
            carrier: clean_kernel::Name::from_string(&head_name),
            corec: corec_const.clone(),
            slots: slots.clone(),
        },
    );
    *env = candidate;
    Ok(RegisteredElabResult {
        result: ElabResult::Skipped,
        warning: None,
        hole_contexts: Vec::new(),
    })
}

/// A recognized corecursive self-call: the new state, plus the index the author
/// wrote (indexed lane only).
struct SelfCall {
    /// The index argument the AUTHOR WROTE, in the indexed lane. `None` in the
    /// plain lane. Kept rather than dropped so the caller can check it against
    /// the codata field's target index.
    index: Option<SurfaceExpr>,
    /// The new corecursion state.
    state: SurfaceExpr,
}

/// If `expr` is a plain self-call, return its new STATE and written INDEX.
///
/// Plain codef: `fname` (zero-state, yields `Unit.unit`) or `fname <state>`.
/// Indexed codef: `fname <idx>` (zero-state) or `fname <idx> <state>`.
///
/// INDEX FIDELITY (closed 2026-08-20). The index is still not CONSUMED here —
/// the codata's own target expression governs the index move — but it is no
/// longer discarded either: it is returned so the caller's index-fidelity
/// guard can check it against the codata field's target index before anything
/// is generated. A self-call that writes a different index is now a loud
/// error rather than a silently different program.
fn self_call_arg(expr: &SurfaceExpr, fname: &str, indexed: bool) -> Option<SelfCall> {
    match strip_parens(expr) {
        SurfaceExpr::Ident(_, id) if id == fname && !indexed => Some(SelfCall {
            index: None,
            state: ident("PUnit.unit"),
        }),
        SurfaceExpr::App(_, h, args) => {
            let SurfaceExpr::Ident(_, id) = strip_parens(h) else {
                return None;
            };
            if id != fname || args.iter().any(|a| a.name.is_some()) {
                return None;
            }
            let expected = if indexed { 2 } else { 1 };
            if args.len() != expected && !(indexed && args.len() == 1) {
                return None;
            }
            // ARITY: in BOTH indexed shapes the index is `args[0]` — the
            // zero-state shape (`tracker (Nat.succ n)`) just leaves the state
            // implicit. Reading "the last argument" as the index is wrong for
            // that shape and silently swaps index for state.
            let index = if indexed {
                Some(args[0].expr.clone())
            } else {
                None
            };
            let state = if args.len() == expected {
                args[expected - 1].expr.clone()
            } else {
                ident("PUnit.unit")
            };
            Some(SelfCall { index, state })
        }
        _ => None,
    }
}

// ── mutual codata (the QPFTypes mutual-blocks answer, at the surface) ──
// Two members over the Bool tag index (member 0 ↦ true, member 1 ↦ false),
// mirroring the hand-validated TreeS/ForestS expansion in
// data/graduation/clean-mtype/proof/MTypeIndexed.lean. Wider blocks need
// the Σ-tag index — a named build item.

struct MutualMember<'a> {
    name: &'a str,
    binders: &'a [SurfaceBinder],
    /// Observations: (name, type). The leading non-recursive fields.
    obs: Vec<(&'a str, &'a SurfaceExpr)>,
    /// Recursive fields: (name, target member index). The trailing block.
    steps: Vec<(&'a str, usize)>,
}

/// Elaborate a `mutual` block whose members are all `codata`.
pub(crate) fn elab_mutual_codata(
    env: &mut Environment,
    members: &[SurfaceDecl],
) -> Result<RegisteredElabResult, ElabError> {
    if members.len() < 2 {
        return Err(unsupported("mutual codata needs at least two members"));
    }
    let names: Vec<&str> = members
        .iter()
        .map(|d| match d {
            SurfaceDecl::Codata { name, .. } => Ok(name.as_str()),
            _ => Err(unsupported(
                "mutual codata: every member of the block must be a `codata` \
                 declaration",
            )),
        })
        .collect::<Result<_, _>>()?;
    let shapes: Vec<(MutualMember<'_>, Option<&str>)> = members
        .iter()
        .map(|d| validate_mutual_member(d, &names))
        .collect::<Result<_, _>>()?;
    let (shapes, polys): (Vec<_>, Vec<_>) = shapes.into_iter().unzip();
    // Every member must declare the SAME universe envelope (all .{u} with one
    // shared name, or all monomorphic) — same discipline as identical binders.
    let poly = polys[0];
    if polys.iter().any(|p| *p != poly) {
        return Err(unsupported(
            "mutual codata v1 requires every member to declare the SAME \
             universe parameter list",
        ));
    }
    let b0: Vec<&str> = shapes[0].binders.iter().map(|b| b.name.as_str()).collect();
    let b1: Vec<&str> = shapes[1].binders.iter().map(|b| b.name.as_str()).collect();
    if b0 != b1 {
        return Err(unsupported(
            "mutual codata v1 requires both members to declare IDENTICAL \
             parameter lists (same names, same order)",
        ));
    }

    let mut candidate = env.clone();
    ensure_codata_seeds(&mut candidate)?;
    let generated_decls = if shapes.len() == 2 {
        generate_mutual(&shapes, poly)
    } else {
        generate_mutual_n(&shapes, poly)
    };
    for (i, generated) in generated_decls.into_iter().enumerate() {
        if std::env::var("CLEAN_CODATA_DUMP").is_ok() {
            eprintln!("[codata-gen {i}] {generated:#?}");
        }
        crate::elaborate_decl_and_register(&mut candidate, &generated).map_err(|e| {
            unsupported(format!(
                "mutual codata `{}`/`{}`: generated declaration {i} failed \
                 to elaborate/kernel-check (env left untouched): {e:?}",
                names[0], names[1]
            ))
        })?;
    }
    *env = candidate;
    Ok(RegisteredElabResult {
        result: ElabResult::Skipped,
        warning: None,
        hole_contexts: Vec::new(),
    })
}

fn validate_mutual_member<'a>(
    decl: &'a SurfaceDecl,
    names: &[&str],
) -> Result<(MutualMember<'a>, Option<&'a str>), ElabError> {
    let SurfaceDecl::Codata {
        name,
        universe_params,
        binders,
        ty,
        fields,
        deriving,
        modifiers,
        ..
    } = decl
    else {
        return Err(unsupported(
            "mutual codata: every member of the block must be a `codata` \
             declaration",
        ));
    };
    let member_poly = match universe_params.as_slice() {
        [] => None,
        [u] => Some(u.as_str()),
        _ => {
            return Err(unsupported(format!(
                "mutual codata member `{name}`: at most ONE universe \
                 parameter is supported in v1"
            )))
        }
    };
    if !deriving.is_empty() || !modifiers.is_default() {
        return Err(unsupported(format!(
            "mutual codata member `{name}`: deriving and modifiers are not \
             supported (same envelope as single codata)"
        )));
    }
    if let Some(t) = ty {
        let sort_ok = match t.as_ref() {
            SurfaceExpr::Universe(_, UniverseExpr::Type) => true,
            SurfaceExpr::Universe(_, UniverseExpr::TypeLevel(l)) => matches!(
                (l.as_ref(), member_poly),
                (LevelExpr::Param(n), Some(u)) if n == u
            ),
            _ => false,
        };
        if !sort_ok {
            return Err(unsupported(format!(
                "mutual codata member `{name}`: the result sort must be \
                 `Type` (or `Type u` matching the declared universe parameter)"
            )));
        }
    }
    for b in binders.iter() {
        if b.info != SurfaceBinderInfo::Explicit || b.ty.is_none() || b.default.is_some() {
            return Err(unsupported(format!(
                "mutual codata member `{name}`: parameters must be simple \
                 explicit binders `(x : T)`"
            )));
        }
    }
    let params: Vec<&str> = binders.iter().map(|b| b.name.as_str()).collect();
    let target_of = |t: &SurfaceExpr| -> Option<usize> {
        names.iter().position(|n| is_self_at_params(t, n, &params))
    };
    let mut split = fields.len();
    while split > 0 && target_of(&fields[split - 1].ty).is_some() {
        split -= 1;
    }
    let (obs_fields, step_fields) = fields.split_at(split);
    if step_fields.is_empty() {
        return Err(unsupported(format!(
            "mutual codata member `{name}`: the final field must be recursive \
             (some block member at the shared parameters)"
        )));
    }
    for f in obs_fields {
        for n in names {
            if mentions(&f.ty, n) {
                return Err(unsupported(format!(
                    "mutual codata member `{name}`: field `{}` mentions `{n}` \
                     but is not exactly `{n}` at the shared parameters — \
                     recursive fields must form the TRAILING block",
                    f.name
                )));
            }
        }
    }
    let mut seen: Vec<&str> = Vec::new();
    for f in fields.iter() {
        if seen.contains(&f.name.as_str()) {
            return Err(unsupported(format!(
                "mutual codata member `{name}`: field names must be distinct"
            )));
        }
        seen.push(&f.name);
    }
    Ok((
        MutualMember {
            name,
            binders,
            obs: obs_fields
                .iter()
                .map(|f| (f.name.as_str(), &f.ty))
                .collect(),
            steps: step_fields
                .iter()
                .map(|f| {
                    (
                        f.name.as_str(),
                        target_of(&f.ty).expect("trailing split guarantees a target"),
                    )
                })
                .collect(),
        },
        member_poly,
    ))
}

/// Right-nested `PProd` of the observation types (`Unit` when none).
/// Label type at the declared level: an obs-less member's label is the unit
/// at the FAMILY universe (`PUnit.{u+1}` when polymorphic) so the shapeF
/// tower's `Type u` motive accepts it.
fn mutual_label_ty_p(obs: &[(&str, &SurfaceExpr)], poly: Option<&str>) -> SurfaceExpr {
    obs.iter()
        .rev()
        .map(|(_, t)| (*t).clone())
        .reduce(|acc, t| plain_app("PProd", vec![t, acc]))
        .unwrap_or_else(|| punit_ty_p(poly))
}

/// Right-nested `PProd.mk` chain (`Unit.unit` when no observations).
fn mutual_pack(vals: &[SurfaceExpr]) -> SurfaceExpr {
    match vals {
        [] => ident("PUnit.unit"),
        [only] => only.clone(),
        [first, rest @ ..] => plain_app("PProd.mk", vec![first.clone(), mutual_pack(rest)]),
    }
}

/// The position type for m recursive fields (same shape as single codata).
/// Position tower at the declared level: `PUnit.{u+1}` towers when the
/// codata is polymorphic (positions live in the same universe as the
/// families — the plain-lane discipline), `PUnit.{1}` otherwise.
fn mut_pos_ty_p(m: usize, poly: Option<&str>) -> SurfaceExpr {
    if m <= 1 {
        punit_ty_p(poly)
    } else {
        plain_app("Sum", vec![punit_ty_p(poly), mut_pos_ty_p(m - 1, poly)])
    }
}

fn mut_pos_point(i: usize, m: usize) -> SurfaceExpr {
    if m <= 1 {
        ident("PUnit.unit")
    } else if i == 0 {
        plain_app("Sum.inl", vec![ident("PUnit.unit")])
    } else {
        plain_app("Sum.inr", vec![mut_pos_point(i - 1, m - 1)])
    }
}

fn lam1(name: &str, body: SurfaceExpr) -> SurfaceExpr {
    SurfaceExpr::Lambda(
        Span::dummy(),
        vec![SurfaceBinder::new(name, None, SurfaceBinderInfo::Explicit)],
        Box::new(body),
    )
}

/// `Bool.rec (motive := <motive>) <false-case> <true-case> <scrut>`
fn bool_rec(
    motive: SurfaceExpr,
    fc: SurfaceExpr,
    tc: SurfaceExpr,
    scrut: SurfaceExpr,
) -> SurfaceExpr {
    let mut args = vec![SurfaceArg::positional(motive)];
    args[0].name = Some("motive".to_string());
    args.extend([
        SurfaceArg::positional(fc),
        SurfaceArg::positional(tc),
        SurfaceArg::positional(scrut),
    ]);
    SurfaceExpr::App(Span::dummy(), Box::new(ident("Bool.rec")), args)
}

/// Non-dependent Sum.rec chain over m positions returning `Bool` targets.
fn mut_tgt_chain_p(targets: &[SurfaceExpr], scrut: SurfaceExpr, poly: Option<&str>) -> SurfaceExpr {
    match targets {
        [only] => only.clone(),
        [first, rest @ ..] => {
            let inner = if rest.len() == 1 {
                lam1("_", rest[0].clone())
            } else {
                lam1("b2", mut_tgt_chain_p(rest, ident("b2"), poly))
            };
            SurfaceExpr::App(
                Span::dummy(),
                Box::new(SurfaceExpr::Explicit(
                    Span::dummy(),
                    Box::new(ident("Sum.rec")),
                )),
                vec![
                    SurfaceArg::positional(punit_ty_p(poly)),
                    SurfaceArg::positional(mut_pos_ty_p(rest.len(), poly)),
                    SurfaceArg::positional(lam1("_", ident("Bool"))),
                    SurfaceArg::positional(lam1("_", first.clone())),
                    SurfaceArg::positional(inner),
                    SurfaceArg::positional(scrut),
                ],
            )
        }
        [] => unreachable!("validated: at least one recursive field"),
    }
}

/// Dependent Sum.rec chain over the member's positions selecting the next
/// STATE for each branch. `wrap` embeds the level's scrutinee back into the
/// FULL position type for the motive's `tgtF` application.
#[allow(clippy::too_many_arguments)]
fn mut_state_chain_p(
    branch_states: &[SurfaceExpr],
    depth: usize,
    st_at: &SurfaceExpr,
    tgt_full: &dyn Fn(SurfaceExpr) -> SurfaceExpr,
    scrut: SurfaceExpr,
    poly: Option<&str>,
) -> SurfaceExpr {
    match branch_states {
        [only] => only.clone(),
        [first, rest @ ..] => {
            let wrap = |e: SurfaceExpr, d: usize| -> SurfaceExpr {
                let mut w = e;
                for _ in 0..d {
                    w = plain_app("Sum.inr", vec![w]);
                }
                w
            };
            let motive = lam1("bm", {
                SurfaceExpr::App(
                    Span::dummy(),
                    Box::new(st_at.clone()),
                    vec![SurfaceArg::positional(tgt_full(wrap(ident("bm"), depth)))],
                )
            });
            let inner = if rest.len() == 1 {
                lam1("_", rest[0].clone())
            } else {
                lam1(
                    "bi",
                    mut_state_chain_p(rest, depth + 1, st_at, tgt_full, ident("bi"), poly),
                )
            };
            SurfaceExpr::App(
                Span::dummy(),
                Box::new(SurfaceExpr::Explicit(
                    Span::dummy(),
                    Box::new(ident("Sum.rec")),
                )),
                vec![
                    SurfaceArg::positional(punit_ty_p(poly)),
                    SurfaceArg::positional(mut_pos_ty_p(rest.len(), poly)),
                    SurfaceArg::positional(motive),
                    SurfaceArg::positional(lam1("_", first.clone())),
                    SurfaceArg::positional(inner),
                    SurfaceArg::positional(scrut),
                ],
            )
        }
        [] => unreachable!("validated: at least one recursive field"),
    }
}

fn generate_mutual(shapes: &[MutualMember<'_>], poly: Option<&str>) -> Vec<SurfaceDecl> {
    let names: Vec<&str> = shapes.iter().map(|m| m.name).collect();
    let param_exprs: Vec<SurfaceExpr> = shapes[0].binders.iter().map(|b| ident(&b.name)).collect();
    let explicit_binders: Vec<SurfaceBinder> = shapes[0].binders.to_vec();
    let implicit_binders: Vec<SurfaceBinder> = explicit_binders
        .iter()
        .map(|b| {
            let mut ib = b.clone();
            ib.info = SurfaceBinderInfo::Implicit;
            ib
        })
        .collect();
    let tag = |mi: usize| ident(if mi == 0 { "true" } else { "false" });

    let joint = format!("{}.{}", names[0], names[1]);
    let shape_f = format!("{joint}.shapeF");
    let pos_f = format!("{joint}.posF");
    let tgt_f = format!("{joint}.tgtF");
    let st_f = format!("{joint}.stF");
    let mk_step = format!("{joint}.mkStep");
    let step_fn = format!("{joint}.step");
    let container = |f: &str| plain_app(f, param_exprs.clone());

    let mut out = Vec::new();

    // shapeF
    out.push(mk_def(
        shape_f.clone(),
        explicit_binders.clone(),
        arrow(ident("Bool"), type_u(poly)),
        lam1(
            "tg",
            bool_rec(
                lam1("_", type_u(poly)),
                mutual_label_ty_p(&shapes[1].obs, poly),
                mutual_label_ty_p(&shapes[0].obs, poly),
                ident("tg"),
            ),
        ),
    ));
    // posF
    out.push(mk_def(
        pos_f.clone(),
        explicit_binders.clone(),
        pi("i", ident("Bool"), {
            let mut args = param_exprs.clone();
            args.push(ident("i"));
            arrow(plain_app(&shape_f, args), type_u(poly))
        }),
        lam1(
            "tg",
            bool_rec(
                lam1("tg2", {
                    let mut args = param_exprs.clone();
                    args.push(ident("tg2"));
                    arrow(plain_app(&shape_f, args), type_u(poly))
                }),
                lam1("_", mut_pos_ty_p(shapes[1].steps.len(), poly)),
                lam1("_", mut_pos_ty_p(shapes[0].steps.len(), poly)),
                ident("tg"),
            ),
        ),
    ));
    // tgtF
    let tgt_case = |m: &MutualMember<'_>| -> SurfaceExpr {
        let targets: Vec<SurfaceExpr> = m.steps.iter().map(|(_, t)| tag(*t)).collect();
        if targets.len() == 1 {
            SurfaceExpr::Lambda(
                Span::dummy(),
                vec![
                    SurfaceBinder::new("_", None, SurfaceBinderInfo::Explicit),
                    SurfaceBinder::new("_", None, SurfaceBinderInfo::Explicit),
                ],
                Box::new(targets[0].clone()),
            )
        } else {
            SurfaceExpr::Lambda(
                Span::dummy(),
                vec![
                    SurfaceBinder::new("_", None, SurfaceBinderInfo::Explicit),
                    SurfaceBinder::new("pb", None, SurfaceBinderInfo::Explicit),
                ],
                Box::new(mut_tgt_chain_p(&targets, ident("pb"), poly)),
            )
        }
    };
    out.push(mk_def(
        tgt_f.clone(),
        explicit_binders.clone(),
        pi("i", ident("Bool"), {
            let mut sargs = param_exprs.clone();
            sargs.push(ident("i"));
            pi("a", plain_app(&shape_f, sargs), {
                let mut pargs = param_exprs.clone();
                pargs.extend([ident("i"), ident("a")]);
                arrow(plain_app(&pos_f, pargs), ident("Bool"))
            })
        }),
        lam1(
            "tg",
            bool_rec(
                lam1("tg2", {
                    let mut sargs = param_exprs.clone();
                    sargs.push(ident("tg2"));
                    pi("a", plain_app(&shape_f, sargs), {
                        let mut pargs = param_exprs.clone();
                        pargs.extend([ident("tg2"), ident("a")]);
                        arrow(plain_app(&pos_f, pargs), ident("Bool"))
                    })
                }),
                tgt_case(&shapes[1]),
                tgt_case(&shapes[0]),
                ident("tg"),
            ),
        ),
    ));

    // Member carriers.
    for (mi, m) in shapes.iter().enumerate() {
        out.push(mk_def(
            m.name.to_string(),
            explicit_binders.clone(),
            type_u(poly),
            at_app(
                "Codata.IMIntl",
                vec![
                    ident("Bool"),
                    container(&shape_f),
                    container(&pos_f),
                    container(&tgt_f),
                    tag(mi),
                ],
            ),
        ));
    }

    // Accessors.
    for (mi, m) in shapes.iter().enumerate() {
        let self_ty = plain_app(m.name, param_exprs.clone());
        let k = m.obs.len();
        for (oi, (obs_name, obs_ty)) in m.obs.iter().enumerate() {
            let mut sel = at_app(
                "Codata.IMhead",
                vec![
                    ident("Bool"),
                    container(&shape_f),
                    container(&pos_f),
                    container(&tgt_f),
                    tag(mi),
                    ident("x"),
                ],
            );
            for _ in 0..oi {
                sel = SurfaceExpr::Proj(Span::dummy(), Box::new(sel), Projection::Index(2));
            }
            if oi + 1 < k {
                sel = SurfaceExpr::Proj(Span::dummy(), Box::new(sel), Projection::Index(1));
            }
            out.push(mk_def(
                format!("{}.{obs_name}", m.name),
                {
                    let mut bs = implicit_binders.clone();
                    bs.push(SurfaceBinder::new(
                        "x",
                        Some(self_ty.clone()),
                        SurfaceBinderInfo::Explicit,
                    ));
                    bs
                },
                (*obs_ty).clone(),
                sel,
            ));
        }
        let mcount = m.steps.len();
        for (si, (step_name, tgt_mi)) in m.steps.iter().enumerate() {
            out.push(mk_def(
                format!("{}.{step_name}", m.name),
                {
                    let mut bs = implicit_binders.clone();
                    bs.push(SurfaceBinder::new(
                        "x",
                        Some(self_ty.clone()),
                        SurfaceBinderInfo::Explicit,
                    ));
                    bs
                },
                plain_app(names[*tgt_mi], param_exprs.clone()),
                at_app(
                    "Codata.IMchild",
                    vec![
                        ident("Bool"),
                        container(&shape_f),
                        container(&pos_f),
                        container(&tgt_f),
                        tag(mi),
                        ident("x"),
                        mut_pos_point(si, mcount),
                    ],
                ),
            ));
        }
    }

    // stF
    out.push(mk_def(
        st_f.clone(),
        vec![
            SurfaceBinder::new("S1", Some(type_u(poly)), SurfaceBinderInfo::Explicit),
            SurfaceBinder::new("S2", Some(type_u(poly)), SurfaceBinderInfo::Explicit),
        ],
        arrow(ident("Bool"), type_u(poly)),
        lam1(
            "tg",
            bool_rec(
                lam1("_", type_u(poly)),
                ident("S2"),
                ident("S1"),
                ident("tg"),
            ),
        ),
    ));
    let st_container = plain_app(&st_f, vec![ident("S1"), ident("S2")]);

    // mkStep
    out.push(mk_def(
        mk_step.clone(),
        {
            let mut bs = implicit_binders.clone();
            bs.extend([
                SurfaceBinder::new("S1", Some(type_u(poly)), SurfaceBinderInfo::Implicit),
                SurfaceBinder::new("S2", Some(type_u(poly)), SurfaceBinderInfo::Implicit),
                SurfaceBinder::new("tg", Some(ident("Bool")), SurfaceBinderInfo::Explicit),
                SurfaceBinder::new(
                    "a",
                    Some({
                        let mut args = param_exprs.clone();
                        args.push(ident("tg"));
                        plain_app(&shape_f, args)
                    }),
                    SurfaceBinderInfo::Explicit,
                ),
                SurfaceBinder::new(
                    "f",
                    Some(SurfaceExpr::Pi(
                        Span::dummy(),
                        vec![SurfaceBinder::new(
                            "b",
                            Some({
                                let mut args = param_exprs.clone();
                                args.extend([ident("tg"), ident("a")]);
                                plain_app(&pos_f, args)
                            }),
                            SurfaceBinderInfo::Explicit,
                        )],
                        Box::new(SurfaceExpr::App(
                            Span::dummy(),
                            Box::new(st_container.clone()),
                            vec![SurfaceArg::positional({
                                let mut args = param_exprs.clone();
                                args.extend([ident("tg"), ident("a"), ident("b")]);
                                plain_app(&tgt_f, args)
                            })],
                        )),
                    )),
                    SurfaceBinderInfo::Explicit,
                ),
            ]);
            bs
        },
        plain_app(
            "Codata.isigmaStep",
            vec![
                container(&shape_f),
                container(&pos_f),
                container(&tgt_f),
                st_container.clone(),
                ident("tg"),
            ],
        ),
        plain_app("Sigma.mk", vec![ident("a"), ident("f")]),
    ));

    // Per-field corec function binders (member 0's fields, then member 1's;
    // member-prefixed so shared field names across members cannot clash).
    let mut fn_binders: Vec<SurfaceBinder> = Vec::new();
    for (mi, m) in shapes.iter().enumerate() {
        let s_own = if mi == 0 { "S1" } else { "S2" };
        for (obs_name, obs_ty) in &m.obs {
            fn_binders.push(SurfaceBinder::new(
                format!("{}_{obs_name}F", m.name).as_str(),
                Some(arrow(ident(s_own), (*obs_ty).clone())),
                SurfaceBinderInfo::Explicit,
            ));
        }
        for (step_name, tgt_mi) in &m.steps {
            let s_tgt = if *tgt_mi == 0 { "S1" } else { "S2" };
            fn_binders.push(SurfaceBinder::new(
                format!("{}_{step_name}F", m.name).as_str(),
                Some(arrow(ident(s_own), ident(s_tgt))),
                SurfaceBinderInfo::Explicit,
            ));
        }
    }
    let all_fn_idents: Vec<SurfaceExpr> = shapes
        .iter()
        .flat_map(|m| {
            m.obs
                .iter()
                .map(|(n, _)| ident(&format!("{}_{n}F", m.name)))
                .chain(
                    m.steps
                        .iter()
                        .map(|(n, _)| ident(&format!("{}_{n}F", m.name))),
                )
                .collect::<Vec<_>>()
        })
        .collect();

    // step (the mutual coalgebra)
    let step_case = |mi: usize| -> SurfaceExpr {
        let m = &shapes[mi];
        let label = mutual_pack(
            &m.obs
                .iter()
                .map(|(n, _)| plain_app(&format!("{}_{n}F", m.name), vec![ident("sv")]))
                .collect::<Vec<_>>(),
        );
        let branch_states: Vec<SurfaceExpr> = m
            .steps
            .iter()
            .map(|(n, _)| plain_app(&format!("{}_{n}F", m.name), vec![ident("sv")]))
            .collect();
        let tgt_full = {
            let param_exprs = param_exprs.clone();
            let tgt_f = tgt_f.clone();
            let label = label.clone();
            let tag_e = tag(mi);
            move |bpos: SurfaceExpr| -> SurfaceExpr {
                let mut args = param_exprs.clone();
                args.extend([tag_e.clone(), label.clone(), bpos]);
                plain_app(&tgt_f, args)
            }
        };
        let child = if branch_states.len() == 1 {
            lam1("_", branch_states[0].clone())
        } else {
            lam1(
                "pb",
                mut_state_chain_p(
                    &branch_states,
                    0,
                    &st_container,
                    &tgt_full,
                    ident("pb"),
                    poly,
                ),
            )
        };
        let mut mk_args = param_exprs.clone();
        mk_args.extend([ident("S1"), ident("S2"), tag(mi), label, child]);
        lam1("sv", at_app(&mk_step, mk_args))
    };
    out.push(mk_def(
        step_fn.clone(),
        {
            let mut bs = implicit_binders.clone();
            bs.extend([
                SurfaceBinder::new("S1", Some(type_u(poly)), SurfaceBinderInfo::Implicit),
                SurfaceBinder::new("S2", Some(type_u(poly)), SurfaceBinderInfo::Implicit),
            ]);
            bs.extend(fn_binders.clone());
            bs
        },
        pi("j", ident("Bool"), {
            arrow(
                SurfaceExpr::App(
                    Span::dummy(),
                    Box::new(st_container.clone()),
                    vec![SurfaceArg::positional(ident("j"))],
                ),
                plain_app(
                    "Codata.isigmaStep",
                    vec![
                        container(&shape_f),
                        container(&pos_f),
                        container(&tgt_f),
                        st_container.clone(),
                        ident("j"),
                    ],
                ),
            )
        }),
        lam1(
            "j",
            bool_rec(
                lam1("tg2", {
                    arrow(
                        SurfaceExpr::App(
                            Span::dummy(),
                            Box::new(st_container.clone()),
                            vec![SurfaceArg::positional(ident("tg2"))],
                        ),
                        plain_app(
                            "Codata.isigmaStep",
                            vec![
                                container(&shape_f),
                                container(&pos_f),
                                container(&tgt_f),
                                st_container.clone(),
                                ident("tg2"),
                            ],
                        ),
                    )
                }),
                step_case(1),
                step_case(0),
                ident("j"),
            ),
        ),
    ));

    // Per-member corec + laws.
    for (mi, m) in shapes.iter().enumerate() {
        let s_own = if mi == 0 { "S1" } else { "S2" };
        let self_ty = plain_app(m.name, param_exprs.clone());
        let corec_name = format!("{}.corec", m.name);
        let step_call = {
            let mut args = param_exprs.clone();
            args.extend([ident("S1"), ident("S2")]);
            args.extend(all_fn_idents.clone());
            at_app(&step_fn, args)
        };
        out.push(mk_def(
            corec_name.clone(),
            {
                let mut bs = implicit_binders.clone();
                bs.extend([
                    SurfaceBinder::new("S1", Some(type_u(poly)), SurfaceBinderInfo::Implicit),
                    SurfaceBinder::new("S2", Some(type_u(poly)), SurfaceBinderInfo::Implicit),
                ]);
                bs.extend(fn_binders.clone());
                bs.push(SurfaceBinder::new(
                    "s",
                    Some(ident(s_own)),
                    SurfaceBinderInfo::Explicit,
                ));
                bs
            },
            self_ty.clone(),
            at_app(
                "Codata.IMcorec",
                vec![
                    ident("Bool"),
                    container(&shape_f),
                    container(&pos_f),
                    container(&tgt_f),
                    st_container.clone(),
                    step_call,
                    tag(mi),
                    ident("s"),
                ],
            ),
        ));
    }
    // Per-member CONSTRUCTORS: M.mk (field values) via Codata.IMmk at the
    // member's tag; children typed at their target members. rfl laws.
    for (mi, m) in shapes.iter().enumerate() {
        let self_ty = plain_app(m.name, param_exprs.clone());
        let mk_step_name = format!("{}.mkStep2", m.name);
        out.push(mk_def(
            mk_step_name.clone(),
            {
                let mut bs = implicit_binders.clone();
                bs.extend([
                    SurfaceBinder::new(
                        "a",
                        Some({
                            let mut args = param_exprs.clone();
                            args.push(tag(mi));
                            plain_app(&shape_f, args)
                        }),
                        SurfaceBinderInfo::Explicit,
                    ),
                    SurfaceBinder::new(
                        "f",
                        Some(SurfaceExpr::Pi(
                            Span::dummy(),
                            vec![SurfaceBinder::new(
                                "b",
                                Some({
                                    let mut args = param_exprs.clone();
                                    args.extend([tag(mi), ident("a")]);
                                    plain_app(&pos_f, args)
                                }),
                                SurfaceBinderInfo::Explicit,
                            )],
                            Box::new(plain_app(
                                "Codata.IMIntl",
                                vec![container(&shape_f), container(&pos_f), container(&tgt_f), {
                                    let mut targs = param_exprs.clone();
                                    targs.extend([tag(mi), ident("a"), ident("b")]);
                                    plain_app(&tgt_f, targs)
                                }],
                            )),
                        )),
                        SurfaceBinderInfo::Explicit,
                    ),
                ]);
                bs
            },
            plain_app(
                "Codata.isigmaStep",
                vec![
                    container(&shape_f),
                    container(&pos_f),
                    container(&tgt_f),
                    plain_app(
                        "Codata.IMIntl",
                        vec![container(&shape_f), container(&pos_f), container(&tgt_f)],
                    ),
                    tag(mi),
                ],
            ),
            plain_app("Sigma.mk", vec![ident("a"), ident("f")]),
        ));
        let mut mk_binders = implicit_binders.clone();
        for (obs_name, obs_ty) in m.obs.iter() {
            mk_binders.push(SurfaceBinder::new(
                format!("{obs_name}V").as_str(),
                Some((*obs_ty).clone()),
                SurfaceBinderInfo::Explicit,
            ));
        }
        for (step_name, tgt_mi) in m.steps.iter() {
            mk_binders.push(SurfaceBinder::new(
                format!("{step_name}V").as_str(),
                Some(plain_app(names[*tgt_mi], param_exprs.clone())),
                SurfaceBinderInfo::Explicit,
            ));
        }
        let mk_label = mutual_pack(
            &m.obs
                .iter()
                .map(|(n, _)| ident(&format!("{n}V")))
                .collect::<Vec<_>>(),
        );
        let mk_children: Vec<SurfaceExpr> = m
            .steps
            .iter()
            .map(|(n, _)| ident(&format!("{n}V")))
            .collect();
        let mk_child_fn = if mk_children.len() == 1 {
            lam1("_", mk_children[0].clone())
        } else {
            let tgt_full = {
                let tgt_f = tgt_f.clone();
                let pe = param_exprs.clone();
                let label = mk_label.clone();
                let tag_e = tag(mi);
                move |bpos: SurfaceExpr| -> SurfaceExpr {
                    let mut targs = pe.clone();
                    targs.extend([tag_e.clone(), label.clone(), bpos]);
                    plain_app(&tgt_f, targs)
                }
            };
            lam1(
                "b",
                mut_state_chain_p(
                    &mk_children,
                    0,
                    &plain_app(
                        "Codata.IMIntl",
                        vec![container(&shape_f), container(&pos_f), container(&tgt_f)],
                    ),
                    &tgt_full,
                    ident("b"),
                    poly,
                ),
            )
        };
        out.push(mk_def(
            format!("{}.mk", m.name),
            mk_binders.clone(),
            self_ty.clone(),
            at_app("Codata.IMmk", {
                let mut mkargs = param_exprs.clone();
                mkargs.extend([mk_label.clone(), mk_child_fn]);
                vec![
                    ident("Bool"),
                    container(&shape_f),
                    container(&pos_f),
                    container(&tgt_f),
                    tag(mi),
                    at_app(&mk_step_name, mkargs),
                ]
            }),
        ));
        let mk_call = {
            let mut args = param_exprs.clone();
            args.extend(
                m.obs
                    .iter()
                    .map(|(n, _)| ident(&format!("{n}V")))
                    .chain(m.steps.iter().map(|(n, _)| ident(&format!("{n}V")))),
            );
            at_app(&format!("{}.mk", m.name), args)
        };
        for field_name in m
            .obs
            .iter()
            .map(|(n, _)| *n)
            .chain(m.steps.iter().map(|(n, _)| *n))
        {
            let full = format!("{}.{field_name}", m.name);
            let mut acc_args = param_exprs.clone();
            acc_args.push(mk_call.clone());
            out.push(mk_theorem(
                format!("{full}_mk"),
                mk_binders.clone(),
                SurfaceExpr::App(
                    Span::dummy(),
                    Box::new(ident("Eq")),
                    vec![
                        SurfaceArg::positional(at_app(&full, acc_args)),
                        SurfaceArg::positional(ident(&format!("{field_name}V"))),
                    ],
                ),
                ident("rfl"),
            ));
        }
    }

    // Laws (after both corecs exist, since cross-member laws reference them).
    for (mi, m) in shapes.iter().enumerate() {
        let corec_call = |member: usize, extra: SurfaceExpr| {
            let mut args = param_exprs.clone();
            args.extend([ident("S1"), ident("S2")]);
            args.extend(all_fn_idents.clone());
            args.push(extra);
            at_app(&format!("{}.corec", names[member]), args)
        };
        let law_binders = || {
            let mut bs = implicit_binders.clone();
            bs.extend([
                SurfaceBinder::new("S1", Some(type_u(poly)), SurfaceBinderInfo::Implicit),
                SurfaceBinder::new("S2", Some(type_u(poly)), SurfaceBinderInfo::Implicit),
            ]);
            bs.extend(fn_binders.clone());
            bs.push(SurfaceBinder::new(
                "s",
                Some(ident(if mi == 0 { "S1" } else { "S2" })),
                SurfaceBinderInfo::Explicit,
            ));
            bs
        };
        for (obs_name, _) in &m.obs {
            let full = format!("{}.{obs_name}", m.name);
            let mut acc_args = param_exprs.clone();
            acc_args.push(corec_call(mi, ident("s")));
            out.push(mk_theorem(
                format!("{full}_corec"),
                law_binders(),
                SurfaceExpr::App(
                    Span::dummy(),
                    Box::new(ident("Eq")),
                    vec![
                        SurfaceArg::positional(at_app(&full, acc_args)),
                        SurfaceArg::positional(plain_app(
                            &format!("{}_{obs_name}F", m.name),
                            vec![ident("s")],
                        )),
                    ],
                ),
                ident("rfl"),
            ));
        }
        for (step_name, tgt_mi) in &m.steps {
            let full = format!("{}.{step_name}", m.name);
            let mut acc_args = param_exprs.clone();
            acc_args.push(corec_call(mi, ident("s")));
            out.push(mk_theorem(
                format!("{full}_corec"),
                law_binders(),
                SurfaceExpr::App(
                    Span::dummy(),
                    Box::new(ident("Eq")),
                    vec![
                        SurfaceArg::positional(at_app(&full, acc_args)),
                        SurfaceArg::positional(corec_call(
                            *tgt_mi,
                            plain_app(&format!("{}_{step_name}F", m.name), vec![ident("s")]),
                        )),
                    ],
                ),
                ident("rfl"),
            ));
        }
    }

    out.into_iter().map(|d| set_uparams(d, poly)).collect()
}

// ── indexed codata (the QPFTypes source-index answer at the surface) ──
// `codata C : (n : I) → Type where obs : T n; step : C <idx-expr>` — the
// container index IS the declared index; each recursive field names the
// index its child lives at. Mirrors the hand-validated IStream expansion.

struct IndexedShape<'a> {
    name: &'a str,
    /// The single declared universe parameter, when polymorphic (v1: ≤1).
    poly: Option<&'a str>,
    binders: &'a [SurfaceBinder],
    idx_binders: &'a [SurfaceBinder],
    idx_name: &'a str,
    idx_ty: &'a SurfaceExpr,
    obs: Vec<(&'a str, &'a SurfaceExpr)>,
    /// (field name, target index expressions — one per index binder)
    steps: Vec<(&'a str, Vec<&'a SurfaceExpr>)>,
}

#[allow(clippy::too_many_arguments)]
fn validate_indexed<'a>(
    name: &'a str,
    universe_params: &'a [String],
    binders: &'a [SurfaceBinder],
    pi_binders: &'a [SurfaceBinder],
    fields: &'a [SurfaceField],
    deriving: &[String],
    modifiers: &DeclModifiers,
) -> Result<IndexedShape<'a>, ElabError> {
    let poly = match universe_params {
        [] => None,
        [u] => Some(u.as_str()),
        _ => {
            return Err(unsupported(format!(
                "indexed codata `{name}`: at most ONE universe parameter is \
                 supported in v1"
            )))
        }
    };
    if !deriving.is_empty() || !modifiers.is_default() {
        return Err(unsupported(format!(
            "indexed codata `{name}`: deriving and modifiers are not supported"
        )));
    }
    for b in binders {
        if b.info != SurfaceBinderInfo::Explicit || b.ty.is_none() || b.default.is_some() {
            return Err(unsupported(format!(
                "indexed codata `{name}`: parameters must be simple explicit \
                 binders `(x : T)`"
            )));
        }
    }
    if pi_binders.is_empty() {
        return Err(unsupported(format!(
            "indexed codata `{name}`: at least one index binder is required"
        )));
    }
    for ib in pi_binders {
        if ib.ty.is_none() {
            return Err(unsupported(format!(
                "indexed codata `{name}`: every index binder needs an \
                 explicit type"
            )));
        }
    }
    let idx = &pi_binders[0];
    let idx_ty = idx.ty.as_deref().expect("checked above");
    if fields.len() < 2 {
        return Err(unsupported(format!(
            "indexed codata `{name}`: need at least one observation and one \
             recursive field"
        )));
    }
    // A recursive field is exactly `C p1 … pk <index-expr>` (the shared
    // parameters in order, then one positional index expression).
    let param_names: Vec<&str> = binders.iter().map(|b| b.name.as_str()).collect();
    let target_of = |t: &'a SurfaceExpr| -> Option<Vec<&'a SurfaceExpr>> {
        let SurfaceExpr::App(_, h, args) = strip_parens(t) else {
            return None;
        };
        if !matches!(strip_parens(h), SurfaceExpr::Ident(_, id) if id == name) {
            return None;
        }
        if args.len() != param_names.len() + pi_binders.len()
            || args.iter().any(|a| a.name.is_some())
        {
            return None;
        }
        for (a, pn) in args.iter().zip(&param_names) {
            if !matches!(strip_parens(&a.expr), SurfaceExpr::Ident(_, id) if id == pn) {
                return None;
            }
        }
        Some(
            args[param_names.len()..]
                .iter()
                .map(|a| &a.expr)
                .collect::<Vec<_>>(),
        )
    };
    let mut split = fields.len();
    while split > 0 && target_of(&fields[split - 1].ty).is_some() {
        split -= 1;
    }
    let (obs_fields, step_fields) = fields.split_at(split);
    if step_fields.is_empty() {
        return Err(unsupported(format!(
            "indexed codata `{name}`: the final field must be recursive \
             (`{name} <index-expr>`)"
        )));
    }
    if obs_fields.is_empty() {
        return Err(unsupported(format!(
            "indexed codata `{name}`: need at least one observation field"
        )));
    }
    for f in obs_fields {
        if mentions(&f.ty, name) {
            return Err(unsupported(format!(
                "indexed codata `{name}`: observation `{}` mentions `{name}` \
                 but is not exactly `{name} <index-expr>` — recursive fields \
                 must form the TRAILING block",
                f.name
            )));
        }
    }
    let mut seen: Vec<&str> = Vec::new();
    for f in fields {
        if seen.contains(&f.name.as_str()) {
            return Err(unsupported(format!(
                "indexed codata `{name}`: field names must be distinct"
            )));
        }
        seen.push(&f.name);
    }
    Ok(IndexedShape {
        name,
        poly,
        binders,
        idx_binders: pi_binders,
        idx_name: &idx.name,
        idx_ty,
        obs: obs_fields
            .iter()
            .map(|f| (f.name.as_str(), &f.ty))
            .collect(),
        steps: step_fields
            .iter()
            .map(|f| {
                (
                    f.name.as_str(),
                    target_of(&f.ty).expect("trailing split guarantees a target"),
                )
            })
            .collect(),
    })
}

fn generate_indexed(shape: &IndexedShape<'_>) -> Vec<SurfaceDecl> {
    let IndexedShape {
        name,
        poly,
        binders,
        idx_binders: _,
        idx_name,
        idx_ty,
        obs,
        steps,
    } = shape;
    let poly = *poly;
    let ity = (*idx_ty).clone();
    let param_exprs: Vec<SurfaceExpr> = binders.iter().map(|b| ident(&b.name)).collect();
    let explicit_params: Vec<SurfaceBinder> = binders.to_vec();
    let implicit_params: Vec<SurfaceBinder> = explicit_params
        .iter()
        .map(|b| {
            let mut ib = b.clone();
            ib.info = SurfaceBinderInfo::Implicit;
            ib
        })
        .collect();
    let capp = |f: &str, extra: Vec<SurfaceExpr>| -> SurfaceExpr {
        let mut args = param_exprs.clone();
        args.extend(extra);
        plain_app(f, args)
    };
    let shape_f = format!("{name}.shapeF");
    let pos_f = format!("{name}.posF");
    let tgt_f = format!("{name}.tgtF");
    let mk_step = format!("{name}.mkStep");
    let step_fn = format!("{name}.stepFn");
    let corec = format!("{name}.corec");
    let m = steps.len();
    let k = obs.len();

    let label_ty = obs
        .iter()
        .rev()
        .map(|(_, t)| (*t).clone())
        .reduce(|acc, t| plain_app("PProd", vec![t, acc]))
        .expect("validated: at least one observation");

    let mut out = Vec::new();
    // def C.shapeF (ps) : I → Type := fun <idx> => <label>
    out.push(mk_def(
        shape_f.clone(),
        explicit_params.clone(),
        arrow(ity.clone(), type_u(poly)),
        lam1(idx_name, label_ty),
    ));
    // def C.posF : (i : I) → C.shapeF i → Type := fun _ _ => <pos>
    out.push(mk_def(
        pos_f.clone(),
        explicit_params.clone(),
        pi(
            "i",
            ity.clone(),
            arrow(capp(&shape_f, vec![ident("i")]), type_u(poly)),
        ),
        SurfaceExpr::Lambda(
            Span::dummy(),
            vec![
                SurfaceBinder::new("_", None, SurfaceBinderInfo::Explicit),
                SurfaceBinder::new("_", None, SurfaceBinderInfo::Explicit),
            ],
            Box::new(mut_pos_ty_p(m, poly)),
        ),
    ));
    // def C.tgtF : (i : I) → (a : shapeF i) → posF i a → I :=
    //   fun <idx> _ pb => <Sum.rec chain of index exprs>
    let idx_targets: Vec<SurfaceExpr> = steps.iter().map(|(_, e)| e[0].clone()).collect();
    let tgt_body = if m == 1 {
        SurfaceExpr::Lambda(
            Span::dummy(),
            vec![
                SurfaceBinder::new(*idx_name, None, SurfaceBinderInfo::Explicit),
                SurfaceBinder::new("_", None, SurfaceBinderInfo::Explicit),
                SurfaceBinder::new("_", None, SurfaceBinderInfo::Explicit),
            ],
            Box::new(idx_targets[0].clone()),
        )
    } else {
        SurfaceExpr::Lambda(
            Span::dummy(),
            vec![
                SurfaceBinder::new(*idx_name, None, SurfaceBinderInfo::Explicit),
                SurfaceBinder::new("_", None, SurfaceBinderInfo::Explicit),
                SurfaceBinder::new("pb", None, SurfaceBinderInfo::Explicit),
            ],
            Box::new(mut_idx_chain_p(&idx_targets, &ity, ident("pb"), None)),
        )
    };
    out.push(mk_def(
        tgt_f.clone(),
        explicit_params.clone(),
        pi("i", ity.clone(), {
            pi("a", capp(&shape_f, vec![ident("i")]), {
                arrow(capp(&pos_f, vec![ident("i"), ident("a")]), ity.clone())
            })
        }),
        tgt_body,
    ));
    // def C (idx : I) : Type := @Codata.IMIntl I shapeF posF tgtF idx
    out.push(mk_def(
        (*name).to_string(),
        {
            let mut bs = explicit_params.clone();
            bs.push(SurfaceBinder::new(
                *idx_name,
                Some(ity.clone()),
                SurfaceBinderInfo::Explicit,
            ));
            bs
        },
        type_u(poly),
        at_app(
            "Codata.IMIntl",
            vec![
                ity.clone(),
                capp(&shape_f, vec![]),
                capp(&pos_f, vec![]),
                capp(&tgt_f, vec![]),
                ident(idx_name),
            ],
        ),
    ));
    let self_at = |e: SurfaceExpr| capp(name, vec![e]);
    let idx_binder = SurfaceBinder::new(*idx_name, Some(ity.clone()), SurfaceBinderInfo::Implicit);
    // Observation accessors.
    for (oi, (obs_name, obs_ty)) in obs.iter().enumerate() {
        let mut sel = at_app(
            "Codata.IMhead",
            vec![
                ity.clone(),
                capp(&shape_f, vec![]),
                capp(&pos_f, vec![]),
                capp(&tgt_f, vec![]),
                ident(idx_name),
                ident("x"),
            ],
        );
        for _ in 0..oi {
            sel = SurfaceExpr::Proj(Span::dummy(), Box::new(sel), Projection::Index(2));
        }
        if oi + 1 < k {
            sel = SurfaceExpr::Proj(Span::dummy(), Box::new(sel), Projection::Index(1));
        }
        out.push(mk_def(
            format!("{name}.{obs_name}"),
            {
                let mut bs = implicit_params.clone();
                bs.extend([
                    idx_binder.clone(),
                    SurfaceBinder::new(
                        "x",
                        Some(self_at(ident(idx_name))),
                        SurfaceBinderInfo::Explicit,
                    ),
                ]);
                bs
            },
            (*obs_ty).clone(),
            sel,
        ));
    }
    // Recursive accessors (result type at the moved index).
    for (si, (step_name, idx_expr)) in steps.iter().enumerate() {
        out.push(mk_def(
            format!("{name}.{step_name}"),
            {
                let mut bs = implicit_params.clone();
                bs.extend([
                    idx_binder.clone(),
                    SurfaceBinder::new(
                        "x",
                        Some(self_at(ident(idx_name))),
                        SurfaceBinderInfo::Explicit,
                    ),
                ]);
                bs
            },
            self_at(idx_expr[0].clone()),
            at_app(
                "Codata.IMchild",
                vec![
                    ity.clone(),
                    capp(&shape_f, vec![]),
                    capp(&pos_f, vec![]),
                    capp(&tgt_f, vec![]),
                    ident(idx_name),
                    ident("x"),
                    mut_pos_point(si, m),
                ],
            ),
        ));
    }
    // mkStep {S : I → Type} (idx) (a) (f)
    let s_binder = SurfaceBinder::new(
        "S",
        Some(arrow(ity.clone(), type_u(poly))),
        SurfaceBinderInfo::Implicit,
    );
    out.push(mk_def(
        mk_step.clone(),
        {
            let mut bs = implicit_params.clone();
            bs.extend(vec![
                s_binder.clone(),
                SurfaceBinder::new(*idx_name, Some(ity.clone()), SurfaceBinderInfo::Explicit),
                SurfaceBinder::new(
                    "a",
                    Some(capp(&shape_f, vec![ident(idx_name)])),
                    SurfaceBinderInfo::Explicit,
                ),
                SurfaceBinder::new(
                    "f",
                    Some(SurfaceExpr::Pi(
                        Span::dummy(),
                        vec![SurfaceBinder::new(
                            "b",
                            Some(capp(&pos_f, vec![ident(idx_name), ident("a")])),
                            SurfaceBinderInfo::Explicit,
                        )],
                        Box::new(SurfaceExpr::App(
                            Span::dummy(),
                            Box::new(ident("S")),
                            vec![SurfaceArg::positional(capp(
                                &tgt_f,
                                vec![ident(idx_name), ident("a"), ident("b")],
                            ))],
                        )),
                    )),
                    SurfaceBinderInfo::Explicit,
                ),
            ]);
            bs
        },
        plain_app(
            "Codata.isigmaStep",
            vec![
                capp(&shape_f, vec![]),
                capp(&pos_f, vec![]),
                capp(&tgt_f, vec![]),
                ident("S"),
                ident(idx_name),
            ],
        ),
        plain_app("Sigma.mk", vec![ident("a"), ident("f")]),
    ));
    // Per-field function binders: obsF : (n : I) → S n → T; stepF : (n : I) → S n → S <idx-expr>
    let fn_ty = |result: SurfaceExpr| {
        SurfaceExpr::Pi(
            Span::dummy(),
            vec![SurfaceBinder::new(
                *idx_name,
                Some(ity.clone()),
                SurfaceBinderInfo::Explicit,
            )],
            Box::new(arrow(
                SurfaceExpr::App(
                    Span::dummy(),
                    Box::new(ident("S")),
                    vec![SurfaceArg::positional(ident(idx_name))],
                ),
                result,
            )),
        )
    };
    let mut fn_binders: Vec<SurfaceBinder> = Vec::new();
    for (obs_name, obs_ty) in obs {
        fn_binders.push(SurfaceBinder::new(
            format!("{obs_name}F").as_str(),
            Some(fn_ty((*obs_ty).clone())),
            SurfaceBinderInfo::Explicit,
        ));
    }
    for (step_name, idx_expr) in steps {
        fn_binders.push(SurfaceBinder::new(
            format!("{step_name}F").as_str(),
            Some(fn_ty(SurfaceExpr::App(
                Span::dummy(),
                Box::new(ident("S")),
                vec![SurfaceArg::positional(idx_expr[0].clone())],
            ))),
            SurfaceBinderInfo::Explicit,
        ));
    }
    let all_fn_idents: Vec<SurfaceExpr> = obs
        .iter()
        .map(|(n, _)| ident(&format!("{n}F")))
        .chain(steps.iter().map(|(n, _)| ident(&format!("{n}F"))))
        .collect();
    // stepFn
    let label_pack = mutual_pack(
        &obs.iter()
            .map(|(n, _)| plain_app(&format!("{n}F"), vec![ident("jv"), ident("sv")]))
            .collect::<Vec<_>>(),
    );
    let branch_states: Vec<SurfaceExpr> = steps
        .iter()
        .map(|(n, _)| plain_app(&format!("{n}F"), vec![ident("jv"), ident("sv")]))
        .collect();
    let child = if m == 1 {
        lam1("_", branch_states[0].clone())
    } else {
        let tgt_full = {
            let tgt_f = tgt_f.clone();
            let tf_params = param_exprs.clone();
            let label_pack = label_pack.clone();
            move |bpos: SurfaceExpr| -> SurfaceExpr {
                let mut args = tf_params.clone();
                args.extend([ident("jv"), label_pack.clone(), bpos]);
                plain_app(&tgt_f, args)
            }
        };
        lam1(
            "pb",
            mut_state_chain_p(&branch_states, 0, &ident("S"), &tgt_full, ident("pb"), None),
        )
    };
    let mut mkargs = param_exprs.clone();
    mkargs.extend([ident("S"), ident("jv"), label_pack.clone(), child]);
    out.push(mk_def(
        step_fn.clone(),
        {
            let mut bs = implicit_params.clone();
            bs.push(s_binder.clone());
            bs.extend(fn_binders.clone());
            bs
        },
        pi("j", ity.clone(), {
            arrow(
                SurfaceExpr::App(
                    Span::dummy(),
                    Box::new(ident("S")),
                    vec![SurfaceArg::positional(ident("j"))],
                ),
                plain_app(
                    "Codata.isigmaStep",
                    vec![
                        capp(&shape_f, vec![]),
                        capp(&pos_f, vec![]),
                        capp(&tgt_f, vec![]),
                        ident("S"),
                        ident("j"),
                    ],
                ),
            )
        }),
        SurfaceExpr::Lambda(
            Span::dummy(),
            vec![
                SurfaceBinder::new("jv", None, SurfaceBinderInfo::Explicit),
                SurfaceBinder::new("sv", None, SurfaceBinderInfo::Explicit),
            ],
            Box::new(at_app(&mk_step, mkargs)),
        ),
    ));
    // corec
    let step_call = {
        let mut args = param_exprs.clone();
        args.push(ident("S"));
        args.extend(all_fn_idents.clone());
        at_app(&step_fn, args)
    };
    out.push(mk_def(
        corec.clone(),
        {
            let mut bs = implicit_params.clone();
            bs.push(s_binder.clone());
            bs.extend(fn_binders.clone());
            bs.extend([
                SurfaceBinder::new(*idx_name, Some(ity.clone()), SurfaceBinderInfo::Explicit),
                SurfaceBinder::new(
                    "s",
                    Some(SurfaceExpr::App(
                        Span::dummy(),
                        Box::new(ident("S")),
                        vec![SurfaceArg::positional(ident(idx_name))],
                    )),
                    SurfaceBinderInfo::Explicit,
                ),
            ]);
            bs
        },
        self_at(ident(idx_name)),
        at_app(
            "Codata.IMcorec",
            vec![
                ity.clone(),
                capp(&shape_f, vec![]),
                capp(&pos_f, vec![]),
                capp(&tgt_f, vec![]),
                ident("S"),
                step_call,
                ident(idx_name),
                ident("s"),
            ],
        ),
    ));
    // The CONSTRUCTOR: C.mk {ps} {idx} (field values) — the finite
    // one-layer node at the given index; children live at their own
    // target indices. Per-field laws are rfl.
    let mk_step_name = format!("{name}.mkStep2");
    out.push(mk_def(
        mk_step_name.clone(),
        {
            let mut bs = implicit_params.clone();
            bs.extend([
                SurfaceBinder::new(*idx_name, Some(ity.clone()), SurfaceBinderInfo::Implicit),
                SurfaceBinder::new(
                    "a",
                    Some(capp(&shape_f, vec![ident(idx_name)])),
                    SurfaceBinderInfo::Explicit,
                ),
                SurfaceBinder::new(
                    "f",
                    Some(SurfaceExpr::Pi(
                        Span::dummy(),
                        vec![SurfaceBinder::new(
                            "b",
                            Some(capp(&pos_f, vec![ident(idx_name), ident("a")])),
                            SurfaceBinderInfo::Explicit,
                        )],
                        Box::new(plain_app("Codata.IMIntl", {
                            vec![
                                capp(&shape_f, vec![]),
                                capp(&pos_f, vec![]),
                                capp(&tgt_f, vec![]),
                                capp(&tgt_f, vec![ident(idx_name), ident("a"), ident("b")]),
                            ]
                        })),
                    )),
                    SurfaceBinderInfo::Explicit,
                ),
            ]);
            bs
        },
        plain_app(
            "Codata.isigmaStep",
            vec![
                capp(&shape_f, vec![]),
                capp(&pos_f, vec![]),
                capp(&tgt_f, vec![]),
                plain_app(
                    "Codata.IMIntl",
                    vec![
                        capp(&shape_f, vec![]),
                        capp(&pos_f, vec![]),
                        capp(&tgt_f, vec![]),
                    ],
                ),
                ident(idx_name),
            ],
        ),
        plain_app("Sigma.mk", vec![ident("a"), ident("f")]),
    ));
    let mut mk_binders = implicit_params.clone();
    mk_binders.push(SurfaceBinder::new(
        *idx_name,
        Some(ity.clone()),
        SurfaceBinderInfo::Implicit,
    ));
    for (obs_name, obs_ty) in obs.iter() {
        mk_binders.push(SurfaceBinder::new(
            format!("{obs_name}V").as_str(),
            Some((*obs_ty).clone()),
            SurfaceBinderInfo::Explicit,
        ));
    }
    for (step_name, idx_expr) in steps.iter() {
        mk_binders.push(SurfaceBinder::new(
            format!("{step_name}V").as_str(),
            Some(self_at(idx_expr[0].clone())),
            SurfaceBinderInfo::Explicit,
        ));
    }
    let mk_label = mutual_pack(
        &obs.iter()
            .map(|(n, _)| ident(&format!("{n}V")))
            .collect::<Vec<_>>(),
    );
    let mk_children: Vec<SurfaceExpr> =
        steps.iter().map(|(n, _)| ident(&format!("{n}V"))).collect();
    let mk_child_fn = if mk_children.len() == 1 {
        lam1("_", mk_children[0].clone())
    } else {
        let tgt_full = {
            let tgt_f = tgt_f.clone();
            let label = mk_label.clone();
            let idx = ident(idx_name);
            move |bpos: SurfaceExpr| -> SurfaceExpr {
                plain_app(&tgt_f, vec![idx.clone(), label.clone(), bpos])
            }
        };
        lam1(
            "b",
            mut_state_chain_p(
                &mk_children,
                0,
                &plain_app(
                    "Codata.IMIntl",
                    vec![
                        capp(&shape_f, vec![]),
                        capp(&pos_f, vec![]),
                        capp(&tgt_f, vec![]),
                    ],
                ),
                &tgt_full,
                ident("b"),
                None,
            ),
        )
    };
    out.push(mk_def(
        format!("{name}.mk"),
        mk_binders.clone(),
        self_at(ident(idx_name)),
        at_app("Codata.IMmk", {
            let mut mkargs = param_exprs.clone();
            mkargs.extend([ident(idx_name), mk_label.clone(), mk_child_fn]);
            vec![
                ity.clone(),
                capp(&shape_f, vec![]),
                capp(&pos_f, vec![]),
                capp(&tgt_f, vec![]),
                ident(idx_name),
                at_app(&mk_step_name, mkargs),
            ]
        }),
    ));
    let mk_call = {
        let mut args = param_exprs.clone();
        args.push(ident(idx_name));
        args.extend(
            obs.iter()
                .map(|(n, _)| ident(&format!("{n}V")))
                .chain(steps.iter().map(|(n, _)| ident(&format!("{n}V")))),
        );
        at_app(&format!("{name}.mk"), args)
    };
    for field_name in obs
        .iter()
        .map(|(n, _)| *n)
        .chain(steps.iter().map(|(n, _)| *n))
    {
        let full = format!("{name}.{field_name}");
        let mut acc_args = param_exprs.clone();
        acc_args.extend([ident(idx_name), mk_call.clone()]);
        out.push(mk_theorem(
            format!("{full}_mk"),
            mk_binders.clone(),
            SurfaceExpr::App(
                Span::dummy(),
                Box::new(ident("Eq")),
                vec![
                    SurfaceArg::positional(at_app(&full, acc_args)),
                    SurfaceArg::positional(ident(&format!("{field_name}V"))),
                ],
            ),
            ident("rfl"),
        ));
    }

    // Laws.
    let corec_call = |idx: SurfaceExpr, extra: SurfaceExpr| {
        let mut args = param_exprs.clone();
        args.push(ident("S"));
        args.extend(all_fn_idents.clone());
        args.extend([idx, extra]);
        at_app(&corec, args)
    };
    let law_binders = || {
        let mut bs = implicit_params.clone();
        bs.push(s_binder.clone());
        bs.extend(fn_binders.clone());
        bs.extend([
            SurfaceBinder::new(*idx_name, Some(ity.clone()), SurfaceBinderInfo::Explicit),
            SurfaceBinder::new(
                "s",
                Some(SurfaceExpr::App(
                    Span::dummy(),
                    Box::new(ident("S")),
                    vec![SurfaceArg::positional(ident(idx_name))],
                )),
                SurfaceBinderInfo::Explicit,
            ),
        ]);
        bs
    };
    for (obs_name, _) in obs {
        let full = format!("{name}.{obs_name}");
        out.push(mk_theorem(
            format!("{full}_corec"),
            law_binders(),
            SurfaceExpr::App(
                Span::dummy(),
                Box::new(ident("Eq")),
                vec![
                    SurfaceArg::positional(plain_app(
                        &full,
                        vec![corec_call(ident(idx_name), ident("s"))],
                    )),
                    SurfaceArg::positional(plain_app(
                        &format!("{obs_name}F"),
                        vec![ident(idx_name), ident("s")],
                    )),
                ],
            ),
            ident("rfl"),
        ));
    }
    for (step_name, idx_expr) in steps {
        let full = format!("{name}.{step_name}");
        out.push(mk_theorem(
            format!("{full}_corec"),
            law_binders(),
            SurfaceExpr::App(
                Span::dummy(),
                Box::new(ident("Eq")),
                vec![
                    SurfaceArg::positional(plain_app(
                        &full,
                        vec![corec_call(ident(idx_name), ident("s"))],
                    )),
                    SurfaceArg::positional(corec_call(
                        idx_expr[0].clone(),
                        plain_app(&format!("{step_name}F"), vec![ident(idx_name), ident("s")]),
                    )),
                ],
            ),
            ident("rfl"),
        ));
    }

    out.into_iter().map(|d| set_uparams(d, poly)).collect()
}

/// Non-dependent Sum.rec chain returning index expressions (motive: the
/// index type).
fn mut_idx_chain_p(
    targets: &[SurfaceExpr],
    ity: &SurfaceExpr,
    scrut: SurfaceExpr,
    poly: Option<&str>,
) -> SurfaceExpr {
    match targets {
        [only] => only.clone(),
        [first, rest @ ..] => {
            let inner = if rest.len() == 1 {
                lam1("_", rest[0].clone())
            } else {
                lam1("b2", mut_idx_chain_p(rest, ity, ident("b2"), poly))
            };
            SurfaceExpr::App(
                Span::dummy(),
                Box::new(SurfaceExpr::Explicit(
                    Span::dummy(),
                    Box::new(ident("Sum.rec")),
                )),
                vec![
                    SurfaceArg::positional(punit_ty_p(poly)),
                    SurfaceArg::positional(mut_pos_ty_p(rest.len(), poly)),
                    SurfaceArg::positional(lam1("_", ity.clone())),
                    SurfaceArg::positional(lam1("_", first.clone())),
                    SurfaceArg::positional(inner),
                    SurfaceArg::positional(scrut),
                ],
            )
        }
        [] => unreachable!("validated: at least one recursive field"),
    }
}

// ── n-member mutual codata (Σ-tags: nested Sum-of-Units) ──
// Tag type = mut_pos_ty_p(n, poly); member i lives at mut_pos_point(i, n). Every
// per-tag container tower is a nested dependent-motive Sum.rec chain: the
// outer motive ranges over the FULL tag, inner levels over inr-wrapped
// payloads (the hand-validated three-member ring in the graduation
// source).

/// Nested Sum.rec chain over the n-point tag with per-member cases.
/// `mk_m(full_tag)` builds the motive body at a given full-tag expression.
fn tag_tower_p(
    cases: &[SurfaceExpr],
    mk_m: &dyn Fn(SurfaceExpr) -> SurfaceExpr,
    depth: usize,
    scrut: SurfaceExpr,
    poly: Option<&str>,
) -> SurfaceExpr {
    match cases {
        [only] => only.clone(),
        [first, rest @ ..] => {
            let wrap = |e: SurfaceExpr, d: usize| -> SurfaceExpr {
                let mut w = e;
                for _ in 0..d {
                    w = plain_app("Sum.inr", vec![w]);
                }
                w
            };
            let motive = lam1("tv", mk_m(wrap(ident("tv"), depth)));
            let inner = if rest.len() == 1 {
                lam1("_", rest[0].clone())
            } else {
                lam1("ti", tag_tower_p(rest, mk_m, depth + 1, ident("ti"), poly))
            };
            SurfaceExpr::App(
                Span::dummy(),
                Box::new(SurfaceExpr::Explicit(
                    Span::dummy(),
                    Box::new(ident("Sum.rec")),
                )),
                vec![
                    SurfaceArg::positional(punit_ty_p(poly)),
                    SurfaceArg::positional(mut_pos_ty_p(rest.len(), poly)),
                    SurfaceArg::positional(motive),
                    SurfaceArg::positional(lam1("_", first.clone())),
                    SurfaceArg::positional(inner),
                    SurfaceArg::positional(scrut),
                ],
            )
        }
        [] => unreachable!("mutual blocks have members"),
    }
}

fn generate_mutual_n(shapes: &[MutualMember<'_>], poly: Option<&str>) -> Vec<SurfaceDecl> {
    let n = shapes.len();
    let names: Vec<&str> = shapes.iter().map(|m| m.name).collect();
    let param_exprs: Vec<SurfaceExpr> = shapes[0].binders.iter().map(|b| ident(&b.name)).collect();
    let explicit_binders: Vec<SurfaceBinder> = shapes[0].binders.to_vec();
    let implicit_binders: Vec<SurfaceBinder> = explicit_binders
        .iter()
        .map(|b| {
            let mut ib = b.clone();
            ib.info = SurfaceBinderInfo::Implicit;
            ib
        })
        .collect();
    let tag_ty = mut_pos_ty_p(n, poly);
    let tag = |mi: usize| mut_pos_point(mi, n);
    let state_name = |mi: usize| format!("S{}", mi + 1);

    let joint = names.join(".");
    let shape_f = format!("{joint}.shapeF");
    let pos_f = format!("{joint}.posF");
    let tgt_f = format!("{joint}.tgtF");
    let st_f = format!("{joint}.stF");
    let mk_step = format!("{joint}.mkStep");
    let step_fn = format!("{joint}.step");
    let container = |f: &str| plain_app(f, param_exprs.clone());
    let st_container = plain_app(
        &st_f,
        (0..n).map(|i| ident(&state_name(i))).collect::<Vec<_>>(),
    );
    let state_binders: Vec<SurfaceBinder> = (0..n)
        .map(|i| {
            SurfaceBinder::new(
                state_name(i).as_str(),
                Some(type_u(poly)),
                SurfaceBinderInfo::Implicit,
            )
        })
        .collect();

    let mut out = Vec::new();

    // shapeF: non-dependent Type tower over member labels.
    out.push(mk_def(
        shape_f.clone(),
        explicit_binders.clone(),
        arrow(tag_ty.clone(), type_u(poly)),
        lam1(
            "tg",
            tag_tower_p(
                &shapes
                    .iter()
                    .map(|m| mutual_label_ty_p(&m.obs, poly))
                    .collect::<Vec<_>>(),
                &|_| type_u(poly),
                0,
                ident("tg"),
                poly,
            ),
        ),
    ));
    // posF: dependent tower (motive: shapeF ps full → Type).
    {
        let shape_f2 = shape_f.clone();
        let pe = param_exprs.clone();
        out.push(mk_def(
            pos_f.clone(),
            explicit_binders.clone(),
            pi("i", tag_ty.clone(), {
                let mut args = param_exprs.clone();
                args.push(ident("i"));
                arrow(plain_app(&shape_f, args), type_u(poly))
            }),
            lam1(
                "tg",
                tag_tower_p(
                    &shapes
                        .iter()
                        .map(|m| lam1("_", mut_pos_ty_p(m.steps.len(), poly)))
                        .collect::<Vec<_>>(),
                    &move |full| {
                        let mut args = pe.clone();
                        args.push(full);
                        arrow(plain_app(&shape_f2, args), type_u(poly))
                    },
                    0,
                    ident("tg"),
                    poly,
                ),
            ),
        ));
    }
    // tgtF: dependent tower (motive: (a : shapeF) → posF a → tagTy).
    {
        let shape_f2 = shape_f.clone();
        let pos_f2 = pos_f.clone();
        let pe = param_exprs.clone();
        let tt = tag_ty.clone();
        let tgt_cases: Vec<SurfaceExpr> = shapes
            .iter()
            .map(|m| {
                let targets: Vec<SurfaceExpr> = m.steps.iter().map(|(_, t)| tag(*t)).collect();
                if targets.len() == 1 {
                    SurfaceExpr::Lambda(
                        Span::dummy(),
                        vec![
                            SurfaceBinder::new("_", None, SurfaceBinderInfo::Explicit),
                            SurfaceBinder::new("_", None, SurfaceBinderInfo::Explicit),
                        ],
                        Box::new(targets[0].clone()),
                    )
                } else {
                    SurfaceExpr::Lambda(
                        Span::dummy(),
                        vec![
                            SurfaceBinder::new("_", None, SurfaceBinderInfo::Explicit),
                            SurfaceBinder::new("pb", None, SurfaceBinderInfo::Explicit),
                        ],
                        Box::new(mut_idx_chain_p(&targets, &tag_ty, ident("pb"), poly)),
                    )
                }
            })
            .collect();
        out.push(mk_def(
            tgt_f.clone(),
            explicit_binders.clone(),
            pi("i", tag_ty.clone(), {
                let mut sargs = param_exprs.clone();
                sargs.push(ident("i"));
                pi("a", plain_app(&shape_f, sargs), {
                    let mut pargs = param_exprs.clone();
                    pargs.extend([ident("i"), ident("a")]);
                    arrow(plain_app(&pos_f, pargs), tag_ty.clone())
                })
            }),
            lam1(
                "tg",
                tag_tower_p(
                    &tgt_cases,
                    &move |full| {
                        let mut sargs = pe.clone();
                        sargs.push(full.clone());
                        pi("a", plain_app(&shape_f2, sargs), {
                            let mut pargs = pe.clone();
                            pargs.extend([full.clone(), ident("a")]);
                            arrow(plain_app(&pos_f2, pargs), tt.clone())
                        })
                    },
                    0,
                    ident("tg"),
                    poly,
                ),
            ),
        ));
    }

    // Carriers + accessors (same as the 2-member path modulo tags).
    for (mi, m) in shapes.iter().enumerate() {
        out.push(mk_def(
            m.name.to_string(),
            explicit_binders.clone(),
            type_u(poly),
            at_app(
                "Codata.IMIntl",
                vec![
                    tag_ty.clone(),
                    container(&shape_f),
                    container(&pos_f),
                    container(&tgt_f),
                    tag(mi),
                ],
            ),
        ));
        let _ = m;
    }
    for (mi, m) in shapes.iter().enumerate() {
        let self_ty = plain_app(m.name, param_exprs.clone());
        let k = m.obs.len();
        for (oi, (obs_name, obs_ty)) in m.obs.iter().enumerate() {
            let mut sel = at_app(
                "Codata.IMhead",
                vec![
                    tag_ty.clone(),
                    container(&shape_f),
                    container(&pos_f),
                    container(&tgt_f),
                    tag(mi),
                    ident("x"),
                ],
            );
            for _ in 0..oi {
                sel = SurfaceExpr::Proj(Span::dummy(), Box::new(sel), Projection::Index(2));
            }
            if oi + 1 < k {
                sel = SurfaceExpr::Proj(Span::dummy(), Box::new(sel), Projection::Index(1));
            }
            out.push(mk_def(
                format!("{}.{obs_name}", m.name),
                {
                    let mut bs = implicit_binders.clone();
                    bs.push(SurfaceBinder::new(
                        "x",
                        Some(self_ty.clone()),
                        SurfaceBinderInfo::Explicit,
                    ));
                    bs
                },
                (*obs_ty).clone(),
                sel,
            ));
        }
        let mcount = m.steps.len();
        for (si, (step_name, tgt_mi)) in m.steps.iter().enumerate() {
            out.push(mk_def(
                format!("{}.{step_name}", m.name),
                {
                    let mut bs = implicit_binders.clone();
                    bs.push(SurfaceBinder::new(
                        "x",
                        Some(self_ty.clone()),
                        SurfaceBinderInfo::Explicit,
                    ));
                    bs
                },
                plain_app(names[*tgt_mi], param_exprs.clone()),
                at_app(
                    "Codata.IMchild",
                    vec![
                        tag_ty.clone(),
                        container(&shape_f),
                        container(&pos_f),
                        container(&tgt_f),
                        tag(mi),
                        ident("x"),
                        mut_pos_point(si, mcount),
                    ],
                ),
            ));
        }
    }

    // stF: non-dependent Type tower over the states.
    out.push(mk_def(
        st_f.clone(),
        (0..n)
            .map(|i| {
                SurfaceBinder::new(
                    state_name(i).as_str(),
                    Some(type_u(poly)),
                    SurfaceBinderInfo::Explicit,
                )
            })
            .collect(),
        arrow(tag_ty.clone(), type_u(poly)),
        lam1(
            "tg",
            tag_tower_p(
                &(0..n).map(|i| ident(&state_name(i))).collect::<Vec<_>>(),
                &|_| type_u(poly),
                0,
                ident("tg"),
                poly,
            ),
        ),
    ));
    // mkStep.
    out.push(mk_def(
        mk_step.clone(),
        {
            let mut bs = implicit_binders.clone();
            bs.extend(state_binders.clone());
            bs.extend([
                SurfaceBinder::new("tg", Some(tag_ty.clone()), SurfaceBinderInfo::Explicit),
                SurfaceBinder::new(
                    "a",
                    Some({
                        let mut args = param_exprs.clone();
                        args.push(ident("tg"));
                        plain_app(&shape_f, args)
                    }),
                    SurfaceBinderInfo::Explicit,
                ),
                SurfaceBinder::new(
                    "f",
                    Some(SurfaceExpr::Pi(
                        Span::dummy(),
                        vec![SurfaceBinder::new(
                            "b",
                            Some({
                                let mut args = param_exprs.clone();
                                args.extend([ident("tg"), ident("a")]);
                                plain_app(&pos_f, args)
                            }),
                            SurfaceBinderInfo::Explicit,
                        )],
                        Box::new(SurfaceExpr::App(
                            Span::dummy(),
                            Box::new(st_container.clone()),
                            vec![SurfaceArg::positional({
                                let mut args = param_exprs.clone();
                                args.extend([ident("tg"), ident("a"), ident("b")]);
                                plain_app(&tgt_f, args)
                            })],
                        )),
                    )),
                    SurfaceBinderInfo::Explicit,
                ),
            ]);
            bs
        },
        plain_app(
            "Codata.isigmaStep",
            vec![
                container(&shape_f),
                container(&pos_f),
                container(&tgt_f),
                st_container.clone(),
                ident("tg"),
            ],
        ),
        plain_app("Sigma.mk", vec![ident("a"), ident("f")]),
    ));

    // Per-field function binders across all members, in member order.
    let mut fn_binders: Vec<SurfaceBinder> = Vec::new();
    for (mi, m) in shapes.iter().enumerate() {
        let s_own = state_name(mi);
        for (obs_name, obs_ty) in &m.obs {
            fn_binders.push(SurfaceBinder::new(
                format!("{}_{obs_name}F", m.name).as_str(),
                Some(arrow(ident(&s_own), (*obs_ty).clone())),
                SurfaceBinderInfo::Explicit,
            ));
        }
        for (step_name, tgt_mi) in &m.steps {
            fn_binders.push(SurfaceBinder::new(
                format!("{}_{step_name}F", m.name).as_str(),
                Some(arrow(ident(&s_own), ident(&state_name(*tgt_mi)))),
                SurfaceBinderInfo::Explicit,
            ));
        }
    }
    let all_fn_idents: Vec<SurfaceExpr> = shapes
        .iter()
        .flat_map(|m| {
            m.obs
                .iter()
                .map(|(o, _)| ident(&format!("{}_{o}F", m.name)))
                .chain(
                    m.steps
                        .iter()
                        .map(|(st, _)| ident(&format!("{}_{st}F", m.name))),
                )
                .collect::<Vec<_>>()
        })
        .collect();

    // step: dependent tower whose member cases build mkStep applications.
    {
        let step_cases: Vec<SurfaceExpr> = shapes
            .iter()
            .enumerate()
            .map(|(mi, m)| {
                let label = mutual_pack(
                    &m.obs
                        .iter()
                        .map(|(o, _)| plain_app(&format!("{}_{o}F", m.name), vec![ident("sv")]))
                        .collect::<Vec<_>>(),
                );
                let branch_states: Vec<SurfaceExpr> = m
                    .steps
                    .iter()
                    .map(|(st, _)| plain_app(&format!("{}_{st}F", m.name), vec![ident("sv")]))
                    .collect();
                let child = if branch_states.len() == 1 {
                    lam1("_", branch_states[0].clone())
                } else {
                    let tgt_full = {
                        let param_exprs = param_exprs.clone();
                        let tgt_f = tgt_f.clone();
                        let label = label.clone();
                        let tag_e = tag(mi);
                        move |bpos: SurfaceExpr| -> SurfaceExpr {
                            let mut args = param_exprs.clone();
                            args.extend([tag_e.clone(), label.clone(), bpos]);
                            plain_app(&tgt_f, args)
                        }
                    };
                    lam1(
                        "pb",
                        mut_state_chain_p(
                            &branch_states,
                            0,
                            &st_container,
                            &tgt_full,
                            ident("pb"),
                            poly,
                        ),
                    )
                };
                let mut mk_args = param_exprs.clone();
                mk_args.extend((0..n).map(|i| ident(&state_name(i))));
                mk_args.extend([tag(mi), label, child]);
                lam1("sv", at_app(&mk_step, mk_args))
            })
            .collect();
        let st_c = st_container.clone();
        let sf = shape_f.clone();
        let pf = pos_f.clone();
        let tf = tgt_f.clone();
        let pe = param_exprs.clone();
        out.push(mk_def(
            step_fn.clone(),
            {
                let mut bs = implicit_binders.clone();
                bs.extend(state_binders.clone());
                bs.extend(fn_binders.clone());
                bs
            },
            pi("j", tag_ty.clone(), {
                arrow(
                    SurfaceExpr::App(
                        Span::dummy(),
                        Box::new(st_container.clone()),
                        vec![SurfaceArg::positional(ident("j"))],
                    ),
                    plain_app(
                        "Codata.isigmaStep",
                        vec![
                            container(&shape_f),
                            container(&pos_f),
                            container(&tgt_f),
                            st_container.clone(),
                            ident("j"),
                        ],
                    ),
                )
            }),
            lam1(
                "j",
                tag_tower_p(
                    &step_cases,
                    &move |full| {
                        arrow(
                            SurfaceExpr::App(
                                Span::dummy(),
                                Box::new(st_c.clone()),
                                vec![SurfaceArg::positional(full.clone())],
                            ),
                            plain_app(
                                "Codata.isigmaStep",
                                vec![
                                    plain_app(&sf, pe.clone()),
                                    plain_app(&pf, pe.clone()),
                                    plain_app(&tf, pe.clone()),
                                    st_c.clone(),
                                    full,
                                ],
                            ),
                        )
                    },
                    0,
                    ident("j"),
                    poly,
                ),
            ),
        ));
    }

    // Per-member corec + laws.
    for (mi, m) in shapes.iter().enumerate() {
        let self_ty = plain_app(m.name, param_exprs.clone());
        let corec_name = format!("{}.corec", m.name);
        let step_call = {
            let mut args = param_exprs.clone();
            args.extend((0..n).map(|i| ident(&state_name(i))));
            args.extend(all_fn_idents.clone());
            at_app(&step_fn, args)
        };
        out.push(mk_def(
            corec_name,
            {
                let mut bs = implicit_binders.clone();
                bs.extend(state_binders.clone());
                bs.extend(fn_binders.clone());
                bs.push(SurfaceBinder::new(
                    "s",
                    Some(ident(&state_name(mi))),
                    SurfaceBinderInfo::Explicit,
                ));
                bs
            },
            self_ty,
            at_app(
                "Codata.IMcorec",
                vec![
                    tag_ty.clone(),
                    container(&shape_f),
                    container(&pos_f),
                    container(&tgt_f),
                    st_container.clone(),
                    step_call,
                    tag(mi),
                    ident("s"),
                ],
            ),
        ));
    }
    // Per-member CONSTRUCTORS: M.mk (field values) via Codata.IMmk at the
    // member's tag; children typed at their target members. rfl laws.
    for (mi, m) in shapes.iter().enumerate() {
        let self_ty = plain_app(m.name, param_exprs.clone());
        let mk_step_name = format!("{}.mkStep2", m.name);
        out.push(mk_def(
            mk_step_name.clone(),
            {
                let mut bs = implicit_binders.clone();
                bs.extend([
                    SurfaceBinder::new(
                        "a",
                        Some({
                            let mut args = param_exprs.clone();
                            args.push(tag(mi));
                            plain_app(&shape_f, args)
                        }),
                        SurfaceBinderInfo::Explicit,
                    ),
                    SurfaceBinder::new(
                        "f",
                        Some(SurfaceExpr::Pi(
                            Span::dummy(),
                            vec![SurfaceBinder::new(
                                "b",
                                Some({
                                    let mut args = param_exprs.clone();
                                    args.extend([tag(mi), ident("a")]);
                                    plain_app(&pos_f, args)
                                }),
                                SurfaceBinderInfo::Explicit,
                            )],
                            Box::new(plain_app(
                                "Codata.IMIntl",
                                vec![container(&shape_f), container(&pos_f), container(&tgt_f), {
                                    let mut targs = param_exprs.clone();
                                    targs.extend([tag(mi), ident("a"), ident("b")]);
                                    plain_app(&tgt_f, targs)
                                }],
                            )),
                        )),
                        SurfaceBinderInfo::Explicit,
                    ),
                ]);
                bs
            },
            plain_app(
                "Codata.isigmaStep",
                vec![
                    container(&shape_f),
                    container(&pos_f),
                    container(&tgt_f),
                    plain_app(
                        "Codata.IMIntl",
                        vec![container(&shape_f), container(&pos_f), container(&tgt_f)],
                    ),
                    tag(mi),
                ],
            ),
            plain_app("Sigma.mk", vec![ident("a"), ident("f")]),
        ));
        let mut mk_binders = implicit_binders.clone();
        for (obs_name, obs_ty) in m.obs.iter() {
            mk_binders.push(SurfaceBinder::new(
                format!("{obs_name}V").as_str(),
                Some((*obs_ty).clone()),
                SurfaceBinderInfo::Explicit,
            ));
        }
        for (step_name, tgt_mi) in m.steps.iter() {
            mk_binders.push(SurfaceBinder::new(
                format!("{step_name}V").as_str(),
                Some(plain_app(names[*tgt_mi], param_exprs.clone())),
                SurfaceBinderInfo::Explicit,
            ));
        }
        let mk_label = mutual_pack(
            &m.obs
                .iter()
                .map(|(n, _)| ident(&format!("{n}V")))
                .collect::<Vec<_>>(),
        );
        let mk_children: Vec<SurfaceExpr> = m
            .steps
            .iter()
            .map(|(n, _)| ident(&format!("{n}V")))
            .collect();
        let mk_child_fn = if mk_children.len() == 1 {
            lam1("_", mk_children[0].clone())
        } else {
            let tgt_full = {
                let tgt_f = tgt_f.clone();
                let pe = param_exprs.clone();
                let label = mk_label.clone();
                let tag_e = tag(mi);
                move |bpos: SurfaceExpr| -> SurfaceExpr {
                    let mut targs = pe.clone();
                    targs.extend([tag_e.clone(), label.clone(), bpos]);
                    plain_app(&tgt_f, targs)
                }
            };
            lam1(
                "b",
                mut_state_chain_p(
                    &mk_children,
                    0,
                    &plain_app(
                        "Codata.IMIntl",
                        vec![container(&shape_f), container(&pos_f), container(&tgt_f)],
                    ),
                    &tgt_full,
                    ident("b"),
                    poly,
                ),
            )
        };
        out.push(mk_def(
            format!("{}.mk", m.name),
            mk_binders.clone(),
            self_ty.clone(),
            at_app("Codata.IMmk", {
                let mut mkargs = param_exprs.clone();
                mkargs.extend([mk_label.clone(), mk_child_fn]);
                vec![
                    tag_ty.clone(),
                    container(&shape_f),
                    container(&pos_f),
                    container(&tgt_f),
                    tag(mi),
                    at_app(&mk_step_name, mkargs),
                ]
            }),
        ));
        let mk_call = {
            let mut args = param_exprs.clone();
            args.extend(
                m.obs
                    .iter()
                    .map(|(n, _)| ident(&format!("{n}V")))
                    .chain(m.steps.iter().map(|(n, _)| ident(&format!("{n}V")))),
            );
            at_app(&format!("{}.mk", m.name), args)
        };
        for field_name in m
            .obs
            .iter()
            .map(|(n, _)| *n)
            .chain(m.steps.iter().map(|(n, _)| *n))
        {
            let full = format!("{}.{field_name}", m.name);
            let mut acc_args = param_exprs.clone();
            acc_args.push(mk_call.clone());
            out.push(mk_theorem(
                format!("{full}_mk"),
                mk_binders.clone(),
                SurfaceExpr::App(
                    Span::dummy(),
                    Box::new(ident("Eq")),
                    vec![
                        SurfaceArg::positional(at_app(&full, acc_args)),
                        SurfaceArg::positional(ident(&format!("{field_name}V"))),
                    ],
                ),
                ident("rfl"),
            ));
        }
    }

    for (mi, m) in shapes.iter().enumerate() {
        let corec_call = |member: usize, extra: SurfaceExpr| {
            let mut args = param_exprs.clone();
            args.extend((0..n).map(|i| ident(&state_name(i))));
            args.extend(all_fn_idents.clone());
            args.push(extra);
            at_app(&format!("{}.corec", names[member]), args)
        };
        let law_binders = || {
            let mut bs = implicit_binders.clone();
            bs.extend(state_binders.clone());
            bs.extend(fn_binders.clone());
            bs.push(SurfaceBinder::new(
                "s",
                Some(ident(&state_name(mi))),
                SurfaceBinderInfo::Explicit,
            ));
            bs
        };
        for (obs_name, _) in &m.obs {
            let full = format!("{}.{obs_name}", m.name);
            let mut acc_args = param_exprs.clone();
            acc_args.push(corec_call(mi, ident("s")));
            out.push(mk_theorem(
                format!("{full}_corec"),
                law_binders(),
                SurfaceExpr::App(
                    Span::dummy(),
                    Box::new(ident("Eq")),
                    vec![
                        SurfaceArg::positional(at_app(&full, acc_args)),
                        SurfaceArg::positional(plain_app(
                            &format!("{}_{obs_name}F", m.name),
                            vec![ident("s")],
                        )),
                    ],
                ),
                ident("rfl"),
            ));
        }
        for (step_name, tgt_mi) in &m.steps {
            let full = format!("{}.{step_name}", m.name);
            let mut acc_args = param_exprs.clone();
            acc_args.push(corec_call(mi, ident("s")));
            out.push(mk_theorem(
                format!("{full}_corec"),
                law_binders(),
                SurfaceExpr::App(
                    Span::dummy(),
                    Box::new(ident("Eq")),
                    vec![
                        SurfaceArg::positional(at_app(&full, acc_args)),
                        SurfaceArg::positional(corec_call(
                            *tgt_mi,
                            plain_app(&format!("{}_{step_name}F", m.name), vec![ident("s")]),
                        )),
                    ],
                ),
                ident("rfl"),
            ));
        }
    }

    out.into_iter().map(|d| set_uparams(d, poly)).collect()
}

// ── mutual codef: joint copattern definitions into a mutual block ──

/// Elaborate a `mutual` block whose members are all `codef`, jointly
/// defining corecursive functions into the members of one mutual codata
/// block. Each codef supplies the clauses for ITS result member; a
/// clause that calls ANY codef of the block is that slot's corecursive
/// step (the new state), and observation clauses may call none of them.
pub(crate) fn elab_mutual_codef(
    env: &mut Environment,
    members: &[SurfaceDecl],
) -> Result<RegisteredElabResult, ElabError> {
    struct CodefBits<'a> {
        name: &'a str,
        binders: &'a [SurfaceBinder],
        ty: &'a SurfaceExpr,
        head: String,
        type_args: Vec<SurfaceExpr>,
        clauses: &'a [(String, SurfaceExpr)],
    }
    let mut bits: Vec<CodefBits<'_>> = Vec::new();
    for d in members {
        let SurfaceDecl::Codef {
            name,
            binders,
            ty,
            clauses,
            modifiers,
            ..
        } = d
        else {
            return Err(unsupported(
                "mutual codef: every member of the block must be a `codef`",
            ));
        };
        if !modifiers.is_default() {
            return Err(unsupported(format!(
                "mutual codef `{name}`: modifiers are not supported"
            )));
        }
        if binders.len() > 1 {
            return Err(unsupported(format!(
                "mutual codef `{name}`: zero or one state binder in v1"
            )));
        }
        for b in binders.iter() {
            if b.info != SurfaceBinderInfo::Explicit || b.ty.is_none() || b.default.is_some() {
                return Err(unsupported(format!(
                    "mutual codef `{name}`: the state binder must be a simple \
                     explicit `(x : T)`"
                )));
            }
        }
        let (head, type_args) = {
            let mut t = strip_parens(ty);
            let mut args: Vec<SurfaceExpr> = Vec::new();
            if let SurfaceExpr::App(_, h, a) = t {
                for arg in a {
                    if arg.name.is_some() {
                        return Err(unsupported(format!(
                            "mutual codef `{name}`: named arguments in the \
                             result type are not supported"
                        )));
                    }
                    args.push(arg.expr.clone());
                }
                t = strip_parens(h);
            }
            let SurfaceExpr::Ident(_, c) = t else {
                return Err(unsupported(format!(
                    "mutual codef `{name}`: the result type must be a codata \
                     member (a constant, possibly applied to parameters)"
                )));
            };
            (c.clone(), args)
        };
        bits.push(CodefBits {
            name,
            binders,
            ty,
            head,
            type_args,
            clauses,
        });
    }
    let fn_names: Vec<&str> = bits.iter().map(|b| b.name).collect();

    // All members must target the same mutual block: their corecs share
    // one recorded slot list. Use member 0's corec as the authority.
    let corec0 = format!("{}.corec", bits[0].head);
    let corec0_const = clean_kernel::Name::from_string(&corec0);
    let param_names = env
        .get_param_names(&corec0_const)
        .ok_or_else(|| {
            unsupported(format!(
                "mutual codef: `{}` is not a codata member (`{corec0}` has no \
                 recorded parameters)",
                bits[0].head
            ))
        })?
        .to_vec();
    let param_infos = env
        .get_param_binder_infos(&corec0_const)
        .ok_or_else(|| unsupported("mutual codef: no binder kinds recorded".to_string()))?
        .to_vec();
    let mut slots: Vec<String> = param_names
        .iter()
        .zip(param_infos.iter())
        .filter(|(_, i)| matches!(i, clean_kernel::BinderInfo::Default))
        .map(|(n, _)| n.clone())
        .collect();
    if slots.is_empty() {
        return Err(unsupported(format!(
            "mutual codef: `{corec0}` has no explicit parameters"
        )));
    }
    slots.pop(); // the trailing state argument

    // Build the shared slot lambdas: slot `<Member>_<field>F` is supplied
    // by the codef whose result head is `<Member>`.
    let mut slot_lambdas: Vec<SurfaceExpr> = Vec::new();
    for slot in &slots {
        let base = slot.strip_suffix('F').unwrap_or(slot);
        let Some((member, field)) = base.split_once('_') else {
            return Err(unsupported(format!(
                "mutual codef: unexpected corecursor slot `{slot}` — \
                 `{corec0}` is not a mutual-codata corecursor"
            )));
        };
        let Some(cb) = bits.iter().find(|b| b.head == member) else {
            return Err(unsupported(format!(
                "mutual codef: no codef in the block targets `{member}` \
                 (needed for its `{field}` clause)"
            )));
        };
        let Some((_, value)) = cb.clauses.iter().find(|(n, _)| n == field) else {
            return Err(unsupported(format!(
                "mutual codef `{}`: missing clause for `{field}` of `{member}`",
                cb.name
            )));
        };
        // A call to ANY block codef is the corecursive step for this slot.
        let body = match mutual_self_call_arg(value, &fn_names) {
            Some(next_state) => next_state,
            None => {
                for fname in &fn_names {
                    if mentions(value, fname) {
                        return Err(unsupported(format!(
                            "mutual codef `{}`: clause `{field}` mentions \
                             `{fname}` but is not a plain call — corecursive \
                             clauses must be exactly `<codef> <next-state>`",
                            cb.name
                        )));
                    }
                }
                value.clone()
            }
        };
        let state_name = cb.binders.first().map_or("_", |b| b.name.as_str());
        slot_lambdas.push(SurfaceExpr::Lambda(
            Span::dummy(),
            vec![SurfaceBinder::new(
                state_name,
                cb.binders.first().and_then(|b| b.ty.as_deref().cloned()),
                SurfaceBinderInfo::Explicit,
            )],
            Box::new(body),
        ));
    }

    // One generated def per codef, all sharing the slot lambdas.
    let mut candidate = env.clone();
    for cb in &bits {
        let state_ty = cb
            .binders
            .first()
            .and_then(|b| b.ty.as_deref().cloned())
            .unwrap_or_else(punit_ty);
        let init_state = cb
            .binders
            .first()
            .map_or_else(|| ident("PUnit.unit"), |b| ident(&b.name));
        // The 2-member corec takes {S1 S2}; n-member {S1..Sn} — all
        // implicit, inferred from the state lambdas' ascribed types and
        // the init state. Pass the member's OWN state type positionally is
        // not possible (implicit), so rely on inference via the explicit
        // fn lambdas — their binder ascriptions pin each S_i.
        let _ = state_ty;
        let mut corec_args = cb.type_args.clone();
        corec_args.extend(slot_lambdas.iter().cloned());
        corec_args.push(init_state);
        let generated = mk_def(
            cb.name.to_string(),
            cb.binders.to_vec(),
            cb.ty.clone(),
            plain_app(&format!("{}.corec", cb.head), corec_args),
        );
        crate::elaborate_decl_and_register(&mut candidate, &generated).map_err(|e| {
            unsupported(format!(
                "mutual codef `{}`: the generated corecursor application \
                 failed to elaborate/kernel-check (env left untouched): {e:?}",
                cb.name
            ))
        })?;
    }
    *env = candidate;
    Ok(RegisteredElabResult {
        result: ElabResult::Skipped,
        warning: None,
        hole_contexts: Vec::new(),
    })
}

/// If `expr` is exactly `<one of fnames> <one-arg>` (or a bare name for
/// zero-state members), return the new-state expression.
fn mutual_self_call_arg(expr: &SurfaceExpr, fnames: &[&str]) -> Option<SurfaceExpr> {
    match strip_parens(expr) {
        SurfaceExpr::Ident(_, id) if fnames.contains(&id.as_str()) => Some(ident("PUnit.unit")),
        SurfaceExpr::App(_, h, args) => {
            let SurfaceExpr::Ident(_, id) = strip_parens(h) else {
                return None;
            };
            if !fnames.contains(&id.as_str()) || args.len() != 1 || args[0].name.is_some() {
                return None;
            }
            Some(args[0].expr.clone())
        }
        _ => None,
    }
}

// ── multi-index codata: k indices packed into a right-nested PProd ──
// The container lives at the packed index; USER-FACING signatures stay
// unpacked (`Grid (r : Nat) (c : Nat)`, accessors over {r c}). Index
// expressions from the surface are wrapped as
// `(fun i1 … ik => E) ip.1 ip.2.1 …` so they read the packed variable.
// Mirrors the hand-validated Grid expansion.

fn generate_multi_indexed(shape: &IndexedShape<'_>) -> Vec<SurfaceDecl> {
    let IndexedShape {
        name,
        poly,
        binders,
        idx_binders,
        obs,
        steps,
        ..
    } = shape;
    let poly = *poly;
    let k_idx = idx_binders.len();
    let param_exprs: Vec<SurfaceExpr> = binders.iter().map(|b| ident(&b.name)).collect();
    let explicit_params: Vec<SurfaceBinder> = binders.to_vec();
    let implicit_params: Vec<SurfaceBinder> = explicit_params
        .iter()
        .map(|b| {
            let mut ib = b.clone();
            ib.info = SurfaceBinderInfo::Implicit;
            ib
        })
        .collect();
    // The packed index type: right-nested PProd of the binder types.
    let packed_ty = idx_binders
        .iter()
        .rev()
        .map(|b| b.ty.as_deref().expect("validated").clone())
        .reduce(|acc, t| plain_app("PProd", vec![t, acc]))
        .expect("validated: at least one index binder");
    // The packed value from the (unpacked) index idents.
    let pack_idents = || -> SurfaceExpr {
        let exprs: Vec<SurfaceExpr> = idx_binders.iter().map(|b| ident(&b.name)).collect();
        mutual_pack_pprod(&exprs)
    };
    // Projection of component i out of the packed variable `ip`.
    let proj = |i: usize| -> SurfaceExpr {
        let mut e = ident("ip");
        for _ in 0..i {
            e = SurfaceExpr::Proj(Span::dummy(), Box::new(e), Projection::Index(2));
        }
        if i + 1 < k_idx {
            e = SurfaceExpr::Proj(Span::dummy(), Box::new(e), Projection::Index(1));
        }
        e
    };
    // Wrap a surface expression mentioning the index names so it reads the
    // packed variable: `(fun i1 … ik => E) ip.1 …`.
    let wrap = |e: SurfaceExpr| -> SurfaceExpr {
        let lam = SurfaceExpr::Lambda(
            Span::dummy(),
            idx_binders
                .iter()
                .map(|b| {
                    SurfaceBinder::new(
                        b.name.as_str(),
                        b.ty.as_deref().cloned(),
                        SurfaceBinderInfo::Explicit,
                    )
                })
                .collect(),
            Box::new(e),
        );
        SurfaceExpr::App(
            Span::dummy(),
            Box::new(lam),
            (0..k_idx)
                .map(|i| SurfaceArg::positional(proj(i)))
                .collect(),
        )
    };

    let shape_f = format!("{name}.shapeF");
    let pos_f = format!("{name}.posF");
    let tgt_f = format!("{name}.tgtF");
    let mk_step = format!("{name}.mkStep");
    let step_fn = format!("{name}.stepFn");
    let corec = format!("{name}.corec");
    let m = steps.len();
    let k_obs = obs.len();
    let capp = |f: &str, extra: Vec<SurfaceExpr>| -> SurfaceExpr {
        let mut args = param_exprs.clone();
        args.extend(extra);
        plain_app(f, args)
    };

    let label_ty = obs
        .iter()
        .rev()
        .map(|(_, t)| (*t).clone())
        .reduce(|acc, t| plain_app("PProd", vec![t, acc]))
        .expect("validated: at least one observation");

    let mut out = Vec::new();
    // shapeF (ps) : packed → Type := fun ip => wrap(label)
    out.push(mk_def(
        shape_f.clone(),
        explicit_params.clone(),
        arrow(packed_ty.clone(), type_u(poly)),
        lam1("ip", wrap(label_ty)),
    ));
    // posF (ps) : (i : packed) → shapeF ps i → Type := fun _ _ => pos
    out.push(mk_def(
        pos_f.clone(),
        explicit_params.clone(),
        pi(
            "i",
            packed_ty.clone(),
            arrow(capp(&shape_f, vec![ident("i")]), type_u(poly)),
        ),
        SurfaceExpr::Lambda(
            Span::dummy(),
            vec![
                SurfaceBinder::new("_", None, SurfaceBinderInfo::Explicit),
                SurfaceBinder::new("_", None, SurfaceBinderInfo::Explicit),
            ],
            Box::new(mut_pos_ty_p(m, poly)),
        ),
    ));
    // tgtF (ps) : (i : packed) → (a : shapeF i) → posF i a → packed :=
    //   fun ip _ pb => <chain of wrapped packed target exprs>
    let idx_targets: Vec<SurfaceExpr> = steps
        .iter()
        .map(|(_, exprs)| {
            let packed = mutual_pack_pprod(&exprs.iter().map(|e| (*e).clone()).collect::<Vec<_>>());
            wrap(packed)
        })
        .collect();
    let tgt_body = if m == 1 {
        SurfaceExpr::Lambda(
            Span::dummy(),
            vec![
                SurfaceBinder::new("ip", None, SurfaceBinderInfo::Explicit),
                SurfaceBinder::new("_", None, SurfaceBinderInfo::Explicit),
                SurfaceBinder::new("_", None, SurfaceBinderInfo::Explicit),
            ],
            Box::new(idx_targets[0].clone()),
        )
    } else {
        SurfaceExpr::Lambda(
            Span::dummy(),
            vec![
                SurfaceBinder::new("ip", None, SurfaceBinderInfo::Explicit),
                SurfaceBinder::new("_", None, SurfaceBinderInfo::Explicit),
                SurfaceBinder::new("pb", None, SurfaceBinderInfo::Explicit),
            ],
            Box::new(mut_idx_chain_p(&idx_targets, &packed_ty, ident("pb"), None)),
        )
    };
    out.push(mk_def(
        tgt_f.clone(),
        explicit_params.clone(),
        pi("i", packed_ty.clone(), {
            pi("a", capp(&shape_f, vec![ident("i")]), {
                arrow(
                    capp(&pos_f, vec![ident("i"), ident("a")]),
                    packed_ty.clone(),
                )
            })
        }),
        tgt_body,
    ));
    // Carrier: C (ps) (i1 : T1) … (ik : Tk) : Type := IMIntl … (pack)
    out.push(mk_def(
        (*name).to_string(),
        {
            let mut bs = explicit_params.clone();
            bs.extend(idx_binders.iter().cloned());
            bs
        },
        type_u(poly),
        at_app(
            "Codata.IMIntl",
            vec![
                packed_ty.clone(),
                capp(&shape_f, vec![]),
                capp(&pos_f, vec![]),
                capp(&tgt_f, vec![]),
                pack_idents(),
            ],
        ),
    ));
    let self_unpacked = || -> SurfaceExpr {
        let mut args = param_exprs.clone();
        args.extend(idx_binders.iter().map(|b| ident(&b.name)));
        plain_app(name, args)
    };
    let implicit_idx: Vec<SurfaceBinder> = idx_binders
        .iter()
        .map(|b| {
            let mut ib = b.clone();
            ib.info = SurfaceBinderInfo::Implicit;
            ib
        })
        .collect();
    // Observation accessors: {ps} {i1..ik} (x : C ps i…) : T[i…]
    for (oi, (obs_name, obs_ty)) in obs.iter().enumerate() {
        let mut sel = at_app(
            "Codata.IMhead",
            vec![
                packed_ty.clone(),
                capp(&shape_f, vec![]),
                capp(&pos_f, vec![]),
                capp(&tgt_f, vec![]),
                pack_idents(),
                ident("x"),
            ],
        );
        for _ in 0..oi {
            sel = SurfaceExpr::Proj(Span::dummy(), Box::new(sel), Projection::Index(2));
        }
        if oi + 1 < k_obs {
            sel = SurfaceExpr::Proj(Span::dummy(), Box::new(sel), Projection::Index(1));
        }
        out.push(mk_def(
            format!("{name}.{obs_name}"),
            {
                let mut bs = implicit_params.clone();
                bs.extend(implicit_idx.iter().cloned());
                bs.push(SurfaceBinder::new(
                    "x",
                    Some(self_unpacked()),
                    SurfaceBinderInfo::Explicit,
                ));
                bs
            },
            (*obs_ty).clone(),
            sel,
        ));
    }
    // Recursive accessors: result C ps e1 … ek (the field's own targets).
    for (si, (step_name, exprs)) in steps.iter().enumerate() {
        let mut res_args = param_exprs.clone();
        res_args.extend(exprs.iter().map(|e| (*e).clone()));
        out.push(mk_def(
            format!("{name}.{step_name}"),
            {
                let mut bs = implicit_params.clone();
                bs.extend(implicit_idx.iter().cloned());
                bs.push(SurfaceBinder::new(
                    "x",
                    Some(self_unpacked()),
                    SurfaceBinderInfo::Explicit,
                ));
                bs
            },
            plain_app(name, res_args),
            at_app(
                "Codata.IMchild",
                vec![
                    packed_ty.clone(),
                    capp(&shape_f, vec![]),
                    capp(&pos_f, vec![]),
                    capp(&tgt_f, vec![]),
                    pack_idents(),
                    ident("x"),
                    mut_pos_point(si, m),
                ],
            ),
        ));
    }
    // mkStep {ps} {S : packed → Type} (ip) (a) (f)
    let s_binder = SurfaceBinder::new(
        "S",
        Some(arrow(packed_ty.clone(), type_u(poly))),
        SurfaceBinderInfo::Implicit,
    );
    out.push(mk_def(
        mk_step.clone(),
        {
            let mut bs = implicit_params.clone();
            bs.push(s_binder.clone());
            bs.extend([
                SurfaceBinder::new("ip", Some(packed_ty.clone()), SurfaceBinderInfo::Explicit),
                SurfaceBinder::new(
                    "a",
                    Some(capp(&shape_f, vec![ident("ip")])),
                    SurfaceBinderInfo::Explicit,
                ),
                SurfaceBinder::new(
                    "f",
                    Some(SurfaceExpr::Pi(
                        Span::dummy(),
                        vec![SurfaceBinder::new(
                            "b",
                            Some(capp(&pos_f, vec![ident("ip"), ident("a")])),
                            SurfaceBinderInfo::Explicit,
                        )],
                        Box::new(SurfaceExpr::App(
                            Span::dummy(),
                            Box::new(ident("S")),
                            vec![SurfaceArg::positional(capp(
                                &tgt_f,
                                vec![ident("ip"), ident("a"), ident("b")],
                            ))],
                        )),
                    )),
                    SurfaceBinderInfo::Explicit,
                ),
            ]);
            bs
        },
        plain_app(
            "Codata.isigmaStep",
            vec![
                capp(&shape_f, vec![]),
                capp(&pos_f, vec![]),
                capp(&tgt_f, vec![]),
                ident("S"),
                ident("ip"),
            ],
        ),
        plain_app("Sigma.mk", vec![ident("a"), ident("f")]),
    ));
    // Per-field function binders over the packed index.
    let fn_ty = |result: SurfaceExpr| {
        SurfaceExpr::Pi(
            Span::dummy(),
            vec![SurfaceBinder::new(
                "ip",
                Some(packed_ty.clone()),
                SurfaceBinderInfo::Explicit,
            )],
            Box::new(arrow(
                SurfaceExpr::App(
                    Span::dummy(),
                    Box::new(ident("S")),
                    vec![SurfaceArg::positional(ident("ip"))],
                ),
                result,
            )),
        )
    };
    let mut fn_binders: Vec<SurfaceBinder> = Vec::new();
    for (obs_name, obs_ty) in obs {
        fn_binders.push(SurfaceBinder::new(
            format!("{obs_name}F").as_str(),
            Some(fn_ty(wrap((*obs_ty).clone()))),
            SurfaceBinderInfo::Explicit,
        ));
    }
    for ((step_name, _), wrapped_tgt) in steps.iter().zip(&idx_targets) {
        fn_binders.push(SurfaceBinder::new(
            format!("{step_name}F").as_str(),
            Some(fn_ty(SurfaceExpr::App(
                Span::dummy(),
                Box::new(ident("S")),
                vec![SurfaceArg::positional(wrapped_tgt.clone())],
            ))),
            SurfaceBinderInfo::Explicit,
        ));
    }
    let all_fn_idents: Vec<SurfaceExpr> = obs
        .iter()
        .map(|(n, _)| ident(&format!("{n}F")))
        .chain(steps.iter().map(|(n, _)| ident(&format!("{n}F"))))
        .collect();
    // stepFn
    let label_pack = mutual_pack(
        &obs.iter()
            .map(|(n, _)| plain_app(&format!("{n}F"), vec![ident("jp"), ident("sv")]))
            .collect::<Vec<_>>(),
    );
    let branch_states: Vec<SurfaceExpr> = steps
        .iter()
        .map(|(n, _)| plain_app(&format!("{n}F"), vec![ident("jp"), ident("sv")]))
        .collect();
    let child = if m == 1 {
        lam1("_", branch_states[0].clone())
    } else {
        let tgt_full = {
            let tgt_f = tgt_f.clone();
            let tf_params = param_exprs.clone();
            let label_pack = label_pack.clone();
            move |bpos: SurfaceExpr| -> SurfaceExpr {
                let mut args = tf_params.clone();
                args.extend([ident("jp"), label_pack.clone(), bpos]);
                plain_app(&tgt_f, args)
            }
        };
        lam1(
            "pb",
            mut_state_chain_p(&branch_states, 0, &ident("S"), &tgt_full, ident("pb"), None),
        )
    };
    let mut mkargs = param_exprs.clone();
    mkargs.extend([ident("S"), ident("jp"), label_pack.clone(), child]);
    out.push(mk_def(
        step_fn.clone(),
        {
            let mut bs = implicit_params.clone();
            bs.push(s_binder.clone());
            bs.extend(fn_binders.clone());
            bs
        },
        pi("j", packed_ty.clone(), {
            arrow(
                SurfaceExpr::App(
                    Span::dummy(),
                    Box::new(ident("S")),
                    vec![SurfaceArg::positional(ident("j"))],
                ),
                plain_app(
                    "Codata.isigmaStep",
                    vec![
                        capp(&shape_f, vec![]),
                        capp(&pos_f, vec![]),
                        capp(&tgt_f, vec![]),
                        ident("S"),
                        ident("j"),
                    ],
                ),
            )
        }),
        SurfaceExpr::Lambda(
            Span::dummy(),
            vec![
                SurfaceBinder::new("jp", None, SurfaceBinderInfo::Explicit),
                SurfaceBinder::new("sv", None, SurfaceBinderInfo::Explicit),
            ],
            Box::new(at_app(&mk_step, mkargs)),
        ),
    ));
    // corec: {ps} {S} (fns…) (i1 … ik) (s : S (pack)) : C ps i…
    let step_call = {
        let mut args = param_exprs.clone();
        args.push(ident("S"));
        args.extend(all_fn_idents.clone());
        at_app(&step_fn, args)
    };
    out.push(mk_def(
        corec.clone(),
        {
            let mut bs = implicit_params.clone();
            bs.push(s_binder.clone());
            bs.extend(fn_binders.clone());
            bs.extend(idx_binders.iter().cloned());
            bs.push(SurfaceBinder::new(
                "s",
                Some(SurfaceExpr::App(
                    Span::dummy(),
                    Box::new(ident("S")),
                    vec![SurfaceArg::positional(pack_idents())],
                )),
                SurfaceBinderInfo::Explicit,
            ));
            bs
        },
        self_unpacked(),
        at_app(
            "Codata.IMcorec",
            vec![
                packed_ty.clone(),
                capp(&shape_f, vec![]),
                capp(&pos_f, vec![]),
                capp(&tgt_f, vec![]),
                ident("S"),
                step_call,
                pack_idents(),
                ident("s"),
            ],
        ),
    ));
    // The CONSTRUCTOR: C.mk {ps} {i1..ik} (field values) at the packed
    // index; children live at their own (unpacked) target indices. rfl laws.
    let mk_step_name = format!("{name}.mkStep2");
    out.push(mk_def(
        mk_step_name.clone(),
        {
            let mut bs = implicit_params.clone();
            bs.extend(implicit_idx.iter().cloned());
            bs.extend([
                SurfaceBinder::new(
                    "a",
                    Some(capp(&shape_f, vec![pack_idents()])),
                    SurfaceBinderInfo::Explicit,
                ),
                SurfaceBinder::new(
                    "f",
                    Some(SurfaceExpr::Pi(
                        Span::dummy(),
                        vec![SurfaceBinder::new(
                            "b",
                            Some(capp(&pos_f, vec![pack_idents(), ident("a")])),
                            SurfaceBinderInfo::Explicit,
                        )],
                        Box::new(plain_app(
                            "Codata.IMIntl",
                            vec![
                                capp(&shape_f, vec![]),
                                capp(&pos_f, vec![]),
                                capp(&tgt_f, vec![]),
                                capp(&tgt_f, vec![pack_idents(), ident("a"), ident("b")]),
                            ],
                        )),
                    )),
                    SurfaceBinderInfo::Explicit,
                ),
            ]);
            bs
        },
        plain_app(
            "Codata.isigmaStep",
            vec![
                capp(&shape_f, vec![]),
                capp(&pos_f, vec![]),
                capp(&tgt_f, vec![]),
                plain_app(
                    "Codata.IMIntl",
                    vec![
                        capp(&shape_f, vec![]),
                        capp(&pos_f, vec![]),
                        capp(&tgt_f, vec![]),
                    ],
                ),
                pack_idents(),
            ],
        ),
        plain_app("Sigma.mk", vec![ident("a"), ident("f")]),
    ));
    let mut mk_binders = implicit_params.clone();
    mk_binders.extend(implicit_idx.iter().cloned());
    for (obs_name, obs_ty) in obs.iter() {
        mk_binders.push(SurfaceBinder::new(
            format!("{obs_name}V").as_str(),
            Some((*obs_ty).clone()),
            SurfaceBinderInfo::Explicit,
        ));
    }
    for (step_name, exprs) in steps.iter() {
        let mut res_args = param_exprs.clone();
        res_args.extend(exprs.iter().map(|e| (*e).clone()));
        mk_binders.push(SurfaceBinder::new(
            format!("{step_name}V").as_str(),
            Some(plain_app(name, res_args)),
            SurfaceBinderInfo::Explicit,
        ));
    }
    let mk_label = mutual_pack(
        &obs.iter()
            .map(|(n, _)| ident(&format!("{n}V")))
            .collect::<Vec<_>>(),
    );
    let mk_children: Vec<SurfaceExpr> =
        steps.iter().map(|(n, _)| ident(&format!("{n}V"))).collect();
    let mk_child_fn = if mk_children.len() == 1 {
        lam1("_", mk_children[0].clone())
    } else {
        let tgt_full = {
            let tgt_f = tgt_f.clone();
            let pe = param_exprs.clone();
            let label = mk_label.clone();
            let packed = pack_idents();
            move |bpos: SurfaceExpr| -> SurfaceExpr {
                let mut targs = pe.clone();
                targs.extend([packed.clone(), label.clone(), bpos]);
                plain_app(&tgt_f, targs)
            }
        };
        lam1(
            "b",
            mut_state_chain_p(
                &mk_children,
                0,
                &plain_app(
                    "Codata.IMIntl",
                    vec![
                        capp(&shape_f, vec![]),
                        capp(&pos_f, vec![]),
                        capp(&tgt_f, vec![]),
                    ],
                ),
                &tgt_full,
                ident("b"),
                None,
            ),
        )
    };
    out.push(mk_def(
        format!("{name}.mk"),
        mk_binders.clone(),
        self_unpacked(),
        at_app("Codata.IMmk", {
            let mut mkargs = param_exprs.clone();
            mkargs.extend(idx_binders.iter().map(|b| ident(&b.name)));
            mkargs.extend([mk_label.clone(), mk_child_fn]);
            vec![
                packed_ty.clone(),
                capp(&shape_f, vec![]),
                capp(&pos_f, vec![]),
                capp(&tgt_f, vec![]),
                pack_idents(),
                at_app(&mk_step_name, mkargs),
            ]
        }),
    ));
    let mk_call = {
        let mut args = param_exprs.clone();
        args.extend(idx_binders.iter().map(|b| ident(&b.name)));
        args.extend(
            obs.iter()
                .map(|(n, _)| ident(&format!("{n}V")))
                .chain(steps.iter().map(|(n, _)| ident(&format!("{n}V")))),
        );
        at_app(&format!("{name}.mk"), args)
    };
    for field_name in obs
        .iter()
        .map(|(n, _)| *n)
        .chain(steps.iter().map(|(n, _)| *n))
    {
        let full = format!("{name}.{field_name}");
        let mut acc_args = param_exprs.clone();
        acc_args.extend(idx_binders.iter().map(|b| ident(&b.name)));
        acc_args.push(mk_call.clone());
        out.push(mk_theorem(
            format!("{full}_mk"),
            mk_binders.clone(),
            SurfaceExpr::App(
                Span::dummy(),
                Box::new(ident("Eq")),
                vec![
                    SurfaceArg::positional(at_app(&full, acc_args)),
                    SurfaceArg::positional(ident(&format!("{field_name}V"))),
                ],
            ),
            ident("rfl"),
        ));
    }

    // Laws.
    let corec_call = |idx: SurfaceExpr, extra: SurfaceExpr| {
        // idx here is already the UNPACKED argument list appended by caller;
        // we pass unpacked binder idents for the self law and target exprs
        // for the step laws — both as pre-flattened argument vectors.
        let _ = &idx;
        extra
    };
    let _ = corec_call;
    let mk_corec_call = |idx_args: Vec<SurfaceExpr>, st: SurfaceExpr| -> SurfaceExpr {
        let mut args = param_exprs.clone();
        args.push(ident("S"));
        args.extend(all_fn_idents.clone());
        args.extend(idx_args);
        args.push(st);
        at_app(&corec, args)
    };
    let law_binders = || {
        let mut bs = implicit_params.clone();
        bs.push(s_binder.clone());
        bs.extend(fn_binders.clone());
        bs.extend(idx_binders.iter().cloned());
        bs.push(SurfaceBinder::new(
            "s",
            Some(SurfaceExpr::App(
                Span::dummy(),
                Box::new(ident("S")),
                vec![SurfaceArg::positional(pack_idents())],
            )),
            SurfaceBinderInfo::Explicit,
        ));
        bs
    };
    let own_idx: Vec<SurfaceExpr> = idx_binders.iter().map(|b| ident(&b.name)).collect();
    for (obs_name, _) in obs {
        let full = format!("{name}.{obs_name}");
        out.push(mk_theorem(
            format!("{full}_corec"),
            law_binders(),
            SurfaceExpr::App(
                Span::dummy(),
                Box::new(ident("Eq")),
                vec![
                    SurfaceArg::positional(plain_app(
                        &full,
                        vec![mk_corec_call(own_idx.clone(), ident("s"))],
                    )),
                    SurfaceArg::positional(plain_app(
                        &format!("{obs_name}F"),
                        vec![pack_idents(), ident("s")],
                    )),
                ],
            ),
            ident("rfl"),
        ));
    }
    for (step_name, exprs) in steps {
        let full = format!("{name}.{step_name}");
        out.push(mk_theorem(
            format!("{full}_corec"),
            law_binders(),
            SurfaceExpr::App(
                Span::dummy(),
                Box::new(ident("Eq")),
                vec![
                    SurfaceArg::positional(plain_app(
                        &full,
                        vec![mk_corec_call(own_idx.clone(), ident("s"))],
                    )),
                    SurfaceArg::positional(mk_corec_call(
                        exprs.iter().map(|e| (*e).clone()).collect(),
                        plain_app(&format!("{step_name}F"), vec![pack_idents(), ident("s")]),
                    )),
                ],
            ),
            ident("rfl"),
        ));
    }

    out.into_iter().map(|d| set_uparams(d, poly)).collect()
}

/// Right-nested `PProd.mk` chain (single value passes through).
fn mutual_pack_pprod(vals: &[SurfaceExpr]) -> SurfaceExpr {
    match vals {
        [] => ident("PUnit.unit"),
        [only] => only.clone(),
        [first, rest @ ..] => plain_app("PProd.mk", vec![first.clone(), mutual_pack_pprod(rest)]),
    }
}

/// Detect and compile a plain codef whose single recursive clause is
/// mk-GUARDED — `step := C.mk g1 … gk (f e)` — via the Bool-flag buffered
/// state: `S' := PProd Bool S`; flag `true` plays the outer node (the
/// user's observation clauses), `false` plays the guard node (the mk's
/// observation values), and the step alternates
/// `true s ↦ false s`, `false s ↦ true e[s]`. Returns `Ok(None)` when the
/// clause set is not mk-guarded (the ordinary path proceeds).
///
/// The user's state-binder name is re-bound with beta-redexes
/// (`(fun s => body) p.2`) instead of substitution. One guard layer in
/// v1 — nested `mk`s reject loudly.
#[allow(clippy::too_many_arguments)]
fn compile_guarded_codef(
    name: &str,
    binders: &[SurfaceBinder],
    ty: &SurfaceExpr,
    clauses: &[(String, SurfaceExpr)],
    slots: &[String],
    head_name: &str,
    type_args: &[SurfaceExpr],
    state: Option<&SurfaceBinder>,
) -> Result<Option<SurfaceDecl>, ElabError> {
    let mk_name = format!("{head_name}.mk");
    fn is_mk_app_impl<'e>(
        e: &'e SurfaceExpr,
        mk_name: &str,
        head_name: &str,
    ) -> Option<&'e [SurfaceArg]> {
        let SurfaceExpr::App(_, h, args) = strip_parens(e) else {
            return None;
        };
        let is_mk = match strip_parens(h) {
            SurfaceExpr::Ident(_, id) => id == mk_name,
            SurfaceExpr::Proj(_, base, Projection::Named(field)) => {
                field == "mk"
                    && matches!(strip_parens(base),
                        SurfaceExpr::Ident(_, id) if id == head_name)
            }
            _ => false,
        };
        if is_mk {
            Some(args)
        } else {
            None
        }
    }

    // Find the (single) mk-guarded recursive clause.
    let mut guarded: Option<usize> = None;
    for (ci, (_, value)) in clauses.iter().enumerate() {
        if is_mk_app_impl(value, &mk_name, head_name).is_some() {
            if guarded.is_some() {
                return Err(unsupported(format!(
                    "codef `{name}`: at most one mk-guarded clause is \
                     supported in v1"
                )));
            }
            guarded = Some(ci);
        }
    }
    let Some(gci) = guarded else {
        return Ok(None);
    };
    // Peel the nested mk layers, collecting per-layer guard values. Each
    // layer supplies one value per field; the last argument of the last
    // layer is the corecursive self-call.
    let obs_count = slots.len() - 1;
    let mut layers: Vec<Vec<SurfaceExpr>> = Vec::new();
    let mut cursor: &SurfaceExpr = &clauses[gci].1;
    while let Some(args) = is_mk_app_impl(cursor, &mk_name, head_name) {
        if args.len() != slots.len() {
            return Err(unsupported(format!(
                "codef `{name}`: each `{mk_name}` guard layer needs exactly \
                 one value per field ({} expected, got {})",
                slots.len(),
                args.len()
            )));
        }
        if args.iter().any(|a| a.name.is_some()) {
            return Err(unsupported(format!(
                "codef `{name}`: named arguments in a guarded mk clause are \
                 not supported"
            )));
        }
        let (inner, guard_vals) = args.split_last().expect("len >= 1");
        layers.push(guard_vals.iter().map(|a| a.expr.clone()).collect());
        cursor = &inner.expr;
    }
    let depth = layers.len();
    debug_assert!(depth >= 1, "guarded => at least one mk layer");
    let Some(next_state) = self_call_arg(cursor, name, false).map(|c| c.state) else {
        return Err(unsupported(format!(
            "codef `{name}`: the innermost `{mk_name}` child must be the \
             corecursive self-call (`{name} <next-state>`)"
        )));
    };
    // Every OTHER clause must be a plain observation (no self-mentions),
    // and guard values may not corecurse.
    for (ci, (cname, value)) in clauses.iter().enumerate() {
        if ci != gci && mentions(value, name) {
            return Err(unsupported(format!(
                "codef `{name}`: clause `{cname}` mentions `{name}` — only \
                 the single mk-guarded clause may corecurse in v1"
            )));
        }
    }
    for layer in &layers {
        for gv in layer {
            if mentions(gv, name) {
                return Err(unsupported(format!(
                    "codef `{name}`: guard observation values may not \
                     mention `{name}` (only the innermost child corecurses)"
                )));
            }
        }
    }

    let state_name = state.map_or("_", |b| b.name.as_str());
    let state_ty = state
        .and_then(|b| b.ty.as_deref().cloned())
        .unwrap_or_else(punit_ty);
    // Buffered state: a Nat flag (0 = the outer node, k = the k-th guard
    // layer) paired with the user's state.
    let buffered_ty = plain_app("PProd", vec![ident("Nat"), state_ty.clone()]);
    let nat_lit = |k: usize| -> SurfaceExpr {
        SurfaceExpr::Lit(
            Span::dummy(),
            clean_parser::SurfaceLit::nat(clean_kernel::BigNat::from(k as u64)),
        )
    };
    let rebind = |e: SurfaceExpr| -> SurfaceExpr {
        SurfaceExpr::App(
            Span::dummy(),
            Box::new(SurfaceExpr::Lambda(
                Span::dummy(),
                vec![SurfaceBinder::new(
                    state_name,
                    Some(state_ty.clone()),
                    SurfaceBinderInfo::Explicit,
                )],
                Box::new(e),
            )),
            vec![SurfaceArg::positional(plain_app(
                "PProd.snd",
                vec![ident("p")],
            ))],
        )
    };
    let flag = plain_app("PProd.fst", vec![ident("p")]);
    let payload = plain_app("PProd.snd", vec![ident("p")]);
    let plam = |body: SurfaceExpr| -> SurfaceExpr {
        SurfaceExpr::Lambda(
            Span::dummy(),
            vec![SurfaceBinder::new(
                "p",
                Some(buffered_ty.clone()),
                SurfaceBinderInfo::Explicit,
            )],
            Box::new(body),
        )
    };
    let beq_flag =
        |k: usize| -> SurfaceExpr { plain_app("Nat.beq", vec![flag.clone(), nat_lit(k)]) };
    // cond chain: flag 0 -> outer, flag k -> layer k (the last layer is
    // the chain's final else branch).
    let cond_chain = |outer: SurfaceExpr, layer_vals: Vec<SurfaceExpr>| -> SurfaceExpr {
        let mut chain = layer_vals
            .last()
            .cloned()
            .expect("depth >= 1: at least one layer");
        for (k, v) in layer_vals.iter().enumerate().rev().skip(1) {
            chain = plain_app("cond", vec![beq_flag(k + 1), v.clone(), chain]);
        }
        plain_app("cond", vec![beq_flag(0), outer, chain])
    };
    let mut slot_lambdas: Vec<SurfaceExpr> = Vec::new();
    for (si, slot) in slots.iter().enumerate() {
        let field = slot.strip_suffix('F').unwrap_or(slot);
        if si == obs_count {
            // The recursive slot: at the last layer wrap back to flag 0
            // with the (re-bound) next state; otherwise advance the flag.
            slot_lambdas.push(plam(plain_app(
                "cond",
                vec![
                    beq_flag(depth),
                    plain_app("PProd.mk", vec![nat_lit(0), rebind(next_state.clone())]),
                    plain_app(
                        "PProd.mk",
                        vec![plain_app("Nat.succ", vec![flag.clone()]), payload.clone()],
                    ),
                ],
            )));
        } else {
            let Some((_, outer)) = clauses.iter().find(|(n, _)| n == field) else {
                return Err(unsupported(format!(
                    "codef `{name}`: missing clause for observation `{field}` \
                     of `{head_name}`"
                )));
            };
            let layer_vals: Vec<SurfaceExpr> =
                layers.iter().map(|l| rebind(l[si].clone())).collect();
            slot_lambdas.push(plam(cond_chain(rebind(outer.clone()), layer_vals)));
        }
    }
    let init = plain_app(
        "PProd.mk",
        vec![
            nat_lit(0),
            state.map_or_else(|| ident("PUnit.unit"), |b| ident(&b.name)),
        ],
    );
    let mut corec_args = type_args.to_vec();
    corec_args.push(buffered_ty);
    corec_args.extend(slot_lambdas);
    corec_args.push(init);
    Ok(Some(mk_def(
        name.to_string(),
        binders.to_vec(),
        ty.clone(),
        at_app(&format!("{head_name}.corec"), corec_args),
    )))
}
