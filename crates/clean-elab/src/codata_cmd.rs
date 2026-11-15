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
    SurfaceDecl, SurfaceExpr, SurfaceField, SurfaceName, TerminationHints, UniverseExpr,
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
pub(crate) fn punit_ty() -> SurfaceExpr {
    SurfaceExpr::UniverseInst(
        Span::dummy(),
        Box::new(ident(GlobalPath("PUnit"))),
        vec![LevelExpr::Lit(1)],
    )
}

/// `Type` or `Type u` — the result-sort/state-sort for generated code,
/// polymorphic when the codata declares `.{u}` (U2 rung 7 part 2).
pub(crate) fn type_u(poly: Option<&SurfaceName>) -> SurfaceExpr {
    match poly {
        Some(u) => SurfaceExpr::Universe(
            Span::dummy(),
            UniverseExpr::TypeLevel(Box::new(LevelExpr::Param(u.clone()))),
        ),
        None => type_universe(),
    }
}

/// `PUnit.{1}` (mono) or `PUnit.{u+1}` (polymorphic): the container
/// index/tag unit at the level matching `Type`/`Type u` families.
pub(crate) fn punit_ty_p(poly: Option<&SurfaceName>) -> SurfaceExpr {
    match poly {
        Some(u) => SurfaceExpr::UniverseInst(
            Span::dummy(),
            Box::new(ident(GlobalPath("PUnit"))),
            vec![LevelExpr::Succ(Box::new(LevelExpr::Param(u.clone())))],
        ),
        None => punit_ty(),
    }
}

/// Stamp the declared universe params onto a generated def/theorem.
pub(crate) fn set_uparams(mut decl: SurfaceDecl, poly: Option<&SurfaceName>) -> SurfaceDecl {
    if let Some(u) = poly {
        match &mut decl {
            SurfaceDecl::Def {
                universe_params, ..
            }
            | SurfaceDecl::Theorem {
                universe_params, ..
            } => *universe_params = vec![u.clone()],
            _ => {}
        }
    }
    decl
}

/// Inputs to this family's compiler-authored AST builders. Text is accepted
/// only with a static lifetime for fixed canonical compiler paths. There is
/// deliberately no String, &String, or general &str implementation: source
/// names and dynamically generated identities must remain SurfaceName values.
pub(crate) trait CodataIdentifier {
    fn surface_name(self) -> SurfaceName;
}

impl CodataIdentifier for SurfaceName {
    fn surface_name(self) -> SurfaceName {
        self
    }
}

impl CodataIdentifier for &SurfaceName {
    fn surface_name(self) -> SurfaceName {
        self.clone()
    }
}

impl CodataIdentifier for &&SurfaceName {
    fn surface_name(self) -> SurfaceName {
        (*self).clone()
    }
}

impl CodataIdentifier for &'static str {
    fn surface_name(self) -> SurfaceName {
        SurfaceName::generated_path(self)
    }
}

/// A generated reference to the GLOBAL constant at this path
/// ([`SurfaceName::global_path`]): never resolved to a local. The codata
/// generators emit their terms inside the user's own binders (field and
/// parameter names), so a constant they name (`Eq`, `PUnit.unit`, `Sum.rec`,
/// `cond`, …) written as a plain generated identifier was captured by a user
/// binder of that spelling. A bare `&'static str` stays a binder the
/// generator itself introduces.
#[derive(Debug, Clone, Copy)]
pub(crate) struct GlobalPath(pub(crate) &'static str);

impl CodataIdentifier for GlobalPath {
    fn surface_name(self) -> SurfaceName {
        SurfaceName::global_path(self.0)
    }
}

pub(crate) fn surface_binder(
    name: impl CodataIdentifier,
    ty: Option<SurfaceExpr>,
    info: SurfaceBinderInfo,
) -> SurfaceBinder {
    SurfaceBinder::new_typed(name.surface_name(), ty, info)
}

/// Affix the actual terminal string component; never format and reparse a
/// displayed path. Numeric/generated identities keep their constructor as a
/// parent of a fresh generated component instead of becoming decimal strings.
pub(crate) fn affix_name(name: &SurfaceName, prefix: &str, suffix: &str) -> SurfaceName {
    match name.name().inner() {
        clean_kernel::name::NameInner::Str(_, text) => {
            name.parent().append(&SurfaceName::from_name(
                clean_kernel::Name::anon().str(format!("{prefix}{text}{suffix}")),
            ))
        }
        _ => name.append(&SurfaceName::from_name(
            clean_kernel::Name::anon().str(format!("{prefix}{suffix}")),
        )),
    }
}

/// Fixed compiler companion under an exact source owner.
pub(crate) fn child_name(name: &SurfaceName, child: &'static str) -> SurfaceName {
    name.append(&SurfaceName::generated_path(child))
}

/// A generated name assembled from two identities. For atomic string names
/// this preserves the historical label; otherwise their structural boundary
/// is retained. Callers still reject duplicate generated family members.
pub(crate) fn pair_name(left: &SurfaceName, separator: &str, right: &SurfaceName) -> SurfaceName {
    match (left.name().inner(), right.name().inner()) {
        (clean_kernel::name::NameInner::Str(lp, l), clean_kernel::name::NameInner::Str(rp, r))
            if lp.is_anon() && rp.is_anon() =>
        {
            SurfaceName::from_name(clean_kernel::Name::anon().str(format!("{l}{separator}{r}")))
        }
        _ => left
            .append(&SurfaceName::from_name(
                clean_kernel::Name::anon().str(separator),
            ))
            .append(right),
    }
}

pub(crate) fn strip_slot_suffix(slot: &SurfaceName) -> Option<SurfaceName> {
    let clean_kernel::name::NameInner::Str(_, text) = slot.name().inner() else {
        return None;
    };
    let field = text.strip_suffix('F').filter(|s| !s.is_empty())?;
    Some(slot.parent().append(&SurfaceName::from_name(
        clean_kernel::Name::anon().str(field),
    )))
}

pub(crate) fn registered_definition_name(
    result: &ElabResult,
) -> Result<clean_kernel::Name, ElabError> {
    match result {
        ElabResult::Definition { name, .. } => Ok(name.clone()),
        _ => Err(unsupported(
            "codata: generated definition did not return an exact registered owner",
        )),
    }
}

/// What a `codata` / `codef` command hands back: every declaration it
/// generated, elaborated, kernel-checked and registered, as one block.
///
/// These commands used to answer `Skipped` after registering real
/// declarations, and `Skipped` is the result of a command that declares
/// NOTHING. Every consumer that counts or re-checks declarations therefore
/// saw nothing: `clean project check` reported a codata-only package as
/// `pass, 0 declarations checked` (and, once its vacuity gate landed, refused
/// that valid package as "checked nothing"), `clean check` reported
/// "Checked 0 declarations", and the per-declaration trust gates of
/// `clean compile` never looked at them. A block of the registered results is
/// what was declared; `ElabResult::leaf_decls` flattens it for every consumer.
pub(crate) fn generated_declarations(results: Vec<ElabResult>) -> RegisteredElabResult {
    RegisteredElabResult {
        result: ElabResult::Multiple(results),
        warning: None,
        hole_contexts: Vec::new(),
    }
}

pub(crate) fn retain_registered_carrier(
    source_owner: &SurfaceName,
    generated: &SurfaceDecl,
    result: &ElabResult,
    carrier: &mut Option<clean_kernel::Name>,
) -> Result<(), ElabError> {
    if matches!(generated, SurfaceDecl::Def { name, .. } if name == source_owner) {
        if carrier.is_some() {
            return Err(unsupported("codata: duplicate generated carrier"));
        }
        *carrier = Some(registered_definition_name(result)?);
    }
    Ok(())
}

pub(crate) fn ident(name: impl CodataIdentifier) -> SurfaceExpr {
    SurfaceExpr::Ident(Span::dummy(), name.surface_name())
}

/// `@name args…` — Explicit-marked head, positional args.
pub(crate) fn at_app(name: impl CodataIdentifier, args: Vec<SurfaceExpr>) -> SurfaceExpr {
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
pub(crate) fn plain_app(name: impl CodataIdentifier, args: Vec<SurfaceExpr>) -> SurfaceExpr {
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
pub(crate) fn lam(names: &[impl CodataIdentifier + Clone], body: SurfaceExpr) -> SurfaceExpr {
    SurfaceExpr::Lambda(
        Span::dummy(),
        names
            .iter()
            .map(|n| {
                SurfaceBinder::new_typed(
                    n.clone().surface_name(),
                    None,
                    SurfaceBinderInfo::Explicit,
                )
            })
            .collect(),
        Box::new(body),
    )
}

/// `(name : ty) → body` (dependent) — a one-binder Pi.
pub(crate) fn pi(name: impl CodataIdentifier, ty: SurfaceExpr, body: SurfaceExpr) -> SurfaceExpr {
    SurfaceExpr::Pi(
        Span::dummy(),
        vec![SurfaceBinder::new_typed(
            name.surface_name(),
            Some(ty),
            SurfaceBinderInfo::Explicit,
        )],
        Box::new(body),
    )
}

/// `a → b` (non-dependent arrow).
pub(crate) fn arrow(a: SurfaceExpr, b: SurfaceExpr) -> SurfaceExpr {
    SurfaceExpr::Arrow(Span::dummy(), Box::new(a), Box::new(b))
}

pub(crate) fn type_universe() -> SurfaceExpr {
    SurfaceExpr::Universe(Span::dummy(), UniverseExpr::Type)
}

pub(crate) fn mk_def(
    name: SurfaceName,
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

pub(crate) fn mk_theorem(
    name: SurfaceName,
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
pub(crate) fn mentions(expr: &SurfaceExpr, name: &SurfaceName) -> bool {
    let mut found = false;
    walk(expr, &mut |e| {
        if let SurfaceExpr::Ident(_, id) = e {
            if id.has_prefix(name) {
                found = true;
            }
        }
    });
    found
}

pub(crate) fn walk(expr: &SurfaceExpr, f: &mut impl FnMut(&SurfaceExpr)) {
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
        | SurfaceExpr::SemiOutParam(_, e)
        // A universe instantiation wraps the name it instantiates. Without
        // this arm `mentions(T.{u} A, "T")` is FALSE, so a recursive argument
        // written `T.{u} A` is classified as a PAYLOAD and the declaration is
        // then refused for having no recursive argument at all — a refusal
        // that names the wrong problem entirely.
        | SurfaceExpr::UniverseInst(_, e, _) => walk(e, f),
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
    name: &'a SurfaceName,
    /// The single declared universe parameter, when polymorphic (v1: ≤1).
    poly: Option<&'a SurfaceName>,
    binders: &'a [SurfaceBinder],
    obs: Vec<(&'a SurfaceName, &'a SurfaceExpr)>,
    steps: Vec<&'a SurfaceName>,
}

fn validate<'a>(
    name: &'a SurfaceName,
    universe_params: &'a [SurfaceName],
    binders: &'a [SurfaceBinder],
    ty: &Option<Box<SurfaceExpr>>,
    fields: &'a [SurfaceField],
    deriving: &[SurfaceName],
    modifiers: &DeclModifiers,
) -> Result<CodataShape<'a>, ElabError> {
    let poly = match universe_params {
        [] => None,
        [u] => Some(u),
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
            deriving
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .join(", ")
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
    let expected_args: Vec<&SurfaceName> = binders.iter().map(|b| &b.name).collect();
    let mut split = fields.len();
    while split > 0 && is_self_at_params(&fields[split - 1].ty, name, &expected_args, poly) {
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
    let mut seen: Vec<&SurfaceName> = Vec::new();
    for f in fields {
        if seen.contains(&&f.name) {
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
            if f.name == SurfaceName::generated_path(reserved) {
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
        obs: obs_fields.iter().map(|f| (&f.name, &f.ty)).collect(),
        steps: step_fields.iter().map(|f| &f.name).collect(),
    })
}

/// Is `expr` exactly `head p1 … pk` (modulo parens) with the given
/// identifier arguments in order?
/// Does `expr` name the carrier `head`, either bare (`T`) or instantiated at
/// the declaration's OWN universe parameter (`T.{u}`)?
///
/// Accepting the second spelling is not cosmetic. `codata T.{u}` makes
/// `| Cons : A → T.{u} A → T.{u} A` the natural thing to write, and it was
/// refused with "must return `T` applied to exactly its declared parameters,
/// by name" — a diagnostic that never mentions universes and so reads as a
/// complaint about the arguments. Only the declaration's own parameter is
/// accepted: `T.{0}` inside a `codata T.{u}` denotes a DIFFERENT type, and
/// treating it as the carrier would silently monomorphise the declaration.
fn self_head_matches(expr: &SurfaceExpr, head: &SurfaceName, poly: Option<&SurfaceName>) -> bool {
    match strip_parens(expr) {
        SurfaceExpr::Ident(_, id) => id == head,
        SurfaceExpr::UniverseInst(_, inner, levels) => {
            let Some(u) = poly else { return false };
            matches!(strip_parens(inner), SurfaceExpr::Ident(_, id) if id == head)
                && matches!(levels.as_slice(), [LevelExpr::Param(p)] if p == u)
        }
        _ => false,
    }
}

pub(crate) fn is_self_at_params(
    expr: &SurfaceExpr,
    head: &SurfaceName,
    params: &[&SurfaceName],
    poly: Option<&SurfaceName>,
) -> bool {
    let expr = strip_parens(expr);
    if params.is_empty() {
        return self_head_matches(expr, head, poly);
    }
    let SurfaceExpr::App(_, h, args) = expr else {
        return false;
    };
    if !self_head_matches(h, head, poly) {
        return false;
    }
    if args.len() != params.len() {
        return false;
    }
    args.iter().zip(params).all(|(a, p)| {
        a.name.is_none() && matches!(strip_parens(&a.expr), SurfaceExpr::Ident(_, id) if id == *p)
    })
}

pub(crate) fn strip_parens(expr: &SurfaceExpr) -> &SurfaceExpr {
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
        body,
        deriving,
        modifiers,
        ..
    } = decl
    else {
        return Err(unsupported("elab_codata_decl: not a codata declaration"));
    };
    // VARIANT body (`| Ret : R → T | …`) — its own lane: the full envelope
    // validation (which takes no environment at all), then the definitional
    // tier generated into a candidate clone. Every envelope violation gets
    // its own named refusal and nothing partial can land. See
    // `designs/2026-08-28-variant-codata-surface.md`.
    let fields = match body {
        clean_parser::CodataBody::Record(fields) => fields,
        clean_parser::CodataBody::Variant(ctors) => {
            return crate::codata_variant::elab_variant_codata(
                env,
                name,
                universe_params,
                binders,
                ty,
                ctors,
                deriving,
                modifiers,
            )
        }
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
                let mut carrier = None;
                let mut declared = Vec::new();
                for (i, generated) in gen_decls.into_iter().enumerate() {
                    let registered = crate::elaborate_decl_and_register(&mut candidate, &generated)
                        .map_err(|e| {
                            unsupported(format!(
                                "indexed codata `{name}`: generated declaration {i} \
                                 failed to elaborate/kernel-check (env left \
                                 untouched): {e:?}"
                            ))
                        })?;
                    retain_registered_carrier(name, &generated, &registered, &mut carrier)?;
                    declared.push(registered);
                }
                // Mark the carrier as GENERATED by this command, so
                // recognition can require provenance rather than accepting any
                // type that merely owns a `<C>.corec`. Into the candidate, so a
                // codata whose generated declarations failed leaves no mark.
                candidate.mark_codata_carrier(
                    carrier.ok_or_else(|| unsupported("codata: generated carrier missing"))?,
                );
                *env = candidate;
                return Ok(generated_declarations(declared));
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

    let mut carrier = None;
    let mut declared = Vec::new();
    for (i, generated) in generate(&shape).into_iter().enumerate() {
        let registered =
            crate::elaborate_decl_and_register(&mut candidate, &generated).map_err(|e| {
                unsupported(format!(
                    "codata `{name}`: generated declaration {i} failed to \
                 elaborate/kernel-check (env left untouched): {e:?}"
                ))
            })?;
        retain_registered_carrier(name, &generated, &registered, &mut carrier)?;
        declared.push(registered);
    }
    // Same carrier provenance mark as the indexed lane above.
    candidate.mark_codata_carrier(
        carrier.ok_or_else(|| unsupported("codata: generated carrier missing"))?,
    );
    *env = candidate;
    Ok(generated_declarations(declared))
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

    let shape_f = child_name(name, "shapeF");
    let pos_f = child_name(name, "posF");
    let tgt_f = child_name(name, "tgtF");
    let container = |f: &SurfaceName| plain_app(f, params.clone());
    let self_ty = plain_app(name, params.clone());
    let corec_step = child_name(name, "corecStep");
    let corec = child_name(name, "corec");

    // The label type: right-nested PProd of the observation types.
    let label_ty = obs
        .iter()
        .rev()
        .map(|(_, t)| (*t).clone())
        .reduce(|acc, t| plain_app(GlobalPath("PProd"), vec![t, acc]))
        .expect("validate guarantees at least one observation");
    // The packed label from per-observation values.
    fn pack(vals: &[SurfaceExpr]) -> SurfaceExpr {
        match vals {
            [only] => only.clone(),
            [first, rest @ ..] => {
                plain_app(GlobalPath("PProd.mk"), vec![first.clone(), pack(rest)])
            }
            [] => unreachable!("validate guarantees at least one observation"),
        }
    }
    // The position type for m recursive fields: Unit for one, a
    // right-nested Sum of Units for more.
    fn pos_ty(m: usize, poly: Option<&SurfaceName>) -> SurfaceExpr {
        if m == 1 {
            punit_ty_p(poly)
        } else {
            plain_app(
                GlobalPath("Sum"),
                vec![punit_ty_p(poly), pos_ty(m - 1, poly)],
            )
        }
    }
    // The i-th position point out of m.
    fn pos_point(i: usize, m: usize) -> SurfaceExpr {
        if m == 1 {
            ident(GlobalPath("PUnit.unit"))
        } else if i == 0 {
            plain_app(GlobalPath("Sum.inl"), vec![ident(GlobalPath("PUnit.unit"))])
        } else {
            plain_app(GlobalPath("Sum.inr"), vec![pos_point(i - 1, m - 1)])
        }
    }
    // The coalgebra child function over the position type: selects the
    // i-th step function's next state.
    fn child_fn(step_apps: &[SurfaceExpr], poly: Option<&SurfaceName>) -> SurfaceExpr {
        match step_apps {
            [only] => lam(&["_"], only.clone()),
            [first, rest @ ..] => {
                let inner = match rest {
                    [only] => lam(&["_"], only.clone()),
                    _ => child_fn(rest, poly),
                };
                SurfaceExpr::Lambda(
                    Span::dummy(),
                    vec![surface_binder("b", None, SurfaceBinderInfo::Explicit)],
                    Box::new(SurfaceExpr::App(
                        Span::dummy(),
                        Box::new(SurfaceExpr::Explicit(
                            Span::dummy(),
                            Box::new(ident(GlobalPath("Sum.rec"))),
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

    let s_binder = surface_binder("S", Some(type_u(poly)), SurfaceBinderInfo::Implicit);
    let obs_f_names: Vec<SurfaceName> = obs.iter().map(|(n, _)| affix_name(n, "", "F")).collect();
    let step_f_names: Vec<SurfaceName> = steps.iter().map(|n| affix_name(n, "", "F")).collect();
    let mut corec_fn_binders: Vec<SurfaceBinder> = obs
        .iter()
        .zip(&obs_f_names)
        .map(|((_, t), fname)| {
            surface_binder(
                fname,
                Some(arrow(ident("S"), (*t).clone())),
                SurfaceBinderInfo::Explicit,
            )
        })
        .collect();
    for step_f in &step_f_names {
        corec_fn_binders.push(surface_binder(
            step_f,
            Some(arrow(ident("S"), ident("S"))),
            SurfaceBinderInfo::Explicit,
        ));
    }

    // @C.corec <ps> S obsF… stepF <extra> — reused by the law statements.
    let corec_call = |extra: SurfaceExpr| {
        let mut args = params.clone();
        args.push(ident("S"));
        args.extend(obs_f_names.iter().map(ident));
        args.extend(step_f_names.iter().map(ident));
        args.push(extra);
        at_app(&corec, args)
    };
    let head_call = |x: SurfaceExpr| {
        at_app(
            GlobalPath("Codata.IMhead"),
            vec![
                punit_ty_p(poly),
                container(&shape_f),
                container(&pos_f),
                container(&tgt_f),
                ident(GlobalPath("PUnit.unit")),
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
            lam(&["_", "_", "_"], ident(GlobalPath("PUnit.unit"))),
        ),
        // def C (ps) : Type := @Codata.IMIntl Unit … Unit.unit
        mk_def(
            (*name).clone(),
            explicit_binders.clone(),
            type_u(poly),
            at_app(
                GlobalPath("Codata.IMIntl"),
                vec![
                    punit_ty_p(poly),
                    container(&shape_f),
                    container(&pos_f),
                    container(&tgt_f),
                    ident(GlobalPath("PUnit.unit")),
                ],
            ),
        ),
    ];

    // Observation accessors: def C.obs_i {ps} (x : C ps) : T_i := <proj chain>
    let k = obs.len();
    for (i, (obs_name, obs_ty)) in obs.iter().enumerate() {
        out.push(mk_def(
            name.append(obs_name),
            {
                let mut bs = implicit_binders.clone();
                bs.push(surface_binder(
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
            name.append(step_name),
            {
                let mut bs = implicit_binders.clone();
                bs.push(surface_binder(
                    "x",
                    Some(self_ty.clone()),
                    SurfaceBinderInfo::Explicit,
                ));
                bs
            },
            self_ty.clone(),
            at_app(
                GlobalPath("Codata.IMchild"),
                vec![
                    punit_ty_p(poly),
                    container(&shape_f),
                    container(&pos_f),
                    container(&tgt_f),
                    ident(GlobalPath("PUnit.unit")),
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
                        plain_app(GlobalPath("Codata.uFam"), vec![ident("S")]),
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
            bs.push(surface_binder(
                "s",
                Some(ident("S")),
                SurfaceBinderInfo::Explicit,
            ));
            bs
        },
        self_ty.clone(),
        at_app(GlobalPath("Codata.ucorec"), {
            let mut step_args = params.clone();
            step_args.push(ident("S"));
            step_args.extend(obs_f_names.iter().map(ident));
            step_args.extend(step_f_names.iter().map(ident));
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
    let mk_step_name = child_name(name, "mkStep");
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
                surface_binder(
                    "a",
                    Some(unit_self(vec![ident(GlobalPath("PUnit.unit"))])),
                    SurfaceBinderInfo::Explicit,
                ),
                surface_binder(
                    "f",
                    Some(SurfaceExpr::Pi(
                        Span::dummy(),
                        vec![surface_binder(
                            "b",
                            Some({
                                let mut args = params.clone();
                                args.extend([ident(GlobalPath("PUnit.unit")), ident("a")]);
                                plain_app(&pos_f, args)
                            }),
                            SurfaceBinderInfo::Explicit,
                        )],
                        Box::new(plain_app(GlobalPath("Codata.IMIntl"), {
                            let mut args =
                                vec![container(&shape_f), container(&pos_f), container(&tgt_f)];
                            args.push({
                                let mut targs = params.clone();
                                targs.extend([
                                    ident(GlobalPath("PUnit.unit")),
                                    ident("a"),
                                    ident("b"),
                                ]);
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
                    GlobalPath("Codata.IMIntl"),
                    vec![container(&shape_f), container(&pos_f), container(&tgt_f)],
                ),
                ident(GlobalPath("PUnit.unit")),
            ],
        ),
        plain_app(GlobalPath("Sigma.mk"), vec![ident("a"), ident("f")]),
    ));
    // Field-value binders for mk.
    let mut mk_binders = implicit_binders.clone();
    for (obs_name, obs_ty) in obs.iter() {
        mk_binders.push(surface_binder(
            affix_name(obs_name, "", "V"),
            Some((*obs_ty).clone()),
            SurfaceBinderInfo::Explicit,
        ));
    }
    for step_name in steps.iter() {
        mk_binders.push(surface_binder(
            affix_name(step_name, "", "V"),
            Some(self_ty.clone()),
            SurfaceBinderInfo::Explicit,
        ));
    }
    let mk_label = pack(
        &obs.iter()
            .map(|(n, _)| ident(affix_name(n, "", "V")))
            .collect::<Vec<_>>(),
    );
    let mk_children: Vec<SurfaceExpr> = steps
        .iter()
        .map(|n| ident(affix_name(n, "", "V")))
        .collect();
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
                targs.extend([ident(GlobalPath("PUnit.unit")), label.clone(), bpos]);
                plain_app(
                    GlobalPath("Codata.IMIntl"),
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
            vec![surface_binder("b", None, SurfaceBinderInfo::Explicit)],
            Box::new(mut_state_chain_p(
                &mk_children,
                0,
                &plain_app(
                    GlobalPath("Codata.IMIntl"),
                    vec![container(&shape_f), container(&pos_f), container(&tgt_f)],
                ),
                &{
                    let tgt_f = tgt_f.clone();
                    let pe = params.clone();
                    let label = mk_label.clone();
                    move |bpos: SurfaceExpr| -> SurfaceExpr {
                        let mut targs = pe.clone();
                        targs.extend([ident(GlobalPath("PUnit.unit")), label.clone(), bpos]);
                        plain_app(&tgt_f, targs)
                    }
                },
                ident("b"),
                None,
            )),
        )
    };
    out.push(mk_def(
        child_name(name, "mk"),
        mk_binders.clone(),
        self_ty.clone(),
        at_app(GlobalPath("Codata.IMmk"), {
            let mut args = vec![
                punit_ty_p(poly),
                container(&shape_f),
                container(&pos_f),
                container(&tgt_f),
                ident(GlobalPath("PUnit.unit")),
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
                .map(|(n, _)| ident(affix_name(n, "", "V")))
                .chain(steps.iter().map(|n| ident(affix_name(n, "", "V")))),
        );
        at_app(child_name(name, "mk"), args)
    };
    for field_name in obs.iter().map(|(n, _)| *n).chain(steps.iter().copied()) {
        let full = name.append(field_name);
        let mut acc_args = params.clone();
        acc_args.push(mk_call.clone());
        out.push(mk_theorem(
            affix_name(&full, "", "_mk"),
            mk_binders.clone(),
            SurfaceExpr::App(
                Span::dummy(),
                Box::new(ident(GlobalPath("Eq"))),
                vec![
                    SurfaceArg::positional(at_app(&full, acc_args)),
                    SurfaceArg::positional(ident(affix_name(field_name, "", "V"))),
                ],
            ),
            ident(GlobalPath("rfl")),
        ));
    }

    // Per-observation law: @C.obs_i ps (corec-call s) = obsF_i s := rfl
    let law_binders = || {
        let mut bs = implicit_binders.clone();
        bs.push(s_binder.clone());
        bs.extend(corec_fn_binders.clone());
        bs.push(surface_binder(
            "s",
            Some(ident("S")),
            SurfaceBinderInfo::Explicit,
        ));
        bs
    };
    for ((obs_name, _), fname) in obs.iter().zip(&obs_f_names) {
        let obs_full = name.append(obs_name);
        let mut obs_args = params.clone();
        obs_args.push(corec_call(ident("s")));
        out.push(mk_theorem(
            affix_name(&obs_full, "", "_corec"),
            law_binders(),
            SurfaceExpr::App(
                Span::dummy(),
                Box::new(ident(GlobalPath("Eq"))),
                vec![
                    SurfaceArg::positional(at_app(&obs_full, obs_args)),
                    SurfaceArg::positional(plain_app(fname, vec![ident("s")])),
                ],
            ),
            ident(GlobalPath("rfl")),
        ));
    }

    // Per-recursive-field law:
    //   @C.step_i ps (corec-call s) = corec-call (step_iF s) := rfl
    for (step_name, fname) in steps.iter().zip(&step_f_names) {
        let step_full = name.append(step_name);
        let mut step_args = params.clone();
        step_args.push(corec_call(ident("s")));
        out.push(mk_theorem(
            affix_name(&step_full, "", "_corec"),
            law_binders(),
            SurfaceExpr::App(
                Span::dummy(),
                Box::new(ident(GlobalPath("Eq"))),
                vec![
                    SurfaceArg::positional(at_app(&step_full, step_args)),
                    SurfaceArg::positional(corec_call(plain_app(fname, vec![ident("s")]))),
                ],
            ),
            ident(GlobalPath("rfl")),
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
    let corec_name = child_name(&head_name, "corec");
    let corec_const = corec_name.name().clone();
    if env.get_const(&corec_const).is_none() {
        return Err(unsupported(format!(
            "codef: `{head_name}` is not a codata type — `{corec_name}` does \
             not exist (declare it with the `codata` command first)"
        )));
    }
    let param_names = env.get_typed_param_names(&corec_const).ok_or_else(|| {
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
    if param_names.len() != param_infos.len() {
        return Err(unsupported(
            "codef: parameter names and binder kinds disagree",
        ));
    }
    let mut slots: Vec<SurfaceName> = param_names
        .iter()
        .zip(param_infos.iter())
        .filter(|(_, i)| matches!(i, clean_kernel::BinderInfo::Default))
        .map(|(n, _)| SurfaceName::from_name(n.clone()))
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
    for slot in &slots {
        if !matches!(
            slot.name().inner(),
            clean_kernel::name::NameInner::Str(_, _)
        ) {
            return Err(unsupported("codef: unsupported non-string corecursor slot"));
        }
    }
    let indexed = slots
        .last()
        .is_some_and(|sl| strip_slot_suffix(sl).is_none());
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
            let registered = crate::elaborate_decl_and_register(&mut candidate, &generated)
                .map_err(|e| {
                    unsupported(format!(
                        "codef `{name}` (mk-guarded): the generated corecursor \
                         application failed to elaborate/kernel-check (env left \
                         untouched): {e:?}"
                    ))
                })?;
            *env = candidate;
            return Ok(generated_declarations(vec![registered]));
        }
    }

    // Map each slot `<field>F` to its clause, building the per-slot lambda.
    let state_name = state.map_or_else(|| SurfaceName::generated_path("_"), |b| b.name.clone());
    let mut slot_lambdas: Vec<SurfaceExpr> = Vec::new();
    let mut used: Vec<SurfaceName> = Vec::new();
    // (field, index the author wrote) for each indexed self-call, checked below.
    let mut idx_checks: Vec<(SurfaceName, SurfaceExpr)> = Vec::new();
    for slot in &slots {
        let field = strip_slot_suffix(slot).ok_or_else(|| unsupported(
            format!("codef: unsupported corecursor slot `{slot}` (expected a nonempty terminal string with F suffix)")
        ))?;
        let Some((_, value)) = clauses.iter().find(|(n, _)| n == &field) else {
            return Err(unsupported(format!(
                "codef: missing clause for observation `{field}` of \
                 `{head_name}`"
            )));
        };
        used.push(field.clone());
        // A syntactic self-call is a corecursive step: the lambda returns
        // the NEW STATE. Anything else is an observation value and must
        // not mention the function being defined (productivity).
        let body = match self_call_arg(value, name, indexed) {
            Some(call) => {
                if let Some(written) = call.index {
                    idx_checks.push((field.clone(), written));
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
            lam_binders.push(surface_binder(
                &ib.name,
                ib.ty.as_deref().cloned(),
                SurfaceBinderInfo::Explicit,
            ));
        }
        lam_binders.push(surface_binder(
            &state_name,
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
        if !used.contains(n) {
            return Err(unsupported(format!(
                "codef: `{n}` is not an observation of `{head_name}` \
                 (expected: {})",
                used.iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(", ")
            )));
        }
    }

    // The state type and initial state.
    let state_ty = state
        .and_then(|b| b.ty.as_deref().cloned())
        .unwrap_or_else(punit_ty);
    let init_state = state.map_or_else(|| ident(GlobalPath("PUnit.unit")), |b| ident(&b.name));

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
        let accessor = head_name.append(field);
        if env.get_const(&accessor.name().clone()).is_none() {
            continue;
        }
        let mut probe_args = type_args.clone();
        probe_args.pop(); // the result type's own index
        probe_args.push(written.clone());
        let mut probe_binders = binders.to_vec();
        probe_binders.push(surface_binder(
            "_idxProbeSelf",
            Some((**ty).clone()),
            SurfaceBinderInfo::Explicit,
        ));
        let probe = mk_def(
            name.append(&affix_name(field, "_indexProbe_", "")),
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
    let registered =
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
        registered_definition_name(&registered)?,
        clean_kernel::CodataOrigin {
            lane: if indexed {
                clean_kernel::CodataLane::Indexed
            } else {
                clean_kernel::CodataLane::Plain
            },
            carrier: head_name.name().clone(),
            corec: corec_const.clone(),
            slots: slots.iter().map(ToString::to_string).collect(),
        },
    );
    *env = candidate;
    Ok(generated_declarations(vec![registered]))
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
fn self_call_arg(expr: &SurfaceExpr, fname: &SurfaceName, indexed: bool) -> Option<SelfCall> {
    match strip_parens(expr) {
        SurfaceExpr::Ident(_, id) if id == fname && !indexed => Some(SelfCall {
            index: None,
            state: ident(GlobalPath("PUnit.unit")),
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
                ident(GlobalPath("PUnit.unit"))
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
    name: &'a SurfaceName,
    binders: &'a [SurfaceBinder],
    /// Observations: (name, type). The leading non-recursive fields.
    obs: Vec<(&'a SurfaceName, &'a SurfaceExpr)>,
    /// Recursive fields: (name, target member index). The trailing block.
    steps: Vec<(&'a SurfaceName, usize)>,
}

/// Elaborate a `mutual` block whose members are all `codata`.
pub(crate) fn elab_mutual_codata(
    env: &mut Environment,
    members: &[SurfaceDecl],
) -> Result<RegisteredElabResult, ElabError> {
    if members.len() < 2 {
        return Err(unsupported("mutual codata needs at least two members"));
    }
    let names: Vec<&SurfaceName> = members
        .iter()
        .map(|d| match d {
            SurfaceDecl::Codata { name, .. } => Ok(name),
            _ => Err(unsupported(
                "mutual codata: every member of the block must be a `codata` \
                 declaration",
            )),
        })
        .collect::<Result<_, _>>()?;
    let shapes: Vec<(MutualMember<'_>, Option<&SurfaceName>)> = members
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
    let b0: Vec<&SurfaceName> = shapes[0].binders.iter().map(|b| &b.name).collect();
    let b1: Vec<&SurfaceName> = shapes[1].binders.iter().map(|b| &b.name).collect();
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
    let mut declared = Vec::new();
    for (i, generated) in generated_decls.into_iter().enumerate() {
        if std::env::var("CLEAN_CODATA_DUMP").is_ok() {
            eprintln!("[codata-gen {i}] {generated:#?}");
        }
        let registered =
            crate::elaborate_decl_and_register(&mut candidate, &generated).map_err(|e| {
                unsupported(format!(
                    "mutual codata `{}`/`{}`: generated declaration {i} failed \
                 to elaborate/kernel-check (env left untouched): {e:?}",
                    names[0], names[1]
                ))
            })?;
        declared.push(registered);
    }
    *env = candidate;
    Ok(generated_declarations(declared))
}

fn validate_mutual_member<'a>(
    decl: &'a SurfaceDecl,
    names: &[&SurfaceName],
) -> Result<(MutualMember<'a>, Option<&'a SurfaceName>), ElabError> {
    let SurfaceDecl::Codata {
        name,
        universe_params,
        binders,
        ty,
        body,
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
    let clean_parser::CodataBody::Record(fields) = body else {
        return Err(unsupported(format!(
            "mutual codata member `{name}`: a VARIANT codata body \
             (`| Ctor : …`) cannot appear in a `mutual` block — mutual \
             variant codata is outside the VC1 envelope \
             (designs/2026-08-28-variant-codata-surface.md §5)"
        )));
    };
    let member_poly = match universe_params.as_slice() {
        [] => None,
        [u] => Some(u),
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
    let params: Vec<&SurfaceName> = binders.iter().map(|b| &b.name).collect();
    let target_of = |t: &SurfaceExpr| -> Option<usize> {
        names
            .iter()
            .position(|n| is_self_at_params(t, n, &params, member_poly))
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
    let mut seen: Vec<&SurfaceName> = Vec::new();
    for f in fields.iter() {
        if seen.contains(&&f.name) {
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
            obs: obs_fields.iter().map(|f| (&f.name, &f.ty)).collect(),
            steps: step_fields
                .iter()
                .map(|f| {
                    (
                        &f.name,
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
fn mutual_label_ty_p(
    obs: &[(&SurfaceName, &SurfaceExpr)],
    poly: Option<&SurfaceName>,
) -> SurfaceExpr {
    obs.iter()
        .rev()
        .map(|(_, t)| (*t).clone())
        .reduce(|acc, t| plain_app(GlobalPath("PProd"), vec![t, acc]))
        .unwrap_or_else(|| punit_ty_p(poly))
}

/// Right-nested `PProd.mk` chain (`Unit.unit` when no observations).
fn mutual_pack(vals: &[SurfaceExpr]) -> SurfaceExpr {
    match vals {
        [] => ident(GlobalPath("PUnit.unit")),
        [only] => only.clone(),
        [first, rest @ ..] => plain_app(
            GlobalPath("PProd.mk"),
            vec![first.clone(), mutual_pack(rest)],
        ),
    }
}

/// The position type for m recursive fields (same shape as single codata).
/// Position tower at the declared level: `PUnit.{u+1}` towers when the
/// codata is polymorphic (positions live in the same universe as the
/// families — the plain-lane discipline), `PUnit.{1}` otherwise.
fn mut_pos_ty_p(m: usize, poly: Option<&SurfaceName>) -> SurfaceExpr {
    if m <= 1 {
        punit_ty_p(poly)
    } else {
        plain_app(
            GlobalPath("Sum"),
            vec![punit_ty_p(poly), mut_pos_ty_p(m - 1, poly)],
        )
    }
}

fn mut_pos_point(i: usize, m: usize) -> SurfaceExpr {
    if m <= 1 {
        ident(GlobalPath("PUnit.unit"))
    } else if i == 0 {
        plain_app(GlobalPath("Sum.inl"), vec![ident(GlobalPath("PUnit.unit"))])
    } else {
        plain_app(GlobalPath("Sum.inr"), vec![mut_pos_point(i - 1, m - 1)])
    }
}

fn lam1(name: impl CodataIdentifier, body: SurfaceExpr) -> SurfaceExpr {
    SurfaceExpr::Lambda(
        Span::dummy(),
        vec![surface_binder(name, None, SurfaceBinderInfo::Explicit)],
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
    args[0].name = Some(SurfaceName::generated_path("motive"));
    args.extend([
        SurfaceArg::positional(fc),
        SurfaceArg::positional(tc),
        SurfaceArg::positional(scrut),
    ]);
    SurfaceExpr::App(Span::dummy(), Box::new(ident(GlobalPath("Bool.rec"))), args)
}

/// Non-dependent Sum.rec chain over m positions returning `Bool` targets.
fn mut_tgt_chain_p(
    targets: &[SurfaceExpr],
    scrut: SurfaceExpr,
    poly: Option<&SurfaceName>,
) -> SurfaceExpr {
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
                    Box::new(ident(GlobalPath("Sum.rec"))),
                )),
                vec![
                    SurfaceArg::positional(punit_ty_p(poly)),
                    SurfaceArg::positional(mut_pos_ty_p(rest.len(), poly)),
                    SurfaceArg::positional(lam1("_", ident(GlobalPath("Bool")))),
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
    poly: Option<&SurfaceName>,
) -> SurfaceExpr {
    match branch_states {
        [only] => only.clone(),
        [first, rest @ ..] => {
            let wrap = |e: SurfaceExpr, d: usize| -> SurfaceExpr {
                let mut w = e;
                for _ in 0..d {
                    w = plain_app(GlobalPath("Sum.inr"), vec![w]);
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
                    Box::new(ident(GlobalPath("Sum.rec"))),
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

fn generate_mutual(shapes: &[MutualMember<'_>], poly: Option<&SurfaceName>) -> Vec<SurfaceDecl> {
    let names: Vec<&SurfaceName> = shapes.iter().map(|m| m.name).collect();
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

    let joint = names[0].append(names[1]);
    let shape_f = child_name(&joint, "shapeF");
    let pos_f = child_name(&joint, "posF");
    let tgt_f = child_name(&joint, "tgtF");
    let st_f = child_name(&joint, "stF");
    let mk_step = child_name(&joint, "mkStep");
    let step_fn = child_name(&joint, "step");
    let container = |f: &SurfaceName| plain_app(f, param_exprs.clone());

    let mut out = Vec::new();

    // shapeF
    out.push(mk_def(
        shape_f.clone(),
        explicit_binders.clone(),
        arrow(ident(GlobalPath("Bool")), type_u(poly)),
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
        pi("i", ident(GlobalPath("Bool")), {
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
                    surface_binder("_", None, SurfaceBinderInfo::Explicit),
                    surface_binder("_", None, SurfaceBinderInfo::Explicit),
                ],
                Box::new(targets[0].clone()),
            )
        } else {
            SurfaceExpr::Lambda(
                Span::dummy(),
                vec![
                    surface_binder("_", None, SurfaceBinderInfo::Explicit),
                    surface_binder("pb", None, SurfaceBinderInfo::Explicit),
                ],
                Box::new(mut_tgt_chain_p(&targets, ident("pb"), poly)),
            )
        }
    };
    out.push(mk_def(
        tgt_f.clone(),
        explicit_binders.clone(),
        pi("i", ident(GlobalPath("Bool")), {
            let mut sargs = param_exprs.clone();
            sargs.push(ident("i"));
            pi("a", plain_app(&shape_f, sargs), {
                let mut pargs = param_exprs.clone();
                pargs.extend([ident("i"), ident("a")]);
                arrow(plain_app(&pos_f, pargs), ident(GlobalPath("Bool")))
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
                        arrow(plain_app(&pos_f, pargs), ident(GlobalPath("Bool")))
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
            m.name.clone(),
            explicit_binders.clone(),
            type_u(poly),
            at_app(
                GlobalPath("Codata.IMIntl"),
                vec![
                    ident(GlobalPath("Bool")),
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
                GlobalPath("Codata.IMhead"),
                vec![
                    ident(GlobalPath("Bool")),
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
                m.name.append(obs_name),
                {
                    let mut bs = implicit_binders.clone();
                    bs.push(surface_binder(
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
                m.name.append(step_name),
                {
                    let mut bs = implicit_binders.clone();
                    bs.push(surface_binder(
                        "x",
                        Some(self_ty.clone()),
                        SurfaceBinderInfo::Explicit,
                    ));
                    bs
                },
                plain_app(names[*tgt_mi], param_exprs.clone()),
                at_app(
                    GlobalPath("Codata.IMchild"),
                    vec![
                        ident(GlobalPath("Bool")),
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
            surface_binder("S1", Some(type_u(poly)), SurfaceBinderInfo::Explicit),
            surface_binder("S2", Some(type_u(poly)), SurfaceBinderInfo::Explicit),
        ],
        arrow(ident(GlobalPath("Bool")), type_u(poly)),
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
                surface_binder("S1", Some(type_u(poly)), SurfaceBinderInfo::Implicit),
                surface_binder("S2", Some(type_u(poly)), SurfaceBinderInfo::Implicit),
                surface_binder(
                    "tg",
                    Some(ident(GlobalPath("Bool"))),
                    SurfaceBinderInfo::Explicit,
                ),
                surface_binder(
                    "a",
                    Some({
                        let mut args = param_exprs.clone();
                        args.push(ident("tg"));
                        plain_app(&shape_f, args)
                    }),
                    SurfaceBinderInfo::Explicit,
                ),
                surface_binder(
                    "f",
                    Some(SurfaceExpr::Pi(
                        Span::dummy(),
                        vec![surface_binder(
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
        plain_app(GlobalPath("Sigma.mk"), vec![ident("a"), ident("f")]),
    ));

    // Per-field corec function binders (member 0's fields, then member 1's;
    // member-prefixed so shared field names across members cannot clash).
    let mut fn_binders: Vec<SurfaceBinder> = Vec::new();
    for (mi, m) in shapes.iter().enumerate() {
        let s_own = if mi == 0 { "S1" } else { "S2" };
        for (obs_name, obs_ty) in &m.obs {
            fn_binders.push(surface_binder(
                affix_name(&pair_name(m.name, "_", obs_name), "", "F"),
                Some(arrow(ident(s_own), (*obs_ty).clone())),
                SurfaceBinderInfo::Explicit,
            ));
        }
        for (step_name, tgt_mi) in &m.steps {
            let s_tgt = if *tgt_mi == 0 { "S1" } else { "S2" };
            fn_binders.push(surface_binder(
                affix_name(&pair_name(m.name, "_", step_name), "", "F"),
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
                .map(|(n, _)| ident(affix_name(&pair_name(m.name, "_", n), "", "F")))
                .chain(
                    m.steps
                        .iter()
                        .map(|(n, _)| ident(affix_name(&pair_name(m.name, "_", n), "", "F"))),
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
                .map(|(n, _)| {
                    plain_app(
                        affix_name(&pair_name(m.name, "_", n), "", "F"),
                        vec![ident("sv")],
                    )
                })
                .collect::<Vec<_>>(),
        );
        let branch_states: Vec<SurfaceExpr> = m
            .steps
            .iter()
            .map(|(n, _)| {
                plain_app(
                    affix_name(&pair_name(m.name, "_", n), "", "F"),
                    vec![ident("sv")],
                )
            })
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
                surface_binder("S1", Some(type_u(poly)), SurfaceBinderInfo::Implicit),
                surface_binder("S2", Some(type_u(poly)), SurfaceBinderInfo::Implicit),
            ]);
            bs.extend(fn_binders.clone());
            bs
        },
        pi("j", ident(GlobalPath("Bool")), {
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
        let corec_name = child_name(m.name, "corec");
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
                    surface_binder("S1", Some(type_u(poly)), SurfaceBinderInfo::Implicit),
                    surface_binder("S2", Some(type_u(poly)), SurfaceBinderInfo::Implicit),
                ]);
                bs.extend(fn_binders.clone());
                bs.push(surface_binder(
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
                    ident(GlobalPath("Bool")),
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
        let mk_step_name = child_name(m.name, "mkStep2");
        out.push(mk_def(
            mk_step_name.clone(),
            {
                let mut bs = implicit_binders.clone();
                bs.extend([
                    surface_binder(
                        "a",
                        Some({
                            let mut args = param_exprs.clone();
                            args.push(tag(mi));
                            plain_app(&shape_f, args)
                        }),
                        SurfaceBinderInfo::Explicit,
                    ),
                    surface_binder(
                        "f",
                        Some(SurfaceExpr::Pi(
                            Span::dummy(),
                            vec![surface_binder(
                                "b",
                                Some({
                                    let mut args = param_exprs.clone();
                                    args.extend([tag(mi), ident("a")]);
                                    plain_app(&pos_f, args)
                                }),
                                SurfaceBinderInfo::Explicit,
                            )],
                            Box::new(plain_app(
                                GlobalPath("Codata.IMIntl"),
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
                        GlobalPath("Codata.IMIntl"),
                        vec![container(&shape_f), container(&pos_f), container(&tgt_f)],
                    ),
                    tag(mi),
                ],
            ),
            plain_app(GlobalPath("Sigma.mk"), vec![ident("a"), ident("f")]),
        ));
        let mut mk_binders = implicit_binders.clone();
        for (obs_name, obs_ty) in m.obs.iter() {
            mk_binders.push(surface_binder(
                affix_name(obs_name, "", "V"),
                Some((*obs_ty).clone()),
                SurfaceBinderInfo::Explicit,
            ));
        }
        for (step_name, tgt_mi) in m.steps.iter() {
            mk_binders.push(surface_binder(
                affix_name(step_name, "", "V"),
                Some(plain_app(names[*tgt_mi], param_exprs.clone())),
                SurfaceBinderInfo::Explicit,
            ));
        }
        let mk_label = mutual_pack(
            &m.obs
                .iter()
                .map(|(n, _)| ident(affix_name(n, "", "V")))
                .collect::<Vec<_>>(),
        );
        let mk_children: Vec<SurfaceExpr> = m
            .steps
            .iter()
            .map(|(n, _)| ident(affix_name(n, "", "V")))
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
                        GlobalPath("Codata.IMIntl"),
                        vec![container(&shape_f), container(&pos_f), container(&tgt_f)],
                    ),
                    &tgt_full,
                    ident("b"),
                    poly,
                ),
            )
        };
        out.push(mk_def(
            child_name(m.name, "mk"),
            mk_binders.clone(),
            self_ty.clone(),
            at_app(GlobalPath("Codata.IMmk"), {
                let mut mkargs = param_exprs.clone();
                mkargs.extend([mk_label.clone(), mk_child_fn]);
                vec![
                    ident(GlobalPath("Bool")),
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
                    .map(|(n, _)| ident(affix_name(n, "", "V")))
                    .chain(m.steps.iter().map(|(n, _)| ident(affix_name(n, "", "V")))),
            );
            at_app(child_name(m.name, "mk"), args)
        };
        for field_name in m
            .obs
            .iter()
            .map(|(n, _)| *n)
            .chain(m.steps.iter().map(|(n, _)| *n))
        {
            let full = m.name.append(field_name);
            let mut acc_args = param_exprs.clone();
            acc_args.push(mk_call.clone());
            out.push(mk_theorem(
                affix_name(&full, "", "_mk"),
                mk_binders.clone(),
                SurfaceExpr::App(
                    Span::dummy(),
                    Box::new(ident(GlobalPath("Eq"))),
                    vec![
                        SurfaceArg::positional(at_app(&full, acc_args)),
                        SurfaceArg::positional(ident(affix_name(field_name, "", "V"))),
                    ],
                ),
                ident(GlobalPath("rfl")),
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
            at_app(child_name(names[member], "corec"), args)
        };
        let law_binders = || {
            let mut bs = implicit_binders.clone();
            bs.extend([
                surface_binder("S1", Some(type_u(poly)), SurfaceBinderInfo::Implicit),
                surface_binder("S2", Some(type_u(poly)), SurfaceBinderInfo::Implicit),
            ]);
            bs.extend(fn_binders.clone());
            bs.push(surface_binder(
                "s",
                Some(ident(if mi == 0 { "S1" } else { "S2" })),
                SurfaceBinderInfo::Explicit,
            ));
            bs
        };
        for (obs_name, _) in &m.obs {
            let full = m.name.append(obs_name);
            let mut acc_args = param_exprs.clone();
            acc_args.push(corec_call(mi, ident("s")));
            out.push(mk_theorem(
                affix_name(&full, "", "_corec"),
                law_binders(),
                SurfaceExpr::App(
                    Span::dummy(),
                    Box::new(ident(GlobalPath("Eq"))),
                    vec![
                        SurfaceArg::positional(at_app(&full, acc_args)),
                        SurfaceArg::positional(plain_app(
                            affix_name(&pair_name(m.name, "_", obs_name), "", "F"),
                            vec![ident("s")],
                        )),
                    ],
                ),
                ident(GlobalPath("rfl")),
            ));
        }
        for (step_name, tgt_mi) in &m.steps {
            let full = m.name.append(step_name);
            let mut acc_args = param_exprs.clone();
            acc_args.push(corec_call(mi, ident("s")));
            out.push(mk_theorem(
                affix_name(&full, "", "_corec"),
                law_binders(),
                SurfaceExpr::App(
                    Span::dummy(),
                    Box::new(ident(GlobalPath("Eq"))),
                    vec![
                        SurfaceArg::positional(at_app(&full, acc_args)),
                        SurfaceArg::positional(corec_call(
                            *tgt_mi,
                            plain_app(
                                affix_name(&pair_name(m.name, "_", step_name), "", "F"),
                                vec![ident("s")],
                            ),
                        )),
                    ],
                ),
                ident(GlobalPath("rfl")),
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
    name: &'a SurfaceName,
    /// The single declared universe parameter, when polymorphic (v1: ≤1).
    poly: Option<&'a SurfaceName>,
    binders: &'a [SurfaceBinder],
    idx_binders: &'a [SurfaceBinder],
    idx_name: &'a SurfaceName,
    idx_ty: &'a SurfaceExpr,
    obs: Vec<(&'a SurfaceName, &'a SurfaceExpr)>,
    /// (field name, target index expressions — one per index binder)
    steps: Vec<(&'a SurfaceName, Vec<&'a SurfaceExpr>)>,
}

#[allow(clippy::too_many_arguments)]
fn validate_indexed<'a>(
    name: &'a SurfaceName,
    universe_params: &'a [SurfaceName],
    binders: &'a [SurfaceBinder],
    pi_binders: &'a [SurfaceBinder],
    fields: &'a [SurfaceField],
    deriving: &[SurfaceName],
    modifiers: &DeclModifiers,
) -> Result<IndexedShape<'a>, ElabError> {
    let poly = match universe_params {
        [] => None,
        [u] => Some(u),
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
    let param_names: Vec<&SurfaceName> = binders.iter().map(|b| &b.name).collect();
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
            if !matches!(strip_parens(&a.expr), SurfaceExpr::Ident(_, id) if id == *pn) {
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
    let mut seen: Vec<&SurfaceName> = Vec::new();
    for f in fields {
        if seen.contains(&&f.name) {
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
        obs: obs_fields.iter().map(|f| (&f.name, &f.ty)).collect(),
        steps: step_fields
            .iter()
            .map(|f| {
                (
                    &f.name,
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
    let capp = |f: &SurfaceName, extra: Vec<SurfaceExpr>| -> SurfaceExpr {
        let mut args = param_exprs.clone();
        args.extend(extra);
        plain_app(f, args)
    };
    let shape_f = child_name(name, "shapeF");
    let pos_f = child_name(name, "posF");
    let tgt_f = child_name(name, "tgtF");
    let mk_step = child_name(name, "mkStep");
    let step_fn = child_name(name, "stepFn");
    let corec = child_name(name, "corec");
    let m = steps.len();
    let k = obs.len();

    let label_ty = obs
        .iter()
        .rev()
        .map(|(_, t)| (*t).clone())
        .reduce(|acc, t| plain_app(GlobalPath("PProd"), vec![t, acc]))
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
                surface_binder("_", None, SurfaceBinderInfo::Explicit),
                surface_binder("_", None, SurfaceBinderInfo::Explicit),
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
                surface_binder(*idx_name, None, SurfaceBinderInfo::Explicit),
                surface_binder("_", None, SurfaceBinderInfo::Explicit),
                surface_binder("_", None, SurfaceBinderInfo::Explicit),
            ],
            Box::new(idx_targets[0].clone()),
        )
    } else {
        SurfaceExpr::Lambda(
            Span::dummy(),
            vec![
                surface_binder(*idx_name, None, SurfaceBinderInfo::Explicit),
                surface_binder("_", None, SurfaceBinderInfo::Explicit),
                surface_binder("pb", None, SurfaceBinderInfo::Explicit),
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
        (*name).clone(),
        {
            let mut bs = explicit_params.clone();
            bs.push(surface_binder(
                *idx_name,
                Some(ity.clone()),
                SurfaceBinderInfo::Explicit,
            ));
            bs
        },
        type_u(poly),
        at_app(
            GlobalPath("Codata.IMIntl"),
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
    let idx_binder = surface_binder(*idx_name, Some(ity.clone()), SurfaceBinderInfo::Implicit);
    // Observation accessors.
    for (oi, (obs_name, obs_ty)) in obs.iter().enumerate() {
        let mut sel = at_app(
            GlobalPath("Codata.IMhead"),
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
            name.append(obs_name),
            {
                let mut bs = implicit_params.clone();
                bs.extend([
                    idx_binder.clone(),
                    surface_binder(
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
            name.append(step_name),
            {
                let mut bs = implicit_params.clone();
                bs.extend([
                    idx_binder.clone(),
                    surface_binder(
                        "x",
                        Some(self_at(ident(idx_name))),
                        SurfaceBinderInfo::Explicit,
                    ),
                ]);
                bs
            },
            self_at(idx_expr[0].clone()),
            at_app(
                GlobalPath("Codata.IMchild"),
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
    let s_binder = surface_binder(
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
                surface_binder(*idx_name, Some(ity.clone()), SurfaceBinderInfo::Explicit),
                surface_binder(
                    "a",
                    Some(capp(&shape_f, vec![ident(idx_name)])),
                    SurfaceBinderInfo::Explicit,
                ),
                surface_binder(
                    "f",
                    Some(SurfaceExpr::Pi(
                        Span::dummy(),
                        vec![surface_binder(
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
        plain_app(GlobalPath("Sigma.mk"), vec![ident("a"), ident("f")]),
    ));
    // Per-field function binders: obsF : (n : I) → S n → T; stepF : (n : I) → S n → S <idx-expr>
    let fn_ty = |result: SurfaceExpr| {
        SurfaceExpr::Pi(
            Span::dummy(),
            vec![surface_binder(
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
        fn_binders.push(surface_binder(
            affix_name(obs_name, "", "F"),
            Some(fn_ty((*obs_ty).clone())),
            SurfaceBinderInfo::Explicit,
        ));
    }
    for (step_name, idx_expr) in steps {
        fn_binders.push(surface_binder(
            affix_name(step_name, "", "F"),
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
        .map(|(n, _)| ident(affix_name(n, "", "F")))
        .chain(steps.iter().map(|(n, _)| ident(affix_name(n, "", "F"))))
        .collect();
    // stepFn
    let label_pack = mutual_pack(
        &obs.iter()
            .map(|(n, _)| plain_app(affix_name(n, "", "F"), vec![ident("jv"), ident("sv")]))
            .collect::<Vec<_>>(),
    );
    let branch_states: Vec<SurfaceExpr> = steps
        .iter()
        .map(|(n, _)| plain_app(affix_name(n, "", "F"), vec![ident("jv"), ident("sv")]))
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
                surface_binder("jv", None, SurfaceBinderInfo::Explicit),
                surface_binder("sv", None, SurfaceBinderInfo::Explicit),
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
                surface_binder(*idx_name, Some(ity.clone()), SurfaceBinderInfo::Explicit),
                surface_binder(
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
    let mk_step_name = child_name(name, "mkStep2");
    out.push(mk_def(
        mk_step_name.clone(),
        {
            let mut bs = implicit_params.clone();
            bs.extend([
                surface_binder(*idx_name, Some(ity.clone()), SurfaceBinderInfo::Implicit),
                surface_binder(
                    "a",
                    Some(capp(&shape_f, vec![ident(idx_name)])),
                    SurfaceBinderInfo::Explicit,
                ),
                surface_binder(
                    "f",
                    Some(SurfaceExpr::Pi(
                        Span::dummy(),
                        vec![surface_binder(
                            "b",
                            Some(capp(&pos_f, vec![ident(idx_name), ident("a")])),
                            SurfaceBinderInfo::Explicit,
                        )],
                        Box::new(plain_app(GlobalPath("Codata.IMIntl"), {
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
                    GlobalPath("Codata.IMIntl"),
                    vec![
                        capp(&shape_f, vec![]),
                        capp(&pos_f, vec![]),
                        capp(&tgt_f, vec![]),
                    ],
                ),
                ident(idx_name),
            ],
        ),
        plain_app(GlobalPath("Sigma.mk"), vec![ident("a"), ident("f")]),
    ));
    let mut mk_binders = implicit_params.clone();
    mk_binders.push(surface_binder(
        *idx_name,
        Some(ity.clone()),
        SurfaceBinderInfo::Implicit,
    ));
    for (obs_name, obs_ty) in obs.iter() {
        mk_binders.push(surface_binder(
            affix_name(obs_name, "", "V"),
            Some((*obs_ty).clone()),
            SurfaceBinderInfo::Explicit,
        ));
    }
    for (step_name, idx_expr) in steps.iter() {
        mk_binders.push(surface_binder(
            affix_name(step_name, "", "V"),
            Some(self_at(idx_expr[0].clone())),
            SurfaceBinderInfo::Explicit,
        ));
    }
    let mk_label = mutual_pack(
        &obs.iter()
            .map(|(n, _)| ident(affix_name(n, "", "V")))
            .collect::<Vec<_>>(),
    );
    let mk_children: Vec<SurfaceExpr> = steps
        .iter()
        .map(|(n, _)| ident(affix_name(n, "", "V")))
        .collect();
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
                    GlobalPath("Codata.IMIntl"),
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
        child_name(name, "mk"),
        mk_binders.clone(),
        self_at(ident(idx_name)),
        at_app(GlobalPath("Codata.IMmk"), {
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
                .map(|(n, _)| ident(affix_name(n, "", "V")))
                .chain(steps.iter().map(|(n, _)| ident(affix_name(n, "", "V")))),
        );
        at_app(child_name(name, "mk"), args)
    };
    for field_name in obs
        .iter()
        .map(|(n, _)| *n)
        .chain(steps.iter().map(|(n, _)| *n))
    {
        let full = name.append(field_name);
        let mut acc_args = param_exprs.clone();
        acc_args.extend([ident(idx_name), mk_call.clone()]);
        out.push(mk_theorem(
            affix_name(&full, "", "_mk"),
            mk_binders.clone(),
            SurfaceExpr::App(
                Span::dummy(),
                Box::new(ident(GlobalPath("Eq"))),
                vec![
                    SurfaceArg::positional(at_app(&full, acc_args)),
                    SurfaceArg::positional(ident(affix_name(field_name, "", "V"))),
                ],
            ),
            ident(GlobalPath("rfl")),
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
            surface_binder(*idx_name, Some(ity.clone()), SurfaceBinderInfo::Explicit),
            surface_binder(
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
        let full = name.append(obs_name);
        out.push(mk_theorem(
            affix_name(&full, "", "_corec"),
            law_binders(),
            SurfaceExpr::App(
                Span::dummy(),
                Box::new(ident(GlobalPath("Eq"))),
                vec![
                    SurfaceArg::positional(plain_app(
                        &full,
                        vec![corec_call(ident(idx_name), ident("s"))],
                    )),
                    SurfaceArg::positional(plain_app(
                        affix_name(obs_name, "", "F"),
                        vec![ident(idx_name), ident("s")],
                    )),
                ],
            ),
            ident(GlobalPath("rfl")),
        ));
    }
    for (step_name, idx_expr) in steps {
        let full = name.append(step_name);
        out.push(mk_theorem(
            affix_name(&full, "", "_corec"),
            law_binders(),
            SurfaceExpr::App(
                Span::dummy(),
                Box::new(ident(GlobalPath("Eq"))),
                vec![
                    SurfaceArg::positional(plain_app(
                        &full,
                        vec![corec_call(ident(idx_name), ident("s"))],
                    )),
                    SurfaceArg::positional(corec_call(
                        idx_expr[0].clone(),
                        plain_app(
                            affix_name(step_name, "", "F"),
                            vec![ident(idx_name), ident("s")],
                        ),
                    )),
                ],
            ),
            ident(GlobalPath("rfl")),
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
    poly: Option<&SurfaceName>,
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
                    Box::new(ident(GlobalPath("Sum.rec"))),
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
    poly: Option<&SurfaceName>,
) -> SurfaceExpr {
    match cases {
        [only] => only.clone(),
        [first, rest @ ..] => {
            let wrap = |e: SurfaceExpr, d: usize| -> SurfaceExpr {
                let mut w = e;
                for _ in 0..d {
                    w = plain_app(GlobalPath("Sum.inr"), vec![w]);
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
                    Box::new(ident(GlobalPath("Sum.rec"))),
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

fn generate_mutual_n(shapes: &[MutualMember<'_>], poly: Option<&SurfaceName>) -> Vec<SurfaceDecl> {
    let n = shapes.len();
    let names: Vec<&SurfaceName> = shapes.iter().map(|m| m.name).collect();
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
    let state_name = |mi: usize| SurfaceName::component(format!("S{}", mi + 1), false);

    let joint = names
        .iter()
        .skip(1)
        .fold(names[0].clone(), |n, next| n.append(next));
    let shape_f = child_name(&joint, "shapeF");
    let pos_f = child_name(&joint, "posF");
    let tgt_f = child_name(&joint, "tgtF");
    let st_f = child_name(&joint, "stF");
    let mk_step = child_name(&joint, "mkStep");
    let step_fn = child_name(&joint, "step");
    let container = |f: &SurfaceName| plain_app(f, param_exprs.clone());
    let st_container = plain_app(
        &st_f,
        (0..n).map(|i| ident(state_name(i))).collect::<Vec<_>>(),
    );
    let state_binders: Vec<SurfaceBinder> = (0..n)
        .map(|i| {
            surface_binder(
                state_name(i),
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
                            surface_binder("_", None, SurfaceBinderInfo::Explicit),
                            surface_binder("_", None, SurfaceBinderInfo::Explicit),
                        ],
                        Box::new(targets[0].clone()),
                    )
                } else {
                    SurfaceExpr::Lambda(
                        Span::dummy(),
                        vec![
                            surface_binder("_", None, SurfaceBinderInfo::Explicit),
                            surface_binder("pb", None, SurfaceBinderInfo::Explicit),
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
            m.name.clone(),
            explicit_binders.clone(),
            type_u(poly),
            at_app(
                GlobalPath("Codata.IMIntl"),
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
                GlobalPath("Codata.IMhead"),
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
                m.name.append(obs_name),
                {
                    let mut bs = implicit_binders.clone();
                    bs.push(surface_binder(
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
                m.name.append(step_name),
                {
                    let mut bs = implicit_binders.clone();
                    bs.push(surface_binder(
                        "x",
                        Some(self_ty.clone()),
                        SurfaceBinderInfo::Explicit,
                    ));
                    bs
                },
                plain_app(names[*tgt_mi], param_exprs.clone()),
                at_app(
                    GlobalPath("Codata.IMchild"),
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
                surface_binder(
                    state_name(i),
                    Some(type_u(poly)),
                    SurfaceBinderInfo::Explicit,
                )
            })
            .collect(),
        arrow(tag_ty.clone(), type_u(poly)),
        lam1(
            "tg",
            tag_tower_p(
                &(0..n).map(|i| ident(state_name(i))).collect::<Vec<_>>(),
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
                surface_binder("tg", Some(tag_ty.clone()), SurfaceBinderInfo::Explicit),
                surface_binder(
                    "a",
                    Some({
                        let mut args = param_exprs.clone();
                        args.push(ident("tg"));
                        plain_app(&shape_f, args)
                    }),
                    SurfaceBinderInfo::Explicit,
                ),
                surface_binder(
                    "f",
                    Some(SurfaceExpr::Pi(
                        Span::dummy(),
                        vec![surface_binder(
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
        plain_app(GlobalPath("Sigma.mk"), vec![ident("a"), ident("f")]),
    ));

    // Per-field function binders across all members, in member order.
    let mut fn_binders: Vec<SurfaceBinder> = Vec::new();
    for (mi, m) in shapes.iter().enumerate() {
        let s_own = state_name(mi);
        for (obs_name, obs_ty) in &m.obs {
            fn_binders.push(surface_binder(
                affix_name(&pair_name(m.name, "_", obs_name), "", "F"),
                Some(arrow(ident(&s_own), (*obs_ty).clone())),
                SurfaceBinderInfo::Explicit,
            ));
        }
        for (step_name, tgt_mi) in &m.steps {
            fn_binders.push(surface_binder(
                affix_name(&pair_name(m.name, "_", step_name), "", "F"),
                Some(arrow(ident(&s_own), ident(state_name(*tgt_mi)))),
                SurfaceBinderInfo::Explicit,
            ));
        }
    }
    let all_fn_idents: Vec<SurfaceExpr> = shapes
        .iter()
        .flat_map(|m| {
            m.obs
                .iter()
                .map(|(o, _)| ident(affix_name(&pair_name(m.name, "_", o), "", "F")))
                .chain(
                    m.steps
                        .iter()
                        .map(|(st, _)| ident(affix_name(&pair_name(m.name, "_", st), "", "F"))),
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
                        .map(|(o, _)| {
                            plain_app(
                                affix_name(&pair_name(m.name, "_", o), "", "F"),
                                vec![ident("sv")],
                            )
                        })
                        .collect::<Vec<_>>(),
                );
                let branch_states: Vec<SurfaceExpr> = m
                    .steps
                    .iter()
                    .map(|(st, _)| {
                        plain_app(
                            affix_name(&pair_name(m.name, "_", st), "", "F"),
                            vec![ident("sv")],
                        )
                    })
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
                mk_args.extend((0..n).map(|i| ident(state_name(i))));
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
        let corec_name = child_name(m.name, "corec");
        let step_call = {
            let mut args = param_exprs.clone();
            args.extend((0..n).map(|i| ident(state_name(i))));
            args.extend(all_fn_idents.clone());
            at_app(&step_fn, args)
        };
        out.push(mk_def(
            corec_name,
            {
                let mut bs = implicit_binders.clone();
                bs.extend(state_binders.clone());
                bs.extend(fn_binders.clone());
                bs.push(surface_binder(
                    "s",
                    Some(ident(state_name(mi))),
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
        let mk_step_name = child_name(m.name, "mkStep2");
        out.push(mk_def(
            mk_step_name.clone(),
            {
                let mut bs = implicit_binders.clone();
                bs.extend([
                    surface_binder(
                        "a",
                        Some({
                            let mut args = param_exprs.clone();
                            args.push(tag(mi));
                            plain_app(&shape_f, args)
                        }),
                        SurfaceBinderInfo::Explicit,
                    ),
                    surface_binder(
                        "f",
                        Some(SurfaceExpr::Pi(
                            Span::dummy(),
                            vec![surface_binder(
                                "b",
                                Some({
                                    let mut args = param_exprs.clone();
                                    args.extend([tag(mi), ident("a")]);
                                    plain_app(&pos_f, args)
                                }),
                                SurfaceBinderInfo::Explicit,
                            )],
                            Box::new(plain_app(
                                GlobalPath("Codata.IMIntl"),
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
                        GlobalPath("Codata.IMIntl"),
                        vec![container(&shape_f), container(&pos_f), container(&tgt_f)],
                    ),
                    tag(mi),
                ],
            ),
            plain_app(GlobalPath("Sigma.mk"), vec![ident("a"), ident("f")]),
        ));
        let mut mk_binders = implicit_binders.clone();
        for (obs_name, obs_ty) in m.obs.iter() {
            mk_binders.push(surface_binder(
                affix_name(obs_name, "", "V"),
                Some((*obs_ty).clone()),
                SurfaceBinderInfo::Explicit,
            ));
        }
        for (step_name, tgt_mi) in m.steps.iter() {
            mk_binders.push(surface_binder(
                affix_name(step_name, "", "V"),
                Some(plain_app(names[*tgt_mi], param_exprs.clone())),
                SurfaceBinderInfo::Explicit,
            ));
        }
        let mk_label = mutual_pack(
            &m.obs
                .iter()
                .map(|(n, _)| ident(affix_name(n, "", "V")))
                .collect::<Vec<_>>(),
        );
        let mk_children: Vec<SurfaceExpr> = m
            .steps
            .iter()
            .map(|(n, _)| ident(affix_name(n, "", "V")))
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
                        GlobalPath("Codata.IMIntl"),
                        vec![container(&shape_f), container(&pos_f), container(&tgt_f)],
                    ),
                    &tgt_full,
                    ident("b"),
                    poly,
                ),
            )
        };
        out.push(mk_def(
            child_name(m.name, "mk"),
            mk_binders.clone(),
            self_ty.clone(),
            at_app(GlobalPath("Codata.IMmk"), {
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
                    .map(|(n, _)| ident(affix_name(n, "", "V")))
                    .chain(m.steps.iter().map(|(n, _)| ident(affix_name(n, "", "V")))),
            );
            at_app(child_name(m.name, "mk"), args)
        };
        for field_name in m
            .obs
            .iter()
            .map(|(n, _)| *n)
            .chain(m.steps.iter().map(|(n, _)| *n))
        {
            let full = m.name.append(field_name);
            let mut acc_args = param_exprs.clone();
            acc_args.push(mk_call.clone());
            out.push(mk_theorem(
                affix_name(&full, "", "_mk"),
                mk_binders.clone(),
                SurfaceExpr::App(
                    Span::dummy(),
                    Box::new(ident(GlobalPath("Eq"))),
                    vec![
                        SurfaceArg::positional(at_app(&full, acc_args)),
                        SurfaceArg::positional(ident(affix_name(field_name, "", "V"))),
                    ],
                ),
                ident(GlobalPath("rfl")),
            ));
        }
    }

    for (mi, m) in shapes.iter().enumerate() {
        let corec_call = |member: usize, extra: SurfaceExpr| {
            let mut args = param_exprs.clone();
            args.extend((0..n).map(|i| ident(state_name(i))));
            args.extend(all_fn_idents.clone());
            args.push(extra);
            at_app(child_name(names[member], "corec"), args)
        };
        let law_binders = || {
            let mut bs = implicit_binders.clone();
            bs.extend(state_binders.clone());
            bs.extend(fn_binders.clone());
            bs.push(surface_binder(
                "s",
                Some(ident(state_name(mi))),
                SurfaceBinderInfo::Explicit,
            ));
            bs
        };
        for (obs_name, _) in &m.obs {
            let full = m.name.append(obs_name);
            let mut acc_args = param_exprs.clone();
            acc_args.push(corec_call(mi, ident("s")));
            out.push(mk_theorem(
                affix_name(&full, "", "_corec"),
                law_binders(),
                SurfaceExpr::App(
                    Span::dummy(),
                    Box::new(ident(GlobalPath("Eq"))),
                    vec![
                        SurfaceArg::positional(at_app(&full, acc_args)),
                        SurfaceArg::positional(plain_app(
                            affix_name(&pair_name(m.name, "_", obs_name), "", "F"),
                            vec![ident("s")],
                        )),
                    ],
                ),
                ident(GlobalPath("rfl")),
            ));
        }
        for (step_name, tgt_mi) in &m.steps {
            let full = m.name.append(step_name);
            let mut acc_args = param_exprs.clone();
            acc_args.push(corec_call(mi, ident("s")));
            out.push(mk_theorem(
                affix_name(&full, "", "_corec"),
                law_binders(),
                SurfaceExpr::App(
                    Span::dummy(),
                    Box::new(ident(GlobalPath("Eq"))),
                    vec![
                        SurfaceArg::positional(at_app(&full, acc_args)),
                        SurfaceArg::positional(corec_call(
                            *tgt_mi,
                            plain_app(
                                affix_name(&pair_name(m.name, "_", step_name), "", "F"),
                                vec![ident("s")],
                            ),
                        )),
                    ],
                ),
                ident(GlobalPath("rfl")),
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
        name: &'a SurfaceName,
        binders: &'a [SurfaceBinder],
        ty: &'a SurfaceExpr,
        head: SurfaceName,
        clauses: &'a [(SurfaceName, SurfaceExpr)],
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
        let head = {
            let mut t = strip_parens(ty);
            if let SurfaceExpr::App(_, h, a) = t {
                for arg in a {
                    if arg.name.is_some() {
                        return Err(unsupported(format!(
                            "mutual codef `{name}`: named arguments in the \
                             result type are not supported"
                        )));
                    }
                }
                t = strip_parens(h);
            }
            let SurfaceExpr::Ident(_, c) = t else {
                return Err(unsupported(format!(
                    "mutual codef `{name}`: the result type must be a codata \
                     member (a constant, possibly applied to parameters)"
                )));
            };
            c.clone()
        };
        bits.push(CodefBits {
            name,
            binders,
            ty,
            head,
            clauses,
        });
    }
    let fn_names: Vec<&SurfaceName> = bits.iter().map(|b| b.name).collect();

    // All members must target the same mutual block: their corecs share
    // one recorded slot list. Use member 0's corec as the authority.
    let corec0 = child_name(&bits[0].head, "corec");
    let corec0_const = corec0.name().clone();
    let param_names = env
        .get_typed_param_names(&corec0_const)
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
    if param_names.len() != param_infos.len() {
        return Err(unsupported(
            "mutual codef: parameter names and binder kinds disagree",
        ));
    }
    let mut slots: Vec<SurfaceName> = param_names
        .iter()
        .zip(param_infos.iter())
        .filter(|(_, i)| matches!(i, clean_kernel::BinderInfo::Default))
        .map(|(n, _)| SurfaceName::from_name(n.clone()))
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
        // Recreate the generated protocol from every authored exact pair.
        // Display splitting cannot identify qualified/quoted member or field names.
        let mut matches = bits.iter().flat_map(|cb| {
            cb.clauses.iter().filter_map(move |(field, value)| {
                (affix_name(&pair_name(&cb.head, "_", field), "", "F") == *slot)
                    .then_some((cb, field, value))
            })
        });
        let Some((cb, field, value)) = matches.next() else {
            // Preserve the established ordinary-label refusal after the exact
            // structural search has already failed. This legacy slot spelling
            // is diagnostic only: splitting it never selects a clause or
            // authorizes a successful generated corecursor application.
            if let Some(base) = strip_slot_suffix(slot) {
                if let Some(text) = base.component_text() {
                    if let Some((member, field)) = text.split_once('_') {
                        if !member.is_empty()
                            && !field.is_empty()
                            && !bits.iter().any(|b| b.head.component_text() == Some(member))
                        {
                            return Err(unsupported(format!(
                                "mutual codef: no codef in the block targets `{member}` \
                                 (needed for its `{field}` clause; unmatched exact slot `{slot}`)"
                            )));
                        }
                    }
                }
            }
            return Err(unsupported(format!(
                "mutual codef: no exact clause for slot `{slot}`"
            )));
        };
        if matches.next().is_some() {
            return Err(unsupported(format!(
                "mutual codef: ambiguous exact slot `{slot}`"
            )));
        }
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
        let state_name = cb
            .binders
            .first()
            .map_or_else(|| SurfaceName::generated_path("_"), |b| b.name.clone());
        slot_lambdas.push(SurfaceExpr::Lambda(
            Span::dummy(),
            vec![surface_binder(
                &state_name,
                cb.binders.first().and_then(|b| b.ty.as_deref().cloned()),
                SurfaceBinderInfo::Explicit,
            )],
            Box::new(body),
        ));
    }

    // One generated def per codef, all sharing the slot lambdas.
    let mut candidate = env.clone();
    let mut declared = Vec::new();
    for cb in &bits {
        let state_ty = cb
            .binders
            .first()
            .and_then(|b| b.ty.as_deref().cloned())
            .unwrap_or_else(punit_ty);
        let init_state = cb
            .binders
            .first()
            .map_or_else(|| ident(GlobalPath("PUnit.unit")), |b| ident(&b.name));
        // The 2-member corec takes {S1 S2}; n-member {S1..Sn} — all
        // implicit, inferred from the state lambdas' ascribed types and
        // the init state. Pass the member's OWN state type positionally is
        // not possible (implicit), so rely on inference via the explicit
        // fn lambdas — their binder ascriptions pin each S_i.
        let _ = state_ty;
        // The written result type fixes the codata parameters. They are
        // implicit in corec, so ordinary application starts at the slot lambdas.
        let mut corec_args = slot_lambdas.clone();
        corec_args.push(init_state);
        let generated = mk_def(
            cb.name.clone(),
            cb.binders.to_vec(),
            cb.ty.clone(),
            plain_app(child_name(&cb.head, "corec"), corec_args),
        );
        let registered =
            crate::elaborate_decl_and_register(&mut candidate, &generated).map_err(|e| {
                unsupported(format!(
                    "mutual codef `{}`: the generated corecursor application \
                 failed to elaborate/kernel-check (env left untouched): {e:?}",
                    cb.name
                ))
            })?;
        declared.push(registered);
    }
    *env = candidate;
    Ok(generated_declarations(declared))
}

/// If `expr` is exactly `<one of fnames> <one-arg>` (or a bare name for
/// zero-state members), return the new-state expression.
fn mutual_self_call_arg(expr: &SurfaceExpr, fnames: &[&SurfaceName]) -> Option<SurfaceExpr> {
    match strip_parens(expr) {
        SurfaceExpr::Ident(_, id) if fnames.contains(&id) => Some(ident(GlobalPath("PUnit.unit"))),
        SurfaceExpr::App(_, h, args) => {
            let SurfaceExpr::Ident(_, id) = strip_parens(h) else {
                return None;
            };
            if !fnames.contains(&id) || args.len() != 1 || args[0].name.is_some() {
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
        .reduce(|acc, t| plain_app(GlobalPath("PProd"), vec![t, acc]))
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
                    surface_binder(
                        &b.name,
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

    let shape_f = child_name(name, "shapeF");
    let pos_f = child_name(name, "posF");
    let tgt_f = child_name(name, "tgtF");
    let mk_step = child_name(name, "mkStep");
    let step_fn = child_name(name, "stepFn");
    let corec = child_name(name, "corec");
    let m = steps.len();
    let k_obs = obs.len();
    let capp = |f: &SurfaceName, extra: Vec<SurfaceExpr>| -> SurfaceExpr {
        let mut args = param_exprs.clone();
        args.extend(extra);
        plain_app(f, args)
    };

    let label_ty = obs
        .iter()
        .rev()
        .map(|(_, t)| (*t).clone())
        .reduce(|acc, t| plain_app(GlobalPath("PProd"), vec![t, acc]))
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
                surface_binder("_", None, SurfaceBinderInfo::Explicit),
                surface_binder("_", None, SurfaceBinderInfo::Explicit),
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
                surface_binder("ip", None, SurfaceBinderInfo::Explicit),
                surface_binder("_", None, SurfaceBinderInfo::Explicit),
                surface_binder("_", None, SurfaceBinderInfo::Explicit),
            ],
            Box::new(idx_targets[0].clone()),
        )
    } else {
        SurfaceExpr::Lambda(
            Span::dummy(),
            vec![
                surface_binder("ip", None, SurfaceBinderInfo::Explicit),
                surface_binder("_", None, SurfaceBinderInfo::Explicit),
                surface_binder("pb", None, SurfaceBinderInfo::Explicit),
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
        (*name).clone(),
        {
            let mut bs = explicit_params.clone();
            bs.extend(idx_binders.iter().cloned());
            bs
        },
        type_u(poly),
        at_app(
            GlobalPath("Codata.IMIntl"),
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
            GlobalPath("Codata.IMhead"),
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
            name.append(obs_name),
            {
                let mut bs = implicit_params.clone();
                bs.extend(implicit_idx.iter().cloned());
                bs.push(surface_binder(
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
            name.append(step_name),
            {
                let mut bs = implicit_params.clone();
                bs.extend(implicit_idx.iter().cloned());
                bs.push(surface_binder(
                    "x",
                    Some(self_unpacked()),
                    SurfaceBinderInfo::Explicit,
                ));
                bs
            },
            plain_app(name, res_args),
            at_app(
                GlobalPath("Codata.IMchild"),
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
    let s_binder = surface_binder(
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
                surface_binder("ip", Some(packed_ty.clone()), SurfaceBinderInfo::Explicit),
                surface_binder(
                    "a",
                    Some(capp(&shape_f, vec![ident("ip")])),
                    SurfaceBinderInfo::Explicit,
                ),
                surface_binder(
                    "f",
                    Some(SurfaceExpr::Pi(
                        Span::dummy(),
                        vec![surface_binder(
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
        plain_app(GlobalPath("Sigma.mk"), vec![ident("a"), ident("f")]),
    ));
    // Per-field function binders over the packed index.
    let fn_ty = |result: SurfaceExpr| {
        SurfaceExpr::Pi(
            Span::dummy(),
            vec![surface_binder(
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
        fn_binders.push(surface_binder(
            affix_name(obs_name, "", "F"),
            Some(fn_ty(wrap((*obs_ty).clone()))),
            SurfaceBinderInfo::Explicit,
        ));
    }
    for ((step_name, _), wrapped_tgt) in steps.iter().zip(&idx_targets) {
        fn_binders.push(surface_binder(
            affix_name(step_name, "", "F"),
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
        .map(|(n, _)| ident(affix_name(n, "", "F")))
        .chain(steps.iter().map(|(n, _)| ident(affix_name(n, "", "F"))))
        .collect();
    // stepFn
    let label_pack = mutual_pack(
        &obs.iter()
            .map(|(n, _)| plain_app(affix_name(n, "", "F"), vec![ident("jp"), ident("sv")]))
            .collect::<Vec<_>>(),
    );
    let branch_states: Vec<SurfaceExpr> = steps
        .iter()
        .map(|(n, _)| plain_app(affix_name(n, "", "F"), vec![ident("jp"), ident("sv")]))
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
                surface_binder("jp", None, SurfaceBinderInfo::Explicit),
                surface_binder("sv", None, SurfaceBinderInfo::Explicit),
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
            bs.push(surface_binder(
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
    let mk_step_name = child_name(name, "mkStep2");
    out.push(mk_def(
        mk_step_name.clone(),
        {
            let mut bs = implicit_params.clone();
            bs.extend(implicit_idx.iter().cloned());
            bs.extend([
                surface_binder(
                    "a",
                    Some(capp(&shape_f, vec![pack_idents()])),
                    SurfaceBinderInfo::Explicit,
                ),
                surface_binder(
                    "f",
                    Some(SurfaceExpr::Pi(
                        Span::dummy(),
                        vec![surface_binder(
                            "b",
                            Some(capp(&pos_f, vec![pack_idents(), ident("a")])),
                            SurfaceBinderInfo::Explicit,
                        )],
                        Box::new(plain_app(
                            GlobalPath("Codata.IMIntl"),
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
                    GlobalPath("Codata.IMIntl"),
                    vec![
                        capp(&shape_f, vec![]),
                        capp(&pos_f, vec![]),
                        capp(&tgt_f, vec![]),
                    ],
                ),
                pack_idents(),
            ],
        ),
        plain_app(GlobalPath("Sigma.mk"), vec![ident("a"), ident("f")]),
    ));
    let mut mk_binders = implicit_params.clone();
    mk_binders.extend(implicit_idx.iter().cloned());
    for (obs_name, obs_ty) in obs.iter() {
        mk_binders.push(surface_binder(
            affix_name(obs_name, "", "V"),
            Some((*obs_ty).clone()),
            SurfaceBinderInfo::Explicit,
        ));
    }
    for (step_name, exprs) in steps.iter() {
        let mut res_args = param_exprs.clone();
        res_args.extend(exprs.iter().map(|e| (*e).clone()));
        mk_binders.push(surface_binder(
            affix_name(step_name, "", "V"),
            Some(plain_app(name, res_args)),
            SurfaceBinderInfo::Explicit,
        ));
    }
    let mk_label = mutual_pack(
        &obs.iter()
            .map(|(n, _)| ident(affix_name(n, "", "V")))
            .collect::<Vec<_>>(),
    );
    let mk_children: Vec<SurfaceExpr> = steps
        .iter()
        .map(|(n, _)| ident(affix_name(n, "", "V")))
        .collect();
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
                    GlobalPath("Codata.IMIntl"),
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
        child_name(name, "mk"),
        mk_binders.clone(),
        self_unpacked(),
        at_app(GlobalPath("Codata.IMmk"), {
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
                .map(|(n, _)| ident(affix_name(n, "", "V")))
                .chain(steps.iter().map(|(n, _)| ident(affix_name(n, "", "V")))),
        );
        at_app(child_name(name, "mk"), args)
    };
    for field_name in obs
        .iter()
        .map(|(n, _)| *n)
        .chain(steps.iter().map(|(n, _)| *n))
    {
        let full = name.append(field_name);
        let mut acc_args = param_exprs.clone();
        acc_args.extend(idx_binders.iter().map(|b| ident(&b.name)));
        acc_args.push(mk_call.clone());
        out.push(mk_theorem(
            affix_name(&full, "", "_mk"),
            mk_binders.clone(),
            SurfaceExpr::App(
                Span::dummy(),
                Box::new(ident(GlobalPath("Eq"))),
                vec![
                    SurfaceArg::positional(at_app(&full, acc_args)),
                    SurfaceArg::positional(ident(affix_name(field_name, "", "V"))),
                ],
            ),
            ident(GlobalPath("rfl")),
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
        bs.push(surface_binder(
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
        let full = name.append(obs_name);
        out.push(mk_theorem(
            affix_name(&full, "", "_corec"),
            law_binders(),
            SurfaceExpr::App(
                Span::dummy(),
                Box::new(ident(GlobalPath("Eq"))),
                vec![
                    SurfaceArg::positional(plain_app(
                        &full,
                        vec![mk_corec_call(own_idx.clone(), ident("s"))],
                    )),
                    SurfaceArg::positional(plain_app(
                        affix_name(obs_name, "", "F"),
                        vec![pack_idents(), ident("s")],
                    )),
                ],
            ),
            ident(GlobalPath("rfl")),
        ));
    }
    for (step_name, exprs) in steps {
        let full = name.append(step_name);
        out.push(mk_theorem(
            affix_name(&full, "", "_corec"),
            law_binders(),
            SurfaceExpr::App(
                Span::dummy(),
                Box::new(ident(GlobalPath("Eq"))),
                vec![
                    SurfaceArg::positional(plain_app(
                        &full,
                        vec![mk_corec_call(own_idx.clone(), ident("s"))],
                    )),
                    SurfaceArg::positional(mk_corec_call(
                        exprs.iter().map(|e| (*e).clone()).collect(),
                        plain_app(
                            affix_name(step_name, "", "F"),
                            vec![pack_idents(), ident("s")],
                        ),
                    )),
                ],
            ),
            ident(GlobalPath("rfl")),
        ));
    }

    out.into_iter().map(|d| set_uparams(d, poly)).collect()
}

/// Right-nested `PProd.mk` chain (single value passes through).
fn mutual_pack_pprod(vals: &[SurfaceExpr]) -> SurfaceExpr {
    match vals {
        [] => ident(GlobalPath("PUnit.unit")),
        [only] => only.clone(),
        [first, rest @ ..] => plain_app(
            GlobalPath("PProd.mk"),
            vec![first.clone(), mutual_pack_pprod(rest)],
        ),
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
    name: &SurfaceName,
    binders: &[SurfaceBinder],
    ty: &SurfaceExpr,
    clauses: &[(SurfaceName, SurfaceExpr)],
    slots: &[SurfaceName],
    head_name: &SurfaceName,
    type_args: &[SurfaceExpr],
    state: Option<&SurfaceBinder>,
) -> Result<Option<SurfaceDecl>, ElabError> {
    let mk_name = child_name(head_name, "mk");
    fn is_mk_app_impl<'e>(
        e: &'e SurfaceExpr,
        mk_name: &SurfaceName,
        head_name: &SurfaceName,
    ) -> Option<&'e [SurfaceArg]> {
        let SurfaceExpr::App(_, h, args) = strip_parens(e) else {
            return None;
        };
        let is_mk = match strip_parens(h) {
            SurfaceExpr::Ident(_, id) => id == mk_name,
            SurfaceExpr::Proj(_, base, Projection::Named(field)) => {
                field == &SurfaceName::generated_path("mk")
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

    let state_name = state.map_or_else(|| SurfaceName::generated_path("_"), |b| b.name.clone());
    let state_ty = state
        .and_then(|b| b.ty.as_deref().cloned())
        .unwrap_or_else(punit_ty);
    // Buffered state: a Nat flag (0 = the outer node, k = the k-th guard
    // layer) paired with the user's state.
    let buffered_ty = plain_app(
        GlobalPath("PProd"),
        vec![ident(GlobalPath("Nat")), state_ty.clone()],
    );
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
                vec![surface_binder(
                    &state_name,
                    Some(state_ty.clone()),
                    SurfaceBinderInfo::Explicit,
                )],
                Box::new(e),
            )),
            vec![SurfaceArg::positional(plain_app(
                GlobalPath("PProd.snd"),
                vec![ident("p")],
            ))],
        )
    };
    let flag = plain_app(GlobalPath("PProd.fst"), vec![ident("p")]);
    let payload = plain_app(GlobalPath("PProd.snd"), vec![ident("p")]);
    let plam = |body: SurfaceExpr| -> SurfaceExpr {
        SurfaceExpr::Lambda(
            Span::dummy(),
            vec![surface_binder(
                "p",
                Some(buffered_ty.clone()),
                SurfaceBinderInfo::Explicit,
            )],
            Box::new(body),
        )
    };
    let beq_flag = |k: usize| -> SurfaceExpr {
        plain_app(GlobalPath("Nat.beq"), vec![flag.clone(), nat_lit(k)])
    };
    // cond chain: flag 0 -> outer, flag k -> layer k (the last layer is
    // the chain's final else branch).
    let cond_chain = |outer: SurfaceExpr, layer_vals: Vec<SurfaceExpr>| -> SurfaceExpr {
        let mut chain = layer_vals
            .last()
            .cloned()
            .expect("depth >= 1: at least one layer");
        for (k, v) in layer_vals.iter().enumerate().rev().skip(1) {
            chain = plain_app(GlobalPath("cond"), vec![beq_flag(k + 1), v.clone(), chain]);
        }
        plain_app(GlobalPath("cond"), vec![beq_flag(0), outer, chain])
    };
    let mut slot_lambdas: Vec<SurfaceExpr> = Vec::new();
    for (si, slot) in slots.iter().enumerate() {
        let field = strip_slot_suffix(slot).ok_or_else(|| unsupported(
            format!("codef: unsupported corecursor slot `{slot}` (expected a nonempty terminal string with F suffix)")
        ))?;
        if si == obs_count {
            // The recursive slot: at the last layer wrap back to flag 0
            // with the (re-bound) next state; otherwise advance the flag.
            slot_lambdas.push(plam(plain_app(
                GlobalPath("cond"),
                vec![
                    beq_flag(depth),
                    plain_app(
                        GlobalPath("PProd.mk"),
                        vec![nat_lit(0), rebind(next_state.clone())],
                    ),
                    plain_app(
                        GlobalPath("PProd.mk"),
                        vec![
                            plain_app(GlobalPath("Nat.succ"), vec![flag.clone()]),
                            payload.clone(),
                        ],
                    ),
                ],
            )));
        } else {
            let Some((_, outer)) = clauses.iter().find(|(n, _)| n == &field) else {
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
        GlobalPath("PProd.mk"),
        vec![
            nat_lit(0),
            state.map_or_else(|| ident(GlobalPath("PUnit.unit")), |b| ident(&b.name)),
        ],
    );
    let mut corec_args = type_args.to_vec();
    corec_args.push(buffered_ty);
    corec_args.extend(slot_lambdas);
    corec_args.push(init);
    Ok(Some(mk_def(
        name.clone(),
        binders.to_vec(),
        ty.clone(),
        at_app(child_name(head_name, "corec"), corec_args),
    )))
}
