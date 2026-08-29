// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The variant-codata PLAN — brick VC-2 of
//! `designs/2026-08-28-variant-codata-surface.md`.
//!
//! [`crate::codata_variant`] decides what is ALLOWED; this module decides
//! what it BECOMES. Given the classified telescope of one constructor it
//! resolves everything the generator needs and consults nothing: no
//! environment, no name lookup, no elaboration. `Pₖ`, `Qₖ` in both the
//! constructor's scope and `posF`'s, the projection path of every payload,
//! the binder name of every argument, and the generator's own internal
//! binder names.
//!
//! The load-bearing piece is [`subst_idents`]. A child domain like `Ans e`
//! is written in the CONSTRUCTOR's scope, where `e` is a binder; inside
//! `posF` that binder does not exist, and the only thing in scope is the
//! shape value. Every payload reference therefore has to become a
//! projection of the shape, and a reference that survives the rewrite is
//! refused rather than emitted — a free `e` there would either fail to
//! elaborate or silently capture a parameter of the same name and mint a
//! well-typed, wrong carrier.

use crate::codata_cmd::{ident, mentions, plain_app, punit_ty};
use crate::codata_variant::{unsupported, CtorArg};
use crate::ElabError;
use clean_parser::{LevelExpr, Projection, Span, SurfaceArg, SurfaceBinder, SurfaceExpr};

/// A non-recursive constructor argument, resolved.
#[derive(Debug)]
pub(crate) struct PayloadPlan<'a> {
    /// The binder name the generated constructor uses. Source binder name
    /// when the clause named it; a fresh `a<i>` for arrow-style arguments.
    pub(crate) arg_name: String,
    /// A SECOND binder name for the same argument, used where the generated
    /// declaration mentions the constructor TWICE — `T.Cⱼ x = T.Cₖ y → False`
    /// and `T.Cₖ x = T.Cₖ y → x = y` (VC-5). Fresh against the parameters,
    /// this constructor's own names, and every EARLIER constructor's names,
    /// so the two telescopes of such a statement can never shadow each other.
    /// Without it, `T.Ret_inj` for `| Ret : (r : R) → T` would bind `r`
    /// twice, the second shadowing the first, and the theorem would degrade
    /// to the vacuous `r = r`.
    pub(crate) alt_name: String,
    /// The argument's type — one factor of `Pₖ`.
    pub(crate) ty: &'a SurfaceExpr,
    /// How this payload is recovered from the bound SHAPE value inside
    /// `posF`: `s`, `s.1`, `s.2.1`, … (the identity when the constructor
    /// has exactly one payload, since `Pₖ` is then the bare type).
    pub(crate) projection: SurfaceExpr,
}

/// The domain of a `D → T p⃗` child argument, in both scopes it is needed.
#[derive(Debug)]
pub(crate) struct FamilyPlan<'a> {
    /// `D` as written — valid in the CONSTRUCTOR's scope, where the payload
    /// binders are in scope by name.
    pub(crate) source: &'a SurfaceExpr,
    /// `D` with every payload reference rewritten to its projection out of
    /// the bound shape — valid in `posF`'s branch, where the only thing in
    /// scope is the shape value. THE load-bearing field of this brick: if
    /// this were `source` unchanged, the payload name would be free and the
    /// lowering silently wrong (or accidentally captured by a parameter of
    /// the same name).
    pub(crate) in_shape: SurfaceExpr,
    /// `D` with every payload reference rewritten to that payload's
    /// [`PayloadPlan::alt_name`] — the domain as it must be spelled on the
    /// SECOND telescope of a two-sided statement (`T.Vis e k = T.Vis e' k'`
    /// needs `k' : Ans e' → T`, not `Ans e → T`).
    pub(crate) in_alt: SurfaceExpr,
}

/// A recursive constructor argument, resolved.
#[derive(Debug)]
pub(crate) struct ChildPlan<'a> {
    pub(crate) arg_name: String,
    /// The second binder name — see [`PayloadPlan::alt_name`].
    pub(crate) alt_name: String,
    /// `None` for a bare `T p⃗` child (position `PUnit.{1}`).
    pub(crate) family: Option<FamilyPlan<'a>>,
}

impl ChildPlan<'_> {
    /// This child's position type in the CONSTRUCTOR's scope.
    pub(crate) fn domain_in_args(&self) -> SurfaceExpr {
        match &self.family {
            Some(f) => f.source.clone(),
            None => punit_ty(),
        }
    }

    /// This child's position type in `posF`'s scope (payload references
    /// rewritten to projections of the bound shape).
    pub(crate) fn domain_in_shape(&self) -> SurfaceExpr {
        match &self.family {
            Some(f) => f.in_shape.clone(),
            None => punit_ty(),
        }
    }
}

/// One constructor argument in SOURCE order — the generated constructor's
/// binder list is exactly this sequence.
#[derive(Debug)]
pub(crate) enum ArgPlan<'a> {
    Payload(PayloadPlan<'a>),
    Child(ChildPlan<'a>),
}

impl<'a> ArgPlan<'a> {
    pub(crate) fn arg_name(&self) -> &str {
        match self {
            ArgPlan::Payload(p) => &p.arg_name,
            ArgPlan::Child(c) => &c.arg_name,
        }
    }

    /// The second binder name — see [`PayloadPlan::alt_name`].
    pub(crate) fn alt_name(&self) -> &str {
        match self {
            ArgPlan::Payload(p) => &p.alt_name,
            ArgPlan::Child(c) => &c.alt_name,
        }
    }

    /// Both names this argument can be bound under.
    fn both_names(&self) -> [&str; 2] {
        [self.arg_name(), self.alt_name()]
    }
}

/// A validated + fully resolved variant constructor: everything the
/// generator needs, with no environment consulted and no name looked up.
#[derive(Debug)]
pub(crate) struct VariantCtorPlan<'a> {
    pub(crate) name: &'a str,
    /// Arguments in source order.
    pub(crate) args: Vec<ArgPlan<'a>>,
    /// `Pₖ` — right-nested `PProd` of the payload types, `PUnit.{1}` when
    /// the constructor has no payload.
    pub(crate) payload_ty: SurfaceExpr,
    /// `Qₖ` in `posF`'s scope — right-nested `Sum` of the child domains
    /// (`PUnit.{1}` per bare child), `PEmpty.{1}` when there are none.
    pub(crate) pos_ty_in_shape: SurfaceExpr,
    /// The same `Qₖ`, spelled in the CONSTRUCTOR's scope (payload binders
    /// by name rather than projections) — what the constructor body's
    /// `Sum.rec` motives and the child laws are stated against.
    pub(crate) pos_ty_in_args: SurfaceExpr,
    /// The binder `posF`'s branch for this constructor binds the shape
    /// value to. Fresh against the parameters, this constructor's argument
    /// names, and every identifier occurring in its child domains, so a
    /// projection can never capture.
    pub(crate) shape_var: String,
}

impl<'a> VariantCtorPlan<'a> {
    pub(crate) fn payloads(&self) -> impl Iterator<Item = &PayloadPlan<'a>> {
        self.args.iter().filter_map(|a| match a {
            ArgPlan::Payload(p) => Some(p),
            ArgPlan::Child(_) => None,
        })
    }

    pub(crate) fn children(&self) -> impl Iterator<Item = &ChildPlan<'a>> {
        self.args.iter().filter_map(|a| match a {
            ArgPlan::Child(c) => Some(c),
            ArgPlan::Payload(_) => None,
        })
    }

    /// Does this constructor have at least one recursive position?
    pub(crate) fn has_child(&self) -> bool {
        self.children().next().is_some()
    }

    /// The `Pₖ` VALUE built from this constructor's own payload binders —
    /// `PUnit.unit`, the single payload, or the right-nested `PProd.mk`.
    pub(crate) fn payload_value(&self) -> SurfaceExpr {
        pack_pprod(
            self.payloads()
                .map(|p| ident(&p.arg_name))
                .collect::<Vec<_>>(),
        )
    }

    /// The same `Pₖ` value under the ALTERNATE naming.
    pub(crate) fn alt_payload_value(&self) -> SurfaceExpr {
        pack_pprod(
            self.payloads()
                .map(|p| ident(&p.alt_name))
                .collect::<Vec<_>>(),
        )
    }

    /// How many non-recursive arguments this constructor has.
    pub(crate) fn payload_count(&self) -> usize {
        self.payloads().count()
    }

    /// Every binder name this constructor can occupy, in either naming —
    /// what a LATER constructor's alternates must stay clear of.
    pub(crate) fn occupied_names(&self) -> Vec<String> {
        self.args
            .iter()
            .flat_map(|a| a.both_names().map(str::to_string))
            .collect()
    }
}

/// Binder names the GENERATOR introduces, freshened against everything the
/// source names.
///
/// Not cosmetic. Every one of these appears in a scope that also holds the
/// declaration's parameters, so a codata whose parameter happens to be
/// called `a`, `b`, `f`, `x` or `s` would otherwise have the generated
/// binder shadow it — sometimes producing a type error (fail-closed, but a
/// baffling one) and sometimes a well-typed wrong term.
#[derive(Debug)]
pub(crate) struct GenNames {
    /// The shape argument of `mkStep`.
    pub(crate) shape_arg: String,
    /// The position argument of `mkStep`'s child function and of the
    /// child laws.
    pub(crate) pos_arg: String,
    /// The child-function argument of `mkStep`.
    pub(crate) child_arg: String,
    /// The carrier argument of `head`.
    pub(crate) value_arg: String,
    /// The corecursor's state TYPE (`S`) — VC-4.
    pub(crate) state_arg: String,
    /// The container index a corecursion step is generic over (`j`) — VC-4.
    pub(crate) index_arg: String,
    /// The coalgebra argument of `corec` (`g`) — VC-4.
    pub(crate) coalg_arg: String,
    /// The initial state of `corec` (`s`) — VC-4.
    pub(crate) init_arg: String,
    /// The fallback value of a payload retraction (`d`) — VC-5. A retraction
    /// out of the shape has to be TOTAL, so every branch other than the
    /// constructor's own returns this.
    pub(crate) default_arg: String,
    /// The equation hypothesis of a discrimination/injectivity companion
    /// (`h`) — VC-5.
    pub(crate) eq_arg: String,
    /// Scrutinee names for the `Sum.rec` towers, by depth — deep enough for
    /// both `posF`'s tag tower and the widest constructor's child dispatch.
    pub(crate) scruts: Vec<String>,
}

/// A validated variant codata declaration, with the whole lowering
/// resolved: `Pₖ`, `Qₖ`, projection paths, argument names. Pure — no
/// environment is consulted anywhere in this module.
#[derive(Debug)]
pub(crate) struct VariantShape<'a> {
    pub(crate) name: &'a str,
    pub(crate) binders: &'a [SurfaceBinder],
    pub(crate) ctors: Vec<VariantCtorPlan<'a>>,
    /// The shape functor's value type: right-nested `Sum` of the `Pₖ`
    /// (the bare `P₁` when there is one constructor, which is exactly the
    /// record lane's label type).
    pub(crate) shape_ty: SurfaceExpr,
    pub(crate) gen_names: GenNames,
    /// Was the coinductive companion tier requested (`deriving Coind`)?
    ///
    /// Opt-in because it is the only tier that costs anything: it needs the
    /// `Codata` coinduction seed section (+31 declarations on first use), and
    /// `iM_coind` discharges are the expensive part of checking the result.
    pub(crate) derive_coind: bool,
}

impl VariantShape<'_> {
    /// The tag of constructor `k` carrying `payload`: the injection into
    /// the right-nested `Sum` (`Sum.inr`ᵏ `Sum.inl`, and `Sum.inr`ⁿ⁻¹ for
    /// the last constructor; the identity when there is one constructor).
    pub(crate) fn tag(&self, k: usize, payload: SurfaceExpr) -> SurfaceExpr {
        inject_sum(k, self.ctors.len(), payload)
    }
}

/// `PEmpty.{1}` — the position type of a constructor with no children.
/// Level-pinned for the same reason [`punit_ty`] is.
pub(crate) fn pempty_ty() -> SurfaceExpr {
    SurfaceExpr::UniverseInst(
        Span::dummy(),
        Box::new(ident("PEmpty")),
        vec![LevelExpr::Lit(1)],
    )
}

/// Right-nested `head a (head b c)`; the bare element for one part.
pub(crate) fn nest_right(head: &str, parts: Vec<SurfaceExpr>) -> Option<SurfaceExpr> {
    parts
        .into_iter()
        .rev()
        .reduce(|acc, t| plain_app(head, vec![t, acc]))
}

/// The `PProd` VALUE of a payload list (`PUnit.unit` when empty).
fn pack_pprod(vals: Vec<SurfaceExpr>) -> SurfaceExpr {
    nest_right("PProd.mk", vals).unwrap_or_else(|| ident("PUnit.unit"))
}

/// Inject `v` at position `k` of a right-nested `n`-ary `Sum`.
pub(crate) fn inject_sum(k: usize, n: usize, v: SurfaceExpr) -> SurfaceExpr {
    if n <= 1 {
        return v;
    }
    if k == 0 {
        return plain_app("Sum.inl", vec![v]);
    }
    plain_app("Sum.inr", vec![inject_sum(k - 1, n - 1, v)])
}

/// The projection chain recovering payload `i` of `k` from `base`:
/// `base` (k = 1), `base.1` / `base.2` (k = 2), `base.1` / `base.2.1` /
/// `base.2.2` (k = 3), … — the right-nested `PProd` path.
pub(crate) fn projection_path(base: &str, i: usize, k: usize) -> SurfaceExpr {
    let mut e = ident(base);
    for _ in 0..i {
        e = SurfaceExpr::Proj(Span::dummy(), Box::new(e), Projection::Index(2));
    }
    if i + 1 < k {
        e = SurfaceExpr::Proj(Span::dummy(), Box::new(e), Projection::Index(1));
    }
    e
}

/// Mint the generator's internal binder names, all distinct and all fresh
/// against every identifier the source could refer to at the point they
/// are bound: the parameters, the constructor argument names, the shape
/// binders, and everything named inside a `Pₖ` or `Qₖ`.
pub(crate) fn gen_names(binders: &[SurfaceBinder], plans: &[VariantCtorPlan<'_>]) -> GenNames {
    let mut used: Vec<String> = binders.iter().map(|b| b.name.clone()).collect();
    let mut depth = plans.len();
    for c in plans {
        used.push(c.shape_var.clone());
        used.extend(c.occupied_names());
        collect_idents(&c.payload_ty, &mut used);
        collect_idents(&c.pos_ty_in_shape, &mut used);
        collect_idents(&c.pos_ty_in_args, &mut used);
        depth = depth.max(c.children().count());
    }
    let mut mint = |base: &str| {
        let n = fresh_name(base, &used);
        used.push(n.clone());
        n
    };
    // Minting ORDER is load-bearing for the spelling of generated binders
    // (each mint reserves its result), so the VC-3 names are minted first
    // and the VC-4/VC-5 additions after: a later brick never renames an
    // earlier brick's binders.
    let shape_arg = mint("a");
    let pos_arg = mint("b");
    let child_arg = mint("f");
    let value_arg = mint("x");
    let scruts: Vec<String> = (0..depth.max(1)).map(|i| mint(&format!("s{i}"))).collect();
    GenNames {
        shape_arg,
        pos_arg,
        child_arg,
        value_arg,
        state_arg: mint("S"),
        index_arg: mint("j"),
        coalg_arg: mint("g"),
        init_arg: mint("st"),
        default_arg: mint("d"),
        eq_arg: mint("h"),
        scruts,
    }
}

/// One resolved argument mid-flight: a payload plus the SOURCE name it can
/// be referenced by, or a child plus its domain as written.
enum Slot<'a> {
    Payload(Option<&'a str>, PayloadPlan<'a>),
    /// `(domain as written, primary binder name, alternate binder name)`.
    Child(Option<&'a SurfaceExpr>, String, String),
}

/// Turn the classified telescope into the fully-resolved plan: argument
/// names, `Pₖ`, the projection path of every payload, and `Qₖ` in both the
/// constructor's scope and `posF`'s.
///
/// `occupied` carries every binder name the EARLIER constructors already
/// claim, in either naming. It only constrains the alternates: a statement
/// mentioning two constructors binds constructor `j`'s telescope under the
/// primary names and constructor `k`'s under the alternates, so the
/// alternates are the side that has to give way.
pub(crate) fn resolve_ctor<'a>(
    name: &str,
    param_names: &[&str],
    cname: &'a str,
    classified: Vec<CtorArg<'a>>,
    occupied: &[String],
) -> Result<VariantCtorPlan<'a>, ElabError> {
    // Argument names first: the source binder name where the clause gave
    // one, else a fresh `a<i>` that cannot collide with a parameter, with
    // another argument, or with anything named inside a child domain.
    let mut used: Vec<String> = param_names.iter().map(|p| (*p).to_string()).collect();
    for arg in &classified {
        match arg {
            CtorArg::Payload { name: Some(n), .. }
            | CtorArg::Child { name: Some(n) }
            | CtorArg::ChildFamily { name: Some(n), .. } => used.push((*n).to_string()),
            _ => {}
        }
        if let CtorArg::ChildFamily { domain, .. } = arg {
            collect_idents(domain, &mut used);
        }
    }
    let arg_names: Vec<String> = classified
        .iter()
        .enumerate()
        .map(|(i, arg)| match arg {
            CtorArg::Payload { name: Some(n), .. }
            | CtorArg::Child { name: Some(n) }
            | CtorArg::ChildFamily { name: Some(n), .. } => (*n).to_string(),
            _ => {
                let fresh = fresh_name(&format!("a{i}"), &used);
                used.push(fresh.clone());
                fresh
            }
        })
        .collect();

    // The shape binder `posF`'s branch introduces. Fresh against the same
    // set, so `s.2.1` in a rewritten domain can never capture.
    let shape_var = fresh_name("s", &used);

    // The ALTERNATE naming (VC-5): a second binder name per argument, fresh
    // against this constructor's own names AND every earlier constructor's,
    // so `T.Cⱼ x⃗ = T.Cₖ y⃗ → False` and `T.Cₖ x⃗ = T.Cₖ y⃗ → x⃗ = y⃗` can put
    // both telescopes in one binder list without either shadowing the other.
    let mut alt_used = used.clone();
    alt_used.push(shape_var.clone());
    alt_used.extend(occupied.iter().cloned());
    let alt_names: Vec<String> = arg_names
        .iter()
        .map(|n| {
            let fresh = fresh_name(&format!("{n}0"), &alt_used);
            alt_used.push(fresh.clone());
            fresh
        })
        .collect();

    let payload_tys: Vec<&SurfaceExpr> = classified
        .iter()
        .filter_map(|a| match a {
            CtorArg::Payload { ty, .. } => Some(*ty),
            _ => None,
        })
        .collect();
    let payload_ty = nest_right("PProd", payload_tys.iter().map(|t| (*t).clone()).collect())
        .unwrap_or_else(punit_ty);

    // Pass 1 — the payload plans, each carrying the projection path that
    // recovers it from the bound shape value.
    let k = payload_tys.len();
    let mut payload_i = 0usize;
    let mut slots: Vec<Slot<'a>> = Vec::new();
    for ((arg, arg_name), alt_name) in classified.iter().zip(&arg_names).zip(&alt_names) {
        slots.push(match arg {
            CtorArg::Payload { name: src, ty } => {
                let plan = PayloadPlan {
                    arg_name: arg_name.clone(),
                    alt_name: alt_name.clone(),
                    ty,
                    projection: projection_path(&shape_var, payload_i, k),
                };
                payload_i += 1;
                Slot::Payload(*src, plan)
            }
            CtorArg::Child { .. } => Slot::Child(None, arg_name.clone(), alt_name.clone()),
            CtorArg::ChildFamily { domain, .. } => {
                Slot::Child(Some(*domain), arg_name.clone(), alt_name.clone())
            }
        });
    }

    // Pass 2 — rewrite each child DOMAIN out of the constructor's scope:
    // into `posF`'s (payload → its projection of the bound shape) and into
    // the alternate telescope's (payload → its alternate binder). Only
    // NAMED payloads can be referenced, so only those enter either
    // substitution.
    let subs: Vec<(String, SurfaceExpr)> = slots
        .iter()
        .filter_map(|s| match s {
            Slot::Payload(Some(src), plan) => Some(((*src).to_string(), plan.projection.clone())),
            _ => None,
        })
        .collect();
    let alt_subs: Vec<(String, SurfaceExpr)> = slots
        .iter()
        .filter_map(|s| match s {
            Slot::Payload(Some(src), plan) => Some(((*src).to_string(), ident(&plan.alt_name))),
            _ => None,
        })
        .collect();
    let mut args: Vec<ArgPlan<'a>> = Vec::new();
    for slot in slots {
        match slot {
            Slot::Payload(_, plan) => args.push(ArgPlan::Payload(plan)),
            Slot::Child(None, arg_name, alt_name) => args.push(ArgPlan::Child(ChildPlan {
                arg_name,
                alt_name,
                family: None,
            })),
            Slot::Child(Some(domain), arg_name, alt_name) => {
                let in_shape = subst_idents(name, cname, domain, &subs, &mut Vec::new())?;
                let in_alt = subst_idents(name, cname, domain, &alt_subs, &mut Vec::new())?;
                // ANTI-VACUITY. `Vis`'s child domain is `Ans e`, and `e` is
                // a constructor binder that does NOT exist inside `posF` —
                // there, the only thing in scope is the shape value. If the
                // rewrite silently left `e` free the generated `posF` would
                // either fail to elaborate or, worse, CAPTURE a parameter of
                // the same name and produce a well-typed wrong carrier.
                // Refuse instead. The alternate spelling is held to the same
                // standard: a surviving `e` there would silently weaken
                // `T.Vis_inj` into a statement about ONE `Vis`.
                for (from, _) in &subs {
                    if mentions(&in_shape, from) || mentions(&in_alt, from) {
                        return Err(unsupported(format!(
                            "variant codata `{name}`: constructor `{cname}`'s \
                             recursive argument domain still mentions the payload \
                             `{from}` after rewriting it to a projection of the \
                             shape — refusing to emit a position family with a \
                             free variable in it"
                        )));
                    }
                }
                args.push(ArgPlan::Child(ChildPlan {
                    arg_name,
                    alt_name,
                    family: Some(FamilyPlan {
                        source: domain,
                        in_shape,
                        in_alt,
                    }),
                }));
            }
        }
    }

    let children: Vec<&ChildPlan<'a>> = args
        .iter()
        .filter_map(|a| match a {
            ArgPlan::Child(c) => Some(c),
            ArgPlan::Payload(_) => None,
        })
        .collect();
    let pos_ty_in_shape = nest_right(
        "Sum",
        children.iter().map(|c| c.domain_in_shape()).collect(),
    )
    .unwrap_or_else(pempty_ty);
    let pos_ty_in_args = nest_right("Sum", children.iter().map(|c| c.domain_in_args()).collect())
        .unwrap_or_else(pempty_ty);

    Ok(VariantCtorPlan {
        name: cname,
        args,
        payload_ty,
        pos_ty_in_shape,
        pos_ty_in_args,
        shape_var,
    })
}

/// A name equal to `base` when that is unused, else `base0`, `base1`, ….
fn fresh_name(base: &str, used: &[String]) -> String {
    let mut candidate = base.to_string();
    let mut i = 0usize;
    while used.contains(&candidate) {
        candidate = format!("{base}{i}");
        i += 1;
    }
    candidate
}

/// Every identifier occurring in `expr`, over exactly the node set
/// [`subst_idents`] traverses (so a name chosen fresh against this list
/// cannot be captured by a rewrite that succeeds).
fn collect_idents(expr: &SurfaceExpr, out: &mut Vec<String>) {
    match expr {
        SurfaceExpr::Ident(_, id) => out.push(id.clone()),
        SurfaceExpr::App(_, h, args) => {
            collect_idents(h, out);
            for a in args {
                collect_idents(&a.expr, out);
            }
        }
        SurfaceExpr::Lambda(_, bs, body) | SurfaceExpr::Pi(_, bs, body) => {
            for b in bs {
                out.push(b.name.clone());
                if let Some(t) = &b.ty {
                    collect_idents(t, out);
                }
            }
            collect_idents(body, out);
        }
        SurfaceExpr::Arrow(_, a, b) | SurfaceExpr::Ascription(_, a, b) => {
            collect_idents(a, out);
            collect_idents(b, out);
        }
        SurfaceExpr::Paren(_, e)
        | SurfaceExpr::Explicit(_, e)
        | SurfaceExpr::OutParam(_, e)
        | SurfaceExpr::SemiOutParam(_, e)
        | SurfaceExpr::Proj(_, e, _)
        | SurfaceExpr::UniverseInst(_, e, _) => collect_idents(e, out),
        _ => {}
    }
}

/// Rewrite `from → to` for every substitution in `subs`, respecting
/// shadowing by binders inside `expr`.
///
/// Total on the expression forms a TYPE can take (the list below); any
/// other form is REFUSED by name rather than copied through, because
/// copying a node we cannot look inside would leave a payload reference
/// free in `posF` — the exact silent miscompile this brick exists to
/// prevent. A constructor with no payloads never calls this.
fn subst_idents(
    name: &str,
    cname: &str,
    expr: &SurfaceExpr,
    subs: &[(String, SurfaceExpr)],
    shadowed: &mut Vec<String>,
) -> Result<SurfaceExpr, ElabError> {
    let rec = |e: &SurfaceExpr, sh: &mut Vec<String>| subst_idents(name, cname, e, subs, sh);
    Ok(match expr {
        SurfaceExpr::Ident(_, id) => {
            if !shadowed.iter().any(|b| b == id) {
                if let Some((_, to)) = subs.iter().find(|(from, _)| from == id) {
                    return Ok(to.clone());
                }
            }
            expr.clone()
        }
        SurfaceExpr::Universe(..)
        | SurfaceExpr::Lit(..)
        | SurfaceExpr::Hole(..)
        | SurfaceExpr::NamedHole(..)
        | SurfaceExpr::SyntheticSorry(..) => expr.clone(),
        SurfaceExpr::App(s, h, args) => {
            let head = rec(h, shadowed)?;
            let mut new_args = Vec::with_capacity(args.len());
            for a in args {
                new_args.push(SurfaceArg {
                    span: a.span,
                    expr: rec(&a.expr, shadowed)?,
                    name: a.name.clone(),
                });
            }
            SurfaceExpr::App(*s, Box::new(head), new_args)
        }
        SurfaceExpr::Lambda(s, bs, body) | SurfaceExpr::Pi(s, bs, body) => {
            let depth = shadowed.len();
            let mut new_bs = Vec::with_capacity(bs.len());
            for b in bs {
                let mut nb = b.clone();
                if let Some(t) = &b.ty {
                    nb.ty = Some(Box::new(rec(t, shadowed)?));
                }
                shadowed.push(b.name.clone());
                new_bs.push(nb);
            }
            let new_body = Box::new(rec(body, shadowed)?);
            shadowed.truncate(depth);
            match expr {
                SurfaceExpr::Lambda(..) => SurfaceExpr::Lambda(*s, new_bs, new_body),
                _ => SurfaceExpr::Pi(*s, new_bs, new_body),
            }
        }
        SurfaceExpr::Arrow(s, a, b) => {
            SurfaceExpr::Arrow(*s, Box::new(rec(a, shadowed)?), Box::new(rec(b, shadowed)?))
        }
        SurfaceExpr::Ascription(s, a, b) => {
            SurfaceExpr::Ascription(*s, Box::new(rec(a, shadowed)?), Box::new(rec(b, shadowed)?))
        }
        SurfaceExpr::Paren(s, e) => SurfaceExpr::Paren(*s, Box::new(rec(e, shadowed)?)),
        SurfaceExpr::Explicit(s, e) => SurfaceExpr::Explicit(*s, Box::new(rec(e, shadowed)?)),
        SurfaceExpr::OutParam(s, e) => SurfaceExpr::OutParam(*s, Box::new(rec(e, shadowed)?)),
        SurfaceExpr::SemiOutParam(s, e) => {
            SurfaceExpr::SemiOutParam(*s, Box::new(rec(e, shadowed)?))
        }
        SurfaceExpr::Proj(s, e, p) => SurfaceExpr::Proj(*s, Box::new(rec(e, shadowed)?), p.clone()),
        SurfaceExpr::UniverseInst(s, e, ls) => {
            SurfaceExpr::UniverseInst(*s, Box::new(rec(e, shadowed)?), ls.clone())
        }
        _ => {
            return Err(unsupported(format!(
                "variant codata `{name}`: constructor `{cname}` has a recursive \
                 argument whose domain uses an expression form the VC1 lowering \
                 cannot rewrite payload references through ({}); the position \
                 family would be emitted with a free variable in it",
                expr_form(expr)
            )))
        }
    })
}

/// A short name for the expression form, for the refusal above.
fn expr_form(expr: &SurfaceExpr) -> &'static str {
    match expr {
        SurfaceExpr::Let(..) | SurfaceExpr::LetRec(..) | SurfaceExpr::LetPattern(..) => "let",
        SurfaceExpr::If(..) | SurfaceExpr::IfLet(..) | SurfaceExpr::IfDecidable(..) => "if",
        SurfaceExpr::Match(..) | SurfaceExpr::PatternMatchLambda(..) => "match",
        _ => "unsupported form",
    }
}
