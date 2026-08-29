// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! VARIANT codata's COINDUCTIVE tier — brick VC-6 of
//! `designs/2026-08-28-variant-codata-surface.md`.
//!
//! VC-3/VC-4/VC-5 emit how a codata COMPUTES and what tells its constructors
//! apart. All of that is `rfl` over `Sum`. This module emits the one thing
//! that is not: **eta**, the law that says an arbitrary value whose head is
//! `Cₖ`'s tag IS a `Cₖ` applied to its own children. Proving it needs
//! coinduction — `Codata.iM_coind` — because the two sides are not
//! definitionally equal for an opaque `x`; they are only bisimilar.
//!
//! Emitted, for a codata `T` with constructors `C₀ … Cₙ₋₁`:
//!
//! | generated | kind | what it is |
//! |---|---|---|
//! | `T.child` / `T.cast` | def | ascribed observation wrappers |
//! | `T.wchild_Cₖ[_i]` | thm (`rfl`) | the VC-3 child laws in wrapper vocabulary |
//! | `T.ExtQ` + 4 companions | def/thm | the bisimulation candidate and its discharge |
//! | `T.ext` | thm | ONE-STEP extensionality: heads agree + children agree ⇒ equal |
//! | `T.CₖChild[i]` | def | per-position child extractor |
//! | `T.Cₖ_eta` | thm | `head x = tagₖ → x = Cₖ (extractors x)` |
//! | `T.CₖChild[i]_compute` | thm (`rfl`) | the extractor lands on the RIGHT child |
//! | `T.CasesP` / `T.cases` | def/thm | the N-ary case tower: x IS one of the constructors |
//! | `T.sumCases`, `T.cases_Cₖ` | thm | the tower's dispatch and its per-constructor leaves |
//!
//! **The children clause is the only per-constructor variation**, and it
//! varies with the POSITION SHAPE, of which VC-1's envelope admits four:
//! empty (`PEmpty.rec`), unit, dependent family, and k-fold `Sum` (a
//! DEPENDENT `Sum.rec` whose motive is the obligation itself). Unit and
//! dependent turn out to be the same template at different arity, so there
//! are three code paths, not four. This was measured, not assumed: the
//! probe at `designs/2026-08-28-variant-codata-surface.md` §9 checked all
//! four against a generated descriptor before a line of this module existed.
//!
//! **The k-fold discharge is fail-closed against a swap.** MEASURED, by
//! building a generator whose `Sum.rec` branches were exchanged: the
//! declaration does not merely produce a wrong-but-checkable law, it
//! REFUSES — generated declaration 69 (`ITr.Br_eta`) fails with a rigid
//! `Sum.inr` vs `Sum.inl` head mismatch, and because registration is
//! transactional the whole `codata` command then fails. The dependent
//! motive is what does that: it carries the position into the obligation,
//! so a branch proving the wrong position cannot typecheck. (My first draft
//! of this paragraph claimed the opposite — that a swap still checks and
//! only the computation pins catch it. The experiment says otherwise, and
//! the experiment wins.)
//!
//! **What `T.CₖChildᵢ_compute` is for, then.** Not that check — these are the
//! extractors' COMPUTATION laws (`T.TauChild (T.Tau t) rfl = t`), the thing
//! that makes an extractor usable on a constructor value at all. They also
//! pin which child each extractor names, which is worth stating explicitly
//! even though the eta law happens to constrain it too.
//!
//! **Cost.** This tier needs the `Codata` coinduction seed section, +31
//! declarations on first use. It is therefore OPT-IN, via `deriving Coind`.
//! A codata that does not ask pays nothing (`codata_seed.rs`
//! `test_coind_section_is_not_in_the_core_seed`).

use crate::codata_cmd::{arrow, at_app, ident, lam, mk_def, mk_theorem, plain_app, punit_ty};
use crate::codata_variant::unsupported;
use crate::codata_variant_generate::{binder, ctor_binders, ctor_call, eq, lam_one, lam_typed};
use crate::codata_variant_plan::{
    inject_sum, nest_right, ChildPlan, VariantCtorPlan, VariantShape,
};
use crate::ElabError;
use clean_parser::{
    Span, SurfaceBinder, SurfaceBinderInfo, SurfaceDecl, SurfaceExpr, UniverseExpr,
};

/// `Prop`, as a sort.
fn prop_universe() -> SurfaceExpr {
    SurfaceExpr::Universe(Span::dummy(), UniverseExpr::Prop)
}

/// An implicit binder `{name : ty}`.
fn implicit(name: &str, ty: SurfaceExpr) -> SurfaceBinder {
    SurfaceBinder {
        ty: Some(Box::new(ty)),
        ..SurfaceBinder::new(name, None, SurfaceBinderInfo::Implicit)
    }
}

fn pi(binders: Vec<SurfaceBinder>, body: SurfaceExpr) -> SurfaceExpr {
    SurfaceExpr::Pi(Span::dummy(), binders, Box::new(body))
}

/// The binder names this tier introduces, freshened against everything the
/// source names AND everything the earlier bricks already minted.
///
/// Minted here rather than added to `GenNames` on purpose: `gen_names`
/// documents that its minting ORDER is load-bearing for the spelling of
/// VC-3/VC-4/VC-5 binders, so appending to it would silently re-spell
/// already-generated terms. Seeding a separate mint with the earlier names
/// marked used gets freshness without touching them.
struct CoindNames {
    idx: String,
    lhs: String,
    rhs: String,
    heq: String,
    pos: String,
    m1: String,
    m2: String,
    rel: String,
    hyp: String,
    val: String,
    e1: String,
    e2: String,
    scrut: String,
    hh: String,
    hc: String,
}

impl CoindNames {
    fn mint(shape: &VariantShape<'_>) -> Self {
        let g = &shape.gen_names;
        let mut used: Vec<String> = shape.binders.iter().map(|b| b.name.clone()).collect();
        for c in &shape.ctors {
            used.push(c.shape_var.clone());
            used.extend(c.occupied_names());
        }
        used.extend([
            g.shape_arg.clone(),
            g.pos_arg.clone(),
            g.child_arg.clone(),
            g.value_arg.clone(),
            g.state_arg.clone(),
            g.index_arg.clone(),
            g.coalg_arg.clone(),
            g.init_arg.clone(),
            g.default_arg.clone(),
            g.eq_arg.clone(),
        ]);
        used.extend(g.scruts.iter().cloned());
        let mut mint = |base: &str| {
            let mut candidate = base.to_string();
            let mut i = 0usize;
            while used.contains(&candidate) {
                candidate = format!("{base}{i}");
                i += 1;
            }
            used.push(candidate.clone());
            candidate
        };
        CoindNames {
            idx: mint("j"),
            lhs: mint("x"),
            rhs: mint("y"),
            heq: mint("e"),
            pos: mint("b"),
            m1: mint("m1"),
            m2: mint("m2"),
            rel: mint("r"),
            hyp: mint("hr"),
            val: mint("v"),
            e1: mint("e1"),
            e2: mint("e2"),
            scrut: mint("z"),
            hh: mint("hh"),
            hc: mint("hc"),
        }
    }
}

/// The three descriptor applications every statement in this module is
/// phrased against, plus the parameter list they are built from.
struct Desc {
    name: String,
    params: Vec<SurfaceExpr>,
    shape_f: SurfaceExpr,
    pos_f: SurfaceExpr,
    tgt_f: SurfaceExpr,
    self_ty: SurfaceExpr,
}

impl Desc {
    fn new(shape: &VariantShape<'_>) -> Self {
        let name = shape.name;
        let params: Vec<SurfaceExpr> = shape
            .binders
            .iter()
            .map(|b| ident(&b.name))
            .collect::<Vec<_>>();
        Desc {
            name: name.to_string(),
            shape_f: plain_app(&format!("{name}.shapeF"), params.clone()),
            pos_f: plain_app(&format!("{name}.posF"), params.clone()),
            tgt_f: plain_app(&format!("{name}.tgtF"), params.clone()),
            self_ty: plain_app(name, params.clone()),
            params,
        }
    }

    /// `T.<suffix> ps extra…` — one of the generated family's members, applied
    /// to the codata parameters and then to `extra`.
    fn member(&self, suffix: &str, extra: Vec<SurfaceExpr>) -> SurfaceExpr {
        let mut args = self.params.clone();
        args.extend(extra);
        plain_app(&format!("{}.{suffix}", self.name), args)
    }

    /// `Codata.IMIntl (T.shapeF ps) (T.posF ps) (T.tgtF ps) j`
    fn imintl(&self, j: SurfaceExpr) -> SurfaceExpr {
        plain_app(
            "Codata.IMIntl",
            vec![
                self.shape_f.clone(),
                self.pos_f.clone(),
                self.tgt_f.clone(),
                j,
            ],
        )
    }

    /// `@Codata.IMhead PUnit.{1} (shapeF) (posF) (tgtF) j v`
    fn imhead(&self, j: SurfaceExpr, v: SurfaceExpr) -> SurfaceExpr {
        at_app(
            "Codata.IMhead",
            vec![
                punit_ty(),
                self.shape_f.clone(),
                self.pos_f.clone(),
                self.tgt_f.clone(),
                j,
                v,
            ],
        )
    }

    /// `@Codata.IMchild PUnit.{1} (shapeF) (posF) (tgtF) j v b`
    fn imchild(&self, j: SurfaceExpr, v: SurfaceExpr, b: SurfaceExpr) -> SurfaceExpr {
        at_app(
            "Codata.IMchild",
            vec![
                punit_ty(),
                self.shape_f.clone(),
                self.pos_f.clone(),
                self.tgt_f.clone(),
                j,
                v,
                b,
            ],
        )
    }

    /// `@Codata.it_congr PUnit.{1} … j l h e b` / `@Codata.icastB …`.
    fn congr_like(
        &self,
        which: &str,
        j: SurfaceExpr,
        l: SurfaceExpr,
        h: SurfaceExpr,
        e: SurfaceExpr,
        b: SurfaceExpr,
    ) -> SurfaceExpr {
        at_app(
            which,
            vec![
                punit_ty(),
                self.shape_f.clone(),
                self.pos_f.clone(),
                self.tgt_f.clone(),
                j,
                l,
                h,
                e,
                b,
            ],
        )
    }

    /// `T.posF ps j h` — the position type at index `j` and shape `h`.
    fn pos_at(&self, j: SurfaceExpr, h: SurfaceExpr) -> SurfaceExpr {
        self.member("posF", vec![j, h])
    }

    /// `T.head ps x`
    fn head_of(&self, x: SurfaceExpr) -> SurfaceExpr {
        self.member("head", vec![x])
    }

    /// `T.child ps x b`
    fn child_of(&self, x: SurfaceExpr, b: SurfaceExpr) -> SurfaceExpr {
        self.member("child", vec![x, b])
    }

    /// `T.cast ps e b`
    fn cast_of(&self, e: SurfaceExpr, b: SurfaceExpr) -> SurfaceExpr {
        self.member("cast", vec![e, b])
    }
}

/// A constructor's position-shape class — the ONE axis the eta proof varies
/// along. VC-1's envelope admits exactly these.
enum PosShape<'a, 'b> {
    /// No recursive argument: the children clause is vacuous.
    Empty,
    /// Exactly one, either bare (`PUnit` position) or a family (`D`).
    Single(&'a ChildPlan<'b>),
    /// Two or more, all BARE — the right-nested `Sum` of `PUnit`s.
    Fold(Vec<&'a ChildPlan<'b>>),
}

/// Classify, refusing loudly outside the probed envelope.
fn classify<'a, 'b>(
    shape_name: &str,
    ctor: &'a VariantCtorPlan<'b>,
) -> Result<PosShape<'a, 'b>, ElabError> {
    let children: Vec<&ChildPlan<'_>> = ctor.children().collect();
    match children.len() {
        0 => Ok(PosShape::Empty),
        1 => Ok(PosShape::Single(children[0])),
        _ => {
            if let Some(c) = children.iter().find(|c| c.family.is_some()) {
                return Err(unsupported(format!(
                    "variant codata `{shape_name}`: `deriving Coind` does not support \
                     constructor `{}` — it has {} recursive arguments and `{}` is an \
                     INDEXED family, so the position type is a Sum with a dependent \
                     summand. MEASURED, not assumed (§12): the eta half GENERALIZES to \
                     this shape — dependent branch binder and all, computation pins \
                     included — but the N-ary case tower does not. The refusal sits here, \
                     covering both, rather than silently emitting a tier whose `cases` is \
                     missing. A named gap, not a silent one: the definitional tier \
                     (VC-3/4/5) still works for this constructor — drop `deriving Coind`",
                    ctor.name,
                    children.len(),
                    c.arg_name
                )));
            }
            Ok(PosShape::Fold(children))
        }
    }
}

/// The name of a constructor's `i`-th child extractor.
fn extractor_name(shape_name: &str, ctor: &VariantCtorPlan<'_>, i: usize, m: usize) -> String {
    if m == 1 {
        format!("{shape_name}.{}Child", ctor.name)
    } else {
        format!("{shape_name}.{}Child{i}", ctor.name)
    }
}

/// The wrapper-vocabulary child law's name for position `i`.
fn wchild_name(shape_name: &str, ctor: &VariantCtorPlan<'_>, i: usize, m: usize) -> String {
    if m <= 1 {
        format!("{shape_name}.wchild_{}", ctor.name)
    } else {
        format!("{shape_name}.wchild_{}_{i}", ctor.name)
    }
}

/// The whole coinductive tier.
pub(crate) fn generate(shape: &VariantShape<'_>) -> Result<Vec<SurfaceDecl>, ElabError> {
    let d = Desc::new(shape);
    let n = CoindNames::mint(shape);
    let mut out = wrappers(shape, &d, &n);
    out.extend(extensionality(shape, &d, &n));
    for (k, ctor) in shape.ctors.iter().enumerate() {
        out.extend(per_ctor(shape, &d, &n, k, ctor)?);
    }
    out.extend(cases_tower(shape, &d, &n));
    Ok(out)
}

/// `T.child` and `T.cast`: the observation wrappers every statement below is
/// phrased in. Without them each obligation would carry the full six-argument
/// `@Codata.IMchild` spelling, and the `Eq.rec` motives would not align.
fn wrappers(shape: &VariantShape<'_>, d: &Desc, n: &CoindNames) -> Vec<SurfaceDecl> {
    let name = shape.name;
    let unit = ident("PUnit.unit");
    let x = ident(&n.lhs);

    let child = {
        let mut bs = shape.binders.to_vec();
        bs.push(binder(&n.lhs, d.self_ty.clone()));
        bs.push(binder(&n.pos, d.pos_at(unit.clone(), d.head_of(x.clone()))));
        mk_def(
            format!("{name}.child"),
            bs,
            d.self_ty.clone(),
            d.imchild(unit.clone(), x.clone(), ident(&n.pos)),
        )
    };

    let cast = {
        let shape_ty = d.member("shapeF", vec![unit.clone()]);
        let mut bs = shape.binders.to_vec();
        bs.push(implicit(&n.m1, shape_ty.clone()));
        bs.push(implicit(&n.m2, shape_ty));
        bs.push(binder(&n.heq, eq(ident(&n.m1), ident(&n.m2))));
        bs.push(binder(&n.pos, d.pos_at(unit.clone(), ident(&n.m2))));
        mk_def(
            format!("{name}.cast"),
            bs,
            d.pos_at(unit.clone(), ident(&n.m1)),
            plain_app(
                "cast",
                vec![
                    plain_app(
                        "congrArg",
                        vec![
                            d.member("posF", vec![unit.clone()]),
                            plain_app("Eq.symm", vec![ident(&n.heq)]),
                        ],
                    ),
                    ident(&n.pos),
                ],
            ),
        )
    };
    vec![child, cast]
}

/// The bisimulation candidate, its two projections, the two `rfl` bridges,
/// and one-step extensionality.
///
/// Six declarations that mention NO constructor — only `shapeF`/`posF`/`tgtF`.
/// That is why VC-6 is template instantiation rather than per-constructor
/// proof engineering: everything constructor-specific is confined to the eta
/// laws below.
fn extensionality(shape: &VariantShape<'_>, d: &Desc, n: &CoindNames) -> Vec<SurfaceDecl> {
    let name = shape.name;
    let unit = ident("PUnit.unit");
    let (j, x, y) = (ident(&n.idx), ident(&n.lhs), ident(&n.rhs));
    let hx = d.imhead(j.clone(), x.clone());
    let hy = d.imhead(j.clone(), y.clone());

    // T.ExtQ : (j : PUnit) → IMIntl … j → IMIntl … j → Prop
    let ext_q = {
        // The children clause quantifies over the head-equality PROOF. That
        // spelling is not cosmetic: `iM_coind`'s obligation reapplies the
        // relation at a head equality it derives itself, so a candidate that
        // fixed one proof would not match (the candidate-spelling lesson,
        // ITreeEco.lean:2813-2823).
        let inner_pos = binder(&n.pos, d.pos_at(j.clone(), hy.clone()));
        let e = ident(&n.heq);
        let b = ident(&n.pos);
        let children = eq(
            plain_app(
                "Codata.icastM",
                vec![
                    d.congr_like(
                        "Codata.it_congr",
                        j.clone(),
                        hx.clone(),
                        hy.clone(),
                        e.clone(),
                        b.clone(),
                    ),
                    d.imchild(
                        j.clone(),
                        x.clone(),
                        d.congr_like(
                            "Codata.icastB",
                            j.clone(),
                            hx.clone(),
                            hy.clone(),
                            e,
                            b.clone(),
                        ),
                    ),
                ],
            ),
            d.imchild(j.clone(), y.clone(), b),
        );
        let body = plain_app(
            "And",
            vec![
                eq(hx.clone(), hy.clone()),
                pi(
                    vec![binder(&n.heq, eq(hx.clone(), hy.clone())), inner_pos],
                    children,
                ),
            ],
        );
        mk_def(
            format!("{name}.ExtQ"),
            shape.binders.to_vec(),
            pi(
                vec![binder(&n.idx, punit_ty())],
                arrow(
                    d.imintl(j.clone()),
                    arrow(d.imintl(j.clone()), prop_universe()),
                ),
            ),
            SurfaceExpr::Lambda(
                Span::dummy(),
                vec![
                    SurfaceBinder::new(&n.idx, None, SurfaceBinderInfo::Explicit),
                    SurfaceBinder::new(&n.lhs, None, SurfaceBinderInfo::Explicit),
                    SurfaceBinder::new(&n.rhs, None, SurfaceBinderInfo::Explicit),
                ],
                Box::new(body),
            ),
        )
    };

    let ext_q_app = |a: SurfaceExpr, b: SurfaceExpr, c: SurfaceExpr| {
        let mut args = d.params.clone();
        args.extend([a, b, c]);
        plain_app(&format!("{name}.ExtQ"), args)
    };
    let ext_q_partial = || plain_app(&format!("{name}.ExtQ"), d.params.clone());

    // T.ExtQ_hhead : ∀ j m1 m2, ExtQ j m1 m2 → IMhead j m1 = IMhead j m2
    let ext_q_hhead = mk_theorem(
        format!("{name}.ExtQ_hhead"),
        shape.binders.to_vec(),
        pi(
            vec![
                binder(&n.idx, punit_ty()),
                binder(&n.m1, d.imintl(j.clone())),
                binder(&n.m2, d.imintl(j.clone())),
            ],
            arrow(
                ext_q_app(j.clone(), ident(&n.m1), ident(&n.m2)),
                eq(
                    d.imhead(j.clone(), ident(&n.m1)),
                    d.imhead(j.clone(), ident(&n.m2)),
                ),
            ),
        ),
        lam(
            &["_", "_", "_", &n.rel],
            plain_app("And.left", vec![ident(&n.rel)]),
        ),
    );

    // T.ExtQ_of_eq : x = y → ExtQ j x y
    let ext_q_of_eq = {
        let mut bs = shape.binders.to_vec();
        bs.push(implicit(&n.idx, punit_ty()));
        bs.push(implicit(&n.lhs, d.imintl(j.clone())));
        bs.push(implicit(&n.rhs, d.imintl(j.clone())));
        bs.push(binder(&n.hyp, eq(x.clone(), y.clone())));
        mk_theorem(
            format!("{name}.ExtQ_of_eq"),
            bs,
            ext_q_app(j.clone(), x.clone(), y.clone()),
            at_app(
                "Eq.rec",
                vec![
                    d.imintl(j.clone()),
                    x.clone(),
                    lam(
                        &[&n.val, "_"],
                        ext_q_app(j.clone(), x.clone(), ident(&n.val)),
                    ),
                    plain_app(
                        "And.intro",
                        vec![ident("rfl"), lam(&["_", "_"], ident("rfl"))],
                    ),
                    y.clone(),
                    ident(&n.hyp),
                ],
            ),
        )
    };

    // The two `rfl` bridges from the raw obligation vocabulary to the
    // wrapper vocabulary. Both are `rfl`; they exist so `T.ext`'s proof term
    // can be written in wrapper vocabulary at all.
    let hxu = d.head_of(x.clone());
    let hyu = d.head_of(y.clone());
    let ext_unwrap = {
        let mut bs = shape.binders.to_vec();
        bs.push(binder(&n.lhs, d.self_ty.clone()));
        bs.push(binder(&n.rhs, d.self_ty.clone()));
        bs.push(binder(&n.heq, eq(hxu.clone(), hyu.clone())));
        bs.push(binder(&n.pos, d.pos_at(unit.clone(), hyu.clone())));
        let e = ident(&n.heq);
        let b = ident(&n.pos);
        mk_theorem(
            format!("{name}.ext_unwrap"),
            bs,
            eq(
                plain_app(
                    "Codata.icastM",
                    vec![
                        d.congr_like(
                            "Codata.it_congr",
                            unit.clone(),
                            hxu.clone(),
                            hyu.clone(),
                            e.clone(),
                            b.clone(),
                        ),
                        d.imchild(
                            unit.clone(),
                            x.clone(),
                            d.congr_like(
                                "Codata.icastB",
                                unit.clone(),
                                hxu.clone(),
                                hyu.clone(),
                                e.clone(),
                                b.clone(),
                            ),
                        ),
                    ],
                ),
                d.child_of(x.clone(), d.cast_of(e, b)),
            ),
            ident("rfl"),
        )
    };

    // Cast-proof irrelevance, in wrapper vocabulary: the obligation arrives
    // with the proof `iM_coind` derived, the hypothesis is stated with the
    // caller's — and they are different terms of the same Prop.
    let ch_cast_irrel = {
        let mut bs = shape.binders.to_vec();
        bs.push(binder(&n.lhs, d.self_ty.clone()));
        bs.push(binder(&n.rhs, d.self_ty.clone()));
        bs.push(binder(&n.e1, eq(hxu.clone(), hyu.clone())));
        bs.push(binder(&n.e2, eq(hxu.clone(), hyu.clone())));
        bs.push(binder(&n.pos, d.pos_at(unit.clone(), hyu.clone())));
        mk_theorem(
            format!("{name}.ch_cast_irrel"),
            bs,
            eq(
                d.child_of(x.clone(), d.cast_of(ident(&n.e1), ident(&n.pos))),
                d.child_of(x.clone(), d.cast_of(ident(&n.e2), ident(&n.pos))),
            ),
            ident("rfl"),
        )
    };

    // T.ext — one-step extensionality, the tier's centerpiece.
    let ext = {
        let mut bs = shape.binders.to_vec();
        bs.push(binder(&n.lhs, d.self_ty.clone()));
        bs.push(binder(&n.rhs, d.self_ty.clone()));
        bs.push(binder(&n.heq, eq(hxu.clone(), hyu.clone())));
        bs.push(binder(
            &n.hc,
            pi(
                vec![binder(&n.pos, d.pos_at(unit.clone(), hyu.clone()))],
                eq(
                    d.child_of(x.clone(), d.cast_of(ident(&n.heq), ident(&n.pos))),
                    d.child_of(y.clone(), ident(&n.pos)),
                ),
            ),
        ));
        let hhead_partial = plain_app(&format!("{name}.ExtQ_hhead"), d.params.clone());
        let of_eq_partial = plain_app(&format!("{name}.ExtQ_of_eq"), d.params.clone());
        // hchild is supplied INLINE. Naming it and reapplying does not
        // typecheck: the relation's children clause is ∀-quantified over the
        // head proof, so the argument must be built where that proof is bound
        // (the reapplication lesson, ITreeEco.lean:2897-2906).
        let hchild = SurfaceExpr::Lambda(
            Span::dummy(),
            vec![
                SurfaceBinder::new(&n.idx, None, SurfaceBinderInfo::Explicit),
                SurfaceBinder::new(&n.m1, None, SurfaceBinderInfo::Explicit),
                SurfaceBinder::new(&n.m2, None, SurfaceBinderInfo::Explicit),
                SurfaceBinder::new(&n.rel, None, SurfaceBinderInfo::Explicit),
                SurfaceBinder::new(&n.pos, None, SurfaceBinderInfo::Explicit),
            ],
            Box::new(plain_app_expr(
                of_eq_partial,
                vec![plain_app(
                    "And.right",
                    vec![
                        ident(&n.rel),
                        plain_app_expr(
                            hhead_partial.clone(),
                            vec![ident(&n.idx), ident(&n.m1), ident(&n.m2), ident(&n.rel)],
                        ),
                        ident(&n.pos),
                    ],
                )],
            )),
        );
        let e = ident(&n.heq);
        let b = ident(&n.pos);
        let witness = plain_app(
            "And.intro",
            vec![
                e.clone(),
                SurfaceExpr::Lambda(
                    Span::dummy(),
                    vec![
                        SurfaceBinder::new(&n.e1, None, SurfaceBinderInfo::Explicit),
                        SurfaceBinder::new(&n.pos, None, SurfaceBinderInfo::Explicit),
                    ],
                    Box::new(plain_app(
                        "Eq.trans",
                        vec![
                            {
                                let mut a = d.params.clone();
                                a.extend([x.clone(), y.clone(), ident(&n.e1), b.clone()]);
                                plain_app(&format!("{name}.ext_unwrap"), a)
                            },
                            plain_app(
                                "Eq.trans",
                                vec![
                                    {
                                        let mut a = d.params.clone();
                                        a.extend([
                                            x.clone(),
                                            y.clone(),
                                            ident(&n.e1),
                                            e.clone(),
                                            b.clone(),
                                        ]);
                                        plain_app(&format!("{name}.ch_cast_irrel"), a)
                                    },
                                    plain_app(&n.hc, vec![b.clone()]),
                                ],
                            ),
                        ],
                    )),
                ),
            ],
        );
        mk_theorem(
            format!("{name}.ext"),
            bs,
            eq(x.clone(), y.clone()),
            at_app(
                "Codata.iM_coind",
                vec![
                    punit_ty(),
                    d.shape_f.clone(),
                    d.pos_f.clone(),
                    d.tgt_f.clone(),
                    ext_q_partial(),
                    hhead_partial,
                    hchild,
                    unit.clone(),
                    x.clone(),
                    y.clone(),
                    witness,
                ],
            ),
        )
    };

    vec![
        ext_q,
        ext_q_hhead,
        ext_q_of_eq,
        ext_unwrap,
        ch_cast_irrel,
        ext,
    ]
}

/// Apply an already-built expression to more arguments.
fn plain_app_expr(head: SurfaceExpr, args: Vec<SurfaceExpr>) -> SurfaceExpr {
    use clean_parser::SurfaceArg;
    if args.is_empty() {
        return head;
    }
    SurfaceExpr::App(
        Span::dummy(),
        Box::new(head),
        args.into_iter().map(SurfaceArg::positional).collect(),
    )
}

/// One constructor's wrapper child laws, extractors, eta law, and the
/// computation pins that make the extractors non-swappable.
fn per_ctor(
    shape: &VariantShape<'_>,
    d: &Desc,
    n: &CoindNames,
    k: usize,
    ctor: &VariantCtorPlan<'_>,
) -> Result<Vec<SurfaceDecl>, ElabError> {
    let name = shape.name;
    let class = classify(name, ctor)?;
    let unit = ident("PUnit.unit");
    let x = ident(&n.lhs);
    let tag = shape.tag(k, ctor.payload_value());
    let hh = ident(&n.hh);

    // The eta law's binders: the codata parameters, the value, this
    // constructor's PAYLOAD binders only (its children are what we extract),
    // and the head hypothesis.
    let payload_binders: Vec<SurfaceBinder> = ctor_binders(ctor, &d.self_ty)
        .into_iter()
        .filter(|b| ctor.payloads().any(|p| p.arg_name == b.name))
        .collect();
    let mut eta_binders = shape.binders.to_vec();
    eta_binders.push(binder(&n.lhs, d.self_ty.clone()));
    eta_binders.extend(payload_binders.clone());
    eta_binders.push(binder(&n.hh, eq(d.head_of(x.clone()), tag.clone())));

    let children: Vec<&ChildPlan<'_>> = ctor.children().collect();
    let m = children.len();

    // The extractor for child `i`, and the value it contributes to the
    // reconstructed constructor call.
    let mut out: Vec<SurfaceDecl> = Vec::new();
    let mut extractor_values: Vec<SurfaceExpr> = Vec::new();
    for (i, c) in children.iter().enumerate() {
        let ex_name = extractor_name(name, ctor, i, m);
        let point = |v: SurfaceExpr| {
            if m == 1 {
                v
            } else {
                inject_sum(i, m, v)
            }
        };
        let (ex_ty, ex_body) = match &c.family {
            // Dependent family: the extractor IS the continuation, pointwise.
            Some(f) => (
                arrow(f.source.clone(), d.self_ty.clone()),
                lam_typed(
                    &n.pos,
                    f.source.clone(),
                    d.child_of(x.clone(), d.cast_of(hh.clone(), point(ident(&n.pos)))),
                ),
            ),
            // Bare child: one value, at this child's canonical position.
            None => (
                d.self_ty.clone(),
                d.child_of(x.clone(), d.cast_of(hh.clone(), point(unit.clone()))),
            ),
        };
        out.push(mk_def(ex_name.clone(), eta_binders.clone(), ex_ty, ex_body));
        let mut call = d.params.clone();
        call.push(x.clone());
        call.extend(payload_binders.iter().map(|b| ident(&b.name)));
        call.push(hh.clone());
        extractor_values.push(plain_app(&ex_name, call));
    }

    // The reconstructed constructor call: payloads as bound, children
    // replaced by their extractors.
    let mut rebuilt_args = d.params.clone();
    {
        let mut ci = 0usize;
        for a in &ctor.args {
            match a {
                crate::codata_variant_plan::ArgPlan::Payload(p) => {
                    rebuilt_args.push(ident(&p.arg_name))
                }
                crate::codata_variant_plan::ArgPlan::Child(_) => {
                    rebuilt_args.push(extractor_values[ci].clone());
                    ci += 1;
                }
            }
        }
    }
    let rebuilt = plain_app(&format!("{name}.{}", ctor.name), rebuilt_args);

    // Wrapper-vocabulary child laws for THIS constructor, over the rebuilt
    // value — the eta proof's children clause is discharged with these.
    for (i, c) in children.iter().enumerate() {
        let law = wchild_name(name, ctor, i, m);
        let mut bs = eta_binders.clone();
        let (extra_binder, point_val, rhs) = match &c.family {
            Some(f) => (
                Some(binder(&n.pos, f.source.clone())),
                ident(&n.pos),
                plain_app_expr(extractor_values[i].clone(), vec![ident(&n.pos)]),
            ),
            None => (None, unit.clone(), extractor_values[i].clone()),
        };
        if let Some(b) = extra_binder {
            bs.push(b);
        }
        let pos = if m == 1 {
            point_val.clone()
        } else {
            inject_sum(i, m, point_val.clone())
        };
        out.push(mk_theorem(
            law,
            bs,
            eq(d.child_of(rebuilt.clone(), pos), rhs),
            ident("rfl"),
        ));
    }

    // The children clause, by position-shape class.
    let obligation = |z: SurfaceExpr| {
        eq(
            d.child_of(x.clone(), d.cast_of(hh.clone(), z.clone())),
            d.child_of(rebuilt.clone(), z),
        )
    };
    let wchild_ref = |i: usize, extra: Vec<SurfaceExpr>| {
        let mut a = d.params.clone();
        a.push(x.clone());
        a.extend(payload_binders.iter().map(|b| ident(&b.name)));
        a.push(hh.clone());
        a.extend(extra);
        plain_app(&wchild_name(name, ctor, i, m), a)
    };
    let hc = match &class {
        PosShape::Empty => lam_typed(
            &n.pos,
            d.pos_at(unit.clone(), tag.clone()),
            at_app(
                "PEmpty.rec",
                vec![lam(&["_"], obligation(ident(&n.pos))), ident(&n.pos)],
            ),
        ),
        PosShape::Single(c) => {
            let arg = match &c.family {
                Some(_) => vec![ident(&n.pos)],
                None => Vec::new(),
            };
            lam_one(&n.pos, plain_app("Eq.symm", vec![wchild_ref(0, arg)]))
        }
        PosShape::Fold(cs) => lam_one(
            &n.pos,
            sum_rec_tower(
                cs.len(),
                0,
                &n.scrut,
                &obligation,
                &|i| plain_app("Eq.symm", vec![wchild_ref(i, Vec::new())]),
                ident(&n.pos),
            ),
        ),
    };

    // The eta law itself.
    out.push(mk_theorem(
        format!("{name}.{}_eta", ctor.name),
        eta_binders.clone(),
        eq(x.clone(), rebuilt.clone()),
        {
            let mut a = d.params.clone();
            a.extend([x.clone(), rebuilt.clone(), hh.clone(), hc]);
            plain_app(&format!("{name}.ext"), a)
        },
    ));

    // Computation pins: the extractor applied to a REAL `Cₖ` returns that
    // constructor's own argument. Without these a swapped k-fold branch still
    // kernel-checks (both children have the same type).
    for (i, c) in children.iter().enumerate() {
        let mut bs = shape.binders.to_vec();
        bs.extend(ctor_binders(ctor, &d.self_ty));
        let mut call = d.params.clone();
        call.push(ctor_call(name, ctor, &d.params));
        call.extend(payload_binders.iter().map(|b| ident(&b.name)));
        call.push(ident("rfl"));
        let applied = plain_app(&extractor_name(name, ctor, i, m), call);
        let (lhs, rhs, bs) = match &c.family {
            Some(f) => {
                let mut bs = bs;
                bs.push(binder(&n.pos, f.source.clone()));
                (
                    plain_app_expr(applied, vec![ident(&n.pos)]),
                    plain_app(&c.arg_name, vec![ident(&n.pos)]),
                    bs,
                )
            }
            None => (applied, ident(&c.arg_name), bs),
        };
        out.push(mk_theorem(
            format!("{}_compute", extractor_name(name, ctor, i, m)),
            bs,
            eq(lhs, rhs),
            ident("rfl"),
        ));
    }

    Ok(out)
}

/// The right-nested `Sum` of `count` copies of `PUnit.{1}` — the position
/// type of an all-bare k-fold constructor, and of each of its tails.
fn punit_sum(count: usize) -> SurfaceExpr {
    nest_right("Sum", vec![punit_ty(); count]).unwrap_or_else(punit_ty)
}

/// Re-inject a value sitting at nesting depth `offset` back into the full
/// position type: `Sum.inr` applied `offset` times.
fn wrap_inr(offset: usize, v: SurfaceExpr) -> SurfaceExpr {
    (0..offset).fold(v, |e, _| plain_app("Sum.inr", vec![e]))
}

/// The dependent `Sum.rec` tower discharging an all-bare k-fold position's
/// children clause. Motive is the obligation itself; leaf `i` is `branch(i)`.
///
/// Right-nested to match [`inject_sum`] (`Sum Q₀ (Sum Q₁ Q₂)`), so `m = 2` is
/// one `Sum.rec` and each further child adds one nesting level whose motive is
/// the obligation composed with the `Sum.inr`s already consumed.
///
/// The leaf is `branch(i)`, whose type mentions the CANONICAL position
/// (`Sum.inr…(Sum.inl PUnit.unit)`) while the branch binder is an arbitrary
/// `PUnit`. Those are definitionally equal by the kernel's unit eta, which is
/// why no `iunit_eq` rewrite appears here — MEASURED against the scaffolded
/// alternative, which also checks but is dead weight
/// (`designs/2026-08-28-variant-codata-surface.md` §9).
fn sum_rec_tower(
    m: usize,
    offset: usize,
    scrut_base: &str,
    obligation: &dyn Fn(SurfaceExpr) -> SurfaceExpr,
    branch: &dyn Fn(usize) -> SurfaceExpr,
    scrut: SurfaceExpr,
) -> SurfaceExpr {
    if offset + 1 == m {
        // Last summand: the tail type is that child's own position, and the
        // scrutinee IS it.
        return branch(offset);
    }
    let z = format!("{scrut_base}{offset}");
    let tail = format!("{scrut_base}t{offset}");
    let tail_ty = punit_sum(m - offset - 1);
    at_app(
        "Sum.rec",
        vec![
            punit_ty(),
            tail_ty.clone(),
            lam_typed(
                &z,
                punit_sum(m - offset),
                obligation(wrap_inr(offset, ident(&z))),
            ),
            lam(&["_"], branch(offset)),
            lam_typed(
                &tail,
                tail_ty,
                sum_rec_tower(m, offset + 1, scrut_base, obligation, branch, ident(&tail)),
            ),
            scrut,
        ],
    )
}

// ────────────────────────────────────────────────────────────────────────
// The N-ary case-analysis tower (VC-6b).
//
// `T.ext` and the eta laws answer "given that x's head is Cₖ's tag, what is
// x?". This answers the prior question — "which constructor IS it?" — with
// no hypothesis at all: `T.cases x : T.CasesP x`, an n-way disjunction of
// existentials, one disjunct per constructor.
//
// It is a consequence of the eta laws plus one fact about `Sum`: a value of
// a right-nested n-fold `Sum` is at exactly one injection. Both halves are
// generated, so the tower needs nothing hand-written.
// ────────────────────────────────────────────────────────────────────────

/// Type of the shape tail from depth `d` on: `Sum P_d (Sum … P_{n-1})`.
fn tail_ty(shape: &VariantShape<'_>, d: usize) -> SurfaceExpr {
    let parts: Vec<SurfaceExpr> = shape.ctors[d..]
        .iter()
        .map(|c| c.payload_ty.clone())
        .collect();
    // `d` always indexes a real constructor, so `parts` is never empty and
    // `nest_right` never returns `None`; `punit_ty` is an unreachable
    // fallback kept only to avoid a panic path.
    nest_right("Sum", parts).unwrap_or_else(punit_ty)
}

/// `Or.inr`ᵏ (`Or.inl` …) — inject a disjunct into the right-nested `Or`.
fn inject_or(k: usize, n: usize, v: SurfaceExpr) -> SurfaceExpr {
    if n <= 1 {
        return v;
    }
    if k == 0 {
        return plain_app("Or.inl", vec![v]);
    }
    plain_app("Or.inr", vec![inject_or(k - 1, n - 1, v)])
}

/// One constructor argument's TYPE, as the `∃` over it must spell it.
fn arg_ty(a: &crate::codata_variant_plan::ArgPlan<'_>, self_ty: &SurfaceExpr) -> SurfaceExpr {
    use crate::codata_variant_plan::ArgPlan;
    match a {
        ArgPlan::Payload(p) => p.ty.clone(),
        ArgPlan::Child(c) => match &c.family {
            Some(f) => arrow(f.source.clone(), self_ty.clone()),
            None => self_ty.clone(),
        },
    }
}

/// The witness for argument `i`: a payload is its own bound binder, a child
/// is the extractor that recovers it.
fn arg_witness(
    shape: &VariantShape<'_>,
    d: &Desc,
    n: &CoindNames,
    ctor: &VariantCtorPlan<'_>,
    payload_binders: &[SurfaceBinder],
    i: usize,
) -> SurfaceExpr {
    use crate::codata_variant_plan::ArgPlan;
    let m = ctor.children().count();
    match &ctor.args[i] {
        ArgPlan::Payload(p) => ident(&p.arg_name),
        ArgPlan::Child(_) => {
            // Which child index is this, counting only children?
            let ci = ctor.args[..i]
                .iter()
                .filter(|a| matches!(a, ArgPlan::Child(_)))
                .count();
            let mut call = d.params.clone();
            call.push(ident(&n.lhs));
            call.extend(payload_binders.iter().map(|b| ident(&b.name)));
            call.push(ident(&n.hh));
            plain_app(&extractor_name(shape.name, ctor, ci, m), call)
        }
    }
}

/// `T.CasesP`, `T.sumCases`, the per-constructor `T.cases_Cₖ` (with the
/// hoisted inner existentials each needs), and `T.cases` itself.
fn cases_tower(shape: &VariantShape<'_>, d: &Desc, n: &CoindNames) -> Vec<SurfaceDecl> {
    let name = shape.name;
    let nctors = shape.ctors.len();
    let x = ident(&n.lhs);
    let mut out: Vec<SurfaceDecl> = Vec::new();

    // ── T.CasesP: the n-way disjunction of existentials.
    let disjunct = |ctor: &VariantCtorPlan<'_>| {
        let mut body = eq(x.clone(), ctor_call(name, ctor, &d.params));
        for a in ctor.args.iter().rev() {
            body = plain_app(
                "Exists",
                vec![lam_typed(a.arg_name(), arg_ty(a, &d.self_ty), body)],
            );
        }
        body
    };
    let cases_p_body = nest_right("Or", shape.ctors.iter().map(disjunct).collect::<Vec<_>>())
        .unwrap_or_else(|| ident("True"));
    let mut cp_binders = shape.binders.to_vec();
    cp_binders.push(binder(&n.lhs, d.self_ty.clone()));
    out.push(mk_def(
        format!("{name}.CasesP"),
        cp_binders,
        prop_universe(),
        cases_p_body,
    ));

    let cases_p_at = |v: SurfaceExpr| d.member("CasesP", vec![v]);

    // ── T.sumCases: a value of `Sum X Y` is at one of the two injections,
    // and the branch LEARNS the equation. `Sum.casesOn` alone would not do:
    // the branches must carry `v = Sum.inl x` to rebuild the head equation
    // the eta laws need, so the motive is `fun w => w = v → C` applied at
    // `rfl` — the standard trick for turning a recursor into a case
    // analysis that remembers its scrutinee.
    if nctors > 1 {
        let (bx, by, bv, bc, bl, br) = ("X", "Y", "v", "C", "hl", "hr");
        let sum_xy = plain_app("Sum", vec![ident(bx), ident(by)]);
        out.push(mk_theorem(
            format!("{name}.sumCases"),
            vec![implicit(bx, ident("Type")), implicit(by, ident("Type"))],
            pi(
                vec![binder(bv, sum_xy.clone()), binder(bc, prop_universe())],
                arrow(
                    pi(
                        vec![binder("xa", ident(bx))],
                        arrow(
                            eq(ident(bv), plain_app("Sum.inl", vec![ident("xa")])),
                            ident(bc),
                        ),
                    ),
                    arrow(
                        pi(
                            vec![binder("ya", ident(by))],
                            arrow(
                                eq(ident(bv), plain_app("Sum.inr", vec![ident("ya")])),
                                ident(bc),
                            ),
                        ),
                        ident(bc),
                    ),
                ),
            ),
            lam(
                &[bv, bc, bl, br],
                at_app(
                    "Sum.rec",
                    vec![
                        ident(bx),
                        ident(by),
                        lam_typed("w", sum_xy, arrow(eq(ident("w"), ident(bv)), ident(bc))),
                        lam(
                            &["xa", "he"],
                            plain_app(
                                bl,
                                vec![ident("xa"), plain_app("Eq.symm", vec![ident("he")])],
                            ),
                        ),
                        lam(
                            &["ya", "he"],
                            plain_app(
                                br,
                                vec![ident("ya"), plain_app("Eq.symm", vec![ident("he")])],
                            ),
                        ),
                        ident(bv),
                        ident("rfl"),
                    ],
                ),
            ),
        ));
    }

    // ── per-constructor `T.cases_Cₖ`, plus the hoisted inner existentials.
    //
    // The nesting is hoisted one lemma per level rather than written as one
    // term: a doubly-nested `Exists.intro` gives the elaborator no way to
    // pin the inner motive (the nested-Exists lesson, ITreeEco:2990-2993).
    for (k, ctor) in shape.ctors.iter().enumerate() {
        let payload_binders: Vec<SurfaceBinder> = ctor_binders(ctor, &d.self_ty)
            .into_iter()
            .filter(|b| ctor.payloads().any(|p| p.arg_name == b.name))
            .collect();
        let mut lemma_binders = shape.binders.to_vec();
        lemma_binders.push(binder(&n.lhs, d.self_ty.clone()));
        lemma_binders.extend(payload_binders.clone());
        lemma_binders.push(binder(
            &n.hh,
            eq(d.head_of(x.clone()), shape.tag(k, ctor.payload_value())),
        ));
        let call_lemma = |suffix: &str| {
            let mut a = d.params.clone();
            a.push(x.clone());
            a.extend(payload_binders.iter().map(|b| ident(&b.name)));
            a.push(ident(&n.hh));
            plain_app(&format!("{name}.{suffix}"), a)
        };
        let witnesses: Vec<SurfaceExpr> = (0..ctor.args.len())
            .map(|i| arg_witness(shape, d, n, ctor, &payload_binders, i))
            .collect();
        let eta = call_lemma(&format!("{}_eta", ctor.name));

        // `∃ a_i … a_{m-1}, x = Cₖ w₀ … w_{i-1} a_i …` — the statement of
        // the level-`i` inner lemma.
        let inner_stmt = |i: usize| {
            let mut applied = d.params.clone();
            for (j, a) in ctor.args.iter().enumerate() {
                applied.push(if j < i {
                    witnesses[j].clone()
                } else {
                    ident(a.arg_name())
                });
            }
            let mut body = eq(
                x.clone(),
                plain_app(&format!("{name}.{}", ctor.name), applied),
            );
            for a in ctor.args[i..].iter().rev() {
                body = plain_app(
                    "Exists",
                    vec![lam_typed(a.arg_name(), arg_ty(a, &d.self_ty), body)],
                );
            }
            body
        };

        let m = ctor.args.len();
        for i in (1..m).rev() {
            let proof = if i + 1 == m {
                plain_app("Exists.intro", vec![witnesses[i].clone(), eta.clone()])
            } else {
                plain_app(
                    "Exists.intro",
                    vec![
                        witnesses[i].clone(),
                        call_lemma(&format!("cases_{}_inner{}", ctor.name, i + 1)),
                    ],
                )
            };
            out.push(mk_theorem(
                format!("{name}.cases_{}_inner{i}", ctor.name),
                lemma_binders.clone(),
                inner_stmt(i),
                proof,
            ));
        }

        let payload = if m == 0 {
            eta.clone()
        } else if m == 1 {
            plain_app("Exists.intro", vec![witnesses[0].clone(), eta.clone()])
        } else {
            plain_app(
                "Exists.intro",
                vec![
                    witnesses[0].clone(),
                    call_lemma(&format!("cases_{}_inner1", ctor.name)),
                ],
            )
        };
        out.push(mk_theorem(
            format!("{name}.cases_{}", ctor.name),
            lemma_binders,
            cases_p_at(x.clone()),
            inject_or(k, nctors, payload),
        ));
    }

    // ── T.cases: dispatch on the head through the `Sum` tower.
    let mut cases_binders = shape.binders.to_vec();
    cases_binders.push(binder(&n.lhs, d.self_ty.clone()));
    let goal = cases_p_at(x.clone());
    let body = if nctors == 1 {
        // No `Sum` at all: the head IS the single constructor's payload, so
        // the tag equation is `rfl`.
        let ctor = &shape.ctors[0];
        let mut a = d.params.clone();
        a.push(x.clone());
        a.extend(
            (0..ctor.payload_count())
                .map(|i| projection_path_of(&d.head_of(x.clone()), i, ctor.payload_count())),
        );
        a.push(ident("rfl"));
        plain_app(&format!("{name}.cases_{}", shape.ctors[0].name), a)
    } else {
        dispatch(shape, d, n, 0, d.head_of(x.clone()), &[], &goal)
    };
    out.push(mk_theorem(
        format!("{name}.cases"),
        cases_binders,
        goal,
        body,
    ));
    out
}

/// The projection chain recovering payload `i` of `k` from an EXPRESSION
/// (the plan's `projection_path` takes a name).
fn projection_path_of(base: &SurfaceExpr, i: usize, k: usize) -> SurfaceExpr {
    use clean_parser::Projection;
    let mut e = base.clone();
    for _ in 0..i {
        e = SurfaceExpr::Proj(Span::dummy(), Box::new(e), Projection::Index(2));
    }
    if i + 1 < k {
        e = SurfaceExpr::Proj(Span::dummy(), Box::new(e), Projection::Index(1));
    }
    e
}

/// Fold an accumulated chain of `Sum.inr` steps plus a leaf equation into
/// `T.head ps x = tagₖ`.
///
/// `chain[j]` is `scrut_{j} = Sum.inr scrut_{j+1}` and `leaf` is the final
/// `scrut_L = Sum.inl p` (or `= Sum.inr p` for the last constructor). Each
/// step wraps the accumulated equation in `Sum.inr` and prepends its own,
/// innermost first.
fn fold_head_eq(shape: &VariantShape<'_>, chain: &[SurfaceExpr], leaf: SurfaceExpr) -> SurfaceExpr {
    let mut acc = leaf;
    for (depth, step) in chain.iter().enumerate().rev() {
        let inner = tail_ty(shape, depth + 1);
        acc = plain_app(
            "Eq.trans",
            vec![
                step.clone(),
                plain_app(
                    "congrArg",
                    vec![
                        lam_typed(
                            "zw",
                            inner.clone(),
                            at_app(
                                "Sum.inr",
                                vec![
                                    shape.ctors[depth].payload_ty.clone(),
                                    inner.clone(),
                                    ident("zw"),
                                ],
                            ),
                        ),
                        acc,
                    ],
                ),
            ],
        );
    }
    acc
}

/// The `T.cases` dispatch, one `T.sumCases` per `Sum` level.
///
/// Two things here are easy to get wrong and were, first time round:
///
/// - **The branch hypothesis must be named per LEVEL.** Every level binds
///   the equation its branch learns, and the chain accumulates those across
///   levels; one shared name lets an inner binder shadow the outer one, so
///   the fold silently reuses the wrong equation and the tag comes out at
///   the wrong depth.
/// - **The last constructor's leaf takes the OUTER chain**, not the chain
///   extended with its own step: `fold_head_eq` appends the leaf equation
///   itself, so passing the extended chain counts that step twice.
///
/// Both faults produce the same symptom — a `Sum` injection at the wrong
/// depth, reported as a discriminant mismatch — which is why they are
/// written down rather than merely fixed.
fn dispatch(
    shape: &VariantShape<'_>,
    d: &Desc,
    n: &CoindNames,
    level: usize,
    scrut: SurfaceExpr,
    chain: &[SurfaceExpr],
    goal: &SurfaceExpr,
) -> SurfaceExpr {
    let name = shape.name;
    let nctors = shape.ctors.len();
    let pname = format!("{}{level}", n.scrut);
    let sname = format!("{}s{level}", n.scrut);
    let hname = format!("{}h{level}", n.scrut);

    let leaf = |k: usize, p: &str, upto: &[SurfaceExpr]| {
        let ctor = &shape.ctors[k];
        let mut a = d.params.clone();
        a.push(ident(&n.lhs));
        a.extend(
            (0..ctor.payload_count())
                .map(|i| projection_path_of(&ident(p), i, ctor.payload_count())),
        );
        a.push(fold_head_eq(shape, upto, ident(&hname)));
        plain_app(&format!("{name}.cases_{}", ctor.name), a)
    };

    let inl_branch = lam(&[&pname, &hname], leaf(level, &pname, chain));
    let inr_branch = {
        let inner = if level + 2 == nctors {
            // The tail is the LAST constructor's payload: no further `Sum`,
            // and this level's own equation IS the leaf.
            leaf(nctors - 1, &sname, chain)
        } else {
            let mut c = chain.to_vec();
            c.push(ident(&hname));
            dispatch(shape, d, n, level + 1, ident(&sname), &c, goal)
        };
        lam(&[&sname, &hname], inner)
    };
    plain_app(
        &format!("{name}.sumCases"),
        vec![scrut, goal.clone(), inl_branch, inr_branch],
    )
}
