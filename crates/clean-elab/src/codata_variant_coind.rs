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
//!
//! **No shape in VC-1's envelope is refused here.** An earlier version
//! refused a constructor with several recursive arguments where one was an
//! indexed family, on the grounds that the shape had no worked precedent.
//! Measured, that shape was always fine, and the refusal was hiding two
//! unrelated generator bugs in far more ordinary shapes — a lone constructor
//! whose first argument is recursive (`| C : T → T`), and a payload after a
//! child (`| C : T A → A → T A`). Both are fixed; see
//! `designs/2026-08-28-variant-codata-surface.md` §12 for the mechanisms and
//! for the one exotic residue that IS still refused by name. The lesson is
//! recorded there too: when a generator fails on a shape, map the
//! neighbouring shapes before theorising about the one in front of you.

use crate::codata_cmd::GlobalPath;
use crate::codata_cmd::{
    affix_name, arrow, at_app, child_name, ident, lam, mentions, mk_def, mk_theorem, plain_app,
    punit_ty, punit_ty_p, surface_binder, type_u, CodataIdentifier,
};
use crate::codata_variant::unsupported;
use crate::codata_variant_generate::{binder, ctor_binders, ctor_call, eq, lam_one, lam_typed};
use crate::codata_variant_plan::{
    inject_sum, nest_right, ChildPlan, VariantCtorPlan, VariantShape,
};
use crate::ElabError;
use clean_parser::{
    Span, SurfaceBinder, SurfaceBinderInfo, SurfaceDecl, SurfaceExpr, SurfaceName, UniverseExpr,
};

/// `Prop`, as a sort.
fn prop_universe() -> SurfaceExpr {
    SurfaceExpr::Universe(Span::dummy(), UniverseExpr::Prop)
}

/// An implicit binder `{name : ty}`.
fn implicit(name: impl CodataIdentifier, ty: SurfaceExpr) -> SurfaceBinder {
    SurfaceBinder {
        ty: Some(Box::new(ty)),
        ..surface_binder(name, None, SurfaceBinderInfo::Implicit)
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
    idx: SurfaceName,
    lhs: SurfaceName,
    rhs: SurfaceName,
    heq: SurfaceName,
    pos: SurfaceName,
    m1: SurfaceName,
    m2: SurfaceName,
    rel: SurfaceName,
    hyp: SurfaceName,
    val: SurfaceName,
    e1: SurfaceName,
    e2: SurfaceName,
    scrut: SurfaceName,
    hh: SurfaceName,
    hc: SurfaceName,
}

impl CoindNames {
    fn mint(shape: &VariantShape<'_>) -> Self {
        let g = &shape.gen_names;
        let mut used: Vec<SurfaceName> = shape.binders.iter().map(|b| b.name.clone()).collect();
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
            let mut candidate = SurfaceName::component(base, false);
            let mut i = 0usize;
            while used.contains(&candidate) {
                candidate = SurfaceName::component(format!("{base}{i}"), false);
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
    name: SurfaceName,
    /// The declared universe parameter, so every pinned level in this tier
    /// (`PUnit` indices, `Type` in `T.sumCases`) is spelled against it.
    poly: Option<SurfaceName>,
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
            name: name.clone(),
            poly: shape.poly.cloned(),
            shape_f: plain_app(child_name(name, "shapeF"), params.clone()),
            pos_f: plain_app(child_name(name, "posF"), params.clone()),
            tgt_f: plain_app(child_name(name, "tgtF"), params.clone()),
            self_ty: plain_app(name, params.clone()),
            params,
        }
    }

    /// `T.<suffix> ps extra…` — one of the generated family's members, applied
    /// to the codata parameters and then to `extra`.
    fn member(&self, suffix: &'static str, extra: Vec<SurfaceExpr>) -> SurfaceExpr {
        let mut args = self.params.clone();
        args.extend(extra);
        plain_app(child_name(&self.name, suffix), args)
    }

    /// `Codata.IMIntl (T.shapeF ps) (T.posF ps) (T.tgtF ps) j`
    fn imintl(&self, j: SurfaceExpr) -> SurfaceExpr {
        plain_app(
            GlobalPath("Codata.IMIntl"),
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
            GlobalPath("Codata.IMhead"),
            vec![
                punit_ty_p(self.poly.as_ref()),
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
            GlobalPath("Codata.IMchild"),
            vec![
                punit_ty_p(self.poly.as_ref()),
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
        which: &'static str,
        j: SurfaceExpr,
        l: SurfaceExpr,
        h: SurfaceExpr,
        e: SurfaceExpr,
        b: SurfaceExpr,
    ) -> SurfaceExpr {
        at_app(
            which,
            vec![
                punit_ty_p(self.poly.as_ref()),
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

/// Classify. Every shape VC-1 admits is buildable — there is no refusal here
/// any more, and the one that used to sit here named the wrong shape entirely
/// (see `designs/2026-08-28-variant-codata-surface.md` §12).
fn classify<'a, 'b>(ctor: &'a VariantCtorPlan<'b>) -> PosShape<'a, 'b> {
    let children: Vec<&ChildPlan<'_>> = ctor.children().collect();
    match children.len() {
        0 => PosShape::Empty,
        1 => PosShape::Single(children[0]),
        _ => PosShape::Fold(children),
    }
}

/// The name of a constructor's `i`-th child extractor.
fn extractor_name(
    shape_name: &SurfaceName,
    ctor: &VariantCtorPlan<'_>,
    i: usize,
    m: usize,
) -> SurfaceName {
    if m == 1 {
        shape_name.append(&affix_name(ctor.name, "", "Child"))
    } else {
        shape_name.append(&affix_name(ctor.name, "", &format!("Child{i}")))
    }
}

/// The wrapper-vocabulary child law's name for position `i`.
fn wchild_name(
    shape_name: &SurfaceName,
    ctor: &VariantCtorPlan<'_>,
    i: usize,
    m: usize,
) -> SurfaceName {
    if m <= 1 {
        shape_name.append(&affix_name(ctor.name, "wchild_", ""))
    } else {
        shape_name.append(&affix_name(ctor.name, "wchild_", &format!("_{i}")))
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
    out.extend(cases_tower(shape, &d, &n)?);
    Ok(out)
}

/// `T.child` and `T.cast`: the observation wrappers every statement below is
/// phrased in. Without them each obligation would carry the full six-argument
/// `@Codata.IMchild` spelling, and the `Eq.rec` motives would not align.
fn wrappers(shape: &VariantShape<'_>, d: &Desc, n: &CoindNames) -> Vec<SurfaceDecl> {
    let name = shape.name;
    let unit = ident(GlobalPath("PUnit.unit"));
    let x = ident(&n.lhs);

    let child = {
        let mut bs = shape.binders.to_vec();
        bs.push(binder(&n.lhs, d.self_ty.clone()));
        bs.push(binder(&n.pos, d.pos_at(unit.clone(), d.head_of(x.clone()))));
        mk_def(
            child_name(name, "child"),
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
            child_name(name, "cast"),
            bs,
            d.pos_at(unit.clone(), ident(&n.m1)),
            plain_app(
                "cast",
                vec![
                    plain_app(
                        "congrArg",
                        vec![
                            d.member("posF", vec![unit.clone()]),
                            plain_app(GlobalPath("Eq.symm"), vec![ident(&n.heq)]),
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
    let unit = ident(GlobalPath("PUnit.unit"));
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
            GlobalPath("And"),
            vec![
                eq(hx.clone(), hy.clone()),
                pi(
                    vec![binder(&n.heq, eq(hx.clone(), hy.clone())), inner_pos],
                    children,
                ),
            ],
        );
        mk_def(
            child_name(name, "ExtQ"),
            shape.binders.to_vec(),
            pi(
                vec![binder(&n.idx, punit_ty_p(d.poly.as_ref()))],
                arrow(
                    d.imintl(j.clone()),
                    arrow(d.imintl(j.clone()), prop_universe()),
                ),
            ),
            SurfaceExpr::Lambda(
                Span::dummy(),
                vec![
                    surface_binder(&n.idx, None, SurfaceBinderInfo::Explicit),
                    surface_binder(&n.lhs, None, SurfaceBinderInfo::Explicit),
                    surface_binder(&n.rhs, None, SurfaceBinderInfo::Explicit),
                ],
                Box::new(body),
            ),
        )
    };

    let ext_q_app = |a: SurfaceExpr, b: SurfaceExpr, c: SurfaceExpr| {
        let mut args = d.params.clone();
        args.extend([a, b, c]);
        plain_app(child_name(name, "ExtQ"), args)
    };
    let ext_q_partial = || plain_app(child_name(name, "ExtQ"), d.params.clone());

    // T.ExtQ_hhead : ∀ j m1 m2, ExtQ j m1 m2 → IMhead j m1 = IMhead j m2
    let ext_q_hhead = mk_theorem(
        child_name(name, "ExtQ_hhead"),
        shape.binders.to_vec(),
        pi(
            vec![
                binder(&n.idx, punit_ty_p(d.poly.as_ref())),
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
            &[
                SurfaceName::generated_path("_"),
                SurfaceName::generated_path("_"),
                SurfaceName::generated_path("_"),
                n.rel.clone(),
            ],
            plain_app(GlobalPath("And.left"), vec![ident(&n.rel)]),
        ),
    );

    // T.ExtQ_of_eq : x = y → ExtQ j x y
    let ext_q_of_eq = {
        let mut bs = shape.binders.to_vec();
        bs.push(implicit(&n.idx, punit_ty_p(d.poly.as_ref())));
        bs.push(implicit(&n.lhs, d.imintl(j.clone())));
        bs.push(implicit(&n.rhs, d.imintl(j.clone())));
        bs.push(binder(&n.hyp, eq(x.clone(), y.clone())));
        mk_theorem(
            child_name(name, "ExtQ_of_eq"),
            bs,
            ext_q_app(j.clone(), x.clone(), y.clone()),
            at_app(
                "Eq.rec",
                vec![
                    d.imintl(j.clone()),
                    x.clone(),
                    lam(
                        &[n.val.clone(), SurfaceName::generated_path("_")],
                        ext_q_app(j.clone(), x.clone(), ident(&n.val)),
                    ),
                    plain_app(
                        GlobalPath("And.intro"),
                        vec![
                            ident(GlobalPath("rfl")),
                            lam(&["_", "_"], ident(GlobalPath("rfl"))),
                        ],
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
            child_name(name, "ext_unwrap"),
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
            ident(GlobalPath("rfl")),
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
            child_name(name, "ch_cast_irrel"),
            bs,
            eq(
                d.child_of(x.clone(), d.cast_of(ident(&n.e1), ident(&n.pos))),
                d.child_of(x.clone(), d.cast_of(ident(&n.e2), ident(&n.pos))),
            ),
            ident(GlobalPath("rfl")),
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
        let hhead_partial = plain_app(child_name(name, "ExtQ_hhead"), d.params.clone());
        let of_eq_partial = plain_app(child_name(name, "ExtQ_of_eq"), d.params.clone());
        // hchild is supplied INLINE. Naming it and reapplying does not
        // typecheck: the relation's children clause is ∀-quantified over the
        // head proof, so the argument must be built where that proof is bound
        // (the reapplication lesson, ITreeEco.lean:2897-2906).
        let hchild = SurfaceExpr::Lambda(
            Span::dummy(),
            vec![
                surface_binder(&n.idx, None, SurfaceBinderInfo::Explicit),
                surface_binder(&n.m1, None, SurfaceBinderInfo::Explicit),
                surface_binder(&n.m2, None, SurfaceBinderInfo::Explicit),
                surface_binder(&n.rel, None, SurfaceBinderInfo::Explicit),
                surface_binder(&n.pos, None, SurfaceBinderInfo::Explicit),
            ],
            Box::new(plain_app_expr(
                of_eq_partial,
                vec![plain_app(
                    GlobalPath("And.right"),
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
            GlobalPath("And.intro"),
            vec![
                e.clone(),
                SurfaceExpr::Lambda(
                    Span::dummy(),
                    vec![
                        surface_binder(&n.e1, None, SurfaceBinderInfo::Explicit),
                        surface_binder(&n.pos, None, SurfaceBinderInfo::Explicit),
                    ],
                    Box::new(plain_app(
                        "Eq.trans",
                        vec![
                            {
                                let mut a = d.params.clone();
                                a.extend([x.clone(), y.clone(), ident(&n.e1), b.clone()]);
                                plain_app(child_name(name, "ext_unwrap"), a)
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
                                        plain_app(child_name(name, "ch_cast_irrel"), a)
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
            child_name(name, "ext"),
            bs,
            eq(x.clone(), y.clone()),
            at_app(
                "Codata.iM_coind",
                vec![
                    punit_ty_p(d.poly.as_ref()),
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
    let class = classify(ctor);
    let unit = ident(GlobalPath("PUnit.unit"));
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
    let rebuilt = plain_app(name.append(ctor.name), rebuilt_args);

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
            ident(GlobalPath("rfl")),
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
        plain_app(wchild_name(name, ctor, i, m), a)
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
            lam_one(
                &n.pos,
                plain_app(GlobalPath("Eq.symm"), vec![wchild_ref(0, arg)]),
            )
        }
        PosShape::Fold(cs) => {
            let doms: Vec<SurfaceExpr> = cs.iter().map(|c| c.domain_in_args()).collect();
            let families: Vec<bool> = cs.iter().map(|c| c.family.is_some()).collect();
            lam_one(
                &n.pos,
                sum_rec_tower(
                    &doms,
                    &families,
                    0,
                    &n.scrut,
                    &obligation,
                    &|i, at| {
                        plain_app(
                            GlobalPath("Eq.symm"),
                            vec![wchild_ref(i, at.into_iter().collect())],
                        )
                    },
                    ident(&n.pos),
                ),
            )
        }
    };

    // The eta law itself.
    out.push(mk_theorem(
        name.append(&affix_name(ctor.name, "", "_eta")),
        eta_binders.clone(),
        eq(x.clone(), rebuilt.clone()),
        {
            let mut a = d.params.clone();
            a.extend([x.clone(), rebuilt.clone(), hh.clone(), hc]);
            plain_app(child_name(name, "ext"), a)
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
        call.push(ident(GlobalPath("rfl")));
        let applied = plain_app(extractor_name(name, ctor, i, m), call);
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
            affix_name(&extractor_name(name, ctor, i, m), "", "_compute"),
            bs,
            eq(lhs, rhs),
            ident(GlobalPath("rfl")),
        ));
    }

    Ok(out)
}

/// Re-inject a value sitting at nesting depth `offset` back into the full
/// position type: `Sum.inr` applied `offset` times.
fn wrap_inr(offset: usize, v: SurfaceExpr) -> SurfaceExpr {
    (0..offset).fold(v, |e, _| plain_app(GlobalPath("Sum.inr"), vec![e]))
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
    doms: &[SurfaceExpr],
    families: &[bool],
    offset: usize,
    scrut_base: &SurfaceName,
    obligation: &dyn Fn(SurfaceExpr) -> SurfaceExpr,
    branch: &dyn Fn(usize, Option<SurfaceExpr>) -> SurfaceExpr,
    scrut: SurfaceExpr,
) -> SurfaceExpr {
    let m = doms.len();
    if offset + 1 == m {
        return branch(offset, families[offset].then(|| scrut.clone()));
    }
    let z = affix_name(scrut_base, "", &format!("{offset}"));
    let tail = affix_name(scrut_base, "", &format!("t{offset}"));
    let here = affix_name(scrut_base, "", &format!("a{offset}"));
    let tail_ty = dom_sum(&doms[offset + 1..]);
    at_app(
        GlobalPath("Sum.rec"),
        vec![
            doms[offset].clone(),
            tail_ty.clone(),
            lam_typed(
                &z,
                dom_sum(&doms[offset..]),
                obligation(wrap_inr(offset, ident(&z))),
            ),
            // A bare child's binder is a `PUnit` nothing reads; an indexed
            // family's is the index its child law is stated at, so it must be
            // bound and passed on rather than discarded.
            if families[offset] {
                lam_typed(
                    &here,
                    doms[offset].clone(),
                    branch(offset, Some(ident(&here))),
                )
            } else {
                lam(&["_"], branch(offset, None))
            },
            lam_typed(
                &tail,
                tail_ty,
                sum_rec_tower(
                    doms,
                    families,
                    offset + 1,
                    scrut_base,
                    obligation,
                    branch,
                    ident(&tail),
                ),
            ),
            scrut,
        ],
    )
}

/// The right-nested `Sum` of a child-domain list.
///
/// Callers always pass a non-empty slice (a k-fold constructor has at least
/// two children), so the fallback is unreachable; it is spelled `PUnit.{1}`
/// rather than threaded through `poly` on that ground alone. If a caller ever
/// does pass an empty slice under `codata T.{u}`, the level would be wrong —
/// hence the debug assertion.
fn dom_sum(doms: &[SurfaceExpr]) -> SurfaceExpr {
    debug_assert!(!doms.is_empty(), "dom_sum: empty domain list");
    nest_right(GlobalPath("Sum"), doms.to_vec()).unwrap_or_else(punit_ty)
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
    nest_right(GlobalPath("Sum"), parts).unwrap_or_else(|| punit_ty_p(shape.poly))
}

/// `Or.inr`ᵏ (`Or.inl` …) — inject a disjunct into the right-nested `Or`.
fn inject_or(k: usize, n: usize, v: SurfaceExpr) -> SurfaceExpr {
    if n <= 1 {
        return v;
    }
    if k == 0 {
        return plain_app(GlobalPath("Or.inl"), vec![v]);
    }
    plain_app(GlobalPath("Or.inr"), vec![inject_or(k - 1, n - 1, v)])
}

/// The BINDER of an existentially quantified constructor argument, at
/// quantification level `i`: its name and its type.
///
/// Existential binders take the plan's ALTERNATE names, never the
/// constructor's primary argument names, and that is a correctness fix, not
/// cosmetics. The proof of `T.cases_Cₖ_innerᵢ` places the witnesses for the
/// arguments BEFORE `i` inside these binders, and a witness is an extractor
/// application carrying every payload binder of the enclosing lemma. If the
/// existential rebinds a payload under its primary name it CAPTURES that
/// payload inside the witness: the extractor then receives the bound
/// variable where the lemma's binder was meant, and `hh`'s type no longer
/// matches. That is what made every constructor with a payload AFTER a child
/// fail (`| C : T A → A → T A`), as an `fvar` mismatch two indices wide.
///
/// Renaming forces an indexed family's domain to be re-spelled to match.
/// `FamilyPlan` carries `source` (primary names) and `in_alt` (alternate),
/// and which is in scope depends on whether the payloads that domain
/// mentions are themselves existentially bound here (`>= i`, alternate) or
/// bound by the enclosing lemma (`< i`, primary). A domain mentioning
/// payloads on BOTH sides has no single correct spelling; it is refused by
/// name rather than mis-spelled.
fn ex_binder(
    shape_name: &SurfaceName,
    ctor: &VariantCtorPlan<'_>,
    j: usize,
    i: usize,
    self_ty: &SurfaceExpr,
) -> Result<(SurfaceName, SurfaceExpr), ElabError> {
    use crate::codata_variant_plan::ArgPlan;
    let name = ctor.args[j].alt_name().clone();
    let ty = match &ctor.args[j] {
        ArgPlan::Payload(p) => p.ty.clone(),
        ArgPlan::Child(c) => match &c.family {
            None => self_ty.clone(),
            Some(f) => {
                let (mut lemma_bound, mut ex_bound) = (false, false);
                for (k, a) in ctor.args.iter().enumerate() {
                    if let ArgPlan::Payload(pp) = a {
                        if mentions(f.source, &pp.arg_name) {
                            if k < i {
                                lemma_bound = true;
                            } else {
                                ex_bound = true;
                            }
                        }
                    }
                }
                if lemma_bound && ex_bound {
                    return Err(unsupported(format!(
                        "variant codata `{shape_name}`: `deriving Coind` cannot state the \
                         case tower for constructor `{}` — the domain of `{}` mentions \
                         payloads on both sides of the quantifier split, so it has no \
                         single correct spelling (some are bound by the lemma, some by \
                         the existential). Reorder the constructor so its payloads \
                         precede its recursive arguments, or drop `deriving Coind`",
                        ctor.name,
                        ctor.args[j].arg_name()
                    )));
                }
                let dom = if ex_bound {
                    f.in_alt.clone()
                } else {
                    f.source.clone()
                };
                arrow(dom, self_ty.clone())
            }
        },
    };
    Ok((name, ty))
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
            plain_app(extractor_name(shape.name, ctor, ci, m), call)
        }
    }
}

/// `T.CasesP`, `T.sumCases`, the per-constructor `T.cases_Cₖ` (with the
/// hoisted inner existentials each needs), and `T.cases` itself.
fn cases_tower(
    shape: &VariantShape<'_>,
    d: &Desc,
    n: &CoindNames,
) -> Result<Vec<SurfaceDecl>, ElabError> {
    let name = shape.name;
    let nctors = shape.ctors.len();
    let x = ident(&n.lhs);
    let mut out: Vec<SurfaceDecl> = Vec::new();

    // ── T.CasesP: the n-way disjunction of existentials.
    let disjunct = |ctor: &VariantCtorPlan<'_>| -> Result<SurfaceExpr, ElabError> {
        let mut applied = d.params.clone();
        applied.extend(ctor.args.iter().map(|a| ident(a.alt_name())));
        let mut body = eq(x.clone(), plain_app(name.append(ctor.name), applied));
        for j in (0..ctor.args.len()).rev() {
            let (bn, bt) = ex_binder(name, ctor, j, 0, &d.self_ty)?;
            body = plain_app(GlobalPath("Exists"), vec![lam_typed(&bn, bt, body)]);
        }
        Ok(body)
    };
    let disjuncts = shape
        .ctors
        .iter()
        .map(disjunct)
        .collect::<Result<Vec<_>, _>>()?;
    let cases_p_body =
        nest_right(GlobalPath("Or"), disjuncts).unwrap_or_else(|| ident(GlobalPath("True")));
    let mut cp_binders = shape.binders.to_vec();
    cp_binders.push(binder(&n.lhs, d.self_ty.clone()));
    out.push(mk_def(
        child_name(name, "CasesP"),
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
        let sum_xy = plain_app(GlobalPath("Sum"), vec![ident(bx), ident(by)]);
        out.push(mk_theorem(
            child_name(name, "sumCases"),
            vec![
                implicit(bx, type_u(d.poly.as_ref())),
                implicit(by, type_u(d.poly.as_ref())),
            ],
            pi(
                vec![binder(bv, sum_xy.clone()), binder(bc, prop_universe())],
                arrow(
                    pi(
                        vec![binder("xa", ident(bx))],
                        arrow(
                            eq(
                                ident(bv),
                                plain_app(GlobalPath("Sum.inl"), vec![ident("xa")]),
                            ),
                            ident(bc),
                        ),
                    ),
                    arrow(
                        pi(
                            vec![binder("ya", ident(by))],
                            arrow(
                                eq(
                                    ident(bv),
                                    plain_app(GlobalPath("Sum.inr"), vec![ident("ya")]),
                                ),
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
                    GlobalPath("Sum.rec"),
                    vec![
                        ident(bx),
                        ident(by),
                        lam_typed("w", sum_xy, arrow(eq(ident("w"), ident(bv)), ident(bc))),
                        lam(
                            &["xa", "he"],
                            plain_app(
                                bl,
                                vec![
                                    ident("xa"),
                                    plain_app(GlobalPath("Eq.symm"), vec![ident("he")]),
                                ],
                            ),
                        ),
                        lam(
                            &["ya", "he"],
                            plain_app(
                                br,
                                vec![
                                    ident("ya"),
                                    plain_app(GlobalPath("Eq.symm"), vec![ident("he")]),
                                ],
                            ),
                        ),
                        ident(bv),
                        ident(GlobalPath("rfl")),
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
        let call_lemma = |suffix: &SurfaceName| {
            let mut a = d.params.clone();
            a.push(x.clone());
            a.extend(payload_binders.iter().map(|b| ident(&b.name)));
            a.push(ident(&n.hh));
            plain_app(name.append(suffix), a)
        };
        let witnesses: Vec<SurfaceExpr> = (0..ctor.args.len())
            .map(|i| arg_witness(shape, d, n, ctor, &payload_binders, i))
            .collect();
        let eta = call_lemma(&affix_name(ctor.name, "", "_eta"));

        // `∃ a_i … a_{m-1}, x = Cₖ w₀ … w_{i-1} a_i …` — the statement of
        // the level-`i` inner lemma.
        // The PREDICATE of the level-`i` existential: `fun aᵢ => ∃ aᵢ₊₁ …,
        // x = Cₖ w₀ … wᵢ₋₁ aᵢ …`. Factored out of the statement because the
        // proof needs it too — see the `@Exists.intro` note below.
        let inner_pred = |i: usize| -> Result<SurfaceExpr, ElabError> {
            let mut applied = d.params.clone();
            for (j, a) in ctor.args.iter().enumerate() {
                applied.push(if j < i {
                    witnesses[j].clone()
                } else {
                    ident(a.alt_name())
                });
            }
            let mut body = eq(x.clone(), plain_app(name.append(ctor.name), applied));
            for j in ((i + 1)..ctor.args.len()).rev() {
                let (bn, bt) = ex_binder(name, ctor, j, i, &d.self_ty)?;
                body = plain_app(GlobalPath("Exists"), vec![lam_typed(&bn, bt, body)]);
            }
            let (bn, bt) = ex_binder(name, ctor, i, i, &d.self_ty)?;
            Ok(lam_typed(&bn, bt, body))
        };
        let inner_stmt = |i: usize| -> Result<SurfaceExpr, ElabError> {
            Ok(plain_app(GlobalPath("Exists"), vec![inner_pred(i)?]))
        };

        // `Exists.intro` with its implicits SPELLED, never inferred.
        //
        // `Exists.intro : {α} → {p : α → Prop} → (w : α) → p w → Exists p`.
        // Leaving `p` implicit works only when the elaborator can propagate
        // the expected type before checking the arguments. Here it often
        // cannot: the goal sits behind the `T.CasesP` definition, and the
        // witness is a compound extractor application rather than a plain
        // local — so `?p w` is not a Miller pattern, positional decomposition
        // assigns `?p := @Exists α`, and the elaboration dies on `Lam` vs
        // `App` with a poisoned metavariable.
        //
        // MEASURED, and it is not the exotic shape it looks like: the trigger
        // is a single-constructor codata whose FIRST argument is recursive.
        // Multi-constructor codata escaped only by accident — `inject_or`
        // wraps the disjunct in `Or.inl`, whose own implicit pins the shape
        // before `Exists.intro` is reached. `codata T where | C : T → T` is
        // the minimal case, and it is about as ordinary as a codata gets.
        let exists_intro =
            |i: usize, w: SurfaceExpr, h: SurfaceExpr| -> Result<SurfaceExpr, ElabError> {
                let (_, ty) = ex_binder(name, ctor, i, i, &d.self_ty)?;
                Ok(at_app(
                    GlobalPath("Exists.intro"),
                    vec![ty, inner_pred(i)?, w, h],
                ))
            };

        let m = ctor.args.len();
        for i in (1..m).rev() {
            let proof = if i + 1 == m {
                exists_intro(i, witnesses[i].clone(), eta.clone())?
            } else {
                exists_intro(
                    i,
                    witnesses[i].clone(),
                    call_lemma(&affix_name(
                        ctor.name,
                        "cases_",
                        &format!("_inner{}", i + 1),
                    )),
                )?
            };
            out.push(mk_theorem(
                name.append(&affix_name(ctor.name, "cases_", &format!("_inner{i}"))),
                lemma_binders.clone(),
                inner_stmt(i)?,
                proof,
            ));
        }

        let payload = if m == 0 {
            eta.clone()
        } else if m == 1 {
            exists_intro(0, witnesses[0].clone(), eta.clone())?
        } else {
            exists_intro(
                0,
                witnesses[0].clone(),
                call_lemma(&affix_name(ctor.name, "cases_", "_inner1")),
            )?
        };
        out.push(mk_theorem(
            name.append(&affix_name(ctor.name, "cases_", "")),
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
        a.push(ident(GlobalPath("rfl")));
        plain_app(
            name.append(&affix_name(shape.ctors[0].name, "cases_", "")),
            a,
        )
    } else {
        dispatch(shape, d, n, 0, d.head_of(x.clone()), &[], &goal)
    };
    out.push(mk_theorem(
        child_name(name, "cases"),
        cases_binders,
        goal,
        body,
    ));
    Ok(out)
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
                                GlobalPath("Sum.inr"),
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
    let pname = affix_name(&n.scrut, "", &format!("{level}"));
    let sname = affix_name(&n.scrut, "", &format!("s{level}"));
    let hname = affix_name(&n.scrut, "", &format!("h{level}"));

    let leaf = |k: usize, p: &SurfaceName, upto: &[SurfaceExpr]| {
        let ctor = &shape.ctors[k];
        let mut a = d.params.clone();
        a.push(ident(&n.lhs));
        a.extend(
            (0..ctor.payload_count())
                .map(|i| projection_path_of(&ident(p), i, ctor.payload_count())),
        );
        a.push(fold_head_eq(shape, upto, ident(&hname)));
        plain_app(name.append(&affix_name(ctor.name, "cases_", "")), a)
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
        child_name(name, "sumCases"),
        vec![scrut, goal.clone(), inl_branch, inr_branch],
    )
}
