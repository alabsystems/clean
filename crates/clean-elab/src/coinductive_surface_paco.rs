// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The PACO / ACCUMULATION companions of the `coinductive` lowering —
//! `P.acc` (strong coinduction), `P.coind_upto` (Park up to a compatible
//! closure), and the PARAMETERIZED PACO TOWER (`P.paco` rung) — split out
//! of [`super`] (the generation half) as a CHILD module along the same
//! file-length seam as the other `coinductive_surface_*` splits; privacy
//! is unchanged (a child sees its parent's private items). See the parent
//! crate module's doc for the rung's semantics; every companion rides the
//! declaration-parameter row through `Shape::papp`/`Shape::f_applied`
//! exactly like every other companion.
//!
//! # The parameterized tower ([`tower`])
//!
//! The faithful per-declaration mirror of the library file's paco section
//! (`data/graduation/clean-coind/proof/Coind.lean` — `paco`,
//! `paco_bot_le_gfp`, `gfp_le_paco`, `paco_acc`), which `P.acc` alone
//! could not give (it is the `r := ⊥` top-level projection). Statements
//! MATCH THE LIBRARY's formulation — `P.paco r` is the gfp of
//! `fun R => P.F (R ∨ r)`, encoded with the same impredicative union of
//! post-fixpoints as `P` itself; the `⊥` correspondence is the library's
//! two-implication pair (no propext `Eq`), with `gfp_le_paco` kept in its
//! generalized every-`r` form:
//!
//! ```text
//! P.paco        : (T⃗ → Prop) → T⃗ → Prop        the parameterized gfp
//! P.paco_coind  : Park for the accumulated functor (gfpRel_coind at F(·∨r))
//! P.paco_unfold : P.paco r ≤ P.F (P.paco r ∨ r)  (gfpRel_unfold at F(·∨r))
//! P.paco_fold   : P.F (P.paco r ∨ r) ≤ P.paco r  (gfpRel_fold at F(·∨r) —
//!                 the step engine of compositional pcofix-style proofs)
//! P.paco_mon    : r ≤ r' → P.paco r ≤ P.paco r'  (monotone in the
//!                 accumulated relation)
//! P.paco_bot    : P.paco ⊥ ≤ P                   (library paco_bot_le_gfp)
//! P.le_paco     : P ≤ P.paco r                   (library gfp_le_paco)
//! P.paco_acc    : r' ≤ P.paco (r ∨ r') → r' ≤ P.paco r
//!                 (the faithful accumulation, library paco_acc verbatim)
//! ```
//!
//! Union ORDER matches the library at every site: `paco`'s functor weakens
//! by `R ∨ r` (candidate left, `RelUnion R r`), `paco_acc` accumulates
//! `r ∨ r'` (older knowledge left, `RelUnion r r'`). All proofs are
//! self-contained direct terms from the tower's own lower rungs plus
//! `P.F_mono`/`P.unfold`/`P.coind` — the library file is graduated DATA,
//! not a compiled dependency, so nothing here applies its theorems by
//! name. Where the library instantiates `gfpRel_coind`/`gfpRel_unfold` at
//! the union functor inline, this module mints the instances as the named
//! companions `P.paco_coind`/`P.paco_unfold` and consumes those (no
//! generic `gfpRel` exists per-declaration to instantiate). `P.paco_fold`
//! has no named library counterpart (the library never needs it); it is
//! minted because compositional two-level accumulation proofs step through
//! it — it is `gfpRel_fold` at the union functor, nothing more.
//!
//! `P.acc`/`P.coind_upto` are UNCHANGED by the tower rung (their pins
//! stand); no bridge lemma `P.acc ↔ P.paco_acc @ ⊥` is minted — the
//! hypothesis shapes differ (an `F`-step against `R ∨ P` vs paco
//! membership) and the conversion is a real proof term, not a natural
//! fallout.

use super::{
    app, arrow, binder, forall_group, global, global_napp, ident, lam, lam_names_of, lam_typed,
    mk_def, mk_theorem, napp, or, prop, Shape, SurfaceBinderInfo, SurfaceDecl, SurfaceExpr, HYP_H,
    HYP_HR, HYP_LE, HYP_POST, REL_R, REL_S,
};
use clean_parser::{Span, SurfaceName};

/// `P.acc` / `P.coind_upto` binder names (paco/accumulation rung): the step
/// hypothesis, the `Or.elim` case hypotheses, the `coind_upto` closure and
/// its side-condition quartet. All carry the `_coind` marker like every
/// generated binder name of the surface module.
const HYP_STEP: &str = "hstep_coind";
const HYP_HU: &str = "hu_coind";
const HYP_HP: &str = "hp_coind";
const HYP_HQ: &str = "hq_coind";
const CLO: &str = "clo_coind";
const REL_Q: &str = "Q_coind";
const HYP_MONO_CLO: &str = "hmono_coind";
const HYP_COMPAT: &str = "hcompat_coind";
const HYP_IDEM: &str = "hidem_coind";
const HYP_INCL: &str = "hincl_coind";
/// Tower binder names (`P.paco` rung): the accumulated relation `r`, the
/// second accumulated/candidate relation `r'`, and the extra `Or.elim`
/// case hypotheses of `paco_acc`'s three-way routing.
const REL_ACC: &str = "r_coind";
const REL_ACC2: &str = "r1_coind";
const HYP_HRR: &str = "hrr_coind";
const HYP_HA: &str = "ha_coind";
const HYP_HB: &str = "hb_coind";

/// Accumulation / strong coinduction.
///
/// ```text
/// theorem P.acc (p⃗) (R) (hstep : ∀ v⃗, R v⃗ → P.F p⃗ (fun v⃗ => R v⃗ ∨ P p⃗ v⃗) v⃗)
///     : ∀ v⃗, R v⃗ → P p⃗ v⃗ :=
///   fun v⃗ h => P.coind p⃗ (fun v⃗ => R v⃗ ∨ P p⃗ v⃗)
///     (fun v⃗ hu => Or.elim hu
///       (fun hr => hstep v⃗ hr)
///       (fun hp => P.F_mono p⃗ (P p⃗) (fun v⃗ => R v⃗ ∨ P p⃗ v⃗)
///         (fun v⃗ hq => Or.inr hq) v⃗ (P.unfold p⃗ v⃗ hp)))
///     v⃗ (Or.inl h)
/// ```
///
/// The candidate may fall back on ACCUMULATED knowledge — P-facts already
/// established — at every recursive position: the union `R ∨ P p⃗` is a
/// post-fixpoint because the R-side steps by `hstep` and the P-side by
/// `P.unfold` weakened through `P.F_mono`. This is the `r := ⊥` top-level
/// projection of the library's `paco_acc` (the faithful mirror is the
/// generated tower's [`paco_acc_thm`], landed by the `P.paco` rung; this
/// theorem stays UNCHANGED — its pins stand), and exactly the
/// `clo := (· ∨ P p⃗)` instance of [`upto_thm`], minted directly with a
/// smaller proof term.
pub(super) fn acc_thm(s: &Shape) -> SurfaceDecl {
    let rel_ty = s.rel_ty();
    let gfp = || s.papp(&s.qname, Vec::new());
    let lam_names: Vec<SurfaceName> = lam_names_of(s, HYP_H);
    let union_pred = || {
        SurfaceExpr::Lambda(
            Span::dummy(),
            s.idx_binders(SurfaceBinderInfo::Explicit),
            Box::new(or(s.applied(ident(REL_R)), s.applied(gfp()))),
        )
    };
    let mut acc_unfold_args = s.var_args();
    acc_unfold_args.push(ident(HYP_HP));
    let mut acc_mono_args = vec![
        gfp(),
        union_pred(),
        lam_typed(
            &lam_names_of(s, HYP_HQ),
            global_napp("Or.inr", vec![ident(HYP_HQ)]),
        ),
    ];
    acc_mono_args.extend(s.var_args());
    acc_mono_args.push(s.papp(&s.unfold_name(), acc_unfold_args));
    let mut acc_step_args = s.var_args();
    acc_step_args.push(ident(HYP_HR));
    let acc_post = lam_typed(
        &lam_names_of(s, HYP_HU),
        napp(
            "Or.elim",
            vec![
                ident(HYP_HU),
                lam(&[HYP_HR], app(ident(HYP_STEP), acc_step_args)),
                lam(&[HYP_HP], s.papp(&s.mono_name(), acc_mono_args)),
            ],
        ),
    );
    let mut acc_coind_args = vec![union_pred(), acc_post];
    acc_coind_args.extend(s.var_args());
    acc_coind_args.push(global_napp("Or.inl", vec![ident(HYP_H)]));
    mk_theorem(
        s.acc_name(),
        s.with_params(vec![
            binder(REL_R, rel_ty.clone(), SurfaceBinderInfo::Explicit),
            binder(
                HYP_STEP,
                s.forall_vars(arrow(
                    s.applied(ident(REL_R)),
                    s.applied(s.f_applied(union_pred())),
                )),
                SurfaceBinderInfo::Explicit,
            ),
        ]),
        s.forall_vars(arrow(s.applied(ident(REL_R)), s.applied(gfp()))),
        lam_typed(&lam_names, s.papp(&s.coind_name(), acc_coind_args)),
    )
}

/// Park up to a compatible closure.
///
/// ```text
/// theorem P.coind_upto (p⃗) (clo : (T⃗ → Prop) → T⃗ → Prop)
///     (hmono : ∀ Q S, (∀ v⃗, Q v⃗ → S v⃗) → ∀ v⃗, clo Q v⃗ → clo S v⃗)
///     (hcompat : ∀ Q, ∀ v⃗, clo (P.F p⃗ Q) v⃗ → P.F p⃗ (clo Q) v⃗)
///     (hidem : ∀ Q, ∀ v⃗, clo (clo Q) v⃗ → clo Q v⃗)
///     (hincl : ∀ Q, ∀ v⃗, Q v⃗ → clo Q v⃗)
///     (R) (hstep : ∀ v⃗, R v⃗ → P.F p⃗ (clo R) v⃗) : ∀ v⃗, R v⃗ → P p⃗ v⃗ :=
///   fun v⃗ h => P.coind p⃗ (clo R)
///     (fun v⃗ hu => P.F_mono p⃗ (clo (clo R)) (clo R) (hidem R) v⃗
///       (hcompat (clo R) v⃗ (hmono R (P.F p⃗ (clo R)) hstep v⃗ hu)))
///     v⃗ (hincl R v⃗ h)
/// ```
///
/// The faithful specialization of the library `gfpRel_upto` at
/// `F := P.F p⃗` (the quantification over `clo` is intrinsic; `Mono F`
/// specializes away through the minted `P.F_mono`); the proof mirrors
/// the library term with `gfpRel_coind ↦ P.coind`.
pub(super) fn upto_thm(s: &Shape) -> SurfaceDecl {
    let rel_ty = s.rel_ty();
    let gfp = || s.papp(&s.qname, Vec::new());
    let lam_names: Vec<SurfaceName> = lam_names_of(s, HYP_H);
    let clo_of = |r: SurfaceExpr| app(ident(CLO), vec![r]);
    let rel_binder = |name: &str| binder(name, rel_ty.clone(), SurfaceBinderInfo::Explicit);
    let upto_inner = {
        let mut hmono_args = vec![
            ident(REL_R),
            s.f_applied(clo_of(ident(REL_R))),
            ident(HYP_STEP),
        ];
        hmono_args.extend(s.var_args());
        hmono_args.push(ident(HYP_HU));
        let mut hcompat_args = vec![clo_of(ident(REL_R))];
        hcompat_args.extend(s.var_args());
        hcompat_args.push(napp(HYP_MONO_CLO, hmono_args));
        let mut mono_args = vec![
            clo_of(clo_of(ident(REL_R))),
            clo_of(ident(REL_R)),
            napp(HYP_IDEM, vec![ident(REL_R)]),
        ];
        mono_args.extend(s.var_args());
        mono_args.push(napp(HYP_COMPAT, hcompat_args));
        s.papp(&s.mono_name(), mono_args)
    };
    let mut upto_incl_args = vec![ident(REL_R)];
    upto_incl_args.extend(s.var_args());
    upto_incl_args.push(ident(HYP_H));
    let mut upto_coind_args = vec![
        clo_of(ident(REL_R)),
        lam_typed(&lam_names_of(s, HYP_HU), upto_inner),
    ];
    upto_coind_args.extend(s.var_args());
    upto_coind_args.push(napp(HYP_INCL, upto_incl_args));
    mk_theorem(
        s.upto_name(),
        s.with_params(vec![
            binder(
                CLO,
                arrow(rel_ty.clone(), rel_ty.clone()),
                SurfaceBinderInfo::Explicit,
            ),
            binder(
                HYP_MONO_CLO,
                forall_group(
                    &[rel_binder(REL_Q), rel_binder(REL_S)],
                    arrow(
                        s.forall_vars(arrow(s.applied(ident(REL_Q)), s.applied(ident(REL_S)))),
                        s.forall_vars(arrow(
                            s.applied(clo_of(ident(REL_Q))),
                            s.applied(clo_of(ident(REL_S))),
                        )),
                    ),
                ),
                SurfaceBinderInfo::Explicit,
            ),
            binder(
                HYP_COMPAT,
                forall_group(
                    &[rel_binder(REL_Q)],
                    s.forall_vars(arrow(
                        s.applied(clo_of(s.f_applied(ident(REL_Q)))),
                        s.applied(s.f_applied(clo_of(ident(REL_Q)))),
                    )),
                ),
                SurfaceBinderInfo::Explicit,
            ),
            binder(
                HYP_IDEM,
                forall_group(
                    &[rel_binder(REL_Q)],
                    s.forall_vars(arrow(
                        s.applied(clo_of(clo_of(ident(REL_Q)))),
                        s.applied(clo_of(ident(REL_Q))),
                    )),
                ),
                SurfaceBinderInfo::Explicit,
            ),
            binder(
                HYP_INCL,
                forall_group(
                    &[rel_binder(REL_Q)],
                    s.forall_vars(arrow(
                        s.applied(ident(REL_Q)),
                        s.applied(clo_of(ident(REL_Q))),
                    )),
                ),
                SurfaceBinderInfo::Explicit,
            ),
            rel_binder(REL_R),
            binder(
                HYP_STEP,
                s.forall_vars(arrow(
                    s.applied(ident(REL_R)),
                    s.applied(s.f_applied(clo_of(ident(REL_R)))),
                )),
                SurfaceBinderInfo::Explicit,
            ),
        ]),
        s.forall_vars(arrow(s.applied(ident(REL_R)), s.applied(gfp()))),
        lam_typed(&lam_names, s.papp(&s.coind_name(), upto_coind_args)),
    )
}

// ── the parameterized paco tower (`P.paco` rung) ─────────────────────────

impl Shape {
    fn paco_name(&self) -> SurfaceName {
        self.qname.append(&SurfaceName::component("paco", false))
    }
    fn paco_coind_name(&self) -> SurfaceName {
        self.qname
            .append(&SurfaceName::component("paco_coind", false))
    }
    fn paco_unfold_name(&self) -> SurfaceName {
        self.qname
            .append(&SurfaceName::component("paco_unfold", false))
    }
    fn paco_fold_name(&self) -> SurfaceName {
        self.qname
            .append(&SurfaceName::component("paco_fold", false))
    }
    fn paco_mon_name(&self) -> SurfaceName {
        self.qname
            .append(&SurfaceName::component("paco_mon", false))
    }
    fn paco_bot_name(&self) -> SurfaceName {
        self.qname
            .append(&SurfaceName::component("paco_bot", false))
    }
    fn le_paco_name(&self) -> SurfaceName {
        self.qname.append(&SurfaceName::component("le_paco", false))
    }
    fn paco_acc_name(&self) -> SurfaceName {
        self.qname
            .append(&SurfaceName::component("paco_acc", false))
    }

    /// `P.paco p⃗ r` — the parameterized gfp at accumulated `r`, as a
    /// partial application (a `T⃗ → Prop` term).
    fn paco_at(&self, r: SurfaceExpr) -> SurfaceExpr {
        self.papp(&self.paco_name(), vec![r])
    }
}

/// `fun (v⃗ : T⃗) => a v⃗ ∨ b v⃗` — the pointwise union of two relations
/// over the shared index row (the library's `RelUnion a b`; candidate/older
/// knowledge on the LEFT at every use site, matching the library's order).
fn union_rel(s: &Shape, a: SurfaceExpr, b: SurfaceExpr) -> SurfaceExpr {
    SurfaceExpr::Lambda(
        Span::dummy(),
        s.idx_binders(SurfaceBinderInfo::Explicit),
        Box::new(or(s.applied(a), s.applied(b))),
    )
}

/// `fun (v⃗ : T⃗) => False` — the empty relation (the library's `RelBot`).
fn bot_rel(s: &Shape) -> SurfaceExpr {
    SurfaceExpr::Lambda(
        Span::dummy(),
        s.idx_binders(SurfaceBinderInfo::Explicit),
        Box::new(global("False")),
    )
}

/// The tower's object — the parameterized greatest fixpoint, the library's
/// `paco F r := gfpRel (fun R => F (RelUnion R r))` with the gfp encoding
/// inlined exactly as `P` itself inlines `gfpRel P.F`:
///
/// ```text
/// def P.paco (p⃗) (r : T⃗ → Prop) (v⃗ : T⃗) : Prop :=
///   ∃ R, (∀ v⃗, R v⃗ → P.F p⃗ (fun v⃗ => R v⃗ ∨ r v⃗) v⃗) ∧ R v⃗
/// ```
fn paco_def(s: &Shape) -> SurfaceDecl {
    let rel_ty = s.rel_ty();
    let post = s.forall_vars(arrow(
        s.applied(ident(REL_R)),
        s.applied(s.f_applied(union_rel(s, ident(REL_R), ident(REL_ACC)))),
    ));
    let mut binders = vec![binder(REL_ACC, rel_ty.clone(), SurfaceBinderInfo::Explicit)];
    binders.extend(s.idx_binders(SurfaceBinderInfo::Explicit));
    mk_def(
        s.paco_name(),
        s.with_params(binders),
        prop(),
        global_napp(
            "Exists",
            vec![SurfaceExpr::Lambda(
                Span::dummy(),
                vec![binder(REL_R, rel_ty, SurfaceBinderInfo::Explicit)],
                Box::new(global_napp("And", vec![post, s.applied(ident(REL_R))])),
            )],
        ),
    )
}

/// Park coinduction for the accumulated functor — `gfpRel_coind` at
/// `fun R => P.F (R ∨ r)`, which the library instantiates inline:
///
/// ```text
/// theorem P.paco_coind (p⃗) (r R : T⃗ → Prop)
///     (hpost : ∀ v⃗, R v⃗ → P.F p⃗ (fun v⃗ => R v⃗ ∨ r v⃗) v⃗) :
///     ∀ v⃗, R v⃗ → P.paco p⃗ r v⃗ :=
///   fun v⃗ h => Exists.intro R (And.intro hpost h)
/// ```
fn paco_coind_thm(s: &Shape) -> SurfaceDecl {
    let rel_ty = s.rel_ty();
    let lam_names: Vec<SurfaceName> = lam_names_of(s, HYP_H);
    mk_theorem(
        s.paco_coind_name(),
        s.with_params(vec![
            binder(REL_ACC, rel_ty.clone(), SurfaceBinderInfo::Explicit),
            binder(REL_R, rel_ty.clone(), SurfaceBinderInfo::Explicit),
            binder(
                HYP_POST,
                s.forall_vars(arrow(
                    s.applied(ident(REL_R)),
                    s.applied(s.f_applied(union_rel(s, ident(REL_R), ident(REL_ACC)))),
                )),
                SurfaceBinderInfo::Explicit,
            ),
        ]),
        s.forall_vars(arrow(
            s.applied(ident(REL_R)),
            s.applied(s.paco_at(ident(REL_ACC))),
        )),
        lam_typed(
            &lam_names,
            global_napp(
                "Exists.intro",
                vec![
                    ident(REL_R),
                    global_napp("And.intro", vec![ident(HYP_POST), ident(HYP_H)]),
                ],
            ),
        ),
    )
}

/// The tower's destructor — `gfpRel_unfold` at the accumulated functor:
///
/// ```text
/// theorem P.paco_unfold (p⃗) (r) :
///     ∀ v⃗, P.paco p⃗ r v⃗ → P.F p⃗ (fun v⃗ => P.paco p⃗ r v⃗ ∨ r v⃗) v⃗ :=
///   fun v⃗ h => Exists.elim h (fun R hR =>
///     P.F_mono p⃗ (fun v⃗ => R v⃗ ∨ r v⃗) (fun v⃗ => P.paco p⃗ r v⃗ ∨ r v⃗)
///       (fun v⃗ hu => Or.elim hu
///         (fun hp => Or.inl (P.paco_coind p⃗ r R hR.left v⃗ hp))
///         (fun hq => Or.inr hq))
///       v⃗ (hR.left v⃗ hR.right))
/// ```
fn paco_unfold_thm(s: &Shape) -> SurfaceDecl {
    let rel_ty = s.rel_ty();
    let lam_names: Vec<SurfaceName> = lam_names_of(s, HYP_H);
    let paco_r = || s.paco_at(ident(REL_ACC));
    let post_hyp = global_napp("And.left", vec![ident(HYP_HR)]);
    let carrier_hyp = global_napp("And.right", vec![ident(HYP_HR)]);
    let mut inl_coind_args = vec![ident(REL_ACC), ident(REL_R), post_hyp.clone()];
    inl_coind_args.extend(s.var_args());
    inl_coind_args.push(ident(HYP_HP));
    let hle = lam_typed(
        &lam_names_of(s, HYP_HU),
        napp(
            "Or.elim",
            vec![
                ident(HYP_HU),
                lam(
                    &[HYP_HP],
                    global_napp("Or.inl", vec![s.papp(&s.paco_coind_name(), inl_coind_args)]),
                ),
                lam(&[HYP_HQ], global_napp("Or.inr", vec![ident(HYP_HQ)])),
            ],
        ),
    );
    let mut mono_args = vec![
        union_rel(s, ident(REL_R), ident(REL_ACC)),
        union_rel(s, paco_r(), ident(REL_ACC)),
        hle,
    ];
    mono_args.extend(s.var_args());
    mono_args.push(app(
        post_hyp,
        s.var_args().into_iter().chain([carrier_hyp]).collect(),
    ));
    mk_theorem(
        s.paco_unfold_name(),
        s.with_params(vec![binder(REL_ACC, rel_ty, SurfaceBinderInfo::Explicit)]),
        s.forall_vars(arrow(
            s.applied(paco_r()),
            s.applied(s.f_applied(union_rel(s, paco_r(), ident(REL_ACC)))),
        )),
        lam_typed(
            &lam_names,
            napp(
                "Exists.elim",
                vec![
                    ident(HYP_H),
                    lam(&[REL_R, HYP_HR], s.papp(&s.mono_name(), mono_args)),
                ],
            ),
        ),
    )
}

/// The tower's constructor — `gfpRel_fold` at the accumulated functor (no
/// named library counterpart; the library never needs it, compositional
/// two-level accumulation proofs step through it):
///
/// ```text
/// theorem P.paco_fold (p⃗) (r) :
///     ∀ v⃗, P.F p⃗ (fun v⃗ => P.paco p⃗ r v⃗ ∨ r v⃗) v⃗ → P.paco p⃗ r v⃗ :=
///   P.paco_coind p⃗ r (P.F p⃗ (fun v⃗ => P.paco p⃗ r v⃗ ∨ r v⃗))
///     (fun v⃗ h => P.F_mono p⃗ (…upaco…) (fun v⃗ => P.F p⃗ (…upaco…) v⃗ ∨ r v⃗)
///       (fun v⃗ hu => Or.elim hu
///         (fun hp => Or.inl (P.paco_unfold p⃗ r v⃗ hp))
///         (fun hq => Or.inr hq))
///       v⃗ h)
/// ```
fn paco_fold_thm(s: &Shape) -> SurfaceDecl {
    let rel_ty = s.rel_ty();
    let paco_r = || s.paco_at(ident(REL_ACC));
    let upaco = || union_rel(s, s.paco_at(ident(REL_ACC)), ident(REL_ACC));
    let f_upaco = || s.f_applied(upaco());
    let mut unfold_args = vec![ident(REL_ACC)];
    unfold_args.extend(s.var_args());
    unfold_args.push(ident(HYP_HP));
    let hle = lam_typed(
        &lam_names_of(s, HYP_HU),
        napp(
            "Or.elim",
            vec![
                ident(HYP_HU),
                lam(
                    &[HYP_HP],
                    global_napp("Or.inl", vec![s.papp(&s.paco_unfold_name(), unfold_args)]),
                ),
                lam(&[HYP_HQ], global_napp("Or.inr", vec![ident(HYP_HQ)])),
            ],
        ),
    );
    let mut mono_args = vec![upaco(), union_rel(s, f_upaco(), ident(REL_ACC)), hle];
    mono_args.extend(s.var_args());
    mono_args.push(ident(HYP_H));
    let post = lam_typed(&lam_names_of(s, HYP_H), s.papp(&s.mono_name(), mono_args));
    mk_theorem(
        s.paco_fold_name(),
        s.with_params(vec![binder(REL_ACC, rel_ty, SurfaceBinderInfo::Explicit)]),
        s.forall_vars(arrow(s.applied(f_upaco()), s.applied(paco_r()))),
        s.papp(&s.paco_coind_name(), vec![ident(REL_ACC), f_upaco(), post]),
    )
}

/// Monotonicity in the ACCUMULATED relation:
///
/// ```text
/// theorem P.paco_mon (p⃗) (r r') (hle : ∀ v⃗, r v⃗ → r' v⃗) :
///     ∀ v⃗, P.paco p⃗ r v⃗ → P.paco p⃗ r' v⃗ :=
///   P.paco_coind p⃗ r' (P.paco p⃗ r)
///     (fun v⃗ h => P.F_mono p⃗ (…paco r ∨ r…) (…paco r ∨ r'…)
///       (fun v⃗ hu => Or.elim hu
///         (fun hp => Or.inl hp)
///         (fun hq => Or.inr (hle v⃗ hq)))
///       v⃗ (P.paco_unfold p⃗ r v⃗ h))
/// ```
fn paco_mon_thm(s: &Shape) -> SurfaceDecl {
    let rel_ty = s.rel_ty();
    let paco_r = || s.paco_at(ident(REL_ACC));
    let mut le_args = s.var_args();
    le_args.push(ident(HYP_HQ));
    let hle = lam_typed(
        &lam_names_of(s, HYP_HU),
        napp(
            "Or.elim",
            vec![
                ident(HYP_HU),
                lam(&[HYP_HP], global_napp("Or.inl", vec![ident(HYP_HP)])),
                lam(
                    &[HYP_HQ],
                    global_napp("Or.inr", vec![app(ident(HYP_LE), le_args)]),
                ),
            ],
        ),
    );
    let mut unfold_args = vec![ident(REL_ACC)];
    unfold_args.extend(s.var_args());
    unfold_args.push(ident(HYP_H));
    let mut mono_args = vec![
        union_rel(s, paco_r(), ident(REL_ACC)),
        union_rel(s, paco_r(), ident(REL_ACC2)),
        hle,
    ];
    mono_args.extend(s.var_args());
    mono_args.push(s.papp(&s.paco_unfold_name(), unfold_args));
    let post = lam_typed(&lam_names_of(s, HYP_H), s.papp(&s.mono_name(), mono_args));
    mk_theorem(
        s.paco_mon_name(),
        s.with_params(vec![
            binder(REL_ACC, rel_ty.clone(), SurfaceBinderInfo::Explicit),
            binder(REL_ACC2, rel_ty.clone(), SurfaceBinderInfo::Explicit),
            binder(
                HYP_LE,
                s.forall_vars(arrow(s.applied(ident(REL_ACC)), s.applied(ident(REL_ACC2)))),
                SurfaceBinderInfo::Explicit,
            ),
        ]),
        s.forall_vars(arrow(
            s.applied(paco_r()),
            s.applied(s.paco_at(ident(REL_ACC2))),
        )),
        s.papp(&s.paco_coind_name(), vec![ident(REL_ACC2), paco_r(), post]),
    )
}

/// The `⊥` correspondence, gfp-ward — the library's `paco_bot_le_gfp`
/// specialized (with the union-functor `gfpRel_unfold` instance it inlines
/// replaced by the minted `P.paco_unfold`):
///
/// ```text
/// theorem P.paco_bot (p⃗) : ∀ v⃗, P.paco p⃗ (fun v⃗ => False) v⃗ → P p⃗ v⃗ :=
///   P.coind p⃗ (P.paco p⃗ ⊥)
///     (fun v⃗ h => P.F_mono p⃗ (…paco ⊥ ∨ ⊥…) (P.paco p⃗ ⊥)
///       (fun v⃗ hu => Or.elim hu (fun hp => hp) (fun hq => False.elim hq))
///       v⃗ (P.paco_unfold p⃗ ⊥ v⃗ h))
/// ```
fn paco_bot_thm(s: &Shape) -> SurfaceDecl {
    let gfp = || s.papp(&s.qname, Vec::new());
    let paco_bot = || s.paco_at(bot_rel(s));
    let hle = lam_typed(
        &lam_names_of(s, HYP_HU),
        napp(
            "Or.elim",
            vec![
                ident(HYP_HU),
                lam(&[HYP_HP], ident(HYP_HP)),
                lam(&[HYP_HQ], global_napp("False.elim", vec![ident(HYP_HQ)])),
            ],
        ),
    );
    let mut unfold_args = vec![bot_rel(s)];
    unfold_args.extend(s.var_args());
    unfold_args.push(ident(HYP_H));
    let mut mono_args = vec![union_rel(s, paco_bot(), bot_rel(s)), paco_bot(), hle];
    mono_args.extend(s.var_args());
    mono_args.push(s.papp(&s.paco_unfold_name(), unfold_args));
    let post = lam_typed(&lam_names_of(s, HYP_H), s.papp(&s.mono_name(), mono_args));
    mk_theorem(
        s.paco_bot_name(),
        s.with_params(Vec::new()),
        s.forall_vars(arrow(s.applied(paco_bot()), s.applied(gfp()))),
        s.papp(&s.coind_name(), vec![paco_bot(), post]),
    )
}

/// The `⊥` correspondence, tower-ward, in the library's generalized
/// every-`r` form (`gfp_le_paco`) — an established P-fact enters ANY paco
/// level (how accumulated knowledge is injected mid-proof):
///
/// ```text
/// theorem P.le_paco (p⃗) (r) : ∀ v⃗, P p⃗ v⃗ → P.paco p⃗ r v⃗ :=
///   P.paco_coind p⃗ r (P p⃗)
///     (fun v⃗ h => P.F_mono p⃗ (P p⃗) (fun v⃗ => P p⃗ v⃗ ∨ r v⃗)
///       (fun v⃗ hp => Or.inl hp)
///       v⃗ (P.unfold p⃗ v⃗ h))
/// ```
fn le_paco_thm(s: &Shape) -> SurfaceDecl {
    let rel_ty = s.rel_ty();
    let gfp = || s.papp(&s.qname, Vec::new());
    let hle = lam_typed(
        &lam_names_of(s, HYP_HP),
        global_napp("Or.inl", vec![ident(HYP_HP)]),
    );
    let mut unfold_args = s.var_args();
    unfold_args.push(ident(HYP_H));
    let mut mono_args = vec![gfp(), union_rel(s, gfp(), ident(REL_ACC)), hle];
    mono_args.extend(s.var_args());
    mono_args.push(s.papp(&s.unfold_name(), unfold_args));
    let post = lam_typed(&lam_names_of(s, HYP_H), s.papp(&s.mono_name(), mono_args));
    mk_theorem(
        s.le_paco_name(),
        s.with_params(vec![binder(REL_ACC, rel_ty, SurfaceBinderInfo::Explicit)]),
        s.forall_vars(arrow(
            s.applied(gfp()),
            s.applied(s.paco_at(ident(REL_ACC))),
        )),
        s.papp(&s.paco_coind_name(), vec![ident(REL_ACC), gfp(), post]),
    )
}

/// THE faithful accumulation — the library's `paco_acc`, verbatim modulo
/// the named tower companions standing in for its inline `gfpRel_coind`/
/// `gfpRel_unfold` instances (union order `r ∨ r'`, older knowledge left,
/// exactly the library's `RelUnion r r'`):
///
/// ```text
/// theorem P.paco_acc (p⃗) (r r')
///     (hstep : ∀ v⃗, r' v⃗ → P.paco p⃗ (fun v⃗ => r v⃗ ∨ r' v⃗) v⃗) :
///     ∀ v⃗, r' v⃗ → P.paco p⃗ r v⃗ :=
///   fun v⃗ hR => P.paco_coind p⃗ r (P.paco p⃗ (r ∨ r'))
///     (fun v⃗ hq => P.F_mono p⃗ (…paco (r∨r') ∨ (r∨r')…) (…paco (r∨r') ∨ r…)
///       (fun v⃗ hu => Or.elim hu
///         (fun hp => Or.inl hp)
///         (fun hrr => Or.elim hrr
///           (fun ha => Or.inr ha)
///           (fun hb => Or.inl (hstep v⃗ hb))))
///       v⃗ (P.paco_unfold p⃗ (r ∨ r') v⃗ hq))
///     v⃗ (hstep v⃗ hR)
/// ```
fn paco_acc_thm(s: &Shape) -> SurfaceDecl {
    let rel_ty = s.rel_ty();
    let union_acc = || union_rel(s, ident(REL_ACC), ident(REL_ACC2));
    let paco_u = || s.paco_at(union_acc());
    let lam_names: Vec<SurfaceName> = lam_names_of(s, HYP_HR);
    let mut step_b_args = s.var_args();
    step_b_args.push(ident(HYP_HB));
    let map = lam_typed(
        &lam_names_of(s, HYP_HU),
        napp(
            "Or.elim",
            vec![
                ident(HYP_HU),
                lam(&[HYP_HP], global_napp("Or.inl", vec![ident(HYP_HP)])),
                lam(
                    &[HYP_HRR],
                    napp(
                        "Or.elim",
                        vec![
                            ident(HYP_HRR),
                            lam(&[HYP_HA], global_napp("Or.inr", vec![ident(HYP_HA)])),
                            lam(
                                &[HYP_HB],
                                global_napp("Or.inl", vec![app(ident(HYP_STEP), step_b_args)]),
                            ),
                        ],
                    ),
                ),
            ],
        ),
    );
    let mut unfold_args = vec![union_acc()];
    unfold_args.extend(s.var_args());
    unfold_args.push(ident(HYP_HQ));
    let mut mono_args = vec![
        union_rel(s, paco_u(), union_acc()),
        union_rel(s, paco_u(), ident(REL_ACC)),
        map,
    ];
    mono_args.extend(s.var_args());
    mono_args.push(s.papp(&s.paco_unfold_name(), unfold_args));
    let post = lam_typed(&lam_names_of(s, HYP_HQ), s.papp(&s.mono_name(), mono_args));
    let mut step_r_args = s.var_args();
    step_r_args.push(ident(HYP_HR));
    let mut coind_args = vec![ident(REL_ACC), paco_u(), post];
    coind_args.extend(s.var_args());
    coind_args.push(app(ident(HYP_STEP), step_r_args));
    mk_theorem(
        s.paco_acc_name(),
        s.with_params(vec![
            binder(REL_ACC, rel_ty.clone(), SurfaceBinderInfo::Explicit),
            binder(REL_ACC2, rel_ty.clone(), SurfaceBinderInfo::Explicit),
            binder(
                HYP_STEP,
                s.forall_vars(arrow(s.applied(ident(REL_ACC2)), s.applied(paco_u()))),
                SurfaceBinderInfo::Explicit,
            ),
        ]),
        s.forall_vars(arrow(
            s.applied(ident(REL_ACC2)),
            s.applied(s.paco_at(ident(REL_ACC))),
        )),
        lam_typed(&lam_names, s.papp(&s.paco_coind_name(), coind_args)),
    )
}

/// The whole tower, in dependency order (`paco_unfold` consumes
/// `paco_coind`; `paco_fold`/`paco_mon`/`paco_bot`/`paco_acc` consume
/// `paco_unfold`; `le_paco` consumes `P.unfold`).
pub(super) fn tower(s: &Shape) -> Vec<SurfaceDecl> {
    vec![
        paco_def(s),
        paco_coind_thm(s),
        paco_unfold_thm(s),
        paco_fold_thm(s),
        paco_mon_thm(s),
        paco_bot_thm(s),
        le_paco_thm(s),
        paco_acc_thm(s),
    ]
}
