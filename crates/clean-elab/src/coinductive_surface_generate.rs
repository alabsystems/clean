// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Generation half of the `coinductive` lowering: a validated
//! [`Shape`] becomes the surface declarations of the greatest-fixpoint
//! family (see the parent module for the envelope, the α-rename onto the
//! shared index row, and the generated shapes). Everything here is pure
//! surface-term construction; the caller kernel-checks every declaration.

use super::{
    guard::GuardedPremise, DisjunctPlan, IndexEquation, Premise, Shape, ARM_PREFIX, HYP_EX_PREFIX,
    HYP_H, HYP_HD_PREFIX, HYP_HR, HYP_HT_PREFIX, HYP_LE, HYP_POST, MOTIVE_C, REL_R, REL_S,
};
use clean_parser::{
    DeclModifiers, Span, SurfaceArg, SurfaceBinder, SurfaceBinderInfo, SurfaceDecl, SurfaceExpr,
    TerminationHints, UniverseExpr,
};

/// The paco/accumulation companions (`P.acc`, `P.coind_upto`) — a CHILD
/// module (it reads this module's private builders and the `Shape` impl),
/// split along the paragon file-length seam like the sibling
/// `coinductive_surface_*` files.
#[path = "coinductive_surface_paco.rs"]
mod paco;

// ── surface-term builders ────────────────────────────────────────────────

pub(super) fn ident(name: &str) -> SurfaceExpr {
    SurfaceExpr::Ident(Span::dummy(), name.to_string())
}

/// Application that FLATTENS a nested head: `app(app(f, [a]), [b])` is
/// `f a b`, the shape a parsed application would have had.
pub(super) fn app(head: SurfaceExpr, args: Vec<SurfaceExpr>) -> SurfaceExpr {
    if args.is_empty() {
        return head;
    }
    let new_args = args.into_iter().map(SurfaceArg::positional);
    match head {
        SurfaceExpr::App(span, h, mut existing) => {
            existing.extend(new_args);
            SurfaceExpr::App(span, h, existing)
        }
        other => SurfaceExpr::App(Span::dummy(), Box::new(other), new_args.collect()),
    }
}

pub(super) fn napp(name: &str, args: Vec<SurfaceExpr>) -> SurfaceExpr {
    app(ident(name), args)
}

pub(super) fn arrow(a: SurfaceExpr, b: SurfaceExpr) -> SurfaceExpr {
    SurfaceExpr::Arrow(Span::dummy(), Box::new(a), Box::new(b))
}

fn prop() -> SurfaceExpr {
    SurfaceExpr::Universe(Span::dummy(), UniverseExpr::Prop)
}

fn binder(name: &str, ty: SurfaceExpr, info: SurfaceBinderInfo) -> SurfaceBinder {
    SurfaceBinder::new(name, Some(ty), info)
}

/// `fun n₁ n₂ … => body` with untyped binders (solved from the expected type).
pub(super) fn lam(names: &[&str], body: SurfaceExpr) -> SurfaceExpr {
    if names.is_empty() {
        return body;
    }
    SurfaceExpr::Lambda(
        Span::dummy(),
        names
            .iter()
            .map(|n| SurfaceBinder::new(*n, None, SurfaceBinderInfo::Explicit))
            .collect(),
        Box::new(body),
    )
}

pub(super) fn and(a: SurfaceExpr, b: SurfaceExpr) -> SurfaceExpr {
    napp("And", vec![a, b])
}

fn or(a: SurfaceExpr, b: SurfaceExpr) -> SurfaceExpr {
    napp("Or", vec![a, b])
}

/// Right-nested combination of a non-empty list (`p₁ ∘ (p₂ ∘ (… ∘ pⱼ))`).
pub(super) fn right_nest(
    mut parts: Vec<SurfaceExpr>,
    f: impl Fn(SurfaceExpr, SurfaceExpr) -> SurfaceExpr,
) -> SurfaceExpr {
    let last = parts.pop().unwrap_or_else(prop);
    parts.into_iter().rev().fold(last, |acc, p| f(p, acc))
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

/// Per-conjunct `F_mono` routing (see [`DisjunctPlan::mono_routes`]).
enum MonoRoute<'a> {
    /// An index equation or a `P`-free premise — carried verbatim.
    Carry,
    /// A flat recursive atom `P e⃗` — `hle e⃗ ·`.
    Atom(&'a [SurfaceExpr]),
    /// A guarded clause — mapped under its guard.
    Guarded(&'a GuardedPremise),
}

// ── per-disjunct pieces ──────────────────────────────────────────────────

impl IndexEquation {
    /// The equation proposition `written = vᵢ`. THE single point that
    /// spells the pinned ORIENTATION: the constructor's written target
    /// argument on the LEFT, the shared index binder on the right — a
    /// `P.cases` arm at index `0` therefore hands the arm `Nat.succ k = 0`,
    /// never `0 = Nat.succ k` (a different type; a statement-level test
    /// pins it).
    fn prop(&self) -> SurfaceExpr {
        napp("Eq", vec![self.written.clone(), ident(&self.row)])
    }

    /// The intro theorem's proof of this equation at the instantiated
    /// target (`vᵢ := written`): `Eq.refl written`.
    fn refl(&self) -> SurfaceExpr {
        napp("Eq.refl", vec![self.written.clone()])
    }
}

impl DisjunctPlan {
    /// The functor-body conjuncts of this disjunct, with the applied head
    /// `rel_head` standing for the recursive occurrences (the bare `R`
    /// inside the functor; the row-applied `P p⃗` at the declared
    /// premises): index equations first (Brick 3), then the premises.
    /// Proof-side accessors ([`conjunct`]) index into THIS order, so it
    /// must stay in sync with [`Self::mono_routes`].
    fn conjuncts(&self, rel_head: &SurfaceExpr) -> Vec<SurfaceExpr> {
        self.equations
            .iter()
            .map(IndexEquation::prop)
            .chain(self.premises.iter().map(|p| match p {
                Premise::Rec(args) => app(rel_head.clone(), args.clone()),
                Premise::Plain(e) => e.clone(),
                Premise::Guarded(g) => g.at_rel(rel_head),
            }))
            .collect()
    }

    /// This disjunct's contribution to the one-step functor body:
    /// `∃ b⃗, c₁ ∧ … ∧ cⱼ`. The `∃` wrap is a no-op while `exists_binders`
    /// is empty, keeping the output byte-identical to the pre-plan code.
    fn body(&self, rel_head: &SurfaceExpr) -> SurfaceExpr {
        let conj = right_nest(self.conjuncts(rel_head), and);
        self.exists_binders.iter().rev().fold(conj, |acc, b| {
            napp(
                "Exists",
                vec![SurfaceExpr::Lambda(
                    Span::dummy(),
                    vec![b.clone()],
                    Box::new(acc),
                )],
            )
        })
    }

    /// Per-conjunct routing for the `F_mono` proof, in [`Self::conjuncts`]
    /// order: an equation or plain premise is carried verbatim, a recursive
    /// occurrence `P e⃗` is mapped through `hle`, and a guarded premise is
    /// mapped UNDER its guard ([`GuardedPremise::mono_map`]).
    fn mono_routes(&self) -> Vec<MonoRoute<'_>> {
        self.equations
            .iter()
            .map(|_| MonoRoute::Carry)
            .chain(self.premises.iter().map(|p| match p {
                Premise::Rec(args) => MonoRoute::Atom(args.as_slice()),
                Premise::Plain(_) => MonoRoute::Carry,
                Premise::Guarded(g) => MonoRoute::Guarded(g),
            }))
            .collect()
    }

    /// The declared premises, with recursive occurrences spelled at the
    /// generated predicate applied to the fixed parameter row (`P p⃗`).
    fn declared_premises(&self, gfp_head: &SurfaceExpr) -> Vec<SurfaceExpr> {
        self.premises
            .iter()
            .map(|p| match p {
                Premise::Rec(args) => app(gfp_head.clone(), args.clone()),
                Premise::Plain(e) => e.clone(),
                Premise::Guarded(g) => g.at_rel(gfp_head),
            })
            .collect()
    }

    /// The `F_mono` image of this disjunct: destructure the `∃ b⃗` layer of
    /// `h` (a no-op without binders), rebuild the conjunction through
    /// [`Self::mono_conj`], and re-wrap the SAME witnesses with
    /// `Exists.intro` — sound because binder types are P-free by the
    /// envelope, so the `R`-side witnesses inhabit the `S`-side `∃` domains
    /// unchanged.
    fn mono_image(&self, h: &SurfaceExpr) -> SurfaceExpr {
        exists_elim_nest(&self.exists_binders, h.clone(), &|hconj| {
            self.exists_intro_nest(self.mono_conj(&hconj))
        })
    }

    /// Rebuild this disjunct's conjunction from a proof `h` of the bare
    /// `R`-side conjunction, routing every recursive conjunct through the
    /// `hle` hypothesis (under its guard, for a guarded premise) and
    /// carrying the others verbatim.
    fn mono_conj(&self, h: &SurfaceExpr) -> SurfaceExpr {
        let routes = self.mono_routes();
        let j = routes.len();
        right_nest(
            routes
                .iter()
                .enumerate()
                .map(|(i, route)| {
                    let acc = conjunct(h.clone(), i, j);
                    match route {
                        MonoRoute::Atom(args) => {
                            let mut a = args.to_vec();
                            a.push(acc);
                            napp(HYP_LE, a)
                        }
                        MonoRoute::Carry => acc,
                        MonoRoute::Guarded(g) => g.mono_map(acc),
                    }
                })
                .collect(),
            |a, b| napp("And.intro", vec![a, b]),
        )
    }

    /// Supply the declared binders as `Exists.intro` witnesses around a
    /// proof of the bare conjunction, rebuilding the `∃` nest of
    /// [`Self::body`] outermost-first. The identity without binders,
    /// keeping binder-free proof terms byte-stable.
    fn exists_intro_nest(&self, conj_proof: SurfaceExpr) -> SurfaceExpr {
        self.exists_binders.iter().rev().fold(conj_proof, |acc, b| {
            napp("Exists.intro", vec![ident(&b.name), acc])
        })
    }

    /// `∀ b⃗, chain` — this disjunct's ∃-bound binders as leading explicit
    /// `∀`s (used by the `cases` arm types; the intro statement uses the
    /// wider `intro_binders` group through [`forall_group`]). The identity
    /// without binders, keeping v1 statements byte-stable.
    fn forall_binders(&self, chain: SurfaceExpr) -> SurfaceExpr {
        forall_group(&self.exists_binders, chain)
    }
}

/// `∀ binders, chain`; the identity for an empty group.
pub(super) fn forall_group(binders: &[SurfaceBinder], chain: SurfaceExpr) -> SurfaceExpr {
    if binders.is_empty() {
        return chain;
    }
    SurfaceExpr::Pi(Span::dummy(), binders.to_vec(), Box::new(chain))
}

/// Destructure the `∃ b⃗` layer of `h` — one `Exists.elim` per binder, the
/// witness rebound under its DECLARED name so the continuation can speak in
/// it — then hand the innermost proof (the bare conjunction) to `inner`.
/// The identity at zero binders, keeping binder-free proofs byte-stable.
pub(super) fn exists_elim_nest(
    binders: &[SurfaceBinder],
    h: SurfaceExpr,
    inner: &dyn Fn(SurfaceExpr) -> SurfaceExpr,
) -> SurfaceExpr {
    match binders.split_first() {
        None => inner(h),
        Some((b, rest)) => {
            let hex = format!("{HYP_EX_PREFIX}{}", rest.len());
            napp(
                "Exists.elim",
                vec![
                    h,
                    lam(
                        &[b.name.as_str(), hex.as_str()],
                        exists_elim_nest(rest, ident(&hex), inner),
                    ),
                ],
            )
        }
    }
}

impl Shape {
    /// The shared index-binder row (see the field doc on [`Shape`]).
    fn idx_names(&self) -> &[String] {
        &self.idx_names
    }

    /// The declaration-parameter row as arguments (`p₁ … pₖ`). Empty for
    /// every pre-rung shape.
    fn param_args(&self) -> Vec<SurfaceExpr> {
        self.params.iter().map(|b| ident(&b.name)).collect()
    }

    /// The declaration-parameter row as binders at the requested info
    /// (EXPLICIT everywhere except `P.cases`, where the row is implicit
    /// like the index row).
    fn param_binders(&self, info: SurfaceBinderInfo) -> Vec<SurfaceBinder> {
        self.params
            .iter()
            .map(|b| SurfaceBinder {
                span: b.span,
                name: b.name.clone(),
                ty: b.ty.clone(),
                default: None,
                info,
            })
            .collect()
    }

    /// `params ++ rest` — the leading binder row of every companion. The
    /// identity at zero parameters, keeping pre-rung output byte-stable.
    fn with_params(&self, rest: Vec<SurfaceBinder>) -> Vec<SurfaceBinder> {
        let mut out = self.param_binders(SurfaceBinderInfo::Explicit);
        out.extend(rest);
        out
    }

    /// `name p⃗ args…` — apply a companion to the FIXED parameter row
    /// first. [`app`] flattens, so at zero parameters this is byte-stable
    /// with the pre-rung `napp`.
    fn papp(&self, name: &str, args: Vec<SurfaceExpr>) -> SurfaceExpr {
        app(app(ident(name), self.param_args()), args)
    }

    /// `P.F p⃗ rel` — the one-step functor at the fixed row.
    fn f_applied(&self, rel: SurfaceExpr) -> SurfaceExpr {
        self.papp(&self.f_name(), vec![rel])
    }

    /// `T₁ → … → Tₙ → Prop` — the type of a candidate relation.
    fn rel_ty(&self) -> SurfaceExpr {
        self.idx_tys
            .iter()
            .rev()
            .fold(prop(), |acc, t| arrow(t.clone(), acc))
    }

    /// `(v₁ : T₁) … (vₙ : Tₙ)` binders at the requested binder info.
    fn idx_binders(&self, info: SurfaceBinderInfo) -> Vec<SurfaceBinder> {
        self.idx_names()
            .iter()
            .zip(&self.idx_tys)
            .map(|(v, t)| binder(v, t.clone(), info))
            .collect()
    }

    fn var_args(&self) -> Vec<SurfaceExpr> {
        self.idx_names().iter().map(|v| ident(v)).collect()
    }

    /// `head v₁ … vₙ`.
    fn applied(&self, head: SurfaceExpr) -> SurfaceExpr {
        app(head, self.var_args())
    }

    /// `∀ (v₁ : T₁) … (vₙ : Tₙ), body`.
    fn forall_vars(&self, body: SurfaceExpr) -> SurfaceExpr {
        SurfaceExpr::Pi(
            Span::dummy(),
            self.idx_binders(SurfaceBinderInfo::Explicit),
            Box::new(body),
        )
    }

    /// The one-step functor body: the right-nested `Or` of the disjunct
    /// bodies. No `Or` wrapper is minted at K = 1 — the K=1 minimization
    /// that keeps the v1 output byte-stable.
    fn functor_body(&self, rel_head: &SurfaceExpr) -> SurfaceExpr {
        right_nest(
            self.disjuncts.iter().map(|d| d.body(rel_head)).collect(),
            or,
        )
    }

    fn f_name(&self) -> String {
        format!("{}.F", self.qname)
    }
    fn coind_name(&self) -> String {
        format!("{}.coind", self.qname)
    }
    fn mono_name(&self) -> String {
        format!("{}.F_mono", self.qname)
    }
    fn unfold_name(&self) -> String {
        format!("{}.unfold", self.qname)
    }
    fn fold_name(&self) -> String {
        format!("{}.fold", self.qname)
    }
    fn cases_name(&self) -> String {
        format!("{}.cases", self.qname)
    }
    fn acc_name(&self) -> String {
        format!("{}.acc", self.qname)
    }
    fn upto_name(&self) -> String {
        format!("{}.coind_upto", self.qname)
    }
}

// ── proof-term combinators ───────────────────────────────────────────────

/// The accessor for the `i`-th conjunct of a right-nested `j`-conjunction
/// proof `h`: `And.left (And.right (… h))`, and plain `h` when `j == 1`.
pub(super) fn conjunct(h: SurfaceExpr, i: usize, j: usize) -> SurfaceExpr {
    let mut acc = h;
    for _ in 0..i {
        acc = napp("And.right", vec![acc]);
    }
    if i + 1 < j {
        acc = napp("And.left", vec![acc]);
    }
    acc
}

/// Inject a proof of disjunct `i`'s body into the `k`-way right-nested
/// disjunction: `Or.inr^i` around one `Or.inl` (elided at the LAST position,
/// which is the raw tail of the nest). The identity at `k == 1`, keeping the
/// v1 proof terms byte-stable.
fn inject(i: usize, k: usize, proof: SurfaceExpr) -> SurfaceExpr {
    let mut acc = proof;
    if i + 1 < k {
        acc = napp("Or.inl", vec![acc]);
    }
    for _ in 0..i {
        acc = napp("Or.inr", vec![acc]);
    }
    acc
}

/// Right-nested `Or.elim` cascade over disjuncts `i..k`, with `cur` proving
/// the remaining disjunction: `branch(i, hᵢ)` consumes a proof of disjunct
/// `i`'s body and must produce the (shared) result type. At `k == 1` the
/// sole branch is applied directly — no `Or` layer exists (mirroring
/// [`Shape::functor_body`]), so K = 1 proof terms stay byte-stable with v1.
fn or_elim_cascade(
    i: usize,
    k: usize,
    cur: SurfaceExpr,
    branch: &dyn Fn(usize, SurfaceExpr) -> SurfaceExpr,
) -> SurfaceExpr {
    if i + 1 == k {
        return branch(i, cur);
    }
    let hd = format!("{HYP_HD_PREFIX}{i}");
    let ht = format!("{HYP_HT_PREFIX}{i}");
    napp(
        "Or.elim",
        vec![
            cur,
            lam(&[&hd], branch(i, ident(&hd))),
            lam(&[&ht], or_elim_cascade(i + 1, k, ident(&ht), branch)),
        ],
    )
}

/// The shared `fun v⃗ hyp => …` binder row of a generated proof lambda: the
/// index names followed by ONE generated hypothesis name.
fn lam_names_of<'a>(s: &'a Shape, hyp: &'a str) -> Vec<&'a str> {
    s.idx_names()
        .iter()
        .map(String::as_str)
        .chain(std::iter::once(hyp))
        .collect()
}

// ── generation ───────────────────────────────────────────────────────────

pub(super) fn generate(s: &Shape) -> Vec<SurfaceDecl> {
    let k = s.disjuncts.len();
    let rel_ty = s.rel_ty();
    // `P p⃗` — the greatest fixpoint at the FIXED declaration-parameter row
    // (bare `P` at zero parameters; every companion reference below rides
    // the same row through `Shape::papp`/`Shape::f_applied`).
    let gfp = || s.papp(&s.qname, Vec::new());
    // `fun v⃗ h_coind => …` — the shared binder row of every generated proof.
    let lam_names: Vec<&str> = lam_names_of(s, HYP_H);

    // ── 1. the one-step functor ────────────────────────────────────────
    // def P.F (p⃗ : A⃗) (R : T⃗ → Prop) (v⃗ : T⃗) : Prop
    //   := ⋁_c ⋀ⱼ Prem_cⱼ[P p⃗ := R]
    let mut f_binders = vec![binder(REL_R, rel_ty.clone(), SurfaceBinderInfo::Explicit)];
    f_binders.extend(s.idx_binders(SurfaceBinderInfo::Explicit));
    let f_def = mk_def(
        s.f_name(),
        s.with_params(f_binders),
        prop(),
        s.functor_body(&ident(REL_R)),
    );

    // `∀ v⃗, rel v⃗ → P.F p⃗ rel v⃗` — "rel is a post-fixpoint of the functor".
    let post_of = |rel: SurfaceExpr| {
        s.forall_vars(arrow(s.applied(rel.clone()), s.applied(s.f_applied(rel))))
    };

    // ── 2. the greatest fixpoint ───────────────────────────────────────
    // def P (p⃗ : A⃗) (v⃗ : T⃗) : Prop
    //   := ∃ R, (∀ v⃗, R v⃗ → P.F p⃗ R v⃗) ∧ R v⃗
    let gfp_def = mk_def(
        s.qname.clone(),
        s.with_params(s.idx_binders(SurfaceBinderInfo::Explicit)),
        prop(),
        napp(
            "Exists",
            vec![SurfaceExpr::Lambda(
                Span::dummy(),
                vec![binder(REL_R, rel_ty.clone(), SurfaceBinderInfo::Explicit)],
                Box::new(and(post_of(ident(REL_R)), s.applied(ident(REL_R)))),
            )],
        ),
    );

    // ── 3. Park coinduction ────────────────────────────────────────────
    // theorem P.coind (p⃗) (R) (post : ∀ v⃗, R v⃗ → P.F p⃗ R v⃗)
    //     : ∀ v⃗, R v⃗ → P p⃗ v⃗ :=
    //   fun v⃗ h => Exists.intro R (And.intro post h)
    let coind_thm = mk_theorem(
        s.coind_name(),
        s.with_params(vec![
            binder(REL_R, rel_ty.clone(), SurfaceBinderInfo::Explicit),
            binder(HYP_POST, post_of(ident(REL_R)), SurfaceBinderInfo::Explicit),
        ]),
        s.forall_vars(arrow(s.applied(ident(REL_R)), s.applied(gfp()))),
        lam(
            &lam_names,
            napp(
                "Exists.intro",
                vec![
                    ident(REL_R),
                    napp("And.intro", vec![ident(HYP_POST), ident(HYP_H)]),
                ],
            ),
        ),
    );

    // ── 4. monotonicity of the generated functor ───────────────────────
    // theorem P.F_mono (R) (S) (hle : ∀ v⃗, R v⃗ → S v⃗)
    //     : ∀ v⃗, P.F R v⃗ → P.F S v⃗ :=
    //   fun v⃗ h => Or.elim h (fun hd => Or.inl ⟨…, hle e⃗ hd.right…, …⟩) …
    //
    // Sound by construction: every recursive premise is a POSITIVE,
    // fully-applied occurrence (the envelope enforces it), so each disjunct
    // is rebuilt through `hle` and re-injected at ITS OWN `Or` position.
    let mono_val = lam(
        &lam_names,
        or_elim_cascade(0, k, ident(HYP_H), &|i, h| {
            inject(i, k, s.disjuncts[i].mono_image(&h))
        }),
    );
    let mono_thm = mk_theorem(
        s.mono_name(),
        s.with_params(vec![
            binder(REL_R, rel_ty.clone(), SurfaceBinderInfo::Explicit),
            binder(REL_S, rel_ty.clone(), SurfaceBinderInfo::Explicit),
            binder(
                HYP_LE,
                s.forall_vars(arrow(s.applied(ident(REL_R)), s.applied(ident(REL_S)))),
                SurfaceBinderInfo::Explicit,
            ),
        ]),
        s.forall_vars(arrow(
            s.applied(s.f_applied(ident(REL_R))),
            s.applied(s.f_applied(ident(REL_S))),
        )),
        mono_val,
    );

    // ── 5. the gfp is a post-fixpoint (the destructor) ─────────────────
    // theorem P.unfold : ∀ v⃗, P v⃗ → P.F P v⃗ :=
    //   fun v⃗ h => Exists.elim h (fun R hR =>
    //     P.F_mono R P (P.coind R hR.left) v⃗ (hR.left v⃗ hR.right))
    let post_hyp = napp("And.left", vec![ident(HYP_HR)]);
    let carrier_hyp = napp("And.right", vec![ident(HYP_HR)]);
    let mut mono_args = vec![
        ident(REL_R),
        gfp(),
        s.papp(&s.coind_name(), vec![ident(REL_R), post_hyp.clone()]),
    ];
    mono_args.extend(s.var_args());
    mono_args.push(app(
        post_hyp,
        s.var_args().into_iter().chain([carrier_hyp]).collect(),
    ));
    let unfold_thm = mk_theorem(
        s.unfold_name(),
        s.with_params(Vec::new()),
        s.forall_vars(arrow(s.applied(gfp()), s.applied(s.f_applied(gfp())))),
        lam(
            &lam_names,
            napp(
                "Exists.elim",
                vec![
                    ident(HYP_H),
                    lam(&[REL_R, HYP_HR], s.papp(&s.mono_name(), mono_args)),
                ],
            ),
        ),
    );

    // ── 6. the gfp is a pre-fixpoint ───────────────────────────────────
    // theorem P.fold : ∀ v⃗, P.F P v⃗ → P v⃗ :=
    //   P.coind (P.F P) (fun v⃗ h => P.F_mono P (P.F P) P.unfold v⃗ h)
    let f_gfp = || s.f_applied(gfp());
    let mut fold_mono_args = vec![gfp(), f_gfp(), s.papp(&s.unfold_name(), Vec::new())];
    fold_mono_args.extend(s.var_args());
    fold_mono_args.push(ident(HYP_H));
    let fold_thm = mk_theorem(
        s.fold_name(),
        s.with_params(Vec::new()),
        s.forall_vars(arrow(s.applied(f_gfp()), s.applied(gfp()))),
        s.papp(
            &s.coind_name(),
            vec![
                f_gfp(),
                lam(&lam_names, s.papp(&s.mono_name(), fold_mono_args)),
            ],
        ),
    );

    // ── 6b/6c. the paco/accumulation companions ────────────────────────
    // `P.acc` (strong coinduction) and `P.coind_upto` (Park up to a
    // compatible closure) — built in the [`paco`] child module.
    let acc_thm = paco::acc_thm(s);
    let upto_thm = paco::upto_thm(s);

    let mut decls = vec![
        f_def, gfp_def, coind_thm, mono_thm, unfold_thm, fold_thm, acc_thm, upto_thm,
    ];

    // ── 6d. the parameterized paco tower ───────────────────────────────
    // `P.paco` and its lemmas (`paco_coind`/`paco_unfold`/`paco_fold`/
    // `paco_mon`/`paco_bot`/`le_paco`/`paco_acc`) — the faithful
    // per-declaration mirror of the library's paco section, built in the
    // [`paco`] child module (see its module doc for statements and union
    // order).
    decls.extend(paco::tower(s));

    // ── 7. the declared constructors ───────────────────────────────────
    // theorem P.cᵢ (p⃗) {fresh rows} : ∀ b⃗ᵢ, Premᵢ₁ → … → Premᵢⱼ → P p⃗ a⃗ᵢ :=
    //   fun b⃗ᵢ h₁ … hⱼ =>
    //     P.fold p⃗ a⃗ᵢ (Or.inrⁱ (Or.inl (Exists.intro b⃗ᵢ
    //       ⟨Eq.refl w₁, …, Eq.refl w_m, h₁, …, hⱼ⟩)))
    //
    // The intro concludes at the WRITTEN target `P p⃗ a⃗ᵢ` (Brick 3): the
    // declaration-parameter row leads EXPLICITLY (the documented deviation
    // from the inductive lane's implicit ctor params — see [`params`]), its
    // implicit header binds exactly the fresh substituted rows, the leading
    // explicit ∀ group is every declared binder (a substituted one under
    // its row name — see the plan's `intro_binders`), and each index
    // equation is closed by `Eq.refl` at the written term, where the
    // instantiated row makes it reflexive. One hypothesis per DECLARED
    // premise, injected at the constructor's own `Or` position. For a
    // v1-shaped constructor every piece degenerates to the old output:
    // whole-row implicit header, ∃-binders group, no `Eq.refl`s.
    for (i, plan) in s.disjuncts.iter().enumerate() {
        let declared = plan.declared_premises(&gfp());
        let hyp_names: Vec<String> = (0..declared.len())
            .map(|c| format!("hprem_coind{c}"))
            .collect();
        let target = app(gfp(), plan.target_args.clone());
        let chain = declared
            .into_iter()
            .rev()
            .fold(target, |acc, p| arrow(p, acc));
        let ctor_ty = forall_group(&plan.intro_binders, chain);
        let packed = right_nest(
            plan.equations
                .iter()
                .map(IndexEquation::refl)
                .chain(hyp_names.iter().map(|h| ident(h)))
                .collect(),
            |a, b| napp("And.intro", vec![a, b]),
        );
        let lam_refs: Vec<&str> = plan
            .intro_binders
            .iter()
            .map(|b| b.name.as_str())
            .chain(hyp_names.iter().map(String::as_str))
            .collect();
        let header: Vec<SurfaceBinder> = plan
            .fresh_rows
            .iter()
            .map(|&r| {
                binder(
                    &s.idx_names[r],
                    s.idx_tys[r].clone(),
                    SurfaceBinderInfo::Implicit,
                )
            })
            .collect();
        decls.push(mk_theorem(
            format!("{}.{}", s.qname, plan.ctor),
            s.with_params(header),
            ctor_ty,
            lam(
                &lam_refs,
                s.papp(
                    &s.fold_name(),
                    plan.target_args
                        .iter()
                        .cloned()
                        .chain([inject(i, k, plan.exists_intro_nest(packed))])
                        .collect(),
                ),
            ),
        ));
    }

    // ── 8. one-step inversion ──────────────────────────────────────────
    // theorem P.cases {v⃗ : T⃗} : P v⃗ → ∀ (C : Prop),
    //     (∀ b⃗₁, eqs₁ → Prem₁₁ → … → C) → … → C :=
    //   fun h C arm₁ … arm_K => Or.elim (P.unfold v⃗ h)
    //     (fun hd => arm₁ hd₍₁₎ … hd₍ⱼ₎) (fun ht => …)
    //
    // Case analysis over ONE unfolding — `Or.elim`/`Exists.elim`/`And`-
    // destructure of `P.unfold` with a CONSTANT `C : Prop` motive (fully
    // general here: the indices are fixed by the statement — the
    // adopted-plan decision). Each arm's continuation takes the
    // constructor's ∃-bound binders as leading ∀s (Brick 2), then one
    // hypothesis per index equation `writtenᵢ = vᵢ` (Brick 3 — how an arm
    // learns which indices its constructor concludes at), then the
    // premises. NOT an induction principle: each arm sees the recursive
    // premises at `P` itself, with no recursive call available.
    let arm_names: Vec<String> = (0..k).map(|i| format!("{ARM_PREFIX}{i}")).collect();
    let cases_ty = arrow(
        s.applied(gfp()),
        SurfaceExpr::Pi(
            Span::dummy(),
            vec![binder(MOTIVE_C, prop(), SurfaceBinderInfo::Explicit)],
            Box::new(
                s.disjuncts
                    .iter()
                    .map(|plan| {
                        plan.forall_binders(
                            plan.equations
                                .iter()
                                .map(IndexEquation::prop)
                                .chain(plan.declared_premises(&gfp()))
                                .collect::<Vec<_>>()
                                .into_iter()
                                .rev()
                                .fold(ident(MOTIVE_C), |acc, p| arrow(p, acc)),
                        )
                    })
                    .rev()
                    .fold(ident(MOTIVE_C), |acc, arm| arrow(arm, acc)),
            ),
        ),
    );
    let cases_lam_names: Vec<&str> = [HYP_H, MOTIVE_C]
        .into_iter()
        .chain(arm_names.iter().map(String::as_str))
        .collect();
    let mut unfold_args = s.var_args();
    unfold_args.push(ident(HYP_H));
    let cases_val = lam(
        &cases_lam_names,
        or_elim_cascade(0, k, s.papp(&s.unfold_name(), unfold_args), &|i, h| {
            // Destructure this disjunct's `∃ b⃗` layer, then hand the arm
            // the witnesses followed by one hypothesis per functor-body
            // conjunct ([`DisjunctPlan::conjuncts`] order).
            let plan = &s.disjuncts[i];
            let j = plan.equations.len() + plan.premises.len();
            exists_elim_nest(&plan.exists_binders, h, &|hconj| {
                app(
                    ident(&arm_names[i]),
                    plan.exists_binders
                        .iter()
                        .map(|b| ident(&b.name))
                        .chain((0..j).map(|c| conjunct(hconj.clone(), c, j)))
                        .collect(),
                )
            })
        }),
    );
    // The parameter row on `P.cases` is IMPLICIT, exactly like the index
    // row: both are forced by the major premise `P p⃗ v⃗` (the one
    // companion where the row is not explicit — see the module docs).
    let mut cases_binders = s.param_binders(SurfaceBinderInfo::Implicit);
    cases_binders.extend(s.idx_binders(SurfaceBinderInfo::Implicit));
    decls.push(mk_theorem(
        s.cases_name(),
        cases_binders,
        cases_ty,
        cases_val,
    ));

    decls
}
