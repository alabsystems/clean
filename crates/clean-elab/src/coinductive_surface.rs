// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The `coinductive` predicate surface (#191, rank 1 of the coinduction
//! ladder): a Lean 4.25-style `coinductive` **Prop-valued** declaration
//! lowered to the impredicative greatest-fixpoint encoding Clean's kernel
//! already checks — no kernel cofix, no new `ExprKind`, no new reduction
//! rule, **zero new axioms**.
//!
//! ```text
//! coinductive Bisim : Str → Str → Prop
//! | step : shd s = shd t → Bisim (stl s) (stl t) → Bisim s t
//! ```
//!
//! generates, and kernel-checks, exactly the shapes the hand-written
//! `data/graduation/clean-coind/proof/Coind.lean` core pins:
//!
//! ```text
//! Bisim.F      : (Str → Str → Prop) → Str → Str → Prop   one-step functor
//! Bisim        : Str → Str → Prop                        gfp = ⋃ post-fixpoints
//! Bisim.coind  : Park coinduction — every post-fixpoint is below the gfp
//! Bisim.F_mono : monotonicity of the generated functor
//! Bisim.unfold : the gfp is a post-fixpoint (the destructor)
//! Bisim.fold   : the gfp is a pre-fixpoint (needs monotonicity)
//! Bisim.step   : the declared constructor, proved through `fold`
//! Bisim.cases  : one-step inversion — `Or.elim`/`And`-destructure of `unfold`
//! Bisim.acc    : accumulation — the candidate may fall back on Bisim itself
//! Bisim.coind_upto : Park up to a compatible closure of the candidate
//! Bisim.paco   : the parameterized gfp — plus its tower (paco_coind,
//!                paco_unfold, paco_fold, paco_mon, paco_bot, le_paco,
//!                paco_acc); see the P.paco paragraph below
//! ```
//!
//! With K ≥ 2 constructors (Brick 1 of
//! `designs/2026-08-25-rank1-full-gfp-lowering.md`) the functor body is the
//! right-nested `Or` of the per-constructor disjuncts (no `Or` layer is
//! minted at K = 1, keeping the v1 output byte-stable), one intro theorem
//! `P.<cᵢ>` is generated per constructor via the matching `Or` injection,
//! `P.F_mono` and `P.cases` case-split with an `Or.elim` cascade, and every
//! constructor's target variables are α-renamed onto the FIRST constructor's
//! target row (the shared index binders). The rename is capture-honoring and
//! fail-closed: a premise that shadows a renamed variable, or mentions a
//! shared-row name as a constant, REFUSES (see [`rename_free`]).
//!
//! With LEADING constructor binders (Brick 2) — `| step (q : St) : Prem →
//! P a⃗` — each declared binder becomes an `∃`-bound variable of that
//! constructor's functor disjunct, in declaration order (`∃ b⃗, ⋀ …`). The
//! intro theorem takes the binders as leading `∀`s and supplies them to
//! `Exists.intro` before the conjunction, `P.F_mono` destructures the `∃`
//! layer with `Exists.elim` and rebuilds it around the premise-mapped
//! conjunction with the SAME witnesses (sound because binder types are
//! P-free by the envelope), and each `P.cases` arm takes the constructor's
//! binders (`∀ b⃗ᵢ, Prem⃗ᵢ → C`), the `∃` destructured in the proof.
//!
//! With COMPOUND targets (Brick 3) — `| step (k : Nat) : P k →
//! P (Nat.succ k)` — a target position that is not an index-substituted
//! bare variable contributes an index EQUATION to its disjunct, before the
//! premises: `∃ k, (Nat.succ k = v) ∧ R k`. The ORIENTATION is pinned —
//! written target on the LEFT, shared index binder on the right
//! (`IndexEquation::prop` is the single point that spells it) — and the
//! equations are HOMOGENEOUS by construction: the index telescope is
//! non-dependent (a dependent one refuses at the signature), so both sides
//! live at the declared index type; no heterogeneous equality, and no
//! funext demand is ever made — an equation at a function-typed index is
//! just `Eq` at the Pi type. Intro theorems conclude at the WRITTEN target
//! and close each equation with `Eq.refl written`; `P.F_mono` carries
//! equations through unchanged (they never mention `R`); each `P.cases`
//! arm receives them as hypotheses between the `∃`-binders and the
//! premises (`∀ b⃗ᵢ, eq⃗ᵢ → Prem⃗ᵢ → C`) — how an arm learns which indices
//! its constructor concluded at, and what `Nat.noConfusion`-style
//! discrimination consumes.
//!
//! With DECLARATION PARAMETERS (the declaration-parameters rung) —
//! `coinductive P (p₁ : A₁) … (pₖ : Aₖ) : T⃗ → Prop` — the parameter row
//! is FIXED through the coinduction: every companion takes the row as
//! leading binders (encoding (b) of the rung — see [`params`] for the
//! choice and its rationale), the candidate relation stays `T⃗ → Prop` at
//! fixed `p⃗`, and the recursive substitution happens at `P p⃗` only.
//! Constructors must apply `P` to EXACTLY the declared row first — in the
//! target and in every recursive occurrence (mirroring the kernel's strict
//! inductive discipline, `inductive/strict.rs` check 3) — a position that
//! varies is an INDEX, not a parameter, and refuses by name. The row is
//! EXPLICIT on every companion except `P.cases`, where it is implicit like
//! the index row. Universe parameters stay refused by name. The
//! zero-parameter output is byte-identical to the pre-rung output (golden-
//! pinned).
//!
//! The PACO / ACCUMULATION rung (the per-declaration half of item 6,
//! `designs/2026-08-20-rank1-coinductive-surface.md:131-134`) mints `P.acc`
//! — strong coinduction: the candidate may step into `P.F (R ∨ P)`, falling
//! back on ACCUMULATED P-knowledge — and `P.coind_upto` — the faithful
//! specialization of the library `gfpRel_upto`: Park where the obligation
//! targets `P.F (clo R)` for a caller-supplied monotone / `P.F`-compatible /
//! idempotent / inflationary closure (quantifying over `clo` is intrinsic;
//! `Mono F` specializes away through the minted `P.F_mono`). `P.acc` is the
//! `clo := (· ∨ P)` instance, minted directly with a smaller proof term; it
//! is the `r := ⊥` top-level projection of the library `paco_acc`. Both
//! proofs are self-contained terms from `P.coind` / `P.F_mono` /
//! `P.unfold`: the library file is graduated DATA, not a compiled
//! dependency, so nothing here applies its theorems by name.
//!
//! The `P.paco` PARAMETERIZED-TOWER rung (the named follow-on, landed)
//! mints the faithful per-declaration mirror of the library's paco
//! section: `P.paco r` — the gfp of `fun R => P.F (R ∨ r)`, same
//! impredicative encoding as `P` — with `P.paco_coind` / `P.paco_unfold` /
//! `P.paco_fold` (Park/destructor/constructor at the accumulated functor),
//! `P.paco_mon` (monotone in `r`), the two-implication `⊥` correspondence
//! `P.paco_bot` / `P.le_paco` (the library's `paco_bot_le_gfp` /
//! `gfp_le_paco`, the latter kept generalized over `r`), and the faithful
//! accumulation `P.paco_acc` (`r' ≤ P.paco (r ∨ r') → r' ≤ P.paco r`) —
//! compositional pcofix-style coinduction, nestable level over level.
//! `P.acc`/`P.coind_upto` are unchanged by the rung. Statement shapes,
//! union orders and proof routes live on the paco child module
//! (`coinductive_surface_paco.rs`).
//!
//! The fixpoint is the standard impredicative union of post-fixpoints
//! (`Coind.lean`'s `gfpRel`) at the declaration's own index telescope:
//!
//! ```text
//! P v⃗ := ∃ R, (∀ v⃗, R v⃗ → P.F R v⃗) ∧ R v⃗
//! ```
//!
//! No induction principle is generated, and none exists: `P` is a `def`, not
//! an inductive type, so there is no `P.rec` to misuse. `P.cases` is NOT one:
//! it destructures a SINGLE unfolding (each arm sees the recursive premises
//! at `P` itself, with a constant `C : Prop` motive — fully general here
//! because the indices are fixed by the statement), and it is proved, not
//! trusted.
//!
//! # v1 envelope (everything outside it REJECTS LOUDLY)
//!
//! A narrow envelope is the point. A `coinductive` declaration must never
//! quietly acquire least-fixpoint meaning, so every shape this module does
//! not fully understand is an [`ElabError::Unsupported`] naming the offending
//! clause — never a best-effort lowering:
//!
//! * result sort `Prop`, reached through a NON-dependent arrow telescope of
//!   arity ≥ 1 (`P : T₁ → … → Tₙ → Prop`);
//! * declaration parameters `(p : A)` are supported as a FIXED row:
//!   explicit binder info only, explicitly typed, types `P`-free with
//!   constant/earlier-parameter free names; every constructor applies `P`
//!   to exactly the row first (target and recursive premises); a bare
//!   parameter name in an INDEX position refuses (ambiguous with a fresh
//!   index variable — write it ascribed, `(p : T)`, to equate); a
//!   constructor, guard or `∃`-conclusion binder shadowing a parameter
//!   name refuses. NO universe parameters (refused by name), no
//!   `deriving`, no modifiers;
//! * at least ONE constructor, with pairwise-DISTINCT names. K = 0 refuses:
//!   an empty disjunction would mint the constantly-False predicate;
//! * every constructor's type is `∀ (b₁ : B₁) … (b_m : B_m), Prem₁ → … →
//!   Premⱼ → P a⃗` (m ≥ 0; equations + premises ≥ 1 — see below): optional
//!   LEADING explicitly-typed binders, then a plain arrow chain of
//!   premises. A binder AFTER the first premise arrow (a dependent premise
//!   telescope) refuses;
//! * each target argument `aᵢ` (Brick 3) is an applicative, hole-free,
//!   P-free term over the constructor's declared binders, its
//!   index-substituted variables and registered constants. A position that
//!   is a bare FRESH variable substitutes at its first bare occurrence
//!   (later bare occurrences equate — `P x x` is admitted, first binds the
//!   index, the second carries `x = v₂`); a bare DECLARED BINDER
//!   substitutes when once-occurring with its declared type structurally
//!   the index type, and otherwise stays ∃-bound behind an equation; a
//!   bare REGISTERED CONSTANT refuses (ambiguous between v1's
//!   fresh-variable reading and the constant — write `(c : T)` for the
//!   constant reading); every other term equates. A fresh variable
//!   occurring ONLY inside compound arguments has no bare position to bind
//!   it and refuses (declare a binder to ∃-bind it);
//! * per-constructor vacuity: index equations + premises ≥ 1. An
//!   equations-only constructor (`| nil : CB 0 0`) is legal — its disjunct
//!   is the equations conjunction — but no equations AND no premises would
//!   make the disjunct constantly true, refused;
//! * each leading binder not consumed by the substitution minimization
//!   becomes an `∃`-bound variable of this constructor's disjunct, in
//!   declaration order. Its TYPE must be P-free (a predicate occurrence
//!   inside a binder type is a nested / negative-position hazard — the
//!   next rung's problem, refused here), its free variables drawn from the
//!   index-substituted target variables, earlier binders and existing
//!   constants. Its NAME must be workable beyond doubt: not `_` (the intro
//!   theorem must supply it as an `Exists.intro` witness), not
//!   implicit/instance, not carrying a default value, not the predicate,
//!   not declared twice, not carrying the generated `_coind` marker, not a
//!   shared-index-row name (the α-rename would be captured; exempt when
//!   the binder itself substitutes — it never ∃-binds then);
//! * from the second constructor on, the α-rename onto the shared index row
//!   must be beyond doubt: a premise binder shadowing a renamed variable
//!   refuses, and a free occurrence of a shared-row name that is not one of
//!   this constructor's own index-substituted variables refuses (it denotes
//!   a constant the row binder would capture);
//! * each premise is a fully-applied recursive occurrence `P e⃗` (arity n,
//!   positional, arguments free of `P`), a premise not mentioning `P` at
//!   all, or — the "P under `∀`/`→`" rung — a parenthesized GUARDED clause
//!   `(∀ b⃗, H₁ → … → Hₙ → C)` whose binders are explicitly typed with
//!   `P`-free types, whose hypotheses are `P`-free, and whose conclusion is
//!   a recursive atom or a positive `∃`-nest over `P`-free conjuncts and
//!   recursive atoms (the Milner weak-bisimulation clause shape; full
//!   envelope, `F_mono` guard mapping and refusal catalog in [`guard`]) —
//!   so recursive occurrences are strictly positive by construction and
//!   the generated `F_mono` proof is always available;
//! * each premise is applicative (identifiers, applications, arrows,
//!   binders); `match` / `do` / tactic premises reject;
//! * every free variable of a premise is a target variable, a declared
//!   leading binder of its constructor, or an existing constant. This
//!   clause is load-bearing: a stray free name would be silently AUTO-BOUND
//!   as an implicit parameter of the generated functor, changing what the
//!   declaration means. A premise-only variable WITHOUT a declared binder
//!   keeps this refusal — the explicit binder is the deliberate tax for an
//!   ∃-bound variable.
//!
//! [`lower`] is pure — it returns surface declarations. The caller elaborates
//! them through the ordinary parse→elaborate→kernel-check path, so every
//! generated definition and theorem is kernel-re-checked exactly like
//! hand-written source.

use crate::ElabError;
use clean_kernel::{Environment, Name};
use clean_parser::{
    DeclModifiers, Span, SurfaceBinder, SurfaceCtor, SurfaceDecl, SurfaceExpr, UniverseExpr,
};

/// Generation half (validated [`Shape`] → surface declarations). Split along
/// the validation/generation seam to keep both files under the paragon
/// file-length ratchet; same module tree, so privacy is unchanged.
#[path = "coinductive_surface_generate.rs"]
mod generate;

/// Target-row analysis (Brick 3): per-position substitution/equation
/// classification and the α-rename helper. Same module-tree split as
/// [`generate`].
#[path = "coinductive_surface_target.rs"]
mod target;

/// Premise classification, including the GUARDED clause envelope of the
/// "P under `∀`/`→`" rung (`∀ b⃗, H₁ → … → Hₙ → C`, `P` strictly positive
/// in the conclusion — atom or `∃`-nest), its `F_mono` guard mapping and
/// its α-rename. Same module-tree split as [`generate`].
#[path = "coinductive_surface_guard.rs"]
mod guard;

/// Declared binder rows: DECLARATION-PARAMETER validation (the
/// declaration-parameters rung — envelope, encoding choice (b) and the
/// exact-row check mirroring the kernel's strict inductive discipline)
/// plus the constructor-binder envelope (Brick 2, moved there whole).
/// Same module-tree split as [`generate`].
#[path = "coinductive_surface_params.rs"]
mod params;

use guard::{classify_premise, Premise};
use target::TargetPos;

/// Companion suffixes this lowering mints under the declaration's name.
/// A constructor may not claim one of them. The second row is the
/// parameterized paco tower (`P.paco` rung).
const RESERVED_SUFFIXES: [&str; 16] = [
    "F",
    "coind",
    "F_mono",
    "unfold",
    "fold",
    "cases",
    "acc",
    "coind_upto",
    "paco",
    "paco_coind",
    "paco_unfold",
    "paco_fold",
    "paco_mon",
    "paco_bot",
    "le_paco",
    "paco_acc",
];

/// Generated binder names, all carrying the `coind` marker so they cannot
/// collide with a target variable (those are checked to be plain identifiers
/// drawn from the user's constructor).
const REL_R: &str = "R_coind";
const REL_S: &str = "S_coind";
const HYP_POST: &str = "hpost_coind";
const HYP_LE: &str = "hle_coind";
const HYP_H: &str = "h_coind";
const HYP_HR: &str = "hR_coind";
/// The `P.cases` motive binder.
const MOTIVE_C: &str = "C_coind";
/// Index-suffixed generated names (`{PREFIX}{i}`): the head/tail hypotheses
/// of an `Or.elim` cascade level and the per-constructor `P.cases` arms.
const HYP_HD_PREFIX: &str = "hd_coind";
const HYP_HT_PREFIX: &str = "ht_coind";
const ARM_PREFIX: &str = "arm_coind";
/// The per-level `Exists.elim` hypotheses destructuring a disjunct's `∃ b⃗`
/// layer (`{HYP_EX_PREFIX}{level}`, where `level` counts REMAINING binders,
/// so the names are distinct within one nest).
const HYP_EX_PREFIX: &str = "hex_coind";
/// The re-abstracted hypotheses of a GUARDED premise inside the `F_mono`
/// proof (`{HYP_G_PREFIX}{i}`; see [`guard`]).
const HYP_G_PREFIX: &str = "hg_coind";

fn unsupported(msg: impl Into<String>) -> ElabError {
    ElabError::Unsupported {
        feature: msg.into(),
    }
}

fn strip_parens(expr: &SurfaceExpr) -> &SurfaceExpr {
    match expr {
        SurfaceExpr::Paren(_, e) => strip_parens(e),
        _ => expr,
    }
}

/// A short label for a surface form this module refuses to analyse, so the
/// reject names the offending construct instead of dumping a debug tree.
fn variant_label(expr: &SurfaceExpr) -> &'static str {
    match expr {
        SurfaceExpr::Match(..) => "match",
        SurfaceExpr::Do(..) => "do",
        SurfaceExpr::ByTactic(..) => "by",
        SurfaceExpr::CalcBlock(..) => "calc",
        SurfaceExpr::If(..) | SurfaceExpr::IfLet(..) | SurfaceExpr::IfDecidable(..) => "if",
        SurfaceExpr::Let(..) | SurfaceExpr::LetRec(..) | SurfaceExpr::LetPattern(..) => "let",
        SurfaceExpr::PatternMatchLambda(..) => "fun | …",
        SurfaceExpr::SyntaxQuote(..) => "syntax quotation",
        SurfaceExpr::SyntheticSorry(..) => "sorry",
        _ => "unsupported term",
    }
}

// ── shape analysis ───────────────────────────────────────────────────────

/// One index equation `written = vᵢ` of a disjunct (Brick 3): `written` is
/// the constructor's target argument at that position (over the shared
/// index row, declared binders and constants), `row` the shared index
/// binder it is equated to. ORIENTATION IS PINNED: written target on the
/// LEFT (`IndexEquation::prop` in the generation half is the single point
/// that spells it; a statement-level test pins it end to end). Equations
/// are HOMOGENEOUS by construction — the index telescope is non-dependent
/// (a dependent telescope refuses at the signature), so both sides live at
/// the declared index type and no heterogeneous-equality machinery exists
/// here.
struct IndexEquation {
    written: SurfaceExpr,
    row: String,
}

/// The lowering plan for ONE constructor — one disjunct of the full rank-1
/// functor body `⋁_c ∃ b⃗_c, (⋀ᵢ aᵢ = vᵢ) ∧ ⋀ⱼ Premⱼ`
/// (`designs/2026-08-25-rank1-full-gfp-lowering.md` §1). Every expression
/// below speaks in the SHARED index row ([`Shape::idx_names`]): `validate`
/// α-renames each constructor's index-substituted target variables onto the
/// first constructor's row before the plan is built. Brick 2 populates
/// `exists_binders`; Brick 3 populates `equations` (compound / repeated /
/// non-substituted target positions) and the substitution minimizations —
/// a bare once-occurring fresh variable or type-matching declared binder
/// IS the index binder, no equation minted (v1 is exactly the case where
/// every position substitutes and all three layers vanish).
struct DisjunctPlan {
    /// Constructor short name (the `step` of `Bisim.step`).
    ctor: String,
    /// `∃ b⃗` binders for constructor-local variables (Brick 2): the
    /// constructor's LEADING explicitly-typed binders, in declaration order,
    /// validated against the binder envelope (explicit, typed, P-free type)
    /// and — from the second constructor on — with their types α-renamed
    /// onto the shared index row. A binder consumed by the substitution
    /// minimization (Brick 3) is NOT here: it became an index binder.
    exists_binders: Vec<SurfaceBinder>,
    /// Index equations for the non-substituted target positions, in
    /// position order (Brick 3). Empty exactly for v1-shaped constructors.
    equations: Vec<IndexEquation>,
    /// Premises in declaration order, over the shared index row.
    premises: Vec<Premise>,
    /// The written target arguments, one per index position, over the
    /// shared row: `vᵢ` at a substituted position, the written term at an
    /// equated one. The intro theorem concludes at `P target_args` and
    /// closes each equation with `Eq.refl written` there.
    target_args: Vec<SurfaceExpr>,
    /// The intro theorem's leading explicit `∀` group: ALL declared binders
    /// in declaration order — ∃-bound ones as declared, substituted ones
    /// under their shared-row name at their declared type. Equal to
    /// `exists_binders` when no binder was substituted (every pre-Brick-3
    /// shape).
    intro_binders: Vec<SurfaceBinder>,
    /// Index positions substituted by a FRESH variable (not a declared
    /// binder): the intro theorem binds exactly these rows implicitly (v1:
    /// every position, reproducing the old whole-row implicit header).
    fresh_rows: Vec<usize>,
}

struct Shape {
    /// Fully-qualified declaration name.
    qname: String,
    /// The FIXED declaration-parameter row, validated ([`params`]): every
    /// companion takes these as leading binders, and every occurrence of
    /// the predicate inside the declaration applies exactly this row first.
    /// Empty for every pre-rung shape (byte-stable output).
    params: Vec<SurfaceBinder>,
    /// Index telescope types, in order.
    idx_tys: Vec<SurfaceExpr>,
    /// The SHARED index-binder row: the FIRST constructor's target-variable
    /// names. Every other constructor's premises are α-renamed onto this row
    /// by `validate`, so generation reads one binder row for the whole
    /// functor. At K = 1 this is the identity of the v1 behavior.
    idx_names: Vec<String>,
    /// One plan per constructor, in declaration order (K ≥ 1; the envelope
    /// refuses K = 0). The functor body is their right-nested `Or`; no `Or`
    /// layer is minted at K = 1, keeping the v1 output byte-stable.
    disjuncts: Vec<DisjunctPlan>,
}

/// Flatten a non-dependent arrow chain, returning `(antecedents, head)`.
/// A `Pi` anywhere in the spine yields `None`: v1 rejects dependent
/// telescopes rather than mis-lowering them.
fn flatten_arrows(expr: &SurfaceExpr) -> Option<(Vec<&SurfaceExpr>, &SurfaceExpr)> {
    let mut parts = Vec::new();
    let mut cur = strip_parens(expr);
    loop {
        match cur {
            SurfaceExpr::Arrow(_, a, b) => {
                parts.push(strip_parens(a));
                cur = strip_parens(b);
            }
            SurfaceExpr::Pi(..) => return None,
            _ => return Some((parts, cur)),
        }
    }
}

/// Does `expr` mention `name` as an identifier (exactly, or as the prefix of
/// a dotted name)? Binder scoping is deliberately IGNORED — a shadowed
/// occurrence still trips the check, which errs toward rejection.
fn mentions(expr: &SurfaceExpr, name: &str) -> bool {
    let mut bound: Vec<&str> = Vec::new();
    let mut fvs: Vec<&str> = Vec::new();
    if all_idents(expr, &mut bound, &mut fvs).is_err() {
        // A form this module cannot analyse is treated as possibly mentioning
        // the name; the caller rejects either way.
        return true;
    }
    let dotted = format!("{name}.");
    fvs.iter().any(|id| *id == name || id.starts_with(&dotted))
}

/// Collect the FREE identifiers of `expr`, honouring lambda/Pi binder scope.
///
/// Returns `Err(label)` for a surface form this module refuses to analyse.
fn all_idents<'a>(
    expr: &'a SurfaceExpr,
    bound: &mut Vec<&'a str>,
    out: &mut Vec<&'a str>,
) -> Result<(), &'static str> {
    match expr {
        SurfaceExpr::Ident(_, id) => {
            let id = id.as_str();
            if !bound.contains(&id) && !out.contains(&id) {
                out.push(id);
            }
        }
        SurfaceExpr::Lit(..) | SurfaceExpr::Universe(..) | SurfaceExpr::Hole(..) => {}
        SurfaceExpr::App(_, h, args) => {
            all_idents(h, bound, out)?;
            for a in args {
                all_idents(&a.expr, bound, out)?;
            }
        }
        SurfaceExpr::Arrow(_, a, b) => {
            all_idents(a, bound, out)?;
            all_idents(b, bound, out)?;
        }
        SurfaceExpr::Lambda(_, bs, body) | SurfaceExpr::Pi(_, bs, body) => {
            let depth = bound.len();
            for b in bs {
                if let Some(t) = &b.ty {
                    all_idents(t, bound, out)?;
                }
                bound.push(b.name.as_str());
            }
            all_idents(body, bound, out)?;
            bound.truncate(depth);
        }
        SurfaceExpr::Paren(_, e)
        | SurfaceExpr::Explicit(_, e)
        | SurfaceExpr::OutParam(_, e)
        | SurfaceExpr::SemiOutParam(_, e)
        | SurfaceExpr::Proj(_, e, _)
        | SurfaceExpr::NamedArg(_, _, e)
        | SurfaceExpr::UniverseInst(_, e, _) => all_idents(e, bound, out)?,
        SurfaceExpr::Ascription(_, e, t) => {
            all_idents(e, bound, out)?;
            all_idents(t, bound, out)?;
        }
        other => return Err(variant_label(other)),
    }
    Ok(())
}

/// Is `id` already a constant of `env`? Used only to tell "constant" from
/// "stray free variable"; an unknown name rejects rather than being
/// auto-bound into the generated functor's signature.
fn known_constant(env: &Environment, id: &str) -> bool {
    env.get_const(&Name::from_string(id)).is_some()
}

#[allow(clippy::too_many_arguments)]
fn validate(
    qname: &str,
    short: &str,
    env: &Environment,
    universe_params: &[String],
    binders: &[SurfaceBinder],
    ty: &SurfaceExpr,
    ctors: &[SurfaceCtor],
    deriving: &[String],
    modifiers: &DeclModifiers,
) -> Result<Shape, ElabError> {
    let what = format!("coinductive declaration `{qname}`");
    if !universe_params.is_empty() {
        return Err(unsupported(format!(
            "{what}: universe-polymorphic coinductive predicates are not \
             supported — the greatest-fixpoint lowering is Prop-valued and \
             monomorphic; only DECLARATION parameters lift \
             (`{short} (p : T) : … → Prop`), universe parameters stay refused"
        )));
    }
    // The declaration-parameters rung: the row is validated fail-closed
    // (explicit, typed, `P`-free — see `params::validate_params`) and FIXED
    // through the coinduction.
    let decl_params = params::validate_params(&what, short, env, binders)?;
    let param_names: Vec<String> = decl_params.iter().map(|b| b.name.clone()).collect();
    if !deriving.is_empty() {
        return Err(unsupported(format!(
            "{what}: `deriving {}` has no meaning for a Prop-valued greatest \
             fixpoint; this is a deliberate loud reject",
            deriving.join(", ")
        )));
    }
    if !modifiers.is_default() {
        return Err(unsupported(format!(
            "{what}: declaration modifiers (private/partial/noncomputable/…) \
             are not supported in v1"
        )));
    }

    // ── the index telescope ────────────────────────────────────────────
    let Some((idx_tys, sort)) = flatten_arrows(ty) else {
        return Err(unsupported(format!(
            "{what}: a DEPENDENT index telescope `(x : A) → …` is not \
             supported in v1; use a non-dependent arrow telescope"
        )));
    };
    if !matches!(sort, SurfaceExpr::Universe(_, UniverseExpr::Prop)) {
        return Err(unsupported(format!(
            "{what}: the result sort must be `Prop` — v1 lowers coinductive \
             PREDICATES to a greatest fixpoint over complete lattices; \
             Type-valued codata is the separate `codata` command"
        )));
    }
    if idx_tys.is_empty() {
        return Err(unsupported(format!(
            "{what}: a coinductive predicate needs at least one index \
             (`{short} : T → … → Prop`)"
        )));
    }
    let arity = idx_tys.len();

    // ── the constructors (K ≥ 1, each individually v1-shaped) ──────────
    if ctors.is_empty() {
        return Err(unsupported(format!(
            "{what}: at least one constructor is required — an EMPTY \
             disjunction would make the one-step functor constantly False \
             and `{qname}` the always-empty predicate; refusing to mint it"
        )));
    }

    // The shared index-binder row: the FIRST constructor's target-variable
    // names. Every later constructor is α-renamed onto it.
    let mut shared: Vec<String> = Vec::new();
    let mut disjuncts: Vec<DisjunctPlan> = Vec::with_capacity(ctors.len());
    for (ci, ctor) in ctors.iter().enumerate() {
        if RESERVED_SUFFIXES.contains(&ctor.name.as_str()) {
            return Err(unsupported(format!(
                "{what}: constructor name `{}` collides with the generated \
                 companion `{qname}.{}`",
                ctor.name, ctor.name
            )));
        }
        if ctors[..ci].iter().any(|c| c.name == ctor.name) {
            return Err(unsupported(format!(
                "{what}: constructor name `{}` is declared more than once — \
                 the generated intro theorems would collide at `{qname}.{}`",
                ctor.name, ctor.name
            )));
        }

        // ── leading constructor binders (Brick 2) ──────────────────────
        // Peel the leading `Pi` groups the parser desugars
        // `| c (b : T) … : τ` into. Only LEADING binders lift the old
        // binder refusal: a `Pi` after the first premise arrow (a dependent
        // premise telescope) still refuses below.
        let mut ctor_binders: Vec<SurfaceBinder> = Vec::new();
        let mut chain = strip_parens(&ctor.ty);
        while let SurfaceExpr::Pi(_, bs, body) = chain {
            ctor_binders.extend(bs.iter().cloned());
            chain = strip_parens(body);
        }
        let Some((prem_exprs, target)) = flatten_arrows(chain) else {
            return Err(unsupported(format!(
                "{what}: constructor `{}` uses binders after its first \
                 premise arrow; only LEADING explicitly-typed binders \
                 (`| {} (x : T) : …`) are supported — a dependent premise \
                 telescope is refused rather than mis-lowered",
                ctor.name, ctor.name
            )));
        };
        // ── target classification (Brick 3) ────────────────────────────
        // Each target position is either an index-SUBSTITUTED bare variable
        // (no equation — the v1 minimization) or an index EQUATION
        // `written = vᵢ`; the full rules live on `target::classify_target`.
        let mut positions = target::classify_target(
            target,
            short,
            arity,
            &ctor.name,
            &what,
            &ctor_binders,
            &idx_tys,
            &param_names,
            env,
        )?;
        let subst_vars: Vec<String> = positions
            .iter()
            .filter_map(|p| match p {
                TargetPos::Subst { var } => Some(var.clone()),
                TargetPos::Equate { .. } => None,
            })
            .collect();

        // Per-constructor vacuity (Brick 3 rule: equations + premises ≥ 1).
        // An equations-only constructor (`| nil : CB 0 0`) is meaningful —
        // its disjunct is the equations conjunction — but a constructor
        // with NO equations and NO premises would make its disjunct, hence
        // the whole functor, constantly true.
        if prem_exprs.is_empty() && subst_vars.len() == arity {
            return Err(unsupported(format!(
                "{what}: constructor `{}` has no premises and no index \
                 equations, so its disjunct of the one-step functor would be \
                 constantly true and `{qname}` would hold of everything; \
                 refusing to mint it",
                ctor.name
            )));
        }

        // ── the leading binders' own envelope (Brick 2) ────────────────
        // Each declared binder becomes an ∃-bound variable of this
        // constructor's functor disjunct, in declaration order. Every
        // clause is fail-closed (explicitly-typed, explicit-info, P-free,
        // non-overlapping, not shadowing a declaration parameter); the
        // whole envelope lives in `params::check_ctor_binders`.
        params::check_ctor_binders(
            &what,
            short,
            env,
            ci,
            &shared,
            &param_names,
            &ctor.name,
            &ctor_binders,
            &subst_vars,
        )?;

        // ── premises ───────────────────────────────────────────────────
        // Flat recursive atom / `P`-free / GUARDED clause (`guard` module);
        // every other shape is refused with the classifier's named reason.
        let mut premises = Vec::with_capacity(prem_exprs.len());
        for p in &prem_exprs {
            let analysed = classify_premise(p, short, &param_names, arity).map_err(|reason| {
                unsupported(format!("{what}: constructor `{}`: {reason}", ctor.name))
            })?;
            premises.push(analysed);
        }

        // Every free variable of a premise must be an index-substituted
        // target variable, a declared leading binder (Brick 2), a
        // declaration parameter, or an existing constant. A stray name
        // would otherwise be AUTO-BOUND as an implicit parameter of the
        // generated functor, silently changing what the declaration means.
        // A premise-only variable WITHOUT a declared binder still refuses —
        // the explicit binder is the tax for an ∃-bound variable.
        for p in &prem_exprs {
            let mut bound: Vec<&str> = Vec::new();
            let mut fvs: Vec<&str> = Vec::new();
            all_idents(p, &mut bound, &mut fvs).map_err(|label| {
                unsupported(format!(
                    "{what}: a premise of `{}` uses the non-applicative surface \
                     form `{label}`; v1 premises must be built from identifiers, \
                     applications, arrows and binders",
                    ctor.name
                ))
            })?;
            for fv in fvs {
                if fv == short
                    || subst_vars.iter().any(|v| v == fv)
                    || ctor_binders.iter().any(|b| b.name == fv)
                    || param_names.iter().any(|p| p == fv)
                    || known_constant(env, fv)
                {
                    continue;
                }
                return Err(unsupported(format!(
                    "{what}: a premise of `{}` mentions `{fv}`, which is neither a \
                     target variable nor a known constant. v1 refuses to auto-bind \
                     it: an implicit parameter silently inserted into the generated \
                     one-step functor would change what `{qname}` means",
                    ctor.name
                )));
            }
        }

        // ── the shared index row + α-rename onto it ────────────────────
        // The FIRST constructor defines the row: a substituted position
        // contributes its own variable, an equated one a GENERATED
        // `v_coind{i}` name — the `_coind` marker makes it un-writable in
        // premises and binders, and a registered constant of that exact
        // name refuses (it would be captured by the row binder).
        if ci == 0 {
            shared = positions
                .iter()
                .enumerate()
                .map(|(i, pos)| match pos {
                    TargetPos::Subst { var } => Ok(var.clone()),
                    TargetPos::Equate { .. } => {
                        let generated = format!("v_coind{i}");
                        if known_constant(env, &generated) {
                            return Err(unsupported(format!(
                                "{what}: the generated index-row name \
                                 `{generated}` collides with a registered \
                                 constant, which the shared binder row would \
                                 capture; rename that constant"
                            )));
                        }
                        Ok(generated)
                    }
                })
                .collect::<Result<Vec<_>, ElabError>>()?;
        } else {
            // Row-capture guard: a free name in this constructor that is a
            // shared-row name but NOT one of its own substituted variables
            // denotes a constant (every free name was vetted above), and
            // the shared binder row would capture it. The α-rename below
            // only maps this constructor's substituted variables, so this
            // guard — not the rename — owns the constant-collision case.
            let mut bound: Vec<&str> = Vec::new();
            let mut fvs: Vec<&str> = Vec::new();
            for p in &prem_exprs {
                let _ = all_idents(p, &mut bound, &mut fvs);
            }
            for pos in &positions {
                if let TargetPos::Equate { written } = pos {
                    let _ = all_idents(written, &mut bound, &mut fvs);
                }
            }
            for b in &ctor_binders {
                if let Some(t) = b.ty.as_deref() {
                    let _ = all_idents(t, &mut bound, &mut fvs);
                }
            }
            for fv in fvs {
                if shared.iter().any(|s| s == fv) && !subst_vars.iter().any(|v| v == fv) {
                    return Err(unsupported(format!(
                        "{what}: constructor `{}` mentions `{fv}`, which is not \
                         one of this constructor's target variables but IS a \
                         shared index-row name (`{}`) — under the shared binder \
                         row that occurrence would be captured",
                        ctor.name,
                        shared.join(" ")
                    )));
                }
            }

            // The α-rename maps this constructor's substituted variables
            // onto the row, positionally. An exact positional match is the
            // identity and runs rename-free (v1 behavior — including its
            // scope-honoring tolerance of shadowed target variables — is
            // preserved exactly).
            let map: Vec<(String, String)> = positions
                .iter()
                .enumerate()
                .filter_map(|(i, pos)| match pos {
                    TargetPos::Subst { var } if *var != shared[i] => {
                        Some((var.clone(), shared[i].clone()))
                    }
                    _ => None,
                })
                .collect();
            if !map.is_empty() {
                let rename_err = |reason: &str| {
                    unsupported(format!(
                        "{what}: constructor `{}` names its target variables \
                         differently from the first constructor (the shared \
                         index row `{}`), and a premise cannot be α-renamed \
                         onto that row: {reason}; renaming refuses rather than \
                         risk changing what the premise means",
                        ctor.name,
                        shared.join(" ")
                    ))
                };
                let renamed = |e: &SurfaceExpr| {
                    target::rename_free(e, &map).map_err(|reason| rename_err(&reason))
                };
                for premise in &mut premises {
                    *premise = match premise {
                        Premise::Rec(args) => Premise::Rec(
                            args.iter()
                                .map(&renamed)
                                .collect::<Result<Vec<_>, ElabError>>()?,
                        ),
                        Premise::Plain(e) => Premise::Plain(renamed(e)?),
                        Premise::Guarded(g) => {
                            Premise::Guarded(g.renamed(&map).map_err(|r| rename_err(&r))?)
                        }
                    };
                }
                // Binder TYPES and equated target arguments may mention this
                // constructor's substituted variables, so they ride the same
                // rename. Binder NAMES stay: they are constructor-local, and
                // overlap with either side of the map was refused above.
                for b in &mut ctor_binders {
                    if let Some(t) = &b.ty {
                        b.ty = Some(Box::new(renamed(t)?));
                    }
                }
                for pos in &mut positions {
                    if let TargetPos::Equate { written } = pos {
                        *written = renamed(written)?;
                    }
                }
            }
        }

        // ── assemble the disjunct plan (Brick 3) ───────────────────────
        let mut equations = Vec::new();
        let mut target_args = Vec::with_capacity(arity);
        let mut fresh_rows = Vec::new();
        for (i, pos) in positions.iter().enumerate() {
            match pos {
                TargetPos::Subst { var } => {
                    target_args.push(SurfaceExpr::Ident(Span::dummy(), shared[i].clone()));
                    if !ctor_binders.iter().any(|b| b.name == *var) {
                        fresh_rows.push(i);
                    }
                }
                TargetPos::Equate { written } => {
                    equations.push(IndexEquation {
                        written: written.clone(),
                        row: shared[i].clone(),
                    });
                    target_args.push(written.clone());
                }
            }
        }
        // A SUBSTITUTED declared binder leaves the ∃ nest — it IS the index
        // binder. In the intro theorem's leading ∀ group it appears under
        // its shared-row name at its declared type (structurally the index
        // type, by the substitution rule), keeping the declared constructor
        // type usable exactly as written.
        let row_of = |name: &str| {
            positions
                .iter()
                .position(|p| matches!(p, TargetPos::Subst { var } if var == name))
        };
        let exists_binders: Vec<SurfaceBinder> = ctor_binders
            .iter()
            .filter(|b| row_of(&b.name).is_none())
            .cloned()
            .collect();
        let intro_binders: Vec<SurfaceBinder> = ctor_binders
            .iter()
            .map(|b| match row_of(&b.name) {
                Some(i) => SurfaceBinder {
                    span: b.span,
                    name: shared[i].clone(),
                    ty: b.ty.clone(),
                    default: None,
                    info: b.info,
                },
                None => b.clone(),
            })
            .collect();

        disjuncts.push(DisjunctPlan {
            ctor: ctor.name.clone(),
            exists_binders,
            equations,
            premises,
            target_args,
            intro_binders,
            fresh_rows,
        });
    }

    Ok(Shape {
        qname: qname.to_string(),
        params: decl_params,
        idx_tys: idx_tys.into_iter().cloned().collect(),
        idx_names: shared,
        disjuncts,
    })
}

// ── lowering entry point ─────────────────────────────────────────────────

/// Validate a `coinductive` declaration against the envelope and return
/// the surface declarations it lowers to, in dependency order.
///
/// # Errors
///
/// [`ElabError::Unsupported`] — naming the declaration and the precise
/// envelope clause — for every shape outside the envelope documented on
/// this module. Nothing is generated in that case.
#[allow(clippy::too_many_arguments)]
pub(crate) fn lower(
    qname: &str,
    short: &str,
    env: &Environment,
    universe_params: &[String],
    binders: &[SurfaceBinder],
    ty: &SurfaceExpr,
    ctors: &[SurfaceCtor],
    deriving: &[String],
    modifiers: &DeclModifiers,
) -> Result<Vec<SurfaceDecl>, ElabError> {
    let shape = validate(
        qname,
        short,
        env,
        universe_params,
        binders,
        ty,
        ctors,
        deriving,
        modifiers,
    )?;
    Ok(generate::generate(&shape))
}
