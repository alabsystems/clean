// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Axiom discharge: replacing a named imported `Declaration::Axiom` with a
//! hand-built kernel PROOF of its exact stated type.
//!
//! # What this is (BRICK 1.0 of the route-to-100 program)
//!
//! Many "axioms" imported from a source system are, in Clean's kernel, actually
//! *provable* — the source declared them axiomatically only because its own
//! kernel lacked the definitional rule Clean has (definitional proof
//! irrelevance, K-style recursor reduction, …). For such an axiom we build a
//! genuine proof term IN RUST — the only place an `Expr` can freely span both
//! imported source names (`Coq.Init.Logic.eq.0`) and Clean prelude primitives —
//! exactly as the `clean_kernel::env::*_proof.rs` modules build Diaconescu's
//! `Classical.em` proof.
//!
//! The proof is registered as a `Declaration::Theorem`, so the kernel
//! type-checks it against the imported type. If it checks, the constant is a
//! genuine `KernelVerified` and carries the [`AxiomProfile::DISCHARGED_AXIOM`]
//! provenance flag (it was an axiom in the source, proven here). If the builder
//! returns `None`, or the kernel *rejects* the proof, the caller falls through
//! byte-identically to today's axiom lane (`AxiomAccepted`). This is
//! **regressed-0 by construction**: the discharge only runs in the value-less
//! `DeclKind::Axiom | DeclKind::Quot` arm, so it can never mask a rejected
//! *value*, and every non-discharge path is exactly the prior behavior.
//!
//! # The rfl-class builders
//!
//! Both currently-registered discharges collapse to one hand-built term: for a
//! statement `∀ telescope, @eq A lhs rhs`, the proof is
//! `fun telescope => eq_refl A lhs` (type `@eq A lhs lhs`), which the kernel
//! accepts *iff* `rhs ≡ lhs` definitionally:
//!
//! * `Coq.Logic.ProofIrrelevance.proof_irrelevance`
//!   (`∀ (P:Prop) (p1 p2 : P), @eq P p1 p2`): closes because `p1 ≡ p2` under
//!   Clean's **definitional proof irrelevance** (`P : Prop`), so
//!   `@eq P p1 p1 ≡ @eq P p1 p2`.
//! * `Coq.Logic.Eqdep.Eq_rect_eq.eq_rect_eq`
//!   (`∀ U p Q x h, @eq (Q p) x (eq_rect U p Q x p h)`): closes only if the
//!   kernel δ-unfolds `eq_rect` and fires **K-like ι** on the imported `eq`
//!   recursor to reduce `eq_rect … p h ≡ x` (`h : @eq U p p` is reflexive).
//!   This is the known-risk discharge: if the kernel cannot fire K on the
//!   `add_inductive`-generated `Coq.Init.Logic.eq.0.rec`, the proof is rejected
//!   and the constant stays `AxiomAccepted` (fail-closed — fine).
//!
//! The builder never fabricates a universe level: it extracts the imported
//! `eq` inductive reference (name + level instance) by pattern-matching the
//! statement's conclusion and reuses it verbatim. Any shape mismatch → `None`.

use clean_kernel::expr::{BinderData, BinderInfo, Expr, ExprKind};
use clean_kernel::level::Level;
use clean_kernel::{Declaration, Environment, Name};

/// A registered axiom-discharge: a source-system axiom `full_name` that Clean
/// can replace with a hand-built kernel proof of its imported type.
///
/// `build` receives the (post-prelude, post-upstream) verification environment
/// and the reconstructed imported type, and returns a proof term, or `None`
/// when the imported type does not match the shape the builder proves.
pub(crate) struct AxiomDischarge {
    /// Fully-qualified imported constant name this discharge applies to.
    pub(crate) full_name: &'static str,
    /// Hand-built proof-term constructor (fails closed by returning `None`).
    pub(crate) build: fn(&Environment, &Expr) -> Option<Expr>,
}

/// The registry of axioms Clean discharges to genuine kernel proofs.
///
/// Keyed by the EXACT imported full name so a discharge is only ever attempted
/// for a known axiom — an unrelated axiom never runs a builder. Every observed
/// corpus alias of a discharged axiom is listed explicitly.
const REGISTRY: &[AxiomDischarge] = &[
    // `∀ (P:Prop) (p1 p2 : P), @eq P p1 p2` — closes by definitional proof
    // irrelevance. Sole corpus row (Coq 8.20 stdlib).
    AxiomDischarge {
        full_name: "Coq.Logic.ProofIrrelevance.proof_irrelevance",
        build: build_eq_refl_of_lhs,
    },
    // `∀ U p Q x h, @eq (Q p) x (eq_rect U p Q x p h)` — closes only if K fires
    // on the imported `eq` recursor. Sole `CoqAxiom` row (the functor-applied
    // `EqdepTheory.eq_rect_eq` / `Classical_Prop.*` spellings are value-bearing
    // `CoqConstant`s that reduce to this one).
    AxiomDischarge {
        full_name: "Coq.Logic.Eqdep.Eq_rect_eq.eq_rect_eq",
        build: build_eq_refl_of_lhs,
    },
    // ── BRICK 1.2: the logic/choice axiom-discharge family ───────────────────
    // Each bridges a Coq classical/extensionality axiom to a Clean kernel
    // theorem that ALREADY EXISTS in the prelude (`funext` proved from
    // `Quot.sound`, `Classical.em` proved from `Classical.choice` via
    // Diaconescu, `propext` foundational), TRANSPORTING between Coq's own
    // Prop-connective inductives (`Coq.Init.Logic.eq.0` / `or.0` / `and.0`,
    // never the kernel's `Eq`/`Or`) and the kernel's. Every carrier/level is
    // EXTRACTED from the imported type — nothing is fabricated — and the kernel
    // re-checks the assembled proof, so a shape/level miss fails closed to a
    // byte-identical `AxiomAccepted`.
    //
    // `Coq.Logic.Classical_Prop.classic` : `∀ P, or P (not P)` — bridged to the
    // proved `Classical.em` (`(p:Prop) → Or p (p → False)`) by casing the
    // kernel `Or` with `Or.rec` and rebuilding the Coq `or`; the `¬p` branch
    // transports `p → kernel.False` to `p → Coq.False` via `False.elim`.
    AxiomDischarge {
        full_name: "Coq.Logic.Classical_Prop.classic",
        build: build_classic,
    },
    // `∀ A (B:A→_) (f g:∀x,B x), (∀x, eq (B x)(f x)(g x)) → eq (∀x,B x) f g` —
    // bridged to the proved `funext`; the crux is the `Coq.eq ↔ kernel.Eq`
    // transport (via the imported eq's own recursor one way, `Eq.rec` the
    // other). The non-dependent spelling is a `CoqConstant` derived from this
    // one, so only the dependent axiom is registered.
    AxiomDischarge {
        full_name: "Coq.Logic.FunctionalExtensionality.functional_extensionality_dep",
        build: build_funext_dep,
    },
    // `∀ P Q : Prop, iff P Q → eq Prop P Q` — bridged to the foundational
    // `propext` (`{a b:Prop} → Iff a b → Eq Prop a b`); destructures Coq's `iff`
    // (`= and (P→Q)(Q→P)`) with `and`'s recursor into a kernel `Iff`, then
    // transports the resulting `kernel.Eq Prop P Q` back to `Coq.eq`.
    AxiomDischarge {
        full_name: "Coq.Logic.PropExtensionality.propositional_extensionality",
        build: build_propext,
    },
];

/// The outcome of an axiom-discharge attempt at the `reconstruct_and_replay_one`
/// hook site. Every arm other than [`DischargeAttempt::Discharged`] means the
/// caller proceeds to mint the axiom exactly as before (fail-closed).
pub(crate) enum DischargeAttempt {
    /// No builder is registered for this name, or the builder returned `None`
    /// (shape mismatch / missing prerequisite). Nothing was added to `env`.
    NotAttempted,
    /// A proof term was built and the kernel ACCEPTED it as a `Theorem`: the
    /// constant is genuinely `KernelVerified`. `env` now holds the theorem.
    Discharged,
    /// A proof term was built but the kernel REJECTED it as a `Theorem`
    /// (`add_decl` is transactional, so `env` is unchanged). The caller mints
    /// the axiom as usual. The string is the kernel rejection (diagnostics).
    ProofRejected(String),
}

/// Attempt to discharge the value-less declaration `decl_name : imported_type`
/// to a kernel-checked `Theorem`. Only ever called from the `Axiom`/`Quot`
/// arm, so it can never mask a rejected proof VALUE.
///
/// On [`DischargeAttempt::Discharged`] the theorem is installed in `env`; on
/// every other arm `env` is untouched and the caller falls through to today's
/// axiom lane byte-identically.
pub(crate) fn attempt_axiom_discharge(
    env: &mut Environment,
    decl_name: &Name,
    level_params: &[Name],
    imported_type: &Expr,
) -> DischargeAttempt {
    let full_name = decl_name.to_string();
    // Build the proof (immutable borrow of env released before add_decl).
    let Some(proof) = try_build_discharge_proof(env, &full_name, imported_type) else {
        return DischargeAttempt::NotAttempted;
    };
    let theorem = Declaration::Theorem {
        name: decl_name.clone(),
        level_params: level_params.to_vec(),
        type_: imported_type.clone(),
        value: proof,
    };
    match env.add_decl(theorem) {
        Ok(()) => DischargeAttempt::Discharged,
        Err(err) => DischargeAttempt::ProofRejected(err.to_string()),
    }
}

/// Look up a builder by full name and run it, returning a proof term (or `None`
/// when no builder is registered or the builder declines the shape).
pub(crate) fn try_build_discharge_proof(
    env: &Environment,
    full_name: &str,
    imported_type: &Expr,
) -> Option<Expr> {
    let entry = REGISTRY.iter().find(|d| d.full_name == full_name)?;
    (entry.build)(env, imported_type)
}

/// Peel a Pi telescope into its `(binder, domain)` prefix and the final
/// conclusion. Metadata wrappers are stripped at every level.
fn peel_pis(ty: &Expr) -> (Vec<(BinderData, Expr)>, Expr) {
    let mut doms: Vec<(BinderData, Expr)> = Vec::new();
    let mut cur: &Expr = ty;
    loop {
        let stripped = cur.strip_mdata();
        if let ExprKind::Pi(bd, dom, body) = stripped.kind() {
            doms.push((*bd, (**dom).clone()));
            cur = body;
        } else {
            return (doms, stripped.clone());
        }
    }
}

/// Wrap `body` in `λ`-binders over `doms` (outermost binder first in `doms`),
/// reusing the imported domain types verbatim.
fn build_lambda(doms: &[(BinderData, Expr)], body: Expr) -> Expr {
    doms.iter()
        .rev()
        .fold(body, |acc, (bd, dom)| Expr::lam(*bd, dom.clone(), acc))
}

/// Builder for every rfl-class discharge: prove `∀ telescope, @eq A lhs rhs`
/// with `fun telescope => eq_refl A lhs`.
///
/// Extracts the imported `eq` inductive reference (`Const(name, levels)`) and
/// its first two conclusion arguments (`A`, `lhs`) verbatim from the statement,
/// and derives the reflexivity constructor as constructor-0 of that inductive
/// (`<eq_name>.0`, the positional constructor spelling the Coq importer emits —
/// e.g. `Coq.Init.Logic.eq.0` ⇒ `Coq.Init.Logic.eq.0.0`). The resulting term
/// has type `@eq A lhs lhs`, which the kernel accepts against `@eq A lhs rhs`
/// exactly when `rhs ≡ lhs`.
///
/// Returns `None` (fail-closed) unless: the conclusion is a `Const`-headed
/// application of exactly three arguments, and the derived constructor is
/// actually registered in `env`. No universe level is ever fabricated — the
/// constructor reuses the extracted inductive's level instance.
fn build_eq_refl_of_lhs(env: &Environment, imported_type: &Expr) -> Option<Expr> {
    let (doms, concl) = peel_pis(imported_type);

    // Conclusion must be `@eq A lhs rhs`: a `Const`-headed spine of 3 args.
    let head = concl.get_app_fn();
    let ExprKind::Const(eq_name, eq_levels) = head.kind() else {
        return None;
    };
    let args = concl.get_app_args();
    if args.len() != 3 {
        return None;
    }
    let carrier = args[0].clone(); // A  (the equated type / index)
    let lhs = args[1].clone(); // lhs (the reflexive witness)

    // Constructor 0 of the eq inductive `<eq_name>` = `<eq_name>.0`. Fail
    // closed unless it is genuinely registered (guards against a non-eq
    // Const-headed conclusion that happens to take three arguments).
    let refl_name = Name::from_string(&format!("{eq_name}.0"));
    env.get_const(&refl_name)?;

    // eq_refl A lhs : @eq A lhs lhs   (reusing eq's extracted level instance).
    let refl = Expr::apps(Expr::const_(refl_name, eq_levels.clone()), [carrier, lhs]);
    Some(build_lambda(&doms, refl))
}

// ── BRICK 1.2: the LOGIC/CHOICE axiom-discharge family ───────────────────────
//
// The bridges below all rest on ONE observation about the Coq importer: Coq's
// Prop connectives (`eq`, `or`, `and`, `not`, `iff`, `False`, `ex`, `sig`) are
// imported as their OWN fresh inductives/definitions
// (`Coq.Init.Logic.eq.0`, `Coq.Init.Logic.or.0`, …), NEVER re-mapped onto the
// kernel's `Eq`/`Or`/`Iff`/`Exists`. So a Clean kernel theorem stated in the
// kernel's connectives (the proved `funext`/`Classical.em`, the foundational
// `propext`) does not match a Coq axiom's stated type on the nose — the last
// mile is a small TRANSPORT across the two encodings. The transports are the
// only new proof content; everything downstream is a kernel-checked
// application.

/// The single-inductive member index the Coq importer appends to a
/// `Coq.Init.Logic.eq`-style name (`Coq.Init.Logic.eq.0`). A constructor is
/// `<ind>.<ctor_idx>` and a recursor is `<ind>.rec` on top of that (so
/// `Coq.Init.Logic.eq.0.0` / `Coq.Init.Logic.eq.0.rec`), exactly as
/// [`build_eq_refl_of_lhs`] derives the reflexivity constructor.
fn ctor_name(ind_name: &str, ctor_idx: u32) -> Name {
    Name::from_string(&format!("{ind_name}.{ctor_idx}"))
}

/// `@Eq.{lvl} carrier a b` in the kernel's own equality.
fn ker_eq(lvl: &Level, carrier: &Expr, a: &Expr, b: &Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![lvl.clone()]),
        [carrier.clone(), a.clone(), b.clone()],
    )
}

/// `@Eq.refl.{lvl} carrier a : @Eq.{lvl} carrier a a`.
fn ker_eq_refl(lvl: &Level, carrier: &Expr, a: &Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq.refl"), vec![lvl.clone()]),
        [carrier.clone(), a.clone()],
    )
}

/// The `Sort`-level of a type expression (`Sort u ↦ u`), or `None`.
fn sort_level(ty: &Expr) -> Option<Level> {
    match ty.strip_mdata().kind() {
        ExprKind::Sort(l) => Some(l.clone()),
        _ => None,
    }
}

/// The codomain of a Pi (`(x : A) → B ↦ B`), or `None`.
fn pi_codomain(ty: &Expr) -> Option<Expr> {
    match ty.strip_mdata().kind() {
        ExprKind::Pi(_, _, body) => Some((**body).clone()),
        _ => None,
    }
}

/// Transport `h : @Coq.eq carrier a b` (the imported inductive `eq_ind_name`,
/// level instance `eq_levels`) to `@Eq.{carrier_lvl} carrier a b` in the
/// kernel's equality, by eliminating the imported `eq` with its own recursor:
///
/// `@<eq>.rec.{0, eq_levels} carrier a (fun y _ => Eq carrier a y) (Eq.refl carrier a) b h`.
///
/// The motive lands in `Prop` (`Eq … : Prop`), so no large elimination is
/// needed — every Coq `eq` recursor supports Prop elimination. `carrier`, `a`,
/// `b`, `h` are read in the caller's binder context; internal binders are
/// accounted for with [`Expr::lift`]. Fails closed if the recursor is absent.
fn coq_eq_to_ker_eq(
    env: &Environment,
    eq_ind_name: &str,
    eq_levels: &[Level],
    carrier_lvl: &Level,
    carrier: &Expr,
    a: &Expr,
    b: &Expr,
    h: &Expr,
) -> Option<Expr> {
    let rec_name = Name::from_string(&format!("{eq_ind_name}.rec"));
    env.get_const(&rec_name)?;
    let coq_eq = Expr::const_(Name::from_string(eq_ind_name), eq_levels.to_vec());

    // motive := fun (y : carrier) (_ : @Coq.eq carrier a y) => @Eq.{cl} carrier a y
    let inner_dom = Expr::apps(coq_eq, [carrier.lift(1), a.lift(1), Expr::bvar(0)]);
    let motive_body = ker_eq(carrier_lvl, &carrier.lift(2), &a.lift(2), &Expr::bvar(1));
    let motive = Expr::lam(
        BinderInfo::Default,
        carrier.clone(),
        Expr::lam(BinderInfo::Default, inner_dom, motive_body),
    );
    // minor := @Eq.refl.{cl} carrier a : @Eq.{cl} carrier a a
    let minor = ker_eq_refl(carrier_lvl, carrier, a);

    let mut rec_levels = vec![Level::zero()];
    rec_levels.extend_from_slice(eq_levels);
    let rec_const = Expr::const_(rec_name, rec_levels);
    Some(Expr::apps(
        rec_const,
        [
            carrier.clone(),
            a.clone(),
            motive,
            minor,
            b.clone(),
            h.clone(),
        ],
    ))
}

/// Transport `h : @Eq.{carrier_lvl} carrier a b` (kernel equality) back to
/// `@Coq.eq carrier a b` (the imported inductive `eq_ind_name`), by eliminating
/// the kernel `Eq` with `Eq.rec`:
///
/// `@Eq.rec.{0, carrier_lvl} carrier a (fun y _ => Coq.eq carrier a y) (Coq.eq.refl carrier a) b h`.
///
/// Fails closed if the imported reflexivity constructor `<eq>.0` is absent.
fn ker_eq_to_coq_eq(
    env: &Environment,
    eq_ind_name: &str,
    eq_levels: &[Level],
    carrier_lvl: &Level,
    carrier: &Expr,
    a: &Expr,
    b: &Expr,
    h: &Expr,
) -> Option<Expr> {
    let refl_name = ctor_name(eq_ind_name, 0);
    env.get_const(&refl_name)?;
    let coq_eq = Expr::const_(Name::from_string(eq_ind_name), eq_levels.to_vec());

    // motive := fun (y : carrier) (_ : @Eq.{cl} carrier a y) => @Coq.eq carrier a y
    let inner_dom = ker_eq(carrier_lvl, &carrier.lift(1), &a.lift(1), &Expr::bvar(0));
    let motive_body = Expr::apps(coq_eq, [carrier.lift(2), a.lift(2), Expr::bvar(1)]);
    let motive = Expr::lam(
        BinderInfo::Default,
        carrier.clone(),
        Expr::lam(BinderInfo::Default, inner_dom, motive_body),
    );
    // minor := @Coq.eq.refl carrier a : @Coq.eq carrier a a
    let minor = Expr::apps(
        Expr::const_(refl_name, eq_levels.to_vec()),
        [carrier.clone(), a.clone()],
    );

    let eq_rec = Expr::const_(
        Name::from_string("Eq.rec"),
        vec![Level::zero(), carrier_lvl.clone()],
    );
    Some(Expr::apps(
        eq_rec,
        [
            carrier.clone(),
            a.clone(),
            motive,
            minor,
            b.clone(),
            h.clone(),
        ],
    ))
}

/// Recover the imported Coq `False` inductive reference from the VALUE of the
/// imported `Coq.Init.Logic.not` definition (`not := fun A => A → False`): peel
/// the `fun A =>` and read the `→`-codomain. A closed reference (no bvars), so
/// it is context-independent. Faithful (extracted, never fabricated).
fn coq_false_from_not(env: &Environment, not_name: &Name) -> Option<Expr> {
    let value = env.get_const(not_name)?.value.as_ref()?;
    let ExprKind::Lam(_, _, body) = value.strip_mdata().kind() else {
        return None;
    };
    let ExprKind::Pi(_, _, cod) = body.strip_mdata().kind() else {
        return None;
    };
    Some((**cod).clone())
}

/// Recover the imported Coq `and` inductive reference (name + level instance)
/// from the VALUE of the imported `Coq.Init.Logic.iff` definition
/// (`iff := fun A B => and (A → B) (B → A)`): peel the two `fun`s and read the
/// application head.
fn coq_and_of_iff(env: &Environment, iff_name: &Name) -> Option<(Name, Vec<Level>)> {
    let value = env.get_const(iff_name)?.value.as_ref()?;
    let mut cur: Expr = value.strip_mdata().clone();
    for _ in 0..2 {
        let ExprKind::Lam(_, _, body) = cur.kind() else {
            return None;
        };
        cur = body.strip_mdata().clone();
    }
    let head = cur.get_app_fn();
    let ExprKind::Const(and_name, and_levels) = head.kind() else {
        return None;
    };
    Some((and_name.clone(), and_levels.to_vec()))
}

/// Project field `field_idx` (0 = first) out of `h : @Coq.and A B` (the
/// imported single-constructor conjunction `and_name`) by eliminating with its
/// recursor: `@<and>.rec.{0, and_levels} A B (fun _ => A|B) (fun x y => x|y) h`.
/// `A`, `B`, `h` are read in the caller's binder context.
fn coq_and_proj(
    env: &Environment,
    and_name: &Name,
    and_levels: &[Level],
    a: &Expr,
    b: &Expr,
    field_idx: u32,
    h: &Expr,
) -> Option<Expr> {
    let rec_name = Name::from_string(&format!("{and_name}.rec"));
    env.get_const(&rec_name)?;
    let coq_and = Expr::const_(and_name.clone(), and_levels.to_vec());

    let and_ab = Expr::apps(coq_and, [a.clone(), b.clone()]);
    let proj_ty = if field_idx == 0 { a } else { b };
    // motive := fun (_ : @Coq.and A B) => (A | B)
    let motive = Expr::lam(BinderInfo::Default, and_ab, proj_ty.lift(1));
    // minor := fun (x : A) (y : B) => (x | y)   [x = bvar1, y = bvar0]
    let selected = if field_idx == 0 {
        Expr::bvar(1)
    } else {
        Expr::bvar(0)
    };
    let minor = Expr::lam(
        BinderInfo::Default,
        a.clone(),
        Expr::lam(BinderInfo::Default, b.lift(1), selected),
    );

    let mut rec_levels = vec![Level::zero()];
    rec_levels.extend_from_slice(and_levels);
    let rec_const = Expr::const_(rec_name, rec_levels);
    Some(Expr::apps(
        rec_const,
        [a.clone(), b.clone(), motive, minor, h.clone()],
    ))
}

/// Discharge `Coq.Logic.Classical_Prop.classic` (`∀ P : Prop, or P (not P)`) to
/// the kernel-proved `Classical.em` (`(p : Prop) → Or p (p → False)`).
///
/// Under `P`, we case the kernel `Or P (P → False)` with `Or.rec` and rebuild
/// the imported `or`:
///   * left `hp : P`  ↦ `Coq.or.inl P (not P) hp`;
///   * right `hnp : P → False` ↦ `Coq.or.inr P (not P) (fun p => False.elim (hnp p))`,
///     transporting `kernel.False` to `Coq.False` (`not P` unfolds to
///     `P → Coq.False`, which the kernel checks by δ-unfolding `not`).
fn build_classic(env: &Environment, imported_type: &Expr) -> Option<Expr> {
    let (doms, concl) = peel_pis(imported_type);
    if doms.len() != 1 {
        return None;
    }
    // concl = @Coq.or P (not P), with P = bvar(0) under the single binder.
    let ExprKind::Const(or_name, or_levels) = concl.get_app_fn().kind() else {
        return None;
    };
    let or_name_s = or_name.to_string();
    let or_levels: Vec<Level> = or_levels.to_vec();
    let args = concl.get_app_args();
    if args.len() != 2 {
        return None;
    }
    let p = args[0].strip_mdata().clone();
    let not_p = args[1].clone();

    // `not P` must be headed by a Const (`Coq.Init.Logic.not`) whose value
    // reveals the imported `Coq.False`.
    let not_head = not_p.strip_mdata().get_app_fn();
    let ExprKind::Const(not_name, _) = not_head.kind() else {
        return None;
    };
    let coq_false = coq_false_from_not(env, not_name)?;

    // Imported `or` constructors and the kernel primitives.
    let or_inl = ctor_name(&or_name_s, 0);
    let or_inr = ctor_name(&or_name_s, 1);
    env.get_const(&or_inl)?;
    env.get_const(&or_inr)?;
    env.get_const(&Name::from_string("Classical.em"))?;

    let false_ker = Expr::const_(Name::from_string("False"), Vec::<Level>::new());
    let or_ker = Expr::const_(Name::from_string("Or"), Vec::<Level>::new());
    let or_rec = Expr::const_(Name::from_string("Or.rec"), Vec::<Level>::new());
    let em = Expr::const_(Name::from_string("Classical.em"), Vec::<Level>::new());
    let false_elim = Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]);
    let coq_or = Expr::const_(or_name.clone(), or_levels.clone());

    // `P → kernel.False` (the shape of `em`'s right disjunct).
    let kernel_not_p = Expr::pi(BinderInfo::Default, p.clone(), false_ker);
    // em P : @Or P (P → False)
    let em_p = Expr::app(em, p.clone());
    // goal := @Coq.or P (not P) (the conclusion itself)
    let goal = Expr::apps(coq_or, [p.clone(), not_p.clone()]);

    // motive := fun (_ : Or P (P → False)) => goal
    let or_p_np = Expr::apps(or_ker, [p.clone(), kernel_not_p.clone()]);
    let motive = Expr::lam(BinderInfo::Default, or_p_np, goal.lift(1));
    // case_left := fun (hp : P) => @Coq.or.inl P (not P) hp
    let case_left = Expr::lam(
        BinderInfo::Default,
        p.clone(),
        Expr::apps(
            Expr::const_(or_inl, or_levels.clone()),
            [p.lift(1), not_p.lift(1), Expr::bvar(0)],
        ),
    );
    // witness := fun (pp : P) => @False.elim.{0} Coq.False (hnp pp)   [hnp = bvar1]
    let witness = Expr::lam(
        BinderInfo::Default,
        p.lift(1),
        Expr::apps(
            false_elim,
            [coq_false, Expr::app(Expr::bvar(1), Expr::bvar(0))],
        ),
    );
    // case_right := fun (hnp : P → False) => @Coq.or.inr P (not P) witness
    let case_right = Expr::lam(
        BinderInfo::Default,
        kernel_not_p.clone(),
        Expr::apps(
            Expr::const_(or_inr, or_levels),
            [p.lift(1), not_p.lift(1), witness],
        ),
    );
    // Or.rec P (P → False) motive case_left case_right (em P)
    let body = Expr::apps(
        or_rec,
        [p, kernel_not_p, motive, case_left, case_right, em_p],
    );
    Some(build_lambda(&doms, body))
}

/// Discharge `functional_extensionality_dep`
/// (`∀ A (B:A→_) (f g:∀x,B x), (∀x, eq (B x)(f x)(g x)) → eq (∀x,B x) f g`) to
/// the kernel-proved `funext`.
///
/// Under the five binders `[A, B, f, g, H]` we (1) transport the pointwise Coq
/// hypothesis to a kernel one (`fun x => coq_eq_to_ker (H x)`), (2) apply
/// `funext.{uA, uB} A B f g` to obtain `@Eq (∀x,B x) f g`, and (3) transport
/// that back to `@Coq.eq (∀x,B x) f g`. Every universe is extracted from the
/// binder domains (`A : Sort uA`, `B : A → Sort uB`).
fn build_funext_dep(env: &Environment, imported_type: &Expr) -> Option<Expr> {
    let (doms, concl) = peel_pis(imported_type);
    if doms.len() != 5 {
        return None;
    }
    // concl = @Coq.eq (∀x,B x) f g. Under the 5 binders A,B,f,g,H:
    // A = bvar4, B = bvar3, f = bvar2, g = bvar1.
    let ExprKind::Const(eq_name, eq_levels) = concl.get_app_fn().kind() else {
        return None;
    };
    let eq_name_s = eq_name.to_string();
    let eq_levels: Vec<Level> = eq_levels.to_vec();
    let args = concl.get_app_args();
    if args.len() != 3 {
        return None;
    }
    let pi_bx = args[0].strip_mdata().clone(); // ∀ (x:A), B x
    let f = args[1].clone();
    let g = args[2].clone();

    // uA from A's domain (Sort uA); uB from B's codomain (A → Sort uB).
    let level_a = sort_level(&doms[0].1)?;
    let level_b = sort_level(&pi_codomain(&doms[1].1)?)?;
    let result_lvl = Level::imax(level_a.clone(), level_b.clone());

    env.get_const(&Name::from_string("funext"))?;

    // Pointwise transport, built under an extra `x : A` binder (so every outer
    // bvar shifts +1): B x = bvar4 · bvar0, f x = bvar3 · bvar0, etc.
    let bx = Expr::app(Expr::bvar(4), Expr::bvar(0));
    let fx = Expr::app(Expr::bvar(3), Expr::bvar(0));
    let gx = Expr::app(Expr::bvar(2), Expr::bvar(0));
    let hx = Expr::app(Expr::bvar(1), Expr::bvar(0));
    let pointwise_ker =
        coq_eq_to_ker_eq(env, &eq_name_s, &eq_levels, &level_b, &bx, &fx, &gx, &hx)?;
    let pointwise = Expr::lam(BinderInfo::Default, Expr::bvar(4), pointwise_ker);

    // @funext.{uA, uB} A B f g pointwise : @Eq.{result_lvl} (∀x,B x) f g
    let funext = Expr::const_(
        Name::from_string("funext"),
        vec![level_a.clone(), level_b.clone()],
    );
    let funext_app = Expr::apps(
        funext,
        [
            Expr::bvar(4),
            Expr::bvar(3),
            f.clone(),
            g.clone(),
            pointwise,
        ],
    );

    let body = ker_eq_to_coq_eq(
        env,
        &eq_name_s,
        &eq_levels,
        &result_lvl,
        &pi_bx,
        &f,
        &g,
        &funext_app,
    )?;
    Some(build_lambda(&doms, body))
}

/// Discharge `propositional_extensionality`
/// (`∀ P Q : Prop, iff P Q → eq Prop P Q`) to the foundational `propext`.
///
/// Under `[P, Q, H]` we destructure the imported `iff P Q` (definitionally
/// `and (P→Q) (Q→P)`) with `and`'s recursor into a kernel `Iff.intro`, apply
/// `propext P Q` to get `@Eq Prop P Q`, and transport it back to `@Coq.eq`.
fn build_propext(env: &Environment, imported_type: &Expr) -> Option<Expr> {
    let (doms, concl) = peel_pis(imported_type);
    if doms.len() != 3 {
        return None;
    }
    // concl = @Coq.eq Prop P Q. Under P,Q,H: P = bvar2, Q = bvar1.
    let ExprKind::Const(eq_name, eq_levels) = concl.get_app_fn().kind() else {
        return None;
    };
    let eq_name_s = eq_name.to_string();
    let eq_levels: Vec<Level> = eq_levels.to_vec();
    let args = concl.get_app_args();
    if args.len() != 3 {
        return None;
    }
    let carrier = args[0].strip_mdata().clone(); // Prop
    let p = args[1].clone();
    let q = args[2].clone();

    // H's domain is `@Coq.iff P Q`; recover the underlying `and`.
    let ExprKind::Const(iff_name, _) = doms[2].1.strip_mdata().get_app_fn().kind() else {
        return None;
    };
    let (and_name, and_levels) = coq_and_of_iff(env, iff_name)?;

    env.get_const(&Name::from_string("propext"))?;
    env.get_const(&Name::from_string("Iff.intro"))?;

    // and's params: A = (P → Q), B = (Q → P). Under P,Q,H (P=bvar2,Q=bvar1);
    // under the Pi the codomain shifts +1.
    let a_and = Expr::pi(BinderInfo::Default, p.clone(), q.lift(1));
    let b_and = Expr::pi(BinderInfo::Default, q.clone(), p.lift(1));
    let h = Expr::bvar(0);
    let mp = coq_and_proj(env, &and_name, &and_levels, &a_and, &b_and, 0, &h)?;
    let mpr = coq_and_proj(env, &and_name, &and_levels, &a_and, &b_and, 1, &h)?;

    // Iff.intro P Q mp mpr : @Iff P Q
    let iff_pq = Expr::apps(
        Expr::const_(Name::from_string("Iff.intro"), Vec::<Level>::new()),
        [p.clone(), q.clone(), mp, mpr],
    );
    // propext P Q iff_pq : @Eq.{1} Prop P Q
    let eq_pq = Expr::apps(
        Expr::const_(Name::from_string("propext"), Vec::<Level>::new()),
        [p.clone(), q.clone(), iff_pq],
    );
    // Prop : Sort 1, so the kernel equality on `Prop` is `Eq.{1}`.
    let carrier_lvl = Level::succ(Level::zero());
    let body = ker_eq_to_coq_eq(
        env,
        &eq_name_s,
        &eq_levels,
        &carrier_lvl,
        &carrier,
        &p,
        &q,
        &eq_pq,
    )?;
    Some(build_lambda(&doms, body))
}

// ── BRICK 1.1: the generic LOCK-PATTERN axiom-discharge rule ─────────────────

/// The imported spelling of Coq's propositional (Leibniz) equality inductive
/// (`Coq.Init.Logic.eq`, inductive index 0) as the `coq-import` reconstructor
/// emits it in a reference position. A lock equation is by definition a
/// `@eq`-equation in THIS relation — restricting to it keeps the unseal
/// faithful (a 3-argument `Const`-headed application of some OTHER inductive is
/// not an "`f = rhs`" fact and must never drive a definition of `f`).
const COQ_EQ_IND_NAME: &str = "Coq.Init.Logic.eq.0";

/// The data extracted from a recognised lock equation, sufficient to unseal the
/// locked constant `f` by upgrading its value-free axiom stub to the checked
/// definition `f := f_value`.
struct LockEquation {
    /// The locked constant `f` (a value-free axiom already in the env).
    f_name: Name,
    /// `f`'s own universe parameters (verbatim from its env entry — the upgrade
    /// requires the incoming definition's params to match the stub's).
    f_level_params: Vec<Name>,
    /// `f`'s own declared type (verbatim from its env entry, so the upgrade's
    /// type-identity precondition holds trivially).
    f_type: Expr,
    /// The definition value `fun binders => rhs` the equation licenses for `f`.
    f_value: Expr,
}

/// Recognise a lock equation `∀ binders, @eq A (f binders) rhs` and extract the
/// definition it licenses for the locked constant `f`.
///
/// This is the SEALING idiom mathcomp/ssreflect (`locked`/module functors) and
/// Coq's `Rdefinitions` use: a value-free axiom `f` (the "locked" constant)
/// paired with a companion axiom `f_def : f = rhs`. Coq emits `f` value-free
/// because its own kernel keeps the module-sealed constant opaque; the equation
/// is the only handle on `f`'s value. Clean can UNSEAL `f`.
///
/// Returns `Some` (fail-closed `None` otherwise) exactly when ALL hold:
///
/// * The whole type is `∀ binders, @eq A lhs rhs` — the `@eq` is the ENTIRE
///   conclusion, with every leading `∀` a plain parameter binder. A binder that
///   `f` is NOT applied to (a genuine hypothesis, e.g. `PArray.get_out_of_bounds`
///   has premises) makes `lhs` a partial application and is rejected below.
/// * The equated relation is Coq's `eq` (`COQ_EQ_IND_NAME`) — not some other
///   3-argument `Const`-headed inductive (non-eq `*_spec` shapes are rejected).
/// * `lhs` is `f` applied to EXACTLY the telescope binders in order
///   (`bvar(k-1) … bvar(0)`), or bare `f` when there is no telescope. This is
///   what makes `fun binders => rhs` the definition `f` needs; any other
///   application shape (`f (g x)`, `f x x`, `f` under a hypothesis) is declined.
/// * `f` is a VALUE-FREE constant already in the env (topological order
///   guarantees this: the equation's type references `f`, so `f` is classified
///   first). An already-value-bearing `f` has nothing to unseal.
/// * `rhs` does not reference `f` (acyclicity). A self-referential "definition"
///   is not a lock; deeper cycles fall out fail-closed via the kernel upgrade,
///   which removes `f`'s stub for the duration of the check.
fn parse_lock_equation(env: &Environment, imported_type: &Expr) -> Option<LockEquation> {
    let (doms, concl) = peel_pis(imported_type);
    let k = doms.len();

    // Conclusion must be `@eq A lhs rhs`: a `Const`-headed spine of 3 args in
    // Coq's `eq` relation specifically.
    let ExprKind::Const(eq_name, _eq_levels) = concl.get_app_fn().kind() else {
        return None;
    };
    if eq_name.to_string() != COQ_EQ_IND_NAME {
        return None;
    }
    let args = concl.get_app_args();
    if args.len() != 3 {
        return None;
    }
    let lhs = args[1].strip_mdata();
    let rhs = args[2];

    // `lhs` must be `f` applied to exactly the telescope binders in order.
    let ExprKind::Const(f_name, _f_levels) = lhs.get_app_fn().kind() else {
        return None;
    };
    let lhs_args = lhs.get_app_args();
    if lhs_args.len() != k {
        return None;
    }
    for (i, arg) in lhs_args.iter().enumerate() {
        // The outermost binder (`doms[0]`) has de Bruijn index `k-1` in the
        // conclusion; the innermost has index 0.
        let expected = u32::try_from(k - 1 - i).ok()?;
        match arg.strip_mdata().kind() {
            ExprKind::BVar(idx) if *idx == expected => {}
            _ => return None,
        }
    }

    // `f` must be a value-FREE constant already registered in the env.
    let f_decl = env.get_const(f_name)?;
    if f_decl.value.is_some() {
        return None;
    }

    // Acyclicity: `rhs` must not mention `f`.
    if rhs.collect_constants().contains(f_name) {
        return None;
    }

    // `f := fun binders => rhs`, reusing the equation's binder domains (which
    // ARE `f`'s parameter types, since `f` is applied to exactly them).
    let f_value = build_lambda(&doms, rhs.clone());

    Some(LockEquation {
        f_name: f_name.clone(),
        f_level_params: f_decl.level_params.clone(),
        f_type: f_decl.type_.clone(),
        f_value,
    })
}

/// Attempt the LOCK-PATTERN discharge (BRICK 1.1) of the value-free equation
/// `decl_name : ∀ binders, @eq A (f binders) rhs`.
///
/// On a recognised lock (see [`parse_lock_equation`]):
///
///   1. UPGRADE `f` from its value-free axiom stub to the checked definition
///      `f := fun binders => rhs` via the audited
///      [`Environment::upgrade_axiom_to_checked_decl`] — the kernel checks
///      `rhs` against `f`'s type with `f`'s stub REMOVED, so a self-supporting
///      or ill-typed `rhs` fails closed and `env` is left untouched. `f` becomes
///      value-bearing, so every downstream constant the seal was blocking now
///      re-verifies against it (they follow `f`/the equation in topological
///      order, being the only handle on `f`'s value).
///   2. Discharge the equation ITSELF: with `f` now definitionally equal to
///      `rhs`, `∀ binders, @eq A (f binders) rhs` holds by reflexivity, proven
///      `fun binders => eq_refl A (f binders)` ([`build_eq_refl_of_lhs`]).
///
/// Returns [`DischargeAttempt::Discharged`] only when BOTH the upgrade and the
/// reflexivity proof are kernel-accepted; on any shape/guard miss it is
/// [`DischargeAttempt::NotAttempted`] and on any kernel rejection
/// [`DischargeAttempt::ProofRejected`]. In every non-`Discharged` arm the caller
/// mints the equation as a plain axiom byte-identically (regressed-0 by
/// construction — this runs only in the value-free `Axiom`/`Quot` arm).
///
/// Restricting the relation to Coq's `eq` and requiring the reflexivity proof
/// to close makes the upgrade faithful: `f` is defined to `rhs` only for a
/// genuine `f = rhs` fact. (Because the upgrade precedes the reflexivity check,
/// a matched-shape lock whose reflexivity step somehow failed would leave `f`
/// upgraded — but for a genuine `Coq.eq` lock the post-upgrade `f binders ≡ rhs`
/// makes that step succeed unconditionally, so the two are effectively atomic.)
pub(crate) fn attempt_lock_pattern_discharge(
    env: &mut Environment,
    decl_name: &Name,
    level_params: &[Name],
    imported_type: &Expr,
) -> DischargeAttempt {
    // Parse under an immutable borrow that is fully released (all fields owned)
    // before the `&mut env` upgrade below.
    let Some(lock) = parse_lock_equation(env, imported_type) else {
        return DischargeAttempt::NotAttempted;
    };

    // Step 1: unseal `f` (transactional; kernel-checked; stub removed for the
    // check so self-reference is impossible).
    let f_definition = Declaration::Definition {
        name: lock.f_name.clone(),
        level_params: lock.f_level_params,
        type_: lock.f_type,
        value: lock.f_value,
        // Regular (semireducible): the kernel delta-unfolds it during `is_def_eq`
        // under Default transparency (matching an ordinary Coq definition), so
        // dependents reduce through it, without the eager-unfold cost of
        // `Reducible` on bigop-heavy terms.
        is_reducible: false,
    };
    if let Err(err) = env.upgrade_axiom_to_checked_decl(f_definition) {
        return DischargeAttempt::ProofRejected(format!("lock unseal of {}: {err}", lock.f_name));
    }

    // Step 2: discharge the equation itself as `eq_refl` (holds by delta on the
    // just-unsealed `f`).
    let Some(proof) = build_eq_refl_of_lhs(env, imported_type) else {
        return DischargeAttempt::ProofRejected(format!(
            "lock equation {decl_name}: eq_refl proof shape declined after unseal"
        ));
    };
    let theorem = Declaration::Theorem {
        name: decl_name.clone(),
        level_params: level_params.to_vec(),
        type_: imported_type.clone(),
        value: proof,
    };
    match env.add_decl(theorem) {
        Ok(()) => DischargeAttempt::Discharged,
        Err(err) => DischargeAttempt::ProofRejected(format!("lock equation {decl_name}: {err}")),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::coq::alpha::{CoqImporter, CoqSessionRegistry};
    use crate::coq::universe_releveling::UniverseConstraintMiner;
    use crate::library::MathverseLibrary;
    use crate::shard::ShardReader;
    use crate::trust::policy::TrustPolicy;
    use crate::types::AxiomProfile;
    use crate::verify::incremental::{
        verify_corpus_incremental, verify_corpus_incremental_with_env, IncrementalVerifyReport,
    };
    use clean_kernel::expr::BinderInfo;
    use clean_kernel::level::Level;

    // VERBATIM Coq 8.20 stdlib dump forms (from
    // `data/corpora/coq-sexp/stdlib/*.sexp`). These are the exact importer
    // inputs the production `coq-import` lane consumes.

    /// `Coq.Init.Logic.eq` inductive (verbatim).
    const RAW_EQ_IND: &str = r#"(CoqInductive Coq.Init.Logic.eq 0 (Prod ((binder_name (Name (Id A))) (binder_relevance Relevant)) (Sort (Type ((((hash 739561026853) (data (Level ((DirPath ((Id Logic) (Id Init) (Id Coq))) 23503782208)))) 0)))) (Prod ((binder_name (Name (Id x))) (binder_relevance Relevant)) (Rel 1) (Prod ((binder_name Anonymous) (binder_relevance Relevant)) (Rel 2) (Sort Prop)))) (NumParams 2) (Ctor Coq.Init.Logic.eq_refl (Prod ((binder_name (Name (Id A))) (binder_relevance Relevant)) (Sort (Type ((((hash 739561026853) (data (Level ((DirPath ((Id Logic) (Id Init) (Id Coq))) 23503782208)))) 0)))) (Prod ((binder_name (Name (Id x))) (binder_relevance Relevant)) (Rel 1) (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id Logic) (Id Init) (Id Coq)))) (Id eq)) ()) 0) (Instance (() ())))) ((Rel 2) (Rel 1) (Rel 1)))))))"#;

    /// `Coq.Logic.ProofIrrelevance.proof_irrelevance` axiom (verbatim).
    const RAW_PROOF_IRRELEVANCE: &str = r#"(CoqAxiom Coq.Logic.ProofIrrelevance.proof_irrelevance (Prod ((binder_name (Name (Id P))) (binder_relevance Relevant)) (Sort Prop) (Prod ((binder_name (Name (Id p1))) (binder_relevance Relevant)) (Rel 1) (Prod ((binder_name (Name (Id p2))) (binder_relevance Relevant)) (Rel 2) (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id Logic) (Id Init) (Id Coq)))) (Id eq)) ()) 0) (Instance (() ())))) ((Rel 3) (Rel 2) (Rel 1)))))))"#;

    const EQ_CONST: &str = "Coq.Init.Logic.eq.0";
    const REFL_CONST: &str = "Coq.Init.Logic.eq.0.0";

    /// Full pipeline mirror of the production `coq-import` lane: mine → install
    /// → registry pre-passes → import → kernel verify (cumulative, as
    /// `coq_import_command` sets it). Returns the post-verify env and report.
    fn import_and_verify(input: &str) -> (clean_kernel::Environment, IncrementalVerifyReport) {
        let mut miner = UniverseConstraintMiner::default();
        miner.scan_signatures(input).expect("signature scan");
        miner.scan_constraints(input).expect("constraint scan");
        let bases = miner.solve();

        let mut registry = CoqSessionRegistry::default();
        registry.install_universe_bases(bases);
        CoqImporter
            .register_inductive_forms(input, &mut registry)
            .expect("inductive registration");
        CoqImporter
            .register_constant_shapes(input, &mut registry)
            .expect("constant-shape registration");
        let mut w = crate::shard::ShardWriter::new();
        CoqImporter
            .import_sexp_with_registry(input, &registry, &mut w)
            .expect("import");
        let mut buf = Vec::new();
        w.write(&mut buf).expect("shard serialization");
        let reader = ShardReader::from_bytes(&buf).expect("shard reader");
        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        lib.load_shard(&reader).expect("shard load");
        let mut prelude =
            clean_kernel::Environment::try_with_prelude().expect("kernel prelude environment");
        prelude.set_cumulative(true);
        verify_corpus_incremental_with_env(&lib, prelude)
    }

    /// Reconstruct one constant's imported type from a raw multi-form input by
    /// importing it and reading the constant's type back out of the shard.
    fn reconstruct_type(input: &str, name: &str) -> Expr {
        let mut registry = CoqSessionRegistry::default();
        CoqImporter
            .register_inductive_forms(input, &mut registry)
            .expect("inductive registration");
        CoqImporter
            .register_constant_shapes(input, &mut registry)
            .expect("constant-shape registration");
        let mut w = crate::shard::ShardWriter::new();
        CoqImporter
            .import_sexp_with_registry(input, &registry, &mut w)
            .expect("import");
        let mut buf = Vec::new();
        w.write(&mut buf).expect("shard serialization");
        let reader = ShardReader::from_bytes(&buf).expect("shard reader");
        let idx = reader
            .constants
            .iter()
            .position(|c| reader.strings.get(c.name_idx as usize).map(String::as_str) == Some(name))
            .unwrap_or_else(|| panic!("{name} not found in imported shard"));
        crate::inductive_replay::reconstruct_constant(name, &reader, &reader.constants[idx])
            .expect("reconstruct")
            .type_expr
    }

    /// An env with the `Coq.Init.Logic.eq` inductive registered exactly as the
    /// production import lane does (cumulative, for `Prop ≤ Type` coercion).
    fn env_with_eq() -> clean_kernel::Environment {
        let (env, _report) = import_and_verify(RAW_EQ_IND);
        assert!(
            env.get_const(&Name::from_string(EQ_CONST)).is_some(),
            "eq inductive must register"
        );
        assert!(
            env.get_const(&Name::from_string(REFL_CONST)).is_some(),
            "eq_refl constructor must register"
        );
        env
    }

    /// (a) POSITIVE — proof_irrelevance discharges end-to-end: the verbatim
    /// axiom, imported alongside `eq`, is proven by the kernel and appears in
    /// both the `discharged` and `kernel_verified` name sets.
    #[test]
    fn test_proof_irrelevance_discharges_end_to_end() {
        let input = format!("{RAW_EQ_IND}\n{RAW_PROOF_IRRELEVANCE}");
        let (_env, report) = import_and_verify(&input);
        let name = "Coq.Logic.ProofIrrelevance.proof_irrelevance";
        assert!(
            report.discharged_axiom_names.iter().any(|n| n == name),
            "proof_irrelevance must be discharged; discharged={:?} fallback={:?} failed={:?}",
            report.discharged_axiom_names,
            report.axiom_fallback_names,
            report.failures,
        );
        assert!(
            report.kernel_verified_names.iter().any(|n| n == name),
            "a discharged axiom counts as KernelVerified"
        );
    }

    /// (a) POSITIVE (unit) — the builder proves proof_irrelevance's VERBATIM
    /// imported type, and the kernel accepts the term as a `Theorem`.
    #[test]
    fn test_builder_proves_proof_irrelevance_type() {
        let mut env = env_with_eq();
        let ty = reconstruct_type(
            &format!("{RAW_EQ_IND}\n{RAW_PROOF_IRRELEVANCE}"),
            "Coq.Logic.ProofIrrelevance.proof_irrelevance",
        );
        let proof = build_eq_refl_of_lhs(&env, &ty).expect("builder must discharge");
        env.add_decl(Declaration::Theorem {
            name: Name::from_string("test.proof_irrel"),
            level_params: vec![],
            type_: ty,
            value: proof,
        })
        .expect("kernel must accept the eq_refl proof (definitional proof irrelevance)");
    }

    /// `∀ (A : Type 0) (x y : A), @eq A x y` in the imported `eq.0` spelling —
    /// a matching-shape but FALSE statement (`x ≢ y` at `Type` level). `A` sits
    /// at `Type 0 = Sort 1`, the level the importer collapses `eq`'s carrier
    /// parameter to, so the statement is well-formed against the registered eq.
    fn false_eq_type() -> Expr {
        let type0 = Expr::sort(Level::succ(Level::zero())); // Type 0 = Sort 1
        let eq = Expr::const_(Name::from_string(EQ_CONST), Vec::<Level>::new());
        // conclusion under 3 binders A,x,y: @eq A(bv2) x(bv1) y(bv0)
        let concl = Expr::apps(eq, [Expr::bvar(2), Expr::bvar(1), Expr::bvar(0)]);
        Expr::pi(
            BinderInfo::Default,
            type0,
            Expr::pi(
                BinderInfo::Default,
                Expr::bvar(0),                                       // x : A
                Expr::pi(BinderInfo::Default, Expr::bvar(1), concl), // y : A
            ),
        )
    }

    /// (b) FAIL-CLOSED — the builder DOES fire on the matching `@eq A x y`
    /// shape and produces a well-formed `eq_refl A x`, but the kernel REJECTS
    /// it as a proof (`x ≢ y`), so the discharge falls through; the plain axiom
    /// registration of the SAME type then succeeds (byte-identical fallback).
    #[test]
    fn test_fail_closed_wrong_type_rejected_then_axiom_accepted() {
        let mut env = env_with_eq();
        let ty = false_eq_type();
        let proof = build_eq_refl_of_lhs(&env, &ty).expect("builder fires on the eq shape");
        let rejected = env.add_decl(Declaration::Theorem {
            name: Name::from_string("test.false_eq"),
            level_params: vec![],
            type_: ty.clone(),
            value: proof,
        });
        assert!(
            rejected.is_err(),
            "kernel must reject eq_refl A x : @eq A x y (x not defeq y) — fail closed"
        );
        // The axiom fallback of the identical type is well-formed and accepted.
        env.add_decl(Declaration::Axiom {
            name: Name::from_string("test.false_eq_axiom"),
            level_params: vec![],
            type_: ty,
        })
        .expect("axiom fallback registers the well-formed type");
    }

    /// (b') FAIL-CLOSED at the hook helper: `attempt_axiom_discharge` for a
    /// registered name whose proof the kernel rejects returns `ProofRejected`
    /// and leaves `env` untouched (so the caller mints the axiom as before).
    #[test]
    fn test_attempt_discharge_reports_proof_rejected() {
        // The registry matches by the real name; feeding the real name with a
        // FALSE `@eq A x y` type forces the built proof to be kernel-rejected.
        let mut env = env_with_eq();
        let ty = false_eq_type();
        let name = Name::from_string("Coq.Logic.ProofIrrelevance.proof_irrelevance");
        match attempt_axiom_discharge(&mut env, &name, &[], &ty) {
            DischargeAttempt::ProofRejected(_) => {}
            DischargeAttempt::Discharged => panic!("must not discharge a false statement"),
            DischargeAttempt::NotAttempted => panic!("builder should have fired on eq shape"),
        }
        assert!(
            env.get_const(&name).is_none(),
            "a rejected discharge must leave env untouched"
        );
    }

    /// (c) SHAPE-MISMATCH — a type whose conclusion is not a `Const`-headed
    /// eq application returns `None` (no discharge attempted).
    #[test]
    fn test_shape_mismatch_returns_none() {
        let env = env_with_eq();
        // `∀ (P : Prop), P` — conclusion is a bound var, not an eq app.
        let ty = Expr::pi(BinderInfo::Default, Expr::prop(), Expr::bvar(0));
        assert!(build_eq_refl_of_lhs(&env, &ty).is_none());
    }

    /// (c') SHAPE-MATCH but MISSING constructor — the derived `<eq>.0`
    /// constructor is not registered, so the builder fails closed.
    #[test]
    fn test_missing_eq_constructor_returns_none() {
        // Bare prelude, no Coq eq inductive registered.
        let env = clean_kernel::Environment::try_with_prelude().expect("prelude");
        let ty = false_eq_type();
        assert!(
            build_eq_refl_of_lhs(&env, &ty).is_none(),
            "no `{REFL_CONST}` in env ⇒ fail closed"
        );
    }

    /// (d-helper) An unrelated name with no discharge builder is unaffected:
    /// `try_build_discharge_proof` returns `None` for any name not registered.
    #[test]
    fn test_unregistered_name_not_attempted() {
        let env = env_with_eq();
        let ty = reconstruct_type(
            &format!("{RAW_EQ_IND}\n{RAW_PROOF_IRRELEVANCE}"),
            "Coq.Logic.ProofIrrelevance.proof_irrelevance",
        );
        assert!(try_build_discharge_proof(&env, "Some.Unrelated.axiom", &ty).is_none());
    }

    /// The `DISCHARGED_AXIOM` provenance flag is a non-axiom hint: a constant
    /// carrying only it reads as kernel-verified with zero axiom dependencies.
    #[test]
    fn test_discharged_profile_is_kernel_verified() {
        let p = AxiomProfile::DISCHARGED_AXIOM;
        assert!(
            p.is_kernel_verified(),
            "discharged is a proof, not an axiom"
        );
        assert_eq!(p.axiom_count(), 0);
    }

    /// Guard against a regression in the prod verify entry point used by
    /// `coq-import`: importing eq alone leaves it kernel-registered.
    #[test]
    fn test_eq_inductive_imports_clean() {
        let mut registry = CoqSessionRegistry::default();
        CoqImporter
            .register_inductive_forms(RAW_EQ_IND, &mut registry)
            .expect("register");
        let mut w = crate::shard::ShardWriter::new();
        CoqImporter
            .import_sexp_with_registry(RAW_EQ_IND, &registry, &mut w)
            .expect("import");
        let mut buf = Vec::new();
        w.write(&mut buf).expect("serialize");
        let reader = ShardReader::from_bytes(&buf).expect("reader");
        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        lib.load_shard(&reader).expect("load");
        let mut env = clean_kernel::Environment::try_with_prelude().expect("prelude");
        env.set_cumulative(true);
        let report = verify_corpus_incremental(&lib, env);
        assert_eq!(report.failed, 0, "eq import must not fail");
    }

    // ── BRICK 1.1: generic lock-pattern discharge ───────────────────────────

    /// `Type 0` (`Sort 1`) — the universe the importer collapses `eq`'s carrier
    /// parameter to (mirrors `false_eq_type`).
    fn type0() -> Expr {
        Expr::sort(Level::succ(Level::zero()))
    }

    /// A monomorphic `Const` (no universe instance) — the imported Coq spelling.
    fn c(name: &str) -> Expr {
        Expr::const_(Name::from_string(name), Vec::<Level>::new())
    }

    /// `@eq A lhs rhs` in the imported `Coq.Init.Logic.eq.0` spelling.
    fn eq_app(carrier: Expr, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(c(EQ_CONST), [carrier, lhs, rhs])
    }

    /// Register a value-free axiom `name : ty` (panics on kernel rejection).
    fn add_axiom(env: &mut clean_kernel::Environment, name: &str, ty: Expr) {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: ty,
        })
        .unwrap_or_else(|e| panic!("axiom {name}: {e}"));
    }

    fn is_value_free(env: &clean_kernel::Environment, name: &str) -> bool {
        env.get_const(&Name::from_string(name))
            .expect("constant present")
            .value
            .is_none()
    }

    /// Env with `eq`, a carrier `Test.T : Type 0`, an inhabitant `Test.a : T`,
    /// and the value-free LOCKED constant `Test.f : T`.
    fn env_with_lock_scaffold() -> clean_kernel::Environment {
        let mut env = env_with_eq();
        add_axiom(&mut env, "Test.T", type0());
        add_axiom(&mut env, "Test.a", c("Test.T"));
        add_axiom(&mut env, "Test.f", c("Test.T"));
        env
    }

    /// (a) POSITIVE (plain) — `f_def : @eq T f a` unseals `f := a` and the
    /// equation itself becomes a kernel-checked `eq_refl` theorem.
    #[test]
    fn test_lock_plain_unseals_f_and_discharges_equation() {
        let mut env = env_with_lock_scaffold();
        let ty = eq_app(c("Test.T"), c("Test.f"), c("Test.a"));
        let f_def = Name::from_string("Test.f_def");
        match attempt_lock_pattern_discharge(&mut env, &f_def, &[], &ty) {
            DischargeAttempt::Discharged => {}
            DischargeAttempt::NotAttempted => panic!("plain lock must be recognized"),
            DischargeAttempt::ProofRejected(e) => panic!("plain lock rejected: {e}"),
        }
        assert!(
            !is_value_free(&env, "Test.f"),
            "f must be unsealed to a value-bearing definition"
        );
        assert!(
            env.get_const(&f_def).is_some(),
            "the equation is registered as a kernel-checked theorem"
        );
    }

    /// (b) POSITIVE (∀-prefix) — `f2_def : ∀ x, @eq B (f2 x) x` unseals
    /// `f2 := fun x => x` and discharges the equation.
    #[test]
    fn test_lock_forall_prefix_unseals_and_discharges() {
        let mut env = env_with_eq();
        add_axiom(&mut env, "Test.B", type0());
        add_axiom(
            &mut env,
            "Test.f2",
            Expr::pi(BinderInfo::Default, c("Test.B"), c("Test.B")),
        );
        // ∀ (x : B), @eq B (f2 x) x
        let concl = eq_app(
            c("Test.B"),
            Expr::apps(c("Test.f2"), [Expr::bvar(0)]),
            Expr::bvar(0),
        );
        let ty = Expr::pi(BinderInfo::Default, c("Test.B"), concl);
        let name = Name::from_string("Test.f2_def");
        match attempt_lock_pattern_discharge(&mut env, &name, &[], &ty) {
            DischargeAttempt::Discharged => {}
            DischargeAttempt::NotAttempted => panic!("∀-prefix lock must be recognized"),
            DischargeAttempt::ProofRejected(e) => panic!("∀-prefix lock rejected: {e}"),
        }
        assert!(
            !is_value_free(&env, "Test.f2"),
            "f2 unsealed to `fun x => x`"
        );
    }

    /// (c-guard) NON-EQ RELATION — a 3-argument `Const`-headed application whose
    /// head is not Coq's `eq` never drives an unseal.
    #[test]
    fn test_guard_non_eq_relation_not_attempted() {
        let mut env = env_with_lock_scaffold();
        add_axiom(
            &mut env,
            "Test.rel",
            Expr::pi(
                BinderInfo::Default,
                c("Test.T"),
                Expr::pi(
                    BinderInfo::Default,
                    c("Test.T"),
                    Expr::pi(BinderInfo::Default, c("Test.T"), Expr::prop()),
                ),
            ),
        );
        let ty = Expr::apps(c("Test.rel"), [c("Test.T"), c("Test.f"), c("Test.a")]);
        match attempt_lock_pattern_discharge(&mut env, &Name::from_string("Test.rel_def"), &[], &ty)
        {
            DischargeAttempt::NotAttempted => {}
            _ => panic!("a non-eq relation must never unseal f"),
        }
        assert!(is_value_free(&env, "Test.f"), "f left untouched");
    }

    /// (c-guard) HYPOTHESIS BINDER — `∀ (x : B) (h : Prop-premise), @eq B (f3 x) b0`
    /// has `f3` applied to only SOME telescope binders (a partial application
    /// over the telescope), so it is rejected (the `PArray.get_out_of_bounds`
    /// premise class).
    #[test]
    fn test_guard_hypothesis_binder_not_attempted() {
        let mut env = env_with_eq();
        add_axiom(&mut env, "Test.B", type0());
        add_axiom(
            &mut env,
            "Test.f3",
            Expr::pi(BinderInfo::Default, c("Test.B"), c("Test.B")),
        );
        add_axiom(&mut env, "Test.b0", c("Test.B"));
        // hypothesis h : @eq B b0 b0 (a Prop premise f3 is NOT applied to).
        let hyp = eq_app(c("Test.B"), c("Test.b0"), c("Test.b0"));
        // conclusion under [x, h]: @eq B (f3 x) b0 — x is de Bruijn index 1.
        let concl = eq_app(
            c("Test.B"),
            Expr::apps(c("Test.f3"), [Expr::bvar(1)]),
            c("Test.b0"),
        );
        let ty = Expr::pi(
            BinderInfo::Default,
            c("Test.B"),
            Expr::pi(BinderInfo::Default, hyp, concl),
        );
        match attempt_lock_pattern_discharge(&mut env, &Name::from_string("Test.f3_def"), &[], &ty)
        {
            DischargeAttempt::NotAttempted => {}
            _ => panic!("a hypothesis-binder shape must be rejected"),
        }
        assert!(is_value_free(&env, "Test.f3"), "f3 left untouched");
    }

    /// (c-guard) ACYCLICITY / byte-identical AxiomAccepted — `@eq T f f` has
    /// `rhs` mentioning `f`, so it is not a lock; it stays a plain axiom (the
    /// exact fall-through the caller takes on `NotAttempted`).
    #[test]
    fn test_guard_rhs_mentions_f_stays_axiom() {
        let mut env = env_with_lock_scaffold();
        let ty = eq_app(c("Test.T"), c("Test.f"), c("Test.f"));
        let f_def = Name::from_string("Test.f_refl");
        match attempt_lock_pattern_discharge(&mut env, &f_def, &[], &ty) {
            DischargeAttempt::NotAttempted => {}
            _ => panic!("rhs-mentions-f must not unseal (acyclicity)"),
        }
        assert!(is_value_free(&env, "Test.f"), "f left untouched");
        // Byte-identical fall-through: the well-typed equation registers as a
        // plain axiom, exactly as `AxiomAccepted` would.
        env.add_decl(Declaration::Axiom {
            name: f_def,
            level_params: vec![],
            type_: ty,
        })
        .expect("well-typed equation still registers as a plain axiom");
    }

    /// (c-guard) F ALREADY VALUE-BEARING — nothing to unseal.
    #[test]
    fn test_guard_value_bearing_f_not_attempted() {
        let mut env = env_with_eq();
        add_axiom(&mut env, "Test.T", type0());
        add_axiom(&mut env, "Test.a", c("Test.T"));
        env.add_decl(Declaration::Definition {
            name: Name::from_string("Test.fd"),
            level_params: vec![],
            type_: c("Test.T"),
            value: c("Test.a"),
            is_reducible: false,
        })
        .expect("value-bearing def");
        let ty = eq_app(c("Test.T"), c("Test.fd"), c("Test.a"));
        match attempt_lock_pattern_discharge(&mut env, &Name::from_string("Test.fd_def"), &[], &ty)
        {
            DischargeAttempt::NotAttempted => {}
            _ => panic!("a value-bearing f has nothing to unseal"),
        }
    }

    /// (c-guard) F NOT YET IN ENV — the ordering invariant. Topological order
    /// guarantees `f` (referenced by the equation's type) is classified first;
    /// if it is somehow absent, the discharge declines rather than fabricating.
    #[test]
    fn test_guard_f_absent_not_attempted() {
        let mut env = env_with_eq();
        add_axiom(&mut env, "Test.T", type0());
        add_axiom(&mut env, "Test.a", c("Test.T"));
        let ty = eq_app(c("Test.T"), c("Missing.f"), c("Test.a"));
        match attempt_lock_pattern_discharge(
            &mut env,
            &Name::from_string("Missing.f_def"),
            &[],
            &ty,
        ) {
            DischargeAttempt::NotAttempted => {}
            _ => panic!("an unregistered f must not be unsealed"),
        }
    }

    /// (d) FAIL-CLOSED — the kernel REJECTS the unseal (`rhs : U` cannot be
    /// `f : T`'s value); the upgrade is transactional, so `f`'s axiom stub is
    /// left intact and the caller mints the equation as a plain axiom.
    #[test]
    fn test_fail_closed_kernel_rejects_unseal_leaves_env_untouched() {
        let mut env = env_with_lock_scaffold();
        add_axiom(&mut env, "Test.U", type0());
        add_axiom(&mut env, "Test.u", c("Test.U"));
        // f_def : @eq T f u — `u : U`, but `f : T`; the unseal `f := u` fails.
        let ty = eq_app(c("Test.T"), c("Test.f"), c("Test.u"));
        match attempt_lock_pattern_discharge(
            &mut env,
            &Name::from_string("Test.f_def_bad"),
            &[],
            &ty,
        ) {
            DischargeAttempt::ProofRejected(_) => {}
            DischargeAttempt::NotAttempted => panic!("the eq shape should have matched"),
            DischargeAttempt::Discharged => panic!("the kernel must reject u : T"),
        }
        assert!(
            is_value_free(&env, "Test.f"),
            "a rejected unseal must restore f's axiom stub verbatim"
        );
    }

    // ── BRICK 1.2: the logic/choice axiom-discharge family ───────────────────
    //
    // Verbatim Coq 8.20 stdlib dump forms (from `Coq.Init.Logic.sexp` /
    // `Coq.Init.Specif.sexp` and the axioms' home modules). Each end-to-end
    // test imports the axiom alongside its exact dependency closure and asserts
    // the production `coq-import` lane both DISCHARGES it and counts it
    // `KernelVerified`.

    const RAW_FALSE_IND: &str =
        r#"(CoqInductive Coq.Init.Logic.False 0 (Sort Prop) (NumParams 0))"#;

    const RAW_OR_IND: &str = r#"(CoqInductive Coq.Init.Logic.or 0 (Prod ((binder_name (Name (Id A))) (binder_relevance Relevant)) (Sort Prop) (Prod ((binder_name (Name (Id B))) (binder_relevance Relevant)) (Sort Prop) (Sort Prop))) (NumParams 2) (Ctor Coq.Init.Logic.or_introl (Prod ((binder_name (Name (Id A))) (binder_relevance Relevant)) (Sort Prop) (Prod ((binder_name (Name (Id B))) (binder_relevance Relevant)) (Sort Prop) (Prod ((binder_name Anonymous) (binder_relevance Relevant)) (Rel 2) (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id Logic) (Id Init) (Id Coq)))) (Id or)) ()) 0) (Instance (() ())))) ((Rel 3) (Rel 2))))))) (Ctor Coq.Init.Logic.or_intror (Prod ((binder_name (Name (Id A))) (binder_relevance Relevant)) (Sort Prop) (Prod ((binder_name (Name (Id B))) (binder_relevance Relevant)) (Sort Prop) (Prod ((binder_name Anonymous) (binder_relevance Relevant)) (Rel 1) (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id Logic) (Id Init) (Id Coq)))) (Id or)) ()) 0) (Instance (() ())))) ((Rel 3) (Rel 2))))))))"#;

    const RAW_AND_IND: &str = r#"(CoqInductive Coq.Init.Logic.and 0 (Prod ((binder_name (Name (Id A))) (binder_relevance Relevant)) (Sort Prop) (Prod ((binder_name (Name (Id B))) (binder_relevance Relevant)) (Sort Prop) (Sort Prop))) (NumParams 2) (Ctor Coq.Init.Logic.conj (Prod ((binder_name (Name (Id A))) (binder_relevance Relevant)) (Sort Prop) (Prod ((binder_name (Name (Id B))) (binder_relevance Relevant)) (Sort Prop) (Prod ((binder_name Anonymous) (binder_relevance Relevant)) (Rel 2) (Prod ((binder_name Anonymous) (binder_relevance Relevant)) (Rel 2) (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id Logic) (Id Init) (Id Coq)))) (Id and)) ()) 0) (Instance (() ())))) ((Rel 4) (Rel 3)))))))))"#;

    const RAW_NOT_CONST: &str = r#"(CoqConstant Coq.Init.Logic.not (Prod ((binder_name (Name (Id A))) (binder_relevance Relevant)) (Sort Prop) (Sort Prop)) (Lambda ((binder_name (Name (Id A))) (binder_relevance Relevant)) (Sort Prop) (Prod ((binder_name Anonymous) (binder_relevance Relevant)) (Rel 1) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Logic) (Id Init) (Id Coq)))) (Id False)) ()) 0) (Instance (() ())))))))"#;

    const RAW_IFF_CONST: &str = r#"(CoqConstant Coq.Init.Logic.iff (Prod ((binder_name (Name (Id A))) (binder_relevance Relevant)) (Sort Prop) (Prod ((binder_name (Name (Id B))) (binder_relevance Relevant)) (Sort Prop) (Sort Prop))) (Lambda ((binder_name (Name (Id A))) (binder_relevance Relevant)) (Sort Prop) (Lambda ((binder_name (Name (Id B))) (binder_relevance Relevant)) (Sort Prop) (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id Logic) (Id Init) (Id Coq)))) (Id and)) ()) 0) (Instance (() ())))) ((Prod ((binder_name Anonymous) (binder_relevance Relevant)) (Rel 2) (Rel 2)) (Prod ((binder_name Anonymous) (binder_relevance Relevant)) (Rel 1) (Rel 3)))))))"#;

    const RAW_CLASSIC: &str = r#"(CoqAxiom Coq.Logic.Classical_Prop.classic (Prod ((binder_name (Name (Id P))) (binder_relevance Relevant)) (Sort Prop) (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id Logic) (Id Init) (Id Coq)))) (Id or)) ()) 0) (Instance (() ())))) ((Rel 1) (App (Const ((Constant (KerName (MPfile (DirPath ((Id Logic) (Id Init) (Id Coq)))) (Id not)) ()) (Instance (() ())))) ((Rel 1)))))))"#;

    const RAW_FUNEXT_DEP: &str = r#"(CoqAxiom Coq.Logic.FunctionalExtensionality.functional_extensionality_dep (Prod ((binder_name (Name (Id A))) (binder_relevance Relevant)) (Sort (Type ((((hash -3080233789710231625) (data (Level ((DirPath ((Id FunctionalExtensionality) (Id Logic) (Id Coq))) 23650315508)))) 0)))) (Prod ((binder_name (Name (Id B))) (binder_relevance Relevant)) (Prod ((binder_name Anonymous) (binder_relevance Relevant)) (Rel 1) (Sort (Type ((((hash -3080233789710166026) (data (Level ((DirPath ((Id FunctionalExtensionality) (Id Logic) (Id Coq))) 23650315508)))) 0))))) (Prod ((binder_name (Name (Id f))) (binder_relevance Relevant)) (Prod ((binder_name (Name (Id x))) (binder_relevance Relevant)) (Rel 2) (App (Rel 2) ((Rel 1)))) (Prod ((binder_name (Name (Id g))) (binder_relevance Relevant)) (Prod ((binder_name (Name (Id x))) (binder_relevance Relevant)) (Rel 3) (App (Rel 3) ((Rel 1)))) (Prod ((binder_name Anonymous) (binder_relevance Relevant)) (Prod ((binder_name (Name (Id x))) (binder_relevance Relevant)) (Rel 4) (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id Logic) (Id Init) (Id Coq)))) (Id eq)) ()) 0) (Instance (() ())))) ((App (Rel 4) ((Rel 1))) (App (Rel 3) ((Rel 1))) (App (Rel 2) ((Rel 1)))))) (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id Logic) (Id Init) (Id Coq)))) (Id eq)) ()) 0) (Instance (() ())))) ((Prod ((binder_name (Name (Id x))) (binder_relevance Relevant)) (Rel 5) (App (Rel 5) ((Rel 1)))) (Rel 3) (Rel 2)))))))))"#;

    const RAW_PROPEXT: &str = r#"(CoqAxiom Coq.Logic.PropExtensionality.propositional_extensionality (Prod ((binder_name (Name (Id P))) (binder_relevance Relevant)) (Sort Prop) (Prod ((binder_name (Name (Id Q))) (binder_relevance Relevant)) (Sort Prop) (Prod ((binder_name Anonymous) (binder_relevance Relevant)) (App (Const ((Constant (KerName (MPfile (DirPath ((Id Logic) (Id Init) (Id Coq)))) (Id iff)) ()) (Instance (() ())))) ((Rel 2) (Rel 1))) (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id Logic) (Id Init) (Id Coq)))) (Id eq)) ()) 0) (Instance (() ())))) ((Sort Prop) (Rel 3) (Rel 2)))))))"#;

    /// Assert an axiom name appears in BOTH the discharged and kernel-verified
    /// sets of an incremental verify report (diagnostics on failure).
    fn assert_discharged(report: &IncrementalVerifyReport, name: &str) {
        assert!(
            report.discharged_axiom_names.iter().any(|n| n == name),
            "{name} must be DISCHARGED; discharged={:?} fallback={:?} failures={:?}",
            report.discharged_axiom_names,
            report.axiom_fallback_names,
            report.failures,
        );
        assert!(
            report.kernel_verified_names.iter().any(|n| n == name),
            "a discharged axiom counts as KernelVerified: {name}"
        );
    }

    /// (a) POSITIVE — `classic` discharges end-to-end to `Classical.em`.
    #[test]
    fn test_classic_discharges_end_to_end() {
        let input = format!("{RAW_FALSE_IND}\n{RAW_OR_IND}\n{RAW_NOT_CONST}\n{RAW_CLASSIC}");
        let (_env, report) = import_and_verify(&input);
        assert_discharged(&report, "Coq.Logic.Classical_Prop.classic");
    }

    /// (a) POSITIVE — `functional_extensionality_dep` discharges to `funext`.
    #[test]
    fn test_funext_dep_discharges_end_to_end() {
        let input = format!("{RAW_EQ_IND}\n{RAW_FUNEXT_DEP}");
        let (_env, report) = import_and_verify(&input);
        assert_discharged(
            &report,
            "Coq.Logic.FunctionalExtensionality.functional_extensionality_dep",
        );
    }

    /// (a) POSITIVE — `propositional_extensionality` discharges to `propext`.
    #[test]
    fn test_propext_discharges_end_to_end() {
        let input = format!("{RAW_EQ_IND}\n{RAW_AND_IND}\n{RAW_IFF_CONST}\n{RAW_PROPEXT}");
        let (_env, report) = import_and_verify(&input);
        assert_discharged(
            &report,
            "Coq.Logic.PropExtensionality.propositional_extensionality",
        );
    }

    /// (b) NEGATIVE control — each builder declines a wrong-shape type (`∀ P,
    /// P`), returning `None` (never a fabricated proof).
    #[test]
    fn test_family_builders_decline_wrong_shape() {
        let env = env_with_eq();
        let ty = Expr::pi(BinderInfo::Default, Expr::prop(), Expr::bvar(0));
        assert!(build_classic(&env, &ty).is_none(), "classic wrong-shape");
        assert!(build_funext_dep(&env, &ty).is_none(), "funext wrong-shape");
        assert!(build_propext(&env, &ty).is_none(), "propext wrong-shape");
    }

    /// (b') NEGATIVE control — the family builders decline the OTHER family
    /// members' verbatim types (arity / connective guards): the 1-binder
    /// `classic` shape is not a 5-binder funext, etc. Confirms the registry's
    /// exact-name keying is backed by real shape discrimination.
    #[test]
    fn test_family_builders_are_shape_specific() {
        // eq + or + and + iff + not so every referenced connective resolves.
        let input = format!(
            "{RAW_EQ_IND}\n{RAW_FALSE_IND}\n{RAW_OR_IND}\n{RAW_AND_IND}\n{RAW_NOT_CONST}\n{RAW_IFF_CONST}"
        );
        let (env, _r) = import_and_verify(&input);
        let classic_ty = reconstruct_type(
            &format!("{RAW_FALSE_IND}\n{RAW_OR_IND}\n{RAW_NOT_CONST}\n{RAW_CLASSIC}"),
            "Coq.Logic.Classical_Prop.classic",
        );
        let propext_ty = reconstruct_type(
            &format!("{RAW_EQ_IND}\n{RAW_AND_IND}\n{RAW_IFF_CONST}\n{RAW_PROPEXT}"),
            "Coq.Logic.PropExtensionality.propositional_extensionality",
        );
        // funext (5 binders) is not classic (1 binder) or propext (3 binders).
        assert!(build_funext_dep(&env, &classic_ty).is_none());
        assert!(build_funext_dep(&env, &propext_ty).is_none());
        // classic keys on a 1-binder `or`-headed conclusion, not propext's 3.
        assert!(build_classic(&env, &propext_ty).is_none());
        // propext keys on 3 binders with an eq conclusion, not classic's 1.
        assert!(build_propext(&env, &classic_ty).is_none());
    }
}
