// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Declared binder rows of the `coinductive` lowering: the DECLARATION
//! PARAMETER row (the declaration-parameters rung of the full-gfp program)
//! and the constructor-binder envelope (Brick 2, moved here whole from the
//! parent module — same module-tree split as [`super::generate`]).
//!
//! # The declaration-parameters rung
//!
//! ```text
//! coinductive P (p₁ : A₁) … (pₖ : Aₖ) : T⃗ → Prop
//! ```
//!
//! The parameter row is FIXED through the coinduction. Encoding choice
//! (documented, pinned by the golden tests): **(b) — params are prefix
//! binders on `P` and EVERY companion quantifies over them outermost**; the
//! candidate relation stays `T⃗ → Prop` at fixed `p⃗` and the recursive
//! substitution happens at `P p⃗` only, so `P.F : (p⃗ : A⃗) →
//! (T⃗ → Prop) → T⃗ → Prop` and `P p⃗ v⃗ := ∃ R, (∀ v⃗, R v⃗ →
//! P.F p⃗ R v⃗) ∧ R v⃗`. The alternative (a per-instantiation fixpoint of
//! an `F` that alone abstracts the row) cannot name ONE `P`, and a
//! param-indexed candidate (`R : A⃗ → T⃗ → Prop`) would bloat every Park
//! obligation with a row the envelope guarantees never varies. Under (b)
//! the zero-parameter output is BYTE-IDENTICAL to the pre-rung output (an
//! empty prefix row is a no-op at every site), which the golden regression
//! pins.
//!
//! Constructors must apply `P` to EXACTLY the declared row first — in the
//! target AND in every recursive occurrence — mirroring the kernel's strict
//! inductive discipline (`crates/clean-kernel/src/inductive/strict.rs`
//! check 3: the first `num_params` constructor-target arguments must be
//! exactly the enclosing parameter variables, anything else is
//! `ConstructorParamMismatch`). A position that varies across occurrences
//! is an INDEX, not a parameter, and refuses by name ([`check_param_row`]).
//!
//! Parameter binder info on the generated companions: EXPLICIT everywhere —
//! including the intro theorems, a documented deviation from the inductive
//! lane (which makes ctor params implicit): the intro is a generated
//! THEOREM whose leading explicit ∀ group is "every declared binder", and
//! the parameter row is declared — EXCEPT `P.cases`, where the row is
//! IMPLICIT exactly like the index row (both are forced by the major
//! premise `P p⃗ v⃗`).
//!
//! Universe parameters stay REFUSED by name (the parent `validate`): the
//! greatest-fixpoint lowering is monomorphic; only DECLARATION parameters
//! lift here.

use super::{all_predicate_idents, known_constant, mentions, unsupported, ElabError, Environment};
use clean_parser::{SurfaceArg, SurfaceBinder, SurfaceBinderInfo, SurfaceExpr, SurfaceName};

/// Validate the declaration-parameter row against its envelope. Every
/// refusal is named; the returned row is the validated binders verbatim
/// (explicit info, explicit `P`-free types).
pub(super) fn validate_params(
    what: &str,
    short: &SurfaceName,
    env: &Environment,
    binders: &[SurfaceBinder],
) -> Result<Vec<SurfaceBinder>, ElabError> {
    for (i, b) in binders.iter().enumerate() {
        if b.name.is_unescaped_component("_") {
            return Err(unsupported(format!(
                "{what}: declares the anonymous declaration parameter `_`; \
                 every parameter must be NAMED — the whole companion family \
                 applies the parameter row by name, and constructors must \
                 spell it (`{short} p⃗ …`)"
            )));
        }
        if b.info != SurfaceBinderInfo::Explicit {
            return Err(unsupported(format!(
                "{what}: declaration parameter `{}` is implicit/instance; \
                 only explicit `({} : T)` declaration parameters are \
                 supported — every generated companion takes the parameter \
                 row as leading explicit arguments (`P.cases` alone binds \
                 it implicitly, alongside the index row)",
                b.name, b.name
            )));
        }
        if b.default.is_some() {
            return Err(unsupported(format!(
                "{what}: declaration parameter `{}` carries a default \
                 value, which has no meaning for a fixed parameter row",
                b.name
            )));
        }
        let Some(bty) = b.ty.as_deref() else {
            return Err(unsupported(format!(
                "{what}: declaration parameter `{}` must be explicitly \
                 typed (`({} : T)`) — its type is a leading Π domain of \
                 every generated companion",
                b.name, b.name
            )));
        };
        if short.has_prefix(&b.name) {
            return Err(unsupported(format!(
                "{what}: declaration parameter `{}` is named after the \
                 predicate or its qualified root; every occurrence of `{short}` in a \
                 constructor must be the recursive predicate, not a local",
                b.name
            )));
        }
        if super::has_generated_marker(&b.name) {
            return Err(unsupported(format!(
                "{what}: declaration parameter `{}` carries the `_coind` \
                 marker reserved for generated binder names — it could be \
                 captured inside the generated proofs",
                b.name
            )));
        }
        if binders[..i].iter().any(|p| p.name == b.name) {
            return Err(unsupported(format!(
                "{what}: declares declaration parameter `{}` twice; the \
                 leading Π row would shadow the first occurrence",
                b.name
            )));
        }
        if mentions(bty, short) {
            return Err(unsupported(format!(
                "{what}: the type of declaration parameter `{}` mentions \
                 `{short}` — the parameter row must be `{short}`-free; a \
                 self-referential parameter type has no greatest-fixpoint \
                 reading here",
                b.name
            )));
        }
        // Free variables of a parameter type: earlier parameters and
        // existing constants only — the same auto-bind hazard as premises,
        // at the outermost Π domain of every companion.
        let mut bound: Vec<&SurfaceName> = Vec::new();
        let mut fvs: Vec<&SurfaceName> = Vec::new();
        all_predicate_idents(bty, short, &mut bound, &mut fvs).map_err(|label| {
            unsupported(format!(
                "{what}: the type of declaration parameter `{}` uses the \
                 non-applicative surface form `{label}`; parameter types \
                 must be built from identifiers, applications, arrows and \
                 binders",
                b.name
            ))
        })?;
        for fv in fvs {
            if binders[..i].iter().any(|p| &p.name == fv) || known_constant(env, fv) {
                continue;
            }
            return Err(unsupported(format!(
                "{what}: the type of declaration parameter `{}` mentions \
                 `{fv}`, which is neither an earlier declaration parameter \
                 nor a known constant; refusing to auto-bind it into the \
                 generated companion family",
                b.name
            )));
        }
    }
    Ok(binders.to_vec())
}

/// Check that the first `params.len()` arguments of a fully-applied
/// occurrence of `short` are EXACTLY the declared parameter row — each a
/// bare identifier naming its parameter, positionally. The mirror of the
/// kernel's strict inductive check 3 (`inductive/strict.rs`:
/// `ConstructorParamMismatch`): a parameter is FIXED across the whole
/// declaration, and a position that varies is an INDEX, not a parameter.
///
/// `Err` carries the WHY; callers prefix the declaration/constructor
/// context.
pub(super) fn check_param_row(
    args: &[SurfaceArg],
    param_names: &[SurfaceName],
    short: &SurfaceName,
) -> Result<(), String> {
    for (i, p) in param_names.iter().enumerate() {
        let ok = matches!(
            super::strip_parens(&args[i].expr),
            SurfaceExpr::Ident(_, id) if id == p
        );
        if !ok {
            return Err(format!(
                "an occurrence of `{short}` must apply the declaration-\
                 parameter row first, EXACTLY as declared (`{short} {} …`); \
                 argument {} here is not the parameter `{p}` — a parameter \
                 is FIXED across the whole declaration, and a position that \
                 varies across occurrences is an INDEX, not a parameter \
                 (declare it as an index instead)",
                super::join_names(param_names),
                i + 1
            ));
        }
    }
    Ok(())
}

/// The constructor-binder envelope (Brick 2; moved here whole from the
/// parent module, plus the declaration-parameter shadow refusal). Each
/// declared leading binder becomes an ∃-bound variable of its constructor's
/// functor disjunct — every clause fail-closed; see the parent module doc.
#[allow(clippy::too_many_arguments)]
pub(super) fn check_ctor_binders(
    what: &str,
    short: &SurfaceName,
    env: &Environment,
    ci: usize,
    shared: &[SurfaceName],
    param_names: &[SurfaceName],
    ctor_name: &SurfaceName,
    ctor_binders: &[SurfaceBinder],
    subst_vars: &[SurfaceName],
) -> Result<(), ElabError> {
    for (bi, b) in ctor_binders.iter().enumerate() {
        let where_ = format!("{what}: constructor `{ctor_name}`");
        if b.name.is_unescaped_component("_") {
            return Err(unsupported(format!(
                "{where_} declares an anonymous binder `_`; an ∃-bound \
                 variable must be NAMED so the generated intro theorem \
                 can supply it as an `Exists.intro` witness"
            )));
        }
        if b.info != SurfaceBinderInfo::Explicit {
            return Err(unsupported(format!(
                "{where_} declares binder `{}` as implicit/instance; \
                 only explicit `({} : T)` constructor binders are \
                 supported — the generated intro theorem and `cases` \
                 arms take them as explicit leading ∀s",
                b.name, b.name
            )));
        }
        if b.default.is_some() {
            return Err(unsupported(format!(
                "{where_} declares binder `{}` with a default value, \
                 which has no meaning for an ∃-bound variable",
                b.name
            )));
        }
        let Some(bty) = b.ty.as_deref() else {
            return Err(unsupported(format!(
                "{where_} declares binder `{}` without a type; a \
                 constructor binder must be explicitly typed \
                 (`({} : T)`) — the type is the ∃ domain in the \
                 generated functor",
                b.name, b.name
            )));
        };
        if short.has_prefix(&b.name) {
            return Err(unsupported(format!(
                "{where_} declares binder `{}` named after the \
                 predicate or its qualified root; every occurrence of `{short}` in a \
                 premise must be the recursive predicate, not a local",
                b.name
            )));
        }
        if param_names.contains(&b.name) {
            return Err(unsupported(format!(
                "{where_} declares binder `{}`, which shadows the \
                 declaration parameter of the same name; under the shadow \
                 a recursive occurrence `{short} {} …` would no longer \
                 apply the FIXED parameter row",
                b.name,
                super::join_names(param_names)
            )));
        }
        if super::has_generated_marker(&b.name) {
            return Err(unsupported(format!(
                "{where_} declares binder `{}`, which carries the \
                 `_coind` marker reserved for generated binder names — \
                 it could be captured inside the generated proofs",
                b.name
            )));
        }
        if ctor_binders[..bi].iter().any(|p| p.name == b.name) {
            return Err(unsupported(format!(
                "{where_} declares binder `{}` twice; the ∃ nest would \
                 shadow the first occurrence",
                b.name
            )));
        }
        // Brick 3 RETIRED the Brick-2 overlap refusal: a binder in a
        // target position is no longer ambiguous — a bare once-occurring
        // type-matching binder IS the index (substitution), anything
        // else stays ∃-bound behind an index equation. A SUBSTITUTED
        // binder is exempt from the shared-row-name check below: it is
        // never ∃-bound, so no capturing binder of that name exists.
        if ci > 0 && shared.contains(&b.name) && !subst_vars.contains(&b.name) {
            return Err(unsupported(format!(
                "{where_} declares binder `{}`, which is a shared \
                 index-row name of the first constructor; under the \
                 α-rename onto the shared row that binder would capture \
                 the renamed index variable",
                b.name
            )));
        }
        if mentions(bty, short) {
            return Err(unsupported(format!(
                "{where_}: the type of binder `{}` mentions `{short}` — \
                 a predicate occurrence inside a binder type is a \
                 nested/negative-position hazard whose positivity is \
                 not established here; binder types must be \
                 `{short}`-free",
                b.name
            )));
        }
        // Free variables of the binder type: index-substituted target
        // variables, EARLIER binders, declaration parameters and existing
        // constants only — the same auto-bind hazard as premises, at the
        // ∃ domain position.
        let mut bound: Vec<&SurfaceName> = Vec::new();
        let mut fvs: Vec<&SurfaceName> = Vec::new();
        all_predicate_idents(bty, short, &mut bound, &mut fvs).map_err(|label| {
            unsupported(format!(
                "{where_}: the type of binder `{}` uses the \
                 non-applicative surface form `{label}`; binder types \
                 must be built from identifiers, applications, arrows \
                 and binders",
                b.name
            ))
        })?;
        for fv in fvs {
            if subst_vars.iter().any(|v| v == fv)
                || ctor_binders[..bi].iter().any(|p| &p.name == fv)
                || param_names.iter().any(|p| p == fv)
                || known_constant(env, fv)
            {
                continue;
            }
            return Err(unsupported(format!(
                "{where_}: the type of binder `{}` mentions `{fv}`, \
                 which is neither a target variable, an earlier binder \
                 of this constructor, nor a known constant; refusing to \
                 auto-bind it into the generated one-step functor",
                b.name
            )));
        }
    }
    Ok(())
}
