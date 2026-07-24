// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Path-B translation harness** — Isabelle theorem `prop` → Lean 4 statement.
//!
//! Industrializes the hand translation that capped the Aristotle Path-B batches
//! at ~30–100 theorems: read a corpus line's `prop` (the [`IsaTerm`] shapes),
//! strip the Pure meta-skeleton (`Trueprop` / `Pure.imp`), generalize the
//! schematic variables to universals, and render the object term through the
//! [`fragments`] pattern library (connectives, arithmetic, lists, sets, orders).
//!
//! ## Faithfulness policy — unsupported over unfaithful
//!
//! The harness **never** emits a plausible-but-wrong statement. Every shape the
//! library cannot render exactly (unknown constant, class/locale premise,
//! polymorphic order/lattice, higher-order binder) yields a first-class
//! [`Unsupported`] verdict, routing that theorem to the human/agent curation
//! tail. The downstream statement-guard remains the enforcement backstop; this
//! lane's contract is only ever "faithful or declined".
//!
//! ## Pipeline
//!
//! 1. [`peel_meta`] — strip `Trueprop`, collect `Pure.imp` hypotheses (a
//!    non-`Trueprop` premise is a class premise → declined).
//! 2. [`collect_vars`] — schematic/free term variables in first-occurrence order
//!    become universally-quantified binders; grouped by rendered type.
//! 3. [`term::translate_term`] — render conclusion + hypotheses through the
//!    fragments.
//! 4. [`emit`] — assemble `theorem NAME BINDERS :\n    BODY`.

pub mod batch;
pub mod census;
mod fragments;
pub mod lean_type;
pub mod render;
pub mod term;
pub mod types;

#[cfg(test)]
mod golden_expansion_tests;
#[cfg(test)]
mod golden_tests;

use std::collections::HashSet;

use super::isabelle_pure::{IsaTerm, IsaType};
use lean_type::{render_type, TyCtx};
use term::{clean_ident, peel_spine, translate_term};
use types::{LeanGoal, SupportedGoal, Unsupported};

/// The Lean theorem name for an Isabelle theorem name: its last dotted
/// component (`List.append_assoc` → `append_assoc`,
/// `Groups.group_add.minus_minus` → `minus_minus`). This mirrors the
/// batch-established naming pattern.
#[must_use]
pub fn lean_name_from_isabelle(isa: &str) -> String {
    isa.rsplit('.').next().unwrap_or(isa).to_string()
}

/// Translate one theorem `prop` to a Lean statement named `name`.
///
/// Returns [`LeanGoal::Supported`] with the rendered signature, or
/// [`LeanGoal::Unsupported`] naming the declined shape. Never panics; never
/// emits an unfaithful statement.
#[must_use]
pub fn translate_prop(prop: &IsaTerm, name: &str) -> LeanGoal {
    match translate_prop_inner(prop, name) {
        Ok(goal) => LeanGoal::Supported(goal),
        Err(u) => LeanGoal::Unsupported(u),
    }
}

fn translate_prop_inner(prop: &IsaTerm, name: &str) -> Result<SupportedGoal, Unsupported> {
    let (hyps, concl) = peel_meta(prop)?;

    // Universally-quantified term variables, grouped by rendered type. Rendering
    // the binder types also interns the schematic type variables into `tcx`, so
    // the `{… : Type*}` binder can be assembled afterward.
    let mut tcx = TyCtx::default();
    let mut seen: HashSet<String> = HashSet::new();
    let mut ordered: Vec<(String, IsaType)> = Vec::new();
    for h in &hyps {
        collect_vars(h, &mut seen, &mut ordered);
    }
    collect_vars(concl, &mut seen, &mut ordered);

    let mut term_binders: Vec<(String, String)> = Vec::with_capacity(ordered.len());
    for (var, ty) in &ordered {
        let rendered_ty = render_type(ty, &mut tcx)?;
        term_binders.push((var.clone(), rendered_ty));
    }

    // Object-term bodies (may decline on an unknown constant / guarded shape).
    let concl_body = render::render_top(&translate_term(concl)?);
    let hyp_bodies: Result<Vec<String>, Unsupported> = hyps
        .iter()
        .map(|h| translate_term(h).map(|t| render::render_top(&t)))
        .collect();
    let hyp_bodies = hyp_bodies?;

    let signature = emit(name, &tcx, &term_binders, &hyp_bodies, &concl_body);
    Ok(SupportedGoal {
        name: name.to_string(),
        signature,
    })
}

/// Strip the Pure meta-skeleton: collect the `Trueprop`-wrapped `Pure.imp`
/// hypotheses and return them with the `Trueprop`-wrapped conclusion (the
/// object-level `bool` terms).
///
/// A `Pure.imp` antecedent that is **not** a `Trueprop` (a bare class/locale
/// predicate such as `group_add …`) is declined as a class premise; a top shape
/// that is neither `Pure.imp` nor `Trueprop` (e.g. `Pure.all`) is declined as an
/// unhandled meta shape.
///
/// # Errors
/// [`Unsupported::ClassPremise`] / [`Unsupported::MetaShape`].
fn peel_meta(prop: &IsaTerm) -> Result<(Vec<&IsaTerm>, &IsaTerm), Unsupported> {
    let mut hyps: Vec<&IsaTerm> = Vec::new();
    let mut t = prop;
    loop {
        let (head, args) = peel_spine(t);
        match head {
            IsaTerm::Const { n, .. } if n == "Pure.imp" && args.len() == 2 => {
                let ante = args[0];
                let hb = strip_trueprop(ante).ok_or_else(|| {
                    Unsupported::ClassPremise(head_const_name(ante).unwrap_or_default())
                })?;
                hyps.push(hb);
                t = args[1];
            }
            IsaTerm::Const { n, .. } if n == "HOL.Trueprop" && args.len() == 1 => {
                return Ok((hyps, args[0]));
            }
            _ => return Err(Unsupported::MetaShape),
        }
    }
}

/// The `bool` inside a `Trueprop b`, or `None` if `t` is not a `Trueprop`.
fn strip_trueprop(t: &IsaTerm) -> Option<&IsaTerm> {
    let (head, args) = peel_spine(t);
    match head {
        IsaTerm::Const { n, .. } if n == "HOL.Trueprop" && args.len() == 1 => Some(args[0]),
        _ => None,
    }
}

/// The head constant name of an application spine (for diagnostics).
fn head_const_name(t: &IsaTerm) -> Option<String> {
    match peel_spine(t).0 {
        IsaTerm::Const { n, .. } => Some(n.clone()),
        _ => None,
    }
}

/// Collect schematic/free term variables in first-occurrence pre-order (function
/// before argument), deduplicated by name. Bound variables and constants are
/// skipped; an `Abs` body is still walked (a lambda makes the whole term
/// unsupported downstream, so any variables gathered under it are inert).
fn collect_vars(t: &IsaTerm, seen: &mut HashSet<String>, out: &mut Vec<(String, IsaType)>) {
    match t {
        IsaTerm::Var { n, t, .. } | IsaTerm::Free { n, t, .. } => {
            let name = clean_ident(n);
            if seen.insert(name.clone()) {
                out.push((name, t.clone()));
            }
        }
        IsaTerm::App { f, a } => {
            collect_vars(f, seen, out);
            collect_vars(a, seen, out);
        }
        IsaTerm::Abs { b, .. } => collect_vars(b, seen, out),
        IsaTerm::Const { .. } | IsaTerm::Bound { .. } => {}
    }
}

/// Assemble the theorem signature (up to, not including, `:=`).
fn emit(
    name: &str,
    tcx: &TyCtx,
    term_binders: &[(String, String)],
    hyp_bodies: &[String],
    concl_body: &str,
) -> String {
    let mut binders: Vec<String> = Vec::new();

    // `{α β γ : Type*}` (one group, greek order) when any type variable is used.
    if !tcx.is_empty() {
        let greeks = tcx.greeks_in_order().join(" ");
        binders.push(format!("{{{greeks} : Type*}}"));
    }

    // Term binders, grouping consecutive variables of identical rendered type.
    let mut i = 0;
    while i < term_binders.len() {
        let (_, ref ty) = term_binders[i];
        let mut names = vec![term_binders[i].0.clone()];
        let mut j = i + 1;
        while j < term_binders.len() && &term_binders[j].1 == ty {
            names.push(term_binders[j].0.clone());
            j += 1;
        }
        binders.push(format!("({} : {ty})", names.join(" ")));
        i = j;
    }

    // Hypothesis binders (`h` for a single premise, `h1 h2 …` for several).
    for (k, body) in hyp_bodies.iter().enumerate() {
        let hname = if hyp_bodies.len() == 1 {
            "h".to_string()
        } else {
            format!("h{}", k + 1)
        };
        binders.push(format!("({hname} : {body})"));
    }

    if binders.is_empty() {
        format!("theorem {name} :\n    {concl_body}")
    } else {
        format!("theorem {name} {} :\n    {concl_body}", binders.join(" "))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lean_name_takes_last_component() {
        assert_eq!(lean_name_from_isabelle("List.append_assoc"), "append_assoc");
        assert_eq!(
            lean_name_from_isabelle("Groups.group_add.minus_minus"),
            "minus_minus"
        );
        assert_eq!(lean_name_from_isabelle("bare"), "bare");
    }
}
