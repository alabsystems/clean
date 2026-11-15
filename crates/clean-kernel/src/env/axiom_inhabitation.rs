// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! An INHABITATION WITNESS for a value-less axiom whose type is data.
//!
//! # Why the prelude census needs this
//!
//! `tests_prelude_axiom_ratchet.rs` splits the non-foundational axioms of the
//! default `clean check` environment by the SORT of their declared type: a
//! `Prop`-typed axiom asserts a proposition (`debt_proposition`), a data-typed
//! one was called an "uninterpreted symbol" that "asserts no proposition"
//! (`debt_signature`). The second half of that reading is FALSE in general.
//! A data-typed axiom asserts that its type is INHABITED, and a type such as
//!
//! ```text
//! Pure.pure : {m : Type u → Type v} → {α : Type u} → α → m α
//! ```
//!
//! is inhabited in no model at all: at `m := fun _ => Empty` it produces an
//! `Empty` from a `Nat`, and `Empty.rec` turns that into a proof of `False`
//! (`docs/issues/2026-09-28-prelude-pure-proves-false.md`). The SORT of the
//! type (`Type (max (u+1) v)`) says nothing about that.
//!
//! # The criterion, and the model that makes it sound
//!
//! [`inhabitation_witness`] accepts an axiom type only when it can name a
//! reason the type is inhabited in ONE fixed model of the whole environment:
//!
//! * every uninterpreted type former (an `Axiom` whose type's conclusion is a
//!   `Sort`, the builtin quotient primitives excepted) is interpreted as the
//!   constant `PUnit` family (`True` at `Prop`);
//! * every other axiom must then be inhabited under that interpretation.
//!
//! The type is peeled to its conclusion under `whnf` (so a definition such as
//! `StateT σ m α := σ → m (α × σ)` is looked through, not trusted by its head),
//! every binder becoming a hypothesis, and the conclusion must be one of:
//!
//! 1. a `Sort` — the axiom is itself a type former ([`Witness::TypeFormer`]);
//! 2. definitionally the type of one of the hypotheses — inhabited by that
//!    hypothesis ([`Witness::Hypothesis`]);
//! 3. headed by an uninterpreted type former — `PUnit` in the model
//!    ([`Witness::OpaqueCarrier`]);
//! 4. an index-free inductive with a non-recursive, non-dependent constructor
//!    each of whose fields is itself witnessed ([`Witness::Constructor`]).
//!
//! Because every accepted axiom is inhabited in the SAME model, the accepted
//! set is jointly consistent with the foundational axioms — which a
//! per-axiom reading could not promise: `OptionT.fail : OptionT m α` and
//! `OptionT.run : OptionT m α → m (Option α)` are each satisfiable alone and
//! prove `False` together; here the second is refused (its conclusion is
//! headed by the bound `m`), which is exactly what breaks the pair.
//!
//! The criterion is CONSERVATIVE: it refuses types that are inhabited for a
//! reason it does not model (`ExceptT.run` over an OPAQUE `ExceptT` is one),
//! and a refusal means "no witness", never "proves `False`". It is decidable:
//! a finite peel, a finite hypothesis scan and a depth-bounded constructor
//! search.

use crate::env::types::ConstantKind;
use crate::env::Environment;
use crate::expr::{Expr, ExprKind};
use crate::name::Name;
use crate::tc::{LocalContext, TypeChecker};

/// How deep the constructor search may recurse into field types.
const MAX_CONSTRUCTOR_DEPTH: usize = 4;

/// Why an axiom's type is inhabited in the census model.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Witness {
    /// The conclusion is a `Sort`: the axiom is a type former or a
    /// proposition symbol, inhabited by `PUnit` / `True`.
    TypeFormer,
    /// The conclusion is definitionally the type of hypothesis `index` of the
    /// axiom's own telescope (0 = outermost binder).
    Hypothesis(usize),
    /// The conclusion is headed by this uninterpreted type former, which the
    /// census model interprets as the constant `PUnit` family.
    OpaqueCarrier(Name),
    /// The conclusion is an inductive type built by this constructor, every
    /// field of which is itself witnessed.
    Constructor(Name),
}

/// Why no witness was found.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum NoWitness {
    /// The conclusion is headed by a variable bound in the axiom's own
    /// telescope — the `Pure.pure` shape. Instantiating that variable with an
    /// empty family makes the axiom produce an inhabitant of an empty type.
    BoundFamilyHead {
        /// The conclusion, rendered.
        conclusion: String,
    },
    /// Any other conclusion the criterion does not model.
    Unmodelled {
        /// The conclusion, rendered.
        conclusion: String,
        /// Which rule declined it.
        reason: &'static str,
    },
}

/// A witness that `ty` (an axiom's declared type) is inhabited in the census
/// model described in the module doc, or the reason none was found.
pub(crate) fn inhabitation_witness(env: &Environment, ty: &Expr) -> Result<Witness, NoWitness> {
    let mut ctx = LocalContext::new();
    let mut hyps: Vec<Expr> = Vec::new();
    witness_in(env, &mut ctx, &mut hyps, ty, 0)
}

/// `true` iff `name` is an uninterpreted type former: an `Axiom` whose type's
/// conclusion is a `Sort`, and not one of the builtin quotient primitives
/// (whose computation rule `Quot.lift f h (Quot.mk r a) ≡ f a` the `PUnit`
/// interpretation would not respect).
pub(crate) fn is_uninterpreted_type_former(env: &Environment, name: &Name) -> bool {
    let Some(info) = env.get_const(name) else {
        return false;
    };
    if info.kind != ConstantKind::Axiom || is_quotient_primitive(name) {
        return false;
    }
    let ty = info.type_.clone();
    matches!(inhabitation_witness_type_former_only(env, &ty), Some(true))
}

fn is_quotient_primitive(name: &Name) -> bool {
    matches!(
        name.to_string().as_str(),
        "Quot" | "Quot.mk" | "Quot.lift" | "Quot.ind"
    )
}

/// `Some(true)` iff `ty` peels (under `whnf`) to a `Sort`.
fn inhabitation_witness_type_former_only(env: &Environment, ty: &Expr) -> Option<bool> {
    let mut ctx = LocalContext::new();
    let mut cur = ty.clone();
    for _ in 0..256 {
        let tc = TypeChecker::with_context(env, ctx.clone());
        let w = tc.whnf(&cur);
        match &w.kind {
            ExprKind::Pi(bd, dom, body) => {
                let id = ctx.push(Name::from_string("x"), (**dom).clone(), *bd);
                cur = body.instantiate(&Expr::fvar(id));
            }
            ExprKind::Sort(_) => return Some(true),
            _ => return Some(false),
        }
    }
    None
}

fn witness_in(
    env: &Environment,
    ctx: &mut LocalContext,
    hyps: &mut Vec<Expr>,
    ty: &Expr,
    depth: usize,
) -> Result<Witness, NoWitness> {
    // Peel the telescope under whnf, every binder becoming a hypothesis.
    let mut cur = ty.clone();
    let concl = loop {
        let tc = TypeChecker::with_context(env, ctx.clone());
        let w = tc.whnf(&cur);
        if let ExprKind::Pi(bd, dom, body) = &w.kind {
            let id = ctx.push(Name::from_string("h"), (**dom).clone(), *bd);
            hyps.push((**dom).clone());
            cur = body.instantiate(&Expr::fvar(id));
            if hyps.len() > 256 {
                return Err(NoWitness::Unmodelled {
                    conclusion: String::new(),
                    reason: "telescope longer than 256 binders",
                });
            }
            continue;
        }
        break w;
    };

    if matches!(concl.kind, ExprKind::Sort(_)) {
        return Ok(Witness::TypeFormer);
    }

    let tc = TypeChecker::with_context(env, ctx.clone());
    if let Some(i) = hyps.iter().position(|h| tc.is_def_eq(h, &concl)) {
        return Ok(Witness::Hypothesis(i));
    }

    let head = concl.get_app_fn();
    match &head.kind {
        ExprKind::FVar(_) => Err(NoWitness::BoundFamilyHead {
            conclusion: concl.to_string(),
        }),
        ExprKind::Const(name, levels) => {
            if is_uninterpreted_type_former(env, name) {
                return Ok(Witness::OpaqueCarrier(name.clone()));
            }
            if depth < MAX_CONSTRUCTOR_DEPTH {
                if let Some(w) = constructor_witness(env, ctx, hyps, &concl, name, levels, depth) {
                    return Ok(w);
                }
            }
            Err(NoWitness::Unmodelled {
                conclusion: concl.to_string(),
                reason: "constant head is neither an uninterpreted type former nor an \
                         inductive with a witnessed constructor",
            })
        }
        _ => Err(NoWitness::Unmodelled {
            conclusion: concl.to_string(),
            reason: "conclusion head is neither a constant nor a bound variable",
        }),
    }
}

/// A constructor of the index-free inductive `ind` whose instantiated fields
/// are non-recursive, non-dependent and each witnessed in the current context.
fn constructor_witness(
    env: &Environment,
    ctx: &mut LocalContext,
    hyps: &[Expr],
    concl: &Expr,
    ind: &Name,
    levels: &[crate::level::Level],
    depth: usize,
) -> Option<Witness> {
    let ind_val = env.get_inductive(ind)?.clone();
    if ind_val.num_indices != 0 {
        return None;
    }
    let args: Vec<Expr> = concl.get_app_args().into_iter().cloned().collect();
    let n_params = usize::try_from(ind_val.num_params).ok()?;
    if args.len() != n_params {
        return None;
    }
    'ctors: for ctor_name in &ind_val.constructor_names {
        let ctor = env.get_constructor(ctor_name)?.clone();
        let mut t = ctor
            .type_
            .instantiate_level_params_direct(&ctor.level_params, levels);
        for a in &args {
            match &t.kind {
                ExprKind::Pi(_, _, body) => t = body.instantiate(a),
                _ => continue 'ctors,
            }
        }
        // Fields: each must be non-dependent, non-recursive, and witnessed.
        while let ExprKind::Pi(_, dom, body) = &t.kind {
            if body.has_loose_bvar(0) || mentions_const(dom, ind) {
                continue 'ctors;
            }
            let mut sub_ctx = ctx.clone();
            let mut sub_hyps = hyps.to_vec();
            if witness_in(env, &mut sub_ctx, &mut sub_hyps, dom, depth + 1).is_err() {
                continue 'ctors;
            }
            // Non-dependent: the body does not mention the field.
            t = body.instantiate(&Expr::sort(crate::level::Level::zero()));
        }
        return Some(Witness::Constructor(ctor_name.clone()));
    }
    None
}

fn mentions_const(e: &Expr, name: &Name) -> bool {
    e.collect_constants().contains(name)
}
