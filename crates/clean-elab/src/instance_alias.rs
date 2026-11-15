// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Reducible class ALIASES in instance search — `DecidableEq`, `DecidableLT`,
//! `DecidableLE`, `DecidableRel`, `DecidablePred`, and any user `abbrev` of the
//! same shape.
//!
//! # Lean's rule
//!
//! Lean keys every instance by its type AFTER a reducible ∀-telescope
//! (`Lean/Meta/Instances.lean`, `mkInstanceKey`: `withReducible do
//! forallMetaTelescopeReducing type`, then `DiscrTree.mkPath`), and opens every
//! goal the same way before lookup (`Lean/Meta/SynthInstance.lean`,
//! `getInstances` and `preprocess`). An instance concluding in `DecidableLT α`
//! — `abbrev DecidableLT α := DecidableRel (· < ·)`, i.e.
//! `∀ a b, Decidable (a < b)` — is therefore an instance of `Decidable`, keyed
//! `Decidable (@LT.lt _ _ _ _)`, and it answers `Decidable (x < y)`.
//!
//! # Clean's filing, and what this module adds
//!
//! Clean files an instance under the SYNTACTIC head of its conclusion
//! (`clean-olean`'s `instance_conclusion_class` and the source paths), so
//! Mathlib's `LinearOrder.toDecidableLT` sits in a `DecidableLT` bucket that no
//! `Decidable` goal ever reads (measured on `Mathlib/Order/Basic.lean`:
//! `min_def_lt`, `max_def_lt`, `LinearOrder.lift` fail
//! `failed to synthesize instance Decidable (a < b)` with the instance in
//! scope). Re-filing every import would move ~55 elaborator sites that key on
//! the literal `DecidableEq` bucket, so the filing stays and the resolver reads
//! the alias buckets too (`infer/instance/alias_search.rs`). This module
//! computes, per registered alias class, the class its reducible telescope
//! concludes in and the constant heading each argument of that conclusion —
//! what the resolver needs to skip whole buckets that cannot answer a goal.
//!
//! Everything here is SYNTACTIC (β and δ of reducible definitions only): it
//! decides which candidates the resolver TRIES. Every candidate is still
//! unified against the goal and the emitted term is re-checked by the kernel,
//! so a wrong answer here can cost a resolution, never admit an ill-typed one.

use clean_kernel::expr::{Expr, ExprKind};
use clean_kernel::name::{Name, NameInner};
use clean_kernel::{ConstantKind, Environment, Reducibility};
use std::collections::HashMap;

/// Cap on reducible unfoldings one head normalisation may perform. Lean's
/// aliases nest two deep (`DecidableLT` → `DecidableRel`); the cap only exists
/// so an ill-formed self-referential alias cannot spin.
const MAX_ALIAS_UNFOLD: usize = 16;

/// A registered class that is a reducible alias of another class, as Lean's
/// instance index sees it.
#[derive(Clone, Debug)]
pub(crate) struct ClassAlias {
    /// The alias (`DecidableLT`), under which instances are filed.
    pub(crate) name: Name,
    /// The class its reducible telescope concludes in (`Decidable`).
    pub(crate) final_class: Name,
    /// One entry per argument of the final-class application: the constant
    /// the ALIAS itself puts at the head of that argument (`Eq` for
    /// `DecidableEq`, `LT.lt` for `DecidableLT`), `None` when it depends on
    /// the instance (the `r` of `DecidableRel r`) or on the telescope.
    pub(crate) heads: Vec<Option<Name>>,
}

/// The value of `name` when it is a definition Lean's reducible transparency
/// unfolds: a `Definition` with a body, `Reducibility::Reducible`, and not an
/// inductive type.
fn reducible_value<'e>(env: &'e Environment, name: &Name) -> Option<&'e Expr> {
    let info = env.get_const(name)?;
    if info.kind != ConstantKind::Definition || info.reducibility != Reducibility::Reducible {
        return None;
    }
    if env.get_inductive(name).is_some() {
        return None;
    }
    info.value.as_ref()
}

/// Whether `name` is a definition Lean's reducible transparency unfolds (see
/// [`reducible_value`]).
pub(crate) fn is_reducible_definition(env: &Environment, name: &Name) -> bool {
    reducible_value(env, name).is_some()
}

/// Whether a head constant survives every reduction the elaborator applies to
/// an instance goal: an inductive type (`Eq`, `And`). Nothing else is safe to
/// judge a whole bucket by — Clean normalises a `Sort`-valued argument that
/// feeds an instance-implicit parameter at instance transparency (`elab_app`'s
/// `whnf_instances` step), so `needsDec (a < b)` asks for
/// `Decidable (fooLt a b)`: a projection function (`LT.lt`) or a definition
/// head may already be gone from the goal.
pub(crate) fn is_stable_head(env: &Environment, name: &Name) -> bool {
    env.get_inductive(name).is_some()
}

/// Strip the leading λ-binders of `value`, returning their count and the body.
fn strip_lams(value: &Expr) -> (usize, &Expr) {
    let mut count = 0;
    let mut body = value;
    while let ExprKind::Lam(_, _, inner) = body.kind() {
        count += 1;
        body = inner.as_ref();
    }
    (count, body)
}

/// Contract the β-redexes at the head of an application spine.
fn head_beta(e: &Expr) -> Expr {
    let mut fun = e.get_app_fn().clone();
    if !matches!(fun.kind(), ExprKind::Lam(..)) {
        return e.clone();
    }
    let args: Vec<Expr> = e.get_app_args().into_iter().cloned().collect();
    let mut consumed = 0;
    while consumed < args.len() {
        let ExprKind::Lam(_, _, body) = fun.kind() else {
            break;
        };
        fun = body.instantiate(&args[consumed]);
        consumed += 1;
    }
    Expr::apps(fun, args[consumed..].iter().cloned())
}

/// Whether a reducible body headed by the constant `c` is one Lean's
/// discrimination-tree reduction would expose: an inductive type (`Decidable`,
/// `Eq`) or another reducible definition (`GE.ge` → `LE.le`). A recursor or
/// its auxiliaries (`S.rec`, `S.casesOn`, a matcher) are not — a projection
/// function spelled through them stays at the projection, as Lean's does.
fn exposes_head(env: &Environment, c: &Name) -> bool {
    if env.get_inductive(c).is_some() {
        return true;
    }
    // Read the last COMPONENT structurally: a rendered name cannot tell the
    // component `rec` from a quoted `«A.rec»`.
    let auxiliary = match c.inner() {
        NameInner::Str(_, last) => {
            matches!(
                last.as_ref(),
                "rec" | "recOn" | "casesOn" | "brecOn" | "below"
            ) || last.starts_with("match_")
        }
        NameInner::Anon | NameInner::Num(..) => false,
    };
    !auxiliary && reducible_value(env, c).is_some()
}

/// One reducible δ-step at the head of `e`: `D a₁ … aₙ` with `D` a reducible
/// definition whose body (under its λs) is a ∀-telescope, or an application
/// whose head [`exposes_head`], becomes that body instantiated with the
/// arguments. A body headed by anything else — a projection (`LE.le`'s
/// `self.1`), a bound variable, a recursor — is left alone.
fn unfold_head_once(env: &Environment, e: &Expr) -> Option<Expr> {
    let ExprKind::Const(head, _) = e.get_app_fn().kind() else {
        return None;
    };
    let value = reducible_value(env, head)?;
    let (arity, body) = strip_lams(value);
    let unfoldable = match body.get_app_fn().kind() {
        ExprKind::Pi(..) => true,
        ExprKind::Const(c, _) => exposes_head(env, c),
        _ => false,
    };
    if !unfoldable {
        return None;
    }
    let args: Vec<Expr> = e.get_app_args().into_iter().cloned().collect();
    if args.len() < arity {
        return None;
    }
    // `instantiate_rev` substitutes BVar(0) with the LAST λ's argument.
    let rev: Vec<Expr> = args[..arity].iter().rev().cloned().collect();
    let unfolded = body.instantiate_rev(&rev);
    Some(Expr::apps(unfolded, args[arity..].iter().cloned()))
}

/// Head-β plus reducible δ at the head, to a fixpoint (bounded).
fn reducible_head_normalize(env: &Environment, e: &Expr) -> Expr {
    let mut cur = head_beta(e);
    for _ in 0..MAX_ALIAS_UNFOLD {
        match unfold_head_once(env, &cur) {
            Some(next) => cur = head_beta(&next),
            None => break,
        }
    }
    cur
}

/// The conclusion of `ty` after peeling every ∀-binder and unfolding every
/// reducible alias at its head — a syntactic `forallTelescopeReducing` at
/// reducible transparency. The conclusion keeps loose bound variables for the
/// peeled binders; only its heads are read.
fn reducible_conclusion(env: &Environment, ty: &Expr) -> Expr {
    let mut cur = ty.clone();
    for _ in 0..MAX_ALIAS_UNFOLD {
        while let ExprKind::Pi(_, _, body) = cur.kind() {
            let next = body.as_ref().clone();
            cur = next;
        }
        match unfold_head_once(env, &cur) {
            Some(next) => cur = head_beta(&next),
            None => break,
        }
    }
    cur
}

/// The constant heading one argument of an alias's unfolded conclusion, under
/// any λ-binders of its own.
fn alias_arg_head(env: &Environment, arg: &Expr) -> Option<Name> {
    let arg = reducible_head_normalize(env, arg);
    let mut body = &arg;
    while let ExprKind::Lam(_, _, inner) = body.kind() {
        body = inner.as_ref();
    }
    match body.get_app_fn().kind() {
        ExprKind::Const(name, _) => Some(name.clone()),
        _ => None,
    }
}

/// The alias view of the registered class `name`, when it is a reducible
/// definition whose telescope concludes in a DIFFERENT registered class.
pub(crate) fn class_alias(
    env: &Environment,
    name: &Name,
    is_class: impl Fn(&Name) -> bool,
) -> Option<ClassAlias> {
    let value = reducible_value(env, name)?;
    let (_, body) = strip_lams(value);
    let conclusion = reducible_conclusion(env, body);
    let (final_class, args) = crate::instances::extract_class_app(&conclusion)?;
    if final_class == *name || !is_class(&final_class) {
        return None;
    }
    let heads = args.iter().map(|arg| alias_arg_head(env, arg)).collect();
    Some(ClassAlias {
        name: name.clone(),
        final_class,
        heads,
    })
}

/// The parameter count of `name` when it is a reducible alias whose telescope
/// concludes in a class `env` has registered — the check Lean's `addInstance`
/// makes on an instance's conclusion (`getClassName`: `isClass?` through a
/// reducible telescope), so an instance concluding in `DecidableLT α` is
/// accepted where a plain structure is refused.
pub(crate) fn alias_class_arity(env: &Environment, name: &Name) -> Option<usize> {
    class_alias(env, name, |n| env.get_class_info(n).is_some())?;
    let mut ty = &env.get_const(name)?.type_;
    let mut arity = 0;
    while let ExprKind::Pi(_, _, body) = ty.kind() {
        arity += 1;
        ty = body.as_ref();
    }
    Some(arity)
}

/// Register the reducible alias `name` as a class, so the instance about to be
/// filed under it is loaded into every later declaration's instance table —
/// the same step `clean-olean` takes for an imported instance whose
/// conclusion head is not yet a class (`register_instances_from_extension`).
/// A registered class is left alone; anything that is not a reducible alias of
/// one is refused (`false`).
pub(crate) fn register_alias_class(env: &mut Environment, name: &Name) -> bool {
    if env.get_class_info(name).is_some() {
        return true;
    }
    let Some(num_params) = alias_class_arity(env, name) else {
        return false;
    };
    env.register_class(clean_kernel::KernelClassInfo {
        name: name.clone(),
        num_params,
        out_params: Vec::new(),
        semi_out_params: Vec::new(),
    });
    true
}

/// Every registered alias class among `class_names`, grouped by the final
/// class it concludes in.
pub(crate) fn class_aliases_by_final<'n>(
    env: &Environment,
    class_names: impl IntoIterator<Item = &'n Name>,
    is_class: impl Fn(&Name) -> bool,
) -> HashMap<Name, Vec<ClassAlias>> {
    let mut by_final: HashMap<Name, Vec<ClassAlias>> = HashMap::new();
    for name in class_names {
        if let Some(alias) = class_alias(env, name, &is_class) {
            by_final
                .entry(alias.final_class.clone())
                .or_default()
                .push(alias);
        }
    }
    by_final
}
