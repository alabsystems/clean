// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! A GLOBAL simp theorem whose statement is neither `=` nor `↔`.
//!
//! # Lean's rule
//!
//! `mkSimpTheoremFromConst` runs every theorem through `preprocess`
//! (`Lean/Meta/Tactic/Simp/SimpTheorems.lean:288-363`) unless its conclusion
//! is already an equation, and `preprocess` turns the conclusion — under its
//! `∀` binders — into rewrite rules:
//!
//! * `a = b` stays as it is and `a ↔ b` becomes `propext h : a = b`;
//! * `a ≠ b` becomes `(a = b) = False` (`eq_false`), and `¬p` becomes
//!   `p = False`, except that `b ≠ true` / `¬(b = true)` become `b = false`
//!   (`Bool.of_not_eq_true`) and the `false` twins become `b = true`;
//! * `p ∧ q` is split into the rules of `p` and of `q` (`h.1`, `h.2`);
//! * any other proposition `p` becomes `p = True` (`eq_true`).
//!
//! # What Clean did instead
//!
//! Only `=` and `↔` conclusions were ever collected (`collect_extra_lemmas`,
//! `collect_registry_lemmas`); everything else fell through to the
//! delta-unfold path, which serves definitions only, so it was silently
//! dropped. `simp [cast_heq]` could not rewrite `HEq (cast h a) a`,
//! `simp only [Decidable.em]` could not rewrite `p ∨ ¬p`, and
//! `simp only [exists_apply_eq_apply]` could not close `∃ a', f a' = f a`.
//! Measured 2026-09-12 on `Mathlib/Logic/Basic.lean` (`heq_of_eq_cast`,
//! `Decidable.and_forall_ne`) and `Mathlib/Logic/Function/Basic.lean`
//! (`Function.FactorsThrough.extend_apply`). LOCAL hypotheses already got the
//! same treatment (`lemmas::local_prop_hyp_lemma`); this is its global twin,
//! built from the same prelude constants (`propext`, `Iff.intro`,
//! `True.intro`, `False.elim`) because `eq_true`/`eq_false` exist only after
//! `import Init`.
//!
//! # Soundness
//!
//! Every rule carries a proof TEMPLATE over the theorem's own binders — the
//! theorem applied to them, wrapped by `propext`/`Iff.intro`/`And.left`/
//! `And.right`/`Bool.of_not_eq_*` — and goes through the simp matcher's
//! template branch like an `↔` rule: its universe parameters are renamed
//! fresh per use, every binder it mentions must be bound, the assembled term
//! is checked against the rewrite by `proof_matches_rewrite`, and the kernel
//! re-checks the finished proof. Nothing here is trusted.

use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprKind, Level};

use super::lemmas::{mk_local_proof_template, prop_false_proof, prop_true_proof};
use super::types::{SimpIndexMode, SimpLemma};
use crate::tactic::core::ProofState;

/// The rewrite rules Lean's `preprocess` makes of a global theorem whose
/// conclusion is neither `=` nor `↔`, or none.
///
/// Empty when the constant's type is not a proposition, or when there is no
/// goal to type-check it in. That test is the WHOLE of Lean's rule
/// (`addDeclToUnfoldOrTheorem`, `Lean/Elab/Tactic/Simp.lean`: `if (← isProp
/// info.type) then thms.addConst … else` unfold): what decides between
/// "theorem" and "definition to unfold" is the TYPE, never the kind of
/// constant. A constructor of an inductive proposition (`List.Pairwise.nil`,
/// `Nat.le.refl`), a proposition-valued structure or class field
/// (`Std.Refl.refl`) and a `def` whose type is a proposition are all simp
/// theorems; refusing every `Definition`-kind constant here dropped them
/// (measured 2026-09-20 against the pinned v4.30.0-rc2 binary, which
/// rewrites with each). A definition of any OTHER type (`def Even (n : Nat) :
/// Prop` has type `Nat → Prop`, which is not a proposition) still yields
/// nothing here and stays on the unfold path (`resolve_unfold_defs`).
///
/// Two refusals Lean does not make, both fail-closed: a rule whose left-hand
/// side would be a bare pattern variable (it would match every subterm, and
/// Clean's candidate index has no star bucket for it) and a conclusion that is
/// literally `True` (a `True = True` rule rewrites nothing).
pub(super) fn mk_prop_simp_lemmas(
    state: &ProofState,
    name: &Name,
    priority: u32,
) -> Vec<SimpLemma> {
    let Some(info) = state.env.get_const(name) else {
        return Vec::new();
    };
    let Some(goal) = state.current_goal() else {
        return Vec::new();
    };
    // Lean's `checkTypeIsProp`: only a proof of a proposition is a theorem.
    let is_prop = state
        .infer_type(goal, &info.type_)
        .is_ok_and(|sort| state.is_def_eq(goal, &sort, &Expr::prop()));
    if !is_prop {
        return Vec::new();
    }
    let mut binder_count = 0u32;
    let mut body = &info.type_;
    while let ExprKind::Pi(_, _, codomain) = body.kind() {
        binder_count += 1;
        body = codomain;
    }
    let levels: Vec<Level> = info
        .level_params
        .iter()
        .cloned()
        .map(Level::param)
        .collect();
    let h = mk_local_proof_template(Expr::const_(name.clone(), levels), binder_count);
    let mut out = Vec::new();
    preprocess(state, name, body, h, priority, &mut out);
    out
}

/// One step of Lean's `preprocess.go` on a conclusion `ty` proved by `h`.
///
/// `h` is the proof over the rule's binders: a constant applied to them for
/// a global theorem, a hypothesis's free variable applied to them for a local
/// one (`lemmas::local_prop_hyp_lemma`, which splits a conjunction through
/// here).
pub(super) fn preprocess(
    state: &ProofState,
    name: &Name,
    ty: &Expr,
    h: Expr,
    priority: u32,
    out: &mut Vec<SimpLemma>,
) {
    let head = match ty.get_app_fn().kind() {
        ExprKind::Const(n, levels) => Some((n.to_string(), levels.clone())),
        _ => None,
    };
    let args = ty.get_app_args();
    let rule = |lhs: Expr, rhs: Expr, eq_type: Expr, proof: Expr| SimpLemma {
        name: name.clone(),
        lhs,
        rhs,
        eq_type: Some(eq_type),
        proof_expr: Some(proof),
        index_mode: SimpIndexMode::Normal,
        priority,
    };
    let true_ = Expr::const_(Name::from_string("True"), vec![]);
    let false_ = Expr::const_(Name::from_string("False"), vec![]);
    let mut push = |lemma: SimpLemma| {
        if !matches!(lemma.lhs.kind(), ExprKind::BVar(_)) {
            out.push(lemma);
        }
    };
    match head.as_ref().map(|(n, levels)| (n.as_str(), levels)) {
        Some(("Eq", _)) if args.len() == 3 => {
            push(rule(args[1].clone(), args[2].clone(), args[0].clone(), h));
        }
        Some(("Iff", _)) if args.len() == 2 => {
            let (a, b) = (args[0].clone(), args[1].clone());
            let proof = Expr::apps(
                Expr::const_(Name::from_string("propext"), vec![]),
                [a.clone(), b.clone(), h],
            );
            push(rule(a, b, Expr::prop(), proof));
        }
        Some(("Ne", levels)) if args.len() == 3 => {
            let eq = Expr::apps(
                Expr::const_(Name::from_string("Eq"), levels.to_vec()),
                [args[0].clone(), args[1].clone(), args[2].clone()],
            );
            if let Some(lemma) = bool_not_eq_rule(state, &eq, &h, &rule) {
                push(lemma);
            } else {
                let proof = prop_false_proof(&eq, &h);
                push(rule(eq, false_, Expr::prop(), proof));
            }
        }
        Some(("Not", _)) if args.len() == 1 => {
            let p = args[0].clone();
            if let Some(lemma) = bool_not_eq_rule(state, &p, &h, &rule) {
                push(lemma);
            } else {
                let proof = prop_false_proof(&p, &h);
                push(rule(p, false_, Expr::prop(), proof));
            }
        }
        Some(("And", _)) if args.len() == 2 => {
            let (p, q) = (args[0].clone(), args[1].clone());
            let (left, right) = (
                Name::from_string("And.left"),
                Name::from_string("And.right"),
            );
            if state.env.get_const(&left).is_none() || state.env.get_const(&right).is_none() {
                return;
            }
            let hp = Expr::apps(
                Expr::const_(left, vec![]),
                [p.clone(), q.clone(), h.clone()],
            );
            let hq = Expr::apps(Expr::const_(right, vec![]), [p.clone(), q.clone(), h]);
            preprocess(state, name, &p, hp, priority, out);
            preprocess(state, name, &q, hq, priority, out);
        }
        Some(("True", _)) if args.is_empty() => {}
        _ => {
            let proof = prop_true_proof(ty, &h);
            push(rule(ty.clone(), true_, Expr::prop(), proof));
        }
    }
}

/// Lean's `Bool` special case for `¬(b = true)` / `¬(b = false)` (and the
/// `≠` spellings): the rule is `b = false` / `b = true`, proved by
/// `Bool.of_not_eq_true` / `Bool.of_not_eq_false`. `None` when `eq` is not
/// such an equation, or the lemma it needs is not in the environment (the
/// generic `(b = true) = False` rule is then used, which is sound but is not
/// the normal form Lean reaches).
///
/// The literal is recognised under BOTH of its spellings ([`bool_literal`]),
/// and the rule's right-hand side answers in the spelling the statement used,
/// so rewriting `fb k = false` leaves the closed `false = false` Lean leaves.
/// Matching the constructor's name alone made this rule unreachable for every
/// source-elaborated statement over the builtin prelude, where a written
/// `true` is the alias (measured 2026-09-20: `simp only [bne_t]` with
/// `bne_t : fb n ≠ true` made no progress on `fb k = false`, which pinned
/// Lean closes — the generic `(fb n = true) = False` rule was built instead).
fn bool_not_eq_rule(
    state: &ProofState,
    eq: &Expr,
    h: &Expr,
    rule: &impl Fn(Expr, Expr, Expr, Expr) -> SimpLemma,
) -> Option<SimpLemma> {
    let ExprKind::Const(eq_name, _) = eq.get_app_fn().kind() else {
        return None;
    };
    let args = eq.get_app_args();
    if eq_name.to_string() != "Eq" || args.len() != 3 {
        return None;
    }
    let (ty, lhs, rhs) = (args[0], args[1], args[2]);
    let literal = bool_literal(state, rhs)?;
    let lemma = Name::from_string(if literal.value {
        "Bool.of_not_eq_true"
    } else {
        "Bool.of_not_eq_false"
    });
    state.env.get_const(&lemma)?;
    let proof = Expr::apps(Expr::const_(lemma, vec![]), [lhs.clone(), h.clone()]);
    Some(rule(lhs.clone(), literal.negated(state), ty.clone(), proof))
}

/// A `Bool` literal as a statement spells it.
struct BoolLiteral {
    /// Which literal it is.
    value: bool,
    /// Whether it is spelled by the builtin prelude's alias (`true`) rather
    /// than the constructor (`Bool.true`).
    alias: bool,
}

impl BoolLiteral {
    /// The OTHER literal, in the same spelling when the environment has it.
    fn negated(&self, state: &ProofState) -> Expr {
        let ctor = Expr::const_(bool_ctor_name(!self.value), vec![]);
        if !self.alias {
            return ctor;
        }
        let alias = Expr::const_(bool_alias_name(!self.value), vec![]);
        if bool_literal(state, &alias).is_some() {
            alias
        } else {
            ctor
        }
    }
}

fn bool_ctor_name(value: bool) -> Name {
    Name::from_string(if value { "Bool.true" } else { "Bool.false" })
}

/// The builtin prelude's alias for a `Bool` literal (`true := Bool.true`).
fn bool_alias_name(value: bool) -> Name {
    Name::from_string(if value { "true" } else { "false" })
}

/// Which `Bool` literal `e` is, or `None`.
///
/// Lean's test is `rhs.isConstOf ``Bool.true`, and in Lean a written `true`
/// IS that constructor (`export Bool (true false)`). Clean's builtin prelude
/// instead registers `true` / `false` as reducible definitions whose VALUE is
/// the constructor, and source elaboration resolves the written literal to
/// them, so exactly those two aliases are accepted too — and only when the
/// environment really defines the name as the matching constructor. Any
/// other reducible abbreviation of a literal keeps the generic rule, as it
/// does in Lean.
fn bool_literal(state: &ProofState, e: &Expr) -> Option<BoolLiteral> {
    let ExprKind::Const(name, levels) = e.kind() else {
        return None;
    };
    if !levels.is_empty() {
        return None;
    }
    let as_ctor = |n: &Name| {
        [true, false]
            .into_iter()
            .find(|value| *n == bool_ctor_name(*value))
    };
    if let Some(value) = as_ctor(name) {
        return Some(BoolLiteral {
            value,
            alias: false,
        });
    }
    let value = [true, false]
        .into_iter()
        .find(|value| *name == bool_alias_name(*value))?;
    let info = state.env.get_const(name)?;
    if !info.is_reducible || !info.level_params.is_empty() {
        return None;
    }
    let ExprKind::Const(target, target_levels) = info.value.as_ref()?.kind() else {
        return None;
    };
    (target_levels.is_empty() && *target == bool_ctor_name(value))
        .then_some(BoolLiteral { value, alias: true })
}
