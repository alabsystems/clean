// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared heterogeneous-operator typeclass-projection peeling.
//!
//! A surface expression `a ⊕ b` desugars to
//! `@H⊕.h⊕ {u v w} α β γ inst a b`, where `H⊕.h⊕` is a *reducible* projection
//! that unfolds (through the instance) to the underlying operation `op` (e.g.
//! `Nat.mul`). Library/builtin rewrite lemmas, by contrast, are stated over the
//! bare op head (`Nat.mul ?n 0`). To make a bare-head lemma match a
//! projection-headed goal subterm, both `rw` (see `equality/rewrite.rs`) and
//! `simp` (its discrimination-tree key paths and its matcher) need to peel
//! *exactly* the projection layer to expose the bare op head — WITHOUT running a
//! full `whnf` that would δ-unfold the op const itself and ι-reduce the operands
//! (`Nat.mul n 0 → Nat.zero`), erasing the very `Nat.mul` head the lemma is
//! keyed on. This module is the single shared implementation of that peel,
//! consumed by both surfaces so the lemma LHS and the goal subterm land on the
//! same head key.

use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprKind};

use super::{Goal, ProofState};

/// Names of the heterogeneous binary-operator typeclass *projection* functions
/// (`HAdd.hAdd`, `HMul.hMul`, …). A goal written `a ⊕ b` desugars to
/// `@H⊕.h⊕ {…} {α β γ} inst a b`, where the projection is a reducible
/// definition unfolding to `α.proj0 inst`. Each of these takes its two operands
/// as the *trailing* two arguments after the implicit type/instance arguments,
/// which lets [`reduce_op_projection_head`] peel exactly the projection layer
/// without touching the operands.
///
/// Kept in sync with the hetero-op flavors in
/// `clean-kernel/src/env/algebra_hetero.rs`. All are binary (2 operands).
pub(crate) const HETERO_OP_PROJECTIONS: &[&str] = &[
    "HAdd.hAdd",
    "HSub.hSub",
    "HMul.hMul",
    "HDiv.hDiv",
    "HMod.hMod",
    "HPow.hPow",
    "HAnd.hAnd",
    "HOr.hOr",
    "HXor.hXor",
    "HShiftLeft.hShiftLeft",
    "HShiftRight.hShiftRight",
    "HAppend.hAppend",
];

/// Whether `name` is one of the heterogeneous binary-op projection functions
/// (see [`HETERO_OP_PROJECTIONS`]).
pub(crate) fn is_hetero_op_projection(name: &Name) -> bool {
    let s = name.to_string();
    HETERO_OP_PROJECTIONS.iter().any(|p| *p == s)
}

/// Given a hetero-op projection name (`HAdd.hAdd`), return the owning class name
/// (`HAdd`) so the constructor `HAdd.mk` can be checked. Returns `None` for a
/// non-projection name.
pub(crate) fn hetero_class_of_projection(name: &Name) -> Option<String> {
    let s = name.to_string();
    HETERO_OP_PROJECTIONS
        .iter()
        .find(|p| **p == s)
        .and_then(|p| p.split_once('.').map(|(class, _)| class.to_string()))
}

/// Reduce exactly the typeclass-projection layer of an op-headed subterm,
/// exposing the underlying operation head WITHOUT reducing the operands.
///
/// Given `haystack = @H⊕.h⊕ {u v w} α β γ inst a b` (head a registered hetero-op
/// projection per [`is_hetero_op_projection`]), this:
///   1. splits off the two trailing operand arguments `a`, `b`;
///   2. extracts the *underlying operation* `op` (`Nat.add`) from the instance
///      argument — the field-0 payload of the `H⊕.mk … op` constructor. The
///      instance is WHNF-reduced ONLY far enough to expose that constructor
///      (so an instance written as the reducible alias `instHAddNat` unfolds to
///      `HAdd.mk … Nat.add`); the stored op field is never *applied*, so this
///      can never trigger the `Nat.add _ 0 → _` ι base-case that full WHNF of
///      the whole subterm would;
///   3. re-applies `a b` to `op`, yielding `op a b` (`Nat.add a b`).
///
/// Crucially this does NOT call `state.whnf` on the whole head application:
/// that δ-unfolds the *reducible* op const itself (`Nat.mul` → its `Nat.rec`
/// body lambda) and ι-reduces the operands (`Nat.mul n 0 → Nat.zero`), losing
/// the `Nat.mul`/`Nat.add` head the pattern/key is keyed on. Pulling the op
/// straight out of the instance constructor keeps the surface op const intact.
///
/// Returns `None` when the head is not an applied hetero-op projection, when it
/// has fewer than two operand arguments, or when the instance does not reduce to
/// a structure constructor whose field-0 payload is the op (e.g. an instance
/// metavariable). The result is the surface `op a b` form to key/match against;
/// any downstream rewrite proof remains kernel-checked, so this only affects
/// *which* form is selected, never soundness.
pub(crate) fn reduce_op_projection_head(
    state: &ProofState,
    goal: &Goal,
    haystack: &Expr,
) -> Option<Expr> {
    let hay_fn = haystack.get_app_fn();
    let ExprKind::Const(hay_name, _) = hay_fn.kind() else {
        return None;
    };
    if !is_hetero_op_projection(hay_name) {
        return None;
    }
    let args: Vec<Expr> = haystack.get_app_args().into_iter().cloned().collect();
    // Binary op: the last two args are the operands; everything before is the
    // implicit type/level/instance prefix that carries the projection.
    if args.len() < 2 {
        return None;
    }
    let split = args.len() - 2;
    let (prefix_args, operands) = args.split_at(split);

    // The instance argument is the LAST prefix arg (`H⊕.hH⊕ {…} α β γ inst`).
    let inst = prefix_args.last()?;

    // Reduce the instance ONLY enough to expose its `H⊕.mk …` constructor.
    // WHNF-ing the *instance term itself* (not the projection application) is
    // safe: the op is a stored field, not applied, so no operator ι-redex fires.
    let inst_whnf = state.whnf(goal, inst);
    let inst_fn = inst_whnf.get_app_fn();
    let ExprKind::Const(inst_ctor, _) = inst_fn.kind() else {
        return None;
    };
    // The constructor must be the matching `H⊕.mk`. Its field-0 payload (the op)
    // is its LAST argument: `H⊕.mk {L} α β γ op`.
    let expected_ctor = format!("{}.mk", hetero_class_of_projection(hay_name)?);
    if inst_ctor.to_string() != expected_ctor {
        return None;
    }
    let inst_args = inst_whnf.get_app_args();
    let op: Expr = (*inst_args.last()?).clone();

    // Re-apply the operands to the op: `op a b`.
    let mut result = op;
    for operand in operands {
        result = Expr::app(result, operand.clone());
    }
    // Lean's own instances do NOT store a bare op const in the field. They store
    // an ETA-EXPANDED LAMBDA over a SECOND (homogeneous) class projection:
    //
    //   instance [Append α] : HAppend α α α where hAppend a b := Append.append a b
    //   instance : Append (List α) := ⟨List.append⟩
    //
    // so the field of `instHAppendOfAppend` is `fun a b => @Append.append α inst a b`
    // and re-applying the operands yields a BETA-REDEX whose head is a `Lam`, not
    // the `List.append` const the lemma is keyed on. Clean's own *fused* prelude
    // instances (`instHAppendListList = HAppend.mk … List.append`) collapse both
    // layers into one, which is why the single-layer peel above was enough for
    // them and silently gave up on every genuine Lean instance after `import Init`.
    // Normalize the two structural differences — head-beta, then any remaining
    // structure-projection layers — so BOTH encodings land on the same bare op
    // head. See `docs/plans/CLASS_PROJECTION_SURFACE_2026-07-29.md`.
    Some(reduce_projection_layers(state, goal, head_beta(&result)))
}

/// Head-beta-reduce `expr`: apply the spine arguments to a `Lam` head for as long
/// as both are available. Only the *head* redex is contracted — arguments are
/// never entered, so no operand is reduced (the invariant
/// [`reduce_op_projection_head`] depends on).
fn head_beta(expr: &Expr) -> Expr {
    let args: Vec<Expr> = expr.get_app_args().into_iter().cloned().collect();
    let mut fun = expr.get_app_fn().clone();
    let mut consumed = 0usize;
    while consumed < args.len() {
        let next = match fun.kind() {
            ExprKind::Lam(_, _, body) => body.instantiate(&args[consumed]),
            _ => break,
        };
        fun = next;
        consumed += 1;
    }
    let mut result = fun;
    for arg in &args[consumed..] {
        result = Expr::app(result, arg.clone());
    }
    result
}

/// Maximum structure-projection layers peeled by [`reduce_projection_layers`].
/// Lean's deepest core stack is three (`HPow.hPow → Pow.pow → NatPow.pow`); the
/// cap only exists so a pathological cyclic-looking environment cannot spin.
const MAX_PROJECTION_LAYERS: usize = 8;

/// Repeatedly peel *structure-projection* layers off `expr`'s head, head-beta
/// reducing between layers, until the head is no longer a projection function.
///
/// Returns the most-reduced form reached (`expr` itself when no layer applies),
/// so a partially-peeled spine is never lost.
///
/// This is what makes the peel uniform across instance encodings: it stops as
/// soon as the head is an ordinary definition (`List.append`, `Nat.mod`), so the
/// op const the rewrite lemma is keyed on is preserved and never δ-unfolded into
/// its `.rec` body.
fn reduce_projection_layers(state: &ProofState, goal: &Goal, expr: Expr) -> Expr {
    let mut current = expr;
    for _ in 0..MAX_PROJECTION_LAYERS {
        match peel_structure_projection(state, goal, &current) {
            Some(next) => current = head_beta(&next),
            None => break,
        }
    }
    current
}

/// Peel exactly one structure-field-accessor layer.
///
/// Recognizes `c a₀ … aₙ` where `c` is a *field accessor* of a single-constructor
/// inductive. Both encodings in this repo count (see [`accessor_shape`]):
/// `λ … => Proj(S, i, xⱼ)` (imported Lean structures, and Clean's
/// `algebra_basic_ofnat.rs`) and `λ … => S.rec …` (most of Clean's hand-rolled
/// prelude, e.g. `Inhabited.default` in `env/data_typeclasses.rs`).
///
/// Only the accessor's OWN arguments are WHNF-reduced — the trailing operands are
/// re-applied untouched, so an operand ι-redex such as `Nat.mul n 0 → Nat.zero`
/// can never fire and erase the op head the rewrite lemma is keyed on. That is
/// the same discipline as the hetero layer above, which reduces the instance term
/// alone.
///
/// Returns `None` when the head is not an accessor const, when it is
/// under-applied, when the structure argument does not WHNF to a known
/// constructor, or when a `.rec`-encoded accessor meets a multi-field structure
/// (no field index to disambiguate) — in every such case the caller keeps the
/// un-peeled form.
fn peel_structure_projection(state: &ProofState, goal: &Goal, expr: &Expr) -> Option<Expr> {
    let ExprKind::Const(head_name, _) = expr.get_app_fn().kind() else {
        return None;
    };
    let accessor = accessor_shape(state, head_name)?;

    let args: Vec<Expr> = expr.get_app_args().into_iter().cloned().collect();
    if args.len() < accessor.arity {
        // Under-applied accessor: nothing to reduce without introducing binders.
        return None;
    }

    // Reduce the STRUCTURE ARGUMENT only, exactly far enough to expose its
    // constructor, then read the field out. The field itself is never reduced
    // and the operands are never entered — so `List.append`/`Nat.mod` survives
    // as a head for the rewrite lemma to key on.
    let structure = state.whnf(goal, args.get(accessor.structure_arg)?);
    let ExprKind::Const(ctor_name, _) = structure.get_app_fn().kind() else {
        return None;
    };
    let ctor = state.env().get_constructor(ctor_name)?;
    let field_idx = match accessor.field {
        Some(idx) => idx,
        // A `.rec`-encoded accessor does not name its field; it is unambiguous
        // only for a one-field structure, which is every class in this family
        // (`Append`, `Div`, `Mod`, `Inhabited`, …).
        None if ctor.num_fields == 1 => 0,
        None => return None,
    };
    let field = structure
        .get_app_args()
        .get(ctor.num_params as usize + field_idx)
        .copied()?
        .clone();

    // Re-apply everything the accessor itself did not consume.
    let mut result = field;
    for arg in &args[accessor.arity..] {
        result = Expr::app(result, arg.clone());
    }
    Some(result)
}

/// Decoded shape of a structure-field accessor: how many arguments it consumes,
/// which of them is the structure, and which field it selects.
struct AccessorShape {
    arity: usize,
    structure_arg: usize,
    /// `None` for the `.rec` encoding, which does not name a field index.
    field: Option<usize>,
}

/// Decode `name` as a field accessor of a single-constructor inductive.
///
/// The single-constructor requirement is what keeps ordinary recursive functions
/// out: `List.append` and `Nat.mod` are `.rec`-bodied too, but `List`/`Nat` have
/// two constructors, so they are never peeled.
fn accessor_shape(state: &ProofState, name: &Name) -> Option<AccessorShape> {
    let value = state.env().get_const(name)?.value.as_ref()?;

    let mut arity = 0usize;
    let mut body: &Expr = value;
    while let ExprKind::Lam(_, _, inner) = body.kind() {
        arity += 1;
        body = inner.as_ref();
    }

    // A de Bruijn index counts from the innermost binder, so binder `d` is
    // argument `arity - 1 - d` in application order.
    let arg_of_bvar = |e: &Expr| match e.kind() {
        ExprKind::BVar(d) => arity.checked_sub(*d as usize + 1),
        _ => None,
    };

    let (structure_name, structure_arg, field) = match body.kind() {
        // `λ … => Proj(S, i, xⱼ)` — imported Lean structures, `OfNat.ofNat`, …
        ExprKind::Proj(structure_name, idx, target) => (
            structure_name.clone(),
            arg_of_bvar(target)?,
            Some(*idx as usize),
        ),
        // `λ … => S.rec … xⱼ` — most of Clean's hand-rolled prelude. The major
        // premise is the recursor's last argument.
        _ => {
            let ExprKind::Const(callee, _) = body.get_app_fn().kind() else {
                return None;
            };
            let inductive_name = state.env().get_recursor(callee)?.inductive_name.clone();
            let major = body.get_app_args().last().copied()?;
            (inductive_name, arg_of_bvar(major)?, None)
        }
    };

    if state
        .env()
        .get_inductive(&structure_name)?
        .constructor_names
        .len()
        != 1
    {
        return None;
    }
    Some(AccessorShape {
        arity,
        structure_arg,
        field,
    })
}
