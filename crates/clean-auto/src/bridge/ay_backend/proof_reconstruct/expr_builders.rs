// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel Expr construction helpers for proof reconstruction.
//!
//! These produce fully-elaborated kernel expressions with all implicit
//! arguments supplied, matching what the Lean 4 kernel expects.

use ay::Sort;
use clean_kernel::expr::ExprKind;
use clean_kernel::name::Name;
use clean_kernel::{Expr, Level};

/// Extract the type name suffix for instance name construction from a ay Sort.
///
/// Follows the Lean 4 convention: `inst{ClassName}{type_suffix}`.
/// E.g., Sort::Int → "Int", yielding "instLTInt", "instHAddInt", etc.
fn sort_type_suffix(sort: &Sort) -> &'static str {
    match sort {
        Sort::Int => "Int",
        Sort::Real => "Real",
        Sort::Bool => "Bool",
        Sort::String => "String",
        _ => "Nat", // conservative default for BitVec, Array, etc.
    }
}

/// Infer the universe level for type formers like `@Eq.{u}` and `@ite.{u}`.
///
/// For `@Eq.{u} α a b`, `u` is the universe such that `α : Sort u`.
/// By the typing rule `Sort n : Sort (n+1)`:
///   - `α = Sort n` → `α : Sort (n+1)`, so `u = succ(n)`
///   - `α = Const (Nat, Int, etc.)` → `α : Type 0 = Sort 1`, so `u = 1`
///
/// For `α = Prop = Sort 0`, returns `succ(0) = 1` (correct: Prop : Type 0).
pub(crate) fn infer_universe_level(ty: &Expr) -> Level {
    match ty.kind() {
        // Sort n : Sort (n+1), so the universe for Eq is succ(n)
        ExprKind::Sort(level) => Level::succ(level.clone()),
        // Const types (Nat, Int, Real, Bool, etc.) live in Type 0, universe 1
        ExprKind::Const(_, _) => Level::succ(Level::zero()),
        // App types (BitVec n, Array k v, etc.) live in Type 0, universe 1
        ExprKind::App(_, _) => Level::succ(Level::zero()),
        // Conservative default: assume Type 0
        _ => Level::succ(Level::zero()),
    }
}

/// Build `@Not p` : `p → False`
pub(crate) fn mk_not(p: &Expr) -> Expr {
    Expr::app(Expr::const_(Name::from_string("Not"), vec![]), p.clone())
}

/// Build `@Eq.{u} α a b` with inferred universe level.
pub(crate) fn mk_eq(ty: &Expr, a: &Expr, b: &Expr) -> Expr {
    let u = infer_universe_level(ty);
    Expr::app(
        Expr::app(
            Expr::app(Expr::const_(Name::from_string("Eq"), vec![u]), ty.clone()),
            a.clone(),
        ),
        b.clone(),
    )
}

/// Build `@And a b`
pub(crate) fn mk_and(a: &Expr, b: &Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("And"), vec![]), a.clone()),
        b.clone(),
    )
}

/// Build `@Or a b`
pub(crate) fn mk_or(a: &Expr, b: &Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Or"), vec![]), a.clone()),
        b.clone(),
    )
}

/// Build `@Xor a b` encoded as `(a ∧ ¬b) ∨ (¬a ∧ b)`
pub(crate) fn mk_xor(a: &Expr, b: &Expr) -> Expr {
    mk_or(&mk_and(a, &mk_not(b)), &mk_and(&mk_not(a), b))
}

/// Attempt to resolve a Decidable instance for a condition expression.
///
/// Returns `Some(instance_expr)` for known decidable conditions,
/// `None` for conditions where no built-in Decidable instance is available.
fn resolve_decidable_instance(cond: &Expr) -> Option<Expr> {
    let head = cond.get_app_fn();
    match head.kind() {
        ExprKind::Const(name, _) => {
            let s = name.to_string();
            if s == "LT.lt" {
                Some(Expr::const_(
                    Name::from_string("instDecidableNatLt"),
                    vec![],
                ))
            } else if s == "LE.le" {
                Some(Expr::const_(
                    Name::from_string("instDecidableNatLe"),
                    vec![],
                ))
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Build `@ite.{u} α cond inst thenBr elseBr` with resolved Decidable instance.
///
/// Lean 4 signature: `@ite.{u} {α : Sort u} (c : Prop) [h : Decidable c] (a b : α) : α`
/// Application order: ite α c h a b (condition before instance).
///
/// Returns `None` if no Decidable instance can be resolved for the condition.
/// The caller should fall back to `Unverified` in that case — fabricating a
/// non-existent instance is worse than falling back to trust.
pub(crate) fn mk_ite_checked(
    sort: &Sort,
    cond: &Expr,
    then_br: &Expr,
    else_br: &Expr,
) -> Option<Expr> {
    let decidable_inst = resolve_decidable_instance(cond)?;
    let ty = sort_to_lean_type(sort);
    let u = infer_universe_level(&ty);
    // @ite.{u} α c h a b — condition (c) at position 2, instance (h) at position 3
    Some(Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(Expr::const_(Name::from_string("ite"), vec![u]), ty),
                    cond.clone(),
                ),
                decidable_inst,
            ),
            then_br.clone(),
        ),
        else_br.clone(),
    ))
}

/// Build `@LT.lt.{0} α inst a b`
///
/// Universe level 0 is correct for all concrete sorts (Int, Nat, Real)
/// which inhabit `Type 0 = Sort 1`.
pub(crate) fn mk_lt(sort: &Sort, a: &Expr, b: &Expr) -> Expr {
    let ty = sort_to_lean_type(sort);
    let suffix = sort_type_suffix(sort);
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("LT.lt"), vec![Level::zero()]),
                    ty,
                ),
                Expr::const_(Name::from_string(&format!("instLT{suffix}")), vec![]),
            ),
            a.clone(),
        ),
        b.clone(),
    )
}

/// Build `@LE.le.{0} α inst a b`
///
/// Universe level 0 is correct for all concrete sorts (Int, Nat, Real)
/// which inhabit `Type 0 = Sort 1`.
pub(crate) fn mk_le(sort: &Sort, a: &Expr, b: &Expr) -> Expr {
    let ty = sort_to_lean_type(sort);
    let suffix = sort_type_suffix(sort);
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
                    ty,
                ),
                Expr::const_(Name::from_string(&format!("instLE{suffix}")), vec![]),
            ),
            a.clone(),
        ),
        b.clone(),
    )
}

/// Build `@HAdd.hAdd.{0,0,0} α α α inst a b`
///
/// `HAdd.hAdd.{u,v,w} : {α : Type u} → {β : Type v} → {γ : Type w} → [HAdd α β γ] → α → β → γ`
/// All supported sorts are Type 0, so u = v = w = 0.
pub(crate) fn mk_add(sort: &Sort, a: &Expr, b: &Expr) -> Expr {
    let ty = sort_to_lean_type(sort);
    let suffix = sort_type_suffix(sort);
    let u = Level::zero();
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::const_(
                                Name::from_string("HAdd.hAdd"),
                                vec![u.clone(), u.clone(), u],
                            ),
                            ty.clone(),
                        ),
                        ty.clone(),
                    ),
                    ty,
                ),
                Expr::const_(Name::from_string(&format!("instHAdd{suffix}")), vec![]),
            ),
            a.clone(),
        ),
        b.clone(),
    )
}

/// Build `@HMul.hMul.{0,0,0} α α α inst a b`
///
/// `HMul.hMul.{u,v,w} : {α : Type u} → {β : Type v} → {γ : Type w} → [HMul α β γ] → α → β → γ`
/// All supported sorts are Type 0, so u = v = w = 0.
pub(crate) fn mk_mul(sort: &Sort, a: &Expr, b: &Expr) -> Expr {
    let ty = sort_to_lean_type(sort);
    let suffix = sort_type_suffix(sort);
    let u = Level::zero();
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::const_(
                                Name::from_string("HMul.hMul"),
                                vec![u.clone(), u.clone(), u],
                            ),
                            ty.clone(),
                        ),
                        ty.clone(),
                    ),
                    ty,
                ),
                Expr::const_(Name::from_string(&format!("instHMul{suffix}")), vec![]),
            ),
            a.clone(),
        ),
        b.clone(),
    )
}

/// Build `@Neg.neg.{0} α inst a`
///
/// `Neg.neg.{u} : {α : Type u} → [inst : Neg α] → α → α`
/// All supported sorts are Type 0, so u = 0.
pub(crate) fn mk_neg(sort: &Sort, a: &Expr) -> Expr {
    let ty = sort_to_lean_type(sort);
    let suffix = sort_type_suffix(sort);
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Neg.neg"), vec![Level::zero()]),
                ty,
            ),
            Expr::const_(Name::from_string(&format!("instNeg{suffix}")), vec![]),
        ),
        a.clone(),
    )
}

/// Build `@Eq.refl.{u} α a : @Eq.{u} α a a`.
pub(crate) fn mk_eq_refl(ty: &Expr, val: &Expr) -> Expr {
    let u = infer_universe_level(ty);
    crate::bridge::eq_proof_builders::mk_eq_refl(&u, ty, val)
}

/// Build `@Eq.symm.{u} α a b h : @Eq.{u} α b a`.
pub(crate) fn mk_eq_symm(ty: &Expr, a: &Expr, b: &Expr, h: &Expr) -> Expr {
    let u = infer_universe_level(ty);
    crate::bridge::eq_proof_builders::mk_eq_symm(&u, ty, a, b, h)
}

/// Build `@Eq.trans.{u} α a b c h₁ h₂ : @Eq.{u} α a c`.
pub(crate) fn mk_eq_trans(ty: &Expr, a: &Expr, b: &Expr, c: &Expr, h1: &Expr, h2: &Expr) -> Expr {
    let u = infer_universe_level(ty);
    crate::bridge::eq_proof_builders::mk_eq_trans(&u, ty, a, b, c, h1, h2)
}

/// Build `@congrArg.{u, v} α β a₁ a₂ f h : f a₁ = f a₂`.
pub(crate) fn mk_congr_arg(
    ty_u: &Level,
    ty_v: &Level,
    alpha: &Expr,
    beta: &Expr,
    a1: &Expr,
    a2: &Expr,
    f: &Expr,
    h: &Expr,
) -> Expr {
    crate::bridge::eq_proof_builders::mk_congr_arg(ty_u, ty_v, alpha, beta, a1, a2, f, h)
}

/// Build `@congr.{u, v} α β f₁ f₂ a₁ a₂ hf ha : f₁ a₁ = f₂ a₂`.
pub(crate) fn mk_congr(
    ty_u: &Level,
    ty_v: &Level,
    alpha: &Expr,
    beta: &Expr,
    f1: &Expr,
    f2: &Expr,
    a1: &Expr,
    a2: &Expr,
    hf: &Expr,
    ha: &Expr,
) -> Expr {
    crate::bridge::eq_proof_builders::mk_congr(ty_u, ty_v, alpha, beta, f1, f2, a1, a2, hf, ha)
}

/// Build `@Eq.mpr.{u} α β h b : α`.
///
/// `Eq.mpr : {α β : Sort u} → (α = β) → β → α`
/// Transports a value of type β to type α via equality α = β (reverse direction).
pub(crate) fn mk_eq_mpr(ty_u: &Level, alpha: &Expr, beta: &Expr, h: &Expr, a: &Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("Eq.mpr"), vec![ty_u.clone()]),
                    alpha.clone(),
                ),
                beta.clone(),
            ),
            h.clone(),
        ),
        a.clone(),
    )
}

/// Map a ay Sort to the corresponding Lean type expression.
///
/// SMT `Bool` corresponds to Lean's `Prop` (Sort 0), not the inductive type
/// `Bool`. In proof reconstruction, `@Eq Bool a b` is ill-typed when `a` and
/// `b` are propositions — the kernel expects `@Eq Prop a b` (#2269).
pub(crate) fn sort_to_lean_type(sort: &Sort) -> Expr {
    match sort {
        Sort::Bool => Expr::sort(Level::zero()), // Prop = Sort 0 (#2269)
        Sort::Int => Expr::const_(Name::from_string("Int"), vec![]),
        Sort::Real => Expr::const_(Name::from_string("Real"), vec![]),
        Sort::BitVec(bv) => Expr::app(
            Expr::const_(Name::from_string("BitVec"), vec![]),
            Expr::nat_lit(bv.width as u64),
        ),
        Sort::Array(arr) => {
            let idx_ty = sort_to_lean_type(&arr.index_sort);
            let elem_ty = sort_to_lean_type(&arr.element_sort);
            Expr::app(
                Expr::app(Expr::const_(Name::from_string("Array"), vec![]), idx_ty),
                elem_ty,
            )
        }
        Sort::String => Expr::const_(Name::from_string("String"), vec![]),
        Sort::Uninterpreted(name) => {
            // Preserve sort identity: each uninterpreted sort becomes a
            // distinct opaque constant, so the kernel detects cross-sort
            // type mismatches instead of silently collapsing to Unit.
            Expr::const_(Name::from_string(name), vec![])
        }
        _ => {
            // Unknown sort variants (RegLan, FloatingPoint, Datatype, Seq, future).
            // Prefixed to avoid collision with real Lean types.
            Expr::const_(Name::from_string("ay.UnknownSort"), vec![])
        }
    }
}
