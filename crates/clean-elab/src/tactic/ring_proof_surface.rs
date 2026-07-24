// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared carrier-specific theorem surface for ring proof reconstruction.

use clean_kernel::name::Name;
use clean_kernel::{BigNat, Expr, ExprKind, Literal};

#[derive(Clone, Copy)]
pub(crate) enum IdentityKind {
    Zero,
    One,
}

#[derive(Clone, Copy)]
pub(crate) struct IdentityEntry {
    pub lemma: &'static str,
    pub id_on_right: bool,
    pub kind: IdentityKind,
    pub annihilator: bool,
}

#[derive(Clone, Copy)]
pub(crate) struct DistributionEntry {
    pub left_distrib: &'static str,
    pub right_distrib: &'static str,
    pub sum_op: &'static str,
}

const NAT_ADD_IDENTITIES: &[IdentityEntry] = &[
    IdentityEntry {
        lemma: "Nat.add_zero",
        id_on_right: true,
        kind: IdentityKind::Zero,
        annihilator: false,
    },
    IdentityEntry {
        lemma: "Nat.zero_add",
        id_on_right: false,
        kind: IdentityKind::Zero,
        annihilator: false,
    },
];

const NAT_MUL_IDENTITIES: &[IdentityEntry] = &[
    IdentityEntry {
        lemma: "Nat.mul_one",
        id_on_right: true,
        kind: IdentityKind::One,
        annihilator: false,
    },
    IdentityEntry {
        lemma: "Nat.one_mul",
        id_on_right: false,
        kind: IdentityKind::One,
        annihilator: false,
    },
    IdentityEntry {
        lemma: "Nat.mul_zero",
        id_on_right: true,
        kind: IdentityKind::Zero,
        annihilator: true,
    },
    IdentityEntry {
        lemma: "Nat.zero_mul",
        id_on_right: false,
        kind: IdentityKind::Zero,
        annihilator: true,
    },
];

const INT_ADD_IDENTITIES: &[IdentityEntry] = &[
    IdentityEntry {
        lemma: "Int.add_zero",
        id_on_right: true,
        kind: IdentityKind::Zero,
        annihilator: false,
    },
    IdentityEntry {
        lemma: "Int.zero_add",
        id_on_right: false,
        kind: IdentityKind::Zero,
        annihilator: false,
    },
];

const INT_MUL_IDENTITIES: &[IdentityEntry] = &[
    IdentityEntry {
        lemma: "Int.mul_one",
        id_on_right: true,
        kind: IdentityKind::One,
        annihilator: false,
    },
    IdentityEntry {
        lemma: "Int.one_mul",
        id_on_right: false,
        kind: IdentityKind::One,
        annihilator: false,
    },
    IdentityEntry {
        lemma: "Int.mul_zero",
        id_on_right: true,
        kind: IdentityKind::Zero,
        annihilator: true,
    },
    IdentityEntry {
        lemma: "Int.zero_mul",
        id_on_right: false,
        kind: IdentityKind::Zero,
        annihilator: true,
    },
];

const RAT_ADD_IDENTITIES: &[IdentityEntry] = &[
    IdentityEntry {
        lemma: "Rat.add_zero",
        id_on_right: true,
        kind: IdentityKind::Zero,
        annihilator: false,
    },
    IdentityEntry {
        lemma: "Rat.zero_add",
        id_on_right: false,
        kind: IdentityKind::Zero,
        annihilator: false,
    },
];

const RAT_MUL_IDENTITIES: &[IdentityEntry] = &[
    IdentityEntry {
        lemma: "Rat.mul_one",
        id_on_right: true,
        kind: IdentityKind::One,
        annihilator: false,
    },
    IdentityEntry {
        lemma: "Rat.one_mul",
        id_on_right: false,
        kind: IdentityKind::One,
        annihilator: false,
    },
    IdentityEntry {
        lemma: "Rat.mul_zero",
        id_on_right: true,
        kind: IdentityKind::Zero,
        annihilator: true,
    },
    IdentityEntry {
        lemma: "Rat.zero_mul",
        id_on_right: false,
        kind: IdentityKind::Zero,
        annihilator: true,
    },
];

// Generic (typeclass-based) identity entries for HAdd.hAdd / HMul.hMul.
// These use the abstract Semiring/Ring axiom names (add_zero, zero_add, etc.)
// without a type-specific prefix, matching the Lean 4 Semiring typeclass fields.

const GENERIC_ADD_IDENTITIES: &[IdentityEntry] = &[
    IdentityEntry {
        lemma: "add_zero",
        id_on_right: true,
        kind: IdentityKind::Zero,
        annihilator: false,
    },
    IdentityEntry {
        lemma: "zero_add",
        id_on_right: false,
        kind: IdentityKind::Zero,
        annihilator: false,
    },
];

const GENERIC_MUL_IDENTITIES: &[IdentityEntry] = &[
    IdentityEntry {
        lemma: "mul_one",
        id_on_right: true,
        kind: IdentityKind::One,
        annihilator: false,
    },
    IdentityEntry {
        lemma: "one_mul",
        id_on_right: false,
        kind: IdentityKind::One,
        annihilator: false,
    },
    IdentityEntry {
        lemma: "mul_zero",
        id_on_right: true,
        kind: IdentityKind::Zero,
        annihilator: true,
    },
    IdentityEntry {
        lemma: "zero_mul",
        id_on_right: false,
        kind: IdentityKind::Zero,
        annihilator: true,
    },
];

/// Map a concrete carrier type expression to its lemma-name prefix.
///
/// `@HAdd.hAdd α β γ inst a b` carries the carrier type `α` as its first
/// explicit argument. When that carrier resolves to a concrete type
/// (`Nat`/`Int`/`Rat`), the kernel-checked, zero-axiom lemmas for that type
/// (`Nat.add_comm`, ...) are usable directly: the proof term
/// `Nat.add_comm a b : Nat.add a b = Nat.add b a` closes the typeclass-headed
/// goal because `close_goal` WHNF-normalizes the inferred type and
/// `@HAdd.hAdd Nat … a b` reduces to `Nat.add a b`.
///
/// Returns `None` for non-concrete carriers (genuine generic goals), so the
/// builder falls back to the typeclass lemma names and fails-closed if those
/// are not registered. Part of #3368.
fn carrier_prefix(carrier: &Expr) -> Option<&'static str> {
    match carrier.kind() {
        ExprKind::Const(n, _) => match n.to_string().as_str() {
            "Nat" => Some("Nat"),
            "Int" => Some("Int"),
            "Rat" => Some("Rat"),
            _ => None,
        },
        _ => None,
    }
}

/// Resolve a binary operator application to its concrete carrier form for
/// structural (proof-carrying) normalization.
///
/// Returns `(op_name, head_const)` where `head_const` applied to `[lhs, rhs]`
/// rebuilds an operator application. Concrete carrier operators (`Nat.add`, ...)
/// take exactly two arguments, so no prefix args are needed; the resulting
/// concrete-headed expressions are definitionally equal to the original
/// typeclass-headed ones (the kernel's `close_goal` WHNF-check bridges the two).
/// Returns `None` for non-concrete typeclass goals so the carry normalizer
/// fails-closed. Part of #3368.
pub(crate) fn resolve_concrete_binop(op_name: &str, args: &[&Expr]) -> Option<(String, Expr)> {
    let resolved = resolve_concrete_op(op_name, args)?;
    if resolved == op_name && matches!(op_name, "HAdd.hAdd" | "HMul.hMul" | "HSub.hSub") {
        // Typeclass head over a non-concrete carrier: no concrete lemmas exist.
        return None;
    }
    let head = Expr::const_(Name::from_string(&resolved), vec![]);
    Some((resolved, head))
}

/// Resolve a typeclass operator head (`HAdd.hAdd`, `HMul.hMul`, `HSub.hSub`)
/// to a concrete carrier-specific operator name (`Nat.add`, ...) using the
/// carrier type argument from the application spine.
///
/// For already-concrete heads (`Nat.add`, `Int.mul`, ...) returns the head
/// unchanged. Returns `None` for typeclass heads over a non-concrete carrier
/// so callers fall back to the generic typeclass surface (which fails-closed
/// when no generic lemma is registered).
///
/// `args` is the full explicit argument spine of the operator application
/// (e.g. `[α, β, γ, inst, a, b]` for a fully-applied `HAdd.hAdd`).
pub(crate) fn resolve_concrete_op(op_name: &str, args: &[&Expr]) -> Option<String> {
    let suffix = match op_name {
        "HAdd.hAdd" => "add",
        "HMul.hMul" => "mul",
        "HSub.hSub" => "sub",
        // Already concrete (or unmapped typeclass head): return as-is.
        _ => return Some(op_name.to_string()),
    };
    // The carrier type is the first explicit argument of the hetero op.
    let carrier = args.first()?;
    let prefix = carrier_prefix(carrier)?;
    Some(format!("{prefix}.{suffix}"))
}

pub(crate) fn assoc_name(op_name: &str) -> Option<&'static str> {
    match op_name {
        "Nat.add" => Some("Nat.add_assoc"),
        "Nat.mul" => Some("Nat.mul_assoc"),
        "Int.add" => Some("Int.add_assoc"),
        "Int.mul" => Some("Int.mul_assoc"),
        "Rat.add" => Some("Rat.add_assoc"),
        "Rat.mul" => Some("Rat.mul_assoc"),
        "HAdd.hAdd" => Some("add_assoc"),
        "HMul.hMul" => Some("mul_assoc"),
        _ => None,
    }
}

pub(crate) fn comm_name(op_name: &str) -> Option<&'static str> {
    match op_name {
        "Nat.add" => Some("Nat.add_comm"),
        "Nat.mul" => Some("Nat.mul_comm"),
        "Int.add" => Some("Int.add_comm"),
        "Int.mul" => Some("Int.mul_comm"),
        "Rat.add" => Some("Rat.add_comm"),
        "Rat.mul" => Some("Rat.mul_comm"),
        "HAdd.hAdd" => Some("add_comm"),
        "HMul.hMul" => Some("mul_comm"),
        _ => None,
    }
}

pub(crate) fn identity_entries(op_name: &str) -> &'static [IdentityEntry] {
    match op_name {
        "Nat.add" => NAT_ADD_IDENTITIES,
        "Nat.mul" => NAT_MUL_IDENTITIES,
        "Int.add" => INT_ADD_IDENTITIES,
        "Int.mul" => INT_MUL_IDENTITIES,
        "Rat.add" => RAT_ADD_IDENTITIES,
        "Rat.mul" => RAT_MUL_IDENTITIES,
        "HAdd.hAdd" => GENERIC_ADD_IDENTITIES,
        "HMul.hMul" => GENERIC_MUL_IDENTITIES,
        _ => &[],
    }
}

/// Carrier-aware identity-entry table.
///
/// For a typeclass head (`HMul.hMul`, ...) over a concrete carrier, returns the
/// concrete-carrier identity entries (`Nat.mul_one`, ...) so the kernel-checked
/// per-type lemmas are used. Falls back to the generic entries (`mul_one`, ...)
/// only when the carrier is not concrete; those generic names are not registered
/// in the real environment, so the builder fails-closed. Part of #3368.
///
/// The identity-element *recognition* (zero/one) is still done with the raw op
/// name via the generic recognizer in [`is_identity_expr`], which already
/// handles `Nat.zero`, `Zero.zero`, `OfNat.ofNat 0`, literals, etc.
pub(crate) fn identity_entries_for(op_name: &str, args: &[&Expr]) -> &'static [IdentityEntry] {
    if let Some(resolved) = resolve_concrete_op(op_name, args) {
        return identity_entries(&resolved);
    }
    identity_entries(op_name)
}

/// Carrier-specific lemma surface for coefficient-merging (`x + x → 2*x`)
/// during proof-carrying ring normalization (#ring-coeff-merge).
///
/// Indexed by the *addition* operator that joins the like monomials. All four
/// lemmas are kernel-checked, zero-domain-axiom `Declaration::Theorem`s in the
/// real Nat/Int/Rat environments:
/// - `mul_op`       — the multiplication operator the coefficient attaches to.
/// - `one_mul`      — `1 * x = x` (peels the unit coefficient).
/// - `right_distrib`— `(a + b) * x = a*x + b*x` (folds `1*x + 1*x` to `(1+1)*x`).
/// - `mul_assoc`    — `(a*b)*c = a*(b*c)` (re-associates `c*(f*g)` to `(c*f)*g`
///   so the fused monomial matches the canonical left-associated factor chain).
#[derive(Clone, Copy)]
pub(crate) struct CoeffMergeEntry {
    pub mul_op: &'static str,
    pub one_mul: &'static str,
    pub right_distrib: &'static str,
    pub mul_assoc: &'static str,
}

/// Resolve the coefficient-merge lemma surface for an addition operator.
///
/// Returns `None` for operators with no registered semiring surface (so the
/// fuser fails-closed and `ring` reports `ArithmeticFailed` rather than
/// fabricating a proof).
pub(crate) fn coeff_merge_entry(add_op: &str) -> Option<CoeffMergeEntry> {
    match add_op {
        "Nat.add" => Some(CoeffMergeEntry {
            mul_op: "Nat.mul",
            one_mul: "Nat.one_mul",
            right_distrib: "Nat.right_distrib",
            mul_assoc: "Nat.mul_assoc",
        }),
        "Int.add" => Some(CoeffMergeEntry {
            mul_op: "Int.mul",
            one_mul: "Int.one_mul",
            right_distrib: "Int.right_distrib",
            mul_assoc: "Int.mul_assoc",
        }),
        "Rat.add" => Some(CoeffMergeEntry {
            mul_op: "Rat.mul",
            one_mul: "Rat.one_mul",
            right_distrib: "Rat.right_distrib",
            mul_assoc: "Rat.mul_assoc",
        }),
        _ => None,
    }
}

pub(crate) fn distribution_entry(op_name: &str) -> Option<DistributionEntry> {
    match op_name {
        "Nat.mul" => Some(DistributionEntry {
            left_distrib: "Nat.left_distrib",
            right_distrib: "Nat.right_distrib",
            sum_op: "Nat.add",
        }),
        "Int.mul" => Some(DistributionEntry {
            left_distrib: "Int.left_distrib",
            right_distrib: "Int.right_distrib",
            sum_op: "Int.add",
        }),
        "Rat.mul" => Some(DistributionEntry {
            left_distrib: "Rat.left_distrib",
            right_distrib: "Rat.right_distrib",
            sum_op: "Rat.add",
        }),
        "HMul.hMul" => Some(DistributionEntry {
            left_distrib: "left_distrib",
            right_distrib: "right_distrib",
            sum_op: "HAdd.hAdd",
        }),
        _ => None,
    }
}

pub(crate) fn zero_const_name(op_name: &str) -> Option<&'static str> {
    match op_name {
        "Nat.add" | "Nat.mul" => Some("Nat.zero"),
        "Int.add" | "Int.mul" | "Int.sub" => Some("Int.zero"),
        "Rat.add" | "Rat.mul" => Some("Rat.zero"),
        "HAdd.hAdd" | "HMul.hMul" | "HSub.hSub" => Some("Zero.zero"),
        _ => None,
    }
}

/// Return the lemma name that rewrites subtraction as addition + negation.
///
/// For `Int.sub a b`, the lemma `Int.sub_eq_add_neg : a - b = a + (-b)`.
/// For `HSub.hSub a b`, the lemma `sub_eq_add_neg`.
/// Part of #3368.
pub(crate) fn sub_eq_add_neg_name(op_name: &str) -> Option<&'static str> {
    match op_name {
        "Int.sub" => Some("Int.sub_eq_add_neg"),
        "HSub.hSub" => Some("sub_eq_add_neg"),
        _ => None,
    }
}

/// Return the addition operator name corresponding to a subtraction operator.
///
/// Part of #3368.
pub(crate) fn sub_to_add_op(op_name: &str) -> Option<&'static str> {
    match op_name {
        "Int.sub" => Some("Int.add"),
        "HSub.hSub" => Some("HAdd.hAdd"),
        _ => None,
    }
}

/// Return the negation operator name corresponding to a subtraction operator.
///
/// Part of #3368.
pub(crate) fn sub_to_neg_op(op_name: &str) -> Option<&'static str> {
    match op_name {
        "Int.sub" => Some("Int.neg"),
        "HSub.hSub" => Some("Neg.neg"),
        _ => None,
    }
}

/// Return the `neg_neg` lemma name for a negation operator.
///
/// For `Int.neg (Int.neg a)`, the lemma `Int.neg_neg : -(-a) = a`.
/// Part of #3368.
pub(crate) fn neg_neg_name(op_name: &str) -> Option<&'static str> {
    match op_name {
        "Int.neg" => Some("Int.neg_neg"),
        "Neg.neg" => Some("neg_neg"),
        _ => None,
    }
}

/// Return the negation-distribute-over-addition lemma name.
///
/// `Int.neg_add : -(a + b) = (-a) + (-b)`.
/// Part of #3368.
pub(crate) fn neg_add_distrib_name(op_name: &str) -> Option<&'static str> {
    match op_name {
        "Int.neg" => Some("Int.neg_add"),
        "Neg.neg" => Some("neg_add"),
        _ => None,
    }
}

pub(crate) fn is_identity_expr(expr: &Expr, op_name: &str, kind: IdentityKind) -> bool {
    match kind {
        IdentityKind::Zero => is_zero_expr(expr, op_name),
        IdentityKind::One => is_one_expr(expr, op_name),
    }
}

fn is_zero_expr(expr: &Expr, op_name: &str) -> bool {
    match op_name {
        "Nat.add" | "Nat.mul" => is_nat_zero(expr),
        "Int.add" | "Int.mul" => is_int_zero(expr),
        "Rat.add" | "Rat.mul" => is_named_const(expr, "Rat.zero"),
        "HAdd.hAdd" | "HMul.hMul" => is_generic_zero(expr),
        _ => false,
    }
}

fn is_one_expr(expr: &Expr, op_name: &str) -> bool {
    match op_name {
        "Nat.add" | "Nat.mul" => is_nat_one(expr),
        "Int.add" | "Int.mul" => is_int_one(expr),
        "Rat.add" | "Rat.mul" => is_named_const(expr, "Rat.one"),
        "HAdd.hAdd" | "HMul.hMul" => is_generic_one(expr),
        _ => false,
    }
}

fn is_named_const(expr: &Expr, name: &str) -> bool {
    matches!(expr.kind(), ExprKind::Const(n, _) if n.to_string() == name)
}

fn is_nat_zero(expr: &Expr) -> bool {
    is_named_const(expr, "Nat.zero")
}

fn is_nat_one(expr: &Expr) -> bool {
    is_named_const(expr, "Nat.one")
        || matches!(expr.kind(), ExprKind::App(f, a)
            if matches!(f.kind(), ExprKind::Const(n, _) if n.to_string() == "Nat.succ")
                && is_nat_zero(a))
}

/// Recognize Int zero: `Int.zero` or `Int.ofNat Nat.zero` or `Int.ofNat (Lit 0)`.
fn is_int_zero(expr: &Expr) -> bool {
    if is_named_const(expr, "Int.zero") {
        return true;
    }
    match expr.kind() {
        ExprKind::App(f, a) if is_named_const(f, "Int.ofNat") => {
            is_nat_zero(a) || matches!(a.kind(), ExprKind::Lit(Literal::Nat(BigNat::Small(0))))
        }
        _ => false,
    }
}

/// Recognize Int one: `Int.ofNat (Nat.succ Nat.zero)` or `Int.ofNat (Lit 1)`.
fn is_int_one(expr: &Expr) -> bool {
    match expr.kind() {
        ExprKind::App(f, a) if is_named_const(f, "Int.ofNat") => {
            is_nat_one(a) || matches!(a.kind(), ExprKind::Lit(Literal::Nat(BigNat::Small(1))))
        }
        _ => false,
    }
}

/// Recognize generic zero for typeclass-based operations.
///
/// Matches: `Zero.zero`, `OfNat.ofNat 0 ...` (with any instance arg),
/// `Nat.zero`, Nat literal 0, or any Nat/Int zero form.
fn is_generic_zero(expr: &Expr) -> bool {
    if is_named_const(expr, "Zero.zero") {
        return true;
    }
    if is_nat_zero(expr) || is_int_zero(expr) {
        return true;
    }
    // OfNat.ofNat applied to literal 0: the head is OfNat.ofNat and the first
    // explicit arg is a Nat literal 0.
    if let ExprKind::App(_, _) = expr.kind() {
        let head = expr.get_app_fn();
        if is_named_const(head, "OfNat.ofNat") {
            let args = expr.get_app_args();
            // OfNat.ofNat takes (α : Type) (n : Nat) (inst : OfNat α n) as args.
            // We check if the second arg (index 1) is Nat zero or literal 0.
            if args.len() >= 2 {
                let n_arg = args[1];
                if is_nat_zero(n_arg)
                    || matches!(n_arg.kind(), ExprKind::Lit(Literal::Nat(BigNat::Small(0))))
                {
                    return true;
                }
            }
        }
    }
    false
}

/// Recognize generic one for typeclass-based operations.
///
/// Matches: `One.one`, `OfNat.ofNat 1 ...`, `Nat.one`, `Nat.succ Nat.zero`,
/// Nat literal 1, or any Nat/Int one form.
fn is_generic_one(expr: &Expr) -> bool {
    if is_named_const(expr, "One.one") {
        return true;
    }
    if is_nat_one(expr) || is_int_one(expr) {
        return true;
    }
    // OfNat.ofNat applied to literal 1
    if let ExprKind::App(_, _) = expr.kind() {
        let head = expr.get_app_fn();
        if is_named_const(head, "OfNat.ofNat") {
            let args = expr.get_app_args();
            if args.len() >= 2 {
                let n_arg = args[1];
                if is_nat_one(n_arg)
                    || matches!(n_arg.kind(), ExprKind::Lit(Literal::Nat(BigNat::Small(1))))
                {
                    return true;
                }
            }
        }
    }
    false
}
