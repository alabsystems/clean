// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Built-in native reducer functions and `@[implemented_by]` registry for
//! common Lean 4 primitives (decidable equality, string ops).
//! Reference: Lean 4 type_checker.cpp:988-991 `reduce_native`

use crate::env::Environment;
use crate::expr::{BigNat, Expr, ExprKind, Literal};
use crate::name::Name;
use std::sync::LazyLock;

/// A native reducer function that provides fast-path computation for a constant.
///
/// Given the arguments of a fully-applied constant (collected via `get_app_args`),
/// returns `Some(reduced_expr)` if the function can compute the result natively,
/// or `None` to fall back to normal delta reduction. Arguments are references
/// to the original expressions in application order.
///
/// Reference: Lean 4 type_checker.cpp:988-991 — native reducers are registered
/// via `@[implemented_by]` and provide optimized computation rules for constants
/// like `Nat.decEq`, `String.decEq`, `UInt32.decEq`, etc.
pub type NativeReducerFn = fn(args: &[&Expr]) -> Option<Expr>;

/// Well-known names for native reducer registration.
mod names {
    use crate::name::Name;
    use std::sync::LazyLock;

    pub(crate) static NAT_DEC_EQ: LazyLock<Name> = LazyLock::new(|| Name::from_string("Nat.decEq"));
    pub(crate) static BOOL_DEC_EQ: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("Bool.decEq"));
    pub(crate) static STRING_DEC_EQ: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("String.decEq"));
    pub(crate) static STRING_APPEND: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("String.append"));
    pub(crate) static STRING_LENGTH: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("String.length"));
    pub(crate) static STRING_PUSH: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("String.push"));
    pub(crate) static STRING_MK: LazyLock<Name> = LazyLock::new(|| Name::from_string("String.mk"));
    pub(crate) static STRING_BEQ: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("String.beq"));
    pub(crate) static STRING_INTERCALATE: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("String.intercalate"));
    pub(crate) static STRING_IS_EMPTY: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("String.isEmpty"));
    pub(crate) static STRING_UTF8_BYTE_SIZE: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("String.utf8ByteSize"));
    pub(crate) static BOOL_NOT: LazyLock<Name> = LazyLock::new(|| Name::from_string("Bool.not"));
    pub(crate) static BOOL_AND: LazyLock<Name> = LazyLock::new(|| Name::from_string("Bool.and"));
    pub(crate) static BOOL_OR: LazyLock<Name> = LazyLock::new(|| Name::from_string("Bool.or"));
    pub(crate) static BOOL_XOR: LazyLock<Name> = LazyLock::new(|| Name::from_string("Bool.xor"));
}

/// Names for `Decidable` constructors used in building decidable equality results.
mod decidable_names {
    use crate::name::Name;
    use std::sync::LazyLock;

    pub(crate) static DECIDABLE_IS_TRUE: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("Decidable.isTrue"));
    pub(crate) static DECIDABLE_IS_FALSE: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("Decidable.isFalse"));
    pub(crate) static EQ_REFL: LazyLock<Name> = LazyLock::new(|| Name::from_string("Eq.refl"));
    pub(crate) static NAT: LazyLock<Name> = LazyLock::new(|| Name::from_string("Nat"));
    pub(crate) static BOOL: LazyLock<Name> = LazyLock::new(|| Name::from_string("Bool"));
    pub(crate) static STRING: LazyLock<Name> = LazyLock::new(|| Name::from_string("String"));
}

/// Extract a Nat value from an expression (literal or constructor form).
fn get_nat_val(e: &Expr) -> Option<u64> {
    match e.kind() {
        ExprKind::Lit(Literal::Nat(n)) => n.to_u64(),
        _ => None,
    }
}

/// Extract a BigNat reference from an expression.
///
/// Handles both `BigNat::Small` and `BigNat::Big` variants, enabling
/// native reducers to operate on Nat values exceeding u64.
fn get_bignat_val(e: &Expr) -> Option<&BigNat> {
    match e.kind() {
        ExprKind::Lit(Literal::Nat(n)) => Some(n),
        _ => None,
    }
}

/// Extract a String value from an expression.
fn get_string_val(e: &Expr) -> Option<&str> {
    match e.kind() {
        ExprKind::Lit(Literal::String(s)) => Some(s),
        _ => None,
    }
}

/// Extract a Bool value from a constructor expression.
/// `Bool.true` -> Some(true), `Bool.false` -> Some(false)
fn get_bool_val(e: &Expr) -> Option<bool> {
    let head = e.get_app_fn();
    if let ExprKind::Const(name, _) = head.kind() {
        static BOOL_TRUE: LazyLock<Name> = LazyLock::new(|| Name::from_string("Bool.true"));
        static BOOL_FALSE: LazyLock<Name> = LazyLock::new(|| Name::from_string("Bool.false"));
        if *name == *BOOL_TRUE {
            return Some(true);
        }
        if *name == *BOOL_FALSE {
            return Some(false);
        }
    }
    None
}

/// Build `Decidable.isTrue (Eq.refl ty a)` for when `a == b`.
///
/// This creates a proof term for decidable equality that proves `a = a`.
pub(crate) fn mk_dec_is_true(type_name: &Name, val: &Expr) -> Expr {
    let one = crate::level::Level::succ(crate::level::Level::zero());
    let ty = Expr::const_(type_name.clone(), vec![]);
    // The decided proposition `@Eq.{1} ty val val : Prop`.
    let eq_prop = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![one.clone()]),
        [ty.clone(), val.clone(), val.clone()],
    );
    // Its proof `@Eq.refl.{1} ty val : @Eq ty val val`.
    let eq_refl = Expr::apps(
        Expr::const_(decidable_names::EQ_REFL.clone(), vec![one]),
        [ty, val.clone()],
    );
    // `@Decidable.isTrue (p : Prop) (h : p) : Decidable p` — supply BOTH the
    // proposition and the proof (the prior form passed only the proof into the
    // `p` slot, producing an ill-typed term).
    Expr::apps(
        Expr::const_(decidable_names::DECIDABLE_IS_TRUE.clone(), vec![]),
        [eq_prop, eq_refl],
    )
}

/// Build `Decidable.isFalse sorry` for when `a != b`.
///
/// The proof of inequality uses sorry since the kernel only needs
/// the `Decidable.isFalse` constructor tag for reduction — it never
/// inspects the disequality proof. Prefer the type-specific sound builders
/// (e.g. [`mk_nat_dec_is_false`]) where a constructive disproof is available.
/// Build a SOUND `@Decidable.isFalse (@Eq Nat a b) <proof>` for distinct Nat
/// literals — NO `sorryAx`. The disequality proof is
/// `Nat.ne_of_beq_false a b (Eq.refl (Nat.beq a b))`: since `a ≠ b`, `Nat.beq a b`
/// δι-reduces to `false`, so `Eq.refl (Nat.beq a b) : Eq (Nat.beq a b) false` by
/// def-eq, and `Nat.ne_of_beq_false` (a real axiom-free kernel theorem) turns
/// that into `a = b → False`. O(1) term size, independent of the literals.
pub(crate) fn mk_nat_dec_is_false(a: &Expr, b: &Expr) -> Expr {
    let one = crate::level::Level::succ(crate::level::Level::zero());
    let nat = Expr::const_(decidable_names::NAT.clone(), vec![]);
    let bool_ty = Expr::const_(Name::from_string("Bool"), vec![]);
    // proposition `@Eq.{1} Nat a b`
    let eq_prop = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![one.clone()]),
        [nat.clone(), a.clone(), b.clone()],
    );
    // `@Eq.refl.{1} Bool (Nat.beq a b)` — typed at `Eq (Nat.beq a b) false` by def-eq.
    let beq_ab = Expr::apps(
        Expr::const_(Name::from_string("Nat.beq"), vec![]),
        [a.clone(), b.clone()],
    );
    let refl = Expr::apps(
        Expr::const_(Name::from_string("Eq.refl"), vec![one]),
        [bool_ty, beq_ab],
    );
    // `Nat.ne_of_beq_false a b refl : @Eq Nat a b → False`
    let ne = Expr::apps(
        Expr::const_(Name::from_string("Nat.ne_of_beq_false"), vec![]),
        [a.clone(), b.clone(), refl],
    );
    Expr::apps(
        Expr::const_(decidable_names::DECIDABLE_IS_FALSE.clone(), vec![]),
        [eq_prop, ne],
    )
}

/// Build a SOUND `@Decidable.isFalse (@Eq ty a b) <proof>` for a WRAPPER type
/// `ty` whose propositional equality is decided structurally by an underlying
/// `Nat` projection `val_fn : ty → Nat` — NO `sorryAx`. From `h : a = b` derive
/// `val_fn a = val_fn b` via `congrArg val_fn`, then refute it with the axiom-free
/// `Nat.ne_of_beq_false (val_fn a) (val_fn b) (Eq.refl (Nat.beq (val_fn a)(val_fn b)))`
/// — the caller knows the underlying Nats differ, so `Nat.beq …` δι-reduces to
/// `false`. `ty` is `Sort 1` (Char/Fin/Float/UInt/…). O(1) term size.
pub(crate) fn mk_wrapper_dec_is_false(ty: &Expr, val_fn: &Expr, a: &Expr, b: &Expr) -> Expr {
    let one = crate::level::Level::succ(crate::level::Level::zero());
    let nat = Expr::const_(decidable_names::NAT.clone(), vec![]);
    let bool_ty = Expr::const_(Name::from_string("Bool"), vec![]);
    let eq_prop = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![one.clone()]),
        [ty.clone(), a.clone(), b.clone()],
    );
    let va = Expr::app(val_fn.clone(), a.clone());
    let vb = Expr::app(val_fn.clone(), b.clone());
    let beq = Expr::apps(
        Expr::const_(Name::from_string("Nat.beq"), vec![]),
        [va.clone(), vb.clone()],
    );
    let refl = Expr::apps(
        Expr::const_(Name::from_string("Eq.refl"), vec![one.clone()]),
        [bool_ty, beq],
    );
    let ne = Expr::apps(
        Expr::const_(Name::from_string("Nat.ne_of_beq_false"), vec![]),
        [va.clone(), vb.clone(), refl],
    );
    // λ (h : @Eq ty a b) => ne (@congrArg.{1,1} ty Nat a b val_fn h)
    let cong = Expr::apps(
        Expr::const_(Name::from_string("congrArg"), vec![one.clone(), one]),
        [
            ty.clone(),
            nat,
            a.clone(),
            b.clone(),
            val_fn.clone(),
            Expr::bvar(0),
        ],
    );
    let disproof = Expr::lam(
        crate::expr::BinderInfo::Default,
        eq_prop.clone(),
        Expr::app(ne, cong),
    );
    Expr::apps(
        Expr::const_(decidable_names::DECIDABLE_IS_FALSE.clone(), vec![]),
        [eq_prop, disproof],
    )
}

/// `Char.decEq` false case. Discriminates via `Char.toNat : Char → Nat` (NOT
/// `Char.val`): under the genuine v4.30 shape `Char.val : Char → UInt32`, so
/// `Nat.ne_of_beq_false (Char.val a) (Char.val b)` would be ill-typed (UInt32
/// operands where Nat is required). `Char.toNat` is `Nat`-valued in BOTH the
/// pure-clean and real-olean environments and reduces to the code-point literal,
/// so the `congrArg`-based disproof (which needs no injectivity) stays sound and
/// axiom-free: distinct chars have distinct `Char.toNat`s, so `Nat.beq …`
/// δι-reduces to `false`.
pub(crate) fn mk_char_dec_is_false(a: &Expr, b: &Expr) -> Expr {
    mk_wrapper_dec_is_false(
        &Expr::const_(Name::from_string("Char"), vec![]),
        &Expr::const_(Name::from_string("Char.toNat"), vec![]),
        a,
        b,
    )
}

/// Build a SOUND `@Decidable.isFalse (@Eq Bool a b) <proof>` for distinct `Bool`
/// constructors — NO `sorryAx`. The disproof is `fun (h : a = b) =>
/// @Bool.noConfusion.{0} False a b h`: for distinct constructors
/// `Bool.noConfusionType False a b` δ-reduces to `False`, so the application has
/// type `False` directly. `a`/`b` are closed `Bool.true`/`Bool.false` constants.
pub(crate) fn mk_bool_dec_is_false(a: &Expr, b: &Expr) -> Expr {
    let one = crate::level::Level::succ(crate::level::Level::zero());
    let bool_ty = Expr::const_(Name::from_string("Bool"), vec![]);
    let eq_prop = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![one]),
        [bool_ty.clone(), a.clone(), b.clone()],
    );
    // λ (h : @Eq Bool a b) => @Bool.noConfusion.{0} False a b h   (h = BVar 0)
    let body = Expr::apps(
        Expr::const_(
            Name::from_string("Bool.noConfusion"),
            vec![crate::level::Level::zero()],
        ),
        [
            Expr::const_(Name::from_string("False"), vec![]),
            a.clone(),
            b.clone(),
            Expr::bvar(0),
        ],
    );
    let disproof = Expr::lam(crate::expr::BinderInfo::Default, eq_prop.clone(), body);
    Expr::apps(
        Expr::const_(decidable_names::DECIDABLE_IS_FALSE.clone(), vec![]),
        [eq_prop, disproof],
    )
}

/// Build a SOUND `Decidable (Nat.le a b)` — NO `sorryAx`. The witness is
/// `Nat.le_of_ble_eq_true a b (Eq.refl (Nat.ble a b))` (true) /
/// `Nat.not_le_of_ble_eq_false a b (Eq.refl (Nat.ble a b))` (false): the caller
/// knows `a ≤ b` resp. `a > b`, so `Nat.ble a b` δι-reduces to `true`/`false`, the
/// `Eq.refl` is accepted by def-eq, and the axiom-free bridge lemmas turn it into
/// the real proof / disproof.
pub(crate) fn mk_nat_le_dec(a: &Expr, b: &Expr, holds: bool) -> Expr {
    let one = crate::level::Level::succ(crate::level::Level::zero());
    let bool_ty = Expr::const_(Name::from_string("Bool"), vec![]);
    let prop = Expr::apps(
        Expr::const_(Name::from_string("Nat.le"), vec![]),
        [a.clone(), b.clone()],
    );
    let ble_ab = Expr::apps(
        Expr::const_(Name::from_string("Nat.ble"), vec![]),
        [a.clone(), b.clone()],
    );
    let refl = Expr::apps(
        Expr::const_(Name::from_string("Eq.refl"), vec![one]),
        [bool_ty, ble_ab],
    );
    let (lemma, ctor) = if holds {
        (
            "Nat.le_of_ble_eq_true",
            decidable_names::DECIDABLE_IS_TRUE.clone(),
        )
    } else {
        (
            "Nat.not_le_of_ble_eq_false",
            decidable_names::DECIDABLE_IS_FALSE.clone(),
        )
    };
    let proof = Expr::apps(
        Expr::const_(Name::from_string(lemma), vec![]),
        [a.clone(), b.clone(), refl],
    );
    Expr::apps(Expr::const_(ctor, vec![]), [prop, proof])
}

/// Build a SOUND `Decidable (Nat.lt a b)` — NO `sorryAx`. `Nat.lt a b` def-unfolds
/// to `Nat.le (succ a) b`, so the `Nat.le` bridge lemmas applied at `(succ a, b)`
/// give a proof / disproof whose type is def-eq to `Nat.lt a b`.
pub(crate) fn mk_nat_lt_dec(a: &Expr, b: &Expr, holds: bool) -> Expr {
    let one = crate::level::Level::succ(crate::level::Level::zero());
    let bool_ty = Expr::const_(Name::from_string("Bool"), vec![]);
    let succ_a = Expr::app(
        Expr::const_(Name::from_string("Nat.succ"), vec![]),
        a.clone(),
    );
    let prop = Expr::apps(
        Expr::const_(Name::from_string("Nat.lt"), vec![]),
        [a.clone(), b.clone()],
    );
    let ble = Expr::apps(
        Expr::const_(Name::from_string("Nat.ble"), vec![]),
        [succ_a.clone(), b.clone()],
    );
    let refl = Expr::apps(
        Expr::const_(Name::from_string("Eq.refl"), vec![one]),
        [bool_ty, ble],
    );
    let (lemma, ctor) = if holds {
        (
            "Nat.le_of_ble_eq_true",
            decidable_names::DECIDABLE_IS_TRUE.clone(),
        )
    } else {
        (
            "Nat.not_le_of_ble_eq_false",
            decidable_names::DECIDABLE_IS_FALSE.clone(),
        )
    };
    let proof = Expr::apps(
        Expr::const_(Name::from_string(lemma), vec![]),
        [succ_a, b.clone(), refl],
    );
    Expr::apps(Expr::const_(ctor, vec![]), [prop, proof])
}

/// Build a SOUND `Decidable (@<T>.lt a b)` for a single-constructor `Nat`-wrapper
/// type `ty` (`<T>.mk : Nat → <T>`, reducible `<T>.val : <T> → Nat`) — NO
/// `sorryAx`. `<T>.lt` is the reducible `fun a b => Nat.lt (<T>.val a) (<T>.val b)`
/// (`algebra_uint_dec_le_proof.rs`), so the decided prop is `@<T>.lt a b`, which
/// δβ-unfolds to `Nat.lt (<T>.val a) (<T>.val b)` and further to
/// `Nat.le (Nat.succ (<T>.val a)) (<T>.val b)`. The witness is therefore the very
/// same `Nat.le` bridge-lemma proof `mk_nat_lt_dec` builds, but on the projected
/// operands `<T>.val a` / `<T>.val b` and at the wrapper prop `@<T>.lt a b`:
/// `Nat.le_of_ble_eq_true (Nat.succ (<T>.val a)) (<T>.val b) (Eq.refl (Nat.ble …))`
/// (true) / `Nat.not_le_of_ble_eq_false …` (false). The caller knows the
/// underlying Nats' order, so `Nat.ble (Nat.succ (<T>.val a)) (<T>.val b)`
/// δι-reduces to `true`/`false`, the `Eq.refl` is accepted by def-eq, and the
/// proof's type is def-eq to `@<T>.lt a b`. O(1) term size; axiom-free.
pub(crate) fn mk_wrapper_lt_dec(ty: &Expr, val_fn: &Expr, a: &Expr, b: &Expr, holds: bool) -> Expr {
    let one = crate::level::Level::succ(crate::level::Level::zero());
    let bool_ty = Expr::const_(Name::from_string("Bool"), vec![]);
    // The decided prop `@<T>.lt a b` (NOT the unfolded Nat form — the surrounding
    // `Decidable.rec` may be parametric in this exact prop, and it is def-eq to
    // the Nat form so the witness still type-checks).
    let lt_name = wrapper_rel_name(ty, "lt");
    let prop = Expr::apps(Expr::const_(lt_name, vec![]), [a.clone(), b.clone()]);
    // Underlying projected operands.
    let va = Expr::app(val_fn.clone(), a.clone());
    let vb = Expr::app(val_fn.clone(), b.clone());
    let succ_va = Expr::app(Expr::const_(Name::from_string("Nat.succ"), vec![]), va);
    let ble = Expr::apps(
        Expr::const_(Name::from_string("Nat.ble"), vec![]),
        [succ_va.clone(), vb.clone()],
    );
    let refl = Expr::apps(
        Expr::const_(Name::from_string("Eq.refl"), vec![one]),
        [bool_ty, ble],
    );
    let (lemma, ctor) = if holds {
        (
            "Nat.le_of_ble_eq_true",
            decidable_names::DECIDABLE_IS_TRUE.clone(),
        )
    } else {
        (
            "Nat.not_le_of_ble_eq_false",
            decidable_names::DECIDABLE_IS_FALSE.clone(),
        )
    };
    let proof = Expr::apps(
        Expr::const_(Name::from_string(lemma), vec![]),
        [succ_va, vb, refl],
    );
    Expr::apps(Expr::const_(ctor, vec![]), [prop, proof])
}

/// `<T>.lt` / `<T>.le` constant name for the wrapper type `ty = Const("<T>")`.
fn wrapper_rel_name(ty: &Expr, rel: &str) -> Name {
    if let ExprKind::Const(n, _) = ty.kind() {
        Name::from_string(&format!("{n}.{rel}"))
    } else {
        Name::from_string(rel)
    }
}

/// Native reducer for `Nat.decEq : (a b : Nat) → Decidable (a = b)`.
///
/// Compares two Nat literals and returns the appropriate `Decidable` constructor.
/// Handles both Small and Big values via BigNat's PartialEq.
fn reduce_nat_dec_eq(args: &[&Expr]) -> Option<Expr> {
    if args.len() < 2 {
        return None;
    }
    // Cap at the SAME range `Nat.beq` reduces (≤ u128 / 2-limb BigNat). The
    // sound `isFalse` witness's `Eq.refl (Nat.beq a b)` only type-checks when the
    // kernel can reduce `Nat.beq a b` to `false`, which `reduce_nat_beq` also caps
    // here; beyond it we leave `Nat.decEq` stuck (exactly as Lean 4 / `Nat.beq` do)
    // rather than emit an unverifiable term or a `sorry`.
    let a_val = super::native_reducers_arith::get_nat_pred_val(args[0])?;
    let b_val = super::native_reducers_arith::get_nat_pred_val(args[1])?;
    if a_val == b_val {
        Some(mk_dec_is_true(&decidable_names::NAT, args[0]))
    } else {
        Some(mk_nat_dec_is_false(args[0], args[1]))
    }
}

/// Native reducer for `Bool.decEq : (a b : Bool) → Decidable (a = b)`.
fn reduce_bool_dec_eq(args: &[&Expr]) -> Option<Expr> {
    if args.len() < 2 {
        return None;
    }
    let a_val = get_bool_val(args[0])?;
    let b_val = get_bool_val(args[1])?;
    if a_val == b_val {
        Some(mk_dec_is_true(&decidable_names::BOOL, args[0]))
    } else {
        Some(mk_bool_dec_is_false(args[0], args[1]))
    }
}

/// Native reducer for `String.decEq : (a b : String) → Decidable (a = b)`.
fn reduce_string_dec_eq(args: &[&Expr]) -> Option<Expr> {
    if args.len() < 2 {
        return None;
    }
    let a_val = get_string_val(args[0])?;
    let b_val = get_string_val(args[1])?;
    if a_val == b_val {
        // Equal strings: `@Eq.refl String s` is a genuine, sorry-free proof.
        Some(mk_dec_is_true(&decidable_names::STRING, args[0]))
    } else {
        // Distinct strings: *decline* the native fast-path and fall back to iota.
        // `String.decEq` is now a CONSTRUCTIVE, axiom-free Definition
        // (`algebra_string_dec_eq_proof.rs`) backed by the recursive
        // `ListChar.decEq`, so iota reduction yields a sound `Decidable.isFalse`
        // disproof — no `sorryAx` is ever laundered here.
        None
    }
}

/// Native reducer for `String.append : String → String → String`.
fn reduce_string_append(args: &[&Expr]) -> Option<Expr> {
    if args.len() < 2 {
        return None;
    }
    let a = get_string_val(args[0])?;
    let b = get_string_val(args[1])?;
    let mut result = String::with_capacity(a.len() + b.len());
    result.push_str(a);
    result.push_str(b);
    Some(Expr::str_lit(&result))
}

/// Native reducer for `String.length : String → Nat`.
///
/// Returns the number of Unicode code points (characters), NOT the byte length.
/// Lean 4 defines `String.length s := s.data.length` where `data : List Char`.
/// For byte length, use `String.utf8ByteSize`.
fn reduce_string_length(args: &[&Expr]) -> Option<Expr> {
    if args.is_empty() {
        return None;
    }
    let s = get_string_val(args[0])?;
    let len = s.chars().count() as u64;
    Some(Expr::nat_lit(len))
}

/// Native reducer for `String.push : String → Char → String`.
///
/// Appends a single character to a string. The Char argument is represented
/// as a Nat literal (its Unicode code point) after WHNF reduction strips the
/// `Char.mk` wrapper. Returns `None` for non-literal arguments.
fn reduce_string_push(args: &[&Expr]) -> Option<Expr> {
    if args.len() < 2 {
        return None;
    }
    let s = get_string_val(args[0])?;
    let char_val = get_nat_val(args[1])?;
    let c = char::from_u32(char_val as u32)?;
    let mut result = String::with_capacity(s.len() + c.len_utf8());
    result.push_str(s);
    result.push(c);
    Some(Expr::str_lit(&result))
}

/// Native reducer for `String.beq : String → String → Bool`.
fn reduce_string_beq(args: &[&Expr]) -> Option<Expr> {
    if args.len() < 2 {
        return None;
    }
    let a = get_string_val(args[0])?;
    let b = get_string_val(args[1])?;
    let name = if a == b { "Bool.true" } else { "Bool.false" };
    Some(Expr::const_(Name::from_string(name), vec![]))
}

/// Native reducer for `String.isEmpty : String → Bool`.
fn reduce_string_is_empty(args: &[&Expr]) -> Option<Expr> {
    if args.is_empty() {
        return None;
    }
    let s = get_string_val(args[0])?;
    let name = if s.is_empty() {
        "Bool.true"
    } else {
        "Bool.false"
    };
    Some(Expr::const_(Name::from_string(name), vec![]))
}

/// Native reducer for `String.utf8ByteSize : String → Nat`.
///
/// Returns the number of UTF-8 bytes in the string (not code points).
fn reduce_string_utf8_byte_size(args: &[&Expr]) -> Option<Expr> {
    if args.is_empty() {
        return None;
    }
    let s = get_string_val(args[0])?;
    let byte_len = u64::try_from(s.len()).ok()?;
    Some(Expr::nat_lit(byte_len))
}

// --- Bool operation native reducers ---
// These avoid delta-unfolding the Bool.and/or/not/xor definitions, each of which
// pattern-matches on both arguments. In decidable proofs with concrete Bool values,
// this saves 4-8 WHNF steps per operation.

/// Build a Bool constant expression.
fn mk_bool_const(val: bool) -> Expr {
    static BOOL_TRUE_NAME: LazyLock<Name> = LazyLock::new(|| Name::from_string("Bool.true"));
    static BOOL_FALSE_NAME: LazyLock<Name> = LazyLock::new(|| Name::from_string("Bool.false"));
    if val {
        Expr::const_(BOOL_TRUE_NAME.clone(), vec![])
    } else {
        Expr::const_(BOOL_FALSE_NAME.clone(), vec![])
    }
}

/// Native reducer for `Bool.not : Bool → Bool`.
fn reduce_bool_not(args: &[&Expr]) -> Option<Expr> {
    if args.is_empty() {
        return None;
    }
    let val = get_bool_val(args[0])?;
    Some(mk_bool_const(!val))
}

/// Native reducer for `Bool.and : Bool → Bool → Bool`.
fn reduce_bool_and(args: &[&Expr]) -> Option<Expr> {
    if args.len() < 2 {
        return None;
    }
    let a = get_bool_val(args[0])?;
    let b = get_bool_val(args[1])?;
    Some(mk_bool_const(a && b))
}

/// Native reducer for `Bool.or : Bool → Bool → Bool`.
fn reduce_bool_or(args: &[&Expr]) -> Option<Expr> {
    if args.len() < 2 {
        return None;
    }
    let a = get_bool_val(args[0])?;
    let b = get_bool_val(args[1])?;
    Some(mk_bool_const(a || b))
}

/// Native reducer for `Bool.xor : Bool → Bool → Bool`.
fn reduce_bool_xor(args: &[&Expr]) -> Option<Expr> {
    if args.len() < 2 {
        return None;
    }
    let a = get_bool_val(args[0])?;
    let b = get_bool_val(args[1])?;
    Some(mk_bool_const(a ^ b))
}

/// Native reducer and `@[implemented_by]` registry methods for Environment.
impl Environment {
    /// Register an `@[implemented_by]` binding.
    ///
    /// Maps `decl_name` to `impl_name`, meaning that applications of `decl_name`
    /// should be replaced by applications of `impl_name` during native reduction.
    pub fn register_implemented_by(&mut self, decl_name: Name, impl_name: Name) {
        self.implemented_by.insert(decl_name, impl_name);
    }

    /// Get the `@[implemented_by]` target for a declaration.
    pub fn get_implemented_by(&self, name: &Name) -> Option<&Name> {
        self.implemented_by.get(name)
    }

    /// Check if a declaration has an `@[implemented_by]` binding.
    pub fn has_implemented_by(&self, name: &Name) -> bool {
        self.implemented_by.contains_key(name)
    }

    /// Register a native reducer function for a constant.
    ///
    /// Native reducers provide fast-path computation for specific constants,
    /// bypassing the normal delta/iota reduction pipeline. The function
    /// receives the arguments of a fully-applied constant and returns
    /// `Some(result)` if native reduction succeeds.
    pub fn register_native_reducer(&mut self, name: Name, reducer: NativeReducerFn) {
        self.native_reducers.insert(name, reducer);
    }

    /// Look up a native reducer for a constant.
    pub fn get_native_reducer(&self, name: &Name) -> Option<&NativeReducerFn> {
        self.native_reducers.get(name)
    }

    /// Register all built-in native reducers.
    ///
    /// Called during environment initialization (e.g., in `with_prelude`)
    /// to make native reduction available for core Lean 4 primitives.
    pub(crate) fn init_native_reducers(&mut self) {
        self.register_native_reducer(names::NAT_DEC_EQ.clone(), reduce_nat_dec_eq);
        self.register_native_reducer(names::BOOL_DEC_EQ.clone(), reduce_bool_dec_eq);
        self.register_native_reducer(names::STRING_DEC_EQ.clone(), reduce_string_dec_eq);
        self.register_native_reducer(names::STRING_APPEND.clone(), reduce_string_append);
        self.register_native_reducer(names::STRING_LENGTH.clone(), reduce_string_length);
        self.register_native_reducer(names::STRING_PUSH.clone(), reduce_string_push);
        self.register_native_reducer(names::STRING_BEQ.clone(), reduce_string_beq);
        self.register_native_reducer(names::STRING_IS_EMPTY.clone(), reduce_string_is_empty);
        self.register_native_reducer(
            names::STRING_UTF8_BYTE_SIZE.clone(),
            reduce_string_utf8_byte_size,
        );
        // Bool operation reducers
        self.register_native_reducer(names::BOOL_NOT.clone(), reduce_bool_not);
        self.register_native_reducer(names::BOOL_AND.clone(), reduce_bool_and);
        self.register_native_reducer(names::BOOL_OR.clone(), reduce_bool_or);
        self.register_native_reducer(names::BOOL_XOR.clone(), reduce_bool_xor);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::Environment;
    use crate::tc::TypeChecker;

    /// Test that Nat.decEq reduces equal Nat literals to Decidable.isTrue.
    #[test]
    fn test_reduce_nat_dec_eq_equal() {
        let result = reduce_nat_dec_eq(&[&Expr::nat_lit(42), &Expr::nat_lit(42)]);
        assert!(result.is_some(), "Nat.decEq 42 42 should reduce");
        let result = result.unwrap();
        // Result should be a Decidable.isTrue application
        let head = result.get_app_fn();
        if let ExprKind::Const(name, _) = head.kind() {
            assert_eq!(*name, *decidable_names::DECIDABLE_IS_TRUE);
        } else {
            panic!("Expected Decidable.isTrue, got {:?}", head);
        }
    }

    /// The Nat order reducers (`Nat.le`/`Nat.lt`) emit SOUND, sorry-free,
    /// well-typed `Decidable` proofs.
    #[test]
    fn test_nat_order_reducers_are_sound() {
        fn mentions_sorry(e: &Expr) -> bool {
            match e.kind() {
                ExprKind::Const(n, _) => {
                    let s = n.to_string();
                    s == "sorryAx" || s == "sorry"
                }
                ExprKind::App(f, a) => mentions_sorry(f) || mentions_sorry(a),
                ExprKind::Lam(_, t, b) | ExprKind::Pi(_, t, b) => {
                    mentions_sorry(t) || mentions_sorry(b)
                }
                ExprKind::Let(_, t, v, b, _) => {
                    mentions_sorry(t) || mentions_sorry(v) || mentions_sorry(b)
                }
                _ => false,
            }
        }
        let env = Environment::with_prelude();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for (a, b) in [(1u64, 2u64), (2, 2), (3, 2)] {
            let la = Expr::nat_lit(a);
            let lb = Expr::nat_lit(b);
            let le = mk_nat_le_dec(&la, &lb, a <= b);
            assert!(!mentions_sorry(&le), "Nat.le {a} {b} sorry-free");
            let _ = tc
                .infer_type(&le)
                .unwrap_or_else(|e| panic!("le {a} {b} typechecks: {e:?}"));
            let lt = mk_nat_lt_dec(&la, &lb, a < b);
            assert!(!mentions_sorry(&lt), "Nat.lt {a} {b} sorry-free");
            let _ = tc
                .infer_type(&lt)
                .unwrap_or_else(|e| panic!("lt {a} {b} typechecks: {e:?}"));
        }
    }

    /// The unequal-case reducer output is a SOUND, sorry-free, well-typed proof
    /// of `Decidable (Eq Nat 1 2)` — `Nat.decEq` reduction no longer injects
    /// `sorryAx`.
    #[test]
    fn test_reduce_nat_dec_eq_not_equal_is_sound() {
        fn mentions(e: &Expr, target: &str) -> bool {
            match e.kind() {
                ExprKind::Const(n, _) => n.to_string() == target,
                ExprKind::App(f, a) => mentions(f, target) || mentions(a, target),
                ExprKind::Lam(_, t, b) | ExprKind::Pi(_, t, b) => {
                    mentions(t, target) || mentions(b, target)
                }
                ExprKind::Let(_, t, v, b, _) => {
                    mentions(t, target) || mentions(v, target) || mentions(b, target)
                }
                _ => false,
            }
        }
        let env = Environment::with_prelude();
        let term = reduce_nat_dec_eq(&[&Expr::nat_lit(1), &Expr::nat_lit(2)])
            .expect("Nat.decEq 1 2 should reduce");
        assert!(
            !mentions(&term, "sorryAx") && !mentions(&term, "sorry"),
            "Nat.decEq 1 2 reducer output must be sorry-free, got {term:?}"
        );
        assert!(
            mentions(&term, "Nat.ne_of_beq_false"),
            "should use the constructive disequality lemma"
        );
        // It must type-check as a real `Decidable (Eq Nat 1 2)` — this verifies
        // the `Eq.refl (Nat.beq 1 2) : Eq (Nat.beq 1 2) false` def-eq and the
        // whole disproof against the kernel.
        let tc = TypeChecker::with_mode(&env, env.mode());
        let _ = tc
            .infer_type(&term)
            .expect("reducer output must kernel-type-check");
    }

    /// Test that Nat.decEq reduces unequal Nat literals to Decidable.isFalse.
    #[test]
    fn test_reduce_nat_dec_eq_not_equal() {
        let result = reduce_nat_dec_eq(&[&Expr::nat_lit(1), &Expr::nat_lit(2)]);
        assert!(result.is_some(), "Nat.decEq 1 2 should reduce");
        let result = result.unwrap();
        let head = result.get_app_fn();
        if let ExprKind::Const(name, _) = head.kind() {
            assert_eq!(*name, *decidable_names::DECIDABLE_IS_FALSE);
        } else {
            panic!("Expected Decidable.isFalse, got {:?}", head);
        }
    }

    /// Test that Nat.decEq returns None for non-literal arguments.
    #[test]
    fn test_reduce_nat_dec_eq_non_literal_returns_none() {
        let var = Expr::const_(Name::from_string("x"), vec![]);
        let result = reduce_nat_dec_eq(&[&var, &Expr::nat_lit(1)]);
        assert!(result.is_none(), "Non-literal args should not reduce");
    }

    /// Test that Nat.decEq returns None for insufficient arguments.
    #[test]
    fn test_reduce_nat_dec_eq_insufficient_args_returns_none() {
        let result = reduce_nat_dec_eq(&[&Expr::nat_lit(1)]);
        assert!(result.is_none(), "Single arg should not reduce");
    }

    /// Test that Bool.decEq reduces equal Bool values.
    #[test]
    fn test_reduce_bool_dec_eq_equal() {
        let t = Expr::const_(Name::from_string("Bool.true"), vec![]);
        let result = reduce_bool_dec_eq(&[&t, &t]);
        assert!(result.is_some(), "Bool.decEq true true should reduce");
        let result = result.unwrap();
        let head = result.get_app_fn();
        if let ExprKind::Const(name, _) = head.kind() {
            assert_eq!(*name, *decidable_names::DECIDABLE_IS_TRUE);
        } else {
            panic!("Expected Decidable.isTrue, got {:?}", head);
        }
    }

    /// Test that Bool.decEq reduces unequal Bool values.
    #[test]
    fn test_reduce_bool_dec_eq_not_equal() {
        let t = Expr::const_(Name::from_string("Bool.true"), vec![]);
        let f = Expr::const_(Name::from_string("Bool.false"), vec![]);
        let result = reduce_bool_dec_eq(&[&t, &f]);
        assert!(result.is_some(), "Bool.decEq true false should reduce");
        let result = result.unwrap();
        let head = result.get_app_fn();
        if let ExprKind::Const(name, _) = head.kind() {
            assert_eq!(*name, *decidable_names::DECIDABLE_IS_FALSE);
        } else {
            panic!("Expected Decidable.isFalse, got {:?}", head);
        }
    }

    /// Test that String.decEq reduces equal String literals.
    #[test]
    fn test_reduce_string_dec_eq_equal() {
        let a = Expr::str_lit("hello");
        let b = Expr::str_lit("hello");
        let result = reduce_string_dec_eq(&[&a, &b]);
        assert!(result.is_some(), "String.decEq should reduce equal strings");
        let result = result.unwrap();
        let head = result.get_app_fn();
        if let ExprKind::Const(name, _) = head.kind() {
            assert_eq!(*name, *decidable_names::DECIDABLE_IS_TRUE);
        } else {
            panic!("Expected Decidable.isTrue, got {:?}", head);
        }
    }

    /// Test that String.decEq reduces unequal String literals.
    #[test]
    fn test_reduce_string_dec_eq_not_equal() {
        let a = Expr::str_lit("hello");
        let b = Expr::str_lit("world");
        // Distinct strings need `List Char` disequality (not yet built), so the
        // reducer declines rather than launder a `Decidable.isFalse sorryAx`.
        // (The equal case still produces a genuine `Eq.refl`-backed `isTrue`.)
        assert!(
            reduce_string_dec_eq(&[&a, &b]).is_none(),
            "String.decEq declines on distinct strings"
        );
    }

    /// Test that String.append natively concatenates string literals.
    #[test]
    fn test_reduce_string_append() {
        let a = Expr::str_lit("hello ");
        let b = Expr::str_lit("world");
        let result = reduce_string_append(&[&a, &b]);
        assert!(result.is_some(), "String.append should reduce literal args");
        let result = result.unwrap();
        if let ExprKind::Lit(Literal::String(s)) = result.kind() {
            assert_eq!(&**s, "hello world");
        } else {
            panic!("Expected string literal, got {:?}", result);
        }
    }

    /// Test that String.length natively computes character count (not byte length).
    #[test]
    fn test_reduce_string_length() {
        let s = Expr::str_lit("hello");
        let result = reduce_string_length(&[&s]);
        assert!(result.is_some(), "String.length should reduce literal arg");
        let result = result.unwrap();
        if let ExprKind::Lit(Literal::Nat(n)) = result.kind() {
            assert_eq!(n.to_u64(), Some(5));
        } else {
            panic!("Expected Nat literal 5, got {:?}", result);
        }
    }

    /// Test that String.length counts characters, not bytes (multi-byte UTF-8).
    #[test]
    fn test_reduce_string_length_unicode() {
        // "caf\u{00e9}" has 4 characters but 5 bytes (e-acute is 2 bytes in UTF-8)
        let s = Expr::str_lit("caf\u{00e9}");
        let result = reduce_string_length(&[&s]);
        assert!(
            result.is_some(),
            "String.length should reduce unicode literal"
        );
        let result = result.unwrap();
        if let ExprKind::Lit(Literal::Nat(n)) = result.kind() {
            assert_eq!(n.to_u64(), Some(4), "Should count chars not bytes");
        } else {
            panic!("Expected Nat literal 4, got {:?}", result);
        }
    }

    // --- String.length Unicode regression tests (Part of #3134) ---
    // Regression: reduce_string_length previously used s.len() (byte count)
    // instead of s.chars().count() (character count). These tests cover all
    // UTF-8 byte widths to prevent reintroduction.

    /// Test String.length with emoji (4-byte UTF-8 characters).
    #[test]
    fn test_reduce_string_length_emoji() {
        // Two emoji: wave + globe = 2 chars, 8 bytes in UTF-8
        let s = Expr::str_lit("\u{1F44B}\u{1F30D}");
        let result = reduce_string_length(&[&s]);
        assert!(
            result.is_some(),
            "String.length should reduce emoji literal"
        );
        if let ExprKind::Lit(Literal::Nat(n)) = result.unwrap().kind() {
            assert_eq!(
                n.to_u64(),
                Some(2),
                "Emoji string should be 2 chars not 8 bytes"
            );
        } else {
            panic!("Expected Nat literal 2");
        }
    }

    /// Test String.length with CJK characters (3-byte UTF-8).
    #[test]
    fn test_reduce_string_length_cjk() {
        // Two CJK characters = 2 chars, 6 bytes in UTF-8
        let s = Expr::str_lit("\u{4F60}\u{597D}");
        let result = reduce_string_length(&[&s]);
        assert!(result.is_some(), "String.length should reduce CJK literal");
        if let ExprKind::Lit(Literal::Nat(n)) = result.unwrap().kind() {
            assert_eq!(
                n.to_u64(),
                Some(2),
                "CJK string should be 2 chars not 6 bytes"
            );
        } else {
            panic!("Expected Nat literal 2");
        }
    }

    /// Test String.length with mixed ASCII and emoji.
    #[test]
    fn test_reduce_string_length_mixed_ascii_emoji() {
        // "a" + party popper + "b" = 3 chars, 6 bytes
        let s = Expr::str_lit("a\u{1F389}b");
        let result = reduce_string_length(&[&s]);
        assert!(
            result.is_some(),
            "String.length should reduce mixed literal"
        );
        if let ExprKind::Lit(Literal::Nat(n)) = result.unwrap().kind() {
            assert_eq!(
                n.to_u64(),
                Some(3),
                "Mixed ASCII/emoji string should be 3 chars not 6 bytes"
            );
        } else {
            panic!("Expected Nat literal 3");
        }
    }

    /// Test String.length with one character from each UTF-8 byte width.
    #[test]
    fn test_reduce_string_length_all_utf8_widths() {
        // 1-byte: 'A' (0x41)
        // 2-byte: e-acute (0xE9)
        // 3-byte: CJK ideograph (0x4E16)
        // 4-byte: musical symbol (0x1D11E)
        // Total: 4 chars, 10 bytes
        let s = Expr::str_lit("A\u{00E9}\u{4E16}\u{1D11E}");
        let result = reduce_string_length(&[&s]);
        assert!(
            result.is_some(),
            "String.length should reduce multi-width literal"
        );
        if let ExprKind::Lit(Literal::Nat(n)) = result.unwrap().kind() {
            assert_eq!(
                n.to_u64(),
                Some(4),
                "4 chars across all UTF-8 widths (1+2+3+4=10 bytes) should be 4"
            );
        } else {
            panic!("Expected Nat literal 4");
        }
    }

    /// Verify String.length vs String.utf8ByteSize gives different results for Unicode.
    #[test]
    fn test_string_length_vs_utf8_byte_size() {
        // This is the critical regression test: for Unicode strings,
        // length (char count) != utf8ByteSize (byte count).
        let s = Expr::str_lit("\u{1F44B}\u{1F30D}"); // 2 emoji
        let len_result = reduce_string_length(&[&s]);
        let byte_result = reduce_string_utf8_byte_size(&[&s]);
        let len = get_nat_val(&len_result.unwrap()).unwrap();
        let bytes = get_nat_val(&byte_result.unwrap()).unwrap();
        assert_eq!(len, 2, "String.length should return 2 chars");
        assert_eq!(bytes, 8, "String.utf8ByteSize should return 8 bytes");
        assert_ne!(
            len, bytes,
            "Length and byte size must differ for multi-byte strings"
        );
    }

    /// Test that native reducers are properly registered and invoked via reduce_native.
    #[test]
    fn test_native_reducer_registration_and_lookup() {
        let mut env = Environment::new();
        env.init_native_reducers();

        // Verify the reducer is registered
        assert!(
            env.get_native_reducer(&names::NAT_DEC_EQ).is_some(),
            "Nat.decEq reducer should be registered"
        );
        assert!(
            env.get_native_reducer(&names::STRING_DEC_EQ).is_some(),
            "String.decEq reducer should be registered"
        );
        assert!(
            env.get_native_reducer(&names::STRING_APPEND).is_some(),
            "String.append reducer should be registered"
        );
    }

    /// Test end-to-end: reduce_native on a TypeChecker fires for Nat.decEq.
    #[test]
    fn test_reduce_native_fires_nat_dec_eq() {
        let mut env = Environment::new();
        env.init_native_reducers();
        let tc = TypeChecker::new(&env);

        // Build: Nat.decEq 3 3
        let nat_dec_eq_app = Expr::app(
            Expr::app(
                Expr::const_(names::NAT_DEC_EQ.clone(), vec![]),
                Expr::nat_lit(3),
            ),
            Expr::nat_lit(3),
        );

        // reduce_native should fire and return Decidable.isTrue
        let result = tc.reduce_native_for_test(&nat_dec_eq_app);
        assert!(
            result.is_some(),
            "reduce_native should fire for Nat.decEq 3 3"
        );
    }

    /// Test end-to-end: reduce_native returns None for unknown constants.
    #[test]
    fn test_reduce_native_returns_none_for_unknown() {
        let mut env = Environment::new();
        env.init_native_reducers();
        let tc = TypeChecker::new(&env);

        // Build: Unknown.foo 1
        let unknown_app = Expr::app(
            Expr::const_(Name::from_string("Unknown.foo"), vec![]),
            Expr::nat_lit(1),
        );

        let result = tc.reduce_native_for_test(&unknown_app);
        assert!(
            result.is_none(),
            "reduce_native should return None for unknown constants"
        );
    }

    /// Test end-to-end: reduce_native returns None for non-Const head.
    #[test]
    fn test_reduce_native_returns_none_for_non_const_head() {
        let mut env = Environment::new();
        env.init_native_reducers();
        let tc = TypeChecker::new(&env);

        // Build: (λ x. x) 1 — head is a lambda, not a const
        let lam_app = Expr::app(
            Expr::lam(
                crate::expr::BinderInfo::Default,
                Expr::type_(),
                Expr::bvar(0),
            ),
            Expr::nat_lit(1),
        );

        let result = tc.reduce_native_for_test(&lam_app);
        assert!(
            result.is_none(),
            "reduce_native should return None for non-Const head"
        );
    }

    /// Test that @[implemented_by] bindings are properly stored and retrieved.
    #[test]
    fn test_implemented_by_registration() {
        let mut env = Environment::new();
        let decl = Name::from_string("Nat.decEq");
        let impl_name = Name::from_string("Nat.decEqNative");
        env.register_implemented_by(decl.clone(), impl_name.clone());

        assert!(env.has_implemented_by(&decl));
        assert_eq!(env.get_implemented_by(&decl), Some(&impl_name));
        assert!(!env.has_implemented_by(&Name::from_string("Unknown")));
    }

    /// Test that String.append native reducer handles empty strings.
    #[test]
    fn test_reduce_string_append_empty() {
        let a = Expr::str_lit("");
        let b = Expr::str_lit("hello");
        let result = reduce_string_append(&[&a, &b]);
        assert!(result.is_some());
        if let ExprKind::Lit(Literal::String(s)) = result.unwrap().kind() {
            assert_eq!(&**s, "hello");
        } else {
            panic!("Expected string literal");
        }
    }

    /// Test that String.length returns 0 for empty string.
    #[test]
    fn test_reduce_string_length_empty() {
        let s = Expr::str_lit("");
        let result = reduce_string_length(&[&s]);
        assert!(result.is_some());
        if let ExprKind::Lit(Literal::Nat(n)) = result.unwrap().kind() {
            assert_eq!(n.to_u64(), Some(0));
        } else {
            panic!("Expected Nat literal 0");
        }
    }

    // --- String.push tests ---

    /// Test that String.push appends an ASCII character to a string.
    #[test]
    fn test_reduce_string_push_ascii() {
        let s = Expr::str_lit("hello");
        let c = Expr::nat_lit(0x21); // '!'
        let result = reduce_string_push(&[&s, &c]);
        assert!(result.is_some(), "String.push should reduce literal args");
        if let ExprKind::Lit(Literal::String(r)) = result.unwrap().kind() {
            assert_eq!(&**r, "hello!");
        } else {
            panic!("Expected string literal");
        }
    }

    /// Test that String.push appends a Unicode character (multi-byte).
    #[test]
    fn test_reduce_string_push_unicode() {
        let s = Expr::str_lit("cafe");
        let c = Expr::nat_lit(0x0301); // combining acute accent U+0301
        let result = reduce_string_push(&[&s, &c]);
        assert!(result.is_some(), "String.push should reduce Unicode char");
        if let ExprKind::Lit(Literal::String(r)) = result.unwrap().kind() {
            assert_eq!(&**r, "cafe\u{0301}");
        } else {
            panic!("Expected string literal");
        }
    }

    /// Test that String.push onto empty string produces a single-char string.
    #[test]
    fn test_reduce_string_push_empty_string() {
        let s = Expr::str_lit("");
        let c = Expr::nat_lit(0x41); // 'A'
        let result = reduce_string_push(&[&s, &c]);
        assert!(result.is_some());
        if let ExprKind::Lit(Literal::String(r)) = result.unwrap().kind() {
            assert_eq!(&**r, "A");
        } else {
            panic!("Expected string literal");
        }
    }

    /// Test that String.push returns None for invalid code points.
    #[test]
    fn test_reduce_string_push_invalid_codepoint_returns_none() {
        let s = Expr::str_lit("test");
        let c = Expr::nat_lit(0xD800); // surrogate half — invalid char
        let result = reduce_string_push(&[&s, &c]);
        assert!(result.is_none(), "Invalid code point should return None");
    }

    /// Test that String.push returns None for insufficient args.
    #[test]
    fn test_reduce_string_push_insufficient_args() {
        let s = Expr::str_lit("test");
        let result = reduce_string_push(&[&s]);
        assert!(result.is_none(), "Single arg should not reduce");
    }

    // --- String.beq tests ---

    /// Test that String.beq returns Bool.true for equal strings.
    #[test]
    fn test_reduce_string_beq_equal() {
        let a = Expr::str_lit("hello");
        let b = Expr::str_lit("hello");
        let result = reduce_string_beq(&[&a, &b]);
        assert!(result.is_some(), "String.beq should reduce equal strings");
        if let ExprKind::Const(name, _) = result.unwrap().kind() {
            assert_eq!(*name, Name::from_string("Bool.true"));
        } else {
            panic!("Expected Bool.true constant");
        }
    }

    /// Test that String.beq returns Bool.false for unequal strings.
    #[test]
    fn test_reduce_string_beq_not_equal() {
        let a = Expr::str_lit("hello");
        let b = Expr::str_lit("world");
        let result = reduce_string_beq(&[&a, &b]);
        assert!(result.is_some(), "String.beq should reduce unequal strings");
        if let ExprKind::Const(name, _) = result.unwrap().kind() {
            assert_eq!(*name, Name::from_string("Bool.false"));
        } else {
            panic!("Expected Bool.false constant");
        }
    }

    /// Test that String.beq returns Bool.true for two empty strings.
    #[test]
    fn test_reduce_string_beq_both_empty() {
        let a = Expr::str_lit("");
        let b = Expr::str_lit("");
        let result = reduce_string_beq(&[&a, &b]);
        assert!(result.is_some());
        if let ExprKind::Const(name, _) = result.unwrap().kind() {
            assert_eq!(*name, Name::from_string("Bool.true"));
        } else {
            panic!("Expected Bool.true constant");
        }
    }

    /// Test that String.beq returns None for non-literal args.
    #[test]
    fn test_reduce_string_beq_non_literal_returns_none() {
        let a = Expr::str_lit("test");
        let b = Expr::const_(Name::from_string("x"), vec![]);
        let result = reduce_string_beq(&[&a, &b]);
        assert!(result.is_none(), "Non-literal should return None");
    }

    // --- String.isEmpty tests ---

    /// Test that String.isEmpty returns Bool.true for empty string.
    #[test]
    fn test_reduce_string_is_empty_true() {
        let s = Expr::str_lit("");
        let result = reduce_string_is_empty(&[&s]);
        assert!(result.is_some(), "String.isEmpty should reduce");
        if let ExprKind::Const(name, _) = result.unwrap().kind() {
            assert_eq!(*name, Name::from_string("Bool.true"));
        } else {
            panic!("Expected Bool.true constant");
        }
    }

    /// Test that String.isEmpty returns Bool.false for non-empty string.
    #[test]
    fn test_reduce_string_is_empty_false() {
        let s = Expr::str_lit("hello");
        let result = reduce_string_is_empty(&[&s]);
        assert!(result.is_some(), "String.isEmpty should reduce");
        if let ExprKind::Const(name, _) = result.unwrap().kind() {
            assert_eq!(*name, Name::from_string("Bool.false"));
        } else {
            panic!("Expected Bool.false constant");
        }
    }

    /// Test that String.isEmpty returns None for non-literal.
    #[test]
    fn test_reduce_string_is_empty_non_literal_returns_none() {
        let x = Expr::const_(Name::from_string("x"), vec![]);
        let result = reduce_string_is_empty(&[&x]);
        assert!(result.is_none(), "Non-literal should return None");
    }

    /// Test that String.isEmpty returns None for insufficient args.
    #[test]
    fn test_reduce_string_is_empty_insufficient_args() {
        let result = reduce_string_is_empty(&[]);
        assert!(result.is_none(), "Empty args should return None");
    }

    // --- String.utf8ByteSize tests ---

    /// Test that String.utf8ByteSize returns byte length for ASCII string.
    #[test]
    fn test_reduce_string_utf8_byte_size_ascii() {
        let s = Expr::str_lit("hello");
        let result = reduce_string_utf8_byte_size(&[&s]);
        assert!(result.is_some(), "utf8ByteSize should reduce");
        if let ExprKind::Lit(Literal::Nat(n)) = result.unwrap().kind() {
            assert_eq!(n.to_u64(), Some(5));
        } else {
            panic!("Expected Nat literal");
        }
    }

    /// Test that String.utf8ByteSize correctly counts multi-byte characters.
    #[test]
    fn test_reduce_string_utf8_byte_size_multibyte() {
        // "cafe\u{0301}" is 5 bytes in UTF-8 (4 ASCII + 2-byte combining accent)
        let s = Expr::str_lit("caf\u{00e9}"); // e-acute = 2 bytes UTF-8
        let result = reduce_string_utf8_byte_size(&[&s]);
        assert!(result.is_some(), "utf8ByteSize should reduce multibyte");
        if let ExprKind::Lit(Literal::Nat(n)) = result.unwrap().kind() {
            // "caf" = 3 bytes, "\u{00e9}" = 2 bytes = 5 total
            assert_eq!(n.to_u64(), Some(5));
        } else {
            panic!("Expected Nat literal");
        }
    }

    /// Test that String.utf8ByteSize returns 0 for empty string.
    #[test]
    fn test_reduce_string_utf8_byte_size_empty() {
        let s = Expr::str_lit("");
        let result = reduce_string_utf8_byte_size(&[&s]);
        assert!(result.is_some());
        if let ExprKind::Lit(Literal::Nat(n)) = result.unwrap().kind() {
            assert_eq!(n.to_u64(), Some(0));
        } else {
            panic!("Expected Nat literal 0");
        }
    }

    /// Test that String.utf8ByteSize returns None for non-literal.
    #[test]
    fn test_reduce_string_utf8_byte_size_non_literal_returns_none() {
        let x = Expr::const_(Name::from_string("x"), vec![]);
        let result = reduce_string_utf8_byte_size(&[&x]);
        assert!(result.is_none(), "Non-literal should return None");
    }

    // --- Registration tests for new reducers ---

    /// Test that all new String reducers are registered after init_native_reducers.
    #[test]
    fn test_new_string_reducers_registered() {
        let mut env = Environment::new();
        env.init_native_reducers();

        assert!(
            env.get_native_reducer(&names::STRING_PUSH).is_some(),
            "String.push reducer should be registered"
        );
        assert!(
            env.get_native_reducer(&names::STRING_BEQ).is_some(),
            "String.beq reducer should be registered"
        );
        assert!(
            env.get_native_reducer(&names::STRING_IS_EMPTY).is_some(),
            "String.isEmpty reducer should be registered"
        );
        assert!(
            env.get_native_reducer(&names::STRING_UTF8_BYTE_SIZE)
                .is_some(),
            "String.utf8ByteSize reducer should be registered"
        );
    }

    // --- Bool operation reducer tests ---

    /// Test that Bool operation reducers are registered after init_native_reducers.
    #[test]
    fn test_bool_op_reducers_registered() {
        let mut env = Environment::new();
        env.init_native_reducers();

        assert!(
            env.get_native_reducer(&names::BOOL_NOT).is_some(),
            "Bool.not reducer should be registered"
        );
        assert!(
            env.get_native_reducer(&names::BOOL_AND).is_some(),
            "Bool.and reducer should be registered"
        );
        assert!(
            env.get_native_reducer(&names::BOOL_OR).is_some(),
            "Bool.or reducer should be registered"
        );
        assert!(
            env.get_native_reducer(&names::BOOL_XOR).is_some(),
            "Bool.xor reducer should be registered"
        );
    }

    /// Test Bool.not true = false.
    #[test]
    fn test_reduce_bool_not_true() {
        let t = Expr::const_(Name::from_string("Bool.true"), vec![]);
        let result = reduce_bool_not(&[&t]);
        assert!(result.is_some(), "Bool.not true should reduce");
        let val = get_bool_val(&result.unwrap());
        assert_eq!(val, Some(false));
    }

    /// Test Bool.not false = true.
    #[test]
    fn test_reduce_bool_not_false() {
        let f = Expr::const_(Name::from_string("Bool.false"), vec![]);
        let result = reduce_bool_not(&[&f]);
        assert!(result.is_some(), "Bool.not false should reduce");
        let val = get_bool_val(&result.unwrap());
        assert_eq!(val, Some(true));
    }

    /// Test Bool.not returns None for non-Bool argument.
    #[test]
    fn test_reduce_bool_not_non_bool_returns_none() {
        let x = Expr::const_(Name::from_string("x"), vec![]);
        let result = reduce_bool_not(&[&x]);
        assert!(result.is_none(), "Non-Bool should return None");
    }

    /// Test Bool.not returns None for empty args.
    #[test]
    fn test_reduce_bool_not_empty_args_returns_none() {
        let result = reduce_bool_not(&[]);
        assert!(result.is_none(), "Empty args should return None");
    }

    /// Test Bool.and truth table.
    #[test]
    fn test_reduce_bool_and_truth_table() {
        let t = Expr::const_(Name::from_string("Bool.true"), vec![]);
        let f = Expr::const_(Name::from_string("Bool.false"), vec![]);

        // true && true = true
        assert_eq!(
            get_bool_val(&reduce_bool_and(&[&t, &t]).unwrap()),
            Some(true)
        );
        // true && false = false
        assert_eq!(
            get_bool_val(&reduce_bool_and(&[&t, &f]).unwrap()),
            Some(false)
        );
        // false && true = false
        assert_eq!(
            get_bool_val(&reduce_bool_and(&[&f, &t]).unwrap()),
            Some(false)
        );
        // false && false = false
        assert_eq!(
            get_bool_val(&reduce_bool_and(&[&f, &f]).unwrap()),
            Some(false)
        );
    }

    /// Test Bool.or truth table.
    #[test]
    fn test_reduce_bool_or_truth_table() {
        let t = Expr::const_(Name::from_string("Bool.true"), vec![]);
        let f = Expr::const_(Name::from_string("Bool.false"), vec![]);

        // true || true = true
        assert_eq!(
            get_bool_val(&reduce_bool_or(&[&t, &t]).unwrap()),
            Some(true)
        );
        // true || false = true
        assert_eq!(
            get_bool_val(&reduce_bool_or(&[&t, &f]).unwrap()),
            Some(true)
        );
        // false || true = true
        assert_eq!(
            get_bool_val(&reduce_bool_or(&[&f, &t]).unwrap()),
            Some(true)
        );
        // false || false = false
        assert_eq!(
            get_bool_val(&reduce_bool_or(&[&f, &f]).unwrap()),
            Some(false)
        );
    }

    /// Test Bool.xor truth table.
    #[test]
    fn test_reduce_bool_xor_truth_table() {
        let t = Expr::const_(Name::from_string("Bool.true"), vec![]);
        let f = Expr::const_(Name::from_string("Bool.false"), vec![]);

        // true ^ true = false
        assert_eq!(
            get_bool_val(&reduce_bool_xor(&[&t, &t]).unwrap()),
            Some(false)
        );
        // true ^ false = true
        assert_eq!(
            get_bool_val(&reduce_bool_xor(&[&t, &f]).unwrap()),
            Some(true)
        );
        // false ^ true = true
        assert_eq!(
            get_bool_val(&reduce_bool_xor(&[&f, &t]).unwrap()),
            Some(true)
        );
        // false ^ false = false
        assert_eq!(
            get_bool_val(&reduce_bool_xor(&[&f, &f]).unwrap()),
            Some(false)
        );
    }

    /// Test Bool binary ops return None for insufficient args.
    #[test]
    fn test_reduce_bool_binary_ops_insufficient_args_returns_none() {
        let t = Expr::const_(Name::from_string("Bool.true"), vec![]);
        assert!(
            reduce_bool_and(&[&t]).is_none(),
            "Bool.and with 1 arg should return None"
        );
        assert!(
            reduce_bool_or(&[&t]).is_none(),
            "Bool.or with 1 arg should return None"
        );
        assert!(
            reduce_bool_xor(&[&t]).is_none(),
            "Bool.xor with 1 arg should return None"
        );
    }
}
