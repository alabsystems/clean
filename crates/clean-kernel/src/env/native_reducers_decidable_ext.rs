// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended native reducers for Decidable propositions and related operations.
//!
//! Complements `native_reducers_decidable.rs` with additional reducers that
//! short-circuit common patterns in Init proof terms:
//!
//! - `Nat.decLe` / `Nat.decLt` — decidable ordering on Nat literals
//! - `decide` — evaluates a `Decidable` instance to `Bool.true`/`Bool.false`
//! - `instDecidableAnd` / `instDecidableOr` / `instDecidableNot` — combinators
//! - `Int.decEq` / `Int.decLe` / `Int.decLt` — Int decidable ops
//!
//! These are critical for the 426+ `_private.Init` heartbeat-exceeded failures
//! (#3210) which involve proof-by-reflection terms that chain Decidable
//! combinators on literal values.

use crate::env::native_reducers::mk_dec_is_true;
use crate::env::Environment;
use crate::expr::{Expr, ExprKind, Literal};
use crate::name::Name;
use std::sync::LazyLock;

/// Well-known names for extended Decidable native reducers.
pub(crate) mod names {
    use crate::name::Name;
    use std::sync::LazyLock;

    pub(crate) static NAT_DEC_LE: LazyLock<Name> = LazyLock::new(|| Name::from_string("Nat.decLe"));
    pub(crate) static NAT_DEC_LT: LazyLock<Name> = LazyLock::new(|| Name::from_string("Nat.decLt"));
    pub(crate) static DECIDE: LazyLock<Name> = LazyLock::new(|| Name::from_string("decide"));
    pub(crate) static DECIDABLE_DECIDE: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("Decidable.decide"));
    pub(crate) static INST_DECIDABLE_AND: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("instDecidableAnd"));
    pub(crate) static INST_DECIDABLE_OR: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("instDecidableOr"));
    pub(crate) static INST_DECIDABLE_NOT: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("instDecidableNot"));
    pub(crate) static INT_DEC_EQ: LazyLock<Name> = LazyLock::new(|| Name::from_string("Int.decEq"));
    pub(crate) static INT_DEC_LE: LazyLock<Name> = LazyLock::new(|| Name::from_string("Int.decLe"));
    pub(crate) static INT_DEC_LT: LazyLock<Name> = LazyLock::new(|| Name::from_string("Int.decLt"));
    pub(crate) static INST_DECIDABLE_EQ_INT: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("instDecidableEqInt"));
    pub(crate) static INST_DECIDABLE_LE_INT: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("instDecidableLeInt"));
    pub(crate) static INST_DECIDABLE_LT_INT: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("instDecidableLtInt"));
}

/// Decidable constructor name constants.
static DECIDABLE_IS_TRUE: LazyLock<Name> = LazyLock::new(|| Name::from_string("Decidable.isTrue"));
static DECIDABLE_IS_FALSE: LazyLock<Name> =
    LazyLock::new(|| Name::from_string("Decidable.isFalse"));
static INT_NAME: LazyLock<Name> = LazyLock::new(|| Name::from_string("Int"));
static BOOL_TRUE: LazyLock<Name> = LazyLock::new(|| Name::from_string("Bool.true"));
static BOOL_FALSE: LazyLock<Name> = LazyLock::new(|| Name::from_string("Bool.false"));

/// Extract a Nat value from an expression literal.
fn get_nat_val(e: &Expr) -> Option<u64> {
    match e.kind() {
        ExprKind::Lit(Literal::Nat(n)) => n.to_u64(),
        _ => None,
    }
}

/// Extract an Int value from an expression.
///
/// Lean 4 Int is an inductive with constructors:
/// - `Int.ofNat : Nat → Int` — non-negative integers
/// - `Int.negSucc : Nat → Int` — negative integers: negSucc(n) = -(n+1)
fn get_int_val(e: &Expr) -> Option<i64> {
    static INT_OF_NAT: LazyLock<Name> = LazyLock::new(|| Name::from_string("Int.ofNat"));
    static INT_NEG_SUCC: LazyLock<Name> = LazyLock::new(|| Name::from_string("Int.negSucc"));

    let head = e.get_app_fn();
    let args = e.get_app_args();
    if let ExprKind::Const(name, _) = head.kind() {
        if *name == *INT_OF_NAT && args.len() == 1 {
            let n = get_nat_val(args[0])?;
            return i64::try_from(n).ok();
        }
        if *name == *INT_NEG_SUCC && args.len() == 1 {
            let n = get_nat_val(args[0])?;
            // negSucc(n) = -(n+1)
            let pos = i64::try_from(n).ok()?;
            return pos.checked_add(1).map(|v| -v);
        }
    }
    // Also handle bare Nat literal (implicit Int.ofNat)
    if let Some(n) = get_nat_val(e) {
        return i64::try_from(n).ok();
    }
    None
}

/// Check if a `Decidable` instance expression is `Decidable.isTrue _` or
/// `Decidable.isFalse _`. Returns `Some(true)` for isTrue, `Some(false)` for
/// isFalse, `None` if the head is neither.
fn get_decidable_val(e: &Expr) -> Option<bool> {
    let head = e.get_app_fn();
    if let ExprKind::Const(name, _) = head.kind() {
        if *name == *DECIDABLE_IS_TRUE {
            return Some(true);
        }
        if *name == *DECIDABLE_IS_FALSE {
            return Some(false);
        }
    }
    None
}

// --- Nat ordering decidable reducers ---

/// Native reducer for `Nat.decLe : (a b : Nat) → Decidable (a ≤ b)`.
pub(crate) fn reduce_nat_dec_le(args: &[&Expr]) -> Option<Expr> {
    if args.len() < 2 {
        return None;
    }
    let a = get_nat_val(args[0])?;
    let b = get_nat_val(args[1])?;
    Some(crate::env::native_reducers::mk_nat_le_dec(
        args[0],
        args[1],
        a <= b,
    ))
}

/// Native reducer for `Nat.decLt : (a b : Nat) → Decidable (a < b)`.
pub(crate) fn reduce_nat_dec_lt(args: &[&Expr]) -> Option<Expr> {
    if args.len() < 2 {
        return None;
    }
    let a = get_nat_val(args[0])?;
    let b = get_nat_val(args[1])?;
    Some(crate::env::native_reducers::mk_nat_lt_dec(
        args[0],
        args[1],
        a < b,
    ))
}

// --- decide reducer ---

/// Native reducer for `decide : {p : Prop} → [inst : Decidable p] → Bool`.
///
/// In Lean 4, `decide` is defined as:
/// ```text
/// @[inline] def decide (p : Prop) [inst : Decidable p] : Bool :=
///   match inst with
///   | isTrue _  => true
///   | isFalse _ => false
/// ```
///
/// When the `Decidable` instance is already concrete (isTrue/isFalse),
/// we can skip the delta/iota reduction and return Bool.true/false directly.
///
/// Args: [p, inst] where p is the Prop and inst is the Decidable instance.
pub(crate) fn reduce_decide(args: &[&Expr]) -> Option<Expr> {
    if args.len() < 2 {
        return None;
    }
    // args[0] is the Prop, args[1] is the Decidable instance
    let result = get_decidable_val(args[1])?;
    if result {
        Some(Expr::const_(BOOL_TRUE.clone(), vec![]))
    } else {
        Some(Expr::const_(BOOL_FALSE.clone(), vec![]))
    }
}

// --- Decidable combinators ---

/// Extract `(is_true, witness)` from a reduced `@Decidable.isX prop h`.
fn decidable_witness(e: &Expr) -> Option<(bool, Expr)> {
    let head = e.get_app_fn();
    let ExprKind::Const(name, _) = head.kind() else {
        return None;
    };
    let is_true = if *name == *DECIDABLE_IS_TRUE {
        true
    } else if *name == *DECIDABLE_IS_FALSE {
        false
    } else {
        return None;
    };
    let h = (*e.get_app_args().get(1)?).clone(); // @Decidable.isX prop h ↦ h
    Some((is_true, h))
}

/// Native reducer for `instDecidableAnd` — SOUND (reuses inner witnesses).
///
/// `{p q : Prop} → [dp : Decidable p] → [dq : Decidable q] → Decidable (p ∧ q)`
/// Args: [p, q, dp, dq]
pub(crate) fn reduce_inst_decidable_and(args: &[&Expr]) -> Option<Expr> {
    if args.len() < 4 {
        return None;
    }
    let (p, q) = (args[0], args[1]);
    let (dp, hp) = decidable_witness(args[2])?;
    let (dq, hq) = decidable_witness(args[3])?;
    let and_pq = Expr::apps(
        Expr::const_(Name::from_string("And"), vec![]),
        [p.clone(), q.clone()],
    );
    if dp && dq {
        // isTrue (And.intro hp hq)
        let pf = Expr::apps(
            Expr::const_(Name::from_string("And.intro"), vec![]),
            [p.clone(), q.clone(), hp, hq],
        );
        Some(Expr::apps(
            Expr::const_(DECIDABLE_IS_TRUE.clone(), vec![]),
            [and_pq, pf],
        ))
    } else if !dp {
        // isFalse (fun (h : p ∧ q) => hp (And.left h))   [hp : ¬p]
        let left = Expr::apps(
            Expr::const_(Name::from_string("And.left"), vec![]),
            [p.clone(), q.clone(), Expr::bvar(0)],
        );
        let body = Expr::app(hp, left);
        let disproof = Expr::lam(crate::expr::BinderInfo::Default, and_pq.clone(), body);
        Some(Expr::apps(
            Expr::const_(DECIDABLE_IS_FALSE.clone(), vec![]),
            [and_pq, disproof],
        ))
    } else {
        // dq false: isFalse (fun (h : p ∧ q) => hq (And.right h))   [hq : ¬q]
        let right = Expr::apps(
            Expr::const_(Name::from_string("And.right"), vec![]),
            [p.clone(), q.clone(), Expr::bvar(0)],
        );
        let body = Expr::app(hq, right);
        let disproof = Expr::lam(crate::expr::BinderInfo::Default, and_pq.clone(), body);
        Some(Expr::apps(
            Expr::const_(DECIDABLE_IS_FALSE.clone(), vec![]),
            [and_pq, disproof],
        ))
    }
}

/// Native reducer for `instDecidableOr` — SOUND (reuses inner witnesses).
///
/// `{p q : Prop} → [dp : Decidable p] → [dq : Decidable q] → Decidable (p ∨ q)`
/// Args: [p, q, dp, dq]
pub(crate) fn reduce_inst_decidable_or(args: &[&Expr]) -> Option<Expr> {
    if args.len() < 4 {
        return None;
    }
    let (p, q) = (args[0], args[1]);
    let (dp, hp) = decidable_witness(args[2])?;
    let (dq, hq) = decidable_witness(args[3])?;
    let or_pq = Expr::apps(
        Expr::const_(Name::from_string("Or"), vec![]),
        [p.clone(), q.clone()],
    );
    if dp {
        // isTrue (Or.inl hp)
        let pf = Expr::apps(
            Expr::const_(Name::from_string("Or.inl"), vec![]),
            [p.clone(), q.clone(), hp],
        );
        Some(Expr::apps(
            Expr::const_(DECIDABLE_IS_TRUE.clone(), vec![]),
            [or_pq, pf],
        ))
    } else if dq {
        // isTrue (Or.inr hq)
        let pf = Expr::apps(
            Expr::const_(Name::from_string("Or.inr"), vec![]),
            [p.clone(), q.clone(), hq],
        );
        Some(Expr::apps(
            Expr::const_(DECIDABLE_IS_TRUE.clone(), vec![]),
            [or_pq, pf],
        ))
    } else {
        // both false: isFalse (fun (h : p ∨ q) =>
        //   @Or.rec p q (fun _ => False) hp hq h)   [hp : ¬p, hq : ¬q]
        let body = Expr::apps(
            Expr::const_(Name::from_string("Or.rec"), vec![]),
            [
                p.clone(),
                q.clone(),
                Expr::lam(
                    crate::expr::BinderInfo::Default,
                    or_pq.clone(),
                    Expr::const_(Name::from_string("False"), vec![]),
                ),
                hp,
                hq,
                Expr::bvar(0),
            ],
        );
        let disproof = Expr::lam(crate::expr::BinderInfo::Default, or_pq.clone(), body);
        Some(Expr::apps(
            Expr::const_(DECIDABLE_IS_FALSE.clone(), vec![]),
            [or_pq, disproof],
        ))
    }
}

/// Native reducer for `instDecidableNot`.
///
/// `{p : Prop} → [dp : Decidable p] → Decidable (¬p)`
///
/// Args: [p, dp]
pub(crate) fn reduce_inst_decidable_not(args: &[&Expr]) -> Option<Expr> {
    if args.len() < 2 {
        return None;
    }
    // SOUND: reuse the inner decision's REAL proof — no sorry, no new lemma.
    //   inner = @Decidable.isFalse p h  (h : ¬p)  ⟹  ¬p holds:
    //     @Decidable.isTrue (Not p) h
    //   inner = @Decidable.isTrue  p h  (h : p)   ⟹  ¬p is false:
    //     @Decidable.isFalse (Not p) (fun (hnp : Not p) => hnp h)
    let p = args[0];
    let inner = args[1];
    let head = inner.get_app_fn();
    let ExprKind::Const(name, _) = head.kind() else {
        return None;
    };
    let inner_args = inner.get_app_args();
    let h = (*inner_args.get(1)?).clone(); // @Decidable.isX p h ↦ h
    let not_p = Expr::app(Expr::const_(Name::from_string("Not"), vec![]), p.clone());
    if *name == *DECIDABLE_IS_FALSE {
        // h : ¬p ≡ Not p — reuse directly.
        Some(Expr::apps(
            Expr::const_(DECIDABLE_IS_TRUE.clone(), vec![]),
            [not_p, h],
        ))
    } else if *name == *DECIDABLE_IS_TRUE {
        // disproof of ¬p:  fun (hnp : Not p) => hnp h    (hnp = BVar 0, h closed)
        let disproof = Expr::lam(
            crate::expr::BinderInfo::Default,
            not_p.clone(),
            Expr::app(Expr::bvar(0), h),
        );
        Some(Expr::apps(
            Expr::const_(DECIDABLE_IS_FALSE.clone(), vec![]),
            [not_p, disproof],
        ))
    } else {
        None
    }
}

// --- Int decidable reducers ---

/// Native reducer for `Int.decEq : (a b : Int) → Decidable (a = b)`.
/// Extract `(is_ofNat, nat_arg)` from a concrete `Int.ofNat n` / `Int.negSucc n`.
fn int_ctor_and_arg(e: &Expr) -> Option<(bool, Expr)> {
    let head = e.get_app_fn();
    let cargs = e.get_app_args();
    if let ExprKind::Const(name, _) = head.kind() {
        if cargs.len() == 1 {
            if name.to_string() == "Int.ofNat" {
                return Some((true, (*cargs[0]).clone()));
            }
            if name.to_string() == "Int.negSucc" {
                return Some((false, (*cargs[0]).clone()));
            }
        }
    }
    None
}

/// Build a SOUND `@Decidable.isFalse (@Eq Int a b) <proof>` for distinct Int
/// literals — NO `sorryAx`. Three cases via `Int.noConfusion`:
///  - same constructor (`ofNat na`/`ofNat nb` or `negSucc na`/`negSucc nb`):
///    `Int.noConfusion` extracts `na = nb`, refuted by `Nat.ne_of_beq_false`.
///  - distinct constructors: `Int.noConfusion` δι-reduces to `False` directly.
fn mk_int_dec_is_false(a: &Expr, b: &Expr) -> Option<Expr> {
    let one = crate::level::Level::succ(crate::level::Level::zero());
    let zero = crate::level::Level::zero();
    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let bool_ty = Expr::const_(Name::from_string("Bool"), vec![]);
    let false_c = Expr::const_(Name::from_string("False"), vec![]);
    let eq_prop = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![one.clone()]),
        [int_ty.clone(), a.clone(), b.clone()],
    );
    let (ca, na) = int_ctor_and_arg(a)?;
    let (cb, nb) = int_ctor_and_arg(b)?;
    let body = if ca == cb {
        // same ctor: @Int.noConfusion.{0} (Eq Nat na nb) a b h (fun e => e) : na = nb
        let eq_nanb = Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![one.clone()]),
            [nat.clone(), na.clone(), nb.clone()],
        );
        let id_cont = Expr::lam(
            crate::expr::BinderInfo::Default,
            eq_nanb.clone(),
            Expr::bvar(0),
        );
        let field_eq = Expr::apps(
            Expr::const_(Name::from_string("Int.noConfusion"), vec![zero]),
            [
                eq_nanb.clone(),
                a.clone(),
                b.clone(),
                Expr::bvar(0),
                id_cont,
            ],
        );
        let beq = Expr::apps(
            Expr::const_(Name::from_string("Nat.beq"), vec![]),
            [na.clone(), nb.clone()],
        );
        let refl = Expr::apps(
            Expr::const_(Name::from_string("Eq.refl"), vec![one.clone()]),
            [bool_ty, beq],
        );
        let ne = Expr::apps(
            Expr::const_(Name::from_string("Nat.ne_of_beq_false"), vec![]),
            [na, nb, refl],
        );
        Expr::app(ne, field_eq)
    } else {
        // distinct ctors: @Int.noConfusion.{0} False a b h : False
        Expr::apps(
            Expr::const_(Name::from_string("Int.noConfusion"), vec![zero]),
            [false_c, a.clone(), b.clone(), Expr::bvar(0)],
        )
    };
    let disproof = Expr::lam(crate::expr::BinderInfo::Default, eq_prop.clone(), body);
    Some(Expr::apps(
        Expr::const_(Name::from_string("Decidable.isFalse"), vec![]),
        [eq_prop, disproof],
    ))
}

pub(crate) fn reduce_int_dec_eq(args: &[&Expr]) -> Option<Expr> {
    if args.len() < 2 {
        return None;
    }
    let a = get_int_val(args[0])?;
    let b = get_int_val(args[1])?;
    if a == b {
        Some(mk_dec_is_true(&INT_NAME, args[0]))
    } else {
        // Sound disproof for concrete Int constructors; decline (don't emit a
        // sorry) if the operands aren't in `ofNat`/`negSucc` form.
        mk_int_dec_is_false(args[0], args[1])
    }
}

/// Native reducer for `Int.decLe : (a b : Int) → Decidable (a ≤ b)`.
///
/// `Int` ordering is not yet backed by an in-kernel order proof, so this
/// reducer *declines* (returns `None`) rather than laundering a
/// `Decidable.isTrue/isFalse sorryAx` witness through the trusted kernel — the
/// kernel falls back to ordinary iota reduction. (Contrast the *equality*
/// reducer `reduce_int_dec_eq`, which has a real `Int.noConfusion`-based
/// disproof.) Sound by omission.
pub(crate) fn reduce_int_dec_le(_args: &[&Expr]) -> Option<Expr> {
    None
}

/// Native reducer for `Int.decLt : (a b : Int) → Decidable (a < b)`. Declines
/// for the same soundness reason as [`reduce_int_dec_le`].
pub(crate) fn reduce_int_dec_lt(_args: &[&Expr]) -> Option<Expr> {
    None
}

/// Register all extended Decidable native reducers on the environment.
impl Environment {
    pub(crate) fn init_decidable_ext_native_reducers(&mut self) {
        // Nat ordering
        self.register_native_reducer(names::NAT_DEC_LE.clone(), reduce_nat_dec_le);
        self.register_native_reducer(names::NAT_DEC_LT.clone(), reduce_nat_dec_lt);

        // decide
        self.register_native_reducer(names::DECIDE.clone(), reduce_decide);
        self.register_native_reducer(names::DECIDABLE_DECIDE.clone(), reduce_decide);

        // Decidable combinators
        self.register_native_reducer(names::INST_DECIDABLE_AND.clone(), reduce_inst_decidable_and);
        self.register_native_reducer(names::INST_DECIDABLE_OR.clone(), reduce_inst_decidable_or);
        self.register_native_reducer(names::INST_DECIDABLE_NOT.clone(), reduce_inst_decidable_not);

        // Int decidable ops
        self.register_native_reducer(names::INT_DEC_EQ.clone(), reduce_int_dec_eq);
        self.register_native_reducer(names::INT_DEC_LE.clone(), reduce_int_dec_le);
        self.register_native_reducer(names::INT_DEC_LT.clone(), reduce_int_dec_lt);
        self.register_native_reducer(names::INST_DECIDABLE_EQ_INT.clone(), reduce_int_dec_eq);
        self.register_native_reducer(names::INST_DECIDABLE_LE_INT.clone(), reduce_int_dec_le);
        self.register_native_reducer(names::INST_DECIDABLE_LT_INT.clone(), reduce_int_dec_lt);
    }
}
