// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Native reducers for Init-specific high-frequency operations.
//!
//! These reducers short-circuit common Init definitions that otherwise spend
//! significant heartbeat budget on delta reduction during `.olean` checking:
//!
//! - `ite` / `dite`
//! - `Ord.compare` for `instOrdNat`
//! - `compareOfLessAndEq` on concrete Nat literals
//! - `List.length` / `List.getLast!` on concrete lists
//! - `Array.size` on concrete arrays

use crate::env::Environment;
use crate::expr::{BigNat, Expr, ExprKind, Literal};
use crate::name::Name;

/// Well-known names for Init native reducers.
pub(crate) mod names {
    use crate::name::Name;
    use std::sync::LazyLock;

    pub(crate) static ITE: LazyLock<Name> = LazyLock::new(|| Name::from_string("ite"));
    pub(crate) static DITE: LazyLock<Name> = LazyLock::new(|| Name::from_string("dite"));
    pub(crate) static ORD_COMPARE: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("Ord.compare"));
    pub(crate) static COMPARE_OF_LESS_AND_EQ: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("compareOfLessAndEq"));
    pub(crate) static LIST_LENGTH: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("List.length"));
    pub(crate) static LIST_GET_LAST_BANG: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("List.getLast!"));
    pub(crate) static ARRAY_SIZE: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("Array.size"));

    pub(crate) static DECIDABLE_IS_TRUE: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("Decidable.isTrue"));
    pub(crate) static DECIDABLE_IS_FALSE: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("Decidable.isFalse"));

    pub(crate) static INST_ORD_NAT: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("instOrdNat"));
    pub(crate) static NAT: LazyLock<Name> = LazyLock::new(|| Name::from_string("Nat"));

    pub(crate) static ORDERING_LT: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("Ordering.lt"));
    pub(crate) static ORDERING_EQ: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("Ordering.eq"));
    pub(crate) static ORDERING_GT: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("Ordering.gt"));

    pub(crate) static LIST_NIL: LazyLock<Name> = LazyLock::new(|| Name::from_string("List.nil"));
    pub(crate) static LIST_CONS: LazyLock<Name> = LazyLock::new(|| Name::from_string("List.cons"));
    pub(crate) static ARRAY_MK: LazyLock<Name> = LazyLock::new(|| Name::from_string("Array.mk"));
}

/// Extract a Nat literal as a `BigNat`.
fn get_nat_val(e: &Expr) -> Option<&BigNat> {
    match e.strip_mdata().kind() {
        ExprKind::Lit(Literal::Nat(n)) => Some(n),
        _ => None,
    }
}

/// Extract the head constant name of an application spine.
fn get_head_const_name(e: &Expr) -> Option<&Name> {
    let head = e.strip_mdata().get_app_fn().strip_mdata();
    if let ExprKind::Const(name, _) = head.kind() {
        return Some(name);
    }
    None
}

/// Extract the constructor tag of a `Decidable` value.
fn get_decidable_val(e: &Expr) -> Option<bool> {
    match get_head_const_name(e)? {
        name if *name == *names::DECIDABLE_IS_TRUE => Some(true),
        name if *name == *names::DECIDABLE_IS_FALSE => Some(false),
        _ => None,
    }
}

/// Extract both the boolean tag and proof payload from a `Decidable` value.
///
/// `Decidable.isTrue`/`isFalse` are constructors of the inductive
/// `Decidable (p : Prop)` with the single inductive PARAMETER `p` followed by
/// exactly one field (the proof `h : p` / `h : ¬p`):
///
/// ```text
/// Decidable.isTrue  : (p : Prop) → p   → Decidable p
/// Decidable.isFalse : (p : Prop) → ¬p  → Decidable p
/// ```
///
/// So a fully-applied constructor `Decidable.isTrue p h` has argument spine
/// `[p, h]`: the PROOF FIELD is `args[1]` (index = num_params = 1), **not**
/// `args[0]` (which is the parameter `p`). Earlier this took `args.first()`,
/// extracting the parameter instead of the proof — so `dite c (isTrue c h) t e`
/// computed `t c` instead of `t h` (Lean's `Decidable.rec` iota rule), making
/// auto-generated `dite`/`dif_pos`/`dif_neg` lemmas fail to type-check.
///
/// We require the constructor to be SATURATED (exactly param + field present)
/// before firing; an under-applied `Decidable.isTrue c` returns `None` so the
/// ordinary recursor/iota machinery handles it (and never mis-selects an arg).
fn get_decidable_proof(e: &Expr) -> Option<(bool, &Expr)> {
    let e = e.strip_mdata();
    let args = e.get_app_args();
    // [param, field]: field (the proof) is the last argument, at index 1.
    if args.len() != 2 {
        return None;
    }
    let proof = args[1];
    match get_head_const_name(e)? {
        name if *name == *names::DECIDABLE_IS_TRUE => Some((true, proof)),
        name if *name == *names::DECIDABLE_IS_FALSE => Some((false, proof)),
        _ => None,
    }
}

/// Extract the head constant name of an instance argument.
fn get_instance_name(e: &Expr) -> Option<&Name> {
    get_head_const_name(e)
}

/// Build an `Ordering` constructor expression.
fn mk_ordering(ord: std::cmp::Ordering) -> Expr {
    match ord {
        std::cmp::Ordering::Less => Expr::const_(names::ORDERING_LT.clone(), vec![]),
        std::cmp::Ordering::Equal => Expr::const_(names::ORDERING_EQ.clone(), vec![]),
        std::cmp::Ordering::Greater => Expr::const_(names::ORDERING_GT.clone(), vec![]),
    }
}

/// Count the length of a concrete `List` constructor spine.
fn get_concrete_list_len(list: &Expr) -> Option<u64> {
    let mut len = 0u64;
    let mut current = list.strip_mdata();

    loop {
        let head = current.get_app_fn().strip_mdata();
        let args = current.get_app_args();
        match head.kind() {
            ExprKind::Const(name, _) if *name == *names::LIST_NIL => return Some(len),
            ExprKind::Const(name, _) if *name == *names::LIST_CONS => {
                if args.len() < 3 {
                    return None;
                }
                len = len.checked_add(1)?;
                current = args[2].strip_mdata();
            }
            _ => return None,
        }
    }
}

/// Return the last element of a concrete non-empty `List` constructor spine.
fn get_concrete_list_last(list: &Expr) -> Option<Expr> {
    let mut current = list.strip_mdata();

    loop {
        let head = current.get_app_fn().strip_mdata();
        let args = current.get_app_args();
        match head.kind() {
            ExprKind::Const(name, _) if *name == *names::LIST_NIL => return None,
            ExprKind::Const(name, _) if *name == *names::LIST_CONS => {
                if args.len() < 3 {
                    return None;
                }
                let elem = args[1];
                let tail = args[2].strip_mdata();
                match get_head_const_name(tail) {
                    Some(name) if *name == *names::LIST_NIL => return Some(elem.clone()),
                    Some(name) if *name == *names::LIST_CONS => current = tail,
                    _ => return None,
                }
            }
            _ => return None,
        }
    }
}

/// Extract the list payload from a concrete `Array.mk` value.
fn get_array_list(array: &Expr) -> Option<&Expr> {
    let array = array.strip_mdata();
    let args = array.get_app_args();
    match get_head_const_name(array)? {
        name if *name == *names::ARRAY_MK && !args.is_empty() => args.last().copied(),
        _ => None,
    }
}

/// Native reducer for `ite`.
///
/// Signature: `{α : Sort u} → (c : Prop) → [Decidable c] → α → α → α`
/// Args: `[α, c, inst, then_val, else_val]`
fn reduce_ite(args: &[&Expr]) -> Option<Expr> {
    if args.len() < 5 {
        return None;
    }
    match get_decidable_val(args[2])? {
        true => Some(args[3].clone()),
        false => Some(args[4].clone()),
    }
}

/// Native reducer for `dite`.
///
/// Signature:
/// `{α : Sort u} → (c : Prop) → [Decidable c] → (c → α) → (¬c → α) → α`
/// Args: `[α, c, inst, then_fn, else_fn]`
fn reduce_dite(args: &[&Expr]) -> Option<Expr> {
    if args.len() < 5 {
        return None;
    }
    let (is_true, proof) = get_decidable_proof(args[2])?;
    if is_true {
        Some(Expr::app(args[3].clone(), proof.clone()))
    } else {
        Some(Expr::app(args[4].clone(), proof.clone()))
    }
}

/// Native reducer for `Ord.compare` with known `instOrdNat`.
///
/// Signature: `{α : Type u} → [Ord α] → α → α → Ordering`
/// Args: `[α, inst, a, b]`
fn reduce_ord_compare(args: &[&Expr]) -> Option<Expr> {
    if args.len() < 4 {
        return None;
    }
    let inst_name = get_instance_name(args[1])?;
    if *inst_name != *names::INST_ORD_NAT {
        return None;
    }
    let a = get_nat_val(args[2])?;
    let b = get_nat_val(args[3])?;
    Some(mk_ordering(a.cmp(b)))
}

/// Native reducer for `compareOfLessAndEq` on concrete Nat literals.
///
/// This is a common Init pattern for Nat ordering instances. The compared
/// values are the last two arguments in the application spine.
fn reduce_compare_of_less_and_eq(args: &[&Expr]) -> Option<Expr> {
    if args.len() < 2 {
        return None;
    }
    match args.first()?.strip_mdata().kind() {
        ExprKind::Const(name, _) if *name == *names::NAT => {}
        _ => return None,
    }
    let a = get_nat_val(args[args.len() - 2])?;
    let b = get_nat_val(args[args.len() - 1])?;
    Some(mk_ordering(a.cmp(b)))
}

/// Native reducer for `List.length` on concrete lists.
///
/// Signature: `{α : Type u} → List α → Nat`
/// Args: `[α, list]`
fn reduce_list_length(args: &[&Expr]) -> Option<Expr> {
    if args.len() < 2 {
        return None;
    }
    Some(Expr::nat_lit(get_concrete_list_len(args[1])?))
}

/// Native reducer for `List.getLast!` on concrete non-empty lists.
///
/// Signature: `{α : Type u} → [Inhabited α] → List α → α`
/// Args: `[α, inst, list]`
fn reduce_list_get_last_bang(args: &[&Expr]) -> Option<Expr> {
    if args.len() < 3 {
        return None;
    }
    get_concrete_list_last(args[2])
}

/// Native reducer for `Array.size` on concrete `Array.mk` values.
///
/// Signature: `{α : Type u} → Array α → Nat`
/// Args: `[α, array]`
fn reduce_array_size(args: &[&Expr]) -> Option<Expr> {
    if args.len() < 2 {
        return None;
    }
    let list = get_array_list(args[1])?;
    Some(Expr::nat_lit(get_concrete_list_len(list)?))
}

/// Register all Init-specific native reducers on the environment.
impl Environment {
    pub(crate) fn init_init_native_reducers(&mut self) {
        self.register_native_reducer(names::ITE.clone(), reduce_ite);
        self.register_native_reducer(names::DITE.clone(), reduce_dite);
        self.register_native_reducer(names::ORD_COMPARE.clone(), reduce_ord_compare);
        self.register_native_reducer(
            names::COMPARE_OF_LESS_AND_EQ.clone(),
            reduce_compare_of_less_and_eq,
        );
        self.register_native_reducer(names::LIST_LENGTH.clone(), reduce_list_length);
        self.register_native_reducer(names::LIST_GET_LAST_BANG.clone(), reduce_list_get_last_bang);
        self.register_native_reducer(names::ARRAY_SIZE.clone(), reduce_array_size);
    }
}
