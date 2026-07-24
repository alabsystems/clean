// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Name handling and trivial structure detection for monomorphization.

use clean_kernel::{Environment, Expr, ExprKind, Name};

use super::is_type_former_type;

/// Information about a trivial structure (single constructor, single relevant field).
///
/// A trivial structure has the same runtime representation as its single relevant field,
/// so pattern matching can be eliminated by direct assignment.
#[derive(Clone, Debug)]
pub struct TrivialStructureInfo {
    /// Name of the single constructor
    pub ctor_name: Name,
    /// Number of type parameters to the inductive
    pub num_params: u32,
    /// Index of the computationally relevant field (0-based among all fields)
    pub field_idx: usize,
}

/// Check if a type is a runtime builtin type.
///
/// Runtime builtin types have special handling in the compiler and should not
/// be treated as trivial structures.
fn is_runtime_builtin_type(name: &Name) -> bool {
    *name == special_names::string_()
        || *name == special_names::uint8_()
        || *name == special_names::uint16_()
        || *name == special_names::uint32_()
        || *name == special_names::uint64_()
        || *name == Name::from_string("USize")
        || *name == Name::from_string("Float")
        || *name == Name::from_string("Float32")
        || *name == special_names::thunk_()
        || *name == special_names::task_()
        || *name == special_names::array_()
        || *name == special_names::byte_array_()
        || *name == special_names::float_array_()
        || *name == special_names::nat_()
        || *name == special_names::int_()
}

/// Peel every `Pi` binder (and transparent `MData`) off a type expression,
/// returning the final codomain.
fn final_codomain(mut ty: &Expr) -> &Expr {
    loop {
        match ty.kind() {
            ExprKind::Pi(_, _, body) => ty = body.as_ref(),
            ExprKind::MData(_, inner) => ty = inner.as_ref(),
            _ => return ty,
        }
    }
}

/// Does `base` (a type expression with its own Pi binders already peeled)
/// live in `Prop`? Decided WITHOUT inference on the (possibly open) `base`:
/// `SProp` directly, or the head constant's DECLARED type — closed by
/// construction — finally lands in `Sort 0` (`Nat.lt`, `Or`, `Eq`, …).
/// `BVar`-headed bases (dependent motives) decline, fail-closed.
fn base_lands_in_prop(base: &Expr, env: &Environment) -> bool {
    if matches!(base.kind(), ExprKind::SProp) {
        return true;
    }
    let head = base.get_app_fn();
    let ExprKind::Const(head_name, _) = head.kind() else {
        return false;
    };
    let Some(head_info) = env.get_const(head_name) else {
        return false;
    };
    let head_codomain = final_codomain(&head_info.type_);
    matches!(head_codomain.kind(), ExprKind::Sort(level) if level.is_zero())
        || matches!(head_codomain.kind(), ExprKind::SProp)
}

/// Check if a constructor field type is computationally irrelevant.
///
/// A field is irrelevant if its type is:
/// - A type-former (Sort, Type, Prop, or Pi returning a sort)
/// - SProp (strict propositions)
/// - A Prop, recognized through the head constant's DECLARED type
///   (`isLt : n < bound` — head `Nat.lt : Nat → Nat → Prop`). The old
///   purely syntactic check missed exactly these, so `Fin`/`Char` (one
///   value field + one proof field) were never trivial structures: their
///   constructors allocated real cells while the C5b scalar-carrier world
///   flows their values as bare scalars — `Fin.val` read a ctor field out
///   of a tagged `Nat` (R3). The head-constant route needs no inference on
///   the open field domain, so it is exact, fail-closed on `BVar` heads.
fn is_field_type_irrelevant(ty: &Expr, env: &Environment) -> bool {
    if is_type_former_type(ty) || matches!(ty.kind(), ExprKind::SProp) {
        return true;
    }
    // Proof fields: `h : n < bound`, `valid : Nat.isValidChar n`, and
    // proof-FUNCTION fields (a Pi into a Prop).
    base_lands_in_prop(final_codomain(ty), env)
}

/// Analyze constructor fields for computational relevance.
///
/// Walks the constructor's Pi telescope, skipping `num_params` parameter
/// binders, then checks each of the `num_fields` field binder domains
/// for irrelevance via [`is_field_type_irrelevant`].
///
/// Returns `Some((count, idx))` where `count` is the number of relevant
/// fields and `idx` is the 0-based field index of the last relevant field.
/// Returns `None` if the constructor type is malformed (not enough Pi binders).
fn count_relevant_fields(
    ctor_type: &Expr,
    num_params: u32,
    num_fields: u32,
    env: &Environment,
) -> Option<(usize, usize)> {
    let mut ty = ctor_type;

    // Skip parameter binders
    for _ in 0..num_params {
        match ty.kind() {
            ExprKind::Pi(_, _, body) => ty = body.as_ref(),
            _ => return None,
        }
    }

    let mut relevant_count = 0;
    let mut relevant_idx = 0;

    // Check each field binder
    for field_idx in 0..num_fields as usize {
        match ty.kind() {
            ExprKind::Pi(_, domain, body) => {
                if !is_field_type_irrelevant(domain, env) {
                    relevant_count += 1;
                    relevant_idx = field_idx;
                }
                ty = body.as_ref();
            }
            _ => return None,
        }
    }

    Some((relevant_count, relevant_idx))
}

/// Check if a type is a trivial structure.
///
/// A trivial structure is an inductive type that:
/// - Is not a runtime builtin type (those have special handlers)
/// - Has exactly one constructor
/// - Is not recursive
/// - The constructor has exactly one computationally relevant field
///   (other fields are types or proofs)
///
/// Trivial structures have the same runtime representation as their single
/// relevant field, so pattern matching can be eliminated by direct assignment.
///
/// # Arguments
/// * `type_name` - Name of the inductive type to check
/// * `env` - Environment for looking up type information
///
/// # Returns
/// `Some(TrivialStructureInfo)` if the type is trivial, `None` otherwise.
pub fn has_trivial_structure(type_name: &Name, env: &Environment) -> Option<TrivialStructureInfo> {
    // Exclude runtime builtin types - they have special handlers
    if is_runtime_builtin_type(type_name) {
        return None;
    }

    // Look up the inductive type
    let ind_val = env.get_inductive(type_name)?;

    // Must have exactly one constructor
    if ind_val.constructor_names.len() != 1 {
        return None;
    }

    // Must not be recursive
    if ind_val.is_recursive {
        return None;
    }

    let ctor_name = &ind_val.constructor_names[0];
    let ctor_val = env.get_constructor(ctor_name)?;

    // Analyze field types for computational relevance.
    // Fields carrying types (Sort, Type) or proofs (Prop, SProp) are irrelevant.
    // A trivial structure needs exactly one relevant field.
    if let Some((relevant_count, relevant_idx)) = count_relevant_fields(
        &ctor_val.type_,
        ctor_val.num_params,
        ctor_val.num_fields,
        env,
    ) {
        if relevant_count == 1 {
            return Some(TrivialStructureInfo {
                ctor_name: ctor_name.clone(),
                num_params: ind_val.num_params,
                field_idx: relevant_idx,
            });
        }
        return None;
    }

    // Fallback: if the constructor type is not a proper Pi telescope (e.g.,
    // simplified type in tests or malformed .olean data), fall back to the
    // simple heuristic: single field is always relevant.
    if ctor_val.num_fields == 1 {
        return Some(TrivialStructureInfo {
            ctor_name: ctor_name.clone(),
            num_params: ind_val.num_params,
            field_idx: 0,
        });
    }

    None
}

/// Is `name` applied to `applied` arguments a PROOF (a value living in
/// `Prop`/`SProp`)?
///
/// Decided from the callee's DECLARED kernel type — closed by construction,
/// so no inference runs on the (possibly open) call site:
///
/// 1. Peel `applied` Pi binders off the declared type; fewer binders means
///    application through a dependent head — decline, fail-closed.
/// 2. Peel the REMAINING Pi binders: an under-applied proof function is
///    still a proof (a term of a Pi INTO a Prop).
/// 3. The base must be headed by a constant whose own declared type's final
///    codomain is `Sort 0` (`Nat.le`, `Or`, `Eq`, …) — i.e. the base is a
///    Prop. A base that is itself a `Sort` means `name` returns a TYPE
///    (a former, not a proof) and is left alone; `BVar`-headed bases
///    (dependent motives) decline, fail-closed.
///
/// Universe-polymorphic codomains (`Sort u`) are not `Sort 0` and decline —
/// under-erasure only, never over-erasure.
pub fn prop_valued_const(name: &Name, applied: usize, env: &Environment) -> bool {
    let Some(info) = env.get_const(name) else {
        return false;
    };
    // 1. Peel the applied binders.
    let mut ty = &info.type_;
    for _ in 0..applied {
        while let ExprKind::MData(_, inner) = ty.kind() {
            ty = inner.as_ref();
        }
        match ty.kind() {
            ExprKind::Pi(_, _, body) => ty = body.as_ref(),
            _ => return false,
        }
    }
    // 2. Peel any remaining binders (proof functions are proofs).
    let mut base = ty;
    loop {
        match base.kind() {
            ExprKind::Pi(_, _, body) => base = body.as_ref(),
            ExprKind::MData(_, inner) => base = inner.as_ref(),
            _ => break,
        }
    }
    // 3. The base must be a Prop: `SProp` directly, or headed by a constant
    //    whose declared type finally lands in `Sort 0`.
    if matches!(base.kind(), ExprKind::SProp) {
        return true;
    }
    let head = base.get_app_fn();
    let ExprKind::Const(head_name, _) = head.kind() else {
        return false;
    };
    let Some(head_info) = env.get_const(head_name) else {
        return false;
    };
    let mut head_ty = &head_info.type_;
    loop {
        match head_ty.kind() {
            ExprKind::Pi(_, _, body) => head_ty = body.as_ref(),
            ExprKind::MData(_, inner) => head_ty = inner.as_ref(),
            _ => break,
        }
    }
    matches!(head_ty.kind(), ExprKind::Sort(level) if level.is_zero())
        || matches!(head_ty.kind(), ExprKind::SProp)
}

/// Names that get special handling during monomorphization.
pub(crate) mod special_names {
    use clean_kernel::Name;

    pub fn decidable_is_true() -> Name {
        Name::from_string("Decidable.isTrue")
    }
    pub fn decidable_is_false() -> Name {
        Name::from_string("Decidable.isFalse")
    }
    pub fn decidable_decide() -> Name {
        Name::from_string("Decidable.decide")
    }
    pub fn quot_mk() -> Name {
        Name::from_string("Quot.mk")
    }
    pub fn quot_lc_inv() -> Name {
        Name::from_string("Quot.lcInv")
    }
    pub fn nat_succ() -> Name {
        Name::from_string("Nat.succ")
    }
    pub fn nat_add() -> Name {
        Name::from_string("Nat.add")
    }
    pub fn bool_true() -> Name {
        Name::from_string("Bool.true")
    }
    pub fn bool_false() -> Name {
        Name::from_string("Bool.false")
    }
    pub fn bool_() -> Name {
        Name::from_string("Bool")
    }
    pub fn decidable_() -> Name {
        Name::from_string("Decidable")
    }
    pub fn nat_zero() -> Name {
        Name::from_string("Nat.zero")
    }
    pub fn nat_() -> Name {
        Name::from_string("Nat")
    }
    pub fn nat_dec_eq() -> Name {
        Name::from_string("Nat.decEq")
    }
    pub fn nat_sub() -> Name {
        Name::from_string("Nat.sub")
    }
    pub fn int_() -> Name {
        Name::from_string("Int")
    }
    pub fn int_of_nat() -> Name {
        Name::from_string("Int.ofNat")
    }
    pub fn int_dec_lt() -> Name {
        Name::from_string("Int.decLt")
    }
    pub fn int_nat_abs() -> Name {
        Name::from_string("Int.natAbs")
    }
    pub fn int_neg_succ() -> Name {
        Name::from_string("Int.negSucc")
    }
    pub fn uint8_() -> Name {
        Name::from_string("UInt8")
    }
    pub fn uint16_() -> Name {
        Name::from_string("UInt16")
    }
    pub fn uint32_() -> Name {
        Name::from_string("UInt32")
    }
    pub fn uint64_() -> Name {
        Name::from_string("UInt64")
    }
    pub fn uint8_to_bit_vec() -> Name {
        Name::from_string("UInt8.toBitVec")
    }
    pub fn uint16_to_bit_vec() -> Name {
        Name::from_string("UInt16.toBitVec")
    }
    pub fn uint32_to_bit_vec() -> Name {
        Name::from_string("UInt32.toBitVec")
    }
    pub fn uint64_to_bit_vec() -> Name {
        Name::from_string("UInt64.toBitVec")
    }
    pub fn array_() -> Name {
        Name::from_string("Array")
    }
    pub fn array_to_list() -> Name {
        Name::from_string("Array.toList")
    }
    pub fn string_() -> Name {
        Name::from_string("String")
    }
    pub fn string_to_list() -> Name {
        Name::from_string("String.toList")
    }
    pub fn byte_array_() -> Name {
        Name::from_string("ByteArray")
    }
    pub fn byte_array_data() -> Name {
        Name::from_string("ByteArray.data")
    }
    pub fn float_array_() -> Name {
        Name::from_string("FloatArray")
    }
    pub fn float_array_data() -> Name {
        Name::from_string("FloatArray.data")
    }
    pub fn thunk_() -> Name {
        Name::from_string("Thunk")
    }
    pub fn thunk_get() -> Name {
        Name::from_string("Thunk.get")
    }
    pub fn task_() -> Name {
        Name::from_string("Task")
    }
    pub fn task_get() -> Name {
        Name::from_string("Task.get")
    }
}
