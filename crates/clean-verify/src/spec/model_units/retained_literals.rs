// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The RETAINED LITERALS of every model declaration moved into a `.clean` unit.
//!
//! These are the exact Rust string literals `add_foundation_types` and
//! `add_expr_model` used to hand to `add_inductive` / `add_recursive_def`
//! before embed-memo W1 moved them to `crates/clean-verify/spec/*.clean`
//! (`designs/2026-08-28-embedding-the-kernel-model.md`, Step 1). They exist
//! for ONE purpose: the fidelity oracle in `model_units::tests` registers each
//! unit twice — once from the `.clean` file, once from this table — through the
//! SAME `add_inductive` / `add_recursive_def` path, and asserts the two kernel
//! environments and spec-definition tables are identical. They are not a
//! fallback and no production build reads them.
//!
//! GENERATED from the pre-move `.rs` files by the W1 extractor; the source and
//! description strings are byte-identical to the originals (Rust string
//! semantics applied: `\`-newline continuations already joined).
//! The Nat.pred explicit-motive marker is repaired in both paths on 2026-11-14;
//! the statement, body modulo that marker and strict fidelity comparison remain.

use super::{LiteralKind, ModelUnit, RetainedLiteral};

/// Units that never existed as a Rust string literal, so they have no retained
/// literal and are not the W1 migration oracle's subject. Pinned rather than
/// inferred from an empty table: see the `None` arm below.
pub(crate) const BORN_AS_FILE: &[ModelUnit] = &[ModelUnit::FoundationAgreement];

/// The retained literals of a unit, in the order the Rust code registered them.
pub(crate) fn of(unit: ModelUnit) -> Option<&'static [RetainedLiteral]> {
    match unit {
        ModelUnit::FoundationEq => Some(FOUNDATION_EQ),
        ModelUnit::FoundationProd => Some(FOUNDATION_PROD),
        ModelUnit::FoundationNat => Some(FOUNDATION_NAT),
        ModelUnit::FoundationOrder => Some(FOUNDATION_ORDER),
        ModelUnit::FoundationEmptyAnd => Some(FOUNDATION_EMPTY_AND),
        ModelUnit::ExprModelCore => Some(EXPR_MODEL_CORE),
        ModelUnit::ExprModelSpine => Some(EXPR_MODEL_SPINE),
        // Born as a file: there is no pre-move literal, because this unit never
        // lived as a Rust string. `None` rather than an empty slice, because an
        // EMPTY SLICE is exactly what a botched edit to one of the seven tables
        // above would also produce -- and every consumer would then treat a MOVED
        // unit as born-as-file, comparing the file build against itself while the
        // oracle still printed green. Absence is typed, and `BORN_AS_FILE` pins
        // which units are allowed to have it.
        ModelUnit::FoundationAgreement => None,
    }
}

/// Retained literals of `spec/foundation_eq.clean`.
pub(crate) const FOUNDATION_EQ: &[RetainedLiteral] = &[RetainedLiteral {
    kind: LiteralKind::Inductive,
    source: r"inductive Eq (α : Sort u) : α → α → Prop
| refl : forall (a : α), Eq α a a",
    description: r"Propositional equality: Eq α a b means a and b are provably equal.",
}];

/// Retained literals of `spec/foundation_prod.clean`.
pub(crate) const FOUNDATION_PROD: &[RetainedLiteral] = &[RetainedLiteral {
    kind: LiteralKind::Inductive,
    source: r"inductive ProdType (α : Type) (β : Type) : Type
| mk : α → β → ProdType α β",
    description: r"Product type: ProdType α β is a pair of α and β.",
}];

/// Retained literals of `spec/foundation_nat.clean`.
pub(crate) const FOUNDATION_NAT: &[RetainedLiteral] = &[
    RetainedLiteral {
        kind: LiteralKind::Inductive,
        source: r"inductive Nat : Type
| zero : Nat
| succ : Nat → Nat",
        description: r"Natural numbers. Used for universe levels, de Bruijn indices, and arithmetic.",
    },
    RetainedLiteral {
        kind: LiteralKind::RecursiveDef,
        source: r"def Nat.add (n : Nat) (m : Nat) : Nat := match m with
| Nat.zero => n
| Nat.succ m' => Nat.succ (Nat.add n m')",
        description: r"Addition on natural numbers.",
    },
    RetainedLiteral {
        kind: LiteralKind::RecursiveDef,
        source: r"def Nat.pred (n : Nat) : Nat := @Nat.rec (fun (_ : Nat) => Nat) Nat.zero (fun (m : Nat) (_ : Nat) => m) n",
        description: r"Predecessor on natural numbers.",
    },
    RetainedLiteral {
        kind: LiteralKind::RecursiveDef,
        source: r"def Nat.sub (a : Nat) (b : Nat) : Nat := match b with
| Nat.zero => a
| Nat.succ b' => Nat.pred (Nat.sub a b')",
        description: r"Subtraction on natural numbers (truncated to zero).",
    },
];

/// Retained literals of `spec/foundation_order.clean`.
pub(crate) const FOUNDATION_ORDER: &[RetainedLiteral] = &[
    RetainedLiteral {
        kind: LiteralKind::Inductive,
        source: r"inductive Lt : Nat → Nat → Type
| zero_lt_succ : forall (n : Nat), Lt Nat.zero (Nat.succ n)
| succ_lt_succ : forall (n : Nat) (m : Nat), Lt n m → Lt (Nat.succ n) (Nat.succ m)",
        description: r"Strict ordering on Nat. Lt n m means n < m. Inductive definition enables structural induction on ordering proofs.",
    },
    RetainedLiteral {
        kind: LiteralKind::Inductive,
        source: r"inductive Le : Nat → Nat → Prop
| refl : forall (n : Nat), Le n n
| step : forall (n : Nat) (m : Nat), Le n m → Le n (Nat.succ m)",
        description: r"Less-than-or-equal on natural numbers as an inductive relation.",
    },
];

/// Retained literals of `spec/foundation_empty_and.clean`.
pub(crate) const FOUNDATION_EMPTY_AND: &[RetainedLiteral] = &[
    RetainedLiteral {
        kind: LiteralKind::Inductive,
        source: r"inductive Empty : Type",
        description: r"Uninhabited type. Used for constructor discrimination via large elimination.",
    },
    RetainedLiteral {
        kind: LiteralKind::Inductive,
        source: r"inductive AndType (A : Type) (B : Type) : Type
| intro : A → B → AndType A B",
        description: r"Proof-relevant conjunction: AndType A B holds when both A and B hold.",
    },
];

/// Retained literals of `spec/expr_model_core.clean`.
pub(crate) const EXPR_MODEL_CORE: &[RetainedLiteral] = &[
    RetainedLiteral {
        kind: LiteralKind::Inductive,
        source: r"inductive Name : Type
| anonymous : Name
| str : Name → Nat → Name",
        description: r"Kernel names for the current KExpr const fragment.",
    },
    RetainedLiteral {
        kind: LiteralKind::Inductive,
        source: r"inductive Level : Type
| zero : Level
| succ : Level → Level
| max : Level → Level → Level
| imax : Level → Level → Level
| param : Name → Level",
        description: r"Universe levels — the full production kernel Level algebra (zero|succ|max|imax|param Name).",
    },
    RetainedLiteral {
        kind: LiteralKind::Inductive,
        source: r"inductive ListType (α : Type) : Type
| nil : ListType α
| cons : α → ListType α → ListType α",
        description: r"Polymorphic lists used for const universe parameters.",
    },
    RetainedLiteral {
        kind: LiteralKind::Inductive,
        source: r"inductive KExpr : Type
| sort : Level → KExpr
| bvar : Nat → KExpr
| app : KExpr → KExpr → KExpr
| lam : KExpr → KExpr → KExpr
| pi : KExpr → KExpr → KExpr
| const : Name → ListType Level → KExpr
| let_ : KExpr → KExpr → KExpr → KExpr
| proj : Name → Nat → KExpr → KExpr
| lit : Nat → KExpr",
        description: r"Kernel expression type with 9 constructors: sort, bvar, app, lam, pi, const, let_, proj, lit. The lit payload uses literal_model's reversible Nat/String codec; literal_nat and literal_string are the typed literal constructors.",
    },
    RetainedLiteral {
        kind: LiteralKind::RecursiveDef,
        source: r"def lift_bvar_at (idx : Nat) (cutoff : Nat) (amount : Nat) : KExpr := @Nat.rec (fun _ => KExpr) (KExpr.bvar (Nat.add idx amount)) (fun _ _ => KExpr.bvar idx) (Nat.sub cutoff idx)",
        description: r"Compute lifted bvar: if idx >= cutoff, add amount; else keep. Part of #410.",
    },
    RetainedLiteral {
        kind: LiteralKind::RecursiveDef,
        source: r"def lift_at (e : KExpr) (cutoff : Nat) (amount : Nat) : KExpr := match e with
| KExpr.sort n => KExpr.sort n
| KExpr.bvar i => lift_bvar_at i cutoff amount
| KExpr.app f a => KExpr.app (lift_at f cutoff amount) (lift_at a cutoff amount)
| KExpr.lam ty body => KExpr.lam (lift_at ty cutoff amount) (lift_at body (Nat.succ cutoff) amount)
| KExpr.pi ty body => KExpr.pi (lift_at ty cutoff amount) (lift_at body (Nat.succ cutoff) amount)
| KExpr.const n us => KExpr.const n us
| KExpr.let_ ty val body => KExpr.let_ (lift_at ty cutoff amount) (lift_at val cutoff amount) (lift_at body (Nat.succ cutoff) amount)
| KExpr.proj s i sub => KExpr.proj s i (lift_at sub cutoff amount)
| KExpr.lit n => KExpr.lit n",
        description: r"Lift bound variables >= cutoff by amount. Part of #410. proj/lit: proj recurses, lit is a leaf.",
    },
    RetainedLiteral {
        kind: LiteralKind::RecursiveDef,
        source: r"def lift (e : KExpr) (amount : Nat) : KExpr := lift_at e Nat.zero amount",
        description: r"Lift all bound variables by amount (lift_at with cutoff 0). Part of #410.",
    },
    RetainedLiteral {
        kind: LiteralKind::RecursiveDef,
        source: r"def instantiate_bvar_geq (idx : Nat) (depth : Nat) (val : KExpr) : KExpr := @Nat.rec (fun _ => KExpr) (lift_at val Nat.zero depth) (fun _ _ => KExpr.bvar (Nat.sub idx (Nat.succ Nat.zero))) (Nat.sub idx depth)",
        description: r"Helper: if idx == depth, substitute with lifted val; if idx > depth, decrement. Part of #643.",
    },
    RetainedLiteral {
        kind: LiteralKind::RecursiveDef,
        source: r"def instantiate_bvar_at (idx : Nat) (depth : Nat) (val : KExpr) : KExpr := @Nat.rec (fun _ => KExpr) (instantiate_bvar_geq idx depth val) (fun _ _ => KExpr.bvar idx) (Nat.sub depth idx)",
        description: r"Helper: three-way comparison idx vs depth for bvar substitution. Part of #643.",
    },
    RetainedLiteral {
        kind: LiteralKind::RecursiveDef,
        source: r"def instantiate_at (body : KExpr) (val : KExpr) (depth : Nat) : KExpr := match body with
| KExpr.sort n => KExpr.sort n
| KExpr.bvar i => instantiate_bvar_at i depth val
| KExpr.app f a => KExpr.app (instantiate_at f val depth) (instantiate_at a val depth)
| KExpr.lam ty b => KExpr.lam (instantiate_at ty val depth) (instantiate_at b val (Nat.succ depth))
| KExpr.pi ty b => KExpr.pi (instantiate_at ty val depth) (instantiate_at b val (Nat.succ depth))
| KExpr.const n us => KExpr.const n us
| KExpr.let_ ty v b => KExpr.let_ (instantiate_at ty val depth) (instantiate_at v val depth) (instantiate_at b val (Nat.succ depth))
| KExpr.proj s i sub => KExpr.proj s i (instantiate_at sub val depth)
| KExpr.lit n => KExpr.lit n",
        description: r"Substitute val for BVar(depth), incrementing depth under binders. Part of #643. proj/lit: proj recurses, lit is a leaf.",
    },
    RetainedLiteral {
        kind: LiteralKind::RecursiveDef,
        source: r"def instantiate (body : KExpr) (val : KExpr) : KExpr := instantiate_at body val Nat.zero",
        description: r"Substitute val for BVar(0) (wrapper for instantiate_at). Part of #643.",
    },
];

/// Retained literals of `spec/expr_model_spine.clean`.
pub(crate) const EXPR_MODEL_SPINE: &[RetainedLiteral] = &[
    RetainedLiteral {
        kind: LiteralKind::RecursiveDef,
        source: r"def kapp_fn (e : KExpr) : KExpr := match e with
| KExpr.sort n => KExpr.sort n
| KExpr.bvar i => KExpr.bvar i
| KExpr.app f a => kapp_fn f
| KExpr.lam ty b => KExpr.lam ty b
| KExpr.pi ty b => KExpr.pi ty b
| KExpr.const n us => KExpr.const n us
| KExpr.let_ ty v b => KExpr.let_ ty v b
| KExpr.proj s i sub => KExpr.proj s i sub
| KExpr.lit n => KExpr.lit n",
        description: r"Head of an application spine: kapp_fn (app .. (app head a1) .. an) = head. Spine recognizer for the computational iota_step substrate. Part of #2859 (Increment A).",
    },
    RetainedLiteral {
        kind: LiteralKind::RecursiveDef,
        source: r"def kapp_arg_count (e : KExpr) : Nat := match e with
| KExpr.sort n => Nat.zero
| KExpr.bvar i => Nat.zero
| KExpr.app f a => Nat.succ (kapp_arg_count f)
| KExpr.lam ty b => Nat.zero
| KExpr.pi ty b => Nat.zero
| KExpr.const n us => Nat.zero
| KExpr.let_ ty v b => Nat.zero
| KExpr.proj s i sub => Nat.zero
| KExpr.lit n => Nat.zero",
        description: r"Argument count of an application spine: kapp_arg_count (app .. (app head a1) .. an) = n. Part of #2859 (Increment A).",
    },
    RetainedLiteral {
        kind: LiteralKind::RecursiveDef,
        source: r"def is_const_app (e : KExpr) : Bool := match e with
| KExpr.sort n => Bool.false
| KExpr.bvar i => Bool.false
| KExpr.app f a => is_const_app f
| KExpr.lam ty b => Bool.false
| KExpr.pi ty b => Bool.false
| KExpr.const n us => Bool.true
| KExpr.let_ ty v b => Bool.false
| KExpr.proj s i sub => Bool.false
| KExpr.lit n => Bool.false",
        description: r"Whether an application spine is headed by a const (recursor/constructor candidate). Part of #2859 (Increment A).",
    },
];
