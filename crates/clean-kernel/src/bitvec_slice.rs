// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Minimal fixed-width BitVec layer for the C1 `bvsub`/`bvadd` equality slice.
//!
//! # What this is (and is not)
//!
//! This is the *minimal* kernel vocabulary needed to **state** and **prove** the
//! narrow slice obligation
//!
//! ```text
//!   not( bvop(a, b) == bvop(a, b) )      bvop ∈ {bvsub, bvadd}, width 32
//! ```
//!
//! and have the producer's *consumed* bit-lemmas come out as **kernel theorems**,
//! not asserted axioms.
//!
//! The layer is deliberately small. It declares:
//!   * `BV : Type` — an opaque (uninterpreted) bitvector carrier sort.
//!   * `getBit : BV → Nat → Bool` — opaque bit-extraction.
//!   * `bvAdd, bvSub : BV → BV → BV` — opaque (uninterpreted) operations.
//!   * `bvEq : BV → BV → Prop` — a **real definition**: the finite `And`-chain of
//!     per-bit equalities `getBit x i = getBit y i` for `i ∈ [0, width)`.
//!
//! # Honesty: why opaque ops are NOT a trust leak for this slice
//!
//! `bvAdd`/`bvSub`/`getBit`/`BV` are *uninterpreted*. They carry **no axiom about
//! their behaviour** — they are signature symbols only. The slice obligation
//! `not(bvop(a,b) == bvop(a,b))` is UNSAT purely because the two sides are the
//! *same term*; the refutation never needs to know what `bvSub` computes. So:
//!   * The per-bit equality units `e_i = (getBit lhs i = getBit rhs i)` are proved
//!     by **reflexivity** — sound and non-vacuous precisely because `lhs` and `rhs`
//!     are syntactically identical (`bvSub a b` on both sides), mirroring the
//!     producer's gate-sharing (`L_i ≡ R_i` by variable identity).
//!   * The full-adder sum/carry/`Not`/const bit-lemmas the producer emits are NOT
//!     consumed by this slice's resolution chain (they only *define* the shared
//!     `Out` vars, which the refutation treats as opaque). We therefore neither
//!     prove nor assert them here — and we say so loudly in the reconstructor.
//!
//! Were the slice ever widened to a non-identical obligation (e.g. real
//! commutativity `bvadd(a,b) == bvadd(b,a)`), `bvAdd` could no longer be opaque and
//! the adder bit-lemmas WOULD have to be proved from a computational `bvAdd`
//! definition.
//!
//! # Successor: the SEMANTICALLY-REAL computational layer
//!
//! That non-reflexive case is no longer hypothetical. [`crate::bitvec_compute`]
//! gives the ops honest **computational definitions** (ripple-carry full-adder,
//! `bvSub a b := a + ¬b + 1`) and proves NON-REFLEXIVE identities
//! (`bvSub a a == bvZero`, `bvAdd a bvZero == a`, `bvAdd` commutativity) as
//! kernel theorems with axiom closure `⊆ FOUNDATIONAL_AXIOMS` — at a concrete
//! 4-bit width (honestly reported there). This `bitvec_slice` module is retained
//! as the opaque/reflexive path; new non-reflexive obligations should target
//! [`crate::bitvec_compute`].

use crate::name::Name;
use crate::{Declaration, EnvError, Environment, Expr, Level};

/// The slice bit width (32). Matches `ay_proof::bv_blast_export::SLICE_WIDTH`.
pub const BV_SLICE_WIDTH: u32 = 32;

/// Names of the declarations the slice layer registers.
pub mod names {
    /// The opaque bitvector carrier sort.
    pub const BV: &str = "Clean.BV";
    /// Opaque bit extraction `BV → Nat → Bool`.
    pub const GET_BIT: &str = "Clean.BV.getBit";
    /// Opaque addition `BV → BV → BV`.
    pub const BV_ADD: &str = "Clean.BV.bvAdd";
    /// Opaque subtraction `BV → BV → BV`.
    pub const BV_SUB: &str = "Clean.BV.bvSub";
    /// Defined per-bit equality predicate `BV → BV → Prop`.
    pub const BV_EQ: &str = "Clean.BV.bvEq";
}

fn bv_ty() -> Expr {
    Expr::const_str(names::BV)
}

fn nat_ty() -> Expr {
    Expr::const_str("Nat")
}

fn bool_ty() -> Expr {
    Expr::const_str("Bool")
}

/// `getBit x (i : Nat) : Bool`.
pub fn get_bit(x: Expr, bit: u32) -> Expr {
    Expr::apps(
        Expr::const_str(names::GET_BIT),
        [x, Expr::nat_lit(u64::from(bit))],
    )
}

/// `bvSub x y : BV` (or `bvAdd`, selected by `add`).
pub fn bv_binop(add: bool, x: Expr, y: Expr) -> Expr {
    let head = if add {
        Expr::const_str(names::BV_ADD)
    } else {
        Expr::const_str(names::BV_SUB)
    };
    Expr::apps(head, [x, y])
}

/// `@Eq.{1} Bool (getBit x bit) (getBit y bit) : Prop` — the per-bit equality
/// proposition `e_bit`.
pub fn bit_eq_prop(x: &Expr, y: &Expr, bit: u32) -> Expr {
    let u1 = Level::succ(Level::zero());
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![u1]),
        [bool_ty(), get_bit(x.clone(), bit), get_bit(y.clone(), bit)],
    )
}

/// `@Eq.refl.{1} Bool (getBit x bit) : @Eq Bool (getBit x bit) (getBit x bit)`.
///
/// A kernel proof of the per-bit equality `e_bit` **when `x` and `y` are the same
/// term**. The reconstructor only calls this for the identical-operand slice, so
/// the reflexivity proof is exactly the right (and sound) witness.
pub fn bit_eq_refl(x: &Expr, bit: u32) -> Expr {
    let u1 = Level::succ(Level::zero());
    Expr::apps(
        Expr::const_(Name::from_string("Eq.refl"), vec![u1]),
        [bool_ty(), get_bit(x.clone(), bit)],
    )
}

/// `bvEq x y : Prop` (the registered `Clean.BV.bvEq` applied to `x`, `y`).
pub fn bv_eq(x: Expr, y: Expr) -> Expr {
    Expr::apps(Expr::const_str(names::BV_EQ), [x, y])
}

/// `Not (bvEq lhs rhs)` — the negated slice goal (the assumption the refutation
/// discharges to `False`).
pub fn negated_goal(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(Expr::const_str("Not"), bv_eq(lhs, rhs))
}

/// Build the `And`-chain body of `bvEq x y` over `[0, width)` as an `Expr` whose
/// free de-Bruijn structure is closed (it references `x`, `y` as the given exprs).
///
/// `width == 0` is degenerate and yields `True`.
fn and_chain(x: &Expr, y: &Expr, width: u32) -> Expr {
    if width == 0 {
        return Expr::const_str("True");
    }
    // Right-associative: e_0 ∧ (e_1 ∧ (... ∧ e_{n-1})).
    let mut acc = bit_eq_prop(x, y, width - 1);
    for bit in (0..width - 1).rev() {
        acc = Expr::apps(
            Expr::const_(Name::from_string("And"), vec![]),
            [bit_eq_prop(x, y, bit), acc],
        );
    }
    acc
}

impl Environment {
    /// Register the minimal slice BitVec layer.
    ///
    /// Idempotent if the symbols are already present (returns the first
    /// [`EnvError::DuplicateName`] otherwise — callers building a fresh env should
    /// call this exactly once). Requires `Eq`, `Bool`, `Nat`, `And`, `True`/`False`
    /// to be initialized first; this method initializes them if absent.
    ///
    /// # Errors
    /// Propagates any [`EnvError`] from declaration insertion / kernel checking.
    pub fn init_bv_slice(&mut self) -> Result<(), EnvError> {
        self.init_eq()?;
        self.init_bool()?;
        self.init_nat()?;
        self.init_and()?;
        self.init_true_false()?;

        let type0 = Expr::type_();

        // BV : Type   (opaque uninterpreted carrier)
        // SOUNDNESS: uninterpreted sort symbol — carries no behavioural axiom.
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(names::BV),
            level_params: vec![],
            type_: type0,
        })?;

        // getBit : BV → Nat → Bool   (opaque)
        // SOUNDNESS: uninterpreted extraction symbol; no behavioural axiom.
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(names::GET_BIT),
            level_params: vec![],
            type_: Expr::arrow(bv_ty(), Expr::arrow(nat_ty(), bool_ty())),
        })?;

        // bvAdd, bvSub : BV → BV → BV   (opaque uninterpreted operations)
        for op in [names::BV_ADD, names::BV_SUB] {
            // SOUNDNESS: uninterpreted operation symbol; no behavioural axiom.
            self.add_decl(Declaration::Axiom {
                name: Name::from_string(op),
                level_params: vec![],
                type_: Expr::arrow(bv_ty(), Expr::arrow(bv_ty(), bv_ty())),
            })?;
        }

        // bvEq : BV → BV → Prop := fun x y => And (getBit x 0 = getBit y 0) (...)
        let x = Expr::bvar(1);
        let y = Expr::bvar(0);
        let body = and_chain(&x, &y, BV_SLICE_WIDTH);
        let value = Expr::lam(
            crate::BinderInfo::Default,
            bv_ty(),
            Expr::lam(crate::BinderInfo::Default, bv_ty(), body),
        );
        self.add_decl(Declaration::Definition {
            name: Name::from_string(names::BV_EQ),
            level_params: vec![],
            type_: Expr::arrow(bv_ty(), Expr::arrow(bv_ty(), Expr::prop())),
            value,
            is_reducible: true,
        })?;

        Ok(())
    }
}

#[cfg(test)]
#[path = "bitvec_slice_tests.rs"]
mod tests;
