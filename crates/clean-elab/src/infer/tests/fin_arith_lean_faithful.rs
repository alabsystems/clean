// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `Fin n` arithmetic is elaborated at `Fin n`, as Lean does, and an operator
//! whose carrier has no instance is refused rather than re-read at `Nat`.
//!
//! The defect these pin: `theorem w1 : (if True then (3 : Fin 4) + 1 else 0) ≠
//! 0 := by decide` was ACCEPTED, elaborated as `ite Nat … (↑(3 : Fin 4) + 1) 0 ≠
//! 0` (`4 ≠ 0`). In Lean the `if` is at `Fin 4`, `(3 : Fin 4) + 1 = 0`, and the
//! statement is false. Two causes, both fixed:
//!
//! * the builtin prelude had no `Fin.add` (`clean-kernel`
//!   `env/data_fin_arith.rs` now mirrors Lean v4.8.0's `Fin.add`/`sub`/`mul`/
//!   `div`/`mod`);
//! * the B104 heterogeneous retry left `HAdd (Fin 4) Nat ?γ` — inputs ground,
//!   only the `outParam` open — postponed instead of failing, so a sibling
//!   numeral solved `?γ := Nat` and the carrier-first pass re-elaborated the
//!   `Fin` leaf through `Fin.val` (`infer/elab_app.rs`,
//!   `hetero_binop_goal_is_determined`). The `Subtype` rows below still have no
//!   instance and exercise that half on its own.
//!
//! Every expectation is Lean 4 semantics; the rows that Lean accepts and
//! Clean still refuses are listed at the bottom as refusals, never as
//! acceptances.

use crate::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::{Environment, Expr, ExprKind, Name};
use clean_parser::parse_file;

/// Elaborate `src` on the builtin prelude: the elaborated TYPE of every
/// theorem that registered, by name, and the error text of every refusal.
fn elab(src: &str) -> (Vec<(String, Expr)>, Vec<String>) {
    let decls = parse_file(src).unwrap_or_else(|e| panic!("must parse: {e}\n{src}"));
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let (mut theorems, mut errors) = (Vec::new(), Vec::new());
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        match elaborate_decl_and_register_with_context(&mut env, &processed, &mut file_ctx) {
            Ok(result) => {
                let mut leaves = Vec::new();
                result.leaf_decls(&mut leaves);
                for leaf in leaves {
                    match leaf {
                        ElabResult::Theorem { name, ty, .. } => {
                            theorems.push((name.to_string(), ty.clone()));
                        }
                        ElabResult::Failed { error, .. } => errors.push(error.to_string()),
                        _ => {}
                    }
                }
            }
            Err(error) => errors.push(error.to_string()),
        }
    }
    (theorems, errors)
}

fn accepted(src: &str) -> Vec<(String, Expr)> {
    let (theorems, errors) = elab(src);
    assert!(
        errors.is_empty(),
        "Lean accepts this; Clean refused: {errors:?}\n{src}"
    );
    theorems
}

fn refused(src: &str) -> String {
    let (theorems, errors) = elab(src);
    assert!(
        !errors.is_empty(),
        "Lean refuses this; Clean accepted {theorems:?}\n{src}"
    );
    errors.join("\n")
}

/// The carrier `α` of the first `@ite α …` in `e`.
fn ite_carrier(e: &Expr) -> Option<Expr> {
    let mut stack = vec![e.clone()];
    while let Some(e) = stack.pop() {
        if matches!(e.get_app_fn().kind(), ExprKind::Const(name, _) if *name == Name::from_string("ite"))
        {
            return e.get_app_args().first().map(|carrier| (*carrier).clone());
        }
        match e.kind() {
            ExprKind::App(f, a) => {
                stack.push((**f).clone());
                stack.push((**a).clone());
            }
            ExprKind::Lam(_, t, b) | ExprKind::Pi(_, t, b) => {
                stack.push((**t).clone());
                stack.push((**b).clone());
            }
            _ => {}
        }
    }
    None
}

fn head_name(e: &Expr) -> Option<String> {
    match e.get_app_fn().kind() {
        ExprKind::Const(name, _) => Some(name.to_string()),
        _ => None,
    }
}

fn assert_ite_at_fin(theorems: &[(String, Expr)], name: &str) {
    let (_, ty) = theorems
        .iter()
        .find(|(n, _)| n == name)
        .unwrap_or_else(|| panic!("{name} registered"));
    let carrier = ite_carrier(ty).unwrap_or_else(|| panic!("{name} is an `ite`: {ty}"));
    assert_eq!(
        head_name(&carrier).as_deref(),
        Some("Fin"),
        "{name}: the `if` must be elaborated at `Fin 4` (Lean), got {carrier}"
    );
}

/// The reported defect, now refused for the right reason: `decide` evaluates
/// the `Fin 4` reading and finds it false.
#[test]
fn ite_branch_fin_sum_false_in_lean_is_refused() {
    let err = refused("theorem w1 : (if True then (3 : Fin 4) + 1 else 0) ≠ 0 := by decide\n");
    assert!(
        err.contains("is false") && err.contains("Fin"),
        "w1 must be refused because it is FALSE at `Fin 4`, not for a side reason: {err}"
    );
    // The sibling spellings from the issue matrix.
    for src in [
        "example : (if True then (3 : Fin 4) + 1 else 0) ≠ 0 := by decide\n",
        "theorem w13 : (match true with | true => (3 : Fin 4) + 1 | false => 0) ≠ 0 := by decide\n",
        "theorem q5 (x : Fin 4) (h : x = 3) : (if True then x + 1 else 0) ≠ 0 := by\n  subst h; decide\n",
        "theorem w5 : (if True then (3 : Fin 4) + 1 else 0) ≠ (0 : Fin 4) := by decide\n",
        "theorem w2 : ((3 : Fin 4) + 1) ≠ 0 := by decide\n",
        "theorem w7 : (if True then (3 : Fin 4) else 0) + 1 ≠ 0 := by decide\n",
        "theorem w8 : (if True then (3 : Fin 4) + 1 else 0) ≠ 0 := by simp\n",
    ] {
        refused(src);
    }
}

/// The true twins Lean accepts, elaborated at `Fin 4`.
#[test]
fn ite_branch_fin_sum_true_in_lean_is_accepted_at_fin() {
    let theorems = accepted(
        "theorem f2 : (if True then (3 : Fin 4) + 1 else 0) = 0 := by decide\n\
         theorem w1t : (if True then (3 : Fin 4) + 1 else 0) ≠ 1 := by decide\n\
         theorem w4t : (if True then (3 : Fin 4) + 1 else (0 : Fin 4)) = 0 := by decide\n\
         theorem w5t : (if True then (3 : Fin 4) + 1 else 0) = (0 : Fin 4) := by decide\n\
         theorem q5t (x : Fin 4) (h : x = 3) : (if True then x + 1 else 0) = 0 := by\n  subst h; decide\n",
    );
    for name in ["f2", "w1t", "w4t", "w5t", "q5t"] {
        assert_ite_at_fin(&theorems, name);
    }
    // `4 : Fin 4` is `0`, so this is TRUE in Lean — and it is true at `Fin 4`,
    // not because `3 + 1 = 4` at `Nat`.
    let theorems =
        accepted("theorem f1 : (if True then (3 : Fin 4) + 1 else 0) = 4 := by decide\n");
    assert_ite_at_fin(&theorems, "f1");
}

/// Top level: `Fin` addition exists and wraps.
#[test]
fn fin_sum_elaborates_and_wraps() {
    accepted(
        "def h : Fin 4 := (3 : Fin 4) + (1 : Fin 4)\n\
         theorem r1t : h = 0 := by decide\n\
         theorem r1r : h = 0 := rfl\n\
         theorem val0 : ((3 : Fin 4) + 1).val = 0 := rfl\n",
    );
    refused("theorem val4 : ((3 : Fin 4) + 1).val = 4 := rfl\n");
}

/// An expected type of `Nat` still reads the sum at `Nat` — Lean's `binop%`
/// seeds its maximal type from the expected type and coerces the `Fin` leaf.
#[test]
fn expected_nat_still_reads_the_sum_at_nat() {
    accepted("theorem q4 : ((3 : Fin 4) + 1 : Nat) = 4 := by decide\n");
    refused("theorem q4f : ((3 : Fin 4) + 1 : Nat) = 0 := by decide\n");
}

/// Lean v4.8.0's `Fin.sub`/`mul`/`div`/`mod` values, and `Fin` equality is
/// decidable.
#[test]
fn fin_ops_have_lean_values() {
    accepted(
        "theorem o_sub : (1 : Fin 4) - 2 = 3 := by decide\n\
         theorem o_mul : (3 : Fin 4) * 3 = 1 := by decide\n\
         theorem o_div : (3 : Fin 4) / 2 = 1 := by decide\n\
         theorem o_mod : (3 : Fin 4) % 2 = 1 := by decide\n\
         theorem o_div0 : (3 : Fin 4) / 0 = 0 := by decide\n\
         theorem o_mod0 : (3 : Fin 4) % 0 = 3 := by decide\n\
         theorem o_sub_rfl : (1 : Fin 4) - 2 = 3 := rfl\n\
         theorem o_ne : (3 : Fin 4) ≠ 2 := by decide\n",
    );
    for src in [
        "theorem of_sub : (1 : Fin 4) - 2 = 0 := by decide\n",
        "theorem of_mul : (3 : Fin 4) * 3 = 2 := by decide\n",
        "theorem of_ne : (3 : Fin 4) ≠ 7 := by decide\n",
    ] {
        refused(src);
    }
}

/// NOT YET LEAN: the `Fin` order. Lean v4.8.0 has `instLTFin`/`instLEFin`;
/// this prelude does not (see `data_fin_arith.rs` for why they were held
/// back), so a `Fin` comparison is REFUSED — loudly, and never read at `Nat`,
/// where `(5 : Fin 4) < 2` would be `5 < 2`. When the order lands, flip these
/// to `accepted`.
#[test]
fn fin_order_is_refused_until_it_lands() {
    for src in [
        "theorem o_lt : (3 : Fin 4) + 1 < 1 := by decide\n",
        "theorem o_lit : (5 : Fin 4) < 2 := by decide\n",
        "theorem o_le : ¬ ((3 : Fin 4) ≤ 2) := by decide\n",
    ] {
        let err = refused(src);
        assert!(
            err.contains("LT (Fin") || err.contains("LE (Fin"),
            "a `Fin` comparison must fail on the missing `Fin` order instance: {err}"
        );
    }
}

/// The elaborator half on its own: `{n : Nat // n > 0}` has no `HAdd`/`HMul`
/// in the builtin prelude (nor in Lean), and coerces to `Nat`. Before the fix
/// both rows were ACCEPTED at `Nat`; Lean refuses them.
#[test]
fn operator_without_an_instance_is_refused_not_read_at_nat() {
    let err = refused(
        "theorem s1 : (if True then (⟨3, by decide⟩ : {n : Nat // n > 0}) + 1 else 0) ≠ 0 := by decide\n",
    );
    assert!(
        err.contains("failed to synthesize") && err.contains("HAdd") && err.contains("Subtype"),
        "must be the operator's own synthesis failure: {err}"
    );
    assert!(
        !err.contains("fvar#"),
        "the open result slot is rendered `?N`, not by its raw fvar id: {err}"
    );
    refused(
        "theorem s12 : (if True then (⟨3, by decide⟩ : {n : Nat // n > 0}) * 2 else 0) = 6 := by decide\n",
    );
    // Operators Lean gives `Fin n` but this prelude does not (bitwise, and no
    // `Pow (Fin n)` in Lean core either): refused, where they were read at
    // `Nat` — `(3 : Fin 4) ||| 4` is `7` at `Nat` and `3` at `Fin 4`.
    refused("theorem s13 : (if True then (3 : Fin 4) ||| 4 else 0) ≠ 3 := by decide\n");
    refused("theorem s14 : (if True then (3 : Fin 4) ^ 2 else 0) ≠ 1 := by decide\n");
}

/// A genuinely heterogeneous instance still elaborates through the B104 retry:
/// the retry now fails only when NO instance exists for the operand types.
#[test]
fn genuine_heterogeneous_instance_still_resolves() {
    accepted(
        "structure Sec where\n  s : Nat\n\nstructure Min' where\n  m : Nat\n\n\
         instance : HAdd Sec Min' Sec where\n  hAdd a b := ⟨a.s + 60 * b.m⟩\n\n\
         theorem hetero_pin : ((⟨30⟩ : Sec) + (⟨2⟩ : Min')).s = 150 := rfl\n",
    );
}

/// Machine-word analogues: `UInt8` has its arithmetic, so the `if` is at
/// `UInt8` and wraps (unchanged). `BitVec` and `USize` have none in the builtin
/// prelude — Lean accepts both rows; Clean refuses them LOUDLY, never at `Nat`.
#[test]
fn machine_word_analogues() {
    let theorems =
        accepted("theorem u8 : (if True then (255 : UInt8) + 1 else 0) = 0 := by decide\n");
    let (_, ty) = &theorems[0];
    let carrier = ite_carrier(ty).expect("an `ite`");
    assert_eq!(head_name(&carrier).as_deref(), Some("UInt8"));
    refused("theorem bv : (if True then (255 : BitVec 8) + 1 else 0) = 0 := by decide\n");
    refused("theorem us (x : USize) : (if True then x + 1 else 0) = x + 1 := rfl\n");
}
