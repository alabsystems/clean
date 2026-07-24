// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! `Nat.mod_lt'` and `bvadd_in_range`, proven down to the foundational axioms
//! (propext / Quot.sound / Classical.choice) with an EMPTY non-foundational
//! axiom closure.
//!
//! This is the value-range fact `(a + b) % 2^w < 2^w` that was a documented
//! BLOCKER while `Nat.mod` was an opaque placeholder. It is now reachable
//! because `Nat.mod` is registered as a genuine structural definition
//! (`Nat.modCore`, fuel-recursive) in `clean-kernel` (env/data_types_nat.rs);
//! the Nat sub/order lemmas absent from `with_prelude` are self-proved by
//! `@Nat.rec` induction below.
//!
//! `Nat.mod` is a real structural definition here:
//!   Nat.mod a n          = Nat.modCore a a n                       (rfl)
//!   Nat.modCore 0 a n     = a                                      (rfl)
//!   Nat.modCore (succ f) a n
//!     = @Nat.rec (fun _ => Nat) (Nat.modCore f (a-n) n) (fun _ _ => a) (n - a)  (rfl)
//! so we prove the bound by induction on the fuel argument.

use clean_elab::{
    elaborate_decl_and_register, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::env::Environment;
use clean_parser::parse_file;

const SRC: &str = r#"
namespace ModLt

-- ============================================================================
-- Self-proved structural helpers.  (None of these are in `with_prelude`.)
-- ============================================================================

-- `a <= 0 -> a = 0`.  Case on `a` via @Nat.rec: `a = 0` is `rfl`; `a = succ a'`
-- gives `Nat.le (succ a') 0 ≡ Nat.lt a' 0`, impossible (`Nat.not_succ_le_zero`).
-- NOTE: the equation in the motive must be parenthesized, else `->` and `=`
-- mis-associate as `(Nat.le k 0 -> k) = Nat.zero`.
theorem le_zero (a : Nat) (h : Nat.le a 0) : a = Nat.zero :=
  @Nat.rec
    (fun k => Nat.le k 0 -> (k = Nat.zero))
    (fun _h0 => rfl)
    (fun a' _ih hs =>
      @False.elim (Nat.succ a' = Nat.zero) (Nat.not_succ_le_zero a' hs))
    a
    h

-- `succ x - succ m = x - m`, by induction on `m`.
--   base m=0:      both sides reduce to `x` (rfl).
--   step m=succ j: LHS = pred (sub (succ x) (succ j)), RHS = pred (sub x j);
--                  close with `congrArg Nat.pred ih`.
theorem succ_sub_succ (x m : Nat) : Nat.sub (Nat.succ x) (Nat.succ m) = Nat.sub x m :=
  @Nat.rec
    (fun k => Nat.sub (Nat.succ x) (Nat.succ k) = Nat.sub x k)
    rfl
    (fun j ih => congrArg Nat.pred ih)
    m

-- `0 - m = 0`, by induction on `m` (pred chain back to 0).
theorem zero_sub (m : Nat) : Nat.sub 0 m = 0 :=
  @Nat.rec
    (fun k => Nat.sub 0 k = 0)
    rfl
    (fun j ih => congrArg Nat.pred ih)
    m

-- `0 < n - a  ->  a < n`.  Proved in the stronger generalized-over-`n` form by
-- induction on `a` (so the IH is available at every `n`):
--   a=0:        n - 0 ≡ n, the hypothesis IS the goal.
--   a=succ a':  case on n.
--     n=0:      n - succ a' = 0 - succ a' = 0  (zero_sub), so the hypothesis is
--               `0 < 0`, refuted by `Nat.not_succ_le_zero 0`.
--     n=succ n': succ n' - succ a' = n' - a'   (succ_sub_succ); the IH at `n'`
--               gives `a' < n'`, then `succ_le_succ` lifts to `succ a' < succ n'`.
theorem sub_pos_lt (a n : Nat) (h : Nat.lt 0 (Nat.sub n a)) : Nat.lt a n :=
  @Nat.rec
    (fun k => forall (m : Nat), Nat.lt 0 (Nat.sub m k) -> Nat.lt k m)
    (fun m hm => hm)
    (fun a' ih =>
      fun m =>
        @Nat.rec
          (fun mm => Nat.lt 0 (Nat.sub mm (Nat.succ a')) -> Nat.lt (Nat.succ a') mm)
          (fun h0 =>
            @False.elim (Nat.lt (Nat.succ a') Nat.zero)
              (Nat.not_succ_le_zero Nat.zero
                (@Eq.subst Nat (fun z => Nat.lt 0 z) (Nat.sub Nat.zero (Nat.succ a')) Nat.zero
                  (zero_sub (Nat.succ a')) h0)))
          (fun n' _ihn hn =>
            @Nat.succ_le_succ (Nat.succ a') n'
              (ih n'
                (@Eq.subst Nat (fun z => Nat.lt 0 z)
                  (Nat.sub (Nat.succ n') (Nat.succ a')) (Nat.sub n' a')
                  (succ_sub_succ n' a') hn)))
          m)
    a
    n
    h

-- The decrease bound for the recursive call:
--   a <= succ f  ->  0 < n  ->  a - n <= f.
-- Case on `n` (positive => succ m), then on `a`.
--   a=0:       0 - succ m = 0 <= f                        (zero_le, transported)
--   a=succ a': succ a' - succ m = a' - m                  (succ_sub_succ)
--              a' - m <= a' <= f  via `Nat.sub_le` + `Nat.le_of_succ_le_succ`
--              + `Nat.le_trans`.
theorem key (a n f : Nat) (ha : Nat.le a (Nat.succ f)) (hn : Nat.lt 0 n) :
    Nat.le (Nat.sub a n) f :=
  @Nat.rec
    (fun nn => Nat.lt 0 nn -> Nat.le (Nat.sub a nn) f)
    (fun h0 =>
      @False.elim (Nat.le (Nat.sub a Nat.zero) f) (Nat.not_succ_le_zero Nat.zero h0))
    (fun m _ihn _hsm =>
      @Nat.rec
        (fun aa => Nat.le aa (Nat.succ f) -> Nat.le (Nat.sub aa (Nat.succ m)) f)
        (fun _haa =>
          @Eq.subst Nat (fun z => Nat.le z f) Nat.zero (Nat.sub Nat.zero (Nat.succ m))
            (Eq.symm (zero_sub (Nat.succ m))) (Nat.zero_le f))
        (fun a' _iha haa =>
          @Eq.subst Nat (fun z => Nat.le z f)
            (Nat.sub a' m) (Nat.sub (Nat.succ a') (Nat.succ m))
            (Eq.symm (succ_sub_succ a' m))
            (@Nat.le_trans (Nat.sub a' m) a' f
              (Nat.sub_le a' m)
              (Nat.le_of_succ_le_succ a' f haa)))
        a
        ha)
    n
    hn

-- ============================================================================
-- The fuel-induction core: `modCore` is bounded by the modulus.
-- ============================================================================
-- modCore_lt fuel : forall a n, a <= fuel -> 0 < n -> modCore fuel a n < n.
-- By @Nat.rec on `fuel` with a forall-carrying Prop motive.
--   base fuel=0:    modCore 0 a n ≡ a; `a <= 0` gives `a = 0` (le_zero), and the
--                   goal `a < n` is `0 < n` (hn) transported back along `a = 0`.
--   step fuel=succ f, IH:  modCore (succ f) a n reduces to
--                   `@Nat.rec (fun _=>Nat) (modCore f (a-n) n) (fun _ _=>a) (n-a)`.
--                   Case-split `n - a` with the equation threaded:
--                     n-a = 0:      result is `modCore f (a-n) n`; apply IH with
--                                   the `key` bound `(a-n) <= f`.
--                     n-a = succ k: result is `a`; `sub_pos_lt` from `0 < n-a`.
-- IMPORTANT: the threaded equation is written `@Eq Nat ...` / `@Eq.refl Nat ...`
-- (not the `=` notation), so the recursor motive carries no unsolved level
-- metavariables.
theorem modCore_lt (fuel : Nat) :
    forall (a n : Nat), Nat.le a fuel -> Nat.lt 0 n -> Nat.lt (Nat.modCore fuel a n) n :=
  @Nat.rec
    (fun f => forall (a n : Nat), Nat.le a f -> Nat.lt 0 n -> Nat.lt (Nat.modCore f a n) n)
    (fun a n ha hn =>
      @Eq.subst Nat (fun z => Nat.lt z n) Nat.zero a (Eq.symm (le_zero a ha)) hn)
    (fun f ih =>
      fun a n ha hn =>
        @Nat.rec
          (fun s =>
            (@Eq Nat (Nat.sub n a) s) ->
              Nat.lt
                (@Nat.rec (fun _ => Nat) (Nat.modCore f (Nat.sub a n) n) (fun _ _ => a) s)
                n)
          (fun _heq => ih (Nat.sub a n) n (key a n f ha hn) hn)
          (fun k _ihk heq =>
            sub_pos_lt a n
              (@Eq.subst Nat (fun z => Nat.lt 0 z) (Nat.succ k) (Nat.sub n a)
                (Eq.symm heq) (Nat.zero_lt_succ k)))
          (Nat.sub n a)
          (@Eq.refl Nat (Nat.sub n a)))
    fuel

-- Headline 1: `Nat.mod a n < n` whenever `0 < n`.
-- `Nat.mod a n ≡ Nat.modCore a a n` (fuel = a), and `a <= a` by `Nat.le_refl`.
theorem Nat.mod_lt' (a n : Nat) (h : Nat.lt 0 n) : Nat.lt (Nat.mod a n) n :=
  modCore_lt a a n (Nat.le_refl a) h

-- ============================================================================
-- Strict positivity of the width modulus (adapted from the e2e reference).
-- ============================================================================
-- `0 < a -> 0 < b -> 0 < a * b`, by @Nat.rec on `b`.
theorem nmul_pos (a b : Nat) : Nat.lt 0 a -> Nat.lt 0 b -> Nat.lt 0 (Nat.mul a b) :=
  fun ha hb =>
    @Nat.rec
      (fun k => Nat.lt 0 k -> Nat.lt 0 (Nat.mul a k))
      (fun h0 => @False.elim (Nat.lt 0 (Nat.mul a 0)) (Nat.lt_irrefl 0 h0))
      (fun j _ih _hsj =>
        @Nat.le_trans 1 (Nat.succ (Nat.mul a j)) (Nat.add (Nat.mul a j) a)
          (@Nat.succ_le_succ 0 (Nat.mul a j) (Nat.zero_le (Nat.mul a j)))
          (Nat.add_le_add_left 1 a ha (Nat.mul a j)))
      b hb

-- `0 < 2 ^ w` at every width, by @Nat.rec on `w` (base `2^0 = 1`; step doubles).
theorem two_pow_pos (w : Nat) : Nat.lt 0 (Nat.pow 2 w) :=
  @Nat.rec
    (fun k => Nat.lt 0 (Nat.pow 2 k))
    (Nat.le_refl 1)
    (fun k ih => nmul_pos (Nat.pow 2 k) 2 ih (@Nat.succ_le_succ 0 1 (Nat.zero_le 1)))
    w

-- Headline 2: `(a + b) mod 2^w` stays in `[0, 2^w)` -- exactly what a bitvector
-- `bvadd` needs to land back in range.
theorem bvadd_in_range (w a b : Nat) :
    Nat.lt (Nat.mod (Nat.add a b) (Nat.pow 2 w)) (Nat.pow 2 w) :=
  Nat.mod_lt' (Nat.add a b) (Nat.pow 2 w) (two_pow_pos w)

end ModLt
"#;

/// Drive the real `clean check` pipeline (parse -> preprocess -> elaborate +
/// kernel-register) over the module, surfacing swallowed inner failures.
fn elaborate_module(source: &str) -> Result<Environment, String> {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).map_err(|e| format!("parse error: {e:?}"))?;
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        let result = elaborate_decl_and_register(&mut env, &processed)
            .map_err(|e| format!("elaborate/kernel-check error: {e}"))?;
        let mut failures = Vec::new();
        collect_failures(&result, &mut failures);
        if !failures.is_empty() {
            return Err(format!("inner failures:\n{}", failures.join("\n")));
        }
    }
    Ok(env)
}

fn collect_failures(result: &ElabResult, out: &mut Vec<String>) {
    match result {
        ElabResult::Multiple(results) => {
            for r in results {
                collect_failures(r, out);
            }
        }
        ElabResult::Failed { name, error, .. } => out.push(format!("{name}: {error}")),
        _ => {}
    }
}

/// Assert `short` is registered AND proven down to the foundational axioms:
/// its transitive non-foundational axiom closure is empty.
fn assert_proven(env: &Environment, short: &str) {
    let name = env
        .constants()
        .map(|c| &c.name)
        .find(|n| n.last_component().as_deref() == Some(short))
        .cloned()
        .unwrap_or_else(|| panic!("no const {short}"));
    let deps = env
        .axiom_deps(&name)
        .unwrap_or_else(|| panic!("{name}: no deps"));
    assert!(deps.is_empty(), "{name} rests on: {deps:?}");
}

#[test]
fn modlt_proven_to_foundations() {
    let env = elaborate_module(SRC).expect("module must elaborate");
    // Both theorems must be proven with an EMPTY non-foundational axiom closure
    // (i.e. down to propext / Quot.sound / Classical.choice only).
    assert_proven(&env, "mod_lt'");
    assert_proven(&env, "bvadd_in_range");
}
