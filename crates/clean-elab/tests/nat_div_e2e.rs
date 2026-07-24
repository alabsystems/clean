// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! `Nat.div`/`Nat.mod` value-properties, proven down to the foundational axioms
//! (propext / Quot.sound / Classical.choice) with an EMPTY non-foundational
//! axiom closure:
//!
//!   div_le_self (a n : Nat) : Nat.le (Nat.div a n) a
//!   div_add_mod (a n : Nat) : (Nat.div a n) * n + (Nat.mod a n) = a
//!                             (the euclidean identity)
//!
//! These are reachable because `Nat.div` and `Nat.mod` are now registered as
//! GENUINE structural definitions (`Nat.divCore` / `Nat.modCore`, fuel-recursive)
//! in `clean-kernel` (env/data_types_nat.rs), not opaque placeholders:
//!
//!   Nat.divCore 0        a n = 0
//!   Nat.divCore (succ f) a n
//!     = @Nat.rec (fun _ => Nat) (succ (divCore f (a-n) n)) (fun _ _ => 0) (n - a)
//!   Nat.div a 0        = 0
//!   Nat.div a (succ k) = Nat.divCore a a (succ k)
//!   Nat.modCore 0        a n = a
//!   Nat.modCore (succ f) a n
//!     = @Nat.rec (fun _ => Nat) (modCore f (a-n) n) (fun _ _ => a) (n - a)
//!   Nat.mod a n = Nat.modCore a a n
//!
//! `divCore` and `modCore` share the SAME fuel/decrement recursion, so the
//! euclidean identity is one JOINT fuel induction (`divmod_id`). The Nat
//! sub/order lemmas absent from `with_prelude` are self-proved by `@Nat.rec`;
//! the harness + the `le_zero`/`succ_sub_succ`/`zero_sub`/`key` helpers and the
//! threaded-`@Eq Nat`-equation fuel-induction pattern are reused from the
//! sibling `nat_mod_lt_e2e.rs` proof. The Nat algebra (`nmul_succ_left`,
//! `add_right_comm`, ...) follows the semiring proofs in
//! `trust_core_typesystem_e2e.rs`.

use clean_elab::{
    elaborate_decl_and_register, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::env::Environment;
use clean_parser::parse_file;

const SRC: &str = r#"
namespace NatDiv

-- ============================================================================
-- Self-proved structural helpers (none are in `with_prelude`), reused verbatim
-- from the `Nat.mod_lt'` proof where useful.
-- ============================================================================

-- `a <= 0 -> a = 0`.
theorem le_zero (a : Nat) (h : Nat.le a 0) : a = Nat.zero :=
  @Nat.rec
    (fun k => Nat.le k 0 -> (k = Nat.zero))
    (fun _h0 => rfl)
    (fun a' _ih hs =>
      @False.elim (Nat.succ a' = Nat.zero) (Nat.not_succ_le_zero a' hs))
    a
    h

-- `succ x - succ m = x - m`.
theorem succ_sub_succ (x m : Nat) : Nat.sub (Nat.succ x) (Nat.succ m) = Nat.sub x m :=
  @Nat.rec
    (fun k => Nat.sub (Nat.succ x) (Nat.succ k) = Nat.sub x k)
    rfl
    (fun j ih => congrArg Nat.pred ih)
    m

-- `0 - m = 0`.
theorem zero_sub (m : Nat) : Nat.sub 0 m = 0 :=
  @Nat.rec
    (fun k => Nat.sub 0 k = 0)
    rfl
    (fun j ih => congrArg Nat.pred ih)
    m

-- The decrease bound for the recursive call:  a <= succ f -> 0 < n -> a - n <= f.
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

-- `n - a = 0 -> n <= a`.  By induction on `a`, generalized over `n`.
--   a=0:        n - 0 ≡ n, so h : n = 0; goal `n <= 0` is `0 <= 0` transported.
--   a=succ a':  case on n.
--     n=0:      `0 <= succ a'` (Nat.zero_le).
--     n=succ n': succ n' - succ a' = n' - a' (succ_sub_succ), IH gives n' <= a',
--                lift with succ_le_succ.
theorem sub_zero_le (n a : Nat) (h : Nat.sub n a = 0) : Nat.le n a :=
  @Nat.rec
    (fun k => forall (m : Nat), Nat.sub m k = 0 -> Nat.le m k)
    (fun m hm =>
      @Eq.subst Nat (fun z => Nat.le z Nat.zero) Nat.zero m (Eq.symm hm) (Nat.zero_le Nat.zero))
    (fun a' ih =>
      fun m =>
        @Nat.rec
          (fun mm => Nat.sub mm (Nat.succ a') = 0 -> Nat.le mm (Nat.succ a'))
          (fun _h0 => Nat.zero_le (Nat.succ a'))
          (fun n' _ihn hn =>
            @Nat.succ_le_succ n' a'
              (ih n'
                (@Eq.subst Nat (fun z => z = 0)
                  (Nat.sub (Nat.succ n') (Nat.succ a')) (Nat.sub n' a')
                  (succ_sub_succ n' a') hn)))
          m)
    a
    n
    h

-- ============================================================================
-- New helper for div: when `0 < n` and `n <= a`, the quotient step strictly
-- shrinks `a`:   succ (a - n) <= a.
-- ============================================================================
-- Threaded through `n - a = 0` (which is exactly `n <= a`). We case on `n`
-- (positive => succ m) and on `a` (must be succ a', since succ m <= a):
--   sub (succ a') (succ m) = sub a' m   (succ_sub_succ)
--   succ (sub a' m) <= succ a'  reduces to  sub a' m <= a'  (Nat.sub_le).
-- The `a = 0` sub-case is impossible: `succ m <= 0` is `Nat.not_succ_le_zero`.
theorem succ_sub_le (a n : Nat) (hn : Nat.lt 0 n) (hna : Nat.le n a) :
    Nat.le (Nat.succ (Nat.sub a n)) a :=
  @Nat.rec
    (fun nn => Nat.lt 0 nn -> Nat.le nn a -> Nat.le (Nat.succ (Nat.sub a nn)) a)
    (fun h0 _hna =>
      @False.elim (Nat.le (Nat.succ (Nat.sub a Nat.zero)) a)
        (Nat.not_succ_le_zero Nat.zero h0))
    (fun m _ihn =>
      fun _hsm hsm_le =>
        @Nat.rec
          (fun aa =>
            Nat.le (Nat.succ m) aa -> Nat.le (Nat.succ (Nat.sub aa (Nat.succ m))) aa)
          (fun haa =>
            @False.elim (Nat.le (Nat.succ (Nat.sub Nat.zero (Nat.succ m))) Nat.zero)
              (Nat.not_succ_le_zero m haa))
          (fun a' _iha _haa =>
            @Eq.subst Nat
              (fun z => Nat.le (Nat.succ z) (Nat.succ a'))
              (Nat.sub a' m) (Nat.sub (Nat.succ a') (Nat.succ m))
              (Eq.symm (succ_sub_succ a' m))
              (@Nat.succ_le_succ (Nat.sub a' m) a' (Nat.sub_le a' m)))
          a
          hsm_le)
    n
    hn
    hna

-- ============================================================================
-- The fuel-induction core: `divCore` is bounded by the dividend (with 0 < n).
-- ============================================================================
-- divCore_le fuel : forall a n, a <= fuel -> 0 < n -> divCore fuel a n <= a.
--   base fuel=0:    divCore 0 a n ≡ 0, and 0 <= a (Nat.zero_le).
--   step fuel=succ f, IH: divCore (succ f) a n reduces to
--     @Nat.rec (fun _=>Nat) (succ (divCore f (a-n) n)) (fun _ _=>0) (n-a).
--     Case-split `n - a` with the equation threaded:
--       n-a = 0  (n <= a):   result is `succ (divCore f (a-n) n)`. By IH with
--         `key` bound `(a-n) <= f`, `divCore f (a-n) n <= a-n`; lift with
--         `succ_le_succ` to `succ(divCore..) <= succ(a-n)`, then `le_trans`
--         with `succ_sub_le` (`succ(a-n) <= a`).
--       n-a = succ k:        result is `0`, and `0 <= a` (Nat.zero_le).
theorem divCore_le (fuel : Nat) :
    forall (a n : Nat), Nat.le a fuel -> Nat.lt 0 n -> Nat.le (Nat.divCore fuel a n) a :=
  @Nat.rec
    (fun f => forall (a n : Nat), Nat.le a f -> Nat.lt 0 n -> Nat.le (Nat.divCore f a n) a)
    (fun a n _ha _hn => Nat.zero_le a)
    (fun f ih =>
      fun a n ha hn =>
        @Nat.rec
          (fun s =>
            (@Eq Nat (Nat.sub n a) s) ->
              Nat.le
                (@Nat.rec (fun _ => Nat)
                  (Nat.succ (Nat.divCore f (Nat.sub a n) n))
                  (fun _ _ => Nat.zero)
                  s)
                a)
          (fun heq =>
            @Nat.le_trans
              (Nat.succ (Nat.divCore f (Nat.sub a n) n))
              (Nat.succ (Nat.sub a n))
              a
              (@Nat.succ_le_succ (Nat.divCore f (Nat.sub a n) n) (Nat.sub a n)
                (ih (Nat.sub a n) n (key a n f ha hn) hn))
              (succ_sub_le a n hn (sub_zero_le n a heq)))
          (fun k _ihk _heq => Nat.zero_le a)
          (Nat.sub n a)
          (@Eq.refl Nat (Nat.sub n a)))
    fuel

-- Headline (MUST-HAVE): `Nat.div a n <= a`.
--   n = 0:        `Nat.div a 0 ≡ 0`, and `0 <= a` (Nat.zero_le).
--   n = succ k:   `Nat.div a (succ k) ≡ Nat.divCore a a (succ k)`; `a <= a`
--                 (Nat.le_refl) and `0 < succ k` (Nat.zero_lt_succ).
theorem div_le_self (a n : Nat) : Nat.le (Nat.div a n) a :=
  @Nat.rec
    (fun nn => Nat.le (Nat.div a nn) a)
    (Nat.zero_le a)
    (fun k _ihk =>
      divCore_le a a (Nat.succ k) (Nat.le_refl a) (Nat.zero_lt_succ k))
    n

-- ============================================================================
-- Nat algebra needed for the euclidean identity (self-proved; the prelude has
-- only add_assoc/add_comm/zero_add, no mul lemmas). Copied in style from the
-- semiring proofs in `trust_core_typesystem_e2e.rs`.
-- ============================================================================

-- `0 * n = 0`.  `Nat.mul` recurses on its 2nd arg, so `mul 0 (succ k)` reduces
-- to `mul 0 k` and the step is just the IH.
theorem nmul_zero_left (n : Nat) : Nat.mul 0 n = 0 :=
  @Nat.rec (fun k => Nat.mul 0 k = 0) rfl (fun _ ih => ih) n

-- `(a + b) + c = (a + c) + b`, pure equational (no induction).
theorem add_right_comm (a b c : Nat) :
    Nat.add (Nat.add a b) c = Nat.add (Nat.add a c) b :=
  Eq.trans (Nat.add_assoc a b c)
    (Eq.trans (congrArg (fun z => Nat.add a z) (Nat.add_comm b c))
      (Eq.symm (Nat.add_assoc a c b)))

-- `mul (succ a) n = (mul a n) + n`, by `@Nat.rec` on `n`.
theorem nmul_succ_left (a n : Nat) :
    Nat.mul (Nat.succ a) n = Nat.add (Nat.mul a n) n :=
  @Nat.rec
    (fun k => Nat.mul (Nat.succ a) k = Nat.add (Nat.mul a k) k)
    rfl
    (fun k ih =>
      Eq.trans
        (congrArg (fun z => Nat.add z (Nat.succ a)) ih)
        (congrArg (fun z => Nat.succ z) (add_right_comm (Nat.mul a k) k a)))
    n

-- `n <= a -> (a - n) + n = a`, by induction on `n` generalized over `a`.
--   n=0:        add (sub a 0) 0 ≡ add a 0 ≡ a   (rfl).
--   n=succ m:   `succ m <= a` forces a = succ a'. sub (succ a') (succ m) =
--               sub a' m (succ_sub_succ), and add _ (succ m) ≡ succ (add _ m)
--               (rfl); IH at a' (m <= a' via le_of_succ_le_succ) closes it.
theorem sub_add_cancel (a n : Nat) (h : Nat.le n a) :
    @Eq Nat (Nat.add (Nat.sub a n) n) a :=
  @Nat.rec
    (fun k => forall (m : Nat), Nat.le k m -> (@Eq Nat (Nat.add (Nat.sub m k) k) m))
    (fun m _hm => @Eq.refl Nat m)
    (fun n' ih =>
      fun m =>
        @Nat.rec
          (fun mm =>
            Nat.le (Nat.succ n') mm ->
              (@Eq Nat (Nat.add (Nat.sub mm (Nat.succ n')) (Nat.succ n')) mm))
          (fun h0 =>
            @False.elim
              (@Eq Nat (Nat.add (Nat.sub Nat.zero (Nat.succ n')) (Nat.succ n')) Nat.zero)
              (Nat.not_succ_le_zero n' h0))
          (fun a' _iha ha' =>
            @Eq.subst Nat
              (fun z => @Eq Nat (Nat.add z (Nat.succ n')) (Nat.succ a'))
              (Nat.sub a' n') (Nat.sub (Nat.succ a') (Nat.succ n'))
              (Eq.symm (succ_sub_succ a' n'))
              (congrArg (fun z => Nat.succ z)
                (ih a' (Nat.le_of_succ_le_succ n' a' ha'))))
          m)
    n
    a
    h

-- ============================================================================
-- The joint div/mod fuel induction: the euclidean identity on `*Core`.
-- ============================================================================
-- divmod_id fuel : forall a n, a <= fuel -> 0 < n ->
--   (divCore fuel a n) * n + (modCore fuel a n) = a.
-- divCore and modCore share the SAME fuel/decrement recursion, so one joint
-- induction handles both.
--   base fuel=0: a <= 0 => a = 0 (le_zero); divCore 0 0 n = 0, modCore 0 0 n = 0,
--     `mul 0 n + 0 ≡ mul 0 n = 0 = a` (nmul_zero_left), transported along a = 0.
--   step fuel=succ f, IH: both *Core reduce via `Nat.rec _ _ _ (n - a)`.
--     n-a = 0  (n <= a, sub_zero_le): div part = succ (divCore f (a-n) n),
--       mod part = modCore f (a-n) n. With q = divCore f (a-n) n,
--       r = modCore f (a-n) n, IH gives q*n + r = a-n; goal is
--       (succ q)*n + r = a, i.e. (q*n + n) + r = a (nmul_succ_left); rearrange
--       to (q*n + r) + n = a (add_right_comm) = (a-n) + n = a (sub_add_cancel).
--     n-a = succ k': div part = 0, mod part = a. Goal `mul 0 n + a = a`:
--       `mul 0 n = 0` (nmul_zero_left), `0 + a = a` (Nat.zero_add), transported.
theorem divmod_id (fuel : Nat) :
    forall (a n : Nat),
      Nat.le a fuel -> Nat.lt 0 n ->
        @Eq Nat
          (Nat.add (Nat.mul (Nat.divCore fuel a n) n) (Nat.modCore fuel a n))
          a :=
  @Nat.rec
    (fun f =>
      forall (a n : Nat),
        Nat.le a f -> Nat.lt 0 n ->
          @Eq Nat
            (Nat.add (Nat.mul (Nat.divCore f a n) n) (Nat.modCore f a n))
            a)
    (fun a n ha _hn =>
      @Eq.subst Nat
        (fun z =>
          @Eq Nat
            (Nat.add (Nat.mul (Nat.divCore Nat.zero z n) n) (Nat.modCore Nat.zero z n))
            z)
        Nat.zero a (Eq.symm (le_zero a ha))
        (nmul_zero_left n))
    (fun f ih =>
      fun a n ha hn =>
        @Nat.rec
          (fun s =>
            (@Eq Nat (Nat.sub n a) s) ->
              @Eq Nat
                (Nat.add
                  (Nat.mul
                    (@Nat.rec (fun _ => Nat)
                      (Nat.succ (Nat.divCore f (Nat.sub a n) n))
                      (fun _ _ => Nat.zero)
                      s)
                    n)
                  (@Nat.rec (fun _ => Nat)
                    (Nat.modCore f (Nat.sub a n) n)
                    (fun _ _ => a)
                    s))
                a)
          (fun heq =>
            -- n <= a branch: q = divCore f (a-n) n, r = modCore f (a-n) n.
            -- goal: (succ q)*n + r = a.
            @Eq.subst Nat
              (fun w => @Eq Nat w a)
              (Nat.add (Nat.add (Nat.mul (Nat.divCore f (Nat.sub a n) n) n) (Nat.modCore f (Nat.sub a n) n)) n)
              (Nat.add (Nat.mul (Nat.succ (Nat.divCore f (Nat.sub a n) n)) n) (Nat.modCore f (Nat.sub a n) n))
              -- proof: (q*n + r) + n = (succ q)*n + r  (i.e. BIG = SMALL).
              (Eq.symm
                (Eq.trans
                  (congrArg (fun z => Nat.add z (Nat.modCore f (Nat.sub a n) n))
                    (nmul_succ_left (Nat.divCore f (Nat.sub a n) n) n))
                  (add_right_comm
                    (Nat.mul (Nat.divCore f (Nat.sub a n) n) n)
                    n
                    (Nat.modCore f (Nat.sub a n) n))))
              -- now show (q*n + r) + n = a, via IH (q*n + r = a-n) then sub_add_cancel.
              (@Eq.subst Nat
                (fun w => @Eq Nat (Nat.add w n) a)
                (Nat.sub a n)
                (Nat.add (Nat.mul (Nat.divCore f (Nat.sub a n) n) n) (Nat.modCore f (Nat.sub a n) n))
                (Eq.symm (ih (Nat.sub a n) n (key a n f ha hn) hn))
                (sub_add_cancel a n (sub_zero_le n a heq))))
          (fun k _ihk _heq =>
            -- n > a branch: div part = 0, mod part = a. goal: mul 0 n + a = a.
            @Eq.subst Nat
              (fun w => @Eq Nat (Nat.add w a) a)
              Nat.zero (Nat.mul Nat.zero n) (Eq.symm (nmul_zero_left n))
              (Nat.zero_add a))
          (Nat.sub n a)
          (@Eq.refl Nat (Nat.sub n a)))
    fuel

-- `Nat.mod a 0 = a`.  Needed for the n = 0 case of the headline.
--   modCore_zero fuel : forall a, modCore fuel a 0 = a.  Mod by zero loops
--   through the FIRST branch (0 - a = 0 always) with `a` unchanged until fuel
--   runs out, so `modCore a a 0 = a` by fuel induction.
theorem modCore_zero (fuel : Nat) :
    forall (a : Nat), @Eq Nat (Nat.modCore fuel a Nat.zero) a :=
  @Nat.rec
    (fun f => forall (a : Nat), @Eq Nat (Nat.modCore f a Nat.zero) a)
    (fun a => @Eq.refl Nat a)
    (fun f ih =>
      fun a =>
        -- modCore (succ f) a 0 = Nat.rec _ (modCore f (a-0) 0) (fun _ _=>a) (0 - a).
        -- `0 - a = 0` (zero_sub), so it is the first branch: modCore f (a-0) 0.
        -- `a - 0 ≡ a`, so this is `modCore f a 0 = a` by ih a.
        @Eq.subst Nat
          (fun s =>
            @Eq Nat
              (@Nat.rec (fun _ => Nat)
                (Nat.modCore f (Nat.sub a Nat.zero) Nat.zero)
                (fun _ _ => a)
                s)
              a)
          Nat.zero (Nat.sub Nat.zero a) (Eq.symm (zero_sub a))
          (ih a))
    fuel

theorem mod_zero (a : Nat) : @Eq Nat (Nat.mod a Nat.zero) a :=
  modCore_zero a a

-- Headline (STRETCH): the euclidean identity  (a/n)*n + a%n = a.
--   n = 0:      div a 0 ≡ 0, mul 0 0 ≡ 0, add 0 (mod a 0) needs 0 + (mod a 0);
--               `mod a 0 = a` (mod_zero), and `0 + a = a` (Nat.zero_add).
--   n = succ k: div a (succ k) ≡ divCore a a (succ k), mod a (succ k) ≡
--               modCore a a (succ k); apply divmod_id with fuel = a, a <= a,
--               0 < succ k.
theorem div_add_mod (a n : Nat) :
    @Eq Nat (Nat.add (Nat.mul (Nat.div a n) n) (Nat.mod a n)) a :=
  @Nat.rec
    (fun nn => @Eq Nat (Nat.add (Nat.mul (Nat.div a nn) nn) (Nat.mod a nn)) a)
    -- n = 0:  add (mul 0 0) (mod a 0) ≡ add 0 (mod a 0).
    --   rewrite (mod a 0) -> a (mod_zero) under `fun z => add 0 z`, then 0+a=a.
    (@Eq.subst Nat
      (fun z => @Eq Nat (Nat.add (Nat.mul (Nat.div a Nat.zero) Nat.zero) z) a)
      a (Nat.mod a Nat.zero) (Eq.symm (mod_zero a))
      (Nat.zero_add a))
    (fun k _ihk =>
      divmod_id a a (Nat.succ k) (Nat.le_refl a) (Nat.zero_lt_succ k))
    n

end NatDiv
"#;

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
fn nat_div_properties_proven_to_foundations() {
    let env = elaborate_module(SRC).expect("module must elaborate");
    // Both headline theorems must be proven with an EMPTY non-foundational axiom
    // closure (down to propext / Quot.sound / Classical.choice only).
    assert_proven(&env, "div_le_self");
    assert_proven(&env, "div_add_mod");
}
