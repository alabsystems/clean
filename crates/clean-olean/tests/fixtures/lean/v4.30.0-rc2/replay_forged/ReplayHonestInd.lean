prelude
import Init.Core

/-!
# `ReplayHonestInd` — inductive families Lean's kernel admits

The control for the recursor/constructor re-derivation (`ReplayForgedRec`,
`ReplayForgedRule`, `ReplayForgedCtor`): every block below is elaborated and checked by
Lean, so a re-check that re-derives each block's constructors and recursors must find
them identical to the stored ones. One block per shape the kernel's `add_inductive`
distinguishes: an enumeration, a recursive type, a parameterised structure, an indexed
family, a `Prop` family with K-like elimination, a mutual pair and a nested type.
-/

universe u

inductive HI where
  | a
  | b

theorem honest_ind_eq : @HI.rec (fun _ => Bool) true false HI.b = false := rfl

inductive HN where
  | z
  | s (n : HN)

theorem honest_hn_eq : @HN.rec (fun _ => Nat) 0 (fun _ ih => Nat.succ ih) (HN.s HN.z) = 1 := rfl

structure HP (α : Type u) where
  val : α
  tag : Nat

theorem honest_hp_eq : (HP.mk (α := Nat) 3 4).tag = 4 := rfl

inductive HV : Nat → Type where
  | nil : HV 0
  | cons (n : Nat) (x : Nat) (xs : HV n) : HV (n + 1)

inductive HEqq {α : Sort u} (a : α) : α → Prop where
  | refl : HEqq a a

theorem honest_heqq {α : Sort u} (a : α) : HEqq a a := HEqq.refl

mutual
  inductive HEv : Nat → Prop where
    | zero : HEv 0
    | succ (n : Nat) : HOd n → HEv (n + 1)
  inductive HOd : Nat → Prop where
    | succ (n : Nat) : HEv n → HOd (n + 1)
end

theorem honest_ev_two : HEv 2 := HEv.succ 1 (HOd.succ 0 HEv.zero)

inductive HT where
  | node : List HT → HT

def honest_ht_leaf : HT := HT.node List.nil
