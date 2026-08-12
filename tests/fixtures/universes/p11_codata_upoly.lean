-- U2 rung 7 part 2 (flipped 2026-08-08): universe-polymorphic codata.
codata GP.{u} (A : Type u) where
  head : A
  tail : GP A

def nats : Nat → GP Nat :=
  fun n => GP.corec (fun s => s) (fun s => Nat.succ s) n

theorem nats_head : GP.head (nats Nat.zero) = Nat.zero := rfl

theorem nats_tail_head :
    GP.head (GP.tail (nats Nat.zero)) = Nat.succ Nat.zero := rfl

def bigs : Type → GP.{1} Type :=
  fun t => GP.corec (fun s => s) (fun s => s) t

theorem bigs_head : GP.head (bigs Nat) = Nat := rfl
