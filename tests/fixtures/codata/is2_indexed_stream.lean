-- Rank-7 width-1 chain, source side.
--
-- `IS2` is an indexed codata stream whose index MOVES (`next : IS2 (n+1)`),
-- carrying first-order state (`acc`) and a first-order observation (`val : Nat`).
-- That combination is the point: an unindexed stream would not exercise the
-- rank-7 claim, and a non-scalar observation would not survive extraction.

codata IS2 : (n : Nat) → Type where
  val : Nat
  next : IS2 (Nat.succ n)

codef doubler (n : Nat) (acc : Nat) : IS2 n where
  val := acc
  next := doubler (Nat.succ n) (acc + acc)

-- Depth-0/1/2 observations, definitionally.
theorem d0 : IS2.val (doubler 0 1) = 1 := rfl
theorem d1 : IS2.val (IS2.next (doubler 0 1)) = 2 := rfl
theorem d2 : IS2.val (IS2.next (IS2.next (doubler 0 1))) = 4 := rfl

-- B1: the finite observation operator. `nth k n s` observes `s` at depth `k`.
-- This is the operator the observational soundness statement is ABOUT: the
-- theorem to prove is `nth k = (decode of k forced target layers)`.
-- Hand-written rather than generated -- generating it is a width problem.
def IS2.nth : Nat → (n : Nat) → IS2 n → Nat :=
  Nat.rec (motive := fun _ => (n : Nat) → IS2 n → Nat)
    (fun n s => IS2.val s)
    (fun _ ih n s => ih (Nat.succ n) (IS2.next s))

-- Both laws should be `rfl`: `val_corec`/`next_corec` are definitional.
theorem nth_zero (n : Nat) (s : IS2 n) : IS2.nth 0 n s = IS2.val s := rfl

theorem nth_succ (k n : Nat) (s : IS2 n) :
    IS2.nth (Nat.succ k) n s = IS2.nth k (Nat.succ n) (IS2.next s) := rfl

-- Closed instances: the shape the width-1 differential will compare against.
theorem nth_d0 : IS2.nth 0 0 (doubler 0 1) = 1 := rfl
theorem nth_d1 : IS2.nth 1 0 (doubler 0 1) = 2 := rfl
theorem nth_d2 : IS2.nth 2 0 (doubler 0 1) = 4 := rfl
theorem nth_d3 : IS2.nth 3 0 (doubler 0 1) = 8 := rfl
