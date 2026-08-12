-- Rank-7 B7, second chain: the PLAIN lane.
--
-- Width, in the ladder's sense: a structurally different declaration through
-- the same certificate. `count` is unindexed and carries a single state slot,
-- where `doubler` is indexed and carries two — so this exercises the IR model
-- and the proof pattern on a shape the first chain did not.

codata St : Type where
  head : Nat
  tail : St

codef count (n : Nat) : St where
  head := n
  tail := count (Nat.succ n)

def St.nth : Nat → St → Nat :=
  Nat.rec (motive := fun _ => St → Nat)
    (fun s => St.head s)
    (fun _ ih s => ih (St.tail s))

inductive IROp where
  | lit   : Nat → IROp
  | slot0 : IROp
  | slot1 : IROp
  | add   : IROp → IROp → IROp
  | succ  : IROp → IROp

def IROp.eval : IROp → Nat → Nat → Nat
  | IROp.lit n,   _,  _  => n
  | IROp.slot0,   s0, _  => s0
  | IROp.slot1,   _,  s1 => s1
  | IROp.add a b, s0, s1 => IROp.eval a s0 s1 + IROp.eval b s0 s1
  | IROp.succ a,  s0, s1 => IROp.eval a s0 s1 + 1

structure IRCorec where
  observe : IROp
  step0 : IROp
  step1 : IROp

def IRCorec.nthFrom : IRCorec → Nat → Nat → Nat → Nat
  | c, 0,          s0, s1 => IROp.eval c.observe s0 s1
  | c, Nat.succ k, s0, s1 =>
      IRCorec.nthFrom c k (IROp.eval c.step0 s0 s1) (IROp.eval c.step1 s0 s1)

-- What `lower_recognized` produces for `count`: one state slot, observed
-- directly, stepped by `succ`. The second slot is unused and pinned to 0.
def countIR : IRCorec :=
  { observe := IROp.slot0,
    step0 := IROp.succ IROp.slot0,
    step1 := IROp.lit 0 }

theorem plain_src_step (k n : Nat) :
    St.nth (Nat.succ k) (count n) = St.nth k (count (Nat.succ n)) := rfl

theorem plain_tgt_step (k n : Nat) :
    IRCorec.nthFrom countIR (Nat.succ k) n 0
      = IRCorec.nthFrom countIR k (Nat.succ n) 0 := rfl

theorem plain_base (n : Nat) :
    St.nth 0 (count n) = IRCorec.nthFrom countIR 0 n 0 := rfl

theorem count_extraction_observationally_correct :
    ∀ (k n : Nat), St.nth k (count n) = IRCorec.nthFrom countIR k n 0 :=
  Nat.rec
    (motive := fun k => ∀ (n : Nat), St.nth k (count n) = IRCorec.nthFrom countIR k n 0)
    (fun n => plain_base n)
    (fun k ih n =>
      Eq.trans (plain_src_step k n)
        (Eq.trans (ih (Nat.succ n)) (Eq.symm (plain_tgt_step k n))))

theorem plain_d0 : St.nth 0 (count 5) = 5 := rfl
theorem plain_d3 : St.nth 3 (count 5) = 8 := rfl
