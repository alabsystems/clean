-- Rank-7 B7: the observational soundness artifact, width 1.
--
-- The claim rank 7 must eventually make is
--
--   for every finite observation depth k,
--   observing the SOURCE corecursive value k layers
--     = decoding k forced TARGET layers
--
-- and this file states and proves exactly that, for the width-1 chain, with
-- zero domain axioms.
--
-- THE VACUITY TRAP THIS FILE MUST AVOID. If the "target semantics" were
-- written by transcribing the source's own recursion, the theorem would be
-- true, nearly `rfl`, and would say nothing about any emitted program. The
-- repo has the loaded gun for it: `iM_bisim_of_eq` already makes tower
-- agreement BE equality in this model.
--
-- So the target side here is an INTERPRETER OVER THE IR AS DATA. `IROp` and
-- `IRCorec` are the extraction IR reflected into Lean; `nthFrom` is a machine
-- that steps a state tuple and observes it. It never mentions `IS2`, `doubler`,
-- or any codata construct. The two sides are different programs over different
-- data, and the theorem relates them.

-- ── the source: an indexed codata stream ──

codata IS2 : (n : Nat) → Type where
  val : Nat
  next : IS2 (Nat.succ n)

codef doubler (n : Nat) (acc : Nat) : IS2 n where
  val := acc
  next := doubler (Nat.succ n) (acc + acc)

-- The finite observation: `nth k n s` observes `s` at depth `k`.
def IS2.nth : Nat → (n : Nat) → IS2 n → Nat :=
  Nat.rec (motive := fun _ => (n : Nat) → IS2 n → Nat)
    (fun n s => IS2.val s)
    (fun _ ih n s => ih (Nat.succ n) (IS2.next s))

-- ── the target: the extraction IR, reflected as data ──

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

-- The lazy machine, in the only form a finite observation can see it: step the
-- state `k` times, then observe. This is the decode of `k` forced layers.
def IRCorec.nthFrom : IRCorec → Nat → Nat → Nat → Nat
  | c, 0,          s0, s1 => IROp.eval c.observe s0 s1
  | c, Nat.succ k, s0, s1 =>
      IRCorec.nthFrom c k (IROp.eval c.step0 s0 s1) (IROp.eval c.step1 s0 s1)

-- ── the emitted term ──
--
-- This is what `lower_recognized` produces for `doubler`, written as data:
-- state `[index, acc]`, observation `acc`, step `[index+1, acc+acc]`.
def doublerIR : IRCorec :=
  { observe := IROp.slot1,
    step0 := IROp.succ IROp.slot0,
    step1 := IROp.add IROp.slot1 IROp.slot1 }

-- ── the observational theorem ──

-- One source step: observing at depth k+1 from index n is observing at depth k
-- from the NEXT layer. Definitional, via the generated `next_corec` law.
theorem src_step (k n acc : Nat) :
    IS2.nth (Nat.succ k) n (doubler n acc)
      = IS2.nth k (Nat.succ n) (doubler (Nat.succ n) (acc + acc)) := rfl

-- One target step: forcing a layer advances the state tuple. Definitional, via
-- the IR machine's own recursion — no codata notion appears here.
theorem tgt_step (k n acc : Nat) :
    IRCorec.nthFrom doublerIR (Nat.succ k) n acc
      = IRCorec.nthFrom doublerIR k (Nat.succ n) (acc + acc) := rfl

-- Depth zero: the source's observation is the target's decode of zero layers.
theorem base_case (n acc : Nat) :
    IS2.nth 0 n (doubler n acc) = IRCorec.nthFrom doublerIR 0 n acc := rfl

-- THE CLAIM: for EVERY finite depth, and every starting index and accumulator,
-- observing the source k layers equals decoding k forced target layers.
--
-- Not a differential at sampled depths — a statement about all of them, proved
-- by induction on the depth, each step discharged by the two definitional
-- lemmas above. The source side walks a codata carrier built on the M-type
-- seed; the target side steps a state tuple through reflected IR data. They are
-- different programs over different data, which is what makes this
-- non-vacuous.
theorem doubler_extraction_observationally_correct :
    ∀ (k n acc : Nat), IS2.nth k n (doubler n acc) = IRCorec.nthFrom doublerIR k n acc :=
  Nat.rec
    (motive := fun k =>
      ∀ (n acc : Nat), IS2.nth k n (doubler n acc) = IRCorec.nthFrom doublerIR k n acc)
    (fun n acc => base_case n acc)
    (fun k ih n acc =>
      Eq.trans
        (src_step k n acc)
        (Eq.trans (ih (Nat.succ n) (acc + acc)) (Eq.symm (tgt_step k n acc))))

-- Closed instances, as a sanity pin on the general theorem above.
theorem b7_d0 : IS2.nth 0 0 (doubler 0 1) = 1 := rfl
theorem b7_d3 : IS2.nth 3 0 (doubler 0 1) = 8 := rfl
theorem b7_ir3 : IRCorec.nthFrom doublerIR 3 0 1 = 8 := rfl
