import Init.WF

/-! Base module for the `honestIsPropStuck` family (#14807). Holds the
tactic-proved `Acc`-trick helpers; `import Init.WF` keeps the closure light. The
generator family `importModules #[ReplayIsPropStuckBase]` and adds the exploit
tail (`Owner`/`asProp`/`proposition`/`observe`/`falseProof`/`trueProof`/
`isprop_stuck_false`) through `addDeclCore`, because the elaborator refuses the
stuck `Owner` carrier that only the vulnerable kernel admits. -/

namespace IPK

def step (x : Bool) (n : Nat) (ih : (m : Nat) → m < n → Bool) : Bool :=
  match n with
  | 0 => x
  | k + 1 => ih k (Nat.lt_succ_self k)

def run (x : Bool) (n : Nat) (h : Acc (· < ·) n) : Bool :=
  Acc.rec (fun m _ => step x m) h

opaque seed : Acc (· < ·) 1 := Nat.lt_wfRel.wf.apply 1

def a := run false 1 seed
def b := run false 1 (Acc.intro 1 fun _ => Acc.inv seed)
def c := run false 0 (Acc.inv seed (Nat.lt_succ_self 0))

theorem run_eq (x : Bool) (n : Nat) (h : Acc (· < ·) n) : run x n h = x := by
  induction h with
  | intro n smaller ih =>
    cases n with
    | zero => rfl
    | succ n => simpa only [run, step] using ih n (Nat.lt_succ_self n)

def P : Prop := a = b
def Q : Prop := a = c
def gate (h : P) : Type := Eq.rec (motive := fun _ _ => Type) Prop h

theorem observedProofsFalse (T : Prop) (observe : T → Bool) (p q : T)
    (onFalse : observe p = false) (onTrue : observe q = true) : False := by
  have same : p = q := proof_irrel p q
  exact Bool.noConfusion (onFalse.symm.trans ((congrArg observe same).trans onTrue))

opaque witness : Q := (run_eq false _ _).trans (run_eq false _ _).symm

end IPK
