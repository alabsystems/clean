/-!
R4 item (ii): the advice cursor threaded through `Except` results. A second
read receives the cursor the first read returned, in `do` notation with the
pair destructured, as the checker's sequential calls do.
-/

inductive Refusal where
  | noToken : Nat → Refusal
  | badToken : Nat → Nat → Refusal

def Refusal.show : Refusal → String
  | .noToken p => s!"no token at {p}"
  | .badToken p v => s!"token {v} at {p} is not a digit"

def readAt : List Nat → Nat → Option Nat
  | [], _ => none
  | v :: _, 0 => some v
  | _ :: vs, n + 1 => readAt vs n

/-- Read one digit token and return it with the advanced cursor. -/
def readDigit (toks : List Nat) (pos : Nat) : Except Refusal (Nat × Nat) :=
  match readAt toks pos with
  | none => .error (.noToken pos)
  | some v => if v < 10 then .ok (v, pos + 1) else .error (.badToken pos v)

/-- Three reads in sequence; each starts where the previous one stopped. -/
def readThree (toks : List Nat) (pos : Nat) : Except Refusal (Nat × Nat) := do
  let (a, p) ← readDigit toks pos
  let (b, q) ← readDigit toks p
  let (c, r) ← readDigit toks q
  return (a * 100 + b * 10 + c, r)

def verdict (r : Except Refusal (Nat × Nat)) : String :=
  match r with
  | .ok (v, p) => s!"ACCEPT value={v} cursor={p}"
  | .error e => s!"REFUSE {e.show}"

def main : IO Unit := do
  IO.println (verdict (readThree [4, 0, 7] 0))
  IO.println (verdict (readThree [9, 4, 0, 7, 1] 1))
  IO.println (verdict (readThree [4, 0] 0))
  IO.println (verdict (readThree [4, 12, 7] 0))
