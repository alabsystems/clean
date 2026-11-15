/-!
NEGATIVE CONTROL for R4 item (vi) (`programs/c29_r4_vi_ground_acceptance_theorem.lean`):
the same block with a ground acceptance that is FALSE, closed by `decide`.
Pinned Lean rejects it. With c29 accepted, it shows the checking kernel
evaluates the block rather than taking the statement on trust.
-/

inductive Tok where
  | core
  | stop
  | same
  | both

inductive Tm where
  | lit : Nat → Tm
  | succ : Tm → Tm
  | pair : Tm → Tm → Tm

inductive Refusal where
  | depth
  | noToken : Nat → Refusal
  | shape : Nat → Refusal
  | differ : Nat → Refusal

def Refusal.show : Refusal → String
  | .depth => "depth"
  | .noToken p => s!"no token at {p}"
  | .shape p => s!"step at {p} does not apply"
  | .differ p => s!"terms differ at {p}"

def tokAt : List Tok → Nat → Option Tok
  | [], _ => none
  | t :: _, 0 => some t
  | _ :: ts, n + 1 => tokAt ts n

def Tm.beq : Tm → Tm → Bool
  | .lit m, .lit n => m == n
  | .succ a, .succ b => Tm.beq a b
  | .pair a b, .pair c d => Tm.beq a c && Tm.beq b d
  | _, _ => false

mutual
/-- Head reduction, one token per step: `core` contracts `succ (lit n)`. -/
def whnf : Nat → Tm → List Tok → Nat → Except Refusal (Tm × Nat)
  | 0, _, _, _ => .error .depth
  | fuel + 1, t, toks, pos =>
    match tokAt toks pos with
    | some .stop => .ok (t, pos + 1)
    | some .core =>
      match t with
      | .succ (.lit n) => whnf fuel (.lit (n + 1)) toks (pos + 1)
      | .succ a =>
        match whnf fuel a toks (pos + 1) with
        | .ok (a', p) => whnf fuel (.succ a') toks p
        | .error e => .error e
      | _ => .error (.shape pos)
    | some _ => .error (.shape pos)
    | none => .error (.noToken pos)

/-- Conversion: `same` compares as they are, `both` reduces both sides. -/
def conv : Nat → Tm → Tm → List Tok → Nat → Except Refusal Nat
  | 0, _, _, _, _ => .error .depth
  | fuel + 1, a, b, toks, pos =>
    match tokAt toks pos with
    | some .same => if Tm.beq a b then .ok (pos + 1) else .error (.differ pos)
    | some .both =>
      match whnf fuel a toks (pos + 1) with
      | .error e => .error e
      | .ok (a', p) =>
        match whnf fuel b toks p with
        | .error e => .error e
        | .ok (b', q) => conv fuel a' b' toks q
    | some _ => .error (.shape pos)
    | none => .error (.noToken pos)

/-- Size of a term; reads no token and keeps the cursor. -/
def infer : Nat → Tm → List Tok → Nat → Except Refusal (Nat × Nat)
  | 0, _, _, _ => .error .depth
  | fuel + 1, t, toks, pos =>
    match t with
    | .lit _ => .ok (1, pos)
    | .succ a =>
      match infer fuel a toks pos with
      | .ok (n, p) => .ok (n + 1, p)
      | .error e => .error e
    | .pair a b =>
      match infer fuel a toks pos with
      | .error e => .error e
      | .ok (m, p) =>
        match infer fuel b toks p with
        | .error e => .error e
        | .ok (n, q) => .ok (m + n + 1, q)
end

def accepts : Except Refusal Nat → Bool
  | .ok _ => true
  | .error _ => false

def two : Tm := .succ (.succ (.lit 0))

def adv : List Tok := [.both, .core, .core, .stop, .core, .stop, .stop, .same]

theorem corrupt_accepted_by_decide : accepts (conv 10 two (.lit 3) adv 0) = true := by decide

def main : IO Unit := do
  IO.println s!"honest: {accepts (conv 10 two (.lit 2) adv 0)}"
  IO.println s!"corrupt: {accepts (conv 10 two (.lit 3) adv 0)}"
