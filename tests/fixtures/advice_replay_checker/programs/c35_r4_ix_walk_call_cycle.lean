/-!
R4 item (ix), from the design's Revision 2: a list-iterating member of the
block (the walk of 2.3.1). At `fuel + 1` it handles one `(argument, label)`
pair, calls another member (`conv`) at `fuel`, and calls itself at `fuel` on
the rest, so every member recurses on the shared counter, not on the list.
-/

inductive Tok where
  | core
  | stop
  | same
  | both
  | inspect

inductive Tm where
  | lit : Nat → Tm
  | succ : Tm → Tm

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
  | _, _ => false

mutual
def whnf : Nat → Tm → List Tok → Nat → Except Refusal (Tm × Nat)
  | 0, _, _, _ => .error .depth
  | fuel + 1, t, toks, pos =>
    match tokAt toks pos with
    | some .inspect =>
      match walk fuel [(t, t)] toks (pos + 1) with
      | .ok p => .ok (t, p)
      | .error e => .error e
    | some .stop => .ok (t, pos + 1)
    | some .core =>
      match t with
      | .succ (.lit n) => whnf fuel (.lit (n + 1)) toks (pos + 1)
      | _ => .error (.shape pos)
    | some _ => .error (.shape pos)
    | none => .error (.noToken pos)
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
/-- Check every argument against its label, one pair per call. -/
def walk : Nat → List (Tm × Tm) → List Tok → Nat → Except Refusal Nat
  | 0, _, _, _ => .error .depth
  | _ + 1, [], _, pos => .ok pos
  | fuel + 1, (arg, label) :: rest, toks, pos =>
    match conv fuel arg label toks pos with
    | .error e => .error e
    | .ok p => walk fuel rest toks p
end

def verdict (name : String) (r : Except Refusal Nat) : String :=
  match r with
  | .ok p => s!"{name}: ACCEPT cursor={p}"
  | .error e => s!"{name}: REFUSE {e.show}"

def main : IO Unit := do
  let pairs : List (Tm × Tm) := [(.lit 3, .lit 3), (.succ (.lit 1), .lit 2), (.lit 0, .lit 0)]
  let adv : List Tok := [.same, .both, .core, .stop, .stop, .same, .same]
  IO.println (verdict "walk-three" (walk 10 pairs adv 0))
  IO.println (verdict "walk-empty" (walk 1 [] [] 4))
  IO.println (verdict "walk-bad-label" (walk 10 [(.lit 3, .lit 3), (.succ (.lit 1), .lit 5)] adv 0))
  IO.println (verdict "walk-depth" (walk 3 pairs adv 0))

  match whnf 20 (.lit 2) [.inspect, .both, .stop, .stop, .same] 0 with
  | .ok (_, p) => IO.println s!"cycle: ACCEPT cursor={p}"
  | .error e => IO.println s!"cycle: REFUSE {e.show}"

  match whnf 20 (.lit 2) [.inspect] 0 with
  | .ok (_, p) => IO.println s!"cycle-truncated: ACCEPT cursor={p}"
  | .error e => IO.println s!"cycle-truncated: REFUSE {e.show}"
  match whnf 2 (.lit 2) [.inspect, .both, .stop, .stop, .same] 0 with
  | .ok (_, p) => IO.println s!"cycle-depth: ACCEPT cursor={p}"
  | .error e => IO.println s!"cycle-depth: REFUSE {e.show}"
