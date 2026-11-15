/-!
R4 item (x), from the design's Revision 2: a report accumulator threaded
through every member's `Except` result. Each member takes the report so far
and returns it extended; the head loop carries it through 10⁶ self tail
calls and must still compile to a loop.
-/

inductive Tm where
  | lit : Nat → Tm
  | succ : Tm → Tm

/-- The report: head steps taken and the largest literal reached. -/
structure Report where
  steps : Nat
  maxLit : Nat

def Report.note (r : Report) (k : Nat) : Report :=
  { steps := r.steps + 1, maxLit := if k > r.maxLit then k else r.maxLit }

def Tm.beq : Tm → Tm → Bool
  | .lit m, .lit n => m == n
  | .succ a, .succ b => Tm.beq a b
  | _, _ => false

mutual
/-- Head loop: the advice is `core` below `n`, then `stop`. -/
def whnf : Nat → Nat → Tm → Nat → Report → Except String (Tm × Nat × Report)
  | 0, _, _, _, _ => .error "depth"
  | fuel + 1, n, t, pos, rep =>
    if pos < n then
      match t with
      | .lit k => whnf fuel n (.lit (k + 1)) (pos + 1) (rep.note (k + 1))
      | .succ a =>
        match walk fuel n [(a, a)] (pos + 1) (rep.note 0) with
        | .error e => .error e
        | .ok (p, rep') => whnf fuel n a p rep' 
    else .ok (t, pos, rep)
termination_by structural fuel _ _ _ _ => fuel
def conv : Nat → Nat → Tm → Tm → Nat → Report → Except String (Nat × Report)
  | 0, _, _, _, _, _ => .error "depth"
  | fuel + 1, n, a, b, pos, rep =>
    match whnf fuel n a pos rep with
    | .error e => .error e
    | .ok (a', p, rep') =>
      if Tm.beq a' b then .ok (p, rep') else .error "sides differ"
termination_by structural fuel _ _ _ _ _ => fuel
def walk : Nat → Nat → List (Tm × Tm) → Nat → Report → Except String (Nat × Report)
  | 0, _, _, _, _ => .error "depth"
  | _ + 1, _, [], pos, rep => .ok (pos, rep)
  | fuel + 1, n, (a, b) :: rest, pos, rep =>
    match conv fuel n a b pos rep with
    | .error e => .error e
    | .ok (p, rep') => walk fuel n rest p rep'
termination_by structural fuel _ _ _ _ => fuel
end

def verdict (name : String) (r : Except String (Nat × Report)) : String :=
  match r with
  | .ok (p, rep) => s!"{name}: ACCEPT cursor={p} steps={rep.steps} max={rep.maxLit}"
  | .error e => s!"{name}: REFUSE {e}"

def main : IO Unit := do
  let start : Report := { steps := 0, maxLit := 0 }
  IO.println (verdict "million-steps" (conv 1000002 1000000 (.lit 0) (.lit 1000000) 0 start))
  IO.println (verdict "walk" (walk 10 3 [(.succ (.succ (.lit 7)), .lit 8), (.lit 9, .lit 9)] 0 start))
  IO.println (verdict "differ" (conv 10 2 (.lit 0) (.lit 3) 0 start))
  IO.println (verdict "depth" (conv 1000000 1000000 (.lit 0) (.lit 1000000) 0 start))

  match whnf 20 1 (.succ (.lit 2)) 0 start with
  | .ok (_, p, rep) => IO.println (verdict "cycle" (.ok (p, rep)))
  | .error e => IO.println (verdict "cycle" (.error e))
  match whnf 2 1 (.succ (.lit 2)) 0 start with
  | .ok (_, p, rep) => IO.println (verdict "cycle-depth" (.ok (p, rep)))
  | .error e => IO.println (verdict "cycle-depth" (.error e))
