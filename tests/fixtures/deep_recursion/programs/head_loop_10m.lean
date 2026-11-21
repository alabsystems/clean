/-!
X4 deep-recursion regression (c27 at 10⁷). R4 item (iv): a head loop of 10⁷ self tail calls. A run of `n` head steps is
a chain of `n` calls of `whnf`, structurally recursive on the counter, so the
recursive call must compile to a loop. The advice is `core` below `n` and
`stop` from there; the term stays small, so only the call chain is deep.
-/

inductive Tm where
  | lit : Nat → Tm
  | succ : Tm → Tm

def coreAt (n pos : Nat) : Bool := pos < n

def headLoop : Nat → Nat → Tm → Nat → Except String (Tm × Nat)
  | 0, _, _, _ => .error "depth"
  | fuel + 1, n, t, pos =>
    if coreAt n pos then
      match t with
      | .lit k => headLoop fuel n (.lit (k + 1)) (pos + 1)
      | .succ a => headLoop fuel n a (pos + 1)
    else .ok (t, pos)

def verdict (r : Except String (Tm × Nat)) : String :=
  match r with
  | .ok (.lit k, p) => s!"ACCEPT lit {k} cursor={p}"
  | .ok (.succ _, p) => s!"ACCEPT succ cursor={p}"
  | .error e => s!"REFUSE {e}"

def main : IO Unit := do
  IO.println (verdict (headLoop 10000001 10000000 (.lit 0) 0))
  IO.println (verdict (headLoop 10000000 10000000 (.lit 0) 0))
  IO.println (verdict (headLoop 10 3 (.succ (.succ (.lit 5))) 0))
