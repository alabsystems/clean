/-!
R4 item (v): the block of item (i) as ONE function over a request sum type,
structurally recursive on the counter (the design's last fallback, 3.2).
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

inductive Req where
  | whnf : Tm → Req
  | conv : Tm → Tm → Req
  | infer : Tm → Req

inductive Resp where
  | term : Tm → Resp
  | done : Resp
  | size : Nat → Resp

inductive Refusal where
  | depth
  | noToken : Nat → Refusal
  | shape : Nat → Refusal
  | differ : Nat → Refusal
  | response : Refusal

def Refusal.show : Refusal → String
  | .depth => "depth"
  | .noToken p => s!"no token at {p}"
  | .shape p => s!"step at {p} does not apply"
  | .differ p => s!"terms differ at {p}"
  | .response => "wrong response"

def tokAt : List Tok → Nat → Option Tok
  | [], _ => none
  | t :: _, 0 => some t
  | _ :: ts, n + 1 => tokAt ts n

def Tm.beq : Tm → Tm → Bool
  | .lit m, .lit n => m == n
  | .succ a, .succ b => Tm.beq a b
  | .pair a b, .pair c d => Tm.beq a c && Tm.beq b d
  | _, _ => false

def run : Nat → Req → List Tok → Nat → Except Refusal (Resp × Nat)
  | 0, _, _, _ => .error .depth
  | fuel + 1, .whnf t, toks, pos =>
    match tokAt toks pos with
    | some .stop => .ok (.term t, pos + 1)
    | some .core =>
      match t with
      | .succ (.lit n) => run fuel (.whnf (.lit (n + 1))) toks (pos + 1)
      | .succ a =>
        match run fuel (.whnf a) toks (pos + 1) with
        | .ok (.term a', p) => run fuel (.whnf (.succ a')) toks p
        | .ok _ => .error .response
        | .error e => .error e
      | _ => .error (.shape pos)
    | some _ => .error (.shape pos)
    | none => .error (.noToken pos)
  | fuel + 1, .conv a b, toks, pos =>
    match tokAt toks pos with
    | some .same => if Tm.beq a b then .ok (.done, pos + 1) else .error (.differ pos)
    | some .both =>
      match run fuel (.whnf a) toks (pos + 1) with
      | .ok (.term a', p) =>
        match run fuel (.whnf b) toks p with
        | .ok (.term b', q) => run fuel (.conv a' b') toks q
        | .ok _ => .error .response
        | .error e => .error e
      | .ok _ => .error .response
      | .error e => .error e
    | some _ => .error (.shape pos)
    | none => .error (.noToken pos)
  | fuel + 1, .infer t, toks, pos =>
    match t with
    | .lit _ => .ok (.size 1, pos)
    | .succ a =>
      match run fuel (.infer a) toks pos with
      | .ok (.size n, p) => .ok (.size (n + 1), p)
      | .ok _ => .error .response
      | .error e => .error e
    | .pair a b =>
      match run fuel (.infer a) toks pos with
      | .ok (.size m, p) =>
        match run fuel (.infer b) toks p with
        | .ok (.size n, q) => .ok (.size (m + n + 1), q)
        | .ok _ => .error .response
        | .error e => .error e
      | .ok _ => .error .response
      | .error e => .error e

def verdict (name : String) (r : Except Refusal (Resp × Nat)) : String :=
  match r with
  | .ok (.done, p) => s!"{name}: ACCEPT cursor={p}"
  | .ok (.size n, p) => s!"{name}: size={n} cursor={p}"
  | .ok (.term _, p) => s!"{name}: term cursor={p}"
  | .error e => s!"{name}: REFUSE {e.show}"

def main : IO Unit := do
  let two := Tm.succ (.succ (.lit 0))
  let adv : List Tok := [.both, .core, .core, .stop, .core, .stop, .stop, .same]
  IO.println (verdict "conv-both" (run 10 (.conv two (.lit 2)) adv 0))
  IO.println (verdict "conv-same" (run 10 (.conv (.lit 2) (.lit 2)) [.same] 0))
  IO.println (verdict "conv-differ" (run 10 (.conv two (.lit 3)) adv 0))
  IO.println (verdict "conv-truncated" (run 10 (.conv two (.lit 2)) [.both, .core] 0))
  IO.println (verdict "conv-wrong-token" (run 10 (.conv two (.lit 2)) [.core] 0))
  IO.println (verdict "conv-depth" (run 2 (.conv two (.lit 2)) adv 0))
  IO.println (verdict "infer" (run 10 (.infer (.pair two (.lit 5))) [] 7))
