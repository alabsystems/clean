/-!
A toy advice-replaying checker (unit X1 of the self-proof execution plan).

`Tm` is a de Bruijn lambda calculus with `Nat` literals, successor and
addition. An untrusted producer hands the checker a term, a claimed normal
form and a list of reduction steps (the advice). The checker replays the
advice one step at a time and never searches. It accepts only when the
replayed term is structurally equal to the claim and the claim has no redex
left; any other advice is refused with the reason.

`main` prints one verdict line per embedded case. The cases whose name starts
with `corrupt-` carry advice or a claim that must be refused.
-/

inductive Tm where
  | var : Nat → Tm
  | app : Tm → Tm → Tm
  | lam : Tm → Tm
  | lit : Nat → Tm
  | succ : Tm → Tm
  | add : Tm → Tm → Tm

/-- One move from a term to a direct subterm. -/
inductive Dir where
  | fn
  | arg
  | body

/-- The reduction rules the advice may name. -/
inductive Rule where
  | beta
  | succLit
  | addLit

/-- One advice step: contract the redex at `path` by `rule`. -/
structure Step where
  path : List Dir
  rule : Rule

/-- Why the checker refused. -/
inductive Refusal where
  | outOfFuel : Nat → Refusal
  | badPath : Nat → Refusal
  | ruleDoesNotApply : Nat → Rule → Refusal
  | mismatch : Refusal
  | claimNotNormal : Refusal

namespace Tm

def beq : Tm → Tm → Bool
  | var i, var j => i == j
  | app f a, app g b => beq f g && beq a b
  | lam b, lam c => beq b c
  | lit m, lit n => m == n
  | succ a, succ b => beq a b
  | add a b, add c d => beq a c && beq b d
  | _, _ => false

/-- Add `d` to every variable at or above the cutoff `c`. -/
def shift (d : Nat) : Nat → Tm → Tm
  | c, var i => if i < c then var i else var (i + d)
  | c, app f a => app (shift d c f) (shift d c a)
  | c, lam b => lam (shift d (c + 1) b)
  | _, lit n => lit n
  | c, succ a => succ (shift d c a)
  | c, add a b => add (shift d c a) (shift d c b)

/-- Replace variable `k` by `s` and lower the variables above it. -/
def subst (s : Tm) : Nat → Tm → Tm
  | k, var i =>
    if i < k then var i
    else if i == k then shift k 0 s
    else var (i - 1)
  | k, app f a => app (subst s k f) (subst s k a)
  | k, lam b => lam (subst s (k + 1) b)
  | _, lit n => lit n
  | k, succ a => succ (subst s k a)
  | k, add a b => add (subst s k a) (subst s k b)

def isLit : Tm → Bool
  | lit _ => true
  | _ => false

/--
`true` when no rule applies anywhere in the term.

The `succ` redex is tested through `isLit` and not by the nested pattern
`succ (lit _)` that the `app` and `add` rows use: both native lanes refuse
that row today (gap `rc-linearity-nested-pattern-under-unary-ctor` in
`data/kcheck_execution_gaps.json`, probe `c03_nested_overlapping_patterns`).
-/
def isNormal : Tm → Bool
  | var _ => true
  | app (lam _) _ => false
  | app f a => isNormal f && isNormal a
  | lam b => isNormal b
  | lit _ => true
  | succ a => !a.isLit && isNormal a
  | add (lit _) (lit _) => false
  | add a b => isNormal a && isNormal b

def render : Tm → String
  | var i => "#" ++ toString i
  | app f a => "(" ++ render f ++ " " ++ render a ++ ")"
  | lam b => "(fun " ++ render b ++ ")"
  | lit n => toString n
  | succ a => "(succ " ++ render a ++ ")"
  | add a b => "(" ++ render a ++ " + " ++ render b ++ ")"

end Tm

def Rule.name : Rule → String
  | .beta => "beta"
  | .succLit => "succLit"
  | .addLit => "addLit"

/-- Contract the redex at the root, or say that the rule does not apply. -/
def contract : Rule → Tm → Option Tm
  | .beta, .app (.lam b) a => some (Tm.subst a 0 b)
  | .succLit, .succ (.lit n) => some (.lit (n + 1))
  | .addLit, .add (.lit m) (.lit n) => some (.lit (m + n))
  | _, _ => none

/-- Walk `path`, contract there, rebuild the term around the result. -/
def stepAt (idx : Nat) (rule : Rule) : List Dir → Tm → Except Refusal Tm
  | [], t =>
    match contract rule t with
    | some t' => .ok t'
    | none => .error (.ruleDoesNotApply idx rule)
  | .fn :: rest, .app f a => do
    let f' ← stepAt idx rule rest f
    pure (.app f' a)
  | .arg :: rest, .app f a => do
    let a' ← stepAt idx rule rest a
    pure (.app f a')
  | .body :: rest, .lam b => do
    let b' ← stepAt idx rule rest b
    pure (.lam b')
  | .arg :: rest, .succ a => do
    let a' ← stepAt idx rule rest a
    pure (.succ a')
  | .fn :: rest, .add a b => do
    let a' ← stepAt idx rule rest a
    pure (.add a' b)
  | .arg :: rest, .add a b => do
    let b' ← stepAt idx rule rest b
    pure (.add a b')
  | _ :: _, _ => .error (.badPath idx)

/-- Replay the advice. `fuel` bounds the number of steps taken. -/
def replay : Nat → Nat → List Step → Tm → Except Refusal Tm
  | _, _, [], t => .ok t
  | 0, idx, _ :: _, _ => .error (.outOfFuel idx)
  | fuel + 1, idx, s :: rest, t => do
    let t' ← stepAt idx s.rule s.path t
    replay fuel (idx + 1) rest t'

/-- The checker: accept exactly when the advice leads to the claim. -/
def check (fuel : Nat) (start claim : Tm) (advice : List Step) : Except Refusal Tm := do
  let reached ← replay fuel 0 advice start
  if !(Tm.beq reached claim) then
    throw .mismatch
  if !(Tm.isNormal claim) then
    throw .claimNotNormal
  pure reached

def Refusal.render : Refusal → String
  | .outOfFuel i => "out of fuel at step " ++ toString i
  | .badPath i => "step " ++ toString i ++ " leaves the term"
  | .ruleDoesNotApply i r => "step " ++ toString i ++ ": " ++ r.name ++ " does not apply"
  | .mismatch => "replayed term is not the claim"
  | .claimNotNormal => "claim is not a normal form"

structure Case where
  name : String
  fuel : Nat
  start : Tm
  claim : Tm
  advice : List Step

def verdictLine (c : Case) : String :=
  match check c.fuel c.start c.claim c.advice with
  | .ok t =>
    c.name ++ ": ACCEPT steps=" ++ toString c.advice.length ++ " nf=" ++ t.render
  | .error r => c.name ++ ": REFUSE " ++ r.render

def two64 : Nat := 18446744073709551616

/-- `fun f x => f (f x)` -/
def twice : Tm := .lam (.lam (.app (.var 1) (.app (.var 1) (.var 0))))

def succFn : Tm := .lam (.succ (.var 0))

def twiceSuccStart : Tm := .app (.app twice succFn) (.lit 40)

def twiceSuccAdvice : List Step :=
  [ ⟨[.fn], .beta⟩,
    ⟨[], .beta⟩,
    ⟨[.arg], .beta⟩,
    ⟨[.arg], .succLit⟩,
    ⟨[], .beta⟩,
    ⟨[], .succLit⟩ ]

def cases : List Case :=
  [ { name := "beta-root", fuel := 8,
      start := .app (.lam (.var 0)) (.lit 5), claim := .lit 5,
      advice := [⟨[], .beta⟩] },
    { name := "add-small", fuel := 8,
      start := .add (.lit 2) (.lit 3), claim := .lit 5,
      advice := [⟨[], .addLit⟩] },
    { name := "add-bignat", fuel := 8,
      start := .add (.lit two64) (.add (.lit two64) (.lit 7)),
      claim := .lit 36893488147419103239,
      advice := [⟨[.arg], .addLit⟩, ⟨[], .addLit⟩] },
    { name := "succ-bignat", fuel := 8,
      start := .succ (.lit 18446744073709551615), claim := .lit two64,
      advice := [⟨[], .succLit⟩] },
    { name := "twice-succ", fuel := 8,
      start := twiceSuccStart, claim := .lit 42,
      advice := twiceSuccAdvice },
    { name := "under-binder", fuel := 8,
      start := .lam (.app (.lam (.app (.var 1) (.var 0))) (.var 0)),
      claim := .lam (.app (.var 0) (.var 0)),
      advice := [⟨[.body], .beta⟩] },
    { name := "capture-shift", fuel := 8,
      start := .lam (.app (.lam (.lam (.var 1))) (.var 0)),
      claim := .lam (.lam (.var 1)),
      advice := [⟨[.body], .beta⟩] },
    { name := "open-stuck", fuel := 8,
      start := .app (.var 3) (.add (.lit 1) (.lit 1)),
      claim := .app (.var 3) (.lit 2),
      advice := [⟨[.arg], .addLit⟩] },
    { name := "empty-advice", fuel := 0,
      start := .lit 9, claim := .lit 9, advice := [] },
    { name := "corrupt-wrong-rule", fuel := 8,
      start := .add (.lit 2) (.lit 3), claim := .lit 5,
      advice := [⟨[], .beta⟩] },
    { name := "corrupt-bad-path", fuel := 8,
      start := .add (.lit 2) (.lit 3), claim := .lit 5,
      advice := [⟨[.body], .addLit⟩] },
    { name := "corrupt-swapped-steps", fuel := 8,
      start := twiceSuccStart, claim := .lit 42,
      advice := [⟨[], .beta⟩, ⟨[.fn], .beta⟩] },
    { name := "corrupt-truncated", fuel := 8,
      start := twiceSuccStart, claim := .lit 42,
      advice := twiceSuccAdvice.take 5 },
    { name := "corrupt-claim-off-by-one", fuel := 8,
      start := .add (.lit two64) (.lit two64),
      claim := .lit 36893488147419103233,
      advice := [⟨[], .addLit⟩] },
    { name := "corrupt-claim-not-normal", fuel := 8,
      start := .add (.lit 1) (.lit 1), claim := .add (.lit 1) (.lit 1),
      advice := [] },
    { name := "corrupt-fuel-short", fuel := 3,
      start := twiceSuccStart, claim := .lit 42,
      advice := twiceSuccAdvice },
    { name := "corrupt-capture", fuel := 8,
      start := .lam (.app (.lam (.lam (.var 1))) (.var 0)),
      claim := .lam (.lam (.var 0)),
      advice := [⟨[.body], .beta⟩] } ]

def main : IO Unit := do
  for c in cases do
    IO.println (verdictLine c)
