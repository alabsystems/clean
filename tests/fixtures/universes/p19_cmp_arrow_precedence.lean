-- infix:50 comparisons bind TIGHTER than → (Lean precedence): every
-- `a REL b → c` is `(a REL b) → c`. Was misparsed as `a REL (b → c)`
-- for ≠ < ≤ > ≥ == ∈ ∉ ⊆ ⊂ ∣ (only = had the arrow-tail split).
-- Found by the Iris scoping lane, fixed 2026-08-08.
def c1 : (x : Nat) → Nat.le x x → Nat := fun x _ => x
def c2 (P : Prop) : Nat.zero < Nat.succ Nat.zero → P → P := fun _ p => p
def c3 (P : Prop) : Nat.zero ≤ Nat.zero → P → P := fun _ p => p
def c4 (s t : Prop) : s ∈ ([s] : List Prop) → t → t := fun _ p => p
def t1 (a b : Nat) (h : a ≠ b) : Nat := a
def t2 : (x : Nat) → x ≠ Nat.zero → Nat := fun x _ => x
theorem t3 (a b : Nat) (h : a ≠ b) : b ≠ a → True := fun _ => True.intro
