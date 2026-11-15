theorem single : ∀ n : Nat, n + 0 = n
  | 0 => rfl
  | n + 1 => by exact congrArg Nat.succ (single n)

theorem byCases (n : Nat) : n + 0 = n := by
  cases n with
  | zero => rfl
  | succ k => exact congrArg Nat.succ (byCases k)

section
variable (p : Prop)
theorem captured (x : α) (hp : p) : ∀ n : Nat, x = x
  | 0 => rfl
  | n + 1 => by exact @captured α x hp n
end

theorem capturedUse : (3 : Nat) = 3 := captured True 3 True.intro 2

section
variable (p : α → Prop)
theorem capturedAuto (x : α) (hp : p x) : ∀ n : Nat, p x
  | 0 => hp
  | n + 1 => by exact @capturedAuto x hp n
theorem mixedAuto (x : α) (y : β) (hp : p x) : ∀ n : Nat, y = y
  | 0 => rfl
  | n + 1 => by exact @mixedAuto β x y hp n
end

theorem capturedAutoUse : True :=
  capturedAuto (fun (_ : Nat) => True) 3 True.intro 2
theorem mixedAutoUse : (3 : Nat) = 3 :=
  mixedAuto (fun (_ : Nat) => True) 4 3 True.intro 2

/-- info: 'single' does not depend on any axioms -/
#guard_msgs in
#print axioms single
/-- info: 'captured' does not depend on any axioms -/
#guard_msgs in
#print axioms captured
/-- info: 'capturedUse' does not depend on any axioms -/
#guard_msgs in
#print axioms capturedUse
/-- info: 'capturedAuto' does not depend on any axioms -/
#guard_msgs in
#print axioms capturedAuto
/-- info: 'mixedAuto' does not depend on any axioms -/
#guard_msgs in
#print axioms mixedAuto
