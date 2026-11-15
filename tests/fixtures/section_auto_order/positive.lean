section
variable (p : Prop)
theorem own (x : α) (hp : p) : x = x := rfl
def identityOwn (x : α) (hp : p) : α := x
theorem equationOwn (x : α) (hp : p) : ∀ n : Nat, x = x
 | 0 => rfl
 | n + 1 => by rfl
theorem recursiveOwn (x : α) (hp : p) : ∀ n : Nat, x = x
 | 0 => rfl
 | n + 1 => by exact @recursiveOwn α x hp n
end
theorem use : (3 : Nat) = 3 := @own True Nat 3 True.intro
theorem useIdentity : @identityOwn True Nat 3 True.intro = 3 := rfl
theorem named : identityOwn (p := True) (x := 3) (hp := True.intro) = 3 := rfl
theorem useEquation : (3 : Nat) = 3 := @equationOwn True Nat 3 True.intro 2
theorem useRecursive : (3 : Nat) = 3 := @recursiveOwn True Nat 3 True.intro 2
section
variable (q : α → Prop)
section
variable (p : Prop)
theorem capturedOwn (x : α) (y : β) (hp : p) (hq : q x) : y = y := rfl
theorem capturedRecursive (x : α) (y : β) (hp : p) (hq : q x) : ∀ n : Nat, y = y
 | 0 => rfl
 | n + 1 => by exact @capturedRecursive β x y hp hq n
end
end
theorem useCaptured : true = true := @capturedOwn Nat (fun _ => True) True Bool 3 true True.intro True.intro
theorem useCapturedRecursive : true = true := @capturedRecursive Nat (fun _ => True) True Bool 3 true True.intro True.intro 2
section
variable (A : Type) (f : A → Type)
def dependent (x : f a) : f a := x
end
theorem useDependent : @dependent Nat (fun _ => Nat) 2 3 = 3 := rfl
/-- info: 'own' does not depend on any axioms -/
#guard_msgs in
#print axioms own
/-- info: 'recursiveOwn' does not depend on any axioms -/
#guard_msgs in
#print axioms recursiveOwn
/-- info: 'useCapturedRecursive' does not depend on any axioms -/
#guard_msgs in
#print axioms useCapturedRecursive
section
variable (A : Type) (f : A → Type)
theorem dependentRecursive (x : f a) : ∀ n : Nat, x = x
 | 0 => rfl
 | n + 1 => by exact @dependentRecursive a x n
end
theorem useDependentRecursive : (3 : Nat) = 3 := @dependentRecursive Nat (fun _ => Nat) 2 3 2
section
variable (p : Prop)
theorem severalOwn (n : Nat) (x : α) (y : β) (hp : p) : x = x := rfl
end
theorem useSeveralOwn : (3 : Nat) = 3 := @severalOwn True Nat Bool 0 3 true True.intro
/-- info: 'dependentRecursive' does not depend on any axioms -/
#guard_msgs in
#print axioms dependentRecursive
