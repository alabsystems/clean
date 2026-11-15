section
variable (p : Prop)
def ordinaryOwn (x : α) (hp : p) : Nat → α
 | 0 => x
 | n + 1 => ordinaryOwn x hp n
end
theorem ordinaryUse : @ordinaryOwn True Nat 3 True.intro 2 = 3 := rfl
section
variable {α : Type}
def ordinaryLength : List α → Nat
 | [] => 0
 | _ :: tail => @ordinaryLength tail + 1
end
theorem ordinaryLengthUse : @ordinaryLength Nat [1, 2] = 2 := rfl
section
variable (A : Type) (f : A → Type)
def ordinaryDependent (x : f a) : Nat → f a
 | 0 => x
 | n + 1 => @ordinaryDependent a x n
end
theorem ordinaryDependentUse : @ordinaryDependent Nat (fun _ => Nat) 2 3 2 = 3 := rfl
section
variable (offset : Nat)
def List.sectionCount (extra : Nat) : List Nat → Nat
 | [] => offset + extra
 | _ :: tail => tail.sectionCount extra + 1
end
theorem ordinaryMethodUse : List.sectionCount 3 4 [1, 2] = 9 := rfl
section
variable (q : α → Prop) (p : Prop)
def ordinaryMixed (x : α) (y : β) (hp : p) (hq : q x) : Nat → β
 | 0 => y
 | n + 1 => @ordinaryMixed β x y hp hq n
end
theorem ordinaryMixedUse : @ordinaryMixed Nat (fun _ => True) True Bool 3 true True.intro True.intro 2 = true := rfl
section
variable (p : Prop) [Decidable p]
def ordinaryDecide : Nat → Bool
 | 0 => decide p
 | n + 1 => @ordinaryDecide n
end
theorem ordinaryDecideUse : ordinaryDecide True 2 = true := rfl
/-- info: 'ordinaryMixed' does not depend on any axioms -/
#guard_msgs in
#print axioms ordinaryMixed
/-- info: 'ordinaryDecide' does not depend on any axioms -/
#guard_msgs in
#print axioms ordinaryDecide
