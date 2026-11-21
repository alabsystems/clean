section
variable (p : Prop)
def oneOwn (x : α) (hp : p) : α := x
def twoOwn (x : α) (y : β) (hp : p) : β := y
def adjacentOwn {β : Type} (x : α) (y : β) (hp : p) : β := y
end
theorem oneNamed : oneOwn (p := True) (x := 3) (hp := True.intro) = 3 := rfl
theorem twoNamed : twoOwn (p := True) (x := 3) (y := true) (hp := True.intro) = true := rfl
theorem adjacentNamed : adjacentOwn (p := True) (α := Nat) (β := Bool) (x := 3) (y := true) (hp := True.intro) = true := rfl
section
variable (q : α → Prop) (p : Prop)
def capturedNamedOwn (x : α) (y : β) (hp : p) (hq : q x) : β := y
end
theorem capturedNamed : capturedNamedOwn (α := Nat) (q := fun _ => True) (p := True) (β := Bool) (x := 3) (y := true) (hp := True.intro) (hq := True.intro) = true := rfl
