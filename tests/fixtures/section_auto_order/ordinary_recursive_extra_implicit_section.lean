section
variable {α : Type}
def recLength : List α → Nat
 | [] => 0
 | _ :: tail => @recLength α tail + 1
end
theorem use : recLength [1, 2] = 2 := rfl
