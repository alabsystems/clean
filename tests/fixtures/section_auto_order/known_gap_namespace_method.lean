namespace List
section
variable (offset : Nat)
def sectionCount (extra : Nat) : List Nat → Nat
 | [] => offset + extra
 | _ :: tail => tail.sectionCount extra + 1
end
end List
theorem ordinaryMethodUse : List.sectionCount 3 4 [1, 2] = 9 := rfl
