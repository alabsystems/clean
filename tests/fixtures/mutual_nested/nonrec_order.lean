-- Non-recursive `mutual` blocks: independent members, and a FIRST member that
-- alone names the second (registered in dependency order).
mutual
def twoA : Nat := 2
def twoB : Nat := 3
end
mutual
def useLater : Nat := later + 1
def later : Nat := 41
end
theorem useLater_eq : useLater = 42 := rfl
