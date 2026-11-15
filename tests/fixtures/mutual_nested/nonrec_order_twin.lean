-- The false twin of nonrec_order.
mutual
def useLater : Nat := later + 1
def later : Nat := 41
end
theorem useLater_eq : useLater = 41 := rfl
