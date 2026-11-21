import MachineMemory431

theorem false_overlap_preserved :
    (Trust.A64.s21StorePair Trust.A64.overlapState).mem 32 = 0 := by decide
