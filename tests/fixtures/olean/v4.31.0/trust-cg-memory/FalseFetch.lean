import MachineFetch431

theorem false_fetch_preserved :
    (Trust.A64.s21StorePair Trust.A64.overlapState).readMem 32 4 = 0 := by decide
