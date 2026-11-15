def wfOwn (x : α) (n : Nat) : α :=
 if h : 0 < n then wfOwn x (n - 1) else x
termination_by n
def use : Nat := @wfOwn Nat 3 2
