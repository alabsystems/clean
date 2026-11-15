section
variable (p : Prop)
def wfOwn (x : α) (hp : p) (n : Nat) : α :=
 if h : 0 < n then wfOwn p x hp (n - 1) else x
termination_by n
end
def use : Nat := @wfOwn True Nat 3 True.intro 2
