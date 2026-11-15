section
variable (p : Prop)
def badRec (x : α) (hp : p) : Nat → α
 | 0 => x
 | n + 1 => badRec x hp (n + 1)
end
