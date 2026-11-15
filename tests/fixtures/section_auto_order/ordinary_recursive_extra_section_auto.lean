section
variable (q : α → Prop) (p : Prop)
def ordinaryMixed (x : α) (y : β) (hp : p) (hq : q x) : Nat → β
 | 0 => y
 | n + 1 => @ordinaryMixed α β x y hp hq n
end
