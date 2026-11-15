section
variable (q : α → Prop) (p : Prop)
theorem capturedOwn (x : α) (y : β) (hp : p) (hq : q x) : y = y := rfl
end
theorem bad : true = true := @capturedOwn Nat Bool (fun _ => True) True 3 true True.intro True.intro
