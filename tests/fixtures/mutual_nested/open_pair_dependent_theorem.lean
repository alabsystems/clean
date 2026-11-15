-- OPEN (design §5.4): a theorem block whose recursion goes through the pair
-- intermediate under a DEPENDENT motive. Lean 4.8 accepts it by well-founded
-- recursion; Clean's lift refuses dependent motives through an intermediate.
inductive C where
  | int : Nat → C
  | record : List (Nat × C) → C
mutual
def C.sz : C → Nat
  | .int n => n
  | .record fs => C.fsz fs
def C.fsz : List (Nat × C) → Nat
  | [] => 0
  | (_, c) :: fs => C.sz c + C.fsz fs
end
mutual
theorem C.sz_self : ∀ c : C, C.sz c = C.sz c
  | .int _ => rfl
  | .record fs => (fun _ => rfl) (C.fsz_self fs)
theorem C.fsz_self : ∀ fs : List (Nat × C), C.fsz fs = C.fsz fs
  | [] => rfl
  | (_, c) :: fs => (fun _ _ => rfl) (C.sz_self c) (C.fsz_self fs)
end
