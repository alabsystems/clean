prelude
import Init.Notation

/-! An `@[implemented_by]` binding written on its declaration inside a macro. The macro's own
names are hygienic, so the bound declaration's name ends in a number
(`hygSlow._@.LateHyg.<hash>._hygCtx._hyg.<n>`), the shape of the `TypeName` instances pinned
`Std` derives; the caller's name comes from the macro's argument and is plain. -/

def hygFast (n : Nat) : Nat := Nat.add n 1

macro "declare_hyg " caller:ident : command =>
  `(@[implemented_by hygFast] def hygSlow (n : Nat) : Nat := Nat.add n 2
    def $(⟨caller.raw⟩) (n : Nat) : Nat := Nat.mul (hygSlow n) 10)

declare_hyg hygCaller
