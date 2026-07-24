/-!
LLVM2-style denotation preservation toy.
-/

set_option autoImplicit false

namespace Mathbot.Tasks.Llvm2

def sourceAddKernel (x y : Nat) : Nat :=
  x + (y + 1)

def loweredAddKernel (x y : Nat) : Nat :=
  x + y + 1

theorem llvm2_add_kernel_denotation_preserved
    (x y : Nat) :
    loweredAddKernel x y = sourceAddKernel x y := by
  unfold loweredAddKernel sourceAddKernel
  rw [Nat.add_assoc]

end Mathbot.Tasks.Llvm2
