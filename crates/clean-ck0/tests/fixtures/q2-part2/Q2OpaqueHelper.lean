import Init.Prelude
namespace Q2Opaque
opaque brecOn : Nat := 0
end Q2Opaque
theorem q2OpaqueSelf : Q2Opaque.brecOn = Q2Opaque.brecOn := rfl
