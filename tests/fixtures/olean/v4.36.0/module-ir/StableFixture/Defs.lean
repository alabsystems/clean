module

public meta import Lean

namespace StableFixture
private def offset : Nat := 1
@[inline] public def addOffset (n : Nat) : Nat := n + offset
public def twice (n : Nat) : Nat := n + n
public theorem zeroRefl : (0 : Nat) = 0 := rfl

elab "stable_witness% " n:num : term => return Lean.mkNatLit (n.getNat + 56)
end StableFixture
