-- Producer module for the `end A.B` namespace-pop regression.
--
-- Ground truth, Lean 4.30.0-rc2: `namespace Alpha.Beta` opens BOTH `Alpha` and
-- `Beta`, and `end Alpha.Beta` closes both. So `g_inside` below registers as
-- `Gamma.g_inside`. Popping ONE component leaves `Alpha` open and registers
-- `Alpha.Gamma.g_inside` instead -- a name no importing module can address.
namespace Alpha.Beta

def b_inside : Nat := 1

end Alpha.Beta

namespace Gamma

def g_inside : Nat := 2

end Gamma

def after_everything : Nat := 3
