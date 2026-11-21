prelude
import Init.Prelude
-- Genuine persistent compiler metadata; all equalities proved by reflexivity.
def slow : Nat := 1
def fast : Nat := 1
@[csimp] theorem slow_eq_fast : Eq slow fast := Eq.refl slow
namespace Scoped
def slow : Nat := 2
def fast : Nat := 2
@[scoped csimp] theorem slow_eq_fast : Eq slow fast := Eq.refl slow
end Scoped
namespace Local
def slow : Nat := 3
def fast : Nat := 3
theorem slow_eq_fast : Eq slow fast := Eq.refl slow
attribute [local csimp] slow_eq_fast
end Local

-- InlineAttrs must be decoded even without any implementedBy entries.
@[macro_inline] def macroIgnore (_ : Nat) : Nat := 0
