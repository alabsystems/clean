import Sib
import Sub.part
inductive Unary | zero | succ (n : Unary)
def Probe.count : Unary → Nat
  | .zero => 0
  | .succ n => Probe.count n + 1
theorem Probe.count_zero : Probe.count .zero = 0 := rfl
class Probe.Cls (α : Type) where
  val : α
instance (priority := 731) Probe.instCls : Probe.Cls Nat := ⟨3⟩
@[simp] theorem Probe.lem : Probe.count .zero = 0 := rfl
namespace Probe.Exports
def «target.dot» : Type := sibTag
end Probe.Exports
export Probe.Exports («target.dot»)
opaque Probe.op : Nat
axiom Probe.ax : Nat
def Probe.nested : Type := nestedTag
def Probe.letProbe (x : Nat) : Nat := let y := x + 1; y * 2
def Probe.strLit : String := "hé"
