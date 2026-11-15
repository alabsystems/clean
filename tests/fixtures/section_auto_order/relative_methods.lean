namespace SectionRouting
inductive Node where
 | leaf : Node
 | node : Node → Node
def Node.relative (k : Nat) : Node → Nat
 | .leaf => k
 | .node tail => Node.relative k tail + 1
def Node.absolute (k : Nat) : Node → Nat
 | .leaf => k
 | .node tail => SectionRouting.Node.absolute k tail + 1
def Node.method (k : Nat) : Node → Nat
 | .leaf => k
 | .node tail => tail.method k + 1
theorem relativeUse : Node.relative 3 (.node (.node .leaf)) = 5 := rfl
theorem absoluteUse : Node.absolute 3 (.node (.node .leaf)) = 5 := rfl
theorem methodUse : Node.method 3 (.node (.node .leaf)) = 5 := rfl
end SectionRouting
