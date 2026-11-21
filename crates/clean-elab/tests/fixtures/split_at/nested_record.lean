inductive BinOp where | bAnd | bOr
inductive Ty where | bool | nat
inductive Inst where | other | binop (op : BinOp) (ty : Ty) (left right : Nat)
structure Node where
  inst : Inst
  results : List Nat

/-- A structural reader over the canonical SemR node, not another evaluator. -/
def readAndNode (node : Node) : Option (Nat × Nat × Nat) :=
  match node with
  | ⟨.binop .bAnd .bool left right, [result]⟩ => some (left, right, result)
  | _ => none

theorem readAndNode_sound {node : Node} {left right result : Nat}
    (h : readAndNode node = some (left, right, result)) :
    node.inst = .binop .bAnd .bool left right ∧ node.results = [result] := by
  unfold readAndNode at h
  split at h <;> simp_all
