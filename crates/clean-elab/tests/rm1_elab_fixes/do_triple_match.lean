-- RM1 fixture (K5 probe a5): a `match` over three discriminants inside `do`.
inductive V where
  | int (v : Int)
  | bool (b : Bool)
  | vec (xs : List Int)

def addv (tag : Nat) (lhs rhs : V) : Except String Int := do
  let base ← pure (0 : Int)
  match tag, lhs, rhs with
  | t, .vec xs, .vec ys => pure (base + t + xs.length + ys.length)
  | _, .int a, .int b => pure (base + a + b)
  | 0, .bool p, .bool q => pure (if p && q then 1 else 0)
  | _, _, _ => throw "type error"

theorem addv_vec : addv 1 (.vec [1, 2]) (.vec [3]) = .ok 4 := rfl
theorem addv_int : addv 7 (.int 2) (.int 3) = .ok 5 := rfl
theorem addv_bool : addv 0 (.bool true) (.bool true) = .ok 1 := rfl
theorem addv_err : addv 1 (.bool true) (.bool true) = .error "type error" := rfl

-- K5 probe a5 verbatim (2026-07-02 report §4.4, semBinOp's shape).
inductive A5Val where
  | int (v : Int)
  | bool (b : Bool)

def a5Add (tag : Nat) (lhs rhs : A5Val) : Except String Int := do
  let base ← pure (0 : Int)
  match tag, lhs, rhs with
  | 0, .int a, .int b => pure (base + a + b)
  | _, _, _ => throw "type error"

theorem a5Add_ok : a5Add 0 (.int 2) (.int 3) = .ok 5 := rfl
theorem a5Add_tag : a5Add 1 (.int 2) (.int 3) = .error "type error" := rfl
