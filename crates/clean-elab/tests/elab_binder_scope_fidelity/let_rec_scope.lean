-- A `let rec go` inside a `where` helper whose sibling helper is also `go`.
def twoGoS (limit : Nat) : Nat :=
  go limit + other limit
where
  go : Nat → Nat
    | 0 => 100
    | k + 1 => go k
  other (n : Nat) : Nat :=
    let rec go : Nat → Nat
      | 0 => 0
      | k + 1 => go k + 1
    go n

theorem twoGoS_three : twoGoS 3 = 103 := by decide
theorem other_three : twoGoS.other 3 = 3 := by decide
theorem other_go_three : twoGoS.other.go 3 = 3 := by decide

-- The same inside a namespace, over a list.
namespace N
def tg (limit : Nat) : Nat := go limit + other limit
where
  go : Nat → Nat
    | 0 => 100
    | k + 1 => go k
  other (n : Nat) : Nat :=
    let rec go : List Nat → Nat
      | [] => 0
      | x :: xs => x + go xs
    go (List.replicate n 2)
end N

theorem tg_other_three : N.tg.other 3 = 6 := by decide

-- A `let rec go` shadows a parameter `go` of the enclosing definition.
def paramGo (go : Nat → Nat) : Nat :=
  let rec go : Nat → Nat
    | 0 => 0
    | k + 1 => go k + 1
  go 3

theorem paramGo_three : paramGo (· + 100) = 3 := by decide

-- A top-level definition's own parameter still shadows its name.
def selfParam (selfParam : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => selfParam k + 1

theorem selfParam_three : selfParam (· + 100) 3 = 103 := by decide

-- A helper's own parameter, and a pattern variable, still shadow a sibling.
def shadows (n : Nat) : Nat := go n + other n + third 5 n
where
  go : Nat → Nat
    | 0 => 100
    | k + 1 => go k
  other : Nat → Nat
    | 0 => 0
    | go + 1 => go
  third (go : Nat) (n : Nat) : Nat := go + n

theorem shadows_five : shadows 5 = 114 := by decide
