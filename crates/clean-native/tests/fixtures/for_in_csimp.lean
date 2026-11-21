def runtimeValue : Nat := 7
@[implemented_by runtimeValue]
def logicalValue : Nat := 0

local instance (priority := 20000) original : ForIn Id (List Nat) Nat where
  forIn _ init step := do
    match ← step 0 init with
    | .done v => pure v
    | .yield v => pure v

@[reducible] def replacement : ForIn Id (List Nat) Nat where
  forIn _ init step := do
    match ← step logicalValue init with
    | .done v => pure v
    | .yield v => pure v

@[csimp] theorem changeDictionary : original = replacement := rfl

def countLoop (xs : List Nat) : Nat := Id.run do
  let mut n := 0
  for x in xs do n := n + x
  return n

def main : IO Unit := IO.println (toString (countLoop [1, 2]))
