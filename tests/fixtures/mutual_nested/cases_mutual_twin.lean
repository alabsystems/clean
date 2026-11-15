-- B5 twin over the mutual block: `A.ofB b` is not `A.base`.
mutual
inductive A where
  | base : A
  | ofB : B → A
inductive B where
  | ofA : A → B
end

theorem mutual_twin (a : A) : a = .base := by
  cases a with
  | base => rfl
  | ofB b => rfl
