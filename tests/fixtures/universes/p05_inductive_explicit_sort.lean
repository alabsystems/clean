inductive MyList.{u} (A : Type u) : Type u where
  | nil : MyList A
  | cons : A → MyList A → MyList A
