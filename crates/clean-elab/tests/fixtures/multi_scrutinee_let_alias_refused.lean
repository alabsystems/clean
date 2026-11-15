theorem packed_alias_keep (a b : Bool) : a = a :=
  let c := a
  have proof : c = a :=
    match c, b with
    | false, false => rfl
    | false, true => rfl
    | true, false => rfl
    | true, true => rfl
  proof
