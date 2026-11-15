inductive Changed (p : α → Prop) : α → Prop where
  | intro {x} : p x → Changed (fun _ => False) x
