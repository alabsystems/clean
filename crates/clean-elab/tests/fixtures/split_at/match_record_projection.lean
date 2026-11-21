structure Packet where
  accepted : Bool
  payload : Nat

def acceptedBit (p : Packet) : Bool :=
  match p with
  | ⟨true, _⟩ => true
  | _ => false

theorem decode_accepted (p : Packet) (h : acceptedBit p = true) : p.accepted = true := by
  unfold acceptedBit at h
  split at h <;> simp_all
