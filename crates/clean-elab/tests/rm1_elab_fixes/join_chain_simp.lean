-- RM1 fixture: simp over a definition lowered through nested join points
-- (the depth-8 skeleton of impliesFuel). simp's equation synthesis must keep
-- each join a `let`: substituting it re-expands every catch-all per
-- constructor at every level (25 GiB on PredLatticeProps).
inductive Q where
  | q0 : Int → Q
  | q1 : Nat → Q
  | q2 : Nat → Bool → Q
  | q3 : Q
  | q4 : Q
  | q5 : List Q → Q
  | q6 : List Q → Q
  | top : Q
  | bot : Q

def chain : Nat → Q → Q → Bool
  | 0, _, _ => false
  | n + 1, a, b =>
    match a, b with
    | .bot, _ => true
    | _, .bot => false
    | _, .top => true
    | .top, _ => false
    | a, b =>
      match b with
      | .q0 .. => chain n a b
      | _ =>
        match a with
        | .q1 .. => chain n a b
        | _ =>
          match b with
          | .q2 .. => chain n a b
          | _ =>
            match a with
            | .q3 .. => chain n a b
            | _ =>
              match b with
              | .q4 .. => chain n a b
              | _ =>
                match a with
                | .q0 .. => chain n a b
                | _ =>
                  match b with
                  | .q1 .. => chain n a b
                  | _ =>
                    match a with
                    | .q2 .. => chain n a b
                    | _ =>
                      false

theorem chain_bot : chain 1 .bot .q3 = true := by simp [chain]
theorem chain_deep : chain 1 .q3 .q4 = false := by simp [chain]
