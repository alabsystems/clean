@[irreducible] def assumption_carrier : Type := Nat
@[irreducible] def assumption_gate : Prop := True

def choose_data (good : Nat) (blocked : assumption_carrier) : Nat := by
  assumption

theorem choose_prop (good : True) (blocked : assumption_gate) : True := by
  assumption

def choose_data_rwa (good : Nat) (blocked : assumption_carrier) : Nat := by
  rwa []

theorem choose_prop_rwa (good : True) (blocked : assumption_gate) : True := by
  rwa []

example (good : Nat) (blocked : assumption_carrier) : choose_data good blocked = good := by
  rfl
example (good : Nat) (blocked : assumption_carrier) : choose_data_rwa good blocked = good := by
  rfl

/-- info: 'choose_data' does not depend on any axioms -/
#guard_msgs in
#print axioms choose_data
/-- info: 'choose_prop' does not depend on any axioms -/
#guard_msgs in
#print axioms choose_prop
/-- info: 'choose_data_rwa' does not depend on any axioms -/
#guard_msgs in
#print axioms choose_data_rwa
/-- info: 'choose_prop_rwa' does not depend on any axioms -/
#guard_msgs in
#print axioms choose_prop_rwa
