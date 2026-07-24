-- Lean 4.26 string compatibility fixture
def greeting : String := "Lean αβ 🌍"

def identity (α : Type) (x : α) : α := x

theorem greeting_eq : greeting = "Lean αβ 🌍" := rfl
