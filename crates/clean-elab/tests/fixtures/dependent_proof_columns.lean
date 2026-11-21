def HasPair : Bool → Prop
  | false => True
  | true => True ∧ True
theorem boolPattern : ∀ b, HasPair b → True
  | false, _ => True.intro
  | true, ⟨h, _⟩ => h
theorem boolTyped : ∀ (b : Bool), HasPair b → True
  | false, _ => True.intro
  | true, And.intro h _ => h
theorem boolBound : ∀ b, HasPair b → True
  | false => fun _ => True.intro
  | true => fun h => And.left h
def Choice : Bool → Type
  | false => Nat
  | true => Bool × Bool
def choose : ∀ b, Choice b → Nat
  | true, (true, _) => 2
  | false, n => n
  | true, (false, _) => 1
theorem chooseValues : choose true (true, false) = 2 ∧ choose false (7 : Nat) = 7 ∧ choose true (false, true) = 1 := ⟨rfl, rfl, rfl⟩
def Distinct : Bool → Prop
  | false => True
  | true => False ∧ True

-- The earlier generalization of a trailing plain hypothesis keeps its own lowering.
def AlwaysPair (_ : Bool) : Prop := True ∧ True
theorem threeColumns : ∀ (b : Bool), AlwaysPair b → b = b → True
  | false, ⟨h, _⟩, _ => h
  | true, ⟨_, h⟩, _ => h

theorem rejectCtor : ∀ b, HasPair b → True
  | false, And.intro h _ => h
  | true, _ => True.intro

theorem wrongField : ∀ b, Distinct b → True
  | false, h => h
  | true, ⟨h, _⟩ => h

theorem rejectWrong : ∀ b, HasPair b → False
  | false, _ => True.intro
  | true, ⟨h, _⟩ => h

def missedOuter : ∀ b, Choice b → Nat
  | true, (true, _) => 2
  | true, (false, _) => 1

def rejectMissing : ∀ b, Choice b → Nat
  | false, _ => 0
  | true, (true, _) => 1

def rejectShadow : ∀ b, Choice b → Nat
  | true, _ => 0
  | false, _ => 0
  | true, (true, _) => 1
