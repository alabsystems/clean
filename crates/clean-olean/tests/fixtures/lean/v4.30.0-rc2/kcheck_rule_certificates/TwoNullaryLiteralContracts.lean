prelude
import KCheckRuleCertificates.TwoNullaryRules
set_option autoImplicit false

namespace TwoNullaryLiteralContracts
open CICL CICL.Model KCheckSpec KCheckRuleCertificates.TwoNullaryRules
universe u

/-- Complete independent literal, including arbitrary Base and prior validity. -/
def rule_valid : Prop :=
  ∀ {height : Nat} {tower : SetValue.UniverseTower.{u} height}
    (b : Base tower) {E : Env} (rooted : Rooted E) (valid : E.Valid b)
    {names : Names} (packet : Packet E names) (secondRule : Bool),
    RuleValid b E (family names) (rule names secondRule)

def family_valid : Prop :=
  ∀ {height : Nat} {tower : SetValue.UniverseTower.{u} height}
    (b : Base tower) {E : Env} (rooted : Rooted E) (valid : E.Valid b)
    {names : Names} (packet : Packet E names),
    FamilyValid b E (family names)

def rule_closed : Prop :=
  ∀ {height : Nat} {tower : SetValue.UniverseTower.{u} height}
    (b : Base tower) {E : Env} (valid : E.Valid b)
    {names : Names} (packet : Packet E names) (secondRule : Bool),
    (rhs names secondRule).Scoped 0 0

def names_reserved : Prop :=
  ∀ {E : Env} {names : Names} (packet : Packet E names),
    ∀ name, name ∈ (family names).names → (E.find name).isSome = true

/-- Exact deletion of only rule_valid's prior-validity binder5. -/
def omittedPriorValidity : Prop :=
  ∀ {height : Nat} {tower : SetValue.UniverseTower.{u} height}
    (b : Base tower) {E : Env} (rooted : Rooted E)
    {names : Names} (packet : Packet E names) (secondRule : Bool),
    RuleValid b E (family names) (rule names secondRule)

/-- Exact result-bit mutations of the existing arithmetic refusal cases. -/
def missing_base_forged : Prop :=
  KCheckRuleCertificates.Budget.covers ⟨1, []⟩ ⟨0, []⟩ = true

def wrong_index_forged : Prop :=
  KCheckRuleCertificates.Budget.covers ⟨0, [(1, 2)]⟩ ⟨0, [(0, 2)]⟩ = true

end TwoNullaryLiteralContracts
