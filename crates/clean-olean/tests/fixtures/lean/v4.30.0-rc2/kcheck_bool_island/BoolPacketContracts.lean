/- Complete propositions are literal data, without using an implementation
theorem constant or its inferred type. All quantifiers remain inside Prop. -/
prelude
import KCheckBoolIsland.BoolFamily
set_option autoImplicit false
namespace BoolPacketContracts
open CICL CICL.Model CICL.Model.RawEvaluation KCheckSpec KCheckRuleCertificates
open KCheckBoolIsland
open KCheckBoolIsland.OperationalCases KCheckBoolIsland.RecursorOperational
open KCheckBoolIsland.SlotOperational KCheckBoolIsland.BoolFamily
universe u

namespace PacketLiterals

def former_found : Prop :=
  E11.find formerName = some formerEntry

def zero_found : Prop :=
  E11.find zeroName = some zeroEntry

def one_found : Prop :=
  E11.find oneName = some oneEntry

def recursor_found : Prop :=
  E11.find recursorName = some recursorEntry

def zero_slot_found : Prop :=
  E11.find zeroSlotName = some zeroSlotEntry

def one_slot_found : Prop :=
  E11.find oneSlotName = some oneSlotEntry

def slot_reports : Prop :=
  zeroSlotEntry.bound = RuleTemplate.recursorBudget ∧
    oneSlotEntry.bound = RuleTemplate.recursorBudget ∧
    recursorEntry.bound = RuleTemplate.recursorBudget

end PacketLiterals

namespace FamilyLiterals

def checked_prefix : Prop :=
  ∀ {height : Nat} {tower : SetValue.UniverseTower.{u} height} (b : Base tower)
    (indexed : ∀ i, SetValue.IndexedUnionClosed (tower.level i))
    (initial : KCheck.base.Valid b),
    RootedAt PSigmaSeed.seed E11 ∧ E11.Valid b

def prior_valid : Prop :=
  ∀ {height : Nat} {tower : SetValue.UniverseTower.{u} height} (b : Base tower)
    (indexed : ∀ i, SetValue.IndexedUnionClosed (tower.level i))
    (initial : KCheck.base.Valid b),
    E11.Valid b

def prior_rooted : Prop :=
  ∀ {height : Nat} {tower : SetValue.UniverseTower.{u} height} (b : Base tower)
    (indexed : ∀ i, SetValue.IndexedUnionClosed (tower.level i))
    (initial : KCheck.base.Valid b),
    Rooted E11

def rule_valid : Prop :=
  ∀ {height : Nat} {tower : SetValue.UniverseTower.{u} height} (b : Base tower)
    (indexed : ∀ i, SetValue.IndexedUnionClosed (tower.level i))
    (initial : KCheck.base.Valid b) (secondRule : Bool),
    RuleValid b E11 KCheckBoolIsland.family (TwoNullaryRules.rule RuleTemplate.names secondRule)

def family_valid : Prop :=
  ∀ {height : Nat} {tower : SetValue.UniverseTower.{u} height} (b : Base tower)
    (indexed : ∀ i, SetValue.IndexedUnionClosed (tower.level i))
    (initial : KCheck.base.Valid b),
    FamilyValid b E11 KCheckBoolIsland.family

def checked_suffix : Prop :=
  E11 = ⟨E3.entries ++ suffix, E3.families⟩

def nominal_fresh : Prop :=
  ∀ name, name ∈ nominal → E3.find name = none

def sealed_prefix : Prop :=
  sealed =
    ⟨E3.entries ++ suffix.map (ModelSealing.sealEntry nominal), E3.families⟩

def seed_to_predicates : Prop :=
  RootedAt PSigmaSeed.seed E3

def registered_predicate_prefix : Prop :=
  RootedAt E3 registered

def registered_rootedAt : Prop :=
  RootedAt PSigmaSeed.seed registered

def registered_rooted : Prop :=
  Rooted registered

def family_registered : Prop :=
  KCheckBoolIsland.family ∈ registered.families

def families_changed : Prop :=
  registered.families ≠ E11.families

def sealed_assignment : Prop :=
  ∀ {height : Nat} {tower : SetValue.UniverseTower.{u} height} (b : Base tower),
    sealed.assignment b = E11.assignment b

def registered_assignment : Prop :=
  ∀ {height : Nat} {tower : SetValue.UniverseTower.{u} height} (b : Base tower),
    registered.assignment b = E11.assignment b

def sealed_valid : Prop :=
  ∀ {height : Nat} {tower : SetValue.UniverseTower.{u} height} (b : Base tower)
    (indexed : ∀ i, SetValue.IndexedUnionClosed (tower.level i))
    (initial : KCheck.base.Valid b),
    sealed.Valid b

def sealed_family_valid : Prop :=
  ∀ {height : Nat} {tower : SetValue.UniverseTower.{u} height} (b : Base tower)
    (indexed : ∀ i, SetValue.IndexedUnionClosed (tower.level i))
    (initial : KCheck.base.Valid b),
    FamilyValid b sealed KCheckBoolIsland.family

def closed_rules : Prop :=
  ∀ {height : Nat} {tower : SetValue.UniverseTower.{u} height} (b : Base tower)
    (indexed : ∀ i, SetValue.IndexedUnionClosed (tower.level i))
    (initial : KCheck.base.Valid b),
    ∀ rule, rule ∈ KCheckBoolIsland.family.rules → rule.rhs.Scoped 0 0

def names_reserved : Prop :=
  ∀ name, name ∈ KCheckBoolIsland.family.names → (sealed.find name).isSome = true

def registered_valid : Prop :=
  ∀ {height : Nat} {tower : SetValue.UniverseTower.{u} height} (b : Base tower)
    (indexed : ∀ i, SetValue.IndexedUnionClosed (tower.level i))
    (initial : KCheck.base.Valid b),
    registered.Valid b

def registered_family_valid : Prop :=
  ∀ {height : Nat} {tower : SetValue.UniverseTower.{u} height} (b : Base tower)
    (indexed : ∀ i, SetValue.IndexedUnionClosed (tower.level i))
    (initial : KCheck.base.Valid b),
    FamilyValid b registered KCheckBoolIsland.family

def psigma_registered_valid : Prop :=
  ∀ {height : Nat} {tower : SetValue.UniverseTower.{u} height} (realizer : TowerRealizer tower)
    (hasNat : BaseMath.Nat.HasNat tower)
    (indexed : ∀ i, SetValue.IndexedUnionClosed (tower.level i)),
    registered.Valid (PSigmaBase.base realizer)

def psigma_prior_valid : Prop :=
  ∀ {height : Nat} {tower : SetValue.UniverseTower.{u} height} (realizer : TowerRealizer tower)
    (hasNat : BaseMath.Nat.HasNat tower)
    (indexed : ∀ i, SetValue.IndexedUnionClosed (tower.level i)),
    E11.Valid (PSigmaBase.base realizer)

def psigma_registered_family_valid : Prop :=
  ∀ {height : Nat} {tower : SetValue.UniverseTower.{u} height} (realizer : TowerRealizer tower)
    (hasNat : BaseMath.Nat.HasNat tower)
    (indexed : ∀ i, SetValue.IndexedUnionClosed (tower.level i)),
    FamilyValid (PSigmaBase.base realizer) registered KCheckBoolIsland.family

def psigma_initialized : Prop :=
  ∀ {height : Nat} {tower : SetValue.UniverseTower.{u} height} (realizer : TowerRealizer tower)
    (hasNat : BaseMath.Nat.HasNat tower)
    (indexed : ∀ i, SetValue.IndexedUnionClosed (tower.level i)),
    KCheck.InitializedSound.Initialized realizer registered

end FamilyLiterals

namespace Data
def nominal : List Lean.Name := [formerName, zeroName, oneName, recursorName]
def suffix : List Entry :=
  [formerEntry, zeroEntry, oneEntry, dEntry, absurdEntry,
    recursorEntry, zeroSlotEntry, oneSlotEntry]
def sealed : Env := ModelSealing.sealEnv [formerName, zeroName, oneName, recursorName] E11
def registered : Env := FamilyRegistration.register
  (ModelSealing.sealEnv [formerName, zeroName, oneName, recursorName] E11) KCheckBoolIsland.family

def packet : TwoNullaryRules.Packet E11 RuleTemplate.names where
  former := formerEntry
  constructor := fun secondRule => if secondRule then oneEntry else zeroEntry
  recursor := recursorEntry
  slot := fun secondRule => if secondRule then oneSlotEntry else zeroSlotEntry
  formerFound := by rfl
  constructorFound := by intro secondRule; cases secondRule <;> rfl
  recursorFound := by rfl
  slotFound := by intro secondRule; cases secondRule <;> rfl
  formerType := RuleTemplate.former_type_eq
  formerParams := rfl
  constructorType := by intro secondRule; cases secondRule <;> exact RuleTemplate.carrier_eq
  constructorParams := by intro secondRule; cases secondRule <;> rfl
  recursorType := RuleTemplate.recursor_type_eq
  recursorParams := rfl
  slotType := by
    intro secondRule
    cases secondRule with
    | false => exact RuleTemplate.zero_slot_type_eq
    | true => exact RuleTemplate.one_slot_type_eq
  slotParams := by intro secondRule; cases secondRule <;> rfl
  constructorBody := fun secondRule => if secondRule then oneValue else zeroValue
  recursorBody := recursorValue
  constructorDefined := by intro secondRule; cases secondRule <;> rfl
  recursorDefined := rfl
  constructorLevels := by
    intro secondRule
    cases secondRule with
    | false => exact RuleTemplate.zero_body_levelScoped
    | true => exact RuleTemplate.one_body_levelScoped
  recursorLevels := RuleTemplate.recursor_body_levelScoped
  slotCovered := by intro secondRule; cases secondRule <;> rfl

end Data

/- Exact binder deletions, not additional proved propositions. -/
def omittedInitialValidity : Prop :=
  ∀ {height : Nat} {tower : SetValue.UniverseTower.{u} height}
    (b : Base tower) (indexed : ∀ i, SetValue.IndexedUnionClosed (tower.level i)),
    RootedAt PSigmaSeed.seed E11 ∧ E11.Valid b
def omittedIndexedClosure : Prop :=
  ∀ {height : Nat} {tower : SetValue.UniverseTower.{u} height}
    (b : Base tower) (initial : KCheck.base.Valid b),
    registered.Valid b
end BoolPacketContracts
