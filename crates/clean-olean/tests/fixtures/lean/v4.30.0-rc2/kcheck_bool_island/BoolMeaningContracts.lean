prelude
import KCheckBoolIsland.BoolSemanticResults
set_option autoImplicit false
namespace BoolMeaningContracts
open CICL CICL.Model CICL.Model.RawEvaluation CICL.Model.BaseMath KCheckSpec
open KCheck KCheckRuleCertificates KCheckBoolIsland
open KCheckBoolIsland.BoolReductionCases
universe u

def constructor_typed : Prop :=
  ∀ {height : Nat} {tower : SetValue.UniverseTower.{u} height} (realizer : TowerRealizer tower) (hasNat : Nat.HasNat tower)
    (indexed : ∀ i, SetValue.IndexedUnionClosed (tower.level i))
    (within : 3 ≤ height) (secondRule : Bool),
    Mem ((BoolFamily.registered.assignment (PSigmaBase.base realizer)).constants
      (if secondRule then oneName else zeroName) [])
      ((BoolFamily.registered.assignment (PSigmaBase.base realizer)).constants formerName [])

def constructor_normalized : Prop :=
  ∀ {height : Nat} {tower : SetValue.UniverseTower.{u} height} (realizer : TowerRealizer tower) (hasNat : Nat.HasNat tower)
    (indexed : ∀ i, SetValue.IndexedUnionClosed (tower.level i))
    (secondRule : Bool) (values : List Nat),
    RawSet.Related
      ((BoolFamily.registered.assignment (PSigmaBase.base realizer)).constants
        (if secondRule then oneName else zeroName) values)
      ((BoolFamily.registered.assignment (PSigmaBase.base realizer)).constants
        (if secondRule then oneName else zeroName) [])

def nat_zero_value : Prop :=
  ∀ {height : Nat} {tower : SetValue.UniverseTower.{u} height} (realizer : TowerRealizer tower) (hasNat : Nat.HasNat tower)
    (indexed : ∀ i, SetValue.IndexedUnionClosed (tower.level i)),
    RawSet.Related
      (closedValue (BoolFamily.registered.assignment (PSigmaBase.base realizer)) [] (.const `Nat.zero []))
      (CICL.Model.BaseMath.encode 0)

def nat_one_value : Prop :=
  ∀ {height : Nat} {tower : SetValue.UniverseTower.{u} height} (realizer : TowerRealizer tower) (hasNat : Nat.HasNat tower)
    (indexed : ∀ i, SetValue.IndexedUnionClosed (tower.level i)),
    RawSet.Related
      (closedValue (BoolFamily.registered.assignment (PSigmaBase.base realizer)) []
        (.app (.const `Nat.succ []) (.const `Nat.zero []) (.const `Nat [])))
      (CICL.Model.BaseMath.encode 1)

def checked_semantics : Prop :=
  ∀ {height : Nat} {tower : SetValue.UniverseTower.{u} height} (realizer : TowerRealizer tower) (hasNat : Nat.HasNat tower)
    (indexed : ∀ i, SetValue.IndexedUnionClosed (tower.level i))
    (within : 3 ≤ height) (secondRule : Bool),
    (recursorTerm secondRule).Scoped 0 0 ∧ (minorDomain secondRule).Scoped 0 0 ∧
    Ann BoolFamily.registered height
      ((BoolFamily.registered.assignment (PSigmaBase.base realizer)).withLevels (pad []))
      0 0 (recursorTerm secondRule) (fun _ => RawSet.empty) ∧
    Ann BoolFamily.registered height
      ((BoolFamily.registered.assignment (PSigmaBase.base realizer)).withLevels (pad []))
      0 0 (minorDomain secondRule) (fun _ => RawSet.empty) ∧
    Mem (closedValue (BoolFamily.registered.assignment (PSigmaBase.base realizer)) [] (recursorTerm secondRule))
      (closedValue (BoolFamily.registered.assignment (PSigmaBase.base realizer)) [] (minorDomain secondRule))

def result_type_related : Prop :=
  ∀ {height : Nat} {tower : SetValue.UniverseTower.{u} height} (realizer : TowerRealizer tower) (hasNat : Nat.HasNat tower)
    (indexed : ∀ i, SetValue.IndexedUnionClosed (tower.level i))
    (within : 3 ≤ height) (secondRule : Bool),
    RawSet.Related
      (closedValue (BoolFamily.registered.assignment (PSigmaBase.base realizer)) [] (minorDomain secondRule))
      (closedValue (BoolFamily.registered.assignment (PSigmaBase.base realizer)) [] natType)

def program_typed_nat : Prop :=
  ∀ {height : Nat} {tower : SetValue.UniverseTower.{u} height} (realizer : TowerRealizer tower) (hasNat : Nat.HasNat tower)
    (indexed : ∀ i, SetValue.IndexedUnionClosed (tower.level i))
    (within : 3 ≤ height) (secondRule : Bool),
    Mem (closedValue (BoolFamily.registered.assignment (PSigmaBase.base realizer)) [] (recursorTerm secondRule))
      (closedValue (BoolFamily.registered.assignment (PSigmaBase.base realizer)) [] natType)

def program_related_expected : Prop :=
  ∀ {height : Nat} {tower : SetValue.UniverseTower.{u} height} (realizer : TowerRealizer tower) (hasNat : Nat.HasNat tower)
    (indexed : ∀ i, SetValue.IndexedUnionClosed (tower.level i))
    (within : 3 ≤ height) (secondRule : Bool),
    RawSet.Related
      (closedValue (BoolFamily.registered.assignment (PSigmaBase.base realizer)) [] (recursorTerm secondRule))
      (closedValue (BoolFamily.registered.assignment (PSigmaBase.base realizer)) [] (expected secondRule))

def expected_value : Prop :=
  ∀ {height : Nat} {tower : SetValue.UniverseTower.{u} height} (realizer : TowerRealizer tower) (hasNat : Nat.HasNat tower)
    (indexed : ∀ i, SetValue.IndexedUnionClosed (tower.level i)) (secondRule : Bool),
    RawSet.Related
      (closedValue (BoolFamily.registered.assignment (PSigmaBase.base realizer)) [] (expected secondRule))
      (CICL.Model.BaseMath.encode (if secondRule then 1 else 0))

def program_result : Prop :=
  ∀ {height : Nat} {tower : SetValue.UniverseTower.{u} height} (realizer : TowerRealizer tower) (hasNat : Nat.HasNat tower)
    (indexed : ∀ i, SetValue.IndexedUnionClosed (tower.level i))
    (within : 3 ≤ height) (secondRule : Bool),
    RawSet.Related
      (closedValue (BoolFamily.registered.assignment (PSigmaBase.base realizer)) [] (recursorTerm secondRule))
      (CICL.Model.BaseMath.encode (if secondRule then 1 else 0))

def zero_result : Prop :=
  ∀ {height : Nat} {tower : SetValue.UniverseTower.{u} height} (realizer : TowerRealizer tower) (hasNat : Nat.HasNat tower)
    (indexed : ∀ i, SetValue.IndexedUnionClosed (tower.level i)) (within : 3 ≤ height),
    RawSet.Related
      (closedValue (BoolFamily.registered.assignment (PSigmaBase.base realizer)) [] (recursorTerm false))
      (CICL.Model.BaseMath.encode 0)

def one_result : Prop :=
  ∀ {height : Nat} {tower : SetValue.UniverseTower.{u} height} (realizer : TowerRealizer tower) (hasNat : Nat.HasNat tower)
    (indexed : ∀ i, SetValue.IndexedUnionClosed (tower.level i)) (within : 3 ≤ height),
    RawSet.Related
      (closedValue (BoolFamily.registered.assignment (PSigmaBase.base realizer)) [] (recursorTerm true))
      (CICL.Model.BaseMath.encode 1)

def wrong_result : Prop :=
  ∀ {height : Nat} {tower : SetValue.UniverseTower.{u} height} (realizer : TowerRealizer tower) (hasNat : Nat.HasNat tower)
    (indexed : ∀ i, SetValue.IndexedUnionClosed (tower.level i))
    (within : 3 ≤ height) (secondRule : Bool),
    ¬ RawSet.Related
      (closedValue (BoolFamily.registered.assignment (PSigmaBase.base realizer)) [] (recursorTerm secondRule))
      (CICL.Model.BaseMath.encode (if secondRule then 0 else 1))

def constructors_distinct : Prop :=
  ∀ {height : Nat} {tower : SetValue.UniverseTower.{u} height} (realizer : TowerRealizer tower) (hasNat : Nat.HasNat tower)
    (indexed : ∀ i, SetValue.IndexedUnionClosed (tower.level i)) (within : 3 ≤ height),
    ¬ RawSet.Related
      ((BoolFamily.registered.assignment (PSigmaBase.base realizer)).constants zeroName [])
      ((BoolFamily.registered.assignment (PSigmaBase.base realizer)).constants oneName [])

def constructors_distinct_all_levels : Prop :=
  ∀ {height : Nat} {tower : SetValue.UniverseTower.{u} height} (realizer : TowerRealizer tower) (hasNat : Nat.HasNat tower)
    (indexed : ∀ i, SetValue.IndexedUnionClosed (tower.level i)) (within : 3 ≤ height)
    (zeroValues oneValues : List Nat),
    ¬ RawSet.Related
      ((BoolFamily.registered.assignment (PSigmaBase.base realizer)).constants zeroName zeroValues)
      ((BoolFamily.registered.assignment (PSigmaBase.base realizer)).constants oneName oneValues)

def two_distinct_inhabitants : Prop :=
  ∀ {height : Nat} {tower : SetValue.UniverseTower.{u} height} (realizer : TowerRealizer tower) (hasNat : Nat.HasNat tower)
    (indexed : ∀ i, SetValue.IndexedUnionClosed (tower.level i)) (within : 3 ≤ height),
    Mem ((BoolFamily.registered.assignment (PSigmaBase.base realizer)).constants zeroName [])
      ((BoolFamily.registered.assignment (PSigmaBase.base realizer)).constants formerName []) ∧
    Mem ((BoolFamily.registered.assignment (PSigmaBase.base realizer)).constants oneName [])
      ((BoolFamily.registered.assignment (PSigmaBase.base realizer)).constants formerName []) ∧
    ¬ RawSet.Related
      ((BoolFamily.registered.assignment (PSigmaBase.base realizer)).constants zeroName [])
      ((BoolFamily.registered.assignment (PSigmaBase.base realizer)).constants oneName [])

/- Only program_result's within binder5 is deleted. -/
def omittedWithin : Prop :=
  ∀ {height : Nat} {tower : SetValue.UniverseTower.{u} height}
    (realizer : TowerRealizer tower) (hasNat : Nat.HasNat tower)
    (indexed : ∀ i, SetValue.IndexedUnionClosed (tower.level i)) (secondRule : Bool),
    RawSet.Related
      (closedValue (BoolFamily.registered.assignment (PSigmaBase.base realizer)) [] (recursorTerm secondRule))
      (CICL.Model.BaseMath.encode (if secondRule then 1 else 0))

/- Only the second constructor name in the conclusion changes from one to zero.
Every premise remains, so this is an output mutation rather than a deletion. -/
def reflexiveConstructorMutation : Prop :=
  ∀ {height : Nat} {tower : SetValue.UniverseTower.{u} height}
    (realizer : TowerRealizer tower) (hasNat : Nat.HasNat tower)
    (indexed : ∀ i, SetValue.IndexedUnionClosed (tower.level i)) (within : 3 ≤ height),
    ¬ RawSet.Related
      ((BoolFamily.registered.assignment (PSigmaBase.base realizer)).constants zeroName [])
      ((BoolFamily.registered.assignment (PSigmaBase.base realizer)).constants zeroName [])
end BoolMeaningContracts
