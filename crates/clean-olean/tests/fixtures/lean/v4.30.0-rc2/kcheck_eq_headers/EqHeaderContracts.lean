/- Independent complete propositions; no implementation theorem or inferred type. -/
prelude
import KCheckEqHeaders
set_option autoImplicit false
namespace EqHeaderContracts
open CICL CICL.Model CICL.Model.SetValue CICL.Model.RawEvaluation CICL.Model.BaseMath KCheckSpec
open KCheckEqHeaders KCheckRuleCertificates KCheckRuleCertificates.TwoNullaryRules
universe u

def headers_iff : Prop := ∀ {E : Env}, EqHeaders E ↔
  E.find `Eq = some (Base.familyEntry `Eq 1 Base.eqType Base.oneLevelBound) ∧
  E.find `Eq.refl = some (Base.familyEntry `Eq.refl 1 Base.eqReflType Base.oneLevelBound) ∧
  E.find `Eq.rec = some (Base.familyEntry `Eq.rec 2 Base.eqRecType Base.twoLevelBound)

def entries_prefix : Prop := ∀ {E E' : Env} (headers : EqHeaders E)
  (entries : ∃ rest, E'.entries = E.entries ++ rest), EqHeaders E'

def rootedAtPrefix : Prop := ∀ {E E' : Env} (headers : EqHeaders E)
  (extension : RootedAt E E'), EqHeaders E'

def of_rooted : Prop := ∀ {E : Env} (rooted : Rooted E), EqHeaders E

def erased_equality_bound : Prop :=
  ∀ {E : Env} (headers : EqHeaders E) (levels : Nat → Nat) (height under : Nat)
    (statement : Term) (cites : statement.CitesWithin E levels height)
    (level : Level) (type left right : Term)
    (shape : statement.toExpr (Metadata := Unit) 0 under =
      (Base.eqApp level type left right).toExpr 0 under), max 1 (level.eval levels + 1) ≤ height

def member_endpoints : Prop :=
  ∀ {height : Nat} {tower : UniverseTower.{u} height}
    (b : Base tower) {E : Env} (headers : EqHeaders E) (valid : E.Valid b)
    (values : List Nat) (slot : Term) {member : RawSet.{u}}
    (typed : Mem member (closedValue (E.assignment b) values slot))
    (cites : slot.CitesWithin E (pad values) height)
    (arguments : List RawSet.{u})
    (tele : InTele ((E.assignment b).withLevels (pad values)) (fun _ => RawSet.empty) 0 slot arguments)
    (level : Level) (type left right : Term)
    (shape : (slot.dropPis arguments.length).toExpr (Metadata := Unit) 0 arguments.length =
      (Base.eqApp level type left right).toExpr 0 arguments.length),
    let A := (E.assignment b).withLevels (pad values)
    let env := pushAll arguments (fun _ => RawSet.empty)
    RawSet.Related (value A env 0 arguments.length left) (value A env 0 arguments.length right)

def entry_endpoints : Prop :=
  ∀ {height : Nat} {tower : UniverseTower.{u} height}
    (b : Base tower) {E : Env} (headers : EqHeaders E) (valid : E.Valid b)
    {entry : Entry} (checked : EntryValid b E entry)
    (values : List Nat) (inside : entry.bound.eval (pad values) ≤ height)
    (arguments : List RawSet.{u})
    (tele : InTele ((E.assignment b).withLevels (pad values)) (fun _ => RawSet.empty) 0
      entry.type arguments)
    (level : Level) (type left right : Term)
    (shape : (entry.type.dropPis arguments.length).toExpr (Metadata := Unit) 0 arguments.length =
      (Base.eqApp level type left right).toExpr 0 arguments.length),
    let A := (E.assignment b).withLevels (pad values)
    let env := pushAll arguments (fun _ => RawSet.empty)
    RawSet.Related (value A env 0 arguments.length left) (value A env 0 arguments.length right)

def found_endpoints : Prop :=
  ∀ {height : Nat} {tower : UniverseTower.{u} height}
    (b : Base tower) {E : Env} (headers : EqHeaders E) (valid : E.Valid b)
    {name : Lean.Name} {entry : Entry} (found : E.find name = some entry)
    (values : List Nat) (inside : entry.bound.eval (pad values) ≤ height)
    (arguments : List RawSet.{u})
    (tele : InTele ((E.assignment b).withLevels (pad values)) (fun _ => RawSet.empty) 0
      entry.type arguments)
    (level : Level) (type left right : Term)
    (shape : (entry.type.dropPis arguments.length).toExpr (Metadata := Unit) 0 arguments.length =
      (Base.eqApp level type left right).toExpr 0 arguments.length),
    let A := (E.assignment b).withLevels (pad values)
    let env := pushAll arguments (fun _ => RawSet.empty)
    RawSet.Related (value A env 0 arguments.length left) (value A env 0 arguments.length right)

def slot_endpoints : Prop :=
  ∀ {height : Nat} {tower : UniverseTower.{u} height}
    (b : Base tower) {E : Env} (headers : EqHeaders E) (valid : E.Valid b)
    {names : Names} (packet : Packet E names) (secondRule : Bool) (values : List Nat)
    (inside : packet.recursor.bound.eval (pad values) ≤ height)
    {motive first second : RawSet.{u}}
    (tele : InTele ((E.assignment b).withLevels (pad values)) (fun _ => RawSet.empty) 0
      (recursorType names) [motive, first, second]),
    RawSet.Related
      (RawSet.traceApps ((E.assignment b).constants names.recursor [pad values 0])
        [motive, first, second, (E.assignment b).constants (constructorName names secondRule) []])
      (if secondRule then second else first)

def rule_valid : Prop :=
  ∀ {height : Nat} {tower : UniverseTower.{u} height}
    (b : Base tower) {E : Env} (headers : EqHeaders E) (valid : E.Valid b)
    {names : Names} (packet : Packet E names) (secondRule : Bool),
    RuleValid b E (family names) (rule names secondRule)

def family_valid : Prop :=
  ∀ {height : Nat} {tower : UniverseTower.{u} height}
    (b : Base tower) {E : Env} (headers : EqHeaders E) (valid : E.Valid b)
    {names : Names} (packet : Packet E names), FamilyValid b E (family names)

def install_valid : Prop :=
  ∀ {height : Nat} {tower : UniverseTower.{u} height} {b : Base tower}
    (indexed : ∀ i, SetValue.IndexedUnionClosed (tower.level i))
    {E : Env} {frames : List ByteArray} {out : KCheckBoolAdmission.Outputs}
    (initial : E.Valid b) (eqs : EqHeaders E)
    (runs : KCheckBoolAdmission.Runs E KCheckBoolIsland.headers frames out.entries)
    (payloads : out.Payloads) (covered : out.covered = true),
    (KCheckBoolAdmission.install E out).Valid b

def check_sound : Prop :=
  ∀ {height : Nat} {tower : UniverseTower.{u} height} {b : Base tower}
    (indexed : ∀ i, SetValue.IndexedUnionClosed (tower.level i))
    {E E' : Env} {adv : KCheck.Advice} {result : Receipt}
    (initial : E.Valid b) (headers : EqHeaders E)
    (run : KCheckBoolAdmission.check E adv = .ok (E', result)),
    E'.Valid b ∧ RootedAt E E' ∧
    E'.families = E.families ++ [KCheckBoolIsland.family] ∧
    ∃ out : KCheckBoolAdmission.Outputs, out.Payloads ∧ out.covered = true ∧
      E' = KCheckBoolAdmission.install E out ∧ result = KCheckBoolAdmission.receipt out

def omittedMemberTyping : Prop :=
  ∀ {height : Nat} {tower : UniverseTower.{u} height}
    (b : Base tower) {E : Env} (headers : EqHeaders E) (valid : E.Valid b)
    (values : List Nat) (slot : Term) {member : RawSet.{u}}
    (cites : slot.CitesWithin E (pad values) height)
    (arguments : List RawSet.{u})
    (tele : InTele ((E.assignment b).withLevels (pad values)) (fun _ => RawSet.empty) 0 slot arguments)
    (level : Level) (type left right : Term)
    (shape : (slot.dropPis arguments.length).toExpr (Metadata := Unit) 0 arguments.length =
      (Base.eqApp level type left right).toExpr 0 arguments.length),
    let A := (E.assignment b).withLevels (pad values)
    let env := pushAll arguments (fun _ => RawSet.empty)
    RawSet.Related (value A env 0 arguments.length left) (value A env 0 arguments.length right)

def omittedInitial : Prop :=
  ∀ {height : Nat} {tower : UniverseTower.{u} height} {b : Base tower}
    (indexed : ∀ i, SetValue.IndexedUnionClosed (tower.level i))
    {E E' : Env} {adv : KCheck.Advice} {result : Receipt}
    (headers : EqHeaders E)
    (run : KCheckBoolAdmission.check E adv = .ok (E', result)),
    E'.Valid b ∧ RootedAt E E' ∧
    E'.families = E.families ++ [KCheckBoolIsland.family] ∧
    ∃ out : KCheckBoolAdmission.Outputs, out.Payloads ∧ out.covered = true ∧
      E' = KCheckBoolAdmission.install E out ∧ result = KCheckBoolAdmission.receipt out

def omittedHeaders : Prop :=
  ∀ {height : Nat} {tower : UniverseTower.{u} height} {b : Base tower}
    (indexed : ∀ i, SetValue.IndexedUnionClosed (tower.level i))
    {E E' : Env} {adv : KCheck.Advice} {result : Receipt}
    (initial : E.Valid b)
    (run : KCheckBoolAdmission.check E adv = .ok (E', result)),
    E'.Valid b ∧ RootedAt E E' ∧
    E'.families = E.families ++ [KCheckBoolIsland.family] ∧
    ∃ out : KCheckBoolAdmission.Outputs, out.Payloads ∧ out.covered = true ∧
      E' = KCheckBoolAdmission.install E out ∧ result = KCheckBoolAdmission.receipt out

def omittedIndexed : Prop :=
  ∀ {height : Nat} {tower : UniverseTower.{u} height} {b : Base tower}
    {E E' : Env} {adv : KCheck.Advice} {result : Receipt}
    (initial : E.Valid b) (headers : EqHeaders E)
    (run : KCheckBoolAdmission.check E adv = .ok (E', result)),
    E'.Valid b ∧ RootedAt E E' ∧
    E'.families = E.families ++ [KCheckBoolIsland.family] ∧
    ∃ out : KCheckBoolAdmission.Outputs, out.Payloads ∧ out.covered = true ∧
      E' = KCheckBoolAdmission.install E out ∧ result = KCheckBoolAdmission.receipt out

end EqHeaderContracts
