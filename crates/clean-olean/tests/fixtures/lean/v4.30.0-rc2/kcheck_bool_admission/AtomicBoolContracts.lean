/- Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0 -/
prelude
import KCheckBoolAdmission.Cases
set_option autoImplicit false

/-! Full literal propositions for every public theorem in the seven
production roots. Quantified model data and all hypotheses occur INSIDE
Prop. The definitions contain no implementation theorem or proof value.
The four mutants are native refusal controls, not proved countermodels. -/
namespace AtomicBoolContracts
open CICL CICL.Model CICL.Model.RawEvaluation KCheckSpec KCheckBoolIsland
open KCheck KCheckRuleCertificates
open KCheckBoolIsland.OperationalCases KCheckBoolIsland.RecursorOperational
open KCheckBoolIsland.SlotOperational
universe u

namespace DataLiteral

def ordinary_parts : Prop :=
  ∀ (header : Header),
    KCheck.ordinaryParts header.ordinary = .ok (KCheckBoolAdmission.ordinary header)


def payloadExact_iff : Prop :=
  ∀ (header : Header) (entry : Entry),
    KCheckBoolAdmission.payloadExact header entry = true ↔ entry = KCheckBoolAdmission.stored header entry.bound


def unpack_entries : Prop :=
  ∀ (out : KCheckBoolAdmission.Outputs),
    KCheckBoolAdmission.Outputs.unpack out.entries = some out


def unpack_sound : Prop :=
  ∀ {entries : List Entry} {out : KCheckBoolAdmission.Outputs}
    (found : KCheckBoolAdmission.Outputs.unpack entries = some out),
    entries = out.entries


def exact_iff : Prop :=
  ∀ (out : KCheckBoolAdmission.Outputs),
    out.payloadsExact = true ↔ out.Payloads


def covered_iff : Prop :=
  ∀ (out : KCheckBoolAdmission.Outputs),
    out.covered = true ↔
    KCheckRuleCertificates.Budget.covers out.zeroSlot.bound out.recursor.bound = true ∧
    KCheckRuleCertificates.Budget.covers out.oneSlot.bound out.recursor.bound = true


def checkedEnv_cons : Prop :=
  ∀ (E : Env) (entry : Entry) (entries : List Entry),
    KCheckBoolAdmission.checkedEnv (KCheckBoolAdmission.append E entry) entries = KCheckBoolAdmission.checkedEnv E (entry :: entries)


def fresh_sound : Prop :=
  ∀ {E : Env} (guard : KCheckBoolAdmission.fresh E = true),
    ∀ name, name ∈ nominalNames → E.find name = none

end DataLiteral

namespace FramesLiteral

def parse_iff : Prop :=
  ∀ {adv : Advice} {frames : List ByteArray},
    KCheckBoolAdmission.Frames.parse adv = some frames ↔
      adv.pending = 0 ∧ adv.spine = .none ∧ adv.pos ≤ adv.bytes.size ∧
      frames.length = 11 ∧
      splitFramesAux adv.bytes (adv.bytes.size + 1) adv.pos [] = .ok frames


def parse_length : Prop :=
  ∀ {adv : Advice} {frames : List ByteArray}
    (run : KCheckBoolAdmission.Frames.parse adv = some frames),
    frames.length = 11


def parse_trace : Prop :=
  ∀ {adv : Advice} {frames : List ByteArray}
    (run : KCheckBoolAdmission.Frames.parse adv = some frames),
    UnitFamilyFrames.FrameTrace adv.bytes adv.pos frames adv.bytes.size


def parse_covers : Prop :=
  ∀ {adv : Advice} {frames : List ByteArray}
    (run : KCheckBoolAdmission.Frames.parse adv = some frames) {index : Nat}
    (lower : adv.pos ≤ index) (upper : index < adv.bytes.size),
    ∃ payload ∈ frames, ∃ header start stop,
      UnitFamilyFrames.FrameSpan adv.bytes header start stop payload ∧
        header ≤ index ∧ index < stop

end FramesLiteral

namespace TransactionLiteral

def runChecks_sound : Prop :=
  ∀ {E : Env} {headers : List Header} {frames : List ByteArray}
    {entries : List Entry} (run : KCheckBoolAdmission.runChecks E headers frames = .ok entries),
    KCheckBoolAdmission.Runs E headers frames entries


def Runs_accepted : Prop :=
  ∀ {E : Env} {headers : List Header} {frames : List ByteArray}
    {entries : List Entry} (runs : KCheckBoolAdmission.Runs E headers frames entries),
    KCheckBoolAdmission.runChecks E headers frames = .ok entries


def check_decomposition : Prop :=
  ∀ {E E' : Env} {adv : Advice} {result : Receipt}
    (run : KCheckBoolAdmission.check E adv = .ok (E', result)),
    ∃ (frames : List ByteArray) (out : KCheckBoolAdmission.Outputs),
      KCheckBoolAdmission.fresh E = true ∧ KCheckBoolAdmission.Frames.parse adv = some frames ∧
      KCheckBoolAdmission.Runs E headers frames out.entries ∧ out.Payloads ∧ out.covered = true ∧
      E' = KCheckBoolAdmission.install E out ∧ result = KCheckBoolAdmission.receipt out


def check_accepts : Prop :=
  ∀ {E : Env} {adv : Advice} {frames : List ByteArray} {out : KCheckBoolAdmission.Outputs}
    (freshNames : KCheckBoolAdmission.fresh E = true) (parsed : KCheckBoolAdmission.Frames.parse adv = some frames)
    (runs : KCheckBoolAdmission.Runs E headers frames out.entries) (payloads : out.Payloads)
    (covered : out.covered = true),
    KCheckBoolAdmission.check E adv = .ok (KCheckBoolAdmission.install E out, KCheckBoolAdmission.receipt out)

end TransactionLiteral

namespace PacketLiteral
end PacketLiteral

namespace PreservationLiteral

def Runs_checked_valid : Prop :=
  ∀ {height : Nat} {tower : SetValue.UniverseTower.{u} height}
    {b : Base tower}
    (indexed : ∀ i, SetValue.IndexedUnionClosed (tower.level i))
    {E : Env} {headers : List Header} {frames : List ByteArray} {entries : List Entry}
    (runs : KCheckBoolAdmission.Runs E headers frames entries) (initial : E.Valid b),
    (KCheckBoolAdmission.checkedEnv E entries).Valid b


def checked_prefix : Prop :=
  ∀ (E : Env) (entries : List Entry),
    RootedAt E (KCheckBoolAdmission.checkedEnv E entries)


def install_eq : Prop :=
  ∀ {E : Env} (out : KCheckBoolAdmission.Outputs) (freshNames : KCheckBoolAdmission.fresh E = true),
    KCheckBoolAdmission.install E out =
      ⟨E.entries ++ out.entries.map (ModelSealing.sealEntry nominalNames),
        E.families ++ [KCheckBoolIsland.family]⟩


def install_prefix : Prop :=
  ∀ {E : Env} (out : KCheckBoolAdmission.Outputs) (freshNames : KCheckBoolAdmission.fresh E = true),
    RootedAt E (KCheckBoolAdmission.install E out)


def install_assignment : Prop :=
  ∀ {height : Nat} {tower : SetValue.UniverseTower.{u} height}
    (b : Base tower) (E : Env) (out : KCheckBoolAdmission.Outputs),
    (KCheckBoolAdmission.install E out).assignment b = (KCheckBoolAdmission.checkedEnv E out.entries).assignment b


def install_family_mem : Prop :=
  ∀ (E : Env) (out : KCheckBoolAdmission.Outputs),
    KCheckBoolIsland.family ∈ (KCheckBoolAdmission.install E out).families


def install_family_count : Prop :=
  ∀ (E : Env) (out : KCheckBoolAdmission.Outputs),
    (KCheckBoolAdmission.install E out).families.length = E.families.length + 1


def check_prefix : Prop :=
  ∀ {E E' : Env} {adv : KCheck.Advice} {result : Receipt}
    (run : KCheckBoolAdmission.check E adv = .ok (E', result)),
    RootedAt E E'


def check_one_family : Prop :=
  ∀ {E E' : Env} {adv : KCheck.Advice} {result : Receipt}
    (run : KCheckBoolAdmission.check E adv = .ok (E', result)),
    E'.families = E.families ++ [KCheckBoolIsland.family] ∧
      E'.families.length = E.families.length + 1

end PreservationLiteral

namespace SoundLiteral

def checked_family_valid : Prop :=
  ∀ {height : Nat} {tower : SetValue.UniverseTower.{u} height}
    {b : Base tower}
    (indexed : ∀ i, SetValue.IndexedUnionClosed (tower.level i))
    {E : Env} {frames : List ByteArray} {out : KCheckBoolAdmission.Outputs}
    (initial : E.Valid b) (rooted : Rooted E)
    (runs : KCheckBoolAdmission.Runs E headers frames out.entries) (payloads : out.Payloads)
    (covered : out.covered = true),
    FamilyValid b (KCheckBoolAdmission.checkedEnv E out.entries) KCheckBoolIsland.family


def install_valid : Prop :=
  ∀ {height : Nat} {tower : SetValue.UniverseTower.{u} height}
    {b : Base tower}
    (indexed : ∀ i, SetValue.IndexedUnionClosed (tower.level i))
    {E : Env} {frames : List ByteArray} {out : KCheckBoolAdmission.Outputs}
    (initial : E.Valid b) (rooted : Rooted E)
    (runs : KCheckBoolAdmission.Runs E headers frames out.entries) (payloads : out.Payloads)
    (covered : out.covered = true),
    (KCheckBoolAdmission.install E out).Valid b


def check_sound : Prop :=
  ∀ {height : Nat} {tower : SetValue.UniverseTower.{u} height}
    {b : Base tower}
    (indexed : ∀ i, SetValue.IndexedUnionClosed (tower.level i))
    {E E' : Env} {adv : KCheck.Advice} {result : Receipt}
    (initial : E.Valid b) (rooted : Rooted E)
    (run : KCheckBoolAdmission.check E adv = .ok (E', result)),
    E'.Valid b ∧ RootedAt E E' ∧ Rooted E' ∧
      E'.families = E.families ++ [KCheckBoolIsland.family] ∧
      ∃ out : KCheckBoolAdmission.Outputs, E'.assignment b = (KCheckBoolAdmission.checkedEnv E out.entries).assignment b ∧
        result = KCheckBoolAdmission.receipt out


def check_family_valid : Prop :=
  ∀ {height : Nat} {tower : SetValue.UniverseTower.{u} height}
    {b : Base tower}
    (indexed : ∀ i, SetValue.IndexedUnionClosed (tower.level i))
    {E E' : Env} {adv : KCheck.Advice} {result : Receipt}
    (initial : E.Valid b) (rooted : Rooted E)
    (run : KCheckBoolAdmission.check E adv = .ok (E', result)),
    FamilyValid b E' KCheckBoolIsland.family


def check_old_constant : Prop :=
  ∀ {height : Nat} {tower : SetValue.UniverseTower.{u} height}
    {b : Base tower}
    (indexed : ∀ i, SetValue.IndexedUnionClosed (tower.level i))
    {E E' : Env} {adv : KCheck.Advice} {result : Receipt}
    (initial : E.Valid b) (rooted : Rooted E)
    (run : KCheckBoolAdmission.check E adv = .ok (E', result))
    (name : Lean.Name) (known : (E.find name).isSome = true),
    (E'.assignment b).constants name = (E.assignment b).constants name


def check_initialized : Prop :=
  ∀ {height : Nat} {tower : SetValue.UniverseTower.{u} height}
    (realizer : TowerRealizer tower)
    (hasNat : BaseMath.Nat.HasNat tower)
    (indexed : ∀ i, SetValue.IndexedUnionClosed (tower.level i))
    {E' : Env} {adv : KCheck.Advice} {result : Receipt}
    (run : KCheckBoolAdmission.check PSigmaSeed.seed adv = .ok (E', result)),
    KCheck.InitializedSound.Initialized realizer E'

end SoundLiteral

namespace CasesLiteral

def payloads : Prop :=
  KCheckBoolAdmission.Cases.outputs.Payloads


def covered : Prop :=
  KCheckBoolAdmission.Cases.outputs.covered = true


def initial_fresh : Prop :=
  KCheckBoolAdmission.fresh PSigmaSeed.seed = true


def actual_runs : Prop :=
  KCheckBoolAdmission.Runs PSigmaSeed.seed headers CompleteOperationalRun.frames KCheckBoolAdmission.Cases.outputs.entries


def actual_frames : Prop :=
  KCheckBoolAdmission.Frames.parse (Advice.start CompleteOperationalRun.advice) =
      some CompleteOperationalRun.frames


def checked_environment : Prop :=
  KCheckBoolAdmission.checkedEnv PSigmaSeed.seed KCheckBoolAdmission.Cases.outputs.entries = E11


def installed_environment : Prop :=
  KCheckBoolAdmission.install PSigmaSeed.seed KCheckBoolAdmission.Cases.outputs = BoolFamily.registered


def transaction_accepted : Prop :=
  KCheckBoolAdmission.check PSigmaSeed.seed (Advice.start CompleteOperationalRun.advice) =
      .ok (BoolFamily.registered, KCheckBoolAdmission.receipt KCheckBoolAdmission.Cases.outputs)


def actual_receipt : Prop :=
  KCheckBoolAdmission.receipt KCheckBoolAdmission.Cases.outputs =
    ⟨formerName, .familyConstant, formerEntry.bound, formerType⟩


def four_bodies_retained : Prop :=
  (ModelSealing.sealEntry nominalNames KCheckBoolAdmission.Cases.outputs.former).value = some formerValue ∧
    (ModelSealing.sealEntry nominalNames KCheckBoolAdmission.Cases.outputs.zero).value = some zeroValue ∧
    (ModelSealing.sealEntry nominalNames KCheckBoolAdmission.Cases.outputs.one).value = some oneValue ∧
    (ModelSealing.sealEntry nominalNames KCheckBoolAdmission.Cases.outputs.recursor).value = some recursorValue


def predicates_preserved : Prop :=
  RootedAt E3 (KCheckBoolAdmission.install PSigmaSeed.seed KCheckBoolAdmission.Cases.outputs)


def transaction_initialized : Prop :=
  ∀ {height : Nat} {tower : SetValue.UniverseTower.{u} height}
    (realizer : TowerRealizer tower)
    (hasNat : BaseMath.Nat.HasNat tower)
    (indexed : ∀ i, SetValue.IndexedUnionClosed (tower.level i)),
    KCheck.InitializedSound.Initialized realizer BoolFamily.registered


def transaction_family_valid : Prop :=
  ∀ {height : Nat} {tower : SetValue.UniverseTower.{u} height}
    (realizer : TowerRealizer tower)
    (hasNat : BaseMath.Nat.HasNat tower)
    (indexed : ∀ i, SetValue.IndexedUnionClosed (tower.level i)),
    FamilyValid (PSigmaBase.base realizer) BoolFamily.registered KCheckBoolIsland.family


def old_head_refused : Prop :=
  ∀ (adv : Advice),
    KCheckBoolAdmission.check E11 adv = .error (.inductiveBlock formerName)


def pending_refused : Prop :=
  ∀ (adv : Advice),
    KCheckBoolAdmission.check PSigmaSeed.seed { adv with pending := 1 } =
      .error (.inductiveBlock formerName)

end CasesLiteral

/- Only the complete `initial` binder (index 8) is deleted. -/
def omittedInitialValidity : Prop :=
  ∀ {height : Nat} {tower : SetValue.UniverseTower.{u} height}
    {b : Base tower}
    (indexed : ∀ i, SetValue.IndexedUnionClosed (tower.level i))
    {E E' : Env} {adv : KCheck.Advice} {result : Receipt}
     (rooted : Rooted E)
    (run : KCheckBoolAdmission.check E adv = .ok (E', result)),
    E'.Valid b ∧ RootedAt E E' ∧ Rooted E' ∧
      E'.families = E.families ++ [KCheckBoolIsland.family] ∧
      ∃ out : KCheckBoolAdmission.Outputs, E'.assignment b = (KCheckBoolAdmission.checkedEnv E out.entries).assignment b ∧
        result = KCheckBoolAdmission.receipt out


/- Only the complete `indexed` binder (index 3) is deleted. -/
def omittedIndexedClosure : Prop :=
  ∀ {height : Nat} {tower : SetValue.UniverseTower.{u} height}
    {b : Base tower}

    {E : Env} {frames : List ByteArray} {out : KCheckBoolAdmission.Outputs}
    (initial : E.Valid b) (rooted : Rooted E)
    (runs : KCheckBoolAdmission.Runs E headers frames out.entries) (payloads : out.Payloads)
    (covered : out.covered = true),
    (KCheckBoolAdmission.install E out).Valid b


/- Only the complete `freshNames` binder (index 2) is deleted. -/
def omittedFreshness : Prop :=
  ∀ {E : Env} (out : KCheckBoolAdmission.Outputs) ,
    KCheckBoolAdmission.install E out =
      ⟨E.entries ++ out.entries.map (ModelSealing.sealEntry nominalNames),
        E.families ++ [KCheckBoolIsland.family]⟩


/- Only the expected receipt kind changes; the original proof value is reused. -/
def wrongReceiptKind : Prop :=
  KCheckBoolAdmission.receipt KCheckBoolAdmission.Cases.outputs =
    ⟨formerName, .definition, formerEntry.bound, formerType⟩

end AtomicBoolContracts
