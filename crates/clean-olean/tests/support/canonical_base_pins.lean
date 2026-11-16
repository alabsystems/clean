/- Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0 -/
import Lean
import CICL.BaseFamilies
open Lean
namespace CleanPinReview

def level (parameters : List Name) : CICL.Level → Except String Lean.Level
  | .zero => .ok .zero
  | .succ value => return .succ (← level parameters value)
  | .max left right => return .max (← level parameters left) (← level parameters right)
  | .imax left right => return .imax (← level parameters left) (← level parameters right)
  | .param index => match parameters[index]? with
    | some name => .ok (.param name)
    | none => .error s!"out-of-range universe parameter {index}"

def binder : CICL.BinderInfo → Lean.BinderInfo
  | .default => .default
  | .implicit => .implicit
  | .strictImplicit => .strictImplicit
  | .instImplicit => .instImplicit

def expression (parameters : List Name) : CICL.Expr Unit → Except String Lean.Expr
  | .bvar index => .ok (.bvar index)
  | .fvar _ => .error "free variable in pin"
  | .sort value => return .sort (← level parameters value)
  | .const name levels => return .const name (← levels.mapM (level parameters))
  | .app function argument => return .app (← expression parameters function) (← expression parameters argument)
  | .lam name type body info => return .lam name (← expression parameters type) (← expression parameters body) (binder info)
  | .pi name type body info => return .forallE name (← expression parameters type) (← expression parameters body) (binder info)
  | .letE name type value body hint => return .letE name (← expression parameters type) (← expression parameters value) (← expression parameters body) hint
  | .lit (.natVal value) => .ok (.lit (.natVal value))
  | .lit (.strVal value) => .ok (.lit (.strVal value))
  | .proj name field body => return .proj name field (← expression parameters body)
  | .mdata _ _ => .error "metadata in pin"


def checkRecursor (pin : CICL.RecursorDescriptor Unit) (info : Lean.RecursorVal) : Lean.Elab.Command.CommandElabM Unit := do
  unless pin.families == info.all && pin.parameters == info.numParams && pin.indices == info.numIndices &&
      pin.motives == info.numMotives && pin.minors == info.numMinors && pin.k == info.k &&
      pin.unsafeDecl == info.isUnsafe && pin.rules.length == info.rules.length do
    throwError "recursor payload mismatch"
  for (rule, actualRule) in pin.rules.zip info.rules do
    let rhs ← match expression info.levelParams rule.rhs with
      | .ok rhs => pure rhs
      | .error reason => throwError "{reason}"
    unless rule.constructorName == actualRule.ctor && rule.fields == actualRule.nfields && Lean.Expr.equal rhs actualRule.rhs do
      throwError "recursor rule mismatch"

def checkFamily (family : CICL.BaseFamily Unit) (expectedFamily : Lean.Name)
    (expectedConstants : List Lean.Name) (expectedRecursor : Lean.Name) (tag : String) :
    Lean.Elab.Command.CommandElabM Unit := do
  let env ← getEnv
  unless family.constants.map (fun entry => entry.name) == expectedConstants &&
      family.recursorName == expectedRecursor do throwError "canonical constant/name census mismatch"
  for entry in family.constants do
    let some actual := env.find? entry.name | throwError "missing actual constant {entry.name}"
    unless actual.levelParams.length == entry.declaration.parameters do
      throwError "universe count mismatch {entry.name}"
    let reflected ← match expression actual.levelParams entry.declaration.type with
      | .ok type => pure type
      | .error reason => throwError "{reason}"
    unless Lean.Expr.equal reflected actual.type do throwError "literal type mismatch {entry.name}"
    let boundMatches := if expectedFamily == `Nat then
      if entry.name == expectedRecursor then
        match entry.bound with | .max (.succ (.succ .zero)) (.succ (.param 0)) => true | _ => false
      else match entry.bound with | .succ (.succ .zero) => true | _ => false
      else if entry.name == expectedRecursor then
        match entry.bound with | .max (.succ (.param 0)) (.succ (.param 1)) => true | _ => false
      else match entry.bound with | .succ (.param 0) => true | _ => false
    unless boundMatches do throwError "chosen bound pin mismatch {entry.name}"
    match entry.declaration.payload, actual with
    | .inductiveDecl pin, .inductInfo info =>
      unless pin.parameters == info.numParams && pin.indices == info.numIndices &&
          pin.families == info.all && pin.constructors == info.ctors && pin.nested == info.numNested &&
          pin.isRecursive == info.isRec && pin.isReflexive == info.isReflexive && pin.unsafeDecl == info.isUnsafe do
        throwError "inductive payload mismatch"
    | .constructorDecl pin, .ctorInfo info =>
      unless pin.family == info.induct && pin.ordinal == info.cidx && pin.parameters == info.numParams &&
          pin.fields == info.numFields && pin.unsafeDecl == info.isUnsafe do
        throwError "constructor payload mismatch"
    | .recursorDecl pin, .recInfo info => checkRecursor pin info
    | _, _ => throwError "declaration kind mismatch {entry.name}"
    logInfo s!"CANONICAL_{tag}_PIN {entry.name} exact-type-and-payload=ok"
  let [schema] := family.block.families | throwError "exact family block census mismatch"
  let some (.inductInfo info) := env.find? schema.name | throwError "block family kind mismatch"
  unless schema.name == expectedFamily && family.block.levelParameters == info.levelParams.length &&
      family.block.parameters == info.numParams && family.block.unsafeDecl == info.isUnsafe &&
      schema.constructors.map (fun ctor => ctor.name) == info.ctors do throwError "block metadata mismatch"
  let reflected ← match expression info.levelParams schema.type with
    | .ok type => pure type | .error reason => throwError "{reason}"
  unless Lean.Expr.equal reflected info.type do throwError "block literal type mismatch"
  for ctor in schema.constructors do
    let some (.ctorInfo actual) := env.find? ctor.name | throwError "block constructor kind mismatch"
    let reflected ← match expression info.levelParams ctor.type with
      | .ok type => pure type | .error reason => throwError "{reason}"
    unless Lean.Expr.equal reflected actual.type do throwError "block constructor literal type mismatch"
  let some (.recInfo recursor) := env.find? family.recursorName | throwError "family recursor kind mismatch"
  checkRecursor family.recursor recursor
  logInfo s!"CANONICAL_{tag}_FAMILY record-and-block=ok"

run_cmd do
  let env ← getEnv
  let [family,punitFamily,natFamily] := (CICL.BaseFamilies.all : List (CICL.BaseFamily Unit)) | throwError "exact Eq/PUnit/Nat family census changed"
  checkFamily family `Eq [`Eq,`Eq.refl,`Eq.rec] `Eq.rec "EQ"
  checkFamily punitFamily `PUnit [`PUnit,`PUnit.unit,`PUnit.rec] `PUnit.rec "PUNIT"
  checkFamily natFamily `Nat [`Nat,`Nat.zero,`Nat.succ,`Nat.rec] `Nat.rec "NAT"
  logInfo "CANONICAL_BASE_FAMILY_CENSUS count=3"
  let some (.inductInfo info) := env.find? `Eq | throwError "Eq kind mismatch"
  let actualEq := info.type
  let .forallE name domain body _ := actualEq | throwError "Eq type shape changed"
  let changedAnnotation := Lean.Expr.forallE name domain body .default
  let changedName := Lean.Expr.forallE (.str .anonymous "changedBinder") domain body .implicit
  unless actualEq == changedAnnotation && actualEq == changedName &&
      !Lean.Expr.equal actualEq changedAnnotation && !Lean.Expr.equal actualEq changedName do
    throwError "structural comparator control failed"
  logInfo "CANONICAL_EQ_COMPARATOR alpha-equal-binder-mutations-refused=ok"
  let some (.ctorInfo info) := env.find? `Nat.succ | throwError "Nat.succ kind mismatch"
  let actual := info.type
  let .forallE name domain body _ := actual | throwError "Nat.succ type shape changed"
  let changedAnnotation := Lean.Expr.forallE name domain body .implicit
  let changedName := Lean.Expr.forallE (.str .anonymous "changedNatBinder") domain body .default
  unless actual == changedAnnotation && actual == changedName &&
      !Lean.Expr.equal actual changedAnnotation && !Lean.Expr.equal actual changedName do
    throwError "Nat structural comparator control failed"
  logInfo "CANONICAL_NAT_COMPARATOR alpha-equal-binder-mutations-refused=ok"
end CleanPinReview
