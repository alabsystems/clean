/- Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0 -/
/-
Compares the pinned terms of `CICL.BaseFamilies` with the environment of the Lean
that runs this file (the one `theories/cic_l/lean-toolchain` names). The level test
`base_family_terms_equal_pinned_lean` (crates/clean-olean/tests/cic_l_level.rs) runs
it with the pinned `lean`, `LEAN_PATH` holding the compiled `cic_l_level` fixture and
pinned Lean's library. By hand, from `theories/cic_l` after `lake build`:

  lake env lean ../../crates/clean-olean/tests/cic_l_level/compare_pinned_terms.lean

Each `CICL.Expr` is translated to a `Lean.Expr`, reading `Level.param i` as the i-th
universe parameter of the declaration, and compared with `Lean.Expr.equal`, which
takes binder names and binder annotations into account. The descriptors are compared
field by field. A mismatch is an error, so the file fails to elaborate. Controls
cover binder annotations, universe argument order, constructor field counts and
recursor bodies.
-/
import Lean
import CICL.BaseFamilies
open Lean Elab Command

def toLevel (params : List Name) : CICL.Level → Level
  | .zero => .zero
  | .succ l => .succ (toLevel params l)
  | .max a b => .max (toLevel params a) (toLevel params b)
  | .imax a b => .imax (toLevel params a) (toLevel params b)
  | .param i => .param (params.getD i `outOfRange)

def toBinderInfo : CICL.BinderInfo → BinderInfo
  | .default => .default
  | .implicit => .implicit
  | .strictImplicit => .strictImplicit
  | .instImplicit => .instImplicit

def toExpr (params : List Name) : CICL.Expr Unit → Expr
  | .bvar i => .bvar i
  | .fvar n => .fvar ⟨n⟩
  | .sort l => .sort (toLevel params l)
  | .const n ls => .const n (ls.map (toLevel params))
  | .app f a => .app (toExpr params f) (toExpr params a)
  | .lam n t b bi => .lam n (toExpr params t) (toExpr params b) (toBinderInfo bi)
  | .pi n t b bi => .forallE n (toExpr params t) (toExpr params b) (toBinderInfo bi)
  | .letE n t v b nd => .letE n (toExpr params t) (toExpr params v) (toExpr params b) nd
  | .lit (.natVal v) => .lit (.natVal v)
  | .lit (.strVal v) => .lit (.strVal v)
  | .proj n i b => .proj n i (toExpr params b)
  | .mdata _ b => toExpr params b

def same (label : String) (ok : Bool) : CommandElabM Unit := do
  unless ok do throwError "MISMATCH {label}"
  logInfo m!"MATCH {label}"

def differs (label : String) (ok : Bool) : CommandElabM Unit := do
  if ok then throwError "CONTROL NOT DETECTED {label}"
  logInfo m!"CONTROL DETECTED {label}"

open CICL.BaseFamilies.Eq in
run_cmd do
  let env ← getEnv
  let some (.inductInfo eq) := env.find? ``Eq | throwError "no Eq"
  let some (.ctorInfo refl) := env.find? ``Eq.refl | throwError "no Eq.refl"
  let some (.recInfo rec) := env.find? ``Eq.rec | throwError "no Eq.rec"
  let d := (declaration : CICL.ConstantDecl Unit)
  let rd := (reflDeclaration : CICL.ConstantDecl Unit)
  let cd := (recDeclaration : CICL.ConstantDecl Unit)
  same "Eq name" (name == ``Eq && reflName == ``Eq.refl && recName == ``Eq.rec)
  same "Eq universe parameter count" (eq.levelParams.length == d.parameters)
  same "Eq type" ((toExpr eq.levelParams d.type).equal eq.type)
  match d.payload with
  | .inductiveDecl i =>
    same "Eq descriptor" (i.parameters == eq.numParams && i.indices == eq.numIndices &&
      i.families == eq.all && i.constructors == eq.ctors && i.nested == eq.numNested &&
      i.isRecursive == eq.isRec && i.isReflexive == eq.isReflexive && i.unsafeDecl == eq.isUnsafe)
  | _ => throwError "Eq payload is not inductive"
  same "Eq.refl universe parameter count" (refl.levelParams.length == rd.parameters)
  same "Eq.refl type" ((toExpr refl.levelParams rd.type).equal refl.type)
  match rd.payload with
  | .constructorDecl c =>
    same "Eq.refl descriptor" (c.family == refl.induct && c.ordinal == refl.cidx &&
      c.parameters == refl.numParams && c.fields == refl.numFields && c.unsafeDecl == refl.isUnsafe)
  | _ => throwError "Eq.refl payload is not a constructor"
  same "Eq.rec universe parameter count" (rec.levelParams.length == cd.parameters)
  same "Eq.rec type" ((toExpr rec.levelParams cd.type).equal rec.type)
  match cd.payload with
  | .recursorDecl r =>
    same "Eq.rec descriptor" (r.families == rec.all && r.parameters == rec.numParams &&
      r.indices == rec.numIndices && r.motives == rec.numMotives && r.minors == rec.numMinors &&
      r.k == rec.k && r.unsafeDecl == rec.isUnsafe && r.rules.length == rec.rules.length)
    match r.rules, rec.rules with
    | [rule], [leanRule] =>
      same "Eq.rec rule" (rule.constructorName == leanRule.ctor && rule.fields == leanRule.nfields &&
        (toExpr rec.levelParams rule.rhs).equal leanRule.rhs)
    | _, _ => throwError "Eq.rec does not have exactly one rule"
  | _ => throwError "Eq.rec payload is not a recursor"
  -- Controls: the comparison sees a binder annotation and the order of universe arguments.
  let flipped : CICL.Expr Unit := match (type : CICL.Expr Unit) with
    | .pi n t b _ => .pi n t b .default
    | other => other
  differs "Eq type with its first binder made explicit" ((toExpr eq.levelParams flipped).equal eq.type)
  differs "Eq.rec type with its universe parameters swapped"
    ((toExpr rec.levelParams.reverse cd.type).equal rec.type)

def termMatches (params : List Name) (pin : CICL.Expr Unit) (actual : Expr) : Bool :=
  (toExpr params pin).equal actual

def constructorMatches (pin : CICL.ConstructorDescriptor) (actual : ConstructorVal) : Bool :=
  pin.family == actual.induct && pin.ordinal == actual.cidx &&
    pin.parameters == actual.numParams && pin.fields == actual.numFields && pin.unsafeDecl == actual.isUnsafe

def ruleMatches (params : List Name) (pin : CICL.RecursorRule Unit) (actual : RecursorRule) : Bool :=
  pin.constructorName == actual.ctor && pin.fields == actual.nfields &&
    termMatches params pin.rhs actual.rhs

/-- Compare against an explicit upstream name, so changing a pinned name cannot
silently redirect the comparison to another declaration. -/
def compareBaseDeclaration (label : String) (upstream declared : Name)
    (pin : CICL.ConstantDecl Unit) : CommandElabM Unit := do
  let env ← getEnv
  let some info := env.find? upstream | throwError "no {upstream}"
  same (label ++ " name") (declared == upstream)
  same (label ++ " universe parameter count") (info.levelParams.length == pin.parameters)
  same (label ++ " type") (termMatches info.levelParams pin.type info.type)
  match pin.payload, info with
  | .inductiveDecl i, .inductInfo actual =>
    same (label ++ " descriptor") (i.parameters == actual.numParams && i.indices == actual.numIndices &&
      i.families == actual.all && i.constructors == actual.ctors && i.nested == actual.numNested &&
      i.isRecursive == actual.isRec && i.isReflexive == actual.isReflexive && i.unsafeDecl == actual.isUnsafe)
  | .constructorDecl c, .ctorInfo actual =>
    same (label ++ " descriptor") (constructorMatches c actual)
  | .recursorDecl r, .recInfo actual =>
    same (label ++ " descriptor") (r.families == actual.all && r.parameters == actual.numParams &&
      r.indices == actual.numIndices && r.motives == actual.numMotives && r.minors == actual.numMinors &&
      r.k == actual.k && r.unsafeDecl == actual.isUnsafe && r.rules.length == actual.rules.length)
    for (rule, actualRule) in r.rules.zip actual.rules do
      same (label ++ " rule " ++ actualRule.ctor.toString)
        (ruleMatches actual.levelParams rule actualRule)
  | _, _ => throwError "{label} payload kind differs from pinned Lean"

run_cmd do
  compareBaseDeclaration "PUnit" ``PUnit CICL.BaseFamilies.PUnit.name
    CICL.BaseFamilies.PUnit.declaration
  compareBaseDeclaration "PUnit.unit" ``PUnit.unit CICL.BaseFamilies.PUnit.unitName
    CICL.BaseFamilies.PUnit.unitDeclaration
  compareBaseDeclaration "PUnit.rec" ``PUnit.rec CICL.BaseFamilies.PUnit.recName
    CICL.BaseFamilies.PUnit.recDeclaration
  compareBaseDeclaration "Nat" ``Nat CICL.BaseFamilies.Nat.name
    CICL.BaseFamilies.Nat.declaration
  compareBaseDeclaration "Nat.zero" ``Nat.zero CICL.BaseFamilies.Nat.zeroName
    CICL.BaseFamilies.Nat.zeroDeclaration
  compareBaseDeclaration "Nat.succ" ``Nat.succ CICL.BaseFamilies.Nat.succName
    CICL.BaseFamilies.Nat.succDeclaration
  compareBaseDeclaration "Nat.rec" ``Nat.rec CICL.BaseFamilies.Nat.recName
    CICL.BaseFamilies.Nat.recDeclaration

  let env ← getEnv
  let some (.recInfo unitRec) := env.find? ``PUnit.rec | throwError "no PUnit.rec"
  differs "PUnit.rec type with its universe parameters swapped"
    (termMatches unitRec.levelParams.reverse CICL.BaseFamilies.PUnit.recType unitRec.type)
  let some (.ctorInfo succ) := env.find? ``Nat.succ | throwError "no Nat.succ"
  let .constructorDecl succPin := (CICL.BaseFamilies.Nat.succDeclaration : CICL.ConstantDecl Unit).payload
    | throwError "Nat.succ pin is not a constructor"
  differs "Nat.succ descriptor with no field" (constructorMatches { succPin with fields := 0 } succ)
  let some (.recInfo natRec) := env.find? ``Nat.rec | throwError "no Nat.rec"
  let some succRule := natRec.rules.find? (fun r => r.ctor == ``Nat.succ)
    | throwError "no Nat.succ rule"
  let .recursorDecl recPin := (CICL.BaseFamilies.Nat.recDeclaration : CICL.ConstantDecl Unit).payload
    | throwError "Nat.rec pin is not a recursor"
  let some rulePin := recPin.rules.find? (fun r => r.constructorName == ``Nat.succ)
    | throwError "no pinned Nat.succ rule"
  differs "Nat.rec successor rule replaced by zero rule"
    (ruleMatches natRec.levelParams { rulePin with rhs := CICL.BaseFamilies.Nat.zeroRule } succRule)
