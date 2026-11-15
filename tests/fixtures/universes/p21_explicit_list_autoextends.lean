-- P21 — an explicit `.{...}` universe list is NOT exhaustive: a universe
-- level left undetermined in the declaration's TYPE becomes an extra
-- parameter after the written ones, as in Lean.
--
-- FLIPPED BACK 2026-10-19 from a FAIL pin to a PASS pin, and renamed back
-- from `p21_explicit_list_closed_MUST_FAIL.lean`. On 2026-08-25 (U2 rung-4
-- explicitness channel) this probe was flipped to a refusal on the reading
-- that Lean's `sortDeclLevelParams` treats a non-empty user list as
-- exhaustive. It does not. `Lean/Elab/MutualDef.lean:1406` runs
-- `levelMVarToParamTypesPreDecls`, which turns a level metavariable left in a
-- declaration's type into a fresh parameter, and `sortDeclLevelParams`
-- (`Lean/Elab/DeclUtil.lean:79-88`) appends every used parameter the list does
-- not name after the written ones; its only error is a written name the
-- declaration never uses. Measured on the pinned v4.30.0-rc2 `lean`, this
-- file elaborates with no error, and `#print` gives
--
--   def leak.{u, u_1} : (A : Type u) → A → (B : Type u_1) → B → B
--   def noAns.{u, u_1} : noEv → Type u
--
-- `noAns` is the graduation corpus's line (`ITreeEco.lean` and three others)
-- that the closed-list refusal broke once an unannotated `fun _` binder was
-- typed `?T : Sort ?u` (dded5a375): the corpus was rewritten to `noEv.{u}`
-- around it on 2026-10-17 (8d2642607). `docs/FRONTEND_CLASS_LEDGER.md` class
-- (164) has the history.
--
-- The use sites force the registered ARITY: `@leak.{0, 0}` and
-- `noAns.{0, 0}` are what Lean accepts; arity 1 would be a
-- `UniverseLevelMismatch`. A level left only in the VALUE is still refused,
-- as Lean refuses it: that is p54, this probe's MUST_FAIL twin.
def leak.{u} (A : Type u) (a : A) := fun (B : Type _) (b : B) => b

def useLeak : Nat := @leak.{0, 0} Nat Nat.zero Nat Nat.zero

def noEv.{u} : Type u := PUnit.{u+1}

def noAns.{u} : noEv → Type u := fun _ => PEmpty.{u+1}

def useNoAns : Type := noAns.{0, 0} PUnit.unit
