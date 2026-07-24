-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Incremental preprocessing reuse soundness for ay SAT-COMP runs. The
-- propositions stand for original formulas, incremental clause/assumption
-- frames, unchanged prefixes, canonical preprocessing artifacts, manifest/
-- digest/epoch guards, recomputation diagnostics, and public SAT/UNSAT
-- reports.

def AyConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyEquisat (before : Prop) (after : Prop) :=
  AyConj (before -> after) (after -> before)

def AySat (cnf : Prop) (model : Prop) :=
  AyConj cnf model

def AyReplay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def AyIdMatch (leftId : Prop) (rightId : Prop) :=
  AyConj (leftId -> rightId) (rightId -> leftId)

def AyDigestMatch (cachedDigest : Prop) (runDigest : Prop) :=
  AyConj (cachedDigest -> runDigest) (runDigest -> cachedDigest)

def AyIncrementalFrame
    (baseCnf : Prop) (addedClauses : Prop) (assumptions : Prop) :=
  AyConj baseCnf (AyConj addedClauses assumptions)

def AyUnchangedPrefix (cachedPrefix : Prop) (currentPrefix : Prop) :=
  AyEquisat cachedPrefix currentPrefix

def AyCanonicalPreprocessArtifact (prefixCnf : Prop) (visibleCnf : Prop) :=
  AyEquisat prefixCnf visibleCnf

def AyIncrementalGuards
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :=
  AyConj
    (AyIdMatch cachedEpoch currentEpoch)
    (AyConj
      (AyIdMatch cachedManifest runManifest)
      (AyDigestMatch cachedDigest runDigest))

def AyAcceptedIncrementalReuse
    (cachedPrefix : Prop) (currentPrefix : Prop)
    (visibleCnf : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :=
  AyConj
    (AyUnchangedPrefix cachedPrefix currentPrefix)
    (AyConj
      (AyCanonicalPreprocessArtifact cachedPrefix visibleCnf)
      (AyIncrementalGuards
        cachedEpoch currentEpoch cachedManifest runManifest
        cachedDigest runDigest))

def AyIncrementalInvalidation
    (changedClauses : Prop) (changedAssumptions : Prop) :=
  AyDisj changedClauses changedAssumptions

def AyNoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def AyRecomputeObligation (currentFrame : Prop) (recompute : Prop) :=
  AyConj currentFrame recompute

def AyAppendOnlyEntry (previousLog : Prop) (entry : Prop) (nextLog : Prop) :=
  AyConj previousLog (AyConj entry nextLog)

def AyAcceptedIncrementalLogEntry
    (previousLog : Prop) (nextLog : Prop)
    (cachedPrefix : Prop) (currentPrefix : Prop) (visibleCnf : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :=
  AyAppendOnlyEntry previousLog
    (AyAcceptedIncrementalReuse
      cachedPrefix currentPrefix visibleCnf
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest)
    nextLog

def AyInvalidationLogEntry
    (previousLog : Prop) (nextLog : Prop)
    (currentFrame : Prop) (changedClauses : Prop)
    (changedAssumptions : Prop) (recompute : Prop) (diagnostic : Prop) :=
  AyAppendOnlyEntry previousLog
    (AyConj
      (AyIncrementalInvalidation changedClauses changedAssumptions)
      (AyConj
        (AyRecomputeObligation currentFrame recompute)
        (AyNoSemanticClaim diagnostic)))
    nextLog

def AySatPullback (visibleModel : Prop) (originalModel : Prop) :=
  visibleModel -> originalModel

def AyExitCodeSound (exitCode : Prop) (claim : Prop) :=
  AyConj exitCode claim

def AyPublicResult
    (currentPrefix : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  AyDisj
    (AyExitCodeSound exitCode (AySat currentPrefix originalModel))
    (AyExitCodeSound exitCode (certificate -> currentPrefix -> conflict))

theorem ay_pir_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyConj left right := by
  intro hleft
  intro hright
  intro result
  intro build
  exact build hleft hright

theorem ay_pir_conj_left
    (left : Prop) (right : Prop) :
    AyConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_pir_conj_right
    (left : Prop) (right : Prop) :
    AyConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_pir_disj_left
    (left : Prop) (right : Prop) :
    left -> AyDisj left right := by
  intro hleft
  intro result
  intro left_case
  intro _right_case
  exact left_case hleft

theorem ay_pir_disj_right
    (left : Prop) (right : Prop) :
    right -> AyDisj left right := by
  intro hright
  intro result
  intro _left_case
  intro right_case
  exact right_case hright

theorem ay_pir_equisat_forward
    (before : Prop) (after : Prop) :
    AyEquisat before after ->
    before ->
    after := by
  intro eq
  exact ay_pir_conj_left (before -> after) (after -> before) eq

theorem ay_pir_equisat_backward
    (before : Prop) (after : Prop) :
    AyEquisat before after ->
    after ->
    before := by
  intro eq
  exact ay_pir_conj_right (before -> after) (after -> before) eq

theorem ay_pir_sat_cnf
    (cnf : Prop) (model : Prop) :
    AySat cnf model ->
    cnf := by
  intro sat
  exact ay_pir_conj_left cnf model sat

theorem ay_pir_sat_model
    (cnf : Prop) (model : Prop) :
    AySat cnf model ->
    model := by
  intro sat
  exact ay_pir_conj_right cnf model sat

theorem ay_pir_frame_base
    (baseCnf : Prop) (addedClauses : Prop) (assumptions : Prop) :
    AyIncrementalFrame baseCnf addedClauses assumptions ->
    baseCnf := by
  intro frame
  exact ay_pir_conj_left baseCnf (AyConj addedClauses assumptions) frame

theorem ay_pir_frame_clauses
    (baseCnf : Prop) (addedClauses : Prop) (assumptions : Prop) :
    AyIncrementalFrame baseCnf addedClauses assumptions ->
    addedClauses := by
  intro frame
  exact ay_pir_conj_left addedClauses assumptions
    (ay_pir_conj_right baseCnf (AyConj addedClauses assumptions) frame)

theorem ay_pir_frame_assumptions
    (baseCnf : Prop) (addedClauses : Prop) (assumptions : Prop) :
    AyIncrementalFrame baseCnf addedClauses assumptions ->
    assumptions := by
  intro frame
  exact ay_pir_conj_right addedClauses assumptions
    (ay_pir_conj_right baseCnf (AyConj addedClauses assumptions) frame)

theorem ay_pir_id_match_forward
    (leftId : Prop) (rightId : Prop) :
    AyIdMatch leftId rightId ->
    leftId ->
    rightId := by
  intro hmatch
  intro hleft
  exact ay_pir_conj_left (leftId -> rightId) (rightId -> leftId)
    hmatch hleft

theorem ay_pir_digest_match_forward
    (cachedDigest : Prop) (runDigest : Prop) :
    AyDigestMatch cachedDigest runDigest ->
    cachedDigest ->
    runDigest := by
  intro hmatch
  intro hcached
  exact ay_pir_conj_left
    (cachedDigest -> runDigest)
    (runDigest -> cachedDigest)
    hmatch
    hcached

theorem ay_pir_guards_epoch
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :
    AyIncrementalGuards
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest ->
    AyIdMatch cachedEpoch currentEpoch := by
  intro guards
  exact ay_pir_conj_left
    (AyIdMatch cachedEpoch currentEpoch)
    (AyConj
      (AyIdMatch cachedManifest runManifest)
      (AyDigestMatch cachedDigest runDigest))
    guards

theorem ay_pir_guards_manifest
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :
    AyIncrementalGuards
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest ->
    AyIdMatch cachedManifest runManifest := by
  intro guards
  exact ay_pir_conj_left
    (AyIdMatch cachedManifest runManifest)
    (AyDigestMatch cachedDigest runDigest)
    (ay_pir_conj_right
      (AyIdMatch cachedEpoch currentEpoch)
      (AyConj
        (AyIdMatch cachedManifest runManifest)
        (AyDigestMatch cachedDigest runDigest))
      guards)

theorem ay_pir_guards_digest
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :
    AyIncrementalGuards
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest ->
    AyDigestMatch cachedDigest runDigest := by
  intro guards
  exact ay_pir_conj_right
    (AyIdMatch cachedManifest runManifest)
    (AyDigestMatch cachedDigest runDigest)
    (ay_pir_conj_right
      (AyIdMatch cachedEpoch currentEpoch)
      (AyConj
        (AyIdMatch cachedManifest runManifest)
        (AyDigestMatch cachedDigest runDigest))
      guards)

theorem ay_pir_reuse_prefix
    (cachedPrefix : Prop) (currentPrefix : Prop) (visibleCnf : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :
    AyAcceptedIncrementalReuse
      cachedPrefix currentPrefix visibleCnf cachedEpoch currentEpoch
      cachedManifest runManifest cachedDigest runDigest ->
    AyUnchangedPrefix cachedPrefix currentPrefix := by
  intro reuse
  exact ay_pir_conj_left
    (AyUnchangedPrefix cachedPrefix currentPrefix)
    (AyConj
      (AyCanonicalPreprocessArtifact cachedPrefix visibleCnf)
      (AyIncrementalGuards
        cachedEpoch currentEpoch cachedManifest runManifest
        cachedDigest runDigest))
    reuse

theorem ay_pir_reuse_artifact
    (cachedPrefix : Prop) (currentPrefix : Prop) (visibleCnf : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :
    AyAcceptedIncrementalReuse
      cachedPrefix currentPrefix visibleCnf cachedEpoch currentEpoch
      cachedManifest runManifest cachedDigest runDigest ->
    AyCanonicalPreprocessArtifact cachedPrefix visibleCnf := by
  intro reuse
  exact ay_pir_conj_left
    (AyCanonicalPreprocessArtifact cachedPrefix visibleCnf)
    (AyIncrementalGuards
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest)
    (ay_pir_conj_right
      (AyUnchangedPrefix cachedPrefix currentPrefix)
      (AyConj
        (AyCanonicalPreprocessArtifact cachedPrefix visibleCnf)
        (AyIncrementalGuards
          cachedEpoch currentEpoch cachedManifest runManifest
          cachedDigest runDigest))
      reuse)

theorem ay_pir_reuse_guards
    (cachedPrefix : Prop) (currentPrefix : Prop) (visibleCnf : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :
    AyAcceptedIncrementalReuse
      cachedPrefix currentPrefix visibleCnf cachedEpoch currentEpoch
      cachedManifest runManifest cachedDigest runDigest ->
    AyIncrementalGuards
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest := by
  intro reuse
  exact ay_pir_conj_right
    (AyCanonicalPreprocessArtifact cachedPrefix visibleCnf)
    (AyIncrementalGuards
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest)
    (ay_pir_conj_right
      (AyUnchangedPrefix cachedPrefix currentPrefix)
      (AyConj
        (AyCanonicalPreprocessArtifact cachedPrefix visibleCnf)
        (AyIncrementalGuards
          cachedEpoch currentEpoch cachedManifest runManifest
          cachedDigest runDigest))
      reuse)

theorem ay_pir_reuse_current_epoch
    (cachedPrefix : Prop) (currentPrefix : Prop) (visibleCnf : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :
    AyAcceptedIncrementalReuse
      cachedPrefix currentPrefix visibleCnf cachedEpoch currentEpoch
      cachedManifest runManifest cachedDigest runDigest ->
    cachedEpoch ->
    currentEpoch := by
  intro reuse
  exact ay_pir_id_match_forward cachedEpoch currentEpoch
    (ay_pir_guards_epoch cachedEpoch currentEpoch
      cachedManifest runManifest cachedDigest runDigest
      (ay_pir_reuse_guards cachedPrefix currentPrefix visibleCnf
        cachedEpoch currentEpoch cachedManifest runManifest
        cachedDigest runDigest reuse))

theorem ay_pir_reuse_run_manifest
    (cachedPrefix : Prop) (currentPrefix : Prop) (visibleCnf : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :
    AyAcceptedIncrementalReuse
      cachedPrefix currentPrefix visibleCnf cachedEpoch currentEpoch
      cachedManifest runManifest cachedDigest runDigest ->
    cachedManifest ->
    runManifest := by
  intro reuse
  exact ay_pir_id_match_forward cachedManifest runManifest
    (ay_pir_guards_manifest cachedEpoch currentEpoch
      cachedManifest runManifest cachedDigest runDigest
      (ay_pir_reuse_guards cachedPrefix currentPrefix visibleCnf
        cachedEpoch currentEpoch cachedManifest runManifest
        cachedDigest runDigest reuse))

theorem ay_pir_reuse_run_digest
    (cachedPrefix : Prop) (currentPrefix : Prop) (visibleCnf : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :
    AyAcceptedIncrementalReuse
      cachedPrefix currentPrefix visibleCnf cachedEpoch currentEpoch
      cachedManifest runManifest cachedDigest runDigest ->
    cachedDigest ->
    runDigest := by
  intro reuse
  exact ay_pir_digest_match_forward cachedDigest runDigest
    (ay_pir_guards_digest cachedEpoch currentEpoch
      cachedManifest runManifest cachedDigest runDigest
      (ay_pir_reuse_guards cachedPrefix currentPrefix visibleCnf
        cachedEpoch currentEpoch cachedManifest runManifest
        cachedDigest runDigest reuse))

theorem ay_pir_cached_to_visible
    (cachedPrefix : Prop) (currentPrefix : Prop) (visibleCnf : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :
    AyAcceptedIncrementalReuse
      cachedPrefix currentPrefix visibleCnf cachedEpoch currentEpoch
      cachedManifest runManifest cachedDigest runDigest ->
    cachedPrefix ->
    visibleCnf := by
  intro reuse
  exact ay_pir_equisat_forward cachedPrefix visibleCnf
    (ay_pir_reuse_artifact cachedPrefix currentPrefix visibleCnf
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest reuse)

theorem ay_pir_visible_to_cached
    (cachedPrefix : Prop) (currentPrefix : Prop) (visibleCnf : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :
    AyAcceptedIncrementalReuse
      cachedPrefix currentPrefix visibleCnf cachedEpoch currentEpoch
      cachedManifest runManifest cachedDigest runDigest ->
    visibleCnf ->
    cachedPrefix := by
  intro reuse
  exact ay_pir_equisat_backward cachedPrefix visibleCnf
    (ay_pir_reuse_artifact cachedPrefix currentPrefix visibleCnf
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest reuse)

theorem ay_pir_current_to_visible
    (cachedPrefix : Prop) (currentPrefix : Prop) (visibleCnf : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :
    AyAcceptedIncrementalReuse
      cachedPrefix currentPrefix visibleCnf cachedEpoch currentEpoch
      cachedManifest runManifest cachedDigest runDigest ->
    currentPrefix ->
    visibleCnf := by
  intro reuse
  intro hcurrent
  exact ay_pir_cached_to_visible cachedPrefix currentPrefix visibleCnf
    cachedEpoch currentEpoch cachedManifest runManifest cachedDigest runDigest
    reuse
    (ay_pir_equisat_backward cachedPrefix currentPrefix
      (ay_pir_reuse_prefix cachedPrefix currentPrefix visibleCnf
        cachedEpoch currentEpoch cachedManifest runManifest
        cachedDigest runDigest reuse)
      hcurrent)

theorem ay_pir_visible_to_current
    (cachedPrefix : Prop) (currentPrefix : Prop) (visibleCnf : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :
    AyAcceptedIncrementalReuse
      cachedPrefix currentPrefix visibleCnf cachedEpoch currentEpoch
      cachedManifest runManifest cachedDigest runDigest ->
    visibleCnf ->
    currentPrefix := by
  intro reuse
  intro hvisible
  exact ay_pir_equisat_forward cachedPrefix currentPrefix
    (ay_pir_reuse_prefix cachedPrefix currentPrefix visibleCnf
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest reuse)
    (ay_pir_visible_to_cached cachedPrefix currentPrefix visibleCnf
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest reuse hvisible)

theorem ay_pir_append_entry
    (previousLog : Prop) (entry : Prop) (nextLog : Prop) :
    AyAppendOnlyEntry previousLog entry nextLog ->
    entry := by
  intro log_entry
  exact ay_pir_conj_left entry nextLog
    (ay_pir_conj_right previousLog (AyConj entry nextLog) log_entry)

theorem ay_pir_append_ends
    (previousLog : Prop) (entry : Prop) (nextLog : Prop) :
    AyAppendOnlyEntry previousLog entry nextLog ->
    AyConj previousLog nextLog := by
  intro log_entry
  exact ay_pir_conj_intro previousLog nextLog
    (ay_pir_conj_left previousLog (AyConj entry nextLog) log_entry)
    (ay_pir_conj_right entry nextLog
      (ay_pir_conj_right previousLog (AyConj entry nextLog) log_entry))

theorem ay_pir_accepted_log_reuse
    (previousLog : Prop) (nextLog : Prop)
    (cachedPrefix : Prop) (currentPrefix : Prop) (visibleCnf : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :
    AyAcceptedIncrementalLogEntry
      previousLog nextLog cachedPrefix currentPrefix visibleCnf
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest ->
    AyAcceptedIncrementalReuse
      cachedPrefix currentPrefix visibleCnf
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest := by
  intro log_entry
  exact ay_pir_append_entry previousLog
    (AyAcceptedIncrementalReuse
      cachedPrefix currentPrefix visibleCnf
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest)
    nextLog log_entry

theorem ay_pir_accepted_log_append_only
    (previousLog : Prop) (nextLog : Prop)
    (cachedPrefix : Prop) (currentPrefix : Prop) (visibleCnf : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :
    AyAcceptedIncrementalLogEntry
      previousLog nextLog cachedPrefix currentPrefix visibleCnf
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest ->
    AyConj previousLog nextLog := by
  intro log_entry
  exact ay_pir_append_ends previousLog
    (AyAcceptedIncrementalReuse
      cachedPrefix currentPrefix visibleCnf
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest)
    nextLog log_entry

theorem ay_pir_invalidation_clauses
    (changedClauses : Prop) (changedAssumptions : Prop) :
    changedClauses ->
    AyIncrementalInvalidation changedClauses changedAssumptions := by
  exact ay_pir_disj_left changedClauses changedAssumptions

theorem ay_pir_invalidation_assumptions
    (changedClauses : Prop) (changedAssumptions : Prop) :
    changedAssumptions ->
    AyIncrementalInvalidation changedClauses changedAssumptions := by
  exact ay_pir_disj_right changedClauses changedAssumptions

theorem ay_pir_recompute_current_frame
    (currentFrame : Prop) (recompute : Prop) :
    AyRecomputeObligation currentFrame recompute ->
    currentFrame := by
  intro obligation
  exact ay_pir_conj_left currentFrame recompute obligation

theorem ay_pir_recompute_obligation
    (currentFrame : Prop) (recompute : Prop) :
    AyRecomputeObligation currentFrame recompute ->
    recompute := by
  intro obligation
  exact ay_pir_conj_right currentFrame recompute obligation

theorem ay_pir_invalidation_entry
    (currentFrame : Prop) (changedClauses : Prop)
    (changedAssumptions : Prop) (recompute : Prop) (diagnostic : Prop) :
    AyIncrementalInvalidation changedClauses changedAssumptions ->
    AyRecomputeObligation currentFrame recompute ->
    diagnostic ->
    AyConj
      (AyIncrementalInvalidation changedClauses changedAssumptions)
      (AyConj
        (AyRecomputeObligation currentFrame recompute)
        (AyNoSemanticClaim diagnostic)) := by
  intro invalidation
  intro obligation
  intro hdiagnostic
  exact ay_pir_conj_intro
    (AyIncrementalInvalidation changedClauses changedAssumptions)
    (AyConj
      (AyRecomputeObligation currentFrame recompute)
      (AyNoSemanticClaim diagnostic))
    invalidation
    (ay_pir_conj_intro
      (AyRecomputeObligation currentFrame recompute)
      (AyNoSemanticClaim diagnostic)
      obligation
      hdiagnostic)

theorem ay_pir_invalidation_log_entry
    (previousLog : Prop) (nextLog : Prop)
    (currentFrame : Prop) (changedClauses : Prop)
    (changedAssumptions : Prop) (recompute : Prop) (diagnostic : Prop) :
    AyInvalidationLogEntry
      previousLog nextLog currentFrame changedClauses
      changedAssumptions recompute diagnostic ->
    AyConj
      (AyIncrementalInvalidation changedClauses changedAssumptions)
      (AyConj
        (AyRecomputeObligation currentFrame recompute)
        (AyNoSemanticClaim diagnostic)) := by
  intro log_entry
  exact ay_pir_append_entry previousLog
    (AyConj
      (AyIncrementalInvalidation changedClauses changedAssumptions)
      (AyConj
        (AyRecomputeObligation currentFrame recompute)
        (AyNoSemanticClaim diagnostic)))
    nextLog log_entry

theorem ay_pir_invalidation_log_no_claim
    (previousLog : Prop) (nextLog : Prop)
    (currentFrame : Prop) (changedClauses : Prop)
    (changedAssumptions : Prop) (recompute : Prop) (diagnostic : Prop) :
    AyInvalidationLogEntry
      previousLog nextLog currentFrame changedClauses
      changedAssumptions recompute diagnostic ->
    AyNoSemanticClaim diagnostic := by
  intro log_entry
  exact ay_pir_conj_right
    (AyRecomputeObligation currentFrame recompute)
    (AyNoSemanticClaim diagnostic)
    (ay_pir_conj_right
      (AyIncrementalInvalidation changedClauses changedAssumptions)
      (AyConj
        (AyRecomputeObligation currentFrame recompute)
        (AyNoSemanticClaim diagnostic))
      (ay_pir_invalidation_log_entry previousLog nextLog currentFrame
        changedClauses changedAssumptions recompute diagnostic log_entry))

theorem ay_pir_invalidation_log_recompute
    (previousLog : Prop) (nextLog : Prop)
    (currentFrame : Prop) (changedClauses : Prop)
    (changedAssumptions : Prop) (recompute : Prop) (diagnostic : Prop) :
    AyInvalidationLogEntry
      previousLog nextLog currentFrame changedClauses
      changedAssumptions recompute diagnostic ->
    recompute := by
  intro log_entry
  exact ay_pir_recompute_obligation currentFrame recompute
    (ay_pir_conj_left
      (AyRecomputeObligation currentFrame recompute)
      (AyNoSemanticClaim diagnostic)
      (ay_pir_conj_right
        (AyIncrementalInvalidation changedClauses changedAssumptions)
        (AyConj
          (AyRecomputeObligation currentFrame recompute)
          (AyNoSemanticClaim diagnostic))
        (ay_pir_invalidation_log_entry previousLog nextLog currentFrame
          changedClauses changedAssumptions recompute diagnostic log_entry)))

theorem ay_pir_invalidation_log_append_only
    (previousLog : Prop) (nextLog : Prop)
    (currentFrame : Prop) (changedClauses : Prop)
    (changedAssumptions : Prop) (recompute : Prop) (diagnostic : Prop) :
    AyInvalidationLogEntry
      previousLog nextLog currentFrame changedClauses
      changedAssumptions recompute diagnostic ->
    AyConj previousLog nextLog := by
  intro log_entry
  exact ay_pir_append_ends previousLog
    (AyConj
      (AyIncrementalInvalidation changedClauses changedAssumptions)
      (AyConj
        (AyRecomputeObligation currentFrame recompute)
        (AyNoSemanticClaim diagnostic)))
    nextLog log_entry

theorem ay_pir_sat_pullback_sound
    (cachedPrefix : Prop) (currentPrefix : Prop) (visibleCnf : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (visibleModel : Prop) (originalModel : Prop) :
    AyAcceptedIncrementalReuse
      cachedPrefix currentPrefix visibleCnf cachedEpoch currentEpoch
      cachedManifest runManifest cachedDigest runDigest ->
    AySatPullback visibleModel originalModel ->
    AySat visibleCnf visibleModel ->
    AySat currentPrefix originalModel := by
  intro reuse
  intro pullback
  intro sat
  exact ay_pir_conj_intro currentPrefix originalModel
    (ay_pir_visible_to_current cachedPrefix currentPrefix visibleCnf
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest reuse
      (ay_pir_sat_cnf visibleCnf visibleModel sat))
    (pullback (ay_pir_sat_model visibleCnf visibleModel sat))

theorem ay_pir_unsat_pushforward_sound
    (cachedPrefix : Prop) (currentPrefix : Prop) (visibleCnf : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyAcceptedIncrementalReuse
      cachedPrefix currentPrefix visibleCnf cachedEpoch currentEpoch
      cachedManifest runManifest cachedDigest runDigest ->
    AyReplay visibleCnf certificate conflict ->
    certificate ->
    currentPrefix ->
    conflict := by
  intro reuse
  intro replay
  intro hcertificate
  intro hcurrent
  exact replay
    (ay_pir_current_to_visible cachedPrefix currentPrefix visibleCnf
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest reuse hcurrent)
    hcertificate

theorem ay_pir_exit_code_sound_intro
    (exitCode : Prop) (claim : Prop) :
    exitCode ->
    claim ->
    AyExitCodeSound exitCode claim := by
  exact ay_pir_conj_intro exitCode claim

theorem ay_pir_public_sat_result
    (currentPrefix : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    exitCode ->
    AySat currentPrefix originalModel ->
    AyPublicResult currentPrefix originalModel certificate conflict exitCode := by
  intro hexit
  intro sat
  exact ay_pir_disj_left
    (AyExitCodeSound exitCode (AySat currentPrefix originalModel))
    (AyExitCodeSound exitCode (certificate -> currentPrefix -> conflict))
    (ay_pir_exit_code_sound_intro exitCode
      (AySat currentPrefix originalModel)
      hexit
      sat)

theorem ay_pir_public_unsat_result
    (currentPrefix : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    exitCode ->
    (certificate -> currentPrefix -> conflict) ->
    AyPublicResult currentPrefix originalModel certificate conflict exitCode := by
  intro hexit
  intro unsat
  exact ay_pir_disj_right
    (AyExitCodeSound exitCode (AySat currentPrefix originalModel))
    (AyExitCodeSound exitCode (certificate -> currentPrefix -> conflict))
    (ay_pir_exit_code_sound_intro exitCode
      (certificate -> currentPrefix -> conflict)
      hexit
      unsat)

theorem ay_preprocess_incremental_sat_public_sound
    (previousLog : Prop) (nextLog : Prop)
    (cachedPrefix : Prop) (currentPrefix : Prop) (visibleCnf : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    AyAcceptedIncrementalLogEntry
      previousLog nextLog cachedPrefix currentPrefix visibleCnf
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest ->
    AySatPullback visibleModel originalModel ->
    AySat visibleCnf visibleModel ->
    exitCode ->
    AyPublicResult currentPrefix originalModel certificate conflict exitCode := by
  intro log_entry
  intro pullback
  intro sat
  intro hexit
  exact ay_pir_public_sat_result
    currentPrefix originalModel certificate conflict exitCode
    hexit
    (ay_pir_sat_pullback_sound cachedPrefix currentPrefix visibleCnf
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest visibleModel originalModel
      (ay_pir_accepted_log_reuse previousLog nextLog cachedPrefix
        currentPrefix visibleCnf cachedEpoch currentEpoch cachedManifest
        runManifest cachedDigest runDigest log_entry)
      pullback
      sat)

theorem ay_preprocess_incremental_unsat_public_sound
    (previousLog : Prop) (nextLog : Prop)
    (cachedPrefix : Prop) (currentPrefix : Prop) (visibleCnf : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    AyAcceptedIncrementalLogEntry
      previousLog nextLog cachedPrefix currentPrefix visibleCnf
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest ->
    AyReplay visibleCnf certificate conflict ->
    exitCode ->
    AyPublicResult currentPrefix originalModel certificate conflict exitCode := by
  intro log_entry
  intro replay
  intro hexit
  exact ay_pir_public_unsat_result
    currentPrefix originalModel certificate conflict exitCode
    hexit
    (ay_pir_unsat_pushforward_sound cachedPrefix currentPrefix visibleCnf
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest certificate conflict
      (ay_pir_accepted_log_reuse previousLog nextLog cachedPrefix
        currentPrefix visibleCnf cachedEpoch currentEpoch cachedManifest
        runManifest cachedDigest runDigest log_entry)
      replay)

theorem ay_preprocess_incremental_changed_no_stale_public_result
    (previousLog : Prop) (nextLog : Prop)
    (currentFrame : Prop) (changedClauses : Prop)
    (changedAssumptions : Prop) (recompute : Prop) (diagnostic : Prop) :
    AyInvalidationLogEntry
      previousLog nextLog currentFrame changedClauses
      changedAssumptions recompute diagnostic ->
    AyConj
      (AyIncrementalInvalidation changedClauses changedAssumptions)
      (AyConj
        (AyRecomputeObligation currentFrame recompute)
        (AyNoSemanticClaim diagnostic)) := by
  exact ay_pir_invalidation_log_entry previousLog nextLog currentFrame
    changedClauses changedAssumptions recompute diagnostic
