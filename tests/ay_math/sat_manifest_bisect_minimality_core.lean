-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Minimal culprit guarantees for ay SAT-COMP manifest-bisect diagnostics.
-- Minimality is diagnostic: it isolates the first digest/output disagreement
-- on an ordered run-manifest path without creating or destroying public
-- SAT/UNSAT semantic claims.

def AyDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyEquisat (before : Prop) (after : Prop) :=
  AyConj (before -> after) (after -> before)

def AyVisibleModelReconstruction (visibleModel : Prop) (originalModel : Prop) :=
  visibleModel -> originalModel

def AyPreprocessingProof (originalFormula : Prop) (visibleFormula : Prop) :=
  originalFormula -> visibleFormula

def AyUnsatReplayWitness (visibleFormula : Prop) (finalClause : Prop) :=
  finalClause -> visibleFormula -> False

def AySatArtifact (visibleModel : Prop) (originalModel : Prop) :=
  AyConj visibleModel
    (AyVisibleModelReconstruction visibleModel originalModel)

def AyUnsatArtifact
    (originalFormula : Prop) (visibleFormula : Prop) (finalClause : Prop) :=
  AyConj finalClause
    (AyConj
      (AyPreprocessingProof originalFormula visibleFormula)
      (AyUnsatReplayWitness visibleFormula finalClause))

def AyCompressedOutcome
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop) :=
  AyDisj
    (AySatArtifact visibleModel originalModel)
    (AyUnsatArtifact originalFormula visibleFormula finalClause)

def AyPublicSoundnessTheorem
    (originalFormula : Prop) (originalModel : Prop) :=
  AyDisj originalModel (Not originalFormula)

def AyOrderedRunManifestPath
    (prefixBefore : Prop) (candidatePrefix : Prop) : Prop :=
  AyConj prefixBefore candidatePrefix

def AyPrefixAgreement (prefix_ok : Prop) : Prop :=
  AyConj prefix_ok prefix_ok

def AyDigestDisagreement
    (baselineDigest : Prop) (candidateDigest : Prop) : Prop :=
  AyConj baselineDigest candidateDigest

def AyOutputDisagreement
    (baselineOutput : Prop) (candidateOutput : Prop) : Prop :=
  AyConj baselineOutput candidateOutput

def AyFirstDisagreement
    (earlierPrefixesAgree : Prop) (laterPrefixDisagrees : Prop) : Prop :=
  AyConj
    (AyPrefixAgreement earlierPrefixesAgree)
    laterPrefixDisagrees

def AyLocalizedMinimalWitness
    (earlierPrefixesAgree : Prop) (laterPrefixDisagrees : Prop)
    (counterexample : Prop) : Prop :=
  AyConj
    (AyFirstDisagreement earlierPrefixesAgree laterPrefixDisagrees)
    counterexample

def AyAuditReplay (accepted : Prop) : Prop :=
  AyConj accepted accepted

def AyRejectedDiagnosticReport
    (earlierPrefixesAgree : Prop) (laterPrefixDisagrees : Prop)
    (counterexample : Prop) (rejected : Prop) : Prop :=
  AyConj
    rejected
    (AyLocalizedMinimalWitness
      earlierPrefixesAgree laterPrefixDisagrees counterexample)

def AyAcceptedBaselineReport
    (baselineAccepted : Prop) (earlierPrefixesAgree : Prop) : Prop :=
  AyConj
    (AyAuditReplay baselineAccepted)
    (AyPrefixAgreement earlierPrefixesAgree)

def AyRunManifest
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop)
    (accepted : Prop) : Prop :=
  AyConj
    (AyAuditReplay accepted)
    (accepted ->
      AyCompressedOutcome
        originalFormula visibleFormula visibleModel originalModel finalClause)

theorem ay_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyConj p q := by
  intro hp
  intro hq
  intro result
  intro build_pair
  exact build_pair hp hq

theorem ay_conj_left
    (p : Prop) (q : Prop) :
    AyConj p q -> p := by
  intro both
  exact both p
    (fun (hp : p) (_hq : q) => hp)

theorem ay_disj_left
    (p : Prop) (q : Prop) :
    p -> AyDisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_disj_right
    (p : Prop) (q : Prop) :
    q -> AyDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyEquisat before after := by
  intro forward
  intro backward
  exact ay_conj_intro
    (before -> after)
    (after -> before)
    forward
    backward

theorem ay_equisat_forward
    (before : Prop) (after : Prop) :
    AyEquisat before after ->
    before -> after := by
  intro eqsat
  exact ay_conj_left (before -> after) (after -> before) eqsat

theorem ay_sat_artifact_visible
    (visibleModel : Prop) (originalModel : Prop) :
    AySatArtifact visibleModel originalModel ->
    visibleModel := by
  intro artifact
  exact ay_conj_left visibleModel
    (AyVisibleModelReconstruction visibleModel originalModel)
    artifact

theorem ay_sat_artifact_reconstruct
    (visibleModel : Prop) (originalModel : Prop) :
    AySatArtifact visibleModel originalModel ->
    AyVisibleModelReconstruction visibleModel originalModel := by
  intro artifact
  exact artifact
    (AyVisibleModelReconstruction visibleModel originalModel)
    (fun _visible reconstruct => reconstruct)

theorem ay_sat_artifact_original
    (visibleModel : Prop) (originalModel : Prop) :
    AySatArtifact visibleModel originalModel ->
    originalModel := by
  intro artifact
  exact
    (ay_sat_artifact_reconstruct visibleModel originalModel artifact)
    (ay_sat_artifact_visible visibleModel originalModel artifact)

theorem ay_unsat_artifact_clause
    (originalFormula : Prop) (visibleFormula : Prop) (finalClause : Prop) :
    AyUnsatArtifact originalFormula visibleFormula finalClause ->
    finalClause := by
  intro artifact
  exact ay_conj_left finalClause
    (AyConj
      (AyPreprocessingProof originalFormula visibleFormula)
      (AyUnsatReplayWitness visibleFormula finalClause))
    artifact

theorem ay_unsat_artifact_preprocess
    (originalFormula : Prop) (visibleFormula : Prop) (finalClause : Prop) :
    AyUnsatArtifact originalFormula visibleFormula finalClause ->
    AyPreprocessingProof originalFormula visibleFormula := by
  intro artifact
  let tail := artifact
    (AyConj
      (AyPreprocessingProof originalFormula visibleFormula)
      (AyUnsatReplayWitness visibleFormula finalClause))
    (fun _clause proof_tail => proof_tail)
  exact ay_conj_left
    (AyPreprocessingProof originalFormula visibleFormula)
    (AyUnsatReplayWitness visibleFormula finalClause)
    tail

theorem ay_unsat_artifact_replay
    (originalFormula : Prop) (visibleFormula : Prop) (finalClause : Prop) :
    AyUnsatArtifact originalFormula visibleFormula finalClause ->
    AyUnsatReplayWitness visibleFormula finalClause := by
  intro artifact
  let tail := artifact
    (AyConj
      (AyPreprocessingProof originalFormula visibleFormula)
      (AyUnsatReplayWitness visibleFormula finalClause))
    (fun _clause proof_tail => proof_tail)
  exact tail
    (AyUnsatReplayWitness visibleFormula finalClause)
    (fun _preprocess replay => replay)

theorem ay_unsat_artifact_original_unsat
    (originalFormula : Prop) (visibleFormula : Prop) (finalClause : Prop) :
    AyUnsatArtifact originalFormula visibleFormula finalClause ->
    Not originalFormula := by
  intro artifact
  intro original
  exact
    (ay_unsat_artifact_replay originalFormula visibleFormula finalClause
      artifact)
    (ay_unsat_artifact_clause originalFormula visibleFormula finalClause
      artifact)
    ((ay_unsat_artifact_preprocess
      originalFormula visibleFormula finalClause artifact) original)

theorem ay_outcome_public_soundness
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop) :
    AyCompressedOutcome
      originalFormula visibleFormula visibleModel originalModel finalClause ->
    AyPublicSoundnessTheorem originalFormula originalModel := by
  intro outcome
  exact outcome
    (AyPublicSoundnessTheorem originalFormula originalModel)
    (fun sat =>
      ay_disj_left originalModel (Not originalFormula)
        (ay_sat_artifact_original visibleModel originalModel sat))
    (fun unsat =>
      ay_disj_right originalModel (Not originalFormula)
        (ay_unsat_artifact_original_unsat
          originalFormula visibleFormula finalClause unsat))

theorem ay_manifest_public_soundness
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop)
    (accepted : Prop) :
    AyRunManifest
      originalFormula visibleFormula visibleModel originalModel finalClause
      accepted ->
    accepted ->
    AyPublicSoundnessTheorem originalFormula originalModel := by
  intro manifest
  intro accepted_h
  let replay := manifest
    (accepted ->
      AyCompressedOutcome
        originalFormula visibleFormula visibleModel originalModel finalClause)
    (fun _accepted replay => replay)
  exact ay_outcome_public_soundness
    originalFormula visibleFormula visibleModel originalModel finalClause
    (replay accepted_h)

theorem ay_prefix_path_left
    (prefixBefore : Prop) (candidatePrefix : Prop) :
    AyOrderedRunManifestPath prefixBefore candidatePrefix ->
    AyPrefixAgreement prefixBefore := by
  intro path
  let prefix_before := ay_conj_left prefixBefore candidatePrefix path
  exact ay_conj_intro prefixBefore prefixBefore prefix_before prefix_before

theorem ay_prefix_monotonicity
    (earlierPrefix : Prop) (laterPrefix : Prop) :
    AyEquisat earlierPrefix laterPrefix ->
    AyPrefixAgreement earlierPrefix ->
    AyPrefixAgreement laterPrefix := by
  intro agreement_transport
  intro earlier_agree
  let earlier := ay_conj_left earlierPrefix earlierPrefix earlier_agree
  let later := ay_equisat_forward
    earlierPrefix laterPrefix agreement_transport earlier
  exact ay_conj_intro laterPrefix laterPrefix later later

theorem ay_first_disagreement_intro
    (earlierPrefixesAgree : Prop) (laterPrefixDisagrees : Prop) :
    AyPrefixAgreement earlierPrefixesAgree ->
    laterPrefixDisagrees ->
    AyFirstDisagreement earlierPrefixesAgree laterPrefixDisagrees := by
  intro earlier
  intro later
  exact ay_conj_intro
    (AyPrefixAgreement earlierPrefixesAgree)
    laterPrefixDisagrees
    earlier
    later

theorem ay_minimal_witness_from_first_bad
    (earlierPrefixesAgree : Prop) (laterPrefixDisagrees : Prop)
    (counterexample : Prop) :
    AyPrefixAgreement earlierPrefixesAgree ->
    laterPrefixDisagrees ->
    counterexample ->
    AyLocalizedMinimalWitness
      earlierPrefixesAgree laterPrefixDisagrees counterexample := by
  intro earlier
  intro later
  intro witness
  exact ay_conj_intro
    (AyFirstDisagreement earlierPrefixesAgree laterPrefixDisagrees)
    counterexample
    (ay_first_disagreement_intro
      earlierPrefixesAgree laterPrefixDisagrees earlier later)
    witness

theorem ay_bisection_search_correctness
    (earlierPrefixesAgree : Prop) (laterPrefixDisagrees : Prop)
    (counterexample : Prop) :
    AyFirstDisagreement earlierPrefixesAgree laterPrefixDisagrees ->
    counterexample ->
    AyLocalizedMinimalWitness
      earlierPrefixesAgree laterPrefixDisagrees counterexample := by
  intro first_bad
  intro witness
  exact ay_conj_intro
    (AyFirstDisagreement earlierPrefixesAgree laterPrefixDisagrees)
    counterexample
    first_bad
    witness

theorem ay_first_bad_isolation
    (earlierPrefixesAgree : Prop) (laterPrefixDisagrees : Prop)
    (counterexample : Prop) :
    AyRejectedDiagnosticReport
      earlierPrefixesAgree laterPrefixDisagrees counterexample
      laterPrefixDisagrees ->
    AyLocalizedMinimalWitness
      earlierPrefixesAgree laterPrefixDisagrees counterexample := by
  intro report
  exact report
    (AyLocalizedMinimalWitness
      earlierPrefixesAgree laterPrefixDisagrees counterexample)
    (fun _rejected minimal => minimal)

theorem ay_rejected_report_minimality
    (earlierPrefixesAgree : Prop) (laterPrefixDisagrees : Prop)
    (counterexample : Prop) (rejected : Prop) :
    AyRejectedDiagnosticReport
      earlierPrefixesAgree laterPrefixDisagrees counterexample rejected ->
    AyLocalizedMinimalWitness
      earlierPrefixesAgree laterPrefixDisagrees counterexample := by
  intro report
  exact report
    (AyLocalizedMinimalWitness
      earlierPrefixesAgree laterPrefixDisagrees counterexample)
    (fun _rejected minimal => minimal)

theorem ay_accepted_baseline_soundness
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop)
    (accepted : Prop) (earlierPrefixesAgree : Prop) :
    AyAcceptedBaselineReport accepted earlierPrefixesAgree ->
    AyRunManifest
      originalFormula visibleFormula visibleModel originalModel finalClause
      accepted ->
    AyPublicSoundnessTheorem originalFormula originalModel := by
  intro accepted_report
  intro manifest
  exact ay_manifest_public_soundness
    originalFormula visibleFormula visibleModel originalModel finalClause
    accepted
    manifest
    (ay_conj_left accepted accepted
      (ay_conj_left
        (AyAuditReplay accepted)
        (AyPrefixAgreement earlierPrefixesAgree)
        accepted_report))

theorem ay_minimality_diagnostic_only
    (earlierPrefixesAgree : Prop) (laterPrefixDisagrees : Prop)
    (counterexample : Prop) (semanticClaim : Prop) :
    AyLocalizedMinimalWitness
      earlierPrefixesAgree laterPrefixDisagrees counterexample ->
    semanticClaim ->
    semanticClaim := by
  intro _minimal
  intro claim
  exact claim

theorem ay_minimality_cannot_destroy_public_soundness
    (originalFormula : Prop) (originalModel : Prop)
    (earlierPrefixesAgree : Prop) (laterPrefixDisagrees : Prop)
    (counterexample : Prop) :
    AyLocalizedMinimalWitness
      earlierPrefixesAgree laterPrefixDisagrees counterexample ->
    AyPublicSoundnessTheorem originalFormula originalModel ->
    AyPublicSoundnessTheorem originalFormula originalModel := by
  intro _minimal
  intro soundness
  exact soundness

theorem ay_public_report_no_claim_behavior
    (earlierPrefixesAgree : Prop) (laterPrefixDisagrees : Prop)
    (counterexample : Prop) (rejected : Prop) :
    AyRejectedDiagnosticReport
      earlierPrefixesAgree laterPrefixDisagrees counterexample rejected ->
    AyConj
      (AyLocalizedMinimalWitness
        earlierPrefixesAgree laterPrefixDisagrees counterexample)
      (AyRejectedDiagnosticReport
        earlierPrefixesAgree laterPrefixDisagrees counterexample rejected) := by
  intro report
  exact ay_conj_intro
    (AyLocalizedMinimalWitness
      earlierPrefixesAgree laterPrefixDisagrees counterexample)
    (AyRejectedDiagnosticReport
      earlierPrefixesAgree laterPrefixDisagrees counterexample rejected)
    (ay_rejected_report_minimality
      earlierPrefixesAgree laterPrefixDisagrees counterexample rejected report)
    report
