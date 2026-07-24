-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Empty-clause uniqueness/reachability guard soundness for ay sequential-main
-- SAT-COMP UNSAT proof publication. Propositions model proof artifact
-- digests, normalized proof digests, empty-clause line digests, reachable
-- empty-clause witnesses, duplicate-empty-clause ledgers, proof line maps,
-- antecedent/reason contexts, checker transcripts, archive/build evidence,
-- fallback no-claim paths, audit transcripts, and fail-closed recompute
-- diagnostics.

def ay_ecug_conj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def ay_ecug_disj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def ay_ecug_map (source : Prop) (target : Prop) :=
  source -> target

def ay_ecug_accepted_evidence
    (proofArtifactDigest : Prop) (normalizedProofDigest : Prop)
    (emptyClauseLineDigest : Prop) (emptyClauseReachabilityWitness : Prop)
    (duplicateEmptyClauseLedger : Prop) (proofLineMapDigest : Prop)
    (antecedentReasonContextDigest : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (archiveManifest : Prop)
    (archiveAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (emptyClauseIdentityPreserved : Prop)
    (originalUnsat : Prop) :=
  forall result : Prop,
    (proofArtifactDigest ->
      normalizedProofDigest ->
      emptyClauseLineDigest ->
      emptyClauseReachabilityWitness ->
      duplicateEmptyClauseLedger ->
      proofLineMapDigest ->
      antecedentReasonContextDigest ->
      checkerTranscript ->
      checkerAccepted ->
      archiveManifest ->
      archiveAccepted ->
      solverBuildEvidence ->
      buildAccepted ->
      fallbackNoClaim ->
      auditTranscript ->
      emptyClauseIdentityPreserved ->
      originalUnsat ->
      result) ->
    result

def ay_ecug_checker_publication_path
    (emptyClauseLineDigest : Prop) (emptyClauseReachabilityWitness : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (originalUnsat : Prop) :=
  ay_ecug_conj
    (ay_ecug_map emptyClauseLineDigest emptyClauseReachabilityWitness)
    (ay_ecug_conj
      (ay_ecug_map emptyClauseReachabilityWitness checkerTranscript)
      (ay_ecug_conj
        (ay_ecug_map checkerTranscript checkerAccepted)
        (ay_ecug_map checkerAccepted originalUnsat)))

def ay_ecug_empty_clause_identity
    (proofArtifactDigest : Prop) (normalizedProofDigest : Prop)
    (duplicateEmptyClauseLedger : Prop) (proofLineMapDigest : Prop)
    (antecedentReasonContextDigest : Prop)
    (emptyClauseIdentityPreserved : Prop) :=
  ay_ecug_conj
    (ay_ecug_map proofArtifactDigest normalizedProofDigest)
    (ay_ecug_conj
      (ay_ecug_map normalizedProofDigest duplicateEmptyClauseLedger)
      (ay_ecug_conj
        (ay_ecug_map duplicateEmptyClauseLedger proofLineMapDigest)
        (ay_ecug_conj
          (ay_ecug_map proofLineMapDigest antecedentReasonContextDigest)
          (ay_ecug_map antecedentReasonContextDigest
            emptyClauseIdentityPreserved))))

def ay_ecug_publication
    (proofArtifactDigest : Prop) (normalizedProofDigest : Prop)
    (emptyClauseLineDigest : Prop) (emptyClauseReachabilityWitness : Prop)
    (duplicateEmptyClauseLedger : Prop) (proofLineMapDigest : Prop)
    (antecedentReasonContextDigest : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (archiveManifest : Prop)
    (archiveAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (emptyClauseIdentityPreserved : Prop)
    (originalUnsat : Prop) :=
  ay_ecug_conj
    (ay_ecug_accepted_evidence proofArtifactDigest normalizedProofDigest
      emptyClauseLineDigest emptyClauseReachabilityWitness
      duplicateEmptyClauseLedger proofLineMapDigest antecedentReasonContextDigest
      checkerTranscript checkerAccepted archiveManifest archiveAccepted
      solverBuildEvidence buildAccepted fallbackNoClaim auditTranscript
      emptyClauseIdentityPreserved originalUnsat)
    originalUnsat

def ay_ecug_failure_reason
    (proofMismatch : Prop) (normalizedMismatch : Prop)
    (emptyLineMismatch : Prop) (duplicateMismatch : Prop)
    (lineMapMismatch : Prop) (antecedentMismatch : Prop)
    (checkerMismatch : Prop) (archiveMismatch : Prop)
    (buildMismatch : Prop) (auditMismatch : Prop) :=
  forall result : Prop,
    (proofMismatch -> result) ->
    (normalizedMismatch -> result) ->
    (emptyLineMismatch -> result) ->
    (duplicateMismatch -> result) ->
    (lineMapMismatch -> result) ->
    (antecedentMismatch -> result) ->
    (checkerMismatch -> result) ->
    (archiveMismatch -> result) ->
    (buildMismatch -> result) ->
    (auditMismatch -> result) ->
    result

def ay_ecug_bad_guard
    (proofMismatch : Prop) (normalizedMismatch : Prop)
    (emptyLineMismatch : Prop) (duplicateMismatch : Prop)
    (lineMapMismatch : Prop) (antecedentMismatch : Prop)
    (checkerMismatch : Prop) (archiveMismatch : Prop)
    (buildMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :=
  ay_ecug_conj
    (ay_ecug_conj noClaim recompute)
    (ay_ecug_failure_reason proofMismatch normalizedMismatch
      emptyLineMismatch duplicateMismatch lineMapMismatch antecedentMismatch
      checkerMismatch archiveMismatch buildMismatch auditMismatch)

def ay_ecug_public_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :=
  ay_ecug_disj noClaim (ay_ecug_disj originalUnsat publicSat)

theorem ay_ecug_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> ay_ecug_conj p q := by
  intro hp hq result build
  exact build hp hq

theorem ay_ecug_disj_left
    (p : Prop) (q : Prop) :
    p -> ay_ecug_disj p q := by
  intro hp result left_to_result _right_to_result
  exact left_to_result hp

theorem ay_ecug_disj_right
    (p : Prop) (q : Prop) :
    q -> ay_ecug_disj p q := by
  intro hq result _left_to_result right_to_result
  exact right_to_result hq

theorem ay_ecug_build_accepted_evidence
    (proofArtifactDigest : Prop) (normalizedProofDigest : Prop)
    (emptyClauseLineDigest : Prop) (emptyClauseReachabilityWitness : Prop)
    (duplicateEmptyClauseLedger : Prop) (proofLineMapDigest : Prop)
    (antecedentReasonContextDigest : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (archiveManifest : Prop)
    (archiveAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (emptyClauseIdentityPreserved : Prop)
    (originalUnsat : Prop) :
    proofArtifactDigest ->
    normalizedProofDigest ->
    emptyClauseLineDigest ->
    emptyClauseReachabilityWitness ->
    duplicateEmptyClauseLedger ->
    proofLineMapDigest ->
    antecedentReasonContextDigest ->
    checkerTranscript ->
    checkerAccepted ->
    archiveManifest ->
    archiveAccepted ->
    solverBuildEvidence ->
    buildAccepted ->
    fallbackNoClaim ->
    auditTranscript ->
    emptyClauseIdentityPreserved ->
    originalUnsat ->
    ay_ecug_accepted_evidence proofArtifactDigest normalizedProofDigest
      emptyClauseLineDigest emptyClauseReachabilityWitness
      duplicateEmptyClauseLedger proofLineMapDigest antecedentReasonContextDigest
      checkerTranscript checkerAccepted archiveManifest archiveAccepted
      solverBuildEvidence buildAccepted fallbackNoClaim auditTranscript
      emptyClauseIdentityPreserved originalUnsat := by
  intro hProof hNormalized hEmptyLine hReachability hDuplicate hLineMap
  intro hAntecedent hTranscript hChecker hArchive hArchiveAccepted hBuild
  intro hBuildAccepted hFallback hAudit hIdentity hOriginal result publish
  exact publish hProof hNormalized hEmptyLine hReachability hDuplicate
    hLineMap hAntecedent hTranscript hChecker hArchive hArchiveAccepted
    hBuild hBuildAccepted hFallback hAudit hIdentity hOriginal

theorem ay_ecug_unsat_requires_checker_replayed_reachable_empty_clause
    (emptyClauseLineDigest : Prop) (emptyClauseReachabilityWitness : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (originalUnsat : Prop) :
    ay_ecug_checker_publication_path emptyClauseLineDigest
      emptyClauseReachabilityWitness checkerTranscript checkerAccepted
      originalUnsat ->
    emptyClauseLineDigest ->
    originalUnsat := by
  intro path hEmptyLine
  exact path originalUnsat
    (fun empty_to_reachability rest =>
      rest originalUnsat
        (fun reachability_to_transcript rest2 =>
          rest2 originalUnsat
            (fun transcript_to_checker checker_to_original =>
              checker_to_original
                (transcript_to_checker
                  (reachability_to_transcript
                    (empty_to_reachability hEmptyLine)))))))

theorem ay_ecug_duplicate_markers_require_identity_context
    (proofArtifactDigest : Prop) (normalizedProofDigest : Prop)
    (duplicateEmptyClauseLedger : Prop) (proofLineMapDigest : Prop)
    (antecedentReasonContextDigest : Prop)
    (emptyClauseIdentityPreserved : Prop) :
    ay_ecug_empty_clause_identity proofArtifactDigest normalizedProofDigest
      duplicateEmptyClauseLedger proofLineMapDigest antecedentReasonContextDigest
      emptyClauseIdentityPreserved ->
    proofArtifactDigest ->
    emptyClauseIdentityPreserved := by
  intro identity hProof
  exact identity emptyClauseIdentityPreserved
    (fun proof_to_normalized rest =>
      rest emptyClauseIdentityPreserved
        (fun normalized_to_duplicate rest2 =>
          rest2 emptyClauseIdentityPreserved
            (fun duplicate_to_line_map rest3 =>
              rest3 emptyClauseIdentityPreserved
                (fun line_map_to_antecedent antecedent_to_identity =>
                  antecedent_to_identity
                    (line_map_to_antecedent
                      (duplicate_to_line_map
                        (normalized_to_duplicate
                          (proof_to_normalized hProof)))))))))

theorem ay_ecug_reachability_available
    (proofArtifactDigest : Prop) (normalizedProofDigest : Prop)
    (emptyClauseLineDigest : Prop) (emptyClauseReachabilityWitness : Prop)
    (duplicateEmptyClauseLedger : Prop) (proofLineMapDigest : Prop)
    (antecedentReasonContextDigest : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (archiveManifest : Prop)
    (archiveAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (emptyClauseIdentityPreserved : Prop)
    (originalUnsat : Prop) :
    ay_ecug_accepted_evidence proofArtifactDigest normalizedProofDigest
      emptyClauseLineDigest emptyClauseReachabilityWitness
      duplicateEmptyClauseLedger proofLineMapDigest antecedentReasonContextDigest
      checkerTranscript checkerAccepted archiveManifest archiveAccepted
      solverBuildEvidence buildAccepted fallbackNoClaim auditTranscript
      emptyClauseIdentityPreserved originalUnsat ->
    emptyClauseReachabilityWitness := by
  intro accepted
  exact accepted emptyClauseReachabilityWitness
    (fun _hProof _hNormalized _hEmptyLine hReachability _hDuplicate
      _hLineMap _hAntecedent _hTranscript _hChecker _hArchive
      _hArchiveAccepted _hBuild _hBuildAccepted _hFallback _hAudit
      _hIdentity _hOriginal =>
      hReachability)

theorem ay_ecug_identity_available
    (proofArtifactDigest : Prop) (normalizedProofDigest : Prop)
    (emptyClauseLineDigest : Prop) (emptyClauseReachabilityWitness : Prop)
    (duplicateEmptyClauseLedger : Prop) (proofLineMapDigest : Prop)
    (antecedentReasonContextDigest : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (archiveManifest : Prop)
    (archiveAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (emptyClauseIdentityPreserved : Prop)
    (originalUnsat : Prop) :
    ay_ecug_accepted_evidence proofArtifactDigest normalizedProofDigest
      emptyClauseLineDigest emptyClauseReachabilityWitness
      duplicateEmptyClauseLedger proofLineMapDigest antecedentReasonContextDigest
      checkerTranscript checkerAccepted archiveManifest archiveAccepted
      solverBuildEvidence buildAccepted fallbackNoClaim auditTranscript
      emptyClauseIdentityPreserved originalUnsat ->
    emptyClauseIdentityPreserved := by
  intro accepted
  exact accepted emptyClauseIdentityPreserved
    (fun _hProof _hNormalized _hEmptyLine _hReachability _hDuplicate
      _hLineMap _hAntecedent _hTranscript _hChecker _hArchive
      _hArchiveAccepted _hBuild _hBuildAccepted _hFallback _hAudit hIdentity
      _hOriginal =>
      hIdentity)

theorem ay_ecug_publication_sound
    (proofArtifactDigest : Prop) (normalizedProofDigest : Prop)
    (emptyClauseLineDigest : Prop) (emptyClauseReachabilityWitness : Prop)
    (duplicateEmptyClauseLedger : Prop) (proofLineMapDigest : Prop)
    (antecedentReasonContextDigest : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (archiveManifest : Prop)
    (archiveAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (emptyClauseIdentityPreserved : Prop)
    (originalUnsat : Prop) :
    ay_ecug_publication proofArtifactDigest normalizedProofDigest
      emptyClauseLineDigest emptyClauseReachabilityWitness
      duplicateEmptyClauseLedger proofLineMapDigest antecedentReasonContextDigest
      checkerTranscript checkerAccepted archiveManifest archiveAccepted
      solverBuildEvidence buildAccepted fallbackNoClaim auditTranscript
      emptyClauseIdentityPreserved originalUnsat ->
    originalUnsat := by
  intro publication
  exact publication originalUnsat
    (fun _accepted hOriginal => hOriginal)

theorem ay_ecug_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :
    originalUnsat ->
    ay_ecug_public_report noClaim originalUnsat publicSat := by
  intro hUnsat
  exact ay_ecug_disj_right noClaim (ay_ecug_disj originalUnsat publicSat)
    (ay_ecug_disj_left originalUnsat publicSat hUnsat)

theorem ay_ecug_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :
    noClaim ->
    ay_ecug_public_report noClaim originalUnsat publicSat := by
  intro hNoClaim
  exact ay_ecug_disj_left noClaim
    (ay_ecug_disj originalUnsat publicSat) hNoClaim

theorem ay_ecug_bad_no_claim
    (proofMismatch : Prop) (normalizedMismatch : Prop)
    (emptyLineMismatch : Prop) (duplicateMismatch : Prop)
    (lineMapMismatch : Prop) (antecedentMismatch : Prop)
    (checkerMismatch : Prop) (archiveMismatch : Prop)
    (buildMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_ecug_bad_guard proofMismatch normalizedMismatch emptyLineMismatch
      duplicateMismatch lineMapMismatch antecedentMismatch checkerMismatch
      archiveMismatch buildMismatch auditMismatch noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun no_claim_and_recompute _reason =>
      no_claim_and_recompute noClaim
        (fun hNoClaim _hRecompute => hNoClaim))

theorem ay_ecug_bad_recompute
    (proofMismatch : Prop) (normalizedMismatch : Prop)
    (emptyLineMismatch : Prop) (duplicateMismatch : Prop)
    (lineMapMismatch : Prop) (antecedentMismatch : Prop)
    (checkerMismatch : Prop) (archiveMismatch : Prop)
    (buildMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_ecug_bad_guard proofMismatch normalizedMismatch emptyLineMismatch
      duplicateMismatch lineMapMismatch antecedentMismatch checkerMismatch
      archiveMismatch buildMismatch auditMismatch noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun no_claim_and_recompute _reason =>
      no_claim_and_recompute recompute
        (fun _hNoClaim hRecompute => hRecompute))

theorem ay_ecug_failed_guard_cannot_bless_unsat
    (proofMismatch : Prop) (normalizedMismatch : Prop)
    (emptyLineMismatch : Prop) (duplicateMismatch : Prop)
    (lineMapMismatch : Prop) (antecedentMismatch : Prop)
    (checkerMismatch : Prop) (archiveMismatch : Prop)
    (buildMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) (publicUnsat : Prop) :
    ay_ecug_bad_guard proofMismatch normalizedMismatch emptyLineMismatch
      duplicateMismatch lineMapMismatch antecedentMismatch checkerMismatch
      archiveMismatch buildMismatch auditMismatch noClaim recompute ->
    ay_ecug_map noClaim (publicUnsat -> recompute) := by
  intro bad _hNoClaim _hPublicUnsat
  exact ay_ecug_bad_recompute proofMismatch normalizedMismatch
    emptyLineMismatch duplicateMismatch lineMapMismatch antecedentMismatch
    checkerMismatch archiveMismatch buildMismatch auditMismatch noClaim
    recompute bad

theorem ay_ecug_duplicate_or_malformed_marker_cannot_publish_without_guard
    (duplicateMismatch : Prop) (emptyLineMismatch : Prop)
    (noClaim : Prop) :
    ay_ecug_disj duplicateMismatch emptyLineMismatch ->
    (duplicateMismatch -> noClaim) ->
    (emptyLineMismatch -> noClaim) ->
    noClaim := by
  intro markerProblem duplicate_to_no_claim empty_to_no_claim
  exact markerProblem noClaim duplicate_to_no_claim empty_to_no_claim

theorem ay_ecug_failure_forces_no_claim
    (proofMismatch : Prop) (normalizedMismatch : Prop)
    (emptyLineMismatch : Prop) (duplicateMismatch : Prop)
    (lineMapMismatch : Prop) (antecedentMismatch : Prop)
    (checkerMismatch : Prop) (archiveMismatch : Prop)
    (buildMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) :
    ay_ecug_failure_reason proofMismatch normalizedMismatch emptyLineMismatch
      duplicateMismatch lineMapMismatch antecedentMismatch checkerMismatch
      archiveMismatch buildMismatch auditMismatch ->
    (proofMismatch -> noClaim) ->
    (normalizedMismatch -> noClaim) ->
    (emptyLineMismatch -> noClaim) ->
    (duplicateMismatch -> noClaim) ->
    (lineMapMismatch -> noClaim) ->
    (antecedentMismatch -> noClaim) ->
    (checkerMismatch -> noClaim) ->
    (archiveMismatch -> noClaim) ->
    (buildMismatch -> noClaim) ->
    (auditMismatch -> noClaim) ->
    noClaim := by
  intro reason proof_to_no_claim normalized_to_no_claim empty_to_no_claim
  intro duplicate_to_no_claim line_map_to_no_claim antecedent_to_no_claim
  intro checker_to_no_claim archive_to_no_claim build_to_no_claim
  intro audit_to_no_claim
  exact reason noClaim proof_to_no_claim normalized_to_no_claim
    empty_to_no_claim duplicate_to_no_claim line_map_to_no_claim
    antecedent_to_no_claim checker_to_no_claim archive_to_no_claim
    build_to_no_claim audit_to_no_claim

theorem ay_ecug_proof_mismatch_forces_no_claim
    (proofMismatch noClaim : Prop) :
    proofMismatch ->
    (proofMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_ecug_normalized_mismatch_forces_no_claim
    (normalizedMismatch noClaim : Prop) :
    normalizedMismatch ->
    (normalizedMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_ecug_empty_line_mismatch_forces_no_claim
    (emptyLineMismatch noClaim : Prop) :
    emptyLineMismatch ->
    (emptyLineMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_ecug_duplicate_mismatch_forces_no_claim
    (duplicateMismatch noClaim : Prop) :
    duplicateMismatch ->
    (duplicateMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_ecug_line_map_mismatch_forces_no_claim
    (lineMapMismatch noClaim : Prop) :
    lineMapMismatch ->
    (lineMapMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_ecug_antecedent_mismatch_forces_no_claim
    (antecedentMismatch noClaim : Prop) :
    antecedentMismatch ->
    (antecedentMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_ecug_checker_mismatch_forces_no_claim
    (checkerMismatch noClaim : Prop) :
    checkerMismatch ->
    (checkerMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_ecug_archive_mismatch_forces_no_claim
    (archiveMismatch noClaim : Prop) :
    archiveMismatch ->
    (archiveMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_ecug_build_mismatch_forces_no_claim
    (buildMismatch noClaim : Prop) :
    buildMismatch ->
    (buildMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_ecug_audit_mismatch_forces_no_claim
    (auditMismatch noClaim : Prop) :
    auditMismatch ->
    (auditMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch
