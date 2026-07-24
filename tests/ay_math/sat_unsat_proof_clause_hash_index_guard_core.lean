-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Clause-hash index guard soundness for ay sequential-main SAT-COMP UNSAT
-- proof checking. Propositions model formula fingerprints, proof-line
-- digests, clause-hash function versions, hash tables, collision resolution,
-- antecedent lookup transcripts, live-clause context, unit-propagation/checker
-- replay transcripts, empty-clause reachability, archive/build evidence,
-- fallback no-claim paths, audit transcripts, and fail-closed recompute
-- diagnostics.

def ay_chig_conj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def ay_chig_disj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def ay_chig_map (source : Prop) (target : Prop) :=
  source -> target

def ay_chig_accepted_evidence
    (originalFormulaFingerprint : Prop) (proofLineDigest : Prop)
    (clauseHashFunctionVersionDigest : Prop) (clauseHashTableDigest : Prop)
    (collisionResolutionWitness : Prop) (antecedentLookupTranscript : Prop)
    (liveClauseContextDigest : Prop) (checkerReplayTranscript : Prop)
    (checkerAccepted : Prop) (emptyClauseReachabilityWitness : Prop)
    (archiveManifest : Prop) (archiveAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (lookupContextResolved : Prop) (originalUnsat : Prop) :=
  forall result : Prop,
    (originalFormulaFingerprint ->
      proofLineDigest ->
      clauseHashFunctionVersionDigest ->
      clauseHashTableDigest ->
      collisionResolutionWitness ->
      antecedentLookupTranscript ->
      liveClauseContextDigest ->
      checkerReplayTranscript ->
      checkerAccepted ->
      emptyClauseReachabilityWitness ->
      archiveManifest ->
      archiveAccepted ->
      solverBuildEvidence ->
      buildAccepted ->
      fallbackNoClaim ->
      auditTranscript ->
      lookupContextResolved ->
      originalUnsat ->
      result) ->
    result

def ay_chig_checker_publication_path
    (clauseHashTableDigest : Prop) (checkerReplayTranscript : Prop)
    (checkerAccepted : Prop) (emptyClauseReachabilityWitness : Prop)
    (originalUnsat : Prop) :=
  ay_chig_conj
    (ay_chig_map clauseHashTableDigest checkerReplayTranscript)
    (ay_chig_conj
      (ay_chig_map checkerReplayTranscript checkerAccepted)
      (ay_chig_conj
        (ay_chig_map checkerAccepted emptyClauseReachabilityWitness)
        (ay_chig_map emptyClauseReachabilityWitness originalUnsat)))

def ay_chig_lookup_context_resolution
    (clauseHashFunctionVersionDigest : Prop) (clauseHashTableDigest : Prop)
    (collisionResolutionWitness : Prop) (antecedentLookupTranscript : Prop)
    (liveClauseContextDigest : Prop) (lookupContextResolved : Prop) :=
  ay_chig_conj
    (ay_chig_map clauseHashFunctionVersionDigest clauseHashTableDigest)
    (ay_chig_conj
      (ay_chig_map clauseHashTableDigest collisionResolutionWitness)
      (ay_chig_conj
        (ay_chig_map collisionResolutionWitness antecedentLookupTranscript)
        (ay_chig_conj
          (ay_chig_map antecedentLookupTranscript liveClauseContextDigest)
          (ay_chig_map liveClauseContextDigest lookupContextResolved))))

def ay_chig_publication
    (originalFormulaFingerprint : Prop) (proofLineDigest : Prop)
    (clauseHashFunctionVersionDigest : Prop) (clauseHashTableDigest : Prop)
    (collisionResolutionWitness : Prop) (antecedentLookupTranscript : Prop)
    (liveClauseContextDigest : Prop) (checkerReplayTranscript : Prop)
    (checkerAccepted : Prop) (emptyClauseReachabilityWitness : Prop)
    (archiveManifest : Prop) (archiveAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (lookupContextResolved : Prop) (originalUnsat : Prop) :=
  ay_chig_conj
    (ay_chig_accepted_evidence originalFormulaFingerprint proofLineDigest
      clauseHashFunctionVersionDigest clauseHashTableDigest
      collisionResolutionWitness antecedentLookupTranscript
      liveClauseContextDigest checkerReplayTranscript checkerAccepted
      emptyClauseReachabilityWitness archiveManifest archiveAccepted
      solverBuildEvidence buildAccepted fallbackNoClaim auditTranscript
      lookupContextResolved originalUnsat)
    originalUnsat

def ay_chig_failure_reason
    (hashMismatch : Prop) (tableMismatch : Prop)
    (collisionMismatch : Prop) (lookupMismatch : Prop)
    (liveContextMismatch : Prop) (replayMismatch : Prop)
    (reachabilityMismatch : Prop) (archiveMismatch : Prop)
    (buildMismatch : Prop) (auditMismatch : Prop) :=
  forall result : Prop,
    (hashMismatch -> result) ->
    (tableMismatch -> result) ->
    (collisionMismatch -> result) ->
    (lookupMismatch -> result) ->
    (liveContextMismatch -> result) ->
    (replayMismatch -> result) ->
    (reachabilityMismatch -> result) ->
    (archiveMismatch -> result) ->
    (buildMismatch -> result) ->
    (auditMismatch -> result) ->
    result

def ay_chig_bad_guard
    (hashMismatch : Prop) (tableMismatch : Prop)
    (collisionMismatch : Prop) (lookupMismatch : Prop)
    (liveContextMismatch : Prop) (replayMismatch : Prop)
    (reachabilityMismatch : Prop) (archiveMismatch : Prop)
    (buildMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :=
  ay_chig_conj
    (ay_chig_conj noClaim recompute)
    (ay_chig_failure_reason hashMismatch tableMismatch collisionMismatch
      lookupMismatch liveContextMismatch replayMismatch reachabilityMismatch
      archiveMismatch buildMismatch auditMismatch)

def ay_chig_public_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :=
  ay_chig_disj noClaim (ay_chig_disj originalUnsat publicSat)

theorem ay_chig_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> ay_chig_conj p q := by
  intro hp hq result build
  exact build hp hq

theorem ay_chig_disj_left
    (p : Prop) (q : Prop) :
    p -> ay_chig_disj p q := by
  intro hp result left_to_result _right_to_result
  exact left_to_result hp

theorem ay_chig_disj_right
    (p : Prop) (q : Prop) :
    q -> ay_chig_disj p q := by
  intro hq result _left_to_result right_to_result
  exact right_to_result hq

theorem ay_chig_build_accepted_evidence
    (originalFormulaFingerprint : Prop) (proofLineDigest : Prop)
    (clauseHashFunctionVersionDigest : Prop) (clauseHashTableDigest : Prop)
    (collisionResolutionWitness : Prop) (antecedentLookupTranscript : Prop)
    (liveClauseContextDigest : Prop) (checkerReplayTranscript : Prop)
    (checkerAccepted : Prop) (emptyClauseReachabilityWitness : Prop)
    (archiveManifest : Prop) (archiveAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (lookupContextResolved : Prop) (originalUnsat : Prop) :
    originalFormulaFingerprint ->
    proofLineDigest ->
    clauseHashFunctionVersionDigest ->
    clauseHashTableDigest ->
    collisionResolutionWitness ->
    antecedentLookupTranscript ->
    liveClauseContextDigest ->
    checkerReplayTranscript ->
    checkerAccepted ->
    emptyClauseReachabilityWitness ->
    archiveManifest ->
    archiveAccepted ->
    solverBuildEvidence ->
    buildAccepted ->
    fallbackNoClaim ->
    auditTranscript ->
    lookupContextResolved ->
    originalUnsat ->
    ay_chig_accepted_evidence originalFormulaFingerprint proofLineDigest
      clauseHashFunctionVersionDigest clauseHashTableDigest
      collisionResolutionWitness antecedentLookupTranscript
      liveClauseContextDigest checkerReplayTranscript checkerAccepted
      emptyClauseReachabilityWitness archiveManifest archiveAccepted
      solverBuildEvidence buildAccepted fallbackNoClaim auditTranscript
      lookupContextResolved originalUnsat := by
  intro hFingerprint hLine hHash hTable hCollision hLookup hLive hReplay
  intro hChecker hReachability hArchive hArchiveAccepted hBuild
  intro hBuildAccepted hFallback hAudit hResolved hOriginal result publish
  exact publish hFingerprint hLine hHash hTable hCollision hLookup hLive
    hReplay hChecker hReachability hArchive hArchiveAccepted hBuild
    hBuildAccepted hFallback hAudit hResolved hOriginal

theorem ay_chig_hash_index_supports_unsat_only_through_replay
    (clauseHashTableDigest : Prop) (checkerReplayTranscript : Prop)
    (checkerAccepted : Prop) (emptyClauseReachabilityWitness : Prop)
    (originalUnsat : Prop) :
    ay_chig_checker_publication_path clauseHashTableDigest
      checkerReplayTranscript checkerAccepted emptyClauseReachabilityWitness
      originalUnsat ->
    clauseHashTableDigest ->
    originalUnsat := by
  intro path hTable
  exact path originalUnsat
    (fun table_to_replay rest =>
      rest originalUnsat
        (fun replay_to_checker rest2 =>
          rest2 originalUnsat
            (fun checker_to_reachability reachability_to_original =>
              reachability_to_original
                (checker_to_reachability
                  (replay_to_checker
                    (table_to_replay hTable)))))))

theorem ay_chig_collisions_and_lookups_resolve_live_context
    (clauseHashFunctionVersionDigest : Prop) (clauseHashTableDigest : Prop)
    (collisionResolutionWitness : Prop) (antecedentLookupTranscript : Prop)
    (liveClauseContextDigest : Prop) (lookupContextResolved : Prop) :
    ay_chig_lookup_context_resolution clauseHashFunctionVersionDigest
      clauseHashTableDigest collisionResolutionWitness
      antecedentLookupTranscript liveClauseContextDigest lookupContextResolved ->
    clauseHashFunctionVersionDigest ->
    lookupContextResolved := by
  intro resolution hHash
  exact resolution lookupContextResolved
    (fun hash_to_table rest =>
      rest lookupContextResolved
        (fun table_to_collision rest2 =>
          rest2 lookupContextResolved
            (fun collision_to_lookup rest3 =>
              rest3 lookupContextResolved
                (fun lookup_to_live live_to_resolved =>
                  live_to_resolved
                    (lookup_to_live
                      (collision_to_lookup
                        (table_to_collision
                          (hash_to_table hHash)))))))))

theorem ay_chig_empty_clause_reachability_available
    (originalFormulaFingerprint : Prop) (proofLineDigest : Prop)
    (clauseHashFunctionVersionDigest : Prop) (clauseHashTableDigest : Prop)
    (collisionResolutionWitness : Prop) (antecedentLookupTranscript : Prop)
    (liveClauseContextDigest : Prop) (checkerReplayTranscript : Prop)
    (checkerAccepted : Prop) (emptyClauseReachabilityWitness : Prop)
    (archiveManifest : Prop) (archiveAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (lookupContextResolved : Prop) (originalUnsat : Prop) :
    ay_chig_accepted_evidence originalFormulaFingerprint proofLineDigest
      clauseHashFunctionVersionDigest clauseHashTableDigest
      collisionResolutionWitness antecedentLookupTranscript
      liveClauseContextDigest checkerReplayTranscript checkerAccepted
      emptyClauseReachabilityWitness archiveManifest archiveAccepted
      solverBuildEvidence buildAccepted fallbackNoClaim auditTranscript
      lookupContextResolved originalUnsat ->
    emptyClauseReachabilityWitness := by
  intro accepted
  exact accepted emptyClauseReachabilityWitness
    (fun _hFingerprint _hLine _hHash _hTable _hCollision _hLookup _hLive
      _hReplay _hChecker hReachability _hArchive _hArchiveAccepted _hBuild
      _hBuildAccepted _hFallback _hAudit _hResolved _hOriginal =>
      hReachability)

theorem ay_chig_lookup_context_available
    (originalFormulaFingerprint : Prop) (proofLineDigest : Prop)
    (clauseHashFunctionVersionDigest : Prop) (clauseHashTableDigest : Prop)
    (collisionResolutionWitness : Prop) (antecedentLookupTranscript : Prop)
    (liveClauseContextDigest : Prop) (checkerReplayTranscript : Prop)
    (checkerAccepted : Prop) (emptyClauseReachabilityWitness : Prop)
    (archiveManifest : Prop) (archiveAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (lookupContextResolved : Prop) (originalUnsat : Prop) :
    ay_chig_accepted_evidence originalFormulaFingerprint proofLineDigest
      clauseHashFunctionVersionDigest clauseHashTableDigest
      collisionResolutionWitness antecedentLookupTranscript
      liveClauseContextDigest checkerReplayTranscript checkerAccepted
      emptyClauseReachabilityWitness archiveManifest archiveAccepted
      solverBuildEvidence buildAccepted fallbackNoClaim auditTranscript
      lookupContextResolved originalUnsat ->
    lookupContextResolved := by
  intro accepted
  exact accepted lookupContextResolved
    (fun _hFingerprint _hLine _hHash _hTable _hCollision _hLookup _hLive
      _hReplay _hChecker _hReachability _hArchive _hArchiveAccepted _hBuild
      _hBuildAccepted _hFallback _hAudit hResolved _hOriginal =>
      hResolved)

theorem ay_chig_publication_sound
    (originalFormulaFingerprint : Prop) (proofLineDigest : Prop)
    (clauseHashFunctionVersionDigest : Prop) (clauseHashTableDigest : Prop)
    (collisionResolutionWitness : Prop) (antecedentLookupTranscript : Prop)
    (liveClauseContextDigest : Prop) (checkerReplayTranscript : Prop)
    (checkerAccepted : Prop) (emptyClauseReachabilityWitness : Prop)
    (archiveManifest : Prop) (archiveAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (lookupContextResolved : Prop) (originalUnsat : Prop) :
    ay_chig_publication originalFormulaFingerprint proofLineDigest
      clauseHashFunctionVersionDigest clauseHashTableDigest
      collisionResolutionWitness antecedentLookupTranscript
      liveClauseContextDigest checkerReplayTranscript checkerAccepted
      emptyClauseReachabilityWitness archiveManifest archiveAccepted
      solverBuildEvidence buildAccepted fallbackNoClaim auditTranscript
      lookupContextResolved originalUnsat ->
    originalUnsat := by
  intro publication
  exact publication originalUnsat
    (fun _accepted hOriginal => hOriginal)

theorem ay_chig_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :
    originalUnsat ->
    ay_chig_public_report noClaim originalUnsat publicSat := by
  intro hUnsat
  exact ay_chig_disj_right noClaim (ay_chig_disj originalUnsat publicSat)
    (ay_chig_disj_left originalUnsat publicSat hUnsat)

theorem ay_chig_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :
    noClaim ->
    ay_chig_public_report noClaim originalUnsat publicSat := by
  intro hNoClaim
  exact ay_chig_disj_left noClaim
    (ay_chig_disj originalUnsat publicSat) hNoClaim

theorem ay_chig_bad_no_claim
    (hashMismatch : Prop) (tableMismatch : Prop)
    (collisionMismatch : Prop) (lookupMismatch : Prop)
    (liveContextMismatch : Prop) (replayMismatch : Prop)
    (reachabilityMismatch : Prop) (archiveMismatch : Prop)
    (buildMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_chig_bad_guard hashMismatch tableMismatch collisionMismatch
      lookupMismatch liveContextMismatch replayMismatch reachabilityMismatch
      archiveMismatch buildMismatch auditMismatch noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun no_claim_and_recompute _reason =>
      no_claim_and_recompute noClaim
        (fun hNoClaim _hRecompute => hNoClaim))

theorem ay_chig_bad_recompute
    (hashMismatch : Prop) (tableMismatch : Prop)
    (collisionMismatch : Prop) (lookupMismatch : Prop)
    (liveContextMismatch : Prop) (replayMismatch : Prop)
    (reachabilityMismatch : Prop) (archiveMismatch : Prop)
    (buildMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_chig_bad_guard hashMismatch tableMismatch collisionMismatch
      lookupMismatch liveContextMismatch replayMismatch reachabilityMismatch
      archiveMismatch buildMismatch auditMismatch noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun no_claim_and_recompute _reason =>
      no_claim_and_recompute recompute
        (fun _hNoClaim hRecompute => hRecompute))

theorem ay_chig_failed_guard_cannot_bless_unsat
    (hashMismatch : Prop) (tableMismatch : Prop)
    (collisionMismatch : Prop) (lookupMismatch : Prop)
    (liveContextMismatch : Prop) (replayMismatch : Prop)
    (reachabilityMismatch : Prop) (archiveMismatch : Prop)
    (buildMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) (publicUnsat : Prop) :
    ay_chig_bad_guard hashMismatch tableMismatch collisionMismatch
      lookupMismatch liveContextMismatch replayMismatch reachabilityMismatch
      archiveMismatch buildMismatch auditMismatch noClaim recompute ->
    ay_chig_map noClaim (publicUnsat -> recompute) := by
  intro bad _hNoClaim _hPublicUnsat
  exact ay_chig_bad_recompute hashMismatch tableMismatch collisionMismatch
    lookupMismatch liveContextMismatch replayMismatch reachabilityMismatch
    archiveMismatch buildMismatch auditMismatch noClaim recompute bad

theorem ay_chig_failure_forces_no_claim
    (hashMismatch : Prop) (tableMismatch : Prop)
    (collisionMismatch : Prop) (lookupMismatch : Prop)
    (liveContextMismatch : Prop) (replayMismatch : Prop)
    (reachabilityMismatch : Prop) (archiveMismatch : Prop)
    (buildMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) :
    ay_chig_failure_reason hashMismatch tableMismatch collisionMismatch
      lookupMismatch liveContextMismatch replayMismatch reachabilityMismatch
      archiveMismatch buildMismatch auditMismatch ->
    (hashMismatch -> noClaim) ->
    (tableMismatch -> noClaim) ->
    (collisionMismatch -> noClaim) ->
    (lookupMismatch -> noClaim) ->
    (liveContextMismatch -> noClaim) ->
    (replayMismatch -> noClaim) ->
    (reachabilityMismatch -> noClaim) ->
    (archiveMismatch -> noClaim) ->
    (buildMismatch -> noClaim) ->
    (auditMismatch -> noClaim) ->
    noClaim := by
  intro reason hash_to_no_claim table_to_no_claim collision_to_no_claim
  intro lookup_to_no_claim live_to_no_claim replay_to_no_claim
  intro reachability_to_no_claim archive_to_no_claim build_to_no_claim
  intro audit_to_no_claim
  exact reason noClaim hash_to_no_claim table_to_no_claim
    collision_to_no_claim lookup_to_no_claim live_to_no_claim
    replay_to_no_claim reachability_to_no_claim archive_to_no_claim
    build_to_no_claim audit_to_no_claim

theorem ay_chig_hash_mismatch_forces_no_claim
    (hashMismatch noClaim : Prop) :
    hashMismatch ->
    (hashMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_chig_table_mismatch_forces_no_claim
    (tableMismatch noClaim : Prop) :
    tableMismatch ->
    (tableMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_chig_collision_mismatch_forces_no_claim
    (collisionMismatch noClaim : Prop) :
    collisionMismatch ->
    (collisionMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_chig_lookup_mismatch_forces_no_claim
    (lookupMismatch noClaim : Prop) :
    lookupMismatch ->
    (lookupMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_chig_live_context_mismatch_forces_no_claim
    (liveContextMismatch noClaim : Prop) :
    liveContextMismatch ->
    (liveContextMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_chig_replay_mismatch_forces_no_claim
    (replayMismatch noClaim : Prop) :
    replayMismatch ->
    (replayMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_chig_reachability_mismatch_forces_no_claim
    (reachabilityMismatch noClaim : Prop) :
    reachabilityMismatch ->
    (reachabilityMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_chig_archive_mismatch_forces_no_claim
    (archiveMismatch noClaim : Prop) :
    archiveMismatch ->
    (archiveMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_chig_build_mismatch_forces_no_claim
    (buildMismatch noClaim : Prop) :
    buildMismatch ->
    (buildMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_chig_audit_mismatch_forces_no_claim
    (auditMismatch noClaim : Prop) :
    auditMismatch ->
    (auditMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch
