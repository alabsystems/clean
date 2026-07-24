-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Proof-compression roundtrip guard soundness for ay sequential-main SAT-COMP
-- UNSAT certificates. Propositions model formula fingerprints, raw and
-- compressed proof digests, decompressor-version digests, decompression
-- transcripts, line-number and antecedent maps, empty-clause replay, checker
-- transcripts, archives, build evidence, fallback no-claim paths, audit
-- transcripts, and fail-closed recompute diagnostics.

def ay_pcsg_conj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def ay_pcsg_disj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def ay_pcsg_map (source : Prop) (target : Prop) :=
  source -> target

def ay_pcsg_accepted_evidence
    (originalFormulaFingerprint : Prop) (rawProofDigest : Prop)
    (compressedProofDigest : Prop) (decompressorVersionDigest : Prop)
    (decompressionTranscript : Prop) (lineNumberMapDigest : Prop)
    (antecedentMapDigest : Prop) (emptyClauseReplay : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (archiveManifest : Prop) (archiveAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (lineContextPreserved : Prop) (antecedentContextPreserved : Prop)
    (originalUnsat : Prop) :=
  forall result : Prop,
    (originalFormulaFingerprint ->
      rawProofDigest ->
      compressedProofDigest ->
      decompressorVersionDigest ->
      decompressionTranscript ->
      lineNumberMapDigest ->
      antecedentMapDigest ->
      emptyClauseReplay ->
      checkerTranscript ->
      checkerAccepted ->
      archiveManifest ->
      archiveAccepted ->
      solverBuildEvidence ->
      buildAccepted ->
      fallbackNoClaim ->
      auditTranscript ->
      lineContextPreserved ->
      antecedentContextPreserved ->
      originalUnsat ->
      result) ->
    result

def ay_pcsg_roundtrip_context
    (rawProofDigest : Prop) (compressedProofDigest : Prop)
    (decompressorVersionDigest : Prop) (decompressionTranscript : Prop)
    (lineNumberMapDigest : Prop) (antecedentMapDigest : Prop)
    (lineContextPreserved : Prop) (antecedentContextPreserved : Prop) :=
  ay_pcsg_conj
    (ay_pcsg_map rawProofDigest compressedProofDigest)
    (ay_pcsg_conj
      (ay_pcsg_map compressedProofDigest decompressorVersionDigest)
      (ay_pcsg_conj
        (ay_pcsg_map decompressorVersionDigest decompressionTranscript)
        (ay_pcsg_conj
          (ay_pcsg_map decompressionTranscript lineNumberMapDigest)
          (ay_pcsg_conj
            (ay_pcsg_map lineNumberMapDigest antecedentMapDigest)
            (ay_pcsg_conj
              (ay_pcsg_map antecedentMapDigest lineContextPreserved)
              (ay_pcsg_map lineContextPreserved
                antecedentContextPreserved)))))))

def ay_pcsg_checker_publication_path
    (decompressionTranscript : Prop) (emptyClauseReplay : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (originalUnsat : Prop) :=
  ay_pcsg_conj
    (ay_pcsg_map decompressionTranscript emptyClauseReplay)
    (ay_pcsg_conj
      (ay_pcsg_map emptyClauseReplay checkerTranscript)
      (ay_pcsg_conj
        (ay_pcsg_map checkerTranscript checkerAccepted)
        (ay_pcsg_map checkerAccepted originalUnsat)))

def ay_pcsg_publication
    (originalFormulaFingerprint : Prop) (rawProofDigest : Prop)
    (compressedProofDigest : Prop) (decompressorVersionDigest : Prop)
    (decompressionTranscript : Prop) (lineNumberMapDigest : Prop)
    (antecedentMapDigest : Prop) (emptyClauseReplay : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (archiveManifest : Prop) (archiveAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (lineContextPreserved : Prop) (antecedentContextPreserved : Prop)
    (originalUnsat : Prop) :=
  ay_pcsg_conj
    (ay_pcsg_accepted_evidence originalFormulaFingerprint rawProofDigest
      compressedProofDigest decompressorVersionDigest decompressionTranscript
      lineNumberMapDigest antecedentMapDigest emptyClauseReplay
      checkerTranscript checkerAccepted archiveManifest archiveAccepted
      solverBuildEvidence buildAccepted fallbackNoClaim auditTranscript
      lineContextPreserved antecedentContextPreserved originalUnsat)
    originalUnsat

def ay_pcsg_failure_reason
    (rawMismatch : Prop) (compressedMismatch : Prop)
    (decompressorMismatch : Prop) (lineMapMismatch : Prop)
    (antecedentMismatch : Prop) (replayMismatch : Prop)
    (checkerMismatch : Prop) (archiveMismatch : Prop)
    (buildMismatch : Prop) (auditMismatch : Prop) :=
  forall result : Prop,
    (rawMismatch -> result) ->
    (compressedMismatch -> result) ->
    (decompressorMismatch -> result) ->
    (lineMapMismatch -> result) ->
    (antecedentMismatch -> result) ->
    (replayMismatch -> result) ->
    (checkerMismatch -> result) ->
    (archiveMismatch -> result) ->
    (buildMismatch -> result) ->
    (auditMismatch -> result) ->
    result

def ay_pcsg_bad_guard
    (rawMismatch : Prop) (compressedMismatch : Prop)
    (decompressorMismatch : Prop) (lineMapMismatch : Prop)
    (antecedentMismatch : Prop) (replayMismatch : Prop)
    (checkerMismatch : Prop) (archiveMismatch : Prop)
    (buildMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :=
  ay_pcsg_conj
    (ay_pcsg_conj noClaim recompute)
    (ay_pcsg_failure_reason rawMismatch compressedMismatch
      decompressorMismatch lineMapMismatch antecedentMismatch replayMismatch
      checkerMismatch archiveMismatch buildMismatch auditMismatch)

def ay_pcsg_public_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :=
  ay_pcsg_disj noClaim (ay_pcsg_disj originalUnsat publicSat)

theorem ay_pcsg_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> ay_pcsg_conj p q := by
  intro hp hq result build
  exact build hp hq

theorem ay_pcsg_disj_left
    (p : Prop) (q : Prop) :
    p -> ay_pcsg_disj p q := by
  intro hp result left_to_result _right_to_result
  exact left_to_result hp

theorem ay_pcsg_disj_right
    (p : Prop) (q : Prop) :
    q -> ay_pcsg_disj p q := by
  intro hq result _left_to_result right_to_result
  exact right_to_result hq

theorem ay_pcsg_build_accepted_evidence
    (originalFormulaFingerprint : Prop) (rawProofDigest : Prop)
    (compressedProofDigest : Prop) (decompressorVersionDigest : Prop)
    (decompressionTranscript : Prop) (lineNumberMapDigest : Prop)
    (antecedentMapDigest : Prop) (emptyClauseReplay : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (archiveManifest : Prop) (archiveAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (lineContextPreserved : Prop) (antecedentContextPreserved : Prop)
    (originalUnsat : Prop) :
    originalFormulaFingerprint ->
    rawProofDigest ->
    compressedProofDigest ->
    decompressorVersionDigest ->
    decompressionTranscript ->
    lineNumberMapDigest ->
    antecedentMapDigest ->
    emptyClauseReplay ->
    checkerTranscript ->
    checkerAccepted ->
    archiveManifest ->
    archiveAccepted ->
    solverBuildEvidence ->
    buildAccepted ->
    fallbackNoClaim ->
    auditTranscript ->
    lineContextPreserved ->
    antecedentContextPreserved ->
    originalUnsat ->
    ay_pcsg_accepted_evidence originalFormulaFingerprint rawProofDigest
      compressedProofDigest decompressorVersionDigest decompressionTranscript
      lineNumberMapDigest antecedentMapDigest emptyClauseReplay
      checkerTranscript checkerAccepted archiveManifest archiveAccepted
      solverBuildEvidence buildAccepted fallbackNoClaim auditTranscript
      lineContextPreserved antecedentContextPreserved originalUnsat := by
  intro hFingerprint hRaw hCompressed hDecompressor hTranscript hLineMap
  intro hAntecedentMap hReplay hCheckerTranscript hChecker hArchive
  intro hArchiveAccepted hBuild hBuildAccepted hFallback hAudit hLineContext
  intro hAntecedentContext hOriginal result publish
  exact publish hFingerprint hRaw hCompressed hDecompressor hTranscript
    hLineMap hAntecedentMap hReplay hCheckerTranscript hChecker hArchive
    hArchiveAccepted hBuild hBuildAccepted hFallback hAudit hLineContext
    hAntecedentContext hOriginal

theorem ay_pcsg_compressed_publish_requires_checker_replay
    (decompressionTranscript : Prop) (emptyClauseReplay : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (originalUnsat : Prop) :
    ay_pcsg_checker_publication_path decompressionTranscript
      emptyClauseReplay checkerTranscript checkerAccepted originalUnsat ->
    decompressionTranscript ->
    originalUnsat := by
  intro path hDecompression
  exact path originalUnsat
    (fun decompression_to_replay rest =>
      rest originalUnsat
        (fun replay_to_checker_transcript rest2 =>
          rest2 originalUnsat
            (fun checker_transcript_to_accept accepted_to_unsat =>
              accepted_to_unsat
                (checker_transcript_to_accept
                  (replay_to_checker_transcript
                    (decompression_to_replay hDecompression)))))))

theorem ay_pcsg_roundtrip_preserves_line_context
    (originalFormulaFingerprint : Prop) (rawProofDigest : Prop)
    (compressedProofDigest : Prop) (decompressorVersionDigest : Prop)
    (decompressionTranscript : Prop) (lineNumberMapDigest : Prop)
    (antecedentMapDigest : Prop) (emptyClauseReplay : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (archiveManifest : Prop) (archiveAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (lineContextPreserved : Prop) (antecedentContextPreserved : Prop)
    (originalUnsat : Prop) :
    ay_pcsg_accepted_evidence originalFormulaFingerprint rawProofDigest
      compressedProofDigest decompressorVersionDigest decompressionTranscript
      lineNumberMapDigest antecedentMapDigest emptyClauseReplay
      checkerTranscript checkerAccepted archiveManifest archiveAccepted
      solverBuildEvidence buildAccepted fallbackNoClaim auditTranscript
      lineContextPreserved antecedentContextPreserved originalUnsat ->
    lineContextPreserved := by
  intro accepted
  exact accepted lineContextPreserved
    (fun _hFingerprint _hRaw _hCompressed _hDecompressor _hTranscript
      _hLineMap _hAntecedentMap _hReplay _hCheckerTranscript _hChecker
      _hArchive _hArchiveAccepted _hBuild _hBuildAccepted _hFallback
      _hAudit hLineContext _hAntecedentContext _hOriginal =>
      hLineContext)

theorem ay_pcsg_roundtrip_preserves_antecedent_context
    (originalFormulaFingerprint : Prop) (rawProofDigest : Prop)
    (compressedProofDigest : Prop) (decompressorVersionDigest : Prop)
    (decompressionTranscript : Prop) (lineNumberMapDigest : Prop)
    (antecedentMapDigest : Prop) (emptyClauseReplay : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (archiveManifest : Prop) (archiveAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (lineContextPreserved : Prop) (antecedentContextPreserved : Prop)
    (originalUnsat : Prop) :
    ay_pcsg_accepted_evidence originalFormulaFingerprint rawProofDigest
      compressedProofDigest decompressorVersionDigest decompressionTranscript
      lineNumberMapDigest antecedentMapDigest emptyClauseReplay
      checkerTranscript checkerAccepted archiveManifest archiveAccepted
      solverBuildEvidence buildAccepted fallbackNoClaim auditTranscript
      lineContextPreserved antecedentContextPreserved originalUnsat ->
    antecedentContextPreserved := by
  intro accepted
  exact accepted antecedentContextPreserved
    (fun _hFingerprint _hRaw _hCompressed _hDecompressor _hTranscript
      _hLineMap _hAntecedentMap _hReplay _hCheckerTranscript _hChecker
      _hArchive _hArchiveAccepted _hBuild _hBuildAccepted _hFallback
      _hAudit _hLineContext hAntecedentContext _hOriginal =>
      hAntecedentContext)

theorem ay_pcsg_empty_clause_replay_checked
    (originalFormulaFingerprint : Prop) (rawProofDigest : Prop)
    (compressedProofDigest : Prop) (decompressorVersionDigest : Prop)
    (decompressionTranscript : Prop) (lineNumberMapDigest : Prop)
    (antecedentMapDigest : Prop) (emptyClauseReplay : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (archiveManifest : Prop) (archiveAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (lineContextPreserved : Prop) (antecedentContextPreserved : Prop)
    (originalUnsat : Prop) :
    ay_pcsg_accepted_evidence originalFormulaFingerprint rawProofDigest
      compressedProofDigest decompressorVersionDigest decompressionTranscript
      lineNumberMapDigest antecedentMapDigest emptyClauseReplay
      checkerTranscript checkerAccepted archiveManifest archiveAccepted
      solverBuildEvidence buildAccepted fallbackNoClaim auditTranscript
      lineContextPreserved antecedentContextPreserved originalUnsat ->
    emptyClauseReplay := by
  intro accepted
  exact accepted emptyClauseReplay
    (fun _hFingerprint _hRaw _hCompressed _hDecompressor _hTranscript
      _hLineMap _hAntecedentMap hReplay _hCheckerTranscript _hChecker
      _hArchive _hArchiveAccepted _hBuild _hBuildAccepted _hFallback
      _hAudit _hLineContext _hAntecedentContext _hOriginal =>
      hReplay)

theorem ay_pcsg_publication_sound
    (originalFormulaFingerprint : Prop) (rawProofDigest : Prop)
    (compressedProofDigest : Prop) (decompressorVersionDigest : Prop)
    (decompressionTranscript : Prop) (lineNumberMapDigest : Prop)
    (antecedentMapDigest : Prop) (emptyClauseReplay : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (archiveManifest : Prop) (archiveAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (lineContextPreserved : Prop) (antecedentContextPreserved : Prop)
    (originalUnsat : Prop) :
    ay_pcsg_publication originalFormulaFingerprint rawProofDigest
      compressedProofDigest decompressorVersionDigest decompressionTranscript
      lineNumberMapDigest antecedentMapDigest emptyClauseReplay
      checkerTranscript checkerAccepted archiveManifest archiveAccepted
      solverBuildEvidence buildAccepted fallbackNoClaim auditTranscript
      lineContextPreserved antecedentContextPreserved originalUnsat ->
    originalUnsat := by
  intro publication
  exact publication originalUnsat
    (fun _accepted hOriginal => hOriginal)

theorem ay_pcsg_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :
    originalUnsat ->
    ay_pcsg_public_report noClaim originalUnsat publicSat := by
  intro hUnsat
  exact ay_pcsg_disj_right noClaim (ay_pcsg_disj originalUnsat publicSat)
    (ay_pcsg_disj_left originalUnsat publicSat hUnsat)

theorem ay_pcsg_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :
    noClaim ->
    ay_pcsg_public_report noClaim originalUnsat publicSat := by
  intro hNoClaim
  exact ay_pcsg_disj_left noClaim
    (ay_pcsg_disj originalUnsat publicSat) hNoClaim

theorem ay_pcsg_bad_no_claim
    (rawMismatch : Prop) (compressedMismatch : Prop)
    (decompressorMismatch : Prop) (lineMapMismatch : Prop)
    (antecedentMismatch : Prop) (replayMismatch : Prop)
    (checkerMismatch : Prop) (archiveMismatch : Prop)
    (buildMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_pcsg_bad_guard rawMismatch compressedMismatch decompressorMismatch
      lineMapMismatch antecedentMismatch replayMismatch checkerMismatch
      archiveMismatch buildMismatch auditMismatch noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun no_claim_and_recompute _reason =>
      no_claim_and_recompute noClaim
        (fun hNoClaim _hRecompute => hNoClaim))

theorem ay_pcsg_bad_recompute
    (rawMismatch : Prop) (compressedMismatch : Prop)
    (decompressorMismatch : Prop) (lineMapMismatch : Prop)
    (antecedentMismatch : Prop) (replayMismatch : Prop)
    (checkerMismatch : Prop) (archiveMismatch : Prop)
    (buildMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_pcsg_bad_guard rawMismatch compressedMismatch decompressorMismatch
      lineMapMismatch antecedentMismatch replayMismatch checkerMismatch
      archiveMismatch buildMismatch auditMismatch noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun no_claim_and_recompute _reason =>
      no_claim_and_recompute recompute
        (fun _hNoClaim hRecompute => hRecompute))

theorem ay_pcsg_failed_guard_cannot_bless_unsat
    (rawMismatch : Prop) (compressedMismatch : Prop)
    (decompressorMismatch : Prop) (lineMapMismatch : Prop)
    (antecedentMismatch : Prop) (replayMismatch : Prop)
    (checkerMismatch : Prop) (archiveMismatch : Prop)
    (buildMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) (publicUnsat : Prop) :
    ay_pcsg_bad_guard rawMismatch compressedMismatch decompressorMismatch
      lineMapMismatch antecedentMismatch replayMismatch checkerMismatch
      archiveMismatch buildMismatch auditMismatch noClaim recompute ->
    ay_pcsg_map noClaim (publicUnsat -> recompute) := by
  intro bad _hNoClaim _hPublicUnsat
  exact ay_pcsg_bad_recompute rawMismatch compressedMismatch
    decompressorMismatch lineMapMismatch antecedentMismatch replayMismatch
    checkerMismatch archiveMismatch buildMismatch auditMismatch noClaim
    recompute bad

theorem ay_pcsg_failure_forces_no_claim
    (rawMismatch : Prop) (compressedMismatch : Prop)
    (decompressorMismatch : Prop) (lineMapMismatch : Prop)
    (antecedentMismatch : Prop) (replayMismatch : Prop)
    (checkerMismatch : Prop) (archiveMismatch : Prop)
    (buildMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) :
    ay_pcsg_failure_reason rawMismatch compressedMismatch decompressorMismatch
      lineMapMismatch antecedentMismatch replayMismatch checkerMismatch
      archiveMismatch buildMismatch auditMismatch ->
    (rawMismatch -> noClaim) ->
    (compressedMismatch -> noClaim) ->
    (decompressorMismatch -> noClaim) ->
    (lineMapMismatch -> noClaim) ->
    (antecedentMismatch -> noClaim) ->
    (replayMismatch -> noClaim) ->
    (checkerMismatch -> noClaim) ->
    (archiveMismatch -> noClaim) ->
    (buildMismatch -> noClaim) ->
    (auditMismatch -> noClaim) ->
    noClaim := by
  intro reason raw_to_no_claim compressed_to_no_claim
  intro decompressor_to_no_claim line_to_no_claim antecedent_to_no_claim
  intro replay_to_no_claim checker_to_no_claim archive_to_no_claim
  intro build_to_no_claim audit_to_no_claim
  exact reason noClaim raw_to_no_claim compressed_to_no_claim
    decompressor_to_no_claim line_to_no_claim antecedent_to_no_claim
    replay_to_no_claim checker_to_no_claim archive_to_no_claim
    build_to_no_claim audit_to_no_claim

theorem ay_pcsg_raw_mismatch_forces_no_claim
    (rawMismatch noClaim : Prop) :
    rawMismatch ->
    (rawMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_pcsg_compressed_mismatch_forces_no_claim
    (compressedMismatch noClaim : Prop) :
    compressedMismatch ->
    (compressedMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_pcsg_decompressor_mismatch_forces_no_claim
    (decompressorMismatch noClaim : Prop) :
    decompressorMismatch ->
    (decompressorMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_pcsg_line_map_mismatch_forces_no_claim
    (lineMapMismatch noClaim : Prop) :
    lineMapMismatch ->
    (lineMapMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_pcsg_antecedent_mismatch_forces_no_claim
    (antecedentMismatch noClaim : Prop) :
    antecedentMismatch ->
    (antecedentMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_pcsg_replay_mismatch_forces_no_claim
    (replayMismatch noClaim : Prop) :
    replayMismatch ->
    (replayMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_pcsg_checker_mismatch_forces_no_claim
    (checkerMismatch noClaim : Prop) :
    checkerMismatch ->
    (checkerMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_pcsg_archive_mismatch_forces_no_claim
    (archiveMismatch noClaim : Prop) :
    archiveMismatch ->
    (archiveMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_pcsg_build_mismatch_forces_no_claim
    (buildMismatch noClaim : Prop) :
    buildMismatch ->
    (buildMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_pcsg_audit_mismatch_forces_no_claim
    (auditMismatch noClaim : Prop) :
    auditMismatch ->
    (auditMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch
