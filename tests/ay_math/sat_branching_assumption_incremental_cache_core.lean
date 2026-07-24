-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded incremental assumption cache soundness skeleton for ay SAT solving.
-- Cached preprocessing and branching guidance can be reused only when the
-- assumption frame, epoch, dependency digest, replay evidence, and current
-- formula agreement all match. Stale or partial replay falls back to a
-- no-claim/recompute path preserving public SAT/UNSAT soundness.

def AyBAICConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyBAICDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyBAICEquisat (before : Prop) (after : Prop) :=
  AyBAICConj (before -> after) (after -> before)

def AyBAICAssumptionFrame (base : Prop) (assumption : Prop) :=
  AyBAICConj base assumption

def AyBAICFormulaState (formula : Prop) (frame : Prop) :=
  AyBAICConj formula frame

def AyBAICCachedArtifact
    (frameId : Prop) (epoch : Prop) (dependencyDigest : Prop)
    (preprocessGuide : Prop) (branchGuide : Prop) :=
  AyBAICConj frameId
    (AyBAICConj epoch
      (AyBAICConj dependencyDigest
        (AyBAICConj preprocessGuide branchGuide)))

def AyBAICReplayMatch
    (frameMatch : Prop) (epochMatch : Prop) (dependencyMatch : Prop)
    (checkerEvidence : Prop) (formulaMatch : Prop) :=
  AyBAICConj frameMatch
    (AyBAICConj epochMatch
      (AyBAICConj dependencyMatch
        (AyBAICConj checkerEvidence formulaMatch)))

def AyBAICAcceptedReuse
    (cache : Prop) (matchWitness : Prop) (fullReplay : Prop) :=
  AyBAICConj cache (AyBAICConj matchWitness fullReplay)

def AyBAICOutcome (model : Prop) (conflict : Prop) :=
  AyBAICDisj model conflict

def AyBAICPublicReport (outcome : Prop) (frameId : Prop) :=
  AyBAICConj outcome frameId

def AyBAICAcceptedReport (reuse : Prop) (public : Prop) :=
  AyBAICConj reuse public

def AyBAICNoClaim (diagnostic : Prop) (fallbackPublic : Prop) :=
  AyBAICConj fallbackPublic diagnostic

theorem ay_baic_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyBAICConj left right :=
  fun leftH rightH result build =>
    build leftH rightH

theorem ay_baic_conj_left
    (left : Prop) (right : Prop) :
    AyBAICConj left right -> left :=
  fun both =>
    both left (fun leftH _rightH => leftH)

theorem ay_baic_conj_right
    (left : Prop) (right : Prop) :
    AyBAICConj left right -> right :=
  fun both =>
    both right (fun _leftH rightH => rightH)

theorem ay_baic_disj_left
    (left : Prop) (right : Prop) :
    left -> AyBAICDisj left right :=
  fun leftH result leftCase _rightCase =>
    leftCase leftH

theorem ay_baic_disj_right
    (left : Prop) (right : Prop) :
    right -> AyBAICDisj left right :=
  fun rightH result _leftCase rightCase =>
    rightCase rightH

theorem ay_baic_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyBAICEquisat before after :=
  fun forward backward =>
    ay_baic_conj_intro (before -> after) (after -> before)
      forward backward

theorem ay_baic_equisat_forward
    (before : Prop) (after : Prop) :
    AyBAICEquisat before after -> before -> after :=
  fun equisat =>
    ay_baic_conj_left (before -> after) (after -> before) equisat

theorem ay_baic_equisat_backward
    (before : Prop) (after : Prop) :
    AyBAICEquisat before after -> after -> before :=
  fun equisat =>
    ay_baic_conj_right (before -> after) (after -> before) equisat

theorem ay_baic_assumption_frame_intro
    (base : Prop) (assumption : Prop) :
    base -> assumption -> AyBAICAssumptionFrame base assumption :=
  fun baseH assumptionH =>
    ay_baic_conj_intro base assumption baseH assumptionH

theorem ay_baic_assumption_frame_base
    (base : Prop) (assumption : Prop) :
    AyBAICAssumptionFrame base assumption -> base :=
  fun frame =>
    ay_baic_conj_left base assumption frame

theorem ay_baic_assumption_frame_value
    (base : Prop) (assumption : Prop) :
    AyBAICAssumptionFrame base assumption -> assumption :=
  fun frame =>
    ay_baic_conj_right base assumption frame

theorem ay_baic_state_under_assumption
    (formula : Prop) (base : Prop) (assumption : Prop) :
    AyBAICFormulaState formula base ->
    assumption ->
    AyBAICFormulaState formula
      (AyBAICAssumptionFrame base assumption) :=
  fun state assumptionH =>
    ay_baic_conj_intro formula
      (AyBAICAssumptionFrame base assumption)
      (ay_baic_conj_left formula base state)
      (ay_baic_assumption_frame_intro base assumption
        (ay_baic_conj_right formula base state)
        assumptionH)

theorem ay_baic_preprocess_transport
    (current : Prop) (preprocessed : Prop) (frameId : Prop) :
    AyBAICEquisat current preprocessed ->
    AyBAICFormulaState current frameId ->
    AyBAICFormulaState preprocessed frameId :=
  fun equisat state =>
    ay_baic_conj_intro preprocessed frameId
      (ay_baic_equisat_forward current preprocessed equisat
        (ay_baic_conj_left current frameId state))
      (ay_baic_conj_right current frameId state)

theorem ay_baic_cached_artifact_intro
    (frameId : Prop) (epoch : Prop) (dependencyDigest : Prop)
    (preprocessGuide : Prop) (branchGuide : Prop) :
    frameId ->
    epoch ->
    dependencyDigest ->
    preprocessGuide ->
    branchGuide ->
    AyBAICCachedArtifact frameId epoch dependencyDigest
      preprocessGuide branchGuide :=
  fun frameH epochH dependencyH preprocessH branchH =>
    ay_baic_conj_intro frameId
      (AyBAICConj epoch
        (AyBAICConj dependencyDigest
          (AyBAICConj preprocessGuide branchGuide)))
      frameH
      (ay_baic_conj_intro epoch
        (AyBAICConj dependencyDigest
          (AyBAICConj preprocessGuide branchGuide))
        epochH
        (ay_baic_conj_intro dependencyDigest
          (AyBAICConj preprocessGuide branchGuide)
          dependencyH
          (ay_baic_conj_intro preprocessGuide branchGuide
            preprocessH branchH)))

theorem ay_baic_cached_artifact_frame
    (frameId : Prop) (epoch : Prop) (dependencyDigest : Prop)
    (preprocessGuide : Prop) (branchGuide : Prop) :
    AyBAICCachedArtifact frameId epoch dependencyDigest
      preprocessGuide branchGuide ->
    frameId :=
  fun cache =>
    ay_baic_conj_left frameId
      (AyBAICConj epoch
        (AyBAICConj dependencyDigest
          (AyBAICConj preprocessGuide branchGuide)))
      cache

theorem ay_baic_cached_artifact_tail
    (frameId : Prop) (epoch : Prop) (dependencyDigest : Prop)
    (preprocessGuide : Prop) (branchGuide : Prop) :
    AyBAICCachedArtifact frameId epoch dependencyDigest
      preprocessGuide branchGuide ->
    AyBAICConj epoch
      (AyBAICConj dependencyDigest
        (AyBAICConj preprocessGuide branchGuide)) :=
  fun cache =>
    ay_baic_conj_right frameId
      (AyBAICConj epoch
        (AyBAICConj dependencyDigest
          (AyBAICConj preprocessGuide branchGuide)))
      cache

theorem ay_baic_cached_artifact_epoch
    (frameId : Prop) (epoch : Prop) (dependencyDigest : Prop)
    (preprocessGuide : Prop) (branchGuide : Prop) :
    AyBAICCachedArtifact frameId epoch dependencyDigest
      preprocessGuide branchGuide ->
    epoch :=
  fun cache =>
    ay_baic_conj_left epoch
      (AyBAICConj dependencyDigest
        (AyBAICConj preprocessGuide branchGuide))
      (ay_baic_cached_artifact_tail frameId epoch dependencyDigest
        preprocessGuide branchGuide cache)

theorem ay_baic_cached_artifact_dependency
    (frameId : Prop) (epoch : Prop) (dependencyDigest : Prop)
    (preprocessGuide : Prop) (branchGuide : Prop) :
    AyBAICCachedArtifact frameId epoch dependencyDigest
      preprocessGuide branchGuide ->
    dependencyDigest :=
  fun cache =>
    ay_baic_conj_left dependencyDigest
      (AyBAICConj preprocessGuide branchGuide)
      (ay_baic_conj_right epoch
        (AyBAICConj dependencyDigest
          (AyBAICConj preprocessGuide branchGuide))
        (ay_baic_cached_artifact_tail frameId epoch dependencyDigest
          preprocessGuide branchGuide cache))

theorem ay_baic_cached_artifact_preprocess_guide
    (frameId : Prop) (epoch : Prop) (dependencyDigest : Prop)
    (preprocessGuide : Prop) (branchGuide : Prop) :
    AyBAICCachedArtifact frameId epoch dependencyDigest
      preprocessGuide branchGuide ->
    preprocessGuide :=
  fun cache =>
    ay_baic_conj_left preprocessGuide branchGuide
      (ay_baic_conj_right dependencyDigest
        (AyBAICConj preprocessGuide branchGuide)
        (ay_baic_conj_right epoch
          (AyBAICConj dependencyDigest
            (AyBAICConj preprocessGuide branchGuide))
          (ay_baic_cached_artifact_tail frameId epoch dependencyDigest
            preprocessGuide branchGuide cache)))

theorem ay_baic_cached_artifact_branch_guide
    (frameId : Prop) (epoch : Prop) (dependencyDigest : Prop)
    (preprocessGuide : Prop) (branchGuide : Prop) :
    AyBAICCachedArtifact frameId epoch dependencyDigest
      preprocessGuide branchGuide ->
    branchGuide :=
  fun cache =>
    ay_baic_conj_right preprocessGuide branchGuide
      (ay_baic_conj_right dependencyDigest
        (AyBAICConj preprocessGuide branchGuide)
        (ay_baic_conj_right epoch
          (AyBAICConj dependencyDigest
            (AyBAICConj preprocessGuide branchGuide))
          (ay_baic_cached_artifact_tail frameId epoch dependencyDigest
            preprocessGuide branchGuide cache)))

theorem ay_baic_replay_match_intro
    (frameMatch : Prop) (epochMatch : Prop) (dependencyMatch : Prop)
    (checkerEvidence : Prop) (formulaMatch : Prop) :
    frameMatch ->
    epochMatch ->
    dependencyMatch ->
    checkerEvidence ->
    formulaMatch ->
    AyBAICReplayMatch frameMatch epochMatch dependencyMatch
      checkerEvidence formulaMatch :=
  fun frameH epochH dependencyH checkerH formulaH =>
    ay_baic_conj_intro frameMatch
      (AyBAICConj epochMatch
        (AyBAICConj dependencyMatch
          (AyBAICConj checkerEvidence formulaMatch)))
      frameH
      (ay_baic_conj_intro epochMatch
        (AyBAICConj dependencyMatch
          (AyBAICConj checkerEvidence formulaMatch))
        epochH
        (ay_baic_conj_intro dependencyMatch
          (AyBAICConj checkerEvidence formulaMatch)
          dependencyH
          (ay_baic_conj_intro checkerEvidence formulaMatch
            checkerH formulaH)))

theorem ay_baic_replay_match_frame
    (frameMatch : Prop) (epochMatch : Prop) (dependencyMatch : Prop)
    (checkerEvidence : Prop) (formulaMatch : Prop) :
    AyBAICReplayMatch frameMatch epochMatch dependencyMatch
      checkerEvidence formulaMatch ->
    frameMatch :=
  fun matchH =>
    ay_baic_conj_left frameMatch
      (AyBAICConj epochMatch
        (AyBAICConj dependencyMatch
          (AyBAICConj checkerEvidence formulaMatch)))
      matchH

theorem ay_baic_replay_match_tail
    (frameMatch : Prop) (epochMatch : Prop) (dependencyMatch : Prop)
    (checkerEvidence : Prop) (formulaMatch : Prop) :
    AyBAICReplayMatch frameMatch epochMatch dependencyMatch
      checkerEvidence formulaMatch ->
    AyBAICConj epochMatch
      (AyBAICConj dependencyMatch
        (AyBAICConj checkerEvidence formulaMatch)) :=
  fun matchH =>
    ay_baic_conj_right frameMatch
      (AyBAICConj epochMatch
        (AyBAICConj dependencyMatch
          (AyBAICConj checkerEvidence formulaMatch)))
      matchH

theorem ay_baic_replay_match_epoch
    (frameMatch : Prop) (epochMatch : Prop) (dependencyMatch : Prop)
    (checkerEvidence : Prop) (formulaMatch : Prop) :
    AyBAICReplayMatch frameMatch epochMatch dependencyMatch
      checkerEvidence formulaMatch ->
    epochMatch :=
  fun matchH =>
    ay_baic_conj_left epochMatch
      (AyBAICConj dependencyMatch
        (AyBAICConj checkerEvidence formulaMatch))
      (ay_baic_replay_match_tail frameMatch epochMatch dependencyMatch
        checkerEvidence formulaMatch matchH)

theorem ay_baic_replay_match_dependency
    (frameMatch : Prop) (epochMatch : Prop) (dependencyMatch : Prop)
    (checkerEvidence : Prop) (formulaMatch : Prop) :
    AyBAICReplayMatch frameMatch epochMatch dependencyMatch
      checkerEvidence formulaMatch ->
    dependencyMatch :=
  fun matchH =>
    ay_baic_conj_left dependencyMatch
      (AyBAICConj checkerEvidence formulaMatch)
      (ay_baic_conj_right epochMatch
        (AyBAICConj dependencyMatch
          (AyBAICConj checkerEvidence formulaMatch))
        (ay_baic_replay_match_tail frameMatch epochMatch dependencyMatch
          checkerEvidence formulaMatch matchH))

theorem ay_baic_replay_match_checker
    (frameMatch : Prop) (epochMatch : Prop) (dependencyMatch : Prop)
    (checkerEvidence : Prop) (formulaMatch : Prop) :
    AyBAICReplayMatch frameMatch epochMatch dependencyMatch
      checkerEvidence formulaMatch ->
    checkerEvidence :=
  fun matchH =>
    ay_baic_conj_left checkerEvidence formulaMatch
      (ay_baic_conj_right dependencyMatch
        (AyBAICConj checkerEvidence formulaMatch)
        (ay_baic_conj_right epochMatch
          (AyBAICConj dependencyMatch
            (AyBAICConj checkerEvidence formulaMatch))
          (ay_baic_replay_match_tail frameMatch epochMatch dependencyMatch
            checkerEvidence formulaMatch matchH)))

theorem ay_baic_replay_match_formula
    (frameMatch : Prop) (epochMatch : Prop) (dependencyMatch : Prop)
    (checkerEvidence : Prop) (formulaMatch : Prop) :
    AyBAICReplayMatch frameMatch epochMatch dependencyMatch
      checkerEvidence formulaMatch ->
    formulaMatch :=
  fun matchH =>
    ay_baic_conj_right checkerEvidence formulaMatch
      (ay_baic_conj_right dependencyMatch
        (AyBAICConj checkerEvidence formulaMatch)
        (ay_baic_conj_right epochMatch
          (AyBAICConj dependencyMatch
            (AyBAICConj checkerEvidence formulaMatch))
          (ay_baic_replay_match_tail frameMatch epochMatch dependencyMatch
            checkerEvidence formulaMatch matchH)))

theorem ay_baic_accepted_reuse_intro
    (cache : Prop) (matchWitness : Prop) (fullReplay : Prop) :
    cache ->
    matchWitness ->
    fullReplay ->
    AyBAICAcceptedReuse cache matchWitness fullReplay :=
  fun cacheH matchH replayH =>
    ay_baic_conj_intro cache (AyBAICConj matchWitness fullReplay)
      cacheH
      (ay_baic_conj_intro matchWitness fullReplay matchH replayH)

theorem ay_baic_accepted_reuse_cache
    (cache : Prop) (matchWitness : Prop) (fullReplay : Prop) :
    AyBAICAcceptedReuse cache matchWitness fullReplay -> cache :=
  fun reuse =>
    ay_baic_conj_left cache (AyBAICConj matchWitness fullReplay)
      reuse

theorem ay_baic_accepted_reuse_match
    (cache : Prop) (matchWitness : Prop) (fullReplay : Prop) :
    AyBAICAcceptedReuse cache matchWitness fullReplay -> matchWitness :=
  fun reuse =>
    ay_baic_conj_left matchWitness fullReplay
      (ay_baic_conj_right cache
        (AyBAICConj matchWitness fullReplay)
        reuse)

theorem ay_baic_accepted_reuse_full_replay
    (cache : Prop) (matchWitness : Prop) (fullReplay : Prop) :
    AyBAICAcceptedReuse cache matchWitness fullReplay -> fullReplay :=
  fun reuse =>
    ay_baic_conj_right matchWitness fullReplay
      (ay_baic_conj_right cache
        (AyBAICConj matchWitness fullReplay)
        reuse)

theorem ay_baic_public_sat_report
    (model : Prop) (conflict : Prop) (frameId : Prop) :
    model ->
    frameId ->
    AyBAICPublicReport (AyBAICOutcome model conflict) frameId :=
  fun modelH frameH =>
    ay_baic_conj_intro (AyBAICOutcome model conflict) frameId
      (ay_baic_disj_left model conflict modelH)
      frameH

theorem ay_baic_public_unsat_report
    (model : Prop) (conflict : Prop) (frameId : Prop) :
    conflict ->
    frameId ->
    AyBAICPublicReport (AyBAICOutcome model conflict) frameId :=
  fun conflictH frameH =>
    ay_baic_conj_intro (AyBAICOutcome model conflict) frameId
      (ay_baic_disj_right model conflict conflictH)
      frameH

theorem ay_baic_accepted_report_intro
    (reuse : Prop) (public : Prop) :
    reuse -> public -> AyBAICAcceptedReport reuse public :=
  fun reuseH publicH =>
    ay_baic_conj_intro reuse public reuseH publicH

theorem ay_baic_accepted_report_reuse
    (reuse : Prop) (public : Prop) :
    AyBAICAcceptedReport reuse public -> reuse :=
  fun report =>
    ay_baic_conj_left reuse public report

theorem ay_baic_accepted_report_public
    (reuse : Prop) (public : Prop) :
    AyBAICAcceptedReport reuse public -> public :=
  fun report =>
    ay_baic_conj_right reuse public report

theorem ay_baic_no_claim_intro
    (diagnostic : Prop) (fallbackPublic : Prop) :
    diagnostic ->
    fallbackPublic ->
    AyBAICNoClaim diagnostic fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_baic_conj_intro fallbackPublic diagnostic fallbackH diagnosticH

theorem ay_baic_no_claim_preserves_fallback
    (diagnostic : Prop) (fallbackPublic : Prop) :
    AyBAICNoClaim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim =>
    ay_baic_conj_left fallbackPublic diagnostic noClaim

theorem ay_baic_frame_mismatch_no_claim
    (frameMismatch : Prop) (fallbackPublic : Prop) :
    frameMismatch ->
    fallbackPublic ->
    AyBAICNoClaim frameMismatch fallbackPublic :=
  fun mismatchH fallbackH =>
    ay_baic_no_claim_intro frameMismatch fallbackPublic
      mismatchH fallbackH

theorem ay_baic_stale_dependency_no_claim
    (staleDependency : Prop) (fallbackPublic : Prop) :
    staleDependency ->
    fallbackPublic ->
    AyBAICNoClaim staleDependency fallbackPublic :=
  fun staleH fallbackH =>
    ay_baic_no_claim_intro staleDependency fallbackPublic
      staleH fallbackH

theorem ay_baic_partial_replay_no_claim
    (partialReplay : Prop) (fallbackPublic : Prop) :
    partialReplay ->
    fallbackPublic ->
    AyBAICNoClaim partialReplay fallbackPublic :=
  fun partialH fallbackH =>
    ay_baic_no_claim_intro partialReplay fallbackPublic
      partialH fallbackH

theorem ay_baic_matching_cache_guides_sat
    (frameId : Prop) (epoch : Prop) (dependencyDigest : Prop)
    (preprocessGuide : Prop) (branchGuide : Prop)
    (frameMatch : Prop) (epochMatch : Prop) (dependencyMatch : Prop)
    (checkerEvidence : Prop) (formulaMatch : Prop)
    (fullReplay : Prop) (model : Prop) (conflict : Prop) :
    AyBAICCachedArtifact frameId epoch dependencyDigest
      preprocessGuide branchGuide ->
    AyBAICReplayMatch frameMatch epochMatch dependencyMatch
      checkerEvidence formulaMatch ->
    fullReplay ->
    model ->
    AyBAICAcceptedReport
      (AyBAICAcceptedReuse
        (AyBAICCachedArtifact frameId epoch dependencyDigest
          preprocessGuide branchGuide)
        (AyBAICReplayMatch frameMatch epochMatch dependencyMatch
          checkerEvidence formulaMatch)
        fullReplay)
      (AyBAICPublicReport (AyBAICOutcome model conflict) frameId) :=
  fun cache matchH replayH modelH =>
    ay_baic_accepted_report_intro
      (AyBAICAcceptedReuse
        (AyBAICCachedArtifact frameId epoch dependencyDigest
          preprocessGuide branchGuide)
        (AyBAICReplayMatch frameMatch epochMatch dependencyMatch
          checkerEvidence formulaMatch)
        fullReplay)
      (AyBAICPublicReport (AyBAICOutcome model conflict) frameId)
      (ay_baic_accepted_reuse_intro
        (AyBAICCachedArtifact frameId epoch dependencyDigest
          preprocessGuide branchGuide)
        (AyBAICReplayMatch frameMatch epochMatch dependencyMatch
          checkerEvidence formulaMatch)
        fullReplay
        cache matchH replayH)
      (ay_baic_public_sat_report model conflict frameId modelH
        (ay_baic_cached_artifact_frame frameId epoch dependencyDigest
          preprocessGuide branchGuide cache))

theorem ay_baic_matching_cache_guides_unsat
    (frameId : Prop) (epoch : Prop) (dependencyDigest : Prop)
    (preprocessGuide : Prop) (branchGuide : Prop)
    (frameMatch : Prop) (epochMatch : Prop) (dependencyMatch : Prop)
    (checkerEvidence : Prop) (formulaMatch : Prop)
    (fullReplay : Prop) (model : Prop) (conflict : Prop) :
    AyBAICCachedArtifact frameId epoch dependencyDigest
      preprocessGuide branchGuide ->
    AyBAICReplayMatch frameMatch epochMatch dependencyMatch
      checkerEvidence formulaMatch ->
    fullReplay ->
    conflict ->
    AyBAICAcceptedReport
      (AyBAICAcceptedReuse
        (AyBAICCachedArtifact frameId epoch dependencyDigest
          preprocessGuide branchGuide)
        (AyBAICReplayMatch frameMatch epochMatch dependencyMatch
          checkerEvidence formulaMatch)
        fullReplay)
      (AyBAICPublicReport (AyBAICOutcome model conflict) frameId) :=
  fun cache matchH replayH conflictH =>
    ay_baic_accepted_report_intro
      (AyBAICAcceptedReuse
        (AyBAICCachedArtifact frameId epoch dependencyDigest
          preprocessGuide branchGuide)
        (AyBAICReplayMatch frameMatch epochMatch dependencyMatch
          checkerEvidence formulaMatch)
        fullReplay)
      (AyBAICPublicReport (AyBAICOutcome model conflict) frameId)
      (ay_baic_accepted_reuse_intro
        (AyBAICCachedArtifact frameId epoch dependencyDigest
          preprocessGuide branchGuide)
        (AyBAICReplayMatch frameMatch epochMatch dependencyMatch
          checkerEvidence formulaMatch)
        fullReplay
        cache matchH replayH)
      (ay_baic_public_unsat_report model conflict frameId conflictH
        (ay_baic_cached_artifact_frame frameId epoch dependencyDigest
          preprocessGuide branchGuide cache))

theorem ay_baic_accepted_cache_report_soundness
    (frameId : Prop) (epoch : Prop) (dependencyDigest : Prop)
    (preprocessGuide : Prop) (branchGuide : Prop)
    (frameMatch : Prop) (epochMatch : Prop) (dependencyMatch : Prop)
    (checkerEvidence : Prop) (formulaMatch : Prop)
    (fullReplay : Prop) (model : Prop) (conflict : Prop) :
    AyBAICAcceptedReport
      (AyBAICAcceptedReuse
        (AyBAICCachedArtifact frameId epoch dependencyDigest
          preprocessGuide branchGuide)
        (AyBAICReplayMatch frameMatch epochMatch dependencyMatch
          checkerEvidence formulaMatch)
        fullReplay)
      (AyBAICPublicReport (AyBAICOutcome model conflict) frameId) ->
    AyBAICPublicReport (AyBAICOutcome model conflict) frameId :=
  fun report =>
    ay_baic_accepted_report_public
      (AyBAICAcceptedReuse
        (AyBAICCachedArtifact frameId epoch dependencyDigest
          preprocessGuide branchGuide)
        (AyBAICReplayMatch frameMatch epochMatch dependencyMatch
          checkerEvidence formulaMatch)
        fullReplay)
      (AyBAICPublicReport (AyBAICOutcome model conflict) frameId)
      report

theorem ay_baic_no_claim_recompute_preserves_soundness
    (diagnostic : Prop) (fallbackPublic : Prop) :
    AyBAICNoClaim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim =>
    ay_baic_no_claim_preserves_fallback diagnostic fallbackPublic noClaim
