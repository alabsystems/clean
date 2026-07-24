-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded rollback/reuse soundness skeleton for incremental ay SAT solving.
-- Learned clauses and guidance retained after popping assumptions are reusable
-- only when their dependencies are contained in the surviving base frame, the
-- epoch/digest matches, and checker replay confirms the retained clause under
-- the original formula. Otherwise restart/recompute/no-claim preserves public
-- SAT/UNSAT soundness.

def AyBARRConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyBARRDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyBARREquisat (before : Prop) (after : Prop) :=
  AyBARRConj (before -> after) (after -> before)

def AyBARRFrame (base : Prop) (assumption : Prop) :=
  AyBARRConj base assumption

def AyBARRState (formula : Prop) (frame : Prop) :=
  AyBARRConj formula frame

def AyBARRRetainedArtifact
    (learnedClause : Prop) (guidance : Prop)
    (dependencySet : Prop) (epoch : Prop) (digest : Prop) :=
  AyBARRConj learnedClause
    (AyBARRConj guidance
      (AyBARRConj dependencySet (AyBARRConj epoch digest)))

def AyBARRReuseGuard
    (dependencyContained : Prop) (epochMatch : Prop)
    (digestMatch : Prop) (checkerReplay : Prop)
    (originalFormula : Prop) :=
  AyBARRConj dependencyContained
    (AyBARRConj epochMatch
      (AyBARRConj digestMatch
        (AyBARRConj checkerReplay originalFormula)))

def AyBARRAcceptedReuse
    (artifact : Prop) (survivingFrame : Prop) (guard : Prop) :=
  AyBARRConj artifact (AyBARRConj survivingFrame guard)

def AyBARROutcome (model : Prop) (conflict : Prop) :=
  AyBARRDisj model conflict

def AyBARRPublicReport (outcome : Prop) (survivingFrame : Prop) :=
  AyBARRConj outcome survivingFrame

def AyBARRAcceptedReport (reuse : Prop) (public : Prop) :=
  AyBARRConj reuse public

def AyBARRNoClaim (diagnostic : Prop) (fallbackPublic : Prop) :=
  AyBARRConj fallbackPublic diagnostic

theorem ay_barr_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyBARRConj left right :=
  fun leftH rightH result build =>
    build leftH rightH

theorem ay_barr_conj_left
    (left : Prop) (right : Prop) :
    AyBARRConj left right -> left :=
  fun both =>
    both left (fun leftH _rightH => leftH)

theorem ay_barr_conj_right
    (left : Prop) (right : Prop) :
    AyBARRConj left right -> right :=
  fun both =>
    both right (fun _leftH rightH => rightH)

theorem ay_barr_disj_left
    (left : Prop) (right : Prop) :
    left -> AyBARRDisj left right :=
  fun leftH result leftCase _rightCase =>
    leftCase leftH

theorem ay_barr_disj_right
    (left : Prop) (right : Prop) :
    right -> AyBARRDisj left right :=
  fun rightH result _leftCase rightCase =>
    rightCase rightH

theorem ay_barr_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyBARREquisat before after :=
  fun forward backward =>
    ay_barr_conj_intro (before -> after) (after -> before)
      forward backward

theorem ay_barr_equisat_forward
    (before : Prop) (after : Prop) :
    AyBARREquisat before after -> before -> after :=
  fun equisat =>
    ay_barr_conj_left (before -> after) (after -> before) equisat

theorem ay_barr_equisat_backward
    (before : Prop) (after : Prop) :
    AyBARREquisat before after -> after -> before :=
  fun equisat =>
    ay_barr_conj_right (before -> after) (after -> before) equisat

theorem ay_barr_frame_intro
    (base : Prop) (assumption : Prop) :
    base -> assumption -> AyBARRFrame base assumption :=
  fun baseH assumptionH =>
    ay_barr_conj_intro base assumption baseH assumptionH

theorem ay_barr_frame_base
    (base : Prop) (assumption : Prop) :
    AyBARRFrame base assumption -> base :=
  fun frame =>
    ay_barr_conj_left base assumption frame

theorem ay_barr_frame_assumption
    (base : Prop) (assumption : Prop) :
    AyBARRFrame base assumption -> assumption :=
  fun frame =>
    ay_barr_conj_right base assumption frame

theorem ay_barr_state_under_assumption
    (formula : Prop) (base : Prop) (assumption : Prop) :
    AyBARRState formula base ->
    assumption ->
    AyBARRState formula (AyBARRFrame base assumption) :=
  fun state assumptionH =>
    ay_barr_conj_intro formula (AyBARRFrame base assumption)
      (ay_barr_conj_left formula base state)
      (ay_barr_frame_intro base assumption
        (ay_barr_conj_right formula base state)
        assumptionH)

theorem ay_barr_rollback_to_base
    (formula : Prop) (base : Prop) (assumption : Prop) :
    AyBARRState formula (AyBARRFrame base assumption) ->
    AyBARRState formula base :=
  fun state =>
    ay_barr_conj_intro formula base
      (ay_barr_conj_left formula (AyBARRFrame base assumption) state)
      (ay_barr_frame_base base assumption
        (ay_barr_conj_right formula (AyBARRFrame base assumption) state))

theorem ay_barr_preprocess_transport
    (original : Prop) (preprocessed : Prop) (frame : Prop) :
    AyBARREquisat original preprocessed ->
    AyBARRState original frame ->
    AyBARRState preprocessed frame :=
  fun equisat state =>
    ay_barr_conj_intro preprocessed frame
      (ay_barr_equisat_forward original preprocessed equisat
        (ay_barr_conj_left original frame state))
      (ay_barr_conj_right original frame state)

theorem ay_barr_retained_artifact_intro
    (learnedClause : Prop) (guidance : Prop)
    (dependencySet : Prop) (epoch : Prop) (digest : Prop) :
    learnedClause ->
    guidance ->
    dependencySet ->
    epoch ->
    digest ->
    AyBARRRetainedArtifact learnedClause guidance dependencySet
      epoch digest :=
  fun learnedH guidanceH dependencyH epochH digestH =>
    ay_barr_conj_intro learnedClause
      (AyBARRConj guidance
        (AyBARRConj dependencySet (AyBARRConj epoch digest)))
      learnedH
      (ay_barr_conj_intro guidance
        (AyBARRConj dependencySet (AyBARRConj epoch digest))
        guidanceH
        (ay_barr_conj_intro dependencySet
          (AyBARRConj epoch digest)
          dependencyH
          (ay_barr_conj_intro epoch digest epochH digestH)))

theorem ay_barr_retained_artifact_learned
    (learnedClause : Prop) (guidance : Prop)
    (dependencySet : Prop) (epoch : Prop) (digest : Prop) :
    AyBARRRetainedArtifact learnedClause guidance dependencySet
      epoch digest ->
    learnedClause :=
  fun artifact =>
    ay_barr_conj_left learnedClause
      (AyBARRConj guidance
        (AyBARRConj dependencySet (AyBARRConj epoch digest)))
      artifact

theorem ay_barr_retained_artifact_tail
    (learnedClause : Prop) (guidance : Prop)
    (dependencySet : Prop) (epoch : Prop) (digest : Prop) :
    AyBARRRetainedArtifact learnedClause guidance dependencySet
      epoch digest ->
    AyBARRConj guidance
      (AyBARRConj dependencySet (AyBARRConj epoch digest)) :=
  fun artifact =>
    ay_barr_conj_right learnedClause
      (AyBARRConj guidance
        (AyBARRConj dependencySet (AyBARRConj epoch digest)))
      artifact

theorem ay_barr_retained_artifact_guidance
    (learnedClause : Prop) (guidance : Prop)
    (dependencySet : Prop) (epoch : Prop) (digest : Prop) :
    AyBARRRetainedArtifact learnedClause guidance dependencySet
      epoch digest ->
    guidance :=
  fun artifact =>
    ay_barr_conj_left guidance
      (AyBARRConj dependencySet (AyBARRConj epoch digest))
      (ay_barr_retained_artifact_tail learnedClause guidance
        dependencySet epoch digest artifact)

theorem ay_barr_retained_artifact_dependency
    (learnedClause : Prop) (guidance : Prop)
    (dependencySet : Prop) (epoch : Prop) (digest : Prop) :
    AyBARRRetainedArtifact learnedClause guidance dependencySet
      epoch digest ->
    dependencySet :=
  fun artifact =>
    ay_barr_conj_left dependencySet (AyBARRConj epoch digest)
      (ay_barr_conj_right guidance
        (AyBARRConj dependencySet (AyBARRConj epoch digest))
        (ay_barr_retained_artifact_tail learnedClause guidance
          dependencySet epoch digest artifact))

theorem ay_barr_retained_artifact_epoch
    (learnedClause : Prop) (guidance : Prop)
    (dependencySet : Prop) (epoch : Prop) (digest : Prop) :
    AyBARRRetainedArtifact learnedClause guidance dependencySet
      epoch digest ->
    epoch :=
  fun artifact =>
    ay_barr_conj_left epoch digest
      (ay_barr_conj_right dependencySet (AyBARRConj epoch digest)
        (ay_barr_conj_right guidance
          (AyBARRConj dependencySet (AyBARRConj epoch digest))
          (ay_barr_retained_artifact_tail learnedClause guidance
            dependencySet epoch digest artifact)))

theorem ay_barr_retained_artifact_digest
    (learnedClause : Prop) (guidance : Prop)
    (dependencySet : Prop) (epoch : Prop) (digest : Prop) :
    AyBARRRetainedArtifact learnedClause guidance dependencySet
      epoch digest ->
    digest :=
  fun artifact =>
    ay_barr_conj_right epoch digest
      (ay_barr_conj_right dependencySet (AyBARRConj epoch digest)
        (ay_barr_conj_right guidance
          (AyBARRConj dependencySet (AyBARRConj epoch digest))
          (ay_barr_retained_artifact_tail learnedClause guidance
            dependencySet epoch digest artifact)))

theorem ay_barr_reuse_guard_intro
    (dependencyContained : Prop) (epochMatch : Prop)
    (digestMatch : Prop) (checkerReplay : Prop)
    (originalFormula : Prop) :
    dependencyContained ->
    epochMatch ->
    digestMatch ->
    checkerReplay ->
    originalFormula ->
    AyBARRReuseGuard dependencyContained epochMatch digestMatch
      checkerReplay originalFormula :=
  fun dependencyH epochH digestH replayH formulaH =>
    ay_barr_conj_intro dependencyContained
      (AyBARRConj epochMatch
        (AyBARRConj digestMatch
          (AyBARRConj checkerReplay originalFormula)))
      dependencyH
      (ay_barr_conj_intro epochMatch
        (AyBARRConj digestMatch
          (AyBARRConj checkerReplay originalFormula))
        epochH
        (ay_barr_conj_intro digestMatch
          (AyBARRConj checkerReplay originalFormula)
          digestH
          (ay_barr_conj_intro checkerReplay originalFormula
            replayH formulaH)))

theorem ay_barr_reuse_guard_dependency
    (dependencyContained : Prop) (epochMatch : Prop)
    (digestMatch : Prop) (checkerReplay : Prop)
    (originalFormula : Prop) :
    AyBARRReuseGuard dependencyContained epochMatch digestMatch
      checkerReplay originalFormula ->
    dependencyContained :=
  fun guard =>
    ay_barr_conj_left dependencyContained
      (AyBARRConj epochMatch
        (AyBARRConj digestMatch
          (AyBARRConj checkerReplay originalFormula)))
      guard

theorem ay_barr_reuse_guard_tail
    (dependencyContained : Prop) (epochMatch : Prop)
    (digestMatch : Prop) (checkerReplay : Prop)
    (originalFormula : Prop) :
    AyBARRReuseGuard dependencyContained epochMatch digestMatch
      checkerReplay originalFormula ->
    AyBARRConj epochMatch
      (AyBARRConj digestMatch
        (AyBARRConj checkerReplay originalFormula)) :=
  fun guard =>
    ay_barr_conj_right dependencyContained
      (AyBARRConj epochMatch
        (AyBARRConj digestMatch
          (AyBARRConj checkerReplay originalFormula)))
      guard

theorem ay_barr_reuse_guard_epoch
    (dependencyContained : Prop) (epochMatch : Prop)
    (digestMatch : Prop) (checkerReplay : Prop)
    (originalFormula : Prop) :
    AyBARRReuseGuard dependencyContained epochMatch digestMatch
      checkerReplay originalFormula ->
    epochMatch :=
  fun guard =>
    ay_barr_conj_left epochMatch
      (AyBARRConj digestMatch
        (AyBARRConj checkerReplay originalFormula))
      (ay_barr_reuse_guard_tail dependencyContained epochMatch
        digestMatch checkerReplay originalFormula guard)

theorem ay_barr_reuse_guard_digest
    (dependencyContained : Prop) (epochMatch : Prop)
    (digestMatch : Prop) (checkerReplay : Prop)
    (originalFormula : Prop) :
    AyBARRReuseGuard dependencyContained epochMatch digestMatch
      checkerReplay originalFormula ->
    digestMatch :=
  fun guard =>
    ay_barr_conj_left digestMatch
      (AyBARRConj checkerReplay originalFormula)
      (ay_barr_conj_right epochMatch
        (AyBARRConj digestMatch
          (AyBARRConj checkerReplay originalFormula))
        (ay_barr_reuse_guard_tail dependencyContained epochMatch
          digestMatch checkerReplay originalFormula guard))

theorem ay_barr_reuse_guard_replay
    (dependencyContained : Prop) (epochMatch : Prop)
    (digestMatch : Prop) (checkerReplay : Prop)
    (originalFormula : Prop) :
    AyBARRReuseGuard dependencyContained epochMatch digestMatch
      checkerReplay originalFormula ->
    checkerReplay :=
  fun guard =>
    ay_barr_conj_left checkerReplay originalFormula
      (ay_barr_conj_right digestMatch
        (AyBARRConj checkerReplay originalFormula)
        (ay_barr_conj_right epochMatch
          (AyBARRConj digestMatch
            (AyBARRConj checkerReplay originalFormula))
          (ay_barr_reuse_guard_tail dependencyContained epochMatch
            digestMatch checkerReplay originalFormula guard)))

theorem ay_barr_reuse_guard_formula
    (dependencyContained : Prop) (epochMatch : Prop)
    (digestMatch : Prop) (checkerReplay : Prop)
    (originalFormula : Prop) :
    AyBARRReuseGuard dependencyContained epochMatch digestMatch
      checkerReplay originalFormula ->
    originalFormula :=
  fun guard =>
    ay_barr_conj_right checkerReplay originalFormula
      (ay_barr_conj_right digestMatch
        (AyBARRConj checkerReplay originalFormula)
        (ay_barr_conj_right epochMatch
          (AyBARRConj digestMatch
            (AyBARRConj checkerReplay originalFormula))
          (ay_barr_reuse_guard_tail dependencyContained epochMatch
            digestMatch checkerReplay originalFormula guard)))

theorem ay_barr_accepted_reuse_intro
    (artifact : Prop) (survivingFrame : Prop) (guard : Prop) :
    artifact ->
    survivingFrame ->
    guard ->
    AyBARRAcceptedReuse artifact survivingFrame guard :=
  fun artifactH frameH guardH =>
    ay_barr_conj_intro artifact (AyBARRConj survivingFrame guard)
      artifactH
      (ay_barr_conj_intro survivingFrame guard frameH guardH)

theorem ay_barr_accepted_reuse_artifact
    (artifact : Prop) (survivingFrame : Prop) (guard : Prop) :
    AyBARRAcceptedReuse artifact survivingFrame guard -> artifact :=
  fun reuse =>
    ay_barr_conj_left artifact (AyBARRConj survivingFrame guard)
      reuse

theorem ay_barr_accepted_reuse_frame
    (artifact : Prop) (survivingFrame : Prop) (guard : Prop) :
    AyBARRAcceptedReuse artifact survivingFrame guard -> survivingFrame :=
  fun reuse =>
    ay_barr_conj_left survivingFrame guard
      (ay_barr_conj_right artifact (AyBARRConj survivingFrame guard)
        reuse)

theorem ay_barr_accepted_reuse_guard
    (artifact : Prop) (survivingFrame : Prop) (guard : Prop) :
    AyBARRAcceptedReuse artifact survivingFrame guard -> guard :=
  fun reuse =>
    ay_barr_conj_right survivingFrame guard
      (ay_barr_conj_right artifact (AyBARRConj survivingFrame guard)
        reuse)

theorem ay_barr_public_sat_report
    (model : Prop) (conflict : Prop) (survivingFrame : Prop) :
    model ->
    survivingFrame ->
    AyBARRPublicReport (AyBARROutcome model conflict)
      survivingFrame :=
  fun modelH frameH =>
    ay_barr_conj_intro (AyBARROutcome model conflict) survivingFrame
      (ay_barr_disj_left model conflict modelH)
      frameH

theorem ay_barr_public_unsat_report
    (model : Prop) (conflict : Prop) (survivingFrame : Prop) :
    conflict ->
    survivingFrame ->
    AyBARRPublicReport (AyBARROutcome model conflict)
      survivingFrame :=
  fun conflictH frameH =>
    ay_barr_conj_intro (AyBARROutcome model conflict) survivingFrame
      (ay_barr_disj_right model conflict conflictH)
      frameH

theorem ay_barr_accepted_report_intro
    (reuse : Prop) (public : Prop) :
    reuse -> public -> AyBARRAcceptedReport reuse public :=
  fun reuseH publicH =>
    ay_barr_conj_intro reuse public reuseH publicH

theorem ay_barr_accepted_report_reuse
    (reuse : Prop) (public : Prop) :
    AyBARRAcceptedReport reuse public -> reuse :=
  fun report =>
    ay_barr_conj_left reuse public report

theorem ay_barr_accepted_report_public
    (reuse : Prop) (public : Prop) :
    AyBARRAcceptedReport reuse public -> public :=
  fun report =>
    ay_barr_conj_right reuse public report

theorem ay_barr_no_claim_intro
    (diagnostic : Prop) (fallbackPublic : Prop) :
    diagnostic ->
    fallbackPublic ->
    AyBARRNoClaim diagnostic fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_barr_conj_intro fallbackPublic diagnostic fallbackH diagnosticH

theorem ay_barr_no_claim_preserves_fallback
    (diagnostic : Prop) (fallbackPublic : Prop) :
    AyBARRNoClaim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim =>
    ay_barr_conj_left fallbackPublic diagnostic noClaim

theorem ay_barr_dependency_escape_no_claim
    (dependencyEscapes : Prop) (fallbackPublic : Prop) :
    dependencyEscapes ->
    fallbackPublic ->
    AyBARRNoClaim dependencyEscapes fallbackPublic :=
  fun escapeH fallbackH =>
    ay_barr_no_claim_intro dependencyEscapes fallbackPublic
      escapeH fallbackH

theorem ay_barr_epoch_mismatch_no_claim
    (epochMismatch : Prop) (fallbackPublic : Prop) :
    epochMismatch ->
    fallbackPublic ->
    AyBARRNoClaim epochMismatch fallbackPublic :=
  fun mismatchH fallbackH =>
    ay_barr_no_claim_intro epochMismatch fallbackPublic
      mismatchH fallbackH

theorem ay_barr_digest_mismatch_no_claim
    (digestMismatch : Prop) (fallbackPublic : Prop) :
    digestMismatch ->
    fallbackPublic ->
    AyBARRNoClaim digestMismatch fallbackPublic :=
  fun mismatchH fallbackH =>
    ay_barr_no_claim_intro digestMismatch fallbackPublic
      mismatchH fallbackH

theorem ay_barr_replay_missing_no_claim
    (replayMissing : Prop) (fallbackPublic : Prop) :
    replayMissing ->
    fallbackPublic ->
    AyBARRNoClaim replayMissing fallbackPublic :=
  fun missingH fallbackH =>
    ay_barr_no_claim_intro replayMissing fallbackPublic
      missingH fallbackH

theorem ay_barr_matching_reuse_guides_sat
    (learnedClause : Prop) (guidance : Prop)
    (dependencySet : Prop) (epoch : Prop) (digest : Prop)
    (survivingFrame : Prop) (dependencyContained : Prop)
    (epochMatch : Prop) (digestMatch : Prop)
    (checkerReplay : Prop) (originalFormula : Prop)
    (model : Prop) (conflict : Prop) :
    AyBARRRetainedArtifact learnedClause guidance dependencySet
      epoch digest ->
    survivingFrame ->
    AyBARRReuseGuard dependencyContained epochMatch digestMatch
      checkerReplay originalFormula ->
    model ->
    AyBARRAcceptedReport
      (AyBARRAcceptedReuse
        (AyBARRRetainedArtifact learnedClause guidance dependencySet
          epoch digest)
        survivingFrame
        (AyBARRReuseGuard dependencyContained epochMatch digestMatch
          checkerReplay originalFormula))
      (AyBARRPublicReport (AyBARROutcome model conflict)
        survivingFrame) :=
  fun artifact frameH guard modelH =>
    ay_barr_accepted_report_intro
      (AyBARRAcceptedReuse
        (AyBARRRetainedArtifact learnedClause guidance dependencySet
          epoch digest)
        survivingFrame
        (AyBARRReuseGuard dependencyContained epochMatch digestMatch
          checkerReplay originalFormula))
      (AyBARRPublicReport (AyBARROutcome model conflict)
        survivingFrame)
      (ay_barr_accepted_reuse_intro
        (AyBARRRetainedArtifact learnedClause guidance dependencySet
          epoch digest)
        survivingFrame
        (AyBARRReuseGuard dependencyContained epochMatch digestMatch
          checkerReplay originalFormula)
        artifact frameH guard)
      (ay_barr_public_sat_report model conflict survivingFrame
        modelH frameH)

theorem ay_barr_matching_reuse_guides_unsat
    (learnedClause : Prop) (guidance : Prop)
    (dependencySet : Prop) (epoch : Prop) (digest : Prop)
    (survivingFrame : Prop) (dependencyContained : Prop)
    (epochMatch : Prop) (digestMatch : Prop)
    (checkerReplay : Prop) (originalFormula : Prop)
    (model : Prop) (conflict : Prop) :
    AyBARRRetainedArtifact learnedClause guidance dependencySet
      epoch digest ->
    survivingFrame ->
    AyBARRReuseGuard dependencyContained epochMatch digestMatch
      checkerReplay originalFormula ->
    conflict ->
    AyBARRAcceptedReport
      (AyBARRAcceptedReuse
        (AyBARRRetainedArtifact learnedClause guidance dependencySet
          epoch digest)
        survivingFrame
        (AyBARRReuseGuard dependencyContained epochMatch digestMatch
          checkerReplay originalFormula))
      (AyBARRPublicReport (AyBARROutcome model conflict)
        survivingFrame) :=
  fun artifact frameH guard conflictH =>
    ay_barr_accepted_report_intro
      (AyBARRAcceptedReuse
        (AyBARRRetainedArtifact learnedClause guidance dependencySet
          epoch digest)
        survivingFrame
        (AyBARRReuseGuard dependencyContained epochMatch digestMatch
          checkerReplay originalFormula))
      (AyBARRPublicReport (AyBARROutcome model conflict)
        survivingFrame)
      (ay_barr_accepted_reuse_intro
        (AyBARRRetainedArtifact learnedClause guidance dependencySet
          epoch digest)
        survivingFrame
        (AyBARRReuseGuard dependencyContained epochMatch digestMatch
          checkerReplay originalFormula)
        artifact frameH guard)
      (ay_barr_public_unsat_report model conflict survivingFrame
        conflictH frameH)

theorem ay_barr_accepted_reuse_report_soundness
    (learnedClause : Prop) (guidance : Prop)
    (dependencySet : Prop) (epoch : Prop) (digest : Prop)
    (survivingFrame : Prop) (dependencyContained : Prop)
    (epochMatch : Prop) (digestMatch : Prop)
    (checkerReplay : Prop) (originalFormula : Prop)
    (model : Prop) (conflict : Prop) :
    AyBARRAcceptedReport
      (AyBARRAcceptedReuse
        (AyBARRRetainedArtifact learnedClause guidance dependencySet
          epoch digest)
        survivingFrame
        (AyBARRReuseGuard dependencyContained epochMatch digestMatch
          checkerReplay originalFormula))
      (AyBARRPublicReport (AyBARROutcome model conflict)
        survivingFrame) ->
    AyBARRPublicReport (AyBARROutcome model conflict)
      survivingFrame :=
  fun report =>
    ay_barr_accepted_report_public
      (AyBARRAcceptedReuse
        (AyBARRRetainedArtifact learnedClause guidance dependencySet
          epoch digest)
        survivingFrame
        (AyBARRReuseGuard dependencyContained epochMatch digestMatch
          checkerReplay originalFormula))
      (AyBARRPublicReport (AyBARROutcome model conflict)
        survivingFrame)
      report

theorem ay_barr_no_claim_recompute_preserves_soundness
    (diagnostic : Prop) (fallbackPublic : Prop) :
    AyBARRNoClaim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim =>
    ay_barr_no_claim_preserves_fallback diagnostic fallbackPublic noClaim
