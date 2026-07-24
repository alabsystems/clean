-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded conflict-clause export guard soundness skeleton for ay SAT solving.
-- A learned conflict clause may be exported to branching, restart, or proof
-- consumers only when derivation, asserting literal, backjump level, metadata,
-- deterministic replay, dependency guard, and public soundness guard agree.

def ay_bceg_conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_bceg_disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_bceg_equisat (before : Prop) (after : Prop) :=
  ay_bceg_conj (before -> after) (after -> before)

def ay_bceg_export_evidence
    (derivationDependencies : Prop) (assertingLiteral : Prop)
    (backjumpLevel : Prop) (lbdActivityMetadata : Prop)
    (deterministicReplay : Prop) (dependencyGuard : Prop)
    (publicSoundnessGuard : Prop) :=
  ay_bceg_conj derivationDependencies
    (ay_bceg_conj assertingLiteral
      (ay_bceg_conj backjumpLevel
        (ay_bceg_conj lbdActivityMetadata
          (ay_bceg_conj deterministicReplay
            (ay_bceg_conj dependencyGuard publicSoundnessGuard)))))

def ay_bceg_export_agreement
    (derivationMatch : Prop) (assertingLiteralMatch : Prop)
    (backjumpLevelMatch : Prop) (metadataMatch : Prop)
    (replayMatch : Prop) (dependencyMatch : Prop)
    (publicGuardMatch : Prop) :=
  ay_bceg_conj derivationMatch
    (ay_bceg_conj assertingLiteralMatch
      (ay_bceg_conj backjumpLevelMatch
        (ay_bceg_conj metadataMatch
          (ay_bceg_conj replayMatch
            (ay_bceg_conj dependencyMatch publicGuardMatch)))))

def ay_bceg_accepted_export
    (evidence : Prop) (agreement : Prop) (exportHint : Prop) :=
  ay_bceg_conj evidence (ay_bceg_conj agreement exportHint)

def ay_bceg_outcome (model : Prop) (conflict : Prop) :=
  ay_bceg_disj model conflict

def ay_bceg_public_report (outcome : Prop) (formula : Prop) :=
  ay_bceg_conj outcome formula

def ay_bceg_accepted_report (exportCert : Prop) (public : Prop) :=
  ay_bceg_conj exportCert public

def ay_bceg_no_claim (diagnostic : Prop) (fallbackPublic : Prop) :=
  ay_bceg_conj fallbackPublic diagnostic

theorem ay_bceg_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_bceg_conj left right :=
  fun leftH rightH result build =>
    build leftH rightH

theorem ay_bceg_conj_left
    (left : Prop) (right : Prop) :
    ay_bceg_conj left right -> left :=
  fun both =>
    both left (fun leftH _rightH => leftH)

theorem ay_bceg_conj_right
    (left : Prop) (right : Prop) :
    ay_bceg_conj left right -> right :=
  fun both =>
    both right (fun _leftH rightH => rightH)

theorem ay_bceg_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_bceg_disj left right :=
  fun leftH result leftCase _rightCase =>
    leftCase leftH

theorem ay_bceg_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_bceg_disj left right :=
  fun rightH result _leftCase rightCase =>
    rightCase rightH

theorem ay_bceg_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    ay_bceg_equisat before after :=
  fun forward backward =>
    ay_bceg_conj_intro (before -> after) (after -> before)
      forward backward

theorem ay_bceg_equisat_forward
    (before : Prop) (after : Prop) :
    ay_bceg_equisat before after -> before -> after :=
  fun equisat =>
    ay_bceg_conj_left (before -> after) (after -> before) equisat

theorem ay_bceg_equisat_backward
    (before : Prop) (after : Prop) :
    ay_bceg_equisat before after -> after -> before :=
  fun equisat =>
    ay_bceg_conj_right (before -> after) (after -> before) equisat

theorem ay_bceg_export_evidence_intro
    (derivationDependencies : Prop) (assertingLiteral : Prop)
    (backjumpLevel : Prop) (lbdActivityMetadata : Prop)
    (deterministicReplay : Prop) (dependencyGuard : Prop)
    (publicSoundnessGuard : Prop) :
    derivationDependencies ->
    assertingLiteral ->
    backjumpLevel ->
    lbdActivityMetadata ->
    deterministicReplay ->
    dependencyGuard ->
    publicSoundnessGuard ->
    ay_bceg_export_evidence derivationDependencies assertingLiteral
      backjumpLevel lbdActivityMetadata deterministicReplay dependencyGuard
      publicSoundnessGuard :=
  fun derivationH assertingH levelH metadataH replayH dependencyH publicH =>
    ay_bceg_conj_intro derivationDependencies
      (ay_bceg_conj assertingLiteral
        (ay_bceg_conj backjumpLevel
          (ay_bceg_conj lbdActivityMetadata
            (ay_bceg_conj deterministicReplay
              (ay_bceg_conj dependencyGuard publicSoundnessGuard)))))
      derivationH
      (ay_bceg_conj_intro assertingLiteral
        (ay_bceg_conj backjumpLevel
          (ay_bceg_conj lbdActivityMetadata
            (ay_bceg_conj deterministicReplay
              (ay_bceg_conj dependencyGuard publicSoundnessGuard))))
        assertingH
        (ay_bceg_conj_intro backjumpLevel
          (ay_bceg_conj lbdActivityMetadata
            (ay_bceg_conj deterministicReplay
              (ay_bceg_conj dependencyGuard publicSoundnessGuard)))
          levelH
          (ay_bceg_conj_intro lbdActivityMetadata
            (ay_bceg_conj deterministicReplay
              (ay_bceg_conj dependencyGuard publicSoundnessGuard))
            metadataH
            (ay_bceg_conj_intro deterministicReplay
              (ay_bceg_conj dependencyGuard publicSoundnessGuard)
              replayH
              (ay_bceg_conj_intro dependencyGuard publicSoundnessGuard
                dependencyH publicH)))))

theorem ay_bceg_export_evidence_derivation
    (derivationDependencies : Prop) (assertingLiteral : Prop)
    (backjumpLevel : Prop) (lbdActivityMetadata : Prop)
    (deterministicReplay : Prop) (dependencyGuard : Prop)
    (publicSoundnessGuard : Prop) :
    ay_bceg_export_evidence derivationDependencies assertingLiteral
      backjumpLevel lbdActivityMetadata deterministicReplay dependencyGuard
      publicSoundnessGuard ->
    derivationDependencies :=
  fun evidence =>
    ay_bceg_conj_left derivationDependencies
      (ay_bceg_conj assertingLiteral
        (ay_bceg_conj backjumpLevel
          (ay_bceg_conj lbdActivityMetadata
            (ay_bceg_conj deterministicReplay
              (ay_bceg_conj dependencyGuard publicSoundnessGuard)))))
      evidence

theorem ay_bceg_export_evidence_tail
    (derivationDependencies : Prop) (assertingLiteral : Prop)
    (backjumpLevel : Prop) (lbdActivityMetadata : Prop)
    (deterministicReplay : Prop) (dependencyGuard : Prop)
    (publicSoundnessGuard : Prop) :
    ay_bceg_export_evidence derivationDependencies assertingLiteral
      backjumpLevel lbdActivityMetadata deterministicReplay dependencyGuard
      publicSoundnessGuard ->
    ay_bceg_conj assertingLiteral
      (ay_bceg_conj backjumpLevel
        (ay_bceg_conj lbdActivityMetadata
          (ay_bceg_conj deterministicReplay
            (ay_bceg_conj dependencyGuard publicSoundnessGuard)))) :=
  fun evidence =>
    ay_bceg_conj_right derivationDependencies
      (ay_bceg_conj assertingLiteral
        (ay_bceg_conj backjumpLevel
          (ay_bceg_conj lbdActivityMetadata
            (ay_bceg_conj deterministicReplay
              (ay_bceg_conj dependencyGuard publicSoundnessGuard)))))
      evidence

theorem ay_bceg_export_evidence_asserting_literal
    (derivationDependencies : Prop) (assertingLiteral : Prop)
    (backjumpLevel : Prop) (lbdActivityMetadata : Prop)
    (deterministicReplay : Prop) (dependencyGuard : Prop)
    (publicSoundnessGuard : Prop) :
    ay_bceg_export_evidence derivationDependencies assertingLiteral
      backjumpLevel lbdActivityMetadata deterministicReplay dependencyGuard
      publicSoundnessGuard ->
    assertingLiteral :=
  fun evidence =>
    ay_bceg_conj_left assertingLiteral
      (ay_bceg_conj backjumpLevel
        (ay_bceg_conj lbdActivityMetadata
          (ay_bceg_conj deterministicReplay
            (ay_bceg_conj dependencyGuard publicSoundnessGuard))))
      (ay_bceg_export_evidence_tail derivationDependencies assertingLiteral
        backjumpLevel lbdActivityMetadata deterministicReplay dependencyGuard
        publicSoundnessGuard evidence)

theorem ay_bceg_export_evidence_after_asserting
    (derivationDependencies : Prop) (assertingLiteral : Prop)
    (backjumpLevel : Prop) (lbdActivityMetadata : Prop)
    (deterministicReplay : Prop) (dependencyGuard : Prop)
    (publicSoundnessGuard : Prop) :
    ay_bceg_export_evidence derivationDependencies assertingLiteral
      backjumpLevel lbdActivityMetadata deterministicReplay dependencyGuard
      publicSoundnessGuard ->
    ay_bceg_conj backjumpLevel
      (ay_bceg_conj lbdActivityMetadata
        (ay_bceg_conj deterministicReplay
          (ay_bceg_conj dependencyGuard publicSoundnessGuard))) :=
  fun evidence =>
    ay_bceg_conj_right assertingLiteral
      (ay_bceg_conj backjumpLevel
        (ay_bceg_conj lbdActivityMetadata
          (ay_bceg_conj deterministicReplay
            (ay_bceg_conj dependencyGuard publicSoundnessGuard))))
      (ay_bceg_export_evidence_tail derivationDependencies assertingLiteral
        backjumpLevel lbdActivityMetadata deterministicReplay dependencyGuard
        publicSoundnessGuard evidence)

theorem ay_bceg_export_evidence_backjump_level
    (derivationDependencies : Prop) (assertingLiteral : Prop)
    (backjumpLevel : Prop) (lbdActivityMetadata : Prop)
    (deterministicReplay : Prop) (dependencyGuard : Prop)
    (publicSoundnessGuard : Prop) :
    ay_bceg_export_evidence derivationDependencies assertingLiteral
      backjumpLevel lbdActivityMetadata deterministicReplay dependencyGuard
      publicSoundnessGuard ->
    backjumpLevel :=
  fun evidence =>
    ay_bceg_conj_left backjumpLevel
      (ay_bceg_conj lbdActivityMetadata
        (ay_bceg_conj deterministicReplay
          (ay_bceg_conj dependencyGuard publicSoundnessGuard)))
      (ay_bceg_export_evidence_after_asserting derivationDependencies
        assertingLiteral backjumpLevel lbdActivityMetadata deterministicReplay
        dependencyGuard publicSoundnessGuard evidence)

theorem ay_bceg_export_evidence_after_level
    (derivationDependencies : Prop) (assertingLiteral : Prop)
    (backjumpLevel : Prop) (lbdActivityMetadata : Prop)
    (deterministicReplay : Prop) (dependencyGuard : Prop)
    (publicSoundnessGuard : Prop) :
    ay_bceg_export_evidence derivationDependencies assertingLiteral
      backjumpLevel lbdActivityMetadata deterministicReplay dependencyGuard
      publicSoundnessGuard ->
    ay_bceg_conj lbdActivityMetadata
      (ay_bceg_conj deterministicReplay
        (ay_bceg_conj dependencyGuard publicSoundnessGuard)) :=
  fun evidence =>
    ay_bceg_conj_right backjumpLevel
      (ay_bceg_conj lbdActivityMetadata
        (ay_bceg_conj deterministicReplay
          (ay_bceg_conj dependencyGuard publicSoundnessGuard)))
      (ay_bceg_export_evidence_after_asserting derivationDependencies
        assertingLiteral backjumpLevel lbdActivityMetadata deterministicReplay
        dependencyGuard publicSoundnessGuard evidence)

theorem ay_bceg_export_evidence_metadata
    (derivationDependencies : Prop) (assertingLiteral : Prop)
    (backjumpLevel : Prop) (lbdActivityMetadata : Prop)
    (deterministicReplay : Prop) (dependencyGuard : Prop)
    (publicSoundnessGuard : Prop) :
    ay_bceg_export_evidence derivationDependencies assertingLiteral
      backjumpLevel lbdActivityMetadata deterministicReplay dependencyGuard
      publicSoundnessGuard ->
    lbdActivityMetadata :=
  fun evidence =>
    ay_bceg_conj_left lbdActivityMetadata
      (ay_bceg_conj deterministicReplay
        (ay_bceg_conj dependencyGuard publicSoundnessGuard))
      (ay_bceg_export_evidence_after_level derivationDependencies
        assertingLiteral backjumpLevel lbdActivityMetadata deterministicReplay
        dependencyGuard publicSoundnessGuard evidence)

theorem ay_bceg_export_evidence_after_metadata
    (derivationDependencies : Prop) (assertingLiteral : Prop)
    (backjumpLevel : Prop) (lbdActivityMetadata : Prop)
    (deterministicReplay : Prop) (dependencyGuard : Prop)
    (publicSoundnessGuard : Prop) :
    ay_bceg_export_evidence derivationDependencies assertingLiteral
      backjumpLevel lbdActivityMetadata deterministicReplay dependencyGuard
      publicSoundnessGuard ->
    ay_bceg_conj deterministicReplay
      (ay_bceg_conj dependencyGuard publicSoundnessGuard) :=
  fun evidence =>
    ay_bceg_conj_right lbdActivityMetadata
      (ay_bceg_conj deterministicReplay
        (ay_bceg_conj dependencyGuard publicSoundnessGuard))
      (ay_bceg_export_evidence_after_level derivationDependencies
        assertingLiteral backjumpLevel lbdActivityMetadata deterministicReplay
        dependencyGuard publicSoundnessGuard evidence)

theorem ay_bceg_export_evidence_replay
    (derivationDependencies : Prop) (assertingLiteral : Prop)
    (backjumpLevel : Prop) (lbdActivityMetadata : Prop)
    (deterministicReplay : Prop) (dependencyGuard : Prop)
    (publicSoundnessGuard : Prop) :
    ay_bceg_export_evidence derivationDependencies assertingLiteral
      backjumpLevel lbdActivityMetadata deterministicReplay dependencyGuard
      publicSoundnessGuard ->
    deterministicReplay :=
  fun evidence =>
    ay_bceg_conj_left deterministicReplay
      (ay_bceg_conj dependencyGuard publicSoundnessGuard)
      (ay_bceg_export_evidence_after_metadata derivationDependencies
        assertingLiteral backjumpLevel lbdActivityMetadata deterministicReplay
        dependencyGuard publicSoundnessGuard evidence)

theorem ay_bceg_export_evidence_dependency
    (derivationDependencies : Prop) (assertingLiteral : Prop)
    (backjumpLevel : Prop) (lbdActivityMetadata : Prop)
    (deterministicReplay : Prop) (dependencyGuard : Prop)
    (publicSoundnessGuard : Prop) :
    ay_bceg_export_evidence derivationDependencies assertingLiteral
      backjumpLevel lbdActivityMetadata deterministicReplay dependencyGuard
      publicSoundnessGuard ->
    dependencyGuard :=
  fun evidence =>
    ay_bceg_conj_left dependencyGuard publicSoundnessGuard
      (ay_bceg_conj_right deterministicReplay
        (ay_bceg_conj dependencyGuard publicSoundnessGuard)
        (ay_bceg_export_evidence_after_metadata derivationDependencies
          assertingLiteral backjumpLevel lbdActivityMetadata deterministicReplay
          dependencyGuard publicSoundnessGuard evidence))

theorem ay_bceg_export_evidence_public
    (derivationDependencies : Prop) (assertingLiteral : Prop)
    (backjumpLevel : Prop) (lbdActivityMetadata : Prop)
    (deterministicReplay : Prop) (dependencyGuard : Prop)
    (publicSoundnessGuard : Prop) :
    ay_bceg_export_evidence derivationDependencies assertingLiteral
      backjumpLevel lbdActivityMetadata deterministicReplay dependencyGuard
      publicSoundnessGuard ->
    publicSoundnessGuard :=
  fun evidence =>
    ay_bceg_conj_right dependencyGuard publicSoundnessGuard
      (ay_bceg_conj_right deterministicReplay
        (ay_bceg_conj dependencyGuard publicSoundnessGuard)
        (ay_bceg_export_evidence_after_metadata derivationDependencies
          assertingLiteral backjumpLevel lbdActivityMetadata deterministicReplay
          dependencyGuard publicSoundnessGuard evidence))

theorem ay_bceg_export_agreement_intro
    (derivationMatch : Prop) (assertingLiteralMatch : Prop)
    (backjumpLevelMatch : Prop) (metadataMatch : Prop)
    (replayMatch : Prop) (dependencyMatch : Prop)
    (publicGuardMatch : Prop) :
    derivationMatch ->
    assertingLiteralMatch ->
    backjumpLevelMatch ->
    metadataMatch ->
    replayMatch ->
    dependencyMatch ->
    publicGuardMatch ->
    ay_bceg_export_agreement derivationMatch assertingLiteralMatch
      backjumpLevelMatch metadataMatch replayMatch dependencyMatch
      publicGuardMatch :=
  fun derivationH assertingH levelH metadataH replayH dependencyH publicH =>
    ay_bceg_export_evidence_intro derivationMatch assertingLiteralMatch
      backjumpLevelMatch metadataMatch replayMatch dependencyMatch publicGuardMatch
      derivationH assertingH levelH metadataH replayH dependencyH publicH

theorem ay_bceg_export_agreement_derivation
    (derivationMatch : Prop) (assertingLiteralMatch : Prop)
    (backjumpLevelMatch : Prop) (metadataMatch : Prop)
    (replayMatch : Prop) (dependencyMatch : Prop)
    (publicGuardMatch : Prop) :
    ay_bceg_export_agreement derivationMatch assertingLiteralMatch
      backjumpLevelMatch metadataMatch replayMatch dependencyMatch
      publicGuardMatch ->
    derivationMatch :=
  fun agreement =>
    ay_bceg_export_evidence_derivation derivationMatch assertingLiteralMatch
      backjumpLevelMatch metadataMatch replayMatch dependencyMatch
      publicGuardMatch agreement

theorem ay_bceg_accepted_export_intro
    (evidence : Prop) (agreement : Prop) (exportHint : Prop) :
    evidence ->
    agreement ->
    exportHint ->
    ay_bceg_accepted_export evidence agreement exportHint :=
  fun evidenceH agreementH hintH =>
    ay_bceg_conj_intro evidence (ay_bceg_conj agreement exportHint)
      evidenceH
      (ay_bceg_conj_intro agreement exportHint agreementH hintH)

theorem ay_bceg_accepted_export_evidence
    (evidence : Prop) (agreement : Prop) (exportHint : Prop) :
    ay_bceg_accepted_export evidence agreement exportHint -> evidence :=
  fun accepted =>
    ay_bceg_conj_left evidence (ay_bceg_conj agreement exportHint) accepted

theorem ay_bceg_accepted_export_agreement
    (evidence : Prop) (agreement : Prop) (exportHint : Prop) :
    ay_bceg_accepted_export evidence agreement exportHint -> agreement :=
  fun accepted =>
    ay_bceg_conj_left agreement exportHint
      (ay_bceg_conj_right evidence (ay_bceg_conj agreement exportHint)
        accepted)

theorem ay_bceg_accepted_export_hint
    (evidence : Prop) (agreement : Prop) (exportHint : Prop) :
    ay_bceg_accepted_export evidence agreement exportHint -> exportHint :=
  fun accepted =>
    ay_bceg_conj_right agreement exportHint
      (ay_bceg_conj_right evidence (ay_bceg_conj agreement exportHint)
        accepted)

theorem ay_bceg_public_sat_report
    (model : Prop) (conflict : Prop) (formula : Prop) :
    model ->
    formula ->
    ay_bceg_public_report (ay_bceg_outcome model conflict) formula :=
  fun modelH formulaH =>
    ay_bceg_conj_intro (ay_bceg_outcome model conflict) formula
      (ay_bceg_disj_left model conflict modelH)
      formulaH

theorem ay_bceg_public_unsat_report
    (model : Prop) (conflict : Prop) (formula : Prop) :
    conflict ->
    formula ->
    ay_bceg_public_report (ay_bceg_outcome model conflict) formula :=
  fun conflictH formulaH =>
    ay_bceg_conj_intro (ay_bceg_outcome model conflict) formula
      (ay_bceg_disj_right model conflict conflictH)
      formulaH

theorem ay_bceg_accepted_report_intro
    (exportCert : Prop) (public : Prop) :
    exportCert ->
    public ->
    ay_bceg_accepted_report exportCert public :=
  fun exportCertH publicH =>
    ay_bceg_conj_intro exportCert public exportCertH publicH

theorem ay_bceg_accepted_report_public
    (exportCert : Prop) (public : Prop) :
    ay_bceg_accepted_report exportCert public -> public :=
  fun accepted =>
    ay_bceg_conj_right exportCert public accepted

theorem ay_bceg_no_claim_intro
    (diagnostic : Prop) (fallbackPublic : Prop) :
    fallbackPublic ->
    diagnostic ->
    ay_bceg_no_claim diagnostic fallbackPublic :=
  fun fallbackH diagnosticH =>
    ay_bceg_conj_intro fallbackPublic diagnostic fallbackH diagnosticH

theorem ay_bceg_no_claim_preserves_fallback
    (diagnostic : Prop) (fallbackPublic : Prop) :
    ay_bceg_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim =>
    ay_bceg_conj_left fallbackPublic diagnostic noClaim

theorem ay_bceg_missing_derivation_no_claim
    (missingDerivation : Prop) (fallbackPublic : Prop) :
    missingDerivation ->
    fallbackPublic ->
    ay_bceg_no_claim missingDerivation fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bceg_no_claim_intro missingDerivation fallbackPublic
      fallbackH diagnosticH

theorem ay_bceg_stale_backjump_level_no_claim
    (staleLevel : Prop) (fallbackPublic : Prop) :
    staleLevel ->
    fallbackPublic ->
    ay_bceg_no_claim staleLevel fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bceg_no_claim_intro staleLevel fallbackPublic fallbackH diagnosticH

theorem ay_bceg_metadata_drift_no_claim
    (metadataDrift : Prop) (fallbackPublic : Prop) :
    metadataDrift ->
    fallbackPublic ->
    ay_bceg_no_claim metadataDrift fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bceg_no_claim_intro metadataDrift fallbackPublic fallbackH diagnosticH

theorem ay_bceg_replay_mismatch_no_claim
    (replayMismatch : Prop) (fallbackPublic : Prop) :
    replayMismatch ->
    fallbackPublic ->
    ay_bceg_no_claim replayMismatch fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bceg_no_claim_intro replayMismatch fallbackPublic fallbackH diagnosticH

theorem ay_bceg_guard_failure_no_claim
    (guardFailure : Prop) (fallbackPublic : Prop) :
    guardFailure ->
    fallbackPublic ->
    ay_bceg_no_claim guardFailure fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bceg_no_claim_intro guardFailure fallbackPublic fallbackH diagnosticH

theorem ay_bceg_bad_export_cannot_publish
    (diagnostic : Prop) (fallbackPublic : Prop) :
    ay_bceg_no_claim diagnostic fallbackPublic ->
    fallbackPublic :=
  fun noClaim =>
    ay_bceg_no_claim_preserves_fallback diagnostic fallbackPublic noClaim

theorem ay_bceg_accepted_export_guides_sat
    (evidence : Prop) (agreement : Prop) (exportHint : Prop)
    (model : Prop) (conflict : Prop) (formula : Prop) :
    ay_bceg_accepted_export evidence agreement exportHint ->
    model ->
    formula ->
    ay_bceg_accepted_report
      (ay_bceg_accepted_export evidence agreement exportHint)
      (ay_bceg_public_report (ay_bceg_outcome model conflict) formula) :=
  fun accepted modelH formulaH =>
    ay_bceg_accepted_report_intro
      (ay_bceg_accepted_export evidence agreement exportHint)
      (ay_bceg_public_report (ay_bceg_outcome model conflict) formula)
      accepted
      (ay_bceg_public_sat_report model conflict formula modelH formulaH)

theorem ay_bceg_accepted_export_guides_unsat
    (evidence : Prop) (agreement : Prop) (exportHint : Prop)
    (model : Prop) (conflict : Prop) (formula : Prop) :
    ay_bceg_accepted_export evidence agreement exportHint ->
    conflict ->
    formula ->
    ay_bceg_accepted_report
      (ay_bceg_accepted_export evidence agreement exportHint)
      (ay_bceg_public_report (ay_bceg_outcome model conflict) formula) :=
  fun accepted conflictH formulaH =>
    ay_bceg_accepted_report_intro
      (ay_bceg_accepted_export evidence agreement exportHint)
      (ay_bceg_public_report (ay_bceg_outcome model conflict) formula)
      accepted
      (ay_bceg_public_unsat_report model conflict formula conflictH formulaH)

theorem ay_bceg_accepted_export_report_soundness
    (exportCert : Prop) (public : Prop) :
    ay_bceg_accepted_report exportCert public -> public :=
  fun accepted =>
    ay_bceg_accepted_report_public exportCert public accepted

theorem ay_bceg_no_claim_recompute_preserves_soundness
    (diagnostic : Prop) (fallbackPublic : Prop) :
    ay_bceg_no_claim diagnostic fallbackPublic ->
    fallbackPublic :=
  fun noClaim =>
    ay_bceg_no_claim_preserves_fallback diagnostic fallbackPublic noClaim
