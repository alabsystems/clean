-- SAT-COMP validator audit Merkle-checkpoint core.
--
-- Checkpoint/resume verification keeps accepted SAT/UNSAT audit claims only
-- when retained membership witnesses and root agreement are present.  Failed
-- resumes are modeled as explicit no-claim diagnostics.

def AyAMCPConj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def AyAMCPDisj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyAMCPEquisat (before after : Prop) : Prop :=
  AyAMCPConj (before -> after) (after -> before)

def AyAMCPPublicResult (satFact unsatFact noClaim : Prop) : Prop :=
  AyAMCPDisj satFact (AyAMCPDisj unsatFact noClaim)

def AyAMCPArtifacts (certId archiveKey : Prop) : Prop :=
  AyAMCPConj certId archiveKey

def AyAMCPEntry
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    Prop :=
  AyAMCPConj exitCode
    (AyAMCPConj artifacts
      (AyAMCPConj checkerDecision
        (AyAMCPConj auditDigest diagnostic)))

def AyAMCPMembership (leafHash root entry : Prop) : Prop :=
  AyAMCPConj leafHash (AyAMCPConj root entry)

def AyAMCPCheckpoint
    (checkpointRoot checkpointDigest retainedClaims : Prop) : Prop :=
  AyAMCPConj checkpointRoot
    (AyAMCPConj checkpointDigest retainedClaims)

def AyAMCPResumedSuffix (suffEntries suffRoot suffTailDigest : Prop) : Prop :=
  AyAMCPConj suffEntries (AyAMCPConj suffRoot suffTailDigest)

def AyAMCPRootAgreement
    (checkpointRoot resumeBaseRoot finalRoot : Prop) : Prop :=
  AyAMCPConj checkpointRoot (AyAMCPConj resumeBaseRoot finalRoot)

def AyAMCPAppendOnly
    (checkpointLog resumedSuffix finalLog : Prop) : Prop :=
  AyAMCPConj checkpointLog (AyAMCPConj resumedSuffix finalLog)

def AyAMCPResumeWitness
    (checkpoint resumedSuffix rootAgreement appendOnly : Prop) : Prop :=
  AyAMCPConj checkpoint
    (AyAMCPConj resumedSuffix
      (AyAMCPConj rootAgreement appendOnly))

def AyAMCPNoClaim (reason auditDigest diagnostic : Prop) : Prop :=
  AyAMCPConj reason (AyAMCPConj auditDigest diagnostic)

def AyAMCPModel (formula assignment : Prop) : Prop :=
  AyAMCPConj formula assignment

def AyAMCPUnsat (formula : Prop) : Prop :=
  formula -> False

def AyAMCPVisibleSAT (original visibleAssignment : Prop) : Prop :=
  AyAMCPModel original visibleAssignment

def AyAMCPPreprocessArtifact (original solver : Prop) : Prop :=
  AyAMCPEquisat original solver

def AyAMCPReplayAccepted (solver stream finalClause : Prop) : Prop :=
  stream -> solver -> finalClause

theorem ay_amcp_conj_intro (left right : Prop) :
    left -> right -> AyAMCPConj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_amcp_conj_left (left right : Prop) :
    AyAMCPConj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_amcp_conj_right (left right : Prop) :
    AyAMCPConj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_amcp_disj_left (left right : Prop) :
    left -> AyAMCPDisj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_amcp_disj_right (left right : Prop) :
    right -> AyAMCPDisj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_amcp_equisat_forward (before after : Prop) :
    AyAMCPEquisat before after -> before -> after :=
  fun witness hbefore =>
    witness after (fun forward _backward => forward hbefore)

theorem ay_amcp_equisat_backward (before after : Prop) :
    AyAMCPEquisat before after -> after -> before :=
  fun witness hafter =>
    witness before (fun _forward backward => backward hafter)

theorem ay_amcp_model_intro (formula assignment : Prop) :
    formula -> assignment -> AyAMCPModel formula assignment :=
  fun formulaProof assignmentProof =>
    ay_amcp_conj_intro formula assignment formulaProof assignmentProof

theorem ay_amcp_model_formula (formula assignment : Prop) :
    AyAMCPModel formula assignment -> formula :=
  fun model => ay_amcp_conj_left formula assignment model

theorem ay_amcp_model_assignment (formula assignment : Prop) :
    AyAMCPModel formula assignment -> assignment :=
  fun model => ay_amcp_conj_right formula assignment model

theorem ay_amcp_entry_intro
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    exitCode -> artifacts -> checkerDecision -> auditDigest -> diagnostic ->
    AyAMCPEntry exitCode artifacts checkerDecision auditDigest diagnostic :=
  fun exitProof artifactsProof checkerProof auditProof diagnosticProof =>
    ay_amcp_conj_intro exitCode
      (AyAMCPConj artifacts
        (AyAMCPConj checkerDecision (AyAMCPConj auditDigest diagnostic)))
      exitProof
      (ay_amcp_conj_intro artifacts
        (AyAMCPConj checkerDecision (AyAMCPConj auditDigest diagnostic))
        artifactsProof
        (ay_amcp_conj_intro checkerDecision
          (AyAMCPConj auditDigest diagnostic)
          checkerProof
          (ay_amcp_conj_intro auditDigest diagnostic auditProof
            diagnosticProof)))

theorem ay_amcp_entry_checker
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    AyAMCPEntry exitCode artifacts checkerDecision auditDigest diagnostic ->
    checkerDecision :=
  fun entry =>
    ay_amcp_conj_right exitCode
      (AyAMCPConj artifacts
        (AyAMCPConj checkerDecision (AyAMCPConj auditDigest diagnostic)))
      entry checkerDecision
      (fun _artifactsProof tail =>
        tail checkerDecision (fun checkerProof _auditTail => checkerProof))

theorem ay_amcp_entry_audit
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    AyAMCPEntry exitCode artifacts checkerDecision auditDigest diagnostic ->
    auditDigest :=
  fun entry =>
    ay_amcp_conj_right exitCode
      (AyAMCPConj artifacts
        (AyAMCPConj checkerDecision (AyAMCPConj auditDigest diagnostic)))
      entry auditDigest
      (fun _artifactsProof tail =>
        tail auditDigest
          (fun _checkerProof auditTail =>
            auditTail auditDigest
              (fun auditProof _diagnosticProof => auditProof)))

theorem ay_amcp_entry_diagnostic
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    AyAMCPEntry exitCode artifacts checkerDecision auditDigest diagnostic ->
    diagnostic :=
  fun entry =>
    ay_amcp_conj_right exitCode
      (AyAMCPConj artifacts
        (AyAMCPConj checkerDecision (AyAMCPConj auditDigest diagnostic)))
      entry diagnostic
      (fun _artifactsProof tail =>
        tail diagnostic
          (fun _checkerProof auditTail =>
            auditTail diagnostic
              (fun _auditProof diagnosticProof => diagnosticProof)))

theorem ay_amcp_membership_intro (leafHash root entry : Prop) :
    leafHash -> root -> entry -> AyAMCPMembership leafHash root entry :=
  fun leafProof rootProof entryProof =>
    ay_amcp_conj_intro leafHash (AyAMCPConj root entry)
      leafProof
      (ay_amcp_conj_intro root entry rootProof entryProof)

theorem ay_amcp_membership_root (leafHash root entry : Prop) :
    AyAMCPMembership leafHash root entry -> root :=
  fun membership =>
    ay_amcp_conj_right leafHash (AyAMCPConj root entry) membership
      root (fun rootProof _entryProof => rootProof)

theorem ay_amcp_membership_entry (leafHash root entry : Prop) :
    AyAMCPMembership leafHash root entry -> entry :=
  fun membership =>
    ay_amcp_conj_right leafHash (AyAMCPConj root entry) membership
      entry (fun _rootProof entryProof => entryProof)

theorem ay_amcp_checkpoint_intro
    (checkpointRoot checkpointDigest retainedClaims : Prop) :
    checkpointRoot -> checkpointDigest -> retainedClaims ->
    AyAMCPCheckpoint checkpointRoot checkpointDigest retainedClaims :=
  fun rootProof digestProof claimsProof =>
    ay_amcp_conj_intro checkpointRoot
      (AyAMCPConj checkpointDigest retainedClaims)
      rootProof
      (ay_amcp_conj_intro checkpointDigest retainedClaims digestProof
        claimsProof)

theorem ay_amcp_checkpoint_root
    (checkpointRoot checkpointDigest retainedClaims : Prop) :
    AyAMCPCheckpoint checkpointRoot checkpointDigest retainedClaims ->
    checkpointRoot :=
  fun checkpoint =>
    ay_amcp_conj_left checkpointRoot
      (AyAMCPConj checkpointDigest retainedClaims) checkpoint

theorem ay_amcp_checkpoint_digest
    (checkpointRoot checkpointDigest retainedClaims : Prop) :
    AyAMCPCheckpoint checkpointRoot checkpointDigest retainedClaims ->
    checkpointDigest :=
  fun checkpoint =>
    ay_amcp_conj_right checkpointRoot
      (AyAMCPConj checkpointDigest retainedClaims)
      checkpoint checkpointDigest
      (fun digestProof _claimsProof => digestProof)

theorem ay_amcp_checkpoint_claims
    (checkpointRoot checkpointDigest retainedClaims : Prop) :
    AyAMCPCheckpoint checkpointRoot checkpointDigest retainedClaims ->
    retainedClaims :=
  fun checkpoint =>
    ay_amcp_conj_right checkpointRoot
      (AyAMCPConj checkpointDigest retainedClaims)
      checkpoint retainedClaims
      (fun _digestProof claimsProof => claimsProof)

theorem ay_amcp_resumed_suffix_intro
    (suffEntries suffRoot suffTailDigest : Prop) :
    suffEntries -> suffRoot -> suffTailDigest ->
    AyAMCPResumedSuffix suffEntries suffRoot suffTailDigest :=
  fun entriesProof rootProof tailProof =>
    ay_amcp_conj_intro suffEntries
      (AyAMCPConj suffRoot suffTailDigest)
      entriesProof
      (ay_amcp_conj_intro suffRoot suffTailDigest rootProof tailProof)

theorem ay_amcp_resumed_suffix_root
    (suffEntries suffRoot suffTailDigest : Prop) :
    AyAMCPResumedSuffix suffEntries suffRoot suffTailDigest -> suffRoot :=
  fun suff =>
    ay_amcp_conj_right suffEntries
      (AyAMCPConj suffRoot suffTailDigest)
      suff suffRoot (fun rootProof _tailProof => rootProof)

theorem ay_amcp_resumed_suffix_tail
    (suffEntries suffRoot suffTailDigest : Prop) :
    AyAMCPResumedSuffix suffEntries suffRoot suffTailDigest ->
    suffTailDigest :=
  fun suff =>
    ay_amcp_conj_right suffEntries
      (AyAMCPConj suffRoot suffTailDigest)
      suff suffTailDigest (fun _rootProof tailProof => tailProof)

theorem ay_amcp_root_agreement_intro
    (checkpointRoot resumeBaseRoot finalRoot : Prop) :
    checkpointRoot -> resumeBaseRoot -> finalRoot ->
    AyAMCPRootAgreement checkpointRoot resumeBaseRoot finalRoot :=
  fun checkpointProof baseProof finalProof =>
    ay_amcp_conj_intro checkpointRoot
      (AyAMCPConj resumeBaseRoot finalRoot)
      checkpointProof
      (ay_amcp_conj_intro resumeBaseRoot finalRoot baseProof finalProof)

theorem ay_amcp_root_agreement_checkpoint
    (checkpointRoot resumeBaseRoot finalRoot : Prop) :
    AyAMCPRootAgreement checkpointRoot resumeBaseRoot finalRoot ->
    checkpointRoot :=
  fun agreement =>
    ay_amcp_conj_left checkpointRoot
      (AyAMCPConj resumeBaseRoot finalRoot) agreement

theorem ay_amcp_root_agreement_resume_base
    (checkpointRoot resumeBaseRoot finalRoot : Prop) :
    AyAMCPRootAgreement checkpointRoot resumeBaseRoot finalRoot ->
    resumeBaseRoot :=
  fun agreement =>
    ay_amcp_conj_right checkpointRoot
      (AyAMCPConj resumeBaseRoot finalRoot)
      agreement resumeBaseRoot
      (fun baseProof _finalProof => baseProof)

theorem ay_amcp_root_agreement_final
    (checkpointRoot resumeBaseRoot finalRoot : Prop) :
    AyAMCPRootAgreement checkpointRoot resumeBaseRoot finalRoot ->
    finalRoot :=
  fun agreement =>
    ay_amcp_conj_right checkpointRoot
      (AyAMCPConj resumeBaseRoot finalRoot)
      agreement finalRoot
      (fun _baseProof finalProof => finalProof)

theorem ay_amcp_append_only_intro
    (checkpointLog resumedSuffix finalLog : Prop) :
    checkpointLog -> resumedSuffix -> finalLog ->
    AyAMCPAppendOnly checkpointLog resumedSuffix finalLog :=
  fun checkpointProof suffProof finalProof =>
    ay_amcp_conj_intro checkpointLog
      (AyAMCPConj resumedSuffix finalLog)
      checkpointProof
      (ay_amcp_conj_intro resumedSuffix finalLog suffProof finalProof)

theorem ay_amcp_append_only_checkpoint
    (checkpointLog resumedSuffix finalLog : Prop) :
    AyAMCPAppendOnly checkpointLog resumedSuffix finalLog ->
    checkpointLog :=
  fun appendOnly =>
    ay_amcp_conj_left checkpointLog
      (AyAMCPConj resumedSuffix finalLog) appendOnly

theorem ay_amcp_append_only_suffix
    (checkpointLog resumedSuffix finalLog : Prop) :
    AyAMCPAppendOnly checkpointLog resumedSuffix finalLog ->
    resumedSuffix :=
  fun appendOnly =>
    ay_amcp_conj_right checkpointLog
      (AyAMCPConj resumedSuffix finalLog)
      appendOnly resumedSuffix
      (fun suffProof _finalProof => suffProof)

theorem ay_amcp_append_only_final
    (checkpointLog resumedSuffix finalLog : Prop) :
    AyAMCPAppendOnly checkpointLog resumedSuffix finalLog ->
    finalLog :=
  fun appendOnly =>
    ay_amcp_conj_right checkpointLog
      (AyAMCPConj resumedSuffix finalLog)
      appendOnly finalLog
      (fun _suffProof finalProof => finalProof)

theorem ay_amcp_resume_witness_intro
    (checkpoint resumedSuffix rootAgreement appendOnly : Prop) :
    checkpoint -> resumedSuffix -> rootAgreement -> appendOnly ->
    AyAMCPResumeWitness checkpoint resumedSuffix rootAgreement appendOnly :=
  fun checkpointProof suffProof rootProof appendProof =>
    ay_amcp_conj_intro checkpoint
      (AyAMCPConj resumedSuffix
        (AyAMCPConj rootAgreement appendOnly))
      checkpointProof
      (ay_amcp_conj_intro resumedSuffix
        (AyAMCPConj rootAgreement appendOnly)
        suffProof
        (ay_amcp_conj_intro rootAgreement appendOnly rootProof
          appendProof))

theorem ay_amcp_resume_checkpoint
    (checkpoint resumedSuffix rootAgreement appendOnly : Prop) :
    AyAMCPResumeWitness checkpoint resumedSuffix rootAgreement appendOnly ->
    checkpoint :=
  fun witness =>
    ay_amcp_conj_left checkpoint
      (AyAMCPConj resumedSuffix
        (AyAMCPConj rootAgreement appendOnly))
      witness

theorem ay_amcp_resume_suffix
    (checkpoint resumedSuffix rootAgreement appendOnly : Prop) :
    AyAMCPResumeWitness checkpoint resumedSuffix rootAgreement appendOnly ->
    resumedSuffix :=
  fun witness =>
    ay_amcp_conj_right checkpoint
      (AyAMCPConj resumedSuffix
        (AyAMCPConj rootAgreement appendOnly))
      witness resumedSuffix
      (fun suffProof _tail => suffProof)

theorem ay_amcp_resume_root_agreement
    (checkpoint resumedSuffix rootAgreement appendOnly : Prop) :
    AyAMCPResumeWitness checkpoint resumedSuffix rootAgreement appendOnly ->
    rootAgreement :=
  fun witness =>
    ay_amcp_conj_right checkpoint
      (AyAMCPConj resumedSuffix
        (AyAMCPConj rootAgreement appendOnly))
      witness rootAgreement
      (fun _suffProof tail =>
        tail rootAgreement (fun rootProof _appendProof => rootProof))

theorem ay_amcp_resume_append_only
    (checkpoint resumedSuffix rootAgreement appendOnly : Prop) :
    AyAMCPResumeWitness checkpoint resumedSuffix rootAgreement appendOnly ->
    appendOnly :=
  fun witness =>
    ay_amcp_conj_right checkpoint
      (AyAMCPConj resumedSuffix
        (AyAMCPConj rootAgreement appendOnly))
      witness appendOnly
      (fun _suffProof tail =>
        tail appendOnly (fun _rootProof appendProof => appendProof))

theorem ay_amcp_no_claim_intro
    (reason auditDigest diagnostic : Prop) :
    reason -> auditDigest -> diagnostic ->
    AyAMCPNoClaim reason auditDigest diagnostic :=
  fun reasonProof auditProof diagnosticProof =>
    ay_amcp_conj_intro reason (AyAMCPConj auditDigest diagnostic)
      reasonProof
      (ay_amcp_conj_intro auditDigest diagnostic auditProof
        diagnosticProof)

theorem ay_amcp_preprocess_model_reconstruct
    (original solver internalAssignment visibleAssignment : Prop) :
    AyAMCPPreprocessArtifact original solver ->
    (internalAssignment -> visibleAssignment) ->
    AyAMCPModel solver internalAssignment ->
    AyAMCPVisibleSAT original visibleAssignment :=
  fun preprocess decode model =>
    ay_amcp_model_intro original visibleAssignment
      (ay_amcp_equisat_backward original solver preprocess
        (ay_amcp_model_formula solver internalAssignment model))
      (decode (ay_amcp_model_assignment solver internalAssignment model))

theorem ay_amcp_preprocess_unsat_reconstruct
    (original solver : Prop) :
    AyAMCPPreprocessArtifact original solver ->
    AyAMCPUnsat solver ->
    AyAMCPUnsat original :=
  fun preprocess solverUnsat originalProof =>
    solverUnsat
      (ay_amcp_equisat_forward original solver preprocess originalProof)

theorem ay_amcp_replay_unsat_public
    (original solver stream finalClause : Prop) :
    AyAMCPPreprocessArtifact original solver ->
    AyAMCPReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    stream ->
    AyAMCPUnsat original :=
  fun preprocess replay closeFinal streamProof originalProof =>
    closeFinal
      (replay streamProof
        (ay_amcp_equisat_forward original solver preprocess originalProof))

theorem ay_amcp_retained_sat_membership_sound
    (leafHash root acceptedSat artifacts satBranch auditDigest diagnostic
      original solver internalAssignment visibleAssignment : Prop) :
    AyAMCPPreprocessArtifact original solver ->
    (internalAssignment -> visibleAssignment) ->
    (satBranch -> AyAMCPModel solver internalAssignment) ->
    AyAMCPMembership leafHash root
      (AyAMCPEntry acceptedSat artifacts satBranch auditDigest diagnostic) ->
    AyAMCPVisibleSAT original visibleAssignment :=
  fun preprocess decode accept membership =>
    ay_amcp_preprocess_model_reconstruct original solver internalAssignment
      visibleAssignment preprocess decode
      (accept
        (ay_amcp_entry_checker acceptedSat artifacts satBranch auditDigest
          diagnostic
          (ay_amcp_membership_entry leafHash root
            (AyAMCPEntry acceptedSat artifacts satBranch auditDigest
              diagnostic)
            membership)))

theorem ay_amcp_retained_unsat_membership_sound
    (leafHash root acceptedUnsat artifacts unsatBranch auditDigest diagnostic
      original solver stream finalClause : Prop) :
    AyAMCPPreprocessArtifact original solver ->
    AyAMCPReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    (unsatBranch -> stream) ->
    AyAMCPMembership leafHash root
      (AyAMCPEntry acceptedUnsat artifacts unsatBranch auditDigest
        diagnostic) ->
    AyAMCPUnsat original :=
  fun preprocess replay closeFinal accept membership =>
    ay_amcp_replay_unsat_public original solver stream finalClause preprocess
      replay closeFinal
      (accept
        (ay_amcp_entry_checker acceptedUnsat artifacts unsatBranch auditDigest
          diagnostic
          (ay_amcp_membership_entry leafHash root
            (AyAMCPEntry acceptedUnsat artifacts unsatBranch auditDigest
              diagnostic)
            membership)))

theorem ay_amcp_matching_resume_preserves_prior_public_claim
    (checkpoint resumedSuffix rootAgreement appendOnly satFact unsatFact
      noClaim : Prop) :
    AyAMCPResumeWitness checkpoint resumedSuffix rootAgreement appendOnly ->
    (checkpoint -> AyAMCPPublicResult satFact unsatFact noClaim) ->
    AyAMCPPublicResult satFact unsatFact noClaim :=
  fun witness checkpointSound =>
    checkpointSound
      (ay_amcp_resume_checkpoint checkpoint resumedSuffix rootAgreement
        appendOnly witness)

theorem ay_amcp_matching_resume_extends_append_only
    (checkpoint resumedSuffix rootAgreement appendOnly : Prop) :
    AyAMCPResumeWitness checkpoint resumedSuffix rootAgreement appendOnly ->
    appendOnly :=
  ay_amcp_resume_append_only checkpoint resumedSuffix rootAgreement appendOnly

theorem ay_amcp_resume_root_agreement_preserved
    (checkpoint resumedSuffix rootAgreement appendOnly : Prop) :
    AyAMCPResumeWitness checkpoint resumedSuffix rootAgreement appendOnly ->
    rootAgreement :=
  ay_amcp_resume_root_agreement checkpoint resumedSuffix rootAgreement
    appendOnly

theorem ay_amcp_checkpoint_root_matches_resume_base
    (checkpointRoot resumeBaseRoot finalRoot : Prop) :
    AyAMCPRootAgreement checkpointRoot resumeBaseRoot finalRoot ->
    AyAMCPConj checkpointRoot resumeBaseRoot :=
  fun agreement =>
    ay_amcp_conj_intro checkpointRoot resumeBaseRoot
      (ay_amcp_root_agreement_checkpoint checkpointRoot resumeBaseRoot
        finalRoot agreement)
      (ay_amcp_root_agreement_resume_base checkpointRoot resumeBaseRoot
        finalRoot agreement)

theorem ay_amcp_retained_membership_root
    (checkpointRoot leafHash entry : Prop) :
    AyAMCPMembership leafHash checkpointRoot entry ->
    checkpointRoot :=
  ay_amcp_membership_root leafHash checkpointRoot entry

theorem ay_amcp_diagnostic_resume_failure_no_claim
    (reason auditDigest diagnostic : Prop) :
    reason -> auditDigest -> diagnostic ->
    AyAMCPNoClaim reason auditDigest diagnostic :=
  ay_amcp_no_claim_intro reason auditDigest diagnostic

theorem ay_amcp_checkpoint_mismatch_no_claim
    (mismatch auditDigest diagnostic : Prop) :
    mismatch -> auditDigest -> diagnostic ->
    AyAMCPNoClaim mismatch auditDigest diagnostic :=
  ay_amcp_no_claim_intro mismatch auditDigest diagnostic

theorem ay_amcp_mismatch_public_result_no_claim
    (satFact unsatFact mismatch auditDigest diagnostic : Prop) :
    mismatch -> auditDigest -> diagnostic ->
    AyAMCPPublicResult satFact unsatFact
      (AyAMCPNoClaim mismatch auditDigest diagnostic) :=
  fun mismatchProof auditProof diagnosticProof =>
    ay_amcp_disj_right satFact
      (AyAMCPDisj unsatFact
        (AyAMCPNoClaim mismatch auditDigest diagnostic))
      (ay_amcp_disj_right unsatFact
        (AyAMCPNoClaim mismatch auditDigest diagnostic)
        (ay_amcp_checkpoint_mismatch_no_claim mismatch auditDigest
          diagnostic mismatchProof auditProof diagnosticProof))

theorem ay_amcp_mismatch_cannot_expose_sat_claim
    (mismatch auditDigest diagnostic noClaim : Prop) :
    mismatch -> auditDigest -> diagnostic ->
    (AyAMCPNoClaim mismatch auditDigest diagnostic -> noClaim) ->
    noClaim :=
  fun mismatchProof auditProof diagnosticProof toNoClaim =>
    toNoClaim
      (ay_amcp_checkpoint_mismatch_no_claim mismatch auditDigest diagnostic
        mismatchProof auditProof diagnosticProof)

theorem ay_amcp_mismatch_cannot_expose_unsat_claim
    (mismatch auditDigest diagnostic noClaim : Prop) :
    mismatch -> auditDigest -> diagnostic ->
    (AyAMCPNoClaim mismatch auditDigest diagnostic -> noClaim) ->
    noClaim :=
  fun mismatchProof auditProof diagnosticProof toNoClaim =>
    toNoClaim
      (ay_amcp_checkpoint_mismatch_no_claim mismatch auditDigest diagnostic
        mismatchProof auditProof diagnosticProof)

theorem ay_amcp_resume_public_result_sound
    (checkpoint resumedSuffix rootAgreement appendOnly satFact unsatFact
      noClaim : Prop) :
    AyAMCPResumeWitness checkpoint resumedSuffix rootAgreement appendOnly ->
    (appendOnly -> rootAgreement ->
      checkpoint -> AyAMCPPublicResult satFact unsatFact noClaim) ->
    AyAMCPPublicResult satFact unsatFact noClaim :=
  fun witness sound =>
    sound
      (ay_amcp_resume_append_only checkpoint resumedSuffix rootAgreement
        appendOnly witness)
      (ay_amcp_resume_root_agreement checkpoint resumedSuffix rootAgreement
        appendOnly witness)
      (ay_amcp_resume_checkpoint checkpoint resumedSuffix rootAgreement
        appendOnly witness)
