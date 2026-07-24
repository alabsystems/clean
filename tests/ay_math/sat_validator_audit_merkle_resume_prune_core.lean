-- SAT-COMP validator audit Merkle resume-prune core.
--
-- A matching checkpoint plus retained post-prune membership keeps accepted
-- SAT/UNSAT public claims available across long validator runs.  Missing
-- retained evidence or root mismatch is represented as an explicit no-claim
-- diagnostic rather than a public SAT/UNSAT result.

def AyAMRPConj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def AyAMRPDisj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyAMRPEquisat (before after : Prop) : Prop :=
  AyAMRPConj (before -> after) (after -> before)

def AyAMRPPublicResult (satFact unsatFact noClaim : Prop) : Prop :=
  AyAMRPDisj satFact (AyAMRPDisj unsatFact noClaim)

def AyAMRPArtifacts (certId archiveKey : Prop) : Prop :=
  AyAMRPConj certId archiveKey

def AyAMRPEntry
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    Prop :=
  AyAMRPConj exitCode
    (AyAMRPConj artifacts
      (AyAMRPConj checkerDecision
        (AyAMRPConj auditDigest diagnostic)))

def AyAMRPMembership (leafHash root entry : Prop) : Prop :=
  AyAMRPConj leafHash (AyAMRPConj root entry)

def AyAMRPCheckpoint
    (checkpointRoot checkpointDigest priorClaims : Prop) : Prop :=
  AyAMRPConj checkpointRoot
    (AyAMRPConj checkpointDigest priorClaims)

def AyAMRPResumedSuffix (suffEntries suffRoot suffTailDigest : Prop) : Prop :=
  AyAMRPConj suffEntries (AyAMRPConj suffRoot suffTailDigest)

def AyAMRPRetainedSummary (retainedPrior retainedSuff finalRoot : Prop) :
    Prop :=
  AyAMRPConj retainedPrior (AyAMRPConj retainedSuff finalRoot)

def AyAMRPPrunedGaps (gapDigest diagnostic : Prop) : Prop :=
  AyAMRPConj gapDigest diagnostic

def AyAMRPRootAgreement
    (checkpointRoot resumeBaseRoot retainedRoot finalRoot : Prop) : Prop :=
  AyAMRPConj checkpointRoot
    (AyAMRPConj resumeBaseRoot
      (AyAMRPConj retainedRoot finalRoot))

def AyAMRPAppendOnly
    (checkpointLog resumedSuffix finalLog : Prop) : Prop :=
  AyAMRPConj checkpointLog (AyAMRPConj resumedSuffix finalLog)

def AyAMRPResumePruneWitness
    (checkpoint resumedSuffix retainedSummary prunedGaps rootAgreement
      appendOnly : Prop) : Prop :=
  AyAMRPConj checkpoint
    (AyAMRPConj resumedSuffix
      (AyAMRPConj retainedSummary
        (AyAMRPConj prunedGaps
          (AyAMRPConj rootAgreement appendOnly))))

def AyAMRPNoClaim (reason auditDigest diagnostic : Prop) : Prop :=
  AyAMRPConj reason (AyAMRPConj auditDigest diagnostic)

def AyAMRPModel (formula assignment : Prop) : Prop :=
  AyAMRPConj formula assignment

def AyAMRPUnsat (formula : Prop) : Prop :=
  formula -> False

def AyAMRPVisibleSAT (original visibleAssignment : Prop) : Prop :=
  AyAMRPModel original visibleAssignment

def AyAMRPPreprocessArtifact (original solver : Prop) : Prop :=
  AyAMRPEquisat original solver

def AyAMRPReplayAccepted (solver stream finalClause : Prop) : Prop :=
  stream -> solver -> finalClause

theorem ay_amrp_conj_intro (left right : Prop) :
    left -> right -> AyAMRPConj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_amrp_conj_left (left right : Prop) :
    AyAMRPConj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_amrp_conj_right (left right : Prop) :
    AyAMRPConj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_amrp_disj_left (left right : Prop) :
    left -> AyAMRPDisj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_amrp_disj_right (left right : Prop) :
    right -> AyAMRPDisj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_amrp_equisat_forward (before after : Prop) :
    AyAMRPEquisat before after -> before -> after :=
  fun witness hbefore =>
    witness after (fun forward _backward => forward hbefore)

theorem ay_amrp_equisat_backward (before after : Prop) :
    AyAMRPEquisat before after -> after -> before :=
  fun witness hafter =>
    witness before (fun _forward backward => backward hafter)

theorem ay_amrp_model_intro (formula assignment : Prop) :
    formula -> assignment -> AyAMRPModel formula assignment :=
  fun formulaProof assignmentProof =>
    ay_amrp_conj_intro formula assignment formulaProof assignmentProof

theorem ay_amrp_model_formula (formula assignment : Prop) :
    AyAMRPModel formula assignment -> formula :=
  fun model => ay_amrp_conj_left formula assignment model

theorem ay_amrp_model_assignment (formula assignment : Prop) :
    AyAMRPModel formula assignment -> assignment :=
  fun model => ay_amrp_conj_right formula assignment model

theorem ay_amrp_entry_intro
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    exitCode -> artifacts -> checkerDecision -> auditDigest -> diagnostic ->
    AyAMRPEntry exitCode artifacts checkerDecision auditDigest diagnostic :=
  fun exitProof artifactsProof checkerProof auditProof diagnosticProof =>
    ay_amrp_conj_intro exitCode
      (AyAMRPConj artifacts
        (AyAMRPConj checkerDecision (AyAMRPConj auditDigest diagnostic)))
      exitProof
      (ay_amrp_conj_intro artifacts
        (AyAMRPConj checkerDecision (AyAMRPConj auditDigest diagnostic))
        artifactsProof
        (ay_amrp_conj_intro checkerDecision
          (AyAMRPConj auditDigest diagnostic)
          checkerProof
          (ay_amrp_conj_intro auditDigest diagnostic auditProof
            diagnosticProof)))

theorem ay_amrp_entry_checker
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    AyAMRPEntry exitCode artifacts checkerDecision auditDigest diagnostic ->
    checkerDecision :=
  fun entry =>
    ay_amrp_conj_right exitCode
      (AyAMRPConj artifacts
        (AyAMRPConj checkerDecision (AyAMRPConj auditDigest diagnostic)))
      entry checkerDecision
      (fun _artifactsProof tail =>
        tail checkerDecision (fun checkerProof _auditTail => checkerProof))

theorem ay_amrp_entry_audit
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    AyAMRPEntry exitCode artifacts checkerDecision auditDigest diagnostic ->
    auditDigest :=
  fun entry =>
    ay_amrp_conj_right exitCode
      (AyAMRPConj artifacts
        (AyAMRPConj checkerDecision (AyAMRPConj auditDigest diagnostic)))
      entry auditDigest
      (fun _artifactsProof tail =>
        tail auditDigest
          (fun _checkerProof auditTail =>
            auditTail auditDigest
              (fun auditProof _diagnosticProof => auditProof)))

theorem ay_amrp_entry_diagnostic
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    AyAMRPEntry exitCode artifacts checkerDecision auditDigest diagnostic ->
    diagnostic :=
  fun entry =>
    ay_amrp_conj_right exitCode
      (AyAMRPConj artifacts
        (AyAMRPConj checkerDecision (AyAMRPConj auditDigest diagnostic)))
      entry diagnostic
      (fun _artifactsProof tail =>
        tail diagnostic
          (fun _checkerProof auditTail =>
            auditTail diagnostic
              (fun _auditProof diagnosticProof => diagnosticProof)))

theorem ay_amrp_membership_intro (leafHash root entry : Prop) :
    leafHash -> root -> entry -> AyAMRPMembership leafHash root entry :=
  fun leafProof rootProof entryProof =>
    ay_amrp_conj_intro leafHash (AyAMRPConj root entry)
      leafProof
      (ay_amrp_conj_intro root entry rootProof entryProof)

theorem ay_amrp_membership_root (leafHash root entry : Prop) :
    AyAMRPMembership leafHash root entry -> root :=
  fun membership =>
    ay_amrp_conj_right leafHash (AyAMRPConj root entry) membership
      root (fun rootProof _entryProof => rootProof)

theorem ay_amrp_membership_entry (leafHash root entry : Prop) :
    AyAMRPMembership leafHash root entry -> entry :=
  fun membership =>
    ay_amrp_conj_right leafHash (AyAMRPConj root entry) membership
      entry (fun _rootProof entryProof => entryProof)

theorem ay_amrp_checkpoint_intro
    (checkpointRoot checkpointDigest priorClaims : Prop) :
    checkpointRoot -> checkpointDigest -> priorClaims ->
    AyAMRPCheckpoint checkpointRoot checkpointDigest priorClaims :=
  fun rootProof digestProof claimsProof =>
    ay_amrp_conj_intro checkpointRoot
      (AyAMRPConj checkpointDigest priorClaims)
      rootProof
      (ay_amrp_conj_intro checkpointDigest priorClaims digestProof
        claimsProof)

theorem ay_amrp_checkpoint_root
    (checkpointRoot checkpointDigest priorClaims : Prop) :
    AyAMRPCheckpoint checkpointRoot checkpointDigest priorClaims ->
    checkpointRoot :=
  fun checkpoint =>
    ay_amrp_conj_left checkpointRoot
      (AyAMRPConj checkpointDigest priorClaims) checkpoint

theorem ay_amrp_checkpoint_claims
    (checkpointRoot checkpointDigest priorClaims : Prop) :
    AyAMRPCheckpoint checkpointRoot checkpointDigest priorClaims ->
    priorClaims :=
  fun checkpoint =>
    ay_amrp_conj_right checkpointRoot
      (AyAMRPConj checkpointDigest priorClaims)
      checkpoint priorClaims
      (fun _digestProof claimsProof => claimsProof)

theorem ay_amrp_resumed_suffix_intro
    (suffEntries suffRoot suffTailDigest : Prop) :
    suffEntries -> suffRoot -> suffTailDigest ->
    AyAMRPResumedSuffix suffEntries suffRoot suffTailDigest :=
  fun entriesProof rootProof tailProof =>
    ay_amrp_conj_intro suffEntries
      (AyAMRPConj suffRoot suffTailDigest)
      entriesProof
      (ay_amrp_conj_intro suffRoot suffTailDigest rootProof tailProof)

theorem ay_amrp_resumed_suffix_root
    (suffEntries suffRoot suffTailDigest : Prop) :
    AyAMRPResumedSuffix suffEntries suffRoot suffTailDigest -> suffRoot :=
  fun suff =>
    ay_amrp_conj_right suffEntries
      (AyAMRPConj suffRoot suffTailDigest)
      suff suffRoot (fun rootProof _tailProof => rootProof)

theorem ay_amrp_retained_summary_intro
    (retainedPrior retainedSuff finalRoot : Prop) :
    retainedPrior -> retainedSuff -> finalRoot ->
    AyAMRPRetainedSummary retainedPrior retainedSuff finalRoot :=
  fun priorProof suffProof rootProof =>
    ay_amrp_conj_intro retainedPrior
      (AyAMRPConj retainedSuff finalRoot)
      priorProof
      (ay_amrp_conj_intro retainedSuff finalRoot suffProof rootProof)

theorem ay_amrp_retained_prior
    (retainedPrior retainedSuff finalRoot : Prop) :
    AyAMRPRetainedSummary retainedPrior retainedSuff finalRoot ->
    retainedPrior :=
  fun summary =>
    ay_amrp_conj_left retainedPrior
      (AyAMRPConj retainedSuff finalRoot) summary

theorem ay_amrp_retained_suffix
    (retainedPrior retainedSuff finalRoot : Prop) :
    AyAMRPRetainedSummary retainedPrior retainedSuff finalRoot ->
    retainedSuff :=
  fun summary =>
    ay_amrp_conj_right retainedPrior
      (AyAMRPConj retainedSuff finalRoot)
      summary retainedSuff (fun suffProof _rootProof => suffProof)

theorem ay_amrp_retained_final_root
    (retainedPrior retainedSuff finalRoot : Prop) :
    AyAMRPRetainedSummary retainedPrior retainedSuff finalRoot ->
    finalRoot :=
  fun summary =>
    ay_amrp_conj_right retainedPrior
      (AyAMRPConj retainedSuff finalRoot)
      summary finalRoot (fun _suffProof rootProof => rootProof)

theorem ay_amrp_pruned_gaps_intro (gapDigest diagnostic : Prop) :
    gapDigest -> diagnostic -> AyAMRPPrunedGaps gapDigest diagnostic :=
  ay_amrp_conj_intro gapDigest diagnostic

theorem ay_amrp_pruned_gaps_diagnostic (gapDigest diagnostic : Prop) :
    AyAMRPPrunedGaps gapDigest diagnostic -> diagnostic :=
  ay_amrp_conj_right gapDigest diagnostic

theorem ay_amrp_root_agreement_intro
    (checkpointRoot resumeBaseRoot retainedRoot finalRoot : Prop) :
    checkpointRoot -> resumeBaseRoot -> retainedRoot -> finalRoot ->
    AyAMRPRootAgreement checkpointRoot resumeBaseRoot retainedRoot
      finalRoot :=
  fun checkpointProof baseProof retainedProof finalProof =>
    ay_amrp_conj_intro checkpointRoot
      (AyAMRPConj resumeBaseRoot
        (AyAMRPConj retainedRoot finalRoot))
      checkpointProof
      (ay_amrp_conj_intro resumeBaseRoot
        (AyAMRPConj retainedRoot finalRoot)
        baseProof
        (ay_amrp_conj_intro retainedRoot finalRoot retainedProof
          finalProof))

theorem ay_amrp_root_agreement_checkpoint
    (checkpointRoot resumeBaseRoot retainedRoot finalRoot : Prop) :
    AyAMRPRootAgreement checkpointRoot resumeBaseRoot retainedRoot
      finalRoot ->
    checkpointRoot :=
  fun agreement =>
    ay_amrp_conj_left checkpointRoot
      (AyAMRPConj resumeBaseRoot
        (AyAMRPConj retainedRoot finalRoot))
      agreement

theorem ay_amrp_root_agreement_final
    (checkpointRoot resumeBaseRoot retainedRoot finalRoot : Prop) :
    AyAMRPRootAgreement checkpointRoot resumeBaseRoot retainedRoot
      finalRoot ->
    finalRoot :=
  fun agreement =>
    ay_amrp_conj_right checkpointRoot
      (AyAMRPConj resumeBaseRoot
        (AyAMRPConj retainedRoot finalRoot))
      agreement finalRoot
      (fun _baseProof tail =>
        tail finalRoot (fun _retainedProof finalProof => finalProof))

theorem ay_amrp_append_only_intro
    (checkpointLog resumedSuffix finalLog : Prop) :
    checkpointLog -> resumedSuffix -> finalLog ->
    AyAMRPAppendOnly checkpointLog resumedSuffix finalLog :=
  fun checkpointProof suffProof finalProof =>
    ay_amrp_conj_intro checkpointLog
      (AyAMRPConj resumedSuffix finalLog)
      checkpointProof
      (ay_amrp_conj_intro resumedSuffix finalLog suffProof finalProof)

theorem ay_amrp_append_only_final
    (checkpointLog resumedSuffix finalLog : Prop) :
    AyAMRPAppendOnly checkpointLog resumedSuffix finalLog -> finalLog :=
  fun appendOnly =>
    ay_amrp_conj_right checkpointLog
      (AyAMRPConj resumedSuffix finalLog)
      appendOnly finalLog (fun _suffProof finalProof => finalProof)

theorem ay_amrp_resume_prune_witness_intro
    (checkpoint resumedSuffix retainedSummary prunedGaps rootAgreement
      appendOnly : Prop) :
    checkpoint -> resumedSuffix -> retainedSummary -> prunedGaps ->
    rootAgreement -> appendOnly ->
    AyAMRPResumePruneWitness checkpoint resumedSuffix retainedSummary
      prunedGaps rootAgreement appendOnly :=
  fun checkpointProof suffProof retainedProof gapsProof rootProof
      appendProof =>
    ay_amrp_conj_intro checkpoint
      (AyAMRPConj resumedSuffix
        (AyAMRPConj retainedSummary
          (AyAMRPConj prunedGaps
            (AyAMRPConj rootAgreement appendOnly))))
      checkpointProof
      (ay_amrp_conj_intro resumedSuffix
        (AyAMRPConj retainedSummary
          (AyAMRPConj prunedGaps
            (AyAMRPConj rootAgreement appendOnly)))
        suffProof
        (ay_amrp_conj_intro retainedSummary
          (AyAMRPConj prunedGaps
            (AyAMRPConj rootAgreement appendOnly))
          retainedProof
          (ay_amrp_conj_intro prunedGaps
            (AyAMRPConj rootAgreement appendOnly)
            gapsProof
            (ay_amrp_conj_intro rootAgreement appendOnly rootProof
              appendProof))))

theorem ay_amrp_resume_prune_checkpoint
    (checkpoint resumedSuffix retainedSummary prunedGaps rootAgreement
      appendOnly : Prop) :
    AyAMRPResumePruneWitness checkpoint resumedSuffix retainedSummary
      prunedGaps rootAgreement appendOnly ->
    checkpoint :=
  fun witness =>
    ay_amrp_conj_left checkpoint
      (AyAMRPConj resumedSuffix
        (AyAMRPConj retainedSummary
          (AyAMRPConj prunedGaps
            (AyAMRPConj rootAgreement appendOnly))))
      witness

theorem ay_amrp_resume_prune_retained
    (checkpoint resumedSuffix retainedSummary prunedGaps rootAgreement
      appendOnly : Prop) :
    AyAMRPResumePruneWitness checkpoint resumedSuffix retainedSummary
      prunedGaps rootAgreement appendOnly ->
    retainedSummary :=
  fun witness =>
    ay_amrp_conj_right checkpoint
      (AyAMRPConj resumedSuffix
        (AyAMRPConj retainedSummary
          (AyAMRPConj prunedGaps
            (AyAMRPConj rootAgreement appendOnly))))
      witness retainedSummary
      (fun _suffProof tail =>
        tail retainedSummary
          (fun retainedProof _gapsTail => retainedProof))

theorem ay_amrp_resume_prune_gaps
    (checkpoint resumedSuffix retainedSummary prunedGaps rootAgreement
      appendOnly : Prop) :
    AyAMRPResumePruneWitness checkpoint resumedSuffix retainedSummary
      prunedGaps rootAgreement appendOnly ->
    prunedGaps :=
  fun witness =>
    ay_amrp_conj_right checkpoint
      (AyAMRPConj resumedSuffix
        (AyAMRPConj retainedSummary
          (AyAMRPConj prunedGaps
            (AyAMRPConj rootAgreement appendOnly))))
      witness prunedGaps
      (fun _suffProof tail =>
        tail prunedGaps
          (fun _retainedProof gapsTail =>
            gapsTail prunedGaps
              (fun gapsProof _rootTail => gapsProof)))

theorem ay_amrp_resume_prune_root_agreement
    (checkpoint resumedSuffix retainedSummary prunedGaps rootAgreement
      appendOnly : Prop) :
    AyAMRPResumePruneWitness checkpoint resumedSuffix retainedSummary
      prunedGaps rootAgreement appendOnly ->
    rootAgreement :=
  fun witness =>
    ay_amrp_conj_right checkpoint
      (AyAMRPConj resumedSuffix
        (AyAMRPConj retainedSummary
          (AyAMRPConj prunedGaps
            (AyAMRPConj rootAgreement appendOnly))))
      witness rootAgreement
      (fun _suffProof tail =>
        tail rootAgreement
          (fun _retainedProof gapsTail =>
            gapsTail rootAgreement
              (fun _gapsProof rootTail =>
                rootTail rootAgreement
                  (fun rootProof _appendProof => rootProof))))

theorem ay_amrp_resume_prune_append_only
    (checkpoint resumedSuffix retainedSummary prunedGaps rootAgreement
      appendOnly : Prop) :
    AyAMRPResumePruneWitness checkpoint resumedSuffix retainedSummary
      prunedGaps rootAgreement appendOnly ->
    appendOnly :=
  fun witness =>
    ay_amrp_conj_right checkpoint
      (AyAMRPConj resumedSuffix
        (AyAMRPConj retainedSummary
          (AyAMRPConj prunedGaps
            (AyAMRPConj rootAgreement appendOnly))))
      witness appendOnly
      (fun _suffProof tail =>
        tail appendOnly
          (fun _retainedProof gapsTail =>
            gapsTail appendOnly
              (fun _gapsProof rootTail =>
                rootTail appendOnly
                  (fun _rootProof appendProof => appendProof))))

theorem ay_amrp_no_claim_intro
    (reason auditDigest diagnostic : Prop) :
    reason -> auditDigest -> diagnostic ->
    AyAMRPNoClaim reason auditDigest diagnostic :=
  fun reasonProof auditProof diagnosticProof =>
    ay_amrp_conj_intro reason (AyAMRPConj auditDigest diagnostic)
      reasonProof
      (ay_amrp_conj_intro auditDigest diagnostic auditProof
        diagnosticProof)

theorem ay_amrp_preprocess_model_reconstruct
    (original solver internalAssignment visibleAssignment : Prop) :
    AyAMRPPreprocessArtifact original solver ->
    (internalAssignment -> visibleAssignment) ->
    AyAMRPModel solver internalAssignment ->
    AyAMRPVisibleSAT original visibleAssignment :=
  fun preprocess decode model =>
    ay_amrp_model_intro original visibleAssignment
      (ay_amrp_equisat_backward original solver preprocess
        (ay_amrp_model_formula solver internalAssignment model))
      (decode (ay_amrp_model_assignment solver internalAssignment model))

theorem ay_amrp_preprocess_unsat_reconstruct
    (original solver : Prop) :
    AyAMRPPreprocessArtifact original solver ->
    AyAMRPUnsat solver ->
    AyAMRPUnsat original :=
  fun preprocess solverUnsat originalProof =>
    solverUnsat
      (ay_amrp_equisat_forward original solver preprocess originalProof)

theorem ay_amrp_replay_unsat_public
    (original solver stream finalClause : Prop) :
    AyAMRPPreprocessArtifact original solver ->
    AyAMRPReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    stream ->
    AyAMRPUnsat original :=
  fun preprocess replay closeFinal streamProof originalProof =>
    closeFinal
      (replay streamProof
        (ay_amrp_equisat_forward original solver preprocess originalProof))

theorem ay_amrp_retained_sat_membership_sound
    (leafHash root acceptedSat artifacts satBranch auditDigest diagnostic
      original solver internalAssignment visibleAssignment : Prop) :
    AyAMRPPreprocessArtifact original solver ->
    (internalAssignment -> visibleAssignment) ->
    (satBranch -> AyAMRPModel solver internalAssignment) ->
    AyAMRPMembership leafHash root
      (AyAMRPEntry acceptedSat artifacts satBranch auditDigest diagnostic) ->
    AyAMRPVisibleSAT original visibleAssignment :=
  fun preprocess decode accept membership =>
    ay_amrp_preprocess_model_reconstruct original solver internalAssignment
      visibleAssignment preprocess decode
      (accept
        (ay_amrp_entry_checker acceptedSat artifacts satBranch auditDigest
          diagnostic
          (ay_amrp_membership_entry leafHash root
            (AyAMRPEntry acceptedSat artifacts satBranch auditDigest
              diagnostic)
            membership)))

theorem ay_amrp_retained_unsat_membership_sound
    (leafHash root acceptedUnsat artifacts unsatBranch auditDigest diagnostic
      original solver stream finalClause : Prop) :
    AyAMRPPreprocessArtifact original solver ->
    AyAMRPReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    (unsatBranch -> stream) ->
    AyAMRPMembership leafHash root
      (AyAMRPEntry acceptedUnsat artifacts unsatBranch auditDigest
        diagnostic) ->
    AyAMRPUnsat original :=
  fun preprocess replay closeFinal accept membership =>
    ay_amrp_replay_unsat_public original solver stream finalClause preprocess
      replay closeFinal
      (accept
        (ay_amrp_entry_checker acceptedUnsat artifacts unsatBranch auditDigest
          diagnostic
          (ay_amrp_membership_entry leafHash root
            (AyAMRPEntry acceptedUnsat artifacts unsatBranch auditDigest
              diagnostic)
            membership)))

theorem ay_amrp_matching_resume_prune_preserves_prior_claim
    (checkpoint resumedSuffix retainedSummary prunedGaps rootAgreement
      appendOnly satFact unsatFact noClaim : Prop) :
    AyAMRPResumePruneWitness checkpoint resumedSuffix retainedSummary
      prunedGaps rootAgreement appendOnly ->
    (checkpoint -> retainedSummary ->
      AyAMRPPublicResult satFact unsatFact noClaim) ->
    AyAMRPPublicResult satFact unsatFact noClaim :=
  fun witness sound =>
    sound
      (ay_amrp_resume_prune_checkpoint checkpoint resumedSuffix
        retainedSummary prunedGaps rootAgreement appendOnly witness)
      (ay_amrp_resume_prune_retained checkpoint resumedSuffix
        retainedSummary prunedGaps rootAgreement appendOnly witness)

theorem ay_amrp_matching_resume_prune_preserves_resumed_claim
    (checkpoint resumedSuffix retainedSummary prunedGaps rootAgreement
      appendOnly satFact unsatFact noClaim : Prop) :
    AyAMRPResumePruneWitness checkpoint resumedSuffix retainedSummary
      prunedGaps rootAgreement appendOnly ->
    (resumedSuffix -> retainedSummary -> rootAgreement ->
      AyAMRPPublicResult satFact unsatFact noClaim) ->
    AyAMRPPublicResult satFact unsatFact noClaim :=
  fun witness sound =>
    sound
      (ay_amrp_conj_right checkpoint
        (AyAMRPConj resumedSuffix
          (AyAMRPConj retainedSummary
            (AyAMRPConj prunedGaps
              (AyAMRPConj rootAgreement appendOnly))))
        witness resumedSuffix
        (fun suffProof _tail => suffProof))
      (ay_amrp_resume_prune_retained checkpoint resumedSuffix
        retainedSummary prunedGaps rootAgreement appendOnly witness)
      (ay_amrp_resume_prune_root_agreement checkpoint resumedSuffix
        retainedSummary prunedGaps rootAgreement appendOnly witness)

theorem ay_amrp_matching_resume_prune_public_sound
    (checkpoint resumedSuffix retainedSummary prunedGaps rootAgreement
      appendOnly satFact unsatFact noClaim : Prop) :
    AyAMRPResumePruneWitness checkpoint resumedSuffix retainedSummary
      prunedGaps rootAgreement appendOnly ->
    (checkpoint -> resumedSuffix -> retainedSummary -> rootAgreement ->
      appendOnly -> AyAMRPPublicResult satFact unsatFact noClaim) ->
    AyAMRPPublicResult satFact unsatFact noClaim :=
  fun witness sound =>
    sound
      (ay_amrp_resume_prune_checkpoint checkpoint resumedSuffix
        retainedSummary prunedGaps rootAgreement appendOnly witness)
      (ay_amrp_conj_right checkpoint
        (AyAMRPConj resumedSuffix
          (AyAMRPConj retainedSummary
            (AyAMRPConj prunedGaps
              (AyAMRPConj rootAgreement appendOnly))))
        witness resumedSuffix
        (fun suffProof _tail => suffProof))
      (ay_amrp_resume_prune_retained checkpoint resumedSuffix
        retainedSummary prunedGaps rootAgreement appendOnly witness)
      (ay_amrp_resume_prune_root_agreement checkpoint resumedSuffix
        retainedSummary prunedGaps rootAgreement appendOnly witness)
      (ay_amrp_resume_prune_append_only checkpoint resumedSuffix
        retainedSummary prunedGaps rootAgreement appendOnly witness)

theorem ay_amrp_checkpoint_mismatch_no_claim
    (checkpointMismatch auditDigest diagnostic : Prop) :
    checkpointMismatch -> auditDigest -> diagnostic ->
    AyAMRPNoClaim checkpointMismatch auditDigest diagnostic :=
  ay_amrp_no_claim_intro checkpointMismatch auditDigest diagnostic

theorem ay_amrp_root_mismatch_no_claim
    (rootMismatch auditDigest diagnostic : Prop) :
    rootMismatch -> auditDigest -> diagnostic ->
    AyAMRPNoClaim rootMismatch auditDigest diagnostic :=
  ay_amrp_no_claim_intro rootMismatch auditDigest diagnostic

theorem ay_amrp_pruned_missing_membership_no_claim
    (missingMembership auditDigest diagnostic : Prop) :
    missingMembership -> auditDigest -> diagnostic ->
    AyAMRPNoClaim missingMembership auditDigest diagnostic :=
  ay_amrp_no_claim_intro missingMembership auditDigest diagnostic

theorem ay_amrp_pruned_gap_no_claim
    (missingMembership gapDigest auditDigest diagnostic : Prop) :
    missingMembership ->
    AyAMRPPrunedGaps gapDigest diagnostic ->
    auditDigest ->
    AyAMRPNoClaim missingMembership auditDigest diagnostic :=
  fun missingProof gaps auditProof =>
    ay_amrp_pruned_missing_membership_no_claim missingMembership auditDigest
      diagnostic missingProof auditProof
      (ay_amrp_pruned_gaps_diagnostic gapDigest diagnostic gaps)

theorem ay_amrp_mismatch_public_result_no_claim
    (satFact unsatFact mismatch auditDigest diagnostic : Prop) :
    mismatch -> auditDigest -> diagnostic ->
    AyAMRPPublicResult satFact unsatFact
      (AyAMRPNoClaim mismatch auditDigest diagnostic) :=
  fun mismatchProof auditProof diagnosticProof =>
    ay_amrp_disj_right satFact
      (AyAMRPDisj unsatFact
        (AyAMRPNoClaim mismatch auditDigest diagnostic))
      (ay_amrp_disj_right unsatFact
        (AyAMRPNoClaim mismatch auditDigest diagnostic)
        (ay_amrp_no_claim_intro mismatch auditDigest diagnostic
          mismatchProof auditProof diagnosticProof))

theorem ay_amrp_missing_membership_public_result_no_claim
    (satFact unsatFact missingMembership auditDigest diagnostic : Prop) :
    missingMembership -> auditDigest -> diagnostic ->
    AyAMRPPublicResult satFact unsatFact
      (AyAMRPNoClaim missingMembership auditDigest diagnostic) :=
  ay_amrp_mismatch_public_result_no_claim satFact unsatFact
    missingMembership auditDigest diagnostic

theorem ay_amrp_no_claim_from_checkpoint_or_root_mismatch
    (checkpointMismatch rootMismatch auditDigest diagnostic noClaim : Prop) :
    AyAMRPDisj checkpointMismatch rootMismatch ->
    auditDigest -> diagnostic ->
    (checkpointMismatch -> AyAMRPNoClaim checkpointMismatch auditDigest
      diagnostic -> noClaim) ->
    (rootMismatch -> AyAMRPNoClaim rootMismatch auditDigest diagnostic ->
      noClaim) ->
    noClaim :=
  fun mismatch auditProof diagnosticProof onCheckpoint onRoot =>
    mismatch noClaim
      (fun checkpointProof =>
        onCheckpoint checkpointProof
          (ay_amrp_checkpoint_mismatch_no_claim checkpointMismatch auditDigest
            diagnostic checkpointProof auditProof diagnosticProof))
      (fun rootProof =>
        onRoot rootProof
          (ay_amrp_root_mismatch_no_claim rootMismatch auditDigest
            diagnostic rootProof auditProof diagnosticProof))
