-- SAT-COMP validator audit Merkle batch-checkpoint-prune core.
--
-- Batch membership validation over checkpointed and pruned audit logs exposes
-- semantic SAT/UNSAT claims only for retained accepted witnesses.  Missing
-- witnesses, rejected batches, partial batches, and pruned gaps are explicit
-- no-claim diagnostics.

def AyAMBCPConj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def AyAMBCPDisj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyAMBCPEquisat (before after : Prop) : Prop :=
  AyAMBCPConj (before -> after) (after -> before)

def AyAMBCPPublicResult (satFact unsatFact noClaim : Prop) : Prop :=
  AyAMBCPDisj satFact (AyAMBCPDisj unsatFact noClaim)

def AyAMBCPArtifacts (certId archiveKey : Prop) : Prop :=
  AyAMBCPConj certId archiveKey

def AyAMBCPEntry
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    Prop :=
  AyAMBCPConj exitCode
    (AyAMBCPConj artifacts
      (AyAMBCPConj checkerDecision
        (AyAMBCPConj auditDigest diagnostic)))

def AyAMBCPMembership (leafHash root entry : Prop) : Prop :=
  AyAMBCPConj leafHash (AyAMBCPConj root entry)

def AyAMBCPCheckpoint
    (checkpointRoot checkpointDigest retainedClaims : Prop) : Prop :=
  AyAMBCPConj checkpointRoot
    (AyAMBCPConj checkpointDigest retainedClaims)

def AyAMBCPRetainedSummary
    (retainedPrefix retainedSuffix retainedRoot : Prop) : Prop :=
  AyAMBCPConj retainedPrefix
    (AyAMBCPConj retainedSuffix retainedRoot)

def AyAMBCPPrunedSummary (prunedGaps auditDigest diagnostic : Prop) : Prop :=
  AyAMBCPConj prunedGaps (AyAMBCPConj auditDigest diagnostic)

def AyAMBCPBatchWitnesses
    (satWitnesses unsatWitnesses sharedRoot : Prop) : Prop :=
  AyAMBCPConj satWitnesses
    (AyAMBCPConj unsatWitnesses sharedRoot)

def AyAMBCPBatchEntries (satEntries unsatEntries batchDigest : Prop) :
    Prop :=
  AyAMBCPConj satEntries (AyAMBCPConj unsatEntries batchDigest)

def AyAMBCPRootAgreement
    (checkpointRoot retainedRoot sharedRoot : Prop) : Prop :=
  AyAMBCPConj checkpointRoot
    (AyAMBCPConj retainedRoot sharedRoot)

def AyAMBCPAcceptedBatch
    (checkpoint retainedSummary batchEntries batchWitnesses rootAgreement :
      Prop) : Prop :=
  AyAMBCPConj checkpoint
    (AyAMBCPConj retainedSummary
      (AyAMBCPConj batchEntries
        (AyAMBCPConj batchWitnesses rootAgreement)))

def AyAMBCPRejectedBatch (failedWitnesses auditDigest diagnostic : Prop) :
    Prop :=
  AyAMBCPConj failedWitnesses (AyAMBCPConj auditDigest diagnostic)

def AyAMBCPNoClaim (reason auditDigest diagnostic : Prop) : Prop :=
  AyAMBCPConj reason (AyAMBCPConj auditDigest diagnostic)

def AyAMBCPModel (formula assignment : Prop) : Prop :=
  AyAMBCPConj formula assignment

def AyAMBCPUnsat (formula : Prop) : Prop :=
  formula -> False

def AyAMBCPVisibleSAT (original visibleAssignment : Prop) : Prop :=
  AyAMBCPModel original visibleAssignment

def AyAMBCPPreprocessArtifact (original solver : Prop) : Prop :=
  AyAMBCPEquisat original solver

def AyAMBCPReplayAccepted (solver stream finalClause : Prop) : Prop :=
  stream -> solver -> finalClause

theorem ay_ambcp_conj_intro (left right : Prop) :
    left -> right -> AyAMBCPConj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_ambcp_conj_left (left right : Prop) :
    AyAMBCPConj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_ambcp_conj_right (left right : Prop) :
    AyAMBCPConj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_ambcp_disj_left (left right : Prop) :
    left -> AyAMBCPDisj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_ambcp_disj_right (left right : Prop) :
    right -> AyAMBCPDisj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_ambcp_equisat_forward (before after : Prop) :
    AyAMBCPEquisat before after -> before -> after :=
  fun witness hbefore =>
    witness after (fun forward _backward => forward hbefore)

theorem ay_ambcp_equisat_backward (before after : Prop) :
    AyAMBCPEquisat before after -> after -> before :=
  fun witness hafter =>
    witness before (fun _forward backward => backward hafter)

theorem ay_ambcp_model_intro (formula assignment : Prop) :
    formula -> assignment -> AyAMBCPModel formula assignment :=
  fun formulaProof assignmentProof =>
    ay_ambcp_conj_intro formula assignment formulaProof assignmentProof

theorem ay_ambcp_model_formula (formula assignment : Prop) :
    AyAMBCPModel formula assignment -> formula :=
  fun model => ay_ambcp_conj_left formula assignment model

theorem ay_ambcp_model_assignment (formula assignment : Prop) :
    AyAMBCPModel formula assignment -> assignment :=
  fun model => ay_ambcp_conj_right formula assignment model

theorem ay_ambcp_entry_intro
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    exitCode -> artifacts -> checkerDecision -> auditDigest -> diagnostic ->
    AyAMBCPEntry exitCode artifacts checkerDecision auditDigest diagnostic :=
  fun exitProof artifactsProof checkerProof auditProof diagnosticProof =>
    ay_ambcp_conj_intro exitCode
      (AyAMBCPConj artifacts
        (AyAMBCPConj checkerDecision (AyAMBCPConj auditDigest diagnostic)))
      exitProof
      (ay_ambcp_conj_intro artifacts
        (AyAMBCPConj checkerDecision (AyAMBCPConj auditDigest diagnostic))
        artifactsProof
        (ay_ambcp_conj_intro checkerDecision
          (AyAMBCPConj auditDigest diagnostic)
          checkerProof
          (ay_ambcp_conj_intro auditDigest diagnostic auditProof
            diagnosticProof)))

theorem ay_ambcp_entry_checker
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    AyAMBCPEntry exitCode artifacts checkerDecision auditDigest diagnostic ->
    checkerDecision :=
  fun entry =>
    ay_ambcp_conj_right exitCode
      (AyAMBCPConj artifacts
        (AyAMBCPConj checkerDecision (AyAMBCPConj auditDigest diagnostic)))
      entry checkerDecision
      (fun _artifactsProof tail =>
        tail checkerDecision (fun checkerProof _auditTail => checkerProof))

theorem ay_ambcp_entry_audit
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    AyAMBCPEntry exitCode artifacts checkerDecision auditDigest diagnostic ->
    auditDigest :=
  fun entry =>
    ay_ambcp_conj_right exitCode
      (AyAMBCPConj artifacts
        (AyAMBCPConj checkerDecision (AyAMBCPConj auditDigest diagnostic)))
      entry auditDigest
      (fun _artifactsProof tail =>
        tail auditDigest
          (fun _checkerProof auditTail =>
            auditTail auditDigest
              (fun auditProof _diagnosticProof => auditProof)))

theorem ay_ambcp_entry_diagnostic
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    AyAMBCPEntry exitCode artifacts checkerDecision auditDigest diagnostic ->
    diagnostic :=
  fun entry =>
    ay_ambcp_conj_right exitCode
      (AyAMBCPConj artifacts
        (AyAMBCPConj checkerDecision (AyAMBCPConj auditDigest diagnostic)))
      entry diagnostic
      (fun _artifactsProof tail =>
        tail diagnostic
          (fun _checkerProof auditTail =>
            auditTail diagnostic
              (fun _auditProof diagnosticProof => diagnosticProof)))

theorem ay_ambcp_membership_intro (leafHash root entry : Prop) :
    leafHash -> root -> entry -> AyAMBCPMembership leafHash root entry :=
  fun leafProof rootProof entryProof =>
    ay_ambcp_conj_intro leafHash (AyAMBCPConj root entry)
      leafProof
      (ay_ambcp_conj_intro root entry rootProof entryProof)

theorem ay_ambcp_membership_root (leafHash root entry : Prop) :
    AyAMBCPMembership leafHash root entry -> root :=
  fun membership =>
    ay_ambcp_conj_right leafHash (AyAMBCPConj root entry) membership
      root (fun rootProof _entryProof => rootProof)

theorem ay_ambcp_membership_entry (leafHash root entry : Prop) :
    AyAMBCPMembership leafHash root entry -> entry :=
  fun membership =>
    ay_ambcp_conj_right leafHash (AyAMBCPConj root entry) membership
      entry (fun _rootProof entryProof => entryProof)

theorem ay_ambcp_checkpoint_intro
    (checkpointRoot checkpointDigest retainedClaims : Prop) :
    checkpointRoot -> checkpointDigest -> retainedClaims ->
    AyAMBCPCheckpoint checkpointRoot checkpointDigest retainedClaims :=
  fun rootProof digestProof claimsProof =>
    ay_ambcp_conj_intro checkpointRoot
      (AyAMBCPConj checkpointDigest retainedClaims)
      rootProof
      (ay_ambcp_conj_intro checkpointDigest retainedClaims digestProof
        claimsProof)

theorem ay_ambcp_checkpoint_root
    (checkpointRoot checkpointDigest retainedClaims : Prop) :
    AyAMBCPCheckpoint checkpointRoot checkpointDigest retainedClaims ->
    checkpointRoot :=
  fun checkpoint =>
    ay_ambcp_conj_left checkpointRoot
      (AyAMBCPConj checkpointDigest retainedClaims) checkpoint

theorem ay_ambcp_checkpoint_claims
    (checkpointRoot checkpointDigest retainedClaims : Prop) :
    AyAMBCPCheckpoint checkpointRoot checkpointDigest retainedClaims ->
    retainedClaims :=
  fun checkpoint =>
    ay_ambcp_conj_right checkpointRoot
      (AyAMBCPConj checkpointDigest retainedClaims)
      checkpoint retainedClaims
      (fun _digestProof claimsProof => claimsProof)

theorem ay_ambcp_retained_summary_intro
    (retainedPrefix retainedSuffix retainedRoot : Prop) :
    retainedPrefix -> retainedSuffix -> retainedRoot ->
    AyAMBCPRetainedSummary retainedPrefix retainedSuffix retainedRoot :=
  fun prefixProof suffixProof rootProof =>
    ay_ambcp_conj_intro retainedPrefix
      (AyAMBCPConj retainedSuffix retainedRoot)
      prefixProof
      (ay_ambcp_conj_intro retainedSuffix retainedRoot suffixProof
        rootProof)

theorem ay_ambcp_retained_root
    (retainedPrefix retainedSuffix retainedRoot : Prop) :
    AyAMBCPRetainedSummary retainedPrefix retainedSuffix retainedRoot ->
    retainedRoot :=
  fun summary =>
    ay_ambcp_conj_right retainedPrefix
      (AyAMBCPConj retainedSuffix retainedRoot)
      summary retainedRoot (fun _suffixProof rootProof => rootProof)

theorem ay_ambcp_pruned_summary_intro
    (prunedGaps auditDigest diagnostic : Prop) :
    prunedGaps -> auditDigest -> diagnostic ->
    AyAMBCPPrunedSummary prunedGaps auditDigest diagnostic :=
  fun gapsProof auditProof diagnosticProof =>
    ay_ambcp_conj_intro prunedGaps
      (AyAMBCPConj auditDigest diagnostic)
      gapsProof
      (ay_ambcp_conj_intro auditDigest diagnostic auditProof
        diagnosticProof)

theorem ay_ambcp_pruned_summary_diagnostic
    (prunedGaps auditDigest diagnostic : Prop) :
    AyAMBCPPrunedSummary prunedGaps auditDigest diagnostic -> diagnostic :=
  fun summary =>
    ay_ambcp_conj_right prunedGaps
      (AyAMBCPConj auditDigest diagnostic)
      summary diagnostic (fun _auditProof diagnosticProof =>
        diagnosticProof)

theorem ay_ambcp_batch_witnesses_intro
    (satWitnesses unsatWitnesses sharedRoot : Prop) :
    satWitnesses -> unsatWitnesses -> sharedRoot ->
    AyAMBCPBatchWitnesses satWitnesses unsatWitnesses sharedRoot :=
  fun satProof unsatProof rootProof =>
    ay_ambcp_conj_intro satWitnesses
      (AyAMBCPConj unsatWitnesses sharedRoot)
      satProof
      (ay_ambcp_conj_intro unsatWitnesses sharedRoot unsatProof
        rootProof)

theorem ay_ambcp_batch_witnesses_sat
    (satWitnesses unsatWitnesses sharedRoot : Prop) :
    AyAMBCPBatchWitnesses satWitnesses unsatWitnesses sharedRoot ->
    satWitnesses :=
  fun witnesses =>
    ay_ambcp_conj_left satWitnesses
      (AyAMBCPConj unsatWitnesses sharedRoot) witnesses

theorem ay_ambcp_batch_witnesses_unsat
    (satWitnesses unsatWitnesses sharedRoot : Prop) :
    AyAMBCPBatchWitnesses satWitnesses unsatWitnesses sharedRoot ->
    unsatWitnesses :=
  fun witnesses =>
    ay_ambcp_conj_right satWitnesses
      (AyAMBCPConj unsatWitnesses sharedRoot)
      witnesses unsatWitnesses
      (fun unsatProof _rootProof => unsatProof)

theorem ay_ambcp_batch_witnesses_root
    (satWitnesses unsatWitnesses sharedRoot : Prop) :
    AyAMBCPBatchWitnesses satWitnesses unsatWitnesses sharedRoot ->
    sharedRoot :=
  fun witnesses =>
    ay_ambcp_conj_right satWitnesses
      (AyAMBCPConj unsatWitnesses sharedRoot)
      witnesses sharedRoot (fun _unsatProof rootProof => rootProof)

theorem ay_ambcp_root_agreement_intro
    (checkpointRoot retainedRoot sharedRoot : Prop) :
    checkpointRoot -> retainedRoot -> sharedRoot ->
    AyAMBCPRootAgreement checkpointRoot retainedRoot sharedRoot :=
  fun checkpointProof retainedProof sharedProof =>
    ay_ambcp_conj_intro checkpointRoot
      (AyAMBCPConj retainedRoot sharedRoot)
      checkpointProof
      (ay_ambcp_conj_intro retainedRoot sharedRoot retainedProof
        sharedProof)

theorem ay_ambcp_root_agreement_shared
    (checkpointRoot retainedRoot sharedRoot : Prop) :
    AyAMBCPRootAgreement checkpointRoot retainedRoot sharedRoot ->
    sharedRoot :=
  fun agreement =>
    ay_ambcp_conj_right checkpointRoot
      (AyAMBCPConj retainedRoot sharedRoot)
      agreement sharedRoot (fun _retainedProof sharedProof => sharedProof)

theorem ay_ambcp_accepted_batch_intro
    (checkpoint retainedSummary batchEntries batchWitnesses rootAgreement :
      Prop) :
    checkpoint -> retainedSummary -> batchEntries -> batchWitnesses ->
    rootAgreement ->
    AyAMBCPAcceptedBatch checkpoint retainedSummary batchEntries
      batchWitnesses rootAgreement :=
  fun checkpointProof retainedProof entriesProof witnessesProof rootProof =>
    ay_ambcp_conj_intro checkpoint
      (AyAMBCPConj retainedSummary
        (AyAMBCPConj batchEntries
          (AyAMBCPConj batchWitnesses rootAgreement)))
      checkpointProof
      (ay_ambcp_conj_intro retainedSummary
        (AyAMBCPConj batchEntries
          (AyAMBCPConj batchWitnesses rootAgreement))
        retainedProof
        (ay_ambcp_conj_intro batchEntries
          (AyAMBCPConj batchWitnesses rootAgreement)
          entriesProof
          (ay_ambcp_conj_intro batchWitnesses rootAgreement
            witnessesProof rootProof)))

theorem ay_ambcp_accepted_batch_checkpoint
    (checkpoint retainedSummary batchEntries batchWitnesses rootAgreement :
      Prop) :
    AyAMBCPAcceptedBatch checkpoint retainedSummary batchEntries
      batchWitnesses rootAgreement ->
    checkpoint :=
  fun batch =>
    ay_ambcp_conj_left checkpoint
      (AyAMBCPConj retainedSummary
        (AyAMBCPConj batchEntries
          (AyAMBCPConj batchWitnesses rootAgreement)))
      batch

theorem ay_ambcp_accepted_batch_retained
    (checkpoint retainedSummary batchEntries batchWitnesses rootAgreement :
      Prop) :
    AyAMBCPAcceptedBatch checkpoint retainedSummary batchEntries
      batchWitnesses rootAgreement ->
    retainedSummary :=
  fun batch =>
    ay_ambcp_conj_right checkpoint
      (AyAMBCPConj retainedSummary
        (AyAMBCPConj batchEntries
          (AyAMBCPConj batchWitnesses rootAgreement)))
      batch retainedSummary (fun retainedProof _tail => retainedProof)

theorem ay_ambcp_accepted_batch_witnesses
    (checkpoint retainedSummary batchEntries batchWitnesses rootAgreement :
      Prop) :
    AyAMBCPAcceptedBatch checkpoint retainedSummary batchEntries
      batchWitnesses rootAgreement ->
    batchWitnesses :=
  fun batch =>
    ay_ambcp_conj_right checkpoint
      (AyAMBCPConj retainedSummary
        (AyAMBCPConj batchEntries
          (AyAMBCPConj batchWitnesses rootAgreement)))
      batch batchWitnesses
      (fun _retainedProof tail =>
        tail batchWitnesses
          (fun _entriesProof witnessTail =>
            witnessTail batchWitnesses
              (fun witnessesProof _rootProof => witnessesProof)))

theorem ay_ambcp_accepted_batch_root_agreement
    (checkpoint retainedSummary batchEntries batchWitnesses rootAgreement :
      Prop) :
    AyAMBCPAcceptedBatch checkpoint retainedSummary batchEntries
      batchWitnesses rootAgreement ->
    rootAgreement :=
  fun batch =>
    ay_ambcp_conj_right checkpoint
      (AyAMBCPConj retainedSummary
        (AyAMBCPConj batchEntries
          (AyAMBCPConj batchWitnesses rootAgreement)))
      batch rootAgreement
      (fun _retainedProof tail =>
        tail rootAgreement
          (fun _entriesProof witnessTail =>
            witnessTail rootAgreement
              (fun _witnessesProof rootProof => rootProof)))

theorem ay_ambcp_rejected_batch_intro
    (failedWitnesses auditDigest diagnostic : Prop) :
    failedWitnesses -> auditDigest -> diagnostic ->
    AyAMBCPRejectedBatch failedWitnesses auditDigest diagnostic :=
  fun failedProof auditProof diagnosticProof =>
    ay_ambcp_conj_intro failedWitnesses
      (AyAMBCPConj auditDigest diagnostic)
      failedProof
      (ay_ambcp_conj_intro auditDigest diagnostic auditProof
        diagnosticProof)

theorem ay_ambcp_no_claim_intro
    (reason auditDigest diagnostic : Prop) :
    reason -> auditDigest -> diagnostic ->
    AyAMBCPNoClaim reason auditDigest diagnostic :=
  fun reasonProof auditProof diagnosticProof =>
    ay_ambcp_conj_intro reason (AyAMBCPConj auditDigest diagnostic)
      reasonProof
      (ay_ambcp_conj_intro auditDigest diagnostic auditProof
        diagnosticProof)

theorem ay_ambcp_rejected_batch_no_claim
    (failedWitnesses auditDigest diagnostic : Prop) :
    AyAMBCPRejectedBatch failedWitnesses auditDigest diagnostic ->
    AyAMBCPNoClaim failedWitnesses auditDigest diagnostic :=
  fun rejected =>
    ay_ambcp_conj_intro failedWitnesses
      (AyAMBCPConj auditDigest diagnostic)
      (ay_ambcp_conj_left failedWitnesses
        (AyAMBCPConj auditDigest diagnostic) rejected)
      (ay_ambcp_conj_right failedWitnesses
        (AyAMBCPConj auditDigest diagnostic) rejected)

theorem ay_ambcp_preprocess_model_reconstruct
    (original solver internalAssignment visibleAssignment : Prop) :
    AyAMBCPPreprocessArtifact original solver ->
    (internalAssignment -> visibleAssignment) ->
    AyAMBCPModel solver internalAssignment ->
    AyAMBCPVisibleSAT original visibleAssignment :=
  fun preprocess decode model =>
    ay_ambcp_model_intro original visibleAssignment
      (ay_ambcp_equisat_backward original solver preprocess
        (ay_ambcp_model_formula solver internalAssignment model))
      (decode (ay_ambcp_model_assignment solver internalAssignment model))

theorem ay_ambcp_preprocess_unsat_reconstruct
    (original solver : Prop) :
    AyAMBCPPreprocessArtifact original solver ->
    AyAMBCPUnsat solver ->
    AyAMBCPUnsat original :=
  fun preprocess solverUnsat originalProof =>
    solverUnsat
      (ay_ambcp_equisat_forward original solver preprocess originalProof)

theorem ay_ambcp_replay_unsat_public
    (original solver stream finalClause : Prop) :
    AyAMBCPPreprocessArtifact original solver ->
    AyAMBCPReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    stream ->
    AyAMBCPUnsat original :=
  fun preprocess replay closeFinal streamProof originalProof =>
    closeFinal
      (replay streamProof
        (ay_ambcp_equisat_forward original solver preprocess originalProof))

theorem ay_ambcp_retained_sat_membership_sound
    (leafHash root acceptedSat artifacts satBranch auditDigest diagnostic
      original solver internalAssignment visibleAssignment : Prop) :
    AyAMBCPPreprocessArtifact original solver ->
    (internalAssignment -> visibleAssignment) ->
    (satBranch -> AyAMBCPModel solver internalAssignment) ->
    AyAMBCPMembership leafHash root
      (AyAMBCPEntry acceptedSat artifacts satBranch auditDigest diagnostic) ->
    AyAMBCPVisibleSAT original visibleAssignment :=
  fun preprocess decode accept membership =>
    ay_ambcp_preprocess_model_reconstruct original solver internalAssignment
      visibleAssignment preprocess decode
      (accept
        (ay_ambcp_entry_checker acceptedSat artifacts satBranch auditDigest
          diagnostic
          (ay_ambcp_membership_entry leafHash root
            (AyAMBCPEntry acceptedSat artifacts satBranch auditDigest
              diagnostic)
            membership)))

theorem ay_ambcp_retained_unsat_membership_sound
    (leafHash root acceptedUnsat artifacts unsatBranch auditDigest diagnostic
      original solver stream finalClause : Prop) :
    AyAMBCPPreprocessArtifact original solver ->
    AyAMBCPReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    (unsatBranch -> stream) ->
    AyAMBCPMembership leafHash root
      (AyAMBCPEntry acceptedUnsat artifacts unsatBranch auditDigest
        diagnostic) ->
    AyAMBCPUnsat original :=
  fun preprocess replay closeFinal accept membership =>
    ay_ambcp_replay_unsat_public original solver stream finalClause preprocess
      replay closeFinal
      (accept
        (ay_ambcp_entry_checker acceptedUnsat artifacts unsatBranch auditDigest
          diagnostic
          (ay_ambcp_membership_entry leafHash root
            (AyAMBCPEntry acceptedUnsat artifacts unsatBranch auditDigest
              diagnostic)
            membership)))

theorem ay_ambcp_accepted_batch_preserves_public_soundness
    (checkpoint retainedSummary batchEntries batchWitnesses rootAgreement
      satFact unsatFact noClaim : Prop) :
    AyAMBCPAcceptedBatch checkpoint retainedSummary batchEntries
      batchWitnesses rootAgreement ->
    (checkpoint -> retainedSummary -> batchWitnesses -> rootAgreement ->
      AyAMBCPPublicResult satFact unsatFact noClaim) ->
    AyAMBCPPublicResult satFact unsatFact noClaim :=
  fun batch sound =>
    sound
      (ay_ambcp_accepted_batch_checkpoint checkpoint retainedSummary
        batchEntries batchWitnesses rootAgreement batch)
      (ay_ambcp_accepted_batch_retained checkpoint retainedSummary
        batchEntries batchWitnesses rootAgreement batch)
      (ay_ambcp_accepted_batch_witnesses checkpoint retainedSummary
        batchEntries batchWitnesses rootAgreement batch)
      (ay_ambcp_accepted_batch_root_agreement checkpoint retainedSummary
        batchEntries batchWitnesses rootAgreement batch)

theorem ay_ambcp_accepted_batch_preserves_sat_entry
    (checkpoint retainedSummary batchEntries batchWitnesses rootAgreement
      satFact : Prop) :
    AyAMBCPAcceptedBatch checkpoint retainedSummary batchEntries
      batchWitnesses rootAgreement ->
    (batchWitnesses -> rootAgreement -> satFact) ->
    satFact :=
  fun batch sound =>
    sound
      (ay_ambcp_accepted_batch_witnesses checkpoint retainedSummary
        batchEntries batchWitnesses rootAgreement batch)
      (ay_ambcp_accepted_batch_root_agreement checkpoint retainedSummary
        batchEntries batchWitnesses rootAgreement batch)

theorem ay_ambcp_accepted_batch_preserves_unsat_entry
    (checkpoint retainedSummary batchEntries batchWitnesses rootAgreement
      unsatFact : Prop) :
    AyAMBCPAcceptedBatch checkpoint retainedSummary batchEntries
      batchWitnesses rootAgreement ->
    (batchWitnesses -> rootAgreement -> unsatFact) ->
    unsatFact :=
  fun batch sound =>
    sound
      (ay_ambcp_accepted_batch_witnesses checkpoint retainedSummary
        batchEntries batchWitnesses rootAgreement batch)
      (ay_ambcp_accepted_batch_root_agreement checkpoint retainedSummary
        batchEntries batchWitnesses rootAgreement batch)

theorem ay_ambcp_missing_witness_no_claim
    (missingWitness auditDigest diagnostic : Prop) :
    missingWitness -> auditDigest -> diagnostic ->
    AyAMBCPNoClaim missingWitness auditDigest diagnostic :=
  ay_ambcp_no_claim_intro missingWitness auditDigest diagnostic

theorem ay_ambcp_pruned_gap_no_claim
    (prunedGap auditDigest diagnostic : Prop) :
    prunedGap -> auditDigest -> diagnostic ->
    AyAMBCPNoClaim prunedGap auditDigest diagnostic :=
  ay_ambcp_no_claim_intro prunedGap auditDigest diagnostic

theorem ay_ambcp_pruned_summary_no_claim
    (prunedGaps auditDigest diagnostic : Prop) :
    AyAMBCPPrunedSummary prunedGaps auditDigest diagnostic ->
    AyAMBCPNoClaim prunedGaps auditDigest diagnostic :=
  fun pruned =>
    ay_ambcp_conj_intro prunedGaps
      (AyAMBCPConj auditDigest diagnostic)
      (ay_ambcp_conj_left prunedGaps
        (AyAMBCPConj auditDigest diagnostic) pruned)
      (ay_ambcp_conj_right prunedGaps
        (AyAMBCPConj auditDigest diagnostic) pruned)

theorem ay_ambcp_rejected_batch_public_result_no_claim
    (satFact unsatFact failedWitnesses auditDigest diagnostic : Prop) :
    AyAMBCPRejectedBatch failedWitnesses auditDigest diagnostic ->
    AyAMBCPPublicResult satFact unsatFact
      (AyAMBCPNoClaim failedWitnesses auditDigest diagnostic) :=
  fun rejected =>
    ay_ambcp_disj_right satFact
      (AyAMBCPDisj unsatFact
        (AyAMBCPNoClaim failedWitnesses auditDigest diagnostic))
      (ay_ambcp_disj_right unsatFact
        (AyAMBCPNoClaim failedWitnesses auditDigest diagnostic)
        (ay_ambcp_rejected_batch_no_claim failedWitnesses auditDigest
          diagnostic rejected))

theorem ay_ambcp_partial_batch_no_claim
    (partialFailure auditDigest diagnostic : Prop) :
    partialFailure -> auditDigest -> diagnostic ->
    AyAMBCPNoClaim partialFailure auditDigest diagnostic :=
  ay_ambcp_no_claim_intro partialFailure auditDigest diagnostic

theorem ay_ambcp_failed_or_pruned_no_claim
    (missingWitness prunedGap auditDigest diagnostic noClaim : Prop) :
    AyAMBCPDisj missingWitness prunedGap ->
    auditDigest -> diagnostic ->
    (missingWitness ->
      AyAMBCPNoClaim missingWitness auditDigest diagnostic -> noClaim) ->
    (prunedGap ->
      AyAMBCPNoClaim prunedGap auditDigest diagnostic -> noClaim) ->
    noClaim :=
  fun failure auditProof diagnosticProof onMissing onPruned =>
    failure noClaim
      (fun missingProof =>
        onMissing missingProof
          (ay_ambcp_missing_witness_no_claim missingWitness auditDigest
            diagnostic missingProof auditProof diagnosticProof))
      (fun prunedProof =>
        onPruned prunedProof
          (ay_ambcp_pruned_gap_no_claim prunedGap auditDigest diagnostic
            prunedProof auditProof diagnosticProof))
