-- SAT-COMP validator audit Merkle incremental-batch core.
--
-- Incremental batch validation extends a previously accepted audit state with
-- appended entries and fresh membership witnesses.  Accepted increments carry
-- prior public soundness forward and add new SAT/UNSAT soundness; rejected
-- increments keep prior soundness and expose only no-claim diagnostics.

def AyAMIBConj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def AyAMIBDisj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyAMIBEquisat (before after : Prop) : Prop :=
  AyAMIBConj (before -> after) (after -> before)

def AyAMIBPublicResult (satFact unsatFact noClaim : Prop) : Prop :=
  AyAMIBDisj satFact (AyAMIBDisj unsatFact noClaim)

def AyAMIBArtifacts (certId archiveKey : Prop) : Prop :=
  AyAMIBConj certId archiveKey

def AyAMIBEntry
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    Prop :=
  AyAMIBConj exitCode
    (AyAMIBConj artifacts
      (AyAMIBConj checkerDecision
        (AyAMIBConj auditDigest diagnostic)))

def AyAMIBMembership (leafHash root entry : Prop) : Prop :=
  AyAMIBConj leafHash (AyAMIBConj root entry)

def AyAMIBPriorState (priorRoot priorBatch priorClaims : Prop) : Prop :=
  AyAMIBConj priorRoot (AyAMIBConj priorBatch priorClaims)

def AyAMIBAppendedEntries (newSatEntries newUnsatEntries appendDigest :
    Prop) : Prop :=
  AyAMIBConj newSatEntries (AyAMIBConj newUnsatEntries appendDigest)

def AyAMIBIncrementalWitnesses
    (newSatWitnesses newUnsatWitnesses updatedRoot : Prop) : Prop :=
  AyAMIBConj newSatWitnesses
    (AyAMIBConj newUnsatWitnesses updatedRoot)

def AyAMIBRootUpdate (priorRoot sharedRoot updatedRoot : Prop) : Prop :=
  AyAMIBConj priorRoot (AyAMIBConj sharedRoot updatedRoot)

def AyAMIBAcceptedIncrement
    (priorState appendedEntries incrementalWitnesses rootUpdate :
      Prop) : Prop :=
  AyAMIBConj priorState
    (AyAMIBConj appendedEntries
      (AyAMIBConj incrementalWitnesses rootUpdate))

def AyAMIBRejectedIncrement (failedWitness auditDigest diagnostic : Prop) :
    Prop :=
  AyAMIBConj failedWitness (AyAMIBConj auditDigest diagnostic)

def AyAMIBNoClaim (reason auditDigest diagnostic : Prop) : Prop :=
  AyAMIBConj reason (AyAMIBConj auditDigest diagnostic)

def AyAMIBModel (formula assignment : Prop) : Prop :=
  AyAMIBConj formula assignment

def AyAMIBUnsat (formula : Prop) : Prop :=
  formula -> False

def AyAMIBVisibleSAT (original visibleAssignment : Prop) : Prop :=
  AyAMIBModel original visibleAssignment

def AyAMIBPreprocessArtifact (original solver : Prop) : Prop :=
  AyAMIBEquisat original solver

def AyAMIBReplayAccepted (solver stream finalClause : Prop) : Prop :=
  stream -> solver -> finalClause

theorem ay_amib_conj_intro (left right : Prop) :
    left -> right -> AyAMIBConj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_amib_conj_left (left right : Prop) :
    AyAMIBConj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_amib_conj_right (left right : Prop) :
    AyAMIBConj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_amib_disj_left (left right : Prop) :
    left -> AyAMIBDisj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_amib_disj_right (left right : Prop) :
    right -> AyAMIBDisj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_amib_equisat_forward (before after : Prop) :
    AyAMIBEquisat before after -> before -> after :=
  fun witness hbefore =>
    witness after (fun forward _backward => forward hbefore)

theorem ay_amib_equisat_backward (before after : Prop) :
    AyAMIBEquisat before after -> after -> before :=
  fun witness hafter =>
    witness before (fun _forward backward => backward hafter)

theorem ay_amib_model_intro (formula assignment : Prop) :
    formula -> assignment -> AyAMIBModel formula assignment :=
  fun formulaProof assignmentProof =>
    ay_amib_conj_intro formula assignment formulaProof assignmentProof

theorem ay_amib_model_formula (formula assignment : Prop) :
    AyAMIBModel formula assignment -> formula :=
  fun model => ay_amib_conj_left formula assignment model

theorem ay_amib_model_assignment (formula assignment : Prop) :
    AyAMIBModel formula assignment -> assignment :=
  fun model => ay_amib_conj_right formula assignment model

theorem ay_amib_entry_intro
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    exitCode -> artifacts -> checkerDecision -> auditDigest -> diagnostic ->
    AyAMIBEntry exitCode artifacts checkerDecision auditDigest diagnostic :=
  fun exitProof artifactsProof checkerProof auditProof diagnosticProof =>
    ay_amib_conj_intro exitCode
      (AyAMIBConj artifacts
        (AyAMIBConj checkerDecision (AyAMIBConj auditDigest diagnostic)))
      exitProof
      (ay_amib_conj_intro artifacts
        (AyAMIBConj checkerDecision (AyAMIBConj auditDigest diagnostic))
        artifactsProof
        (ay_amib_conj_intro checkerDecision
          (AyAMIBConj auditDigest diagnostic)
          checkerProof
          (ay_amib_conj_intro auditDigest diagnostic auditProof
            diagnosticProof)))

theorem ay_amib_entry_checker
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    AyAMIBEntry exitCode artifacts checkerDecision auditDigest diagnostic ->
    checkerDecision :=
  fun entry =>
    ay_amib_conj_right exitCode
      (AyAMIBConj artifacts
        (AyAMIBConj checkerDecision (AyAMIBConj auditDigest diagnostic)))
      entry checkerDecision
      (fun _artifactsProof tail =>
        tail checkerDecision (fun checkerProof _auditTail => checkerProof))

theorem ay_amib_membership_entry (leafHash root entry : Prop) :
    AyAMIBMembership leafHash root entry -> entry :=
  fun membership =>
    ay_amib_conj_right leafHash (AyAMIBConj root entry) membership
      entry (fun _rootProof entryProof => entryProof)

theorem ay_amib_prior_state_intro
    (priorRoot priorBatch priorClaims : Prop) :
    priorRoot -> priorBatch -> priorClaims ->
    AyAMIBPriorState priorRoot priorBatch priorClaims :=
  fun rootProof batchProof claimsProof =>
    ay_amib_conj_intro priorRoot (AyAMIBConj priorBatch priorClaims)
      rootProof
      (ay_amib_conj_intro priorBatch priorClaims batchProof claimsProof)

theorem ay_amib_prior_state_claims
    (priorRoot priorBatch priorClaims : Prop) :
    AyAMIBPriorState priorRoot priorBatch priorClaims -> priorClaims :=
  fun prior =>
    ay_amib_conj_right priorRoot (AyAMIBConj priorBatch priorClaims)
      prior priorClaims (fun _batchProof claimsProof => claimsProof)

theorem ay_amib_appended_entries_intro
    (newSatEntries newUnsatEntries appendDigest : Prop) :
    newSatEntries -> newUnsatEntries -> appendDigest ->
    AyAMIBAppendedEntries newSatEntries newUnsatEntries appendDigest :=
  fun satProof unsatProof digestProof =>
    ay_amib_conj_intro newSatEntries
      (AyAMIBConj newUnsatEntries appendDigest)
      satProof
      (ay_amib_conj_intro newUnsatEntries appendDigest unsatProof
        digestProof)

theorem ay_amib_incremental_witnesses_intro
    (newSatWitnesses newUnsatWitnesses updatedRoot : Prop) :
    newSatWitnesses -> newUnsatWitnesses -> updatedRoot ->
    AyAMIBIncrementalWitnesses newSatWitnesses newUnsatWitnesses
      updatedRoot :=
  fun satProof unsatProof rootProof =>
    ay_amib_conj_intro newSatWitnesses
      (AyAMIBConj newUnsatWitnesses updatedRoot)
      satProof
      (ay_amib_conj_intro newUnsatWitnesses updatedRoot unsatProof
        rootProof)

theorem ay_amib_incremental_witnesses_sat
    (newSatWitnesses newUnsatWitnesses updatedRoot : Prop) :
    AyAMIBIncrementalWitnesses newSatWitnesses newUnsatWitnesses
      updatedRoot ->
    newSatWitnesses :=
  fun witnesses =>
    ay_amib_conj_left newSatWitnesses
      (AyAMIBConj newUnsatWitnesses updatedRoot) witnesses

theorem ay_amib_incremental_witnesses_unsat
    (newSatWitnesses newUnsatWitnesses updatedRoot : Prop) :
    AyAMIBIncrementalWitnesses newSatWitnesses newUnsatWitnesses
      updatedRoot ->
    newUnsatWitnesses :=
  fun witnesses =>
    ay_amib_conj_right newSatWitnesses
      (AyAMIBConj newUnsatWitnesses updatedRoot)
      witnesses newUnsatWitnesses
      (fun unsatProof _rootProof => unsatProof)

theorem ay_amib_incremental_witnesses_root
    (newSatWitnesses newUnsatWitnesses updatedRoot : Prop) :
    AyAMIBIncrementalWitnesses newSatWitnesses newUnsatWitnesses
      updatedRoot ->
    updatedRoot :=
  fun witnesses =>
    ay_amib_conj_right newSatWitnesses
      (AyAMIBConj newUnsatWitnesses updatedRoot)
      witnesses updatedRoot (fun _unsatProof rootProof => rootProof)

theorem ay_amib_root_update_intro
    (priorRoot sharedRoot updatedRoot : Prop) :
    priorRoot -> sharedRoot -> updatedRoot ->
    AyAMIBRootUpdate priorRoot sharedRoot updatedRoot :=
  fun priorProof sharedProof updatedProof =>
    ay_amib_conj_intro priorRoot (AyAMIBConj sharedRoot updatedRoot)
      priorProof
      (ay_amib_conj_intro sharedRoot updatedRoot sharedProof updatedProof)

theorem ay_amib_root_update_updated
    (priorRoot sharedRoot updatedRoot : Prop) :
    AyAMIBRootUpdate priorRoot sharedRoot updatedRoot -> updatedRoot :=
  fun rootUpdate =>
    ay_amib_conj_right priorRoot (AyAMIBConj sharedRoot updatedRoot)
      rootUpdate updatedRoot (fun _sharedProof updatedProof =>
        updatedProof)

theorem ay_amib_accepted_increment_intro
    (priorState appendedEntries incrementalWitnesses rootUpdate : Prop) :
    priorState -> appendedEntries -> incrementalWitnesses -> rootUpdate ->
    AyAMIBAcceptedIncrement priorState appendedEntries
      incrementalWitnesses rootUpdate :=
  fun priorProof appendedProof witnessesProof rootProof =>
    ay_amib_conj_intro priorState
      (AyAMIBConj appendedEntries
        (AyAMIBConj incrementalWitnesses rootUpdate))
      priorProof
      (ay_amib_conj_intro appendedEntries
        (AyAMIBConj incrementalWitnesses rootUpdate)
        appendedProof
        (ay_amib_conj_intro incrementalWitnesses rootUpdate
          witnessesProof rootProof))

theorem ay_amib_accepted_increment_prior
    (priorState appendedEntries incrementalWitnesses rootUpdate : Prop) :
    AyAMIBAcceptedIncrement priorState appendedEntries incrementalWitnesses
      rootUpdate ->
    priorState :=
  fun accepted =>
    ay_amib_conj_left priorState
      (AyAMIBConj appendedEntries
        (AyAMIBConj incrementalWitnesses rootUpdate))
      accepted

theorem ay_amib_accepted_increment_witnesses
    (priorState appendedEntries incrementalWitnesses rootUpdate : Prop) :
    AyAMIBAcceptedIncrement priorState appendedEntries incrementalWitnesses
      rootUpdate ->
    incrementalWitnesses :=
  fun accepted =>
    ay_amib_conj_right priorState
      (AyAMIBConj appendedEntries
        (AyAMIBConj incrementalWitnesses rootUpdate))
      accepted incrementalWitnesses
      (fun _appendedProof tail =>
        tail incrementalWitnesses
          (fun witnessesProof _rootProof => witnessesProof))

theorem ay_amib_accepted_increment_root_update
    (priorState appendedEntries incrementalWitnesses rootUpdate : Prop) :
    AyAMIBAcceptedIncrement priorState appendedEntries incrementalWitnesses
      rootUpdate ->
    rootUpdate :=
  fun accepted =>
    ay_amib_conj_right priorState
      (AyAMIBConj appendedEntries
        (AyAMIBConj incrementalWitnesses rootUpdate))
      accepted rootUpdate
      (fun _appendedProof tail =>
        tail rootUpdate (fun _witnessesProof rootProof => rootProof))

theorem ay_amib_rejected_increment_intro
    (failedWitness auditDigest diagnostic : Prop) :
    failedWitness -> auditDigest -> diagnostic ->
    AyAMIBRejectedIncrement failedWitness auditDigest diagnostic :=
  fun failedProof auditProof diagnosticProof =>
    ay_amib_conj_intro failedWitness
      (AyAMIBConj auditDigest diagnostic)
      failedProof
      (ay_amib_conj_intro auditDigest diagnostic auditProof
        diagnosticProof)

theorem ay_amib_no_claim_intro
    (reason auditDigest diagnostic : Prop) :
    reason -> auditDigest -> diagnostic ->
    AyAMIBNoClaim reason auditDigest diagnostic :=
  fun reasonProof auditProof diagnosticProof =>
    ay_amib_conj_intro reason (AyAMIBConj auditDigest diagnostic)
      reasonProof
      (ay_amib_conj_intro auditDigest diagnostic auditProof
        diagnosticProof)

theorem ay_amib_rejected_increment_no_claim
    (failedWitness auditDigest diagnostic : Prop) :
    AyAMIBRejectedIncrement failedWitness auditDigest diagnostic ->
    AyAMIBNoClaim failedWitness auditDigest diagnostic :=
  fun rejected =>
    ay_amib_conj_intro failedWitness
      (AyAMIBConj auditDigest diagnostic)
      (ay_amib_conj_left failedWitness
        (AyAMIBConj auditDigest diagnostic) rejected)
      (ay_amib_conj_right failedWitness
        (AyAMIBConj auditDigest diagnostic) rejected)

theorem ay_amib_preprocess_model_reconstruct
    (original solver internalAssignment visibleAssignment : Prop) :
    AyAMIBPreprocessArtifact original solver ->
    (internalAssignment -> visibleAssignment) ->
    AyAMIBModel solver internalAssignment ->
    AyAMIBVisibleSAT original visibleAssignment :=
  fun preprocess decode model =>
    ay_amib_model_intro original visibleAssignment
      (ay_amib_equisat_backward original solver preprocess
        (ay_amib_model_formula solver internalAssignment model))
      (decode (ay_amib_model_assignment solver internalAssignment model))

theorem ay_amib_preprocess_unsat_reconstruct
    (original solver : Prop) :
    AyAMIBPreprocessArtifact original solver ->
    AyAMIBUnsat solver ->
    AyAMIBUnsat original :=
  fun preprocess solverUnsat originalProof =>
    solverUnsat
      (ay_amib_equisat_forward original solver preprocess originalProof)

theorem ay_amib_replay_unsat_public
    (original solver stream finalClause : Prop) :
    AyAMIBPreprocessArtifact original solver ->
    AyAMIBReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    stream ->
    AyAMIBUnsat original :=
  fun preprocess replay closeFinal streamProof originalProof =>
    closeFinal
      (replay streamProof
        (ay_amib_equisat_forward original solver preprocess originalProof))

theorem ay_amib_retained_sat_membership_sound
    (leafHash root acceptedSat artifacts satBranch auditDigest diagnostic
      original solver internalAssignment visibleAssignment : Prop) :
    AyAMIBPreprocessArtifact original solver ->
    (internalAssignment -> visibleAssignment) ->
    (satBranch -> AyAMIBModel solver internalAssignment) ->
    AyAMIBMembership leafHash root
      (AyAMIBEntry acceptedSat artifacts satBranch auditDigest diagnostic) ->
    AyAMIBVisibleSAT original visibleAssignment :=
  fun preprocess decode accept membership =>
    ay_amib_preprocess_model_reconstruct original solver internalAssignment
      visibleAssignment preprocess decode
      (accept
        (ay_amib_entry_checker acceptedSat artifacts satBranch auditDigest
          diagnostic
          (ay_amib_membership_entry leafHash root
            (AyAMIBEntry acceptedSat artifacts satBranch auditDigest
              diagnostic)
            membership)))

theorem ay_amib_retained_unsat_membership_sound
    (leafHash root acceptedUnsat artifacts unsatBranch auditDigest diagnostic
      original solver stream finalClause : Prop) :
    AyAMIBPreprocessArtifact original solver ->
    AyAMIBReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    (unsatBranch -> stream) ->
    AyAMIBMembership leafHash root
      (AyAMIBEntry acceptedUnsat artifacts unsatBranch auditDigest
        diagnostic) ->
    AyAMIBUnsat original :=
  fun preprocess replay closeFinal accept membership =>
    ay_amib_replay_unsat_public original solver stream finalClause preprocess
      replay closeFinal
      (accept
        (ay_amib_entry_checker acceptedUnsat artifacts unsatBranch auditDigest
          diagnostic
          (ay_amib_membership_entry leafHash root
            (AyAMIBEntry acceptedUnsat artifacts unsatBranch auditDigest
              diagnostic)
            membership)))

theorem ay_amib_accepted_increment_preserves_prior_public_soundness
    (priorState appendedEntries incrementalWitnesses rootUpdate
      satFact unsatFact noClaim : Prop) :
    AyAMIBAcceptedIncrement priorState appendedEntries incrementalWitnesses
      rootUpdate ->
    (priorState -> AyAMIBPublicResult satFact unsatFact noClaim) ->
    AyAMIBPublicResult satFact unsatFact noClaim :=
  fun accepted priorSound =>
    priorSound
      (ay_amib_accepted_increment_prior priorState appendedEntries
        incrementalWitnesses rootUpdate accepted)

theorem ay_amib_accepted_increment_adds_new_sat_entries
    (priorState appendedEntries incrementalWitnesses rootUpdate satFact :
      Prop) :
    AyAMIBAcceptedIncrement priorState appendedEntries incrementalWitnesses
      rootUpdate ->
    (incrementalWitnesses -> rootUpdate -> satFact) ->
    satFact :=
  fun accepted newSound =>
    newSound
      (ay_amib_accepted_increment_witnesses priorState appendedEntries
        incrementalWitnesses rootUpdate accepted)
      (ay_amib_accepted_increment_root_update priorState appendedEntries
        incrementalWitnesses rootUpdate accepted)

theorem ay_amib_accepted_increment_adds_new_unsat_entries
    (priorState appendedEntries incrementalWitnesses rootUpdate unsatFact :
      Prop) :
    AyAMIBAcceptedIncrement priorState appendedEntries incrementalWitnesses
      rootUpdate ->
    (incrementalWitnesses -> rootUpdate -> unsatFact) ->
    unsatFact :=
  fun accepted newSound =>
    newSound
      (ay_amib_accepted_increment_witnesses priorState appendedEntries
        incrementalWitnesses rootUpdate accepted)
      (ay_amib_accepted_increment_root_update priorState appendedEntries
        incrementalWitnesses rootUpdate accepted)

theorem ay_amib_accepted_increment_public_result_sound
    (priorState appendedEntries incrementalWitnesses rootUpdate
      satFact unsatFact noClaim : Prop) :
    AyAMIBAcceptedIncrement priorState appendedEntries incrementalWitnesses
      rootUpdate ->
    (priorState -> incrementalWitnesses -> rootUpdate ->
      AyAMIBPublicResult satFact unsatFact noClaim) ->
    AyAMIBPublicResult satFact unsatFact noClaim :=
  fun accepted sound =>
    sound
      (ay_amib_accepted_increment_prior priorState appendedEntries
        incrementalWitnesses rootUpdate accepted)
      (ay_amib_accepted_increment_witnesses priorState appendedEntries
        incrementalWitnesses rootUpdate accepted)
      (ay_amib_accepted_increment_root_update priorState appendedEntries
        incrementalWitnesses rootUpdate accepted)

theorem ay_amib_rejected_increment_preserves_prior_public_soundness
    (priorState failedWitness auditDigest diagnostic satFact unsatFact
      noClaim : Prop) :
    AyAMIBRejectedIncrement failedWitness auditDigest diagnostic ->
    priorState ->
    (priorState -> AyAMIBPublicResult satFact unsatFact noClaim) ->
    AyAMIBPublicResult satFact unsatFact noClaim :=
  fun _rejected priorProof priorSound => priorSound priorProof

theorem ay_amib_duplicate_witness_no_claim
    (duplicateWitness auditDigest diagnostic : Prop) :
    duplicateWitness -> auditDigest -> diagnostic ->
    AyAMIBNoClaim duplicateWitness auditDigest diagnostic :=
  ay_amib_no_claim_intro duplicateWitness auditDigest diagnostic

theorem ay_amib_missing_witness_no_claim
    (missingWitness auditDigest diagnostic : Prop) :
    missingWitness -> auditDigest -> diagnostic ->
    AyAMIBNoClaim missingWitness auditDigest diagnostic :=
  ay_amib_no_claim_intro missingWitness auditDigest diagnostic

theorem ay_amib_bad_witness_no_claim
    (badWitness auditDigest diagnostic : Prop) :
    badWitness -> auditDigest -> diagnostic ->
    AyAMIBNoClaim badWitness auditDigest diagnostic :=
  ay_amib_no_claim_intro badWitness auditDigest diagnostic

theorem ay_amib_rejected_increment_public_result_no_claim
    (satFact unsatFact failedWitness auditDigest diagnostic : Prop) :
    AyAMIBRejectedIncrement failedWitness auditDigest diagnostic ->
    AyAMIBPublicResult satFact unsatFact
      (AyAMIBNoClaim failedWitness auditDigest diagnostic) :=
  fun rejected =>
    ay_amib_disj_right satFact
      (AyAMIBDisj unsatFact
        (AyAMIBNoClaim failedWitness auditDigest diagnostic))
      (ay_amib_disj_right unsatFact
        (AyAMIBNoClaim failedWitness auditDigest diagnostic)
        (ay_amib_rejected_increment_no_claim failedWitness auditDigest
          diagnostic rejected))

theorem ay_amib_failed_increment_no_sat_or_unsat_claim
    (duplicateWitness missingWitness badWitness auditDigest diagnostic
      noClaim : Prop) :
    AyAMIBDisj duplicateWitness
      (AyAMIBDisj missingWitness badWitness) ->
    auditDigest -> diagnostic ->
    (duplicateWitness ->
      AyAMIBNoClaim duplicateWitness auditDigest diagnostic -> noClaim) ->
    (missingWitness ->
      AyAMIBNoClaim missingWitness auditDigest diagnostic -> noClaim) ->
    (badWitness ->
      AyAMIBNoClaim badWitness auditDigest diagnostic -> noClaim) ->
    noClaim :=
  fun failure auditProof diagnosticProof onDuplicate onMissing onBad =>
    failure noClaim
      (fun duplicateProof =>
        onDuplicate duplicateProof
          (ay_amib_duplicate_witness_no_claim duplicateWitness auditDigest
            diagnostic duplicateProof auditProof diagnosticProof))
      (fun tail =>
        tail noClaim
          (fun missingProof =>
            onMissing missingProof
              (ay_amib_missing_witness_no_claim missingWitness auditDigest
                diagnostic missingProof auditProof diagnosticProof))
          (fun badProof =>
            onBad badProof
              (ay_amib_bad_witness_no_claim badWitness auditDigest
                diagnostic badProof auditProof diagnosticProof)))
