-- SAT-COMP validator audit Merkle batch-membership core.
--
-- Batch verification checks many audit leaves against one shared Merkle root.
-- Accepted batches expose entry soundness through retained membership
-- witnesses; rejected or partial batches expose only no-claim diagnostics.

def AyAMBMConj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def AyAMBMDisj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyAMBMEquisat (before after : Prop) : Prop :=
  AyAMBMConj (before -> after) (after -> before)

def AyAMBMPublicResult (satFact unsatFact noClaim : Prop) : Prop :=
  AyAMBMDisj satFact (AyAMBMDisj unsatFact noClaim)

def AyAMBMArtifacts (certId archiveKey : Prop) : Prop :=
  AyAMBMConj certId archiveKey

def AyAMBMEntry
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    Prop :=
  AyAMBMConj exitCode
    (AyAMBMConj artifacts
      (AyAMBMConj checkerDecision
        (AyAMBMConj auditDigest diagnostic)))

def AyAMBMMembership (leafHash root entry : Prop) : Prop :=
  AyAMBMConj leafHash (AyAMBMConj root entry)

def AyAMBMBatchEntries (satEntries unsatEntries batchDigest : Prop) : Prop :=
  AyAMBMConj satEntries (AyAMBMConj unsatEntries batchDigest)

def AyAMBMBatchWitnesses
    (satWitnesses unsatWitnesses sharedRoot : Prop) : Prop :=
  AyAMBMConj satWitnesses (AyAMBMConj unsatWitnesses sharedRoot)

def AyAMBMRootAgreement (declaredRoot checkedRoot sharedRoot : Prop) : Prop :=
  AyAMBMConj declaredRoot (AyAMBMConj checkedRoot sharedRoot)

def AyAMBMAcceptedBatch
    (batchEntries batchWitnesses rootAgreement reportDigest : Prop) :
    Prop :=
  AyAMBMConj batchEntries
    (AyAMBMConj batchWitnesses
      (AyAMBMConj rootAgreement reportDigest))

def AyAMBMRejectedBatch (failedWitnesses auditDigest diagnostic : Prop) :
    Prop :=
  AyAMBMConj failedWitnesses (AyAMBMConj auditDigest diagnostic)

def AyAMBMNoClaim (reason auditDigest diagnostic : Prop) : Prop :=
  AyAMBMConj reason (AyAMBMConj auditDigest diagnostic)

def AyAMBMModel (formula assignment : Prop) : Prop :=
  AyAMBMConj formula assignment

def AyAMBMUnsat (formula : Prop) : Prop :=
  formula -> False

def AyAMBMVisibleSAT (original visibleAssignment : Prop) : Prop :=
  AyAMBMModel original visibleAssignment

def AyAMBMPreprocessArtifact (original solver : Prop) : Prop :=
  AyAMBMEquisat original solver

def AyAMBMReplayAccepted (solver stream finalClause : Prop) : Prop :=
  stream -> solver -> finalClause

theorem ay_ambm_conj_intro (left right : Prop) :
    left -> right -> AyAMBMConj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_ambm_conj_left (left right : Prop) :
    AyAMBMConj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_ambm_conj_right (left right : Prop) :
    AyAMBMConj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_ambm_disj_left (left right : Prop) :
    left -> AyAMBMDisj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_ambm_disj_right (left right : Prop) :
    right -> AyAMBMDisj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_ambm_equisat_forward (before after : Prop) :
    AyAMBMEquisat before after -> before -> after :=
  fun witness hbefore =>
    witness after (fun forward _backward => forward hbefore)

theorem ay_ambm_equisat_backward (before after : Prop) :
    AyAMBMEquisat before after -> after -> before :=
  fun witness hafter =>
    witness before (fun _forward backward => backward hafter)

theorem ay_ambm_model_intro (formula assignment : Prop) :
    formula -> assignment -> AyAMBMModel formula assignment :=
  fun formulaProof assignmentProof =>
    ay_ambm_conj_intro formula assignment formulaProof assignmentProof

theorem ay_ambm_model_formula (formula assignment : Prop) :
    AyAMBMModel formula assignment -> formula :=
  fun model => ay_ambm_conj_left formula assignment model

theorem ay_ambm_model_assignment (formula assignment : Prop) :
    AyAMBMModel formula assignment -> assignment :=
  fun model => ay_ambm_conj_right formula assignment model

theorem ay_ambm_entry_intro
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    exitCode -> artifacts -> checkerDecision -> auditDigest -> diagnostic ->
    AyAMBMEntry exitCode artifacts checkerDecision auditDigest diagnostic :=
  fun exitProof artifactsProof checkerProof auditProof diagnosticProof =>
    ay_ambm_conj_intro exitCode
      (AyAMBMConj artifacts
        (AyAMBMConj checkerDecision (AyAMBMConj auditDigest diagnostic)))
      exitProof
      (ay_ambm_conj_intro artifacts
        (AyAMBMConj checkerDecision (AyAMBMConj auditDigest diagnostic))
        artifactsProof
        (ay_ambm_conj_intro checkerDecision
          (AyAMBMConj auditDigest diagnostic)
          checkerProof
          (ay_ambm_conj_intro auditDigest diagnostic auditProof
            diagnosticProof)))

theorem ay_ambm_entry_checker
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    AyAMBMEntry exitCode artifacts checkerDecision auditDigest diagnostic ->
    checkerDecision :=
  fun entry =>
    ay_ambm_conj_right exitCode
      (AyAMBMConj artifacts
        (AyAMBMConj checkerDecision (AyAMBMConj auditDigest diagnostic)))
      entry checkerDecision
      (fun _artifactsProof tail =>
        tail checkerDecision (fun checkerProof _auditTail => checkerProof))

theorem ay_ambm_entry_audit
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    AyAMBMEntry exitCode artifacts checkerDecision auditDigest diagnostic ->
    auditDigest :=
  fun entry =>
    ay_ambm_conj_right exitCode
      (AyAMBMConj artifacts
        (AyAMBMConj checkerDecision (AyAMBMConj auditDigest diagnostic)))
      entry auditDigest
      (fun _artifactsProof tail =>
        tail auditDigest
          (fun _checkerProof auditTail =>
            auditTail auditDigest
              (fun auditProof _diagnosticProof => auditProof)))

theorem ay_ambm_entry_diagnostic
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    AyAMBMEntry exitCode artifacts checkerDecision auditDigest diagnostic ->
    diagnostic :=
  fun entry =>
    ay_ambm_conj_right exitCode
      (AyAMBMConj artifacts
        (AyAMBMConj checkerDecision (AyAMBMConj auditDigest diagnostic)))
      entry diagnostic
      (fun _artifactsProof tail =>
        tail diagnostic
          (fun _checkerProof auditTail =>
            auditTail diagnostic
              (fun _auditProof diagnosticProof => diagnosticProof)))

theorem ay_ambm_membership_intro (leafHash root entry : Prop) :
    leafHash -> root -> entry -> AyAMBMMembership leafHash root entry :=
  fun leafProof rootProof entryProof =>
    ay_ambm_conj_intro leafHash (AyAMBMConj root entry)
      leafProof
      (ay_ambm_conj_intro root entry rootProof entryProof)

theorem ay_ambm_membership_root (leafHash root entry : Prop) :
    AyAMBMMembership leafHash root entry -> root :=
  fun membership =>
    ay_ambm_conj_right leafHash (AyAMBMConj root entry) membership
      root (fun rootProof _entryProof => rootProof)

theorem ay_ambm_membership_entry (leafHash root entry : Prop) :
    AyAMBMMembership leafHash root entry -> entry :=
  fun membership =>
    ay_ambm_conj_right leafHash (AyAMBMConj root entry) membership
      entry (fun _rootProof entryProof => entryProof)

theorem ay_ambm_batch_entries_intro
    (satEntries unsatEntries batchDigest : Prop) :
    satEntries -> unsatEntries -> batchDigest ->
    AyAMBMBatchEntries satEntries unsatEntries batchDigest :=
  fun satProof unsatProof digestProof =>
    ay_ambm_conj_intro satEntries
      (AyAMBMConj unsatEntries batchDigest)
      satProof
      (ay_ambm_conj_intro unsatEntries batchDigest unsatProof
        digestProof)

theorem ay_ambm_batch_entries_sat
    (satEntries unsatEntries batchDigest : Prop) :
    AyAMBMBatchEntries satEntries unsatEntries batchDigest -> satEntries :=
  fun entries =>
    ay_ambm_conj_left satEntries
      (AyAMBMConj unsatEntries batchDigest) entries

theorem ay_ambm_batch_entries_unsat
    (satEntries unsatEntries batchDigest : Prop) :
    AyAMBMBatchEntries satEntries unsatEntries batchDigest -> unsatEntries :=
  fun entries =>
    ay_ambm_conj_right satEntries
      (AyAMBMConj unsatEntries batchDigest)
      entries unsatEntries (fun unsatProof _digestProof => unsatProof)

theorem ay_ambm_batch_witnesses_intro
    (satWitnesses unsatWitnesses sharedRoot : Prop) :
    satWitnesses -> unsatWitnesses -> sharedRoot ->
    AyAMBMBatchWitnesses satWitnesses unsatWitnesses sharedRoot :=
  fun satProof unsatProof rootProof =>
    ay_ambm_conj_intro satWitnesses
      (AyAMBMConj unsatWitnesses sharedRoot)
      satProof
      (ay_ambm_conj_intro unsatWitnesses sharedRoot unsatProof rootProof)

theorem ay_ambm_batch_witnesses_sat
    (satWitnesses unsatWitnesses sharedRoot : Prop) :
    AyAMBMBatchWitnesses satWitnesses unsatWitnesses sharedRoot ->
    satWitnesses :=
  fun witnesses =>
    ay_ambm_conj_left satWitnesses
      (AyAMBMConj unsatWitnesses sharedRoot) witnesses

theorem ay_ambm_batch_witnesses_unsat
    (satWitnesses unsatWitnesses sharedRoot : Prop) :
    AyAMBMBatchWitnesses satWitnesses unsatWitnesses sharedRoot ->
    unsatWitnesses :=
  fun witnesses =>
    ay_ambm_conj_right satWitnesses
      (AyAMBMConj unsatWitnesses sharedRoot)
      witnesses unsatWitnesses
      (fun unsatProof _rootProof => unsatProof)

theorem ay_ambm_batch_witnesses_root
    (satWitnesses unsatWitnesses sharedRoot : Prop) :
    AyAMBMBatchWitnesses satWitnesses unsatWitnesses sharedRoot ->
    sharedRoot :=
  fun witnesses =>
    ay_ambm_conj_right satWitnesses
      (AyAMBMConj unsatWitnesses sharedRoot)
      witnesses sharedRoot (fun _unsatProof rootProof => rootProof)

theorem ay_ambm_root_agreement_intro
    (declaredRoot checkedRoot sharedRoot : Prop) :
    declaredRoot -> checkedRoot -> sharedRoot ->
    AyAMBMRootAgreement declaredRoot checkedRoot sharedRoot :=
  fun declaredProof checkedProof sharedProof =>
    ay_ambm_conj_intro declaredRoot
      (AyAMBMConj checkedRoot sharedRoot)
      declaredProof
      (ay_ambm_conj_intro checkedRoot sharedRoot checkedProof sharedProof)

theorem ay_ambm_root_agreement_declared
    (declaredRoot checkedRoot sharedRoot : Prop) :
    AyAMBMRootAgreement declaredRoot checkedRoot sharedRoot ->
    declaredRoot :=
  fun agreement =>
    ay_ambm_conj_left declaredRoot
      (AyAMBMConj checkedRoot sharedRoot) agreement

theorem ay_ambm_root_agreement_checked
    (declaredRoot checkedRoot sharedRoot : Prop) :
    AyAMBMRootAgreement declaredRoot checkedRoot sharedRoot ->
    checkedRoot :=
  fun agreement =>
    ay_ambm_conj_right declaredRoot
      (AyAMBMConj checkedRoot sharedRoot)
      agreement checkedRoot (fun checkedProof _sharedProof => checkedProof)

theorem ay_ambm_root_agreement_shared
    (declaredRoot checkedRoot sharedRoot : Prop) :
    AyAMBMRootAgreement declaredRoot checkedRoot sharedRoot ->
    sharedRoot :=
  fun agreement =>
    ay_ambm_conj_right declaredRoot
      (AyAMBMConj checkedRoot sharedRoot)
      agreement sharedRoot (fun _checkedProof sharedProof => sharedProof)

theorem ay_ambm_accepted_batch_intro
    (batchEntries batchWitnesses rootAgreement reportDigest : Prop) :
    batchEntries -> batchWitnesses -> rootAgreement -> reportDigest ->
    AyAMBMAcceptedBatch batchEntries batchWitnesses rootAgreement
      reportDigest :=
  fun entriesProof witnessesProof rootProof reportProof =>
    ay_ambm_conj_intro batchEntries
      (AyAMBMConj batchWitnesses
        (AyAMBMConj rootAgreement reportDigest))
      entriesProof
      (ay_ambm_conj_intro batchWitnesses
        (AyAMBMConj rootAgreement reportDigest)
        witnessesProof
        (ay_ambm_conj_intro rootAgreement reportDigest rootProof
          reportProof))

theorem ay_ambm_accepted_batch_entries
    (batchEntries batchWitnesses rootAgreement reportDigest : Prop) :
    AyAMBMAcceptedBatch batchEntries batchWitnesses rootAgreement
      reportDigest ->
    batchEntries :=
  fun batch =>
    ay_ambm_conj_left batchEntries
      (AyAMBMConj batchWitnesses
        (AyAMBMConj rootAgreement reportDigest))
      batch

theorem ay_ambm_accepted_batch_witnesses
    (batchEntries batchWitnesses rootAgreement reportDigest : Prop) :
    AyAMBMAcceptedBatch batchEntries batchWitnesses rootAgreement
      reportDigest ->
    batchWitnesses :=
  fun batch =>
    ay_ambm_conj_right batchEntries
      (AyAMBMConj batchWitnesses
        (AyAMBMConj rootAgreement reportDigest))
      batch batchWitnesses (fun witnessesProof _tail => witnessesProof)

theorem ay_ambm_accepted_batch_root_agreement
    (batchEntries batchWitnesses rootAgreement reportDigest : Prop) :
    AyAMBMAcceptedBatch batchEntries batchWitnesses rootAgreement
      reportDigest ->
    rootAgreement :=
  fun batch =>
    ay_ambm_conj_right batchEntries
      (AyAMBMConj batchWitnesses
        (AyAMBMConj rootAgreement reportDigest))
      batch rootAgreement
      (fun _witnessesProof tail =>
        tail rootAgreement (fun rootProof _reportProof => rootProof))

theorem ay_ambm_rejected_batch_intro
    (failedWitnesses auditDigest diagnostic : Prop) :
    failedWitnesses -> auditDigest -> diagnostic ->
    AyAMBMRejectedBatch failedWitnesses auditDigest diagnostic :=
  fun failedProof auditProof diagnosticProof =>
    ay_ambm_conj_intro failedWitnesses
      (AyAMBMConj auditDigest diagnostic)
      failedProof
      (ay_ambm_conj_intro auditDigest diagnostic auditProof
        diagnosticProof)

theorem ay_ambm_no_claim_intro
    (reason auditDigest diagnostic : Prop) :
    reason -> auditDigest -> diagnostic ->
    AyAMBMNoClaim reason auditDigest diagnostic :=
  fun reasonProof auditProof diagnosticProof =>
    ay_ambm_conj_intro reason (AyAMBMConj auditDigest diagnostic)
      reasonProof
      (ay_ambm_conj_intro auditDigest diagnostic auditProof
        diagnosticProof)

theorem ay_ambm_rejected_batch_no_claim
    (failedWitnesses auditDigest diagnostic : Prop) :
    AyAMBMRejectedBatch failedWitnesses auditDigest diagnostic ->
    AyAMBMNoClaim failedWitnesses auditDigest diagnostic :=
  fun rejected =>
    ay_ambm_conj_intro failedWitnesses
      (AyAMBMConj auditDigest diagnostic)
      (ay_ambm_conj_left failedWitnesses
        (AyAMBMConj auditDigest diagnostic) rejected)
      (ay_ambm_conj_right failedWitnesses
        (AyAMBMConj auditDigest diagnostic) rejected)

theorem ay_ambm_preprocess_model_reconstruct
    (original solver internalAssignment visibleAssignment : Prop) :
    AyAMBMPreprocessArtifact original solver ->
    (internalAssignment -> visibleAssignment) ->
    AyAMBMModel solver internalAssignment ->
    AyAMBMVisibleSAT original visibleAssignment :=
  fun preprocess decode model =>
    ay_ambm_model_intro original visibleAssignment
      (ay_ambm_equisat_backward original solver preprocess
        (ay_ambm_model_formula solver internalAssignment model))
      (decode (ay_ambm_model_assignment solver internalAssignment model))

theorem ay_ambm_preprocess_unsat_reconstruct
    (original solver : Prop) :
    AyAMBMPreprocessArtifact original solver ->
    AyAMBMUnsat solver ->
    AyAMBMUnsat original :=
  fun preprocess solverUnsat originalProof =>
    solverUnsat
      (ay_ambm_equisat_forward original solver preprocess originalProof)

theorem ay_ambm_replay_unsat_public
    (original solver stream finalClause : Prop) :
    AyAMBMPreprocessArtifact original solver ->
    AyAMBMReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    stream ->
    AyAMBMUnsat original :=
  fun preprocess replay closeFinal streamProof originalProof =>
    closeFinal
      (replay streamProof
        (ay_ambm_equisat_forward original solver preprocess originalProof))

theorem ay_ambm_retained_sat_membership_sound
    (leafHash root acceptedSat artifacts satBranch auditDigest diagnostic
      original solver internalAssignment visibleAssignment : Prop) :
    AyAMBMPreprocessArtifact original solver ->
    (internalAssignment -> visibleAssignment) ->
    (satBranch -> AyAMBMModel solver internalAssignment) ->
    AyAMBMMembership leafHash root
      (AyAMBMEntry acceptedSat artifacts satBranch auditDigest diagnostic) ->
    AyAMBMVisibleSAT original visibleAssignment :=
  fun preprocess decode accept membership =>
    ay_ambm_preprocess_model_reconstruct original solver internalAssignment
      visibleAssignment preprocess decode
      (accept
        (ay_ambm_entry_checker acceptedSat artifacts satBranch auditDigest
          diagnostic
          (ay_ambm_membership_entry leafHash root
            (AyAMBMEntry acceptedSat artifacts satBranch auditDigest
              diagnostic)
            membership)))

theorem ay_ambm_retained_unsat_membership_sound
    (leafHash root acceptedUnsat artifacts unsatBranch auditDigest diagnostic
      original solver stream finalClause : Prop) :
    AyAMBMPreprocessArtifact original solver ->
    AyAMBMReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    (unsatBranch -> stream) ->
    AyAMBMMembership leafHash root
      (AyAMBMEntry acceptedUnsat artifacts unsatBranch auditDigest
        diagnostic) ->
    AyAMBMUnsat original :=
  fun preprocess replay closeFinal accept membership =>
    ay_ambm_replay_unsat_public original solver stream finalClause preprocess
      replay closeFinal
      (accept
        (ay_ambm_entry_checker acceptedUnsat artifacts unsatBranch auditDigest
          diagnostic
          (ay_ambm_membership_entry leafHash root
            (AyAMBMEntry acceptedUnsat artifacts unsatBranch auditDigest
              diagnostic)
            membership)))

theorem ay_ambm_accepted_batch_preserves_root_agreement
    (batchEntries batchWitnesses rootAgreement reportDigest : Prop) :
    AyAMBMAcceptedBatch batchEntries batchWitnesses rootAgreement
      reportDigest ->
    rootAgreement :=
  ay_ambm_accepted_batch_root_agreement batchEntries batchWitnesses
    rootAgreement reportDigest

theorem ay_ambm_accepted_batch_preserves_sat_claim
    (batchEntries batchWitnesses rootAgreement reportDigest satFact : Prop) :
    AyAMBMAcceptedBatch batchEntries batchWitnesses rootAgreement
      reportDigest ->
    (batchWitnesses -> rootAgreement -> satFact) ->
    satFact :=
  fun batch sound =>
    sound
      (ay_ambm_accepted_batch_witnesses batchEntries batchWitnesses
        rootAgreement reportDigest batch)
      (ay_ambm_accepted_batch_root_agreement batchEntries batchWitnesses
        rootAgreement reportDigest batch)

theorem ay_ambm_accepted_batch_preserves_unsat_claim
    (batchEntries batchWitnesses rootAgreement reportDigest unsatFact :
      Prop) :
    AyAMBMAcceptedBatch batchEntries batchWitnesses rootAgreement
      reportDigest ->
    (batchWitnesses -> rootAgreement -> unsatFact) ->
    unsatFact :=
  fun batch sound =>
    sound
      (ay_ambm_accepted_batch_witnesses batchEntries batchWitnesses
        rootAgreement reportDigest batch)
      (ay_ambm_accepted_batch_root_agreement batchEntries batchWitnesses
        rootAgreement reportDigest batch)

theorem ay_ambm_accepted_batch_public_result_sound
    (batchEntries batchWitnesses rootAgreement reportDigest satFact unsatFact
      noClaim : Prop) :
    AyAMBMAcceptedBatch batchEntries batchWitnesses rootAgreement
      reportDigest ->
    (batchEntries -> batchWitnesses -> rootAgreement ->
      AyAMBMPublicResult satFact unsatFact noClaim) ->
    AyAMBMPublicResult satFact unsatFact noClaim :=
  fun batch sound =>
    sound
      (ay_ambm_accepted_batch_entries batchEntries batchWitnesses
        rootAgreement reportDigest batch)
      (ay_ambm_accepted_batch_witnesses batchEntries batchWitnesses
        rootAgreement reportDigest batch)
      (ay_ambm_accepted_batch_root_agreement batchEntries batchWitnesses
        rootAgreement reportDigest batch)

theorem ay_ambm_missing_witness_no_claim
    (missingWitness auditDigest diagnostic : Prop) :
    missingWitness -> auditDigest -> diagnostic ->
    AyAMBMNoClaim missingWitness auditDigest diagnostic :=
  ay_ambm_no_claim_intro missingWitness auditDigest diagnostic

theorem ay_ambm_bad_witness_no_claim
    (badWitness auditDigest diagnostic : Prop) :
    badWitness -> auditDigest -> diagnostic ->
    AyAMBMNoClaim badWitness auditDigest diagnostic :=
  ay_ambm_no_claim_intro badWitness auditDigest diagnostic

theorem ay_ambm_rejected_batch_public_result_no_claim
    (satFact unsatFact failedWitnesses auditDigest diagnostic : Prop) :
    AyAMBMRejectedBatch failedWitnesses auditDigest diagnostic ->
    AyAMBMPublicResult satFact unsatFact
      (AyAMBMNoClaim failedWitnesses auditDigest diagnostic) :=
  fun rejected =>
    ay_ambm_disj_right satFact
      (AyAMBMDisj unsatFact
        (AyAMBMNoClaim failedWitnesses auditDigest diagnostic))
      (ay_ambm_disj_right unsatFact
        (AyAMBMNoClaim failedWitnesses auditDigest diagnostic)
        (ay_ambm_rejected_batch_no_claim failedWitnesses auditDigest
          diagnostic rejected))

theorem ay_ambm_partial_batch_no_claim
    (partialFailure auditDigest diagnostic : Prop) :
    partialFailure -> auditDigest -> diagnostic ->
    AyAMBMNoClaim partialFailure auditDigest diagnostic :=
  ay_ambm_no_claim_intro partialFailure auditDigest diagnostic

theorem ay_ambm_failed_witnesses_no_sat_or_unsat_claim
    (missingWitness badWitness auditDigest diagnostic noClaim : Prop) :
    AyAMBMDisj missingWitness badWitness ->
    auditDigest -> diagnostic ->
    (missingWitness ->
      AyAMBMNoClaim missingWitness auditDigest diagnostic -> noClaim) ->
    (badWitness ->
      AyAMBMNoClaim badWitness auditDigest diagnostic -> noClaim) ->
    noClaim :=
  fun failure auditProof diagnosticProof onMissing onBad =>
    failure noClaim
      (fun missingProof =>
        onMissing missingProof
          (ay_ambm_missing_witness_no_claim missingWitness auditDigest
            diagnostic missingProof auditProof diagnosticProof))
      (fun badProof =>
        onBad badProof
          (ay_ambm_bad_witness_no_claim badWitness auditDigest diagnostic
            badProof auditProof diagnosticProof))
