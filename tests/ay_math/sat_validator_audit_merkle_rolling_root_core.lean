-- SAT-COMP validator audit Merkle rolling-root core.
--
-- Rolling checkpoints rotate bounded audit artifacts from an old root to a new
-- root.  Accepted claims survive only through retained memberships and a
-- checked append-only rotation witness; skipped or bad transitions become
-- explicit no-claim diagnostics.

def AyAMRRConj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def AyAMRRDisj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyAMRREquisat (before after : Prop) : Prop :=
  AyAMRRConj (before -> after) (after -> before)

def AyAMRRPublicResult (satFact unsatFact noClaim : Prop) : Prop :=
  AyAMRRDisj satFact (AyAMRRDisj unsatFact noClaim)

def AyAMRRArtifacts (certId archiveKey : Prop) : Prop :=
  AyAMRRConj certId archiveKey

def AyAMRREntry
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    Prop :=
  AyAMRRConj exitCode
    (AyAMRRConj artifacts
      (AyAMRRConj checkerDecision
        (AyAMRRConj auditDigest diagnostic)))

def AyAMRRMembership (leafHash root entry : Prop) : Prop :=
  AyAMRRConj leafHash (AyAMRRConj root entry)

def AyAMRRRootSequence (oldRoot newRoot sequenceDigest : Prop) : Prop :=
  AyAMRRConj oldRoot (AyAMRRConj newRoot sequenceDigest)

def AyAMRRSuffixAppend (oldLog suffixLog newLog : Prop) : Prop :=
  AyAMRRConj oldLog (AyAMRRConj suffixLog newLog)

def AyAMRRRetainedMemberships (oldRetained newRetained retainedDigest :
    Prop) : Prop :=
  AyAMRRConj oldRetained (AyAMRRConj newRetained retainedDigest)

def AyAMRRRootRotation
    (rootSequence suffixAppend retainedMemberships rotationDigest : Prop) :
    Prop :=
  AyAMRRConj rootSequence
    (AyAMRRConj suffixAppend
      (AyAMRRConj retainedMemberships rotationDigest))

def AyAMRRRotationFailure (failureKind auditDigest diagnostic : Prop) :
    Prop :=
  AyAMRRConj failureKind (AyAMRRConj auditDigest diagnostic)

def AyAMRRNoClaim (reason auditDigest diagnostic : Prop) : Prop :=
  AyAMRRConj reason (AyAMRRConj auditDigest diagnostic)

def AyAMRRModel (formula assignment : Prop) : Prop :=
  AyAMRRConj formula assignment

def AyAMRRUnsat (formula : Prop) : Prop :=
  formula -> False

def AyAMRRVisibleSAT (original visibleAssignment : Prop) : Prop :=
  AyAMRRModel original visibleAssignment

def AyAMRRPreprocessArtifact (original solver : Prop) : Prop :=
  AyAMRREquisat original solver

def AyAMRRReplayAccepted (solver stream finalClause : Prop) : Prop :=
  stream -> solver -> finalClause

theorem ay_amrr_conj_intro (left right : Prop) :
    left -> right -> AyAMRRConj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_amrr_conj_left (left right : Prop) :
    AyAMRRConj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_amrr_conj_right (left right : Prop) :
    AyAMRRConj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_amrr_disj_left (left right : Prop) :
    left -> AyAMRRDisj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_amrr_disj_right (left right : Prop) :
    right -> AyAMRRDisj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_amrr_equisat_forward (before after : Prop) :
    AyAMRREquisat before after -> before -> after :=
  fun witness hbefore =>
    witness after (fun forward _backward => forward hbefore)

theorem ay_amrr_equisat_backward (before after : Prop) :
    AyAMRREquisat before after -> after -> before :=
  fun witness hafter =>
    witness before (fun _forward backward => backward hafter)

theorem ay_amrr_model_intro (formula assignment : Prop) :
    formula -> assignment -> AyAMRRModel formula assignment :=
  fun formulaProof assignmentProof =>
    ay_amrr_conj_intro formula assignment formulaProof assignmentProof

theorem ay_amrr_model_formula (formula assignment : Prop) :
    AyAMRRModel formula assignment -> formula :=
  fun model => ay_amrr_conj_left formula assignment model

theorem ay_amrr_model_assignment (formula assignment : Prop) :
    AyAMRRModel formula assignment -> assignment :=
  fun model => ay_amrr_conj_right formula assignment model

theorem ay_amrr_entry_intro
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    exitCode -> artifacts -> checkerDecision -> auditDigest -> diagnostic ->
    AyAMRREntry exitCode artifacts checkerDecision auditDigest diagnostic :=
  fun exitProof artifactsProof checkerProof auditProof diagnosticProof =>
    ay_amrr_conj_intro exitCode
      (AyAMRRConj artifacts
        (AyAMRRConj checkerDecision (AyAMRRConj auditDigest diagnostic)))
      exitProof
      (ay_amrr_conj_intro artifacts
        (AyAMRRConj checkerDecision (AyAMRRConj auditDigest diagnostic))
        artifactsProof
        (ay_amrr_conj_intro checkerDecision
          (AyAMRRConj auditDigest diagnostic)
          checkerProof
          (ay_amrr_conj_intro auditDigest diagnostic auditProof
            diagnosticProof)))

theorem ay_amrr_entry_checker
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    AyAMRREntry exitCode artifacts checkerDecision auditDigest diagnostic ->
    checkerDecision :=
  fun entry =>
    ay_amrr_conj_right exitCode
      (AyAMRRConj artifacts
        (AyAMRRConj checkerDecision (AyAMRRConj auditDigest diagnostic)))
      entry checkerDecision
      (fun _artifactsProof tail =>
        tail checkerDecision (fun checkerProof _auditTail => checkerProof))

theorem ay_amrr_entry_audit
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    AyAMRREntry exitCode artifacts checkerDecision auditDigest diagnostic ->
    auditDigest :=
  fun entry =>
    ay_amrr_conj_right exitCode
      (AyAMRRConj artifacts
        (AyAMRRConj checkerDecision (AyAMRRConj auditDigest diagnostic)))
      entry auditDigest
      (fun _artifactsProof tail =>
        tail auditDigest
          (fun _checkerProof auditTail =>
            auditTail auditDigest
              (fun auditProof _diagnosticProof => auditProof)))

theorem ay_amrr_entry_diagnostic
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    AyAMRREntry exitCode artifacts checkerDecision auditDigest diagnostic ->
    diagnostic :=
  fun entry =>
    ay_amrr_conj_right exitCode
      (AyAMRRConj artifacts
        (AyAMRRConj checkerDecision (AyAMRRConj auditDigest diagnostic)))
      entry diagnostic
      (fun _artifactsProof tail =>
        tail diagnostic
          (fun _checkerProof auditTail =>
            auditTail diagnostic
              (fun _auditProof diagnosticProof => diagnosticProof)))

theorem ay_amrr_membership_intro (leafHash root entry : Prop) :
    leafHash -> root -> entry -> AyAMRRMembership leafHash root entry :=
  fun leafProof rootProof entryProof =>
    ay_amrr_conj_intro leafHash (AyAMRRConj root entry)
      leafProof
      (ay_amrr_conj_intro root entry rootProof entryProof)

theorem ay_amrr_membership_root (leafHash root entry : Prop) :
    AyAMRRMembership leafHash root entry -> root :=
  fun membership =>
    ay_amrr_conj_right leafHash (AyAMRRConj root entry) membership
      root (fun rootProof _entryProof => rootProof)

theorem ay_amrr_membership_entry (leafHash root entry : Prop) :
    AyAMRRMembership leafHash root entry -> entry :=
  fun membership =>
    ay_amrr_conj_right leafHash (AyAMRRConj root entry) membership
      entry (fun _rootProof entryProof => entryProof)

theorem ay_amrr_root_sequence_intro
    (oldRoot newRoot sequenceDigest : Prop) :
    oldRoot -> newRoot -> sequenceDigest ->
    AyAMRRRootSequence oldRoot newRoot sequenceDigest :=
  fun oldProof newProof digestProof =>
    ay_amrr_conj_intro oldRoot (AyAMRRConj newRoot sequenceDigest)
      oldProof
      (ay_amrr_conj_intro newRoot sequenceDigest newProof digestProof)

theorem ay_amrr_root_sequence_old
    (oldRoot newRoot sequenceDigest : Prop) :
    AyAMRRRootSequence oldRoot newRoot sequenceDigest -> oldRoot :=
  fun roots =>
    ay_amrr_conj_left oldRoot (AyAMRRConj newRoot sequenceDigest) roots

theorem ay_amrr_root_sequence_new
    (oldRoot newRoot sequenceDigest : Prop) :
    AyAMRRRootSequence oldRoot newRoot sequenceDigest -> newRoot :=
  fun roots =>
    ay_amrr_conj_right oldRoot (AyAMRRConj newRoot sequenceDigest)
      roots newRoot (fun newProof _digestProof => newProof)

theorem ay_amrr_suffix_append_intro
    (oldLog suffixLog newLog : Prop) :
    oldLog -> suffixLog -> newLog ->
    AyAMRRSuffixAppend oldLog suffixLog newLog :=
  fun oldProof suffixProof newProof =>
    ay_amrr_conj_intro oldLog (AyAMRRConj suffixLog newLog)
      oldProof
      (ay_amrr_conj_intro suffixLog newLog suffixProof newProof)

theorem ay_amrr_suffix_append_old
    (oldLog suffixLog newLog : Prop) :
    AyAMRRSuffixAppend oldLog suffixLog newLog -> oldLog :=
  fun append =>
    ay_amrr_conj_left oldLog (AyAMRRConj suffixLog newLog) append

theorem ay_amrr_suffix_append_new
    (oldLog suffixLog newLog : Prop) :
    AyAMRRSuffixAppend oldLog suffixLog newLog -> newLog :=
  fun append =>
    ay_amrr_conj_right oldLog (AyAMRRConj suffixLog newLog)
      append newLog (fun _suffixProof newProof => newProof)

theorem ay_amrr_retained_memberships_intro
    (oldRetained newRetained retainedDigest : Prop) :
    oldRetained -> newRetained -> retainedDigest ->
    AyAMRRRetainedMemberships oldRetained newRetained retainedDigest :=
  fun oldProof newProof digestProof =>
    ay_amrr_conj_intro oldRetained
      (AyAMRRConj newRetained retainedDigest)
      oldProof
      (ay_amrr_conj_intro newRetained retainedDigest newProof digestProof)

theorem ay_amrr_retained_old
    (oldRetained newRetained retainedDigest : Prop) :
    AyAMRRRetainedMemberships oldRetained newRetained retainedDigest ->
    oldRetained :=
  fun retained =>
    ay_amrr_conj_left oldRetained
      (AyAMRRConj newRetained retainedDigest) retained

theorem ay_amrr_retained_new
    (oldRetained newRetained retainedDigest : Prop) :
    AyAMRRRetainedMemberships oldRetained newRetained retainedDigest ->
    newRetained :=
  fun retained =>
    ay_amrr_conj_right oldRetained
      (AyAMRRConj newRetained retainedDigest)
      retained newRetained (fun newProof _digestProof => newProof)

theorem ay_amrr_root_rotation_intro
    (rootSequence suffixAppend retainedMemberships rotationDigest : Prop) :
    rootSequence -> suffixAppend -> retainedMemberships -> rotationDigest ->
    AyAMRRRootRotation rootSequence suffixAppend retainedMemberships
      rotationDigest :=
  fun rootsProof appendProof retainedProof digestProof =>
    ay_amrr_conj_intro rootSequence
      (AyAMRRConj suffixAppend
        (AyAMRRConj retainedMemberships rotationDigest))
      rootsProof
      (ay_amrr_conj_intro suffixAppend
        (AyAMRRConj retainedMemberships rotationDigest)
        appendProof
        (ay_amrr_conj_intro retainedMemberships rotationDigest
          retainedProof digestProof))

theorem ay_amrr_rotation_roots
    (rootSequence suffixAppend retainedMemberships rotationDigest : Prop) :
    AyAMRRRootRotation rootSequence suffixAppend retainedMemberships
      rotationDigest ->
    rootSequence :=
  fun rotation =>
    ay_amrr_conj_left rootSequence
      (AyAMRRConj suffixAppend
        (AyAMRRConj retainedMemberships rotationDigest))
      rotation

theorem ay_amrr_rotation_append
    (rootSequence suffixAppend retainedMemberships rotationDigest : Prop) :
    AyAMRRRootRotation rootSequence suffixAppend retainedMemberships
      rotationDigest ->
    suffixAppend :=
  fun rotation =>
    ay_amrr_conj_right rootSequence
      (AyAMRRConj suffixAppend
        (AyAMRRConj retainedMemberships rotationDigest))
      rotation suffixAppend
      (fun appendProof _tail => appendProof)

theorem ay_amrr_rotation_retained
    (rootSequence suffixAppend retainedMemberships rotationDigest : Prop) :
    AyAMRRRootRotation rootSequence suffixAppend retainedMemberships
      rotationDigest ->
    retainedMemberships :=
  fun rotation =>
    ay_amrr_conj_right rootSequence
      (AyAMRRConj suffixAppend
        (AyAMRRConj retainedMemberships rotationDigest))
      rotation retainedMemberships
      (fun _appendProof tail =>
        tail retainedMemberships
          (fun retainedProof _digestProof => retainedProof))

theorem ay_amrr_rotation_failure_intro
    (failureKind auditDigest diagnostic : Prop) :
    failureKind -> auditDigest -> diagnostic ->
    AyAMRRRotationFailure failureKind auditDigest diagnostic :=
  fun failureProof auditProof diagnosticProof =>
    ay_amrr_conj_intro failureKind (AyAMRRConj auditDigest diagnostic)
      failureProof
      (ay_amrr_conj_intro auditDigest diagnostic auditProof
        diagnosticProof)

theorem ay_amrr_rotation_failure_no_claim
    (failureKind auditDigest diagnostic : Prop) :
    AyAMRRRotationFailure failureKind auditDigest diagnostic ->
    AyAMRRNoClaim failureKind auditDigest diagnostic :=
  fun failure =>
    ay_amrr_conj_intro failureKind (AyAMRRConj auditDigest diagnostic)
      (ay_amrr_conj_left failureKind
        (AyAMRRConj auditDigest diagnostic) failure)
      (ay_amrr_conj_right failureKind
        (AyAMRRConj auditDigest diagnostic) failure)

theorem ay_amrr_no_claim_intro
    (reason auditDigest diagnostic : Prop) :
    reason -> auditDigest -> diagnostic ->
    AyAMRRNoClaim reason auditDigest diagnostic :=
  fun reasonProof auditProof diagnosticProof =>
    ay_amrr_conj_intro reason (AyAMRRConj auditDigest diagnostic)
      reasonProof
      (ay_amrr_conj_intro auditDigest diagnostic auditProof
        diagnosticProof)

theorem ay_amrr_preprocess_model_reconstruct
    (original solver internalAssignment visibleAssignment : Prop) :
    AyAMRRPreprocessArtifact original solver ->
    (internalAssignment -> visibleAssignment) ->
    AyAMRRModel solver internalAssignment ->
    AyAMRRVisibleSAT original visibleAssignment :=
  fun preprocess decode model =>
    ay_amrr_model_intro original visibleAssignment
      (ay_amrr_equisat_backward original solver preprocess
        (ay_amrr_model_formula solver internalAssignment model))
      (decode (ay_amrr_model_assignment solver internalAssignment model))

theorem ay_amrr_preprocess_unsat_reconstruct
    (original solver : Prop) :
    AyAMRRPreprocessArtifact original solver ->
    AyAMRRUnsat solver ->
    AyAMRRUnsat original :=
  fun preprocess solverUnsat originalProof =>
    solverUnsat
      (ay_amrr_equisat_forward original solver preprocess originalProof)

theorem ay_amrr_replay_unsat_public
    (original solver stream finalClause : Prop) :
    AyAMRRPreprocessArtifact original solver ->
    AyAMRRReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    stream ->
    AyAMRRUnsat original :=
  fun preprocess replay closeFinal streamProof originalProof =>
    closeFinal
      (replay streamProof
        (ay_amrr_equisat_forward original solver preprocess originalProof))

theorem ay_amrr_retained_sat_membership_sound
    (leafHash root acceptedSat artifacts satBranch auditDigest diagnostic
      original solver internalAssignment visibleAssignment : Prop) :
    AyAMRRPreprocessArtifact original solver ->
    (internalAssignment -> visibleAssignment) ->
    (satBranch -> AyAMRRModel solver internalAssignment) ->
    AyAMRRMembership leafHash root
      (AyAMRREntry acceptedSat artifacts satBranch auditDigest diagnostic) ->
    AyAMRRVisibleSAT original visibleAssignment :=
  fun preprocess decode accept membership =>
    ay_amrr_preprocess_model_reconstruct original solver internalAssignment
      visibleAssignment preprocess decode
      (accept
        (ay_amrr_entry_checker acceptedSat artifacts satBranch auditDigest
          diagnostic
          (ay_amrr_membership_entry leafHash root
            (AyAMRREntry acceptedSat artifacts satBranch auditDigest
              diagnostic)
            membership)))

theorem ay_amrr_retained_unsat_membership_sound
    (leafHash root acceptedUnsat artifacts unsatBranch auditDigest diagnostic
      original solver stream finalClause : Prop) :
    AyAMRRPreprocessArtifact original solver ->
    AyAMRRReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    (unsatBranch -> stream) ->
    AyAMRRMembership leafHash root
      (AyAMRREntry acceptedUnsat artifacts unsatBranch auditDigest
        diagnostic) ->
    AyAMRRUnsat original :=
  fun preprocess replay closeFinal accept membership =>
    ay_amrr_replay_unsat_public original solver stream finalClause preprocess
      replay closeFinal
      (accept
        (ay_amrr_entry_checker acceptedUnsat artifacts unsatBranch auditDigest
          diagnostic
          (ay_amrr_membership_entry leafHash root
            (AyAMRREntry acceptedUnsat artifacts unsatBranch auditDigest
              diagnostic)
            membership)))

theorem ay_amrr_rotation_preserves_prior_public_claim
    (rootSequence suffixAppend retainedMemberships rotationDigest
      satFact unsatFact noClaim : Prop) :
    AyAMRRRootRotation rootSequence suffixAppend retainedMemberships
      rotationDigest ->
    (retainedMemberships -> AyAMRRPublicResult satFact unsatFact noClaim) ->
    AyAMRRPublicResult satFact unsatFact noClaim :=
  fun rotation retainedSound =>
    retainedSound
      (ay_amrr_rotation_retained rootSequence suffixAppend
        retainedMemberships rotationDigest rotation)

theorem ay_amrr_rotation_preserves_append_only
    (rootSequence suffixAppend retainedMemberships rotationDigest : Prop) :
    AyAMRRRootRotation rootSequence suffixAppend retainedMemberships
      rotationDigest ->
    suffixAppend :=
  ay_amrr_rotation_append rootSequence suffixAppend retainedMemberships
    rotationDigest

theorem ay_amrr_rotation_public_result_sound
    (rootSequence suffixAppend retainedMemberships rotationDigest
      satFact unsatFact noClaim : Prop) :
    AyAMRRRootRotation rootSequence suffixAppend retainedMemberships
      rotationDigest ->
    (rootSequence -> suffixAppend -> retainedMemberships ->
      AyAMRRPublicResult satFact unsatFact noClaim) ->
    AyAMRRPublicResult satFact unsatFact noClaim :=
  fun rotation sound =>
    sound
      (ay_amrr_rotation_roots rootSequence suffixAppend retainedMemberships
        rotationDigest rotation)
      (ay_amrr_rotation_append rootSequence suffixAppend retainedMemberships
        rotationDigest rotation)
      (ay_amrr_rotation_retained rootSequence suffixAppend
        retainedMemberships rotationDigest rotation)

theorem ay_amrr_skipped_transition_no_claim
    (skippedTransition auditDigest diagnostic : Prop) :
    skippedTransition -> auditDigest -> diagnostic ->
    AyAMRRNoClaim skippedTransition auditDigest diagnostic :=
  ay_amrr_no_claim_intro skippedTransition auditDigest diagnostic

theorem ay_amrr_bad_root_transition_no_claim
    (badRootTransition auditDigest diagnostic : Prop) :
    badRootTransition -> auditDigest -> diagnostic ->
    AyAMRRNoClaim badRootTransition auditDigest diagnostic :=
  ay_amrr_no_claim_intro badRootTransition auditDigest diagnostic

theorem ay_amrr_failure_public_result_no_claim
    (satFact unsatFact failureKind auditDigest diagnostic : Prop) :
    AyAMRRRotationFailure failureKind auditDigest diagnostic ->
    AyAMRRPublicResult satFact unsatFact
      (AyAMRRNoClaim failureKind auditDigest diagnostic) :=
  fun failure =>
    ay_amrr_disj_right satFact
      (AyAMRRDisj unsatFact
        (AyAMRRNoClaim failureKind auditDigest diagnostic))
      (ay_amrr_disj_right unsatFact
        (AyAMRRNoClaim failureKind auditDigest diagnostic)
        (ay_amrr_rotation_failure_no_claim failureKind auditDigest
          diagnostic failure))

theorem ay_amrr_skipped_or_bad_transition_no_claim
    (skippedTransition badRootTransition auditDigest diagnostic noClaim :
      Prop) :
    AyAMRRDisj skippedTransition badRootTransition ->
    auditDigest -> diagnostic ->
    (skippedTransition ->
      AyAMRRNoClaim skippedTransition auditDigest diagnostic -> noClaim) ->
    (badRootTransition ->
      AyAMRRNoClaim badRootTransition auditDigest diagnostic -> noClaim) ->
    noClaim :=
  fun failure auditProof diagnosticProof onSkipped onBad =>
    failure noClaim
      (fun skippedProof =>
        onSkipped skippedProof
          (ay_amrr_skipped_transition_no_claim skippedTransition auditDigest
            diagnostic skippedProof auditProof diagnosticProof))
      (fun badProof =>
        onBad badProof
          (ay_amrr_bad_root_transition_no_claim badRootTransition auditDigest
            diagnostic badProof auditProof diagnosticProof))

theorem ay_amrr_failure_cannot_expose_sat_claim
    (failureKind auditDigest diagnostic noClaim : Prop) :
    AyAMRRRotationFailure failureKind auditDigest diagnostic ->
    (AyAMRRNoClaim failureKind auditDigest diagnostic -> noClaim) ->
    noClaim :=
  fun failure toNoClaim =>
    toNoClaim
      (ay_amrr_rotation_failure_no_claim failureKind auditDigest diagnostic
        failure)

theorem ay_amrr_failure_cannot_expose_unsat_claim
    (failureKind auditDigest diagnostic noClaim : Prop) :
    AyAMRRRotationFailure failureKind auditDigest diagnostic ->
    (AyAMRRNoClaim failureKind auditDigest diagnostic -> noClaim) ->
    noClaim :=
  fun failure toNoClaim =>
    toNoClaim
      (ay_amrr_rotation_failure_no_claim failureKind auditDigest diagnostic
        failure)
