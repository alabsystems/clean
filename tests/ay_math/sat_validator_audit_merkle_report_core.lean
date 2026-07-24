-- SAT-COMP validator audit Merkle-report core.
--
-- Reports are backed by Merkle membership for their hashed audit entry.  An
-- accepted SAT/UNSAT membership exposes the same soundness theorem as the
-- report entry; diagnostic membership remains an explicit no-claim.

def AyAMRConj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def AyAMRDisj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyAMREquisat (before after : Prop) : Prop :=
  AyAMRConj (before -> after) (after -> before)

def AyAMROutcome (sat unsat : Prop) : Prop :=
  AyAMRDisj sat unsat

def AyAMRPublicResult (satFact unsatFact noClaim : Prop) : Prop :=
  AyAMRDisj satFact (AyAMRDisj unsatFact noClaim)

def AyAMRArtifacts (certId archiveKey : Prop) : Prop :=
  AyAMRConj certId archiveKey

def AyAMREntry
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    Prop :=
  AyAMRConj exitCode
    (AyAMRConj artifacts
      (AyAMRConj checkerDecision
        (AyAMRConj auditDigest diagnostic)))

def AyAMRLeafHash (entry leafHash : Prop) : Prop :=
  AyAMRConj entry leafHash

def AyAMRMembership (leafHash root entry : Prop) : Prop :=
  AyAMRConj leafHash (AyAMRConj root entry)

def AyAMRReport (entry leafHash root : Prop) : Prop :=
  AyAMRConj (AyAMRLeafHash entry leafHash)
    (AyAMRMembership leafHash root entry)

def AyAMRNoClaim (exitCode auditDigest diagnostic : Prop) : Prop :=
  AyAMRConj exitCode (AyAMRConj auditDigest diagnostic)

def AyAMRModel (formula assignment : Prop) : Prop :=
  AyAMRConj formula assignment

def AyAMRUnsat (formula : Prop) : Prop :=
  formula -> False

def AyAMRVisibleSAT (original visibleAssignment : Prop) : Prop :=
  AyAMRModel original visibleAssignment

def AyAMRPreprocessArtifact (original solver : Prop) : Prop :=
  AyAMREquisat original solver

def AyAMRReplayAccepted (solver stream finalClause : Prop) : Prop :=
  stream -> solver -> finalClause

theorem ay_amr_conj_intro (left right : Prop) :
    left -> right -> AyAMRConj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_amr_conj_left (left right : Prop) :
    AyAMRConj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_amr_conj_right (left right : Prop) :
    AyAMRConj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_amr_disj_left (left right : Prop) :
    left -> AyAMRDisj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_amr_disj_right (left right : Prop) :
    right -> AyAMRDisj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_amr_equisat_forward (before after : Prop) :
    AyAMREquisat before after -> before -> after :=
  fun witness hbefore =>
    witness after (fun forward _backward => forward hbefore)

theorem ay_amr_equisat_backward (before after : Prop) :
    AyAMREquisat before after -> after -> before :=
  fun witness hafter =>
    witness before (fun _forward backward => backward hafter)

theorem ay_amr_model_intro (formula assignment : Prop) :
    formula -> assignment -> AyAMRModel formula assignment :=
  fun formulaProof assignmentProof =>
    ay_amr_conj_intro formula assignment formulaProof assignmentProof

theorem ay_amr_model_formula (formula assignment : Prop) :
    AyAMRModel formula assignment -> formula :=
  fun model => ay_amr_conj_left formula assignment model

theorem ay_amr_model_assignment (formula assignment : Prop) :
    AyAMRModel formula assignment -> assignment :=
  fun model => ay_amr_conj_right formula assignment model

theorem ay_amr_artifacts_intro (certId archiveKey : Prop) :
    certId -> archiveKey -> AyAMRArtifacts certId archiveKey :=
  ay_amr_conj_intro certId archiveKey

theorem ay_amr_entry_intro
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    exitCode -> artifacts -> checkerDecision -> auditDigest -> diagnostic ->
    AyAMREntry exitCode artifacts checkerDecision auditDigest diagnostic :=
  fun exitProof artifactsProof checkerProof auditProof diagnosticProof =>
    ay_amr_conj_intro exitCode
      (AyAMRConj artifacts
        (AyAMRConj checkerDecision (AyAMRConj auditDigest diagnostic)))
      exitProof
      (ay_amr_conj_intro artifacts
        (AyAMRConj checkerDecision (AyAMRConj auditDigest diagnostic))
        artifactsProof
        (ay_amr_conj_intro checkerDecision
          (AyAMRConj auditDigest diagnostic)
          checkerProof
          (ay_amr_conj_intro auditDigest diagnostic auditProof
            diagnosticProof)))

theorem ay_amr_entry_exit
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    AyAMREntry exitCode artifacts checkerDecision auditDigest diagnostic ->
    exitCode :=
  fun entry =>
    ay_amr_conj_left exitCode
      (AyAMRConj artifacts
        (AyAMRConj checkerDecision (AyAMRConj auditDigest diagnostic)))
      entry

theorem ay_amr_entry_checker
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    AyAMREntry exitCode artifacts checkerDecision auditDigest diagnostic ->
    checkerDecision :=
  fun entry =>
    ay_amr_conj_right exitCode
      (AyAMRConj artifacts
        (AyAMRConj checkerDecision (AyAMRConj auditDigest diagnostic)))
      entry checkerDecision
      (fun _artifactsProof tail =>
        tail checkerDecision (fun checkerProof _auditTail => checkerProof))

theorem ay_amr_entry_audit
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    AyAMREntry exitCode artifacts checkerDecision auditDigest diagnostic ->
    auditDigest :=
  fun entry =>
    ay_amr_conj_right exitCode
      (AyAMRConj artifacts
        (AyAMRConj checkerDecision (AyAMRConj auditDigest diagnostic)))
      entry auditDigest
      (fun _artifactsProof tail =>
        tail auditDigest
          (fun _checkerProof auditTail =>
            auditTail auditDigest
              (fun auditProof _diagnosticProof => auditProof)))

theorem ay_amr_entry_diagnostic
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    AyAMREntry exitCode artifacts checkerDecision auditDigest diagnostic ->
    diagnostic :=
  fun entry =>
    ay_amr_conj_right exitCode
      (AyAMRConj artifacts
        (AyAMRConj checkerDecision (AyAMRConj auditDigest diagnostic)))
      entry diagnostic
      (fun _artifactsProof tail =>
        tail diagnostic
          (fun _checkerProof auditTail =>
            auditTail diagnostic
              (fun _auditProof diagnosticProof => diagnosticProof)))

theorem ay_amr_leaf_hash_intro (entry leafHash : Prop) :
    entry -> leafHash -> AyAMRLeafHash entry leafHash :=
  ay_amr_conj_intro entry leafHash

theorem ay_amr_leaf_hash_entry (entry leafHash : Prop) :
    AyAMRLeafHash entry leafHash -> entry :=
  ay_amr_conj_left entry leafHash

theorem ay_amr_leaf_hash_value (entry leafHash : Prop) :
    AyAMRLeafHash entry leafHash -> leafHash :=
  ay_amr_conj_right entry leafHash

theorem ay_amr_membership_intro (leafHash root entry : Prop) :
    leafHash -> root -> entry -> AyAMRMembership leafHash root entry :=
  fun leafProof rootProof entryProof =>
    ay_amr_conj_intro leafHash (AyAMRConj root entry)
      leafProof
      (ay_amr_conj_intro root entry rootProof entryProof)

theorem ay_amr_membership_leaf (leafHash root entry : Prop) :
    AyAMRMembership leafHash root entry -> leafHash :=
  fun membership =>
    ay_amr_conj_left leafHash (AyAMRConj root entry) membership

theorem ay_amr_membership_root (leafHash root entry : Prop) :
    AyAMRMembership leafHash root entry -> root :=
  fun membership =>
    ay_amr_conj_right leafHash (AyAMRConj root entry) membership
      root (fun rootProof _entryProof => rootProof)

theorem ay_amr_membership_entry (leafHash root entry : Prop) :
    AyAMRMembership leafHash root entry -> entry :=
  fun membership =>
    ay_amr_conj_right leafHash (AyAMRConj root entry) membership
      entry (fun _rootProof entryProof => entryProof)

theorem ay_amr_report_intro (entry leafHash root : Prop) :
    AyAMRLeafHash entry leafHash ->
    AyAMRMembership leafHash root entry ->
    AyAMRReport entry leafHash root :=
  ay_amr_conj_intro (AyAMRLeafHash entry leafHash)
    (AyAMRMembership leafHash root entry)

theorem ay_amr_report_leaf_hash (entry leafHash root : Prop) :
    AyAMRReport entry leafHash root -> AyAMRLeafHash entry leafHash :=
  ay_amr_conj_left (AyAMRLeafHash entry leafHash)
    (AyAMRMembership leafHash root entry)

theorem ay_amr_report_membership (entry leafHash root : Prop) :
    AyAMRReport entry leafHash root -> AyAMRMembership leafHash root entry :=
  ay_amr_conj_right (AyAMRLeafHash entry leafHash)
    (AyAMRMembership leafHash root entry)

theorem ay_amr_report_entry (entry leafHash root : Prop) :
    AyAMRReport entry leafHash root -> entry :=
  fun report =>
    ay_amr_membership_entry leafHash root entry
      (ay_amr_report_membership entry leafHash root report)

theorem ay_amr_report_root (entry leafHash root : Prop) :
    AyAMRReport entry leafHash root -> root :=
  fun report =>
    ay_amr_membership_root leafHash root entry
      (ay_amr_report_membership entry leafHash root report)

theorem ay_amr_no_claim_intro (exitCode auditDigest diagnostic : Prop) :
    exitCode -> auditDigest -> diagnostic ->
    AyAMRNoClaim exitCode auditDigest diagnostic :=
  fun exitProof auditProof diagnosticProof =>
    ay_amr_conj_intro exitCode (AyAMRConj auditDigest diagnostic)
      exitProof
      (ay_amr_conj_intro auditDigest diagnostic auditProof diagnosticProof)

theorem ay_amr_diagnostic_entry_no_claim
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    AyAMREntry exitCode artifacts checkerDecision auditDigest diagnostic ->
    AyAMRNoClaim exitCode auditDigest diagnostic :=
  fun entry =>
    ay_amr_no_claim_intro exitCode auditDigest diagnostic
      (ay_amr_entry_exit exitCode artifacts checkerDecision auditDigest
        diagnostic entry)
      (ay_amr_entry_audit exitCode artifacts checkerDecision auditDigest
        diagnostic entry)
      (ay_amr_entry_diagnostic exitCode artifacts checkerDecision auditDigest
        diagnostic entry)

theorem ay_amr_preprocess_model_reconstruct
    (original solver internalAssignment visibleAssignment : Prop) :
    AyAMRPreprocessArtifact original solver ->
    (internalAssignment -> visibleAssignment) ->
    AyAMRModel solver internalAssignment ->
    AyAMRVisibleSAT original visibleAssignment :=
  fun preprocess decode model =>
    ay_amr_model_intro original visibleAssignment
      (ay_amr_equisat_backward original solver preprocess
        (ay_amr_model_formula solver internalAssignment model))
      (decode (ay_amr_model_assignment solver internalAssignment model))

theorem ay_amr_preprocess_unsat_reconstruct
    (original solver : Prop) :
    AyAMRPreprocessArtifact original solver ->
    AyAMRUnsat solver ->
    AyAMRUnsat original :=
  fun preprocess solverUnsat originalProof =>
    solverUnsat
      (ay_amr_equisat_forward original solver preprocess originalProof)

theorem ay_amr_replay_unsat_public
    (original solver stream finalClause : Prop) :
    AyAMRPreprocessArtifact original solver ->
    AyAMRReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    stream ->
    AyAMRUnsat original :=
  fun preprocess replay closeFinal streamProof originalProof =>
    closeFinal
      (replay streamProof
        (ay_amr_equisat_forward original solver preprocess originalProof))

theorem ay_amr_sat_entry_sound
    (acceptedSat artifacts satBranch auditDigest diagnostic original solver
      internalAssignment visibleAssignment : Prop) :
    AyAMRPreprocessArtifact original solver ->
    (internalAssignment -> visibleAssignment) ->
    (satBranch -> AyAMRModel solver internalAssignment) ->
    AyAMREntry acceptedSat artifacts satBranch auditDigest diagnostic ->
    AyAMRVisibleSAT original visibleAssignment :=
  fun preprocess decode accept entry =>
    ay_amr_preprocess_model_reconstruct original solver internalAssignment
      visibleAssignment preprocess decode
      (accept
        (ay_amr_entry_checker acceptedSat artifacts satBranch auditDigest
          diagnostic entry))

theorem ay_amr_unsat_entry_sound
    (acceptedUnsat artifacts unsatBranch auditDigest diagnostic original solver
      stream finalClause : Prop) :
    AyAMRPreprocessArtifact original solver ->
    AyAMRReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    (unsatBranch -> stream) ->
    AyAMREntry acceptedUnsat artifacts unsatBranch auditDigest diagnostic ->
    AyAMRUnsat original :=
  fun preprocess replay closeFinal accept entry =>
    ay_amr_replay_unsat_public original solver stream finalClause preprocess
      replay closeFinal
      (accept
        (ay_amr_entry_checker acceptedUnsat artifacts unsatBranch auditDigest
          diagnostic entry))

theorem ay_amr_sat_report_membership_sound
    (leafHash root acceptedSat artifacts satBranch auditDigest diagnostic
      original solver internalAssignment visibleAssignment : Prop) :
    AyAMRPreprocessArtifact original solver ->
    (internalAssignment -> visibleAssignment) ->
    (satBranch -> AyAMRModel solver internalAssignment) ->
    AyAMRReport
      (AyAMREntry acceptedSat artifacts satBranch auditDigest diagnostic)
      leafHash root ->
    AyAMRVisibleSAT original visibleAssignment :=
  fun preprocess decode accept report =>
    ay_amr_sat_entry_sound acceptedSat artifacts satBranch auditDigest
      diagnostic original solver internalAssignment visibleAssignment
      preprocess decode accept
      (ay_amr_report_entry
        (AyAMREntry acceptedSat artifacts satBranch auditDigest diagnostic)
        leafHash root report)

theorem ay_amr_unsat_report_membership_sound
    (leafHash root acceptedUnsat artifacts unsatBranch auditDigest diagnostic
      original solver stream finalClause : Prop) :
    AyAMRPreprocessArtifact original solver ->
    AyAMRReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    (unsatBranch -> stream) ->
    AyAMRReport
      (AyAMREntry acceptedUnsat artifacts unsatBranch auditDigest diagnostic)
      leafHash root ->
    AyAMRUnsat original :=
  fun preprocess replay closeFinal accept report =>
    ay_amr_unsat_entry_sound acceptedUnsat artifacts unsatBranch auditDigest
      diagnostic original solver stream finalClause preprocess replay
      closeFinal accept
      (ay_amr_report_entry
        (AyAMREntry acceptedUnsat artifacts unsatBranch auditDigest
          diagnostic)
        leafHash root report)

theorem ay_amr_diagnostic_report_membership_no_claim
    (leafHash root exitCode artifacts checkerDecision auditDigest diagnostic :
      Prop) :
    AyAMRReport
      (AyAMREntry exitCode artifacts checkerDecision auditDigest diagnostic)
      leafHash root ->
    AyAMRNoClaim exitCode auditDigest diagnostic :=
  fun report =>
    ay_amr_diagnostic_entry_no_claim exitCode artifacts checkerDecision
      auditDigest diagnostic
      (ay_amr_report_entry
        (AyAMREntry exitCode artifacts checkerDecision auditDigest
          diagnostic)
        leafHash root report)

theorem ay_amr_report_public_result
    (satReport unsatReport diagnosticReport satFact unsatFact noClaim : Prop) :
    (satReport -> satFact) ->
    (unsatReport -> unsatFact) ->
    (diagnosticReport -> noClaim) ->
    AyAMRDisj satReport (AyAMRDisj unsatReport diagnosticReport) ->
    AyAMRPublicResult satFact unsatFact noClaim :=
  fun satSound unsatSound diagnosticNoClaim reports result onSat onRest =>
    reports result
      (fun satProof => onSat (satSound satProof))
      (fun rest =>
        rest result
          (fun unsatProof =>
            onRest
              (ay_amr_disj_left unsatFact noClaim
                (unsatSound unsatProof)))
          (fun diagnosticProof =>
            onRest
              (ay_amr_disj_right unsatFact noClaim
                (diagnosticNoClaim diagnosticProof))))

theorem ay_amr_membership_root_agrees_with_report
    (entry leafHash root : Prop) :
    AyAMRReport entry leafHash root -> root :=
  ay_amr_report_root entry leafHash root

theorem ay_amr_leaf_hash_agrees_with_report
    (entry leafHash root : Prop) :
    AyAMRReport entry leafHash root -> leafHash :=
  fun report =>
    ay_amr_leaf_hash_value entry leafHash
      (ay_amr_report_leaf_hash entry leafHash root report)
