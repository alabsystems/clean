-- SAT-COMP validator audit Merkle-bisect core.
--
-- This self-contained package models bisection over Merkle-backed validator
-- audit logs.  A witness selects the first bad audit/report mismatch while
-- preserving earlier accepted SAT/UNSAT soundness and diagnostic no-claim
-- leaves.

def AyAMBConj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def AyAMBDisj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyAMBEquisat (before after : Prop) : Prop :=
  AyAMBConj (before -> after) (after -> before)

def AyAMBOutcome (sat unsat : Prop) : Prop :=
  AyAMBDisj sat unsat

def AyAMBPublicResult (satFact unsatFact noClaim : Prop) : Prop :=
  AyAMBDisj satFact (AyAMBDisj unsatFact noClaim)

def AyAMBArtifacts (certId archiveKey : Prop) : Prop :=
  AyAMBConj certId archiveKey

def AyAMBEntry
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    Prop :=
  AyAMBConj exitCode
    (AyAMBConj artifacts
      (AyAMBConj checkerDecision
        (AyAMBConj auditDigest diagnostic)))

def AyAMBLeafHash (entry leafHash : Prop) : Prop :=
  AyAMBConj entry leafHash

def AyAMBMembership (leafHash root entry : Prop) : Prop :=
  AyAMBConj leafHash (AyAMBConj root entry)

def AyAMBReport (entry leafHash root : Prop) : Prop :=
  AyAMBConj (AyAMBLeafHash entry leafHash)
    (AyAMBMembership leafHash root entry)

def AyAMBTailRootAgreement (tailDigest root : Prop) : Prop :=
  AyAMBConj tailDigest root

def AyAMBMismatch (expectedRoot actualRoot entry : Prop) : Prop :=
  AyAMBConj expectedRoot (AyAMBConj actualRoot entry)

def AyAMBBisectWitness
    (earlierAccepted selectedMismatch tailAgreement : Prop) : Prop :=
  AyAMBConj earlierAccepted (AyAMBConj selectedMismatch tailAgreement)

def AyAMBNoClaim (exitCode auditDigest diagnostic : Prop) : Prop :=
  AyAMBConj exitCode (AyAMBConj auditDigest diagnostic)

def AyAMBModel (formula assignment : Prop) : Prop :=
  AyAMBConj formula assignment

def AyAMBUnsat (formula : Prop) : Prop :=
  formula -> False

def AyAMBVisibleSAT (original visibleAssignment : Prop) : Prop :=
  AyAMBModel original visibleAssignment

def AyAMBPreprocessArtifact (original solver : Prop) : Prop :=
  AyAMBEquisat original solver

def AyAMBReplayAccepted (solver stream finalClause : Prop) : Prop :=
  stream -> solver -> finalClause

theorem ay_amb_conj_intro (left right : Prop) :
    left -> right -> AyAMBConj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_amb_conj_left (left right : Prop) :
    AyAMBConj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_amb_conj_right (left right : Prop) :
    AyAMBConj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_amb_disj_left (left right : Prop) :
    left -> AyAMBDisj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_amb_disj_right (left right : Prop) :
    right -> AyAMBDisj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_amb_equisat_forward (before after : Prop) :
    AyAMBEquisat before after -> before -> after :=
  fun witness hbefore =>
    witness after (fun forward _backward => forward hbefore)

theorem ay_amb_equisat_backward (before after : Prop) :
    AyAMBEquisat before after -> after -> before :=
  fun witness hafter =>
    witness before (fun _forward backward => backward hafter)

theorem ay_amb_model_intro (formula assignment : Prop) :
    formula -> assignment -> AyAMBModel formula assignment :=
  fun formulaProof assignmentProof =>
    ay_amb_conj_intro formula assignment formulaProof assignmentProof

theorem ay_amb_model_formula (formula assignment : Prop) :
    AyAMBModel formula assignment -> formula :=
  fun model => ay_amb_conj_left formula assignment model

theorem ay_amb_model_assignment (formula assignment : Prop) :
    AyAMBModel formula assignment -> assignment :=
  fun model => ay_amb_conj_right formula assignment model

theorem ay_amb_artifacts_intro (certId archiveKey : Prop) :
    certId -> archiveKey -> AyAMBArtifacts certId archiveKey :=
  ay_amb_conj_intro certId archiveKey

theorem ay_amb_entry_intro
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    exitCode -> artifacts -> checkerDecision -> auditDigest -> diagnostic ->
    AyAMBEntry exitCode artifacts checkerDecision auditDigest diagnostic :=
  fun exitProof artifactsProof checkerProof auditProof diagnosticProof =>
    ay_amb_conj_intro exitCode
      (AyAMBConj artifacts
        (AyAMBConj checkerDecision (AyAMBConj auditDigest diagnostic)))
      exitProof
      (ay_amb_conj_intro artifacts
        (AyAMBConj checkerDecision (AyAMBConj auditDigest diagnostic))
        artifactsProof
        (ay_amb_conj_intro checkerDecision
          (AyAMBConj auditDigest diagnostic)
          checkerProof
          (ay_amb_conj_intro auditDigest diagnostic auditProof
            diagnosticProof)))

theorem ay_amb_entry_exit
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    AyAMBEntry exitCode artifacts checkerDecision auditDigest diagnostic ->
    exitCode :=
  fun entry =>
    ay_amb_conj_left exitCode
      (AyAMBConj artifacts
        (AyAMBConj checkerDecision (AyAMBConj auditDigest diagnostic)))
      entry

theorem ay_amb_entry_checker
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    AyAMBEntry exitCode artifacts checkerDecision auditDigest diagnostic ->
    checkerDecision :=
  fun entry =>
    ay_amb_conj_right exitCode
      (AyAMBConj artifacts
        (AyAMBConj checkerDecision (AyAMBConj auditDigest diagnostic)))
      entry checkerDecision
      (fun _artifactsProof tail =>
        tail checkerDecision (fun checkerProof _auditTail => checkerProof))

theorem ay_amb_entry_audit
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    AyAMBEntry exitCode artifacts checkerDecision auditDigest diagnostic ->
    auditDigest :=
  fun entry =>
    ay_amb_conj_right exitCode
      (AyAMBConj artifacts
        (AyAMBConj checkerDecision (AyAMBConj auditDigest diagnostic)))
      entry auditDigest
      (fun _artifactsProof tail =>
        tail auditDigest
          (fun _checkerProof auditTail =>
            auditTail auditDigest
              (fun auditProof _diagnosticProof => auditProof)))

theorem ay_amb_entry_diagnostic
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    AyAMBEntry exitCode artifacts checkerDecision auditDigest diagnostic ->
    diagnostic :=
  fun entry =>
    ay_amb_conj_right exitCode
      (AyAMBConj artifacts
        (AyAMBConj checkerDecision (AyAMBConj auditDigest diagnostic)))
      entry diagnostic
      (fun _artifactsProof tail =>
        tail diagnostic
          (fun _checkerProof auditTail =>
            auditTail diagnostic
              (fun _auditProof diagnosticProof => diagnosticProof)))

theorem ay_amb_leaf_hash_intro (entry leafHash : Prop) :
    entry -> leafHash -> AyAMBLeafHash entry leafHash :=
  ay_amb_conj_intro entry leafHash

theorem ay_amb_leaf_hash_entry (entry leafHash : Prop) :
    AyAMBLeafHash entry leafHash -> entry :=
  ay_amb_conj_left entry leafHash

theorem ay_amb_leaf_hash_value (entry leafHash : Prop) :
    AyAMBLeafHash entry leafHash -> leafHash :=
  ay_amb_conj_right entry leafHash

theorem ay_amb_membership_intro (leafHash root entry : Prop) :
    leafHash -> root -> entry -> AyAMBMembership leafHash root entry :=
  fun leafProof rootProof entryProof =>
    ay_amb_conj_intro leafHash (AyAMBConj root entry)
      leafProof
      (ay_amb_conj_intro root entry rootProof entryProof)

theorem ay_amb_membership_leaf (leafHash root entry : Prop) :
    AyAMBMembership leafHash root entry -> leafHash :=
  fun membership =>
    ay_amb_conj_left leafHash (AyAMBConj root entry) membership

theorem ay_amb_membership_root (leafHash root entry : Prop) :
    AyAMBMembership leafHash root entry -> root :=
  fun membership =>
    ay_amb_conj_right leafHash (AyAMBConj root entry) membership
      root (fun rootProof _entryProof => rootProof)

theorem ay_amb_membership_entry (leafHash root entry : Prop) :
    AyAMBMembership leafHash root entry -> entry :=
  fun membership =>
    ay_amb_conj_right leafHash (AyAMBConj root entry) membership
      entry (fun _rootProof entryProof => entryProof)

theorem ay_amb_report_intro (entry leafHash root : Prop) :
    AyAMBLeafHash entry leafHash ->
    AyAMBMembership leafHash root entry ->
    AyAMBReport entry leafHash root :=
  ay_amb_conj_intro (AyAMBLeafHash entry leafHash)
    (AyAMBMembership leafHash root entry)

theorem ay_amb_report_membership (entry leafHash root : Prop) :
    AyAMBReport entry leafHash root -> AyAMBMembership leafHash root entry :=
  ay_amb_conj_right (AyAMBLeafHash entry leafHash)
    (AyAMBMembership leafHash root entry)

theorem ay_amb_report_entry (entry leafHash root : Prop) :
    AyAMBReport entry leafHash root -> entry :=
  fun report =>
    ay_amb_membership_entry leafHash root entry
      (ay_amb_report_membership entry leafHash root report)

theorem ay_amb_report_root (entry leafHash root : Prop) :
    AyAMBReport entry leafHash root -> root :=
  fun report =>
    ay_amb_membership_root leafHash root entry
      (ay_amb_report_membership entry leafHash root report)

theorem ay_amb_tail_root_agreement_intro (tailDigest root : Prop) :
    tailDigest -> root -> AyAMBTailRootAgreement tailDigest root :=
  ay_amb_conj_intro tailDigest root

theorem ay_amb_tail_root_agreement_tail (tailDigest root : Prop) :
    AyAMBTailRootAgreement tailDigest root -> tailDigest :=
  ay_amb_conj_left tailDigest root

theorem ay_amb_tail_root_agreement_root (tailDigest root : Prop) :
    AyAMBTailRootAgreement tailDigest root -> root :=
  ay_amb_conj_right tailDigest root

theorem ay_amb_mismatch_intro (expectedRoot actualRoot entry : Prop) :
    expectedRoot -> actualRoot -> entry ->
    AyAMBMismatch expectedRoot actualRoot entry :=
  fun expectedProof actualProof entryProof =>
    ay_amb_conj_intro expectedRoot (AyAMBConj actualRoot entry)
      expectedProof
      (ay_amb_conj_intro actualRoot entry actualProof entryProof)

theorem ay_amb_mismatch_expected (expectedRoot actualRoot entry : Prop) :
    AyAMBMismatch expectedRoot actualRoot entry -> expectedRoot :=
  fun mismatch =>
    ay_amb_conj_left expectedRoot (AyAMBConj actualRoot entry) mismatch

theorem ay_amb_mismatch_actual (expectedRoot actualRoot entry : Prop) :
    AyAMBMismatch expectedRoot actualRoot entry -> actualRoot :=
  fun mismatch =>
    ay_amb_conj_right expectedRoot (AyAMBConj actualRoot entry) mismatch
      actualRoot (fun actualProof _entryProof => actualProof)

theorem ay_amb_mismatch_entry (expectedRoot actualRoot entry : Prop) :
    AyAMBMismatch expectedRoot actualRoot entry -> entry :=
  fun mismatch =>
    ay_amb_conj_right expectedRoot (AyAMBConj actualRoot entry) mismatch
      entry (fun _actualProof entryProof => entryProof)

theorem ay_amb_bisect_witness_intro
    (earlierAccepted selectedMismatch tailAgreement : Prop) :
    earlierAccepted -> selectedMismatch -> tailAgreement ->
    AyAMBBisectWitness earlierAccepted selectedMismatch tailAgreement :=
  fun earlierProof mismatchProof tailProof =>
    ay_amb_conj_intro earlierAccepted
      (AyAMBConj selectedMismatch tailAgreement)
      earlierProof
      (ay_amb_conj_intro selectedMismatch tailAgreement mismatchProof
        tailProof)

theorem ay_amb_bisect_earlier
    (earlierAccepted selectedMismatch tailAgreement : Prop) :
    AyAMBBisectWitness earlierAccepted selectedMismatch tailAgreement ->
    earlierAccepted :=
  fun witness =>
    ay_amb_conj_left earlierAccepted
      (AyAMBConj selectedMismatch tailAgreement) witness

theorem ay_amb_bisect_mismatch
    (earlierAccepted selectedMismatch tailAgreement : Prop) :
    AyAMBBisectWitness earlierAccepted selectedMismatch tailAgreement ->
    selectedMismatch :=
  fun witness =>
    ay_amb_conj_right earlierAccepted
      (AyAMBConj selectedMismatch tailAgreement) witness
      selectedMismatch (fun mismatchProof _tailProof => mismatchProof)

theorem ay_amb_bisect_tail_agreement
    (earlierAccepted selectedMismatch tailAgreement : Prop) :
    AyAMBBisectWitness earlierAccepted selectedMismatch tailAgreement ->
    tailAgreement :=
  fun witness =>
    ay_amb_conj_right earlierAccepted
      (AyAMBConj selectedMismatch tailAgreement) witness
      tailAgreement (fun _mismatchProof tailProof => tailProof)

theorem ay_amb_no_claim_intro (exitCode auditDigest diagnostic : Prop) :
    exitCode -> auditDigest -> diagnostic ->
    AyAMBNoClaim exitCode auditDigest diagnostic :=
  fun exitProof auditProof diagnosticProof =>
    ay_amb_conj_intro exitCode (AyAMBConj auditDigest diagnostic)
      exitProof
      (ay_amb_conj_intro auditDigest diagnostic auditProof diagnosticProof)

theorem ay_amb_diagnostic_entry_no_claim
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    AyAMBEntry exitCode artifacts checkerDecision auditDigest diagnostic ->
    AyAMBNoClaim exitCode auditDigest diagnostic :=
  fun entry =>
    ay_amb_no_claim_intro exitCode auditDigest diagnostic
      (ay_amb_entry_exit exitCode artifacts checkerDecision auditDigest
        diagnostic entry)
      (ay_amb_entry_audit exitCode artifacts checkerDecision auditDigest
        diagnostic entry)
      (ay_amb_entry_diagnostic exitCode artifacts checkerDecision auditDigest
        diagnostic entry)

theorem ay_amb_preprocess_model_reconstruct
    (original solver internalAssignment visibleAssignment : Prop) :
    AyAMBPreprocessArtifact original solver ->
    (internalAssignment -> visibleAssignment) ->
    AyAMBModel solver internalAssignment ->
    AyAMBVisibleSAT original visibleAssignment :=
  fun preprocess decode model =>
    ay_amb_model_intro original visibleAssignment
      (ay_amb_equisat_backward original solver preprocess
        (ay_amb_model_formula solver internalAssignment model))
      (decode (ay_amb_model_assignment solver internalAssignment model))

theorem ay_amb_preprocess_unsat_reconstruct
    (original solver : Prop) :
    AyAMBPreprocessArtifact original solver ->
    AyAMBUnsat solver ->
    AyAMBUnsat original :=
  fun preprocess solverUnsat originalProof =>
    solverUnsat
      (ay_amb_equisat_forward original solver preprocess originalProof)

theorem ay_amb_replay_unsat_public
    (original solver stream finalClause : Prop) :
    AyAMBPreprocessArtifact original solver ->
    AyAMBReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    stream ->
    AyAMBUnsat original :=
  fun preprocess replay closeFinal streamProof originalProof =>
    closeFinal
      (replay streamProof
        (ay_amb_equisat_forward original solver preprocess originalProof))

theorem ay_amb_sat_entry_sound
    (acceptedSat artifacts satBranch auditDigest diagnostic original solver
      internalAssignment visibleAssignment : Prop) :
    AyAMBPreprocessArtifact original solver ->
    (internalAssignment -> visibleAssignment) ->
    (satBranch -> AyAMBModel solver internalAssignment) ->
    AyAMBEntry acceptedSat artifacts satBranch auditDigest diagnostic ->
    AyAMBVisibleSAT original visibleAssignment :=
  fun preprocess decode accept entry =>
    ay_amb_preprocess_model_reconstruct original solver internalAssignment
      visibleAssignment preprocess decode
      (accept
        (ay_amb_entry_checker acceptedSat artifacts satBranch auditDigest
          diagnostic entry))

theorem ay_amb_unsat_entry_sound
    (acceptedUnsat artifacts unsatBranch auditDigest diagnostic original solver
      stream finalClause : Prop) :
    AyAMBPreprocessArtifact original solver ->
    AyAMBReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    (unsatBranch -> stream) ->
    AyAMBEntry acceptedUnsat artifacts unsatBranch auditDigest diagnostic ->
    AyAMBUnsat original :=
  fun preprocess replay closeFinal accept entry =>
    ay_amb_replay_unsat_public original solver stream finalClause preprocess
      replay closeFinal
      (accept
        (ay_amb_entry_checker acceptedUnsat artifacts unsatBranch auditDigest
          diagnostic entry))

theorem ay_amb_accepted_leaf_preserves_sat
    (leafHash root acceptedSat artifacts satBranch auditDigest diagnostic
      original solver internalAssignment visibleAssignment : Prop) :
    AyAMBPreprocessArtifact original solver ->
    (internalAssignment -> visibleAssignment) ->
    (satBranch -> AyAMBModel solver internalAssignment) ->
    AyAMBMembership leafHash root
      (AyAMBEntry acceptedSat artifacts satBranch auditDigest diagnostic) ->
    AyAMBVisibleSAT original visibleAssignment :=
  fun preprocess decode accept membership =>
    ay_amb_sat_entry_sound acceptedSat artifacts satBranch auditDigest
      diagnostic original solver internalAssignment visibleAssignment
      preprocess decode accept
      (ay_amb_membership_entry leafHash root
        (AyAMBEntry acceptedSat artifacts satBranch auditDigest diagnostic)
        membership)

theorem ay_amb_accepted_leaf_preserves_unsat
    (leafHash root acceptedUnsat artifacts unsatBranch auditDigest diagnostic
      original solver stream finalClause : Prop) :
    AyAMBPreprocessArtifact original solver ->
    AyAMBReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    (unsatBranch -> stream) ->
    AyAMBMembership leafHash root
      (AyAMBEntry acceptedUnsat artifacts unsatBranch auditDigest
        diagnostic) ->
    AyAMBUnsat original :=
  fun preprocess replay closeFinal accept membership =>
    ay_amb_unsat_entry_sound acceptedUnsat artifacts unsatBranch auditDigest
      diagnostic original solver stream finalClause preprocess replay
      closeFinal accept
      (ay_amb_membership_entry leafHash root
        (AyAMBEntry acceptedUnsat artifacts unsatBranch auditDigest
          diagnostic)
        membership)

theorem ay_amb_diagnostic_leaf_no_claim
    (leafHash root exitCode artifacts checkerDecision auditDigest diagnostic :
      Prop) :
    AyAMBMembership leafHash root
      (AyAMBEntry exitCode artifacts checkerDecision auditDigest diagnostic) ->
    AyAMBNoClaim exitCode auditDigest diagnostic :=
  fun membership =>
    ay_amb_diagnostic_entry_no_claim exitCode artifacts checkerDecision
      auditDigest diagnostic
      (ay_amb_membership_entry leafHash root
        (AyAMBEntry exitCode artifacts checkerDecision auditDigest
          diagnostic)
        membership)

theorem ay_amb_bisect_localizes_first_bad
    (earlierAccepted expectedRoot actualRoot badEntry tailAgreement : Prop) :
    AyAMBBisectWitness earlierAccepted
      (AyAMBMismatch expectedRoot actualRoot badEntry) tailAgreement ->
    AyAMBMismatch expectedRoot actualRoot badEntry :=
  fun witness =>
    ay_amb_bisect_mismatch earlierAccepted
      (AyAMBMismatch expectedRoot actualRoot badEntry) tailAgreement witness

theorem ay_amb_bisect_preserves_earlier_sat_soundness
    (earlierAccepted selectedMismatch tailAgreement satFact : Prop) :
    AyAMBBisectWitness earlierAccepted selectedMismatch tailAgreement ->
    (earlierAccepted -> satFact) ->
    satFact :=
  fun witness earlierSound =>
    earlierSound
      (ay_amb_bisect_earlier earlierAccepted selectedMismatch tailAgreement
        witness)

theorem ay_amb_bisect_preserves_earlier_unsat_soundness
    (earlierAccepted selectedMismatch tailAgreement unsatFact : Prop) :
    AyAMBBisectWitness earlierAccepted selectedMismatch tailAgreement ->
    (earlierAccepted -> unsatFact) ->
    unsatFact :=
  fun witness earlierSound =>
    earlierSound
      (ay_amb_bisect_earlier earlierAccepted selectedMismatch tailAgreement
        witness)

theorem ay_amb_bisect_tail_agreement_preserved
    (earlierAccepted selectedMismatch tailAgreement : Prop) :
    AyAMBBisectWitness earlierAccepted selectedMismatch tailAgreement ->
    tailAgreement :=
  ay_amb_bisect_tail_agreement earlierAccepted selectedMismatch tailAgreement

theorem ay_amb_mismatch_entry_selected
    (earlierAccepted expectedRoot actualRoot badEntry tailAgreement : Prop) :
    AyAMBBisectWitness earlierAccepted
      (AyAMBMismatch expectedRoot actualRoot badEntry) tailAgreement ->
    badEntry :=
  fun witness =>
    ay_amb_mismatch_entry expectedRoot actualRoot badEntry
      (ay_amb_bisect_localizes_first_bad earlierAccepted expectedRoot
        actualRoot badEntry tailAgreement witness)

theorem ay_amb_bisect_public_result_preserved
    (earlierAccepted selectedMismatch tailAgreement satFact unsatFact
      noClaim : Prop) :
    AyAMBBisectWitness earlierAccepted selectedMismatch tailAgreement ->
    (earlierAccepted -> AyAMBPublicResult satFact unsatFact noClaim) ->
    AyAMBPublicResult satFact unsatFact noClaim :=
  fun witness earlierResult =>
    earlierResult
      (ay_amb_bisect_earlier earlierAccepted selectedMismatch tailAgreement
        witness)
