-- SAT-COMP validator audit Merkle-summary core.
--
-- Merkle hashes are abstract propositions here.  A membership proof connects a
-- leaf entry hash to a compacted root.  Accepted SAT/UNSAT membership exposes
-- the corresponding soundness theorem; diagnostic membership remains no-claim.

def AyAMSConj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def AyAMSDisj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyAMSEquisat (before after : Prop) : Prop :=
  AyAMSConj (before -> after) (after -> before)

def AyAMSOutcome (sat unsat : Prop) : Prop :=
  AyAMSDisj sat unsat

def AyAMSPublicResult (satFact unsatFact noClaim : Prop) : Prop :=
  AyAMSDisj satFact (AyAMSDisj unsatFact noClaim)

def AyAMSArtifacts (certId archiveKey : Prop) : Prop :=
  AyAMSConj certId archiveKey

def AyAMSEntry
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    Prop :=
  AyAMSConj exitCode
    (AyAMSConj artifacts
      (AyAMSConj checkerDecision
        (AyAMSConj auditDigest diagnostic)))

def AyAMSLeafHash (entry leafHash : Prop) : Prop :=
  AyAMSConj entry leafHash

def AyAMSSummaryRoot (acceptedSat acceptedUnsat diagnostics root : Prop) :
    Prop :=
  AyAMSConj acceptedSat
    (AyAMSConj acceptedUnsat (AyAMSConj diagnostics root))

def AyAMSMembership (leafHash root entry : Prop) : Prop :=
  AyAMSConj leafHash (AyAMSConj root entry)

def AyAMSTailRootAgreement (tailDigest root : Prop) : Prop :=
  AyAMSConj tailDigest root

def AyAMSNoClaim (exitCode auditDigest diagnostic : Prop) : Prop :=
  AyAMSConj exitCode (AyAMSConj auditDigest diagnostic)

def AyAMSModel (formula assignment : Prop) : Prop :=
  AyAMSConj formula assignment

def AyAMSUnsat (formula : Prop) : Prop :=
  formula -> False

def AyAMSVisibleSAT (original visibleAssignment : Prop) : Prop :=
  AyAMSModel original visibleAssignment

def AyAMSPreprocessArtifact (original solver : Prop) : Prop :=
  AyAMSEquisat original solver

def AyAMSReplayAccepted (solver stream finalClause : Prop) : Prop :=
  stream -> solver -> finalClause

theorem ay_ams_conj_intro (left right : Prop) :
    left -> right -> AyAMSConj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_ams_conj_left (left right : Prop) :
    AyAMSConj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_ams_conj_right (left right : Prop) :
    AyAMSConj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_ams_disj_left (left right : Prop) :
    left -> AyAMSDisj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_ams_disj_right (left right : Prop) :
    right -> AyAMSDisj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_ams_equisat_forward (before after : Prop) :
    AyAMSEquisat before after -> before -> after :=
  fun witness hbefore =>
    witness after (fun forward _backward => forward hbefore)

theorem ay_ams_equisat_backward (before after : Prop) :
    AyAMSEquisat before after -> after -> before :=
  fun witness hafter =>
    witness before (fun _forward backward => backward hafter)

theorem ay_ams_model_intro (formula assignment : Prop) :
    formula -> assignment -> AyAMSModel formula assignment :=
  fun formulaProof assignmentProof =>
    ay_ams_conj_intro formula assignment formulaProof assignmentProof

theorem ay_ams_model_formula (formula assignment : Prop) :
    AyAMSModel formula assignment -> formula :=
  fun model => ay_ams_conj_left formula assignment model

theorem ay_ams_model_assignment (formula assignment : Prop) :
    AyAMSModel formula assignment -> assignment :=
  fun model => ay_ams_conj_right formula assignment model

theorem ay_ams_entry_intro
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    exitCode -> artifacts -> checkerDecision -> auditDigest -> diagnostic ->
    AyAMSEntry exitCode artifacts checkerDecision auditDigest diagnostic :=
  fun exitProof artifactsProof checkerProof auditProof diagnosticProof =>
    ay_ams_conj_intro exitCode
      (AyAMSConj artifacts
        (AyAMSConj checkerDecision (AyAMSConj auditDigest diagnostic)))
      exitProof
      (ay_ams_conj_intro artifacts
        (AyAMSConj checkerDecision (AyAMSConj auditDigest diagnostic))
        artifactsProof
        (ay_ams_conj_intro checkerDecision
          (AyAMSConj auditDigest diagnostic)
          checkerProof
          (ay_ams_conj_intro auditDigest diagnostic auditProof
            diagnosticProof)))

theorem ay_ams_entry_exit
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    AyAMSEntry exitCode artifacts checkerDecision auditDigest diagnostic ->
    exitCode :=
  fun entry =>
    ay_ams_conj_left exitCode
      (AyAMSConj artifacts
        (AyAMSConj checkerDecision (AyAMSConj auditDigest diagnostic)))
      entry

theorem ay_ams_entry_checker
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    AyAMSEntry exitCode artifacts checkerDecision auditDigest diagnostic ->
    checkerDecision :=
  fun entry =>
    ay_ams_conj_right exitCode
      (AyAMSConj artifacts
        (AyAMSConj checkerDecision (AyAMSConj auditDigest diagnostic)))
      entry checkerDecision
      (fun _artifactsProof tail =>
        tail checkerDecision (fun checkerProof _auditTail => checkerProof))

theorem ay_ams_entry_audit
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    AyAMSEntry exitCode artifacts checkerDecision auditDigest diagnostic ->
    auditDigest :=
  fun entry =>
    ay_ams_conj_right exitCode
      (AyAMSConj artifacts
        (AyAMSConj checkerDecision (AyAMSConj auditDigest diagnostic)))
      entry auditDigest
      (fun _artifactsProof tail =>
        tail auditDigest
          (fun _checkerProof auditTail =>
            auditTail auditDigest
              (fun auditProof _diagnosticProof => auditProof)))

theorem ay_ams_entry_diagnostic
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    AyAMSEntry exitCode artifacts checkerDecision auditDigest diagnostic ->
    diagnostic :=
  fun entry =>
    ay_ams_conj_right exitCode
      (AyAMSConj artifacts
        (AyAMSConj checkerDecision (AyAMSConj auditDigest diagnostic)))
      entry diagnostic
      (fun _artifactsProof tail =>
        tail diagnostic
          (fun _checkerProof auditTail =>
            auditTail diagnostic
              (fun _auditProof diagnosticProof => diagnosticProof)))

theorem ay_ams_leaf_hash_intro (entry leafHash : Prop) :
    entry -> leafHash -> AyAMSLeafHash entry leafHash :=
  ay_ams_conj_intro entry leafHash

theorem ay_ams_leaf_hash_entry (entry leafHash : Prop) :
    AyAMSLeafHash entry leafHash -> entry :=
  ay_ams_conj_left entry leafHash

theorem ay_ams_leaf_hash_value (entry leafHash : Prop) :
    AyAMSLeafHash entry leafHash -> leafHash :=
  ay_ams_conj_right entry leafHash

theorem ay_ams_membership_intro (leafHash root entry : Prop) :
    leafHash -> root -> entry -> AyAMSMembership leafHash root entry :=
  fun leafProof rootProof entryProof =>
    ay_ams_conj_intro leafHash (AyAMSConj root entry)
      leafProof
      (ay_ams_conj_intro root entry rootProof entryProof)

theorem ay_ams_membership_leaf (leafHash root entry : Prop) :
    AyAMSMembership leafHash root entry -> leafHash :=
  fun membership =>
    ay_ams_conj_left leafHash (AyAMSConj root entry) membership

theorem ay_ams_membership_root (leafHash root entry : Prop) :
    AyAMSMembership leafHash root entry -> root :=
  fun membership =>
    ay_ams_conj_right leafHash (AyAMSConj root entry) membership
      root (fun rootProof _entryProof => rootProof)

theorem ay_ams_membership_entry (leafHash root entry : Prop) :
    AyAMSMembership leafHash root entry -> entry :=
  fun membership =>
    ay_ams_conj_right leafHash (AyAMSConj root entry) membership
      entry (fun _rootProof entryProof => entryProof)

theorem ay_ams_summary_intro
    (acceptedSat acceptedUnsat diagnostics root : Prop) :
    acceptedSat -> acceptedUnsat -> diagnostics -> root ->
    AyAMSSummaryRoot acceptedSat acceptedUnsat diagnostics root :=
  fun satProof unsatProof diagnosticsProof rootProof =>
    ay_ams_conj_intro acceptedSat
      (AyAMSConj acceptedUnsat (AyAMSConj diagnostics root))
      satProof
      (ay_ams_conj_intro acceptedUnsat (AyAMSConj diagnostics root)
        unsatProof
        (ay_ams_conj_intro diagnostics root diagnosticsProof rootProof))

theorem ay_ams_summary_sat
    (acceptedSat acceptedUnsat diagnostics root : Prop) :
    AyAMSSummaryRoot acceptedSat acceptedUnsat diagnostics root ->
    acceptedSat :=
  fun summary =>
    ay_ams_conj_left acceptedSat
      (AyAMSConj acceptedUnsat (AyAMSConj diagnostics root)) summary

theorem ay_ams_summary_unsat
    (acceptedSat acceptedUnsat diagnostics root : Prop) :
    AyAMSSummaryRoot acceptedSat acceptedUnsat diagnostics root ->
    acceptedUnsat :=
  fun summary =>
    ay_ams_conj_right acceptedSat
      (AyAMSConj acceptedUnsat (AyAMSConj diagnostics root))
      summary acceptedUnsat (fun unsatProof _tail => unsatProof)

theorem ay_ams_summary_diagnostics
    (acceptedSat acceptedUnsat diagnostics root : Prop) :
    AyAMSSummaryRoot acceptedSat acceptedUnsat diagnostics root ->
    diagnostics :=
  fun summary =>
    ay_ams_conj_right acceptedSat
      (AyAMSConj acceptedUnsat (AyAMSConj diagnostics root))
      summary diagnostics
      (fun _unsatProof tail =>
        tail diagnostics (fun diagnosticsProof _rootProof =>
          diagnosticsProof))

theorem ay_ams_summary_root
    (acceptedSat acceptedUnsat diagnostics root : Prop) :
    AyAMSSummaryRoot acceptedSat acceptedUnsat diagnostics root -> root :=
  fun summary =>
    ay_ams_conj_right acceptedSat
      (AyAMSConj acceptedUnsat (AyAMSConj diagnostics root))
      summary root
      (fun _unsatProof tail =>
        tail root (fun _diagnosticsProof rootProof => rootProof))

theorem ay_ams_tail_root_agreement_intro (tailDigest root : Prop) :
    tailDigest -> root -> AyAMSTailRootAgreement tailDigest root :=
  ay_ams_conj_intro tailDigest root

theorem ay_ams_tail_root_agreement_tail (tailDigest root : Prop) :
    AyAMSTailRootAgreement tailDigest root -> tailDigest :=
  ay_ams_conj_left tailDigest root

theorem ay_ams_tail_root_agreement_root (tailDigest root : Prop) :
    AyAMSTailRootAgreement tailDigest root -> root :=
  ay_ams_conj_right tailDigest root

theorem ay_ams_no_claim_intro (exitCode auditDigest diagnostic : Prop) :
    exitCode -> auditDigest -> diagnostic ->
    AyAMSNoClaim exitCode auditDigest diagnostic :=
  fun exitProof auditProof diagnosticProof =>
    ay_ams_conj_intro exitCode (AyAMSConj auditDigest diagnostic)
      exitProof
      (ay_ams_conj_intro auditDigest diagnostic auditProof diagnosticProof)

theorem ay_ams_diagnostic_entry_no_claim
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    AyAMSEntry exitCode artifacts checkerDecision auditDigest diagnostic ->
    AyAMSNoClaim exitCode auditDigest diagnostic :=
  fun entry =>
    ay_ams_no_claim_intro exitCode auditDigest diagnostic
      (ay_ams_entry_exit exitCode artifacts checkerDecision auditDigest
        diagnostic entry)
      (ay_ams_entry_audit exitCode artifacts checkerDecision auditDigest
        diagnostic entry)
      (ay_ams_entry_diagnostic exitCode artifacts checkerDecision auditDigest
        diagnostic entry)

theorem ay_ams_preprocess_model_reconstruct
    (original solver internalAssignment visibleAssignment : Prop) :
    AyAMSPreprocessArtifact original solver ->
    (internalAssignment -> visibleAssignment) ->
    AyAMSModel solver internalAssignment ->
    AyAMSVisibleSAT original visibleAssignment :=
  fun preprocess decode model =>
    ay_ams_model_intro original visibleAssignment
      (ay_ams_equisat_backward original solver preprocess
        (ay_ams_model_formula solver internalAssignment model))
      (decode (ay_ams_model_assignment solver internalAssignment model))

theorem ay_ams_preprocess_unsat_reconstruct
    (original solver : Prop) :
    AyAMSPreprocessArtifact original solver ->
    AyAMSUnsat solver ->
    AyAMSUnsat original :=
  fun preprocess solverUnsat originalProof =>
    solverUnsat
      (ay_ams_equisat_forward original solver preprocess originalProof)

theorem ay_ams_replay_unsat_public
    (original solver stream finalClause : Prop) :
    AyAMSPreprocessArtifact original solver ->
    AyAMSReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    stream ->
    AyAMSUnsat original :=
  fun preprocess replay closeFinal streamProof originalProof =>
    closeFinal
      (replay streamProof
        (ay_ams_equisat_forward original solver preprocess originalProof))

theorem ay_ams_sat_entry_sound
    (acceptedSat artifacts satBranch auditDigest diagnostic original solver
      internalAssignment visibleAssignment : Prop) :
    AyAMSPreprocessArtifact original solver ->
    (internalAssignment -> visibleAssignment) ->
    (satBranch -> AyAMSModel solver internalAssignment) ->
    AyAMSEntry acceptedSat artifacts satBranch auditDigest diagnostic ->
    AyAMSVisibleSAT original visibleAssignment :=
  fun preprocess decode accept entry =>
    ay_ams_preprocess_model_reconstruct original solver internalAssignment
      visibleAssignment preprocess decode
      (accept
        (ay_ams_entry_checker acceptedSat artifacts satBranch auditDigest
          diagnostic entry))

theorem ay_ams_unsat_entry_sound
    (acceptedUnsat artifacts unsatBranch auditDigest diagnostic original solver
      stream finalClause : Prop) :
    AyAMSPreprocessArtifact original solver ->
    AyAMSReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    (unsatBranch -> stream) ->
    AyAMSEntry acceptedUnsat artifacts unsatBranch auditDigest diagnostic ->
    AyAMSUnsat original :=
  fun preprocess replay closeFinal accept entry =>
    ay_ams_replay_unsat_public original solver stream finalClause preprocess
      replay closeFinal
      (accept
        (ay_ams_entry_checker acceptedUnsat artifacts unsatBranch auditDigest
          diagnostic entry))

theorem ay_ams_sat_membership_sound
    (leafHash root acceptedSat artifacts satBranch auditDigest diagnostic
      original solver internalAssignment visibleAssignment : Prop) :
    AyAMSPreprocessArtifact original solver ->
    (internalAssignment -> visibleAssignment) ->
    (satBranch -> AyAMSModel solver internalAssignment) ->
    AyAMSMembership leafHash root
      (AyAMSEntry acceptedSat artifacts satBranch auditDigest diagnostic) ->
    AyAMSVisibleSAT original visibleAssignment :=
  fun preprocess decode accept membership =>
    ay_ams_sat_entry_sound acceptedSat artifacts satBranch auditDigest
      diagnostic original solver internalAssignment visibleAssignment
      preprocess decode accept
      (ay_ams_membership_entry leafHash root
        (AyAMSEntry acceptedSat artifacts satBranch auditDigest diagnostic)
        membership)

theorem ay_ams_unsat_membership_sound
    (leafHash root acceptedUnsat artifacts unsatBranch auditDigest diagnostic
      original solver stream finalClause : Prop) :
    AyAMSPreprocessArtifact original solver ->
    AyAMSReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    (unsatBranch -> stream) ->
    AyAMSMembership leafHash root
      (AyAMSEntry acceptedUnsat artifacts unsatBranch auditDigest
        diagnostic) ->
    AyAMSUnsat original :=
  fun preprocess replay closeFinal accept membership =>
    ay_ams_unsat_entry_sound acceptedUnsat artifacts unsatBranch auditDigest
      diagnostic original solver stream finalClause preprocess replay
      closeFinal accept
      (ay_ams_membership_entry leafHash root
        (AyAMSEntry acceptedUnsat artifacts unsatBranch auditDigest
          diagnostic)
        membership)

theorem ay_ams_diagnostic_membership_no_claim
    (leafHash root exitCode artifacts checkerDecision auditDigest diagnostic :
      Prop) :
    AyAMSMembership leafHash root
      (AyAMSEntry exitCode artifacts checkerDecision auditDigest
        diagnostic) ->
    AyAMSNoClaim exitCode auditDigest diagnostic :=
  fun membership =>
    ay_ams_diagnostic_entry_no_claim exitCode artifacts checkerDecision
      auditDigest diagnostic
      (ay_ams_membership_entry leafHash root
        (AyAMSEntry exitCode artifacts checkerDecision auditDigest
          diagnostic)
        membership)

theorem ay_ams_summary_membership_root_agrees
    (leafHash acceptedSat acceptedUnsat diagnostics root entry : Prop) :
    AyAMSSummaryRoot acceptedSat acceptedUnsat diagnostics root ->
    AyAMSMembership leafHash root entry ->
    root :=
  fun _summary membership =>
    ay_ams_membership_root leafHash root entry membership

theorem ay_ams_tail_root_membership_agrees
    (tailDigest root leafHash entry : Prop) :
    AyAMSTailRootAgreement tailDigest root ->
    AyAMSMembership leafHash root entry ->
    AyAMSConj tailDigest root :=
  fun agreement membership =>
    ay_ams_conj_intro tailDigest root
      (ay_ams_tail_root_agreement_tail tailDigest root agreement)
      (ay_ams_membership_root leafHash root entry membership)

theorem ay_ams_summary_sat_membership_preserved
    (acceptedSat acceptedUnsat diagnostics root satFact : Prop) :
    (acceptedSat -> satFact) ->
    AyAMSSummaryRoot acceptedSat acceptedUnsat diagnostics root ->
    satFact :=
  fun satSound summary =>
    satSound
      (ay_ams_summary_sat acceptedSat acceptedUnsat diagnostics root summary)

theorem ay_ams_summary_unsat_membership_preserved
    (acceptedSat acceptedUnsat diagnostics root unsatFact : Prop) :
    (acceptedUnsat -> unsatFact) ->
    AyAMSSummaryRoot acceptedSat acceptedUnsat diagnostics root ->
    unsatFact :=
  fun unsatSound summary =>
    unsatSound
      (ay_ams_summary_unsat acceptedSat acceptedUnsat diagnostics root
        summary)

theorem ay_ams_summary_diagnostic_no_claim
    (acceptedSat acceptedUnsat diagnostics root noClaim : Prop) :
    (diagnostics -> noClaim) ->
    AyAMSSummaryRoot acceptedSat acceptedUnsat diagnostics root ->
    noClaim :=
  fun diagnosticsNoClaim summary =>
    diagnosticsNoClaim
      (ay_ams_summary_diagnostics acceptedSat acceptedUnsat diagnostics root
        summary)
