-- SAT-COMP validator audit Merkle-pruning core.
--
-- Safe pruning keeps retained membership witnesses for accepted SAT/UNSAT
-- leaves and turns missing/pruned evidence into explicit no-claim diagnostics.
-- Merkle roots and retained prefix/suffix summaries are abstract propositions.

def AyAMPConj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def AyAMPDisj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyAMPEquisat (before after : Prop) : Prop :=
  AyAMPConj (before -> after) (after -> before)

def AyAMPOutcome (sat unsat : Prop) : Prop :=
  AyAMPDisj sat unsat

def AyAMPPublicResult (satFact unsatFact noClaim : Prop) : Prop :=
  AyAMPDisj satFact (AyAMPDisj unsatFact noClaim)

def AyAMPArtifacts (certId archiveKey : Prop) : Prop :=
  AyAMPConj certId archiveKey

def AyAMPEntry
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    Prop :=
  AyAMPConj exitCode
    (AyAMPConj artifacts
      (AyAMPConj checkerDecision
        (AyAMPConj auditDigest diagnostic)))

def AyAMPLeafHash (entry leafHash : Prop) : Prop :=
  AyAMPConj entry leafHash

def AyAMPMembership (leafHash root entry : Prop) : Prop :=
  AyAMPConj leafHash (AyAMPConj root entry)

def AyAMPFullLog (entries root tailDigest : Prop) : Prop :=
  AyAMPConj entries (AyAMPConj root tailDigest)

def AyAMPRetainedSummary (pref suff root tailDigest : Prop) : Prop :=
  AyAMPConj pref (AyAMPConj suff (AyAMPConj root tailDigest))

def AyAMPPrunedLeaf (entry diagnostic : Prop) : Prop :=
  AyAMPConj entry diagnostic

def AyAMPRootAgreement (fullRoot retainedRoot : Prop) : Prop :=
  AyAMPConj fullRoot retainedRoot

def AyAMPNoClaim (reason auditDigest diagnostic : Prop) : Prop :=
  AyAMPConj reason (AyAMPConj auditDigest diagnostic)

def AyAMPPruneWitness
    (fullLog retainedSummary prunedDiagnostics rootAgreement : Prop) : Prop :=
  AyAMPConj fullLog
    (AyAMPConj retainedSummary
      (AyAMPConj prunedDiagnostics rootAgreement))

def AyAMPModel (formula assignment : Prop) : Prop :=
  AyAMPConj formula assignment

def AyAMPUnsat (formula : Prop) : Prop :=
  formula -> False

def AyAMPVisibleSAT (original visibleAssignment : Prop) : Prop :=
  AyAMPModel original visibleAssignment

def AyAMPPreprocessArtifact (original solver : Prop) : Prop :=
  AyAMPEquisat original solver

def AyAMPReplayAccepted (solver stream finalClause : Prop) : Prop :=
  stream -> solver -> finalClause

theorem ay_amp_conj_intro (left right : Prop) :
    left -> right -> AyAMPConj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_amp_conj_left (left right : Prop) :
    AyAMPConj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_amp_conj_right (left right : Prop) :
    AyAMPConj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_amp_disj_left (left right : Prop) :
    left -> AyAMPDisj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_amp_disj_right (left right : Prop) :
    right -> AyAMPDisj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_amp_equisat_forward (before after : Prop) :
    AyAMPEquisat before after -> before -> after :=
  fun witness hbefore =>
    witness after (fun forward _backward => forward hbefore)

theorem ay_amp_equisat_backward (before after : Prop) :
    AyAMPEquisat before after -> after -> before :=
  fun witness hafter =>
    witness before (fun _forward backward => backward hafter)

theorem ay_amp_model_intro (formula assignment : Prop) :
    formula -> assignment -> AyAMPModel formula assignment :=
  fun formulaProof assignmentProof =>
    ay_amp_conj_intro formula assignment formulaProof assignmentProof

theorem ay_amp_model_formula (formula assignment : Prop) :
    AyAMPModel formula assignment -> formula :=
  fun model => ay_amp_conj_left formula assignment model

theorem ay_amp_model_assignment (formula assignment : Prop) :
    AyAMPModel formula assignment -> assignment :=
  fun model => ay_amp_conj_right formula assignment model

theorem ay_amp_entry_intro
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    exitCode -> artifacts -> checkerDecision -> auditDigest -> diagnostic ->
    AyAMPEntry exitCode artifacts checkerDecision auditDigest diagnostic :=
  fun exitProof artifactsProof checkerProof auditProof diagnosticProof =>
    ay_amp_conj_intro exitCode
      (AyAMPConj artifacts
        (AyAMPConj checkerDecision (AyAMPConj auditDigest diagnostic)))
      exitProof
      (ay_amp_conj_intro artifacts
        (AyAMPConj checkerDecision (AyAMPConj auditDigest diagnostic))
        artifactsProof
        (ay_amp_conj_intro checkerDecision
          (AyAMPConj auditDigest diagnostic)
          checkerProof
          (ay_amp_conj_intro auditDigest diagnostic auditProof
            diagnosticProof)))

theorem ay_amp_entry_checker
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    AyAMPEntry exitCode artifacts checkerDecision auditDigest diagnostic ->
    checkerDecision :=
  fun entry =>
    ay_amp_conj_right exitCode
      (AyAMPConj artifacts
        (AyAMPConj checkerDecision (AyAMPConj auditDigest diagnostic)))
      entry checkerDecision
      (fun _artifactsProof tail =>
        tail checkerDecision (fun checkerProof _auditTail => checkerProof))

theorem ay_amp_entry_audit
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    AyAMPEntry exitCode artifacts checkerDecision auditDigest diagnostic ->
    auditDigest :=
  fun entry =>
    ay_amp_conj_right exitCode
      (AyAMPConj artifacts
        (AyAMPConj checkerDecision (AyAMPConj auditDigest diagnostic)))
      entry auditDigest
      (fun _artifactsProof tail =>
        tail auditDigest
          (fun _checkerProof auditTail =>
            auditTail auditDigest
              (fun auditProof _diagnosticProof => auditProof)))

theorem ay_amp_entry_diagnostic
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    AyAMPEntry exitCode artifacts checkerDecision auditDigest diagnostic ->
    diagnostic :=
  fun entry =>
    ay_amp_conj_right exitCode
      (AyAMPConj artifacts
        (AyAMPConj checkerDecision (AyAMPConj auditDigest diagnostic)))
      entry diagnostic
      (fun _artifactsProof tail =>
        tail diagnostic
          (fun _checkerProof auditTail =>
            auditTail diagnostic
              (fun _auditProof diagnosticProof => diagnosticProof)))

theorem ay_amp_membership_intro (leafHash root entry : Prop) :
    leafHash -> root -> entry -> AyAMPMembership leafHash root entry :=
  fun leafProof rootProof entryProof =>
    ay_amp_conj_intro leafHash (AyAMPConj root entry)
      leafProof
      (ay_amp_conj_intro root entry rootProof entryProof)

theorem ay_amp_membership_leaf (leafHash root entry : Prop) :
    AyAMPMembership leafHash root entry -> leafHash :=
  fun membership =>
    ay_amp_conj_left leafHash (AyAMPConj root entry) membership

theorem ay_amp_membership_root (leafHash root entry : Prop) :
    AyAMPMembership leafHash root entry -> root :=
  fun membership =>
    ay_amp_conj_right leafHash (AyAMPConj root entry) membership
      root (fun rootProof _entryProof => rootProof)

theorem ay_amp_membership_entry (leafHash root entry : Prop) :
    AyAMPMembership leafHash root entry -> entry :=
  fun membership =>
    ay_amp_conj_right leafHash (AyAMPConj root entry) membership
      entry (fun _rootProof entryProof => entryProof)

theorem ay_amp_full_log_intro (entries root tailDigest : Prop) :
    entries -> root -> tailDigest -> AyAMPFullLog entries root tailDigest :=
  fun entriesProof rootProof tailProof =>
    ay_amp_conj_intro entries (AyAMPConj root tailDigest)
      entriesProof
      (ay_amp_conj_intro root tailDigest rootProof tailProof)

theorem ay_amp_full_log_root (entries root tailDigest : Prop) :
    AyAMPFullLog entries root tailDigest -> root :=
  fun log =>
    ay_amp_conj_right entries (AyAMPConj root tailDigest) log
      root (fun rootProof _tailProof => rootProof)

theorem ay_amp_full_log_tail (entries root tailDigest : Prop) :
    AyAMPFullLog entries root tailDigest -> tailDigest :=
  fun log =>
    ay_amp_conj_right entries (AyAMPConj root tailDigest) log
      tailDigest (fun _rootProof tailProof => tailProof)

theorem ay_amp_retained_summary_intro
    (pref suff root tailDigest : Prop) :
    pref -> suff -> root -> tailDigest ->
    AyAMPRetainedSummary pref suff root tailDigest :=
  fun prefProof suffProof rootProof tailProof =>
    ay_amp_conj_intro pref
      (AyAMPConj suff (AyAMPConj root tailDigest))
      prefProof
      (ay_amp_conj_intro suff (AyAMPConj root tailDigest)
        suffProof
        (ay_amp_conj_intro root tailDigest rootProof tailProof))

theorem ay_amp_retained_prefix (pref suff root tailDigest : Prop) :
    AyAMPRetainedSummary pref suff root tailDigest -> pref :=
  fun summary =>
    ay_amp_conj_left pref
      (AyAMPConj suff (AyAMPConj root tailDigest)) summary

theorem ay_amp_retained_suffix (pref suff root tailDigest : Prop) :
    AyAMPRetainedSummary pref suff root tailDigest -> suff :=
  fun summary =>
    ay_amp_conj_right pref
      (AyAMPConj suff (AyAMPConj root tailDigest))
      summary suff (fun suffProof _tail => suffProof)

theorem ay_amp_retained_root (pref suff root tailDigest : Prop) :
    AyAMPRetainedSummary pref suff root tailDigest -> root :=
  fun summary =>
    ay_amp_conj_right pref
      (AyAMPConj suff (AyAMPConj root tailDigest))
      summary root
      (fun _suffProof tail =>
        tail root (fun rootProof _tailProof => rootProof))

theorem ay_amp_retained_tail (pref suff root tailDigest : Prop) :
    AyAMPRetainedSummary pref suff root tailDigest -> tailDigest :=
  fun summary =>
    ay_amp_conj_right pref
      (AyAMPConj suff (AyAMPConj root tailDigest))
      summary tailDigest
      (fun _suffProof tail =>
        tail tailDigest (fun _rootProof tailProof => tailProof))

theorem ay_amp_pruned_leaf_intro (entry diagnostic : Prop) :
    entry -> diagnostic -> AyAMPPrunedLeaf entry diagnostic :=
  ay_amp_conj_intro entry diagnostic

theorem ay_amp_pruned_leaf_entry (entry diagnostic : Prop) :
    AyAMPPrunedLeaf entry diagnostic -> entry :=
  ay_amp_conj_left entry diagnostic

theorem ay_amp_pruned_leaf_diagnostic (entry diagnostic : Prop) :
    AyAMPPrunedLeaf entry diagnostic -> diagnostic :=
  ay_amp_conj_right entry diagnostic

theorem ay_amp_root_agreement_intro (fullRoot retainedRoot : Prop) :
    fullRoot -> retainedRoot -> AyAMPRootAgreement fullRoot retainedRoot :=
  ay_amp_conj_intro fullRoot retainedRoot

theorem ay_amp_root_agreement_full (fullRoot retainedRoot : Prop) :
    AyAMPRootAgreement fullRoot retainedRoot -> fullRoot :=
  ay_amp_conj_left fullRoot retainedRoot

theorem ay_amp_root_agreement_retained (fullRoot retainedRoot : Prop) :
    AyAMPRootAgreement fullRoot retainedRoot -> retainedRoot :=
  ay_amp_conj_right fullRoot retainedRoot

theorem ay_amp_prune_witness_intro
    (fullLog retainedSummary prunedDiagnostics rootAgreement : Prop) :
    fullLog -> retainedSummary -> prunedDiagnostics -> rootAgreement ->
    AyAMPPruneWitness fullLog retainedSummary prunedDiagnostics
      rootAgreement :=
  fun fullProof retainedProof prunedProof rootProof =>
    ay_amp_conj_intro fullLog
      (AyAMPConj retainedSummary
        (AyAMPConj prunedDiagnostics rootAgreement))
      fullProof
      (ay_amp_conj_intro retainedSummary
        (AyAMPConj prunedDiagnostics rootAgreement)
        retainedProof
        (ay_amp_conj_intro prunedDiagnostics rootAgreement prunedProof
          rootProof))

theorem ay_amp_prune_full_log
    (fullLog retainedSummary prunedDiagnostics rootAgreement : Prop) :
    AyAMPPruneWitness fullLog retainedSummary prunedDiagnostics
      rootAgreement ->
    fullLog :=
  fun witness =>
    ay_amp_conj_left fullLog
      (AyAMPConj retainedSummary
        (AyAMPConj prunedDiagnostics rootAgreement))
      witness

theorem ay_amp_prune_retained_summary
    (fullLog retainedSummary prunedDiagnostics rootAgreement : Prop) :
    AyAMPPruneWitness fullLog retainedSummary prunedDiagnostics
      rootAgreement ->
    retainedSummary :=
  fun witness =>
    ay_amp_conj_right fullLog
      (AyAMPConj retainedSummary
        (AyAMPConj prunedDiagnostics rootAgreement))
      witness retainedSummary
      (fun retainedProof _tail => retainedProof)

theorem ay_amp_prune_diagnostics
    (fullLog retainedSummary prunedDiagnostics rootAgreement : Prop) :
    AyAMPPruneWitness fullLog retainedSummary prunedDiagnostics
      rootAgreement ->
    prunedDiagnostics :=
  fun witness =>
    ay_amp_conj_right fullLog
      (AyAMPConj retainedSummary
        (AyAMPConj prunedDiagnostics rootAgreement))
      witness prunedDiagnostics
      (fun _retainedProof tail =>
        tail prunedDiagnostics
          (fun prunedProof _rootProof => prunedProof))

theorem ay_amp_prune_root_agreement
    (fullLog retainedSummary prunedDiagnostics rootAgreement : Prop) :
    AyAMPPruneWitness fullLog retainedSummary prunedDiagnostics
      rootAgreement ->
    rootAgreement :=
  fun witness =>
    ay_amp_conj_right fullLog
      (AyAMPConj retainedSummary
        (AyAMPConj prunedDiagnostics rootAgreement))
      witness rootAgreement
      (fun _retainedProof tail =>
        tail rootAgreement (fun _prunedProof rootProof => rootProof))

theorem ay_amp_no_claim_intro (reason auditDigest diagnostic : Prop) :
    reason -> auditDigest -> diagnostic ->
    AyAMPNoClaim reason auditDigest diagnostic :=
  fun reasonProof auditProof diagnosticProof =>
    ay_amp_conj_intro reason (AyAMPConj auditDigest diagnostic)
      reasonProof
      (ay_amp_conj_intro auditDigest diagnostic auditProof diagnosticProof)

theorem ay_amp_pruned_leaf_no_claim
    (reason exitCode artifacts checkerDecision auditDigest diagnostic :
      Prop) :
    reason ->
    AyAMPPrunedLeaf
      (AyAMPEntry exitCode artifacts checkerDecision auditDigest diagnostic)
      diagnostic ->
    AyAMPNoClaim reason auditDigest diagnostic :=
  fun reasonProof pruned =>
    ay_amp_no_claim_intro reason auditDigest diagnostic
      reasonProof
      (ay_amp_entry_audit exitCode artifacts checkerDecision auditDigest
        diagnostic (ay_amp_pruned_leaf_entry
          (AyAMPEntry exitCode artifacts checkerDecision auditDigest
            diagnostic)
          diagnostic pruned))
      (ay_amp_pruned_leaf_diagnostic
        (AyAMPEntry exitCode artifacts checkerDecision auditDigest
          diagnostic)
        diagnostic pruned)

theorem ay_amp_missing_membership_no_claim
    (missingEvidence auditDigest diagnostic : Prop) :
    missingEvidence -> auditDigest -> diagnostic ->
    AyAMPNoClaim missingEvidence auditDigest diagnostic :=
  ay_amp_no_claim_intro missingEvidence auditDigest diagnostic

theorem ay_amp_preprocess_model_reconstruct
    (original solver internalAssignment visibleAssignment : Prop) :
    AyAMPPreprocessArtifact original solver ->
    (internalAssignment -> visibleAssignment) ->
    AyAMPModel solver internalAssignment ->
    AyAMPVisibleSAT original visibleAssignment :=
  fun preprocess decode model =>
    ay_amp_model_intro original visibleAssignment
      (ay_amp_equisat_backward original solver preprocess
        (ay_amp_model_formula solver internalAssignment model))
      (decode (ay_amp_model_assignment solver internalAssignment model))

theorem ay_amp_preprocess_unsat_reconstruct
    (original solver : Prop) :
    AyAMPPreprocessArtifact original solver ->
    AyAMPUnsat solver ->
    AyAMPUnsat original :=
  fun preprocess solverUnsat originalProof =>
    solverUnsat
      (ay_amp_equisat_forward original solver preprocess originalProof)

theorem ay_amp_replay_unsat_public
    (original solver stream finalClause : Prop) :
    AyAMPPreprocessArtifact original solver ->
    AyAMPReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    stream ->
    AyAMPUnsat original :=
  fun preprocess replay closeFinal streamProof originalProof =>
    closeFinal
      (replay streamProof
        (ay_amp_equisat_forward original solver preprocess originalProof))

theorem ay_amp_sat_membership_sound
    (leafHash root acceptedSat artifacts satBranch auditDigest diagnostic
      original solver internalAssignment visibleAssignment : Prop) :
    AyAMPPreprocessArtifact original solver ->
    (internalAssignment -> visibleAssignment) ->
    (satBranch -> AyAMPModel solver internalAssignment) ->
    AyAMPMembership leafHash root
      (AyAMPEntry acceptedSat artifacts satBranch auditDigest diagnostic) ->
    AyAMPVisibleSAT original visibleAssignment :=
  fun preprocess decode accept membership =>
    ay_amp_preprocess_model_reconstruct original solver internalAssignment
      visibleAssignment preprocess decode
      (accept
        (ay_amp_entry_checker acceptedSat artifacts satBranch auditDigest
          diagnostic
          (ay_amp_membership_entry leafHash root
            (AyAMPEntry acceptedSat artifacts satBranch auditDigest
              diagnostic)
            membership)))

theorem ay_amp_unsat_membership_sound
    (leafHash root acceptedUnsat artifacts unsatBranch auditDigest diagnostic
      original solver stream finalClause : Prop) :
    AyAMPPreprocessArtifact original solver ->
    AyAMPReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    (unsatBranch -> stream) ->
    AyAMPMembership leafHash root
      (AyAMPEntry acceptedUnsat artifacts unsatBranch auditDigest
        diagnostic) ->
    AyAMPUnsat original :=
  fun preprocess replay closeFinal accept membership =>
    ay_amp_replay_unsat_public original solver stream finalClause preprocess
      replay closeFinal
      (accept
        (ay_amp_entry_checker acceptedUnsat artifacts unsatBranch auditDigest
          diagnostic
          (ay_amp_membership_entry leafHash root
            (AyAMPEntry acceptedUnsat artifacts unsatBranch auditDigest
              diagnostic)
            membership)))

theorem ay_amp_root_agreement_from_prune
    (fullLog retainedSummary prunedDiagnostics fullRoot retainedRoot : Prop) :
    AyAMPPruneWitness fullLog retainedSummary prunedDiagnostics
      (AyAMPRootAgreement fullRoot retainedRoot) ->
    AyAMPRootAgreement fullRoot retainedRoot :=
  fun witness =>
    ay_amp_prune_root_agreement fullLog retainedSummary prunedDiagnostics
      (AyAMPRootAgreement fullRoot retainedRoot) witness

theorem ay_amp_retained_membership_root
    (pref suff retainedRoot tailDigest leafHash entry : Prop) :
    AyAMPRetainedSummary pref suff retainedRoot tailDigest ->
    AyAMPMembership leafHash retainedRoot entry ->
    retainedRoot :=
  fun _summary membership =>
    ay_amp_membership_root leafHash retainedRoot entry membership

theorem ay_amp_retained_sat_membership_preserved
    (fullLog retainedSummary prunedDiagnostics rootAgreement satFact : Prop) :
    AyAMPPruneWitness fullLog retainedSummary prunedDiagnostics
      rootAgreement ->
    (retainedSummary -> satFact) ->
    satFact :=
  fun witness retainedSound =>
    retainedSound
      (ay_amp_prune_retained_summary fullLog retainedSummary
        prunedDiagnostics rootAgreement witness)

theorem ay_amp_retained_unsat_membership_preserved
    (fullLog retainedSummary prunedDiagnostics rootAgreement unsatFact :
      Prop) :
    AyAMPPruneWitness fullLog retainedSummary prunedDiagnostics
      rootAgreement ->
    (retainedSummary -> unsatFact) ->
    unsatFact :=
  fun witness retainedSound =>
    retainedSound
      (ay_amp_prune_retained_summary fullLog retainedSummary
        prunedDiagnostics rootAgreement witness)

theorem ay_amp_pruned_gap_no_claim
    (fullLog retainedSummary prunedDiagnostics rootAgreement noClaim : Prop) :
    AyAMPPruneWitness fullLog retainedSummary prunedDiagnostics
      rootAgreement ->
    (prunedDiagnostics -> noClaim) ->
    noClaim :=
  fun witness diagnosticsNoClaim =>
    diagnosticsNoClaim
      (ay_amp_prune_diagnostics fullLog retainedSummary prunedDiagnostics
        rootAgreement witness)

theorem ay_amp_public_result_after_pruning
    (fullLog retainedSummary prunedDiagnostics rootAgreement satFact unsatFact
      noClaim : Prop) :
    AyAMPPruneWitness fullLog retainedSummary prunedDiagnostics
      rootAgreement ->
    (retainedSummary -> AyAMPPublicResult satFact unsatFact noClaim) ->
    (prunedDiagnostics -> noClaim) ->
    AyAMPPublicResult satFact unsatFact noClaim :=
  fun witness retainedResult _diagnosticsNoClaim =>
    retainedResult
      (ay_amp_prune_retained_summary fullLog retainedSummary
        prunedDiagnostics rootAgreement witness)

theorem ay_amp_public_result_for_pruned_only
    (satFact unsatFact prunedDiagnostics noClaim : Prop) :
    (prunedDiagnostics -> noClaim) ->
    prunedDiagnostics ->
    AyAMPPublicResult satFact unsatFact noClaim :=
  fun diagnosticsNoClaim prunedProof =>
    ay_amp_disj_right satFact (AyAMPDisj unsatFact noClaim)
      (ay_amp_disj_right unsatFact noClaim
        (diagnosticsNoClaim prunedProof))
