-- SAT-COMP validator audit report-cache eviction core.
--
-- Bounded report caches may publish only retained fresh hits with matching
-- root/digest/membership evidence.  Evicted, missing, or stale entries create
-- recomputation obligations and no-claim diagnostics instead of SAT/UNSAT
-- public claims.

def AyARCEConj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def AyARCEDisj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyARCEEquisat (before after : Prop) : Prop :=
  AyARCEConj (before -> after) (after -> before)

def AyARCEPublicResult (satFact unsatFact noClaim : Prop) : Prop :=
  AyARCEDisj satFact (AyARCEDisj unsatFact noClaim)

def AyARCEArtifacts (certId archiveKey : Prop) : Prop :=
  AyARCEConj certId archiveKey

def AyARCEEntry
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    Prop :=
  AyARCEConj exitCode
    (AyARCEConj artifacts
      (AyARCEConj checkerDecision
        (AyARCEConj auditDigest diagnostic)))

def AyARCEMembership (leafHash root entry : Prop) : Prop :=
  AyARCEConj leafHash (AyARCEConj root entry)

def AyARCECachedReport
    (reportDigest cachedRoot cachedMembership cacheEpoch : Prop) : Prop :=
  AyARCEConj reportDigest
    (AyARCEConj cachedRoot
      (AyARCEConj cachedMembership cacheEpoch))

def AyARCEFreshEvidence
    (rootMatch digestMatch membershipEvidence epochFresh : Prop) : Prop :=
  AyARCEConj rootMatch
    (AyARCEConj digestMatch
      (AyARCEConj membershipEvidence epochFresh))

def AyARCERetainedHit (cachedReport freshEvidence publicReport : Prop) :
    Prop :=
  AyARCEConj cachedReport (AyARCEConj freshEvidence publicReport)

def AyARCEEvictedEntry (evictionEpoch auditDigest diagnostic : Prop) :
    Prop :=
  AyARCEConj evictionEpoch (AyARCEConj auditDigest diagnostic)

def AyARCEMissingEntry (missReason auditDigest diagnostic : Prop) : Prop :=
  AyARCEConj missReason (AyARCEConj auditDigest diagnostic)

def AyARCEStaleReport (staleEpoch staleDigest diagnostic : Prop) : Prop :=
  AyARCEConj staleEpoch (AyARCEConj staleDigest diagnostic)

def AyARCERecomputeObligation
    (reason auditDigest diagnostic : Prop) : Prop :=
  AyARCEConj reason (AyARCEConj auditDigest diagnostic)

def AyARCENoClaim (reason auditDigest diagnostic : Prop) : Prop :=
  AyARCEConj reason (AyARCEConj auditDigest diagnostic)

def AyARCEModel (formula assignment : Prop) : Prop :=
  AyARCEConj formula assignment

def AyARCEUnsat (formula : Prop) : Prop :=
  formula -> False

def AyARCEVisibleSAT (original visibleAssignment : Prop) : Prop :=
  AyARCEModel original visibleAssignment

def AyARCEPreprocessArtifact (original solver : Prop) : Prop :=
  AyARCEEquisat original solver

def AyARCEReplayAccepted (solver stream finalClause : Prop) : Prop :=
  stream -> solver -> finalClause

theorem ay_arce_conj_intro (left right : Prop) :
    left -> right -> AyARCEConj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_arce_conj_left (left right : Prop) :
    AyARCEConj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_arce_conj_right (left right : Prop) :
    AyARCEConj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_arce_disj_left (left right : Prop) :
    left -> AyARCEDisj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_arce_disj_right (left right : Prop) :
    right -> AyARCEDisj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_arce_equisat_forward (before after : Prop) :
    AyARCEEquisat before after -> before -> after :=
  fun witness hbefore =>
    witness after (fun forward _backward => forward hbefore)

theorem ay_arce_equisat_backward (before after : Prop) :
    AyARCEEquisat before after -> after -> before :=
  fun witness hafter =>
    witness before (fun _forward backward => backward hafter)

theorem ay_arce_model_intro (formula assignment : Prop) :
    formula -> assignment -> AyARCEModel formula assignment :=
  fun formulaProof assignmentProof =>
    ay_arce_conj_intro formula assignment formulaProof assignmentProof

theorem ay_arce_model_formula (formula assignment : Prop) :
    AyARCEModel formula assignment -> formula :=
  fun model => ay_arce_conj_left formula assignment model

theorem ay_arce_model_assignment (formula assignment : Prop) :
    AyARCEModel formula assignment -> assignment :=
  fun model => ay_arce_conj_right formula assignment model

theorem ay_arce_entry_intro
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    exitCode -> artifacts -> checkerDecision -> auditDigest -> diagnostic ->
    AyARCEEntry exitCode artifacts checkerDecision auditDigest diagnostic :=
  fun exitProof artifactsProof checkerProof auditProof diagnosticProof =>
    ay_arce_conj_intro exitCode
      (AyARCEConj artifacts
        (AyARCEConj checkerDecision (AyARCEConj auditDigest diagnostic)))
      exitProof
      (ay_arce_conj_intro artifacts
        (AyARCEConj checkerDecision (AyARCEConj auditDigest diagnostic))
        artifactsProof
        (ay_arce_conj_intro checkerDecision
          (AyARCEConj auditDigest diagnostic)
          checkerProof
          (ay_arce_conj_intro auditDigest diagnostic auditProof
            diagnosticProof)))

theorem ay_arce_entry_checker
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    AyARCEEntry exitCode artifacts checkerDecision auditDigest diagnostic ->
    checkerDecision :=
  fun entry =>
    ay_arce_conj_right exitCode
      (AyARCEConj artifacts
        (AyARCEConj checkerDecision (AyARCEConj auditDigest diagnostic)))
      entry checkerDecision
      (fun _artifactsProof tail =>
        tail checkerDecision (fun checkerProof _auditTail => checkerProof))

theorem ay_arce_membership_intro (leafHash root entry : Prop) :
    leafHash -> root -> entry -> AyARCEMembership leafHash root entry :=
  fun leafProof rootProof entryProof =>
    ay_arce_conj_intro leafHash (AyARCEConj root entry)
      leafProof
      (ay_arce_conj_intro root entry rootProof entryProof)

theorem ay_arce_membership_entry (leafHash root entry : Prop) :
    AyARCEMembership leafHash root entry -> entry :=
  fun membership =>
    ay_arce_conj_right leafHash (AyARCEConj root entry) membership
      entry (fun _rootProof entryProof => entryProof)

theorem ay_arce_cached_report_intro
    (reportDigest cachedRoot cachedMembership cacheEpoch : Prop) :
    reportDigest -> cachedRoot -> cachedMembership -> cacheEpoch ->
    AyARCECachedReport reportDigest cachedRoot cachedMembership
      cacheEpoch :=
  fun digestProof rootProof membershipProof epochProof =>
    ay_arce_conj_intro reportDigest
      (AyARCEConj cachedRoot
        (AyARCEConj cachedMembership cacheEpoch))
      digestProof
      (ay_arce_conj_intro cachedRoot
        (AyARCEConj cachedMembership cacheEpoch)
        rootProof
        (ay_arce_conj_intro cachedMembership cacheEpoch membershipProof
          epochProof))

theorem ay_arce_fresh_evidence_intro
    (rootMatch digestMatch membershipEvidence epochFresh : Prop) :
    rootMatch -> digestMatch -> membershipEvidence -> epochFresh ->
    AyARCEFreshEvidence rootMatch digestMatch membershipEvidence
      epochFresh :=
  fun rootProof digestProof membershipProof epochProof =>
    ay_arce_conj_intro rootMatch
      (AyARCEConj digestMatch
        (AyARCEConj membershipEvidence epochFresh))
      rootProof
      (ay_arce_conj_intro digestMatch
        (AyARCEConj membershipEvidence epochFresh)
        digestProof
        (ay_arce_conj_intro membershipEvidence epochFresh membershipProof
          epochProof))

theorem ay_arce_fresh_evidence_membership
    (rootMatch digestMatch membershipEvidence epochFresh : Prop) :
    AyARCEFreshEvidence rootMatch digestMatch membershipEvidence
      epochFresh ->
    membershipEvidence :=
  fun evidence =>
    ay_arce_conj_right rootMatch
      (AyARCEConj digestMatch
        (AyARCEConj membershipEvidence epochFresh))
      evidence membershipEvidence
      (fun _digestProof tail =>
        tail membershipEvidence
          (fun membershipProof _epochProof => membershipProof))

theorem ay_arce_fresh_evidence_epoch
    (rootMatch digestMatch membershipEvidence epochFresh : Prop) :
    AyARCEFreshEvidence rootMatch digestMatch membershipEvidence
      epochFresh ->
    epochFresh :=
  fun evidence =>
    ay_arce_conj_right rootMatch
      (AyARCEConj digestMatch
        (AyARCEConj membershipEvidence epochFresh))
      evidence epochFresh
      (fun _digestProof tail =>
        tail epochFresh (fun _membershipProof epochProof => epochProof))

theorem ay_arce_retained_hit_intro
    (cachedReport freshEvidence publicReport : Prop) :
    cachedReport -> freshEvidence -> publicReport ->
    AyARCERetainedHit cachedReport freshEvidence publicReport :=
  fun reportProof evidenceProof publicProof =>
    ay_arce_conj_intro cachedReport
      (AyARCEConj freshEvidence publicReport)
      reportProof
      (ay_arce_conj_intro freshEvidence publicReport evidenceProof
        publicProof)

theorem ay_arce_retained_hit_report
    (cachedReport freshEvidence publicReport : Prop) :
    AyARCERetainedHit cachedReport freshEvidence publicReport ->
    cachedReport :=
  fun hit =>
    ay_arce_conj_left cachedReport
      (AyARCEConj freshEvidence publicReport) hit

theorem ay_arce_retained_hit_evidence
    (cachedReport freshEvidence publicReport : Prop) :
    AyARCERetainedHit cachedReport freshEvidence publicReport ->
    freshEvidence :=
  fun hit =>
    ay_arce_conj_right cachedReport
      (AyARCEConj freshEvidence publicReport)
      hit freshEvidence (fun evidenceProof _publicProof => evidenceProof)

theorem ay_arce_retained_hit_public
    (cachedReport freshEvidence publicReport : Prop) :
    AyARCERetainedHit cachedReport freshEvidence publicReport ->
    publicReport :=
  fun hit =>
    ay_arce_conj_right cachedReport
      (AyARCEConj freshEvidence publicReport)
      hit publicReport (fun _evidenceProof publicProof => publicProof)

theorem ay_arce_no_claim_intro
    (reason auditDigest diagnostic : Prop) :
    reason -> auditDigest -> diagnostic ->
    AyARCENoClaim reason auditDigest diagnostic :=
  fun reasonProof auditProof diagnosticProof =>
    ay_arce_conj_intro reason (AyARCEConj auditDigest diagnostic)
      reasonProof
      (ay_arce_conj_intro auditDigest diagnostic auditProof
        diagnosticProof)

theorem ay_arce_recompute_intro
    (reason auditDigest diagnostic : Prop) :
    reason -> auditDigest -> diagnostic ->
    AyARCERecomputeObligation reason auditDigest diagnostic :=
  fun reasonProof auditProof diagnosticProof =>
    ay_arce_conj_intro reason (AyARCEConj auditDigest diagnostic)
      reasonProof
      (ay_arce_conj_intro auditDigest diagnostic auditProof
        diagnosticProof)

theorem ay_arce_evicted_entry_intro
    (evictionEpoch auditDigest diagnostic : Prop) :
    evictionEpoch -> auditDigest -> diagnostic ->
    AyARCEEvictedEntry evictionEpoch auditDigest diagnostic :=
  fun epochProof auditProof diagnosticProof =>
    ay_arce_conj_intro evictionEpoch
      (AyARCEConj auditDigest diagnostic)
      epochProof
      (ay_arce_conj_intro auditDigest diagnostic auditProof
        diagnosticProof)

theorem ay_arce_evicted_entry_no_claim
    (evictionEpoch auditDigest diagnostic : Prop) :
    AyARCEEvictedEntry evictionEpoch auditDigest diagnostic ->
    AyARCENoClaim evictionEpoch auditDigest diagnostic :=
  fun evicted =>
    ay_arce_conj_intro evictionEpoch
      (AyARCEConj auditDigest diagnostic)
      (ay_arce_conj_left evictionEpoch
        (AyARCEConj auditDigest diagnostic) evicted)
      (ay_arce_conj_right evictionEpoch
        (AyARCEConj auditDigest diagnostic) evicted)

theorem ay_arce_evicted_entry_recompute
    (evictionEpoch auditDigest diagnostic : Prop) :
    AyARCEEvictedEntry evictionEpoch auditDigest diagnostic ->
    AyARCERecomputeObligation evictionEpoch auditDigest diagnostic :=
  fun evicted =>
    ay_arce_conj_intro evictionEpoch
      (AyARCEConj auditDigest diagnostic)
      (ay_arce_conj_left evictionEpoch
        (AyARCEConj auditDigest diagnostic) evicted)
      (ay_arce_conj_right evictionEpoch
        (AyARCEConj auditDigest diagnostic) evicted)

theorem ay_arce_missing_entry_intro
    (missReason auditDigest diagnostic : Prop) :
    missReason -> auditDigest -> diagnostic ->
    AyARCEMissingEntry missReason auditDigest diagnostic :=
  fun missProof auditProof diagnosticProof =>
    ay_arce_conj_intro missReason (AyARCEConj auditDigest diagnostic)
      missProof
      (ay_arce_conj_intro auditDigest diagnostic auditProof
        diagnosticProof)

theorem ay_arce_missing_entry_no_claim
    (missReason auditDigest diagnostic : Prop) :
    AyARCEMissingEntry missReason auditDigest diagnostic ->
    AyARCENoClaim missReason auditDigest diagnostic :=
  fun missing =>
    ay_arce_conj_intro missReason (AyARCEConj auditDigest diagnostic)
      (ay_arce_conj_left missReason
        (AyARCEConj auditDigest diagnostic) missing)
      (ay_arce_conj_right missReason
        (AyARCEConj auditDigest diagnostic) missing)

theorem ay_arce_stale_report_intro
    (staleEpoch staleDigest diagnostic : Prop) :
    staleEpoch -> staleDigest -> diagnostic ->
    AyARCEStaleReport staleEpoch staleDigest diagnostic :=
  fun epochProof digestProof diagnosticProof =>
    ay_arce_conj_intro staleEpoch
      (AyARCEConj staleDigest diagnostic)
      epochProof
      (ay_arce_conj_intro staleDigest diagnostic digestProof
        diagnosticProof)

theorem ay_arce_stale_report_no_claim
    (staleEpoch staleDigest diagnostic : Prop) :
    AyARCEStaleReport staleEpoch staleDigest diagnostic ->
    AyARCENoClaim staleEpoch staleDigest diagnostic :=
  fun stale =>
    ay_arce_conj_intro staleEpoch (AyARCEConj staleDigest diagnostic)
      (ay_arce_conj_left staleEpoch
        (AyARCEConj staleDigest diagnostic) stale)
      (ay_arce_conj_right staleEpoch
        (AyARCEConj staleDigest diagnostic) stale)

theorem ay_arce_preprocess_model_reconstruct
    (original solver internalAssignment visibleAssignment : Prop) :
    AyARCEPreprocessArtifact original solver ->
    (internalAssignment -> visibleAssignment) ->
    AyARCEModel solver internalAssignment ->
    AyARCEVisibleSAT original visibleAssignment :=
  fun preprocess decode model =>
    ay_arce_model_intro original visibleAssignment
      (ay_arce_equisat_backward original solver preprocess
        (ay_arce_model_formula solver internalAssignment model))
      (decode (ay_arce_model_assignment solver internalAssignment model))

theorem ay_arce_preprocess_unsat_reconstruct
    (original solver : Prop) :
    AyARCEPreprocessArtifact original solver ->
    AyARCEUnsat solver ->
    AyARCEUnsat original :=
  fun preprocess solverUnsat originalProof =>
    solverUnsat
      (ay_arce_equisat_forward original solver preprocess originalProof)

theorem ay_arce_replay_unsat_public
    (original solver stream finalClause : Prop) :
    AyARCEPreprocessArtifact original solver ->
    AyARCEReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    stream ->
    AyARCEUnsat original :=
  fun preprocess replay closeFinal streamProof originalProof =>
    closeFinal
      (replay streamProof
        (ay_arce_equisat_forward original solver preprocess originalProof))

theorem ay_arce_retained_sat_membership_sound
    (leafHash root acceptedSat artifacts satBranch auditDigest diagnostic
      original solver internalAssignment visibleAssignment : Prop) :
    AyARCEPreprocessArtifact original solver ->
    (internalAssignment -> visibleAssignment) ->
    (satBranch -> AyARCEModel solver internalAssignment) ->
    AyARCEMembership leafHash root
      (AyARCEEntry acceptedSat artifacts satBranch auditDigest diagnostic) ->
    AyARCEVisibleSAT original visibleAssignment :=
  fun preprocess decode accept membership =>
    ay_arce_preprocess_model_reconstruct original solver internalAssignment
      visibleAssignment preprocess decode
      (accept
        (ay_arce_entry_checker acceptedSat artifacts satBranch auditDigest
          diagnostic
          (ay_arce_membership_entry leafHash root
            (AyARCEEntry acceptedSat artifacts satBranch auditDigest
              diagnostic)
            membership)))

theorem ay_arce_retained_unsat_membership_sound
    (leafHash root acceptedUnsat artifacts unsatBranch auditDigest diagnostic
      original solver stream finalClause : Prop) :
    AyARCEPreprocessArtifact original solver ->
    AyARCEReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    (unsatBranch -> stream) ->
    AyARCEMembership leafHash root
      (AyARCEEntry acceptedUnsat artifacts unsatBranch auditDigest
        diagnostic) ->
    AyARCEUnsat original :=
  fun preprocess replay closeFinal accept membership =>
    ay_arce_replay_unsat_public original solver stream finalClause preprocess
      replay closeFinal
      (accept
        (ay_arce_entry_checker acceptedUnsat artifacts unsatBranch auditDigest
          diagnostic
          (ay_arce_membership_entry leafHash root
            (AyARCEEntry acceptedUnsat artifacts unsatBranch auditDigest
              diagnostic)
            membership)))

theorem ay_arce_retained_fresh_hit_preserves_public_soundness
    (cachedReport freshEvidence publicReport satFact unsatFact noClaim :
      Prop) :
    AyARCERetainedHit cachedReport freshEvidence publicReport ->
    (cachedReport -> freshEvidence -> publicReport ->
      AyARCEPublicResult satFact unsatFact noClaim) ->
    AyARCEPublicResult satFact unsatFact noClaim :=
  fun hit sound =>
    sound
      (ay_arce_retained_hit_report cachedReport freshEvidence publicReport
        hit)
      (ay_arce_retained_hit_evidence cachedReport freshEvidence publicReport
        hit)
      (ay_arce_retained_hit_public cachedReport freshEvidence publicReport
        hit)

theorem ay_arce_retained_fresh_hit_preserves_sat_claim
    (cachedReport freshEvidence publicReport satFact : Prop) :
    AyARCERetainedHit cachedReport freshEvidence publicReport ->
    (freshEvidence -> publicReport -> satFact) ->
    satFact :=
  fun hit sound =>
    sound
      (ay_arce_retained_hit_evidence cachedReport freshEvidence publicReport
        hit)
      (ay_arce_retained_hit_public cachedReport freshEvidence publicReport
        hit)

theorem ay_arce_retained_fresh_hit_preserves_unsat_claim
    (cachedReport freshEvidence publicReport unsatFact : Prop) :
    AyARCERetainedHit cachedReport freshEvidence publicReport ->
    (freshEvidence -> publicReport -> unsatFact) ->
    unsatFact :=
  fun hit sound =>
    sound
      (ay_arce_retained_hit_evidence cachedReport freshEvidence publicReport
        hit)
      (ay_arce_retained_hit_public cachedReport freshEvidence publicReport
        hit)

theorem ay_arce_evicted_public_result_no_claim
    (satFact unsatFact evictionEpoch auditDigest diagnostic : Prop) :
    AyARCEEvictedEntry evictionEpoch auditDigest diagnostic ->
    AyARCEPublicResult satFact unsatFact
      (AyARCENoClaim evictionEpoch auditDigest diagnostic) :=
  fun evicted =>
    ay_arce_disj_right satFact
      (AyARCEDisj unsatFact
        (AyARCENoClaim evictionEpoch auditDigest diagnostic))
      (ay_arce_disj_right unsatFact
        (AyARCENoClaim evictionEpoch auditDigest diagnostic)
        (ay_arce_evicted_entry_no_claim evictionEpoch auditDigest
          diagnostic evicted))

theorem ay_arce_missing_public_result_no_claim
    (satFact unsatFact missReason auditDigest diagnostic : Prop) :
    AyARCEMissingEntry missReason auditDigest diagnostic ->
    AyARCEPublicResult satFact unsatFact
      (AyARCENoClaim missReason auditDigest diagnostic) :=
  fun missing =>
    ay_arce_disj_right satFact
      (AyARCEDisj unsatFact
        (AyARCENoClaim missReason auditDigest diagnostic))
      (ay_arce_disj_right unsatFact
        (AyARCENoClaim missReason auditDigest diagnostic)
        (ay_arce_missing_entry_no_claim missReason auditDigest diagnostic
          missing))

theorem ay_arce_stale_public_result_no_claim
    (satFact unsatFact staleEpoch staleDigest diagnostic : Prop) :
    AyARCEStaleReport staleEpoch staleDigest diagnostic ->
    AyARCEPublicResult satFact unsatFact
      (AyARCENoClaim staleEpoch staleDigest diagnostic) :=
  fun stale =>
    ay_arce_disj_right satFact
      (AyARCEDisj unsatFact
        (AyARCENoClaim staleEpoch staleDigest diagnostic))
      (ay_arce_disj_right unsatFact
        (AyARCENoClaim staleEpoch staleDigest diagnostic)
        (ay_arce_stale_report_no_claim staleEpoch staleDigest diagnostic
          stale))

theorem ay_arce_evicted_missing_or_stale_recompute
    (evictionEpoch missReason staleEpoch auditDigest diagnostic recompute :
      Prop) :
    AyARCEDisj evictionEpoch (AyARCEDisj missReason staleEpoch) ->
    auditDigest -> diagnostic ->
    (evictionEpoch ->
      AyARCERecomputeObligation evictionEpoch auditDigest diagnostic ->
      recompute) ->
    (missReason ->
      AyARCERecomputeObligation missReason auditDigest diagnostic ->
      recompute) ->
    (staleEpoch ->
      AyARCERecomputeObligation staleEpoch auditDigest diagnostic ->
      recompute) ->
    recompute :=
  fun failure auditProof diagnosticProof onEvicted onMissing onStale =>
    failure recompute
      (fun evictedProof =>
        onEvicted evictedProof
          (ay_arce_recompute_intro evictionEpoch auditDigest diagnostic
            evictedProof auditProof diagnosticProof))
      (fun tail =>
        tail recompute
          (fun missProof =>
            onMissing missProof
              (ay_arce_recompute_intro missReason auditDigest diagnostic
                missProof auditProof diagnosticProof))
          (fun staleProof =>
            onStale staleProof
              (ay_arce_recompute_intro staleEpoch auditDigest diagnostic
                staleProof auditProof diagnosticProof)))
