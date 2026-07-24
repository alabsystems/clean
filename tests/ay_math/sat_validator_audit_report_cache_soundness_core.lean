-- SAT-COMP validator audit report-cache soundness core.
--
-- Cached audit reports may be reused only when root, digest, and membership
-- evidence match the current validation context.  Missing or stale cache
-- entries are diagnostics/recompute obligations, not SAT/UNSAT claims.

def AyARCSConj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def AyARCSDisj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyARCSEquisat (before after : Prop) : Prop :=
  AyARCSConj (before -> after) (after -> before)

def AyARCSPublicResult (satFact unsatFact noClaim : Prop) : Prop :=
  AyARCSDisj satFact (AyARCSDisj unsatFact noClaim)

def AyARCSArtifacts (certId archiveKey : Prop) : Prop :=
  AyARCSConj certId archiveKey

def AyARCSEntry
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    Prop :=
  AyARCSConj exitCode
    (AyARCSConj artifacts
      (AyARCSConj checkerDecision
        (AyARCSConj auditDigest diagnostic)))

def AyARCSMembership (leafHash root entry : Prop) : Prop :=
  AyARCSConj leafHash (AyARCSConj root entry)

def AyARCSCachedReport (reportDigest cachedRoot cachedEntry : Prop) : Prop :=
  AyARCSConj reportDigest (AyARCSConj cachedRoot cachedEntry)

def AyARCSCacheEvidence
    (rootMatch digestMatch membershipEvidence : Prop) : Prop :=
  AyARCSConj rootMatch (AyARCSConj digestMatch membershipEvidence)

def AyARCSCacheHit (cachedReport cacheEvidence publicReport : Prop) : Prop :=
  AyARCSConj cachedReport (AyARCSConj cacheEvidence publicReport)

def AyARCSCacheMiss (missReason auditDigest diagnostic : Prop) : Prop :=
  AyARCSConj missReason (AyARCSConj auditDigest diagnostic)

def AyARCSStaleCache (staleRoot staleDigest diagnostic : Prop) : Prop :=
  AyARCSConj staleRoot (AyARCSConj staleDigest diagnostic)

def AyARCSRecomputeObligation
    (reason auditDigest diagnostic : Prop) : Prop :=
  AyARCSConj reason (AyARCSConj auditDigest diagnostic)

def AyARCSNoClaim (reason auditDigest diagnostic : Prop) : Prop :=
  AyARCSConj reason (AyARCSConj auditDigest diagnostic)

def AyARCSModel (formula assignment : Prop) : Prop :=
  AyARCSConj formula assignment

def AyARCSUnsat (formula : Prop) : Prop :=
  formula -> False

def AyARCSVisibleSAT (original visibleAssignment : Prop) : Prop :=
  AyARCSModel original visibleAssignment

def AyARCSPreprocessArtifact (original solver : Prop) : Prop :=
  AyARCSEquisat original solver

def AyARCSReplayAccepted (solver stream finalClause : Prop) : Prop :=
  stream -> solver -> finalClause

theorem ay_arcs_conj_intro (left right : Prop) :
    left -> right -> AyARCSConj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_arcs_conj_left (left right : Prop) :
    AyARCSConj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_arcs_conj_right (left right : Prop) :
    AyARCSConj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_arcs_disj_left (left right : Prop) :
    left -> AyARCSDisj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_arcs_disj_right (left right : Prop) :
    right -> AyARCSDisj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_arcs_equisat_forward (before after : Prop) :
    AyARCSEquisat before after -> before -> after :=
  fun witness hbefore =>
    witness after (fun forward _backward => forward hbefore)

theorem ay_arcs_equisat_backward (before after : Prop) :
    AyARCSEquisat before after -> after -> before :=
  fun witness hafter =>
    witness before (fun _forward backward => backward hafter)

theorem ay_arcs_model_intro (formula assignment : Prop) :
    formula -> assignment -> AyARCSModel formula assignment :=
  fun formulaProof assignmentProof =>
    ay_arcs_conj_intro formula assignment formulaProof assignmentProof

theorem ay_arcs_model_formula (formula assignment : Prop) :
    AyARCSModel formula assignment -> formula :=
  fun model => ay_arcs_conj_left formula assignment model

theorem ay_arcs_model_assignment (formula assignment : Prop) :
    AyARCSModel formula assignment -> assignment :=
  fun model => ay_arcs_conj_right formula assignment model

theorem ay_arcs_entry_intro
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    exitCode -> artifacts -> checkerDecision -> auditDigest -> diagnostic ->
    AyARCSEntry exitCode artifacts checkerDecision auditDigest diagnostic :=
  fun exitProof artifactsProof checkerProof auditProof diagnosticProof =>
    ay_arcs_conj_intro exitCode
      (AyARCSConj artifacts
        (AyARCSConj checkerDecision (AyARCSConj auditDigest diagnostic)))
      exitProof
      (ay_arcs_conj_intro artifacts
        (AyARCSConj checkerDecision (AyARCSConj auditDigest diagnostic))
        artifactsProof
        (ay_arcs_conj_intro checkerDecision
          (AyARCSConj auditDigest diagnostic)
          checkerProof
          (ay_arcs_conj_intro auditDigest diagnostic auditProof
            diagnosticProof)))

theorem ay_arcs_entry_checker
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    AyARCSEntry exitCode artifacts checkerDecision auditDigest diagnostic ->
    checkerDecision :=
  fun entry =>
    ay_arcs_conj_right exitCode
      (AyARCSConj artifacts
        (AyARCSConj checkerDecision (AyARCSConj auditDigest diagnostic)))
      entry checkerDecision
      (fun _artifactsProof tail =>
        tail checkerDecision (fun checkerProof _auditTail => checkerProof))

theorem ay_arcs_entry_audit
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    AyARCSEntry exitCode artifacts checkerDecision auditDigest diagnostic ->
    auditDigest :=
  fun entry =>
    ay_arcs_conj_right exitCode
      (AyARCSConj artifacts
        (AyARCSConj checkerDecision (AyARCSConj auditDigest diagnostic)))
      entry auditDigest
      (fun _artifactsProof tail =>
        tail auditDigest
          (fun _checkerProof auditTail =>
            auditTail auditDigest
              (fun auditProof _diagnosticProof => auditProof)))

theorem ay_arcs_membership_intro (leafHash root entry : Prop) :
    leafHash -> root -> entry -> AyARCSMembership leafHash root entry :=
  fun leafProof rootProof entryProof =>
    ay_arcs_conj_intro leafHash (AyARCSConj root entry)
      leafProof
      (ay_arcs_conj_intro root entry rootProof entryProof)

theorem ay_arcs_membership_root (leafHash root entry : Prop) :
    AyARCSMembership leafHash root entry -> root :=
  fun membership =>
    ay_arcs_conj_right leafHash (AyARCSConj root entry) membership
      root (fun rootProof _entryProof => rootProof)

theorem ay_arcs_membership_entry (leafHash root entry : Prop) :
    AyARCSMembership leafHash root entry -> entry :=
  fun membership =>
    ay_arcs_conj_right leafHash (AyARCSConj root entry) membership
      entry (fun _rootProof entryProof => entryProof)

theorem ay_arcs_cached_report_intro
    (reportDigest cachedRoot cachedEntry : Prop) :
    reportDigest -> cachedRoot -> cachedEntry ->
    AyARCSCachedReport reportDigest cachedRoot cachedEntry :=
  fun digestProof rootProof entryProof =>
    ay_arcs_conj_intro reportDigest
      (AyARCSConj cachedRoot cachedEntry)
      digestProof
      (ay_arcs_conj_intro cachedRoot cachedEntry rootProof entryProof)

theorem ay_arcs_cached_report_digest
    (reportDigest cachedRoot cachedEntry : Prop) :
    AyARCSCachedReport reportDigest cachedRoot cachedEntry ->
    reportDigest :=
  fun report =>
    ay_arcs_conj_left reportDigest
      (AyARCSConj cachedRoot cachedEntry) report

theorem ay_arcs_cached_report_root
    (reportDigest cachedRoot cachedEntry : Prop) :
    AyARCSCachedReport reportDigest cachedRoot cachedEntry -> cachedRoot :=
  fun report =>
    ay_arcs_conj_right reportDigest
      (AyARCSConj cachedRoot cachedEntry)
      report cachedRoot (fun rootProof _entryProof => rootProof)

theorem ay_arcs_cache_evidence_intro
    (rootMatch digestMatch membershipEvidence : Prop) :
    rootMatch -> digestMatch -> membershipEvidence ->
    AyARCSCacheEvidence rootMatch digestMatch membershipEvidence :=
  fun rootProof digestProof membershipProof =>
    ay_arcs_conj_intro rootMatch
      (AyARCSConj digestMatch membershipEvidence)
      rootProof
      (ay_arcs_conj_intro digestMatch membershipEvidence digestProof
        membershipProof)

theorem ay_arcs_cache_evidence_root
    (rootMatch digestMatch membershipEvidence : Prop) :
    AyARCSCacheEvidence rootMatch digestMatch membershipEvidence ->
    rootMatch :=
  fun evidence =>
    ay_arcs_conj_left rootMatch
      (AyARCSConj digestMatch membershipEvidence) evidence

theorem ay_arcs_cache_evidence_digest
    (rootMatch digestMatch membershipEvidence : Prop) :
    AyARCSCacheEvidence rootMatch digestMatch membershipEvidence ->
    digestMatch :=
  fun evidence =>
    ay_arcs_conj_right rootMatch
      (AyARCSConj digestMatch membershipEvidence)
      evidence digestMatch
      (fun digestProof _membershipProof => digestProof)

theorem ay_arcs_cache_evidence_membership
    (rootMatch digestMatch membershipEvidence : Prop) :
    AyARCSCacheEvidence rootMatch digestMatch membershipEvidence ->
    membershipEvidence :=
  fun evidence =>
    ay_arcs_conj_right rootMatch
      (AyARCSConj digestMatch membershipEvidence)
      evidence membershipEvidence
      (fun _digestProof membershipProof => membershipProof)

theorem ay_arcs_cache_hit_intro
    (cachedReport cacheEvidence publicReport : Prop) :
    cachedReport -> cacheEvidence -> publicReport ->
    AyARCSCacheHit cachedReport cacheEvidence publicReport :=
  fun reportProof evidenceProof publicProof =>
    ay_arcs_conj_intro cachedReport
      (AyARCSConj cacheEvidence publicReport)
      reportProof
      (ay_arcs_conj_intro cacheEvidence publicReport evidenceProof
        publicProof)

theorem ay_arcs_cache_hit_report
    (cachedReport cacheEvidence publicReport : Prop) :
    AyARCSCacheHit cachedReport cacheEvidence publicReport ->
    cachedReport :=
  fun hit =>
    ay_arcs_conj_left cachedReport
      (AyARCSConj cacheEvidence publicReport) hit

theorem ay_arcs_cache_hit_evidence
    (cachedReport cacheEvidence publicReport : Prop) :
    AyARCSCacheHit cachedReport cacheEvidence publicReport ->
    cacheEvidence :=
  fun hit =>
    ay_arcs_conj_right cachedReport
      (AyARCSConj cacheEvidence publicReport)
      hit cacheEvidence (fun evidenceProof _publicProof => evidenceProof)

theorem ay_arcs_cache_hit_public
    (cachedReport cacheEvidence publicReport : Prop) :
    AyARCSCacheHit cachedReport cacheEvidence publicReport ->
    publicReport :=
  fun hit =>
    ay_arcs_conj_right cachedReport
      (AyARCSConj cacheEvidence publicReport)
      hit publicReport (fun _evidenceProof publicProof => publicProof)

theorem ay_arcs_no_claim_intro
    (reason auditDigest diagnostic : Prop) :
    reason -> auditDigest -> diagnostic ->
    AyARCSNoClaim reason auditDigest diagnostic :=
  fun reasonProof auditProof diagnosticProof =>
    ay_arcs_conj_intro reason (AyARCSConj auditDigest diagnostic)
      reasonProof
      (ay_arcs_conj_intro auditDigest diagnostic auditProof
        diagnosticProof)

theorem ay_arcs_cache_miss_intro
    (missReason auditDigest diagnostic : Prop) :
    missReason -> auditDigest -> diagnostic ->
    AyARCSCacheMiss missReason auditDigest diagnostic :=
  fun missProof auditProof diagnosticProof =>
    ay_arcs_conj_intro missReason (AyARCSConj auditDigest diagnostic)
      missProof
      (ay_arcs_conj_intro auditDigest diagnostic auditProof
        diagnosticProof)

theorem ay_arcs_cache_miss_recompute_obligation
    (missReason auditDigest diagnostic : Prop) :
    AyARCSCacheMiss missReason auditDigest diagnostic ->
    AyARCSRecomputeObligation missReason auditDigest diagnostic :=
  fun miss =>
    ay_arcs_conj_intro missReason (AyARCSConj auditDigest diagnostic)
      (ay_arcs_conj_left missReason
        (AyARCSConj auditDigest diagnostic) miss)
      (ay_arcs_conj_right missReason
        (AyARCSConj auditDigest diagnostic) miss)

theorem ay_arcs_cache_miss_no_claim
    (missReason auditDigest diagnostic : Prop) :
    AyARCSCacheMiss missReason auditDigest diagnostic ->
    AyARCSNoClaim missReason auditDigest diagnostic :=
  fun miss =>
    ay_arcs_conj_intro missReason (AyARCSConj auditDigest diagnostic)
      (ay_arcs_conj_left missReason
        (AyARCSConj auditDigest diagnostic) miss)
      (ay_arcs_conj_right missReason
        (AyARCSConj auditDigest diagnostic) miss)

theorem ay_arcs_stale_cache_intro
    (staleRoot staleDigest diagnostic : Prop) :
    staleRoot -> staleDigest -> diagnostic ->
    AyARCSStaleCache staleRoot staleDigest diagnostic :=
  fun rootProof digestProof diagnosticProof =>
    ay_arcs_conj_intro staleRoot
      (AyARCSConj staleDigest diagnostic)
      rootProof
      (ay_arcs_conj_intro staleDigest diagnostic digestProof
        diagnosticProof)

theorem ay_arcs_stale_cache_no_claim
    (staleRoot staleDigest diagnostic : Prop) :
    AyARCSStaleCache staleRoot staleDigest diagnostic ->
    AyARCSNoClaim staleRoot staleDigest diagnostic :=
  fun stale =>
    ay_arcs_conj_intro staleRoot (AyARCSConj staleDigest diagnostic)
      (ay_arcs_conj_left staleRoot
        (AyARCSConj staleDigest diagnostic) stale)
      (ay_arcs_conj_right staleRoot
        (AyARCSConj staleDigest diagnostic) stale)

theorem ay_arcs_preprocess_model_reconstruct
    (original solver internalAssignment visibleAssignment : Prop) :
    AyARCSPreprocessArtifact original solver ->
    (internalAssignment -> visibleAssignment) ->
    AyARCSModel solver internalAssignment ->
    AyARCSVisibleSAT original visibleAssignment :=
  fun preprocess decode model =>
    ay_arcs_model_intro original visibleAssignment
      (ay_arcs_equisat_backward original solver preprocess
        (ay_arcs_model_formula solver internalAssignment model))
      (decode (ay_arcs_model_assignment solver internalAssignment model))

theorem ay_arcs_preprocess_unsat_reconstruct
    (original solver : Prop) :
    AyARCSPreprocessArtifact original solver ->
    AyARCSUnsat solver ->
    AyARCSUnsat original :=
  fun preprocess solverUnsat originalProof =>
    solverUnsat
      (ay_arcs_equisat_forward original solver preprocess originalProof)

theorem ay_arcs_replay_unsat_public
    (original solver stream finalClause : Prop) :
    AyARCSPreprocessArtifact original solver ->
    AyARCSReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    stream ->
    AyARCSUnsat original :=
  fun preprocess replay closeFinal streamProof originalProof =>
    closeFinal
      (replay streamProof
        (ay_arcs_equisat_forward original solver preprocess originalProof))

theorem ay_arcs_retained_sat_membership_sound
    (leafHash root acceptedSat artifacts satBranch auditDigest diagnostic
      original solver internalAssignment visibleAssignment : Prop) :
    AyARCSPreprocessArtifact original solver ->
    (internalAssignment -> visibleAssignment) ->
    (satBranch -> AyARCSModel solver internalAssignment) ->
    AyARCSMembership leafHash root
      (AyARCSEntry acceptedSat artifacts satBranch auditDigest diagnostic) ->
    AyARCSVisibleSAT original visibleAssignment :=
  fun preprocess decode accept membership =>
    ay_arcs_preprocess_model_reconstruct original solver internalAssignment
      visibleAssignment preprocess decode
      (accept
        (ay_arcs_entry_checker acceptedSat artifacts satBranch auditDigest
          diagnostic
          (ay_arcs_membership_entry leafHash root
            (AyARCSEntry acceptedSat artifacts satBranch auditDigest
              diagnostic)
            membership)))

theorem ay_arcs_retained_unsat_membership_sound
    (leafHash root acceptedUnsat artifacts unsatBranch auditDigest diagnostic
      original solver stream finalClause : Prop) :
    AyARCSPreprocessArtifact original solver ->
    AyARCSReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    (unsatBranch -> stream) ->
    AyARCSMembership leafHash root
      (AyARCSEntry acceptedUnsat artifacts unsatBranch auditDigest
        diagnostic) ->
    AyARCSUnsat original :=
  fun preprocess replay closeFinal accept membership =>
    ay_arcs_replay_unsat_public original solver stream finalClause preprocess
      replay closeFinal
      (accept
        (ay_arcs_entry_checker acceptedUnsat artifacts unsatBranch auditDigest
          diagnostic
          (ay_arcs_membership_entry leafHash root
            (AyARCSEntry acceptedUnsat artifacts unsatBranch auditDigest
              diagnostic)
            membership)))

theorem ay_arcs_cache_hit_requires_matching_evidence
    (cachedReport cacheEvidence publicReport rootMatch digestMatch
      membershipEvidence : Prop) :
    AyARCSCacheHit cachedReport
      (AyARCSCacheEvidence rootMatch digestMatch membershipEvidence)
      publicReport ->
    AyARCSConj rootMatch (AyARCSConj digestMatch membershipEvidence) :=
  fun hit =>
    ay_arcs_cache_hit_evidence cachedReport
      (AyARCSCacheEvidence rootMatch digestMatch membershipEvidence)
      publicReport hit

theorem ay_arcs_cache_hit_preserves_public_soundness
    (cachedReport cacheEvidence publicReport satFact unsatFact noClaim :
      Prop) :
    AyARCSCacheHit cachedReport cacheEvidence publicReport ->
    (cachedReport -> cacheEvidence -> publicReport ->
      AyARCSPublicResult satFact unsatFact noClaim) ->
    AyARCSPublicResult satFact unsatFact noClaim :=
  fun hit sound =>
    sound
      (ay_arcs_cache_hit_report cachedReport cacheEvidence publicReport hit)
      (ay_arcs_cache_hit_evidence cachedReport cacheEvidence publicReport
        hit)
      (ay_arcs_cache_hit_public cachedReport cacheEvidence publicReport hit)

theorem ay_arcs_cache_hit_preserves_sat_claim
    (cachedReport cacheEvidence publicReport satFact : Prop) :
    AyARCSCacheHit cachedReport cacheEvidence publicReport ->
    (cacheEvidence -> publicReport -> satFact) ->
    satFact :=
  fun hit sound =>
    sound
      (ay_arcs_cache_hit_evidence cachedReport cacheEvidence publicReport
        hit)
      (ay_arcs_cache_hit_public cachedReport cacheEvidence publicReport hit)

theorem ay_arcs_cache_hit_preserves_unsat_claim
    (cachedReport cacheEvidence publicReport unsatFact : Prop) :
    AyARCSCacheHit cachedReport cacheEvidence publicReport ->
    (cacheEvidence -> publicReport -> unsatFact) ->
    unsatFact :=
  fun hit sound =>
    sound
      (ay_arcs_cache_hit_evidence cachedReport cacheEvidence publicReport
        hit)
      (ay_arcs_cache_hit_public cachedReport cacheEvidence publicReport hit)

theorem ay_arcs_cache_miss_public_result_no_claim
    (satFact unsatFact missReason auditDigest diagnostic : Prop) :
    AyARCSCacheMiss missReason auditDigest diagnostic ->
    AyARCSPublicResult satFact unsatFact
      (AyARCSNoClaim missReason auditDigest diagnostic) :=
  fun miss =>
    ay_arcs_disj_right satFact
      (AyARCSDisj unsatFact
        (AyARCSNoClaim missReason auditDigest diagnostic))
      (ay_arcs_disj_right unsatFact
        (AyARCSNoClaim missReason auditDigest diagnostic)
        (ay_arcs_cache_miss_no_claim missReason auditDigest diagnostic
          miss))

theorem ay_arcs_stale_cache_public_result_no_claim
    (satFact unsatFact staleRoot staleDigest diagnostic : Prop) :
    AyARCSStaleCache staleRoot staleDigest diagnostic ->
    AyARCSPublicResult satFact unsatFact
      (AyARCSNoClaim staleRoot staleDigest diagnostic) :=
  fun stale =>
    ay_arcs_disj_right satFact
      (AyARCSDisj unsatFact
        (AyARCSNoClaim staleRoot staleDigest diagnostic))
      (ay_arcs_disj_right unsatFact
        (AyARCSNoClaim staleRoot staleDigest diagnostic)
        (ay_arcs_stale_cache_no_claim staleRoot staleDigest diagnostic
          stale))

theorem ay_arcs_stale_or_missing_cache_recompute
    (staleRoot missReason auditDigest diagnostic recompute : Prop) :
    AyARCSDisj staleRoot missReason ->
    auditDigest -> diagnostic ->
    (staleRoot ->
      AyARCSRecomputeObligation staleRoot auditDigest diagnostic ->
      recompute) ->
    (missReason ->
      AyARCSRecomputeObligation missReason auditDigest diagnostic ->
      recompute) ->
    recompute :=
  fun cacheFailure auditProof diagnosticProof onStale onMiss =>
    cacheFailure recompute
      (fun staleProof =>
        onStale staleProof
          (ay_arcs_conj_intro staleRoot
            (AyARCSConj auditDigest diagnostic)
            staleProof
            (ay_arcs_conj_intro auditDigest diagnostic auditProof
              diagnosticProof)))
      (fun missProof =>
        onMiss missProof
          (ay_arcs_conj_intro missReason
            (AyARCSConj auditDigest diagnostic)
            missProof
            (ay_arcs_conj_intro auditDigest diagnostic auditProof
              diagnosticProof)))
