-- SAT-COMP validator incremental result-cache replay soundness core.
--
-- Cached public SAT/UNSAT results can be reused only when the run manifest,
-- formula fingerprint, assumptions, artifact digest, checker replay, and
-- archive membership agree.  Stale or assumption-mismatched caches produce
-- no-claim recomputation obligations.

def AyVIRCConj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def AyVIRCDisj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyVIRCEquisat (before after : Prop) : Prop :=
  AyVIRCConj (before -> after) (after -> before)

def AyVIRCPublicResult (satFact unsatFact noClaim : Prop) : Prop :=
  AyVIRCDisj satFact (AyVIRCDisj unsatFact noClaim)

def AyVIRCCacheAgreement
    (runManifest formulaFingerprint assumptionsMatch artifactDigest
      checkerReplay archiveMembership : Prop) : Prop :=
  AyVIRCConj runManifest
    (AyVIRCConj formulaFingerprint
      (AyVIRCConj assumptionsMatch
        (AyVIRCConj artifactDigest
          (AyVIRCConj checkerReplay archiveMembership))))

def AyVIRCCachedResult
    (cacheKey publicLabel cachedArtifact cacheDigest : Prop) : Prop :=
  AyVIRCConj cacheKey
    (AyVIRCConj publicLabel
      (AyVIRCConj cachedArtifact cacheDigest))

def AyVIRCReplayBundle
    (cachedResult cacheAgreement replayTrace publicResult : Prop) :
    Prop :=
  AyVIRCConj cachedResult
    (AyVIRCConj cacheAgreement
      (AyVIRCConj replayTrace publicResult))

def AyVIRCEntry
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    Prop :=
  AyVIRCConj exitCode
    (AyVIRCConj artifacts
      (AyVIRCConj checkerDecision
        (AyVIRCConj auditDigest diagnostic)))

def AyVIRCMembership (leafHash root entry : Prop) : Prop :=
  AyVIRCConj leafHash (AyVIRCConj root entry)

def AyVIRCNoClaim (reason auditDigest diagnostic : Prop) : Prop :=
  AyVIRCConj reason (AyVIRCConj auditDigest diagnostic)

def AyVIRCRecomputeObligation
    (reason auditDigest diagnostic : Prop) : Prop :=
  AyVIRCConj reason (AyVIRCConj auditDigest diagnostic)

def AyVIRCModel (formula assignment : Prop) : Prop :=
  AyVIRCConj formula assignment

def AyVIRCUnsat (formula : Prop) : Prop :=
  formula -> False

def AyVIRCVisibleSAT (original visibleAssignment : Prop) : Prop :=
  AyVIRCModel original visibleAssignment

def AyVIRCPreprocessArtifact (original solver : Prop) : Prop :=
  AyVIRCEquisat original solver

def AyVIRCReplayAccepted (solver stream finalClause : Prop) : Prop :=
  stream -> solver -> finalClause

theorem ay_virc_conj_intro (left right : Prop) :
    left -> right -> AyVIRCConj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_virc_conj_left (left right : Prop) :
    AyVIRCConj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_virc_conj_right (left right : Prop) :
    AyVIRCConj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_virc_disj_right (left right : Prop) :
    right -> AyVIRCDisj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_virc_equisat_forward (before after : Prop) :
    AyVIRCEquisat before after -> before -> after :=
  fun witness hbefore =>
    witness after (fun forward _backward => forward hbefore)

theorem ay_virc_equisat_backward (before after : Prop) :
    AyVIRCEquisat before after -> after -> before :=
  fun witness hafter =>
    witness before (fun _forward backward => backward hafter)

theorem ay_virc_model_intro (formula assignment : Prop) :
    formula -> assignment -> AyVIRCModel formula assignment :=
  fun formulaProof assignmentProof =>
    ay_virc_conj_intro formula assignment formulaProof assignmentProof

theorem ay_virc_model_formula (formula assignment : Prop) :
    AyVIRCModel formula assignment -> formula :=
  fun model => ay_virc_conj_left formula assignment model

theorem ay_virc_model_assignment (formula assignment : Prop) :
    AyVIRCModel formula assignment -> assignment :=
  fun model => ay_virc_conj_right formula assignment model

theorem ay_virc_cache_agreement_intro
    (runManifest formulaFingerprint assumptionsMatch artifactDigest
      checkerReplay archiveMembership : Prop) :
    runManifest -> formulaFingerprint -> assumptionsMatch ->
    artifactDigest -> checkerReplay -> archiveMembership ->
    AyVIRCCacheAgreement runManifest formulaFingerprint assumptionsMatch
      artifactDigest checkerReplay archiveMembership :=
  fun manifestProof fingerprintProof assumptionsProof digestProof
      replayProof archiveProof =>
    ay_virc_conj_intro runManifest
      (AyVIRCConj formulaFingerprint
        (AyVIRCConj assumptionsMatch
          (AyVIRCConj artifactDigest
            (AyVIRCConj checkerReplay archiveMembership))))
      manifestProof
      (ay_virc_conj_intro formulaFingerprint
        (AyVIRCConj assumptionsMatch
          (AyVIRCConj artifactDigest
            (AyVIRCConj checkerReplay archiveMembership)))
        fingerprintProof
        (ay_virc_conj_intro assumptionsMatch
          (AyVIRCConj artifactDigest
            (AyVIRCConj checkerReplay archiveMembership))
          assumptionsProof
          (ay_virc_conj_intro artifactDigest
            (AyVIRCConj checkerReplay archiveMembership)
            digestProof
            (ay_virc_conj_intro checkerReplay archiveMembership
              replayProof archiveProof))))

theorem ay_virc_cache_agreement_assumptions
    (runManifest formulaFingerprint assumptionsMatch artifactDigest
      checkerReplay archiveMembership : Prop) :
    AyVIRCCacheAgreement runManifest formulaFingerprint assumptionsMatch
      artifactDigest checkerReplay archiveMembership ->
    assumptionsMatch :=
  fun agreement =>
    ay_virc_conj_right runManifest
      (AyVIRCConj formulaFingerprint
        (AyVIRCConj assumptionsMatch
          (AyVIRCConj artifactDigest
            (AyVIRCConj checkerReplay archiveMembership))))
      agreement assumptionsMatch
      (fun _fingerprintProof tail =>
        tail assumptionsMatch (fun assumptionsProof _tail2 =>
          assumptionsProof))

theorem ay_virc_cache_agreement_replay
    (runManifest formulaFingerprint assumptionsMatch artifactDigest
      checkerReplay archiveMembership : Prop) :
    AyVIRCCacheAgreement runManifest formulaFingerprint assumptionsMatch
      artifactDigest checkerReplay archiveMembership ->
    checkerReplay :=
  fun agreement =>
    ay_virc_conj_right runManifest
      (AyVIRCConj formulaFingerprint
        (AyVIRCConj assumptionsMatch
          (AyVIRCConj artifactDigest
            (AyVIRCConj checkerReplay archiveMembership))))
      agreement checkerReplay
      (fun _fingerprintProof tail =>
        tail checkerReplay
          (fun _assumptionsProof tail2 =>
            tail2 checkerReplay
              (fun _digestProof tail3 =>
                tail3 checkerReplay
                  (fun replayProof _archiveProof => replayProof))))

theorem ay_virc_cache_agreement_archive
    (runManifest formulaFingerprint assumptionsMatch artifactDigest
      checkerReplay archiveMembership : Prop) :
    AyVIRCCacheAgreement runManifest formulaFingerprint assumptionsMatch
      artifactDigest checkerReplay archiveMembership ->
    archiveMembership :=
  fun agreement =>
    ay_virc_conj_right runManifest
      (AyVIRCConj formulaFingerprint
        (AyVIRCConj assumptionsMatch
          (AyVIRCConj artifactDigest
            (AyVIRCConj checkerReplay archiveMembership))))
      agreement archiveMembership
      (fun _fingerprintProof tail =>
        tail archiveMembership
          (fun _assumptionsProof tail2 =>
            tail2 archiveMembership
              (fun _digestProof tail3 =>
                tail3 archiveMembership
                  (fun _replayProof archiveProof => archiveProof))))

theorem ay_virc_cached_result_intro
    (cacheKey publicLabel cachedArtifact cacheDigest : Prop) :
    cacheKey -> publicLabel -> cachedArtifact -> cacheDigest ->
    AyVIRCCachedResult cacheKey publicLabel cachedArtifact cacheDigest :=
  fun keyProof labelProof artifactProof digestProof =>
    ay_virc_conj_intro cacheKey
      (AyVIRCConj publicLabel
        (AyVIRCConj cachedArtifact cacheDigest))
      keyProof
      (ay_virc_conj_intro publicLabel
        (AyVIRCConj cachedArtifact cacheDigest)
        labelProof
        (ay_virc_conj_intro cachedArtifact cacheDigest artifactProof
          digestProof))

theorem ay_virc_replay_bundle_intro
    (cachedResult cacheAgreement replayTrace publicResult : Prop) :
    cachedResult -> cacheAgreement -> replayTrace -> publicResult ->
    AyVIRCReplayBundle cachedResult cacheAgreement replayTrace
      publicResult :=
  fun cachedProof agreementProof traceProof publicProof =>
    ay_virc_conj_intro cachedResult
      (AyVIRCConj cacheAgreement
        (AyVIRCConj replayTrace publicResult))
      cachedProof
      (ay_virc_conj_intro cacheAgreement
        (AyVIRCConj replayTrace publicResult)
        agreementProof
        (ay_virc_conj_intro replayTrace publicResult traceProof
          publicProof))

theorem ay_virc_replay_bundle_cached
    (cachedResult cacheAgreement replayTrace publicResult : Prop) :
    AyVIRCReplayBundle cachedResult cacheAgreement replayTrace
      publicResult ->
    cachedResult :=
  fun bundle =>
    ay_virc_conj_left cachedResult
      (AyVIRCConj cacheAgreement
        (AyVIRCConj replayTrace publicResult))
      bundle

theorem ay_virc_replay_bundle_agreement
    (cachedResult cacheAgreement replayTrace publicResult : Prop) :
    AyVIRCReplayBundle cachedResult cacheAgreement replayTrace
      publicResult ->
    cacheAgreement :=
  fun bundle =>
    ay_virc_conj_right cachedResult
      (AyVIRCConj cacheAgreement
        (AyVIRCConj replayTrace publicResult))
      bundle cacheAgreement (fun agreementProof _tail => agreementProof)

theorem ay_virc_replay_bundle_public
    (cachedResult cacheAgreement replayTrace publicResult : Prop) :
    AyVIRCReplayBundle cachedResult cacheAgreement replayTrace
      publicResult ->
    publicResult :=
  fun bundle =>
    ay_virc_conj_right cachedResult
      (AyVIRCConj cacheAgreement
        (AyVIRCConj replayTrace publicResult))
      bundle publicResult
      (fun _agreementProof tail =>
        tail publicResult (fun _traceProof publicProof => publicProof))

theorem ay_virc_entry_intro
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    exitCode -> artifacts -> checkerDecision -> auditDigest -> diagnostic ->
    AyVIRCEntry exitCode artifacts checkerDecision auditDigest diagnostic :=
  fun exitProof artifactsProof checkerProof auditProof diagnosticProof =>
    ay_virc_conj_intro exitCode
      (AyVIRCConj artifacts
        (AyVIRCConj checkerDecision (AyVIRCConj auditDigest diagnostic)))
      exitProof
      (ay_virc_conj_intro artifacts
        (AyVIRCConj checkerDecision (AyVIRCConj auditDigest diagnostic))
        artifactsProof
        (ay_virc_conj_intro checkerDecision
          (AyVIRCConj auditDigest diagnostic)
          checkerProof
          (ay_virc_conj_intro auditDigest diagnostic auditProof
            diagnosticProof)))

theorem ay_virc_entry_checker
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    AyVIRCEntry exitCode artifacts checkerDecision auditDigest diagnostic ->
    checkerDecision :=
  fun entry =>
    ay_virc_conj_right exitCode
      (AyVIRCConj artifacts
        (AyVIRCConj checkerDecision (AyVIRCConj auditDigest diagnostic)))
      entry checkerDecision
      (fun _artifactsProof tail =>
        tail checkerDecision (fun checkerProof _auditTail => checkerProof))

theorem ay_virc_membership_intro (leafHash root entry : Prop) :
    leafHash -> root -> entry -> AyVIRCMembership leafHash root entry :=
  fun leafProof rootProof entryProof =>
    ay_virc_conj_intro leafHash (AyVIRCConj root entry)
      leafProof
      (ay_virc_conj_intro root entry rootProof entryProof)

theorem ay_virc_membership_entry (leafHash root entry : Prop) :
    AyVIRCMembership leafHash root entry -> entry :=
  fun membership =>
    ay_virc_conj_right leafHash (AyVIRCConj root entry) membership
      entry (fun _rootProof entryProof => entryProof)

theorem ay_virc_no_claim_intro
    (reason auditDigest diagnostic : Prop) :
    reason -> auditDigest -> diagnostic ->
    AyVIRCNoClaim reason auditDigest diagnostic :=
  fun reasonProof auditProof diagnosticProof =>
    ay_virc_conj_intro reason (AyVIRCConj auditDigest diagnostic)
      reasonProof
      (ay_virc_conj_intro auditDigest diagnostic auditProof
        diagnosticProof)

theorem ay_virc_recompute_intro
    (reason auditDigest diagnostic : Prop) :
    reason -> auditDigest -> diagnostic ->
    AyVIRCRecomputeObligation reason auditDigest diagnostic :=
  ay_virc_no_claim_intro reason auditDigest diagnostic

theorem ay_virc_preprocess_model_reconstruct
    (original solver internalAssignment visibleAssignment : Prop) :
    AyVIRCPreprocessArtifact original solver ->
    (internalAssignment -> visibleAssignment) ->
    AyVIRCModel solver internalAssignment ->
    AyVIRCVisibleSAT original visibleAssignment :=
  fun preprocess decode model =>
    ay_virc_model_intro original visibleAssignment
      (ay_virc_equisat_backward original solver preprocess
        (ay_virc_model_formula solver internalAssignment model))
      (decode (ay_virc_model_assignment solver internalAssignment model))

theorem ay_virc_preprocess_unsat_reconstruct
    (original solver : Prop) :
    AyVIRCPreprocessArtifact original solver ->
    AyVIRCUnsat solver ->
    AyVIRCUnsat original :=
  fun preprocess solverUnsat originalProof =>
    solverUnsat
      (ay_virc_equisat_forward original solver preprocess originalProof)

theorem ay_virc_replay_unsat_public
    (original solver stream finalClause : Prop) :
    AyVIRCPreprocessArtifact original solver ->
    AyVIRCReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    stream ->
    AyVIRCUnsat original :=
  fun preprocess replay closeFinal streamProof originalProof =>
    closeFinal
      (replay streamProof
        (ay_virc_equisat_forward original solver preprocess originalProof))

theorem ay_virc_retained_sat_membership_sound
    (leafHash root acceptedSat artifacts satBranch auditDigest diagnostic
      original solver internalAssignment visibleAssignment : Prop) :
    AyVIRCPreprocessArtifact original solver ->
    (internalAssignment -> visibleAssignment) ->
    (satBranch -> AyVIRCModel solver internalAssignment) ->
    AyVIRCMembership leafHash root
      (AyVIRCEntry acceptedSat artifacts satBranch auditDigest diagnostic) ->
    AyVIRCVisibleSAT original visibleAssignment :=
  fun preprocess decode accept membership =>
    ay_virc_preprocess_model_reconstruct original solver internalAssignment
      visibleAssignment preprocess decode
      (accept
        (ay_virc_entry_checker acceptedSat artifacts satBranch auditDigest
          diagnostic
          (ay_virc_membership_entry leafHash root
            (AyVIRCEntry acceptedSat artifacts satBranch auditDigest
              diagnostic)
            membership)))

theorem ay_virc_retained_unsat_membership_sound
    (leafHash root acceptedUnsat artifacts unsatBranch auditDigest diagnostic
      original solver stream finalClause : Prop) :
    AyVIRCPreprocessArtifact original solver ->
    AyVIRCReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    (unsatBranch -> stream) ->
    AyVIRCMembership leafHash root
      (AyVIRCEntry acceptedUnsat artifacts unsatBranch auditDigest
        diagnostic) ->
    AyVIRCUnsat original :=
  fun preprocess replay closeFinal accept membership =>
    ay_virc_replay_unsat_public original solver stream finalClause preprocess
      replay closeFinal
      (accept
        (ay_virc_entry_checker acceptedUnsat artifacts unsatBranch
          auditDigest diagnostic
          (ay_virc_membership_entry leafHash root
            (AyVIRCEntry acceptedUnsat artifacts unsatBranch auditDigest
              diagnostic)
            membership)))

theorem ay_virc_cached_result_public_sound
    (cachedResult cacheAgreement replayTrace publicResult
      satFact unsatFact noClaim : Prop) :
    AyVIRCReplayBundle cachedResult cacheAgreement replayTrace
      publicResult ->
    (cachedResult -> cacheAgreement -> publicResult ->
      AyVIRCPublicResult satFact unsatFact noClaim) ->
    AyVIRCPublicResult satFact unsatFact noClaim :=
  fun bundle sound =>
    sound
      (ay_virc_replay_bundle_cached cachedResult cacheAgreement replayTrace
        publicResult bundle)
      (ay_virc_replay_bundle_agreement cachedResult cacheAgreement
        replayTrace publicResult bundle)
      (ay_virc_replay_bundle_public cachedResult cacheAgreement replayTrace
        publicResult bundle)

theorem ay_virc_cached_result_preserves_sat
    (cachedResult cacheAgreement replayTrace publicResult satFact : Prop) :
    AyVIRCReplayBundle cachedResult cacheAgreement replayTrace
      publicResult ->
    (cacheAgreement -> publicResult -> satFact) ->
    satFact :=
  fun bundle sound =>
    sound
      (ay_virc_replay_bundle_agreement cachedResult cacheAgreement
        replayTrace publicResult bundle)
      (ay_virc_replay_bundle_public cachedResult cacheAgreement replayTrace
        publicResult bundle)

theorem ay_virc_cached_result_preserves_unsat
    (cachedResult cacheAgreement replayTrace publicResult unsatFact : Prop) :
    AyVIRCReplayBundle cachedResult cacheAgreement replayTrace
      publicResult ->
    (cacheAgreement -> publicResult -> unsatFact) ->
    unsatFact :=
  fun bundle sound =>
    sound
      (ay_virc_replay_bundle_agreement cachedResult cacheAgreement
        replayTrace publicResult bundle)
      (ay_virc_replay_bundle_public cachedResult cacheAgreement replayTrace
        publicResult bundle)

theorem ay_virc_stale_cache_no_claim
    (staleCache auditDigest diagnostic : Prop) :
    staleCache -> auditDigest -> diagnostic ->
    AyVIRCNoClaim staleCache auditDigest diagnostic :=
  ay_virc_no_claim_intro staleCache auditDigest diagnostic

theorem ay_virc_assumption_mismatch_no_claim
    (assumptionMismatch auditDigest diagnostic : Prop) :
    assumptionMismatch -> auditDigest -> diagnostic ->
    AyVIRCNoClaim assumptionMismatch auditDigest diagnostic :=
  ay_virc_no_claim_intro assumptionMismatch auditDigest diagnostic

theorem ay_virc_failure_public_result_no_claim
    (satFact unsatFact reason auditDigest diagnostic : Prop) :
    AyVIRCNoClaim reason auditDigest diagnostic ->
    AyVIRCPublicResult satFact unsatFact
      (AyVIRCNoClaim reason auditDigest diagnostic) :=
  fun noClaim =>
    ay_virc_disj_right satFact
      (AyVIRCDisj unsatFact
        (AyVIRCNoClaim reason auditDigest diagnostic))
      (ay_virc_disj_right unsatFact
        (AyVIRCNoClaim reason auditDigest diagnostic)
        noClaim)

theorem ay_virc_stale_or_assumption_mismatch_recompute
    (staleCache assumptionMismatch auditDigest diagnostic recompute : Prop) :
    AyVIRCDisj staleCache assumptionMismatch ->
    auditDigest -> diagnostic ->
    (staleCache ->
      AyVIRCRecomputeObligation staleCache auditDigest diagnostic ->
      recompute) ->
    (assumptionMismatch ->
      AyVIRCRecomputeObligation assumptionMismatch auditDigest diagnostic ->
      recompute) ->
    recompute :=
  fun failure auditProof diagnosticProof onStale onAssumption =>
    failure recompute
      (fun staleProof =>
        onStale staleProof
          (ay_virc_recompute_intro staleCache auditDigest diagnostic
            staleProof auditProof diagnosticProof))
      (fun assumptionProof =>
        onAssumption assumptionProof
          (ay_virc_recompute_intro assumptionMismatch auditDigest diagnostic
            assumptionProof auditProof diagnosticProof))
