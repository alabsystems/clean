-- SAT-COMP validator assumption-delta result-cache soundness core.
--
-- Public results reused across assumption/cube deltas require matching base
-- formula, assumption frame, artifact digest, checker replay, archive
-- membership, and delta preprocessing chain.  Wrong-frame caches are
-- no-claim recomputation obligations.

def AyVADCConj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def AyVADCDisj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyVADCEquisat (before after : Prop) : Prop :=
  AyVADCConj (before -> after) (after -> before)

def AyVADCPublicResult (satFact unsatFact noClaim : Prop) : Prop :=
  AyVADCDisj satFact (AyVADCDisj unsatFact noClaim)

def AyVADCDeltaAgreement
    (baseFormula assumptionFrame artifactDigest checkerReplay
      archiveMembership deltaPreprocess : Prop) : Prop :=
  AyVADCConj baseFormula
    (AyVADCConj assumptionFrame
      (AyVADCConj artifactDigest
        (AyVADCConj checkerReplay
          (AyVADCConj archiveMembership deltaPreprocess))))

def AyVADCCachedDeltaResult
    (cacheKey deltaKey publicLabel cachedArtifact : Prop) : Prop :=
  AyVADCConj cacheKey
    (AyVADCConj deltaKey
      (AyVADCConj publicLabel cachedArtifact))

def AyVADCReplayBundle
    (cachedResult deltaAgreement replayTrace publicResult : Prop) :
    Prop :=
  AyVADCConj cachedResult
    (AyVADCConj deltaAgreement
      (AyVADCConj replayTrace publicResult))

def AyVADCEntry
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    Prop :=
  AyVADCConj exitCode
    (AyVADCConj artifacts
      (AyVADCConj checkerDecision
        (AyVADCConj auditDigest diagnostic)))

def AyVADCMembership (leafHash root entry : Prop) : Prop :=
  AyVADCConj leafHash (AyVADCConj root entry)

def AyVADCNoClaim (reason auditDigest diagnostic : Prop) : Prop :=
  AyVADCConj reason (AyVADCConj auditDigest diagnostic)

def AyVADCRecomputeObligation
    (reason auditDigest diagnostic : Prop) : Prop :=
  AyVADCConj reason (AyVADCConj auditDigest diagnostic)

def AyVADCModel (formula assignment : Prop) : Prop :=
  AyVADCConj formula assignment

def AyVADCUnsat (formula : Prop) : Prop :=
  formula -> False

def AyVADCVisibleSAT (original visibleAssignment : Prop) : Prop :=
  AyVADCModel original visibleAssignment

def AyVADCPreprocessArtifact (original solver : Prop) : Prop :=
  AyVADCEquisat original solver

def AyVADCReplayAccepted (solver stream finalClause : Prop) : Prop :=
  stream -> solver -> finalClause

theorem ay_vadc_conj_intro (left right : Prop) :
    left -> right -> AyVADCConj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_vadc_conj_left (left right : Prop) :
    AyVADCConj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_vadc_conj_right (left right : Prop) :
    AyVADCConj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_vadc_disj_right (left right : Prop) :
    right -> AyVADCDisj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_vadc_equisat_forward (before after : Prop) :
    AyVADCEquisat before after -> before -> after :=
  fun witness hbefore =>
    witness after (fun forward _backward => forward hbefore)

theorem ay_vadc_equisat_backward (before after : Prop) :
    AyVADCEquisat before after -> after -> before :=
  fun witness hafter =>
    witness before (fun _forward backward => backward hafter)

theorem ay_vadc_model_intro (formula assignment : Prop) :
    formula -> assignment -> AyVADCModel formula assignment :=
  fun formulaProof assignmentProof =>
    ay_vadc_conj_intro formula assignment formulaProof assignmentProof

theorem ay_vadc_model_formula (formula assignment : Prop) :
    AyVADCModel formula assignment -> formula :=
  fun model => ay_vadc_conj_left formula assignment model

theorem ay_vadc_model_assignment (formula assignment : Prop) :
    AyVADCModel formula assignment -> assignment :=
  fun model => ay_vadc_conj_right formula assignment model

theorem ay_vadc_delta_agreement_intro
    (baseFormula assumptionFrame artifactDigest checkerReplay
      archiveMembership deltaPreprocess : Prop) :
    baseFormula -> assumptionFrame -> artifactDigest -> checkerReplay ->
    archiveMembership -> deltaPreprocess ->
    AyVADCDeltaAgreement baseFormula assumptionFrame artifactDigest
      checkerReplay archiveMembership deltaPreprocess :=
  fun baseProof frameProof digestProof replayProof archiveProof
      preprocessProof =>
    ay_vadc_conj_intro baseFormula
      (AyVADCConj assumptionFrame
        (AyVADCConj artifactDigest
          (AyVADCConj checkerReplay
            (AyVADCConj archiveMembership deltaPreprocess))))
      baseProof
      (ay_vadc_conj_intro assumptionFrame
        (AyVADCConj artifactDigest
          (AyVADCConj checkerReplay
            (AyVADCConj archiveMembership deltaPreprocess)))
        frameProof
        (ay_vadc_conj_intro artifactDigest
          (AyVADCConj checkerReplay
            (AyVADCConj archiveMembership deltaPreprocess))
          digestProof
          (ay_vadc_conj_intro checkerReplay
            (AyVADCConj archiveMembership deltaPreprocess)
            replayProof
            (ay_vadc_conj_intro archiveMembership deltaPreprocess
              archiveProof preprocessProof))))

theorem ay_vadc_delta_agreement_frame
    (baseFormula assumptionFrame artifactDigest checkerReplay
      archiveMembership deltaPreprocess : Prop) :
    AyVADCDeltaAgreement baseFormula assumptionFrame artifactDigest
      checkerReplay archiveMembership deltaPreprocess ->
    assumptionFrame :=
  fun agreement =>
    ay_vadc_conj_right baseFormula
      (AyVADCConj assumptionFrame
        (AyVADCConj artifactDigest
          (AyVADCConj checkerReplay
            (AyVADCConj archiveMembership deltaPreprocess))))
      agreement assumptionFrame (fun frameProof _tail => frameProof)

theorem ay_vadc_delta_agreement_replay
    (baseFormula assumptionFrame artifactDigest checkerReplay
      archiveMembership deltaPreprocess : Prop) :
    AyVADCDeltaAgreement baseFormula assumptionFrame artifactDigest
      checkerReplay archiveMembership deltaPreprocess ->
    checkerReplay :=
  fun agreement =>
    ay_vadc_conj_right baseFormula
      (AyVADCConj assumptionFrame
        (AyVADCConj artifactDigest
          (AyVADCConj checkerReplay
            (AyVADCConj archiveMembership deltaPreprocess))))
      agreement checkerReplay
      (fun _frameProof tail =>
        tail checkerReplay
          (fun _digestProof tail2 =>
            tail2 checkerReplay
              (fun replayProof _tail3 => replayProof)))

theorem ay_vadc_delta_agreement_preprocess
    (baseFormula assumptionFrame artifactDigest checkerReplay
      archiveMembership deltaPreprocess : Prop) :
    AyVADCDeltaAgreement baseFormula assumptionFrame artifactDigest
      checkerReplay archiveMembership deltaPreprocess ->
    deltaPreprocess :=
  fun agreement =>
    ay_vadc_conj_right baseFormula
      (AyVADCConj assumptionFrame
        (AyVADCConj artifactDigest
          (AyVADCConj checkerReplay
            (AyVADCConj archiveMembership deltaPreprocess))))
      agreement deltaPreprocess
      (fun _frameProof tail =>
        tail deltaPreprocess
          (fun _digestProof tail2 =>
            tail2 deltaPreprocess
              (fun _replayProof tail3 =>
                tail3 deltaPreprocess
                  (fun _archiveProof preprocessProof =>
                    preprocessProof))))

theorem ay_vadc_cached_delta_result_intro
    (cacheKey deltaKey publicLabel cachedArtifact : Prop) :
    cacheKey -> deltaKey -> publicLabel -> cachedArtifact ->
    AyVADCCachedDeltaResult cacheKey deltaKey publicLabel cachedArtifact :=
  fun cacheProof deltaProof labelProof artifactProof =>
    ay_vadc_conj_intro cacheKey
      (AyVADCConj deltaKey (AyVADCConj publicLabel cachedArtifact))
      cacheProof
      (ay_vadc_conj_intro deltaKey
        (AyVADCConj publicLabel cachedArtifact)
        deltaProof
        (ay_vadc_conj_intro publicLabel cachedArtifact labelProof
          artifactProof))

theorem ay_vadc_replay_bundle_intro
    (cachedResult deltaAgreement replayTrace publicResult : Prop) :
    cachedResult -> deltaAgreement -> replayTrace -> publicResult ->
    AyVADCReplayBundle cachedResult deltaAgreement replayTrace
      publicResult :=
  fun cachedProof agreementProof traceProof publicProof =>
    ay_vadc_conj_intro cachedResult
      (AyVADCConj deltaAgreement
        (AyVADCConj replayTrace publicResult))
      cachedProof
      (ay_vadc_conj_intro deltaAgreement
        (AyVADCConj replayTrace publicResult)
        agreementProof
        (ay_vadc_conj_intro replayTrace publicResult traceProof
          publicProof))

theorem ay_vadc_replay_bundle_cached
    (cachedResult deltaAgreement replayTrace publicResult : Prop) :
    AyVADCReplayBundle cachedResult deltaAgreement replayTrace
      publicResult ->
    cachedResult :=
  fun bundle =>
    ay_vadc_conj_left cachedResult
      (AyVADCConj deltaAgreement
        (AyVADCConj replayTrace publicResult))
      bundle

theorem ay_vadc_replay_bundle_agreement
    (cachedResult deltaAgreement replayTrace publicResult : Prop) :
    AyVADCReplayBundle cachedResult deltaAgreement replayTrace
      publicResult ->
    deltaAgreement :=
  fun bundle =>
    ay_vadc_conj_right cachedResult
      (AyVADCConj deltaAgreement
        (AyVADCConj replayTrace publicResult))
      bundle deltaAgreement (fun agreementProof _tail => agreementProof)

theorem ay_vadc_replay_bundle_public
    (cachedResult deltaAgreement replayTrace publicResult : Prop) :
    AyVADCReplayBundle cachedResult deltaAgreement replayTrace
      publicResult ->
    publicResult :=
  fun bundle =>
    ay_vadc_conj_right cachedResult
      (AyVADCConj deltaAgreement
        (AyVADCConj replayTrace publicResult))
      bundle publicResult
      (fun _agreementProof tail =>
        tail publicResult (fun _traceProof publicProof => publicProof))

theorem ay_vadc_entry_intro
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    exitCode -> artifacts -> checkerDecision -> auditDigest -> diagnostic ->
    AyVADCEntry exitCode artifacts checkerDecision auditDigest diagnostic :=
  fun exitProof artifactsProof checkerProof auditProof diagnosticProof =>
    ay_vadc_conj_intro exitCode
      (AyVADCConj artifacts
        (AyVADCConj checkerDecision (AyVADCConj auditDigest diagnostic)))
      exitProof
      (ay_vadc_conj_intro artifacts
        (AyVADCConj checkerDecision (AyVADCConj auditDigest diagnostic))
        artifactsProof
        (ay_vadc_conj_intro checkerDecision
          (AyVADCConj auditDigest diagnostic)
          checkerProof
          (ay_vadc_conj_intro auditDigest diagnostic auditProof
            diagnosticProof)))

theorem ay_vadc_entry_checker
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    AyVADCEntry exitCode artifacts checkerDecision auditDigest diagnostic ->
    checkerDecision :=
  fun entry =>
    ay_vadc_conj_right exitCode
      (AyVADCConj artifacts
        (AyVADCConj checkerDecision (AyVADCConj auditDigest diagnostic)))
      entry checkerDecision
      (fun _artifactsProof tail =>
        tail checkerDecision (fun checkerProof _auditTail => checkerProof))

theorem ay_vadc_membership_intro (leafHash root entry : Prop) :
    leafHash -> root -> entry -> AyVADCMembership leafHash root entry :=
  fun leafProof rootProof entryProof =>
    ay_vadc_conj_intro leafHash (AyVADCConj root entry)
      leafProof
      (ay_vadc_conj_intro root entry rootProof entryProof)

theorem ay_vadc_membership_entry (leafHash root entry : Prop) :
    AyVADCMembership leafHash root entry -> entry :=
  fun membership =>
    ay_vadc_conj_right leafHash (AyVADCConj root entry) membership
      entry (fun _rootProof entryProof => entryProof)

theorem ay_vadc_no_claim_intro
    (reason auditDigest diagnostic : Prop) :
    reason -> auditDigest -> diagnostic ->
    AyVADCNoClaim reason auditDigest diagnostic :=
  fun reasonProof auditProof diagnosticProof =>
    ay_vadc_conj_intro reason (AyVADCConj auditDigest diagnostic)
      reasonProof
      (ay_vadc_conj_intro auditDigest diagnostic auditProof
        diagnosticProof)

theorem ay_vadc_recompute_intro
    (reason auditDigest diagnostic : Prop) :
    reason -> auditDigest -> diagnostic ->
    AyVADCRecomputeObligation reason auditDigest diagnostic :=
  ay_vadc_no_claim_intro reason auditDigest diagnostic

theorem ay_vadc_preprocess_model_reconstruct
    (original solver internalAssignment visibleAssignment : Prop) :
    AyVADCPreprocessArtifact original solver ->
    (internalAssignment -> visibleAssignment) ->
    AyVADCModel solver internalAssignment ->
    AyVADCVisibleSAT original visibleAssignment :=
  fun preprocess decode model =>
    ay_vadc_model_intro original visibleAssignment
      (ay_vadc_equisat_backward original solver preprocess
        (ay_vadc_model_formula solver internalAssignment model))
      (decode (ay_vadc_model_assignment solver internalAssignment model))

theorem ay_vadc_preprocess_unsat_reconstruct
    (original solver : Prop) :
    AyVADCPreprocessArtifact original solver ->
    AyVADCUnsat solver ->
    AyVADCUnsat original :=
  fun preprocess solverUnsat originalProof =>
    solverUnsat
      (ay_vadc_equisat_forward original solver preprocess originalProof)

theorem ay_vadc_replay_unsat_public
    (original solver stream finalClause : Prop) :
    AyVADCPreprocessArtifact original solver ->
    AyVADCReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    stream ->
    AyVADCUnsat original :=
  fun preprocess replay closeFinal streamProof originalProof =>
    closeFinal
      (replay streamProof
        (ay_vadc_equisat_forward original solver preprocess originalProof))

theorem ay_vadc_retained_sat_membership_sound
    (leafHash root acceptedSat artifacts satBranch auditDigest diagnostic
      original solver internalAssignment visibleAssignment : Prop) :
    AyVADCPreprocessArtifact original solver ->
    (internalAssignment -> visibleAssignment) ->
    (satBranch -> AyVADCModel solver internalAssignment) ->
    AyVADCMembership leafHash root
      (AyVADCEntry acceptedSat artifacts satBranch auditDigest diagnostic) ->
    AyVADCVisibleSAT original visibleAssignment :=
  fun preprocess decode accept membership =>
    ay_vadc_preprocess_model_reconstruct original solver internalAssignment
      visibleAssignment preprocess decode
      (accept
        (ay_vadc_entry_checker acceptedSat artifacts satBranch auditDigest
          diagnostic
          (ay_vadc_membership_entry leafHash root
            (AyVADCEntry acceptedSat artifacts satBranch auditDigest
              diagnostic)
            membership)))

theorem ay_vadc_retained_unsat_membership_sound
    (leafHash root acceptedUnsat artifacts unsatBranch auditDigest diagnostic
      original solver stream finalClause : Prop) :
    AyVADCPreprocessArtifact original solver ->
    AyVADCReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    (unsatBranch -> stream) ->
    AyVADCMembership leafHash root
      (AyVADCEntry acceptedUnsat artifacts unsatBranch auditDigest
        diagnostic) ->
    AyVADCUnsat original :=
  fun preprocess replay closeFinal accept membership =>
    ay_vadc_replay_unsat_public original solver stream finalClause preprocess
      replay closeFinal
      (accept
        (ay_vadc_entry_checker acceptedUnsat artifacts unsatBranch
          auditDigest diagnostic
          (ay_vadc_membership_entry leafHash root
            (AyVADCEntry acceptedUnsat artifacts unsatBranch auditDigest
              diagnostic)
            membership)))

theorem ay_vadc_cached_delta_public_sound
    (cachedResult deltaAgreement replayTrace publicResult
      satFact unsatFact noClaim : Prop) :
    AyVADCReplayBundle cachedResult deltaAgreement replayTrace
      publicResult ->
    (cachedResult -> deltaAgreement -> publicResult ->
      AyVADCPublicResult satFact unsatFact noClaim) ->
    AyVADCPublicResult satFact unsatFact noClaim :=
  fun bundle sound =>
    sound
      (ay_vadc_replay_bundle_cached cachedResult deltaAgreement replayTrace
        publicResult bundle)
      (ay_vadc_replay_bundle_agreement cachedResult deltaAgreement
        replayTrace publicResult bundle)
      (ay_vadc_replay_bundle_public cachedResult deltaAgreement replayTrace
        publicResult bundle)

theorem ay_vadc_cached_delta_preserves_sat
    (cachedResult deltaAgreement replayTrace publicResult satFact : Prop) :
    AyVADCReplayBundle cachedResult deltaAgreement replayTrace
      publicResult ->
    (deltaAgreement -> publicResult -> satFact) ->
    satFact :=
  fun bundle sound =>
    sound
      (ay_vadc_replay_bundle_agreement cachedResult deltaAgreement
        replayTrace publicResult bundle)
      (ay_vadc_replay_bundle_public cachedResult deltaAgreement replayTrace
        publicResult bundle)

theorem ay_vadc_cached_delta_preserves_unsat
    (cachedResult deltaAgreement replayTrace publicResult unsatFact : Prop) :
    AyVADCReplayBundle cachedResult deltaAgreement replayTrace
      publicResult ->
    (deltaAgreement -> publicResult -> unsatFact) ->
    unsatFact :=
  fun bundle sound =>
    sound
      (ay_vadc_replay_bundle_agreement cachedResult deltaAgreement
        replayTrace publicResult bundle)
      (ay_vadc_replay_bundle_public cachedResult deltaAgreement replayTrace
        publicResult bundle)

theorem ay_vadc_wrong_frame_no_claim
    (wrongFrame auditDigest diagnostic : Prop) :
    wrongFrame -> auditDigest -> diagnostic ->
    AyVADCNoClaim wrongFrame auditDigest diagnostic :=
  ay_vadc_no_claim_intro wrongFrame auditDigest diagnostic

theorem ay_vadc_stale_delta_cache_no_claim
    (staleDeltaCache auditDigest diagnostic : Prop) :
    staleDeltaCache -> auditDigest -> diagnostic ->
    AyVADCNoClaim staleDeltaCache auditDigest diagnostic :=
  ay_vadc_no_claim_intro staleDeltaCache auditDigest diagnostic

theorem ay_vadc_failure_public_result_no_claim
    (satFact unsatFact reason auditDigest diagnostic : Prop) :
    AyVADCNoClaim reason auditDigest diagnostic ->
    AyVADCPublicResult satFact unsatFact
      (AyVADCNoClaim reason auditDigest diagnostic) :=
  fun noClaim =>
    ay_vadc_disj_right satFact
      (AyVADCDisj unsatFact
        (AyVADCNoClaim reason auditDigest diagnostic))
      (ay_vadc_disj_right unsatFact
        (AyVADCNoClaim reason auditDigest diagnostic)
        noClaim)

theorem ay_vadc_wrong_frame_or_stale_recompute
    (wrongFrame staleDeltaCache auditDigest diagnostic recompute : Prop) :
    AyVADCDisj wrongFrame staleDeltaCache ->
    auditDigest -> diagnostic ->
    (wrongFrame ->
      AyVADCRecomputeObligation wrongFrame auditDigest diagnostic ->
      recompute) ->
    (staleDeltaCache ->
      AyVADCRecomputeObligation staleDeltaCache auditDigest diagnostic ->
      recompute) ->
    recompute :=
  fun failure auditProof diagnosticProof onWrong onStale =>
    failure recompute
      (fun wrongProof =>
        onWrong wrongProof
          (ay_vadc_recompute_intro wrongFrame auditDigest diagnostic
            wrongProof auditProof diagnosticProof))
      (fun staleProof =>
        onStale staleProof
          (ay_vadc_recompute_intro staleDeltaCache auditDigest diagnostic
            staleProof auditProof diagnosticProof))
