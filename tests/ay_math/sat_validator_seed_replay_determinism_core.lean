-- SAT-COMP deterministic seed/replay validator soundness core.
--
-- A sequential-main run may be replayed for public validation only when seed,
-- configuration, formula fingerprint, preprocessing chain, and emitted checker
-- trace agree.  Divergent replay or stale seed/config artifacts produce
-- no-claim recomputation obligations.

def AyVSRDConj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def AyVSRDDisj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyVSRDEquisat (before after : Prop) : Prop :=
  AyVSRDConj (before -> after) (after -> before)

def AyVSRDPublicResult (satFact unsatFact noClaim : Prop) : Prop :=
  AyVSRDDisj satFact (AyVSRDDisj unsatFact noClaim)

def AyVSRDReplayAgreement
    (seedMatch configMatch fingerprintMatch preprocessMatch traceMatch :
      Prop) : Prop :=
  AyVSRDConj seedMatch
    (AyVSRDConj configMatch
      (AyVSRDConj fingerprintMatch
        (AyVSRDConj preprocessMatch traceMatch)))

def AyVSRDReplayBundle
    (originalRun replayRun replayAgreement checkerTrace : Prop) : Prop :=
  AyVSRDConj originalRun
    (AyVSRDConj replayRun
      (AyVSRDConj replayAgreement checkerTrace))

def AyVSRDEntry
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    Prop :=
  AyVSRDConj exitCode
    (AyVSRDConj artifacts
      (AyVSRDConj checkerDecision
        (AyVSRDConj auditDigest diagnostic)))

def AyVSRDMembership (leafHash root entry : Prop) : Prop :=
  AyVSRDConj leafHash (AyVSRDConj root entry)

def AyVSRDNoClaim (reason auditDigest diagnostic : Prop) : Prop :=
  AyVSRDConj reason (AyVSRDConj auditDigest diagnostic)

def AyVSRDRecomputeObligation
    (reason auditDigest diagnostic : Prop) : Prop :=
  AyVSRDConj reason (AyVSRDConj auditDigest diagnostic)

def AyVSRDModel (formula assignment : Prop) : Prop :=
  AyVSRDConj formula assignment

def AyVSRDUnsat (formula : Prop) : Prop :=
  formula -> False

def AyVSRDVisibleSAT (original visibleAssignment : Prop) : Prop :=
  AyVSRDModel original visibleAssignment

def AyVSRDPreprocessArtifact (original solver : Prop) : Prop :=
  AyVSRDEquisat original solver

def AyVSRDReplayAccepted (solver stream finalClause : Prop) : Prop :=
  stream -> solver -> finalClause

theorem ay_vsrd_conj_intro (left right : Prop) :
    left -> right -> AyVSRDConj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_vsrd_conj_left (left right : Prop) :
    AyVSRDConj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_vsrd_conj_right (left right : Prop) :
    AyVSRDConj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_vsrd_disj_right (left right : Prop) :
    right -> AyVSRDDisj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_vsrd_equisat_forward (before after : Prop) :
    AyVSRDEquisat before after -> before -> after :=
  fun witness hbefore =>
    witness after (fun forward _backward => forward hbefore)

theorem ay_vsrd_equisat_backward (before after : Prop) :
    AyVSRDEquisat before after -> after -> before :=
  fun witness hafter =>
    witness before (fun _forward backward => backward hafter)

theorem ay_vsrd_model_intro (formula assignment : Prop) :
    formula -> assignment -> AyVSRDModel formula assignment :=
  fun formulaProof assignmentProof =>
    ay_vsrd_conj_intro formula assignment formulaProof assignmentProof

theorem ay_vsrd_model_formula (formula assignment : Prop) :
    AyVSRDModel formula assignment -> formula :=
  fun model => ay_vsrd_conj_left formula assignment model

theorem ay_vsrd_model_assignment (formula assignment : Prop) :
    AyVSRDModel formula assignment -> assignment :=
  fun model => ay_vsrd_conj_right formula assignment model

theorem ay_vsrd_replay_agreement_intro
    (seedMatch configMatch fingerprintMatch preprocessMatch traceMatch :
      Prop) :
    seedMatch -> configMatch -> fingerprintMatch -> preprocessMatch ->
    traceMatch ->
    AyVSRDReplayAgreement seedMatch configMatch fingerprintMatch
      preprocessMatch traceMatch :=
  fun seedProof configProof fingerprintProof preprocessProof traceProof =>
    ay_vsrd_conj_intro seedMatch
      (AyVSRDConj configMatch
        (AyVSRDConj fingerprintMatch
          (AyVSRDConj preprocessMatch traceMatch)))
      seedProof
      (ay_vsrd_conj_intro configMatch
        (AyVSRDConj fingerprintMatch
          (AyVSRDConj preprocessMatch traceMatch))
        configProof
        (ay_vsrd_conj_intro fingerprintMatch
          (AyVSRDConj preprocessMatch traceMatch)
          fingerprintProof
          (ay_vsrd_conj_intro preprocessMatch traceMatch preprocessProof
            traceProof)))

theorem ay_vsrd_replay_agreement_seed
    (seedMatch configMatch fingerprintMatch preprocessMatch traceMatch :
      Prop) :
    AyVSRDReplayAgreement seedMatch configMatch fingerprintMatch
      preprocessMatch traceMatch ->
    seedMatch :=
  fun agreement =>
    ay_vsrd_conj_left seedMatch
      (AyVSRDConj configMatch
        (AyVSRDConj fingerprintMatch
          (AyVSRDConj preprocessMatch traceMatch)))
      agreement

theorem ay_vsrd_replay_agreement_trace
    (seedMatch configMatch fingerprintMatch preprocessMatch traceMatch :
      Prop) :
    AyVSRDReplayAgreement seedMatch configMatch fingerprintMatch
      preprocessMatch traceMatch ->
    traceMatch :=
  fun agreement =>
    ay_vsrd_conj_right seedMatch
      (AyVSRDConj configMatch
        (AyVSRDConj fingerprintMatch
          (AyVSRDConj preprocessMatch traceMatch)))
      agreement traceMatch
      (fun _configProof tail =>
        tail traceMatch
          (fun _fingerprintProof tail2 =>
            tail2 traceMatch
              (fun _preprocessProof traceProof => traceProof)))

theorem ay_vsrd_replay_bundle_intro
    (originalRun replayRun replayAgreement checkerTrace : Prop) :
    originalRun -> replayRun -> replayAgreement -> checkerTrace ->
    AyVSRDReplayBundle originalRun replayRun replayAgreement checkerTrace :=
  fun originalProof replayProof agreementProof traceProof =>
    ay_vsrd_conj_intro originalRun
      (AyVSRDConj replayRun
        (AyVSRDConj replayAgreement checkerTrace))
      originalProof
      (ay_vsrd_conj_intro replayRun
        (AyVSRDConj replayAgreement checkerTrace)
        replayProof
        (ay_vsrd_conj_intro replayAgreement checkerTrace agreementProof
          traceProof))

theorem ay_vsrd_replay_bundle_original
    (originalRun replayRun replayAgreement checkerTrace : Prop) :
    AyVSRDReplayBundle originalRun replayRun replayAgreement checkerTrace ->
    originalRun :=
  fun bundle =>
    ay_vsrd_conj_left originalRun
      (AyVSRDConj replayRun
        (AyVSRDConj replayAgreement checkerTrace))
      bundle

theorem ay_vsrd_replay_bundle_agreement
    (originalRun replayRun replayAgreement checkerTrace : Prop) :
    AyVSRDReplayBundle originalRun replayRun replayAgreement checkerTrace ->
    replayAgreement :=
  fun bundle =>
    ay_vsrd_conj_right originalRun
      (AyVSRDConj replayRun
        (AyVSRDConj replayAgreement checkerTrace))
      bundle replayAgreement
      (fun _replayProof tail =>
        tail replayAgreement (fun agreementProof _traceProof =>
          agreementProof))

theorem ay_vsrd_replay_bundle_trace
    (originalRun replayRun replayAgreement checkerTrace : Prop) :
    AyVSRDReplayBundle originalRun replayRun replayAgreement checkerTrace ->
    checkerTrace :=
  fun bundle =>
    ay_vsrd_conj_right originalRun
      (AyVSRDConj replayRun
        (AyVSRDConj replayAgreement checkerTrace))
      bundle checkerTrace
      (fun _replayProof tail =>
        tail checkerTrace (fun _agreementProof traceProof => traceProof))

theorem ay_vsrd_entry_intro
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    exitCode -> artifacts -> checkerDecision -> auditDigest -> diagnostic ->
    AyVSRDEntry exitCode artifacts checkerDecision auditDigest diagnostic :=
  fun exitProof artifactsProof checkerProof auditProof diagnosticProof =>
    ay_vsrd_conj_intro exitCode
      (AyVSRDConj artifacts
        (AyVSRDConj checkerDecision (AyVSRDConj auditDigest diagnostic)))
      exitProof
      (ay_vsrd_conj_intro artifacts
        (AyVSRDConj checkerDecision (AyVSRDConj auditDigest diagnostic))
        artifactsProof
        (ay_vsrd_conj_intro checkerDecision
          (AyVSRDConj auditDigest diagnostic)
          checkerProof
          (ay_vsrd_conj_intro auditDigest diagnostic auditProof
            diagnosticProof)))

theorem ay_vsrd_entry_checker
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    AyVSRDEntry exitCode artifacts checkerDecision auditDigest diagnostic ->
    checkerDecision :=
  fun entry =>
    ay_vsrd_conj_right exitCode
      (AyVSRDConj artifacts
        (AyVSRDConj checkerDecision (AyVSRDConj auditDigest diagnostic)))
      entry checkerDecision
      (fun _artifactsProof tail =>
        tail checkerDecision (fun checkerProof _auditTail => checkerProof))

theorem ay_vsrd_membership_intro (leafHash root entry : Prop) :
    leafHash -> root -> entry -> AyVSRDMembership leafHash root entry :=
  fun leafProof rootProof entryProof =>
    ay_vsrd_conj_intro leafHash (AyVSRDConj root entry)
      leafProof
      (ay_vsrd_conj_intro root entry rootProof entryProof)

theorem ay_vsrd_membership_entry (leafHash root entry : Prop) :
    AyVSRDMembership leafHash root entry -> entry :=
  fun membership =>
    ay_vsrd_conj_right leafHash (AyVSRDConj root entry) membership
      entry (fun _rootProof entryProof => entryProof)

theorem ay_vsrd_no_claim_intro
    (reason auditDigest diagnostic : Prop) :
    reason -> auditDigest -> diagnostic ->
    AyVSRDNoClaim reason auditDigest diagnostic :=
  fun reasonProof auditProof diagnosticProof =>
    ay_vsrd_conj_intro reason (AyVSRDConj auditDigest diagnostic)
      reasonProof
      (ay_vsrd_conj_intro auditDigest diagnostic auditProof
        diagnosticProof)

theorem ay_vsrd_recompute_intro
    (reason auditDigest diagnostic : Prop) :
    reason -> auditDigest -> diagnostic ->
    AyVSRDRecomputeObligation reason auditDigest diagnostic :=
  ay_vsrd_no_claim_intro reason auditDigest diagnostic

theorem ay_vsrd_preprocess_model_reconstruct
    (original solver internalAssignment visibleAssignment : Prop) :
    AyVSRDPreprocessArtifact original solver ->
    (internalAssignment -> visibleAssignment) ->
    AyVSRDModel solver internalAssignment ->
    AyVSRDVisibleSAT original visibleAssignment :=
  fun preprocess decode model =>
    ay_vsrd_model_intro original visibleAssignment
      (ay_vsrd_equisat_backward original solver preprocess
        (ay_vsrd_model_formula solver internalAssignment model))
      (decode (ay_vsrd_model_assignment solver internalAssignment model))

theorem ay_vsrd_preprocess_unsat_reconstruct
    (original solver : Prop) :
    AyVSRDPreprocessArtifact original solver ->
    AyVSRDUnsat solver ->
    AyVSRDUnsat original :=
  fun preprocess solverUnsat originalProof =>
    solverUnsat
      (ay_vsrd_equisat_forward original solver preprocess originalProof)

theorem ay_vsrd_replay_unsat_public
    (original solver stream finalClause : Prop) :
    AyVSRDPreprocessArtifact original solver ->
    AyVSRDReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    stream ->
    AyVSRDUnsat original :=
  fun preprocess replay closeFinal streamProof originalProof =>
    closeFinal
      (replay streamProof
        (ay_vsrd_equisat_forward original solver preprocess originalProof))

theorem ay_vsrd_retained_sat_membership_sound
    (leafHash root acceptedSat artifacts satBranch auditDigest diagnostic
      original solver internalAssignment visibleAssignment : Prop) :
    AyVSRDPreprocessArtifact original solver ->
    (internalAssignment -> visibleAssignment) ->
    (satBranch -> AyVSRDModel solver internalAssignment) ->
    AyVSRDMembership leafHash root
      (AyVSRDEntry acceptedSat artifacts satBranch auditDigest diagnostic) ->
    AyVSRDVisibleSAT original visibleAssignment :=
  fun preprocess decode accept membership =>
    ay_vsrd_preprocess_model_reconstruct original solver internalAssignment
      visibleAssignment preprocess decode
      (accept
        (ay_vsrd_entry_checker acceptedSat artifacts satBranch auditDigest
          diagnostic
          (ay_vsrd_membership_entry leafHash root
            (AyVSRDEntry acceptedSat artifacts satBranch auditDigest
              diagnostic)
            membership)))

theorem ay_vsrd_retained_unsat_membership_sound
    (leafHash root acceptedUnsat artifacts unsatBranch auditDigest diagnostic
      original solver stream finalClause : Prop) :
    AyVSRDPreprocessArtifact original solver ->
    AyVSRDReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    (unsatBranch -> stream) ->
    AyVSRDMembership leafHash root
      (AyVSRDEntry acceptedUnsat artifacts unsatBranch auditDigest
        diagnostic) ->
    AyVSRDUnsat original :=
  fun preprocess replay closeFinal accept membership =>
    ay_vsrd_replay_unsat_public original solver stream finalClause preprocess
      replay closeFinal
      (accept
        (ay_vsrd_entry_checker acceptedUnsat artifacts unsatBranch
          auditDigest diagnostic
          (ay_vsrd_membership_entry leafHash root
            (AyVSRDEntry acceptedUnsat artifacts unsatBranch auditDigest
              diagnostic)
            membership)))

theorem ay_vsrd_matching_replay_public_sound
    (originalRun replayRun replayAgreement checkerTrace
      satFact unsatFact noClaim : Prop) :
    AyVSRDReplayBundle originalRun replayRun replayAgreement checkerTrace ->
    (originalRun -> replayAgreement -> checkerTrace ->
      AyVSRDPublicResult satFact unsatFact noClaim) ->
    AyVSRDPublicResult satFact unsatFact noClaim :=
  fun bundle sound =>
    sound
      (ay_vsrd_replay_bundle_original originalRun replayRun replayAgreement
        checkerTrace bundle)
      (ay_vsrd_replay_bundle_agreement originalRun replayRun replayAgreement
        checkerTrace bundle)
      (ay_vsrd_replay_bundle_trace originalRun replayRun replayAgreement
        checkerTrace bundle)

theorem ay_vsrd_matching_replay_preserves_sat
    (originalRun replayRun replayAgreement checkerTrace satFact : Prop) :
    AyVSRDReplayBundle originalRun replayRun replayAgreement checkerTrace ->
    (replayAgreement -> checkerTrace -> satFact) ->
    satFact :=
  fun bundle sound =>
    sound
      (ay_vsrd_replay_bundle_agreement originalRun replayRun replayAgreement
        checkerTrace bundle)
      (ay_vsrd_replay_bundle_trace originalRun replayRun replayAgreement
        checkerTrace bundle)

theorem ay_vsrd_matching_replay_preserves_unsat
    (originalRun replayRun replayAgreement checkerTrace unsatFact : Prop) :
    AyVSRDReplayBundle originalRun replayRun replayAgreement checkerTrace ->
    (replayAgreement -> checkerTrace -> unsatFact) ->
    unsatFact :=
  fun bundle sound =>
    sound
      (ay_vsrd_replay_bundle_agreement originalRun replayRun replayAgreement
        checkerTrace bundle)
      (ay_vsrd_replay_bundle_trace originalRun replayRun replayAgreement
        checkerTrace bundle)

theorem ay_vsrd_replay_diverged_no_claim
    (replayDiverged auditDigest diagnostic : Prop) :
    replayDiverged -> auditDigest -> diagnostic ->
    AyVSRDNoClaim replayDiverged auditDigest diagnostic :=
  ay_vsrd_no_claim_intro replayDiverged auditDigest diagnostic

theorem ay_vsrd_stale_seed_artifact_no_claim
    (staleSeed auditDigest diagnostic : Prop) :
    staleSeed -> auditDigest -> diagnostic ->
    AyVSRDNoClaim staleSeed auditDigest diagnostic :=
  ay_vsrd_no_claim_intro staleSeed auditDigest diagnostic

theorem ay_vsrd_stale_config_artifact_no_claim
    (staleConfig auditDigest diagnostic : Prop) :
    staleConfig -> auditDigest -> diagnostic ->
    AyVSRDNoClaim staleConfig auditDigest diagnostic :=
  ay_vsrd_no_claim_intro staleConfig auditDigest diagnostic

theorem ay_vsrd_failure_public_result_no_claim
    (satFact unsatFact reason auditDigest diagnostic : Prop) :
    AyVSRDNoClaim reason auditDigest diagnostic ->
    AyVSRDPublicResult satFact unsatFact
      (AyVSRDNoClaim reason auditDigest diagnostic) :=
  fun noClaim =>
    ay_vsrd_disj_right satFact
      (AyVSRDDisj unsatFact
        (AyVSRDNoClaim reason auditDigest diagnostic))
      (ay_vsrd_disj_right unsatFact
        (AyVSRDNoClaim reason auditDigest diagnostic)
        noClaim)

theorem ay_vsrd_replay_failure_recompute
    (replayDiverged staleSeed staleConfig auditDigest diagnostic recompute :
      Prop) :
    AyVSRDDisj replayDiverged
      (AyVSRDDisj staleSeed staleConfig) ->
    auditDigest -> diagnostic ->
    (replayDiverged ->
      AyVSRDRecomputeObligation replayDiverged auditDigest diagnostic ->
      recompute) ->
    (staleSeed ->
      AyVSRDRecomputeObligation staleSeed auditDigest diagnostic ->
      recompute) ->
    (staleConfig ->
      AyVSRDRecomputeObligation staleConfig auditDigest diagnostic ->
      recompute) ->
    recompute :=
  fun failure auditProof diagnosticProof onDiverged onSeed onConfig =>
    failure recompute
      (fun divergedProof =>
        onDiverged divergedProof
          (ay_vsrd_recompute_intro replayDiverged auditDigest diagnostic
            divergedProof auditProof diagnosticProof))
      (fun tail =>
        tail recompute
          (fun seedProof =>
            onSeed seedProof
              (ay_vsrd_recompute_intro staleSeed auditDigest diagnostic
                seedProof auditProof diagnosticProof))
          (fun configProof =>
            onConfig configProof
              (ay_vsrd_recompute_intro staleConfig auditDigest diagnostic
                configProof auditProof diagnosticProof)))
