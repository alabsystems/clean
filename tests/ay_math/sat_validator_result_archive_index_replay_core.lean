-- SAT-COMP validator result archive-index replay soundness core.
--
-- Archived SAT/UNSAT results are replayable through a result index only when
-- archive membership, run manifest, artifact digest, formula fingerprint,
-- checker evidence, and public label agree.  Stale index entries and replay
-- divergence are no-claim recomputation obligations.

def AyVRAIConj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def AyVRAIDisj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyVRAIEquisat (before after : Prop) : Prop :=
  AyVRAIConj (before -> after) (after -> before)

def AyVRAIPublicResult (satFact unsatFact noClaim : Prop) : Prop :=
  AyVRAIDisj satFact (AyVRAIDisj unsatFact noClaim)

def AyVRAIReplayAgreement
    (archiveMember runManifest artifactDigest formulaFingerprint
      checkerEvidence publicLabel : Prop) : Prop :=
  AyVRAIConj archiveMember
    (AyVRAIConj runManifest
      (AyVRAIConj artifactDigest
        (AyVRAIConj formulaFingerprint
          (AyVRAIConj checkerEvidence publicLabel))))

def AyVRAIResultIndex
    (indexMember indexDigest archivedResult : Prop) : Prop :=
  AyVRAIConj indexMember (AyVRAIConj indexDigest archivedResult)

def AyVRAIReplayBundle
    (resultIndex replayAgreement replayTrace publicResult : Prop) : Prop :=
  AyVRAIConj resultIndex
    (AyVRAIConj replayAgreement
      (AyVRAIConj replayTrace publicResult))

def AyVRAIEntry
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    Prop :=
  AyVRAIConj exitCode
    (AyVRAIConj artifacts
      (AyVRAIConj checkerDecision
        (AyVRAIConj auditDigest diagnostic)))

def AyVRAIMembership (leafHash root entry : Prop) : Prop :=
  AyVRAIConj leafHash (AyVRAIConj root entry)

def AyVRAINoClaim (reason auditDigest diagnostic : Prop) : Prop :=
  AyVRAIConj reason (AyVRAIConj auditDigest diagnostic)

def AyVRAIRecomputeObligation
    (reason auditDigest diagnostic : Prop) : Prop :=
  AyVRAIConj reason (AyVRAIConj auditDigest diagnostic)

def AyVRAIModel (formula assignment : Prop) : Prop :=
  AyVRAIConj formula assignment

def AyVRAIUnsat (formula : Prop) : Prop :=
  formula -> False

def AyVRAIVisibleSAT (original visibleAssignment : Prop) : Prop :=
  AyVRAIModel original visibleAssignment

def AyVRAIPreprocessArtifact (original solver : Prop) : Prop :=
  AyVRAIEquisat original solver

def AyVRAIReplayAccepted (solver stream finalClause : Prop) : Prop :=
  stream -> solver -> finalClause

theorem ay_vrai_conj_intro (left right : Prop) :
    left -> right -> AyVRAIConj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_vrai_conj_left (left right : Prop) :
    AyVRAIConj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_vrai_conj_right (left right : Prop) :
    AyVRAIConj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_vrai_disj_right (left right : Prop) :
    right -> AyVRAIDisj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_vrai_equisat_forward (before after : Prop) :
    AyVRAIEquisat before after -> before -> after :=
  fun witness hbefore =>
    witness after (fun forward _backward => forward hbefore)

theorem ay_vrai_equisat_backward (before after : Prop) :
    AyVRAIEquisat before after -> after -> before :=
  fun witness hafter =>
    witness before (fun _forward backward => backward hafter)

theorem ay_vrai_model_intro (formula assignment : Prop) :
    formula -> assignment -> AyVRAIModel formula assignment :=
  fun formulaProof assignmentProof =>
    ay_vrai_conj_intro formula assignment formulaProof assignmentProof

theorem ay_vrai_model_formula (formula assignment : Prop) :
    AyVRAIModel formula assignment -> formula :=
  fun model => ay_vrai_conj_left formula assignment model

theorem ay_vrai_model_assignment (formula assignment : Prop) :
    AyVRAIModel formula assignment -> assignment :=
  fun model => ay_vrai_conj_right formula assignment model

theorem ay_vrai_replay_agreement_intro
    (archiveMember runManifest artifactDigest formulaFingerprint
      checkerEvidence publicLabel : Prop) :
    archiveMember -> runManifest -> artifactDigest -> formulaFingerprint ->
    checkerEvidence -> publicLabel ->
    AyVRAIReplayAgreement archiveMember runManifest artifactDigest
      formulaFingerprint checkerEvidence publicLabel :=
  fun archiveProof manifestProof digestProof fingerprintProof checkerProof
      labelProof =>
    ay_vrai_conj_intro archiveMember
      (AyVRAIConj runManifest
        (AyVRAIConj artifactDigest
          (AyVRAIConj formulaFingerprint
            (AyVRAIConj checkerEvidence publicLabel))))
      archiveProof
      (ay_vrai_conj_intro runManifest
        (AyVRAIConj artifactDigest
          (AyVRAIConj formulaFingerprint
            (AyVRAIConj checkerEvidence publicLabel)))
        manifestProof
        (ay_vrai_conj_intro artifactDigest
          (AyVRAIConj formulaFingerprint
            (AyVRAIConj checkerEvidence publicLabel))
          digestProof
          (ay_vrai_conj_intro formulaFingerprint
            (AyVRAIConj checkerEvidence publicLabel)
            fingerprintProof
            (ay_vrai_conj_intro checkerEvidence publicLabel checkerProof
              labelProof))))

theorem ay_vrai_replay_agreement_archive
    (archiveMember runManifest artifactDigest formulaFingerprint
      checkerEvidence publicLabel : Prop) :
    AyVRAIReplayAgreement archiveMember runManifest artifactDigest
      formulaFingerprint checkerEvidence publicLabel ->
    archiveMember :=
  fun agreement =>
    ay_vrai_conj_left archiveMember
      (AyVRAIConj runManifest
        (AyVRAIConj artifactDigest
          (AyVRAIConj formulaFingerprint
            (AyVRAIConj checkerEvidence publicLabel))))
      agreement

theorem ay_vrai_replay_agreement_checker
    (archiveMember runManifest artifactDigest formulaFingerprint
      checkerEvidence publicLabel : Prop) :
    AyVRAIReplayAgreement archiveMember runManifest artifactDigest
      formulaFingerprint checkerEvidence publicLabel ->
    checkerEvidence :=
  fun agreement =>
    ay_vrai_conj_right archiveMember
      (AyVRAIConj runManifest
        (AyVRAIConj artifactDigest
          (AyVRAIConj formulaFingerprint
            (AyVRAIConj checkerEvidence publicLabel))))
      agreement checkerEvidence
      (fun _manifestProof tail =>
        tail checkerEvidence
          (fun _digestProof tail2 =>
            tail2 checkerEvidence
              (fun _fingerprintProof tail3 =>
                tail3 checkerEvidence
                  (fun checkerProof _labelProof => checkerProof))))

theorem ay_vrai_replay_agreement_label
    (archiveMember runManifest artifactDigest formulaFingerprint
      checkerEvidence publicLabel : Prop) :
    AyVRAIReplayAgreement archiveMember runManifest artifactDigest
      formulaFingerprint checkerEvidence publicLabel ->
    publicLabel :=
  fun agreement =>
    ay_vrai_conj_right archiveMember
      (AyVRAIConj runManifest
        (AyVRAIConj artifactDigest
          (AyVRAIConj formulaFingerprint
            (AyVRAIConj checkerEvidence publicLabel))))
      agreement publicLabel
      (fun _manifestProof tail =>
        tail publicLabel
          (fun _digestProof tail2 =>
            tail2 publicLabel
              (fun _fingerprintProof tail3 =>
                tail3 publicLabel
                  (fun _checkerProof labelProof => labelProof))))

theorem ay_vrai_result_index_intro
    (indexMember indexDigest archivedResult : Prop) :
    indexMember -> indexDigest -> archivedResult ->
    AyVRAIResultIndex indexMember indexDigest archivedResult :=
  fun memberProof digestProof resultProof =>
    ay_vrai_conj_intro indexMember
      (AyVRAIConj indexDigest archivedResult)
      memberProof
      (ay_vrai_conj_intro indexDigest archivedResult digestProof
        resultProof)

theorem ay_vrai_result_index_member
    (indexMember indexDigest archivedResult : Prop) :
    AyVRAIResultIndex indexMember indexDigest archivedResult ->
    indexMember :=
  fun index =>
    ay_vrai_conj_left indexMember
      (AyVRAIConj indexDigest archivedResult) index

theorem ay_vrai_replay_bundle_intro
    (resultIndex replayAgreement replayTrace publicResult : Prop) :
    resultIndex -> replayAgreement -> replayTrace -> publicResult ->
    AyVRAIReplayBundle resultIndex replayAgreement replayTrace
      publicResult :=
  fun indexProof agreementProof traceProof publicProof =>
    ay_vrai_conj_intro resultIndex
      (AyVRAIConj replayAgreement
        (AyVRAIConj replayTrace publicResult))
      indexProof
      (ay_vrai_conj_intro replayAgreement
        (AyVRAIConj replayTrace publicResult)
        agreementProof
        (ay_vrai_conj_intro replayTrace publicResult traceProof
          publicProof))

theorem ay_vrai_replay_bundle_index
    (resultIndex replayAgreement replayTrace publicResult : Prop) :
    AyVRAIReplayBundle resultIndex replayAgreement replayTrace
      publicResult ->
    resultIndex :=
  fun bundle =>
    ay_vrai_conj_left resultIndex
      (AyVRAIConj replayAgreement
        (AyVRAIConj replayTrace publicResult))
      bundle

theorem ay_vrai_replay_bundle_agreement
    (resultIndex replayAgreement replayTrace publicResult : Prop) :
    AyVRAIReplayBundle resultIndex replayAgreement replayTrace
      publicResult ->
    replayAgreement :=
  fun bundle =>
    ay_vrai_conj_right resultIndex
      (AyVRAIConj replayAgreement
        (AyVRAIConj replayTrace publicResult))
      bundle replayAgreement
      (fun agreementProof _tail => agreementProof)

theorem ay_vrai_replay_bundle_public
    (resultIndex replayAgreement replayTrace publicResult : Prop) :
    AyVRAIReplayBundle resultIndex replayAgreement replayTrace
      publicResult ->
    publicResult :=
  fun bundle =>
    ay_vrai_conj_right resultIndex
      (AyVRAIConj replayAgreement
        (AyVRAIConj replayTrace publicResult))
      bundle publicResult
      (fun _agreementProof tail =>
        tail publicResult (fun _traceProof publicProof => publicProof))

theorem ay_vrai_entry_intro
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    exitCode -> artifacts -> checkerDecision -> auditDigest -> diagnostic ->
    AyVRAIEntry exitCode artifacts checkerDecision auditDigest diagnostic :=
  fun exitProof artifactsProof checkerProof auditProof diagnosticProof =>
    ay_vrai_conj_intro exitCode
      (AyVRAIConj artifacts
        (AyVRAIConj checkerDecision (AyVRAIConj auditDigest diagnostic)))
      exitProof
      (ay_vrai_conj_intro artifacts
        (AyVRAIConj checkerDecision (AyVRAIConj auditDigest diagnostic))
        artifactsProof
        (ay_vrai_conj_intro checkerDecision
          (AyVRAIConj auditDigest diagnostic)
          checkerProof
          (ay_vrai_conj_intro auditDigest diagnostic auditProof
            diagnosticProof)))

theorem ay_vrai_entry_checker
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    AyVRAIEntry exitCode artifacts checkerDecision auditDigest diagnostic ->
    checkerDecision :=
  fun entry =>
    ay_vrai_conj_right exitCode
      (AyVRAIConj artifacts
        (AyVRAIConj checkerDecision (AyVRAIConj auditDigest diagnostic)))
      entry checkerDecision
      (fun _artifactsProof tail =>
        tail checkerDecision (fun checkerProof _auditTail => checkerProof))

theorem ay_vrai_membership_intro (leafHash root entry : Prop) :
    leafHash -> root -> entry -> AyVRAIMembership leafHash root entry :=
  fun leafProof rootProof entryProof =>
    ay_vrai_conj_intro leafHash (AyVRAIConj root entry)
      leafProof
      (ay_vrai_conj_intro root entry rootProof entryProof)

theorem ay_vrai_membership_entry (leafHash root entry : Prop) :
    AyVRAIMembership leafHash root entry -> entry :=
  fun membership =>
    ay_vrai_conj_right leafHash (AyVRAIConj root entry) membership
      entry (fun _rootProof entryProof => entryProof)

theorem ay_vrai_no_claim_intro
    (reason auditDigest diagnostic : Prop) :
    reason -> auditDigest -> diagnostic ->
    AyVRAINoClaim reason auditDigest diagnostic :=
  fun reasonProof auditProof diagnosticProof =>
    ay_vrai_conj_intro reason (AyVRAIConj auditDigest diagnostic)
      reasonProof
      (ay_vrai_conj_intro auditDigest diagnostic auditProof
        diagnosticProof)

theorem ay_vrai_recompute_intro
    (reason auditDigest diagnostic : Prop) :
    reason -> auditDigest -> diagnostic ->
    AyVRAIRecomputeObligation reason auditDigest diagnostic :=
  ay_vrai_no_claim_intro reason auditDigest diagnostic

theorem ay_vrai_preprocess_model_reconstruct
    (original solver internalAssignment visibleAssignment : Prop) :
    AyVRAIPreprocessArtifact original solver ->
    (internalAssignment -> visibleAssignment) ->
    AyVRAIModel solver internalAssignment ->
    AyVRAIVisibleSAT original visibleAssignment :=
  fun preprocess decode model =>
    ay_vrai_model_intro original visibleAssignment
      (ay_vrai_equisat_backward original solver preprocess
        (ay_vrai_model_formula solver internalAssignment model))
      (decode (ay_vrai_model_assignment solver internalAssignment model))

theorem ay_vrai_preprocess_unsat_reconstruct
    (original solver : Prop) :
    AyVRAIPreprocessArtifact original solver ->
    AyVRAIUnsat solver ->
    AyVRAIUnsat original :=
  fun preprocess solverUnsat originalProof =>
    solverUnsat
      (ay_vrai_equisat_forward original solver preprocess originalProof)

theorem ay_vrai_replay_unsat_public
    (original solver stream finalClause : Prop) :
    AyVRAIPreprocessArtifact original solver ->
    AyVRAIReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    stream ->
    AyVRAIUnsat original :=
  fun preprocess replay closeFinal streamProof originalProof =>
    closeFinal
      (replay streamProof
        (ay_vrai_equisat_forward original solver preprocess originalProof))

theorem ay_vrai_retained_sat_membership_sound
    (leafHash root acceptedSat artifacts satBranch auditDigest diagnostic
      original solver internalAssignment visibleAssignment : Prop) :
    AyVRAIPreprocessArtifact original solver ->
    (internalAssignment -> visibleAssignment) ->
    (satBranch -> AyVRAIModel solver internalAssignment) ->
    AyVRAIMembership leafHash root
      (AyVRAIEntry acceptedSat artifacts satBranch auditDigest diagnostic) ->
    AyVRAIVisibleSAT original visibleAssignment :=
  fun preprocess decode accept membership =>
    ay_vrai_preprocess_model_reconstruct original solver internalAssignment
      visibleAssignment preprocess decode
      (accept
        (ay_vrai_entry_checker acceptedSat artifacts satBranch auditDigest
          diagnostic
          (ay_vrai_membership_entry leafHash root
            (AyVRAIEntry acceptedSat artifacts satBranch auditDigest
              diagnostic)
            membership)))

theorem ay_vrai_retained_unsat_membership_sound
    (leafHash root acceptedUnsat artifacts unsatBranch auditDigest diagnostic
      original solver stream finalClause : Prop) :
    AyVRAIPreprocessArtifact original solver ->
    AyVRAIReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    (unsatBranch -> stream) ->
    AyVRAIMembership leafHash root
      (AyVRAIEntry acceptedUnsat artifacts unsatBranch auditDigest
        diagnostic) ->
    AyVRAIUnsat original :=
  fun preprocess replay closeFinal accept membership =>
    ay_vrai_replay_unsat_public original solver stream finalClause preprocess
      replay closeFinal
      (accept
        (ay_vrai_entry_checker acceptedUnsat artifacts unsatBranch
          auditDigest diagnostic
          (ay_vrai_membership_entry leafHash root
            (AyVRAIEntry acceptedUnsat artifacts unsatBranch auditDigest
              diagnostic)
            membership)))

theorem ay_vrai_replay_bundle_public_sound
    (resultIndex replayAgreement replayTrace publicResult
      satFact unsatFact noClaim : Prop) :
    AyVRAIReplayBundle resultIndex replayAgreement replayTrace
      publicResult ->
    (resultIndex -> replayAgreement -> publicResult ->
      AyVRAIPublicResult satFact unsatFact noClaim) ->
    AyVRAIPublicResult satFact unsatFact noClaim :=
  fun bundle sound =>
    sound
      (ay_vrai_replay_bundle_index resultIndex replayAgreement replayTrace
        publicResult bundle)
      (ay_vrai_replay_bundle_agreement resultIndex replayAgreement
        replayTrace publicResult bundle)
      (ay_vrai_replay_bundle_public resultIndex replayAgreement replayTrace
        publicResult bundle)

theorem ay_vrai_replay_bundle_preserves_sat
    (resultIndex replayAgreement replayTrace publicResult satFact : Prop) :
    AyVRAIReplayBundle resultIndex replayAgreement replayTrace
      publicResult ->
    (replayAgreement -> publicResult -> satFact) ->
    satFact :=
  fun bundle sound =>
    sound
      (ay_vrai_replay_bundle_agreement resultIndex replayAgreement
        replayTrace publicResult bundle)
      (ay_vrai_replay_bundle_public resultIndex replayAgreement replayTrace
        publicResult bundle)

theorem ay_vrai_replay_bundle_preserves_unsat
    (resultIndex replayAgreement replayTrace publicResult unsatFact : Prop) :
    AyVRAIReplayBundle resultIndex replayAgreement replayTrace
      publicResult ->
    (replayAgreement -> publicResult -> unsatFact) ->
    unsatFact :=
  fun bundle sound =>
    sound
      (ay_vrai_replay_bundle_agreement resultIndex replayAgreement
        replayTrace publicResult bundle)
      (ay_vrai_replay_bundle_public resultIndex replayAgreement replayTrace
        publicResult bundle)

theorem ay_vrai_stale_index_no_claim
    (staleIndex auditDigest diagnostic : Prop) :
    staleIndex -> auditDigest -> diagnostic ->
    AyVRAINoClaim staleIndex auditDigest diagnostic :=
  ay_vrai_no_claim_intro staleIndex auditDigest diagnostic

theorem ay_vrai_replay_divergence_no_claim
    (replayDivergence auditDigest diagnostic : Prop) :
    replayDivergence -> auditDigest -> diagnostic ->
    AyVRAINoClaim replayDivergence auditDigest diagnostic :=
  ay_vrai_no_claim_intro replayDivergence auditDigest diagnostic

theorem ay_vrai_failure_public_result_no_claim
    (satFact unsatFact reason auditDigest diagnostic : Prop) :
    AyVRAINoClaim reason auditDigest diagnostic ->
    AyVRAIPublicResult satFact unsatFact
      (AyVRAINoClaim reason auditDigest diagnostic) :=
  fun noClaim =>
    ay_vrai_disj_right satFact
      (AyVRAIDisj unsatFact
        (AyVRAINoClaim reason auditDigest diagnostic))
      (ay_vrai_disj_right unsatFact
        (AyVRAINoClaim reason auditDigest diagnostic)
        noClaim)

theorem ay_vrai_stale_or_divergent_recompute
    (staleIndex replayDivergence auditDigest diagnostic recompute : Prop) :
    AyVRAIDisj staleIndex replayDivergence ->
    auditDigest -> diagnostic ->
    (staleIndex ->
      AyVRAIRecomputeObligation staleIndex auditDigest diagnostic ->
      recompute) ->
    (replayDivergence ->
      AyVRAIRecomputeObligation replayDivergence auditDigest diagnostic ->
      recompute) ->
    recompute :=
  fun failure auditProof diagnosticProof onStale onDivergence =>
    failure recompute
      (fun staleProof =>
        onStale staleProof
          (ay_vrai_recompute_intro staleIndex auditDigest diagnostic
            staleProof auditProof diagnosticProof))
      (fun divergenceProof =>
        onDivergence divergenceProof
          (ay_vrai_recompute_intro replayDivergence auditDigest diagnostic
            divergenceProof auditProof diagnosticProof))
