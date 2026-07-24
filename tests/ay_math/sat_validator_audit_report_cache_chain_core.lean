-- SAT-COMP validator audit report-cache chain core.
--
-- A chained cache hit is sound only when every link carries fresh root, epoch,
-- digest, and membership evidence.  Broken or stale links become recomputation
-- obligations and no-claim diagnostics rather than public SAT/UNSAT claims.

def AyARCCConj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def AyARCCDisj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyARCCEquisat (before after : Prop) : Prop :=
  AyARCCConj (before -> after) (after -> before)

def AyARCCPublicResult (satFact unsatFact noClaim : Prop) : Prop :=
  AyARCCDisj satFact (AyARCCDisj unsatFact noClaim)

def AyARCCEntry
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    Prop :=
  AyARCCConj exitCode
    (AyARCCConj artifacts
      (AyARCCConj checkerDecision
        (AyARCCConj auditDigest diagnostic)))

def AyARCCMembership (leafHash root entry : Prop) : Prop :=
  AyARCCConj leafHash (AyARCCConj root entry)

def AyARCCCacheLink
    (fromRoot toRoot fromEpoch toEpoch digestLink membershipEvidence :
      Prop) : Prop :=
  AyARCCConj fromRoot
    (AyARCCConj toRoot
      (AyARCCConj fromEpoch
        (AyARCCConj toEpoch
          (AyARCCConj digestLink membershipEvidence))))

def AyARCCFreshLink
    (cacheLink rootMatch epochFresh digestMatch : Prop) : Prop :=
  AyARCCConj cacheLink
    (AyARCCConj rootMatch (AyARCCConj epochFresh digestMatch))

def AyARCCCacheChain
    (firstLink restLinks finalReport : Prop) : Prop :=
  AyARCCConj firstLink (AyARCCConj restLinks finalReport)

def AyARCCBrokenLink (brokenReason auditDigest diagnostic : Prop) : Prop :=
  AyARCCConj brokenReason (AyARCCConj auditDigest diagnostic)

def AyARCCStaleLink (staleEpoch auditDigest diagnostic : Prop) : Prop :=
  AyARCCConj staleEpoch (AyARCCConj auditDigest diagnostic)

def AyARCCRecomputeObligation
    (reason auditDigest diagnostic : Prop) : Prop :=
  AyARCCConj reason (AyARCCConj auditDigest diagnostic)

def AyARCCNoClaim (reason auditDigest diagnostic : Prop) : Prop :=
  AyARCCConj reason (AyARCCConj auditDigest diagnostic)

def AyARCCModel (formula assignment : Prop) : Prop :=
  AyARCCConj formula assignment

def AyARCCUnsat (formula : Prop) : Prop :=
  formula -> False

def AyARCCVisibleSAT (original visibleAssignment : Prop) : Prop :=
  AyARCCModel original visibleAssignment

def AyARCCPreprocessArtifact (original solver : Prop) : Prop :=
  AyARCCEquisat original solver

def AyARCCReplayAccepted (solver stream finalClause : Prop) : Prop :=
  stream -> solver -> finalClause

theorem ay_arcc_conj_intro (left right : Prop) :
    left -> right -> AyARCCConj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_arcc_conj_left (left right : Prop) :
    AyARCCConj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_arcc_conj_right (left right : Prop) :
    AyARCCConj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_arcc_disj_right (left right : Prop) :
    right -> AyARCCDisj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_arcc_equisat_forward (before after : Prop) :
    AyARCCEquisat before after -> before -> after :=
  fun witness hbefore =>
    witness after (fun forward _backward => forward hbefore)

theorem ay_arcc_equisat_backward (before after : Prop) :
    AyARCCEquisat before after -> after -> before :=
  fun witness hafter =>
    witness before (fun _forward backward => backward hafter)

theorem ay_arcc_model_intro (formula assignment : Prop) :
    formula -> assignment -> AyARCCModel formula assignment :=
  fun formulaProof assignmentProof =>
    ay_arcc_conj_intro formula assignment formulaProof assignmentProof

theorem ay_arcc_model_formula (formula assignment : Prop) :
    AyARCCModel formula assignment -> formula :=
  fun model => ay_arcc_conj_left formula assignment model

theorem ay_arcc_model_assignment (formula assignment : Prop) :
    AyARCCModel formula assignment -> assignment :=
  fun model => ay_arcc_conj_right formula assignment model

theorem ay_arcc_entry_intro
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    exitCode -> artifacts -> checkerDecision -> auditDigest -> diagnostic ->
    AyARCCEntry exitCode artifacts checkerDecision auditDigest diagnostic :=
  fun exitProof artifactsProof checkerProof auditProof diagnosticProof =>
    ay_arcc_conj_intro exitCode
      (AyARCCConj artifacts
        (AyARCCConj checkerDecision (AyARCCConj auditDigest diagnostic)))
      exitProof
      (ay_arcc_conj_intro artifacts
        (AyARCCConj checkerDecision (AyARCCConj auditDigest diagnostic))
        artifactsProof
        (ay_arcc_conj_intro checkerDecision
          (AyARCCConj auditDigest diagnostic)
          checkerProof
          (ay_arcc_conj_intro auditDigest diagnostic auditProof
            diagnosticProof)))

theorem ay_arcc_entry_checker
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    AyARCCEntry exitCode artifacts checkerDecision auditDigest diagnostic ->
    checkerDecision :=
  fun entry =>
    ay_arcc_conj_right exitCode
      (AyARCCConj artifacts
        (AyARCCConj checkerDecision (AyARCCConj auditDigest diagnostic)))
      entry checkerDecision
      (fun _artifactsProof tail =>
        tail checkerDecision (fun checkerProof _auditTail => checkerProof))

theorem ay_arcc_membership_entry (leafHash root entry : Prop) :
    AyARCCMembership leafHash root entry -> entry :=
  fun membership =>
    ay_arcc_conj_right leafHash (AyARCCConj root entry) membership
      entry (fun _rootProof entryProof => entryProof)

theorem ay_arcc_cache_link_intro
    (fromRoot toRoot fromEpoch toEpoch digestLink membershipEvidence :
      Prop) :
    fromRoot -> toRoot -> fromEpoch -> toEpoch -> digestLink ->
    membershipEvidence ->
    AyARCCCacheLink fromRoot toRoot fromEpoch toEpoch digestLink
      membershipEvidence :=
  fun fromProof toProof fromEpochProof toEpochProof digestProof
      membershipProof =>
    ay_arcc_conj_intro fromRoot
      (AyARCCConj toRoot
        (AyARCCConj fromEpoch
          (AyARCCConj toEpoch
            (AyARCCConj digestLink membershipEvidence))))
      fromProof
      (ay_arcc_conj_intro toRoot
        (AyARCCConj fromEpoch
          (AyARCCConj toEpoch
            (AyARCCConj digestLink membershipEvidence)))
        toProof
        (ay_arcc_conj_intro fromEpoch
          (AyARCCConj toEpoch
            (AyARCCConj digestLink membershipEvidence))
          fromEpochProof
          (ay_arcc_conj_intro toEpoch
            (AyARCCConj digestLink membershipEvidence)
            toEpochProof
            (ay_arcc_conj_intro digestLink membershipEvidence digestProof
              membershipProof))))

theorem ay_arcc_fresh_link_intro
    (cacheLink rootMatch epochFresh digestMatch : Prop) :
    cacheLink -> rootMatch -> epochFresh -> digestMatch ->
    AyARCCFreshLink cacheLink rootMatch epochFresh digestMatch :=
  fun linkProof rootProof epochProof digestProof =>
    ay_arcc_conj_intro cacheLink
      (AyARCCConj rootMatch (AyARCCConj epochFresh digestMatch))
      linkProof
      (ay_arcc_conj_intro rootMatch
        (AyARCCConj epochFresh digestMatch)
        rootProof
        (ay_arcc_conj_intro epochFresh digestMatch epochProof
          digestProof))

theorem ay_arcc_fresh_link_cache
    (cacheLink rootMatch epochFresh digestMatch : Prop) :
    AyARCCFreshLink cacheLink rootMatch epochFresh digestMatch ->
    cacheLink :=
  fun fresh =>
    ay_arcc_conj_left cacheLink
      (AyARCCConj rootMatch (AyARCCConj epochFresh digestMatch)) fresh

theorem ay_arcc_fresh_link_root
    (cacheLink rootMatch epochFresh digestMatch : Prop) :
    AyARCCFreshLink cacheLink rootMatch epochFresh digestMatch ->
    rootMatch :=
  fun fresh =>
    ay_arcc_conj_right cacheLink
      (AyARCCConj rootMatch (AyARCCConj epochFresh digestMatch))
      fresh rootMatch (fun rootProof _tail => rootProof)

theorem ay_arcc_fresh_link_epoch
    (cacheLink rootMatch epochFresh digestMatch : Prop) :
    AyARCCFreshLink cacheLink rootMatch epochFresh digestMatch ->
    epochFresh :=
  fun fresh =>
    ay_arcc_conj_right cacheLink
      (AyARCCConj rootMatch (AyARCCConj epochFresh digestMatch))
      fresh epochFresh
      (fun _rootProof tail =>
        tail epochFresh (fun epochProof _digestProof => epochProof))

theorem ay_arcc_cache_chain_intro
    (firstLink restLinks finalReport : Prop) :
    firstLink -> restLinks -> finalReport ->
    AyARCCCacheChain firstLink restLinks finalReport :=
  fun firstProof restProof finalProof =>
    ay_arcc_conj_intro firstLink (AyARCCConj restLinks finalReport)
      firstProof
      (ay_arcc_conj_intro restLinks finalReport restProof finalProof)

theorem ay_arcc_cache_chain_first
    (firstLink restLinks finalReport : Prop) :
    AyARCCCacheChain firstLink restLinks finalReport -> firstLink :=
  fun chain =>
    ay_arcc_conj_left firstLink (AyARCCConj restLinks finalReport) chain

theorem ay_arcc_cache_chain_rest
    (firstLink restLinks finalReport : Prop) :
    AyARCCCacheChain firstLink restLinks finalReport -> restLinks :=
  fun chain =>
    ay_arcc_conj_right firstLink (AyARCCConj restLinks finalReport)
      chain restLinks (fun restProof _finalProof => restProof)

theorem ay_arcc_cache_chain_final
    (firstLink restLinks finalReport : Prop) :
    AyARCCCacheChain firstLink restLinks finalReport -> finalReport :=
  fun chain =>
    ay_arcc_conj_right firstLink (AyARCCConj restLinks finalReport)
      chain finalReport (fun _restProof finalProof => finalProof)

theorem ay_arcc_no_claim_intro
    (reason auditDigest diagnostic : Prop) :
    reason -> auditDigest -> diagnostic ->
    AyARCCNoClaim reason auditDigest diagnostic :=
  fun reasonProof auditProof diagnosticProof =>
    ay_arcc_conj_intro reason (AyARCCConj auditDigest diagnostic)
      reasonProof
      (ay_arcc_conj_intro auditDigest diagnostic auditProof
        diagnosticProof)

theorem ay_arcc_recompute_intro
    (reason auditDigest diagnostic : Prop) :
    reason -> auditDigest -> diagnostic ->
    AyARCCRecomputeObligation reason auditDigest diagnostic :=
  fun reasonProof auditProof diagnosticProof =>
    ay_arcc_conj_intro reason (AyARCCConj auditDigest diagnostic)
      reasonProof
      (ay_arcc_conj_intro auditDigest diagnostic auditProof
        diagnosticProof)

theorem ay_arcc_broken_link_intro
    (brokenReason auditDigest diagnostic : Prop) :
    brokenReason -> auditDigest -> diagnostic ->
    AyARCCBrokenLink brokenReason auditDigest diagnostic :=
  ay_arcc_no_claim_intro brokenReason auditDigest diagnostic

theorem ay_arcc_stale_link_intro
    (staleEpoch auditDigest diagnostic : Prop) :
    staleEpoch -> auditDigest -> diagnostic ->
    AyARCCStaleLink staleEpoch auditDigest diagnostic :=
  ay_arcc_no_claim_intro staleEpoch auditDigest diagnostic

theorem ay_arcc_broken_link_no_claim
    (brokenReason auditDigest diagnostic : Prop) :
    AyARCCBrokenLink brokenReason auditDigest diagnostic ->
    AyARCCNoClaim brokenReason auditDigest diagnostic :=
  fun broken => broken

theorem ay_arcc_stale_link_no_claim
    (staleEpoch auditDigest diagnostic : Prop) :
    AyARCCStaleLink staleEpoch auditDigest diagnostic ->
    AyARCCNoClaim staleEpoch auditDigest diagnostic :=
  fun stale => stale

theorem ay_arcc_preprocess_model_reconstruct
    (original solver internalAssignment visibleAssignment : Prop) :
    AyARCCPreprocessArtifact original solver ->
    (internalAssignment -> visibleAssignment) ->
    AyARCCModel solver internalAssignment ->
    AyARCCVisibleSAT original visibleAssignment :=
  fun preprocess decode model =>
    ay_arcc_model_intro original visibleAssignment
      (ay_arcc_equisat_backward original solver preprocess
        (ay_arcc_model_formula solver internalAssignment model))
      (decode (ay_arcc_model_assignment solver internalAssignment model))

theorem ay_arcc_preprocess_unsat_reconstruct
    (original solver : Prop) :
    AyARCCPreprocessArtifact original solver ->
    AyARCCUnsat solver ->
    AyARCCUnsat original :=
  fun preprocess solverUnsat originalProof =>
    solverUnsat
      (ay_arcc_equisat_forward original solver preprocess originalProof)

theorem ay_arcc_replay_unsat_public
    (original solver stream finalClause : Prop) :
    AyARCCPreprocessArtifact original solver ->
    AyARCCReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    stream ->
    AyARCCUnsat original :=
  fun preprocess replay closeFinal streamProof originalProof =>
    closeFinal
      (replay streamProof
        (ay_arcc_equisat_forward original solver preprocess originalProof))

theorem ay_arcc_retained_sat_membership_sound
    (leafHash root acceptedSat artifacts satBranch auditDigest diagnostic
      original solver internalAssignment visibleAssignment : Prop) :
    AyARCCPreprocessArtifact original solver ->
    (internalAssignment -> visibleAssignment) ->
    (satBranch -> AyARCCModel solver internalAssignment) ->
    AyARCCMembership leafHash root
      (AyARCCEntry acceptedSat artifacts satBranch auditDigest diagnostic) ->
    AyARCCVisibleSAT original visibleAssignment :=
  fun preprocess decode accept membership =>
    ay_arcc_preprocess_model_reconstruct original solver internalAssignment
      visibleAssignment preprocess decode
      (accept
        (ay_arcc_entry_checker acceptedSat artifacts satBranch auditDigest
          diagnostic
          (ay_arcc_membership_entry leafHash root
            (AyARCCEntry acceptedSat artifacts satBranch auditDigest
              diagnostic)
            membership)))

theorem ay_arcc_retained_unsat_membership_sound
    (leafHash root acceptedUnsat artifacts unsatBranch auditDigest diagnostic
      original solver stream finalClause : Prop) :
    AyARCCPreprocessArtifact original solver ->
    AyARCCReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    (unsatBranch -> stream) ->
    AyARCCMembership leafHash root
      (AyARCCEntry acceptedUnsat artifacts unsatBranch auditDigest
        diagnostic) ->
    AyARCCUnsat original :=
  fun preprocess replay closeFinal accept membership =>
    ay_arcc_replay_unsat_public original solver stream finalClause preprocess
      replay closeFinal
      (accept
        (ay_arcc_entry_checker acceptedUnsat artifacts unsatBranch auditDigest
          diagnostic
          (ay_arcc_membership_entry leafHash root
            (AyARCCEntry acceptedUnsat artifacts unsatBranch auditDigest
              diagnostic)
            membership)))

theorem ay_arcc_fresh_chain_preserves_public_soundness
    (firstLink restLinks finalReport satFact unsatFact noClaim : Prop) :
    AyARCCCacheChain firstLink restLinks finalReport ->
    (firstLink -> restLinks -> finalReport ->
      AyARCCPublicResult satFact unsatFact noClaim) ->
    AyARCCPublicResult satFact unsatFact noClaim :=
  fun chain sound =>
    sound
      (ay_arcc_cache_chain_first firstLink restLinks finalReport chain)
      (ay_arcc_cache_chain_rest firstLink restLinks finalReport chain)
      (ay_arcc_cache_chain_final firstLink restLinks finalReport chain)

theorem ay_arcc_fresh_link_preserves_sat_claim
    (cacheLink rootMatch epochFresh digestMatch satFact : Prop) :
    AyARCCFreshLink cacheLink rootMatch epochFresh digestMatch ->
    (cacheLink -> rootMatch -> epochFresh -> satFact) ->
    satFact :=
  fun fresh sound =>
    sound
      (ay_arcc_fresh_link_cache cacheLink rootMatch epochFresh digestMatch
        fresh)
      (ay_arcc_fresh_link_root cacheLink rootMatch epochFresh digestMatch
        fresh)
      (ay_arcc_fresh_link_epoch cacheLink rootMatch epochFresh digestMatch
        fresh)

theorem ay_arcc_fresh_link_preserves_unsat_claim
    (cacheLink rootMatch epochFresh digestMatch unsatFact : Prop) :
    AyARCCFreshLink cacheLink rootMatch epochFresh digestMatch ->
    (cacheLink -> rootMatch -> epochFresh -> unsatFact) ->
    unsatFact :=
  fun fresh sound =>
    sound
      (ay_arcc_fresh_link_cache cacheLink rootMatch epochFresh digestMatch
        fresh)
      (ay_arcc_fresh_link_root cacheLink rootMatch epochFresh digestMatch
        fresh)
      (ay_arcc_fresh_link_epoch cacheLink rootMatch epochFresh digestMatch
        fresh)

theorem ay_arcc_broken_link_public_result_no_claim
    (satFact unsatFact brokenReason auditDigest diagnostic : Prop) :
    AyARCCBrokenLink brokenReason auditDigest diagnostic ->
    AyARCCPublicResult satFact unsatFact
      (AyARCCNoClaim brokenReason auditDigest diagnostic) :=
  fun broken =>
    ay_arcc_disj_right satFact
      (AyARCCDisj unsatFact
        (AyARCCNoClaim brokenReason auditDigest diagnostic))
      (ay_arcc_disj_right unsatFact
        (AyARCCNoClaim brokenReason auditDigest diagnostic)
        (ay_arcc_broken_link_no_claim brokenReason auditDigest diagnostic
          broken))

theorem ay_arcc_stale_link_public_result_no_claim
    (satFact unsatFact staleEpoch auditDigest diagnostic : Prop) :
    AyARCCStaleLink staleEpoch auditDigest diagnostic ->
    AyARCCPublicResult satFact unsatFact
      (AyARCCNoClaim staleEpoch auditDigest diagnostic) :=
  fun stale =>
    ay_arcc_disj_right satFact
      (AyARCCDisj unsatFact
        (AyARCCNoClaim staleEpoch auditDigest diagnostic))
      (ay_arcc_disj_right unsatFact
        (AyARCCNoClaim staleEpoch auditDigest diagnostic)
        (ay_arcc_stale_link_no_claim staleEpoch auditDigest diagnostic
          stale))

theorem ay_arcc_broken_or_stale_recompute
    (brokenReason staleEpoch auditDigest diagnostic recompute : Prop) :
    AyARCCDisj brokenReason staleEpoch ->
    auditDigest -> diagnostic ->
    (brokenReason ->
      AyARCCRecomputeObligation brokenReason auditDigest diagnostic ->
      recompute) ->
    (staleEpoch ->
      AyARCCRecomputeObligation staleEpoch auditDigest diagnostic ->
      recompute) ->
    recompute :=
  fun failure auditProof diagnosticProof onBroken onStale =>
    failure recompute
      (fun brokenProof =>
        onBroken brokenProof
          (ay_arcc_recompute_intro brokenReason auditDigest diagnostic
            brokenProof auditProof diagnosticProof))
      (fun staleProof =>
        onStale staleProof
          (ay_arcc_recompute_intro staleEpoch auditDigest diagnostic
            staleProof auditProof diagnosticProof))
