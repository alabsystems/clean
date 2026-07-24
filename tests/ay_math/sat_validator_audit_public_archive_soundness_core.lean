-- SAT-COMP validator public audit archive soundness core.
--
-- Public archives may expose SAT/UNSAT reports only when archived root,
-- digest, membership, and cache-chain evidence match.  Stale or broken
-- archive entries are recomputation obligations and no-claim diagnostics.

def AyAPASConj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def AyAPASDisj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyAPASEquisat (before after : Prop) : Prop :=
  AyAPASConj (before -> after) (after -> before)

def AyAPASPublicResult (satFact unsatFact noClaim : Prop) : Prop :=
  AyAPASDisj satFact (AyAPASDisj unsatFact noClaim)

def AyAPASEntry
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    Prop :=
  AyAPASConj exitCode
    (AyAPASConj artifacts
      (AyAPASConj checkerDecision
        (AyAPASConj auditDigest diagnostic)))

def AyAPASMembership (leafHash root entry : Prop) : Prop :=
  AyAPASConj leafHash (AyAPASConj root entry)

def AyAPASArchivedReport
    (archiveDigest reportDigest archivedRoot archivedEntry : Prop) : Prop :=
  AyAPASConj archiveDigest
    (AyAPASConj reportDigest
      (AyAPASConj archivedRoot archivedEntry))

def AyAPASArchiveEvidence
    (rootMatch digestMatch membershipEvidence cacheChain : Prop) : Prop :=
  AyAPASConj rootMatch
    (AyAPASConj digestMatch
      (AyAPASConj membershipEvidence cacheChain))

def AyAPASArchiveHit
    (archivedReport archiveEvidence publicReport : Prop) : Prop :=
  AyAPASConj archivedReport
    (AyAPASConj archiveEvidence publicReport)

def AyAPASStaleArchive (staleDigest auditDigest diagnostic : Prop) : Prop :=
  AyAPASConj staleDigest (AyAPASConj auditDigest diagnostic)

def AyAPASBrokenArchive (brokenLink auditDigest diagnostic : Prop) : Prop :=
  AyAPASConj brokenLink (AyAPASConj auditDigest diagnostic)

def AyAPASRecomputeObligation
    (reason auditDigest diagnostic : Prop) : Prop :=
  AyAPASConj reason (AyAPASConj auditDigest diagnostic)

def AyAPASNoClaim (reason auditDigest diagnostic : Prop) : Prop :=
  AyAPASConj reason (AyAPASConj auditDigest diagnostic)

def AyAPASModel (formula assignment : Prop) : Prop :=
  AyAPASConj formula assignment

def AyAPASUnsat (formula : Prop) : Prop :=
  formula -> False

def AyAPASVisibleSAT (original visibleAssignment : Prop) : Prop :=
  AyAPASModel original visibleAssignment

def AyAPASPreprocessArtifact (original solver : Prop) : Prop :=
  AyAPASEquisat original solver

def AyAPASReplayAccepted (solver stream finalClause : Prop) : Prop :=
  stream -> solver -> finalClause

theorem ay_apas_conj_intro (left right : Prop) :
    left -> right -> AyAPASConj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_apas_conj_left (left right : Prop) :
    AyAPASConj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_apas_conj_right (left right : Prop) :
    AyAPASConj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_apas_disj_right (left right : Prop) :
    right -> AyAPASDisj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_apas_equisat_forward (before after : Prop) :
    AyAPASEquisat before after -> before -> after :=
  fun witness hbefore =>
    witness after (fun forward _backward => forward hbefore)

theorem ay_apas_equisat_backward (before after : Prop) :
    AyAPASEquisat before after -> after -> before :=
  fun witness hafter =>
    witness before (fun _forward backward => backward hafter)

theorem ay_apas_model_intro (formula assignment : Prop) :
    formula -> assignment -> AyAPASModel formula assignment :=
  fun formulaProof assignmentProof =>
    ay_apas_conj_intro formula assignment formulaProof assignmentProof

theorem ay_apas_model_formula (formula assignment : Prop) :
    AyAPASModel formula assignment -> formula :=
  fun model => ay_apas_conj_left formula assignment model

theorem ay_apas_model_assignment (formula assignment : Prop) :
    AyAPASModel formula assignment -> assignment :=
  fun model => ay_apas_conj_right formula assignment model

theorem ay_apas_entry_intro
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    exitCode -> artifacts -> checkerDecision -> auditDigest -> diagnostic ->
    AyAPASEntry exitCode artifacts checkerDecision auditDigest diagnostic :=
  fun exitProof artifactsProof checkerProof auditProof diagnosticProof =>
    ay_apas_conj_intro exitCode
      (AyAPASConj artifacts
        (AyAPASConj checkerDecision (AyAPASConj auditDigest diagnostic)))
      exitProof
      (ay_apas_conj_intro artifacts
        (AyAPASConj checkerDecision (AyAPASConj auditDigest diagnostic))
        artifactsProof
        (ay_apas_conj_intro checkerDecision
          (AyAPASConj auditDigest diagnostic)
          checkerProof
          (ay_apas_conj_intro auditDigest diagnostic auditProof
            diagnosticProof)))

theorem ay_apas_entry_checker
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    AyAPASEntry exitCode artifacts checkerDecision auditDigest diagnostic ->
    checkerDecision :=
  fun entry =>
    ay_apas_conj_right exitCode
      (AyAPASConj artifacts
        (AyAPASConj checkerDecision (AyAPASConj auditDigest diagnostic)))
      entry checkerDecision
      (fun _artifactsProof tail =>
        tail checkerDecision (fun checkerProof _auditTail => checkerProof))

theorem ay_apas_membership_intro (leafHash root entry : Prop) :
    leafHash -> root -> entry -> AyAPASMembership leafHash root entry :=
  fun leafProof rootProof entryProof =>
    ay_apas_conj_intro leafHash (AyAPASConj root entry)
      leafProof
      (ay_apas_conj_intro root entry rootProof entryProof)

theorem ay_apas_membership_entry (leafHash root entry : Prop) :
    AyAPASMembership leafHash root entry -> entry :=
  fun membership =>
    ay_apas_conj_right leafHash (AyAPASConj root entry) membership
      entry (fun _rootProof entryProof => entryProof)

theorem ay_apas_archived_report_intro
    (archiveDigest reportDigest archivedRoot archivedEntry : Prop) :
    archiveDigest -> reportDigest -> archivedRoot -> archivedEntry ->
    AyAPASArchivedReport archiveDigest reportDigest archivedRoot
      archivedEntry :=
  fun archiveProof reportProof rootProof entryProof =>
    ay_apas_conj_intro archiveDigest
      (AyAPASConj reportDigest
        (AyAPASConj archivedRoot archivedEntry))
      archiveProof
      (ay_apas_conj_intro reportDigest
        (AyAPASConj archivedRoot archivedEntry)
        reportProof
        (ay_apas_conj_intro archivedRoot archivedEntry rootProof
          entryProof))

theorem ay_apas_archive_evidence_intro
    (rootMatch digestMatch membershipEvidence cacheChain : Prop) :
    rootMatch -> digestMatch -> membershipEvidence -> cacheChain ->
    AyAPASArchiveEvidence rootMatch digestMatch membershipEvidence
      cacheChain :=
  fun rootProof digestProof membershipProof chainProof =>
    ay_apas_conj_intro rootMatch
      (AyAPASConj digestMatch
        (AyAPASConj membershipEvidence cacheChain))
      rootProof
      (ay_apas_conj_intro digestMatch
        (AyAPASConj membershipEvidence cacheChain)
        digestProof
        (ay_apas_conj_intro membershipEvidence cacheChain
          membershipProof chainProof))

theorem ay_apas_archive_evidence_membership
    (rootMatch digestMatch membershipEvidence cacheChain : Prop) :
    AyAPASArchiveEvidence rootMatch digestMatch membershipEvidence
      cacheChain ->
    membershipEvidence :=
  fun evidence =>
    ay_apas_conj_right rootMatch
      (AyAPASConj digestMatch
        (AyAPASConj membershipEvidence cacheChain))
      evidence membershipEvidence
      (fun _digestProof tail =>
        tail membershipEvidence
          (fun membershipProof _chainProof => membershipProof))

theorem ay_apas_archive_evidence_cache_chain
    (rootMatch digestMatch membershipEvidence cacheChain : Prop) :
    AyAPASArchiveEvidence rootMatch digestMatch membershipEvidence
      cacheChain ->
    cacheChain :=
  fun evidence =>
    ay_apas_conj_right rootMatch
      (AyAPASConj digestMatch
        (AyAPASConj membershipEvidence cacheChain))
      evidence cacheChain
      (fun _digestProof tail =>
        tail cacheChain (fun _membershipProof chainProof => chainProof))

theorem ay_apas_archive_hit_intro
    (archivedReport archiveEvidence publicReport : Prop) :
    archivedReport -> archiveEvidence -> publicReport ->
    AyAPASArchiveHit archivedReport archiveEvidence publicReport :=
  fun reportProof evidenceProof publicProof =>
    ay_apas_conj_intro archivedReport
      (AyAPASConj archiveEvidence publicReport)
      reportProof
      (ay_apas_conj_intro archiveEvidence publicReport evidenceProof
        publicProof)

theorem ay_apas_archive_hit_report
    (archivedReport archiveEvidence publicReport : Prop) :
    AyAPASArchiveHit archivedReport archiveEvidence publicReport ->
    archivedReport :=
  fun hit =>
    ay_apas_conj_left archivedReport
      (AyAPASConj archiveEvidence publicReport) hit

theorem ay_apas_archive_hit_evidence
    (archivedReport archiveEvidence publicReport : Prop) :
    AyAPASArchiveHit archivedReport archiveEvidence publicReport ->
    archiveEvidence :=
  fun hit =>
    ay_apas_conj_right archivedReport
      (AyAPASConj archiveEvidence publicReport)
      hit archiveEvidence (fun evidenceProof _publicProof => evidenceProof)

theorem ay_apas_archive_hit_public
    (archivedReport archiveEvidence publicReport : Prop) :
    AyAPASArchiveHit archivedReport archiveEvidence publicReport ->
    publicReport :=
  fun hit =>
    ay_apas_conj_right archivedReport
      (AyAPASConj archiveEvidence publicReport)
      hit publicReport (fun _evidenceProof publicProof => publicProof)

theorem ay_apas_no_claim_intro
    (reason auditDigest diagnostic : Prop) :
    reason -> auditDigest -> diagnostic ->
    AyAPASNoClaim reason auditDigest diagnostic :=
  fun reasonProof auditProof diagnosticProof =>
    ay_apas_conj_intro reason (AyAPASConj auditDigest diagnostic)
      reasonProof
      (ay_apas_conj_intro auditDigest diagnostic auditProof
        diagnosticProof)

theorem ay_apas_recompute_intro
    (reason auditDigest diagnostic : Prop) :
    reason -> auditDigest -> diagnostic ->
    AyAPASRecomputeObligation reason auditDigest diagnostic :=
  fun reasonProof auditProof diagnosticProof =>
    ay_apas_conj_intro reason (AyAPASConj auditDigest diagnostic)
      reasonProof
      (ay_apas_conj_intro auditDigest diagnostic auditProof
        diagnosticProof)

theorem ay_apas_stale_archive_intro
    (staleDigest auditDigest diagnostic : Prop) :
    staleDigest -> auditDigest -> diagnostic ->
    AyAPASStaleArchive staleDigest auditDigest diagnostic :=
  ay_apas_no_claim_intro staleDigest auditDigest diagnostic

theorem ay_apas_broken_archive_intro
    (brokenLink auditDigest diagnostic : Prop) :
    brokenLink -> auditDigest -> diagnostic ->
    AyAPASBrokenArchive brokenLink auditDigest diagnostic :=
  ay_apas_no_claim_intro brokenLink auditDigest diagnostic

theorem ay_apas_stale_archive_no_claim
    (staleDigest auditDigest diagnostic : Prop) :
    AyAPASStaleArchive staleDigest auditDigest diagnostic ->
    AyAPASNoClaim staleDigest auditDigest diagnostic :=
  fun stale => stale

theorem ay_apas_broken_archive_no_claim
    (brokenLink auditDigest diagnostic : Prop) :
    AyAPASBrokenArchive brokenLink auditDigest diagnostic ->
    AyAPASNoClaim brokenLink auditDigest diagnostic :=
  fun broken => broken

theorem ay_apas_preprocess_model_reconstruct
    (original solver internalAssignment visibleAssignment : Prop) :
    AyAPASPreprocessArtifact original solver ->
    (internalAssignment -> visibleAssignment) ->
    AyAPASModel solver internalAssignment ->
    AyAPASVisibleSAT original visibleAssignment :=
  fun preprocess decode model =>
    ay_apas_model_intro original visibleAssignment
      (ay_apas_equisat_backward original solver preprocess
        (ay_apas_model_formula solver internalAssignment model))
      (decode (ay_apas_model_assignment solver internalAssignment model))

theorem ay_apas_preprocess_unsat_reconstruct
    (original solver : Prop) :
    AyAPASPreprocessArtifact original solver ->
    AyAPASUnsat solver ->
    AyAPASUnsat original :=
  fun preprocess solverUnsat originalProof =>
    solverUnsat
      (ay_apas_equisat_forward original solver preprocess originalProof)

theorem ay_apas_replay_unsat_public
    (original solver stream finalClause : Prop) :
    AyAPASPreprocessArtifact original solver ->
    AyAPASReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    stream ->
    AyAPASUnsat original :=
  fun preprocess replay closeFinal streamProof originalProof =>
    closeFinal
      (replay streamProof
        (ay_apas_equisat_forward original solver preprocess originalProof))

theorem ay_apas_retained_sat_membership_sound
    (leafHash root acceptedSat artifacts satBranch auditDigest diagnostic
      original solver internalAssignment visibleAssignment : Prop) :
    AyAPASPreprocessArtifact original solver ->
    (internalAssignment -> visibleAssignment) ->
    (satBranch -> AyAPASModel solver internalAssignment) ->
    AyAPASMembership leafHash root
      (AyAPASEntry acceptedSat artifacts satBranch auditDigest diagnostic) ->
    AyAPASVisibleSAT original visibleAssignment :=
  fun preprocess decode accept membership =>
    ay_apas_preprocess_model_reconstruct original solver internalAssignment
      visibleAssignment preprocess decode
      (accept
        (ay_apas_entry_checker acceptedSat artifacts satBranch auditDigest
          diagnostic
          (ay_apas_membership_entry leafHash root
            (AyAPASEntry acceptedSat artifacts satBranch auditDigest
              diagnostic)
            membership)))

theorem ay_apas_retained_unsat_membership_sound
    (leafHash root acceptedUnsat artifacts unsatBranch auditDigest diagnostic
      original solver stream finalClause : Prop) :
    AyAPASPreprocessArtifact original solver ->
    AyAPASReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    (unsatBranch -> stream) ->
    AyAPASMembership leafHash root
      (AyAPASEntry acceptedUnsat artifacts unsatBranch auditDigest
        diagnostic) ->
    AyAPASUnsat original :=
  fun preprocess replay closeFinal accept membership =>
    ay_apas_replay_unsat_public original solver stream finalClause preprocess
      replay closeFinal
      (accept
        (ay_apas_entry_checker acceptedUnsat artifacts unsatBranch auditDigest
          diagnostic
          (ay_apas_membership_entry leafHash root
            (AyAPASEntry acceptedUnsat artifacts unsatBranch auditDigest
              diagnostic)
            membership)))

theorem ay_apas_archived_public_report_sound
    (archivedReport archiveEvidence publicReport satFact unsatFact noClaim :
      Prop) :
    AyAPASArchiveHit archivedReport archiveEvidence publicReport ->
    (archivedReport -> archiveEvidence -> publicReport ->
      AyAPASPublicResult satFact unsatFact noClaim) ->
    AyAPASPublicResult satFact unsatFact noClaim :=
  fun hit sound =>
    sound
      (ay_apas_archive_hit_report archivedReport archiveEvidence publicReport
        hit)
      (ay_apas_archive_hit_evidence archivedReport archiveEvidence
        publicReport hit)
      (ay_apas_archive_hit_public archivedReport archiveEvidence
        publicReport hit)

theorem ay_apas_archived_public_report_preserves_sat
    (archivedReport archiveEvidence publicReport satFact : Prop) :
    AyAPASArchiveHit archivedReport archiveEvidence publicReport ->
    (archiveEvidence -> publicReport -> satFact) ->
    satFact :=
  fun hit sound =>
    sound
      (ay_apas_archive_hit_evidence archivedReport archiveEvidence
        publicReport hit)
      (ay_apas_archive_hit_public archivedReport archiveEvidence
        publicReport hit)

theorem ay_apas_archived_public_report_preserves_unsat
    (archivedReport archiveEvidence publicReport unsatFact : Prop) :
    AyAPASArchiveHit archivedReport archiveEvidence publicReport ->
    (archiveEvidence -> publicReport -> unsatFact) ->
    unsatFact :=
  fun hit sound =>
    sound
      (ay_apas_archive_hit_evidence archivedReport archiveEvidence
        publicReport hit)
      (ay_apas_archive_hit_public archivedReport archiveEvidence
        publicReport hit)

theorem ay_apas_stale_archive_public_result_no_claim
    (satFact unsatFact staleDigest auditDigest diagnostic : Prop) :
    AyAPASStaleArchive staleDigest auditDigest diagnostic ->
    AyAPASPublicResult satFact unsatFact
      (AyAPASNoClaim staleDigest auditDigest diagnostic) :=
  fun stale =>
    ay_apas_disj_right satFact
      (AyAPASDisj unsatFact
        (AyAPASNoClaim staleDigest auditDigest diagnostic))
      (ay_apas_disj_right unsatFact
        (AyAPASNoClaim staleDigest auditDigest diagnostic)
        (ay_apas_stale_archive_no_claim staleDigest auditDigest diagnostic
          stale))

theorem ay_apas_broken_archive_public_result_no_claim
    (satFact unsatFact brokenLink auditDigest diagnostic : Prop) :
    AyAPASBrokenArchive brokenLink auditDigest diagnostic ->
    AyAPASPublicResult satFact unsatFact
      (AyAPASNoClaim brokenLink auditDigest diagnostic) :=
  fun broken =>
    ay_apas_disj_right satFact
      (AyAPASDisj unsatFact
        (AyAPASNoClaim brokenLink auditDigest diagnostic))
      (ay_apas_disj_right unsatFact
        (AyAPASNoClaim brokenLink auditDigest diagnostic)
        (ay_apas_broken_archive_no_claim brokenLink auditDigest diagnostic
          broken))

theorem ay_apas_stale_or_broken_archive_recompute
    (staleDigest brokenLink auditDigest diagnostic recompute : Prop) :
    AyAPASDisj staleDigest brokenLink ->
    auditDigest -> diagnostic ->
    (staleDigest ->
      AyAPASRecomputeObligation staleDigest auditDigest diagnostic ->
      recompute) ->
    (brokenLink ->
      AyAPASRecomputeObligation brokenLink auditDigest diagnostic ->
      recompute) ->
    recompute :=
  fun failure auditProof diagnosticProof onStale onBroken =>
    failure recompute
      (fun staleProof =>
        onStale staleProof
          (ay_apas_recompute_intro staleDigest auditDigest diagnostic
            staleProof auditProof diagnosticProof))
      (fun brokenProof =>
        onBroken brokenProof
          (ay_apas_recompute_intro brokenLink auditDigest diagnostic
            brokenProof auditProof diagnosticProof))
