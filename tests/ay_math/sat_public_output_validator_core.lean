-- SAT-COMP public output validator core.
--
-- This self-contained package models the public boundary for ay output:
-- SAT/UNSAT/UNKNOWN tokens, certificate availability, compressed indexed
-- outcome lookup, branch checker acceptance, preprocessing reconstruction, and
-- archive consistency for UNKNOWN.

def AyPOVConj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def AyPOVDisj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyPOVEquisat (before after : Prop) : Prop :=
  AyPOVConj (before -> after) (after -> before)

def AyPOVOutcome (sat unsat : Prop) : Prop :=
  AyPOVDisj sat unsat

def AyPOVPublicOutput (satToken unsatToken unknownToken : Prop) : Prop :=
  AyPOVDisj satToken (AyPOVDisj unsatToken unknownToken)

def AyPOVCompressed (payload : Prop) : Prop :=
  payload

def AyPOVIndexed (index payload : Prop) : Prop :=
  AyPOVConj index payload

def AyPOVCertificateAvailable (token index archive : Prop) : Prop :=
  AyPOVConj token (AyPOVConj index archive)

def AyPOVArchiveConsistent (archive : Prop) : Prop :=
  archive

def AyPOVModel (formula assignment : Prop) : Prop :=
  AyPOVConj formula assignment

def AyPOVUnsat (formula : Prop) : Prop :=
  formula -> False

def AyPOVVisibleSAT (original visibleAssignment : Prop) : Prop :=
  AyPOVModel original visibleAssignment

def AyPOVReplayAccepted (solver stream finalClause : Prop) : Prop :=
  stream -> solver -> finalClause

def AyPOVSatChecker (branch visibleSat : Prop) : Prop :=
  branch -> visibleSat

def AyPOVUnsatChecker (branch publicUnsat : Prop) : Prop :=
  branch -> publicUnsat

def AyPOVPreprocessArtifact (original solver : Prop) : Prop :=
  AyPOVEquisat original solver

def AyPOVValidated (satFact unsatFact archiveFact : Prop) : Prop :=
  AyPOVDisj satFact (AyPOVDisj unsatFact archiveFact)

theorem ay_pov_conj_intro (left right : Prop) :
    left -> right -> AyPOVConj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_pov_conj_left (left right : Prop) :
    AyPOVConj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_pov_conj_right (left right : Prop) :
    AyPOVConj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_pov_disj_left (left right : Prop) :
    left -> AyPOVDisj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_pov_disj_right (left right : Prop) :
    right -> AyPOVDisj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_pov_equisat_forward (before after : Prop) :
    AyPOVEquisat before after -> before -> after :=
  fun witness hbefore =>
    witness after (fun forward _backward => forward hbefore)

theorem ay_pov_equisat_backward (before after : Prop) :
    AyPOVEquisat before after -> after -> before :=
  fun witness hafter =>
    witness before (fun _forward backward => backward hafter)

theorem ay_pov_model_intro (formula assignment : Prop) :
    formula -> assignment -> AyPOVModel formula assignment :=
  fun formulaProof assignmentProof =>
    ay_pov_conj_intro formula assignment formulaProof assignmentProof

theorem ay_pov_model_formula (formula assignment : Prop) :
    AyPOVModel formula assignment -> formula :=
  fun model => ay_pov_conj_left formula assignment model

theorem ay_pov_model_assignment (formula assignment : Prop) :
    AyPOVModel formula assignment -> assignment :=
  fun model => ay_pov_conj_right formula assignment model

theorem ay_pov_compressed_expand (payload : Prop) :
    AyPOVCompressed payload -> payload :=
  fun compressed => compressed

theorem ay_pov_compressed_pack (payload : Prop) :
    payload -> AyPOVCompressed payload :=
  fun payloadProof => payloadProof

theorem ay_pov_indexed_intro (index payload : Prop) :
    index -> payload -> AyPOVIndexed index payload :=
  fun indexProof payloadProof =>
    ay_pov_conj_intro index payload indexProof payloadProof

theorem ay_pov_indexed_index (index payload : Prop) :
    AyPOVIndexed index payload -> index :=
  fun indexed => ay_pov_conj_left index payload indexed

theorem ay_pov_indexed_payload (index payload : Prop) :
    AyPOVIndexed index payload -> payload :=
  fun indexed => ay_pov_conj_right index payload indexed

theorem ay_pov_indexed_compressed_lookup (index payload : Prop) :
    AyPOVIndexed index (AyPOVCompressed payload) ->
    index ->
    payload :=
  fun indexed _indexProof =>
    ay_pov_compressed_expand payload
      (ay_pov_indexed_payload index (AyPOVCompressed payload) indexed)

theorem ay_pov_certificate_token (token index archive : Prop) :
    AyPOVCertificateAvailable token index archive -> token :=
  fun available => ay_pov_conj_left token (AyPOVConj index archive) available

theorem ay_pov_certificate_index (token index archive : Prop) :
    AyPOVCertificateAvailable token index archive -> index :=
  fun available =>
    ay_pov_conj_right token (AyPOVConj index archive) available
      index (fun indexProof _archiveProof => indexProof)

theorem ay_pov_certificate_archive (token index archive : Prop) :
    AyPOVCertificateAvailable token index archive ->
    AyPOVArchiveConsistent archive :=
  fun available =>
    ay_pov_conj_right token (AyPOVConj index archive) available
      archive (fun _indexProof archiveProof => archiveProof)

theorem ay_pov_outcome_map
    (beforeSat afterSat beforeUnsat afterUnsat : Prop) :
    (beforeSat -> afterSat) ->
    (beforeUnsat -> afterUnsat) ->
    AyPOVOutcome beforeSat beforeUnsat ->
    AyPOVOutcome afterSat afterUnsat :=
  fun satMap unsatMap outcome result onSat onUnsat =>
    outcome result
      (fun satProof => onSat (satMap satProof))
      (fun unsatProof => onUnsat (unsatMap unsatProof))

theorem ay_pov_preprocess_model_reconstruct
    (original solver internalAssignment visibleAssignment : Prop) :
    AyPOVPreprocessArtifact original solver ->
    (internalAssignment -> visibleAssignment) ->
    AyPOVModel solver internalAssignment ->
    AyPOVVisibleSAT original visibleAssignment :=
  fun preprocess decode model =>
    ay_pov_model_intro original visibleAssignment
      (ay_pov_equisat_backward original solver preprocess
        (ay_pov_model_formula solver internalAssignment model))
      (decode (ay_pov_model_assignment solver internalAssignment model))

theorem ay_pov_preprocess_unsat_reconstruct
    (original solver : Prop) :
    AyPOVPreprocessArtifact original solver ->
    AyPOVUnsat solver ->
    AyPOVUnsat original :=
  fun preprocess solverUnsat originalProof =>
    solverUnsat
      (ay_pov_equisat_forward original solver preprocess originalProof)

theorem ay_pov_unsat_replay_solver
    (solver stream finalClause : Prop) :
    AyPOVReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    stream ->
    AyPOVUnsat solver :=
  fun replay closeFinal streamProof solverProof =>
    closeFinal (replay streamProof solverProof)

theorem ay_pov_unsat_replay_public
    (original solver stream finalClause : Prop) :
    AyPOVPreprocessArtifact original solver ->
    AyPOVReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    stream ->
    AyPOVUnsat original :=
  fun preprocess replay closeFinal streamProof =>
    ay_pov_preprocess_unsat_reconstruct original solver preprocess
      (ay_pov_unsat_replay_solver solver stream finalClause replay
        closeFinal streamProof)

theorem ay_pov_sat_checker_public
    (original solver internalAssignment visibleAssignment satBranch : Prop) :
    AyPOVPreprocessArtifact original solver ->
    (internalAssignment -> visibleAssignment) ->
    (satBranch -> AyPOVModel solver internalAssignment) ->
    AyPOVSatChecker satBranch
      (AyPOVVisibleSAT original visibleAssignment) :=
  fun preprocess decode accept branchProof =>
    ay_pov_preprocess_model_reconstruct original solver internalAssignment
      visibleAssignment preprocess decode (accept branchProof)

theorem ay_pov_unsat_checker_public
    (original solver stream finalClause unsatBranch : Prop) :
    AyPOVPreprocessArtifact original solver ->
    AyPOVReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    (unsatBranch -> stream) ->
    AyPOVUnsatChecker unsatBranch (AyPOVUnsat original) :=
  fun preprocess replay closeFinal accept branchProof =>
    ay_pov_unsat_replay_public original solver stream finalClause
      preprocess replay closeFinal (accept branchProof)

theorem ay_pov_indexed_checked_outcome
    (index satBranch unsatBranch publicSat publicUnsat : Prop) :
    AyPOVSatChecker satBranch publicSat ->
    AyPOVUnsatChecker unsatBranch publicUnsat ->
    AyPOVIndexed index
      (AyPOVCompressed (AyPOVOutcome satBranch unsatBranch)) ->
    index ->
    AyPOVOutcome publicSat publicUnsat :=
  fun satChecker unsatChecker indexed indexProof =>
    ay_pov_outcome_map satBranch publicSat unsatBranch publicUnsat
      satChecker unsatChecker
      (ay_pov_indexed_compressed_lookup index
        (AyPOVOutcome satBranch unsatBranch) indexed indexProof)

theorem ay_pov_sat_output_sound
    (satToken archive index original solver internalAssignment
      visibleAssignment satBranch unsatBranch : Prop) :
    AyPOVCertificateAvailable satToken index archive ->
    AyPOVPreprocessArtifact original solver ->
    (internalAssignment -> visibleAssignment) ->
    (satBranch -> AyPOVModel solver internalAssignment) ->
    AyPOVIndexed index
      (AyPOVCompressed (AyPOVOutcome satBranch unsatBranch)) ->
    satBranch ->
    AyPOVVisibleSAT original visibleAssignment :=
  fun _available preprocess decode accept _indexed branchProof =>
    ay_pov_sat_checker_public original solver internalAssignment
      visibleAssignment satBranch preprocess decode accept branchProof

theorem ay_pov_unsat_output_sound
    (unsatToken archive index original solver stream finalClause satBranch
      unsatBranch : Prop) :
    AyPOVCertificateAvailable unsatToken index archive ->
    AyPOVPreprocessArtifact original solver ->
    AyPOVReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    (unsatBranch -> stream) ->
    AyPOVIndexed index
      (AyPOVCompressed (AyPOVOutcome satBranch unsatBranch)) ->
    unsatBranch ->
    AyPOVUnsat original :=
  fun _available preprocess replay closeFinal accept _indexed branchProof =>
    ay_pov_unsat_checker_public original solver stream finalClause
      unsatBranch preprocess replay closeFinal accept branchProof

theorem ay_pov_unknown_output_archive_consistent
    (unknownToken index archive : Prop) :
    AyPOVCertificateAvailable unknownToken index archive ->
    AyPOVArchiveConsistent archive :=
  fun available => ay_pov_certificate_archive unknownToken index archive available

theorem ay_pov_public_output_validator
    (satToken unsatToken unknownToken archive original visibleAssignment :
      Prop) :
    (satToken -> AyPOVVisibleSAT original visibleAssignment) ->
    (unsatToken -> AyPOVUnsat original) ->
    (unknownToken -> AyPOVArchiveConsistent archive) ->
    AyPOVPublicOutput satToken unsatToken unknownToken ->
    AyPOVValidated
      (AyPOVVisibleSAT original visibleAssignment)
      (AyPOVUnsat original)
      (AyPOVArchiveConsistent archive) :=
  fun satSound unsatSound unknownArchive output result onSat onRest =>
    output result
      (fun satTokenProof => onSat (satSound satTokenProof))
      (fun rest =>
        rest result
          (fun unsatTokenProof =>
            onRest
              (ay_pov_disj_left
                (AyPOVUnsat original)
                (AyPOVArchiveConsistent archive)
                (unsatSound unsatTokenProof)))
          (fun unknownTokenProof =>
            onRest
              (ay_pov_disj_right
                (AyPOVUnsat original)
                (AyPOVArchiveConsistent archive)
                (unknownArchive unknownTokenProof))))
