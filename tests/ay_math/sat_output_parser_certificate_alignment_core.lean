-- SAT-COMP output parser / certificate alignment core.
--
-- This file models the public text-output layer abstractly: parsed
-- SAT/UNSAT/UNKNOWN tokens, certificate ids, archive keys, compressed indexed
-- outcomes, branch checker obligations, and validator dispatch.

def AyPCAConj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def AyPCADisj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyPCAEquisat (before after : Prop) : Prop :=
  AyPCAConj (before -> after) (after -> before)

def AyPCAParsedOutput (satToken unsatToken unknownToken : Prop) : Prop :=
  AyPCADisj satToken (AyPCADisj unsatToken unknownToken)

def AyPCAOutcome (sat unsat : Prop) : Prop :=
  AyPCADisj sat unsat

def AyPCACompressed (payload : Prop) : Prop :=
  payload

def AyPCAIndexed (index payload : Prop) : Prop :=
  AyPCAConj index payload

def AyPCACertKey (certId archiveKey : Prop) : Prop :=
  AyPCAConj certId archiveKey

def AyPCAManifestConsistent (archiveKey : Prop) : Prop :=
  archiveKey

def AyPCAModel (formula assignment : Prop) : Prop :=
  AyPCAConj formula assignment

def AyPCAUnsat (formula : Prop) : Prop :=
  formula -> False

def AyPCAVisibleSAT (original visibleAssignment : Prop) : Prop :=
  AyPCAModel original visibleAssignment

def AyPCASatChecker (branch visibleSat : Prop) : Prop :=
  branch -> visibleSat

def AyPCAUnsatChecker (branch publicUnsat : Prop) : Prop :=
  branch -> publicUnsat

def AyPCASatDispatch (satToken certId archiveKey satBranch : Prop) : Prop :=
  AyPCAConj satToken (AyPCAConj (AyPCACertKey certId archiveKey) satBranch)

def AyPCAUnsatDispatch
    (unsatToken certId archiveKey unsatBranch : Prop) : Prop :=
  AyPCAConj unsatToken
    (AyPCAConj (AyPCACertKey certId archiveKey) unsatBranch)

def AyPCAUnknownDispatch (unknownToken archiveKey : Prop) : Prop :=
  AyPCAConj unknownToken (AyPCAManifestConsistent archiveKey)

def AyPCAValidated (satFact unsatFact manifestFact : Prop) : Prop :=
  AyPCADisj satFact (AyPCADisj unsatFact manifestFact)

theorem ay_pca_conj_intro (left right : Prop) :
    left -> right -> AyPCAConj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_pca_conj_left (left right : Prop) :
    AyPCAConj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_pca_conj_right (left right : Prop) :
    AyPCAConj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_pca_disj_left (left right : Prop) :
    left -> AyPCADisj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_pca_disj_right (left right : Prop) :
    right -> AyPCADisj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_pca_equisat_forward (before after : Prop) :
    AyPCAEquisat before after -> before -> after :=
  fun witness hbefore =>
    witness after (fun forward _backward => forward hbefore)

theorem ay_pca_equisat_backward (before after : Prop) :
    AyPCAEquisat before after -> after -> before :=
  fun witness hafter =>
    witness before (fun _forward backward => backward hafter)

theorem ay_pca_model_intro (formula assignment : Prop) :
    formula -> assignment -> AyPCAModel formula assignment :=
  fun formulaProof assignmentProof =>
    ay_pca_conj_intro formula assignment formulaProof assignmentProof

theorem ay_pca_model_formula (formula assignment : Prop) :
    AyPCAModel formula assignment -> formula :=
  fun model => ay_pca_conj_left formula assignment model

theorem ay_pca_model_assignment (formula assignment : Prop) :
    AyPCAModel formula assignment -> assignment :=
  fun model => ay_pca_conj_right formula assignment model

theorem ay_pca_compressed_expand (payload : Prop) :
    AyPCACompressed payload -> payload :=
  fun compressed => compressed

theorem ay_pca_compressed_pack (payload : Prop) :
    payload -> AyPCACompressed payload :=
  fun payloadProof => payloadProof

theorem ay_pca_indexed_intro (index payload : Prop) :
    index -> payload -> AyPCAIndexed index payload :=
  fun indexProof payloadProof =>
    ay_pca_conj_intro index payload indexProof payloadProof

theorem ay_pca_indexed_index (index payload : Prop) :
    AyPCAIndexed index payload -> index :=
  fun indexed => ay_pca_conj_left index payload indexed

theorem ay_pca_indexed_payload (index payload : Prop) :
    AyPCAIndexed index payload -> payload :=
  fun indexed => ay_pca_conj_right index payload indexed

theorem ay_pca_indexed_compressed_lookup (index payload : Prop) :
    AyPCAIndexed index (AyPCACompressed payload) ->
    index ->
    payload :=
  fun indexed _indexProof =>
    ay_pca_compressed_expand payload
      (ay_pca_indexed_payload index (AyPCACompressed payload) indexed)

theorem ay_pca_cert_key_intro (certId archiveKey : Prop) :
    certId -> archiveKey -> AyPCACertKey certId archiveKey :=
  ay_pca_conj_intro certId archiveKey

theorem ay_pca_cert_key_id (certId archiveKey : Prop) :
    AyPCACertKey certId archiveKey -> certId :=
  ay_pca_conj_left certId archiveKey

theorem ay_pca_cert_key_archive (certId archiveKey : Prop) :
    AyPCACertKey certId archiveKey -> AyPCAManifestConsistent archiveKey :=
  ay_pca_conj_right certId archiveKey

theorem ay_pca_outcome_map
    (beforeSat afterSat beforeUnsat afterUnsat : Prop) :
    (beforeSat -> afterSat) ->
    (beforeUnsat -> afterUnsat) ->
    AyPCAOutcome beforeSat beforeUnsat ->
    AyPCAOutcome afterSat afterUnsat :=
  fun satMap unsatMap outcome result onSat onUnsat =>
    outcome result
      (fun satProof => onSat (satMap satProof))
      (fun unsatProof => onUnsat (unsatMap unsatProof))

theorem ay_pca_sat_dispatch_token
    (satToken certId archiveKey satBranch : Prop) :
    AyPCASatDispatch satToken certId archiveKey satBranch -> satToken :=
  fun dispatch =>
    ay_pca_conj_left satToken
      (AyPCAConj (AyPCACertKey certId archiveKey) satBranch) dispatch

theorem ay_pca_sat_dispatch_key
    (satToken certId archiveKey satBranch : Prop) :
    AyPCASatDispatch satToken certId archiveKey satBranch ->
    AyPCACertKey certId archiveKey :=
  fun dispatch =>
    ay_pca_conj_right satToken
      (AyPCAConj (AyPCACertKey certId archiveKey) satBranch) dispatch
      (AyPCACertKey certId archiveKey)
      (fun keyProof _branchProof => keyProof)

theorem ay_pca_sat_dispatch_branch
    (satToken certId archiveKey satBranch : Prop) :
    AyPCASatDispatch satToken certId archiveKey satBranch -> satBranch :=
  fun dispatch =>
    ay_pca_conj_right satToken
      (AyPCAConj (AyPCACertKey certId archiveKey) satBranch) dispatch
      satBranch (fun _keyProof branchProof => branchProof)

theorem ay_pca_unsat_dispatch_token
    (unsatToken certId archiveKey unsatBranch : Prop) :
    AyPCAUnsatDispatch unsatToken certId archiveKey unsatBranch ->
    unsatToken :=
  fun dispatch =>
    ay_pca_conj_left unsatToken
      (AyPCAConj (AyPCACertKey certId archiveKey) unsatBranch) dispatch

theorem ay_pca_unsat_dispatch_key
    (unsatToken certId archiveKey unsatBranch : Prop) :
    AyPCAUnsatDispatch unsatToken certId archiveKey unsatBranch ->
    AyPCACertKey certId archiveKey :=
  fun dispatch =>
    ay_pca_conj_right unsatToken
      (AyPCAConj (AyPCACertKey certId archiveKey) unsatBranch) dispatch
      (AyPCACertKey certId archiveKey)
      (fun keyProof _branchProof => keyProof)

theorem ay_pca_unsat_dispatch_branch
    (unsatToken certId archiveKey unsatBranch : Prop) :
    AyPCAUnsatDispatch unsatToken certId archiveKey unsatBranch ->
    unsatBranch :=
  fun dispatch =>
    ay_pca_conj_right unsatToken
      (AyPCAConj (AyPCACertKey certId archiveKey) unsatBranch) dispatch
      unsatBranch (fun _keyProof branchProof => branchProof)

theorem ay_pca_unknown_manifest
    (unknownToken archiveKey : Prop) :
    AyPCAUnknownDispatch unknownToken archiveKey ->
    AyPCAManifestConsistent archiveKey :=
  fun dispatch =>
    ay_pca_conj_right unknownToken
      (AyPCAManifestConsistent archiveKey) dispatch

theorem ay_pca_sat_dispatch_sound
    (satToken certId archiveKey satBranch visibleSat : Prop) :
    AyPCASatChecker satBranch visibleSat ->
    AyPCASatDispatch satToken certId archiveKey satBranch ->
    visibleSat :=
  fun checker dispatch =>
    checker
      (ay_pca_sat_dispatch_branch satToken certId archiveKey satBranch
        dispatch)

theorem ay_pca_unsat_dispatch_sound
    (unsatToken certId archiveKey unsatBranch publicUnsat : Prop) :
    AyPCAUnsatChecker unsatBranch publicUnsat ->
    AyPCAUnsatDispatch unsatToken certId archiveKey unsatBranch ->
    publicUnsat :=
  fun checker dispatch =>
    checker
      (ay_pca_unsat_dispatch_branch unsatToken certId archiveKey unsatBranch
        dispatch)

theorem ay_pca_sat_dispatch_exact
    (satToken certId archiveKey satBranch visibleSat : Prop) :
    AyPCASatChecker satBranch visibleSat ->
    (visibleSat -> AyPCASatDispatch satToken certId archiveKey satBranch) ->
    AyPCAEquisat
      (AyPCASatDispatch satToken certId archiveKey satBranch)
      visibleSat :=
  fun checker reconstruct =>
    ay_pca_conj_intro
      (AyPCASatDispatch satToken certId archiveKey satBranch -> visibleSat)
      (visibleSat ->
        AyPCASatDispatch satToken certId archiveKey satBranch)
      (ay_pca_sat_dispatch_sound satToken certId archiveKey satBranch
        visibleSat checker)
      reconstruct

theorem ay_pca_unsat_dispatch_exact
    (unsatToken certId archiveKey unsatBranch publicUnsat : Prop) :
    AyPCAUnsatChecker unsatBranch publicUnsat ->
    (publicUnsat ->
      AyPCAUnsatDispatch unsatToken certId archiveKey unsatBranch) ->
    AyPCAEquisat
      (AyPCAUnsatDispatch unsatToken certId archiveKey unsatBranch)
      publicUnsat :=
  fun checker reconstruct =>
    ay_pca_conj_intro
      (AyPCAUnsatDispatch unsatToken certId archiveKey unsatBranch ->
        publicUnsat)
      (publicUnsat ->
        AyPCAUnsatDispatch unsatToken certId archiveKey unsatBranch)
      (ay_pca_unsat_dispatch_sound unsatToken certId archiveKey unsatBranch
        publicUnsat checker)
      reconstruct

theorem ay_pca_indexed_outcome_to_sat_dispatch
    (index satToken certId archiveKey satBranch unsatBranch : Prop) :
    AyPCAIndexed index
      (AyPCACompressed (AyPCAOutcome satBranch unsatBranch)) ->
    index ->
    satToken ->
    AyPCACertKey certId archiveKey ->
    satBranch ->
    AyPCASatDispatch satToken certId archiveKey satBranch :=
  fun _indexed _indexProof satProof keyProof branchProof =>
    ay_pca_conj_intro satToken
      (AyPCAConj (AyPCACertKey certId archiveKey) satBranch)
      satProof
      (ay_pca_conj_intro (AyPCACertKey certId archiveKey) satBranch
        keyProof branchProof)

theorem ay_pca_indexed_outcome_to_unsat_dispatch
    (index unsatToken certId archiveKey satBranch unsatBranch : Prop) :
    AyPCAIndexed index
      (AyPCACompressed (AyPCAOutcome satBranch unsatBranch)) ->
    index ->
    unsatToken ->
    AyPCACertKey certId archiveKey ->
    unsatBranch ->
    AyPCAUnsatDispatch unsatToken certId archiveKey unsatBranch :=
  fun _indexed _indexProof unsatProof keyProof branchProof =>
    ay_pca_conj_intro unsatToken
      (AyPCAConj (AyPCACertKey certId archiveKey) unsatBranch)
      unsatProof
      (ay_pca_conj_intro (AyPCACertKey certId archiveKey) unsatBranch
        keyProof branchProof)

theorem ay_pca_validation_dispatch
    (satToken unsatToken unknownToken certId archiveKey satBranch unsatBranch
      visibleSat publicUnsat : Prop) :
    AyPCASatChecker satBranch visibleSat ->
    AyPCAUnsatChecker unsatBranch publicUnsat ->
    AyPCASatDispatch satToken certId archiveKey satBranch ->
    AyPCAUnsatDispatch unsatToken certId archiveKey unsatBranch ->
    AyPCAUnknownDispatch unknownToken archiveKey ->
    AyPCAParsedOutput satToken unsatToken unknownToken ->
    AyPCAValidated visibleSat publicUnsat
      (AyPCAManifestConsistent archiveKey) :=
  fun satChecker unsatChecker satDispatch unsatDispatch unknownDispatch
      parsed result onSat onRest =>
    parsed result
      (fun _satProof =>
        onSat
          (ay_pca_sat_dispatch_sound satToken certId archiveKey satBranch
            visibleSat satChecker satDispatch))
      (fun rest =>
        rest result
          (fun _unsatProof =>
            onRest
              (ay_pca_disj_left publicUnsat
                (AyPCAManifestConsistent archiveKey)
                (ay_pca_unsat_dispatch_sound unsatToken certId archiveKey
                  unsatBranch publicUnsat unsatChecker unsatDispatch)))
          (fun _unknownProof =>
            onRest
              (ay_pca_disj_right publicUnsat
                (AyPCAManifestConsistent archiveKey)
                (ay_pca_unknown_manifest unknownToken archiveKey
                  unknownDispatch))))

theorem ay_pca_unknown_no_semantic_claim
    (unknownToken archiveKey visibleSat publicUnsat : Prop) :
    AyPCAUnknownDispatch unknownToken archiveKey ->
    AyPCAValidated visibleSat publicUnsat
      (AyPCAManifestConsistent archiveKey) :=
  fun unknownDispatch =>
    ay_pca_disj_right visibleSat
      (AyPCADisj publicUnsat (AyPCAManifestConsistent archiveKey))
      (ay_pca_disj_right publicUnsat
        (AyPCAManifestConsistent archiveKey)
        (ay_pca_unknown_manifest unknownToken archiveKey unknownDispatch))
