-- SAT-COMP top checker contract core.
--
-- This self-contained package models the public checker boundary for ay: an
-- indexed compressed solver outcome is looked up, the selected SAT or UNSAT
-- branch checker accepts, and preprocessing artifacts transport the accepted
-- branch back to the original CNF obligation.

def AyTCCConj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def AyTCCDisj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyTCCEquisat (before after : Prop) : Prop :=
  AyTCCConj (before -> after) (after -> before)

def AyTCCOutcome (sat unsat : Prop) : Prop :=
  AyTCCDisj sat unsat

def AyTCCCompressed (payload : Prop) : Prop :=
  payload

def AyTCCIndexed (index payload : Prop) : Prop :=
  AyTCCConj index payload

def AyTCCLookup (index payload : Prop) : Prop :=
  index -> payload

def AyTCCModel (formula assignment : Prop) : Prop :=
  AyTCCConj formula assignment

def AyTCCUnsat (formula : Prop) : Prop :=
  formula -> False

def AyTCCVisibleSAT (original visibleAssignment : Prop) : Prop :=
  AyTCCModel original visibleAssignment

def AyTCCReplayAccepted (solver stream finalClause : Prop) : Prop :=
  stream -> solver -> finalClause

def AyTCCSatChecker (branch visibleSat : Prop) : Prop :=
  branch -> visibleSat

def AyTCCUnsatChecker (branch publicUnsat : Prop) : Prop :=
  branch -> publicUnsat

def AyTCCPreprocessArtifact (original solver : Prop) : Prop :=
  AyTCCEquisat original solver

theorem ay_tcc_conj_intro (left right : Prop) :
    left -> right -> AyTCCConj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_tcc_conj_left (left right : Prop) :
    AyTCCConj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_tcc_conj_right (left right : Prop) :
    AyTCCConj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_tcc_disj_left (left right : Prop) :
    left -> AyTCCDisj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_tcc_disj_right (left right : Prop) :
    right -> AyTCCDisj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_tcc_equisat_forward (before after : Prop) :
    AyTCCEquisat before after -> before -> after :=
  fun witness hbefore =>
    witness after (fun forward _backward => forward hbefore)

theorem ay_tcc_equisat_backward (before after : Prop) :
    AyTCCEquisat before after -> after -> before :=
  fun witness hafter =>
    witness before (fun _forward backward => backward hafter)

theorem ay_tcc_equisat_refl (formula : Prop) :
    AyTCCEquisat formula formula :=
  ay_tcc_conj_intro (formula -> formula) (formula -> formula)
    (fun h => h) (fun h => h)

theorem ay_tcc_model_intro (formula assignment : Prop) :
    formula -> assignment -> AyTCCModel formula assignment :=
  fun formulaProof assignmentProof =>
    ay_tcc_conj_intro formula assignment formulaProof assignmentProof

theorem ay_tcc_model_formula (formula assignment : Prop) :
    AyTCCModel formula assignment -> formula :=
  fun model => ay_tcc_conj_left formula assignment model

theorem ay_tcc_model_assignment (formula assignment : Prop) :
    AyTCCModel formula assignment -> assignment :=
  fun model => ay_tcc_conj_right formula assignment model

theorem ay_tcc_compressed_expand (payload : Prop) :
    AyTCCCompressed payload -> payload :=
  fun compressed => compressed

theorem ay_tcc_compressed_pack (payload : Prop) :
    payload -> AyTCCCompressed payload :=
  fun payloadProof => payloadProof

theorem ay_tcc_indexed_intro (index payload : Prop) :
    index -> payload -> AyTCCIndexed index payload :=
  fun indexProof payloadProof =>
    ay_tcc_conj_intro index payload indexProof payloadProof

theorem ay_tcc_indexed_index (index payload : Prop) :
    AyTCCIndexed index payload -> index :=
  fun indexed => ay_tcc_conj_left index payload indexed

theorem ay_tcc_indexed_payload (index payload : Prop) :
    AyTCCIndexed index payload -> payload :=
  fun indexed => ay_tcc_conj_right index payload indexed

theorem ay_tcc_lookup_from_indexed (index payload : Prop) :
    AyTCCIndexed index payload -> AyTCCLookup index payload :=
  fun indexed _indexProof => ay_tcc_indexed_payload index payload indexed

theorem ay_tcc_indexed_compressed_lookup (index payload : Prop) :
    AyTCCIndexed index (AyTCCCompressed payload) ->
    index ->
    payload :=
  fun indexed indexProof =>
    ay_tcc_compressed_expand payload
      (ay_tcc_lookup_from_indexed index (AyTCCCompressed payload) indexed
        indexProof)

theorem ay_tcc_outcome_map
    (beforeSat afterSat beforeUnsat afterUnsat : Prop) :
    (beforeSat -> afterSat) ->
    (beforeUnsat -> afterUnsat) ->
    AyTCCOutcome beforeSat beforeUnsat ->
    AyTCCOutcome afterSat afterUnsat :=
  fun satMap unsatMap outcome result onSat onUnsat =>
    outcome result
      (fun satProof => onSat (satMap satProof))
      (fun unsatProof => onUnsat (unsatMap unsatProof))

theorem ay_tcc_sat_checker_accepts
    (branch visibleSat : Prop) :
    AyTCCSatChecker branch visibleSat -> branch -> visibleSat :=
  fun checker branchProof => checker branchProof

theorem ay_tcc_unsat_checker_accepts
    (branch publicUnsat : Prop) :
    AyTCCUnsatChecker branch publicUnsat -> branch -> publicUnsat :=
  fun checker branchProof => checker branchProof

theorem ay_tcc_preprocess_model_reconstruct
    (original solver internalAssignment visibleAssignment : Prop) :
    AyTCCPreprocessArtifact original solver ->
    (internalAssignment -> visibleAssignment) ->
    AyTCCModel solver internalAssignment ->
    AyTCCVisibleSAT original visibleAssignment :=
  fun preprocess decode model =>
    ay_tcc_model_intro original visibleAssignment
      (ay_tcc_equisat_backward original solver preprocess
        (ay_tcc_model_formula solver internalAssignment model))
      (decode (ay_tcc_model_assignment solver internalAssignment model))

theorem ay_tcc_preprocess_unsat_reconstruct
    (original solver : Prop) :
    AyTCCPreprocessArtifact original solver ->
    AyTCCUnsat solver ->
    AyTCCUnsat original :=
  fun preprocess solverUnsat originalProof =>
    solverUnsat
      (ay_tcc_equisat_forward original solver preprocess originalProof)

theorem ay_tcc_unsat_replay_checker
    (solver stream finalClause : Prop) :
    AyTCCReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    stream ->
    AyTCCUnsat solver :=
  fun replay closeFinal streamProof solverProof =>
    closeFinal (replay streamProof solverProof)

theorem ay_tcc_unsat_replay_public
    (original solver stream finalClause : Prop) :
    AyTCCPreprocessArtifact original solver ->
    AyTCCReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    stream ->
    AyTCCUnsat original :=
  fun preprocess replay closeFinal streamProof =>
    ay_tcc_preprocess_unsat_reconstruct original solver preprocess
      (ay_tcc_unsat_replay_checker solver stream finalClause replay
        closeFinal streamProof)

theorem ay_tcc_branch_checkers_to_public
    (satBranch unsatBranch publicSat publicUnsat : Prop) :
    AyTCCSatChecker satBranch publicSat ->
    AyTCCUnsatChecker unsatBranch publicUnsat ->
    AyTCCOutcome satBranch unsatBranch ->
    AyTCCOutcome publicSat publicUnsat :=
  fun satChecker unsatChecker =>
    ay_tcc_outcome_map satBranch publicSat unsatBranch publicUnsat
      (ay_tcc_sat_checker_accepts satBranch publicSat satChecker)
      (ay_tcc_unsat_checker_accepts unsatBranch publicUnsat unsatChecker)

theorem ay_tcc_indexed_checked_outcome
    (index satBranch unsatBranch publicSat publicUnsat : Prop) :
    AyTCCSatChecker satBranch publicSat ->
    AyTCCUnsatChecker unsatBranch publicUnsat ->
    AyTCCIndexed index
      (AyTCCCompressed (AyTCCOutcome satBranch unsatBranch)) ->
    index ->
    AyTCCOutcome publicSat publicUnsat :=
  fun satChecker unsatChecker indexed indexProof =>
    ay_tcc_branch_checkers_to_public satBranch unsatBranch publicSat
      publicUnsat satChecker unsatChecker
      (ay_tcc_indexed_compressed_lookup index
        (AyTCCOutcome satBranch unsatBranch) indexed indexProof)

theorem ay_tcc_sat_branch_public_checker
    (original solver internalAssignment visibleAssignment satBranch : Prop) :
    AyTCCPreprocessArtifact original solver ->
    (internalAssignment -> visibleAssignment) ->
    (satBranch -> AyTCCModel solver internalAssignment) ->
    AyTCCSatChecker satBranch
      (AyTCCVisibleSAT original visibleAssignment) :=
  fun preprocess decode accept branchProof =>
    ay_tcc_preprocess_model_reconstruct original solver internalAssignment
      visibleAssignment preprocess decode (accept branchProof)

theorem ay_tcc_unsat_branch_public_checker
    (original solver stream finalClause unsatBranch : Prop) :
    AyTCCPreprocessArtifact original solver ->
    AyTCCReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    (unsatBranch -> stream) ->
    AyTCCUnsatChecker unsatBranch (AyTCCUnsat original) :=
  fun preprocess replay closeFinal accept branchProof =>
    ay_tcc_unsat_replay_public original solver stream finalClause
      preprocess replay closeFinal (accept branchProof)

theorem ay_tcc_compressed_indexed_top_sound
    (index original solver internalAssignment visibleAssignment stream
      finalClause satBranch unsatBranch : Prop) :
    AyTCCPreprocessArtifact original solver ->
    (internalAssignment -> visibleAssignment) ->
    AyTCCReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    (satBranch -> AyTCCModel solver internalAssignment) ->
    (unsatBranch -> stream) ->
    AyTCCIndexed index
      (AyTCCCompressed (AyTCCOutcome satBranch unsatBranch)) ->
    index ->
    AyTCCOutcome
      (AyTCCVisibleSAT original visibleAssignment)
      (AyTCCUnsat original) :=
  fun preprocess decode replay closeFinal satAccept unsatAccept indexed
      indexProof =>
    ay_tcc_indexed_checked_outcome index satBranch unsatBranch
      (AyTCCVisibleSAT original visibleAssignment)
      (AyTCCUnsat original)
      (ay_tcc_sat_branch_public_checker original solver internalAssignment
        visibleAssignment satBranch preprocess decode satAccept)
      (ay_tcc_unsat_branch_public_checker original solver stream finalClause
        unsatBranch preprocess replay closeFinal unsatAccept)
      indexed indexProof

theorem ay_tcc_public_outcome_reconstructs_indexed
    (index satBranch unsatBranch publicSat publicUnsat : Prop) :
    index ->
    (publicSat -> satBranch) ->
    (publicUnsat -> unsatBranch) ->
    AyTCCOutcome publicSat publicUnsat ->
    AyTCCIndexed index
      (AyTCCCompressed (AyTCCOutcome satBranch unsatBranch)) :=
  fun indexProof satBack unsatBack publicOutcome =>
    ay_tcc_indexed_intro index
      (AyTCCCompressed (AyTCCOutcome satBranch unsatBranch))
      indexProof
      (ay_tcc_compressed_pack (AyTCCOutcome satBranch unsatBranch)
        (ay_tcc_outcome_map publicSat satBranch publicUnsat unsatBranch
          satBack unsatBack publicOutcome))

theorem ay_tcc_checker_contract_roundtrip
    (index satBranch unsatBranch publicSat publicUnsat : Prop) :
    index ->
    AyTCCSatChecker satBranch publicSat ->
    AyTCCUnsatChecker unsatBranch publicUnsat ->
    (publicSat -> satBranch) ->
    (publicUnsat -> unsatBranch) ->
    AyTCCEquisat
      (AyTCCIndexed index
        (AyTCCCompressed (AyTCCOutcome satBranch unsatBranch)))
      (AyTCCOutcome publicSat publicUnsat) :=
  fun indexProof satChecker unsatChecker satBack unsatBack =>
    ay_tcc_conj_intro
      (AyTCCIndexed index
        (AyTCCCompressed (AyTCCOutcome satBranch unsatBranch)) ->
        AyTCCOutcome publicSat publicUnsat)
      (AyTCCOutcome publicSat publicUnsat ->
        AyTCCIndexed index
          (AyTCCCompressed (AyTCCOutcome satBranch unsatBranch)))
      (fun indexed =>
        ay_tcc_indexed_checked_outcome index satBranch unsatBranch publicSat
          publicUnsat satChecker unsatChecker indexed
          (ay_tcc_indexed_index index
            (AyTCCCompressed (AyTCCOutcome satBranch unsatBranch)) indexed))
      (ay_tcc_public_outcome_reconstructs_indexed index satBranch
        unsatBranch publicSat publicUnsat indexProof satBack unsatBack)
