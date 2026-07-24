-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checker contract for ay UNSAT certificates. The public SAT-COMP UNSAT answer
-- is sound when a compressed solver-emitted replay artifact is projected to a
-- visible replay artifact, the replay checker accepts it, validates the empty
-- clause, and preprocessing transports visible UNSAT back to the original CNF.

def AyUCCConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyUCCDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyUCCMap (source : Prop) (target : Prop) :=
  source -> target

def AyUCCEquisat (before : Prop) (after : Prop) :=
  AyUCCConj (before -> after) (after -> before)

def AyUCCCompressedProjection
    (emittedArtifact : Prop) (visibleArtifact : Prop)
    (compressedCertificate : Prop) :=
  AyUCCConj compressedCertificate
    (AyUCCMap emittedArtifact visibleArtifact)

def AyUCCReplayChecker
    (visibleArtifact : Prop) (checkerAccepts : Prop)
    (emptyClause : Prop) :=
  AyUCCConj
    (AyUCCMap visibleArtifact checkerAccepts)
    (AyUCCMap checkerAccepts emptyClause)

def AyUCCEmptyValidation
    (emptyClause : Prop) (visibleUnsat : Prop) :=
  AyUCCMap emptyClause visibleUnsat

def AyUCCPreprocessContract
    (originalCNF : Prop) (visibleCNF : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUCCConj
    (AyUCCEquisat originalCNF visibleCNF)
    (AyUCCMap visibleUnsat originalUnsat)

def AyUCCUnsatCheckerContract
    (originalCNF : Prop) (visibleCNF : Prop)
    (emittedArtifact : Prop) (visibleArtifact : Prop)
    (compressedCertificate : Prop)
    (checkerAccepts : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUCCConj
    (AyUCCCompressedProjection
      emittedArtifact visibleArtifact compressedCertificate)
    (AyUCCConj
      (AyUCCReplayChecker visibleArtifact checkerAccepts emptyClause)
      (AyUCCConj
        (AyUCCEmptyValidation emptyClause visibleUnsat)
        (AyUCCPreprocessContract
          originalCNF visibleCNF visibleUnsat originalUnsat)))

def AyUCCPublicAnswer (satWitness : Prop) (unsatWitness : Prop) :=
  AyUCCDisj satWitness unsatWitness

theorem ay_ucc_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyUCCConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_ucc_conj_left
    (p : Prop) (q : Prop) :
    AyUCCConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_ucc_disj_left
    (p : Prop) (q : Prop) :
    p -> AyUCCDisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_ucc_disj_right
    (p : Prop) (q : Prop) :
    q -> AyUCCDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_ucc_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyUCCEquisat before after := by
  intro forward
  intro backward
  exact ay_ucc_conj_intro
    (before -> after)
    (after -> before)
    forward
    backward

theorem ay_ucc_equisat_forward
    (before : Prop) (after : Prop) :
    AyUCCEquisat before after ->
    before ->
    after := by
  intro cert
  exact cert (before -> after)
    (fun forward _backward => forward)

theorem ay_ucc_equisat_backward
    (before : Prop) (after : Prop) :
    AyUCCEquisat before after ->
    after ->
    before := by
  intro cert
  exact cert (after -> before)
    (fun _forward backward => backward)

theorem ay_ucc_compressed_certificate
    (emittedArtifact : Prop) (visibleArtifact : Prop)
    (compressedCertificate : Prop) :
    AyUCCCompressedProjection
      emittedArtifact visibleArtifact compressedCertificate ->
    compressedCertificate := by
  intro projection
  exact ay_ucc_conj_left compressedCertificate
    (AyUCCMap emittedArtifact visibleArtifact)
    projection

theorem ay_ucc_project_visible_artifact
    (emittedArtifact : Prop) (visibleArtifact : Prop)
    (compressedCertificate : Prop) :
    AyUCCCompressedProjection
      emittedArtifact visibleArtifact compressedCertificate ->
    emittedArtifact ->
    visibleArtifact := by
  intro projection
  exact projection (emittedArtifact -> visibleArtifact)
    (fun _compressed project => project)

theorem ay_ucc_checker_accepts_visible
    (visibleArtifact : Prop) (checkerAccepts : Prop)
    (emptyClause : Prop) :
    AyUCCReplayChecker visibleArtifact checkerAccepts emptyClause ->
    visibleArtifact ->
    checkerAccepts := by
  intro checker
  exact checker (visibleArtifact -> checkerAccepts)
    (fun visible_to_accept _accept_to_empty => visible_to_accept)

theorem ay_ucc_checker_empty_clause
    (visibleArtifact : Prop) (checkerAccepts : Prop)
    (emptyClause : Prop) :
    AyUCCReplayChecker visibleArtifact checkerAccepts emptyClause ->
    checkerAccepts ->
    emptyClause := by
  intro checker
  exact checker (checkerAccepts -> emptyClause)
    (fun _visible_to_accept accept_to_empty => accept_to_empty)

theorem ay_ucc_checker_empty_from_visible
    (visibleArtifact : Prop) (checkerAccepts : Prop)
    (emptyClause : Prop) :
    AyUCCReplayChecker visibleArtifact checkerAccepts emptyClause ->
    visibleArtifact ->
    emptyClause := by
  intro checker
  intro hvisible
  exact ay_ucc_checker_empty_clause visibleArtifact checkerAccepts emptyClause
    checker
    (ay_ucc_checker_accepts_visible
      visibleArtifact checkerAccepts emptyClause checker hvisible)

theorem ay_ucc_validate_empty_clause
    (emptyClause : Prop) (visibleUnsat : Prop) :
    AyUCCEmptyValidation emptyClause visibleUnsat ->
    emptyClause ->
    visibleUnsat := by
  intro validation
  exact validation

theorem ay_ucc_preprocess_equisat
    (originalCNF : Prop) (visibleCNF : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCCPreprocessContract
      originalCNF visibleCNF visibleUnsat originalUnsat ->
    AyUCCEquisat originalCNF visibleCNF := by
  intro preprocess
  exact ay_ucc_conj_left
    (AyUCCEquisat originalCNF visibleCNF)
    (AyUCCMap visibleUnsat originalUnsat)
    preprocess

theorem ay_ucc_preprocess_original_to_visible
    (originalCNF : Prop) (visibleCNF : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCCPreprocessContract
      originalCNF visibleCNF visibleUnsat originalUnsat ->
    originalCNF ->
    visibleCNF := by
  intro preprocess
  exact ay_ucc_equisat_forward originalCNF visibleCNF
    (ay_ucc_preprocess_equisat
      originalCNF visibleCNF visibleUnsat originalUnsat preprocess)

theorem ay_ucc_preprocess_visible_to_original
    (originalCNF : Prop) (visibleCNF : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCCPreprocessContract
      originalCNF visibleCNF visibleUnsat originalUnsat ->
    visibleCNF ->
    originalCNF := by
  intro preprocess
  exact ay_ucc_equisat_backward originalCNF visibleCNF
    (ay_ucc_preprocess_equisat
      originalCNF visibleCNF visibleUnsat originalUnsat preprocess)

theorem ay_ucc_preprocess_unsat_transport
    (originalCNF : Prop) (visibleCNF : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCCPreprocessContract
      originalCNF visibleCNF visibleUnsat originalUnsat ->
    visibleUnsat ->
    originalUnsat := by
  intro preprocess
  exact preprocess (visibleUnsat -> originalUnsat)
    (fun _equisat transport => transport)

theorem ay_ucc_contract_projection
    (originalCNF : Prop) (visibleCNF : Prop)
    (emittedArtifact : Prop) (visibleArtifact : Prop)
    (compressedCertificate : Prop)
    (checkerAccepts : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCCUnsatCheckerContract originalCNF visibleCNF emittedArtifact
      visibleArtifact compressedCertificate checkerAccepts emptyClause
      visibleUnsat originalUnsat ->
    AyUCCCompressedProjection
      emittedArtifact visibleArtifact compressedCertificate := by
  intro contract
  exact ay_ucc_conj_left
    (AyUCCCompressedProjection
      emittedArtifact visibleArtifact compressedCertificate)
    (AyUCCConj
      (AyUCCReplayChecker visibleArtifact checkerAccepts emptyClause)
      (AyUCCConj
        (AyUCCEmptyValidation emptyClause visibleUnsat)
        (AyUCCPreprocessContract
          originalCNF visibleCNF visibleUnsat originalUnsat)))
    contract

theorem ay_ucc_contract_checker
    (originalCNF : Prop) (visibleCNF : Prop)
    (emittedArtifact : Prop) (visibleArtifact : Prop)
    (compressedCertificate : Prop)
    (checkerAccepts : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCCUnsatCheckerContract originalCNF visibleCNF emittedArtifact
      visibleArtifact compressedCertificate checkerAccepts emptyClause
      visibleUnsat originalUnsat ->
    AyUCCReplayChecker visibleArtifact checkerAccepts emptyClause := by
  intro contract
  exact contract (AyUCCReplayChecker visibleArtifact checkerAccepts emptyClause)
    (fun _projection tail =>
      tail (AyUCCReplayChecker visibleArtifact checkerAccepts emptyClause)
        (fun checker _rest => checker))

theorem ay_ucc_contract_empty_validation
    (originalCNF : Prop) (visibleCNF : Prop)
    (emittedArtifact : Prop) (visibleArtifact : Prop)
    (compressedCertificate : Prop)
    (checkerAccepts : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCCUnsatCheckerContract originalCNF visibleCNF emittedArtifact
      visibleArtifact compressedCertificate checkerAccepts emptyClause
      visibleUnsat originalUnsat ->
    AyUCCEmptyValidation emptyClause visibleUnsat := by
  intro contract
  exact contract (AyUCCEmptyValidation emptyClause visibleUnsat)
    (fun _projection tail =>
      tail (AyUCCEmptyValidation emptyClause visibleUnsat)
        (fun _checker rest =>
          rest (AyUCCEmptyValidation emptyClause visibleUnsat)
            (fun validation _preprocess => validation)))

theorem ay_ucc_contract_preprocess
    (originalCNF : Prop) (visibleCNF : Prop)
    (emittedArtifact : Prop) (visibleArtifact : Prop)
    (compressedCertificate : Prop)
    (checkerAccepts : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCCUnsatCheckerContract originalCNF visibleCNF emittedArtifact
      visibleArtifact compressedCertificate checkerAccepts emptyClause
      visibleUnsat originalUnsat ->
    AyUCCPreprocessContract
      originalCNF visibleCNF visibleUnsat originalUnsat := by
  intro contract
  exact contract
    (AyUCCPreprocessContract
      originalCNF visibleCNF visibleUnsat originalUnsat)
    (fun _projection tail =>
      tail
        (AyUCCPreprocessContract
          originalCNF visibleCNF visibleUnsat originalUnsat)
        (fun _checker rest =>
          rest
            (AyUCCPreprocessContract
              originalCNF visibleCNF visibleUnsat originalUnsat)
            (fun _validation preprocess => preprocess)))

theorem ay_ucc_contract_visible_artifact
    (originalCNF : Prop) (visibleCNF : Prop)
    (emittedArtifact : Prop) (visibleArtifact : Prop)
    (compressedCertificate : Prop)
    (checkerAccepts : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCCUnsatCheckerContract originalCNF visibleCNF emittedArtifact
      visibleArtifact compressedCertificate checkerAccepts emptyClause
      visibleUnsat originalUnsat ->
    emittedArtifact ->
    visibleArtifact := by
  intro contract
  exact ay_ucc_project_visible_artifact
    emittedArtifact visibleArtifact compressedCertificate
    (ay_ucc_contract_projection
      originalCNF visibleCNF emittedArtifact visibleArtifact
      compressedCertificate checkerAccepts emptyClause
      visibleUnsat originalUnsat contract)

theorem ay_ucc_contract_checker_accepts
    (originalCNF : Prop) (visibleCNF : Prop)
    (emittedArtifact : Prop) (visibleArtifact : Prop)
    (compressedCertificate : Prop)
    (checkerAccepts : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCCUnsatCheckerContract originalCNF visibleCNF emittedArtifact
      visibleArtifact compressedCertificate checkerAccepts emptyClause
      visibleUnsat originalUnsat ->
    emittedArtifact ->
    checkerAccepts := by
  intro contract
  intro emitted
  exact ay_ucc_checker_accepts_visible visibleArtifact checkerAccepts emptyClause
    (ay_ucc_contract_checker
      originalCNF visibleCNF emittedArtifact visibleArtifact
      compressedCertificate checkerAccepts emptyClause
      visibleUnsat originalUnsat contract)
    (ay_ucc_contract_visible_artifact
      originalCNF visibleCNF emittedArtifact visibleArtifact
      compressedCertificate checkerAccepts emptyClause
      visibleUnsat originalUnsat contract emitted)

theorem ay_ucc_contract_empty_clause
    (originalCNF : Prop) (visibleCNF : Prop)
    (emittedArtifact : Prop) (visibleArtifact : Prop)
    (compressedCertificate : Prop)
    (checkerAccepts : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCCUnsatCheckerContract originalCNF visibleCNF emittedArtifact
      visibleArtifact compressedCertificate checkerAccepts emptyClause
      visibleUnsat originalUnsat ->
    emittedArtifact ->
    emptyClause := by
  intro contract
  intro emitted
  exact ay_ucc_checker_empty_clause visibleArtifact checkerAccepts emptyClause
    (ay_ucc_contract_checker
      originalCNF visibleCNF emittedArtifact visibleArtifact
      compressedCertificate checkerAccepts emptyClause
      visibleUnsat originalUnsat contract)
    (ay_ucc_contract_checker_accepts
      originalCNF visibleCNF emittedArtifact visibleArtifact
      compressedCertificate checkerAccepts emptyClause
      visibleUnsat originalUnsat contract emitted)

theorem ay_ucc_contract_visible_unsat
    (originalCNF : Prop) (visibleCNF : Prop)
    (emittedArtifact : Prop) (visibleArtifact : Prop)
    (compressedCertificate : Prop)
    (checkerAccepts : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCCUnsatCheckerContract originalCNF visibleCNF emittedArtifact
      visibleArtifact compressedCertificate checkerAccepts emptyClause
      visibleUnsat originalUnsat ->
    emittedArtifact ->
    visibleUnsat := by
  intro contract
  intro emitted
  exact ay_ucc_validate_empty_clause emptyClause visibleUnsat
    (ay_ucc_contract_empty_validation
      originalCNF visibleCNF emittedArtifact visibleArtifact
      compressedCertificate checkerAccepts emptyClause
      visibleUnsat originalUnsat contract)
    (ay_ucc_contract_empty_clause
      originalCNF visibleCNF emittedArtifact visibleArtifact
      compressedCertificate checkerAccepts emptyClause
      visibleUnsat originalUnsat contract emitted)

theorem ay_ucc_contract_original_unsat
    (originalCNF : Prop) (visibleCNF : Prop)
    (emittedArtifact : Prop) (visibleArtifact : Prop)
    (compressedCertificate : Prop)
    (checkerAccepts : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCCUnsatCheckerContract originalCNF visibleCNF emittedArtifact
      visibleArtifact compressedCertificate checkerAccepts emptyClause
      visibleUnsat originalUnsat ->
    emittedArtifact ->
    originalUnsat := by
  intro contract
  intro emitted
  exact ay_ucc_preprocess_unsat_transport
    originalCNF visibleCNF visibleUnsat originalUnsat
    (ay_ucc_contract_preprocess
      originalCNF visibleCNF emittedArtifact visibleArtifact
      compressedCertificate checkerAccepts emptyClause
      visibleUnsat originalUnsat contract)
    (ay_ucc_contract_visible_unsat
      originalCNF visibleCNF emittedArtifact visibleArtifact
      compressedCertificate checkerAccepts emptyClause
      visibleUnsat originalUnsat contract emitted)

theorem ay_ucc_public_unsat_answer
    (satWitness : Prop) (originalUnsat : Prop) :
    originalUnsat ->
    AyUCCPublicAnswer satWitness originalUnsat := by
  intro unsat
  exact ay_ucc_disj_right satWitness originalUnsat unsat

theorem ay_ucc_public_answer_sound
    (satWitness : Prop)
    (originalCNF : Prop) (visibleCNF : Prop)
    (emittedArtifact : Prop) (visibleArtifact : Prop)
    (compressedCertificate : Prop)
    (checkerAccepts : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCCUnsatCheckerContract originalCNF visibleCNF emittedArtifact
      visibleArtifact compressedCertificate checkerAccepts emptyClause
      visibleUnsat originalUnsat ->
    emittedArtifact ->
    AyUCCPublicAnswer satWitness originalUnsat := by
  intro contract
  intro emitted
  exact ay_ucc_public_unsat_answer satWitness originalUnsat
    (ay_ucc_contract_original_unsat
      originalCNF visibleCNF emittedArtifact visibleArtifact
      compressedCertificate checkerAccepts emptyClause
      visibleUnsat originalUnsat contract emitted)

theorem ay_ucc_replay_checker_contract_sound
    (originalCNF : Prop) (visibleCNF : Prop)
    (emittedArtifact : Prop) (visibleArtifact : Prop)
    (compressedCertificate : Prop)
    (checkerAccepts : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCCUnsatCheckerContract originalCNF visibleCNF emittedArtifact
      visibleArtifact compressedCertificate checkerAccepts emptyClause
      visibleUnsat originalUnsat ->
    emittedArtifact ->
    originalUnsat := by
  intro contract
  exact ay_ucc_contract_original_unsat
    originalCNF visibleCNF emittedArtifact visibleArtifact
    compressedCertificate checkerAccepts emptyClause
    visibleUnsat originalUnsat contract
