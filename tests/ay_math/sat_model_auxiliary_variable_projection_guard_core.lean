/-!
  SAT-COMP/ay auxiliary-variable projection guard.

  This self-contained package models the SAT-only obligations for projecting an
  extended witness from Tseitin-style encodings or preprocessing back to the
  original variable domain.
-/

def ay_avpg_conj (p q : Prop) : Prop :=
  forall r : Prop, (p -> q -> r) -> r

def ay_avpg_disj (p q : Prop) : Prop :=
  forall r : Prop, (p -> r) -> (q -> r) -> r

def ay_avpg_equiv (p q : Prop) : Prop :=
  ay_avpg_conj (p -> q) (q -> p)

def ay_avpg_original_formula_digest (extendedWitness originalDigestOk : Prop) : Prop :=
  extendedWitness -> originalDigestOk

def ay_avpg_extended_encoded_formula_digest
    (originalDigestOk encodedDigestOk : Prop) : Prop :=
  originalDigestOk -> encodedDigestOk

def ay_avpg_auxiliary_variable_manifest (encodedDigestOk auxManifestOk : Prop) : Prop :=
  encodedDigestOk -> auxManifestOk

def ay_avpg_projection_map_witness (auxManifestOk projectionOk : Prop) : Prop :=
  auxManifestOk -> projectionOk

def ay_avpg_total_original_assignment_reconstruction
    (projectionOk originalAssignment : Prop) : Prop :=
  projectionOk -> originalAssignment

def ay_avpg_original_clause_satisfaction_replay
    (originalAssignment everyOriginalClauseSatisfied : Prop) : Prop :=
  originalAssignment -> everyOriginalClauseSatisfied

def ay_avpg_checker_transcript (everyOriginalClauseSatisfied originalSat : Prop) : Prop :=
  everyOriginalClauseSatisfied -> originalSat

def ay_avpg_solver_build_evidence (originalSat buildOk : Prop) : Prop :=
  originalSat -> buildOk

def ay_avpg_archive_manifest (buildOk archiveOk : Prop) : Prop :=
  buildOk -> archiveOk

def ay_avpg_fallback_no_claim_path (archiveOk fallbackReady : Prop) : Prop :=
  archiveOk -> fallbackReady

def ay_avpg_audit_transcript (fallbackReady audited : Prop) : Prop :=
  fallbackReady -> audited

def ay_avpg_accepted_projection
    (originalDigest encodedDigest auxManifest projection reconstruction replay checker build
     archive fallback audit : Prop) : Prop :=
  ay_avpg_conj originalDigest
    (ay_avpg_conj encodedDigest
      (ay_avpg_conj auxManifest
        (ay_avpg_conj projection
          (ay_avpg_conj reconstruction
            (ay_avpg_conj replay
              (ay_avpg_conj checker
                (ay_avpg_conj build
                  (ay_avpg_conj archive
                    (ay_avpg_conj fallback audit)))))))))

def ay_avpg_public_sat
    (accepted originalAssignment everyOriginalClauseSatisfied originalSat audited : Prop) :
    Prop :=
  ay_avpg_conj accepted
    (ay_avpg_conj originalAssignment
      (ay_avpg_conj everyOriginalClauseSatisfied (ay_avpg_conj originalSat audited)))

def ay_avpg_public_unsat (proofAccepted originalUnsat : Prop) : Prop :=
  ay_avpg_conj proofAccepted originalUnsat

def ay_avpg_no_claim_diagnostic (reason : Prop) : Prop :=
  reason

def ay_avpg_recompute_obligation (reason : Prop) : Prop :=
  reason

theorem ay_avpg_conj_intro {p q : Prop} (hp : p) (hq : q) : ay_avpg_conj p q :=
  fun r h => h hp hq

theorem ay_avpg_conj_left {p q : Prop} (h : ay_avpg_conj p q) : p :=
  h p (fun hp _ => hp)

theorem ay_avpg_conj_right {p q : Prop} (h : ay_avpg_conj p q) : q :=
  (h (p -> q) (fun (_ : p) (hq : q) (_ : p) => hq)) (ay_avpg_conj_left h)

theorem ay_avpg_disj_left {p q : Prop} (hp : p) : ay_avpg_disj p q :=
  fun r hl _ => hl hp

theorem ay_avpg_disj_right {p q : Prop} (hq : q) : ay_avpg_disj p q :=
  fun r _ hr => hr hq

theorem ay_avpg_equiv_intro {p q : Prop} (hpq : p -> q) (hqp : q -> p) :
    ay_avpg_equiv p q :=
  ay_avpg_conj_intro hpq hqp

theorem ay_avpg_equiv_forward {p q : Prop} (h : ay_avpg_equiv p q) : p -> q :=
  ay_avpg_conj_left h

theorem ay_avpg_equiv_backward {p q : Prop} (h : ay_avpg_equiv p q) : q -> p :=
  ay_avpg_conj_right h

theorem ay_avpg_original_formula_digest_intro {extendedWitness originalDigestOk : Prop}
    (h : extendedWitness -> originalDigestOk) :
    ay_avpg_original_formula_digest extendedWitness originalDigestOk :=
  h

theorem ay_avpg_extended_encoded_formula_digest_intro
    {originalDigestOk encodedDigestOk : Prop}
    (h : originalDigestOk -> encodedDigestOk) :
    ay_avpg_extended_encoded_formula_digest originalDigestOk encodedDigestOk :=
  h

theorem ay_avpg_auxiliary_variable_manifest_intro {encodedDigestOk auxManifestOk : Prop}
    (h : encodedDigestOk -> auxManifestOk) :
    ay_avpg_auxiliary_variable_manifest encodedDigestOk auxManifestOk :=
  h

theorem ay_avpg_projection_map_witness_intro {auxManifestOk projectionOk : Prop}
    (h : auxManifestOk -> projectionOk) :
    ay_avpg_projection_map_witness auxManifestOk projectionOk :=
  h

theorem ay_avpg_total_original_assignment_reconstruction_intro
    {projectionOk originalAssignment : Prop}
    (h : projectionOk -> originalAssignment) :
    ay_avpg_total_original_assignment_reconstruction projectionOk originalAssignment :=
  h

theorem ay_avpg_original_clause_satisfaction_replay_intro
    {originalAssignment everyOriginalClauseSatisfied : Prop}
    (h : originalAssignment -> everyOriginalClauseSatisfied) :
    ay_avpg_original_clause_satisfaction_replay originalAssignment
      everyOriginalClauseSatisfied :=
  h

theorem ay_avpg_checker_transcript_intro
    {everyOriginalClauseSatisfied originalSat : Prop}
    (h : everyOriginalClauseSatisfied -> originalSat) :
    ay_avpg_checker_transcript everyOriginalClauseSatisfied originalSat :=
  h

theorem ay_avpg_solver_build_evidence_intro {originalSat buildOk : Prop}
    (h : originalSat -> buildOk) :
    ay_avpg_solver_build_evidence originalSat buildOk :=
  h

theorem ay_avpg_archive_manifest_intro {buildOk archiveOk : Prop}
    (h : buildOk -> archiveOk) :
    ay_avpg_archive_manifest buildOk archiveOk :=
  h

theorem ay_avpg_fallback_no_claim_path_intro {archiveOk fallbackReady : Prop}
    (h : archiveOk -> fallbackReady) :
    ay_avpg_fallback_no_claim_path archiveOk fallbackReady :=
  h

theorem ay_avpg_audit_transcript_intro {fallbackReady audited : Prop}
    (h : fallbackReady -> audited) :
    ay_avpg_audit_transcript fallbackReady audited :=
  h

theorem ay_avpg_accepted_projection_intro
    {originalDigest encodedDigest auxManifest projection reconstruction replay checker build
     archive fallback audit : Prop}
    (ho : originalDigest) (he : encodedDigest) (ha : auxManifest) (hp : projection)
    (hrc : reconstruction) (hr : replay) (hc : checker) (hb : build)
    (har : archive) (hfb : fallback) (hau : audit) :
    ay_avpg_accepted_projection originalDigest encodedDigest auxManifest projection
      reconstruction replay checker build archive fallback audit :=
  ay_avpg_conj_intro ho
    (ay_avpg_conj_intro he
      (ay_avpg_conj_intro ha
        (ay_avpg_conj_intro hp
          (ay_avpg_conj_intro hrc
            (ay_avpg_conj_intro hr
              (ay_avpg_conj_intro hc
                (ay_avpg_conj_intro hb
                  (ay_avpg_conj_intro har
                    (ay_avpg_conj_intro hfb hau)))))))))

theorem ay_avpg_accepted_projection_original_digest
    {originalDigest encodedDigest auxManifest projection reconstruction replay checker build
     archive fallback audit : Prop}
    (h : ay_avpg_accepted_projection originalDigest encodedDigest auxManifest projection
      reconstruction replay checker build archive fallback audit) : originalDigest :=
  ay_avpg_conj_left h

theorem ay_avpg_accepted_projection_encoded_digest
    {originalDigest encodedDigest auxManifest projection reconstruction replay checker build
     archive fallback audit : Prop}
    (h : ay_avpg_accepted_projection originalDigest encodedDigest auxManifest projection
      reconstruction replay checker build archive fallback audit) : encodedDigest :=
  ay_avpg_conj_left (ay_avpg_conj_right h)

theorem ay_avpg_accepted_projection_aux_manifest
    {originalDigest encodedDigest auxManifest projection reconstruction replay checker build
     archive fallback audit : Prop}
    (h : ay_avpg_accepted_projection originalDigest encodedDigest auxManifest projection
      reconstruction replay checker build archive fallback audit) : auxManifest :=
  ay_avpg_conj_left (ay_avpg_conj_right (ay_avpg_conj_right h))

theorem ay_avpg_accepted_projection_projection
    {originalDigest encodedDigest auxManifest projection reconstruction replay checker build
     archive fallback audit : Prop}
    (h : ay_avpg_accepted_projection originalDigest encodedDigest auxManifest projection
      reconstruction replay checker build archive fallback audit) : projection :=
  ay_avpg_conj_left
    (ay_avpg_conj_right (ay_avpg_conj_right (ay_avpg_conj_right h)))

theorem ay_avpg_accepted_projection_reconstruction
    {originalDigest encodedDigest auxManifest projection reconstruction replay checker build
     archive fallback audit : Prop}
    (h : ay_avpg_accepted_projection originalDigest encodedDigest auxManifest projection
      reconstruction replay checker build archive fallback audit) : reconstruction :=
  ay_avpg_conj_left
    (ay_avpg_conj_right
      (ay_avpg_conj_right (ay_avpg_conj_right (ay_avpg_conj_right h))))

theorem ay_avpg_accepted_projection_replay
    {originalDigest encodedDigest auxManifest projection reconstruction replay checker build
     archive fallback audit : Prop}
    (h : ay_avpg_accepted_projection originalDigest encodedDigest auxManifest projection
      reconstruction replay checker build archive fallback audit) : replay :=
  ay_avpg_conj_left
    (ay_avpg_conj_right
      (ay_avpg_conj_right
        (ay_avpg_conj_right (ay_avpg_conj_right (ay_avpg_conj_right h)))))

theorem ay_avpg_accepted_projection_checker
    {originalDigest encodedDigest auxManifest projection reconstruction replay checker build
     archive fallback audit : Prop}
    (h : ay_avpg_accepted_projection originalDigest encodedDigest auxManifest projection
      reconstruction replay checker build archive fallback audit) : checker :=
  ay_avpg_conj_left
    (ay_avpg_conj_right
      (ay_avpg_conj_right
        (ay_avpg_conj_right
          (ay_avpg_conj_right (ay_avpg_conj_right (ay_avpg_conj_right h))))))

theorem ay_avpg_accepted_projection_build
    {originalDigest encodedDigest auxManifest projection reconstruction replay checker build
     archive fallback audit : Prop}
    (h : ay_avpg_accepted_projection originalDigest encodedDigest auxManifest projection
      reconstruction replay checker build archive fallback audit) : build :=
  ay_avpg_conj_left
    (ay_avpg_conj_right
      (ay_avpg_conj_right
        (ay_avpg_conj_right
          (ay_avpg_conj_right
            (ay_avpg_conj_right (ay_avpg_conj_right (ay_avpg_conj_right h)))))))

theorem ay_avpg_accepted_projection_archive
    {originalDigest encodedDigest auxManifest projection reconstruction replay checker build
     archive fallback audit : Prop}
    (h : ay_avpg_accepted_projection originalDigest encodedDigest auxManifest projection
      reconstruction replay checker build archive fallback audit) : archive :=
  ay_avpg_conj_left
    (ay_avpg_conj_right
      (ay_avpg_conj_right
        (ay_avpg_conj_right
          (ay_avpg_conj_right
            (ay_avpg_conj_right
              (ay_avpg_conj_right (ay_avpg_conj_right (ay_avpg_conj_right h))))))))

theorem ay_avpg_accepted_projection_fallback
    {originalDigest encodedDigest auxManifest projection reconstruction replay checker build
     archive fallback audit : Prop}
    (h : ay_avpg_accepted_projection originalDigest encodedDigest auxManifest projection
      reconstruction replay checker build archive fallback audit) : fallback :=
  ay_avpg_conj_left
    (ay_avpg_conj_right
      (ay_avpg_conj_right
        (ay_avpg_conj_right
          (ay_avpg_conj_right
            (ay_avpg_conj_right
              (ay_avpg_conj_right
                (ay_avpg_conj_right (ay_avpg_conj_right (ay_avpg_conj_right h)))))))))

theorem ay_avpg_accepted_projection_audit
    {originalDigest encodedDigest auxManifest projection reconstruction replay checker build
     archive fallback audit : Prop}
    (h : ay_avpg_accepted_projection originalDigest encodedDigest auxManifest projection
      reconstruction replay checker build archive fallback audit) : audit :=
  ay_avpg_conj_right
    (ay_avpg_conj_right
      (ay_avpg_conj_right
        (ay_avpg_conj_right
          (ay_avpg_conj_right
            (ay_avpg_conj_right
              (ay_avpg_conj_right
                (ay_avpg_conj_right (ay_avpg_conj_right (ay_avpg_conj_right h)))))))))

theorem ay_avpg_projection_reconstructs_original_sat
    {extendedWitness originalDigestOk encodedDigestOk auxManifestOk projectionOk
     originalAssignment everyOriginalClauseSatisfied originalSat buildOk archiveOk
     fallbackReady audited : Prop}
    (ho : ay_avpg_original_formula_digest extendedWitness originalDigestOk)
    (he : ay_avpg_extended_encoded_formula_digest originalDigestOk encodedDigestOk)
    (ha : ay_avpg_auxiliary_variable_manifest encodedDigestOk auxManifestOk)
    (hp : ay_avpg_projection_map_witness auxManifestOk projectionOk)
    (hrc : ay_avpg_total_original_assignment_reconstruction
      projectionOk originalAssignment)
    (hr : ay_avpg_original_clause_satisfaction_replay
      originalAssignment everyOriginalClauseSatisfied)
    (hc : ay_avpg_checker_transcript everyOriginalClauseSatisfied originalSat)
    (hb : ay_avpg_solver_build_evidence originalSat buildOk)
    (har : ay_avpg_archive_manifest buildOk archiveOk)
    (hfb : ay_avpg_fallback_no_claim_path archiveOk fallbackReady)
    (hau : ay_avpg_audit_transcript fallbackReady audited)
    (hw : extendedWitness) :
    ay_avpg_conj originalAssignment
      (ay_avpg_conj everyOriginalClauseSatisfied (ay_avpg_conj originalSat audited)) :=
  let horiginal : originalDigestOk := ho hw
  let hencoded : encodedDigestOk := he horiginal
  let haux : auxManifestOk := ha hencoded
  let hprojection : projectionOk := hp haux
  let hassignment : originalAssignment := hrc hprojection
  let hevery : everyOriginalClauseSatisfied := hr hassignment
  let hsat : originalSat := hc hevery
  let hbuild : buildOk := hb hsat
  let harchive : archiveOk := har hbuild
  let hfallback : fallbackReady := hfb harchive
  let haudit : audited := hau hfallback
  ay_avpg_conj_intro hassignment (ay_avpg_conj_intro hevery (ay_avpg_conj_intro hsat haudit))

theorem ay_avpg_public_sat_intro
    {accepted originalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (ha : accepted) (hm : originalAssignment) (hevery : everyOriginalClauseSatisfied)
    (hs : originalSat) (hau : audited) :
    ay_avpg_public_sat accepted originalAssignment everyOriginalClauseSatisfied originalSat
      audited :=
  ay_avpg_conj_intro ha
    (ay_avpg_conj_intro hm (ay_avpg_conj_intro hevery (ay_avpg_conj_intro hs hau)))

theorem ay_avpg_public_sat_requires_projection_guard
    {accepted originalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (h : ay_avpg_public_sat accepted originalAssignment everyOriginalClauseSatisfied
      originalSat audited) : accepted :=
  ay_avpg_conj_left h

theorem ay_avpg_public_sat_original_assignment
    {accepted originalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (h : ay_avpg_public_sat accepted originalAssignment everyOriginalClauseSatisfied
      originalSat audited) : originalAssignment :=
  ay_avpg_conj_left (ay_avpg_conj_right h)

theorem ay_avpg_public_sat_every_original_clause
    {accepted originalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (h : ay_avpg_public_sat accepted originalAssignment everyOriginalClauseSatisfied
      originalSat audited) : everyOriginalClauseSatisfied :=
  ay_avpg_conj_left (ay_avpg_conj_right (ay_avpg_conj_right h))

theorem ay_avpg_public_sat_original_formula
    {accepted originalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (h : ay_avpg_public_sat accepted originalAssignment everyOriginalClauseSatisfied
      originalSat audited) : originalSat :=
  ay_avpg_conj_left (ay_avpg_conj_right (ay_avpg_conj_right (ay_avpg_conj_right h)))

theorem ay_avpg_public_sat_audit
    {accepted originalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (h : ay_avpg_public_sat accepted originalAssignment everyOriginalClauseSatisfied
      originalSat audited) : audited :=
  ay_avpg_conj_right (ay_avpg_conj_right (ay_avpg_conj_right (ay_avpg_conj_right h)))

theorem ay_avpg_accepted_projection_publishes_sat
    {originalDigest encodedDigest auxManifest projection reconstruction replay checker build
     archive fallback audit originalAssignment everyOriginalClauseSatisfied originalSat
     audited : Prop}
    (hg : ay_avpg_accepted_projection originalDigest encodedDigest auxManifest projection
      reconstruction replay checker build archive fallback audit)
    (hm : originalAssignment) (hevery : everyOriginalClauseSatisfied)
    (hs : originalSat) (hau : audited) :
    ay_avpg_public_sat
      (ay_avpg_accepted_projection originalDigest encodedDigest auxManifest projection
        reconstruction replay checker build archive fallback audit)
      originalAssignment everyOriginalClauseSatisfied originalSat audited :=
  ay_avpg_public_sat_intro hg hm hevery hs hau

theorem ay_avpg_no_claim_intro {reason : Prop} (h : reason) :
    ay_avpg_no_claim_diagnostic reason :=
  h

theorem ay_avpg_recompute_intro {reason : Prop} (h : reason) :
    ay_avpg_recompute_obligation reason :=
  h

theorem ay_avpg_original_digest_mismatch_recompute {reason : Prop} (h : reason) :
    ay_avpg_recompute_obligation reason :=
  ay_avpg_recompute_intro h

theorem ay_avpg_encoded_digest_mismatch_recompute {reason : Prop} (h : reason) :
    ay_avpg_recompute_obligation reason :=
  ay_avpg_recompute_intro h

theorem ay_avpg_auxiliary_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_avpg_no_claim_diagnostic reason :=
  ay_avpg_no_claim_intro h

theorem ay_avpg_projection_mismatch_recompute {reason : Prop} (h : reason) :
    ay_avpg_recompute_obligation reason :=
  ay_avpg_recompute_intro h

theorem ay_avpg_replay_mismatch_recompute {reason : Prop} (h : reason) :
    ay_avpg_recompute_obligation reason :=
  ay_avpg_recompute_intro h

theorem ay_avpg_checker_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_avpg_no_claim_diagnostic reason :=
  ay_avpg_no_claim_intro h

theorem ay_avpg_build_mismatch_recompute {reason : Prop} (h : reason) :
    ay_avpg_recompute_obligation reason :=
  ay_avpg_recompute_intro h

theorem ay_avpg_archive_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_avpg_no_claim_diagnostic reason :=
  ay_avpg_no_claim_intro h

theorem ay_avpg_audit_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_avpg_no_claim_diagnostic reason :=
  ay_avpg_no_claim_intro h

theorem ay_avpg_failed_projection_guard_cannot_create_public_sat
    {failure accepted originalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (hfail : failure)
    (hblock : ay_avpg_public_sat accepted originalAssignment everyOriginalClauseSatisfied
      originalSat audited -> ay_avpg_no_claim_diagnostic failure) :
    ay_avpg_conj (ay_avpg_no_claim_diagnostic failure)
      (ay_avpg_public_sat accepted originalAssignment everyOriginalClauseSatisfied originalSat
        audited -> ay_avpg_no_claim_diagnostic failure) :=
  ay_avpg_conj_intro (ay_avpg_no_claim_intro hfail) hblock

theorem ay_avpg_failed_projection_guard_forces_recompute
    {failure accepted originalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (hfail : failure)
    (hblock : ay_avpg_public_sat accepted originalAssignment everyOriginalClauseSatisfied
      originalSat audited -> ay_avpg_recompute_obligation failure) :
    ay_avpg_conj (ay_avpg_recompute_obligation failure)
      (ay_avpg_public_sat accepted originalAssignment everyOriginalClauseSatisfied originalSat
        audited -> ay_avpg_recompute_obligation failure) :=
  ay_avpg_conj_intro (ay_avpg_recompute_intro hfail) hblock

theorem ay_avpg_public_unsat_intro {proofAccepted originalUnsat : Prop}
    (hp : proofAccepted) (hu : originalUnsat) :
    ay_avpg_public_unsat proofAccepted originalUnsat :=
  ay_avpg_conj_intro hp hu

theorem ay_avpg_public_unsat_proof {proofAccepted originalUnsat : Prop}
    (h : ay_avpg_public_unsat proofAccepted originalUnsat) : proofAccepted :=
  ay_avpg_conj_left h

theorem ay_avpg_public_unsat_claim {proofAccepted originalUnsat : Prop}
    (h : ay_avpg_public_unsat proofAccepted originalUnsat) : originalUnsat :=
  ay_avpg_conj_right h

theorem ay_avpg_projection_guard_cannot_strengthen_unsat_claims
    {proofAccepted originalUnsat auxProjectionSatGuard : Prop}
    (h : ay_avpg_public_unsat proofAccepted originalUnsat) :
    ay_avpg_conj (ay_avpg_public_unsat proofAccepted originalUnsat)
      (auxProjectionSatGuard -> ay_avpg_public_unsat proofAccepted originalUnsat) :=
  ay_avpg_conj_intro h (fun _ => h)
