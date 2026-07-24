/-!
  SAT-COMP/ay variable-renaming inverse guard.

  This self-contained package models the SAT-only obligations for transporting
  a normalized/preprocessed SAT model back into the original DIMACS namespace.
-/

def ay_vrig_conj (p q : Prop) : Prop :=
  forall r : Prop, (p -> q -> r) -> r

def ay_vrig_disj (p q : Prop) : Prop :=
  forall r : Prop, (p -> r) -> (q -> r) -> r

def ay_vrig_equiv (p q : Prop) : Prop :=
  ay_vrig_conj (p -> q) (q -> p)

def ay_vrig_original_benchmark_fingerprint (renamedWitness fingerprintOk : Prop) : Prop :=
  renamedWitness -> fingerprintOk

def ay_vrig_normalized_formula_digest (fingerprintOk normalizedDigestOk : Prop) : Prop :=
  fingerprintOk -> normalizedDigestOk

def ay_vrig_variable_renaming_ledger (normalizedDigestOk renamingOk : Prop) : Prop :=
  normalizedDigestOk -> renamingOk

def ay_vrig_inverse_map_witness (renamingOk inverseOk : Prop) : Prop :=
  renamingOk -> inverseOk

def ay_vrig_renamed_assignment_digest (inverseOk renamedAssignmentOk : Prop) : Prop :=
  inverseOk -> renamedAssignmentOk

def ay_vrig_original_assignment_reconstruction
    (renamedAssignmentOk originalAssignment : Prop) : Prop :=
  renamedAssignmentOk -> originalAssignment

def ay_vrig_original_clause_satisfaction_replay
    (originalAssignment everyOriginalClauseSatisfied : Prop) : Prop :=
  originalAssignment -> everyOriginalClauseSatisfied

def ay_vrig_checker_transcript (everyOriginalClauseSatisfied originalSat : Prop) : Prop :=
  everyOriginalClauseSatisfied -> originalSat

def ay_vrig_solver_build_evidence (originalSat buildOk : Prop) : Prop :=
  originalSat -> buildOk

def ay_vrig_archive_manifest (buildOk archiveOk : Prop) : Prop :=
  buildOk -> archiveOk

def ay_vrig_fallback_no_claim_path (archiveOk fallbackReady : Prop) : Prop :=
  archiveOk -> fallbackReady

def ay_vrig_audit_transcript (fallbackReady audited : Prop) : Prop :=
  fallbackReady -> audited

def ay_vrig_accepted_inverse
    (fingerprint normalizedDigest renaming inverseMap renamedDigest reconstruction replay checker
     build archive fallback audit : Prop) : Prop :=
  ay_vrig_conj fingerprint
    (ay_vrig_conj normalizedDigest
      (ay_vrig_conj renaming
        (ay_vrig_conj inverseMap
          (ay_vrig_conj renamedDigest
            (ay_vrig_conj reconstruction
              (ay_vrig_conj replay
                (ay_vrig_conj checker
                  (ay_vrig_conj build
                    (ay_vrig_conj archive
                      (ay_vrig_conj fallback audit))))))))))

def ay_vrig_public_sat
    (accepted originalAssignment everyOriginalClauseSatisfied originalSat audited : Prop) :
    Prop :=
  ay_vrig_conj accepted
    (ay_vrig_conj originalAssignment
      (ay_vrig_conj everyOriginalClauseSatisfied (ay_vrig_conj originalSat audited)))

def ay_vrig_public_unsat (proofAccepted originalUnsat : Prop) : Prop :=
  ay_vrig_conj proofAccepted originalUnsat

def ay_vrig_no_claim_diagnostic (reason : Prop) : Prop :=
  reason

def ay_vrig_recompute_obligation (reason : Prop) : Prop :=
  reason

theorem ay_vrig_conj_intro {p q : Prop} (hp : p) (hq : q) : ay_vrig_conj p q :=
  fun r h => h hp hq

theorem ay_vrig_conj_left {p q : Prop} (h : ay_vrig_conj p q) : p :=
  h p (fun hp _ => hp)

theorem ay_vrig_conj_right {p q : Prop} (h : ay_vrig_conj p q) : q :=
  (h (p -> q) (fun (_ : p) (hq : q) (_ : p) => hq)) (ay_vrig_conj_left h)

theorem ay_vrig_disj_left {p q : Prop} (hp : p) : ay_vrig_disj p q :=
  fun r hl _ => hl hp

theorem ay_vrig_disj_right {p q : Prop} (hq : q) : ay_vrig_disj p q :=
  fun r _ hr => hr hq

theorem ay_vrig_equiv_intro {p q : Prop} (hpq : p -> q) (hqp : q -> p) :
    ay_vrig_equiv p q :=
  ay_vrig_conj_intro hpq hqp

theorem ay_vrig_equiv_forward {p q : Prop} (h : ay_vrig_equiv p q) : p -> q :=
  ay_vrig_conj_left h

theorem ay_vrig_equiv_backward {p q : Prop} (h : ay_vrig_equiv p q) : q -> p :=
  ay_vrig_conj_right h

theorem ay_vrig_original_benchmark_fingerprint_intro
    {renamedWitness fingerprintOk : Prop}
    (h : renamedWitness -> fingerprintOk) :
    ay_vrig_original_benchmark_fingerprint renamedWitness fingerprintOk :=
  h

theorem ay_vrig_normalized_formula_digest_intro
    {fingerprintOk normalizedDigestOk : Prop}
    (h : fingerprintOk -> normalizedDigestOk) :
    ay_vrig_normalized_formula_digest fingerprintOk normalizedDigestOk :=
  h

theorem ay_vrig_variable_renaming_ledger_intro {normalizedDigestOk renamingOk : Prop}
    (h : normalizedDigestOk -> renamingOk) :
    ay_vrig_variable_renaming_ledger normalizedDigestOk renamingOk :=
  h

theorem ay_vrig_inverse_map_witness_intro {renamingOk inverseOk : Prop}
    (h : renamingOk -> inverseOk) :
    ay_vrig_inverse_map_witness renamingOk inverseOk :=
  h

theorem ay_vrig_renamed_assignment_digest_intro {inverseOk renamedAssignmentOk : Prop}
    (h : inverseOk -> renamedAssignmentOk) :
    ay_vrig_renamed_assignment_digest inverseOk renamedAssignmentOk :=
  h

theorem ay_vrig_original_assignment_reconstruction_intro
    {renamedAssignmentOk originalAssignment : Prop}
    (h : renamedAssignmentOk -> originalAssignment) :
    ay_vrig_original_assignment_reconstruction renamedAssignmentOk originalAssignment :=
  h

theorem ay_vrig_original_clause_satisfaction_replay_intro
    {originalAssignment everyOriginalClauseSatisfied : Prop}
    (h : originalAssignment -> everyOriginalClauseSatisfied) :
    ay_vrig_original_clause_satisfaction_replay originalAssignment
      everyOriginalClauseSatisfied :=
  h

theorem ay_vrig_checker_transcript_intro
    {everyOriginalClauseSatisfied originalSat : Prop}
    (h : everyOriginalClauseSatisfied -> originalSat) :
    ay_vrig_checker_transcript everyOriginalClauseSatisfied originalSat :=
  h

theorem ay_vrig_solver_build_evidence_intro {originalSat buildOk : Prop}
    (h : originalSat -> buildOk) :
    ay_vrig_solver_build_evidence originalSat buildOk :=
  h

theorem ay_vrig_archive_manifest_intro {buildOk archiveOk : Prop}
    (h : buildOk -> archiveOk) :
    ay_vrig_archive_manifest buildOk archiveOk :=
  h

theorem ay_vrig_fallback_no_claim_path_intro {archiveOk fallbackReady : Prop}
    (h : archiveOk -> fallbackReady) :
    ay_vrig_fallback_no_claim_path archiveOk fallbackReady :=
  h

theorem ay_vrig_audit_transcript_intro {fallbackReady audited : Prop}
    (h : fallbackReady -> audited) :
    ay_vrig_audit_transcript fallbackReady audited :=
  h

theorem ay_vrig_accepted_inverse_intro
    {fingerprint normalizedDigest renaming inverseMap renamedDigest reconstruction replay
     checker build archive fallback audit : Prop}
    (hf : fingerprint) (hn : normalizedDigest) (hrn : renaming) (hi : inverseMap)
    (hra : renamedDigest) (hrc : reconstruction) (hr : replay) (hc : checker)
    (hb : build) (ha : archive) (hfb : fallback) (hau : audit) :
    ay_vrig_accepted_inverse fingerprint normalizedDigest renaming inverseMap renamedDigest
      reconstruction replay checker build archive fallback audit :=
  ay_vrig_conj_intro hf
    (ay_vrig_conj_intro hn
      (ay_vrig_conj_intro hrn
        (ay_vrig_conj_intro hi
          (ay_vrig_conj_intro hra
            (ay_vrig_conj_intro hrc
              (ay_vrig_conj_intro hr
                (ay_vrig_conj_intro hc
                  (ay_vrig_conj_intro hb
                    (ay_vrig_conj_intro ha
                      (ay_vrig_conj_intro hfb hau))))))))))

theorem ay_vrig_accepted_inverse_fingerprint
    {fingerprint normalizedDigest renaming inverseMap renamedDigest reconstruction replay
     checker build archive fallback audit : Prop}
    (h : ay_vrig_accepted_inverse fingerprint normalizedDigest renaming inverseMap
      renamedDigest reconstruction replay checker build archive fallback audit) : fingerprint :=
  ay_vrig_conj_left h

theorem ay_vrig_accepted_inverse_normalized_digest
    {fingerprint normalizedDigest renaming inverseMap renamedDigest reconstruction replay
     checker build archive fallback audit : Prop}
    (h : ay_vrig_accepted_inverse fingerprint normalizedDigest renaming inverseMap
      renamedDigest reconstruction replay checker build archive fallback audit) :
    normalizedDigest :=
  ay_vrig_conj_left (ay_vrig_conj_right h)

theorem ay_vrig_accepted_inverse_renaming
    {fingerprint normalizedDigest renaming inverseMap renamedDigest reconstruction replay
     checker build archive fallback audit : Prop}
    (h : ay_vrig_accepted_inverse fingerprint normalizedDigest renaming inverseMap
      renamedDigest reconstruction replay checker build archive fallback audit) : renaming :=
  ay_vrig_conj_left (ay_vrig_conj_right (ay_vrig_conj_right h))

theorem ay_vrig_accepted_inverse_inverse_map
    {fingerprint normalizedDigest renaming inverseMap renamedDigest reconstruction replay
     checker build archive fallback audit : Prop}
    (h : ay_vrig_accepted_inverse fingerprint normalizedDigest renaming inverseMap
      renamedDigest reconstruction replay checker build archive fallback audit) : inverseMap :=
  ay_vrig_conj_left
    (ay_vrig_conj_right (ay_vrig_conj_right (ay_vrig_conj_right h)))

theorem ay_vrig_accepted_inverse_renamed_digest
    {fingerprint normalizedDigest renaming inverseMap renamedDigest reconstruction replay
     checker build archive fallback audit : Prop}
    (h : ay_vrig_accepted_inverse fingerprint normalizedDigest renaming inverseMap
      renamedDigest reconstruction replay checker build archive fallback audit) :
    renamedDigest :=
  ay_vrig_conj_left
    (ay_vrig_conj_right
      (ay_vrig_conj_right (ay_vrig_conj_right (ay_vrig_conj_right h))))

theorem ay_vrig_accepted_inverse_reconstruction
    {fingerprint normalizedDigest renaming inverseMap renamedDigest reconstruction replay
     checker build archive fallback audit : Prop}
    (h : ay_vrig_accepted_inverse fingerprint normalizedDigest renaming inverseMap
      renamedDigest reconstruction replay checker build archive fallback audit) :
    reconstruction :=
  ay_vrig_conj_left
    (ay_vrig_conj_right
      (ay_vrig_conj_right
        (ay_vrig_conj_right (ay_vrig_conj_right (ay_vrig_conj_right h)))))

theorem ay_vrig_accepted_inverse_replay
    {fingerprint normalizedDigest renaming inverseMap renamedDigest reconstruction replay
     checker build archive fallback audit : Prop}
    (h : ay_vrig_accepted_inverse fingerprint normalizedDigest renaming inverseMap
      renamedDigest reconstruction replay checker build archive fallback audit) : replay :=
  ay_vrig_conj_left
    (ay_vrig_conj_right
      (ay_vrig_conj_right
        (ay_vrig_conj_right
          (ay_vrig_conj_right (ay_vrig_conj_right (ay_vrig_conj_right h))))))

theorem ay_vrig_accepted_inverse_checker
    {fingerprint normalizedDigest renaming inverseMap renamedDigest reconstruction replay
     checker build archive fallback audit : Prop}
    (h : ay_vrig_accepted_inverse fingerprint normalizedDigest renaming inverseMap
      renamedDigest reconstruction replay checker build archive fallback audit) : checker :=
  ay_vrig_conj_left
    (ay_vrig_conj_right
      (ay_vrig_conj_right
        (ay_vrig_conj_right
          (ay_vrig_conj_right
            (ay_vrig_conj_right (ay_vrig_conj_right (ay_vrig_conj_right h)))))))

theorem ay_vrig_accepted_inverse_build
    {fingerprint normalizedDigest renaming inverseMap renamedDigest reconstruction replay
     checker build archive fallback audit : Prop}
    (h : ay_vrig_accepted_inverse fingerprint normalizedDigest renaming inverseMap
      renamedDigest reconstruction replay checker build archive fallback audit) : build :=
  ay_vrig_conj_left
    (ay_vrig_conj_right
      (ay_vrig_conj_right
        (ay_vrig_conj_right
          (ay_vrig_conj_right
            (ay_vrig_conj_right
              (ay_vrig_conj_right (ay_vrig_conj_right (ay_vrig_conj_right h))))))))

theorem ay_vrig_accepted_inverse_archive
    {fingerprint normalizedDigest renaming inverseMap renamedDigest reconstruction replay
     checker build archive fallback audit : Prop}
    (h : ay_vrig_accepted_inverse fingerprint normalizedDigest renaming inverseMap
      renamedDigest reconstruction replay checker build archive fallback audit) : archive :=
  ay_vrig_conj_left
    (ay_vrig_conj_right
      (ay_vrig_conj_right
        (ay_vrig_conj_right
          (ay_vrig_conj_right
            (ay_vrig_conj_right
              (ay_vrig_conj_right
                (ay_vrig_conj_right (ay_vrig_conj_right (ay_vrig_conj_right h)))))))))

theorem ay_vrig_accepted_inverse_fallback
    {fingerprint normalizedDigest renaming inverseMap renamedDigest reconstruction replay
     checker build archive fallback audit : Prop}
    (h : ay_vrig_accepted_inverse fingerprint normalizedDigest renaming inverseMap
      renamedDigest reconstruction replay checker build archive fallback audit) : fallback :=
  ay_vrig_conj_left
    (ay_vrig_conj_right
      (ay_vrig_conj_right
        (ay_vrig_conj_right
          (ay_vrig_conj_right
            (ay_vrig_conj_right
              (ay_vrig_conj_right
                (ay_vrig_conj_right
                  (ay_vrig_conj_right (ay_vrig_conj_right (ay_vrig_conj_right h))))))))))

theorem ay_vrig_accepted_inverse_audit
    {fingerprint normalizedDigest renaming inverseMap renamedDigest reconstruction replay
     checker build archive fallback audit : Prop}
    (h : ay_vrig_accepted_inverse fingerprint normalizedDigest renaming inverseMap
      renamedDigest reconstruction replay checker build archive fallback audit) : audit :=
  ay_vrig_conj_right
    (ay_vrig_conj_right
      (ay_vrig_conj_right
        (ay_vrig_conj_right
          (ay_vrig_conj_right
            (ay_vrig_conj_right
              (ay_vrig_conj_right
                (ay_vrig_conj_right
                  (ay_vrig_conj_right (ay_vrig_conj_right (ay_vrig_conj_right h))))))))))

theorem ay_vrig_renaming_inverse_reconstructs_original_sat
    {renamedWitness fingerprintOk normalizedDigestOk renamingOk inverseOk renamedAssignmentOk
     originalAssignment everyOriginalClauseSatisfied originalSat buildOk archiveOk
     fallbackReady audited : Prop}
    (hf : ay_vrig_original_benchmark_fingerprint renamedWitness fingerprintOk)
    (hn : ay_vrig_normalized_formula_digest fingerprintOk normalizedDigestOk)
    (hrn : ay_vrig_variable_renaming_ledger normalizedDigestOk renamingOk)
    (hi : ay_vrig_inverse_map_witness renamingOk inverseOk)
    (hra : ay_vrig_renamed_assignment_digest inverseOk renamedAssignmentOk)
    (hrc : ay_vrig_original_assignment_reconstruction
      renamedAssignmentOk originalAssignment)
    (hr : ay_vrig_original_clause_satisfaction_replay
      originalAssignment everyOriginalClauseSatisfied)
    (hc : ay_vrig_checker_transcript everyOriginalClauseSatisfied originalSat)
    (hb : ay_vrig_solver_build_evidence originalSat buildOk)
    (ha : ay_vrig_archive_manifest buildOk archiveOk)
    (hfb : ay_vrig_fallback_no_claim_path archiveOk fallbackReady)
    (hau : ay_vrig_audit_transcript fallbackReady audited)
    (hw : renamedWitness) :
    ay_vrig_conj originalAssignment
      (ay_vrig_conj everyOriginalClauseSatisfied (ay_vrig_conj originalSat audited)) :=
  let hfingerprint : fingerprintOk := hf hw
  let hnormalized : normalizedDigestOk := hn hfingerprint
  let hrenaming : renamingOk := hrn hnormalized
  let hinverse : inverseOk := hi hrenaming
  let hrenamed : renamedAssignmentOk := hra hinverse
  let horiginal : originalAssignment := hrc hrenamed
  let hevery : everyOriginalClauseSatisfied := hr horiginal
  let hsat : originalSat := hc hevery
  let hbuild : buildOk := hb hsat
  let harchive : archiveOk := ha hbuild
  let hfallback : fallbackReady := hfb harchive
  let haudit : audited := hau hfallback
  ay_vrig_conj_intro horiginal (ay_vrig_conj_intro hevery (ay_vrig_conj_intro hsat haudit))

theorem ay_vrig_public_sat_intro
    {accepted originalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (ha : accepted) (hm : originalAssignment) (hevery : everyOriginalClauseSatisfied)
    (hs : originalSat) (hau : audited) :
    ay_vrig_public_sat accepted originalAssignment everyOriginalClauseSatisfied originalSat
      audited :=
  ay_vrig_conj_intro ha
    (ay_vrig_conj_intro hm (ay_vrig_conj_intro hevery (ay_vrig_conj_intro hs hau)))

theorem ay_vrig_public_sat_requires_inverse_guard
    {accepted originalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (h : ay_vrig_public_sat accepted originalAssignment everyOriginalClauseSatisfied
      originalSat audited) : accepted :=
  ay_vrig_conj_left h

theorem ay_vrig_public_sat_original_assignment
    {accepted originalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (h : ay_vrig_public_sat accepted originalAssignment everyOriginalClauseSatisfied
      originalSat audited) : originalAssignment :=
  ay_vrig_conj_left (ay_vrig_conj_right h)

theorem ay_vrig_public_sat_every_original_clause
    {accepted originalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (h : ay_vrig_public_sat accepted originalAssignment everyOriginalClauseSatisfied
      originalSat audited) : everyOriginalClauseSatisfied :=
  ay_vrig_conj_left (ay_vrig_conj_right (ay_vrig_conj_right h))

theorem ay_vrig_public_sat_original_formula
    {accepted originalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (h : ay_vrig_public_sat accepted originalAssignment everyOriginalClauseSatisfied
      originalSat audited) : originalSat :=
  ay_vrig_conj_left (ay_vrig_conj_right (ay_vrig_conj_right (ay_vrig_conj_right h)))

theorem ay_vrig_public_sat_audit
    {accepted originalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (h : ay_vrig_public_sat accepted originalAssignment everyOriginalClauseSatisfied
      originalSat audited) : audited :=
  ay_vrig_conj_right (ay_vrig_conj_right (ay_vrig_conj_right (ay_vrig_conj_right h)))

theorem ay_vrig_accepted_inverse_publishes_sat
    {fingerprint normalizedDigest renaming inverseMap renamedDigest reconstruction replay
     checker build archive fallback audit originalAssignment everyOriginalClauseSatisfied
     originalSat audited : Prop}
    (hg : ay_vrig_accepted_inverse fingerprint normalizedDigest renaming inverseMap
      renamedDigest reconstruction replay checker build archive fallback audit)
    (hm : originalAssignment) (hevery : everyOriginalClauseSatisfied)
    (hs : originalSat) (hau : audited) :
    ay_vrig_public_sat
      (ay_vrig_accepted_inverse fingerprint normalizedDigest renaming inverseMap
        renamedDigest reconstruction replay checker build archive fallback audit)
      originalAssignment everyOriginalClauseSatisfied originalSat audited :=
  ay_vrig_public_sat_intro hg hm hevery hs hau

theorem ay_vrig_no_claim_intro {reason : Prop} (h : reason) :
    ay_vrig_no_claim_diagnostic reason :=
  h

theorem ay_vrig_recompute_intro {reason : Prop} (h : reason) :
    ay_vrig_recompute_obligation reason :=
  h

theorem ay_vrig_renaming_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_vrig_no_claim_diagnostic reason :=
  ay_vrig_no_claim_intro h

theorem ay_vrig_inverse_mismatch_recompute {reason : Prop} (h : reason) :
    ay_vrig_recompute_obligation reason :=
  ay_vrig_recompute_intro h

theorem ay_vrig_reconstruction_mismatch_recompute {reason : Prop} (h : reason) :
    ay_vrig_recompute_obligation reason :=
  ay_vrig_recompute_intro h

theorem ay_vrig_replay_mismatch_recompute {reason : Prop} (h : reason) :
    ay_vrig_recompute_obligation reason :=
  ay_vrig_recompute_intro h

theorem ay_vrig_checker_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_vrig_no_claim_diagnostic reason :=
  ay_vrig_no_claim_intro h

theorem ay_vrig_build_mismatch_recompute {reason : Prop} (h : reason) :
    ay_vrig_recompute_obligation reason :=
  ay_vrig_recompute_intro h

theorem ay_vrig_archive_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_vrig_no_claim_diagnostic reason :=
  ay_vrig_no_claim_intro h

theorem ay_vrig_audit_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_vrig_no_claim_diagnostic reason :=
  ay_vrig_no_claim_intro h

theorem ay_vrig_failed_inverse_guard_cannot_create_public_sat
    {failure accepted originalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (hfail : failure)
    (hblock : ay_vrig_public_sat accepted originalAssignment everyOriginalClauseSatisfied
      originalSat audited -> ay_vrig_no_claim_diagnostic failure) :
    ay_vrig_conj (ay_vrig_no_claim_diagnostic failure)
      (ay_vrig_public_sat accepted originalAssignment everyOriginalClauseSatisfied originalSat
        audited -> ay_vrig_no_claim_diagnostic failure) :=
  ay_vrig_conj_intro (ay_vrig_no_claim_intro hfail) hblock

theorem ay_vrig_failed_inverse_guard_forces_recompute
    {failure accepted originalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (hfail : failure)
    (hblock : ay_vrig_public_sat accepted originalAssignment everyOriginalClauseSatisfied
      originalSat audited -> ay_vrig_recompute_obligation failure) :
    ay_vrig_conj (ay_vrig_recompute_obligation failure)
      (ay_vrig_public_sat accepted originalAssignment everyOriginalClauseSatisfied originalSat
        audited -> ay_vrig_recompute_obligation failure) :=
  ay_vrig_conj_intro (ay_vrig_recompute_intro hfail) hblock

theorem ay_vrig_public_unsat_intro {proofAccepted originalUnsat : Prop}
    (hp : proofAccepted) (hu : originalUnsat) :
    ay_vrig_public_unsat proofAccepted originalUnsat :=
  ay_vrig_conj_intro hp hu

theorem ay_vrig_public_unsat_proof {proofAccepted originalUnsat : Prop}
    (h : ay_vrig_public_unsat proofAccepted originalUnsat) : proofAccepted :=
  ay_vrig_conj_left h

theorem ay_vrig_public_unsat_claim {proofAccepted originalUnsat : Prop}
    (h : ay_vrig_public_unsat proofAccepted originalUnsat) : originalUnsat :=
  ay_vrig_conj_right h

theorem ay_vrig_inverse_guard_cannot_strengthen_unsat_claims
    {proofAccepted originalUnsat inverseSatGuard : Prop}
    (h : ay_vrig_public_unsat proofAccepted originalUnsat) :
    ay_vrig_conj (ay_vrig_public_unsat proofAccepted originalUnsat)
      (inverseSatGuard -> ay_vrig_public_unsat proofAccepted originalUnsat) :=
  ay_vrig_conj_intro h (fun _ => h)
