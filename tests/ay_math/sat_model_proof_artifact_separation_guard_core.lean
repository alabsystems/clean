/-!
  SAT-COMP/ay model/proof artifact separation guard.

  This self-contained package models the obligations that keep SAT model
  artifacts and UNSAT proof artifacts separated under the selected status.
-/

def ay_pasg_conj (p q : Prop) : Prop :=
  forall r : Prop, (p -> q -> r) -> r

def ay_pasg_disj (p q : Prop) : Prop :=
  forall r : Prop, (p -> r) -> (q -> r) -> r

def ay_pasg_benchmark_fingerprint (statusDigest benchmarkOk : Prop) : Prop :=
  statusDigest -> benchmarkOk

def ay_pasg_status_digest (benchmarkOk statusOk : Prop) : Prop :=
  benchmarkOk -> statusOk

def ay_pasg_model_artifact_digest_option (statusOk modelArtifactOk : Prop) : Prop :=
  statusOk -> modelArtifactOk

def ay_pasg_proof_artifact_digest_option (statusOk proofArtifactOk : Prop) : Prop :=
  statusOk -> proofArtifactOk

def ay_pasg_artifact_kind_manifest
    (modelArtifactOk proofArtifactOk kindOk : Prop) : Prop :=
  modelArtifactOk -> proofArtifactOk -> kindOk

def ay_pasg_archive_path_map_digest (kindOk pathMapOk : Prop) : Prop :=
  kindOk -> pathMapOk

def ay_pasg_checker_transcript_for_selected_kind
    (pathMapOk checkerOk : Prop) : Prop :=
  pathMapOk -> checkerOk

def ay_pasg_stale_artifact_quarantine_ledger
    (checkerOk quarantineOk : Prop) : Prop :=
  checkerOk -> quarantineOk

def ay_pasg_solver_build_evidence (quarantineOk buildOk : Prop) : Prop :=
  quarantineOk -> buildOk

def ay_pasg_validator_gate (buildOk validatorOk : Prop) : Prop :=
  buildOk -> validatorOk

def ay_pasg_fallback_no_claim_path (validatorOk fallbackReady : Prop) : Prop :=
  validatorOk -> fallbackReady

def ay_pasg_audit_transcript (fallbackReady audited : Prop) : Prop :=
  fallbackReady -> audited

def ay_pasg_accepted_separation
    (benchmark status modelArtifact proofArtifact kind pathMap checker quarantine build
     validator fallback audit : Prop) : Prop :=
  forall r : Prop,
    (benchmark -> status -> modelArtifact -> proofArtifact -> kind -> pathMap -> checker ->
      quarantine -> build -> validator -> fallback -> audit -> r) -> r

def ay_pasg_public_sat
    (accepted selectedStatus modelArtifact modelChecker validatorOk audited : Prop) : Prop :=
  ay_pasg_conj accepted
    (ay_pasg_conj selectedStatus
      (ay_pasg_conj modelArtifact (ay_pasg_conj modelChecker
        (ay_pasg_conj validatorOk audited))))

def ay_pasg_public_unsat
    (accepted selectedStatus proofArtifact proofChecker validatorOk audited : Prop) : Prop :=
  ay_pasg_conj accepted
    (ay_pasg_conj selectedStatus
      (ay_pasg_conj proofArtifact (ay_pasg_conj proofChecker
        (ay_pasg_conj validatorOk audited))))

def ay_pasg_no_claim_diagnostic (reason : Prop) : Prop :=
  reason

def ay_pasg_recompute_obligation (reason : Prop) : Prop :=
  reason

theorem ay_pasg_conj_intro {p q : Prop} (hp : p) (hq : q) : ay_pasg_conj p q :=
  fun r h => h hp hq

theorem ay_pasg_conj_left {p q : Prop} (h : ay_pasg_conj p q) : p :=
  h p (fun hp _ => hp)

theorem ay_pasg_conj_right {p q : Prop} (h : ay_pasg_conj p q) : q :=
  (h (p -> q) (fun (_ : p) (hq : q) (_ : p) => hq)) (ay_pasg_conj_left h)

theorem ay_pasg_disj_left {p q : Prop} (hp : p) : ay_pasg_disj p q :=
  fun r hl _ => hl hp

theorem ay_pasg_disj_right {p q : Prop} (hq : q) : ay_pasg_disj p q :=
  fun r _ hr => hr hq

theorem ay_pasg_benchmark_fingerprint_intro {statusDigest benchmarkOk : Prop}
    (h : statusDigest -> benchmarkOk) :
    ay_pasg_benchmark_fingerprint statusDigest benchmarkOk :=
  h

theorem ay_pasg_status_digest_intro {benchmarkOk statusOk : Prop}
    (h : benchmarkOk -> statusOk) :
    ay_pasg_status_digest benchmarkOk statusOk :=
  h

theorem ay_pasg_model_artifact_digest_option_intro {statusOk modelArtifactOk : Prop}
    (h : statusOk -> modelArtifactOk) :
    ay_pasg_model_artifact_digest_option statusOk modelArtifactOk :=
  h

theorem ay_pasg_proof_artifact_digest_option_intro {statusOk proofArtifactOk : Prop}
    (h : statusOk -> proofArtifactOk) :
    ay_pasg_proof_artifact_digest_option statusOk proofArtifactOk :=
  h

theorem ay_pasg_artifact_kind_manifest_intro
    {modelArtifactOk proofArtifactOk kindOk : Prop}
    (h : modelArtifactOk -> proofArtifactOk -> kindOk) :
    ay_pasg_artifact_kind_manifest modelArtifactOk proofArtifactOk kindOk :=
  h

theorem ay_pasg_archive_path_map_digest_intro {kindOk pathMapOk : Prop}
    (h : kindOk -> pathMapOk) :
    ay_pasg_archive_path_map_digest kindOk pathMapOk :=
  h

theorem ay_pasg_checker_transcript_for_selected_kind_intro
    {pathMapOk checkerOk : Prop}
    (h : pathMapOk -> checkerOk) :
    ay_pasg_checker_transcript_for_selected_kind pathMapOk checkerOk :=
  h

theorem ay_pasg_stale_artifact_quarantine_ledger_intro
    {checkerOk quarantineOk : Prop}
    (h : checkerOk -> quarantineOk) :
    ay_pasg_stale_artifact_quarantine_ledger checkerOk quarantineOk :=
  h

theorem ay_pasg_solver_build_evidence_intro {quarantineOk buildOk : Prop}
    (h : quarantineOk -> buildOk) :
    ay_pasg_solver_build_evidence quarantineOk buildOk :=
  h

theorem ay_pasg_validator_gate_intro {buildOk validatorOk : Prop}
    (h : buildOk -> validatorOk) :
    ay_pasg_validator_gate buildOk validatorOk :=
  h

theorem ay_pasg_fallback_no_claim_path_intro {validatorOk fallbackReady : Prop}
    (h : validatorOk -> fallbackReady) :
    ay_pasg_fallback_no_claim_path validatorOk fallbackReady :=
  h

theorem ay_pasg_audit_transcript_intro {fallbackReady audited : Prop}
    (h : fallbackReady -> audited) :
    ay_pasg_audit_transcript fallbackReady audited :=
  h

theorem ay_pasg_accepted_separation_intro
    {benchmark status modelArtifact proofArtifact kind pathMap checker quarantine build
     validator fallback audit : Prop}
    (hb : benchmark) (hs : status) (hm : modelArtifact) (hp : proofArtifact)
    (hk : kind) (hpath : pathMap) (hc : checker) (hq : quarantine) (hbuild : build)
    (hv : validator) (hfb : fallback) (hau : audit) :
    ay_pasg_accepted_separation benchmark status modelArtifact proofArtifact kind pathMap
      checker quarantine build validator fallback audit :=
  fun r k => k hb hs hm hp hk hpath hc hq hbuild hv hfb hau

theorem ay_pasg_accepted_separation_status
    {benchmark status modelArtifact proofArtifact kind pathMap checker quarantine build
     validator fallback audit : Prop}
    (h : ay_pasg_accepted_separation benchmark status modelArtifact proofArtifact kind
      pathMap checker quarantine build validator fallback audit) : status :=
  h status (fun _ hs _ _ _ _ _ _ _ _ _ _ => hs)

theorem ay_pasg_accepted_separation_model
    {benchmark status modelArtifact proofArtifact kind pathMap checker quarantine build
     validator fallback audit : Prop}
    (h : ay_pasg_accepted_separation benchmark status modelArtifact proofArtifact kind
      pathMap checker quarantine build validator fallback audit) : modelArtifact :=
  h modelArtifact (fun _ _ hm _ _ _ _ _ _ _ _ _ => hm)

theorem ay_pasg_accepted_separation_proof
    {benchmark status modelArtifact proofArtifact kind pathMap checker quarantine build
     validator fallback audit : Prop}
    (h : ay_pasg_accepted_separation benchmark status modelArtifact proofArtifact kind
      pathMap checker quarantine build validator fallback audit) : proofArtifact :=
  h proofArtifact (fun _ _ _ hp _ _ _ _ _ _ _ _ => hp)

theorem ay_pasg_accepted_separation_checker
    {benchmark status modelArtifact proofArtifact kind pathMap checker quarantine build
     validator fallback audit : Prop}
    (h : ay_pasg_accepted_separation benchmark status modelArtifact proofArtifact kind
      pathMap checker quarantine build validator fallback audit) : checker :=
  h checker (fun _ _ _ _ _ _ hc _ _ _ _ _ => hc)

theorem ay_pasg_accepted_separation_validator
    {benchmark status modelArtifact proofArtifact kind pathMap checker quarantine build
     validator fallback audit : Prop}
    (h : ay_pasg_accepted_separation benchmark status modelArtifact proofArtifact kind
      pathMap checker quarantine build validator fallback audit) : validator :=
  h validator (fun _ _ _ _ _ _ _ _ _ hv _ _ => hv)

theorem ay_pasg_accepted_separation_audit
    {benchmark status modelArtifact proofArtifact kind pathMap checker quarantine build
     validator fallback audit : Prop}
    (h : ay_pasg_accepted_separation benchmark status modelArtifact proofArtifact kind
      pathMap checker quarantine build validator fallback audit) : audit :=
  h audit (fun _ _ _ _ _ _ _ _ _ _ _ hau => hau)

theorem ay_pasg_public_sat_intro
    {accepted selectedStatus modelArtifact modelChecker validatorOk audited : Prop}
    (ha : accepted) (hs : selectedStatus) (hm : modelArtifact) (hc : modelChecker)
    (hv : validatorOk) (hau : audited) :
    ay_pasg_public_sat accepted selectedStatus modelArtifact modelChecker validatorOk
      audited :=
  ay_pasg_conj_intro ha
    (ay_pasg_conj_intro hs
      (ay_pasg_conj_intro hm (ay_pasg_conj_intro hc
        (ay_pasg_conj_intro hv hau))))

theorem ay_pasg_public_unsat_intro
    {accepted selectedStatus proofArtifact proofChecker validatorOk audited : Prop}
    (ha : accepted) (hs : selectedStatus) (hp : proofArtifact) (hc : proofChecker)
    (hv : validatorOk) (hau : audited) :
    ay_pasg_public_unsat accepted selectedStatus proofArtifact proofChecker validatorOk
      audited :=
  ay_pasg_conj_intro ha
    (ay_pasg_conj_intro hs
      (ay_pasg_conj_intro hp (ay_pasg_conj_intro hc
        (ay_pasg_conj_intro hv hau))))

theorem ay_pasg_sat_publication_uses_model_checker_only
    {benchmark status modelArtifact proofArtifact kind pathMap checker quarantine build
     validator fallback audit : Prop}
    (h : ay_pasg_accepted_separation benchmark status modelArtifact proofArtifact kind
      pathMap checker quarantine build validator fallback audit) :
    ay_pasg_public_sat
      (ay_pasg_accepted_separation benchmark status modelArtifact proofArtifact kind pathMap
        checker quarantine build validator fallback audit)
      status modelArtifact checker validator audit :=
  ay_pasg_public_sat_intro
    h
    (ay_pasg_accepted_separation_status h)
    (ay_pasg_accepted_separation_model h)
    (ay_pasg_accepted_separation_checker h)
    (ay_pasg_accepted_separation_validator h)
    (ay_pasg_accepted_separation_audit h)

theorem ay_pasg_unsat_publication_uses_proof_checker_only
    {benchmark status modelArtifact proofArtifact kind pathMap checker quarantine build
     validator fallback audit : Prop}
    (h : ay_pasg_accepted_separation benchmark status modelArtifact proofArtifact kind
      pathMap checker quarantine build validator fallback audit) :
    ay_pasg_public_unsat
      (ay_pasg_accepted_separation benchmark status modelArtifact proofArtifact kind pathMap
        checker quarantine build validator fallback audit)
      status proofArtifact checker validator audit :=
  ay_pasg_public_unsat_intro
    h
    (ay_pasg_accepted_separation_status h)
    (ay_pasg_accepted_separation_proof h)
    (ay_pasg_accepted_separation_checker h)
    (ay_pasg_accepted_separation_validator h)
    (ay_pasg_accepted_separation_audit h)

theorem ay_pasg_stale_opposite_kind_artifact_quarantined
    {staleOppositeArtifact quarantine noClaim recompute : Prop}
    (hq : staleOppositeArtifact -> quarantine)
    (hn : quarantine -> noClaim)
    (hr : quarantine -> recompute)
    (hs : staleOppositeArtifact) :
    ay_pasg_conj noClaim recompute :=
  let hquarantine : quarantine := hq hs
  ay_pasg_conj_intro (hn hquarantine) (hr hquarantine)

theorem ay_pasg_no_claim_intro {reason : Prop} (h : reason) :
    ay_pasg_no_claim_diagnostic reason :=
  h

theorem ay_pasg_recompute_intro {reason : Prop} (h : reason) :
    ay_pasg_recompute_obligation reason :=
  h

theorem ay_pasg_status_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_pasg_no_claim_diagnostic mismatch :=
  ay_pasg_no_claim_intro h

theorem ay_pasg_kind_mismatch_recompute {mismatch : Prop} (h : mismatch) :
    ay_pasg_recompute_obligation mismatch :=
  ay_pasg_recompute_intro h

theorem ay_pasg_path_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_pasg_no_claim_diagnostic mismatch :=
  ay_pasg_no_claim_intro h

theorem ay_pasg_model_mismatch_recompute {mismatch : Prop} (h : mismatch) :
    ay_pasg_recompute_obligation mismatch :=
  ay_pasg_recompute_intro h

theorem ay_pasg_proof_mismatch_recompute {mismatch : Prop} (h : mismatch) :
    ay_pasg_recompute_obligation mismatch :=
  ay_pasg_recompute_intro h

theorem ay_pasg_checker_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_pasg_no_claim_diagnostic mismatch :=
  ay_pasg_no_claim_intro h

theorem ay_pasg_build_mismatch_recompute {mismatch : Prop} (h : mismatch) :
    ay_pasg_recompute_obligation mismatch :=
  ay_pasg_recompute_intro h

theorem ay_pasg_validator_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_pasg_no_claim_diagnostic mismatch :=
  ay_pasg_no_claim_intro h

theorem ay_pasg_archive_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_pasg_no_claim_diagnostic mismatch :=
  ay_pasg_no_claim_intro h

theorem ay_pasg_audit_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_pasg_no_claim_diagnostic mismatch :=
  ay_pasg_no_claim_intro h

theorem ay_pasg_failed_separation_guard_cannot_bless_sat_publication
    {failure publicSat : Prop}
    (fallback : failure -> ay_pasg_no_claim_diagnostic failure)
    (noBless : ay_pasg_no_claim_diagnostic failure -> publicSat -> failure)
    (hfailure : failure) (hpublic : publicSat) : failure :=
  noBless (fallback hfailure) hpublic

theorem ay_pasg_failed_separation_guard_cannot_bless_unsat_publication
    {failure publicUnsat : Prop}
    (fallback : failure -> ay_pasg_no_claim_diagnostic failure)
    (noBless : ay_pasg_no_claim_diagnostic failure -> publicUnsat -> failure)
    (hfailure : failure) (hpublic : publicUnsat) : failure :=
  noBless (fallback hfailure) hpublic

theorem ay_pasg_failed_separation_guard_forces_recompute
    {failure : Prop}
    (fallback : failure -> ay_pasg_recompute_obligation failure)
    (hfailure : failure) :
    ay_pasg_recompute_obligation failure :=
  fallback hfailure
