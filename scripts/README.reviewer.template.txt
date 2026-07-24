Gamma-Crown Formal Verification Artifact (Clean, 15 conjectures C001-C030)

Files: verification_report.{txt,json,csv,tex}, environment.json,
       PAPER_ARTIFACT.md.

READ FIRST (#3502 honesty disclosure):
  Kernel type-checking alone is NOT a proof. Many gamma-crown claim-level
  theorems are Declaration::Opaque entries whose bodies are inhabited by
  @sorry -- logically vacuous placeholders. The artifact reports four
  distinct status values; ONLY "PROVED" entries are publishable proofs.

Status terms:
  PROVED     (VERIFIED_CONSTRUCTIVE) -- every claim is a real proof term;
             transitive axiom closure is contained in the foundational set.
  MIXED      (VERIFIED_MIXED)        -- zero domain axioms, but one or more
             claim-level Opaques are sorry-inhabited. Per-theorem audit
             required before any specific sub-claim is cited.
  SCAFFOLDED (VERIFIED_SCAFFOLDED)   -- zero domain axioms, ALL claim-level
             Opaques are sorry-inhabited. Kernel-accepted but logically
             vacuous.
  FORMAL     (VERIFIED_AXIOM_DEPENDENT) -- kernel type-checked; one or more
             Declaration::Axiom entries remain unproved.

Each conjecture runs in a fresh Clean kernel Environment. Every
declaration passes through add_decl(), which invokes the kernel type
checker. A conjecture is "PROVED" iff proof_mechanism == "constructive"
(see data/axiom_audit.json for the source-of-truth classification).

See PAPER_ARTIFACT.md for the full honesty narrative, the current count
per status bucket, and the Target A remediation plan. See
reports/audit/2026-04-19-auditor-round4.md for the audit that triggered
this disclosure format.

Reproduce: install Rust (https://rustup.rs/), then from the repo root run
./scripts/reproduce_gamma_crown.sh (or with --output-dir artifact/).
