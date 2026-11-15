# ck0's remaining trust floor

`clean-ck0` is an independent, unproved Rust kernel implementation and a bounded
export reader. Its `#![forbid(unsafe_code)]` source and adversarial tests do not
prove correspondence to Lean or semantic soundness. Read the current rule and
refusal inventory in the Q2 report, and the Q0/Q4 reports for counted-quorum
limitations. Q6's candidate evidence does not change those claims.

A verdict still relies on:

1. Specification faithfulness of ck0's rules, parsing, policies, and any caller's
   translation. An accepted test is not a proof of rule faithfulness.
2. The compiler and backend, their bootstrap origins, compiler runtime, standard
   library, linker, system libraries, OS and hardware. Exact executable/sysroot
   identities narrow provenance; they do not prove translation correctness.
   Trust and stock rustc share ancestry. Their agreement does not remove this
   floor or constitute independent compiler implementations or classical DDC.
3. The actual resolved arithmetic and other dependencies. Standalone Clean uses
   registry num-bigint/num-integer/num-traits. Trust's temporal workspace patches
   those packages to ty's tla-bignum implementations. Qualifying the former does
   not qualify the latter. Export builds also enable sha2, serde and serde_json;
   the lock and recorded dependency-source inventories name the precise closure.
4. The shell, environment, build scripts, configuration and evidence producer.
   Q6's Python tool is unproved evidence bookkeeping. It is not a trusted proof
   checker, signed attestation, or assurance that all future build inputs have
   been discovered. Committed inventories and negative controls detect specified
   drift; a party replacing code and all its pins is outside that claim.

The old `MANIFEST.txt` is historical and stale. `CANDIDATE.json` names measured
source without genesis promotion. Binary digests in the qualification record do
not promise portable custody, bit-for-bit reproduction, or production deployment.
A full Q6 remains open until independent compilation and the exact production
closure are qualified and the genesis seed can honestly be promoted.

The adopted self-proof route remains a Lean-defined `kcheck` compiled by Trust,
by design until its gates hold in fact. Soundness is per universe bound; a
generation proves no more consistency than its base, and the quorum stays.
