# Acknowledgments and Citations

Clean is authored by Andrew Yates.

## Lean 4 Foundations

Clean is a from-scratch Rust implementation, but it is built against and explicitly credits the public Lean 4 ecosystem:

- Lean 4: <https://github.com/leanprover/lean4>
- Std4: <https://github.com/leanprover/std4>
- Mathlib4: <https://github.com/leanprover-community/mathlib4>
- lean4lean (Mario Carneiro): <https://github.com/digama0/lean4lean>
- lean4lean coverage matrix: docs/LEAN4LEAN_COVERAGE.md

`lean4lean` is the primary public kernel-reference specification used for Clean parity and cross-validation. Lean 4, Std4, and Mathlib4 are the upstream compatibility and import targets that Clean parses, loads, and checks.

## Self-Verification and Kernel Metatheory — Prior Art

Clean's self-verification effort (`clean-verify`: proving the kernel's own
metatheory — confluence, type preservation, strong normalization, subject
reduction, consistency — inside Clean, to retire admitted axioms such as
`church_rosser_whnf`) builds directly on, and is informed by, the following
prior work on formalized proof-assistant metatheory. These are the closest
comparable efforts and the source of several techniques we use or adapt:

- **Lean4Lean** — M. Carneiro, *"Lean4Lean: Towards a Formalized Metatheory for
  the Lean Theorem Prover"* (arXiv:2403.14064, 2024), and the `lean4lean` repo
  (<https://github.com/digama0/lean4lean>). A reimplementation of the Lean 4
  kernel in Lean 4 with an in-progress formalized metatheory. Lean uses the same
  **app-spine recursor encoding** as Clean (recursors are a `const` applied to a
  spine, with the same iota-cascade and over-application behavior), so its
  treatment of definitional equality and constructor injectivity is the most
  directly applicable reference for Clean's `church_rosser_whnf` work.
- **The Type Theory of Lean** — M. Carneiro, MSc thesis, Carnegie Mellon
  University, 2019. The declarative specification of Lean's type theory and
  definitional equality underlying the above.
- **Coq Coq Correct! / MetaCoq** — M. Sozeau, S. Boulier, Y. Forster,
  N. Tabareau, T. Winterhalter, *"Coq Coq Correct! Verification of Type Checking
  and Erasure for Coq, in Coq"* (POPL 2020). The gold-standard mechanization of a
  CIC kernel's metatheory in Coq, including **confluence of PCUIC reduction** and
  type-checker correctness, **modulo an axiomatized strong normalization** — the
  same Gödelian floor Clean adopts (a small, clearly-labeled SN assumption rather
  than a faked zero-axiom claim).
- **Candle** — O. Abrahamsson, M. O. Myreen, R. Kumar, T. Sewell, *"Candle: A
  Verified Implementation of HOL Light"* (ITP 2022). A HOL Light kernel verified
  down to machine code (a simpler logic than CIC, but an end-to-end
  self-verification reference).
- **Milawa** — J. Davis, M. O. Myreen, *"The reflective Milawa theorem prover is
  sound (down to the machine code that runs it)"* (Journal of Automated
  Reasoning, 2015). The canonical layered self-verifying prover (a weak
  first-order logic).
- **Parallel reduction / Church–Rosser** — M. Takahashi, *"Parallel Reductions
  in λ-Calculus"* (Information and Computation 118(1), 1995); W. W. Tait and
  P. Martin-Löf (the complete-development method). The confluence technique
  Clean's `par_reduces_p` / `par_strips_p` development adapts to the app-spine,
  cascading, over-applicable recursor setting.

Clean does not claim to surpass these efforts; MetaCoq and Lean4Lean are further
along on the metatheory. Clean's distinct contribution is the *combination* — a
from-scratch, `#![forbid(unsafe_code)]` Rust kernel that is simultaneously a
Lean-4-compatible production checker and a self-verified artifact, with the
trusted base collapsed toward three foundational axioms.

## TLA+ and TLAPS

`Clean-tla` depends on the public `tla-core` crate from the public <https://github.com/alabsystems/ty> repository. The names differ because `ty` is the repository name, while `tla-core` is the reusable library crate inside it that Clean imports. Clean reuses that shared public TLA+ AST and TLAPS obligation model instead of maintaining a divergent second TLA+ front end.

Additional references:

- `ty`: <https://github.com/alabsystems/ty>
- TLAPM: <https://github.com/tlaplus/tlapm>

## Mathverse Library Provenance

The Mathverse Library is built from upstream formal-math repositories. The complete credit and reproducibility record lives in:

- [data/MATHVERSE_PROVENANCE.md](data/MATHVERSE_PROVENANCE.md)
- [data/MATHVERSE_LIBRARIES.md](data/MATHVERSE_LIBRARIES.md)
- data/MATHVERSE_KERNEL_COMPATIBILITY.md

These files enumerate the imported repositories, commit hashes, download dates, file counts, declaration counts, and verification status used to build the released `.mathverse` shards.
