# Project Mathbot — pointer

Mathbot is Clean's proof-synthesis research program: **AI proposes, the kernel
disposes**. This file is only a pointer; the program lives in:

- [`MATHBOT-CHARTER.md`](MATHBOT-CHARTER.md) — the charter: invariants, scope,
  and the kernel-as-ground-truth rule.
- `docs/MATHBOT.md` — the design: core loop
  (Propose/Trust/Import/Decompose), the worked `crown-proofs/` existence proof,
  and the honest accounting of what the bakeoff actually measures.
- `docs/mathbot/` — the working corpus: bakeoff design and
  reviews, HX-Test designs, policies (leakage, escalation, reproducibility),
  mining notes, and the publication path. Date-stamped session artifacts are
  under `docs/mathbot/archive/`.

Status: a research program, not a set of completed theorem claims. Nothing
counts as proved until the Clean kernel (or its exact external-certificate
verifier) checks it.
