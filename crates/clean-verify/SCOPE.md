# `clean-verify` scope

`clean-verify` defines metatheory for a reflected model of the Clean kernel and
registers the resulting definitions and proof terms in Clean's own kernel. It
does **not** prove that the full production Rust kernel or compiled binary
implements that model.

For the measured claim ledger and remaining gaps, see
`SELF_VERIFICATION_CERTIFICATE.md`.

## Standing under the adopted self-proof route

The metatheory this file describes is legacy and is not a step of the current
route. Two sources say so, each for its own part:

- **Decision R29** in `docs/DECISIONS.md`
  (2026-10-15) says the kernel's proof authority *becomes* `kcheck`, a checker
  "defined in Clean", once `kcheck_sound` is kernel-checked and re-checked by
  the other checkers it names; until then the authority stays with
  `clean-kernel` under the fenced theory. R29 is not a completed transfer. It
  stops the items its text lists (of those that touch this crate: new Crystal
  chains and link-5 widening on `clean-kernel`'s spine, and new `CandModel`
  fields or `CandModel`-conditional theorems for fragments with proof
  irrelevance) and caps other Crystal and `CandModel` work on `clean-kernel` at
  one non-merge commit in four (R4's cap). It keeps this crate's axiom census and the vacuity firewall in
  force.
- **The route of record**,
  `docs/plans/SELF_PROOF_EXECUTION_PLAN_2026-11-12.md`
  (adopted 2026-11-12, amending R29), is what takes the reflected-model stack
  off the route, what stops the Crystal work R29 only capped, and what says
  trusted checkers are to be written in Lean. By
  design the kernel's soundness theorem is to live in Lean packages under
  `theories/` (the specification in
  `theories/cic_l`, a set model in
  `theories/cic_l_model`, the checker
  in a package of its own, `theories/kcheck`): `kcheck` is to replay untrusted advice from `clean-kernel` and
  to be proved sound against the set model, per universe bound. Whether the
  checker or that theorem exists is read from the plan's unit rows and from
  `theories/`, never from this file.

So the sections below record what a reflected model of the Rust kernel
establishes. Where one of them says "current", "program" or "required", read it
as a description of this legacy stack, not of the route. On 2026-11-12 this
crate's git history showed no kernel-metatheory theorem added since R29
(2026-10-15). The crate's active work is elsewhere: the EvalIR semantics and the
feature-gated source-IR connections (see the crate documentation in
[`src/lib.rs`](src/lib.rs)).

## Reflected expression language

The current `KExpr` inductive has nine constructors
([`expr_model.rs`](src/spec/core_spec/expr_model.rs)):

| Constructor | Meaning | Production analogue |
|---|---|---|
| `sort level` | universe sort | `ExprKind::Sort` |
| `bvar index` | de Bruijn bound variable | `ExprKind::BVar` |
| `app fn arg` | application | `ExprKind::App` |
| `lam type body` | lambda abstraction | `ExprKind::Lam` |
| `pi domain codomain` | dependent function type | `ExprKind::Pi` |
| `const name levels` | named constant with universe arguments | `ExprKind::Const` |
| `let_ type value body` | genuine dependent let binder | `ExprKind::Let` |
| `proj structure index expr` | structure projection | `ExprKind::Proj` |
| `lit code` | reversibly tagged natural value or interned string identity | `ExprKind::Lit` |

The reflected language still omits production-only nodes such as `FVar`,
`MData`, `SProp`, `Squash`, cubical forms, and ZFC forms. Omission from `KExpr`
is a model boundary, not evidence that the production form is semantically
irrelevant.

## Judgment coverage is narrower than syntax coverage

Representing a constructor in `KExpr` does not mean every judgment handles it:

| Judgment | Current modeled rules | Important boundary |
|---|---|---|
| `Typing` / `has_type` | `sort`, `pi`, `lam`, `app`, `conv` | context-free fragment; deliberately no variable, constant, or let rule |
| `TypingCtx` | `var`, `sort`, `pi`, `lam`, `app`, `const`, `let_` | no projection or literal rule |
| `TypingCtxConv` | `TypingCtx` rules plus conversion and Nat/String literals | no projection rule; prelude/environment validity is separate |
| `KernelInfers` | `sort`, `bvar`, `pi`, `lam`, `const`, `app`, `let_`, `lit_nat`, `lit_string` | nine algorithmic arms; no projection arm or general universe-instantiated constant rule |

The literal codec in [`literal_model.rs`](src/spec/core_spec/literal_model.rs)
retains kind and payload; string identities still need an injective connection
to production strings. The Nat/String bridge now supplies constructible literal
cases to `impl_infer_sound`, not an impossible literal guard. These are
model-to-model statements. The actual Rust helper's extraction and refinement
remain open; the
execution ledger
records the current validation checkpoint.

`DefEq` models equivalence closure, beta, congruence for
application/lambda/Pi/let/projection, delta, iota, and zeta. It does not yet
model every production equality rule: lambda eta, structure eta, native
literal reduction, and quotient-native computation remain outside this
relation.

## Ten-rung metatheory program (legacy)

The source contains ten cumulative rungs of the legacy reflected-model program.
None is a rung of the adopted plan, whose own rungs are in its "Rungs" table:

1. dependent `let` / zeta;
2. production-shaped universe levels;
3. concrete `Nat.rec`;
4. projection and literal syntax;
5. a generic first-order recursor schema;
6. indexed families;
7. universe polymorphism;
8. mutual families;
9. higher-order/W-type fields; and
10. nested rose/list families.

These rungs establish different bounded results. Their strong-normalization
specializations still quantify over a reducibility candidate model
(`CandModel`), several computation/adequacy layers remain incomplete, and the
rungs encode family constants and recursor environments rather than proving a
general correspondence with production inductive-declaration checking.

## Implementation-fidelity boundary

The differential fidelity gate
([`fidelity_gate.rs`](src/fidelity_gate.rs)) compares the real Rust checker in
check mode with the reflected micro-checker only over the closed
`{Sort, BVar, Pi, Lam, App, Let}` fragment. Unsupported constructors are
counted rather than silently skipped, and the known-divergence allowlist is
pinned empty. This is empirical corroboration over six constructors, not a
whole-kernel proof.

The shipping recursive `infer_type` / `whnf` / `is_def_eq` checker spine and
the compiled kernel binary have not been proved end to end against this model.
That model-to-implementation bridge was a required layer of the legacy
self-verification program. The adopted route does not build it: by design the
proved object is to be the Lean-defined checker itself, with no model of Rust
source in between (the plan's "Why the checker is written in Lean and compiled
by Trust"), so the bridge is recorded here as a gap of this stack, not as work
the route owes.

## Trust floor

The live `clean-verify` census has three genuine foundational axioms
(`propext`, `Quot.sound`, `Classical.choice`), zero domain axioms, and zero
current `DerivedProved` debt. The conservative 11-entry value-less census also
contains four quotient primitives and four anti-trust tripwires proved
unreachable from certified theorem closures. See
`SELF_VERIFICATION_PROGRAM.md` for
the accounting and commands.

## Primary sources

- [`expr_model.rs`](src/spec/core_spec/expr_model.rs) — `KExpr` and structural
  operations.
- [`dependent_sn_richmodel.rs`](src/spec/core_spec/dependent_sn_richmodel.rs) —
  dependent typing, `KernelInfers`, and candidate-model SN.
- [`fidelity_gate.rs`](src/fidelity_gate.rs) — bounded model-versus-Rust
  differential gate.
- `SELF_VERIFICATION_CERTIFICATE.md`
  — current measured claims and gap table.
