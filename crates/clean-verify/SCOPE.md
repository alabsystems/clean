# `clean-verify` scope

`clean-verify` defines metatheory for a reflected model of the Clean kernel and
registers the resulting definitions and proof terms in Clean's own kernel. It
does **not** prove that the full production Rust kernel or compiled binary
implements that model.

For the measured claim ledger and remaining gaps, see
`SELF_VERIFICATION_CERTIFICATE.md`.

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
| `lit value` | natural-number literal node | `ExprKind::Lit` |

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
| `TypingCtxConv` | `TypingCtx` rules plus conversion | no projection or literal rule |
| `KernelInfers` | `sort`, `bvar`, `pi`, `lam`, `const`, `app`, `let_` | seven algorithmic arms; no projection or literal arm |

`DefEq` models equivalence closure, beta, congruence for
application/lambda/Pi/let/projection, delta, iota, and zeta. It does not yet
model every production equality rule: lambda eta, structure eta, native
literal reduction, and quotient-native computation remain outside this
relation.

## Ten-rung metatheory program

The current source contains ten cumulative rungs:

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
That model-to-implementation bridge is a separate required layer of the
self-verification program.

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
