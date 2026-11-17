# clean-ck0 quorum boundary (Q2)

This is an independent, unproved Rust kernel. Feature `export` enables `ck0-replay FILE.ndjson`, which reads
lean4export 3.1.0 bytes directly, without clean-olean, clean-kernel or clean-elab.
`Dialect::Lean4Export31` is provisional pending Q0. Exit 0 requires a nonempty
accepted set with no refused declarations; exit 1 reports named refusals; exit 2
refuses the export syntax/dialect/resource envelope. Ax0 admits only exact propext, Classical.choice and Quot.sound declarations,
including their full types and checked canonical prerequisites. Reports measure
admitted axioms and each target's transitive checked closure. The bounded Q2 rules have the honest-case shortfalls recorded below; counted quorum
integration additionally requires Q0's adopted dialect and Q4's vote contract.

Source inventory, 2026-11-13 (bounded Q2 reader):

| Rule family | Existing kernel implementation | Export boundary in this landing |
|---|---|---|
| Sort/Pi/lambda/application/let, inference | `infer.rs`, `validate.rs` | checked from empty environment |
| Universes, polymorphic constants | `level/`, arity/scoping validation | named parameters mapped to positions per declaration; inherited R177 level-provenance guards remain enforced |
| WHNF, beta/zeta/delta, function eta | `whnf.rs`, `def_eq.rs` | definitions checked before registration; theorem/opaque bodies stay opaque |
| Proof irrelevance | `def_eq.rs`; different propositions/non-Prop negative controls in `m1_core` | available in core |
| Eq/PUnit/Nat, recursors, iota/K | `inductive.rs`, `recursor*`, `whnf/iota.rs`; M2 and R162 tests | checked transactionally; supplied recursor type, layout, K flag, universes and every typed RHS compared with independently derived records |
| General single/mutual/nested inductive admission | `inductive/`, `mutual.rs`, `nested/`, positivity checks | single and mutual families checked (parameters, indices, strict positivity, shared universes and elimination gate); recursive-field analysis reduces field heads while preserving declared binders and constructor-result syntax; single/mutual-original nested exports checked, including indexed containers and every member of nested mutual containers |
| Projections, structure eta | `infer.rs`, `def_eq.rs`, structure-eta guards | projections and guarded structure eta available for eligible admitted families, excluding every member of recursive mutual blocks; field-free neutral values compare through full type identity, including owner, parameters and universes |
| Quotients | `whnf.rs`, MinimalEnv quotient classification; `m1_core` lift control | checked canonical signatures for Quot/mk/lift/ind, including canonical Eq prerequisite and direct lift/ind computation tests |
| Nat/String literals | Nat literal/constructor equality and native folds in `whnf/native_nat.rs`; String constructor view in `whnf/string.rs` | arbitrary-precision Nat and String literals require canonical type identities; String conversion uses checked standard definitions; all 15 native Nat folds require exact pinned types/bodies and their checked dependency closure, with differential tests against actual unfolding; the pinned 4.30 profile covers all 15 folds, and the older 4.29.1 profile licenses its eight binary operations plus successor |
| Metadata/free variables/metavariables | no free-variable RawExpr variant | metadata erased after shape check; free/metavariables refused |

Direct production dependencies before Q2: num-bigint, num-traits, thiserror.
Transitive production closure: num-integer, autocfg, thiserror-impl, proc-macro2,
quote, syn, unicode-ident (plus standard library). Proptest is test-only.
The optional `export` feature adds serde/serde_json/SHA-256 and their stock-compatible closure; default core consumers do not include the reader or JSON dependencies. No Trust-only
feature or Clean crate is needed. The command-minted dependency trees and compiler
identities belong in the qualification report; a manifest alone proves no build.

Reader resource limits: 1 MiB per line, 512 MiB and 8,388,608 lines per
export; name spines 64; level trees 256 nodes/depth 64; each materialized
expression DAG 1,000,000 weighted nodes/depth 512. The DAG weight includes
literal payload bytes and local level trees, once per shared node. Sparse
indices remain supported and every reference must already be bound. Duplicate
JSON keys, rebound indices, duplicate declarations, wrong field sets, scoped
universes, constant arity, malformed literals and open terms still refuse.
These are measured resource envelopes, not soundness conditions.

`RawExpr::Shared(Arc<RawExpr>)` preserves the export's sharing. Validation,
substitution and exact equality visit shared identities once per relevant
binder scope. A scoped weak hash-consing pool shares checked nodes; collisions
require exact structural equality. Decision caches own node identities and key
open terms by the transitively needed suffix of context types. They are cleared
between outer decisions, so answers never cross environment changes.

Conversion follows the pinned kernel's pair-directed definition-height strategy,
delays expensive projections until their subjects can be compared, and retries
applied projections before final application congruence. Core head reduction can
perform checked iota inside cheap projection subjects. Native folds retain their
canonical-definition licenses and stop after a nonliteral first operand. Internal
type queries on already checked terms have a separate context-keyed cache; they
cannot satisfy full checking. Public inference and conversion never assume this
precondition. Every application argument and incoming declaration still checks.

`DEFAULT_DECISION_STEPS = 2,097,152` is a finite measured resource allowance;
exhaustion refuses. The reduction-frame bound stays 512 and the reduct/validation
depth stays 1,024. The Init residual report
records its derivation and complete subject/control results. Source changes
invalidate the Q6 lineage capture until that lane re-captures it canonically;
they do not promote the historical genesis manifest.

Statement pins keep the existing v1 encoding. Target mode first measures its
expanded encoding over the DAG and refuses above 1 MiB; whole-export checking
has no expanded-tree requirement. Pinned subjects need at most 814,899 bytes.
See the shared-term measurements and replay
for the exact subjects, limits and remaining refusals.

The part 2 boundary preserves public signatures and keeps primitive recursors
out of plain Const. Legitimate admitted inductives such as Nat.le.below are
distinguished from primitive eliminators.
It lowers only admitted primitive recursors to ElimRef, checking the full supplied
level vector. Checked ordinary helpers with reserved suffixes use private forwarding aliases
to the original checked declaration. Opacity and definition-height scheduling
are preserved. Bodies are bounded and checked separately at admission; helper
references keep their names and sharing for lazy conversion. No alias becomes
a primitive recursor or obtains an iota rule.
The internal iota RHSs use dummy lambda domains, so the reader independently
reconstructs their real domains from the derived recursor and constructor
telescopes before structural comparison. Only binder annotations are ignored;
conversion and proof irrelevance cannot hide a forged rule. A failed comparison
commits no member of the block.

Measured part 2 coverage and exact refusals:
`reports/self-proof-q2-part2-2026-11-12/README.md`.
The requested Q2 rule families and review corrections are implemented within the
retained bounds. Metadata flags inspect validated constructor syntax before
checked identity annotations are consumed; a raw shared recursion flag excludes
all block members from structure eta. The measured census has no unsupported Q2
inductive, recursor, quotient or literal family. This is bounded source
qualification, not complete Lean parity or a counted Q0/Q4 vote.

Availability qualifications: the Ax0-restricted pinned Init fits the shared reader envelope;
work-budget, raw-level and policy refusals can pre-empt Arena targets. Every bad
signature is pinned and incidental cases are explicitly labelled. No semantic
soundness, formal verification, full CI or complete Lean replacement claim
follows. Soundness remains per universe bound, a generation's logical strength
is bounded by its base, and the independent quorum remains required.

For a statement-bound result:

```
ck0-replay FILE.ndjson --target-json '[{"str":"theoremName"}]' --statement-sha256 EXPECTED_SHA256
```

The target must be a theorem, all declarations must pass, and the expected
statement hash must match. Its actual axiom closure is reported. The explicit
`--inspect-target-json NAME` diagnostic reports `matched:false`; it does not
produce a counted vote. Name and statement encoding are specified in
the Q2 report.
Default whole-export mode retains its coverage semantics.

Inductive transactions share a read-only prior environment and own only their
staged delta; both outcomes flatten it. Derived mutual records are shared.
Native licensing never trusts a producer hash or installs the reference export
as an environment. Each actual declaration is checked first.

Verdicts are JSON objects, one per line. Declaration rows carry `kind`,
`name` (tagged string/numeric component list), `accepted`, and for refusals
`reason` and `detail`. A final `kind: coverage` row gives measured counts.
Names cannot inject output lines; control characters in wire names refuse.
Numeric components are decimal strings and remain distinct from string names.
Admission failures retain the `admission` class; unknown constants use
`unknown-constant`, and atomic block refusals retain their underlying class.
