# Carcara source dependency

### Versioned checker capability: `array_const_select_v1`

The updated explicit `checker::Config::clean_dialect()` implements the
premiseless, argument-free, discharge-free positive unit equality
`(= (select ((as const (Array I Bool)) fill) key) fill)`, in either
orientation. Standard `Config::default()` remains disabled and refuses the
unknown rule. AY's corresponding Clean exporter discloses this capability;
older Clean and pinned upstream checkers have no support claim.

`carcara/src/checker/rules/array_const_select.rs` independently inspects the
fresh native AST. Fill is a Bool variable or Boolean constant, compared by
pool identity in both positions. Key is a flat Bool/Int/BV(1..128) variable
or canonical literal; Int literals are at most 128 significant bits. A parsed
unary minus over one nonnegative bounded Int numeral is the negative-literal
representation. Arbitrary arithmetic/compound keys, compound fill, different
fill, wrong sorts, malformed arities, ordinary function lookalikes and
unsupported domains refuse. Existing source-premise authentication and
typed parser ownership remain mandatory; no solver or AY producer payload
is consulted. A fixed 64-unit admission precedes AST reads, and inherited
deadline checks precede validation and acceptance. Name/value payloads are
borrowed; no term, sort or recursive body is constructed or cloned.

Modified upstream files: checker `mod.rs`, `shared.rs`, `error.rs`, and
`rules/mod.rs`. Added Clean files: `rules/array_const_select.rs`, its unit
tests, `carcara/tests/array_const_select.rs`, the explicit
`carcara/examples/array_const_select_fresh_exports.rs` qualification tool, and
the original-row2 source/proof fixture pair under
`carcara/tests/fixtures/array_const_select_v1/`. The SMT
source is the unchanged1745-byte original; the proof is an actual AY export.
`UPSTREAM.json` preserves
upstream identities and records each changed/local file. The normal Clean
production adapter has a positive semantic and forged-unit refusal test.
The earlier qualification passed two unit controls, six hermetic integration
controls, the same loop over all37 actual AY exports independently reparsed
against original sources, and the normal production adapter's
semantic/forged-unit control. That cross-repository fresh37 loop now lives in
an explicitly invoked tool and fails closed without its artifact directory;
the hermetic original-row2 regression remains always on.
The required Trust attempt refused the proc-macro TCB and emitted no proof
coverage. These are private source results, not publication or consumer adoption.
See `docs/array_const_select_checker.md` for commands, identities and gates.

This directory is Clean's vendored copy of **Carcara**, the Alethe proof checker
by Bruno Andreotti, Haniel Barbosa, Vinicius Gomes, Bernardo Borges, Tiago Campos
and contributors, taken from upstream revision
`d62d45cf972875b3c1463b287e9a86536b56551d` (<https://github.com/ufmg-smite/carcara>,
"Add tests for arrays rules", 2026-08-12). It is the checker behind `clean cert
verify-external` for Alethe certificates: `clean-auto` builds it as a path
dependency behind the `carcara-verify` feature. Trust relies on that path for
trust-cg's proof gate (`TCG_CLEAN_CHECKER`) and trust-router's N-version UNSAT
cross-check, so a defect here is a defect in Clean's trust root.

This file lists **every** local change. `README.md` is the upstream README,
unchanged.

## License

Carcara is licensed under **Apache-2.0**; the license text is kept verbatim in
`LICENSE`. Clean is also Apache-2.0. Apache-2.0 section 4 permits redistributing
modified copies on three conditions, all met here:

- **Include the license.** `LICENSE` is kept verbatim.
- **Mark modified files.** Every modified file carries a `Modified in Clean`
  comment at each change (every added test an `Added in Clean` comment), and
  is listed below.
- **Keep upstream notices.** Upstream ships no `NOTICE` file and no per-file
  copyright headers; the author list in `carcara/Cargo.toml` is unchanged.

## What is vendored, and `UPSTREAM.json`

The complete `carcara`, `carcara-macros` and `test-generator` crates, plus the
upstream `LICENSE`, `README.md` and `rustfmt.toml`. The upstream CLI, benchmark
corpus, docs, scripts and `rust-toolchain.toml` (which pinned 1.87; this
directory inherits Clean's `trust` pin) are not included.

`UPSTREAM.json` has one row per imported file:

- `bytes` and `sha256` are the **upstream** file at d62d45cf. They are never
  rewritten, so the import stays checkable against upstream.
- A file changed here also carries `local`, the `bytes` and `sha256` of the
  file as committed. A file without `local` must be byte-identical to upstream.
- The root `Cargo.toml` and `Cargo.lock` *replace* upstream's files of those
  names, so they are ordinary rows with a `local` digest.
- `local_files` lists the files that are Clean's own (the new
  `carcara/src/checker/scoping.rs`, `carcara/src/checker/budget.rs`,
  `carcara/src/checker/deadline.rs`, `carcara/src/checker/rules/datatypes.rs`, `carcara/tests/rules/datatypes.rs`,
  `carcara/tests/problem_reading.rs`, `carcara/tests/malformed_steps.rs` and
  `carcara/tests/resource_budget.rs`, and the `soundness/` battery), with their
  digests. `DOWNSTREAM.md` and
  `UPSTREAM.json` themselves are not listed.

## Workspace layout

`third-party/carcara` is its own Cargo workspace with its own `Cargo.lock`.
Clean's root `Cargo.toml` lists it under `exclude`, so Cargo does not claim the
path dependency as a Clean workspace member. Clean's root `Cargo.lock` resolves
`carcara` and `carcara-macros` from this path; they have no `source` line.

Run the vendored suites from this directory, with the Trust toolchain on `PATH`:

```bash
targo --unverified test --locked --release --workspace   # carcara unit/rule/proof tests + the battery's tests
targo --unverified run --locked --release -p carcara-soundness -- --mutants 20000 --seed 11
```

The second command exits 1 when any accepted step has a counterexample and
prints each one with its model. `--fill DEFINITIONS PROOF` prints the term the
checker expects in place of a `; @@fill NAME` hole; it produced the circuit
tests in `carcara/tests/rules/bitvectors.rs`.

## Local changes

The measured effect of every change below, before and after, is in
`reports/2026-09-24-carcara.md` (fixes
1-33, on the commit that reconciled them onto this tree),
`reports/2026-09-24-carcara-fixes-34-35.md`
(fixes 34 and 35 and the battery extensions) and
`reports/2026-09-30-zero-extend-dialect.md`
(the `zero_extend` dialect entry and the checked bit-vector widths). Fixes 36 to
40 and C2 record their measurements here, below their tables. The
upstream write-up, with a minimal counterexample per defect, is
`reports/2026-09-17-carcara-soundness-upstream-report.md`
(not sent).

### Packaging (no checker semantics)

1. `Cargo.toml` (workspace): the local manifest selects the three vendored
   crates and the Clean-authored `soundness` member; it is not the upstream
   manifest.
2. `Cargo.lock`: upstream's lockfile with the entries used only by the
   unvendored `cli` dropped and the ones used by `soundness` added. No
   upstream package changed version.

### Dialect: opt-in legacy `bv2nat` (`allow_legacy_bv2nat`, `carcara/src/parser/mod.rs`)

Its opt-in `allow_legacy_bv2nat` setting resolves an otherwise unbound
application of `bv2nat` through the existing typed `UBvToInt` operator.
Declarations, function definitions, and local bindings take precedence over this
alias. Arity and sort checks are unchanged. It changes no proof rule and no
checker code. Clean enables this setting when parsing the original problem and
certificate together. Its regression tests live in
`crates/clean-auto/src/bridge/ay_backend/carcara_verify/bv2nat_tests.rs` relative
to the Clean repository root. They exercise the actual parser and the production
verification adapter, including declarations that must not acquire builtin
semantics.

The same file also carries half of soundness fix 33 below (the `(_ bv<n> <w>)`
literal is reduced modulo `2^w`) and its correction in fix 35; those changes
touch a different function.

### Dialect: `zero_extend` read as its SMT-LIB definition (`expand_zero_extend`, `carcara/src/parser/mod.rs`)

SMT-LIB's QF_BV logic defines `((_ zero_extend 0) t)` as `t`, and
`((_ zero_extend i) t)` as an abbreviation of `(concat ((_ repeat i) #b0) t)`.
With `expand_zero_extend`, the parser builds every such application as that
definition:

- `t` when `i = 0`;
- otherwise `(concat Z t)`, built through the parser's own `concat`
  construction. `Z` is the all-zero bit-vector constant of width `i`, the
  term that both `(_ bv0 i)` and `#b0…0` parse to.

It applies to every term the parser builds: the problem, `define-fun`
bodies, proof clauses, `:args`, anchor assignments and RARE rule files. So
no `zero_extend` term exists after parsing, and no rule sees one. The option
introduces no symbol, assumption or rule, and every rule still checks the
terms it is given.

The reading is exact. A wrong reading would not be visible to rule
checking, because the refutation would then be about a different problem.
So the reading is held by tests that compare the parsed term with the
definition computed from the source text:

- `crates/clean-auto/src/bridge/ay_backend/carcara_verify/zero_extend_dialect_tests.rs`,
  which runs at every AY move;
- the battery's `parser:zero_extend` audit, which is run by hand (see the
  report).

Width arithmetic follows the parser's general width rule (*Also hardened*,
below).

`Config::clean_dialect()` turns this option on beside `allow_legacy_bv2nat`.
A producer that relies on it names it: AY's
`CleanOnlySpelling::ZeroExtendAsConcat`, key `dialect:expand_zero_extend`.

From `ba5e28ff5` (2026-09-15) Clean read `zero_extend` the same way, in an
adapter post-pass. A `clean` built before that commit, such as the installed
0.9.0, refuses these documents. The post-pass also refused any certificate
past a whole-certificate work budget of 4,000,000 units, whether or not it
mentioned `zero_extend`; the parse-boundary reading bounds nothing but widths.

### Dialect rule: scalar BV equality (`dialect:eq_simplify_bv_offsets`)

`checker::Config::clean_dialect()` explicitly enables this extension of
`eq_simplify`; `checker::Config::new()` and its default keep the upstream
contract. Clean's production Alethe adapter selects both this checker dialect
and the existing `parser::Config::clean_dialect()`. The soundness battery's
`--dialect clean` selects both too. A producer relying on the extension must
disclose `dialect:eq_simplify_bv_offsets`; it is not a portable/pinned-Carcara
rule claim, and older Clean packages (including signed cohort 13482) lack it.

The additional premise-free, argument-free unit forms, with either outer
equality orientation, are:

```
(= (= A B) BOOL)
(= (= (bvadd X A) (bvadd X B)) BOOL)
(= (= (bvadd X A) (bvadd X B)) (= A B))
```

`A` and `B` are canonical literal bit-vectors of exactly the same width in
`1..=128`; `BOOL` is their actual equality value. In each binary builtin
`bvadd`, either position may contain its literal. The common `X` is the
identical opaque hash-consed term with that same BV width. Every operand,
application and equality has its actual recorded sort checked. Aliases,
premises, named/private function heads, nonliteral offsets, recursive
normalization and other arithmetic operations confer no authority.

The theorem is cancellation in the additive group `Z/(2^w)`: adding `X` is a
bijection, so equality is exactly the equality of the two literal offsets,
including wraparound. Parsed numeral spellings are already canonical; the
inspector independently checks their sign, width and significant bit count
before converting at most two limbs to `u128`.

`checker/rules/simplification/bv_eq.rs` inspects the supplied source and result
directly, without building intermediate equality/Boolean nodes or allocating
private scratch. Both orientations and failed candidates share a fixed
256-unit meter; every slot read, cached sort lookup, pointer comparison and
bounded literal inspection is charged before it runs. Exhaustion refuses the
step. No SAT/polynomial fallback, existing expansion budget, whole-proof cap
or deadline is changed. Legacy `eq_simplify` cases remain its own fallback.

Controls are in `carcara/tests/bv_offset_dialect.rs`, the inspector's unit
tests, the soundness generator, and the production adapter's
`bv_offset_dialect_tests.rs`. They cover exhaustive small words and all base
valuations, four addend placements, widths 1/8/64/128, canonical wraparound,
wrong claims/bases/operators/arity/sorts/widths/literals, alias premises,
default-dialect refusal and inspection-budget boundaries. Actual execution
evidence is recorded in the corresponding decision; this description alone
is no completed-proof or end-to-end kernel-verification claim.

### Dialect rule: bounded BV offset spines v1 (`dialect:eq_simplify_bv_offset_spines_v1`)

The separate wire name `eq_simplify_bv_offset_spines` is unknown to both
`checker::Config::new()` and the older `checker::Config::clean_dialect()`.
Only explicit `.with_bv_offset_spines_v1()` enables it. The production Clean
adapter selects that capability beside its existing Clean parser/rule dialect;
the soundness battery selects it only under `--dialect clean-bv-offset-spines-v1`.
Old `--dialect clean`, the immediate `eq_simplify` rule, its fees and its
capability `dialect:eq_simplify_bv_offsets` keep their existing contracts.
Producers must disclose the new versioned capability; neither signed Clean
13482 nor the earlier scalar-only 059f checker supplies it.

The exact premise-free, argument-free positive unit is `(= (= S T) BOOL)`
or its outer equality reversal, where `BOOL` is a literal Boolean and the
recorded bit-vector width is in `1..=128`. Iteratively peel at most 16 frames
per side: binary builtin `bvadd` with exactly one canonical literal in either
position, or binary builtin `bvsub` with a literal on the right. Every opened
head, arity, result/child width and encountered literal's sign, width and bit
count is checked before bounded conversion. A constant-only frame or a
literal leaf refuses the attempt. A seventeenth eligible frame is inspected
once and refused, never silently hidden as an opaque base.

The base is a same-width, nonliteral opaque term, identical by hash-consed
pointer on both sides. An unsupported well-typed expression can remain the
whole base; its interiors supply no arithmetic authority and retain the
pipeline's existing well-formedness obligations. In particular neither-child
literal addition and nonliteral-right subtraction remain opaque; aliases,
private/indexed arithmetic spellings, multiplication, negation, shifts or
multiple-base algebra are not normalized. No producer offsets or annotations
are trusted, and no source term is rewritten.

The independent checker recomputes modular offsets using wrapping `u128`
addition/subtraction and a width mask, with `u128::MAX` at width 128. An
induction over frames gives `value(S) = value(base(S)) + offset(S)` modulo
`2^w`; cancellation with an identical base therefore decides exactly whether
the offsets agree. Only that actual Boolean result is accepted.

`checker/rules/bv_offset_spines.rs` uses borrowed input and fixed stack state:
no private heap, maps, recursive walks, term materialization, BigInt clone,
SAT/polynomial/legacy fallback or diagnostic rendering of the source. One
8192-unit work meter covers both sides and every failed attempt, with no
orientation retry or reset. Every bounded inspection/operation is charged
before it runs, and the existing deadline is polled before inspection and
between frames. Its accounting table bounds schema/root/mask work at 256,
34 visits including over-limit lookaheads at 192 each, and final comparison
at 32: at most 6816 units. Failure refuses the step. Existing parser,
expansion, process, certificate and deadline limits are unchanged; AY's
separate native admission and whole-proof limits remain its own obligations.

The inspector unit tests, `carcara/tests/bv_offset_spines.rs`, the independent
soundness generator and the real adapter's `bv_offset_spines_tests.rs` hold
the shape, arithmetic, resource, default/old-capability and causal-refusal
boundaries. Actual commands, input/cohort identities and results belong in
the corresponding qualification receipt, not this grammar description.

### Performance: indexed reverse unit propagation (`carcara/src/drup.rs`; no checker semantics)

`rup` (behind `drup`, `drat` and `check_drat`) copied every clause and then, after
each literal it propagated, rescanned the clause list from its first clause for the
next unit one: O(P x N) clause visits, each two SipHash lookups, for P propagations
over N clauses. A `drup` step whose premises form one implication chain (P ~ N, the
shape AY prints for a transported resolution chain of 8 or more links since AY
d39838422a, 2026-09-30) cost O(N^2). trust-cg's `x86_64: BSR_I64 (nonzero) ==
width-1-Ctlz` certificate (63 such steps, up to 16,769 premises, sum of N^2/2 =
3.1e9) took 155 CPU-s in `cert verify-external`, 99.8% of it in this loop, and timed
out its 120 s gate budget; `LSDA EH: ... (partition)` (54 steps, up to 17,583
premises) took 110 CPU-s against its test's 60 s.

Now each term lists the clauses it occurs in (one flat array) and each clause counts
its literals whose term is unassigned, so an assignment touches only the clauses of
its term; the premises are borrowed, not copied. A call takes at most 4L + C unit
steps for L literal occurrences and C clauses (`indexed_rup` counts them). The
verdict is the same, by the argument in the comment above `rup`: both versions
return a story exactly when unit propagation from the negated goal reaches a
falsified clause, which does not depend on the order units are propagated in, and
the old code's two watches only ever skipped a satisfied clause or one with two
unassigned literals. Literal identity (`(polarity, term with every negation
removed)`, the term by pointer), the clause sets, tautology handling (never unit)
and the story's form are unchanged; an invariant lookup that failed would refuse
the step rather than panic. The replaced implementation stays in the file, verbatim
apart from a step counter, as the reference of two tests:

- `rup_equivalence` compares the two on 300,000 random clause sets (literals under
  up to two negations, duplicate and complementary literals, empty clauses and
  goals; both verdicts over 10,000 times each) and replays every story either
  returns as unit propagation over the clauses it was given.
- `rup_cost` checks a complete synthetic certificate (one `drup` step over an
  n-clause implication chain, premises scrambled, then resolution to the empty
  clause) end to end with each implementation and compares the steps `rup` reports:
  the indexed one takes 6n + 7 (n = 256, 512, 1024: 1,543, 3,079, 6,151), the
  rescanning one about n^2/2 (34,437, 134,405, 530,949). A chain missing a link is
  refused by both.

`crates/clean-auto/src/bridge/ay_backend/carcara_verify/drup_chain_tests.rs` sends the
same shape (2,000 links) through Clean's adapter: it verifies, and a dropped link or
a flipped lemma literal is refused at the `drup` step.

Measured 2026-10-08 with `clean cert verify-external`, both binaries built by the same
toolchain from Clean `3b4bb1811` (before) and this change (after); CPU-s is
user+sys, instructions retired are load-independent:

| certificate | before | after |
|---|---|---|
| BSR_I64 | 155.0, 155.1 CPU-s; 1.488e12 | 0.88, 0.89, 0.87 CPU-s; 9.54e9 |
| `LSDA EH: ... (partition)` | 110.1, 110.6 CPU-s; 1.040e12 | 0.60, 0.60, 0.59 CPU-s; 5.70e9 |
| `A64 decoded BFM Xd, Xn insert ...` | 52.7 CPU-s; 6.94e11 | 3.72 CPU-s; 3.74e10 |
| NEON `Movi.4s ... (faithful)` | 29.8 CPU-s; 3.91e11 | 0.51 CPU-s; 6.09e9 |
| QF_ABV Axiom 2b | 25.7 CPU-s; 3.36e11 | 2.26 CPU-s; 2.66e10 |

Eighteen mutants of the BSR_I64 and LSDA certificates (a flipped literal in the
first and the last `drup` lemma and in the last resolution step, a dropped premise
of the last `drup` and the last resolution step, `and_pos` renamed `or_pos`, the
last `drup` renamed `and_pos`, a corrupted `@bit_of` index or constant bit in the
last bit-blast step, and a changed constant in the query's assertion) are refused
by both, at the same step with the same error. A sweep of 35 certificates from
trust-cg's proof-gate cache (the 10 largest, up to 93 MB; 20 spread by size; the 5
with the most `drup` work) all still verify completely with both binaries. None
needs more instructions beyond run-to-run noise: at most +0.3% on a certificate over
1 MB, and -1% to +3% in single runs of those under 100 kB, which are about 4e7
instructions of mostly process start-up and where repeated runs of the two binaries
overlap. Those with `drup` steps are up to 58x faster: 182 -> 42 CPU-s over the 35.
The soundness battery restricted to these rules (`--rules drup,drat --mutants 20000
--seed 11 --threads 1`, deterministic) judges the same 204,484 mutated instances with
identical counts before and after (`drup` 76 accepted, 56 exercised; `drat` 63 and
11; no counterexample), and the full battery at `--mutants 20000 --seed 11` reports
no counterexample.

An adversarial review of this change (2026-10-08) looked for a proof the new `rup`
accepts and the old one refuses, aiming at what the index changes: a clause
satisfied and then fully assigned (a stale count), repeated and complementary
literals, empty clauses, goal literals against premise units, literal identity
under double negations, tautological and repeated premises, deletions between
lemmas, and the conclusion check. It found none. The release binaries of the two
versions gave the same verdict on 7,030 generated certificates (`drup` and `drat`
steps over up to 14 atoms with those features; every one of the 2,128 steps they
accepted is implied by its premises, by truth table) and on 100 mutants of real
`drup` steps from the BSR_I64, LSDA and NEON certificates, each proof cut after the
mutated step (premises dropped, repeated or reversed; a lemma literal flipped,
dropped or added; a premise deleted first; the conclusion permuted; the rule
renamed `drat`). The review added `rup_adversarial`, three tests that judge `rup`
by references independent of the replaced code (a plain fixpoint over atoms and
signs and, for every refutation, a truth table):

- `long_chains_with_stale_counts_and_repeated_literals`: 50,000 clause sets built
  around implication chains through up to 40 atoms, so a refutation propagates
  dozens of literals, which `rup_equivalence`'s at most 14 clauses do not reach. Of
  16 mutants of `indexed_rup` the review tried, `rup_equivalence` caught all but an
  equivalent one and one that gives up after 16 propagations; this test catches
  that one.
- `shapes_with_known_verdicts`: those situations one at a time, each with its
  expected verdict.
- `check_drup_is_sound`: 100,000 whole `check_drup` calls, `drup` and `drat`, lemmas
  and deletions interleaved, run with both implementations; their results must be
  equal and every accepted conclusion must hold in every model of the premises. It
  catches five unsound mutants of `check_drup` and `check_drat` (fix 22 dropped, RAT
  checked against only the first clause holding the negated pivot, the pivot left
  in the resolvent, a failed lemma kept, the conclusion check skipped); of the
  tests `targo test` runs, the `drup`/`drat` rule tests catch two of them. The
  battery (`--rules drup,drat`) catches all five.

### Performance: `Polyeq` caches the pairs it finds unequal (`carcara/src/ast/polyeq.rs`; no checker semantics)

`Polyeq` cached only the pairs it found equal. Modulo the order of equalities, it tries
`(= a1 a2)` against `(= b1 b2)` in both orientations, so a sub-pair that fails was compared again
on every path to it, in time exponential in the depth of shared terms. Two named chains
`E_i = (= E_(i-1) E_(i-1))` and `F_i = (= F_(i-1) F_(i-1))` over `E_0 = (= k m)` and
`F_0 = (= k j)`, 26 deep (2.4 KB), took 1.8 s to compare, doubling with each level (40 would take
about 9 hours), reached by any rule that compares with `polyeq` or `alpha_equiv`: an `assume` of
`(or F_26 p)` against a problem asserting `(or E_26 p)` took 1.7 s, and `concat_eq` stripping
`(str.at (ite E_26 "a" "b") 0)` against the same over `F_26`, 1.8 s (review of the string-rules
lane, 2026-10-14). The cache now holds whether each pair compared is equal, reused under the same
rule as an equality: under alpha-equivalence inside a binder, fix 10 read only the innermost
scope's entries, and since 2026-10-15 an answer is reused wherever the bindings it read are as they
were (the next paragraph but one). Either way a cached answer is the one the comparison would
compute. Both reproducers, at 26 and at 40 levels, now take under a millisecond.
`polyeq_caches_unequal_pairs_within_their_scope` (`ast/tests.rs`) compares 64-level chains
(without the change the test does not finish) and checks that an answer found inside a binder is
not reused outside it, nor one found outside reused inside.

**Answers found under a binder are reused under its siblings (2026-10-15; found by the
fix-forward of the review of `7006ac377..6a7aff128`, 2026-10-14).** Alpha-equivalence opened a
cache scope at every binder and dropped it on leaving, and under fix 10 only the innermost scope
was read, so a comparison made under one binder was made again under its sibling:
`a_i = (and (forall ((x Int)) a_(i-1)) (forall ((y Int)) a_(i-1)))` against the same chain named
apart (`z`, `w`) was compared once per path, and `refl` accepted it, correctly, after `2^n`
comparisons. The De Bruijn map kept a map per open binder on each side and searched them innermost
first, so a variable read under `d` nested binders cost `d` lookups.

What a pair's answer depends on is the pair, the comparator's configuration (set when it is
built), whether some variable is bound (identical terms are equal at once only while none is),
the answers its cache gives, and the bindings of the names the comparison reads from outside the
pair, and nothing else. Names bound inside the pair the comparison binds itself, at the next
indices of the counter, which exceed every index bound outside it; indices are only compared for
equality, so these compare alike wherever the pair is compared. So the cache is keyed on what was
read. A pair compared with no variable bound is reused wherever none is, as before. A pair compared
under a binder is kept with the names it read from outside the pair, each with its side (a side
is a position in the comparison: `compare_chainable` and the singleton case of n-ary operators put
a subterm of either term on either side), together with the names recorded by the answers its
cache gave it, and is anchored at the innermost binder level that bound one of them (or at none).
It is reused while that level is open and none of those names is bound at a deeper level, so
under a sibling binder too unless the sibling rebinds one of them, and it is dropped as its level
closes: a closed level never opens again, so while the answer is kept the scopes up to its anchor
are those it was found in, and each name it read is bound in them as it was, or nowhere, as it was.
A name never bound before is not recorded: it was free, and recording every free name a comparison
reads, a problem's constants among them, would put most comparisons past the 16 names recorded.
The De Bruijn map numbers a name when it is first bound. Until then a read of it during a
comparison under a binder stamps it with the clock, the count of comparisons under a binder started
so far, and the stamp it has when it is first bound is its lateness. An answer carries the stamp
of its comparison, lowered to that of each answer its cache gave and of each comparison inside it,
and is reused only while every name bound has a lateness below that stamp: a comparison that read
a name free started no later than that read, so the name, if bound since, is late for it. A name
first bound without having been read free is late for nothing, so the names of nested siblings,
each first bound under the level above, cost no reuse. (Until the review of this change, below,
the map numbered every name a binder of the two terms binds before the first binder was entered,
walking both terms, and dropped every answer when it had to number a name later.) A comparison
that read more than 16 names records none and is reused only at its own level, under the rule
upstream applied to every answer. The deadline is polled as before: a comparison that sees it pass
returns at once, and nothing is cached past it. The De Bruijn map is now one map from each name to
its stack of bindings on each side, innermost last, so a read is one lookup at any depth, and a
binder undoes its own bindings as it closes. A pair holds at most 4 answers, the one anchored
outermost dropped first, which only costs comparing the pair again. So a lookup costs one hash of
the pair, then at most 4 answers, each a comparison of stamps and of at most 16 reads (the name
bound innermost first), and binding a name costs one lookup of it; nothing walks the terms. The
invariant, and why it holds, are stated on `BoundAnswer` (`ast/polyeq.rs`). The comparator answers
every pair as before; no checker semantics change.

Measured (release probe, the adapter's parse and check, base `40ea22d1c`; `gen_alpha.py` in the
lane's probes makes every input): the chain above 20, 22 and 26 deep took 0.78 s, 2.97 s and
54.7 s, and now under a millisecond (64 deep 1 ms, 1,000 deep 9 ms), at 3 MB (9 MB at 1,000).
Joined by `=`, whose two orientations are both tried, with leaves `p` and `q` (not
alpha-equivalent), it took 0.73 s, 3.22 s and 55.0 s, and now under a millisecond. Siblings binding
an `Int` and a `Bool` took 59.4 s at 26 deep, leaves reading a name bound above every sibling
69.4 s, and second siblings rebinding that name on both sides 57.4 s; all now under a millisecond
(the last 0.14 s at 1,000 deep: under each such sibling the chain below is compared again, once
per level). Second siblings rebinding it on one side only (not alpha-equivalent) are refused at
once, before and after. A chain whose siblings bind `x(i-1)` at different indices, the second
binding another variable first, while the leaves read every `xi`, reads different bindings on
every path, so no answer can be shared: it took 9.0 s and 41.7 s at 20 and 22 deep and did not
finish in 300 s at 26, and now takes 1.8 s, 9.4 s and 109 s (each read is one lookup); the
deadline bounds it ("The checker stops at a deadline", below).

The tests (`ast/tests.rs`): `alpha_equivalence_reuses_answers_across_sibling_binders` compares
64-deep chains of seven shapes (those above; one whose second siblings rebind, on one side only,
the name the leaves read, which reusing the first sibling's answer would accept; and one whose
every level binds names no other level binds) in at most four comparisons per level (quadratic for
the rebinding on both sides), each answer the oracle's at 6 deep; on the base tree it does not
finish (killed at 120 s). Two tests hold the comparator to an oracle, the comparator of
`40ea22d1c` kept verbatim (`ast/polyeq_oracle.rs`, test only), in all sixteen configurations, each
pair alone and all of them in turn through one comparator:
`the_comparator_answers_as_its_oracle_where_bindings_differ` (shadowing, a name bound at
different depths, sibling binders over different sorts, a shared subterm whose name a sibling
rebinds, free outside and bound inside both ways, a name read free under a binder and first bound
by a later sibling on one side, whose earlier answers may not be reused under it, directly,
through an answer that relied on one, through a comparison inside one, under a deeper binder, or
after it was read free again; a pair unequal under an inner binder that binds its name at
different indices on the two sides and equal outside it; `choice`, `lambda` and `let` binders;
and a conjunction reading 20 bound names, past what is recorded) and
`the_comparator_answers_as_its_oracle_on_random_terms` (random pairs over few names and four
sorts, with `forall`, `exists`, `choice`, `lambda`, `let` and `match` binders and subterms shared
across them, a term against its variants with binders renamed, consistently or not, equalities
flipped and conjunctions regrouped, from 160 seeds: 182,464 comparisons, 89,292 of them equal, and
18,987 keeping answers found under a binder). Twenty mutants of the cache each fail at least one
of the tests: an answer reused whatever the lateness of the names bound, or when a name was made
late by its own comparison's read; a reused answer's stamp, or a finished comparison's, not passed
on; an answer stamped when it ends; a free name not stamped, or not stamped again when read again;
a name's lateness forgotten when it is first bound; the lateness of names bound outside the
innermost level not counted; the clock not advancing (every answer refused: the 64-deep chains run
out of memory); any answer reused under any binding; bound or free names not recorded; every
answer anchored at no binder, or at the outermost binding it read; a reused answer's names or a
finished comparison's names not passed on; an answer reading every binding reused at a deeper
level; answers kept past their level; and identical terms equal at once under binders.
`polyeq_caches_unequal_pairs_within_their_scope` passes unchanged.

Regression (release probes of `40ea22d1c` and of the change, each mirroring the adapter's parse,
define-fun retry and check): all 5,441 trust-cg certificates keep their verdicts, 5,428 verified
and 13 refused at the same `bitblast_ashr` steps with the same messages; only 16 of them contain a
binder. Check times summed 310.9 s on the base and 319.2 s and 323.4 s in two runs of the change,
on a loaded machine; the 12 slowest, best of 3 interleaved, took 19.0 s and 19.2 s, and in a
second round 25.3 s and 25.2 s; peak memory moved by at most 6 MB either way. The soundness battery
at `--mutants 200 --seed 11 --threads 1` checks the same 605,934 instances with the same 221,570
parse errors and no panic on both, its 189 per-rule rows identical, with no counterexample. The
vendored workspace tests (release, 454), clean-auto's `--features carcara-verify,ay-bv-blast
--lib` tests (2,487), and with `carcara-verify` the server's `external_cert_alethe` tests (3) and
the CLI's `tests_external_cert` (14) pass; `targo tippy` reports on the vendored workspace exactly
the 33 lints it reported on `40ea22d1c`, and nothing with `-D warnings` on clean-auto, clean-server
and clean-cli (all targets, with those features).

**The review of this change, fixed forward (2026-10-15).** The review found three costs the
comparison paid for work it did not need, each making a deadline refuse a valid proof that the base
tree accepts at once:

- Before the first binder, the De Bruijn map walked both binder bodies whole to number the names
  bound in them. `alpha_equiv` builds a comparator for every call (`refl` makes up to four a
  step), so a comparison refused at its first argument still walked both terms. `K` `refl` steps
  comparing `(forall ((z Int)) (or (= x z) H))` with `(forall ((z Int)) (or (= y z) H))`, in a
  subproof whose context maps `x` to `y`, `H` a definition of `M` atoms, cost `K * M`: 10,000 of
  each (1.1 MB) took 18.7 s against 0.06 s, and a 5 s deadline refused the proof. Names are now
  numbered when first bound, and nothing walks the terms.
- A pair whose comparison reads a name that every level rebinds got an answer at each level, all
  of them kept while their levels were open, and a lookup examined every one: `d` levels
  `A_i = (forall ((v Int)) (and PS A_(i-1)))`, `PS` a conjunction of `K` atoms reading `v` and
  seven names bound above, cost `K * d^2`: 2,000 of each (386 KB) took 143.6 s and 790 MB against
  0.79 s and 431 MB. A pair now holds at most 4 answers.
- Numbering a name late dropped every answer with `HashMap::clear`, which keeps a table's capacity
  and pays for all of it each time, at every top-level binder that bound a new name: `N` atoms
  compared under one binder, then `K` sibling binders of new names, cost `N * K` (10^6 and 10^5,
  18 MB, took 19.1 s against 2.2 s). Binding a new name now drops nothing; only the builders drop
  answers, and they replace the tables instead of clearing them.

Also from the review: `mod_reordering`, `mod_nary` and `mod_string_concat` drop the answers held,
as `alpha_equiv` did (every builder chain in Carcara and Clean runs before the first comparison, so
nothing observed the difference). A pair's first answer is held in its table entry, not in a vector
of its own, and an identical constant equals itself under any binder at once, holding no answer:
the third reproducer (10^6 atoms, 10^5 siblings) now holds 135 MB beyond the base's peak, where it
held 470 MB before the review. The paragraphs above now state the costs with their bounds. The
review's reproducers, all accepted on every tree (release probes of origin/main `98415fe0d`, of
this change merged with it before the review's fixes, and of the result, each mirroring the
adapter's parse, define-fun retry and check, on a machine at load 30, where times move by about
20%):

| Input | Base | Before the fixes | Now |
|---|---|---|---|
| `K` `refl` steps over an `H` of `M` atoms: `K` = `M` = 10,000; 20,000 | 0.06 s; 0.12 s | 8.3 s; 34.2 s | 0.07 s; 0.12 s |
| the same, `K` = 1,000 and `M` = 100,000; `K` = 100,000 and `M` = 1,000 | 0.17 s; 0.45 s | 9.5 s; 10.1 s | 0.18 s; 0.47 s |
| `d` levels of `K` atoms: 1,000 of each | 0.22 s, 118 MB | 13.9 s, 202 MB | 0.40 s, 24 MB |
| the same, `d` 2,000 and `K` 1,000; `d` 1,000 and `K` 2,000 | 0.57 s, 0.41 s | 73.6 s, 27.5 s | 0.80 s, 0.83 s |
| the same, 2,000 of each | 0.98 s, 426 MB | 109.7 s, 786 MB | 1.62 s, 76 MB |
| `N` atoms under one binder, `K` siblings of new names: 10^6 and 10^3 | 1.87 s, 757 MB | 1.82 s, 1,226 MB | 1.73 s, 878 MB |
| the same, 10^6 and 10^5; 10^3 and 10^5 | 2.19 s; 0.24 s | 5.32 s; 0.33 s | 2.06 s; 0.24 s |

With a 5 s deadline the first row's 10,000 steps were refused at 5.002 s and are accepted in
0.07 s; `d` 1,000 and `K` 2,000 were refused at 10.5 s with a 10 s deadline and are accepted in
0.93 s with a 5 s one.
The chain whose every path reads different bindings, 26 deep, is refused at 2.000 s and 5.000 s
with deadlines of 2 s and 5 s: a lookup examines at most 4 answers, so the comparison sees the
deadline at once. The chains above keep their times: 22 deep (siblings, the leaves reading an
outer name, and siblings binding names no other level binds) under a millisecond, against 3.3 s,
3.9 s and 2.9 s on the base; 5,000 deep in 0.04 s (the base did not finish in 120 s); and the
chain whose every path reads different bindings 1.7 s at 20 deep, against 8.1 s.

The tests (`ast/tests.rs`) count the comparator's work with a test-only counter (the pairs
compared, the answers and reads a lookup examines, the entries visited as a level closes, and the
table slots a reset frees), and each fails on the change as it was before the review, given the
same counter: `alpha_equivalence_refused_at_its_first_argument_costs_only_what_it_compared` (eight
comparators, as `refl` builds them, over an `H` of 1,000 and of 4,000 atoms: 64 units both times,
where the walk made them 24,144 and 96,144);
`a_lookup_examines_few_answers_where_a_name_it_reads_is_rebound_at_every_level` (32 and 64 levels
of 8 atoms: 9,185 and 18,657 units, where examining every answer made them 82,996 and 324,644;
and the oracle's answers 8 deep where the two sides differ only at the deepest level); and
`answers_found_under_a_binder_outlive_siblings_that_bind_new_names` (200 and 400 atoms and
siblings: the atoms' answers are still held after the siblings, which dropped them before, and
the work doubles, 803 and 1,603 units). The `fresh` sibling chains took 383 comparisons before,
since the second top-level sibling's names were numbered late, and take 193 now.

Left as they are: inputs shaped like the second reproducer, where every pair records 16 names and
one of them is rebound at every level, take 1.4 to 2 times the base's time in a fifth of its
memory (recording each answer's reads costs time the base does not spend; it is linear). A
comparator keeps every name it has bound, so `K` siblings of new names hold `2K` names until the
comparison ends (134 MB against 93 MB at 10^5). The chain whose every path reads different
bindings is still exponential, and the deadline bounds it. Siblings that bind the names read at
the same indices still compare the shared term again under each: holding such answers until the
parent closes, checked by index, would share them, at memory proportional to the siblings. The
memory the comparator holds is not charged to the step budget; it is at most 4 answers per pair
compared under a binder. The reviewer measured the stack per term level 8 to 11% above the
base's (240 bytes a level for a quantifier chain), far inside the adapter's 1 GiB stack at
`MAX_TERM_DEPTH`.

Regression, merged with origin/main `98415fe0d` (release probes of `98415fe0d` and of the result):
all 5,441 trust-cg certificates keep their verdicts and messages, 5,428 verified and 13 refused at
the same `bitblast_ashr` steps; no run was capped; check times summed 305.4 s and 302.6 s, and peak
memory moved by at most 5 MB either way. The soundness battery at `--mutants 200 --seed 11
--threads 1` checks the same 606,427 instances with the same 222,144 parse errors and no panic on
both, its 189 per-rule rows identical, with no counterexample. The vendored workspace tests
(release, 471), clean-auto's `--features carcara-verify,ay-bv-blast --lib` tests (2,487), and with
`carcara-verify` the server's `external_cert_alethe` tests (3) and the CLI's `tests_external_cert`
(14) pass. `targo tippy` reports on the vendored workspace the same 28 lints as on `98415fe0d`, and
nothing with `-D warnings` on clean-auto, clean-server and clean-cli (all targets, with those
features). Twenty mutants of the cache each fail the comparator's tests (the list is in the tests
paragraph above).

### Malformed steps are refused, not a panic (`checker/rules/*`, `ast/term.rs`, `parser/mod.rs`)

An adversarial review (2026-10-09) found that `clean cert verify-external` panicked, an index out
of bounds in this checker, on a certificate whose `drup` step concluding `(cl)` (`:args ((cl))`)
was renamed `pbblast_bvand`. A panic fails closed, but it is a crash of the trusted checker on
input the certificate's author controls, and Clean's release profile has `panic = "abort"`, so it
ends the whole process. A one-off sweep then looked for the rest of the class, over the 2,127
rule-test cases in `carcara/tests/rules/` (those with a numeral of 6 to 19 digits left out, see
below). It renamed every step to each of 191 rule names (the 190 `get_rule` dispatches on, and
`sat_refutation`) with no `:args` or no premises, with one to three integer or Boolean arguments,
and with the step's first conclusion literal one to three times (4,135,914 checks that reached the
checker). It mutated each case's proof: every numeral replaced by 0 to 3, 7, 8, 63 to 65, `2^64`
and `10^30`; in every list one of the first three elements or the last one dropped, the last one
repeated, all but the head dropped, or the whole list emptied. Every mutant that parsed (82,046)
was checked under its own rule and renamed to every rule as above (17,238,430 checks), and
second-order mutants of every fifth one, with mutants of the definitions, added 2,531,116. On
origin/main this found panics at 24 sites (the first six rows below); probes written while fixing
them found the last one and the 0-bit widths below. On this tree the sweep finds none in about 24
million checks (release build), nor in a debug build, whose overflow checks catch a wrap a release
build hides, over every fifth case (829,704 renamings, 15,444 first-order mutants and 583,246
second-order ones).

| Site | Cause | Now |
|---|---|---|
| the 15 `pbblast_*` rules (`pb_blasting.rs`), `arrays_ext`, `cp_literal` | `&conclusion[0]` without a check of the clause length | `first_conclusion_literal` (`checker/rules/mod.rs`) refuses the empty clause with `WrongLengthOfClause`; any other conclusion is read as before, so a longer clause keeps its verdict |
| `cp_division`, `cp_saturation` | `&premises[0].clause[0]` unchecked | the premise must be a unit clause, as in `cp_addition` and `cp_multiplication` (fix 41: a longer one was also a soundness defect) |
| `bitvector_size` (`bitvectors.rs`) | `panic!` on an operand that is not a bit-vector, which `bitblast_equal` reaches, since it matches `(= x y)` at any sort | an error, returned through `get_term_bits`, `shift_add_multiplier`, `bitblast_ult`, `bitblast_shift_op` and `bitblast_udiv_urem` |
| `la_mult_sign` (`extras.rs`) | `todo!()` for a factor of the monomial no hypothesis gives a sign | an error naming the factor |
| `la_mult_pos`, `la_mult_neg` (`extras.rs`) | `unreachable!()` on a multiplied atom whose operator is not a comparison, such as `(cl x y)` (found 2026-10-15 by the soundness battery, `--dialect clean --seed 77`) | `ExpectedComparisonOp` |
| `Term::as_usize_err` (`ast/term.rs`) | `to_usize().unwrap()` on an integer of `2^64` or more, such as `and`'s index argument | an error |
| `(_ BitVec w)` and `(_ bvN w)` (`parser/mod.rs`) | a width `w` of `2^64` or more unwrapped | parse errors |
| `(_ bvN w)` (`parser/mod.rs`) | the `N` of `(_ bvx 4)` or `(_ bv 4)` unwrapped | a parse error |

The parser also refuses 0-bit sorts, which did not panic in the parser. `(_ BitVec 0)` and
`((_ repeat 0) x)` made one; SMT-LIB requires a positive width, and on a 0-bit variable
`bitblast_ult`, `bitblast_equal` and the shift rules indexed an empty list of bits. The checks are
in `make_indexed_sort` and beside `repeat`'s result-width check (a result width past `usize` is
`BitVecWidthOverflow`, "Also hardened" below, which covers `concat`, the extensions, `repeat` and
`extract`).

Sites hardened the same way that no parsed step reaches, the parser ruling the shape out: the
`extract` and `sign_extend` indices of `bitblast_extract`/`bitblast_sign_extend` (numerals the parser
bounds), `get_bitvector_terms` (an operand of `bvand`/`bvxor`, a bit-vector by sort), the `choice`
binding of `pbblast_bvand`/`pbblast_bvxor` (the parser refuses an empty binding list), the sign-bit
subtractions of the signed `pbblast` rules, and the bit positions converted to `u32` in
`bitblast_const` and `pbblast_pbbconst`.

**Verdicts.** Each changed site returns the verdict it returned before on every input on which it
did not panic, and the same error message, with two exceptions, both refusals of input that is
wrong: fix 41, and 0-bit sorts. A 0-bit sort never occurs in a certificate a producer means, and no
test or fixture in this repository uses one.

**Tests.** `carcara/tests/malformed_steps.rs` (new) renames every step of ten small valid proofs to
every rule name `get_rule` dispatches on (read from its source, so a rule added there is covered
with no list to keep), with no `:args`, with `(cl)` and with zero to three integers or copies of the
first conclusion literal: 38,582 mutants, none of which may panic (134 did on origin/main), and at
least 95% of which must reach the checker (99.7% do). Its other six tests pin each class
in the table: the reported certificate and every rule of the first row on `(cl)`, `bitblast_equal`
at `Int`, fix 41 and its two satisfiable counterexamples, `la_mult_sign`, an index argument of
`2^64`, and the parser's widths, each with the well-formed form still accepted. All seven fail on
origin/main. `a_multiplied_atom_that_is_not_a_comparison_is_refused` (2026-10-15) holds `la_mult_pos`
and `la_mult_neg` to refusing `(cl x y)` under both dialects and accepting the comparison; on
origin/main `80f09a7e9` it panics. `crates/clean-auto/src/bridge/ay_backend/carcara_verify/malformed_step_tests.rs` sends
the reported certificate through Clean's adapter and renames every step of four certificate shapes
(a pseudo-Boolean word equality, an anchor closed by `bind`, AY's bit-vector `poly_simp` and a `drup`
refutation) to every rule with no `:args`, three integers or `(cl)`: 10,260 mutants through
`verify_alethe_proof`, none of which may panic.

**Measured.** The soundness battery at `--mutants 200 --seed 11 --threads 1` (deterministic)
checked the same 605,470 instances on origin/main `971772ea9` and on this tree, with the same
221,108 parse errors (and the same on `a8e90d4b5`, before the zero_extend dialect landed). Checker panics fell from 205 to 0, and no rule has a counterexample on either.
The battery drops a panicking instance whole; refused now, the steps before the refused one are
judged like any other accepted step, which adds 5 accepted `hole`, 2 `or` and 2 `resolution` steps
(all sound). Every other count is identical. `clean cert verify-external`, built from this change
on `a8e90d4b5`, refuses the reported certificate (`checking failed on step 't1' with rule
'pbblast_bvand'`, exit 1, no abort), verifies its unrenamed `drup` form, and fully verifies 54
certificates from trust-cg's proof-gate cache (the 5 largest, up to 72 MB, and every 110th by
size). Vendored suites (release):
lib 128/128, rules 230/230, `malformed_steps` 7/7, `problem_reading` 16/16, proof 3/3, battery ok.
clean-auto `--features carcara-verify,ay-bv-blast --lib`: 2,462 passed, and `targo tippy` on it with
`-D warnings` is clean. On this crate, `targo tippy --workspace --all-targets` reports the lints it
reported on origin/main, less one (the loop counter `extract` no longer has).

**Resources: the next entry.** A width that fits a `usize` but is in the billions is
well-formed, and bit-blasting it builds that many terms: the sweep's first run grew past 30 GB on
`bitblast_ult` of two `((_ zero_extend 4294967295) #b0)` operands (a case from `evaluate`'s tests
renamed) before it was stopped, which is why the sweep leaves out numerals of 6 to 19 digits.
`bitblast_udiv_urem_rec` also recursed once per bit. That is a resource budget, not a malformed
shape; it is "Bit-vector expansion has a resource budget", next.

### Bit-vector expansion has a resource budget (`checker/budget.rs`, `checker/rules/{bitvectors,clausification,extras,linear_arithmetic,pb_blasting,polynomial,quantifier,simplification,strings}.rs`, `rare/mod.rs`, `ast/{evaluate,term,rc}.rs`, `ast/pool/{mod,advanced,storage}.rs`)

A bit-vector width is a `usize`, and SMT-LIB puts no bound on it, so a step over a term of
4,294,967,296 bits is well formed and a few dozen bytes long. Upstream's bit-blasting rules build
a term per bit of every operand they split (the multiplier and the divider a term per pair of
bits), `poly_simp` and `aci_simp` compute `2^w`, and the pseudo-Boolean rules compared each
coefficient with a computed `2^i`. On such a step the checker of attacker-controlled certificates
allocated until the machine ran out of memory, or, for a `2^w` past GMP's integer type (about
2^37 bits), aborted in GMP. A shared (`:named`) subterm does the same at any width, from a few
kilobytes of text: an n-ary `bitblast_and`/`_or`/`_xor`/`_add` reads one `@bbterm` n times (a
285 KB certificate grew past 8 GB), `poly_simp` walks a shared subterm once per path to it and
multiplies out a product of sums (2^24 monomials from 2 KB), and `aci_simp` keeps every copy of
an argument of an operator that is not idempotent (2^30 arguments from 885 bytes). A checker
must refuse what it cannot afford to check, not die on it.

So every step that expands a bit-vector or a polynomial now has a budget: before building
anything, it charges what it is about to expand to an `ExpansionBudget`, and a step whose total would pass
`MAX_EXPANDED_BITS` = 2^18 = 262,144 is refused with `CheckerError::ResourceBudgetExceeded`,
whose message (`resource budget exceeded: <what> would bring the step to <n> expanded bits, more
than the 262144 one step may use`) carries counts, never a term. A step within the budget is
checked exactly as before; the budget only decides whether the check runs. The charges, each made
before the terms it counts are built (`checker/budget.rs` has the reasoning):

| Charge | Where |
|---|---|
| `w` for each operand whose bits it reads, split into `@bit_of`/`@int_of` terms or spelled out by the proof as a `@bbterm`/`@pbbterm` | `get_term_bits` (every `bitblast_*` rule), `get_bitvector_terms` (`pbblast_bvand`, `pbblast_bvxor`) |
| `i` for the bits `((_ sign_extend i) x)` adds | `sign_extend` |
| `w` per stage of the barrel shifter, `ceil(log2 w) + 1` stages | `bitblast_shift_op` (`bitblast_shl`, `_lshr`, `_ashr`) |
| `w * w` per product | `shift_add_multiplier` (`bitblast_mult`) |
| `4w` per divider step, one step per bit of the dividend up to its highest bit that is not `false` | `bitblast_udiv_urem_steps` (`bitblast_udiv`, `bitblast_urem`) |
| `w` for `2^w` | `poly_simp`'s modulus, `aci_simp`'s `bvand` identity `2^w - 1` |
| in words: 1 per term visited, plus the 64-bit words of the coefficient it carries and of the numeral it reads, plus `MONOMIAL_WORDS` (16) and the coefficient's words for each atom's monomial | `Polynomial::add_term` (`poly_simp`) |
| in words, per product of two polynomials: `MONOMIAL_WORDS` per pair of monomials (a constant that is not zero counting as one of degree 0), plus `n_B` times the factors and coefficient words of `A` and `n_A` times those of `B`; and `MONOMIAL_WORDS` for each monomial moved out of the product | `Polynomial::mul`, `Polynomial::add_term` (`poly_simp`) |
| in words, `w / 64` for each negative coefficient reduced modulo `2^w` | `poly_simp` |
| in words, 1 per argument a flattening builds | `apply_aci_simp` (`aci_simp`) |
| in words, for each conjunction, disjunction and literal, once per path to it, the clauses of the conjunctive normal form it builds times their most literals plus one; and 8 for each variable a universal quantifier binds, once per path to it | `cnf_cost` (`qnt_cnf`) |
| in words, for a quantifier over `k > 0` Boolean variables: 64 (a bit) for each of its `2^k` instances, and for each pair of a subterm of the body and its mask (the variables it mentions that its context has not rebound, when there is one), `2^|mask|` times 64 plus the words the rebuilt term copies (its argument list, and the names it binds) | `bfun_elim_instances` (`bfun_elim`) |
| `2^m` times its arguments plus one, for an application to `m > 0` Boolean arguments that are not constants | `apply_bfun_elim` (`bfun_elim`) |
| in words, for each flattening of a `str.++` application or a string constant, 1 for each term the walk visits, once per path to it, and 1 for each character past the first a split constant becomes | `StringStep::flatten` (the `concat_*` rules, `re_concat_unfold_pos`, `re_kleene_star_unfold_pos`) |
| in words, each value read or computed: 1, plus 1 for each 64 bits of its numbers (8 bytes of a string); and before a sum, difference, product or quotient of numbers is computed, twice the words its arguments' bits together, plus one each, can reach | `eval_op`, `eval_param_op` (`evaluate`) |
| in words: 1 per term visited plus the words of the coefficient it carries, plus the words of each numeral it reads | `LinearComb::add_term` (`la_generic`, `bounded_farkas`, `la_tautology`) |

A step's cost is the sum. A comparison, bitwise operation or addition of two `w`-bit operands
costs `2w`, so those rules check operands of up to 131,072 bits; the multiplier checks up to 511
bits and the divider up to 255. The per-bit work these charges do not count separately (carry and
comparison chains, selections) is a constant per charged bit, so the charge bounds what a step
builds. The divider's limit stays at 255 bits (a 256-bit division costs
262,656 and is refused), although per unit charged it takes half the memory `bitblast_neg` does
(302 MB at 255 bits against 601 MB at the budget, below): the charge stays conservative, and no
certificate below is wider than 128 bits.

**Words** (2026-10-14). `poly_simp`, `aci_simp` and `qnt_cnf` (below) build words and pointers,
not terms per bit, so their charges are in words, `WORDS_PER_EXPANDED_BIT` = 64 to an expanded
bit: such a step may use 2^24 words. Charged a bit a unit, as they were at first, they refused steps of a few kilobytes
that check in a few megabytes, none of them adversarial (the review measured each verified by
`46d887ef9`, before the budget, at 3 to 8 MB, the flat sums at about 100 MB, and refused by
`b09c2715c`; each is verified now):
`poly_simp` over a monomial of degree 362 on both sides (1.7 KB); over the spelled-out expansion
of `(x + y + z + 1)^16` on both sides (969 monomials, 34 KB a side), or a product of 16 copies of
`(+ x y z 1)`, written flat or by named squares, against it, over `Int` and 64-bit vectors; over
a flat sum of 131,100 atoms; and `aci_simp` over a chain of 724 nested `bvadd`s against its
flattening (37 KB), or of 3,000 (53 MB). A product also charged each monomial once more for a
constant that is zero, which builds nothing: `(* x x ... x)` was charged twice the monomials it
builds, and is now charged those.

The rate is measured, not assumed. A bit-blasted bit costs about 2.3 KB at the budget
(`bitblast_neg`, 601 MB at 2^18 bits); a word charged to these rules costs at most about 12 bytes
at theirs, once each monomial entry `poly_simp` builds is charged the 16 words it takes
(`MONOMIAL_WORDS`: the map's bucket, its index slot, and the heap blocks of the factors and of the
coefficient). Charged one word an entry, `(= (* S T) (* T S))` over two sums of 1,000 atoms (a
million monomials of degree 2 a side) was accepted at 445 MB, and over two sums of 2,000 refused
at 963 MB, where the budget stopped the second side. The costliest steps the word budget admits,
measured (release probe, one step, peak resident memory of the process): `aci_simp` over 23 nested
`bvadd`s of two copies (8,388,608 arguments) at 197 MB and over a chain of 5,791 nested `bvadd`s
at 175 MB; `poly_simp` judging a product of two sums of 700 atoms (490,000 monomials) at 120 MB,
over a product of two sums of 490 atoms on both sides (240,100 monomials a side) at 114 MB, over a
product of 16 sums of two (65,536 monomials of degree 16) at 73 MB, and over a monomial of degree
4,061 on both sides, the most the budget admits, at 4 MB; `qnt_cnf` over 19 disjoined
conjunctions (524,288 clauses of 19 literals) at 96 MB; each in under half a second. The
adversarial shapes measured below are still refused, at up to 197 MB rather than 6 MB: a product of 24 sums at 69 MB, 30 nested `bvadd`s of two copies under `aci_simp` at 197 MB
(after the flattenings the budget admits), and under `poly_simp` at 3 to 8 MB.

**A charge that was missing** (2026-10-14). Reducing a bit-vector polynomial modulo `2^w` makes
each negative coefficient a `w`-bit number, and nothing charged that. Within `b09c2715c`'s budget
(a unit a term visited, `w` for the modulus), `poly_simp` over `(= N N)`, `N = (bvneg (bvadd y_0
... y_97999))` at 65,536 bits (a 1.4 MB proof over a 4 MB problem that declares the `y_i`), was
accepted at a peak of 2,125 MB; the budget admitted 2^34 bits of such numbers (2 GiB). Each
negative coefficient is now charged `w / 64` words before the reduction: that step is refused at
77 MB, and at 65,536 bits the budget admits 6,037 negated terms on each side (100 MB of numbers).

The budget bounds one step. Across steps: the checker stops at the first step it refuses for any
reason; the terms an accepted bit-blasting step builds are those of its conclusion, which the
proof spells out, up to a constant factor (the divider discards one adder's sums, an n-ary step
its intermediate `@bbterm`s), and so are `bfun_elim`'s instances; `poly_simp` keeps nothing past
its step, nor does `qnt_cnf` (below), and neither do `aci_simp` and the string rules (since
2026-10-14). Its flattenings are not part of the conclusion: a
flattening of `n` copies of a shared sum is a term of `n` arguments the proof never spells out. They used to be added to the
term pool, where they stayed for the rest of the proof, up to one budget per accepted step: 2,000
steps of `(= n16 n16)`, `n16` a sum of two copies of a sum of two copies 16 deep over a fresh
constant (a proof of 1.2 MB), were accepted at a peak of 2,029 MB. `apply_aci_simp` now builds
them in a `StepTerms` (`ast/pool/mod.rs`), a hash-consing table the step owns on top of the pool,
which it only reads through the new `TermPool::find`: a flattening the pool already holds is the
pool's own `Rc`, any other is the step's, so every comparison the rule makes, by pointer or as a
multiset, is the one it made when the pool interned them, and the step's terms are freed when it
ends. The same proof is accepted at a peak of 23 MB (8.2 s against 7.0 s: the step frees what
the pool kept). Building the flattenings in a table that does not consult the pool would not be
exact: `(= (concat (concat a b) c) (bvand (concat a b c) #b111111111111))` compares the left
side's flattening, by pointer, with the pool's `(concat a b c)`, and was refused that way
(`aci_simp` "Flattenings compare as the pool's terms" in `tests/rules/simplification.rs` keeps
it; `aci_simp_adds_no_terms_to_the_pool` checks the pool). Nor does the budget bound the *time*
of a proof that repeats an affordable step, each time naming the same conclusion; the checker's
deadline does ("The checker stops at a deadline", below). The checker's other rules are not
charged.

**Why 2^18.** It is chosen from the certificates the checker exists for, with room to spare.
trust-cg's proof-gate cache holds 5,441 certificates (9.7 GB, every one Trust's gate has
produced): no bit-vector in them is wider than 128 bits, and the costliest step of any of them,
measured with every charge logged, costs 16,640 (12 certificates: 128-bit multiplications of
spelled-out operands, 128² for the products and 128 for each operand's bits; and 16,512 in 2
more, a 64-bit division). 3,629 certificates expand anything; the next costliest steps cost 4,224
and 4,160 (102 certificates) and 1,536. In words (see "Words", above), their costliest
`poly_simp` step costs 8,271 (130 bits, 128 of them a 128-bit modulus; 910 certificates use the
rule), and their costliest `aci_simp` step 8,196 (129 bits, 128 of them a 128-bit `bvand`
identity; 6 certificates use it). The budget is 15.75 times the costliest step: a full 128-bit division costs 65,792 and a
256-bit multiplication 66,048, a quarter of it.
And it is small enough to be cheap to refuse at: the widest step of each rule within the budget,
measured with the release probe (one step; peak resident memory of the whole process; check time
on a machine running other builds, load average 35, so an upper bound):

| Rule (width at the budget) | Peak RSS | Check |
|---|---|---|
| `bitblast_neg` (262,144) | 601 MB | 0.94 s |
| `bitblast_ult`, `_slt`, `_add` (131,072); `_udiv`, `_urem` (255) | 302 MB | 0.39 s |
| `bitblast_not` (262,144) | 192 MB | 0.17 s |
| `bitblast_mult` (511) | 191 MB | 0.22 s |
| `bitblast_var` (262,144); `_equal`, `_and`, `_xnor`, `_comp` (131,072) | 156 MB | 0.18 s |
| `bitblast_concat`, `pbblast_bvand`, `pbblast_bvxor` (131,072) | 106 MB | 0.12 s |
| `bitblast_shl`, `_lshr`, `_ashr` (13,797) | 89 MB | 0.11 s |
| `bitblast_add` over 256 copies of one `:named` 1,024-bit `@bbterm` | 333 MB | 0.41 s |
| `bitblast_and`, `_xor` over 129 copies of one `:named` 1,024-bit `@bbterm` | 39 MB | 0.03 s |
| `bitblast_sign_extend` (262,136 bits added) | 7 MB | 0.00 s |
| `poly_simp`, `aci_simp` (262,143) | 3 MB | 0.00 s |
| `aci_simp` over 23 nested `bvadd`s of two copies; over a chain of 5,791 nested `bvadd`s | 197 MB; 175 MB | 0.42 s; 0.32 s |
| `poly_simp` judging a product of two sums of 700 atoms; over a product of 16 sums of two; over a monomial of degree 4,061 on both sides | 120 MB; 73 MB; 4 MB | 0.16 s; 0.10 s; 0.11 s |

One bit past the budget, a 2-ary step is refused before its expansion, at no more than 82 MB (a
rule may split its first operand before the second one's charge refuses the step). An n-ary step
charges each operand as it reads it, so one copy past the budget it is refused after its first
rounds: `bitblast_add` over 257 copies at 332 MB, no more than at the budget. Twice the budget
would put the worst case near 1.2 GB a step, which parallel proof-gate checks multiply.

**What it fixes, beside the budget.**

| Site | Before | Now |
|---|---|---|
| `bitblast_udiv_urem_rec` | recursed once per divider step, `w` deep | `bitblast_udiv_urem_steps`, a loop over the same steps from the last to the first; it builds the same terms (`the_divider_loop_builds_the_recursions_terms` holds it to upstream's recursion, kept verbatim in the test, on every pair of words of up to 4 bits over `false`, `true` and variables, and 1,600 sampled pairs of 5 to 12 bits) |
| `check_pbblast_sum`, `check_pbblast_sum_short_circuit`, `check_pbblast_signed_relation` | compared each coefficient with a computed `2^i`, `i` taken from the sort (`2^(2^40 - 1)` overflowed GMP) | `is_two_to_the` reads the coefficient's bits (`is_two_to_the_agrees_with_shifting` checks it against the shift for every `i <= 210` and 1,146 coefficients) |
| `value` (`bitblast_const`), `pbblast_pbbconst` | added a computed `2^i` per set bit, time quadratic in the width | set bit `i`; the bits are distinct, so the value is the same |
| RARE's `bv_nil_if_empty` | computed `bvand`'s nil `2^w - 1` at any width | only up to `MAX_EXPANDED_BITS`; a wider nil is left un-normalized, as one of unknown width is: the empty `(bvand)` stays, neither refused nor normalized. Clean's adapter passes no RARE rules, so it does not reach this |
| `aci_simp`'s identity filter | cloned the identity for every argument it compared (a `bvand` identity is a numeral as wide as the operands) | compares each argument with it through a borrow (`Term` equality), not with a clone; it must stay a comparison of terms, since the identity is a fresh `Term` no pool holds, so no pool term is it by pointer |
| `Term`'s drop (`ast/term.rs`, with `Rc::into_inner` in `ast/rc.rs`) | freeing a term recursed once per level of the arguments it last held, so freeing the carry chain of a refused step (two levels per bit) could overflow the stack | arguments held in a list are freed from a work list (`freeing_a_deep_term_does_not_recurse_per_level` frees a 300,000-level chain on a 256 KiB stack) |

**`bfun_elim`** (2026-10-14). The rule replaces a quantifier over `k` Boolean variables by the
conjunction (or disjunction) of its `2^k` instances, each built by substitution, and an
application to `m` Boolean arguments that are not constants by an `ite` tree over `2^m` copies of
it. Upstream first reserved `Vec::with_capacity(2usize.pow(n))` for a quantifier over `n`
variables of any sort: about 45 of them asked the allocator for 256 TiB, which aborts the process,
and 64 overflowed `pow` (a panic under Clean's release profile, `overflow-checks = true`, and so
an abort with `panic = "abort"`). Below that, the expansion itself grew without bound. Both
expansions are now charged first (the table above): an instance can build at most as many terms
as its body has distinct subterms, counted by a walk that stops where the charge refuses anyway,
and the partial instances on the way are as many again, a constant factor; what expands nothing
(`k` or `m` zero) is rebuilt as it is and charged nothing. Upstream also skipped each binding that
is not Boolean with a recursive call, so a quantifier over 100,000 `Int`s took 60 MB of stack in
a release build, past a main thread's 8 MB; the skip is now `rposition`, and the recursion left
is one level per Boolean variable, 18 at most within the budget. Measured (release probe, 4 GB
cap), before / after: quantifiers over 30, 64 and 200 Booleans (500 bytes to 3 KB), past 4 GB in
11.7 to 13.4 s / refused at 2.8 MB; an application to 30 and to 64 Booleans, past 4 GB in 9.2 and
9.4 s / refused at 2.7 MB; over 45 Booleans, not run before (it aborts in the allocator) / refused
at 2.6 MB; the 100,000-`Int` quantifier, 60 MB of stack / 64 KiB or less (166 KiB unoptimized).
That charge counted every distinct subterm of the body, once an instance: a quantifier over `k`
Booleans whose body had more than `2^18 / 2^k` distinct subterms was refused whether or not they
mentioned the variables, so `(forall ((x Bool) (y Bool)) (or x y (= (+ i0 1 2 ... 70000) 0)))`
(409 KB), whose four instances origin/main checks at 34 MB, was refused. And it undercounted, found
while measuring the change below: an inner binder that rebinds one of the variables shadows it for
what it reaches, so a subterm shared under such binders is instantiated differently on each path,
and an instance can hold many versions of it. Over 12 variables, `L_i = (and (forall ((x_i Bool))
L_(i-1)) L_(i-1))` (291 KB) was admitted, built 1,254 MB in 52 s, and was refused only by the charge
of a nested quantifier (over 10 and 11, 157 and 492 MB); with `(let ((x_i true)) ..)` in place of
the binders it was accepted outright, at 1,702 MB in 118 s.

**`bfun_elim` instances** (2026-10-14, `bfun_elim_instances`). Where no `let` or `match` in the
body rebinds one of the quantifier's Boolean variables and no binder in it binds one twice, a single
substitution of a Boolean constant replaces the variable's free occurrences and nothing else: a
binder that binds its name is left as it is (`can_skip_instead_of_renaming`), and the only name
such a substitution renames is the variable's own, so nothing is renamed. Upstream's `2^k` chains
of single substitutions are then the simultaneous substitution of each variable's value (its last
binding's, the one a chain substitutes first), which the rule now builds directly: a subterm is
rebuilt only where it mentions a variable its context has not rebound, and is otherwise the body's
own term. Where a
`let` or `match` rebinds a variable, upstream's substitution renames the bound variable throughout
what it binds, whether or not the variable occurs there, and the cost of that is not bounded by
these pairs: such a step is refused (`bfun_elim: a `let` or `match` in the quantifier's body
rebinds one of its Boolean variables ...`), a deliberate refusal of a shape no surveyed producer
writes. Measured (release probe): the 70,000-term body is accepted at 61 MB in 0.17 s; the binder
chains over 8 to 13 variables are refused by the budget before building, at 3.2 to 5.6 MB in at
most 57 ms (over 8, which base judged at 22 MB, the instances need 256 x 1,026 = 262,656 terms, just
past the budget); the `let` chains are refused by the rule at 3.0 to 4.2 MB.
`instances_are_upstreams` (`clausification.rs`) holds the instances to upstream's chains, kept in
the test, term for term and in order on 4,000 random quantifiers (repeated names, `Int`s of the
same names, shared bodies under rebinding binders of either sort, `let`s of other names,
applications), and checks the refusals. No trust-cg certificate uses `bfun_elim`.
`resource_budget.rs` holds both charges to the edge (a
quantifier over 16 Booleans whose body is `(or x0 .. x15 (and x0 q0) .. (and x0 q110))` is judged by
the rule, one more `and`, or 17 Booleans, refused; over 14, `(or x0 .. x13 q0 .. q880)` judged and
882 constants refused; likewise an application to 14 Booleans of 15 and 16 arguments), accepts a
correct step, refuses 45, 64 and 200 Booleans, and checks the 100,000-`Int` quantifier on a 1 MiB
stack.

**What the instances build** (2026-10-14, review of the change above). That charge counted one
unit per pair of a subterm and a context, an instance, but rebuilding a subterm copies its whole
argument list, closed arguments too, and does so in each instance that rebuilds it. Over 14
Booleans, `(or x1 .. x14 c .. c)` with 16,000 copies of `c` (a 32 KB proof) cost `2^14 x 16`, the
budget exactly, and peaked at 2,065 MB in 8.8 s before the rule judged it (base was killed at its
3.5 GB cap); over 13, 2,000 and 8,000 copies took 134 and 520 MB, 8 bytes per argument per
instance. And the instances rebuilt a subterm in every instance although it depends only on the
values of the variables it mentions: over 16 Booleans, `(or x1 c .. c)` with 20,000 copies (40 KB)
took 19 s at 6 MB to build the same two terms 65,536 times. Keyed by the whole context rather than
by the variables in it the subterm mentions, a subterm reached under binders that rebind only
other variables was also counted once per binder: a `define-fun` `(T y) = (or y c .. c)` with
200,000 copies of `c`, used as `(T x1)` under the 255 binders over nonempty subsets of `x2` ..
`x9` inside a quantifier over `x1` .. `x9`, was refused at 263,168 (base built it and judged it
in 75 s).

A subterm's instance depends only on its *mask*, the variables it mentions free that its context
has not rebound, so the rule now builds each pair of a subterm and its mask once for each of the
`2^|mask|` assignments of the mask, whichever instances share it (`Instantiation`'s table is keyed
by the subterm, its mask and the assignment), and charges, in words (`WORDS_PER_EXPANDED_BIT` = 64
to a bit), 64 for each such term plus the words it copies, its argument list and the names it
binds with their bytes (`bfun_elim_copied_words`), and 64 for each instance's place in the
conjunction (the table above). That is what the instances build, and what `apply_bfun_elim`'s walk
over their conjunction visits. Measured (release probe built like the adapter, 3.5 GB cap), before /
after: the 14-variable, 16,000-constant body 2,065 MB / refused at 3.5 MB in 8 ms; the 13-variable
bodies 134 and 520 MB / refused at 3 MB; the 16-variable body 19.2 s / judged in 17 ms at 5 MB; the
macro under 255 binders refused / judged in 3.0 s at 22 MB. At the edge, over 14 Booleans the
`or` of the variables and 881 constants is judged at 124 MB in 0.57 s and 882 are refused; over 10,
16,244 constants at 133 MB; a body of `n` distinct `(and x1 .. xk c_j)` over `k` Booleans, the most
nodes the budget admits, is judged over 1 with 125,200 of them at 232 MB (142 MB of it the
problem's parse), over 4 with 14,977 at 128 MB, and over 8 with 883 at 84 MB. The 13- and
14-variable bodies, which the old charge let the rule judge, are refused deliberately: their
instances copy more than 2^24 words of argument lists. `instances_are_upstreams` still holds the
instances to upstream's term for term.

**Nested quantifiers that rebind their Boolean** (2026-10-14, from a review of
`7006ac377..6a7aff128`, finding 1). The review found `c7b3cf934`'s charge refusing the complete
certificate eliminating `B_359`, `B_k = (forall ((x Int) (b Bool)) (and (F b) (P x) B_(k-1)))`
(64 KB; `46d887ef9` checks it at 6 MB in 0.01 s), because it counted each level's whole nested
chain again. The instances above count only what a level rebuilds, so `B_359` to `B_16384` are
accepted, but the walk that finds which variables each subterm mentions (`bfun_elim_mentions`)
still visited every level below each level: time quadratic in the depth, 2.5 s at 4,096 deep and
39 s at 16,384 (2.2 MB), at the memory of the instances. A binder that binds every one of the
variables once mentions none of them free whatever it holds, and every substitution of upstream's
chain returns it whole (`Substitution::can_skip_instead_of_renaming`), so the walk no longer enters
it; a `let` or `match` inside it, which no substitution reaches, is not refused. Measured (release
probe built like the adapter): `B_4096` 2.47 s / 0.12 s, `B_16384` 39.0 s / 0.46 s (129 MB), both
accepted. `the_mentions_walk_stops_where_every_variable_is_rebound` holds the walk to the
outermost body's own terms under 1,000 such levels, and the instances, a `let` inside such a binder
included, to upstream's.

**Nested quantifiers named apart** (2026-10-15). Named apart, `b_k` at level `k`, no binder rebinds a
level's variable, so each level's walk still visited every level below it, quadratic in the depth.
The walk now records a subterm in which none of the variables' names occurs, free or bound, with the
mask zero and does not enter it (`NamesBelow`, `bfun_elim_mentions`): each subterm's set of the names
occurring in it (its variables' names and the names its binders, `let`s and `match` cases bind, in
the subterms the walk reaches) is the union of its children's and its own, a persistent set that
shares structure with theirs ("Free-variable sets share structure"), computed once for a step and
kept across its levels, so a chain of `n` levels costs a path of the sets a level, not `n^2 / 2`
names. It is exact: a nonzero mask comes from a variable of one of the names, and every refusal of
the walk from a binder, `let` or `match` case that binds one of them, so in a subterm holding none of
them the walk would have found only zero masks and nothing to refuse; the instances and their charge
read masks only below a nonzero one, where every child is recorded.

The sets have a cost of their own, which the lane's review found (2026-10-15): a merge of two sets is
linear in their size wherever they share no structure, and the sets cover every subterm of the
step's body, so they could be quadratic where the walk without them was linear. Two chains over
distinct constants merged at each link, `(h A_j B_j)` with `A_j = (f c_j A_(j-1))` and `B_j = (g d_j
B_(j-1))`, under `(forall ((b Bool)) (and b BIG Z))` with `Z = (and (pz c_1 d_1) ...)` interleaving
the names, all `:named` in the proof (5,000 links, 680 KB), took 1,560 MB and 1.65 s where base took
20 MB and 0.06 s; 40,000 links ran past a 4 GB cap. So the sets are computed with fuel
(`ast::pool::Fuel`): each term read earns 64 units for itself, each of its children and each name
it binds, and a merge or insertion spends 1 for each node it visits and 16 for each node it
allocates. One that would spend more than is left stops and drops what it built; the term then has
no set, nor does any term above it, and the walk enters such a term, as it entered every subterm
before the sets. So a step's sets allocate at most 4 trie nodes a link of the terms read (256 bytes)
and visit at most 64, and the walk costs at most what it cost without them. A chain of nested
quantifiers spends 28 to 40 units a link (2,000 to 100,000 levels) and keeps every set.

Measured (release probes built like the adapter, medians of three, base `40ea22d1c` / this tree),
the chains of nested quantifiers: 2,048 levels (390 KB) 0.93 s / 0.060 s, 8,192 (1.6 MB) 14.7 s /
0.24 s at 82 and 72 MB, 24,576 (4.9 MB) 191.6 s / 0.77 s at 207 and 220 MB, all accepted; 32,768
levels are refused by the step's budget on both. The merged chains at 2,500, 5,000, 10,000, 20,000,
40,000 and 80,000 links (0.33 to 11.7 MB): 0.024, 0.052, 0.11, 0.26, 0.64 and 1.36 s at 12, 20, 40,
74, 147 and 285 MB on base, 0.035, 0.079, 0.19, 0.41, 0.87 and 1.94 s at 21, 40, 76, 145, 293 and
567 MB here; with `B_j` over the `c_j` too, whose sets are equal to `A_j`'s but built apart (so each
merge visits them, allocating nothing), 0.024, 0.051, 0.12, 0.25, 0.55 and 1.23 s on base and
0.049, 0.11, 0.27, 0.68, 1.57 and 3.97 s here (the lane before the fix: 0.10, 0.24, 0.89 and 3.38 s
up to 20,000), at 12 to 290 MB and 17 to 422 MB. All are accepted.

Tests (`clausification.rs`): `names_below_spend_their_fuel_on_chains_merged_apart` reads 3,000
merged links one at a time and checks every 50 links that the trie nodes allocated are at most 4 a
link read (computed without fuel, the sets fail it at the 100th link, with 11,547 nodes for 1,610
links), that the chains keep their sets and some links have none, and that the walk's masks and the
instances over the whole quantifier are upstream's; `the_mentions_walk_skips_what_holds_none_of_the_names`
holds each level's walk of a 2,000-level chain under 16 subterms (base walked 8,004 at the top
level, and fails it), its instances to upstream's, and the refusals of a `let`, a `match` case and a
binder that rebind a variable inside a subterm that does not mention it free.
`tests/free_variables.rs` checks the complete certificates: 2,048 levels named apart
(`bfun_elim_over_quantifiers_named_apart_is_checked`) and the review's certificate at 1,000 links
(`bfun_elim_over_chains_merged_apart_is_checked`). The clausification tests run on a stack of their
own: reading the 1,000-level chain of `the_mentions_walk_stops_where_every_variable_is_rebound` took
the test harness's whole 2 MiB stack, and overflowed it on origin/main `40ea22d1c`.

**`qnt_cnf`** (2026-10-14). The rule converts its premise to conjunctive normal form, where a
disjunction's clauses are the product of its arguments', and none of its walks has a cache, so a
shared subterm is converted once per path to it. `(forall ((x Int)) (or (and a_0 b_0) ... (and
a_(n-1) b_(n-1))))` has `2^n` clauses of `n` literals: at `n` = 20 (497 bytes) the step was
accepted at 555 MB, at 21 at 1,240 MB, and at 26 (605 bytes) it grew past 6 GB in 1.6 s; a shared
conjunction doubled 24 times took 1.56 GB, and 30 times ran past 60 s. Before it prenexes, the
rule now charges what the conversion will build, counted over the DAG without building anything
(`cnf_cost`: for each node, once per path, its clauses times their most literals plus one, in
words), and a step past the budget is refused: the shapes above at `n` = 20, 21 and 26 and the
doubled conjunctions are refused at 3 MB. The prenexing walks also copy a quantifier's variables
once per path to it, which the clauses do not count: a quantifier over 2,000 variables under a
conjunction doubled 14 times (30 KB) was accepted at 1,510 MB, and 12 times at 382 MB. Each
variable is charged 8 words a path; those are refused at 4 MB, and 10 times (100 MB) is
admitted. Upstream's `distribute` also recursed once per disjunct
and copied each partial clause once per disjunct after it, so a flat disjunction of 100,000
literals took 14.8 s and one of 1,000,000 ran past 60 s; it now builds each clause once, in the
order the recursion did (`distribute_builds_the_clauses_upstreams_recursion_built` holds it to
upstream's recursion, kept in the test), checked in 0.12 and 3.0 s (the larger mostly parsing).
And upstream added every clause to the pool, where it stayed for the rest of the proof though the
conclusion names one; each is now compared with the conclusion's clause as the term it would be,
which is the comparison the pool made: `n` = 19 is accepted at 96 MB where it took 284 MB. No
trust-cg certificate uses `qnt_cnf`. `resource_budget.rs` holds the charge to its edge (19
accepted, its first and last clause found, a clause not in the form refused by the rule; 20
refused by the budget with the count `cnf_cost` gives; 26 refused; the 2,000 variables under a
conjunction doubled 10 times accepted, 11 times refused with its count), and `quantifier.rs`'s
`cnf_cost_counts_at_least_what_the_conversion_builds` checks the count against the conversion.

**`evaluate`** (2026-10-14, from a review of `7006ac377..6a7aff128`). The rule computes the value
of a ground term, caching each node of the DAG, and nothing bounded the integers and rationals it
computes: `MAX_EVALUATED_BV_WIDTH` (fix 35) bounds bit-vectors and `int.pow2`, not arithmetic. A
product squares what it reads, so `d_0 = 3`, `d_i = (* d_(i-1) d_(i-1))` reaches `3^(2^n)`, about
`1.58 * 2^n` bits, from text linear in `n`: `(= d_28 0)` (1 KB) peaked at 559 MB, `d_30` at
2,114 MB in 7.3 s, `d_32` (1.3 KB) grew past 3 GB, and past about 2^37 bits GMP aborts the
process. A sum of a rational and its reciprocal doubles a numerator and a denominator alike. The
evaluator now charges the step's budget, in words, each value it reads (a copy) or computes, one
word and one for each 64 bits of its numbers, and, before a sum, difference, product or quotient
of numbers is computed, twice the words its arguments' bits together (plus one each) can reach:
the result, and the space GMP works in. A number it computes therefore has at most 2^29 bits,
and a step's together at most 2^24 words. The terms it builds are hash-consed in a `StepTerms`
(as `aci_simp`'s flattenings are), not added to the pool, where every number computed stayed for
the rest of the proof. Measured (release probes of `6a7aff128` / this change, 3 GB cap, without
rendering the refusal): `d_24` and `d_26`, judged by the rule (neither is 0), at 33 / 35 MB and
140 / 140 MB, in 0.12 and 0.41 s alike; `d_27`, `d_28`, `d_30` and `d_32`, refused at 138 to
143 MB in 0.41 s, where `d_28` peaked at 559 MB and `d_30` at 2,114 MB. A `match` is now left
unevaluated, as a `let` is: it reached a `todo!()`, a panic and so an abort of the process under
Clean's release profile, from a three-line certificate (`(step t1 (cl (= (match x ((nil 0) ((cons
h t) h))) 1)) :rule evaluate)` over a declared list datatype; `malformed_steps.rs` now sweeps a
step over a `match`, renamed to every rule). `resource_budget.rs`'s
`evaluated_numbers_are_charged_before_they_are_computed` judges the products 24 deep and refuses
them 28 and 64 deep, judges the sums of reciprocals 16 deep and refuses them 64 deep, and accepts
a correct step.

**`la_generic`** (2026-10-14, from the same review). `LinearComb::add_term`, which reads the
linear combinations of `la_generic`, `bounded_farkas` and `la_tautology` (and of the Farkas
elaborator), walks a term once per path to each subterm, with no cache: upstream measured a cache
to double the rule's average time, and chose none. It was charged nothing, so a sum built by
doubling shared definitions, `d_i = (+ d_(i-1) d_(i-1))`, was visited `2^n` times: `(cl (<= d_n
0) (> x 0))` with `:args (1 1)` (which the adapter's rewrite of `la_generic` without `:args` does
not touch) took 4.7 s at 26 deep (1 KB), and 40 deep (1.5 KB) about 21 hours by extrapolation, at
3 MB. It is now charged as `Polynomial::add_term` is: a word for each term visited plus the
words of the coefficient it carries, and the words of each numeral it reads, so a step may visit
`2^24` terms. Measured (`6a7aff128` / this change): 20 and 22 deep, judged by the rule (the sum
is not a contradiction) alike; 24 deep 1.07 s / refused in 0.6 s; 26 deep 4.75 s / refused; 40
deep past 30 s / refused in 0.7 s, all at 3 MB. `resource_budget.rs`'s
`linear_combinations_are_charged_per_visit` judges 16 deep and refuses 24 and 40 deep.

Clean's adapter prints a budget refusal whole (`crates/clean-auto/src/bridge/ay_backend/carcara_verify/diagnostics.rs`):
`checking failed on step 't1' with rule 'bitblast_ult': resource budget exceeded: splitting a
bit-vector into its bits would bring the step to 4294967296 expanded bits, more than the 262144
one step may use; term details omitted`.

**Measured** (2026-10-14, release builds of origin/main `46d887ef9` and of this change, the same
probe parsing and checking as the adapter does):

- **Verdicts.** All 5,441 trust-cg certificates get the same verdict before and after: 5,428 fully
  verified, and 13 refused at the same `bitblast_ashr` step by both. None comes within a
  fifteenth of the budget.
  The soundness battery at `--mutants 200 --seed 11 --threads 1` (deterministic) checks the same
  605,470 instances with the same 221,108 parse errors before and after, and its per-rule report
  (accepted, exercised, unsound) is identical line for line; no rule has a counterexample.
- **Adversarial steps.** Before, each of these grew past 8 GB, where it was stopped (in 2.7 to
  14.6 s): `bitblast_ult` of two `((_ zero_extend 4294967295) #b0)`-wide operands (the case the
  sweep above ran into), `bitblast_udiv` of `((_ zero_extend 4294967295) #b1)`, and
  `bitblast_var`, `_ult`, `_neg`, `_udiv`, `_shl` at 2^32 bits, `bitblast_mult` at 2^20,
  `bitblast_sign_extend` by 2^62. `poly_simp` and `aci_simp` at 2^40 and 2^64 - 1 bits, and the
  signed `pbblast_*` rules at 2^40, compute a `2^w` past GMP's integer type, which aborts; they
  were not run on origin/main, to leave no crash report. After, every one of them is refused
  within 0.07 s at a peak of 3 MB: by the budget, and the pseudo-Boolean step by its rule, which
  now reads the coefficient without computing `2^(2^40 - 1)`.
- **Shared subterms** (8 GB and 60 s caps). Before / after: `bitblast_add` of 2,048 copies of a
  `:named` 2,048-bit `@bbterm` (70 KB), 5,328 MB in 9.8 s / refused at 332 MB in 0.7 s;
  `bitblast_and` of 8,192 copies of an 8,192-bit one (285 KB), past 8 GB in 10.5 s / refused at
  42 MB; the same at 2,048, 1,212 MB / 40 MB; `bitblast_ult` of two 2,000,000-bit spelled-out
  operands (8 MB), 1,231 MB and a stack overflow freeing the comparison / refused at 60 MB;
  `poly_simp` of a product of 24 sums of two 8-bit constants (2 KB), past 8 GB in 10.6 s, and of
  20, 625 MB / refused at 5 MB; `aci_simp` of 30 nested `bvadd`s, or Int `+`s, of two copies
  (900 bytes), past 8 GB in 13 and 20 s / refused at 6 MB; `poly_simp` of 30 nested `bvadd`s of
  two copies, still walking at 3 MB when stopped at 60 s, and of 30 nested Int `*`s, or 24 over
  a 16,384-bit numeral, still running at 2.5 GB when stopped at 60 s / refused at 3 to 5 MB. Every refusal is within
  0.7 s. (Charged in words since 2026-10-14, these are refused at 3 to 197 MB; see "Words".)
- **Time.** On the 5 certificates of the proof gate's speed report and the 10 slowest of the
  cache, three runs each (medians), instructions retired change by +0.04% to +1.51% (the drop's
  check of a freed term's arguments; the most, 30.93e9 vs 31.39e9, on a 69 MB certificate) and
  user+sys time by at most 0.05 CPU-s (1.25 vs 1.30 there, at load average 28); peak memory is
  unchanged to within 2 MB.

**Tests.** `carcara/tests/resource_budget.rs` (new) checks, for each of 17 rules, that the widest
step within the budget is judged by the rule and one bit wider is refused by the budget (widths
derived from the charges, so they follow `MAX_EXPANDED_BITS`); that a correct `bitblast_var` step
at the budget is accepted; that the reported case and a step of each kind in the billions of
bits are refused, with the count the refusal names; that n-ary `bitblast_and`, `_or`, `_xor` and
`_add` steps over copies of one `:named` `@bbterm`, and a comparison of two spelled-out operands,
are judged up to the budget and refused one copy or bit past it; that `poly_simp`'s products of
sums and walks of shared sums and products, and `aci_simp`'s flattenings of shared sums, are
judged a few levels deep and refused 30 deep; and that `poly_simp` charges a coefficient's words
(a 16,384-bit coefficient times a sum of 54,648 is judged and of 54,649 refused, while a one-word
coefficient times 54,649 is judged). `word_charged_rules_are_held_to_their_edges` holds the word
charges to their edges: a monomial of degree 4,061 on both sides is accepted and 4,062 refused
(362, which the first charges refused, is accepted); negating 6,037 terms of 65,536 bits on both
sides is accepted and 6,038 refused; `aci_simp` over a chain of 5,791 nested sums is accepted and
5,792 refused (724 is accepted).
`every_rule_on_a_wide_step_is_judged_within_the_budget`
(`carcara/tests/malformed_steps.rs`) renames each of 30 steps over 2^32 + 1 and 2^64 - 2 bit
operands to every rule `get_rule` dispatches on, in every argument shape (91,680 checks): none
panics, none exhausts memory (6 MB peak), and 1,072 meet the budget. Run against origin/main at
2^36 + 1 bits, the same sweep grew past 6 GB within 9 s and was stopped. The unit tests are in
`checker/budget.rs`, `checker/rules/bitvectors.rs` (the divider) and `ast/term.rs` (the drop),
and `diagnostics.rs` checks the adapter's message.

**The string rules** (2026-10-14, `checker/rules/strings.rs`). The last lane found them with none of
this, and measured the first two. They flattened `str.++` applications (`string_concat_flatten`,
`concat_extract`) and expanded string constants (`expand_string_constants`) by recursive walks
without a cache, once per path to a shared (`:named`) subterm, and added what they built to the
pool. Measured on base (`6a7aff128`, release probe, the adapter's parse and check, RSS and time
capped), each fix's commit has the details:

| Input | Base | Now |
|---|---|---|
| `concat_eq` over `(= n24 n24)`, `n_i = (str.++ n_(i-1) n_(i-1))` named (1 KB) | 776 MB, accepted | refused by the budget at 3 MB |
| the same 22 deep | 195 MB | 67 MB, accepted |
| an accepted `concat_eq` over `(str.++ "a" n24)` against `(str.++ "b" n24)` | 1,385 MB | refused at 3 MB (20 deep: 91 / 27 MB, accepted) |
| 32 accepted steps over chains 20 deep (33 KB) | 1,067 MB, 9.1 s | 28 MB, 1.7 s |
| a chain of `(str.++ "" "")` 30 deep; a conclusion `(= d30 d30)` of doubled `and`s | 20 s; past 120 s | refused at once; judged in 1 ms |
| `re_concat_unfold_pos` over `(str.to_re n24)` | 904 MB | refused at 3 MB |
| `concat_cprop_prefix`, `_suffix`, head word `c a^m b` against `a^(m+1)` | m = 3,000: 54 s; 10,000: past 1.7 GB and 120 s | 3.7 MB in 3 ms at 10,000; 5 MB at 30,000 |
| `re_concat_unfold_pos` over 20,000 / 50,000 `str.to_re` arguments | 1,688 MB / past 8 GB | 11.5 / 22 MB |
| the same over 5,000 arguments that are not `str.to_re` (10 KB) | 2,430 MB in 14 s, then refused | refused at 3 MB in 2 ms |
| `re_unfold_neg_concat_fixed_prefix` over a doubled `re.++` 30 / 70 deep | 7.3 s / past 120 s | 1 ms / refused as unmeasurable |
| `string_decompose` at a doubled sum 30 deep | 3.6 s | 1 ms |
| `concat_eq` stripping `2^16` copies of terms equal modulo an equality's order 10,000 levels down (121 KB) | 34.6 s | 20 ms |
| `concat_eq` stripping 16,000 distinct entries over two chains equal modulo an equality's order 16,000 levels down (2.6 MB) | 15.4 s | 134 ms |

What changed:

- **Flattenings are charged, walked by loops, and built outside the pool.** Each application of a
  string rule builds through a `StringStep`. A flattening is charged to the step's budget before
  it is built, in words (the table above): what it visits and builds, counted over the DAG with a
  count memoised per term. `expand_string_constants` expands each term once (an expansion depends
  on the term alone). Every term the rule builds is hash-consed in a `StepTerms` the step owns, as
  `aci_simp`'s flattenings are: a term the pool holds is the pool's `Rc`, so every comparison by
  pointer is the one the pool made, and the step's terms are freed with it. `(= n22 n22)` (two
  flattenings of `2^23 - 1` visits) is the deepest such step the budget admits.
  `flattenings_and_expansions_are_upstreams` holds the loops to upstream's recursions, kept in the
  test, term for term on 3,200 random shared terms.
- **`concat_cprop_prefix`, `_suffix`**: the overlap position is read off one Z-array over the
  middle word, a separator and the head word, in time and memory linear in both; upstream's
  `overlap` and `is_compatible` recursed once per position and per character, copying the rest of
  both words at each (`overlap_is_upstreams` compares them on every pair of words of up to 7
  characters over two letters and up to 4 over three).
- **`re_concat_unfold_pos`**: its helper recursed once per argument of the `re.++`, adding the rest
  of the list to the pool at each level, and built a Skolem witness for each argument that is not a
  `str.to_re` (each naming every one before it) before fix 32 refused the step. It now reads the
  arguments in one pass and refuses at the first that is not a `str.to_re`, before building
  anything (the message fix 32 gave); otherwise it builds the term upstream built
  (`re_unfold_pos_concat_is_upstreams`). `re_kleene_star_unfold_pos` is refused at the same place.
- **`str_fixed_len_re` and `is_syntactically_nonnegative`** (found while measuring) recursed once
  per path, in time exponential in a shared term's depth. Each visits each subterm once now, in
  upstream's order for the errors; a regular expression whose length passes a `usize` (64 levels
  of doubling), where upstream would have overflowed after as many steps, cannot be evaluated
  (`fixed_lengths_and_split_points_are_upstreams`).
- **Pairs of terms are decided once a step** (found while measuring, and by the review):
  `strip_prefix_or_suffix` and `is_prefix_or_suffix` compared entry by entry with a fresh
  `polyeq` each, and a flattening repeats a shared subterm's entries. Distinct entries can also
  share a deep subterm, which a comparator for each pair walked again: `concat_eq` over `(str.at
  X_d i)` against `(str.at Y_d i)` for `i < n`, `X_d` and `Y_d` equal only modulo the order of an
  equality `d` levels down, took 1.05 s at `d = n = 4,000` (615 KB) and 15.4 s at 16,000 (2.6 MB),
  quadratic. `StringStep::polyeq` compares every pair through one `Polyeq` for the step, whose
  cache holds each pair of terms it decides, equal or not ("`Polyeq` caches the pairs it finds
  unequal"); `polyeq` depends on the pair alone, so the answers are the same. Those inputs take
  32 and 134 ms (`a_step_decides_each_pair_of_terms_once`).

No trust-cg certificate uses a string rule. `resource_budget.rs` holds the flattening charge to its
exact edge (`concat_conflict` over 22 chains and `k` variables: 23 judged, 24 refused), accepts
`(= n22 n22)` and refuses 23 with its count, refuses the empty chain 60 deep, charges
`concat_extract`, and checks each fix above at the rule (`string_flattenings_are_charged_before_they_are_built`,
`expanding_a_shared_conclusion_visits_each_term_once`, `re_concat_unfold_pos_is_linear_in_its_arguments`,
`shared_regular_expressions_and_split_points_are_walked_once`); `tests/rules/strings.rs`'
`concat_cprop_overlap_positions` accepts both overlap rules at the position for six word pairs and
refuses one character before and after it; `string_rules_add_no_terms_to_the_pool` checks the pool.

### Diagnostics write a term abridged (`ast/printer.rs`, `ast/sort.rs`, four exact users)

A term is a DAG in the pool, and its text is the unshared tree: 40 definitions
`(define-fun d_i () Bool (and d_(i-1) d_(i-1)))` are 41 terms, and the text of `d40` is 2^40
copies of `p`. Upstream's `Display` for `Term` rendered that whole text into a buffer before
writing it, and every error message, the derived `Debug` of everything that holds a term, and the
74 `CheckerError::Explanation(format!(..))` sites go through it. So a step that only *failed*
could exhaust memory building its error: `bitblast_equal` on `(= (= d40 d40) true)` reads `d40` as
a bit-vector, and `bitvector_size`'s `format!` of it grew past 2 GB in 10.6 s (stopped at a 2 GB
cap; a 1.7 KB proof). A sort is a DAG too (`define-sort`), and its `Display` and derived `Debug`
wrote the unshared tree the same way, as `pb_blasting`'s error about a choice binder's sort does.
Clean's adapter never prints a term (`diagnostics.rs`), but the checker builds those messages
before the adapter sees the error, and other callers (the battery, `Debug`, a panic message) print
them.

The fix is in the one place every message goes through, not at the sites. `Display` for `Term`
and for `Sort` (and `Debug` for both, now `Display`, as `Term`'s already was) stream the text into
the formatter through the proof printer (`AlethePrinter`), which now also writes sorts
(`write_sort`, upstream's `Sort` text byte for byte), and stops at a limit:
`MAX_DISPLAYED_BYTES` (4,096) bytes per term or sort, after which the text ends in `...`
(cut at a character boundary), and `MAX_DISPLAYED_DEPTH` (64) nested terms and sorts, past which a
subterm is written `...`. The depth limit bounds the printer's recursion: writing a term 64 deep
takes about 60 KiB of stack in a release build (280 KiB unoptimized). Each limit is per `Display`
call, so a message naming three terms is at most about 12 KB, and building it costs no more than
writing it. A message that lists terms (a linear combination, a binding list, the `Debug` of a
list of terms) is abridged per item, so it is linear in the length of the list, about 4 KB an
item, as the list is in the input that names it; every `Explanation(format!(..))` site names a
fixed number of terms, and Clean's adapter renders no message that lists them. A term within the limits is written exactly as before.

Output that must be exact does not go through the abridged `Display`. Every user of `Display` for
`Term` and `Sort` was found by compiling the workspace with those impls removed: the proof printer
(`AlethePrinter`: proofs, `write_asserts`, the SMT problems written for external tools) never
used it except for a `match` scrutinee, now streamed through a printer set up as `Display` was, so
its text is unchanged; and four exact users now write `term.unabridged()` / `sort.unabridged()`
(new, the old unbounded text): `check_external`'s arguments to an external tool
(`checker/shared.rs`), `ProblemPrelude`'s declarations (the prelude handed to external tools), the
Eunoia translation's function names (`translation/eunoia/alethe_2_eunoia.rs`), and the battery's
`@@fill` term and its sort names (`soundness/src/{oracle,sort}.rs`). The rest are diagnostics.

**Measured** (the adapter's parse and check in a release probe, RSS capped):

- The reproducer above: before, past 2 GB in 10.6 s; after, refused at 2.8 MB peak in 1 ms, the
  error's message 4,208 bytes. The adapter prints `checking failed on step 't1' with rule
  'bitblast_equal': rule validation failed; term details omitted`.
- Two trust-cg certificates (4.6 MB each) that are refused at a `bitblast_ashr` step: rendering
  that refusal's message (an `EqualityError` naming two `@bbterm`s) grew past 6 GB in 63 s, where
  it was stopped; after, 8,304 bytes, at 50 MB peak for the whole check.
- The 5,441 trust-cg certificates: the same verdicts before and after (5,428 verified, 13
  refused at the same `bitblast_ashr` step), and the same text, byte for byte, from the prelude's
  `Display`, the proof printer (with sharing) and the sort of every premise and conclusion (7.8 GB
  in all).

**Tests.** `ast/printer.rs`: a 40- and a 100-deep doubling chain written abridged, as `Display`,
`Debug` and `{:#}` and inside an error; the full text within the limit and through `unabridged()`;
a cut inside a two-byte character; a 100,000-deep term written within a 1 MiB stack; a shared and
a deep sort; every sort variant, and `match`, `as`, binders, `let` and constants, written as before
by `Display`, `unabridged()`, the proof printer and the prelude. `diagnostics.rs` (clean-auto)
holds the adapter's message for the reproducer.

### The checker stops at a deadline (`checker/{deadline,mod,error}.rs`, `checker/parallel/mod.rs`, `ast/polyeq.rs`, `parser/{mod,error}.rs`; Clean's adapter, server and CLI pass one)

The resource budget bounds what one step builds, not how long a proof takes: a proof can repeat
an affordable step, and some comparisons are bounded by nothing but time (alpha-equivalence of a
shared term read under different bindings on every path, "Performance: `Polyeq` caches the pairs
it finds unequal", above). This document and `budget.rs` left that to "the caller's wall-clock
limit", and a review of `7006ac377..6a7aff128` (2026-10-14) found that Clean's own callers had
none. `clean-server`'s certificate handlers wrapped the synchronous check in `tokio::time::timeout`,
which cannot fire while a future that never yields runs, so a request held its runtime worker
until the check returned, whatever its `timeout_ms`; `clean cert verify-external` and
`verify-external-batch` had no limit at all.

So the checker takes a deadline (`checker::Config::deadline`, `None` by default). It reads the
clock before and after every command, and a command that ends past the deadline is refused with
`CheckerError::DeadlineExceeded` ("the check ran past its deadline"), whatever it found. Inside a
command, `Polyeq` polls it per comparison (`checker/deadline.rs`'s `expired`, which reads a
thread-local flag and the clock once every 4,096 polls) and stops when it has passed, caching
nothing: the answer it then gives is never used, because the command is refused. The deadline is
kept per thread, for the check running on it; a check inside another keeps the earlier deadline.
The parallel checker's workers read it as the sequential checker does. A check that ends before
its deadline is the check it was without one: the deadline only decides whether it goes on.

Clean passes it: `verify_alethe_proof_until` (clean-auto; `verify_alethe_proof` has no deadline)
checks before each reading of the problem and after parsing it, parses under it (since
2026-10-16, "The parse stops at the deadline" below; until then parsing was not interrupted),
does not retry a reading the deadline stopped with the definitions expanded, and returns
`VerifyError::CarcaraDeadline`; `verify_alethe_certificate_until`
(clean-elab) returns the new `timeout` error code; the server's external-certificate handlers run
every verification off the runtime's threads (on Tokio's blocking pool until 2026-10-15, on
`clean-server`'s work pool since, below), so the request's timeout fires while it runs, and
hand the Alethe check the request's deadline (the batch handler also starts no item past it);
and `clean cert verify-external` and `verify-external-batch` take `--timeout-ms`, a limit on each
Alethe check (600,000 by default, `0` for none). Measured (release probe, the adapter's parse
and check): the alpha-equivalence chain 40 deep (`2^40` comparisons; 22 deep took 3.3 s), which
`6a7aff128` was still checking at a 30 s cap, is refused 0.201 s after the check starts with a
0.2 s deadline, and 2.001 s with a 2 s one, at 3 MB. That chain is now decided in a millisecond
(answers found under a binder are reused under its siblings, above), so since 2026-10-15 the
tests use one whose siblings bind `x(i-1)` at different indices while the leaves read every `xi`,
which reads different bindings on every path and so shares no answer: 40 deep it is refused
0.201 s and 2.000 s after the check starts with deadlines of 0.2 s and 2 s, at 4 MB, as on the
base tree. Its levels are defined in the proof, where the binders they are used under capture the
`xi` their definitions read (in the problem that is refused, fix 36). The tests: `deadline.rs`'s
unit test (the per-thread deadline and its restoration), `resource_budget.rs`'s
`the_checker_stops_at_its_deadline` (that chain refused at the deadline although `refl` holds, a
passed deadline refusing the first command, a distant one changing nothing), and in Clean the
adapter's `a_check_stops_at_its_deadline`, the server's
`test_verify_alethe_certificate_stops_at_its_timeout` and the CLI's
`cert_verify_external_alethe_stops_at_its_timeout`.

**The parse stops at the deadline** (2026-10-16). Parsing was not interrupted: the adapter read the
clock before each reading of the problem and after it, so a parse ran to its end however long it
took, past the caller's deadline, holding its thread and its checker slot. A parse is linear in its
input but for the shapes this document leaves open, and for scopes nested deep (the symbol table
looks a global up through every scope, upstream's design): 8,000 nested quantifiers that each
mention a global 50 times (1.1 MB) take 4.3 s to read in a release build. `parse_instance_until`
(`parser/mod.rs`) sets the deadline on the thread for the parse (`deadline::arm`, as the checker
does), and the parser polls it (`deadline::expired`: a thread-local read, and the clock once every
4,096 polls) at every token it reads (`next_token`), at every new subterm whose depth it records
(`record_depth`, which a term built from definitions reaches many times per token), and in the
capture checks' loops over names and variables. Past the deadline a poll refuses with
`ParserError::DeadlineExceeded` ("the parse ran past its deadline") at the current position, and a
parse that ends past its deadline is refused whatever it read (`parse_instance_with_pool` reads the
clock once more at the end; the flag a poll latches stays set until the parse ends), so no refusal
caught on the way can leave a parse cut short to be returned. A parse that ends before its deadline
is the parse it was without one. Clean's adapter parses with `parse_instance_until` and maps the
refusal to `VerifyError::CarcaraDeadline` (`diagnostics.rs`), which `pb_widths.rs` does not retry
with the definitions expanded.

Measured (release probes built like the adapter, base origin/main `f1d72b1fb`, a 0.2 s deadline,
medians of three runs interleaved), base / new: the 1.1 MB problem above read whole and refused
after parsing at 3.87 s / refused by the parser at 0.204 s; the 8,000 links each one binder deeper
than the last ("Free-variable sets share structure", 0.9 MB) 2.19 s / 0.209 s; 600,000 flat
assertions (17.3 MB) 1.16 s at 525 MB / 0.214 s at 144 MB. Without a deadline the polls cost
nothing measurable: the 1.1 MB problem parses in 4.32 s on both, the 17.3 MB one in 1.11 s and
1.07 s. The tests: `parser/tests.rs`'s `a_parse_stops_at_its_deadline` (a deadline already passed
refuses at the first token, a distant one changes nothing; with `parse_instance_until` shimmed onto
base, which polls nothing, it fails there) and `a_parse_cut_short_by_its_deadline_is_refused_never_returned`
(3,000 named links in binders of their own and a proof of 3,000 steps, read under 41 deadlines from
0 to 4/3 of the time the parse takes without one: each reading is refused with the deadline's
refusal or returns the problem and proof whole), and the adapter's `a_parse_stops_at_its_deadline`
(the 1.1 MB problem with a 0.2 s deadline is refused by the parser, and not read again). Not
interrupted: between two polls the parser finishes one step of its own, such as a definition's
expansion (a substitution over its body) or the free variables of a term a capture check asks the
pool for, and that one step can be quadratic ("Free-variable sets share structure", "Not fixed"):
two chains over distinct constants named at top level, merged in a random pairing and folded, all
named there (so no set is computed), then one binder naming the fold inside a binder, so that one
capture check asks the pool for the fold's free variables (the review's `apartperm_onebind`). With a
0.2 s deadline the parse is refused only after that step: at 5,000 links (1.1 MB) after 3.9 s at
1.39 GB and at 10,000 (2.2 MB) after 12.0 s at 5.1 GB in the review's runs, where base, which reads
the clock only after parsing, took 4.0 s at 1.49 GB and 13.8 s at 5.9 GB; at 5,000 links 1.62 s at
897 MB with the table's bound, against 1.73 s at 1,387 MB before it. Deep scopes are interrupted:
8,000 nested binders over 200,000 mentions of a global were refused at 0.214 s in the review's runs
(base 6.1 s).

A parse that hits an ordinary parse error after its deadline has passed is refused as
`ParserError::DeadlineExceeded`, which the adapter maps to `CarcaraDeadline` and `clean-elab`
reports as its `timeout` code, where base returned the parse error itself (unless the `define-fun`
retry reached the deadline first); a problem refused for a capture under a tight deadline is likewise
now refused as the deadline. Either way nothing is accepted: only the refusal's category moves.

**The rest of `clean-server`** (2026-10-15). The external-certificate handlers were the only ones
fixed: every other handler with a `timeout_ms` wrapped its synchronous work in
`tokio::time::timeout` (`check`, `prove`, `batchCheck`, `verifyCert`, `verifyCertArchive`,
`batchVerifyCert`, `batchVerifyCertArchive`, `getPremises`, `batchGetPremises`, `proveTLA`,
`batchProveTLA`, `verifyC`, `searchProof`), checked it only between tactic steps
(`verifyProof`, `verifyProofBatch`, `verifyFile`, `fillSorries`, `composeProof`), or accepted
it and ignored it (`initProofState`, `applyTactic`, `batchApplyTactic`); the batch handlers that
did run on Tokio's blocking pool ran abandoned work to its end. Measured on the release server
(`40ea22d1c` with `clean server` kept serving, Init preloaded: 94,670 constants), a `check` of
`rfl` at `Nat.rec` unfolded 60,000 times with `timeout_ms: 300` answered a valid result after
2.87 s, and a `check` of `Nat` sent 0.3 s later on another connection waited 2.57 s for it, on
the default 18-worker runtime; a `verifyCert` whose `DefEq` step asks the certificate verifier to
reduce `(fun x => x x) (fun x => x x)` (its reduction has no fuel) with `timeout_ms: 500` never
answered, and the server reached 8,236 MiB in 1.3 s, when the probe killed it.

The kernel now has the interrupt `TypeError::Interrupted` was reserved for:
`clean_kernel::tc::run_until(deadline, f)` installs a deadline on the thread for one call
(`tc/deadline.rs`). The tick sites the heartbeat and the declaration budget already use poll it
(`infer_type`, `whnf_impl`, `is_def_eq_core`, the retained-certificate inference), and so do the
certificate verifier's recursion and reduction (`CertError::Interrupted`) and clean-auto's
work-budget charges, which the superposition loop makes instead of kernel calls. A poll reads the
clock once every 1,024 polls and latches; past the deadline the work degrades as on a spent
heartbeat (refusals, unreduced terms, "not shown equal"), and `run_until` returns `None` whatever
the work then returns, so nothing reached past the latch is reported. A call the deadline never
interrupted returns what it returns without one, and a thread without a deadline pays one
thread-local load per tick. Work that is bounded by construction and fills process-wide state
(the cubical authority's canonical table, the elaborator's bridge seeding) runs with the deadline
suspended, so a deadline cannot leave a half-built table for the next caller. `clean-server` runs
each request's work on a pool of threads (`handlers/work.rs`) under the request's deadline: the
request's timeout fires on time and answers the existing timeout error (`-32004`), the work stops
at its next tick, at most one piece of work per core runs at once (abandoned work included; a
request waits for a slot inside its own timeout), and a thread whose work was interrupted or
panicked exits rather than keep thread-local caches (the simp-set cache) filled past the deadline;
a batch that runs tactics does so on a rayon pool of its own for the same reason. The shared
environment is only read, and proof states are cached on the async side from work that finished.

Measured with release servers built from `40ea22d1c` (with `clean server` kept serving) and from
this change, alternating, two rounds on the shared machine at a load of 50 to 57: the `check`
above answers the timeout error 0.306 s and 0.308 s after it was sent, against a valid result at
3.42 s and 10.28 s, and the `check` of `Nat` sent 0.3 s later answers in 6 and 7 ms, against 3.12 s
and 9.98 s; a `batchCheck` of four such items with `timeout_ms: 300` answers the timeout error at
0.302 s and 0.304 s, against a result at 21.1 s and 37.7 s; the self-applying `verifyCert` answers
the timeout error at 0.503 s and 0.506 s, the server peaking at 2,491 and 2,465 MiB (from 13 MiB:
the certificate grows memory until its deadline), where on `40ea22d1c` it had not answered when
the server passed 8 GiB at 1.6 s and 3.6 s. The server's CPU a second after the answers is 0.0 to
0.4%. With no deadline installed the tick sites cost nothing measurable: `clean check` of `rfl` at
`Nat.rec` unfolded 60,000 and 20,000 times and of a structural sum to 40,000, five runs each,
alternating, takes 9.27 s, 3.99 s and 6.68 s of user time on `40ea22d1c` and 9.28 s, 4.03 s and
6.66 s with this change.

Not fixed: work that polls no tick site runs to its end after its request has answered (parsing,
a decision procedure bounded only by its own counts such as the SMT conflict limit, scoring the
premises of one goal, a Farkas or entailment certificate, one big-number operation); the pool's
slots bound how much of it piles up. The certificate verifier's reduction still has no fuel of its
own, so until its deadline the self-applying certificate grows memory at the rate measured above;
its code is `clean-kernel`'s (`cert/reduction.rs`), so fuel waits for a pin train (still open on
2026-10-16). Methods without a `timeout_ms` other than `getType` ran on the runtime's threads:
`addDecl` (bounded by its heartbeat limit, and holding the session map's write lock while it
checks), the certificate compression and archive methods, `proofState.openObligation`,
`getProofState`, `proofState.searchTheorems`, `proofState.searchTactics`, `extractProof`, the
environment methods, and the widget and goal methods. Reconciled with the code on 2026-10-16:
`getType`, `addDecl`, `proofState.openObligation`, a solved state's `getProofState`,
`extractProof` and `loadEnvironment` run on the pool under a `timeout_ms` (R32, landed at
`cb6f601fd`, below), `importModule` too (`3e6c70906`, R34), and the certificate codec methods,
`saveEnvironment`, `getEnvironment` with its JSON, the two proof-state searches and an unsolved
state's `llm` `getProofState` as well (R36, "The server's residuals after the writers", below).
What still runs on the runtime's threads is mostly bounded by tables the server keeps or by a
constant: an unsolved state's `full` or `compact` `getProofState` with no Mathverse corpus
installed (a rendering), `getEnvironment`'s summary, `proofState.close`, `retain` and
`explainFailure`, the widget methods (registry look-ups), the goal methods (empty answers) and the
status methods. Two things there grow with a request's input, which the transport bounds at 10 MiB
(a TCP line, and a WebSocket message since the review below): the transport's parsing of each
request and writing of each answer, and `verifyFile`, `fillSorries` and `composeProof` parsing
their file (`parse_lean_file`). The rest is in the "Still open" list below. The
tests: `deadline.rs`'s 13 (the latch, nesting, suspension,
restoration on unwinding, thread locality, the type checker refusing past a deadline and unchanged
before it, the certificate verifier stopping on the self-applying certificate), clean-auto's
`test_work_budget_charge_refuses_past_a_callers_deadline`, the pool's 7 (`work_tests.rs`: reuse,
retirement after an interrupt or a panic, the slots bounding abandoned work, a batch item that
panics past its deadline counting as interrupted) and `request_deadline.rs`'s 21: a positive
control and one test per handler but proveTLA's (no slow obligation was found) and the external
certificates' (whose own tests predate this). In each, the slow request answers the timeout
error, a fast `check` sent 50 ms later is answered first on the test's single-threaded runtime,
and the abandoned work's slot comes back within the one-minute hang detector (for the batches and
the self-applying certificate, whose unbounded work runs far past it). On `40ea22d1c` 19 of them fail
or never finish: 11 answer a result instead of the timeout error, 4 are killed at a 180 s wall cap
and 4 at a 6 GB memory cap. The positive control passes there, and so does batchProveTLA's: that
handler already ran on Tokio's blocking pool, so its timeout fired, and the batch it abandoned
(which ran on to its end) shows only in the pool's slot count, which `40ea22d1c` has no pool to
report.

**The review's findings on the server timeouts, fixed forward** (2026-10-15). Each is pinned by a
test that fails on the lane before the fix (`2beb9e958`, merged with main) and passes after it;
the server's are in `handlers/tests/request_work.rs`.

1. Lock order. `applyTactic` took the environment's read guard and then waited for a work slot;
every other pool request takes the slot first. The lock is write-preferring, so a queued writer
(`verifyFile`, `fillSorries` and `composeProof` set the environment up under the write lock) closed
a cycle: the slot's holder waited for the guard behind the writer, the writer for `applyTactic`'s
guard, `applyTactic` for the slot. Nothing on the pool was answered until `applyTactic`'s own
`timeout_ms` passed. It takes the slot and then the guard now, both inside its timeout, and
`work.rs` states the order. `apply_tactic_never_waits_for_a_slot_holding_the_environment` (one
slot held 3 s by a check, a queued `getType`, `applyTactic rfl` with an hour's timeout, a queued
`verifyFile`): before the fix `applyTactic` was not answered within the one-minute hang detector
(11 s of CPU in 76 s of wall time), after it all four answer. Release server, Init preloaded, 18
slots each held by a check interrupted at 3 s, 18 queued `getType`s, the same `applyTactic` and a
`verifyFile`: the checks answer the timeout error at 3.01 s, the writer at 3.33 s, the `getType`s
at 3.34 s and `applyTactic` its proof at 3.42 s.

2. A release server aborted on `proveTLA` with `timeout_ms: 0`. The engine was built under the
request's deadline; a deadline already passed refused `Environment::new()`'s first seed declaration,
and its `expect` panicked, which `panic = "abort"` turns into a killed server: the pool's
`catch_unwind` was dead code in release. `Environment::new()` now seeds its three declarations with
the deadline suspended, and clean-tla's `TlaContext::new`, `TlaTacticEngine::new` and `with_env`
seed their theories with the ambient bounds suspended (`with_declaration_budget_suspended`): fixed
sets, bounded by construction, so nothing changes without a deadline. No answer depends on catching
a panic any more: the pool counts what it catches, and `no_request_work_panics_at_a_short_deadline`
sends 15 methods (6 tactics for `applyTactic`) at deadlines of 0 to 21 ms and requires none (before:
`proveTLA` at all 5 deadlines). Also `prove_tla_work_never_panics_at_a_short_deadline`, the kernel's
`a_fresh_environment_is_seeded_whole_under_a_passed_deadline` and clean-tla's
`test_tactic_engine_is_built_whole_under_a_passed_deadline`, each a panic before the fix. The
review's release probe (`tla_crash_probe.py`) on the fixed binary: `proveTLA` with `timeout_ms` 0
(twice), 1 and 3 answers the timeout error in 1 to 5 ms, and the server goes on serving.

3. `batchCheck` read neither the latch nor the clock between items, so past its deadline it went
through every item left in degraded mode, holding its slot and the environment's guard (the
review: 20,000 items, the slot back 19 s after the answer). It reads the clock before and after
each item now. `batch_check_gives_its_slot_back_at_its_deadline_whatever_is_left` (200,000 items,
300 ms): before the fix the slot was not back within the hang detector.

Also fixed from the review: an item the deadline may have cut short is no longer reported as a
verdict on the progress stream (`batchCheck`, `batchGetPremises`, `verifyC` read the clock after
each item; `batch_check_reports_no_verdict_its_deadline_cut_short` sweeps 21 deadlines and can
only fail on a wrong verdict, but the race it guards did not show on the lane either); a panic
before the deadline answers an internal error instead of being resumed on the request's task,
which dropped the TCP connection; a batch's rayon pool has at most one thread per item and a batch
whose pool cannot be built answers an internal error instead of falling back to rayon's global pool;
`batchVerifyCertArchive` reads the clock between the archives it unpacks; `JSON_RPC_API.md` says
that the verify family sets the environment up outside its timeout and that `initProofState`,
`applyTactic` and `batchApplyTactic` now get the server's default timeout without one.

Left open: `getType` has no deadline and holds its slot until its work ends, so a few slow ones can
occupy every slot and requests that carry a timeout then answer the timeout error while they wait
(on `40ea22d1c` they held runtime workers instead; closed the same day, below); the verify family's
environment setup waits for the write lock outside its timeout, by design; `batch_prove_tla_stops_at_its_deadline` passes on
`40ea22d1c` too (its abandoned batch shows only in the pool's slot count). Not a defect:
`prelude_reuse` reuses the shared template under a deadline, and should, because the template is
built on its own worker thread, which has no deadline, so the prelude reused is whole.

**`getType`'s deadline, and the other kernel checks the lane left without one** (2026-10-15). The
first item left open above is closed: `getType` takes a `timeout_ms` (the server's default without
one) and runs under its deadline as `check` does. An audit of every handler for kernel work outside
a deadline found more, all on the runtime's threads with none: `proofState.openObligation`
inferred the goal's type; `getProofState` and `extractProof` re-checked a solved state's closed
proof; `applyTactic` re-checked the closed proof of the state it solved, or of a solved state it
was sent, after its work had answered; `addDecl` checked its declaration holding the session map's
write lock, bounded only by `heartbeat_limit` (none at `0`); and `loadEnvironment`'s merge
re-checked every loaded declaration holding the environment's write lock. Each now runs that work
on the pool under its request's deadline (`applyTactic` inside its own `timeout_ms`; the others take
one, ten times the default for `loadEnvironment`), and a check the deadline interrupts answers the
timeout error and keeps nothing: no state opened, no declaration added, nothing merged, never
`verified: false`. The writers check on a copy, which replaces the session only when the
declaration is accepted and the environment only when the merge finished; their locks are held
across the check as before, taken after the work slot. The methods still on the request threads
make no kernel check (the codec and archive methods, the environment's save, summary and import,
the proof-state search, close, retain and explain methods, widgets, goals and status). Decision:
`docs/DECISIONS.md` R32.

Measured in debug test builds on the shared machine (load about 60 on 18 cores), base `f1d72b1fb`
against this change: two `getType`s of `rfl` at `Nat.rec` unfolded 60,000 times with
`timeout_ms: 300` filling a two-slot pool answered their type at 10.7 s and 10.9 s, and a `check`
queued behind them with the default timeout answered the timeout error at 5.02 s; with this change
the `getType`s answer the timeout error at 0.303 s, the slots are back 20 ms later, and the queued
`check` is answered at 0.381 s. The new tests (`request_deadline.rs`: one per handler above;
`request_work.rs`: `slow_get_types_give_their_slots_back_at_their_deadline`) all fail on the base,
each answering a result instead of the timeout error: `getType` its type after 12.6 s, `addDecl`
an accepted `kernelVerified` verdict, `loadEnvironment` a finished merge, `extractProof` a verified
certificate. `no_request_work_panics_at_a_short_deadline` sweeps the seven requests too, with no
caught panic. A `getType` sent without `timeout_ms` now answers the timeout error past the default
(`apply_tactic_never_waits_for_a_slot_holding_the_environment`'s queued `getType`, which waits
behind a 3 s check and a writer, now carries the hang detector as its timeout).

Not fixed: `loadEnvironment`'s merge still holds the environment's write lock while it runs (now at
most until its timeout), so requests that read the environment wait for it. `importModule` loads on
a blocking thread outside the pool with no timeout, and installs a clone of the environment taken
before its load, so an environment change that lands meanwhile (a merge, the verify family's setup)
is overwritten. `proofState.openObligation` refuses as "not a type or proposition" a goal whose type
reduces to `Prop` only past the kernel's unfolding of a large literal (`Nat.rec` on a literal of
80,000 here, where 60,000 opens): a refusal, not a wrong verdict.

**The concurrency review of that change, fixed before it landed** (2026-10-16). Two regressions
reachable over RPC, and one wait outside a timeout:
- `getProofState` sent every state through the pool, though only a solved state's trust summary
  re-checks a proof (an unsolved state's is its ledger's, and the rest is rendering). One slow
  `check` holding a one-slot pool made it answer `-32004` after 1.0 s, where the base answered in
  4 ms. It takes a slot only for a solved state now; an unsolved one renders on the request
  thread, its wait for the environment inside its timeout (R32: no kernel check, no slot).
  (Narrowed 2026-10-16, "The server's residuals after the writers", below: the default `llm`
  snapshot selects premises from the whole environment, so it takes a slot too.)
- `proofState.openObligation` checked its goal on the pool under one read of the environment and
  rendered the new state under a second, taken outside its timeout. A `loadEnvironment` merge
  queued during the check was granted in between, so the request answered at 14.9 s with
  `timeout_ms: 12000` (the base, 2.9 s), against an environment other than the one it checked
  in. It renders from the read its check held now (`core::slot_then_env`, which `applyTactic`
  shares).
- `addDecl` looked its session up before its timeout started, so behind another session's check
  it answered after 2.9 s with `timeout_ms: 300`; the look is inside the timeout now.

`request_work.rs` pins each, deterministically: the test holds the pool's only slot (an unsolved
state's `getProofState` is answered, a solved one's times out), a writer queued during the goal's
check that keeps the environment until `openObligation` has answered (a second read never
answers), and the session map's write lock (`addDecl` answers `-32004`). All three failed on the
first cut (`c25bd4972`), each at the hang detector, and pass with the fix. The reviewer's own
timing reproducers agree: `getProofState` 4.7 ms, `openObligation` 2.8 s with the merge after it at
12.3 s, `addDecl` 302 ms.

Left open, reachable only from Rust (no method opens a session; `ServerState::create_session` has
no caller outside the tests): `addDecl` holds the session map's write lock across its check, so
`addDecl`s to different sessions wait for each other, and one queued for that lock holds its work
slot while it waits, in the pool's lock order. A burst of them fills the pool: with two slots, two
queued behind a third made a `check` of `Type` with `timeout_ms: 1000` answer `-32004`, where the
base, whose `addDecl` took no slot, answered in 1 ms. A lock per session would end the wait
across sessions. Ending the slot held while queued needs that session's lock taken before the slot
(safe only while no slot holder waits for a session), or a check on a copy committed only when the
session has not changed since. Each changes how concurrent `addDecl`s are ordered, so it waits for
a method that opens sessions.

**The writers' residuals, fixed** (2026-10-16). Three of the four items R32 left open (the
`addDecl` session lock above, the merge's write lock, `importModule`'s lost update and
`openObligation`'s refusal; `docs/DECISIONS.md` R34 lists them) are closed:
- `addDecl` sessions have a lock each. The session map is held only to look a session up, so
  `addDecl`s to different sessions no longer wait for each other. Those to one session are checked
  one at a time, first come first served (tokio's `Mutex` is fair), each against every declaration
  accepted before it. A session's lock is taken before the work slot, so one waiting for its
  session holds no slot. That order closes no cycle: no slot holder waits for a session.
- `loadEnvironment`'s merge and `importModule` work on a copy of the environment, made under a read
  hold that is let go before the work runs, and take the write lock only to publish. A copy is
  published only over the environment it was copied from: the environment counts its changes
  (`handlers/shared_env.rs`), and when it changed meanwhile the copy is dropped and the work runs
  again on a copy of the current environment, inside the same timeout. No accepted change is
  overwritten, and readers wait for nothing but the swap. The writers that publish a whole
  environment (`loadEnvironment` in either mode, `importModule`) take turns, so two of them never
  compute on the same environment. The verify family's set-up takes no turn, and counts a change
  only when it adds something (an environment with the prelude already sends no writer round
  again).
- `importModule` takes a `timeout_ms` (ten times the default without one) and loads on the pool
  under its deadline; at the deadline it answers `-32004` and imports nothing. Reading and
  registering the modules does not stop at the deadline, so a load past it can run to its end in
  its slot, and what it loaded is dropped (closed the same day: "The server's residuals after the
  writers", below).

`handlers/tests/concurrent_writers.rs` reproduces each item with real requests. Every test fails on
origin/main `d693e7d88`, whose clean-server is `cb6f601fd`'s, and passes with the fix:
- `add_decls_to_different_sessions_do_not_wait_for_each_other`: the quick `addDecl` was answered
  after the slow one's check.
- `add_decls_queued_on_their_session_hold_no_work_slot`: with one `addDecl` checking and another
  queued on its session in a two-slot pool, a `check` of `Type` waited for a slot until the first
  one finished.
- `load_environment_merge_checks_while_the_environment_is_read`: the test holds a read of the
  environment. The old merge waited for the write lock before checking anything, holding its slot,
  and answered `-32004` at its 60 s timeout. The new one checks, gives its slot back, waits only to
  publish, and publishes once the read ends.
- `import_module_keeps_a_change_made_during_its_load`: the module is a named pipe, so the load
  waits in the middle until the test writes it. Meanwhile `verifyFile` seeds the logical prelude.
  The old import overwrote `True`; the new one loads again onto the changed environment.
- `import_module_answers_its_timeout_and_imports_nothing`: the old import was not answered within
  the hang detector.

`handlers/shared_env_tests.rs` pins the revision rules. `no_request_work_panics_at_a_short_deadline`
sweeps `importModule` too, with no caught panic.

Still open: `proofState.openObligation` refuses as "not a type or proposition" a goal whose type is
`Prop` reached through a `Nat.rec` fold over a literal of 65,536 or more. Probed on `d693e7d88`
with `Nat.rec (fun _ => Type) … (fun _ ih => ih) n`, nested twice:
- At n = 60,000 the obligation opens after 2.9 s.
- At 70,000, 80,000 and 100,000 it is refused in about 3 ms.
- At 70,000 the kernel's `whnf` leaves the type stuck even with no heartbeat limit, in 39 µs, and
  the heartbeat is not spent.

The cause is not the heartbeat. It is `TypeChecker::native_closed_fold_grind_stuck`
(`crates/clean-kernel/src/tc/reduction/nat.rs`, `CLOSED_FOLD_GRIND_STUCK_THRESHOLD = 1 << 16`). It
leaves stuck any closed, constant-motive `Nat.rec` fold whose step uses its induction hypothesis
and whose count is a literal of 2^16 or more, which is the guard against Θ(count) unary grinds.
That is a sound narrowing: the refusal is not a wrong verdict. Every later kernel check of such a
goal sees the same stuck term, so opening it would only move the refusal. A fix changes what the
kernel reduces, which is a `clean-kernel` change and needs the pin train, so it is left open here.

**The server's residuals after the writers, fixed** (2026-10-16). R34's landing and its two
reviews left the first two items open, the older "Not fixed" paragraph above the third, and an
audit of what still ran on the runtime's threads found the fourth; `docs/DECISIONS.md` R36 records
the choices. Measured in debug test builds on the
shared machine, with the pinned toolchain's `Init` (v4.30.0-rc2) and `Init.Core`:
- `importModule`'s load reads its deadline. Reading, decoding and converting the modules reached
  no tick site, so a load past its deadline ran to its end in its work slot after the request
  had answered `-32004`. `clean-olean`'s loaders now read the caller's deadline
  (`import/deadline.rs`): the clock before each module is read, decoded or registered (a
  `run_until` nested with no deadline of its own resets the kernel's poll countdown, so the poll
  after it reads the clock), the kernel's poll before each declaration is converted, and they
  stop with `ImportError::Interrupted`. A module enters the server's module cache only from a
  decode that finished with the deadline not passed. An `Init.Core` import with `timeout_ms: 300`
  answered `-32004` at 0.30 s and its slot came back at 0.330 s, where on the base it came back
  at 0.733 s, when its load had ended; an `Init` import's slot came back at 0.313 s, where the
  whole load it cut (63,366 constants) takes 789 s in this build, and held the slot as long.
- Freeing an environment walks every constant it holds, and the environment a publish or a
  replace let go, a stale copy and a cancelled writer's copy were freed on a runtime worker. They
  are freed on Tokio's blocking pool now (`handlers/off_runtime.rs`; the work pool was not used:
  a free has no deadline, answer or timeout, a slot taken by one would make requests wait behind
  it, and the writers bound how many there are). Dropping `Init.Core`'s environment takes 5 ms,
  `Init`'s 0.12 s.
- Work with no bound of its own ran on the runtime's threads with no timeout: the certificate
  codec methods (bounded only by the codec's limits, a million expanded nodes and 512 MiB
  decompressed), `saveEnvironment` (0.12 s for `Init.Core`, 104 s for `Init`),
  `getEnvironment` with `include_json` (over the logical prelude and `Init`, 64,090 constants, it
  had built over 27 GB of JSON on one thread after 20 minutes, when the probe was stopped) and the
  two proof-state searches, which first copied the whole environment there. They take a
  `timeout_ms` and run on the pool; the searches' scans of the environment stop at the deadline.
- Proof states: every read of a cached state copied it, environment and all, on the runtime under
  the cache's one lock (9 ms per read and 6 ms to drop the copy at `Init.Core`'s size on the
  base, growing with the environment); reads share the state now, and `applyTactic` copies what
  it changes on the pool. `proofState.openObligation` rendered its `llm` snapshot on the runtime
  after its work, and an unsolved state's `getProofState` stayed there (R32's review): that
  snapshot selects premises from every theorem of the environment (about 30 ms at `Init`'s size)
  and scans an installed Mathverse corpus. `openObligation` finds those in its pool work, and
  `getProofState` takes a slot when its snapshot searches as well as when it checks a proof;
  `full` and `compact` snapshots with no corpus installed still take none.
- The review's probes that pin R34's rules are landed (`handlers/tests/writer_turns.rs`), each
  failing under the revert it names (below). Not landed: the randomly interleaved multi-writer
  probe, which passed with the revision check removed.

The tests, each run against origin/main `e2fa3dbaf`'s `clean-server` and `clean-olean` sources:
`request_bounds.rs`'s `import_module_stops_its_load_at_its_deadline` (the named pipes order the
load; the base load opened the second pipe and kept its slot to the hang detector),
`load_environment_replace_frees_the_old_environment_off_the_runtime`,
`unbounded_methods_wait_for_a_work_slot_inside_their_timeout` (the base answered all eleven
methods with the pool's only slot held), `reading_a_cached_proof_state_copies_no_environment`
(three reads made three more holders of the environment's source) and
`closing_a_proof_state_frees_its_environment_off_the_runtime`; `shared_env_tests.rs`'s four
frees (replace, publish, stale copy, cancelled copy); `request_work.rs`'s
`get_proof_state_takes_a_work_slot_only_to_check_or_search` (the base answered the `llm`
snapshot with the slot held). All ten fail on the base and pass with the fix. A gated constant
source (`free_gate.rs`) makes a free last until the test releases it, so a free on the test's
one-thread runtime is one the test can never release. `clean-olean`'s
`a_load_past_its_deadline_reads_nothing_and_caches_nothing` (the base load returned with all
three modules read, decoded and cached) and `the_recursive_loader_stops_at_its_deadline` fail with
the loaders' reads removed, and so does the server's import test;
`a_load_cut_anywhere_leaves_the_cache_holding_whole_modules` sweeps 25 cuts over a 24-module
chain and requires a load from what each cut left to register what a fresh load does (with the
reads removed it fails too: no load is cut). Each `writer_turns.rs` test fails under the revert
its doc names, run one at a time: a publish that ignores the revision fails
`a_merge_keeps_a_seed_made_while_it_merges`; a seed that always counts a change fails
`repeated_verify_file_set_up_counts_one_change`; `importModule` with no timeout fails
`writers_waiting_for_their_turn_answer_their_timeout`; the merge holding the write lock while it
works fails `a_merge_cancelled_while_it_waits_to_publish_publishes_nothing`; the import's turn
held by its work fails `a_cancelled_import_lets_the_turn_go_and_publishes_nothing`; an `addDecl`
taking its slot before its session fails `cancelled_add_decls_leave_nothing_held`; one letting
its session go while it checks fails `same_session_add_decls_are_checked_in_arrival_order`.

**The review of the residuals, fixed** (2026-10-16). Two reviews of the fix above (a
concurrency lens and an API lens) refuted three of its claims and found more of the same class.
`docs/DECISIONS.md` R36 records the choices:
- A failed `applyTactic` dropped the copy of the proof state its tactic ran on, a whole
  environment, on the runtime; the review's probe over the prelude plus 200,000 axioms measured
  the runtime stalled 67-69 ms per failed tactic, against 2.3 ms for one that succeeded. A state
  refused at the lifecycle limit was dropped inside `ProofStateCache::insert_child`, under the
  cache's write lock (47-70 ms). Both are freed off the runtime now.
- A request cancelled after its work sent its answer, before it took it, dropped the answer with
  the channel on the runtime: a writer's copy (the review's reproducer blocked the runtime to its
  hang detector), and as well any proof state, new state or batch's children in an answer. The
  work pool's answer channel frees an answer nobody took off the runtime, for every method at once.
- A save past its timeout held the environment for reading while it wrote its file, so a writer
  queued behind it waited for the write and, the lock being write-preferring, the readers behind
  the writer answered `-32004` (the review's save to a pipe nobody read). The save lets its hold go
  once it has encoded, and gets ten times the server's default timeout, as `loadEnvironment` does.
- Closing a session (`ServerState::drop_session`) and the session copy an `addDecl` replaced or
  left were freed on the runtime; they are freed off it. `applyTactic`'s trust-policy refusal
  scanned an installed Mathverse corpus on the runtime while holding an unused work slot; it
  scans in that slot.
- WebSocket messages were read up to 64 MiB (frames 16 MiB), not the 10 MiB given above; both
  transports bound a request at 10 MiB now.
- States `applyTactic` caches kept the checker caches their tactic built; its job lets them go
  on the pool. `batchApplyTactic`'s children still keep theirs (see below).
- Pinned: the searches stop at their deadline, and premise selection asserts in debug builds that
  it runs on no runtime thread. Two timing premises are gone from the tests.

The tests, each failing on the code before the review's fixes and passing with them:
`runtime_frees.rs`'s `a_failed_tactic_frees_its_copy_off_the_runtime`,
`a_state_refused_at_the_lifecycle_limit_is_freed_off_the_runtime`,
`add_decl_frees_what_it_lets_go_off_the_runtime`, `closing_a_session_frees_it_off_the_runtime`
and `a_save_past_its_timeout_keeps_no_writer_or_reader_waiting`; `work_tests.rs`'s
`an_answer_its_request_never_took_is_freed_off_the_runtime`; `shared_env_tests.rs`'s
`a_copy_cancelled_after_its_work_answered_is_freed_off_the_runtime`; and `websocket.rs`'s
`test_websocket_message_past_the_line_limit_is_refused`. `runtime_frees.rs`'s
`the_searches_stop_at_their_deadline` fails with either scan's deadline poll removed, and the
`openObligation` tests panic with its premise selection moved back to the runtime.

Still open (2026-10-17: every item after the transport's is closed, "R36's residuals, closed",
below): the certificate verifier's reduction has no fuel of its own (`clean-kernel`'s
`cert/reduction.rs`: a pin train); work that reads no deadline (the codec's, the encodings, a
save's write, MePo's scoring of premises) runs to its end in its slot after its answer, and such
work that reads the environment (a save's encoding, `getEnvironment`'s JSON, MePo's scoring) keeps
its read hold to its end, so a writer queued meanwhile waits for it and readers queued behind that
writer can answer their timeout errors; the transport reads each request (at most 10 MiB) and
writes each answer on the runtime, and a codec method's answer is as large as what it decoded;
`verifyFile`, `fillSorries` and `composeProof` parse their file on the runtime;
`applyTactic`'s refusal at the lifecycle limit scans an installed Mathverse corpus on the runtime
(its slot went to the tactic, and it holds the environment); a proof state the cache lets go
while a request still holds it is freed where that request lets it go, and so is a session
closed while an `addDecl` holds it (the `addDecl`'s share is the last, and goes on the
runtime when its handler ends); `batchApplyTactic` caches each child with the checker caches
its tactic built (memory only: nothing reads a cached state's checker caches); and
`ServerState::create_session` and `addDecl` (reached only from Rust) copy a session's environment
on the runtime; and a save's write is not atomic, so a retried save and the first one still
writing can interleave in one file.

**R36's residuals, closed** (2026-10-17). The open list above, all but its first three items, is
closed in `clean-server`; `clean-kernel` is unchanged. `docs/DECISIONS.md` R87 records the
choices:
- `verifyFile`, `fillSorries` and `composeProof` parsed their file on the runtime, with no
  deadline, before any of their work took a slot. They parse it on the work pool now, in a slot of
  their own, under the request's deadline and inside its timeout (`verify::parse_on_pool`). The
  parse reads the deadline: the kernel's poll before each line it scans for holes, and the clock
  before each `theorem` or `lemma` line, each of which searches the rest of the file. The hole scan
  had stripped a line's comments again for each candidate, and searched every token to the line's
  end for each one; it strips each line once and searches each token forward once now. An
  exhaustive comparison with the old scan, over every line of up to four of 19 pieces that decide a
  hole (137,560 lines), finds the same holes. This lane's audit found one more parse on the
  runtime: `composeProof` answers a failed set-up of the environment with the holes left in the
  proof it was sent, which parses the proof. It does that on the pool too. The parse asserts in
  debug builds that it runs on no runtime thread.
- `applyTactic`'s refusal at the lifecycle limit scanned an installed Mathverse corpus on the
  runtime: its slot had gone with the tactic's work, and it held the environment. It lets the
  environment go and finds the candidates in a slot of its own; with no corpus it takes none. The
  corpus scan asserts in debug builds that it runs on no runtime thread.
  `MathverseProvider::is_loaded` took the library's lock, which a scan holds while it runs, so a
  request deciding whether to take a slot for a scan waited for another request's scan; it reads a
  flag fixed when the provider is built, and the lock's poison (which takes no lock). A scan its
  deadline cuts answers `-32004`, and one no work thread could run an internal error: new answers
  for this refusal, which records the refused attempt only for an answer that names it
  (`attempt_id`), so neither records one (2026-10-19; recorded first, it was a failure-cache row
  no client could look up).
- A proof state the cache let go while a request held it, and a session closed while an `addDecl`
  held it, were freed where that request let go, on the runtime. Both are held as
  `off_runtime::Shared` now, whose last holder frees the value off the runtime wherever it lets
  go.
- `ServerState::create_session` copied the environment on the runtime, under a read hold, and
  `addDecl` copied its session there, holding the session's lock. Both copy on the pool, in its lock
  order. `create_session` returns an error when no work thread can run the copy; its callers are
  Rust only. It waits for a slot and the environment with no bound of its own.
- `verifyFile`, `fillSorries` and `composeProof` set the environment up (the logical prelude,
  where it is missing) on the runtime, holding its write lock, and the kernel adds each inductive
  transactionally, copying the whole environment and freeing the copy: four of each for an
  environment without that prelude, 0.84 to 1.53 s in a debug build (review of 2026-10-19). They
  seed on the pool now (`SharedEnv::seed`), in a slot of their own, still uncharged to their
  timeout. `seed_verify_file_env` asserts in debug builds that it runs on no runtime thread.
- `verifyFile`'s answers that list the file's holes were built on the runtime: 10 MiB of `sorry`
  lines answer 1,747,619 holes, 91.5 MB. They are built on the pool now (the transport still
  writes them on the runtime).
- `batchApplyTactic` cached each child with the checker caches its tactic built. They go on the
  batch's pool now, as `applyTactic`'s do. No test pins this: nothing outside `clean-elab` can see a
  goal's checker caches, and they only cost memory.
- A save truncated its file and then wrote it, so a save cut short (the process killed, a full
  disk, the file-size limit) left a torn file, and a save whose request had answered `-32004`
  still replaced the file. It writes a temporary file beside the target, created with the old
  file's permissions, flushes it, renames it over the target and flushes the directory
  (`handlers/save_file.rs`). It reads the deadline before it writes and before it renames, and
  the save and its request decide once whether it commits (`save_file::Commit`): the timeout
  error means the file is as it was, success that it was replaced (or created where nothing was).
  A file the server may not
  write is refused, as before; the directory must be writable now. Pipes and devices are written
  in place, as before. A symbolic link is followed, link by link, to the path the last one names
  (a relative link's contents joined to its directory's real path), and the file there is
  replaced or created the same way; the links stay links. A link to nothing
  had been written in place (2026-10-19). A path that can name no new file (ending in `/`, `.` or
  `..`, or empty) is refused by `fs::write`, as before, writing nothing.
- Each handler's log span formatted its request's parameters with `Debug` on the runtime, and
  every log line inside the span repeated them. The CLI's default `fmt` subscriber enables those
  spans. They record no parameters now; the file methods record `content_bytes`.

The tests, each run against origin/main `9cced250a`'s `clean-server` sources, ported to its API
(`create_session` returns a `SessionId` there, and the parse-deadline test runs the whole parse),
with the fix's two debug-build detectors added. `runtime_residuals.rs`: the file methods' test and
`compose_proof_answers_a_failed_set_up_from_the_pool` panic on the runtime parse;
`the_file_parse_stops_at_its_deadline` finds the theorem and its hole past the deadline; the
proof-state and session frees wait for the gated free to the hang detector, which then finds it
on the runtime's thread. `runtime_frees.rs`'s `sessions_are_copied_off_the_runtime`: opening a
session made both of its copies on the runtime's thread. `save_file.rs`: under a 64-block
file-size limit the save answered `File too large` and left a torn file (65,536 of the
encoding's 1,242,262 bytes), and a save whose request answered `-32004` replaced the file. Two
tests there pass on the base, as they must: the save run with no limit, and the one that keeps
links and permissions. `is_loaded_never_waits_for_a_scan` waits out its hang detector, and
`tests/corpus_scans.rs` panics on the refusal's scan on the runtime. That is nine of nine failing
in the library and one of one in `corpus_scans`. The composeProof test fails at its set-up path
too, run against this change with only that path reverted: the set-up's answer parses on the
runtime. `the_hole_scan_finds_what_it_found_before` compares the new scan with a copy of the old
one, so it has no base run. With the change, every one of them passes in a full `clean-server`
run (719 library tests then, 733 at 2026-10-19's reviewed tip, 734 at its landing; `corpus_scans`, `api_surface`,
`ay_contract_ratchet` and the doc-test), and `targo tippy -p clean-server --all-targets -- -D
warnings` reports nothing.

The review of the save (2026-10-18) found its answer and its file could disagree, and three
changes to what a save does that nothing recorded; each is fixed or recorded in R87, and pinned in
`save_file.rs`. Its probes, against the real handler: 12 of 186 saves swept across their deadline
answered `-32004` and replaced the file (the save read the deadline before it renamed, but the
request's timer was its own); a read-only file was replaced (`fs::write` refused it at its open);
a 250-byte name was refused (the temporary name repeated it whole, past the 255-byte limit); a
writable file in a read-only directory was refused (recorded, not changed: the temporary file must
be created there). Also: the temporary file was created with the default mode, so an owner-only
file's new contents were readable by others while the save wrote. The tests pause a save at one of
its steps (`save_file::seam`) and fire a request timer of their own (`admin::save_until`).
`a_save_whose_request_stopped_waiting_before_it_committed_never_renames` and
`a_save_that_began_replacing_its_file_is_answered_by_its_outcome` fail with the commit decision
reverted to the old one (the request answers `-32004` when its timer fires, and the save renames
whatever its request answered): the first finds the file replaced, the second answers `-32004`.
`a_save_refuses_a_file_the_server_may_not_write_as_fs_write_did`,
`a_save_of_a_name_at_the_limit_gets_a_temporary_file` and
`a_save_creates_its_new_file_no_more_readable_than_the_old` fail with their own fix reverted;
`a_save_in_a_directory_it_may_not_write_is_refused_with_the_reason` pins the recorded refusal.
`mathverse_provider.rs`'s `a_poisoned_library_is_not_loaded` fails with the poison check
removed.

The reviews of 2026-10-19 (server-concurrency and server-api, of `5409138cd`) found a save
through a symbolic link that names nothing outside all of that: it went to `fs::write` before
either deadline read and took no commit, so it answered `-32004` and then created the file (6 of
6 trials), and a write cut short left that file torn (8 of 30 SIGKILLs). They also found that the
name test above passed with its fix reverted on APFS, whose limit is 255 characters, not bytes
(83 three-byte characters are 249 bytes but 83 characters), so the sentence above was not true
of it there. Each fix of that round, reverted on its own in the 2026-10-19 tip (`ddfbc9453`), fails
its test: the link to nothing written in place again fails
`a_save_through_a_link_to_nothing_whose_request_timed_out_creates_nothing` (the file created) and,
under the file-size limit, `a_save_cut_short_leaves_the_old_file_whole` (the linked file torn); the
name cut reverted fails `a_save_of_a_name_at_the_limit_gets_a_temporary_file` ("File name too
long": its name is 252 bytes and 250 characters now, and the test first checks that a temporary
name repeating it whole is too long on the file system it runs on); the first deadline read
removed fails `a_save_past_its_deadline_creates_no_file` (the temporary file created), the second
`a_save_whose_deadline_passed_while_it_wrote_never_commits` (the file replaced; `seam::expire`
makes the deadline pass while the save writes); sending paths that name no new file to the
temporary file again fails `a_save_of_a_path_that_names_no_new_file_writes_nothing`; seeding on the
runtime fails `the_file_methods_set_the_environment_up_off_the_runtime` on the debug-build
assertion, and with the assertion removed too on its count (4 of 4 copies made on the runtime's
thread); building `verifyFile`'s hole list on the runtime trips `holes_response`'s assertion. The
lifecycle refusal's attempt record on a timeout has no test: it needs an installed corpus, which
only `tests/corpus_scans.rs`'s process has, a scan the deadline cuts, and a look at the
proof-state cache, which is private to the crate.

The re-checks of that round (2026-10-19, of `8461cc13a`) found one thing the link fix broke, safe
but wrong: it joined each relative link's contents to the link's directory as written, so every
link of a chain lengthened the path, and a chain the system opens (30 links, each in a directory
with a 60-byte name) was refused as `File name too long` at the 14th, where `realpath(3)`, which
the save used before that fix for a path that exists, follows it (read from `/bin/realpath`, not
run through the server before the fix). Each link's contents are joined to its directory's real
path now (the directory exists: the link is in it).
`a_save_through_a_long_chain_of_relative_links_replaces_the_file_at_its_end` (24 links in
200-byte directories, past macOS's and Linux's path limits that way) fails with the join as
written put back: refused as `File name too long` at the 5th link, while the other 16 save tests
pass. The 32-link limit counts the links a save follows itself, at the end of each path it
reaches; the system also counts those in the directories, so near the limit a chain it refuses
may be followed (one of 25 layouts in the re-check, reached through `/var`). Answer and file
agree either way.

Still open, each with its reason:
- The certificate verifier's reduction has no fuel of its own. Its code is `clean-kernel`'s
  (`cert/reduction.rs`), so the fuel waits for a pin train.
- Work that reads no deadline still runs to its end in its slot after its answer: the codec's,
  the encodings (a save's encoding, and its write once the write has started) and MePo's
  scoring. Such work that reads the environment keeps its read hold to its end. A deadline read
  there would go inside a library that offers none (serde, bincode, the codec).
- The transport reads each request and writes each answer on the runtime. A request is at most
  10 MiB, and the work is linear in it. A release probe over the lock's `serde_json` 1.0.150, with
  a request line of 11.3 MB (a little over the limit), measured the line's parse at 8.3 ms and
  11.4 ms (medians of seven runs, at load 12 and 30 on 18 CPUs) and an answer of that size's
  encoding at 5.1 ms and 7.2 ms. A span's `Debug` of the parameters took 9.6 ms and 13.3 ms; that no
  longer runs. A request must be read before the server knows which method it names and whether
  that method takes a work slot, so reading it in a slot would make the bounded methods, which
  take none, wait behind long work.
- The three file methods' set-up of the environment, and its waits for a slot and the write lock,
  are not charged to their timeout (they answered up to 0.87 s past it under a storm of writers,
  debug build, 2026-10-19). It is bounded by the fixed prelude it adds, times the copies of the
  environment the kernel makes to add it.
- An answer is not bounded by its request: the 91.5 MB `verifyFile` answer above took 1.89 s to
  encode on a debug build's runtime thread. The transport writes every answer there.

**Regression, the review's fix-forward** (2026-10-14: `evaluate`'s charges and its `match`, the
linear combinations' charge, the deadline, and `bfun_elim`'s walk stopping at binders that rebind
every variable; release probes of `6a7aff128`, of origin/main `c87881afb` before these changes,
and of the result, each mirroring the adapter's parse, define-fun retry and check). All 5,441
trust-cg certificates keep their verdicts against both: 5,428 verified, and 13 refused at the same
`bitblast_ashr` steps with the same messages; no run was capped, and peak memory moved by at most
6 MB either way. Check times followed the shared machine's load (summed: 434 s, 275 s and 357 s).
The soundness battery at `--mutants 200 --seed 11 --threads 1` checks the same 605,934 instances
with the same 221,570 parse errors and no panic on `c87881afb` and on the result, its per-rule
report identical line for line, with no counterexample. The vendored workspace tests (release) and
clean-auto's `--features carcara-verify,ay-bv-blast --lib` tests (2,487) pass; `targo tippy`
reports on the vendored workspace exactly the lints it reported on `c87881afb`, and nothing with
`-D warnings` on clean-auto, clean-elab (with `carcara-verify`, with `ay-smt` alone, and with
default features), clean-server, clean-cli and clean-kernel.

### Terms nest at most 2^18 deep (`parser/{mod,error}.rs`; Clean's adapter checks on a 1 GiB stack)

The parser recurses once per term or sort written inside another, and the checker's rules and the
substitutions recurse once per level of the terms they walk (the free-variable sets did too, until
they were computed with a stack of their own: "Free-variable sets share structure"). Clean's
adapter ran all of it on its caller's thread: 8 MiB on a process's main thread (`clean cert
verify-external`), 2 MiB on a worker (`verify-external-batch`'s rayon pool). A deep term overflows
that stack, which ends the process. Measured with a release probe that paints a large stack and
reads back how much of it a check used:

| Input | Stack it took | Size |
|---|---|---|
| `(not (not ... p))` written 3,700 deep in a `hole` step | 8.1 MiB, past a main thread's 8 MiB | 22 KB |
| the same 10,000 deep, in a `refl` step | 22 MiB | 120 KB |
| `poly_simp` of `g_20000`, `g_j = (+ 1 g_(j-1))` defined in the proof | 20 MiB | 780 KB |
| 100,000 `define-sort`s, `S_j = (Array S_(j-1) Bool)` (freeing the sort) | 9.2 MiB | 4.3 MB |

A sweep of every rule `get_rule` dispatches on, over steps whose terms are 2,000 deep (built by
definitions, so the parser does not recurse) in 24 shapes (Boolean connectives, arithmetic,
bit-vectors, binders, `let`, applications, strings, arrays), with and without premises and
arguments, found every shape walked by some rule at 0.9 to 1.4 KiB of stack per level (the most:
`ac_simp` over `exists` and `let` chains, `poly_simp` over products); the parser takes 2.3 KiB per
level written.

So the parser now bounds both, as it reads (`parse_term`, `parse_application`, `parse_sort`):

- `MAX_WRITTEN_NESTING` = 16,384 terms or sorts written inside each other
  (`ParserError::WrittenTooDeep`). Every trust-cg certificate is written less than 80 deep.
- `MAX_TERM_DEPTH` = 2^18 = 262,144 levels of a term or a sort, as written or as built from
  definitions, `:named` terms and `define-sort`s (`ParserError::TooDeep`). The parser records the
  depth of each term and sort it returns, from its children's (read before it), and walks a
  definition's expansion once, without recursion. The deepest trust-cg certificate is 8,585 deep
  (the circuit of a 64-bit division); a division of the widest operands the expansion budget admits
  (255 bits) is about 136,000 deep, so no step within the budget needs a deeper term.

Clean's adapter (`carcara_verify.rs`, `CHECKER_STACK_BYTES`) checks on a thread of its own with a
1 GiB stack: at the rates above a release build needs about 37 MiB to read the deepest written
term and about 365 MiB to walk the deepest built one (an unoptimized build several times that).
Only the pages a check touches are committed. A term within the limits is read and checked
exactly as before; a deeper one is refused. Each check running reserves the 1 GiB of address
space, and one of its steps may use up to about 600 MB, so concurrent checks multiply both: on a
host that does not overcommit (Linux `vm.overcommit_memory = 2`) a reservation that cannot be made
refuses its certificate (fail closed, but a legitimate one too). Since a review of
`7006ac377..6a7aff128` (2026-10-14) the adapter runs at most one check per available core at once
(`CheckerSlots`); the others wait their turn, until their deadline if they have one, and the
server's batch handler caps a request's `threads` at the cores. Terms the checker builds itself can be deeper (a
bit-blasted carry chain of a `w`-bit addition is about `2w`, `nary_elim`'s expansion of `n`
arguments `n`). A rule compares such a term with the conclusion it read by pointer, or by a walk
the conclusion's depth bounds; `Display` writes at most 64 levels of it, and `Term`'s drop frees
it without recursion. Building one must not recurse per level either: `nary_elim` did, below.

**`nary_elim`** (2026-10-14). Upstream's `expand_assoc` built the expansion of an n-ary `=>`,
`+`, `-` or `*` recursively, a frame per argument ("if the argument list if very long, this may
overflow the stack", its comment said): `(=> p ... p)` of 7,000,000 arguments, a 14 MB proof that
nothing earlier refuses, took 1.2 GiB of stack, past the adapter's 1 GiB (about 176 bytes an
argument). The expansion is now a fold that adds the same terms to the pool in the same order,
innermost first, so the rule checks it at no stack depth. And since the expansion of `n`
arguments is at least `n` deep, while the parser reads no conclusion deeper than
`MAX_TERM_DEPTH`, a list of more than 2^18 arguments is refused before its terms are built
(upstream built them, and then failed the comparison): the same step is
now refused at 138 MB (the parsed proof) in 0.9 s, and one of 1,000,000 at 24 MB, where upstream
built its expansion (474 MB) before failing the comparison; one of 262,143 arguments against its
spelled-out expansion is accepted, as it was.

**Measured** (release probe; the adapter's thread): the four inputs above are checked at 13 to
49 MB peak; `(not ... p)` written 100,000 deep is refused at 43 MB; `poly_simp` of a 100,000-deep
sum is checked, its walk taking 98 MiB of the checker's stack (the expansion budget refused it
before its charges were in words, after the same walk). The 5,441 trust-cg certificates keep their verdicts; recording depths adds 1.9%
to 3.5% to the instructions of five of the costliest and at most 6 MB to their peak memory. The
soundness battery (`--mutants 200 --seed 11 --threads 1`) on this tree, given origin/main's seeds,
reports origin/main's 605,470 instances, 221,108 parse errors and per-rule counts line for line,
with no panic and no counterexample; given this tree's seeds (four more `aci_simp` cases) it
checks 605,934 instances, with no counterexample.

**Tests.** `tests/problem_reading.rs` (`nesting_and_depth_are_bounded`): a term and a sort written
16,384 deep are read and 16,385 refused; a term and a sort built 2^18 deep by definitions are read
and one more level refused. `diagnostics.rs` (clean-auto): a `refl` step over a term written
10,000 deep and a `poly_simp` step over a sum built 20,000 deep are checked (on the caller's
thread, each overflowed it), a term written 100,000 deep is refused with the limit named, and
`TooDeep` prints its limit. `resource_budget.rs`
(`nary_elim_expands_without_recursion_and_refuses_what_no_conclusion_can_be`): 200,001 arguments
are judged on a 1 MiB stack, and 2^18 + 1 are refused with the limit named; `tests/rules`'
`nary_elim` cases keep upstream's verdicts.

**Fixed since (2026-10-15).** Found while measuring the above: a chain of terms over distinct
constants, `e_j = (bvadd c_j e_(j-1))`, cost memory quadratic in its length whenever the pool was
asked for the free variables of its end, by three routes (10,000 links, 1.75 GB). The pool's sets now
share structure; see "Free-variable sets share structure", below.

### Free-variable sets share structure (`ast/pool/{free_vars,mod,advanced}.rs`, `ast/substitution.rs`, `parser/mod.rs`, `utils.rs`, `checker/scoping.rs`, `checker/rules/{arrays,extras,pb_blasting,quantifier,strings,subproof}.rs`)

The pool cached, for each term it was asked about and each subterm its computation reached, an
`IndexSet` of the term's free variables, copied from its subterms' sets, and handed each caller a
copy. A chain of terms over distinct constants, `e_j = (bvadd c_j e_(j-1))`, made those sets hold
`n^2 / 2` entries: 10,000 links (876 KB with the declarations) took 1.75 GB by each of three routes,
the links named in the problem at top level (`check_named_term_is_closed` asks for the free
variables of each `:named` term), the same inside one `exists` (the parser's capture check of each
use of a name), and the links defined in the proof and read once by a `qnt_rm_unused` step; 40,000
links ran past 4 GB within 17 s.

A set is now a `FreeVars`, a persistent big-endian Patricia trie (Okasaki and Gill, "Fast Mergeable
Integer Maps", 1998): a term's set is its children's merged, and a merge copies only the paths on
which they differ, so the chain's sets share all but a path each, of at most 128 nodes (20,000
links take fewer than 40 nodes a link, `a_chains_sets_share_structure`). A variable's key is the
hash of its name in the high 64 bits and the address of its term in the low 64, and the leaf holds
the term, so the address is not reused while the set exists: two keys are equal exactly when the
variables are the same allocation, the identity the pool's terms compare by, and the variables of
one name lie under one prefix. The pool computes the sets with a stack of its own rather than a
recursion per level, caches the terms upstream's recursion cached, and adds to the pool the bound
variables upstream's added: the proof printer decides what to share by how many references a term
has (`Rc::strong_count`), and each cache entry holds one.

What the callers read, at the 22 calls of `free_vars`:

| Call site | What it reads | Where the set's order showed |
|---|---|---|
| `bind`, `qnt_rm_unused`, `qnt_cnf`'s last check, `miniscope_split`, `miniscope_ite` | whether a bound variable is free | nowhere |
| `onepoint` (two), `bind_let`, `qnt_cnf`'s prenexing, `re_unfold_neg`, `pbblast`'s `z`, `arrays_ext`'s fresh name | whether a variable of a given name is free | nowhere (the fresh name depends on membership alone) |
| `Substitution` (four): its cache, `should_be_renamed`, `rename_binding_list` | whether the mapped variable is free in a cached term; the names of the free variables of the terms it maps to and of a binder's body, for membership | nowhere |
| the printer's `is_closed` | whether every free variable is global | nowhere |
| `beta_equiv` | whether a variable named like a remaining binder is free in an argument | the message's variable |
| the anchor scoping checks and `check_not_exported` (`scoping.rs`, `subproof.rs`) | whether a variable of a bound or assigned name is free | the message's variable, read off a `HashSet` in an order that changed from run to run |
| `check_named_term_is_closed`, `expand_macro` | the free variables whose names are bound locally | the message's variable; the order of the placeholders, which no substitution reads |

`should_be_renamed`, which upstream filled with the names of the free variables of every term the
substitution maps to, is now those terms' sets merged, beside the names it maps; nothing but
membership was ever read from it. A substitution's result does not depend on the order of its map:
it looks terms up in it, and its renaming reads `should_be_renamed` by membership. So no verdict,
built term or fresh name depends on the order in which a set lists its variables, and a `FreeVars`
has no deterministic order. The four messages that name one variable among several that offend now
name `first_free_var`'s choice: the first offending variable in a walk that reads a term's children
in the order upstream's sets listed them (a function before its arguments, a `let`'s body before
its values, a `match`'s scrutinee before its cases). That is upstream's choice whenever one variable
offends, and differs from it only where removing a binder's variable (`swap_remove`) had permuted
upstream's set; the anchor scoping checks' choice no longer changes from run to run.

The parser's capture checks also looked up, at every named term and every use of a definition, each
free variable of the term in every scope: a chain of 10,000 named links inside an `exists` that
binds 10,000 variables took 9.1 s at 1.76 GB on base, and 11.7 s with the shared sets alone, each
lookup now chasing a trie's pointers. `Parser::locally_bound_free_vars` keeps, for each scope, the
answers computed while the symbol table is at one generation (`HashMapStack::generation`: inserting
an entry or pushing a scope gives the table a number it never had, and popping a scope gives back
the number it had before the push, since it then holds what it held then), and answers an
application from its children's when each is a variable, a constant or a term already answered: its
free variables are the union of theirs, and the names bound locally are the same for all of them.
Any other term is answered from its free variables, by looking the local names up in its set or its
variables up in the scopes, whichever is fewer lookups. Tests and unoptimized builds check every
answer against the uncached one. (Until the lane's review the generation changed with every pop as
well, so a `let` beside each link emptied the cache at every link: 10,000 links took 4.95 s and
20,000 26.4 s, base 7.17 s at 1,766 MB and past 4 GB; it now takes 0.048 s and 0.115 s.)

`beta_equiv` reads, for each argument with free variables, whichever is shorter: the argument's
free variables, each looked up among the remaining binders' names, or those names, each looked up
in the argument's set. Looking every remaining binder's name up in every argument's set cost the
arguments times the remaining binders, where base read each argument's free variables (none for a
numeral): a `lambda` over 40,000 `Int`s applied to 20,000 numerals (878 KB) took 4.0 s, base
0.57 s, which its check that no remaining binder shadows an applied one spent comparing every pair.
Both checks now look names up in a set: 0.036 s.

Why it is sound. The sets hold exactly upstream's variables: they are computed by upstream's
recursion over the same children, with a merge for `extend` and a removal for `swap_remove`, and both
act on the set's members alone; membership answers by allocation, as upstream's `IndexSet<Rc<Term>>`
did, and a variable's name is read from the term the set holds. Each caller reads the same
membership, so each check accepts and refuses exactly what it did; only which of several offending
variables a refusal's message names can differ. The parser's cache answers what the uncached
computation answers, since a generation fixes the names bound locally and an application's free
variables are its children's.

Measured (release probe built like the adapter: its parse, `define-fun` retry and check on a
1 GiB thread; three interleaved runs, medians, and peak RSS), base / new:

| Input | Size | Base | New |
|---|---|---|---|
| links named at top level: 2,500, 5,000, 10,000 | 216, 436, 876 KB | 0.19 s 130 MB, 0.87 s 470 MB, 3.70 s 1,761 MB | 0.009 s 10 MB, 0.021 s 18 MB, 0.045 s 32 MB |
| the same inside one `exists` | 193, 391, 786 KB | 0.35 s 130 MB, 1.44 s 469 MB, 6.27 s 1,763 MB | 0.012 s 10 MB, 0.020 s 17 MB, 0.045 s 32 MB |
| defined in the proof, read by `qnt_rm_unused` | 221, 446, 896 KB | 0.23 s 128 MB, 0.85 s 467 MB, 3.54 s 1,752 MB | 0.009 s 9 MB, 0.018 s 14 MB, 0.039 s 26 MB |
| the three at 40,000 links | 3.3 to 3.7 MB | killed at a 4 GB cap after 9.1 to 16.4 s | 0.23 to 0.27 s, 98 to 124 MB |
| the three at 100,000 links | 8.3 to 9.4 MB | not run | 0.58 to 0.75 s, 237 to 293 MB |
| 5,000 and 10,000 links named inside an `exists` of as many variables | 455, 915 KB | 2.13 s 472 MB, 9.06 s 1,761 MB | 0.028 s 18 MB, 0.054 s 33 MB |

All are accepted, on base where it finished and here.

**Tests.** `ast/pool/free_vars.rs`: `the_trie_is_a_persistent_map` (20,000 random insertions, removals,
merges and intersection tests on keys that agree in their high or their low 64 bits, against a
`BTreeMap`, each version unchanged by the operations on it), `free_variable_sets_hold_upstreams_variables`
(upstream's `free_vars` kept in the test; on 300 batches of random terms over names in several
sorts, a sort variable among them, with shared subterms, applications, binders of every kind that
bind a name twice or shadow one, `let`s and `match`es, 49,200 sets hold upstream's variables, answer
membership of every variable and every name as upstream's do, and have their sizes; and
`first_free_var` chooses as a naive walk does, upstream's first candidate in 37,010 of 38,035
choices, every other one with several candidates under a binder, `let` or `match`),
`layered_pools_compute_upstreams_sets` (the parallel checker's `ContextPool` and `LocalPool`) and
`a_chains_sets_share_structure` (20,000 links, the trie nodes allocated checked every 100 links
against 40 a link: with merges that copy their operands rather than share them it fails at the
100th link, with 24,607 nodes, where it used to run past 4 GB before its one check at the end).
`parser/tests.rs`: `capture_checks_answer_from_their_cache_as_without_it` (800 random problems read
with definitions as premises and as macros, 226 read and 574 refused for a capture, each answer of
the cache checked against the uncached one; with the cache's union of an application's arguments
cut to the first, it fails) and `capture_checks_keep_their_answers_across_a_scope_entered_and_left`
(500 links with a `let` beside each, at most 2 answered from their free variables; 498 when a pop
renumbers the table). `utils.rs`: `a_generation_names_the_stacks_contents` (20,000 random pushes,
pops and insertions: a generation read twice reads the same scopes, and a change never keeps one;
it fails if a pop restores any other number). `tests/free_variables.rs` checks the verdicts end to
end at sizes the quadratic code also finished: `chains_of_links_are_checked_by_each_route` (2,000
links by each route) and `chains_of_links_still_refuse_what_they_mention` (a link that mentions a
bound variable, and a `qnt_rm_unused` step removing a variable the chain mentions, refused by base
and by this tree). (It checked 40,000 links by each route, which a regression would have answered
by taking some 28 GB of a shared machine rather than by failing.) `test_free_vars` (`ast/tests.rs`)
reads the new sets.

**Regression** (2026-10-15: these sets, the parser's cache, and `bfun_elim`'s walk over levels named
apart, "Nested quantifiers named apart"; release probes of origin/main `40ea22d1c` and of the result,
each mirroring the adapter's parse, `define-fun` retry and check). All 5,441 trust-cg certificates
keep their verdicts and their messages against base: 5,428 verified, and 13 refused at the same
`bitblast_ashr` steps; no run was capped, and a certificate's peak memory moved by at most 3.8 MB up
and 12.4 MB down. Check times followed the shared machine's load (summed: 333 s on base, 650 s here
at a load average near 60); checked interleaved, best of three, the eight costliest took within 4%
of base's either way (3.1 to 4.4 s). The soundness battery at
`--mutants 200 --seed 11 --threads 1` checks the same 605,934 instances with the same 221,570 parse
errors and no panic on both, its 189 per-rule rows identical line for line, with no counterexample
(only its list of the ten slowest instances differs). The vendored workspace tests (release) pass,
459 and a doc test (base: 450), and so do clean-auto's `--features carcara-verify,ay-bv-blast --lib`
tests (2,487). `targo tippy` reports on the vendored workspace base's 33 lints less the five that
left with the code they flagged (four in upstream's `free_vars`, one closure in
`rename_binding_list`), and nothing new; `targo fmt --check` is clean.

**Regression after the review** (2026-10-15: the fuel, the parser's cache per scope, `beta_equiv`'s
lookups and `la_mult`'s refusal, on the tree merged with origin/main `80f09a7e9`, whose vendored
Carcara is `40ea22d1c`'s; release probes of each, mirroring the adapter's parse, `define-fun` retry
and check). All 5,441 trust-cg certificates keep their verdicts and messages against base: 5,428
verified, and 13 refused at the same `bitblast_ashr` steps; no run was capped, and a certificate's
peak memory moved by at most 2.5 MB up and 15.5 MB down. The soundness battery at
`--mutants 200 --seed 11 --threads 1` on base's seeds checks the same 605,934 instances with the
same 221,570 parse errors and no panic as base, its 189 per-rule rows identical; on this tree's seeds (two more,
from `beta_equiv_capture`), base and this tree check the same 606,427 instances with 222,144 parse
errors and no panic, rows identical. In Clean's dialect at `--seed 77 --threads 1` both check
605,198 instances with 221,643 parse errors, rows identical, and base's one panic (`la_mult_pos` on
`(cl x y)`) is gone. The vendored workspace tests (release) pass, 464 and a doc test, and so do
clean-auto's `--features carcara-verify,ay-bv-blast --lib` tests (2,487). `targo tippy` reports on the
vendored workspace base's 33 lints less the same five, and nothing new; `targo fmt --check` is
clean, and so are the ledger and the source inventory.

**The lane's review** (2026-10-15) found the sets' cost in `bfun_elim` ("Nested quantifiers named
apart"), the parser's cache emptied by every scope change, `beta_equiv`'s lookups, tests that could
detect a regression only by exhausting memory, and a `la_mult_pos` panic that base has too
("Malformed steps are refused, not a panic"); each is fixed above, and the paragraph below is
corrected. It also recorded, for whoever compares two trees' battery reports or messages: some of
base's messages differ from run to run (two runs of base at seed 5 differ in 105 messages:
`onepoint`'s "expected binding list in left-hand side to be ...", read off a `HashSet` union, and
the `cp_addition`, `cp_division`, `cp_multiplication` and `cp_saturation` messages; the premise and
anchor scoping messages did too until this lane), so an A/B comparison has to treat those as
noise; with `--threads` above 1 the battery's per-rule totals drift between runs of one tree (a
mutant's seed includes its thread's index, and each thread dedupes on its own), so only
`--threads 1` reports compare line by line; and `expand_macro` sorts its capture candidates by
name, so two of one name and different sorts keep an order that depends on their addresses, which
reaches only the placeholders' map, whose order no substitution reads.

**Round 2: merges remembered, answers carried into scopes pushed inside, the parse under the
deadline** (2026-10-16, on origin/main `f1d72b1fb`). What this section left open, fixed:

1. *Two chains merged at every link.* A merge copies the paths on which its operands differ, so two
sets that share no structure cost a merge linear in their size. Over distinct constants, `p_j =
(bvadd c_j p_(j-1))`, `q_j = (bvmul d_j q_(j-1))` and `r_j = (bvor p_j q_j)`, each `r_j`'s set was
new and held `2j` variables, so memory was quadratic too: 10,000 links took 4.7 GB, named at top
level, inside an `exists`, or defined in the proof and read by `qnt_rm_unused`. Over the same
constants (`q_j = (bvmul c_j q_(j-1))`) the two sets are equal but built apart, and each merge
visited them whole: quadratic time. Each thread now remembers the merges of free-variable tries it
computed (`Merges`, `ast/pool/free_vars.rs`): for two branches that hold at least 32 keys together,
the result, by the addresses of the two operands. `r_j`'s merge meets, off the two paths `c_j` and
`d_j` changed, the pairs of subtrees `r_(j-1)`'s merge met, and takes their results, so a link costs
a few paths of the trie and some 32 keys' worth of merging on each (about 110 trie nodes a link).
An entry holds its operands and its result weakly, so it keeps no trie alive; a weak reference
keeps its allocation (only the contents are dropped), so an address an entry holds is not reused
while the entry exists, and an entry is found only for the nodes it was made for. Once the table
holds twice the entries its last sweep left (and at least 4,096), the entries with a dead node are
dropped; and it holds at most one entry for every 8 trie nodes that live on its thread (or 4,096
entries), past which it is emptied (item 5, added after the review of this round). A thread's table
outlives the pools it served until it is swept or emptied, or the thread ends; Clean's adapter
checks each certificate on a thread of its own. `bfun_elim`'s name sets
(`Trie<()>`, one step's, metered by their fuel) remember nothing, so their fuel runs out where it
did; theirs are the only metered merges, so no metered merge is ever looked up or remembered.

   This section named interning the trie's nodes, so that equal sets are one allocation. That would
make the second shape's merges constant, but not the first's, whose sets are new; the remembered
merges make both linear, so no node is interned. The threshold of 32 keys is a trade: a merge of
fewer keys is computed each time, which a link pays on each path it changed, and each entry costs
the merges that no remembered result serves. On two chains over distinct constants whose links are
merged in a random pairing and read by one `qnt_rm_unused` step (quadratic on base and here, "Not
fixed" below; five runs interleaved, before the table had a bound), remembering every merge of 8
keys or more took 0.55 s at 464 MB for 2,500 links and 2.20 s at 1,795 MB for 5,000, where 32 took
0.39 s at 378 MB and 1.56 s at 1,383 MB, no table 0.34 s at 376 MB and 1.50 s at 1,488 MB, and base
0.34 s at 377 MB and 1.42 s at 1,489 MB. The threshold did not keep the table small where sets over
the same constants are merged in many pairs: there it took up to seven times base's memory (item
5).

2. *The capture checks ask the pool only for the sets they look in.* `check_named_term_is_closed`
asked the pool for the free variables of every named term, and `expand_macro` for the body of every
definition used inside a local scope, so that the pool cached them as before this section's sets.
They now ask only where `locally_bound_free_vars` looks in a set, and `first_free_var` runs only
when a capture is found, to name it. Where no local scope binds a name (outside every binder, or in
the parameter scope of a `define-fun` without parameters) nothing is bound locally and nothing is
asked, so two chains named at top level compute no set, merged in any order or pairing. Inside a
scope an application is answered from its children's answers, and the links' names, bound nowhere,
make each answer empty, so the merged links inside one `exists` compute none either. Which sets the
pool caches changes no set it computes. The cache's only other reader is the proof printer's sharing
heuristic, which counts a term's references (`Rc::strong_count`) where it writes a proof or an
SMT-LIB problem with sharing (`print_proof`, `write_proof_to_dest`, `generate_lia_smt_instances`,
and the external solvers of `lia_generic` and `sat_refutation`), none of which Clean calls.

3. *Links each under binders of their own.* Inside an `exists` of 10,000 variables, `(exists ((u
Bool)) (and u link))` around each link read each link in a scope entered for it alone, where no
answer was kept, so each was answered from its free variables: quadratic time. An answer of
`locally_bound_free_vars` is now kept with the state of the scopes it was computed in, a chain of
`ScopeState`s, one per depth, each holding the symbol table's generation for its scopes up to that
depth (`HashMapStack::generation_at`: the table's generation for its innermost scope, and for any
other the generation the table had when the scope inside it was pushed, which it keeps while that
scope is on the table). Two equal generations at a depth read the same scopes up to it and the same
generations at every depth below. An answer answers again wherever the table's scopes up to some
depth are in the state it recorded: its own depth, or, for an answer that holds no variable, a
depth below it, found by walking its chain outward at most 64 depths (fewer names are bound there,
so it holds none either). Up to that depth the same names are bound, and the names the scopes
pushed inside it since bind are looked up in the term's free variables, unless they outnumber what
answering from the free variables would look up. So a link read in a sibling scope answers the
next link from the wide `exists` they share, with `u` looked up; a link in two binders of its own
costs two depths; a link one binder deeper than the last answers from the scope it is nested in.
`HashMapStack::inner_len` is kept as entries come and go instead of summed over the scopes at each
call.

4. *The deadline interrupts parsing* ("The parse stops at the deadline", in "The checker stops at a
deadline" above).

5. *The table's bound, and the parser's answers swept* (added after the review of this round, the
same day). The table had no bound but its sweep, which drops only entries with a dead node, and an
entry lives as long as the tries it was made from, which the pool caches. Where sets are merged in
many pairs that recur little, the table became most of the memory and grew faster than the tries
did, where base's merges allocated nothing. Two chains over the same constants, `p_j = (bvadd c_j
p_(j-1))` and `q_j = (bvmul c_j q_(j-1))`, merged in random pairs with the superset first and
folded, `s_i = (bvand s_(i-1) (bvor p_k q_m))` with `k >= m`, and read by one `qnt_rm_unused`
step (the review's `twinsup_qnt`): at 20,000 links the table held 3.74 million entries for 0.54
million live trie nodes, and the check took 739 MB against base's 101 MB; at 40,000, 1,484 MB
against 202 MB (the review counted 10.8 million entries there, none dropped by 12 sweeps, against
1.17 million trie nodes allocated, the entries growing about 2.9 times for each doubling of the
links). The same pairs each named inside a binder inside a binder (`twinsup_bind`), so that the
parser's capture checks reach the pool: 489 MB against 176 MB at 20,000. Merged in an unordered
random pairing (`twinperm_qnt`, quadratic in memory on base too), the table saved no time and took
two thirds more memory: 2,258 MB against 1,365 MB at 10,000 links.

   Now each trie node counts itself in a count of its thread's when it is allocated and out when
it is dropped (`live_nodes`; a node dropped on a thread other than its own counts out there, where
the count stops at zero, which only loosens the first thread's bound and tightens the second's),
and the table holds at most one entry for every 8 live nodes (`LIVE_NODES_PER_ENTRY`), or 4,096 if
that is more: past that it is replaced by an empty table, so its memory goes too. An entry takes
about as much memory as a node, so the table takes about an eighth of what its tries take. A merge
an emptied table no longer holds is computed again, and gives the same trie. Two chains merged at
every link reuse mostly the last few links' entries, so they pay little for the bound: read by
`qnt_rm_unused` at 40,000 links, without a bound they kept 0.37 entries a live node over distinct
constants and 0.71 over the same ones, and with it they take the same time at less memory (below).
Where the entries serve much, as in `twinsup`, the bound gives back the time they saved. The
divisor trades the two (an instrumented build, medians of three runs interleaved): on
`twinsup_qnt` at 20,000 links one entry for every 8, 16 and 32 nodes took 11.0, 12.8 and 14.3 s at
104, 102 and 101 MB (no bound 1.4 s at 745 MB); on `twinperm_qnt` at 10,000, 3.3, 3.4 and 3.4 s at
1,489, 1,380 and 1,348 MB (no bound 2.8 s at 2,258 MB); the chains merged at every link took the
same time at each. 8 keeps `twinsup` at about base's time.

   The parser's answers had no bound either: an answer of `locally_bound_free_vars` was kept for
the whole parse with the scopes it was computed in, where base dropped a scope's answers when the
scope went (a resource the review noted, not a soundness one). Once the answers are twice as many
as the last sweep left (and at least 4,096), those that answer nowhere now are dropped
(`answering_depth`, which `carried_answer` reads too): a depth whose state changed, by a name bound
there or its scope left, never has that state again, since the symbol table gives each change a
generation it never had, so they would never answer again. The answers then grow with the scopes
the parser is in, as base's caches did.

Why it is sound. A remembered merge is the merge of the same two nodes, and a trie never changes,
so a merge that finds it returns what computing it would: a trie with the same keys, so the same
shape and the same order of values (a Patricia trie's shape is a function of its keys, and a key
names one variable). Only the identity of its branch nodes can differ, which nothing but the table
and the merges' shortcuts reads. Asking the pool for fewer sets changes no set it computes, only
which it caches. A carried answer is the answer computed in scopes whose names up to a depth are
the table's now, joined with the variables of each name bound in the scopes pushed inside it since,
which is the definition of the answer here; an empty answer stays empty at a depth below its own.
An emptied table of merges or a swept answer is only computed again. Tests and unoptimized builds
still check every answer against the one computed from the term's free variables alone. So every capture check accepts and refuses what it did and names the
variable it named, and every caller of `free_vars` reads the same membership in the same order.

Measured (release probes built like the adapter: its parse, `define-fun` retry and check on a
1 GiB thread; base origin/main `f1d72b1fb`; medians of three runs interleaved, and peak RSS, at a
load average of 8 to 35 on the shared machine; a run past 6 GB or 60 s was killed, by SIGKILL),
base / new, new before the table's bound (item 5; the chains below cost the same time with it, at
the same or less memory, as the next table shows):

| Input | Size | Base | New |
|---|---|---|---|
| two chains over distinct constants merged at every link, named at top level: 5,000, 10,000, 20,000 links | 0.9, 1.8, 3.7 MB | 1.02 s 1,185 MB, 4.75 s 4,665 MB, killed at 6 GB after 3.0 s | 0.034 s 24 MB, 0.068 s 45 MB, 0.127 s 84 MB |
| the same inside one `exists` | 0.9, 1.7, 3.6 MB | 0.68 s 1,181 MB, 3.74 s 4,663 MB, killed after 2.3 s | 0.027 s 23 MB, 0.059 s 48 MB, 0.146 s 92 MB |
| the same defined in the proof, read by `qnt_rm_unused` | 1.2, 2.5, 5.0 MB | 0.91 s 1,183 MB, 3.36 s 4,662 MB, killed after 3.3 s | 0.074 s 73 MB, 0.155 s 144 MB, 0.360 s 287 MB |
| the same, each link in an `exists` of its own inside an `exists` of as many variables | 1.1, 2.1, 4.4 MB | 2.64 s 1,185 MB, 16.7 s 4,668 MB, killed after 19.3 s | 0.041 s 36 MB, 0.094 s 67 MB, 0.197 s 136 MB |
| two chains over the same constants, named at top level: 10,000, 20,000 | 1.5, 3.1 MB | 0.62 s 53 MB, 2.37 s 102 MB | 0.052 s 34 MB, 0.101 s 64 MB |
| the same read by `qnt_rm_unused` | 2.1, 4.4 MB | 0.49 s 49 MB, 2.34 s 103 MB | 0.094 s 64 MB, 0.203 s 130 MB |
| 10,000 links merged in a random order, named at top level: over distinct, over the same constants | 2.1, 1.7 MB | 3.17 s 4,661 MB, 0.64 s 62 MB | 0.059 s 44 MB, 0.056 s 39 MB |
| 5,000 and 10,000 links merged in a random pairing, named at top level | 1.0, 2.1 MB | 0.65 s 1,025 MB, 2.83 s 4,026 MB | 0.030 s 23 MB, 0.060 s 44 MB |
| one chain, each link in an `exists` of its own inside an `exists` of as many variables: 10,000, 20,000 | 1.2, 2.4 MB | 3.50 s 35 MB, 19.0 s 71 MB | 0.046 s 36 MB, 0.108 s 69 MB |
| the same, each link in two binders of its own | 1.4, 2.9 MB | 3.88 s 45 MB, 18.5 s 88 MB | 0.058 s 45 MB, 0.123 s 91 MB |
| one chain, each link one binder deeper than the last: 2,500, 5,000, 8,000 | 0.3, 0.6, 0.9 MB | 0.18 s, 0.81 s, 2.34 s (26 to 75 MB) | 0.064 s, 0.236 s, 0.603 s (26 to 73 MB) |
| one chain of 20,000 links named at top level, inside one `exists`, inside an `exists` of 20,000 variables | 1.8, 1.6, 1.9 MB | 0.075 s 59 MB, 0.079 s 58 MB, 0.089 s 60 MB | 0.050 s 38 MB, 0.055 s 39 MB, 0.061 s 42 MB |

All are accepted, on base where it finished and here. Two chains over the same constants merged
at every link and read by `qnt_rm_unused` took about a quarter more memory than base before the
bound (the table's entries; base's merges allocate nothing there), and take what base takes with it
(below). A link one binder deeper than the last still costs what the symbol table's lookups cost
("Not fixed", below).

With the bound (item 5; the same probes, base `f1d72b1fb`, before the bound `cf8051d16`, medians of
three runs interleaved, at a load average of 30 to 40; base at 40,000 links one run):

| Input | Size | Base | Before the bound | With it |
|---|---|---|---|---|
| `twinsup_qnt` (above): 5,000, 10,000, 20,000, 40,000 links | 1.1, 2.1, 4.4, 8.8 MB | 0.33 s 26 MB, 1.92 s 49 MB, 9.48 s 101 MB, 41.4 s 202 MB | 0.14 s 64 MB, 0.36 s 207 MB, 1.08 s 739 MB, 2.94 s 1,484 MB | 0.36 s 27 MB, 1.99 s 53 MB, 8.61 s 104 MB, 37.5 s 205 MB |
| `twinsup_bind` (above): 10,000, 20,000, 40,000 | 2.3, 4.7, 9.5 MB | 1.12 s 87 MB, 4.17 s 176 MB, 32.2 s 360 MB | 0.37 s 245 MB, 1.06 s 489 MB, 3.70 s 1,646 MB | 1.06 s 106 MB, 4.28 s 209 MB, 27.8 s 426 MB |
| `twinperm_qnt` (above): 5,000, 10,000 | 1.1, 2.1 MB | 0.61 s 344 MB, 2.55 s 1,365 MB | 0.68 s 579 MB, 3.13 s 2,258 MB | 0.74 s 389 MB, 3.10 s 1,490 MB |
| two chains over distinct constants merged in a random pairing, read by `qnt_rm_unused`: 5,000 | 1.2 MB | 1.74 s 1,489 MB | 1.77 s 1,385 MB | 1.51 s 893 MB |
| two chains merged at every link, read by `qnt_rm_unused`, over distinct constants: 20,000, 40,000 | 5.0, 10.2 MB | killed at 6 GB after 3.2 s | 0.41 s 287 MB, 0.91 s 587 MB | 0.43 s 252 MB, 0.86 s 512 MB |
| the same over the same constants | 4.4, 8.8 MB | 2.64 s 103 MB at 20,000 | 0.25 s 132 MB, 0.49 s 259 MB | 0.25 s 104 MB, 0.45 s 198 MB |

The other shapes of the first table, measured again at 20,000 links (and 40,000 for the links in
binders of their own; the chain one binder deeper than the last at 10,000, which both refuse past
`MAX_WRITTEN_NESTING`), take the same time and memory before the bound and with it, within 0.01 s
and 2 MB; the rest are accepted on both. Two chains over distinct constants merged in a random
pairing take less memory with the bounded table than before the bound and than base (893 MB
against 1,385 and 1,489 MB at 5,000 links).

**Tests.** `ast/pool/free_vars.rs`: `two_chains_merged_at_every_link_cost_a_few_paths_a_link`
(20,000 links of tries over distinct keys and over the same keys, the merges' visits and
allocations checked every 100 links against 4,000 and 200 units a link, also with every link's sets
kept, so that the table is emptied at its bound as the tries grow; the same merges of tries whose
values remember nothing fail it within the first 1,000 links),
`remembered_merges_stay_within_the_tries_they_serve` (item 5: the `twinsup` shape over tries of
4,000 keys, every set kept; the table holds at most one entry for every 8 nodes of the live tries,
or 4,096, counted every 250 merges; without the bound it fails at the 250th, with 54,603 entries
for 90,813 nodes),
`a_pools_sets_of_two_chains_merged_at_every_link_share_structure` (the pool's sets of 20,000 merged
links, at most 200 trie nodes a link; ported onto base it fails at the 300th link, with 72,356
nodes), `remembered_merges_keep_no_trie_alive` (a remembered result dies with its operands, and
2,000 rounds of merges that die leave at most 8,192 entries),
`wide_sets_hold_upstreams_variables_through_remembered_merges` (upstream's `free_vars`, kept in the
test, as the oracle: on 30 batches, two chains of 150 links merged in order, over the same
variables and in a random pairing, and random terms built on them with binders, `let`s and
`match`es that bind their names; every set holds upstream's variables, by membership, name and
size, and `first_free_var` chooses as the documented walk does: 34,260 sets and 26,559 choices,
served by some 16,000 merges found remembered, in pools made one after another on one thread, so that
the table holds entries of tries that died; with the table keyed by one operand it fails, and so
do the two chains' tests and the persistent map's), and `the_trie_is_a_persistent_map` (against a
`BTreeMap`, for tries that remember their merges and tries that do not). `parser/tests.rs`:
`capture_checks_carry_their_answers_into_scopes_entered_inside` (500 links each in one or two
binders of their own inside a wide `exists`, or each one binder deeper than the last: at most 2
answered from their free variables; ported onto base it fails, 498 of 500 so answered),
`an_answer_holding_a_variable_answers_only_in_its_own_scopes`,
`capture_checks_drop_the_answers_of_scopes_left` (item 5: 10,000 named terms, each in a `forall`
of its own, leave at most 4,096 answers; without the sweep all 10,000 are kept), and
`capture_checks_answer_from_their_cache_as_without_it` (now 800 random problems with binders of one
or two names, terms reused in scopes nested inside and beside the ones they were answered in, each
read with definitions as premises and as macros: 304 readings accepted and 1,296 refused for a
capture, every answer checked against the uncached one; it passes on base too); the deadline's
tests are above. `utils.rs`: `a_generation_names_the_stacks_contents` also checks `generation_at` (a
generation read at a depth twice reads the same scopes up to it and the same generations below) and
`inner_len`. `tests/free_variables.rs`: `chains_merged_at_every_link_are_checked_by_each_route`
(2,000 links, over distinct and over the same constants, named at top level, inside an `exists`,
each in an `exists` of its own inside a wide one, each one binder deeper, and read by
`qnt_rm_unused`) and `chains_merged_at_every_link_still_refuse_what_they_mention` (a link that
mentions its own binder's variable, and a `qnt_rm_unused` step removing a variable the second chain
mentions, both refused, as on base).

**Regression** (2026-10-16, before the bound of item 5: release probes of origin/main `f1d72b1fb`
and of `cf8051d16`, each mirroring the adapter's parse, `define-fun` retry and check). All 5,441 trust-cg certificates keep
their verdicts and messages against base: 5,428 verified, and 13 refused at the same
`bitblast_ashr` steps; no run was capped, and a certificate's peak memory moved by at most 2.4 MB
up and 9.5 MB down. Check times followed the shared machine's load (a load average of 25 to 40;
summed, 327 s on base and 349 s here); checked interleaved, best of three, the eight costliest took
16.9 s on base and 17.1 s here in all, each within the runs' spread. The soundness battery at
`--mutants 200 --seed 11 --threads 1` checks the same 606,427 instances with the same 222,144 parse
errors and no panic on both, its 190 per-rule rows identical line for line, with no counterexample.
The vendored workspace tests (release) pass, 480 and a doc test, and so do clean-auto's `--features
carcara-verify,ay-bv-blast --lib` tests (2,489). `targo tippy` reports on the vendored workspace
exactly base's lints, and nothing on clean-auto (`--all-targets`, those features, `-D warnings`);
`targo fmt --check` is clean, and so are the ledger and the source inventory.

With the bound and the answers' sweep (item 5; a release probe of this tree): the 5,441
certificates keep their verdicts and messages against base and against `cf8051d16` (5,428
verified, 13 refused at the same `bitblast_ashr` steps), no run was capped, and a certificate's
peak memory moved by 3.5 MB up and 7.2 MB down at most against base. The battery checks the same
606,427 instances with the same 222,144 parse errors and no panic, its 190 per-rule rows identical
to base's, with no counterexample. The vendored workspace tests (release) pass, 482 and a doc test,
and so do clean-auto's (2,489). `targo tippy` reports on the vendored workspace exactly base's
lints; `targo fmt --check` is clean.

**Not fixed.** Two chains whose links are merged in a random pairing (`r_k = (bvor p_k q_(s(k)))`)
and read by one step that asks for a term's free variables (`qnt_rm_unused`, or any rule that reads
a set) still cost quadratic time and memory, as on base: over distinct constants 1.51 s and 893 MB
at 5,000 links (base 1.74 s and 1,489 MB); over the same constants, unordered (`twinperm_qnt`),
3.10 s and 1,490 MB at 10,000 (base 2.55 s and 1,365 MB): each `r_k`'s set is new and shares little
with the others, and the pool caches a set for every subterm it reaches. Bounding it would need the
pool to answer membership without building a set for every subterm it reaches. The same pairings
named in the problem compute no set (item 2). Over the same constants with the superset first
(`twinsup`), the time stays quadratic as on base, at about base's memory (item 5); the remembered
merges made it linear before the bound, at up to seven times base's memory, which a larger table
would buy back. A link one binder deeper than the last costs the symbol table's lookups of each
global through every scope (upstream's `HashMapStack::get`), quadratic in the depth, which
`MAX_WRITTEN_NESTING` bounds: 8,000 links 0.60 s; the deadline interrupts it. `collect_binders`
(choice terms, read by `sat_refutation` and the external tools only, which Clean's adapter does not
configure) still caches an `IndexSet` per term. Unoptimized builds still compute every capture
check's answer from the term's free variables too, to check it. A chain of scope states
(`ScopeState`) is dropped recursively, one frame for each scope it nests, and anchors nest in a proof
without the parser recursing, so only their number bounds it: the review read 100,000 nested anchors
with a `define-fun` at the bottom, whose capture check builds a chain of 100,001 states, on the
adapter's 1 GiB thread, to the same term graph as base (base 62.3 s, here 33.7 s, both about
182 MB); base already drops nested subproofs recursively, so this adds no new failure, and deeper
nests are bounded in practice by the symbol table's lookups and the deadline. A thread's table of
merges keeps the entries of the pools it served until it is swept or emptied (at most one for every
8 live trie nodes), so a library caller checking many proofs on one long-lived thread holds that
much until then; Clean's adapter checks each on a thread of its own.

### Soundness fixes (1-41)

Every defect below made upstream d62d45cf accept a step whose conclusion is
false in some model where its premises hold, except fixes 36 to 40, which are
about the problem. Fixes 36 to 38 and 40 are parser defects: the problem was
read with premises other than the script's, so a complete refutation of those
premises certified a satisfiable script. Fix 39 is not a misreading: it
refuses a construct whose SMT-LIB reading, an axiom that need not be
consistent, a producer reads differently. Each fix checks the missing side
condition, computes the correct term or reads the script as SMT-LIB does (or
refuses it); none of them trusts the producer.

| # | Rule(s) | Root cause | Fix | Files |
|---|---|---|---|---|
| 1 | `bitblast_udiv`, `bitblast_urem` | `ripple_carry_adder` returned the carry *into* the top bit instead of the carry out, and the remainder took `true` where it needed the difference `r - y` | Return the carry out; keep `r - y` when `r >= y` (the cvc5 circuit) | `checker/rules/bitvectors.rs` |
| 2 | `bitblast_ashr` | A shift by at least the width filled with `false` | Fill with the sign bit, as SMT-LIB `bvashr` requires | `checker/rules/bitvectors.rs` |
| 3 | `aci_simp` | Duplicates were removed for every associative operator | Remove duplicates only for idempotent operators: `and`, `or`, `bvand`, `bvor` | `checker/rules/simplification.rs` |
| 4 | `div_simplify` | `t / t = 1` and `(div t t) = 1` were accepted for a symbolic `t`, which fails at `t = 0` (division by zero is unspecified) | Accept `t / t` only for a nonzero numeral | `checker/rules/simplification.rs` |
| 5 | `beta_equiv` | On a partial application, an argument could be captured by a remaining binder; an applied binder shadowed by a remaining one was substituted anyway; too many arguments panicked | Refuse capture and shadowing; refuse extra arguments | `checker/rules/extras.rs` |
| 6 | `evaluate` | `as_signed_bitvec` returned the magnitude, so every signed operator had the wrong sign; `bvsub` used it; `bvsmod` used a wrong formula; `extract` dropped the top bit; `rotate_left` underflowed; `div`/`mod` truncated instead of Euclidean division; division by zero panicked; `bvashr` by at least the width aborted the process (GMP overflow); shifts by huge amounts allocated huge integers | Two's complement signed values; `bvsub` modulo `2^w`; `bvsmod` as floor division; `extract` keeps `i + 1` bits; rotations modulo the width; Euclidean `div`/`mod`; no value for division by zero; shifts at or above the width computed directly; no `unwrap` on indices | `ast/evaluate.rs` |
| 7 | `la_tautology` and every other user of `as_fraction` | `(div a b)` on constants was read as the rational `a/b`; a zero denominator panicked | Euclidean integer quotient for `div`; no constant for a zero denominator | `ast/term.rs` |
| 8 | `arrays_ext` | The choice witness was always named `x`, capturing a free `x` of the arrays | Pick a name free in both arrays and compare modulo renaming of bound variables | `checker/rules/arrays.rs`, `checker/rules/mod.rs` |
| 9 | `la_generic`, `bounded_farkas` | Integer strengthening (`s > d` into `s >= floor(d) + 1`) was applied to `Real` atoms and depended on whether `d * a` was an integer; a strict literal multiplied by zero kept the sum strict | Strengthen only when every atom is `Int`, rounding to the lattice of the scaled coefficients; a zero multiplier contributes nothing; a sum is strict when any strict literal takes part (this last change restores upstream's own `Real` tests, which had passed only through the unsound strengthening) | `checker/rules/linear_arithmetic.rs`, `elaborator/local/farkas.rs` |
| 10 | `assume`, `refl`, `ite_intro`, `subproof` and every rule that compares terms with `polyeq`/`alpha_equiv` | Under n-ary sugar, `(- a)` was taken to be `a`; a division literal ignored arguments beyond two, panicked on a zero denominator, and mixed up the negated forms; alpha-equivalence reused an equality cached outside a binder that rebinds one of its names | Unary `-` is negation; division literals have exactly two arguments and a nonzero denominator; alpha-equivalence reads only the innermost cache scope under binders (since 2026-10-15, an answer found under a binder is reused only while the names it read are bound as they were and no name it read free has been bound since: "Performance: `Polyeq` caches the pairs it finds unequal") | `ast/polyeq.rs` |
| 11 | `bind` | The right-hand bindings were checked against `r - r` (always empty); substituted variables need not be bound on the left, nor their images on the right | Check that each `x := y` renames a bound left variable to a distinct context variable bound on the right, and that all other bindings are the same context variables on both sides | `checker/rules/subproof.rs` |
| 12 | Any rule ending an anchor with arguments | The step ending the subproof is exported to the enclosing proof, but only context rules discharge the context: `subproof` (or `refl`, or any rule) could export a statement proved under `(:= (x U) a)` as if it held for every `x` | Only `bind`, `let`, `onepoint`, `sko_ex`, `sko_forall` or `bind_let` may end an anchor with arguments; `hole` and `lia_generic` are exempt because they already mark the proof holey | `checker/shared.rs` |
| 13 | `bind`, `let`, `onepoint`, `sko_ex`, `sko_forall`, `bind_let`, and every step inside an anchor with arguments | Variables were identified by name only, so a statement crossed the anchor boundary with its names reinterpreted: a step inside the anchor could use a premise in which `x` was the outer `x`; a closing rule could export a term mentioning the constrained `x` (for example `(= (let ((x a)) (P x)) (P x))` from `(= (P x) (P x))` under `(:= (x U) a)`); an assigned value could mention a name that the same or a nested anchor binds; `bind` could rename onto a variable also bound on the left; `bind_let` never looked at its anchor | A premise may not cross an anchor that binds one of its free names; closing rules refuse an exported term mentioning an assigned variable; assigned values may not mention names bound later in the same anchor or by a nested anchor; `let` values may not mention assigned names; `bind` refuses renaming onto a left-bound variable; `bind_let` requires every occurring let variable to be a fixed variable of an anchor without assignments | `checker/scoping.rs` (new), `checker/shared.rs`, `checker/mod.rs`, `checker/rules/subproof.rs`, `checker/rules/extras.rs`, `ast/context.rs` |
| 14 | `onepoint` | The context substitution was applied to a point before matching it, so under `(:= (x U) a)` the point `(= x x)` became `(= x a)`, and `(forall ((x U)) (=> (= x x) (P x)))` was accepted as equal to `(P a)` | A point `(= x t)` eliminates `x` only if `t` mentions neither `x` nor a variable eliminated after it; points are matched in assignment order | `checker/rules/subproof.rs` |
| 15 | `qnt_cnf` | Prenexing moved a universal quantifier out of a disjunction over a free occurrence of its variable | Refuse when a prenexed variable is free in the formula | `checker/rules/quantifier.rs` |
| 16 | `string_decompose` | In the reverse direction the split point was `n` instead of `(str.len t) - n` | Split at `(str.len t) - n` | `checker/rules/strings.rs` |
| 17 | `concat_cprop_prefix`, `concat_cprop_suffix` | The overlap argument was applied to components that are not string constants | Require the head (or tail) word and the middle component to be string constants | `checker/rules/strings.rs` |
| 18 | `cp_literal`, `cp_saturation`, `cp_division` | These rules are only valid for 0/1 valued literals, but accepted any `Int` term | Require every literal to be `((_ @int_of i) bv)` with `i` below the width | `checker/rules/cutting_planes.rs` |
| 19 | `cp_addition`, `cp_multiplication`, `cp_normalize` | A repeated literal overwrote its earlier coefficient; `cp_addition` skipped conclusion literals with coefficient 0; literals were keyed by printed name, so a variable named `~x` was the negation of `x`; `cp_normalize` ignored one side's polarity, read `(- a)` as `a`, and turned `>` into `>= k + 1` over `Real` terms | Accumulate coefficients; compare every literal of both sums; key literals by term and polarity; compare both polarities; unary `-` negates; require `Int` sides | `checker/rules/cutting_planes.rs` |
| 20 | `pbblast_bveq`, `pbblast_bv{u,s}{lt,le,gt,ge}` | A sum with fewer summands than bits was accepted, dropping high bits | Require exactly one summand per bit (per bit but the sign for signed relations) | `checker/rules/pb_blasting.rs` |
| 21 | `pbblast_bvand_ith_bit`, `pbblast_bvxor_ith_bit`, `pbblast_bvand`, `pbblast_bvxor` | The `ith_bit` lemmas accepted arguments that are not 0/1 bits (the choice then has no witness); the choice variable `z` captured a free `z` of the arguments | Require bit arguments (`@int_of` terms or 0/1 numerals) and no free `z` | `checker/rules/pb_blasting.rs` |
| 22 | `drat` | A RAT lemma only preserves satisfiability, yet a `drat` step using one could conclude a non-empty clause, which the rest of the proof then used as a consequence | A step that used a RAT lemma must conclude the empty clause | `drup.rs` |
| 23 | `resolution`, `th_resolution` | The greedy pivot search let a literal cancel its complement inside the same clause, deriving the empty clause from satisfiable premises | A greedy success is confirmed by a bounded, complete propositional entailment check before it is accepted (RUP is unchanged) | `checker/rules/resolution.rs`, `resolution.rs` |
| 24 | `refl`, `assume` and every rule comparing terms with `polyeq`/`alpha_equiv` | `compare_binder` zipped the two binding lists, so a binder was alpha-equivalent to one binding *more* variables: `refl` proved `(= (forall ((x Bool)) (or x y)) (forall ((x Bool) (y Bool)) (or x y)))`, false at `y = true` | Binders are only compared when they bind the same number of variables | `ast/polyeq.rs` |
| 25 | the same rules, on `let` | The same function inserted each binding into the De Bruijn map before comparing the *next* binding's value, reading a `let` value in the binder's own scope. SMT-LIB `let` binds in parallel, so `(let ((x 1) (y x)) y)` compared equal to `(let ((z 1) (y z)) y)`, where the two values are the *outer* `x` and `z` | Every value is compared before any of this list's variables enters the map | `ast/polyeq.rs` |
| 26 | `forall_inst`, `beta_equiv`, `bfun_elim`, `refl` under a `bind` anchor, and every user of `Substitution` | `rename_binding_list` renamed a bound variable to `<name>_renamed` without looking at the body: a free `y_renamed` in the body was captured, so `forall_inst` proved `(or (not (forall ((x Bool)) (forall ((y Bool)) (or x y y_renamed)))) (forall ((z Bool)) (or y z z)))`, false at `y = false, y_renamed = true` | A replacement name must not occur free in the term the renaming is applied to | `ast/substitution.rs` |
| 27 | the same rules, on `let` | `Substitution::apply`'s `Term::Let` arm applied only the internal renaming to the binding values, never the substitution itself, so an instantiated term kept reading an outer variable; and reaching a `let` before any binder panicked on `should_be_renamed.as_ref().unwrap()` | The values are substituted in the enclosing scope (and the renaming deliberately is not applied to them, `let` binding in parallel); `should_be_renamed` is computed in `rename_binding_list` | `ast/substitution.rs` |
| 28 | every check built on free variables — capture avoidance, `check_not_exported`, the anchor scoping checks | `TermPool::free_vars` ignored the *values* of a `let`, so `(let ((y x)) y)` reported no free variable at all; `collect_binders` skipped them too | Free variables of the values are free in the `let`; binders inside a value are collected | `ast/pool/mod.rs` |
| 29 | `onepoint` | `extract_points` descended through nested binders and kept the points it found there, so a `(= x t)` under a binder that *rebinds* `x`, or whose `t` mentions a variable that binder binds, was read as a point for the outer `x`: `(forall ((x Bool)) (=> (exists ((x Bool)) (= x t)) (= x p)))` was accepted as equal to `(=> (exists ((x Bool)) (= x t)) (= t p))` | The enclosing binders are tracked; a point whose variable is shadowed, or whose term mentions a variable bound there, is dropped | `checker/rules/subproof.rs` |
| 30 | `string_decompose` | The premise `(>= (str.len t) n)` bounds `n` only from above. With `n` negative it holds vacuously while the conclusion `(= (str.len w) n)` is false, a length never being negative: `(>= (str.len s) (- 1))` proved `(= (str.len (str.substr s 0 (- 1))) (- 1))` | The split point must be syntactically non-negative (a non-negative numeral, a `str.len`, or a sum or product of such) | `checker/rules/strings.rs` |
| 31 | `re_unfold_neg` | The generated `forall` always bound a variable named `L`, capturing a free `L` of the word or the regular expression | The name is taken from the conclusion and checked not to occur free in either | `checker/rules/strings.rs` |
| 32 | `re_concat_unfold_pos`, `re_kleene_star_unfold_pos` | The Skolem witness naming a component of the decomposition is `(choice ((x String)) (exists ((k_0 String) (R_0 RegLan) (R_1 RegLan)) (and (= t (str.++ k_0 x)) (str.in_re k_0 R_0) (str.in_re x R_1))))`. Both `str.in_re` conjuncts are vacuous — every string is in *some* regular language — so the witness is only constrained to be a factor of `t`, while the conclusion uses it as one particular component of one particular split | Refuse every application that would build such a witness \u2014 `re_unfold_pos_concat` refuses it at the one place it would generate a component, before building it (since 2026-10-14; it used to set a flag there and refuse after building), so the condition is a property of the application, not an inference from the shape of the conclusion. What is left is the case where the premise determines the decomposition outright: every argument of the `re.++` a `(str.to_re s_i)`, whose language is the singleton `{s_1 ++ .. ++ s_n}`, so the conclusion is the plain equality with no witness. `re_kleene_star_unfold_pos` unfolds `(re.* r)` into `(re.++ r (re.* r) r)`, whose middle argument is never a `str.to_re`, so it has no instances left. See the upstream report for the redesign this needs | `checker/rules/strings.rs` |
| 33 | `evaluate` | SMT-LIB `(_ bv<n> <w>)` denotes `n mod 2^w`, but `Value::from_constant` took `n` as written: `(= (_ bv5 2) #b01)` evaluated to `false` and `(bvult #b10 (_ bv5 2))` to `true` | The literal is reduced modulo `2^w` at the parser, so it *is* the term it denotes, and again in `Value::from_constant` (as first committed, the parser half cast `w` to `u32`; fix 35 corrects it) | `parser/mod.rs`, `ast/evaluate.rs` |
| 34 | `refl`, `assume` and every rule comparing terms with `alpha_equiv` | Fix 25 compared a binder's `let` values before their variables entered the De Bruijn map, but after the binder's new *cache* scope was pushed. An equality found for a value holds in the enclosing scope; cached in the binder's scope, the body reused it after the binder had rebound one of its names. `refl` proved `(= (let ((u p)) (let ((u (not u)) (w u)) (or u w))) (let ((v p)) (let ((z (not v)) (w v)) (or v w))))`, false at `p = false`: the pair `(u, v)` was cached while `u` was the outer variable and reused when it was the inner one | The values are compared before either scope is pushed, so everything cached in a binder's scope was derived under that binder's own bindings | `ast/polyeq.rs` |
| 35 | `evaluate`, and every rule reading a `(_ bv<n> <w>)` literal | Bit-vector widths are `usize`, but `Value::new_bitvec` and the `bvadd`-family fold truncated with `keep_bits(w as u32)`, reducing modulo `2^(w mod 2^32)`: `evaluate` proved `(= (= ((_ sign_extend 4294967295) #b1) ((_ sign_extend 4294967295) #b0)) true)` (both read as the width-0 value `0`) and `bvadd` of `1` and `1` at width `2^32 + 1` equal to `0`. Fix 33's parser half made the same cast, so `refl` proved `(= (_ bv5 4294967298) (_ bv1 4294967298))` | `Value::new_bitvec` returns no value for a width above `MAX_EVALUATED_BV_WIDTH` (`2^16`, the bound `int.pow2` already had); every evaluator value passes through it, so each later `u32` cast of a width or bit index is exact, and `repeat` checks its result width before looping. The parser reduces a literal only when `n` has more than `w` significant bits, where `w` is below `n`'s bit count and the cast is exact | `ast/evaluate.rs`, `parser/mod.rs` |
| 36 | every rule, through the premises it is checked against | A function definition (a `define-fun` read as a macro, which Clean's adapter retries when the ordinary reading fails, or a `:named` term, which is a macro in both readings) was expanded as it stood. Where a binder at the use site rebound a name its body mentions, the binder captured it: with `(define-fun k () Int x)`, `(define-fun h ((x Int)) Int k)` defined `h` as the identity instead of the constant `x`, and `(exists ((x Int)) (not (= k x)))` read as `false`. And a definition took precedence over a local binding of its own name, so `(exists ((k Int)) (not (= k 5)))` under `(define-fun k () Int 5)` read the bound `k` as `5` | Hygienic expansion for `define-fun` parameters: where a parameter shadows a global that a macro used in the body mentions, the expansion holds the global under a placeholder, and closing the definition renames that parameter (`x\param`; a backslash is in no lexed symbol, so no script can name it) and restores the global. Any other capture (a quantifier, `lambda`, `choice`, `let` or `match` case; a `define-fun-rec` parameter too, until fix 39 refused the command) is refused while parsing the problem; a proof keeps upstream's reading, since its terms are judged as written. A local binding shadows a definition. A `:named` term in the problem must be closed, and one named inside a `define-fun` body is defined as the global it mentions | `parser/mod.rs`, `parser/error.rs` |
| 37 | every rule, through the premises it is checked against | `parse_problem` ignored `push`, `pop`, `reset` and `reset-assertions`, made every `check-sat-assuming` assumption a permanent premise, kept the assertions after a `check-sat` or `exit`, and skipped every command it did not know: `(assert p) (reset-assertions) (assert (not p))`, `(check-sat-assuming (p)) (assert (not p)) (check-sat)`, `(push 1) (assert (and p (not p))) (pop 1) (check-sat)` and `(assert p) (check-sat-using smt) (assert (not p))` were refuted (AY's `check-sat-using` is a query, like `check-sat`; AY answers `sat`) | A problem is one query: the assertions before its first `check-sat`, `check-sat-assuming` (whose assumptions are added) or `exit`, or every assertion when there is none. `push`, `pop`, `reset` and `reset-assertions` are refused, and so is any command that changes the problem after the query ends; `get-*`, `set-info`, `set-option`, `echo` and `exit` may follow it. Every other command, wherever it appears, is refused: an extension such as `check-sat-using`, `assert-soft`, `define-const`, `declare-var` or `simplify`, a command name written as a quoted symbol, or a command that is not a symbol. The parser cannot tell whether such a command ends the query or changes the assertions | `parser/mod.rs`, `parser/error.rs` |
| 38 | every rule, through the premises it is checked against | Names were not kept apart. A symbol was looked up as a definition, then as a built-in operator, and only then in the symbol table, so a local binding (a `define-fun` parameter, a `let`, quantifier, `lambda`, `choice` or `match` binder, an anchor argument) named like a built-in operator was the built-in inside its own scope: under `(define-fun h ((re.all RegLan)) Bool (str.in_re "a" re.all))` both `(h (str.to_re "a"))` and `(not (h re.none))` read as `(str.in_re "a" re.all)` and its negation, and `(let ((re.all re.none)) (str.in_re s re.all))` as `(str.in_re s re.all)`. Built-in sort names were matched before local sort parameters, so `val` in `(par (Bool) ((mk (val Bool))))` returned `Bool` at every instance, and three `(val _)` of `(Box Int)` constants could not be distinct. A `:named` label, or a `define-fun` read as a macro, took precedence over every symbol of its name, before and after it, a declared constant or a built-in such as `true` included: `(declare-fun x () Int) (assert (= y (! 5 :named x))) (assert (not (= x 5)))` read its last assertion as `(not (= 5 5))`, and `(! false :named true)` turned every later `true` into `false`. A constant declared twice was one `Term::Var`, a global named like a built-in (`(declare-const real.pi Real)`) was the built-in, and a sort declared twice, or named like a built-in sort, was one sort. And an assertion did not have to be a formula | A local binding takes precedence over a built-in operator of the same name, as a term, as the head of an application and in `(as <op> <sort>)`. A local sort parameter takes precedence over a built-in sort of the same name, and takes no arguments (upstream dropped them). In the problem every declared or defined name (`declare-fun`, `declare-const`, `define-fun` in either reading, a `:named` label, a datatype constructor, selector or tester; `define-fun(s)-rec` until fix 39 refused it) must be new: neither a built-in operator nor a name already declared or defined. Same-named datatype symbols keep C2's rule (refused when their argument sorts overlap), so a label or definition named like a selector of other argument sorts stays legal: every use of either is then a sort error, never a misreading. Every declared or defined sort (`declare-sort`, `define-sort`, a datatype) must be new too: neither a built-in sort nor one already declared or defined. An assertion and a `check-sat-assuming` assumption must be formulas (upstream took `(assert 5)`) | `parser/mod.rs`, `parser/datatypes.rs`, `parser/error.rs` |
| 39 | every rule, through the premises it is checked against | Not a misreading. `define-fun-rec` and `define-funs-rec` were read as SMT-LIB defines them, a declaration and a universally quantified equation per function, and that axiom need not be consistent: `(define-fun-rec f ((x Int)) Int (+ (f x) 1))` and `(define-fun-rec c () Int (+ c 1))` (the third review's R01 and R03) and `(define-funs-rec ((f ((n Int)) Int) (g ((n Int)) Int)) ((+ (g n) 1) (f n)))` are unsatisfiable, and were refuted with `forall_inst` and `la_generic`. AY 0.27.0 unfolds a recursive definition lazily and answers `sat` for each of the three (with an empty model for R01), while it answers `unsat` for R01's axiom written out with `declare-fun` and `assert` | Both commands are refused in the problem, wherever they appear (`RecursiveDefinitionRefused`). A refutation through the axiom would certify SMT-LIB's reading against a producer's other one, and an inconsistent recursive definition makes every query over it vacuously unsatisfiable. No surveyed producer writes one | `parser/mod.rs`, `parser/error.rs`; upstream's `parser/tests.rs` now expects the refusal |
| 40 | every rule, through the premises it is checked against | The lexer did not read SMT-LIB's lexicon. A `;` comment ended at LF only, so `(assert (or a ; c<CR> b)) (assert (or b<LF> a))` lost `b)) (assert (or b` and read as `(or a a)` (L01, built on the third review's note that the two lexers differ; SMT-LIB and AY end a comment at CR or LF). Its number extensions read SMT-LIB symbols as numbers: `-5` and `-5abc` (declared quoted, `\|-5\|`) were the numeral `-5`, the second followed by `abc`; `1/2` was a rational where SMT-LIB reads `1` and the symbol `/2`; `1.` and `1.x` were the decimal `1.0` where SMT-LIB reads `1` and the symbol `.` or `.x`. `(declare-const \|-5\| Int) (assert (= -5 3))` and three more such scripts (L04..L06), each `sat` for AY, were refuted. `1/x` panicked on an empty denominator, and every Unicode white space character outside a literal was whitespace | A comment ends at LF or CR. Whitespace is space, tab, LF and CR; any other character outside a string, quoted symbol or comment is refused, as AY refuses it. A `.` or `/` is part of a number only when a digit follows it, so `1.`, `1.x` and `1/x` read as SMT-LIB reads them. The lexer records, for each number it reads, the symbol SMT-LIB reads in its place (`-5`, `-5abc`, `-1/2`, or `/2x` after `1`), and the parser refuses that number in the problem where the symbol is declared, defined or bound (`SymbolReadAsNumber`). A number whose SMT-LIB symbol is not in scope keeps its reading: SMT-LIB would refuse the script, and AY reads an undeclared `-5` as the numeral too. A proof keeps Carcara's numbers (`:args (-1)`, `1/7`), its terms being judged as written. Clean feeds both texts through a second tokenizer first, the `(_ bvN W)` pre-pass in `crates/clean-auto/src/bridge/ay_backend/carcara_verify/bv_literals.rs`, and it follows the same lexicon: had it kept ending a comment at LF only, it would disagree with this lexer about where a string literal begins after a CR and rewrite `(_ bvN W)` inside what Carcara reads as a string (X01..X03 and k1 in the fourth review, each `sat` for AY, were then refuted; X04 panicked) | `parser/lexer.rs`, `parser/mod.rs`, `parser/error.rs`; outside the vendored tree, `clean-auto`'s `bv_literals.rs` |
| 41 | `cp_division`, `cp_saturation` | The premise was read as `premises[0].clause[0]`, unchecked: the other literals of a longer clause were ignored, so the rule divided or saturated one disjunct of a clause as if it held. From `(cl (>= (* 2 x1) 2) (>= (* 2 x2) 2))`, which holds at `x1 = 0, x2 = 1`, `cp_division` by 2 derived `(>= (* 1 x1) 1)`, which does not. An empty premise clause panicked (found by the sweep in "Malformed steps are refused, not a panic") | The premise must be a unit clause, as `cp_addition` and `cp_multiplication` already required | `checker/rules/cutting_planes.rs` |

### Fixes 36 to 40: who writes these constructs, and the measured effect

Found by three adversarial reviews on 2026-10-02. The first (documents B03..B11
and Z01) found fixes 36 and 37: before them Clean (origin/main 4dc90e8ea)
certified (`PASSED`) a complete refutation of each of B03, B04, B06, B07, B10
and B11 (fix 36) and B08, B09 and Z01 (fix 37). C2's base ed7d04907 and
Trust's stage-2 `clean` certified each of them except B10, which goes through
`dt_project`: there `(h fst)` was read as `(fst (mk a b))` instead of
`(g (mk a b))`, and the `dt_project` step was correct for the term the parser
built. The second reviewed that fix and found what it left open: binders and
sort parameters named like built-ins (T1, T6..T9, S1, S6), reused names (R1,
R1b, R1c, R1e, R1f, R3, R5, R8..R10, R13) and AY's `check-sat-using` (U1, U2).
Origin/main and the first fix certified each of those; fix 38 and fix 37's
refusal of unknown commands close them. The third found refutations through
an inconsistent recursive definition that AY answers `sat` for (R01, R03 and
the `define-funs-rec` form; fix 39), and noted that the lexer ends a comment
at LF only. Following that note, this lane found the comment refutation (L01)
and four more scripts the lexer read with numbers where SMT-LIB reads a symbol
(L02, L04, L05, L06; fix 40). Origin/main and every earlier fix certified each
of them.

**Consumer survey (what decides refuse versus support).** None of the
producers whose problem text reaches this checker writes a definition, a
named term, a recursive definition, a scoping command other than through
Clean's own backend (below), `check-sat-assuming` or a sort parameter.
Trust's router can write a function named like a Carcara built-in, and AY's
export declares whatever names the session declared, one named like a
Carcara built-in or a quoted numeric-looking one such as `|-1|` included
(below):

- Trust's router, `problem_smt2` in `crates/trust-router/src/in_process_ay_backend.rs`
  (what `carcara_cross_check.rs` checks): `set-logic`, the datatype and sort
  preamble, `declare-fun`s, one `assert` and `check-sat`. trust-ir's
  `Formula::to_smtlib` prints quantifiers, never a `let`, `:named` or
  `define-fun`, and prints a negative integer as `(- 7)`. The preamble has no
  `par` datatype and no `define-sort`. Variables and the datatype family
  (sorts, constructors, selectors) are rendered in Trust's `__trust_`
  namespace (`ay_symbol_namespace.rs`), but uninterpreted `Pred` and `FnApp`
  names are not: they keep their source spelling (a user's Rust function
  name, or `opaque_loop_state`) unless it already starts with `__trust_`, and
  `reserved_symbol_handed_to_ay` declines only names AY reserves. So a
  function named like a Carcara built-in that AY does not reserve (`exp`,
  `sin`, `cos`, `tan`, `sqrt`, `tuple`, `real.pi`, `int.pow2`, ...) is
  declared and used under that name, and fix 38 refuses its declaration
  (`BuiltinNameDeclared`). Such a problem was not checkable before either: the
  use read as the built-in, a parse or sort error where the symbol is applied
  (measured: C08, `(declare-fun sin (Int) Int)` applied to `1`, `FAILED` on
  origin/main at the application and now at the declaration), so no verdict
  regresses.
- trust-cg's obligation queries (`obligation_cert_store.rs` hands the exact
  query to `clean cert verify-external`): `set-option`, `set-logic`,
  `declare-const` and `declare-fun`, `assert`, one `check-sat`, `get-value`
  and a trailing `exit`; the HORN path declares `Valid`. AY's 249-body
  `trust_cg_resident_session` corpus has nothing else.
- AY's own Alethe problem export (`alethe_problem_smt2_for`): `set-logic ALL`,
  `declare-sort`, `declare-fun`/`declare-const`, `assert`, `check-sat`, for the
  query's own assertion scope, one declaration per name of AY's context (AY's
  reserved operator names skipped), used by the query or not. It declines
  `define-fun` and datatype contexts. A session that declared a symbol named
  like a Carcara built-in AY does not reserve therefore has every proof
  refused, even when no assertion mentions the symbol: a completeness loss with
  no misreading behind it (C07, an unused `(declare-const exp Int)`, `PASSED`
  on origin/main and refused since fix 38). AY's printer quotes a name that
  Carcara's lexer would read as a number (`quote_symbol` writes `|-1|`,
  `|-1a|`), so such a session's export quotes every occurrence; it is read
  correctly and stays legal, since fix 40 refuses only a bare number whose
  SMT-LIB symbol is in scope (C14).
- Clean's own `AyProofBackend` (`clean-auto`, `proof_backend/execution.rs`)
  writes `last_problem`: `set-logic`, `(set-option :timeout ..)`, the
  translator's declarations (`declare-const`/`declare-fun` of `fvar_N`,
  `str_N`, `sk_exists_N`), its `assert`s, a `(push 1)` or `(pop 1)` line for
  each `push()` or `pop()`, and `check-sat`. Under a tier-1 proof profile,
  `verify_proof_if_required` (`proof_backend/verification.rs`) hands it to
  Carcara when ay's native check of the proof is incomplete. clean-elab's
  `smt` tactic reaches that path with `ProofProfile::carcara_verified` and
  never calls `push` or `pop`; trust-certify sets no profile (`new_with_proofs`,
  `new_default`) and never calls them either. Before fix 37 the fallback read a
  scoped script with its popped assertions as premises. It now refuses a script
  that used `push`/`pop` before invoking Carcara, with the reason
  (`SCOPED_SCRIPT_REFUSAL`, pinned by
  `tier_one_refuses_the_carcara_fallback_for_a_script_with_scopes`); a
  complete native check, which reads ay's own scopes, is unaffected. Nothing
  legitimate regresses: no caller combines `push`/`pop` with a tier-1 profile.
  (The first survey said Clean's adapter wrote no problem text. That was
  wrong: `pb_widths.rs` only reads it, but this backend writes it.)

User scripts are the other input to `clean cert verify-external`, and there
definitions are legitimate: AY's `carcara_external_check` tests solve and
prove scripts with nullary and parameterized `define-fun`s, `:named` labels
used as terms, and `check-sat-assuming`. So definitions are supported, with
the SMT-LIB reading (hygiene where the parser can rename a parameter, a
refusal where it would have to rename a binder that a premise shows), and so is
one `check-sat-assuming` query. Scoping commands, which only Clean's own
backend writes and which would need declarations scoped as well as
assertions, are refused, and so is every command the parser does not read. A
binder or sort parameter named like a built-in gets SMT-LIB's reading (it
shadows the built-in), which costs no refusal. A reused name is refused: no
producer writes one, and AY refuses every reuse except a `:named` label's.
A recursive definition is refused (fix 39): no surveyed producer writes one.
AY's command line does pair an authored script that has one with its proof,
but its proofs of such scripts inline the definition, so they never matched
the axiom Carcara read (`rec1`..`rec4`, AY's own proofs: holey, or an `assume`
not in the problem, on origin/main and now). The one such proof that passed is
one that never uses the definition (C09); it is now refused. The lexer reads
SMT-LIB's comments, whitespace and numbers (fix 40), which no legitimate
script reads differently (measured against Carcara and against Clean's
`bv_literals` pre-pass, which now shares the lexicon), and a number is refused
only where SMT-LIB reads a symbol in scope there, which no surveyed producer
writes. "No AY-sat document passes" holds for the measured sample only.

**Measured** (`clean cert verify-external`, `targo --unverified` builds, no
proof claim; base is origin/main 4dc90e8ea, "36-37" is fixes 36 and 37 as
first committed, "38" adds fix 38, new adds fixes 39 and 40 and the tester
check; AY is 0.27.0, build 11536). Each count is the documents that `PASSED`:

| Documents | AY's answer | Base | 36-37 | 38 | New |
|---|---|---|---|---|---|
| The first review's 97 (`adv` 28, `adv2` 11, `r2` 58) | B03, B08, Z01 `sat`; B09 `sat sat`; B04, B10, B11 not parsed (a function symbol used as a value); B06, B07 not parsed (a `:named` label used as a term) | 24 | 15: the 9 above flip to `FAILED` | 14: A20 (a datatype named `Int`, `unsat`) is now refused | 14 |
| Found while fixing them: S01, S02 (a binder named like a definition), S03, S04 (a binder capturing a definition's global), Q01..Q05 (a second `check-sat`, an assertion after `check-sat` or `exit`, `push`/`pop`, `reset`) | `sat`, except S03 (not parsed), Q01 (`sat unsat`, two queries) and Q03 (no answer; it stops at `exit`) | 9 of 9 | 0 | 0 | 0 |
| Controls C01..C06: one `check-sat-assuming` query, commands after `check-sat`, the B03 shape read correctly, a `:named` label, a `lambda` definition, a binder shadowing a definition | `unsat`, except C04 (not parsed) | 5 (not C03, whose hygienic reading base got wrong) | 6 | 6 | 6 |
| The second review's 40 refutations (T1, T6..T9, S1, S6, R1..R16 with proofs, A1, A2, A4, H1..H4, P1, P2, Q1..Q6, W1, W2) | `sat` for 18 of the 27 that base certified besides P1 and R1d (T6, T7, T9, S6, R1, R1b, R1e, R1f, R5, R13, A1, A2, Q1..Q6), refused by AY for T1, S1, R1c, R3, R8..R10, `unknown` for T8, `unsat` for R7, P1 and R1d | 29 | 21: A1, A2 and Q1..Q6 flip | 2: P1 and R1d, both `unsat` | 2 |
| The second review's 13 certificate shapes (`rev1`: commands around the query, two `check-sat`s, `check-sat-using`, sort aliases) | `sat` or `sat unsat` for s6, u1, u2 and `sort_capture`; `unsat` for the rest (s5 has no `check-sat`) | 12 | 9: s6, s7, s9 refused | 7: u1 and u2 refused | 7 |
| The third review's 11 (`rev3`: B03, H01..H07, R01..R03) | `sat` for B03, H01, H02, H05 and R01..R03; H03, H04, H06 not parsed (a `:named` label or a function used as a value); `unsat` for H07 | 4: B03, H02, R01, R03 | 2: R01, R03 | 2 | 0: R01 and R03 refused |
| Fix 40's attacks (`lex`: L01..L08, with a second L02 proof) | `sat` for all nine | 6: L01, L02 (both), L04, L05, L06; L07 crashed the checker (`1/x`) | 6 | 6 | 0 |
| Controls C07..C14: an unused constant named `exp`, a used function named `sin`, an AY proof beside an unused `define-fun-rec`, a comment ended by CR, numerals beside `-x` and `/x`, R01's axiom written out, a tester, `\|-1\|` declared and used quoted | `unsat` for all eight | 6: not C08 (a parser error at `(sin 1)`) or C10 (read with the comment running on) | 6 | 5: C07 refused | 5: C09 refused, C10 read correctly |

Over these 193 documents, none that AY answers `sat` for in any of its
queries (72 of them) passes on the new binary. That is a statement about this
sample, not a general claim: what fixes 36 to 40 establish is pinned by the
reading tests below, and the oracle is not authoritative either. AY 0.27.0
reads `define-fun-rec` against SMT-LIB (fix 39: `sat` with an empty model for
R01, `unsat` for its axiom written out, and `recursion depth limit (1000)
exceeded` for `(get-value ((f 0)))`; `sat` and `memout` for R03's
`(get-value (c))`), which is an AY defect to report there. AY does not take a
`:named` label as a term (`unknown constant m`), so it gives no answer for
H03, H04 and the B07 family, and their satisfiability rests on the SMT-LIB
reading alone. Every document still `PASSED` is one AY answers `unsat` for,
or one of three it does not answer whose problems are unsatisfiable: A15 (a
higher-order field, so `(h (mkE f))` is `f`), C04 (`x < 3` and its negation)
and s5 (`p` and `(not p)`, then `exit` with no `check-sat`). The refusals of
documents AY answers `unsat` for are deliberate: A20 (a datatype named
`Int`), R7 (a label `k` defined twice), s7 (a second `check-sat`), s9 (a
declaration after `check-sat`), C07 (a constant named like a built-in) and C09
(a recursive definition). The per-document table, with AY's answer and the
four verdicts, was kept with the lane's evidence
(`target/parser-soundness/TABLE-r3.tsv`).

Legitimate inputs were replayed through base and the new binary, proof by
proof. The first two sets give identical verdicts and identical reasons for
each failure:

- AY 0.27.0's proofs of the `trust_cg_resident_session` corpus: 148 `sat`, 101
  `unsat`, 100 proofs written; 95 `PASSED` and 5 holey on both.
- 32 scripts: 29 in the shapes of AY's `nullary_macro_assertions`,
  `named_label_uses` and `define_fun_reading` tests and three parameterized
  `define-fun`s (one whose parameter is named like a global, one with the
  B03 capture, one binder named like a definition). AY's command line answers
  `unsat` for 26 and writes 22 proofs (it does not take a `:named` label as a
  term); 9 `PASSED` and 13 `FAILED` on both (3 holey, 9 `assume` steps not in
  the problem, 1 `equiv_neg2`).
- AY's proofs of five scripts with a recursive definition (`rec1`..`rec4`,
  `rec6`; `rec5` wrote none): `FAILED` on both (holey or an `assume` not in
  the problem on base, the recursive definition refused now), except `rec6`
  (C09 above).

**Tests.** `carcara/tests/problem_reading.rs` (new) pins each reading as the
premises of an equivalent script written without definitions (or, for a
binder named like a built-in, as an alpha-equivalent one with a fresh name),
refuses each of the refutations above (in both `define-fun` readings), and
has positive controls. 15 of its 16 tests fail on origin/main (the 16th is
the controls), and the 3 that pin fixes 39 and 40 and the tester check fail
with fix 38's parser. The lexer's own tests (`parser/lexer.rs`) gain three, and
upstream's `test_define_fun_rec` (`parser/tests.rs`) now expects the refusal.
The clean-auto adapter adds 38 `pr_u*` refutations, each refused with the
reason named (`pr_u31`..`pr_u38` for fixes 39 and 40, two of them written
inline so that no checkout rewrites their CR), and 13 `ok_pr_*` refutations
that must verify.
Disabling each part of the fix, by editing the parser in place and restoring
it, fails these tests:

- no free-variable scan at all (upstream's expansion): the hygiene, capture,
  renamed-name and refutation tests;
- no placeholder (a captured parameter refused instead of renamed): the
  hygiene and renamed-name tests;
- no refusal under other binders: the capture test;
- a definition taking precedence over a local binding: the shadowing and
  refutation tests;
- no closedness check for `:named`: its test;
- a `:named` definition inside a body keeping its placeholder: the hygiene
  test;
- the parameter not renamed: the hygiene, renamed-name and refutation tests;
- no script check, scoping commands allowed, or commands after the query
  allowed: the query and refutation tests;
- unknown commands skipped, or a quoted command name read as the command: the
  unknown-command (and refutation) tests;
- a built-in operator taking precedence over a local binding, as a term or as
  the head of an application: the operator-shadowing (and refutation) tests;
- a built-in sort taking precedence over a sort parameter, or a sort parameter
  taking arguments: the sort-shadowing (and refutation) tests;
- a built-in operator name, a reused name, a built-in sort name (for a
  `declare-sort`, `define-sort` or datatype) or a reused sort name allowed: the
  names test (and the refutation test for the first two);
- an assertion that is not a formula allowed: the sort-shadowing test;
- recursive definitions read (fix 39): the recursive-definition test and
  upstream's `test_define_fun_rec`;
- a comment ending at LF only, Unicode white space skipped, a `.` or `/` taken
  into a number without a digit after it, the number check off or blind to
  definitions, or a negative or rational number's SMT-LIB symbol not recorded
  (fix 40): the lexing test and one of the lexer's own; the check applied to
  proofs as well: the lexing test (a proof's `:args (-1)` beside a declared
  `|-1|`);
- a tester accepted for any constructor, for a local binding, with other than
  one argument, or with a non-symbol index: the tester test.

A first choice of `|` for the unforgeable names made the printer panic
(`quote_symbol` asserts that no symbol contains `|`), which one of these runs
showed; a backslash is just as unforgeable and prints.

The vendored suite (`targo --unverified test --locked --release --workspace`)
passes on origin/main and with these changes, which add only the 16
problem-reading tests and three lexer tests: `carcara` 122 unit, 3 proof,
230 rule and 1 doc test, `carcara-soundness` 16 unit tests and the bounded
battery test. Two entries of C2's `ambiguous_datatype_symbols_are_refused`
acceptance list, a constant and a sort each declared twice, moved to
`problem_reading.rs` as refusals, and its two `define-fun(s)-rec` refusals
left it (fix 39 refuses the command first). The battery, `--mutants 200
--seed 11` over every rule, reports 0 unsound on each tree; its counts move
between runs of one tree (origin/main: 609,959 instances, 222,957 parse
errors, 382 checker panics; the same tree in the C2 review: 609,361, 222,836,
364; fixes 36 and 37: 609,584, 223,002, 386; fix 38: 610,130, 223,197, 388;
fixes 39 and 40: 609,872, 223,315, 350, at a 16.25 GB peak). The battery
judges accepted steps against the terms the parser built (its datatype table
comes from the same parse), so it cannot see a problem read with the wrong
premises; the rule tests and the adapter fixtures cover these fixes.

What stays fail-closed or open:

- A capture under a quantifier, `lambda`, `choice`, `let` or `match` case is
  refused rather than renamed: renaming that binder would change a premise a
  proof has to `assume`.
- In the ordinary reading a renamed parameter appears in the definition's
  `lambda` premise, which a proof cannot write; the macro reading, which the
  adapter tries next, verifies such a refutation.
- A reused name is refused, not read: every `:named` label, definition,
  declaration and datatype symbol of the problem must have a new name, and so
  must every sort. AY refuses most such scripts (a constant declared twice, a
  definition of a declared name, `true` or `re.all` declared), but accepts a
  `:named` label that reuses a name (R1, R1b, R1e, R1f, R5 and R13 answer
  `sat`, R7, a label defined twice, `unsat`) and a declaration or label named
  like a built-in it does not reserve (G2's `real.pi`, G3's and R14's
  `re.none` answer `sat`). Clean refuses all of them, used or not: a
  declaration named like a built-in that no assertion uses (C07, AY `unsat`)
  is refused although nothing would be misread, which costs the AY export and
  Trust's unprefixed function names described above. The one reuse left legal
  is C2's: a datatype symbol and another global of the same name whose
  argument sorts do not overlap, where every use of either is a sort error
  rather than a misreading.
- A recursive definition is refused even when it is consistent, or unused
  (C09, AY `unsat`).
- A number written as Carcara's extensions write it (`-5`, `1/2`) is still
  read as a number in the problem where SMT-LIB reads a symbol that is not in
  scope. Such a script is ill-formed SMT-LIB rather than misread; AY reads an
  undeclared `-5` as the numeral too, and refuses `1/2` (`unknown constant
  /2`). Scope is judged where the number is read, so in `(assert (= -5 3))
  (declare-const |-5| Int)` the number keeps its reading, as it does for AY,
  while SMT-LIB refuses that assertion (its symbol is undeclared there).
- A binding list that binds one name twice (`(define-fun h ((x Int) (x Int))
  ..)`, `(let ((x 1) (x 2)) ..)`) keeps upstream's reading, the last binding;
  AY reads P1 the same way (`unsat`).
- Inside a proof, a definition or binder is read as upstream reads it; proof
  terms are judged as written, and every `assume` must still match a premise.
- `(check-sat) (check-sat)` with nothing between, and a declaration after the
  query, are refused although harmless; no surveyed producer writes either.
- A name or sort refusal of a declaration reports the position after the
  command, not the symbol's own; the message names the symbol.

### Completeness extensions (no soundness fix)

These accept more valid steps; each one is sound by the argument given and is
covered by the soundness battery like every other rule.

| # | Rule(s) | What was rejected | Change | Files |
|---|---|---|---|---|
| C1 | `and_simplify`, `or_simplify` | A step whose single remaining argument (after removing the skip constant `true`/`false` and duplicates) is itself an application of the rule operator and IS the result: `(= (and true (and p q)) (and p q))`, `(= (or (or p q) false) (or p q))`. The result's arguments `[p, q]` were compared with `[(and p q)]`, while `(= (and true q) q)` was accepted. AY emits this form for bit-blasted `and`/`or` words (7 trust-cg proof-database rows) | Also accept when exactly one argument is left and it equals the result term. Removing identities and duplicates of an idempotent operator preserves the value, and an application with one argument left equals that argument | `checker/rules/simplification.rs` |
| C2 | `dt_project` (new rule; Clean-only: no upstream Carcara has a datatype rule, neither d62d45cf, AY's pinned 9a352ee nor main 0b38c860) | Every datatype fact. Constructors and selectors were registered as uninterpreted symbols and no rule read them, so a proof could not use `sel_i(C(t_0 .. t_n)) = t_i`. AY printed its internal `DatatypeSelectorProject` step as `:rule hole`, and Trust's Carcara gate downgraded four trust-router datatype tests from UNSAT to Unknown | A fully checked rule (never hole-like). The conclusion is the single literal `(= (S (C t_0 .. t_n)) t_i)`, with no premises and no arguments. `C` is a constructor of a declared non-parametric datatype `D`, applied with its declared arity and field sorts. `S` is the `i`-th selector *of `C`*, of sort `(-> D T_i)`, and is no other symbol of `D`. The right side is the same (hash-consed) term as `t_i`. No enclosing anchor binds the name `S` or `C`. Everything else is refused: another constructor's selector (SMT-LIB leaves its value unspecified), an uninterpreted function, any other field or value, the reversed orientation (use `symm`), a nullary constructor, a parametric datatype (written bare, its constructor's sort is `(par ..)`; qualified with `as`, as in `((as some (Opt Int)) a)`, the constructor returns an instance of the parametric sort), extra literals, premises, arguments. Sound because every SMT-LIB model interprets `D` as the term algebra of its constructors, where `S` is the projection of `C`'s `i`-th field. Carcara resolves an application by the symbol's name alone (the later declaration wins), and a `Term::Var` is only a name and a sort, so the rule's reading of `S` and `C` needs two guards. **Parser:** these ill-formed SMT-LIB scripts are refused. (1) A global declaration that shares its name *and argument sorts* with a constructor, selector or tester, whatever its result sort, in either order: a `declare-fun`, `declare-const`, `define-fun` (declared or expanded as a macro), `define-fun(s)-rec`, a problem's `:named` term, or another datatype's constructor, selector or tester. A `par` symbol (a parametric datatype's constructor, selector or tester) overlaps any declaration of its arity, and (5) keeps it at that arity. (2) A proof's `define-fun` or `:named` term that overlaps a datatype symbol the same way. (3) A datatype declared twice, or named like a `declare-sort` or `define-sort` sort, in either order. (4) A name used twice inside one datatype (upstream kept the last of two same-named constructors silently). (5) `(as f S)` for a `par` symbol `f` whose sort `S` is not an instance of `f`'s `par` sort. Upstream built `f` at any `S` ("TODO test unification"), so with a parametric `L` declaring a constructor `snd` of another arity after `P` declared its selector `snd`, `(as snd (-> P Int))` was `P`'s selector, and `dt_project` certified refutations of satisfiable problems with it (found in review, 2026-10-02). `Sort::match_with`, which does the unifying, now also requires sequences of equal length: upstream's `zip` matched `(-> X Int (L X))` with `(-> P Int)`. Same-named symbols with different argument sorts stay legal, as two datatypes' same-named fields must: a use of the earlier one after the later is a sort error, never a misreading. **Rule:** an anchor argument with the same name and sort is a variable, so an enclosing anchor that binds either name refuses the step. The parallel checker also needed an upstream crash fixed (`LocalPool::get_datatype`, see "Also hardened"). These guards settle which symbols `S` and `C` are; they cannot protect against a misread application structure. The rule checks the term the parser built, so a problem read with the wrong premises passes it unnoticed: under fix 36's capture, B10's `(h fst)` became `(fst (mk a b))` instead of `(g (mk a b))`, and a correct `dt_project` step refuted a satisfiable problem. Reading the problem as SMT-LIB does is the parser's responsibility (fixes 36 to 40) | `checker/rules/datatypes.rs` (new), `checker/rules/mod.rs`, `checker/shared.rs`, `parser/datatypes.rs`, `parser/mod.rs`, `parser/error.rs`, `ast/sort.rs`, `ast/pool/advanced.rs`; `ast/problem.rs` gains a read accessor for the battery; tests in `carcara/tests/rules/datatypes.rs` (new), registered in the upstream `carcara/tests/rules/mod.rs` |

C1 adds the "Single remaining ... argument is the result" groups to
`and_simplify` and `or_simplify` in `carcara/tests/rules/simplification.rs`
(each fails with the change reverted, and each has rejected neighbours), and two
sound refutations (`ok_and_simplify_nested_result`, `ok_or_simplify_nested_result`)
to the clean-auto adapter's `soundness_tests.rs`. The battery run
`--mutants 20000 --seed 11 --rules and_simplify,or_simplify` over the seeds
including these cases reported 0 unsound in each of three runs on f3acd3dac plus
C1. The accepted counts differ between runs of the same command: 1,750 to 1,813
`and_simplify` and 1,748 to 1,809 `or_simplify` steps.

C2's tests are `carcara/tests/rules/datatypes.rs` (new), registered by one line
in the upstream `carcara/tests/rules/mod.rs`. It holds a `test_cases!` group for
each condition above, and refutations run through the sequential checker and
the parallel one with 1 and 4 threads, which must agree on acceptance and on
the holey flag: complete, *not holey* refutations through `dt_project` and
through `symm`, and complete refutations of six satisfiable problems, each
refused at the `dt_project` step or at parse time. The
satisfiable problems use another constructor's selector (both directions), an
uninterpreted function, the other field, an anchor that rebinds the selector,
and a selector redeclared by `declare-fun`. A parametric datatype is refused
with its reason, bare and `as`-qualified. The parser refusals are checked in
both `define-fun` modes, and each has accepted neighbours: same-named fields
of two datatypes (different argument sorts), a constructor's name with other
argument sorts, binders that shadow a constructor or selector, an ordinary
symbol or sort declared twice, and a `:named` term with a fresh name.
`par_symbols_are_qualified_only_at_an_instance_of_their_sort` refuses guard (5)
in both `define-fun` modes: a nullary or binary `par` constructor named like
`P`'s selector or constructor, qualified at `P`'s symbol's sort through a problem
`define-fun`, an equation or one `declare-datatypes` block, at a sort no symbol
has, or at a constant's sort, and the same qualification in a proof. It keeps
instances legal (bare and applied, nullary and not), and refuses the full
refutation the review built from it. The test
cases include mutually recursive datatypes, a `define-fun` around the
constructor or selector (a macro, expanded before the rule sees it), a `let`
(not looked through) and a binder inside a field that shadows the
constructor's name.

Disabling each condition makes these tests fail. Measured by editing the rule
in place, then restoring it:

- dropping the anchor check accepts the shadowing refutation of a satisfiable
  problem as complete (`Ok(false)`, not holey);
- dropping the parser guard does the same for the redeclared selector;
- comparing whole sorts instead of argument sorts accepts twin datatypes whose
  constructors share argument sorts; dropping either half of the sort-name
  check accepts a datatype named like a declared sort (or the reverse); not
  recording macro `define-fun`s and `:named` terms lets the two `define-fun`
  modes disagree;
- taking the selector from any constructor of `D`, or accepting any field,
  fails the "Selector of another constructor" and "Wrong value" cases;
- dropping the premise, argument or clause-length checks fails the "Exactly
  one literal" cases. These three are well-formedness conditions: the
  conclusion stays valid without them;
- dropping the `as` instance check (guard 5) parses the first refused problem,
  a problem `define-fun` around `(as snd (-> P Int))`. `clean cert
  verify-external` on the branch before the check certified (`PASSED`) each of
  the six `dt_u12`..`dt_u17` adapter fixtures below;
- matching sequences only up to the shorter length, as upstream's `zip` did,
  parses exactly the `(snd (h1 X) (h2 Int))` case and still refuses the rest;
- making the parallel checker report every proof holey fails
  `dt_project_refutations_are_not_holey` (`Ok(true)` against `Ok(false)` with
  1 thread);
- dropping the instantiated-sort check (`sort_args`) changes nothing: the
  backup check on the datatype's parameters then refuses the `as`-qualified
  constructor with the same message. Dropping both refuses it for a sort
  mismatch instead, which fails the reason the test asserts. Neither weakening
  accepts the step.

The battery catches four of these weakenings on its own: the anchor check,
the parser guard against a same-sorted redeclaration, the selector of any
constructor, and any field. It cannot catch the argument-sort, sort-name,
macro or `as` weakenings, because its datatype table comes from the same parse
(see "How it judges them"). Measured with `--mutants 200 --seed 11 --rules
dt_project` on the C2 tree before guard (5), the battery rebuilt against each
weakened checker:

| Weakening | UNSOUND rows |
|---|---|
| None | 0 (two runs) |
| Anchor check dropped | `bind` 9, `trans` 2, `resolution` 2 (a step inside an anchor is judged through what the subproof exports) |
| Selector of any constructor | `dt_project` 36; 38 in a second run |
| Any field accepted | `dt_project` 68; 68 in a second run |
| Parser guard dropped | `dt_project` 4, `resolution` 2 (the generator's redeclared selector, read as uninterpreted) |

The counts vary between runs of the same command, so only the qualitative
claim is stable: each weakening is caught, and the unweakened checker gives 0.
The two runs of the unweakened checker accepted 198 and 187 `dt_project` steps
(155 and 151 exercised). An earlier tree, before the argument-sort guard, gave
42 and 64 for the two `dt_project` weakenings, and an independent
implementation of them (in review, 2026-10-01) gave 36 and 76.

The prototype this rule grew from (`dt_project_prototype.patch`, 2026-10-01) had
neither guard. Its build answered `valid` (complete, not holey) for both
refutations of satisfiable problems: the anchor that rebinds `snd`, and
`(declare-fun snd (P) Int)`. AY 0.27.0 (build 11536, fce0a8fae) itself refuses
the second problem ("would conflate the user symbol with the builtin datatype
operation").

The clean-auto adapter's `soundness_tests.rs` runs the same cases through
`verify_alethe_proof`, the path behind `clean cert verify-external`. Its
`ok_dt_project` (AY's `__trust_*` spelling), `ok_dt_project_symm` and
`ok_dt_project_mutual` must verify. Six `dt_u*` refutations of satisfiable
problems must be refused at the named step. Eleven more must be refused at
parse time, each ill-formed and satisfiable under the reading in which the
symbol is not the datatype's own: a redeclared selector and constructor, twin
datatypes whose constructors share argument sorts, a datatype named like a
declared sort over which `snd` was already declared, a `define-fun` named like a
constructor, and six (`dt_u12`..`dt_u17`) that qualify a parametric datatype's
constructor named like `P`'s selector or constructor at a sort that is not an
instance of its own (guard 5). `dt_u9`..`dt_u11` were certified (`PASSED`) by
`clean cert verify-external` before the parser guard covered argument sorts,
sort names and macro `define-fun`s, `dt_u11` through the adapter's retry with
`define-fun` expanded as macros; `dt_u12`..`dt_u17` were certified before guard
(5), and with `hole` in place of `dt_project` each of them is only holey. AY
0.27.0 (build 11536, fce0a8fae) reports `unsat` for the three sound problems
(its own proofs still print the step as `hole`) and `sat` for `dt_u1`..`dt_u4`.
It does not parse `dt_u5`/`dt_u6` (function-sorted binders), refuses
`dt_u7`..`dt_u11` ("would conflate", "ambiguous overloaded symbol", "sort 'P'
is already declared"), and reports `unknown` for `dt_u12`..`dt_u17`, as it does
not parse a function symbol used as a value ("function 'g' requires
arguments"). When both `define-fun` readings fail, the adapter now reports both
errors (`pb_widths.rs`, Clean's own code; before, a refusal under the macro
reading was hidden behind the ordinary reading's error), pinned by
`both_define_fun_readings_are_reported_when_both_fail`.

The battery now models non-parametric datatypes (see "How it judges them"), and
`dt_project` is in its rule-swap table and has its own generator. On the final
C2 tree, `--mutants 20000 --rules dt_project` reported 0 unsound for every rule
(about 18 s each, 0.13 GB peak under `heavy_gate`):

| Seed | Instances | Parse errors | Checker panics | `dt_project` accepted | `dt_project` exercised |
|---|---|---|---|---|---|
| 11 | 526,864 | 445,115 | 131 | 2,811 | 1,423 |
| 12 | 527,091 | 445,259 | 139 | 2,801 | 1,415 |

The panic each run printed is the empty-clause `pbblast` index panic, a
refusal since "Malformed steps are refused, not a panic". Over all rules, `--mutants 200
--seed 11` on the final tree checked 609,361 instances (222,836 parse errors,
364 checker panics) and reported 0 unsound for every rule, in 36 s at a
0.60 GB peak. Without mutants
(`--mutants 0`), two runs each accepted 48 `dt_project` steps
and exercised 46: 23/22 from the seeds and 25/24 from the generator.
The two that were not exercised match, by count, the two accepted steps that
sit inside an anchor (the `(y Int)` seed and the `(z Int)` generator case),
which the battery never judges locally. Why about half of the accepted mutant
steps go unexercised was not measured. The bounded battery test
(`tests/battery.rs`, every rule, 40 mutants per seed) passed with no
seed-expectation mismatch.

Fix 13 is deliberately conservative. An anchor value that mentions a name the
same anchor binds, such as `(:= (x U) (f x))`, is refused even where reading
`f x` in the outer scope would be sound, because `x` then has two meanings
inside the anchor. Upstream's rule tests contain no such anchor, and neither does
the 98-proof AY corpus below (it uses no anchor with arguments at all).

Also hardened, with no counterexample claimed: `pbblast_pbbconst` compared a bit
after wrapping it to `i32`, so `4294967297` read as `1`. `@pbbterm` has no SMT-LIB
semantics for bits outside {0, 1}, so the battery cannot judge that case. The
comparison is now exact. Separately, `(@d (cl))` in `drup` no longer panics.
And a tester `(_ is C)` (`parser/mod.rs`, `make_indexed_op`, an upstream
`TODO`) took any term as `C` and any arguments. Substitution and free variables
do not look inside an indexed operator's arguments, so a `define-fun` parameter
or binder variable written as `C` was never substituted or seen. No rule reads
a tester and AY refuses an ill-formed one, so no refutation of a satisfiable
script came of it (third review). `C` must now be a constructor of the single
argument's datatype, and the global constructor rather than a local binding of
its name (`InvalidTester`); `testers_name_a_constructor_of_their_argument` in
`problem_reading.rs` pins it.

Fixed with C2, an upstream crash (not a soundness defect; worth its own line in
an upstream report): `LocalPool::get_datatype` (`ast/pool/advanced.rs`) read
the thread-local pool, which never holds a datatype, so in the parallel checker
the first rule to look a datatype up panicked. Upstream has no such rule, so
nothing reached it there; `dt_project` does. It now reads the global pool.
`dt_project_refutations_are_not_holey` runs each refutation through the
parallel checker with 1 and 4 threads.

Also hardened: bit-vector result widths are checked at the parser, for every
operator that computes one (`parser/mod.rs`, `parser/error.rs`
`BitVecWidthOverflow`). `TermPool::compute_sort` adds and multiplies widths
unchecked and cannot return an error, so on pinned Carcara 9a352ee (release)
`((_ sign_extend 18446744073709551615) #b11)`, the same `zero_extend` and
`(concat (_ bv0 18446744073709551615) #b11)` each sort-checked as
`(_ BitVec 1)`, and `((_ repeat 9223372036854775809) #b11)` panicked. Now
`concat`, `zero_extend`, `sign_extend` and `repeat` refuse a result that does
not fit `usize`, and `extract` requires `i >= j` and a width that fits even
over an operand whose width is not known (`ParamBitVec`). The tests are
`crates/clean-auto/src/bridge/ay_backend/carcara_verify/parser_width_tests.rs`.

### Tests changed

Upstream tests that expected unsound behaviour were changed. Each change is
marked in the file:

- `evaluate` "Arithmetic": the expected value is corrected from `0` to `3`.
- `div_simplify` "Transformation #1": the symbolic `t / t` cases are now `false`.
- `string_decompose` "Reverse argument set to true": the old skolems are now
  `false`, and the correct skolems are added as `true`.
- `cp_division`, `cp_saturation`, `cp_literal`, `pbblast_bv{and,xor}_ith_bit`:
  the literals are now `@int_of` bits. The two `(* 2 l)` literal cases, which
  upstream marked "SHOULD BE AVOIDED", are now `false`.

Fixes 24-33 changed four more upstream expectations, each marked in the file:

- `re_concat_unfold_pos` "Simple working examples" cases 2 and 3, and both
  `re_kleene_star_unfold_pos` "Simple working examples" cases, expected the
  Skolem-witness conclusions of fix 32 to pass. They are now `false`, under a
  heading that says why, and a `str.to_re`-only positive case is added for
  `re_concat_unfold_pos`. In the first kleene case the premise's word is
  literally named `x`, which the generated `choice` binder — it always binds
  `x` — captures as well.
- `ast/substitution.rs`'s own `test_substitutions` expected
  `(forall ((y Int) (y_renamed Int)) (= y y_renamed))` under `{x -> y}` to
  rename *both* bindings. With fix 26 the first binding skips past the body's
  free `y_renamed` to `y_renamed_renamed` and the second is left alone; both
  results are alpha-equivalent to the original, and the new one captures
  nothing.

Fixes 34 and 35 add `refl_let_values_do_not_leak_into_the_body` in
`carcara/tests/rules/reflexivity.rs` and the "Bit-vector widths are not truncated
to 32 bits" and "Wide literals are distinct terms" groups of
`evaluate_smt_lib_semantics` in `carcara/tests/rules/extras.rs`; each fails with
its fix reverted.

Fix 41 and the malformed-step sites (see "Malformed steps are refused, not a
panic") are tested in `carcara/tests/malformed_steps.rs` (new) and, through the
adapter, in
`crates/clean-auto/src/bridge/ay_backend/carcara_verify/malformed_step_tests.rs`;
no upstream test changed.

The resource budget (see "Bit-vector expansion has a resource budget") is tested in
`carcara/tests/resource_budget.rs` (new), by `every_rule_on_a_wide_step_is_judged_within_the_budget`
in `carcara/tests/malformed_steps.rs`, by unit tests beside the code it changes, and, through the
adapter, in `carcara_verify/diagnostics.rs`; no upstream test changed.

Fix 39 changes upstream's `test_define_fun_rec` (`carcara/src/parser/tests.rs`),
which read three recursive definitions as premises, to expect the refusal.
Fix 40 adds three tests to the lexer's own (`carcara/src/parser/lexer.rs`);
upstream's lexer tests pass unchanged.

New tests cover every counterexample, next to valid instances of the same
rule. They live in `carcara/tests/rules/{arrays,bitvectors,cutting_planes,drup,extras,linear_arithmetic,pb_blasting,quantifier,reflexivity,resolution,simplification,strings,subproof}.rs`
and `carcara/tests/test_proof.rs`; the last also runs the anchor-scoping cases
through the parallel checker. The clean-auto adapter adds end-to-end
certificates in
`crates/clean-auto/src/bridge/ay_backend/carcara_verify/soundness_tests.rs`: 51
complete refutations of satisfiable problems, each of which must be rejected
at the named step (45 that the verbatim copy fully verified, and six `dt_u*`
ones through C2's rule, which upstream rejects as an unknown rule); eleven
ill-formed `dt_u*` problems the parser must refuse; 38 `pr_u*` refutations of
problems fixes 36 to 40 read differently (or, for fix 39, through an axiom AY
reads differently), each refused with its reason named; and 40 sound
refutations that must verify. C2's rule tests are
`carcara/tests/rules/datatypes.rs`; fixes 36 to 40 are tested in
`carcara/tests/problem_reading.rs` (new), and fix 40 also in the lexer's own
tests. AY's r18 cross-review (2026-10-07) added 31 `bs_u_*` refutations in
`crates/clean-auto/src/bridge/ay_backend/carcara_verify/builtin_spelling_tests.rs`:
a user symbol spelled like a built-in operator or sort (declared, defined, a
datatype symbol or label, at the built-in's own arity too), a quoted numeral, and
`|false|` (bound, or declared), each refuted by `evaluate` reading it as the
built-in. Clean 6a916983, which predates fix 38, fully verified 15 of them; each
is now refused with its reason named, and `names_in_use_are_refused_in_the_problem`
covers the same-arity declarations and `|false|`.


## The soundness battery (`soundness/`, Clean-authored)

`soundness/` is not upstream code. It is a mechanical rule-soundness battery.

**How it generates instances.**

- It takes every case of Carcara's own `test_cases!` rule tests as a seed, read
  at run time.
- It mutates each seed syntactically: subterms, operators, arguments, numerals,
  sorts, binder names, clauses, premises and rule names.
- It adds systematic generators for rule families whose conclusions the checker
  computes or whose side conditions are hard to reach by mutation:
  - bit-blasting circuits at widths 1–4;
  - `evaluate` over every operator on small constants;
  - arithmetic simplification on constants, including zero divisors;
  - random one- to three-literal linear lemmas over `Int` and `Real`;
  - `aci_simp`/`ac_simp` rewrites;
  - partial `beta_equiv`;
  - array extensionality witnesses;
  - `polyeq` through `assume` and `refl`;
  - `forall_inst` capture;
  - pseudo-Boolean ith-bit lemmas;
  - `qnt_cnf` capture;
  - `poly_simp_rel` over `Int`, `Real` and bit-vector differences;
  - context subproofs whose inner steps are checked rules;
  - binder scoping over **finite** sorts: alpha-equivalence of binders of
    different arity, `let` values read in the enclosing scope, `forall_inst`
    and `beta_equiv` whose bodies rebind the instantiation term's variables or
    hide one in a `let` value, `bind` over a `refl` that has to rename. The
    older binder generators build over `Int`, where every quantifier the
    evaluator meets is `Unknown`; these are `Bool`-sorted, so it decides them;
  - `onepoint` points under a binder that rebinds the eliminated variable or
    binds a variable of the point's term;
  - `string_decompose` at split points the premise does not bound from below;
  - `re_unfold_neg` over words whose free variables the generated quantifier may
    capture, and the two positive unfoldings over a *constant* word, where the
    Skolem witness the rule builds makes the conclusion contradict itself;
  - `evaluate` over `(_ bv<n> <w>)` literals with `n` outside `[0, 2^w)`;
  - `refl` over a `let` nested in a `let`, `forall` or `exists`, where the inner
    `let` rebinds a variable its own values mention, each side named
    independently (a fixed seed-dependent sample of 6,000 pairs plus the three
    counterexamples of fix 34);
  - `evaluate` and `refl` over bit-vectors of widths `2^32` to `2^33 + 1` built
    from small values (`zero_extend`, `sign_extend`, `concat`, literals, and the
    arithmetic, bitwise, comparison, shift and `extract` operators over them);
  - `dt_project` over every selector of four datatypes (two-constructor pairs,
    a recursive datatype with a nullary constructor, and a mutually recursive
    pair), plus an uninterpreted function of a selector's sort. Each is applied
    to constructor applications and to a free constant, against every candidate
    value of the field sort, in both orientations. On top of that, the two
    attacks C2 guards against: complete refutations of satisfiable problems
    through an anchor that rebinds a selector or constructor name, and through a
    selector redeclared by `declare-fun` or `declare-const`. It generates
    nothing for guard (5): its datatype table shares the checker's parse (see
    "How it judges them").

It also audits the parser directly (`soundness/src/literals.rs`, reported as the
pseudo-rule `parser:bv_literal`): every `(_ bv<n> <w>)` over 17 widths from 1 to
`2^40 + 3` and 10 numerals up to `2^100 - 1` must parse to `n mod 2^w`, computed
from the numerals as written. The evaluator judges the parsed term, so a literal
the parser already read wrongly is invisible to it; fix 35's parser half is
only visible to this audit.

`soundness/src/zero_extend.rs` (pseudo-rule `parser:zero_extend`) audits the
`zero_extend` dialect entry the same way: under `Config::clean_dialect()`,
`((_ zero_extend k) d)` over 15 operand widths from 1 to `2^40 + 3` and 9
extensions from 0 to `2^33 + 1` must parse to `d` or `(concat Z d)` built from
the numerals as written, with width `w + k`, and on the closed operands
`(_ bv0 w)`, `(_ bv1 w)` and `(_ bv5 w)` must evaluate to that value at that
width. `--dialect clean` runs the whole battery under the dialect, the
configuration `clean cert verify-external` checks with; the wide-width
generator then exercises the reading at widths of `2^32` and above.

**How it judges them.**

- It runs the real `ProofChecker`, in crash-isolated worker processes.
- It judges every accepted step with an independent three-valued SMT-LIB
  evaluator (`soundness/src/eval.rs`). The evaluator shares no code with
  Carcara's `evaluate`.
- Models are exhaustive over finite free constants (`Bool`, bit-vectors up to
  width 5, three-element uninterpreted sorts), and sampled otherwise.
- Bit-vectors are exact at every width. Widths and bit indices are never cast
  to `u32` unless they fit; a value that would need a `2^w` wider than `2^16`
  (the complement or negation of a nonzero value, a negative residue) is
  unknown, never computed at a truncated width. Sampled
  models include each instance's own constants and their neighbours.
- Uninterpreted functions, division by zero and Hilbert choice are interpreted
  as consistent free functions.
- Non-parametric datatypes are free term algebras (`soundness/src/datatypes.rs`,
  added with C2). A constructor builds a value. Values are equal exactly when
  they are built by the same constructor from equal fields. A selector projects
  its own constructor's field. A selector applied to another constructor's value
  is a consistent free function, because SMT-LIB leaves that value unspecified.
  A tester `(_ is C)` holds exactly of `C` values. A binder that rebinds a
  constructor or selector name is a variable. A constructor or selector that a
  `declare-fun` or `declare-const` redeclares with the same sort is read as
  uninterpreted. The parser refuses that script, and this reading keeps the
  judgement independent of the refusal. The battery's datatype table is built
  (`DtTable::from_terms`) from the term pool the checker's own parse produced,
  so it shares any misreading by the parser and cannot detect one: for example
  the later-declaration-wins resolution of an overload whose argument sorts
  are equal (twin datatypes, or a datatype named like a declared sort), or
  `(as snd (-> P Int))` built from another datatype's `par` symbol `snd`, which
  it read as `P`'s selector exactly as the checker did. The parser now refuses
  both. Those refusals are covered by the rule tests and the
  adapter fixtures, not by the battery. Domains are built from constructors up to
  nesting depth 2, from at most 4 sampled values per non-datatype field, and hold
  at most 64 values. A non-recursive datatype over finite fields gets its
  complete carrier, so its quantifiers are decided.
- A quantifier over an infinite sort is only ever *definitely* false (a
  counterexample in the sample) or unknown, never definitely true.
- A step is reported only when every premise is definitely true and the
  conclusion definitely false.

**What it cannot judge.** Every rule is run, but the judgement is exact only
where the conclusion is decidable on the model. Steps whose truth is unknown
are counted as "accepted" but not "exercised":

- rules over transcendentals;
- `int.log2`/`int.ispow2` at non-positive arguments;
- `re.from_automaton` and `str.replace_re*`;
- parametric datatypes, `match` terms, legacy `is-C` testers (read as
  uninterpreted), sets and relations;
- a step inside an anchor with arguments, `dt_project` included: it is judged
  only through the global judgement of what its subproof exports;
- `@pbbterm` with non-0/1 bits;
- bit-vectors wider than `2^16` whose value would need `2^w` materialized;
- a `forall` over an infinite sort whose conclusion is *true*: the evaluator can
  find a counterexample in the sample but can never confirm the universal. This
  is why `re_unfold_neg` is judged on the capturing instances and on nothing
  else.

Two rules are not reachable at all with Clean's configuration:

- `rare_rewrite`: Clean passes no RARE rule library, so it is always refused.
- `sat_refutation`: no external tools are configured, so it is always refused.

**Commands** (from this directory, with the Trust toolchain on `PATH`):

```bash
targo --unverified test --locked --release -p carcara-soundness   # evaluator unit tests + a bounded battery run
targo --unverified run --locked --release -p carcara-soundness -- --mutants 20000 --seed 11
```

The second command exits 1 when any accepted step has a counterexample and
prints each one with its model. `--fill DEFINITIONS PROOF` prints the term the
checker expects in place of a `; @@fill NAME` hole; it produced the circuit
tests in `carcara/tests/rules/bitvectors.rs`.

Run the second command under Clean's `scripts/heavy_gate.sh`. Memory grows
with `--mutants` and with the rule set, because the crash-isolated workers run
in parallel. Restricted to one rule it is small: `--mutants 20000 --rules
dt_project` peaked at 0.13 GB. Over all rules, `--mutants 2000` peaked at
about 20-21 GB summed over the workers, both with and without C2's datatype
modelling. Single workers reached 10.6-11.5 GB with it and 7.1-8.8 GB without,
which does not settle whether the modelling raises the per-worker peak (measured
in review, 2026-10-01). The all-rule `--mutants 20000` run needs more than that,
so size its reservation from `scripts/heavy_gate.sh peaks`, not from older labels.
The all-rule `--mutants 200 --seed 11` run can peak near 20 GB however it is
launched. On 2026-10-02 three runs of one built binary
(`$CARGO_TARGET_DIR/release/carcara-soundness`, in review) peaked at 17.23,
0.50 and 19.69 GB, this lane's two runs of the binary built from fixes 39 and
40 at 16.58 and 16.25 GB, and the day's other runs of that command spread from
about 0.5 to 21.2 GB, under `targo run` and as the binary alike. (A first reading
here, that `targo run` cost 19.3-19.6 GB and the built binary 0.52-0.59 GB,
rested on too few runs: the peak moves from run to run, probably with how the
work falls to the long-lived workers, which was not measured.) Size the
reservation from `scripts/heavy_gate.sh peaks` for the label class, never from
a low run. Building first (`targo --unverified build --locked --release -p
carcara-soundness`) only keeps the compile out of that reservation.

No Clean gate leg runs these vendored suites or the battery:
`scripts/check_lint_coverage.py` records the vendored crates as run by no leg.
The clean-auto `carcara_verify` tests, which include the adapter fixtures
above, run only when an AY move is qualified
(`data/ay_consumer_qualification.json`). A regression of a fix here, `dt_project`
and its parser guards included, and the problem reading of fixes 36 to 40, is
caught only by running these commands.


### What is fail-closed rather than fixed

- `re_kleene_star_unfold_pos` has no admissible instance left, and
  `re_concat_unfold_pos` only the one the premise determines (fix 32). Four
  upstream rule-test expectations were flipped to `false` for this. It is a
  deliberate completeness loss; the redesign the rules need is in section 30 of
  the upstream report.
- Fix 13 refuses an anchor value that mentions a name the same anchor binds.
- Fix 30's `is_syntactically_nonnegative` admits only non-negative numerals,
  `str.len`, and sums and products of those.
- Fix 35: `evaluate` produces no value for a bit-vector wider than `2^16`, so a
  step that needs one is refused. Clean's own certificate front end already
  refuses decimal literals wider than 16,384 bits.
- A step that would expand bit-vectors into more than 2^18 bits is refused
  ("Bit-vector expansion has a resource budget"): comparisons and bitwise
  operations of operands wider than 131,072 bits, multiplications wider than
  511 bits, divisions wider than 255 bits, n-ary steps whose operands' bits
  (spelled out or not) sum past it, `poly_simp` and `aci_simp` steps whose
  products, flattenings or reductions modulo `2^w` would (charged in words,
  2^24 a step: a monomial of degree 4,062 on both sides, a flattening of a
  chain of 5,792 sums), `qnt_cnf` steps whose conjunctive normal form would
  (19 disjoined conjunctions of two are admitted, 20 are not), `bfun_elim`
  steps whose instances would
  (a quantifier over 19 Booleans, over 17 whose body mentions them all, or over
  14 whose body is an `or` of the 14 and 882 constants), string-rule steps whose flattenings would visit more than
  2^24 terms (`concat_eq` over `(= n23 n23)`, two flattenings of a doubled
  concatenation 23 deep), `evaluate` steps whose numbers would (in words: 27
  nested squarings of 3), and linear arithmetic steps that visit more than 2^24
  terms. No trust-cg certificate comes within a fifteenth of it.
- A `bfun_elim` step over a quantifier whose body rebinds one of its Boolean
  variables with a `let` or `match`, or binds one twice in a binder, is refused:
  upstream's instantiation renames the bound variable, at a cost no charge here
  bounds.
- A term or sort written more than 16,384 deep, or more than 2^18 deep as built
  from definitions, is refused ("Terms nest at most 2^18 deep"), and so is a
  `nary_elim` step over more than 2^18 arguments, whose expansion no such term
  can be. The deepest trust-cg certificate is 8,585 deep.
- Fixes 36 to 40 refuse a problem where a definition would be captured by a
  binder other than a `define-fun` parameter, a problem with `push`, `pop`,
  `reset`, `reset-assertions`, `define-fun-rec`, `define-funs-rec` or a
  command the parser does not read, any command that changes the problem
  after its query ends, a problem that declares or defines a name or sort
  twice or under a built-in's name, a number where SMT-LIB reads a symbol in
  scope, and white space other than SMT-LIB's (see "Fixes 36 to 40" for why
  each is a refusal).
- The crashes on malformed steps this list used to name, the `todo!()` in
  `la_mult_sign` and the index-out-of-bounds panic on empty-clause `pbblast`
  steps, are refusals now, with the rest of their class (see "Malformed steps
  are refused, not a panic"). The battery still runs the checker in
  crash-isolated workers and counts any panic.

## Integration notes

- **The adapter parses under `Config::clean_dialect()`.** The clean-auto
  adapter (`carcara_verify/pb_widths.rs`) parses every problem and certificate
  under the configuration this file's `### Dialect:` entries state, and its
  tests hold that list to them
  (`the_dialect_section_lists_exactly_the_clean_dialect_options`).

- **Trust patches the old git URL.** Trust's root `Cargo.toml` patches
  `https://github.com/ufmg-smite/carcara` to its own vendored copy of the older
  rev `fecb4224` (`vendor/carcara_1_1_0`). That `[patch]` does not apply to a
  path dependency: a Trust build whose `first-party/clean` gitlink names this
  tree compiles this directory.
- **The offline config is stale.** `.cargo/config.offline.toml` still names a
  `fecb4224` git source for Carcara. A path dependency needs no source
  replacement.

### Versioned checker capability: `bv_reconstruct_v1`

The wire rule `bv_reconstruct_v1` checks the ordered unit `(= packed word)`
without premises, arguments or discharged assumptions. It is available only
through `checker::Config::with_bv_reconstruct_v1()`; neither default configuration,
the old `clean_dialect()` nor the offset-spine opt-in grants it. The production
`clean cert verify-external` adapter selects this capability explicitly. Upstream
and older Clean readers reject the unknown rule. This is a new checked intrinsic,
not a relabeling of a bit-blast or polynomial proof.

The actual parsed operands must have the same cached BV sort of width 1..128.
The word is opaque and compared by pool identity, never by recursively comparing
or inspecting its body. A borrowed iterative inspection follows binary builtin
`bvor`, `bvshl` with a canonical same-width literal below the operand width,
indexed unary `zero_extend`, and leaf indexed `extract` from that identical word.
Indices, literals, arities, operand/result widths and Boolean equality sort are
checked from actual terms. Extract destination positions must equal their source
positions. Propagated intermediate-width boundaries prevent a claimed bit from
being truncated by a narrow shift. A fixed 128-entry bit occupancy array admits
each source position exactly once and requires complete full-width coverage.
Canonical zero leaves contribute no bits. The bare full-width word, a full-width
extract, and zero extension by zero are supported. Aliases require ordinary
checked congruence/transitivity/source proofs outside this rule.

Clean's existing parser contract remains in force: it reads `zero_extend(k,t)`
as `(concat 0_k t)` for positive k and as `t` for k=0. The inspector independently
checks exactly that zero-prefix concat representation as an extension; general
concat is refused. Consequently structural limits apply to the actual parsed
semantic tree, where a zero-prefix concat counts as one extension and its checked
prefix is metadata. Erased zero extensions do not consume tree occurrences or
depth. Native/raw inspectors can refuse a larger raw spelling that this existing
parser makes smaller; that representation difference is disclosed and tested,
not a grant to trust a producer's node count. Non-erased OR/shift controls hold
the consumer's own precise bounds independently.

Each attempt uses one fixed 524,288-work and 16,384-byte private-state allowance,
including failures and deadline refusals, with no reset/fallback. Fixed header
and stack admission precedes AST reads. At most 2,048 semantic occurrences and
depth 256 are inspected with one 257-slot borrowed stack; shift amount literals
count as occurrences. Each occurrence reserves 128 work units plus its deadline
poll, at most 129 total occupancy tests cost eight units each, and the 4,096-unit
header reserve bounds state initialization. This is below the fixed allowance;
stack/occupancy state fits 16 KiB. No private heap, maps, arbitrary integer clones,
intermediate terms, SAT or polynomial solver are used. Existing proof admission,
expensive-BV and promotion policies remain unchanged. The separate finite-model
battery dialect is `clean-bv-reconstruct-v1`; the old dialect stays unchanged.

### Dialect: typed unary array lambdas (`array_lambda_dialect`, `arrays_lambda`)

Clean's existing parser/checker `Config::clean_dialect()` enables this extension;
the default/upstream configuration retains ordinary function lambdas and rejects
the `arrays_lambda` rule. This is a Clean dialect capability, not upstream Alethe
parity or a proved-kernel claim.

`Binder::ArrayLambda` is distinct from `Binder::Lambda`. Its one bound index has
its actual parsed domain sort and its body has the actual range sort; the pool
computes `Array(domain, range)`, never a Function/Array sort equivalence. Before
one outer term is parsed, a finite constructor-unification pass over immutable
native lexer tokens derives lambda-role hints by exact token position. It reads
real declaration sorts and lexical binder/parallel-let identities; equality
orientation, select/store, declared parameters/results, ITE and match-result
constraints propagate through the same graph. Native sort syntax is read by the
existing sort parser under an input-cursor restoration guard. The ordinary typed
parser independently validates all of it. Genuine Function constraints remain
Function; incompatible uses refuse. Unconstrained lambdas retain their existing
Function interpretation, including an unconstrained nested lambda range. No new
CLI flag, source assumption, default/epsilon axiom or reset budget is introduced.
The pass and actual parse share the original deadline and written-depth limits.

`arrays_lambda` checks only a unit equality
`(= (select (lambda ((x I)) body) index) result)`, with no premises or arguments.
The binder must be the typed ArrayLambda, index sort exactly `I`, and read/result
sorts exactly the body range. Existing capture-avoiding `Substitution::single`
and `apply` reconstruct the body with the actual index; alpha equivalence checks
the result. A reverse equality uses the standard `symm` rule. Function application
continues to use `beta_equiv`; a same-spelled declared function cannot act as the
new binder or select operator. This rule supplies no array-default fact.

Affected consumers: AST sort computation/printing, the parser's typed binder
construction and role pass, generic binder substitution/free variables, and the
non-quantifier branch of Boolean-function elimination. The Eunoia translator had
no faithful lambda representation and used a TODO `exists` spelling. Both function
and array lambda now retain explicit unsupported DATA; the existing fallible
Eunoia printer propagates an Unsupported I/O error recursively instead of emitting
that invented formula. This changes no Clean kernel/Lean proof authority.
