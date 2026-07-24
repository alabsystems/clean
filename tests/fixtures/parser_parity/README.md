# parser parse-parity fixture

Ground truth for the **parse-parity harness**
(`crates/clean-parser/tests/parse_parity.rs`), the permanent guard specified in
`docs/plans/PARSER_ELAB_DROPIN_AUDIT_2026-07-08.md`
§6. Same discipline as the kernel's
[`carrier_v4_30`](../carrier_v4_30/) fixture: a checked-in Lean-oracle table,
replayed row-by-row, exact-match, with a pinned regeneration recipe.

| file | role |
|---|---|
| `ground_truth.tsv` | 228 probes: `family · input · expected_kind · lean_tree · lean_value` |
| `gen_ground_truth.lean` | regeneration recipe (pinned toolchain oracle queries) |
| `README.md` | this file |

**Oracle:** `leanprover/lean4 v4.30.0-rc2` (commit `3dc1a088`). Probes captured
2026-07-08 with the pinned oracle (8 verified family specs; regeneration
recipe: `gen_ground_truth.lean`).

## What the harness measures

For each row the test runs `clean_parser::parse_expr(input)` and classifies:

- **MATCH** — clean parses and its tree structurally corresponds to Lean's
  (the renderer's skeleton equals the row's `lean_tree`).
- **LOUD** — clean returns a `ParseError` where Lean parses. A loud gap is the
  *acceptable* outcome for not-yet-implemented syntax (a loud gap ≫ a silent
  misparse — task-C guidance).
- **SILENT-DIVERGENT** — clean parses a tree that disagrees with Lean, **or**
  clean accepts input Lean rejects at parse time (over-acceptance). This is the
  failure class the existing phase-1/PutnamBench gates (which only score
  `parse == Ok`) are structurally blind to.

**The test passes iff SILENT-DIVERGENT = 0 modulo the pinned allowlist.** It
prints a per-family scoreboard so coverage progress is measurable as Brick 3
lands.

## Scoreboard at HEAD (post-Brick-3 surface expansion)

```
family      match   loud  divergent  total
bigop           5      1         15     21
getelem        25      1          2     28
monadic        31      3          0     34
brace          25      1          2     28
binder         38      0          2     40
lowprec        24      5          0     29
rewrite        13      3          5     21
freqsweep      24      1          2     27
TOTAL         185     15         28    228
```

Brick 3 (operator/notation coverage) originally took MATCH from 63 → 181 and
the pinned allowlist from 42 → 20. Later compatibility rungs deliberately
expanded the Mathlib surface with `⨆`/`⨅`, separator set-builders, and `×ˢ`;
those eight exact core-Lean rejections are pinned as intentional superset rows,
bringing the allowlist to 28. Array slicing is now a MATCH: the pinned Lean
oracle expands `arr[0:2]` to `Array.toSubarray arr 0 2` (confirmed against the
v4.30.0-rc2 toolchain), replacing the fixture's former prose placeholder.
The remaining divergences are documented Mathlib-surface or parser/elaborator
boundary choices, including `∑`/`∏` families, set-builders, `∃!`, `×ˢ`, the
pattern-fun global-name rule, and postfix-whitespace leniency.

### Fixture normalization corrections (2026-07-08, Brick 3)

20 rows' `lean_tree` values were corrected during Brick 3 — these were
**authoring defects in the fixture**, not divergence paper-overs:

- rows whose `lean_tree` held prose placeholders ("`loud gap — clean rejects;
  Lean parse skeleton`", "`parse-ok in Lean; elab err …`") instead of a real
  skeleton — unreachable-as-MATCH by construction; replaced with the skeleton
  derived from the family specs' verified Lean parses;
- rows authored against the wrong renderer grammar: compound projection bases
  render `(. base field)` (never `base.field`), and ascriptions in the input
  are kept (`(3 : Nat)` → `(: 3 Nat)`).

Every corrected value was cross-checked against the pinned-oracle probe rows
(grouping, head constant, value).

### RHS unit-thunk regeneration (2026-07-08, Brick 3 §3(a))

The 23 rows whose skeleton contains a lazy/seq head (`Seq.seq`,
`SeqLeft.seqLeft`, `SeqRight.seqRight`, `HAndThen.hAndThen`,
`HOrElse.hOrElse`) were regenerated when clean's parser gained the
Lean-faithful RHS unit-thunk desugar: each head's second argument is now the
thunk `fun _ : Unit => rhs`, so the skeleton pins
`(HAndThen.hAndThen a (fun b))` instead of the former un-thunked
`(HAndThen.hAndThen a b)` (which had treated the thunk as a downstream
macro-expansion artifact). The expected trees were derived mechanically from
the pinned toolchain's own macro text — `Init/Prelude.lean` macro_rules
(`$x <*> $y` → `Seq.seq $x fun _ : Unit => $y`, likewise `<*`/`*>`) and
`Init/Notation.lean:428-449` + `Lean/Elab/Extra.lean:92` `binop_lazy%`
(`f a (fun () => b)`) for `>>`/`<|>` — applied to the previously-verified
skeletons (wrap arg 2 in `(fun …)`; binders stay abstracted per the grammar
above). MATCH/LOUD/DIVERGENT counts are unchanged by the regeneration.

## The `lean_tree` skeleton grammar

`lean_tree` is **not** raw Lean `pp.parens` output — it is a normalized
S-expression that captures the two things parse-parity cares about (head
constants + parenthesization/associativity shape) while abstracting surface
noise the two engines render differently. Clean's `SurfaceExpr` is folded into
the *same* grammar by `parse_parity_support/render.rs`, and comparison is exact
string equality. Grammar:

- **Leaves:** identifiers verbatim (`f`, `Nat.succ`); `Nat` literals verbatim
  (`3`); `#str` / `#char` / `#float` for other literals; `_` for holes; `·` for
  a `(· …)` section variable.
- **Application:** `(head arg …)`, spine-flattened (`(f a) b` ≡ `f a b`) so
  clean's curried `|>`/`<|` desugar matches Lean's flatten-macro.
- **Operators:** the desugared head, prefix — `a + b` → `(HAdd.hAdd a b)`,
  `f <$> a` → `(Functor.map f a)`, `a ▸ b` → `(Eq.rec a b)`, etc. (Clean already
  lowers every infix it supports to this head form.) The five lazy/seq
  operators include Lean's RHS unit-thunk in their desugar, so the second
  argument is a `(fun …)` body: `a >> b` → `(HAndThen.hAndThen a (fun b))`,
  `f <*> x` → `(Seq.seq f (fun x))` (likewise `<* *> <|>`).
- **Binders abstracted:** `fun`/`pi`/`let`/`match` render as a tag + body
  (`(fun BODY)`, `(pi BODY)`, `(match SCRUT n)` with arm-count `n`); binder
  *names/types* and match-arm *bodies* are dropped — the engines disagree on
  binder pretty-printing (`fun x` vs `fun ⦃x⦄`, dropped ascriptions) and the
  interesting divergences live in the operator spine. **Consequence:** binder
  *info* (strict-implicit vs implicit) and pattern-fun arm bodies are not
  verified here; those probes assert only that clean parses the construct
  without fabricating/dropping.
- **`Paren` transparent**; `Ascription` `(: e T)`; `Proj` folds a bare base into
  a dotted name (`Sigma.mk`, `xs.reverse`) else `(. e field)`; struct/anon-ctor
  `(structInst …)` / `(anonymousCtor …)`; opaque tags `#do` `#by` `#calc`
  `#quote` `#istr` for whole-block constructs both engines accept.

For a construct both engines accept and that clean represents with a dedicated
surface node (structInst, `⟨⟩`, pattern-`fun`, `do`/`by`/`calc`), the row pins
clean's structural skeleton (hand-verified to correspond to Lean's parse). The
strong Lean-divergence detection is concentrated on the operator / precedence /
associativity families, where the skeleton is the desugared head spine.

## The ratchet and deliberate surface expansions

The current divergences are pinned in `ALLOWLIST` in
`parse_parity_support/allowlist.rs`, each keyed `(family, input)` and tagged
with a **Brick 3** tag (`B3-bigop-gate`, `B3-setbuilder-gate`, …; the tag
glossary is in the `parse_parity.rs` header). The test ratchets in **both** directions:

- a divergent probe **not** on the allowlist fails the test — a new silent
  misparse or over-acceptance regressed;
- an allowlist entry that is **no longer** divergent fails the test — its brick
  landed, so the entry is stale and must be deleted.

**Normal rule: the allowlist only shrinks.** An entry is removed only by fixing
the parser so its probe flips to MATCH (or LOUD) — never by editing the fixture
to paper over a divergence. A deliberate compatibility-surface expansion may
add exact rows only when the new lowering has its own structural tests and the
core-Lean-vs-Mathlib distinction is documented here; the `⨆`/`⨅`, separator
set-builder, and `×ˢ` rows are that explicit exception.

## Regenerating

1. **Oracle** — run `gen_ground_truth.lean` through the pinned toolchain:
   ```bash
   ~/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean \
     tests/fixtures/parser_parity/gen_ground_truth.lean
   ```
   Each `set_option pp.parens true in #check <input>` yields the fully
   parenthesized parse tree (or a parse error → an `ERROR` row).
2. **Normalize** — fold each oracle tree into the skeleton grammar above and
   write it to the row's `lean_tree`. (The clean side is normalized by the same
   `render.rs`; a row is MATCH when the two skeletons coincide.)
3. Re-run `cargo test -p clean-parser --test parse_parity -- --nocapture` and
   reconcile the scoreboard / allowlist.

The `.mathverse`-style shard rule does not apply here — this fixture is small,
deterministic, and checked in.
