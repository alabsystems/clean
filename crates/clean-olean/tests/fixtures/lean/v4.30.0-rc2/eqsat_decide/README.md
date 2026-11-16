# eqsat_decide: decision procedures for trust-cg's rule statements (PKG-U6)

The `eqsat_rules` family states what a trust-cg e-graph rewrite rule means,
`EqsatRule.Sound <rule literal> <type>`, and proves the rules of the
hand-written rule set with one lemma each. A rule that a search finds gets no
lemma. This family holds decision procedures instead: each is a function
`Rule → STy → Bool` with one soundness theorem, and the proof of a discovered
rule is that theorem applied to the rule's literal and to a proof that the
procedure answers `true`. That last proof is `Eq.refl true`, so the kernel
accepts it only by evaluating the procedure on the literal. No tactic, no
solver and no elaborator runs per rule, and a procedure that is wrong has no
soundness theorem.

The vocabulary (`EqsatRule.lean`) and the proof helpers (`EqsatBasics.lean`)
are the `eqsat_rules` family's, taken with `from eqsat_rules` lines in
`ORDER`. This family holds no copy and changes neither: the gate compares the
closure digest of `EqsatRule.Sound` on its own replayed environment with the
pin in `crates/clean-olean/tests/eqsat_rules.rs`.

## Modules

| Module | What it holds |
|---|---|
| `EqsatResidue` | `Pat.evalR`, a pattern evaluated on bare residues; `evalR_agrees`, what each of its outcomes says of `EqsatRule.Pat.eval`; `checkR`, the test of one assignment, and `checkR_sound` |
| `EqsatExhaust` | `exhaust8`, which runs `checkR` on every assignment at `bool`, `i8` and `u8` and answers `false` at every other type; `exhaust8_sound : exhaust8 r T = true → Sound r T`; `exhaust8_defined` and `exhaust8_satisfiable`; `rflTrue` |
| `EqsatDecideControls` | rules proved by `exhaust8_sound _ _ rflTrue`, and rules on which `exhaust8 … = false`, each with the reason (the module's header has the table) |

## What is proved, and how a rule is proved with it

```lean
theorem exhaust8_sound (r : Rule) (T : STy) (h : exhaust8 r T = true) : Sound r T
theorem exhaust8_defined (r : Rule) (T : STy) (h : exhaust8 r T = true) : Defined r T
theorem exhaust8_satisfiable (r : Rule) (T : STy) (h : exhaust8 r T = true) : Satisfiable r T
theorem rflTrue : true = true
```

`Sound` and `Satisfiable` are the `eqsat_rules` family's. `Defined r T`
(`EqsatExhaust.lean`) says the rule says something at `T`: at every admitted
pointer width some admitted assignment satisfies the side conditions and both
sides are one common value there.

`exhaust8_sound` has no other hypothesis. The proof of
`EqsatRule.Sound <literal> <type>` for a rule a search found is the closed
term

```
EqsatDecide.exhaust8_sound <literal> <type> EqsatDecide.rflTrue
```

It has that type only if `exhaust8 <literal> <type>` and `true` are one term
up to evaluation, so the kernel accepts it only by evaluating the procedure on
the literal. The term names two constants of this family
(`EqsatDecide.exhaust8_sound` and `EqsatDecide.rflTrue`) and no universe
level; the literal and the type are constructors of `EqsatRule` and `SemR`,
and `exhaust8` appears only in the term's type. Both constants are in
`EqsatExhaust`, as are `exhaust8_satisfiable` and `exhaust8_defined`, so a
bundle that proves rules takes its roots from that module and does not need
the controls module.

`exhaust8 r T` answers `true` only when all four hold:

| Test | What it requires | Definition |
|---|---|---|
| type | `T` is `i8`, `u8` or `bool`. At every other type the answer is `false` before the rule is read (`exhaust8_run`), so a term cannot be reused at another width: `exhaust8 r (.int .u64)` and `true` are two terms | `exhaust8` |
| size | the rule has at most 1,024 assignments (`maxAssignments`): a variable of sort `t` at an integer type counts 256, every other variable 2. That is one 8-bit variable with up to two Booleans, or up to ten Booleans. Two 8-bit variables are 65,536 and are answered `false` at once | `small`, `space` |
| a defined instance | some assignment satisfies the side conditions and gives the left side a value. A rule is `Sound` whatever its sides are when no assignment satisfies its conditions, and a `refines` rule is `Sound` whatever its right side is when its left side is undefined behaviour on every assignment that does; this route admits neither. `exhaust8_defined` gives `Defined r T` from the same `true`, and `exhaust8_satisfiable` gives `EqsatRule.Satisfiable r T`, so a rule with a `where` clause gets that statement with the same proof argument | `live` |
| every assignment | each assignment fails the side conditions, or its two sides stand as the direction says and neither is `bad` (`checkR`, below) | `sweep` |

**`false` is not a refutation.** It says the rule is not proved by this
procedure: the type is not covered, the rule is too large, its conditions are
never met, its left side is never a value, a side is not a term, or some
assignment fails. The controls hold five rules that are `Sound` and on which
`exhaust8` answers `false`: `contradictory` and `contradictoryBeside` (no
assignment meets the conditions), `udivZeroRefines` and `udivZeroRefinesTt`
(`(udiv ?x (const 0))` refined to `(const 7)` and to `true`: the left side is
undefined on every assignment), all four by design, and `twoVars`, for its
size. Only `exhaust8_sound` is claimed; completeness is not stated.

**What `exhaust8` does not check.** It proves `Sound`, and `Sound` reads a
rule's two sides only through SemR's evaluation. That a side is of the sort
the rule's type calls for is the rule parser's business: `Defined` gives one
assignment on which both sides are one common value, and nothing here says
what sort that value has, or that a side evaluates without a type error on an
assignment the side conditions exclude.

`sweep_sound`, `live_defined` and `live_satisfiable` are stated at any
instance type, width
and modulus (`WidthOf pb T w`, `m = modulus w`); `exhaust8` uses them at
width 8 and modulus 256, which are the width and modulus of `i8` and `u8`
under every pointer width.

## What stays unproved

* **Every type above eight bits.** `i16` to `i128`, `u16` to `u128`, `isize`
  and `usize`: `exhaust8` answers `false`. A rule that holds at every width is
  proved here at `i8` and `u8` only, and that proof says nothing of another
  width: `(and ?x (const 255)) = ?x` is proved at `u8` and is false at `u16`
  (`EqsatDecideControls.and255_not_sound_u16`).
* **Two or more variables of the instance type at `i8` or `u8`**, and so any
  rule with three of them: 65,536 assignments or more, over the size limit,
  `false` at once. The budget section says what the enumeration would cost.
  More than two Booleans beside one 8-bit variable, or more than ten Booleans,
  are over the limit too.
* **Refutations.** No theorem here says a rule is false. `exhaust8 … = false`
  is not one.
* **Anything about the search.** Which rules are proposed, and whether a rule
  the procedure refuses is true, is outside this family.

## No axiom and no trusted code

Every declaration of the family replays from the empty environment through
Clean's reference entry with a closure inside `propext`, `Classical.choice`
and `Quot.sound`. `exhaust8` is a definition, not a checker anyone trusts: the
kernel accepts `exhaust8_sound` only as a proof about the unchanged
`EqsatRule.Sound`, so a procedure that answered `true` on a false rule would
have no soundness theorem and the family would not compile. Nothing in
`EqsatRule.lean` or in the `eqsat_rules` family changed, and the gate compares
the closure digest of `EqsatRule.Sound` with that family's pin. What is
trusted is what was trusted before: the kernel, and the reading of
`EqsatRule.Sound`.

## What `EqsatResidue` proves

`Pat.evalR int w m env p` evaluates pattern `p` on an assignment of residue
values (`RV`: a residue or a `Bool`). `int` says the instance type is an
integer type, `w` is its width and `m` its modulus. Its outcome (`RR`) is one
of three, and `Agrees` says what each claims of SemR's outcome:

| `evalR` answers | It claims of `Pat.eval` |
|---|---|
| `ok v` | it is the value `v` stands for at the instance type, and `v` is well formed there (a residue below the modulus at an integer type, never a residue at `bool`) |
| `ub` | it is undefined behaviour |
| `bad` | nothing |

`evalR_agrees` is that claim for every pattern, at every instance type `T`,
width `w` with `WidthOf pb T w`, modulus `m = modulus w` and well-formed
assignment. It covers every pattern form and every operator of SemR's
`BinOp`, `UnOp` and `ICmpOp`, the ones outside the rule grammar included
(division, remainder and the shifts go through SemR's `intBin` and can answer
`ub`).

The evaluator answers `bad` wherever it does not follow SemR: an unbound
variable, `(const INT)` at `bool`, an operand of the wrong sort, an operator
the sort does not admit, and an operator result that is not below the modulus.
That last test is run, never assumed, for the rotations, the bit counts,
`bswap` and `bitreverse`; `add sub mul and or xor neg not` reduce modulo `m` by
their form and skip it.

`checkR d lhs rhs cs int w m env` tests one assignment of a rule given by its
direction, two sides and side conditions (a procedure takes the rule apart
once, not once per assignment), and `checkR_sound` is the body of
`EqsatRule.Sound` at that assignment: from `checkR … = true`, under
`CondsHold`, the two sides stand as the direction says (`Holds`) in SemR's own
evaluation. On an assignment that meets the side conditions:

* an `equiv` rule needs one common value on both sides;
* a `refines` rule needs that, or undefined behaviour on the left beside a
  right side that is a value or undefined behaviour;
* any other outcome answers `false`: `bad` on either side under either
  direction (`holdsR_bad_left`, `holdsR_bad_right`), undefined behaviour on
  the right beside a value, undefined behaviour on the left of an `equiv`
  rule.

This is `Sound`'s reading but for one case, where `checkR` is the stricter:
under `refines`, beside a left side that is undefined behaviour, `Sound` asks
nothing of the right side, and `checkR` refuses one that is `bad`. A side
whose outcome is `bad` therefore passes on no assignment that meets the
conditions. (`ub` and `bad` are outcomes of a whole side: as in SemR, the
first operand that is undefined behaviour is the outcome, whatever the
operands after it are.)

A side condition is decided in the one direction that cannot admit a false
rule: `condsR` is `true` wherever `CondsHold` holds (`condsR_of_condsHold`),
and an assignment where it is `false` is skipped. `EqsatExhaust` proves the
other direction for its `live` test (`condsHold_of_condsR`), so `condsR`
decides the conditions exactly.

## Cost, and the budget (U6-BUDGET)

The kernel evaluates `checkR` once per assignment, so every definition on
that path is one recursor application with closed minor premises: no matcher,
no `brecOn`, no string, and the modulus is a parameter so that it is a literal
at each use.

### What the gate measures

The gate has the entry accept `exhaust8_sound <literal> <type> rflTrue` for
`Sound <literal> <type>` at a budget of 200,000 for the replay and for each
check, and prints for each rule the time of that check and the smallest
heartbeat limit under which the same check passes (bisection with
`Environment::check_decl_readonly_with_heartbeat`; every refusal below the
limit must name heartbeats). Its run on the build host:

| Rule | Type | Assignments | Smallest passing limit | Time of the check |
|---|---|---|---|---|
| `(const 0) = (const 0)` | `u8` | 1 | 68 | 0.2 ms |
| `(select ?c ?x ?x) = ?x` | `bool` | 4 | 129 | 0.8 ms |
| `(band ?p (bor ?p ?q)) = ?p` | `bool` | 4 | 153 | 0.8 ms |
| `(and ?x (const 255)) = ?x` | `u8`, `i8` | 256 | 4,682 | 22 to 24 ms |
| `(rotl ?n ?n) = ?n where ?n == 0 mod width` | `u8` | 256 | 5,131 | 16 ms |
| `(and ?x (not ?x)) = (const 0)` | `u8`, `i8` | 256 | 5,461 | 25 ms |
| `(select ?c ?x ?x) = ?x` | `u8`, `i8` | 512 | 8,764 | 56 to 60 ms |
| `(udiv ?x ?x)` refines to `(const 1)` | `u8`, `i8` | 256 | 10,840 | 42 ms |
| `(and ?c (sub ?c 1)) = 0 where (pow2 ?c)` | `u8` | 256 | 19,888 | 42 ms |
| `(select ?p (select ?q ?x ?x) ?x) = ?x` | `u8` | 1,024 | 21,573 | 183 ms |
| `(ctpop (bitreverse (bswap ?x))) = (ctpop ?x)` | `u8` | 256 | 54,664 | 149 ms |
| `(select ?p (select ?q H H) H) = (ctpop ?x)`, `H` the left side of the row above | `u8` | 1,024 | 88,993 | 365 ms |

The heartbeat figures are exact and the same on every run; the times are one
run's. The sixteen checks together cost 250,093 heartbeats. The family
(768 declarations of the five audited modules, 2,681 with their cone) replays
from the empty environment under the same 200,000 in about 3.0 s.

Refusals are cheap. The record term for each of six rules over the size limit
is refused, with `exhaust8 … = false` accepted and `= true` refused beside it,
in 23 ms for all eighteen checks.

### What step 0 measured

Before `exhaust8` was written, a prototype of the enumeration over this
family's `checkR`, with no size limit and no `live` test, was measured the
same way on `exhaust8 <literal> <type> = true` against `Eq.refl true`. The
harness is not in the tree, so these are not gate figures. The two-variable
rows are what the size limit now answers `false` on without enumerating. The
limit is the smallest `maxHeartbeats` at which the check passes; time is wall
time on the build host.

| Rule | Type | Assignments | Smallest passing limit | Time |
|---|---|---|---|---|
| `(band ?p (bor ?p ?q)) = ?p` | `bool` | 4 | 115 | under 1 ms |
| `(and ?x (const 255)) = ?x` | `u8` | 256 | 4,660 | 20 ms |
| `(and ?x (not ?x)) = (const 0)` | `u8`, `i8` | 256 | 5,441 | 24 ms |
| `(select ?p ?x ?x) = ?x` | `u8` | 512 | 8,724 | 56 ms |
| `(icmp.ult ?x (const 0)) = false` | `u8` | 256 | 9,268 | 30 ms |
| `(bitreverse (bitreverse ?x)) = ?x` | `u8` | 256 | 37,478 | 103 ms |
| `(ctpop (bitreverse (bswap ?x))) = (ctpop ?x)` | `u8` | 256 | 54,645 | 141 ms |
| `(rotl ?x (const ?n)) = ?x where ?n == 0 mod width` | `u8` | 65,536 | between 1,212,417 and 1,214,464 | 4.5 s |
| `(and ?x (or ?x ?y)) = ?x` | `u8` | 65,536 | between 1,572,865 and 1,574,912 | 9.5 s |
| `(sub (add ?x ?y) ?y) = ?x` | `u8` | 65,536 | between 1,572,865 and 1,574,912 | 9.2 s |
| `(rotl (rotr ?x ?y) ?y) = ?x` | `u8` | 65,536 | between 2,228,225 and 2,232,320 | 11.1 s |

The last row is refused at the entry's default of 2,000,000.

A false rule costs little: `exhaust8 … = false` for `(and ?x (const 254)) =
?x` passes at 66 and for the two-variable `(sub (add ?x ?y) ?x) = ?x` at 92,
and `= true` for a false rule is refused as a type mismatch. At a type the
procedure does not cover (`u16`), `= false` passes at 7.

**The budget is 200,000 heartbeats per check.** Under it:

* every rule the gate proves passes: the dearest one-variable rule (three bit
  operators, 54,664) with 3.6 times its cost to spare, and the dearest rule at
  the size limit (the same operators in each arm of two selects, 88,993) with
  2.2 times;
* a check that runs out is refused after about a second (step 0 measured `(and
  ?x (or ?x ?y)) = ?x`, refused with `HeartbeatExceeded` at 200,000 in 1,126 ms),
  so thirty rules at `i8` and `u8` cost about a minute even if every check ran
  out, and 2 to 9 s at the measured costs;
* **a rule with two integer variables is out of scope**: its enumeration
  needs 1.2 to 2.3 million heartbeats and 4 to 11 s, so thirty of them at two
  types would take 4 to 11 minutes on every registry build. `exhaust8` answers
  `false` on such a rule before enumerating (`small`), so the record term is
  refused at once as a type mismatch and not after a second as a timeout; a
  caller that counts the assignments first need not ask. The gate checks that
  the budget is what stops the enumeration: `sweep` of `(and ?x (or ?x ?y)) =
  ?x`, asked for directly, is refused with `HeartbeatExceeded` at 200,000
  (after about a second; the gate prints the time).

The size limit is 1,024 assignments. Cost is not proportional to the number
of assignments. On 256 assignments the rules the gate proves cost 18 to 214
heartbeats an assignment (4,682 to 54,664). At the limit `selectNested` is
proved with 21,573 (21 an assignment) and `bitsHeavyNested`, whose two
selects have the dearest one-variable left side in each of their three arms,
with 88,993 (87 an assignment). So the dearest rule measured at the limit
passes with 2.2 times its cost to spare, and no rule at the limit was
measured to run out. If one does, it is `timed-out`, which admits nothing. A
limit of 2,048 was not measured: 1,024 was chosen as the size that keeps two
Booleans beside an 8-bit variable (at 512 such a rule would be answered
`false` unasked), not because a larger one was shown to fail. Raising it is a
change to `maxAssignments`, to be made with a measured rule at the new size.

The entry has one `maxHeartbeats` for the replay of the bundle and for each
closed-term check, so the budget must also cover the replay. Step 0 measured
the smallest budget for `EqsatRule`, `EqsatBasics` and `EqsatResidue` at 6,964
(the dearest declaration is `EqsatRule.bits_cases._proof_1_18`), and for the
whole `eqsat_rules` family at 11,549 (`EqsatInt.mul_255_neg_i8_i8._proof_1_28`).
It was not measured again with `EqsatExhaust`. The controls module holds
theorems proved by the procedure, so its replay needs what the dearest of them
needs, 88,993 or a little more; the gate replays all five modules at 200,000.
A bundle that takes only the cone of `exhaust8_sound` and `rflTrue` does not
replay the controls.

An enumeration is written as one counter of 256 per variable, never one
counter over all assignments: Clean's kernel leaves a `Nat.rec` with a
constant motive and a step that uses its induction hypothesis unreduced when
its count is a literal of 65,536 or more
(`native_closed_fold_grind_stuck`, `crates/clean-kernel/src/tc/reduction/nat.rs`).
Measured: such a fold over 65,535 is accepted in 200 ms, and over 65,536 it is
refused at once as a type mismatch. A procedure for 16-bit types has to
respect that.

A check refused for lack of budget names heartbeats: each of the 139 refusals
below a passing limit in step 0 did, and the gate's bisection fails on one
that does not. A refusal that names a type mismatch is a wrong claim, a rule
`exhaust8` does not admit, or the guard above; the gate counts a forged term
as refused for the claim only when the entry's refusal is that one
(`TypeMismatch`), never one for lack of budget, depth or memory. Neither kind
is a refutation,
and neither is a passing check of `exhaust8 … = false`: a caller decides
`refuted` by exhibiting an assignment, outside this family.

Written the plain way (`match`, structural recursion), the same evaluator cost
5.5 times the heartbeats: 29,824 against 5,441 for the one-variable rule.

Two or three integer variables are within reach of a different procedure, not
of a larger budget. A prototype that packs the 256 values of the innermost
variable into one `Nat` of 256 sixteen-bit lanes, for `add sub and or xor neg
not`, variables and literals, passes `(and ?x (or ?x ?y)) = ?x` at 2,338
heartbeats in 12 ms and `(sub (add ?x ?y) ?y) = ?x` at 3,139 in 14 ms. It has
no soundness theorem; it is a procedure of its own, to be added beside
`exhaust8` with its own proof.

## Compiling

The pinned Lean is v4.30.0-rc2. `compiled_fixture_dir("eqsat_decide")`
(`clean_olean::test_support`) compiles `ORDER` in a cache directory; by hand,
in a scratch directory holding `semr/SemR.lean`, `eqsat_rules/EqsatRule.lean`,
`eqsat_rules/EqsatBasics.lean` and this family's `.lean` files:

```sh
L=~/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean
for m in SemR EqsatRule EqsatBasics EqsatResidue EqsatExhaust EqsatDecideControls; do
    LEAN_PATH=$PWD $L --root . -o $m.olean $m.lean || break
done
```

No `sorry`, `native_decide`, `bv_decide`, `Lean.ofReduceBool` or new axiom:
every closure is within `propext`, `Classical.choice` and `Quot.sound`.
`crates/clean-olean/tests/eqsat_decide.rs` replays every declaration of the
family and of the two modules it takes from `eqsat_rules` from the empty
environment through Clean's reference entry, compares the closure digest of
`EqsatRule.Sound` with the `eqsat_rules` gate's pin, requires every theorem of
the three modules by name with its statement pinned, has the kernel evaluate
the evaluator on closed terms, each accepted outcome beside a forged one that
is refused (16 outcomes of `checkR` and `Pat.evalR`, and one row per operator
in `crates/clean-olean/tests/eqsat_decide/operators.rs`, 39 rows: the outcome
beside the one a neighbouring operator, the other signedness, the unreduced
result or a lost refusal would give), and runs the procedure controls
(`crates/clean-olean/tests/eqsat_decide/procedure.rs`) under the budget: the
record term accepted for sixteen rule and type pairs, and refused for the
claim on a false rule, at each of the ten other integer types, for a
refines-only rule offered as `equiv`, over the size limit, for a rule with
contradictory side conditions, and for a `refines` rule whose left side is
undefined on every assignment (72 refused terms). The three counts are
asserted, so a control removed is an edit of a number:

```sh
targo --unverified test --locked --profile authority -p clean-olean \
    --test eqsat_decide -- --include-ignored --nocapture
```

A module added to `ORDER` is added to the test's `MODULES` (the test compares
the two).

`STATEMENTS` holds one `name digest` row per theorem of the three modules, in
the `eqsat_rules` family's format: SHA-256 over the theorem's type as the kernel
holds it and the closure digest of every constant the type names. It moves
when a statement is edited and when the meaning of anything it mentions
changes (an edit to `evalR` moves every row that mentions it), and not when a
proof does. The row of `EqsatDecide.exhaust8_sound` is the pin of what the
soundness theorem states: it moves with `exhaust8`, with `EqsatRule.Sound` and
with anything either reaches. Re-pin a row only with the reason in the commit
message.
