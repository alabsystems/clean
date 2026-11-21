# eqsat_decide: decision procedures for trust-cg's rule statements (PKG-U6, PKG-U6b)

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

## The four procedures

| Procedure | Types | Rules it can prove | How it decides |
|---|---|---|---|
| `exhaust8` | `i8`, `u8`, `bool` | any operator of the rule grammar, side conditions, at most 1,024 assignments (one 8-bit variable) | every assignment, one at a time |
| `exhaust8p` (PKG-U6b) | `i8`, `u8` | at most two variables of the instance type, no side condition, `add sub and or xor neg not`, variables and integer literals | every assignment, 256 at a time: the 256 values of one variable are the lanes of one natural number |
| `bitwiseAll` (PKG-U6b) | each of the twelve integer types | at most eight variables of the instance type, no side condition, `and or xor not`, variables, `(const 0)` and `(const -1)` | one truth table: these operators act on each bit by itself, so the table stands at every width |
| `ringAll` (PKG-U6b) | each of the twelve integer types | any number of variables, each one a side reads of the instance type; no side condition, `add sub mul neg not`, variables and integer literals | both sides normalized as polynomials with integer coefficients; the same polynomial is the same residue at every width |

Each is sound and none is complete: `false` says the rule is not proved by
that procedure, never that the rule is false. A procedure asked about a rule
outside its fragment, or at a type it does not cover, answers `false`. The
sections below are `exhaust8`'s; "The three procedures of PKG-U6b" has the
other three.

## Modules

| Module | What it holds |
|---|---|
| `EqsatResidue` | `Pat.evalR`, a pattern evaluated on bare residues; `evalR_agrees`, what each of its outcomes says of `EqsatRule.Pat.eval`; `checkR`, the test of one assignment, and `checkR_sound` |
| `EqsatExhaust` | `exhaust8`, which runs `checkR` on every assignment at `bool`, `i8` and `u8` and answers `false` at every other type; `exhaust8_sound : exhaust8 r T = true → Sound r T`; `exhaust8_defined` and `exhaust8_satisfiable`; `rflTrue` |
| `EqsatDecideControls` | rules proved by `exhaust8_sound _ _ rflTrue`, and rules on which `exhaust8 … = false`, each with the reason (the module's header has the table) |
| `EqsatPacked` | `exhaust8p` and `exhaust8p_sound : exhaust8p r T = true → Sound r T`; `exhaust8p_defined`, `exhaust8p_satisfiable`; in `EqsatDecide.Packed`, the lane vectors (`pack`, `pack_inj`), the lane evaluator `evalV` and `evalV_lanes`, which says what each of its lanes holds |
| `EqsatPackedControls` | rules proved by `exhaust8p_sound _ _ rflTrue`, rules on which `exhaust8p … = false`, and the lane evaluator on closed terms |
| `EqsatBitwise` | `bitwiseAll` and `bitwiseAll_sound : bitwiseAll r T = true → Sound r T`; `bitwise_sound : bitwise r = true → ∀ t, Sound r (.int t)`; `bitwiseAll_defined`, `bitwiseAll_satisfiable`; in `EqsatDecide.Bitwise`, the one-bit evaluator `evalB` and `frag_eval`, which says that bit `j` of a pattern's residue is `evalB` on bit `j` of each variable |
| `EqsatBitwiseControls` | rules proved by `bitwiseAll_sound _ _ rflTrue` and rules on which `bitwiseAll … = false` |
| `EqsatRing` | `ringAll` and `ringAll_sound : ringAll r T = true → Sound r T`; `ringAll_defined`, `ringAll_satisfiable`; in `EqsatDecide.RingAll`, the normalizer `ringNorm`, `ringPat_norm` (a pattern's polynomial has the pattern's value modulo `2^w`) and `ringRun_sound : ringRun r = true → ∀ t, Sound r (.int t)` |
| `EqsatRingControls` | rules proved by `ringAll_sound _ _ rflTrue` and rules on which `ringAll … = false` |

`EqsatPacked`, `EqsatBitwise` and `EqsatRing` each import `EqsatExhaust` (for
`rflTrue`, `Defined`, `allBelow`, `both` and `guard_true`) and none imports
another. All nine modules load into one environment, so the parts of each
PKG-U6b procedure are in a namespace of its own (`EqsatDecide.Packed`,
`EqsatDecide.Bitwise`, `EqsatDecide.RingAll`); only the procedures and their
theorems are in `EqsatDecide`.

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

By `exhaust8`:

* **Every type above eight bits.** `i16` to `i128`, `u16` to `u128`, `isize`
  and `usize`: `exhaust8` answers `false`. A rule that holds at every width is
  proved by it at `i8` and `u8` only, and that proof says nothing of another
  width: `(and ?x (const 255)) = ?x` is proved at `u8` and is false at `u16`
  (`EqsatDecideControls.and255_not_sound_u16`).
* **Two or more variables of the instance type at `i8` or `u8`**, and so any
  rule with three of them: 65,536 assignments or more, over the size limit,
  `false` at once. The budget section says what the enumeration would cost.
  More than two Booleans beside one 8-bit variable, or more than ten Booleans,
  are over the limit too.

By the family as a whole, with the three procedures of PKG-U6b:

* **Above eight bits, every rule outside the two all-width fragments.** A
  rule is proved at `i16` and wider only if it is bitwise (`and or xor not`,
  0 and -1) or a polynomial identity (`add sub mul neg not`, literals). A
  rule that mixes the two (`(add (and ?x ?y) (or ?x ?y)) = (add ?x ?y)`), a
  division, remainder, shift or rotation, a bit count, `bswap`, `bitreverse`,
  a comparison, a `select`, a Boolean operator, and any rule with a side
  condition are proved at eight bits or not at all. A rule that holds only
  modulo one width's modulus is proved only where that width is eight:
  `(mul ?x (const 256)) = (const 0)` holds at `u8`, `ringAll` answers `false`
  on it there, and `exhaust8` proves it
  (`EqsatRingControls.mul256_sound_u8`).
* **At eight bits, a rule with two variables of the instance type that is
  outside `exhaust8p`'s fragment and outside the two all-width fragments**
  (a division or remainder, a shift, a rotation, a bit count, a comparison,
  a `select`, a side condition, a Boolean variable beside the two, `mul`
  mixed with a bitwise operator), and **a rule with three variables or
  more** outside the two all-width fragments.
* **Refutations.** No theorem here says a rule is false, and no procedure's
  `false` is one.
* **Completeness.** No procedure is proved to answer `true` on every sound
  rule of its fragment. `ringNorm` is not proved to be a normal form.
* **Anything about the search.** Which rules are proposed, which procedure a
  rule is offered to, and whether a rule every procedure refuses is true, is
  outside this family.

## No axiom and no trusted code

Every declaration of the family replays from the empty environment through
Clean's reference entry with a closure inside `propext`, `Classical.choice`
and `Quot.sound`. Each procedure is a definition, not a checker anyone trusts:
the kernel accepts its soundness theorem only as a proof about the unchanged
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
(1,398 declarations of the eleven audited modules, the nine of this family
and the two taken from `eqsat_rules`; 3,877 with their cone) replays from the
empty environment under the same 200,000 in about 4.6 s.

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
needs, 88,993 or a little more; the gate replays all eleven modules at
200,000, the three procedures of PKG-U6b and their controls among them. The
smallest budget at which each of those six modules replays was not measured.
A bundle that takes only the cone of a soundness theorem and `rflTrue` does
not replay the controls.

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

Two integer variables are within reach of a different procedure, not of a
larger budget. Step 0 measured a prototype that packs the 256 values of one
variable into one `Nat` of 256 sixteen-bit lanes, for `add sub and or xor neg
not`, variables and literals: `(and ?x (or ?x ?y)) = ?x` at 2,338 heartbeats
and `(sub (add ?x ?y) ?y) = ?x` at 3,139. That prototype had no soundness
theorem. `exhaust8p` is the same evaluator with one (next section); the gate
measures the two rules at 3,386 and 4,189.

## The three procedures of PKG-U6b

Each is used as `exhaust8` is, and each has the same three theorems with no
other hypothesis:

```lean
theorem exhaust8p_sound (r : Rule) (T : STy) (h : exhaust8p r T = true) : Sound r T
theorem bitwiseAll_sound (r : Rule) (T : STy) (h : bitwiseAll r T = true) : Sound r T
theorem ringAll_sound (r : Rule) (T : STy) (h : ringAll r T = true) : Sound r T
```

with `exhaust8p_defined`, `bitwiseAll_defined` and `ringAll_defined` for
`Defined r T`, and `exhaust8p_satisfiable`, `bitwiseAll_satisfiable` and
`ringAll_satisfiable` for `Satisfiable r T`, from the same `true`. The proof
of `EqsatRule.Sound <literal> <type>` is `exhaust8`'s term with one constant
renamed:

```
EqsatDecide.exhaust8p_sound <literal> <type> EqsatDecide.rflTrue
EqsatDecide.bitwiseAll_sound <literal> <type> EqsatDecide.rflTrue
EqsatDecide.ringAll_sound <literal> <type> EqsatDecide.rflTrue
```

A term names its procedure, its rule and its type, and the kernel accepts it
only by evaluating that procedure on that literal at that type. Each
soundness theorem is in the module of its procedure (`EqsatPacked`,
`EqsatBitwise`, `EqsatRing`) and `rflTrue` is in `EqsatExhaust`, so a bundle
that proves rules needs no controls module.

No operator of the three fragments is undefined behaviour and no pattern of
them is `bad`: on every admitted assignment each side is a value. So none of
the three reads the rule's direction (`equiv` and `refines` ask the same
thing there, one common value on every assignment), and a rule one of them
admits says something, which is what the `_defined` theorems state. None of
the three handles a side condition: a rule with a `where` clause is answered
`false`, whatever the clause.

### `exhaust8p`: two 8-bit variables, 256 assignments at a time

A lane vector is one natural number of 256 sixteen-bit lanes; lane `i` holds
a pattern's residue where the variable of rank 0 is `i`. `add` and `sub` of
two residues below 256 stay inside a lane, one `Nat.land` with 255 in every
lane reduces every lane modulo 256, `and or xor` act on each lane by
themselves, and two sides are equal on all 256 assignments exactly when their
vectors are one number (`Packed.pack_inj`). A second variable is a counter of
256, so a rule with two variables is 256 comparisons of 4,096-bit numbers and
not 65,536 evaluations. `exhaust8p r T` answers `true` only when all six
hold:

| Test | What it requires |
|---|---|
| type | `T` is `i8` or `u8`. At every other type, `bool` included, the answer is `false` before the rule is read |
| sorts | every variable is of sort `t` (`Packed.allT`). A rule with a Boolean variable is `exhaust8`'s |
| size | at most two variables (`Packed.maxVars`). None and one are accepted; three are answered `false` at once |
| no side condition | `Packed.noConds` |
| fragment | both sides are built from variables the rule binds (`?v` and `(const ?v)`), integer literals (read modulo 256), `add sub and or xor`, `neg` and `not` (`Packed.frag`). `mul`, a division or remainder, a shift or rotation, `band bor bxor`, a bit count, `bswap`, `bitreverse`, a comparison, a `select`, `true`, `false` and an unbound variable make the answer `false`, wherever they stand |
| every assignment | the two sides are one lane vector under each value of the counted variable (`Packed.sweepP`) |

Three variables are refused because nesting a second counter is 65,536
comparisons: with the limit raised in a copy, two such rules took 11.5 s and
22.2 s under the pinned Lean's own kernel, against 13 to 22 ms for two
variables. That was not run through Clean's entry. The soundness proof does
not read the limit.

The four constants of the evaluator (1, the lane's index, 255 and 256 in
every lane) are proved to be the vectors they are by having the kernel read
each lane with a shift and a remainder (`Packed.lanesOk`), not by evaluating
`pack`: `pack` raises 2 to a lane's offset, and Clean's kernel leaves
`Nat.pow` unreduced above 1,024 bits.

### `bitwiseAll`: one truth table for every width

At an integer type of width `w`, a pattern built from `and or xor not`,
variables, 0 and -1 evaluates to a residue whose bit `j`, for each `j < w`,
is the same Boolean function of bit `j` of each variable
(`Bitwise.frag_eval`). So two sides with one truth table are one residue at
every width, and no fact about `w` is used. `bitwiseAll r T` answers `true`
only when all of these hold:

| Test | What it requires |
|---|---|
| type | `T` is an integer type, any of the twelve. At `bool` the answer is `false` before the rule is read. `bitwiseAll r (.int t)` is `bitwise r`, which does not read `t`; `bitwise_sound : bitwise r = true → ∀ t, Sound r (.int t)` states all twelve at once |
| no side condition | `Bitwise.noConds` |
| sorts and size | every variable is of sort `t`, and there are at most eight (`maxBitVars`), so at most 256 rows |
| fragment | both sides are built from variables the rule binds, `(const 0)` written `lit false 0`, `(const -1)` written `lit true 1`, `and`, `or`, `xor` and `not` (`Bitwise.fragB`). Every other literal is refused, `(const 255)` and `lit true 0` among them: 255 is all ones at eight bits only |
| every row | on each assignment of one bit to each variable the two sides are the same bit (`Bitwise.allBits`) |

### `ringAll`: one polynomial for every width

At an integer type of width `w`, SemR's `add sub mul neg not` on residues
are, modulo `2^w`, the operations of the integers, with `(not a)` read as
`-a - 1`. So the residue of a pattern of the fragment is, modulo `2^w`, the
value of a polynomial with integer coefficients at the assignment's residues
(`RingAll.ringPat_norm`), and two sides with one polynomial are one residue
at every width. `ringAll r T` answers `true` only when all four hold:

| Test | What it requires |
|---|---|
| type | `T` is an integer type, any of the twelve. At `bool` the answer is `false` (`ringAll_bool`); at an integer type it is `RingAll.ringRun r`, whatever the type (`ringAll_int`), and `RingAll.ringRun_sound : ringRun r = true → ∀ t, Sound r (.int t)` states all twelve at once |
| no side condition | the rule's conditions are `Conds.nil` |
| fragment | both sides are built from variables of sort `t` that the rule binds, `(const INT)` for any integer, `add`, `sub`, `mul`, `neg` and `not` (`RingAll.ringPat`). Every other operator, a variable of sort `bool` that a side reads and an unbound variable make the answer `false`. The test is on the variables the sides read (`RingAll.isT`), not on the rule's list: a Boolean variable that neither side reads is accepted (`EqsatRingControls.beside_bool_u8`), where `exhaust8p` and `bitwiseAll` answer `false` on any rule that binds one |
| one polynomial | the two sides normalize to the same list of terms (`RingAll.ringNorm`, compared by `RingAll.Polyn.beq`) |

The normalizer is this family's own: a monomial is the ascending list of its
variables' ranks, a polynomial the sorted list of its terms with `Int`
coefficients. Lean's `Init.Grind` normalizer proves the same theorem and was
measured beside it under the pinned Lean: three to six times the kernel time
a check, and 1,275 declarations in the soundness theorem's cone that
`exhaust8_sound`'s does not have, against 137. It is not in the family.

The procedure has no size limit. A product of polynomials of `k` and `l`
terms is `k * l` insertions, and a rule whose expansion is too large for the
budget runs out of it, which admits nothing. It finds identities of
polynomials over the integers only: a rule that holds modulo one type's
modulus and not over the integers is answered `false` (`(mul ?x (const 256))
= (const 0)` at `u8`).

### What the gate measures of the three

As for `exhaust8`: the entry accepts the record term at a budget of 200,000,
and the gate prints the smallest heartbeat limit the same check passes under.
The heartbeat figures are exact; the times are one run's.

| Procedure | Rule | Types | Smallest passing limit | Time of the check |
|---|---|---|---|---|
| `exhaust8p` | `(and ?x (or ?x ?y)) = ?x` | `i8`, `u8` | 3,386 | 22 ms |
| `exhaust8p` | `(sub (add ?x ?y) ?y) = ?x` | `i8`, `u8` | 4,189 | 24 to 26 ms |
| `exhaust8p` | `(xor (xor ?x ?y) ?y) = ?x` | `i8`, `u8` | 3,386 | 22 to 23 ms |
| `exhaust8p` | `(add (and ?x ?y) (or ?x ?y)) = (add ?x ?y)` | `u8` | 3,666 | 31 ms |
| `exhaust8p` | `(not (and (not ?x) (not ?y))) = (or ?x ?y)` | `u8` | 3,403 | 31 ms |
| `exhaust8p` | `(add ?x ?y)` refines to `(add ?y ?x)` | `u8` | 3,150 | 23 ms |
| `exhaust8p` | `(sub (const -1) ?x) = (not ?x)` (one variable) | `i8` | 124 | 0.4 ms |
| `exhaust8p` | `(add (const 1) (const 255)) = (const 0)` (no variable) | `u8` | 105 | 0.3 ms |
| `exhaust8p` | `(and ?x (const 255)) = ?x` (one variable) | `u8` | 93 | 0.3 ms |
| `bitwiseAll` | `(and ?x (not ?x)) = (const 0)` | each of the twelve | 53 | 0.2 to 0.3 ms |
| `bitwiseAll` | `(or ?x (and ?x ?y)) = ?x` | `u8`, `u64` | 73 | 0.3 ms |
| `bitwiseAll` | `(or ?x (not ?x)) = (const -1)` | `u128` | 50 | 0.2 ms |
| `bitwiseAll` | `(not (and ?x (and ?y ?z)))` refines to `(or (not ?x) (or (not ?y) (not ?z)))` | `i64` | 187 | 1.1 ms |
| `bitwiseAll` | the `xor` of eight variables = the same in the reverse order (256 rows) | `u64` | 12,745 | 167 ms |
| `ringAll` | `(sub (add ?x ?y) ?y) = ?x` | each of the twelve | 83 | 0.3 to 0.4 ms |
| `ringAll` | `(sub (add ?x ?y) ?y)` refines to `?x` | `u64` | 83 | 0.4 ms |
| `ringAll` | `(add ?x ?x) = (mul ?x (const 2))` | `u8` | 90 | 0.4 ms |
| `ringAll` | `(neg (not ?x)) = (add ?x (const 1))` | `isize` | 80 | 0.3 ms |
| `ringAll` | `(mul ?x (add ?y ?z)) = (add (mul ?x ?y) (mul ?x ?z))` | `u16` | 120 | 0.6 ms |
| `ringAll` | `(mul ?x ?y) = (mul ?y ?x)` | `u8` | 82 | 0.4 ms |
| `ringAll` | `(mul (add ?x ?y) (add ?x ?y)) = (add (add (mul ?x ?x) (mul (const 2) (mul ?x ?y))) (mul ?y ?y))` | `i128` | 220 | 1.2 ms |
| `ringAll` | `(mul (sub ?x ?y) (add ?x ?y)) = (sub (mul ?x ?x) (mul ?y ?y))` | `i64` | 207 | 0.9 ms |

That is 12 rule and type pairs by `exhaust8p` (32,463 heartbeats together,
the dearest 4,189), 17 by `bitwiseAll` (13,764, the dearest 12,745) and 19 by
`ringAll` (1,878, the dearest 220). `exhaust8`'s enumeration of the first two
rules was measured in step 0 at about 1,573,000 heartbeats each. A rule with
one variable costs `exhaust8p` one comparison: `(and ?x (const 255)) = ?x` at
`u8` is 93 here and 4,682 by `exhaust8`.

At an integer type the answer of `bitwiseAll` and of `ringAll` does not
depend on the type, and the cost is the same at each. The term still names
its type, so twelve types are twelve terms and twelve checks.

The gate has the entry refuse 69 terms of `exhaust8p`, 49 of `bitwiseAll` and
41 of `ringAll`, each for the claim (`TypeMismatch`). For a rule a procedure
does not admit at a type, the entry accepts `<procedure> <literal> <type> =
false` and refuses both `= true` and the record term:

* **`(and ?x (const 255)) = ?x` at `u16`**, under each of the three. It is
  false there (`EqsatBitwiseControls.and255_not_sound_u16`). `exhaust8p`
  proves it at `u8` and answers `false` at `u16` for the type; `bitwiseAll`
  refuses it at every type for the literal, and `ringAll` for `and`;
* **false rules**: under `exhaust8p`, `(sub (add ?x ?y) ?x) = ?x`, trust-cg's
  `wrong_operand_order`, `(add ?x ?y) = (or ?x ?y)` and four rules that each
  fail on one assignment of the 65,536 (the four corners); under
  `bitwiseAll`, `(or ?x ?y) = ?x` (proved not `Sound` at `u8` beside it),
  `(xor ?x ?x) = ?x`, `(and ?x ?y) = (or ?x ?y)` and `(const 0) = (const -1)`;
  under `ringAll`, `(add ?x (const 1)) = ?x` (proved not `Sound` at `u8`),
  `(mul ?x (const 2)) = ?x`, `wrong_operand_order` and
  `(neg (not ?x)) = (sub ?x (const 1))`;
* **rules outside each fragment**: an operator of another procedure's
  fragment (`bitwiseAll` is asked for `ringAll`'s subject, `ringAll` for the
  subjects of the other two, and each of the three for a `mul` or `and` rule
  it does not cover), a comparison, a `select`, a Boolean variable (one that
  no side reads under `exhaust8p` and `bitwiseAll`; one that both sides read
  under `ringAll`, which accepts a rule beside a Boolean variable it does not
  read), a side condition, a side that is not a term, a third variable for
  `exhaust8p`, a ninth for `bitwiseAll`;
* **`Sound` rules a procedure does not admit**: for seven of the rules
  refused, the entry accepts a proof of `Sound` beside the refusal (two under
  `exhaust8p`, by hand; three under `bitwiseAll` and two under `ringAll`, by
  `exhaust8`, `(mul ?x (const 256)) = (const 0)` at `u8` among them). `false`
  is not a refutation;
* **another type**: each procedure at `bool`; `exhaust8p` at each of the ten
  wider integer types, with its `u8` term offered there; the `u8` term of a
  rule offered at `u16` and the `u64` term at `bool` under the two all-width
  procedures, where the rule holds at both integer types and the term still
  names one;
* **another rule**: the term of a true rule offered for a false one;
* **`Defined` and `Satisfiable`** claimed by a procedure's term for a rule
  it does not admit (accepted beside them for a rule it does).

What was not measured: the smallest budget at which each of the six modules
replays; any rule that runs out of the budget under one of the three
(`exhaust8p`'s cost grows with the size of the two sides, `bitwiseAll`'s with
that size times the rows, `ringAll`'s with the terms of the expansion; none
of the three bounds the size of the sides, `exhaust8p` and `bitwiseAll` bound
the number of variables, at two and eight, and `ringAll` bounds nothing);
three variables under
`exhaust8p` through Clean's entry.

## Compiling

The pinned Lean is v4.30.0-rc2. `compiled_fixture_dir("eqsat_decide")`
(`clean_olean::test_support`) compiles `ORDER` in a cache directory; by hand,
in a scratch directory holding `semr/SemR.lean`, `eqsat_rules/EqsatRule.lean`,
`eqsat_rules/EqsatBasics.lean` and this family's `.lean` files:

```sh
L=~/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean
for m in SemR EqsatRule EqsatBasics EqsatResidue EqsatExhaust EqsatDecideControls \
        EqsatPacked EqsatPackedControls EqsatBitwise EqsatBitwiseControls \
        EqsatRing EqsatRingControls; do
    LEAN_PATH=$PWD $L --root . -o $m.olean $m.lean || break
done
```

No `sorry`, `native_decide`, `bv_decide`, `Lean.ofReduceBool` or new axiom:
every closure is within `propext`, `Classical.choice` and `Quot.sound`.
`crates/clean-olean/tests/eqsat_decide.rs` replays every declaration of the
family and of the two modules it takes from `eqsat_rules` from the empty
environment through Clean's reference entry, compares the closure digest of
`EqsatRule.Sound` with the `eqsat_rules` gate's pin, requires every theorem of
the family's nine modules by name with its statement pinned (447 rows), has
the kernel evaluate
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
undefined on every assignment (72 refused terms). It then runs the controls
of the three procedures of PKG-U6b
(`crates/clean-olean/tests/eqsat_decide/three_procedures.rs`; "What the gate
measures of the three" above): the record term accepted for 12 rule and type
pairs under `exhaust8p`, 17 under `bitwiseAll` and 19 under `ringAll`, and 69,
49 and 41 terms refused for the claim. Every count is asserted, so a control
removed is an edit of a number:

```sh
targo --unverified test --locked --profile authority -p clean-olean \
    --test eqsat_decide -- --include-ignored --nocapture
```

A module added to `ORDER` is added to the test's `MODULES` (the test compares
the two).

`STATEMENTS` holds one `name digest` row per theorem of the nine modules, in
the `eqsat_rules` family's format: SHA-256 over the theorem's type as the kernel
holds it and the closure digest of every constant the type names. It moves
when a statement is edited and when the meaning of anything it mentions
changes (an edit to `evalR` moves every row that mentions it), and not when a
proof does. The row of `EqsatDecide.exhaust8_sound` is the pin of what the
soundness theorem states: it moves with `exhaust8`, with `EqsatRule.Sound` and
with anything either reaches. The rows of `EqsatDecide.exhaust8p_sound`,
`EqsatDecide.bitwiseAll_sound` and `EqsatDecide.ringAll_sound` are the same
pin for the other three. Re-pin a row only with the reason in the commit
message.
