# `eqsat_rules` — trust-cg's e-graph rules as theorems over SemR (PKG-U2)

A rewrite rule of trust-cg's equality-saturation engine is one object: the
five-clause rule text of trust-cg `docs/eqsat-tier-e.md` section 5.1. This
family states what such a rule says over trust-ir's SemR and proves the rules
of trust-cg's integer rule set. trust-cg's rule registry is to admit a rule
at a type only when the Clean kernel accepts a lemma of this family for the
statement trust-cg generates from its own parsed rule.

The family imports the `semr` family's `SemR.lean` unchanged
(`from semr SemR`): there is one SemR copy in Clean. Nothing here is in
clean-kernel's built-in library or under `theories/`.

## Modules

| Module | What it declares |
|---|---|
| `EqsatRule.lean` (imports `SemR`) | The vocabulary: `Srt`, `Sorts`, `Pat`, `Cond`, `Conds`, `Dir`, `Rule`, `STy`, the evaluator `Pat.eval`, the hypotheses `Admits`, `CondsHold` and `PbOk`, the statement `Sound rule T`, and the second statement `Satisfiable rule T` (the side conditions can be met). Flat inductives, no string literal, every operator evaluated by SemR's own `evalBinop`, `evalUnop`, `evalIcmp` and `selectVal`. **These definitions are the meaning of a rule and are trusted as read.** |
| `EqsatBasics.lean` | Proof helpers, not part of the meaning: `Admits` as the assignment's shape, SemR's value evaluators reduced to its residue operators on admitted operands, widths under `PbOk`. |
| `EqsatAnchors.lean` | Kernel-checked statements that pin the vocabulary, each required by name by the gate with its statement pinned (`STATEMENTS`): `admits_one_iff` (one variable admits exactly what SemR's `rejectPoison` and `expectTy` accept), `admits_inhabited` and `pbOk_inhabited` (every variable list has an admitted assignment), `sound_equiv_iff` and `sound_refines_iff` (the two branches of `Sound`, unfolded), `equiv_gives_refines` and its converse for total operators `refines_gives_equiv_of_total`, every operator arm of `Pat.eval` against SemR in general (`bin_eval`, `un_eval`, `cmp_eval`, `sel_eval`, the `*_stop*` theorems, `bin_int`, `un_int`, `cmp_int`, `sel_int`) and on concrete values (`bin_reads`, `un_reads`, `cmp_reads`, `sel_reads`, `stop_order`), what a direction says of a side that is not a value, what `Satisfiable` adds to `Sound`, and how literals, unbound variables, operand types and side conditions read. |
| `EqsatIntRuleDefs.lean` | GENERATED. One `def EqsatRule.Defs.<rule> : EqsatRule.Rule` per rule of trust-cg `crates/trust-cg-eqsat/rules/integer_identities.rules` (76 rules). |
| `EqsatIntWrongRuleDefs.lean` | GENERATED. One `def EqsatRule.WrongDefs.<file> : EqsatRule.Rule` per file of trust-cg `crates/trust-cg-eqsat/tests/wrong_rules/` (10 rules). |
| `STATEMENTS` | Not Lean. One `name digest` row per theorem of `EqsatAnchors` and `EqsatIntControls` and per satisfiability lemma: the gate's pin of each statement (below). |
| `LEMMAS` | Not Lean. GENERATED. One `rule scope kind lemma` row per rule of the integer rule set and scope of its domain: the lemma that scope needs, or `-` for a `fold_*` rule. The gate requires every lemma named there, with exactly its row's statement (below). |
| `EqsatIntSample.lean` | Six lemmas of the integer rule set, in the namespace and under the names the rest of the set uses: `EqsatInt.add_zero`, `select_same` and `rotl_full` at every integer type, `select_same_bool`, `band_true`, and the one-way `band_false`; and `rotl_full_sat`, the satisfiability lemma of a rule with a `where` clause. |
| `EqsatIntArith.lean`, `EqsatIntCmpSelBool.lean`, `EqsatIntBitwise.lean`, `EqsatIntNegRot.lean` | The lemma groups of the integer rule set (below): every other lemma of the set, and the satisfiability lemmas `sub_const_to_add_sat` and `rotr_full_sat`. Each module's header lists its rules and names its helpers (`arith_*`, `bitwise_*`, `negrot_*`). |
| `EqsatIntControls.lean` | The non-vacuity evidence: `¬ Sound` for each wrong rule that is false as a statement, at a named small type and at every integer type (`<rule>_all`); the pointer-width controls (`ptr64_only_not_usize`, `ptr32_only_not_usize`, `not_sixteen_holds_usize`); the direction controls (`udiv_self_refines_u8`, `panic_only_udiv_self_u8`, `refines_does_not_give_equiv`, and `band_false_as_equiv_is_true`); a refines statement with a non-term right side that holds (`refines_ub_left_any_rhs`); a rule that is `Sound` for want of an assignment and not `Satisfiable` (`contradictory`); and two pairs of different literals with one proposition (`same_residue_one_statement`, `eval_free_twin_holds`). |

## What a rule says

`Sound rule T` is: for every pointer width `pb` the type admits (`PbOk`), every
assignment of admitted values to the rule's variables (`Admits`) that
satisfies the side conditions (`CondsHold`),

* `equiv`: both sides evaluate to one common `.ok` value;
* `refines`: the left side is undefined behaviour, or both sides evaluate to
  one common `.ok` value.

Choices fixed here, each the fail-closed one:

* **Equiv is a common value, not equal outcomes.** Two sides that are the same
  type error do not stand in `equiv`, so a generator fault that makes both
  sides ill-typed proves nothing. `refines` is weaker
  (`equiv_gives_refines`), and strictly weaker only through an operator that
  is not total: the one witness is `udiv` (`refines_does_not_give_equiv`).
  Where the left side names only total operators the two statements are
  equivalent (`refines_gives_equiv_of_total`), and the rule grammar admits
  total operators only, so **for every rule the grammar can state the
  direction has no kernel content** (below).
* **Pointer width.** `PbOk` requires `pb = 32 ∨ pb = 64` at `isize` and `usize`
  only; a rule at any other type is proved for every pointer width, as the
  checker's `Ctx::width` admits fixed-width types whatever
  `Module::pointer_bits()` is.
* **Variables.** A variable of sort `T` at an integer type is a residue below
  the type's modulus; at `bool`, and for sort `bool`, a `Bool`. Poison is never
  admitted. A constant variable ranges over the same values as a term
  variable; the `const` flag is part of the literal and of its digest, is
  read as data, and does not reach the proposition (`const_flag_is_data`).
* **Literals.** `(const INT)` is `Pat.lit neg mag` as written, and denotes
  `INT mod 2^w` by SemR's `negR` and `modulus` (the checker's `Int::residue`).
  At `bool` it is not a term: it evaluates to `.stop .outOfFuel`, as does an
  unbound variable. An `equiv` statement with such a pattern on either side,
  and a `refines` statement with it on the left side, fails on every
  assignment that satisfies the hypotheses (`equiv_stop_never`,
  `refines_stop_left`). A `refines` statement with it on the right side is
  not thereby false (below).
* **Side conditions** test the residue of a variable exactly as the checker's
  `rule_step` does. A condition with no residue to test (the type is `bool`,
  or the rank is unbound) holds, so a malformed condition never makes a
  statement easier.
* **Satisfiability is a second statement.** `Sound` is an implication from the
  side conditions, so a rule whose conditions no assignment satisfies at `T`
  is `Sound` there whatever its sides are (`sound_of_unsatisfiable`,
  `contradictory_is_sound`; contradictory at one width only:
  `contradictoryAt8`). The checker's parser accepts such a rule and it never
  fires, so this is not unsound, but its row would read as proved while
  saying nothing. `Satisfiable rule T` says that at every admitted pointer
  width some admitted assignment meets the conditions. It holds for nothing
  when the rule has no `where` clause or `T` is `bool`
  (`satisfiable_of_no_conds`, `satisfiable_bool`); a rule with a `where`
  clause carries the lemma `EqsatInt.<rule>_sat` at each integer type, and
  trust-cg's registry is to require it beside the `Sound` record or mark the
  row. The three such rules of the set have it (`rotl_full_sat`,
  `rotr_full_sat`, `sub_const_to_add_sat`).
* **`(eval OP ?a ...)`** is quoted as `OP` over the constant variables. A rule
  whose right side uses `eval` under an operator (`sub_const_to_add`,
  `add_add_const`, `mul_mul_const`, `and_and_const`, `or_or_const`,
  `xor_xor_const`) is proved in that reading and carries the named premise
  `checker-ground-eval`: that the checker's Rust evaluator computes SemR's
  operator on constants is not proved here.
* **The 28 `fold_*` rules get no lemma.** Their quoted sides are the same
  pattern, so a kernel check of the statement would establish only that the
  operator is defined; they are dispositioned `Unsupported("fold-evaluator")`
  until the checker's ground evaluator is tied to SemR. Their literals are in
  `EqsatIntRuleDefs.lean` so that trust-cg can state the disposition per rule.

What is not established:

* No theorem ties the checker's replay (instantiation, congruence,
  transitivity, `refines` used forward only) to `Pat.eval`.
* **The kernel does not hold a rule's direction.** A one-way rule of the
  grammar stated as `equiv` is a true and provable statement
  (`band_false_as_equiv_is_true`; likewise `mul_zero`, `and_zero`, `or_ones`,
  `double_to_mul`). The kernel refuses the committed refines lemma for the
  equiv statement, which is a different proposition, but a proof of the
  equiv statement exists. What keeps a one-way rule one-way is the rule
  digest and the checker's `SymOfRefines` refusal, in trust-cg.
* **A `refines` statement does not constrain its right side where the left
  side is undefined behaviour** (`refines_value_left`). With a left side
  that is always undefined behaviour it holds with any right side, even a
  non-term (`refines_ub_left_any_rhs`). No rule of the grammar is like that,
  because every operator it admits is total; if a non-total operator is ever
  admitted, a refines rule over it needs a statement about its right side
  that this vocabulary does not make.
* **The kernel binds a lemma to the proposition, not to the literal.** Two
  literals that differ only in a `const` flag, in `var` against `cvar` (so
  also `(eval OP ?a ?b)` against `OP` over term variables), or in two
  integer literals of one residue at the instance type give one proposition,
  and a lemma of one is accepted for the other (`const_flag_is_data`,
  `var_cvar_one_statement`, `same_residue_one_statement`,
  `eval_free_twin_holds`; the gate asserts both acceptances on Clean's
  entry). No false rule is admitted by this, since one proposition has one
  truth value. But an edit of this kind is refused by the rule digest only,
  and whether a row is a `fold_*` row or carries `checker-ground-eval` must
  be read from the parsed rule (its right side is, or contains, `eval`),
  never from the statement or the record.
* The registry's own well-formedness refusals (an ordered comparison at
  `bool`, a non-total operator) are not restated in `Pat.eval`, which gives
  such a pattern SemR's value or SemR's refusal.
* **The statement does not carry the rule's domain.** `Sound rule T` is stated
  per type and nothing in it says `T` is in the rule's domain. A bool-only
  rule has no variable, literal or operator of sort `T`, so its statement is
  the same proposition at every instance type, and the kernel accepts
  `EqsatInt.band_true` for `Sound Defs.band_true (.int .u64)` (the gate
  asserts this). Which types a rule may fire at is trust-cg's domain test;
  the statement digest stays trust-cg's too.

## Generated modules

`gen_rule_defs.py` (untrusted, beside this file) reads rule text and prints the
literals. Variables are indexed by rank in the order of their names' bytes,
the order a derivation's substitution uses; every index and literal is a raw
`Nat` literal (`nat_lit n`), which is the term trust-cg's generator builds.
trust-cg builds the same literal in Rust from its checker's parsed rule; a
literal written wrongly on either side whose statement is a different
proposition is a kernel refusal there, never a proved rule. A different
literal with the same proposition is accepted ("What is not established").
The script reads rule text as UTF-8 and accepts and refuses what the
checker's tokenizer does; `python3 gen_rule_defs.py --self-test` runs its own
controls.

Regenerate (from this directory; the script's header has the same commands):

```sh
R=origin/main:crates/trust-cg-eqsat
git -C ~/trust-cg show $R/rules/integer_identities.rules > /tmp/integer_identities.rules
python3 gen_rule_defs.py --module EqsatIntRuleDefs --namespace Defs \
    --source "trust-cg crates/trust-cg-eqsat/rules/integer_identities.rules" \
    /tmp/integer_identities.rules > EqsatIntRuleDefs.lean

mkdir -p /tmp/wrong_rules
for f in missing_side_condition one_way_reversed panic_only_sdiv_neg_one \
         panic_only_udiv_self wrong_boolean_constant wrong_constant wrong_fold \
         wrong_operand_order wrong_select_arm wrong_width; do
    git -C ~/trust-cg show $R/tests/wrong_rules/$f.rules > /tmp/wrong_rules/$f.rules
done
python3 gen_rule_defs.py --module EqsatIntWrongRuleDefs --namespace WrongDefs \
    --name-from-file --allow-partial-ops \
    --source "trust-cg crates/trust-cg-eqsat/tests/wrong_rules/" \
    /tmp/wrong_rules/*.rules > EqsatIntWrongRuleDefs.lean
```

`LEMMAS` is the first command with `--lemmas` and `> LEMMAS`. Add
`--check <file>` to any of the three to compare a committed file with the
rule text instead of printing; `--table` prints
`name direction kind domain` rows. Each generated module's header records the
SHA-256 of the rule text it was read from (trust-cg `8bac4e06d`; the same
bytes at `43cb5a33d2`).

## Lemma names and the record term

All lemmas are in namespace `EqsatInt`:

* `EqsatInt.<rule> : ∀ t, EqsatRule.Sound EqsatRule.Defs.<rule> (.int t)` for a
  rule that holds at every integer type; the record term at `u64` is
  `EqsatInt.<rule> SemR.IntTy.u64`;
* `EqsatInt.<rule>_bool : EqsatRule.Sound EqsatRule.Defs.<rule> .bool` for a
  rule whose domain has integer types and `bool`;
* `EqsatInt.<rule> : EqsatRule.Sound EqsatRule.Defs.<rule> .bool` for a
  bool-only rule;
* `EqsatInt.<rule>_<type>` for a rule proved one type at a time
  (`mul_255_neg_i8_i8`, `mul_255_neg_i8_u8`);
* `EqsatInt.<rule>_sat : ∀ t, EqsatRule.Satisfiable EqsatRule.Defs.<rule> (.int t)`
  for a rule with a `where` clause: the statement trust-cg builds is
  `EqsatRule.Satisfiable <literal> <type>` with the same literal and type as
  the `Sound` statement, and the term at `u64` is
  `EqsatInt.<rule>_sat SemR.IntTy.u64`.

A lemma that cannot be proved is not stated: it is left out and the row is
`timed-out`, with what was tried.

The lemma modules share the namespace and are loaded into one environment by
the gate, so a name is declared in one module only: a helper two groups need
goes in `EqsatBasics.lean`, and a helper of one group takes a name no rule
has.

## The rule set and its lemma groups

`integer_identities.rules` has 76 rules. 28 are `fold_*` (no lemma, above).
The other 48 need 56 lemmas: 41 at every integer type, 2 at one type each
(`mul_255_neg_i8`), 7 `bool` instances of rules that also have integer types,
and 6 bool-only rules. **All 56 are proved; none is timed out.** The three
rules with a `where` clause (`rotl_full`, `rotr_full`, `sub_const_to_add`)
also need a satisfiability lemma each, at every integer type; all three are
proved.

`LEMMAS` is the list: one `rule scope kind lemma` row per rule and scope of
its domain, where the scope is `int` (the domain has all twelve integer types
and the lemma is `∀ t, Sound Defs.<rule> (.int t)`), one integer type, or
`bool`, and the kind is `plain`, `eval` (premise `checker-ground-eval`) or
`fold` (no lemma). `gen_rule_defs.py --lemmas` writes it from the rule text.
The gate requires each named lemma as a theorem whose type is the row's
statement term for term, checks that Clean's entry accepts its record term
at every type of the scope, and refuses a `Sound` theorem of the lemma modules
that no row names. A lemma that is not proved is listed in the gate's
`TIMED_OUT` (`crates/clean-olean/tests/eqsat_rules/lemmas.rs`) with what was
tried written here, and must then be absent from the sources; it is never
dropped from `LEMMAS`. `TIMED_OUT` is empty.

Each lemma at every integer type is one proof at an arbitrary width, from
`Nat` arithmetic and `Nat` bit operations modulo SemR's modulus; none splits
on the type or the width, and none of the 56 uses the pointer-width
hypothesis, so each holds at any pointer width (`bv_decide` and
`native_decide` are refused by the entry, so there is no bit-blasting
fallback).

| Group | Module | Rules (lemmas) |
|---|---|---|
| a. additive and multiplicative | `EqsatIntArith` | `add_const_right`, `mul_const_right`, `add_zero` (in `EqsatIntSample`), `sub_zero`, `sub_self`, `mul_one`, `mul_zero`, `double_to_mul`, `add_add_const`, `mul_mul_const`: 10 rules, 10 lemmas |
| b. comparisons, select, bool | `EqsatIntCmpSelBool` | `icmp_eq_self`, `icmp_ne_self`, `icmp_ult_self`, `icmp_ule_self`, `icmp_slt_self`, `icmp_sle_self`, `select_same`, `select_true`, `select_false`; the `_bool` instances of `icmp_eq_self`, `icmp_ne_self`, `select_same`, `select_true`, `select_false`, `and_self` and `or_self`; the bool-only `band_true`, `band_false`, `bor_false`, `bxor_false`, `bxor_self`, `bxor_true_true` (`select_same`, `select_same_bool`, `band_true` and `band_false` are in `EqsatIntSample`): 15 rules, 22 lemmas |
| c. bitwise and not | `EqsatIntBitwise` | `and_const_right`, `or_const_right`, `xor_const_right`, `and_self`, `and_zero`, `and_ones`, `or_self`, `or_zero`, `or_ones`, `xor_self`, `xor_zero`, `not_not`, `and_and_const`, `or_or_const`, `xor_xor_const`: 15 rules, 15 lemmas |
| d. negation, rotation, per-type | `EqsatIntNegRot` | `mul_neg_one`, `mul_255_neg_i8` (at `i8` and at `u8`), `neg_neg`, `zero_sub`, `add_neg`, `sub_const_to_add`, `rotl_full` (in `EqsatIntSample`), `rotr_full`: 8 rules, 9 lemmas |

## Compiling

The pinned Lean is v4.30.0-rc2. `compiled_fixture_dir("eqsat_rules")`
(`clean_olean::test_support`) compiles `ORDER` in a cache directory; by hand,
in a scratch directory holding `semr/SemR.lean`, this family's `.lean` files
and its `ORDER`:

```sh
L=~/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean
for m in SemR $(grep -v -e '^#' -e '^from ' ORDER); do
    LEAN_PATH=$PWD $L --root . -o $m.olean $m.lean || break
done
```

No `sorry`, `native_decide`, `bv_decide`, `Lean.ofReduceBool` or new axiom:
every closure is within `propext`, `Classical.choice` and `Quot.sound`.
`crates/clean-olean/tests/eqsat_rules.rs` replays every declaration of the
family from the empty environment through Clean's reference entry, runs the
kernel controls, pins the closure digests of `EqsatRule.Sound` and
`EqsatRule.Satisfiable`, requires every theorem of `EqsatAnchors` and
`EqsatIntControls` and every `_sat` lemma by name with its statement pinned,
and requires every lemma of `LEMMAS` with its row's statement:

```sh
targo --unverified test --locked --profile authority -p clean-olean \
    --test eqsat_rules -- --include-ignored --nocapture
```

A module added to `ORDER` is added to the test's `MODULES` (the test compares
the two).

`STATEMENTS` holds one `name digest` row per pinned theorem. The digest is
SHA-256 over the theorem's type as the kernel holds it and the closure digest
of every constant the type names, so it moves when the statement is edited
and when the meaning of anything it mentions changes, and not when a proof
does. The gate fails when a theorem of the two pinned modules has no row, when
a row names a theorem the replayed environment lacks, or when a digest
differs; it prints the table it computed. Re-pin a row only with the reason
in the commit message.
