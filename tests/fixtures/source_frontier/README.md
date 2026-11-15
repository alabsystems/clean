# `source_frontier` — the Mathlib-SOURCE frontier probe family

**Landed:** 2026-08-26 (FRONTIER STAGE 0, "the instrument"), extended the same
day by FRONTIER STAGE I-1 (CLASS I, the candidate side — see below and
[`data/frontier_stage1.PENDING.md`](../../../data/frontier_stage1.PENDING.md)
for what only the corpus box can settle) and then by FRONTIER STAGE I-2 (CLASS
I, the GOAL side — p18 flips, p24/p25/p26 are new).
**Recon:** `docs/analysis/frontier-next-class-2026-08-25.md`.
**Gate:** `scripts/source_frontier_battery.sh` — asserts every verdict and every
pinned error fragment below, fail-closed.

Every probe here runs under `--prelude builtin` with **no Mathlib and no
imports**, in well under a second, and reproduces a class measured on real
Mathlib source in
`reports/source-elab/srcelab-2026-08-25-g08b7b05d9.json` (497 error entries
across five pinned files). p01–p14 are the recon's own probes, executed there
and landed here as committed, gated pins; p15, p16 and p17 are new on 2026-08-26
(the two that fire the third mask, and the one that pins the artifact-form
message); p18–p23 are new on 2026-08-26 with **stage I-1** — the goal-side
residue, and the five probes that pin the risk axis a capability-adding change
to instance search creates; p24–p26 are new the same day with **stage I-2**,
which closes that residue and pins its two refusals.

## What a probe here has to do

The U2 battery's rule applies unchanged: **a `MUST_FAIL` probe cannot tell a
precise refusal from an over-broad one**, because both satisfy it. So every
failing probe here ships with at least one PASSING control that rules out the
broad reading, and every fixture's header states, in order: what it proves, and
what its control rules out. A probe with no control is not evidence.

The `_MUST_FAIL` suffix marks today's measured verdict, never a desired one.
A probe that flips is a result — re-pin it deliberately, with a dated note in
the battery, exactly as `scripts/u2_battery.sh` does.

## Class II — dot notation whose target does not resolve

44 of the 497 corpus entries (all five files), reported before 2026-08-26 as
`NotImplemented("cannot extract type name from <raw Expr dump>")`. The recon's
§5.4 finding is that this is **not a missing feature**: it is an unknown
identifier wearing an NYI mask, with the name deleted from the message.

| probe | verdict | isolates |
|---|---|---|
| `p03_dot_pi_receiver_MUST_FAIL` | 1 pass / 1 fail | the Pi sub-shape (35 corpus entries): a `def`-based Prop alias, δ-unfolded by `get_type_name`'s leading `whnf` before its head can be read |
| `p06_dot_proj_receiver_MUST_FAIL` | 3 pass / 1 fail | the Proj sub-shape (9 corpus entries, all `Order/Basic`): a projection stuck on an opaque instance variable, `Proj(MyLE, 0, Proj(MyPre, 0, FVar))` — structurally the corpus's `Proj(LE, 0, Proj(Preorder, 0, FVar))` |
| `p05_control_const_head_MUST_FAIL` | 0 pass / 1 fail | **control.** The same missing field on a `Const`-headed receiver already named the identifier (`And.nosuchfield`). Rules out "missing-field reporting is broadly wrong", and pins the untouched path against leakage from the repair |
| `p01_control_pi_receiver_resolvable` | 4 pass | **control.** p03's receiver shape with a target that RESOLVES. Rules out "dot notation on non-`Const`-headed receivers is unimplemented" |
| `p04_control_namespaced_resolvable` | 3 pass | **control.** p01 inside a namespace, so the recovered head is qualified. Rules out "the pre-whnf head try is root-only", which is what the namespaced corpus entries would need to be a genuine gap |
| `p07_control_proj_receiver_resolvable` | 7 pass | **control.** p06's receiver with a resolvable target, under both the derived and the direct instance. Rules out "the Proj sub-shape is a separate capability gap" |
| `p13_control_strict_implicit_resolvable` | 4 pass | **control.** The `Function.Injective` shape — a `def` alias over strict-implicit `⦃a b⦄` binders. Rules out "the strict-implicit Pi chain is a harder sub-shape" |
| `p17_artifact_form_MUST_FAIL` | 1 pass / 1 fail | p03's body inside a namespace, which is how every Mathlib declaration is written — and the only probe that pins the message the CORPUS REPORT will carry. `clean check` renders a top-level failure with `{e:?}` and a namespaced one with `{e}`, so the Display form is invisible from the terminal form p03 pins. Its control is p03: the identifier is named in both renderings, so this fixture measures the rendering path, not the repair |

**The stage-0 repair landed against these.** `infer/elab_proj.rs` now names the
target — `ElabError::UnresolvedDotTarget`, message led by
`Unknown identifier: <Head>.<field>` — instead of dumping the receiver's
normalised type. It is a diagnostic change only: it runs on the `?` path that
line always took, no site selects on the error's shape, and all twelve verdicts
above are byte-identical across it. Two things about the message are
load-bearing and should not be casually reworded: the `Unknown identifier:`
prefix is what moves these entries out of `not implemented (elaborator NYI)` in
`scripts/srcelab_classify.py` (first-match-wins) and what survives
`per_error_class`'s 400-char truncation, and the `dot notation` substring is
what keeps them separable from the pre-existing unknown-identifier population
in the same report.

**What this does NOT establish, and cannot on this box:** how many of the 44
corpus entries are independent capability gaps rather than cascade from a
declaration that failed earlier in the same file. The recon measured 86% cascade
among the *properly-labelled* unknown identifiers (§2.3). Settling it for these
44 needs the corpus box: `scripts/source_elab_gate.sh --jobs 2 --update`, then
re-read the class. No count claim belongs here — see recon §7.1.

## Class I — instance search cannot see through a `def`-based class alias

34 of the 53 `instance synthesis` corpus entries, every one of them a
`Decidable`/`DecidableEq` goal. `DecidableEq` is a `def`, not a `class`, so it
answers neither `is_class` nor `extract_class_app` once normalised.

**Stage I-1 landed here on 2026-08-26** (the candidate side).
`ElabCtx::resolve_local_instance_telescoped`
(`crates/clean-elab/src/infer/instance.rs`) matches LOCAL instance binders the
alias had made invisible, three ways in order: **(A)** the goal as handed in
against each local's type as bound, no normalisation on either side; **(C)**
for a **Pi-shaped** goal with no class application left — the alias the
*caller* already unfolded — the whole normalised goal against the whole
normalised local; **(B)** under the local's ∀-telescope, matching its
conclusion and returning the local *applied* (`h a b`).

(C)'s Pi restriction is load-bearing, not tidiness. Unifying a *whole* goal is
the one match here that could SOLVE the goal expression rather than match it:
handed a goal still standing as a bare metavariable, `try_unify` would assign
`?goal := <the first local's type>` and hand back that local — inventing the
class instead of finding evidence for it. (A) and (B) cannot do that; both
require a rigid `Const` head before they look at anything. A δ-unfolded class
alias is always a Pi, so the restriction costs the match nothing.

It is consulted **only after the primary search has returned `None`**. That is
the whole safety argument and it is structural, not empirical: no goal that
resolved before this change can take a different answer after it, because the
new code is never reached while an answer exists.

| probe | verdict | isolates |
|---|---|---|
| `p08_deceq_bridge` | **2 pass** (was 0/2) | the existing `Decidable (@Eq α a b)` bridge, which used to fire and then die one level down at its own delegation to `DecidableEq α`. Match (A) now hands it the dictionary |
| `p11_unwhnfd_goal` | **1 pass** (was 0/1) | the CANDIDATE face. The goal here is *not* normalised (`inferInstance` does not whnf) and it failed anyway — which is why the fix is a candidate-side match and **not** the recon's explicitly not-recommended "drop the goal-side `whnf`" |
| `p09_deceq_goal_face` | **2 pass** (was 1/2) | the GOAL face, in the corpus's exact printed shape. **Scheduled for stage I-2 and flipped at I-1** — its carrier is a local binder of the same declaration, so the goal had to be found, not built. Match (C) |
| `p18_goal_side_constructed` | **3 pass** (was 2/1) | **the residue, closed by stage I-2** (below). The same Pi-shaped alias goal with NO local of that type. Its in-file control `bodyIsSolvable` shows the Pi's BODY — `Decidable (a = b)` at `Nat` — resolved from the global table before this stage and resolves now, so what moved is the ABSTRACTION: *building* `fun n n1 => …`, which no candidate-side match can do |
| `p10_control_class_declared` | 3 pass | **control.** p09's shape over a `class`-declared class. Ruled out "local instance binders are not consulted" and "the callee's signature is the problem"; byte-stable across stage I-1 |
| `p12_control_explicit_dictionary` | 2 pass | **control.** The same `DecidableEq α` local passed explicitly. Ruled out "`DecidableEq` is unusable / breaks elaboration generally" — it broke instance LOOKUP and nothing else; byte-stable across stage I-1 |

### The risk axis: more candidates must not mean a wrong candidate

Widening instance search has exactly two failure modes — admitting a candidate
that should lose, and cost. The acceptance path is unchanged (typeclass
resolution, then kernel re-check), so the first is what the probes below are
for. The second is measured, not assumed, and it is a *share*, never a rate:
this box carries other lanes.

| probe | verdict | isolates |
|---|---|---|
| `p19_control_two_carriers_selected` | 1 pass | **selection.** Two alias locals at different carriers; each `if` takes its OWN dictionary and survives the kernel re-check. A "grab the first local you can name" implementation would emit an ill-typed term here |
| `p20_wrong_carrier_refused_MUST_FAIL` | 0 pass / 1 fail | **refusal.** A `[DecidableEq α]` local is NOT grabbed for a `Decidable (b = b)` goal at an unrelated `β`, and the pre-existing diagnostic is unchanged. p19 alone would be satisfied by "grab any local"; p20 alone by "grab nothing" |
| `p21_control_local_beats_global` | 10 pass | **ambiguity.** Half 1: a telescoped local IS a viable candidate for `MyE Nat` (without this, half 2 is vacuous). Half 2: at a class that also has a global instance, the LOCAL dictionary wins — measured by an `rfl` against that exact dictionary field |
| `p22_undetermined_binder_refused_MUST_FAIL` | 3 pass / 1 fail | **hygiene in an ordinary instance lambda.** A telescope binder the goal does not determine is refused, not emitted as `h ?x`. An unassigned metavariable is a tagged free variable and would surface far away as the kernel's "Declaration contains free variables" |
| `p23_control_telescoped_local_no_bridge` | 4 pass | **the general capability**, with the hand-written `Decidable`/`Eq` bridge out of the picture: a user-declared class and `def`-based alias, conclusion matched under the telescope, term returned APPLIED |

**What stage I-1 does NOT claim.** Nothing about the 34 corpus entries. They
are CANDIDATES to leave the `instance synthesis` class, never a measured gain,
and this box cannot say otherwise — see `data/frontier_stage1.PENDING.md` and
recon §7.1.

### Stage I-2 — the GOAL side: the alias goal whose answer must be BUILT

**Landed 2026-08-26.** `ElabCtx::resolve_pi_goal_by_abstraction`
(`crates/clean-elab/src/infer/instance.rs`) closes the residue p18 pinned.
When the goal that reaches instance search is a **Pi** — the class alias the
*caller* already δ-unfolded, with no local of that type in scope — open its
∀-telescope over fresh **rigid locals**, resolve the conclusion as an ordinary
instance goal, and re-abstract the locals into lambdas: `fun n n1 => inst n n1`.

Same safety argument as stage I-1, one rung further out: it is consulted
**only after the primary search AND the candidate-side match have both
returned `None`**, so it can add resolutions and never change one.

Three restrictions are load-bearing rather than tidy, and each has a probe:

- **Rigid locals, not metavariables.** Opening the telescope with
  metavariables would let the conclusion's own search *assign* the telescope
  variables and "succeed" at one argument, emitting a lambda that is ill-typed
  for every other. p25 is that refusal, with an in-file control showing the one
  argument its instance covers is answerable today.
- **Ground goals only.** A goal still carrying metavariables is refused
  outright: solving the conclusion under the telescope can assign one of the
  goal's OWN metavariables to a term mentioning a telescope local, and
  abstracting the *returned term* does not fix the caller's metavariable
  context. The δ-unfolded alias goals this exists for are ground — their
  carrier was pinned before the instance goal was raised.
- **The arity cap refuses whole, never truncates.** A truncated telescope
  would build a lambda of the wrong arity. p26 is that refusal, with the same
  alias shape at two binders passing in the same file as its control.

An `[inst]` binder inside the goal's own telescope is likewise refused rather
than guessed: it would have to enter scope as a local instance for the
conclusion's search, which is a separate increment with its own argument.

| probe | verdict | isolates |
|---|---|---|
| `p18_goal_side_constructed` | **3 pass** (was 2/1) | the stage's exit criterion, in the corpus's exact printed shape (`(n : Nat) -> (n1 : Nat) -> Decidable (Eq {1} Nat n n1)`) |
| `p24_goal_side_telescope_no_bridge` | **10 pass** (was 8/2) | **the general capability**, with the hand-written `Decidable`/`Eq` bridge out of the picture — p18 and p09 both run through it. User-declared class, alias and global instance. `depUse` adds a DEPENDENT telescope (`(x : α) → (y : x = x) → …`) whose second binder type mentions the first binder: it kernel-checks only if abstraction reaches into binder types, not just the conclusion. In-file control `bodyIsSolvable` was passing before and after |
| `p25_goal_side_arbitrary_argument_MUST_FAIL` | 5 pass / 1 fail | **refusal — arbitrary argument.** The only instance covers `MyD (true = true)`; generalising it to `fun x y => trueMyD` must not happen. Byte-identical before and after the stage. Its in-file control `bodyAtTrue` resolves that one argument, so this is not "the instance is unreachable" |
| `p26_goal_telescope_arity_cap_MUST_FAIL` | 7 pass / 1 fail | **refusal — arity.** Nine binders exceeds `MAX_GOAL_TELESCOPE` and the goal is refused whole. Its in-file control `useNarrow` — same alias shape, two binders — flipped to PASS with this stage, so what is refused is the arity and nothing else |
| `p27_goal_side_candidate_subgoal` | **9 pass** (was 8/1 before 2026-09-10) | **the same telescope, one level DOWN**: `Pi.hasLe' : [∀ i, LE (π i)] → LE (∀ i, π i)` with only `[∀ i, Pre (π i)]` in scope (`Pre extends LE`), so the candidate's premise is `fun i => Pre.toLE` and has to be built under the candidate. A `depth == 0` guard on `resolve_pi_goal_by_abstraction` (307dc1afb, 2026-08-28) refused that; Lean's `SynthInstance.tryResolve` opens every sub-goal's telescope, at any depth. Retired 2026-09-10 — the five `Mathlib/Order/Basic.lean` regressions in `srcelab-2026-09-02-ge0b3ef7dd.json` were this guard. Six in-file controls, each one link of the chain, pass before and after; p25/p26 still refuse |
| `p28_class_typed_local_is_an_instance` | **6 pass** (was 2/4 before 2026-09-10) | **the local side**: a local is an instance because of its TYPE, not its brackets (Lean's `withNewLocalInstances` is keyed on `isClass?`). `{_ : Cls α}`, `{inst : Cls α}` and `(h : Cls α)` now count like `[Cls α]`; every push site used to test `BinderInfo::InstImplicit` only. Control `viaInst` is the bracket spelling, passing throughout. Mathlib's `uniqueElim_default {_ : Unique ι}` is this shape |
| `p29_rfl_closes_iff_and_heq` | **6 pass** (was 2/4 before 2026-09-10) | **`rfl` on every `@[refl]` relation**: `Iff.refl`/`Iff.rfl` and `HEq.refl` beside `Eq.refl`, dispatched on the goal's head as Lean's `rfl` does. Clean applied `Eq.refl` to an `Iff` goal and reported `rigid head/arity mismatch: Eq vs Iff` — the failure `Pi.preorder`'s autoParam script `by intros; rfl` hit on `Mathlib/Order/Basic.lean`. Controls `eqRfl` and `iffExact` pass throughout |

**What stage I-2 does NOT claim.** The same rule as I-1: no corpus count. The
before/after here is the 25 builtin-prelude probes of this family, mutation-proved
by rebuilding the release binary at HEAD with the repair reverted and re-running
every one of them — p18/p24/p26 move, p25 and the other 21 are byte-identical.
The Mathlib per-file delta is a corpus-box reading and is **owed**, not asserted.

## The third mask — auto-implicit swallowing an unresolved applied head

17 corpus entries, `Order/Basic` only — the row that file was pinned to expose.

| probe | verdict | isolates |
|---|---|---|
| `p14_control_term_body_MUST_FAIL` | 0 pass / 1 fail | **control.** Unresolved applied head in a VALUE position reports correctly (`UnknownIdentWithSuggestions { name: "nosuchfn" }`) — auto-implicit is off inside term bodies by design |
| `p15_sorthead_binder_type_MUST_FAIL` | 0 pass / 1 fail | the mask, fired: the same head in a BINDER TYPE is auto-bound as a fresh `Sort u`-typed fvar, and applying arguments to it fails `TooManyArguments { func_type: "Sort(Param(u_0))", remaining_args: 2 }` — the identifier deleted from the report |
| `p16_sorthead_result_type_MUST_FAIL` | 0 pass / 1 fail | the same mask in a RESULT TYPE. Rules out "binder types are elaborated in a special mode": every signature position auto-binds |

**Correction to the recon.** §2.6 and §7.5 record that a naive probe did not
fire this face, and leave the class unattributed pending "the corpus lines that
trigger auto-implicit in that position". Those lines are not needed. The recon's
probe (p14 here) put the unresolved head in a theorem *body*, where
auto-implicit is switched off on purpose; the trigger is any *signature*
position. The class is attributable from a builtin prelude, and p15/p16 attribute
it.

Stage 0 **pins** this mask and does not repair it. Naming the swallowed
identifier means either touching the five `TooManyArguments` raise sites or
refusing the auto-bind — and refusing it changes which declarations elaborate,
which a stage-0 instrument may not do. That repair is now a well-specified
follow-on with a committed trigger, which it did not have before.

## Source preconditions repaired 2026-11-06

The dated source audit retains every original fixture and both actual Lean
versions' decisions. Ordinary definition aliases in bracketed headers were
invalid Lean source; their replacements are explicitly reducible. Explicit
class field parameters are supplied. p21 now asserts Lean's actual local
precedence and retains the old wrong-global equality as a rejected control in
the audit. p22 reaches synthesis inside a term instance lambda; declaration
header annotation checks stay enabled. p24's dependent conclusion now mentions
its proof parameter, with a Sort-polymorphic reflexive instance. p26's two/nine
parameters all occur forward; both Lean versions accept the wide case, while
Clean retains its documented cap refusal. p27 uses Type _ and keeps bare
Pre.toLE. Historical measurements above belong to their original source bytes.
The registered39 assertions, exact counts and refusal fragments are unchanged;
its two registered mutation arms must be replayed for these inputs. This battery
has no Mathlib corpus count and supplies no full replacement claim.
