# FRONTIER stage I-2 — obligations PENDING on this box (honest ledger)

Date: 2026-08-26 • Lane: FRONTIER stage I-2 (CLASS I, the GOAL side — the
alias goal whose answer must be BUILT). Sibling of
[`frontier_stage1.PENDING.md`](frontier_stage1.PENDING.md), which owns the
candidate side and whose §0/§1/§3 rules apply here unchanged.

Code: `crates/clean-elab/src/infer/instance.rs`,
`ElabCtx::resolve_pi_goal_by_abstraction` — opens a Pi-shaped instance goal's
∀-telescope over fresh RIGID locals, resolves the conclusion as an ordinary
instance goal, re-abstracts into lambdas. Consulted only after the primary
search AND stage I-1's candidate-side match have both returned `None`.
Probes: `tests/fixtures/source_frontier/` p18 (re-pinned), p24, p25, p26;
gated by `scripts/source_frontier_battery.sh`.

---

## 0. The one thing that must not be misread

**No count in this lane is a corpus count**, and stage I-1's §0 says why. The
`Decidable`-shaped entries of the `instance synthesis` class are CANDIDATES to
leave that class. Clearing one face on this frontier has revealed the next four
times running — stage I-1 cleared the candidate face and revealed this one; this
stage clears the goal face and reveals §3 below.

## 1. The five-file source-elab gate re-measurement — CORPUS BOX ONLY

Not run here, and the reason is measured rather than assumed. The corpus IS
present on this box (`$HOME/mathlib4-43ad0e9d…`), so the gate starts;
what it cannot do is finish inside a session that shares a 24 GB machine with
three other build lanes:

- `clean check --imports-prefer-olean` on `Mathlib/Logic/Unique.lean` — the
  CHEAPEST of the five pinned files, 270 lines — passes **10.8 GB RSS within
  22 s** and was RSS-killed at a 9 GiB safety cap (measured 2026-08-26, both
  the HEAD and the repaired binary, identically).
- The gate's own recorded walls for the two large files are **13,932 s** and
  **11,467 s** (`scripts/source_elab_gate.sh:293`). A before/after PAIR on
  `Mathlib/Logic/Function/Basic.lean` is ~6.4 wall-hours at up to ~20 GB.

That is precisely the concurrency hazard `CLAUDE.md`'s machine-limits section
exists to prevent (two kernel panics, 2026-08-19 and 2026-08-24), so the run was
stopped rather than pushed through. The reading stays:

```
scripts/source_elab_gate.sh --jobs 2 --update
```

**The claim to make afterwards is per-declaration, never per-total**, and it
must be measured as a PAIR in one window (a HEAD binary and a repaired binary on
the same corpus under the same load) — the 2026-08-25 arming note beside
`data/source_elab_ratchet.json` is the template. Do **not** difference against
the committed baselines: they were measured at `08b7b05d9` and several lanes
have landed since, so any delta read that way is unattributable.

Two things to check in the same read, because this stage predicts them:

- The corpus entries whose printed goal is a Pi (`(x : α) -> (x1 : α) ->
  Decidable (Eq {u} α x x1)` and its concrete-carrier siblings) must **leave**
  the `instance synthesis` class. Where they land is the finding.
- The **19 non-`DecidableEq` instance-synthesis entries** (`LE`, `LT`, `SDiff`,
  `Max` on `Pi`/`Prod`/`Sum` carriers) are a different mechanism and are
  expected **unchanged**. If they move, the change was wider than its design.

## 2. Wall-time A/B at corpus scale — CORPUS BOX ONLY

Same rule as stage I-1 §2: a *share* is load-insensitive, a *rate* is not, and
this box carries other lanes. What WAS measured here is a bounded proxy, and it
is reported as one: the 25-fixture `source_frontier` family totals **6.58 s** on
a HEAD binary and **6.60 s** on the repaired one, twice each — +0.3%, at the
noise floor. That is a 25-file builtin-prelude figure and must not be quoted as
a Mathlib cost.

The structural argument is what carries the risk, not that number. The new path
is reached only on a search that has already returned `None` twice, and it is
bounded three ways: `MAX_GOAL_TELESCOPE` = 8, the recursion re-enters the
existing `MAX_DEPTH` = 32 and cycle-key machinery, and a goal that is not
ground is refused before any work is done.

**A wall regression on the five-file gate is a BLOCKER even with every verdict
green.**

## 3. The residue this stage reveals — the next brick, named

A goal that still carries **metavariables** is refused outright by design (the
`goal_is_ground` guard). The hazard is real and stated at the function: solving
the conclusion under the telescope can assign one of the goal's OWN
metavariables to a term mentioning a telescope local, and abstracting the
returned TERM does not repair the caller's metavariable context. Closing that
needs a scoped-metavariable discipline, not a wider guard — and it needs a probe
that exhibits the escape, which this lane does not have. Nothing here claims it.

Likewise an `[inst]` binder inside the goal's own telescope is refused: it would
have to enter scope as a local instance for the conclusion's search. Separate
increment, separate argument.

## 4. `scripts/source_frontier_battery.sh` green-through-its-own-gate — AFTER COMMIT

Identical to stage I-1 §4 and for the identical reason. With this lane's
fixtures uncommitted the battery prints `PROVENANCE: UNPINNED` and the artifact
records `inputs_pinned: false`. **Run once after commit:**

```
SRCFRONTIER_REQUIRE_PINNED=1 scripts/source_frontier_battery.sh
```

## 5. What WAS measured on this box before landing

All against `target/release/clean` built from this tree, `--prelude builtin`, no
Mathlib, no imports — and **mutation-proved**, not reasoned about: the repair was
reverted with `git stash`, the release binary rebuilt from that tree, and every
probe re-run against both binaries.

| probe | HEAD | with the repair |
|---|---|---|
| `p18_goal_side_constructed` | 2 pass / 1 fail | **3 pass** |
| `p24_goal_side_telescope_no_bridge` | 8 pass / 2 fail | **10 pass** |
| `p26_goal_telescope_arity_cap_MUST_FAIL` | 6 pass / 2 fail | **7 pass / 1 fail** |
| `p25_goal_side_arbitrary_argument_MUST_FAIL` | 5 pass / 1 fail | 5 pass / 1 fail |
| the other 21 fixtures | — | byte-identical, every verdict and every pinned fragment |

p24's `depUse` and p26's `useNarrow` are the two declarations that flip inside an
otherwise-unchanged file, which is what makes those files measurements rather
than assertions. p25 failing IDENTICALLY both ways is the point of p25: the
capability must not have become a blanket.
