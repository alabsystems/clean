# FRONTIER stage I-1 — obligations PENDING on this box (honest ledger)

Date: 2026-08-26 • Lane: FRONTIER stage 1 (CLASS I, the candidate side —
telescoped local instances)
Recon: `docs/analysis/frontier-next-class-2026-08-25.md`
§4 (the class), §4.3 (the recommended cut), §4.5 (staging), §6 (stage 1), §7
(what this box cannot do).
Code: `crates/clean-elab/src/infer/instance.rs`,
`ElabCtx::resolve_local_instance_telescoped` — matches (A) as-bound,
(C) whole normalised type for a **Pi-shaped** goal, (B) under the local's
∀-telescope; consulted only after the primary search returns `None`.
Probes: `tests/fixtures/source_frontier/`, gated by
`scripts/source_frontier_battery.sh`.

---

## 0. The one thing that must not be misread

**No count in this lane is a corpus count.** Recon §7.1 forbids any
success-count claim, any ratchet arming and any per-file delta from this box,
and this file asserts none. The 34 `Decidable`-shaped entries of the
`instance synthesis` class are **CANDIDATES** to leave that class. They are
not a measured gain, not a promised gain, and not a number to add to
`164/83/13/8/58`. Clearing one face on this frontier has revealed the next
three times running.

---

## 1. The five-file source-elab gate re-measurement — CORPUS BOX ONLY

This box has no Mathlib corpus (verified again 2026-08-26: `data/raw/mathlib4`
absent, `$HOME` absent — both of `scripts/source_elab_gate.sh`'s
default candidates). The gate SKIPS without one; `SRCELAB_GATE_REQUIRE_MEASURED=1`
turns that skip into a hard failure. Command, per the armed ratchet's own
recorded invocation:

```
scripts/source_elab_gate.sh --jobs 2 --update
```

**The claim to make afterwards is per-declaration, never per-total.** In the
new report's `per_error_class`, the 34 entries whose goal reads

```
failed to synthesize instance `(x : α) -> (x1 : α) -> Decidable (Eq {u} α x x1)`
```

(Function/Basic 28, Order/Basic 6) must **leave** the `instance synthesis`
class. Where they land is the finding: another class means the next face,
`success` means the declaration completed.

Two things to check in the same read, because stage I-1 predicts them:

- The **19 non-`DecidableEq` instance-synthesis entries** (`LE` 8, `LT` 7,
  `SDiff` 3, `Max` 1, on `Pi`/`Prod`/`Sum` carriers) are a different
  mechanism and are expected **unchanged**. If they move, the change was
  wider than its design and that is a finding in its own right.
- The 2026-08-25 report has **zero** `kernel free-variable leak` entries in
  Function/Basic and Order/Basic (3 in Logic/Basic). That count must not
  rise. Opening a telescope allocates one metavariable per binder, and an
  undetermined one would surface exactly there. It is refused in-tree
  (`p22_undetermined_binder_refused_MUST_FAIL`), and this is the corpus-scale
  check of that refusal.

The armed ratchet enforces the success floor independently: per-file
`success_baseline` is monotonic-up, so a regression fails closed as
`SRCELAB_GATE=failed:ratchet-regression` whatever anyone claims here.

**Correction carried forward, not fixed here** (recon §8.1): the live floor is
`164/83/13/8/58 = 326/784`, and `data/u2_stage1.PENDING.md:27` still names the
one-arming-stale `154/77/13/8/58`. Out of this lane's write scope.

## 2. Wall-time A/B at corpus scale — CORPUS BOX ONLY

Recon §7.7: profile *shares* are load-insensitive, *rates* are not, and this
box carries other lanes. What was measured here is a share (§5 below); it is
not a rate and must not be quoted as one.

The risk is real and named: instance resolution is this frontier's historical
hot path (`docs/issues/2026-08-21-mathlib-source-frontier-logic-basic.md`,
"Where the time goes" — `resolve_instance_with_depth` was 100% of
elaboration). The design's answer is structural rather than empirical: the new
code is reached **only on a search that has already returned `None`**, and
inside it, match (C) — the only one that can fire on a goal with no class
application at all — runs exactly where the primary search used to bail on its
first line and do no work whatsoever. Costs, in order of when they are paid:

- zero when no local instance binder is in scope (a `len()` check);
- one `extract_class_app` spine walk per local for match (A), no `whnf`;
- one `whnf` + one `try_unify` per local for (C)/(B), on failure paths only.

Method for the corpus-box run, unchanged from the lane that established it:
two release binaries of one tree, launched concurrently, 1 ms `sample(1)`
windows. **A wall regression on the five-file gate is a BLOCKER even with every
verdict green.**

## 3. clean-verify spec test binaries — UNKNOWN by policy

The 8.8 GB class and any `verify_runner_pinned.sh` sweep are banned on this box
by `CLAUDE.md`'s machine-limits policy (kernel panic 2026-08-19, segment
exhaustion). Those rows stay UNKNOWN here; the pinned runner on the suite box
owns them. UNKNOWN is the absence of information and is not rounded up.

## 4. `scripts/source_frontier_battery.sh` green-through-its-own-gate — AFTER COMMIT

The battery reports its provenance rather than asserting it, and
`SRCFRONTIER_REQUIRE_PINNED=1` turns the report back into an assertion. With
this lane's fixtures uncommitted it prints `PROVENANCE: UNPINNED` and the
artifact records `inputs_pinned: false` — by design, so an unpinned artifact
can never be mistaken for a pinned one. **Run once after commit:**

```
SRCFRONTIER_REQUIRE_PINNED=1 scripts/source_frontier_battery.sh
```

Until then every verdict below was still *measured*; only the pin is pending.

## 5. What WAS measured on this box before landing

All against `target/release/clean` built from this tree
(`cargo build --locked -j 2 --release -p clean --bin clean`), `--prelude
builtin`, no Mathlib, no imports.

- **The stage's exit criterion.** `p08` FAIL→PASS (0/2 → 2/0) and `p11`
  FAIL→PASS (0/1 → 1/0). Both re-pinned as PASS probes with exact declaration
  counts and renamed to drop `_MUST_FAIL`.
- **`p09` also flipped** (1/2 → 2/0), which the recon scheduled for stage I-2.
  Its carrier is a local binder of the same declaration, so the goal had to be
  found and not built. **The goal side is not therefore done** — `p18` pins the
  residue that still needs it: the same Pi-shaped alias goal with no local of
  that type. p18 carries its own in-file control showing the Pi's BODY
  (`Decidable (a = b)` at `Nat`) already resolves from the global table — so
  what is missing is the ABSTRACTION, `fun n n1 => …`, which no candidate-side
  match can build.
- **Risk axis (a), over-eager admission — five new probes.** `p19` selection
  (two alias locals at different carriers, each `if` takes its own dictionary
  and survives the kernel re-check); `p20` refusal (a local at a foreign
  carrier is still not grabbed, with its pre-existing diagnostic unchanged);
  `p21` ambiguity (a telescoped local IS a viable candidate — half 1 — and at
  a class that also has a global instance the GLOBAL still wins, measured by
  an `rfl` that closes only on the global); `p22` hygiene (an undetermined
  telescope binder is refused, not emitted); `p23` the general capability with
  the hand-written `Decidable`/`Eq` bridge removed from the picture.
- **No other verdict moved, and that was measured over the whole tree, not
  just the probe family.** Every `.lean` file under `tests/fixtures/` and
  `demos/` — **117 files**, including the `import Init` tactic-family
  fixtures, `parser_parity`, `universes`, `codata`, `pattern_lambda`,
  `namespace_shadowing`, `math_project` and the public demos — was checked
  with the BEFORE and the AFTER binary and the summary lines diffed. The diff
  is **exactly six files, all of them this stage's own probes, all in the gain
  direction**:

  | fixture | before | after |
  |---|---|---|
  | `p08_deceq_bridge` | 0 pass / 2 fail | 2 pass / 0 fail |
  | `p09_deceq_goal_face` | 1 pass / 1 fail | 2 pass / 0 fail |
  | `p11_unwhnfd_goal` | 0 pass / 1 fail | 1 pass / 0 fail |
  | `p19_control_two_carriers_selected` | 0 pass / 1 fail | 1 pass / 0 fail |
  | `p21_control_global_beats_telescoped_local` | 9 pass / 1 fail | 10 pass / 0 fail |
  | `p23_control_telescoped_local_no_bridge` | 3 pass / 1 fail | 4 pass / 0 fail |

  The other **111 files are byte-identical**. Nothing that resolved before
  resolves differently, and no declaration that passed before fails now.
- **Everyday battery** via `test_r100_everyday_battery_full`, and
  **`scripts/u2_battery.sh`** GREEN at its committed 37-pass / 9-fail-pinned
  split with every fixture digest unchanged (the artifact differs only in
  `commit` and `clean_binary_sha256`).
- **Elaboration wall-time, BEFORE vs AFTER, same tree, same box.** Two release
  binaries of one tree (the second built from the same tree with
  `crates/clean-elab/src/infer/instance.rs` reverted), 11 interleaved rounds
  per probe with the arm order alternated each round so machine drift cancels
  between the arms rather than accruing to one. Medians, reported as a
  **ratio** — a share, never a rate, per recon §7.7:

  | probe | verdicts BEFORE / AFTER | ratio after/before |
  |---|---|---:|
  | A — 400 decls, arithmetic, **no local instance binders at all** | 800 pass / 800 pass | **1.008** |
  | B — 400 decls, `class`-declared locals the PRIMARY loop answers | 801 pass / 801 pass | **1.000** |
  | C — 400 decls, `[DecidableEq a]` locals (the new path) | **800 fail / 800 pass** | **0.536** |
  | D — 400 decls, locals in scope, EVERY resolution fails on both arms | 2 pass 400 fail / identical | **1.009** |

  **D is the number that matters for regression**: identical verdicts on both
  arms, a local instance binder in scope, and every instance goal failing — so
  the new code runs to completion and finds nothing on every single failure.
  1.009 is inside this box's run-to-run spread. A and B are the untouched
  paths and read 1.008 / 1.000. C is not a regression measurement at all (the
  arms do different work); it is recorded because the AFTER arm elaborates 800
  declarations the BEFORE arm could not, in **half** the wall time — failure
  paths were the expensive ones.

  The whole set was measured twice, on two successive builds of the AFTER arm
  (before and after a `while_let_loop` clippy rewrite): 1.004 / 1.000 / 0.541 /
  1.007 and 1.008 / 1.000 / 0.536 / 1.009. The four rows are stable to the
  third decimal across independent builds, which is what makes the reading a
  share rather than one machine-state snapshot.

  This does not discharge obligation 2. It is a builtin-prelude probe set on a
  loaded box; the corpus-scale profile is still owed.

- **Two pre-existing red gates, verified NOT ours.** `scripts/tactic_parity/`'s
  G-SIMP and G-AUTO family gates are both red at HEAD against baselines
  recorded 2026-08-15 at `b33ed2b52`. Re-run with the BEFORE binary they are
  **byte-identical**: G-SIMP `pass=71/127`, the same 17 baseline rows
  regressed; G-AUTO `pass=68/131`, the same 24 rows, and the same
  `logic.lean: no parseable JSON report on stdout (exit -6)`. That abort was
  isolated to one declaration, `p_auto_aesop_11 (p q : Prop) (h : ¬(p ∨ q)) :
  ¬p := by aesop`, panicking at
  `crates/clean-elab/src/tactic/core/goal_ops.rs:540` ("focused goal target
  must be definitionally equal to its metavariable type") — a propositional
  goal with no instance binder anywhere in it, and it reproduces identically
  on the BEFORE binary. Filed here as an observation, unowned by this lane.
  Artifacts, AFTER then BEFORE:
  `reports/tactic-families/g_simp-2026-08-26-214224.json` /
  `…-215237.json`, `g_auto-2026-08-26-214354.json` / `…-215245.json`
  (the `-latest.json` symlink-equivalents were left pointing at the BEFORE
  run, since that was the last one executed). **Neither baseline was
  re-armed**: re-arming a stale family baseline is not this lane's call, and
  doing it here would have buried a pre-existing red under a stage-I-1 commit.
- `cargo check --locked --workspace` (27/27 crates) clean;
  `cargo fmt --all --check` clean; `cargo clippy --locked --workspace
  --all-targets -- -D warnings` clean (it caught one `while_let_loop` in the
  telescope walk on the first pass; rewritten, not `allow`ed);
  `cargo test --locked --lib -p clean-elab instance` — **541 passed, 0
  failed**; `test_r100_everyday_battery_full` — **63/63 pass**, name for name.

**One gate could not run in its pinned form here, and that is not a pass.**
`scripts/rust_frontend.sh` refuses when the resolved sysroot is not
`rust-toolchain.toml`'s pinned `trust` channel — and this box has no `trust`
toolchain, so the lane's mandated `RUSTUP_TOOLCHAIN=stable` makes it refuse by
design ("running the gate here would silently use a different frontend and a
different lint set"). The lint and format legs above were therefore run through
plain `cargo fmt` / `cargo clippy` on stable. That is a real check, not a
weaker spelling of the same one: the pinned frontend's lint set may differ.
**Re-run both through `scripts/rust_frontend.sh` on a box that carries the
`trust` toolchain before treating the lint leg as pinned.**

---

## 6. Corrections this stage produced (dated 2026-08-26)

1. **`p09` is not a stage I-2 probe.** The recon (§4.5, §6) scheduled the goal
   face for the goal-side telescope and expected stage I-1 to leave it red. It
   flipped at stage I-1. The reason generalises and should be carried into the
   stage I-2 plan: a `[DecidableEq α]` argument whose carrier is a **local
   binder of the same declaration** does not need its goal BUILT, only FOUND —
   the caller's `whnf` destroyed the head, but the local's `whnf` destroys it
   the same way, so the two normalised forms match. The goals that genuinely
   need the goal-side telescope are the ones at a **concrete** carrier with no
   local to match (`p18`). Stage I-2's expected yield should be re-derived on
   that basis before it is planned.
2. **The recon's §4.3 point 1 was not implemented as written, and deliberately.**
   It proposed recording each local's telescope arity and conclusion class at
   `push_local_instance`. That pays a `whnf` on **every** instance-binder push
   whether or not the search ever needs it, on a path the frontier has already
   measured as its hot one. The landed shape computes the same thing lazily, in
   the failure path, so a local that the primary loop already matches costs
   exactly zero — and `push_local_instance` keeps its current one-line body.
3. **A third match was needed that §4.3 does not name.** (A) as-bound and (B)
   under-the-telescope are §4.3's two halves; neither answers a goal the
   *caller* has already δ-unfolded into a Pi, which is the shape the corpus
   prints and the shape `p09` carries. That needed (C): unify the whole
   normalised goal against the whole normalised local. It is not the goal-side
   telescope — it opens nothing and builds nothing — which is exactly why `p18`
   still fails.
4. **(C) had to be restricted to a Pi-shaped goal, and the reason is the risk
   axis itself.** In its first form (C) unified the whole normalised goal
   against each local's whole normalised type for ANY goal with no class
   application. That is the one match here that can *solve* the goal
   expression rather than match it: handed a goal still standing as a bare
   metavariable, `try_unify` assigns `?goal := <the first local's type>` and
   returns that local — inventing the class instead of finding evidence for
   it, which is precisely the wrong-candidate failure this stage exists not to
   create. (A) and (B) are immune; both demand a rigid `Const` head on the
   goal before they look at anything. A δ-unfolded class alias is always a Pi,
   so the restriction costs the match nothing and closes the hole. Recorded
   because the hole is not visible from §4.3's description of the cut.
5. **The `is_class` gate at `instance.rs` was not the thing to widen.** Recon
   §4.2 point 3 reads the `if !self.instances.is_class(&class_name)` bail as
   the second door closing on `DecidableEq`. Widening `is_class` to know about
   `def`-based aliases would have changed which candidates the PRIMARY search
   admits, for every goal, whether or not it currently succeeds. The landed fix
   leaves that gate exactly as it is; nothing reaches the new code until the
   gated search has already failed.
