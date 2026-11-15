#!/usr/bin/env bash
# u2_battery.sh — the U2 universe-polymorphism probe battery (rung 0 of
# designs/2026-08-08-u2-universe-polymorphism-ladder.md).
#
# Pins TODAY'S measured elaborator behavior exactly: declaration-side
# polymorphism AND concrete constructor instantiation PASS (P1-P9; the
# loud rigid refusal P6 stays a FAIL pin), the remaining solver-gap
# uses FAIL with their pinned error shapes (P10-P12). Each U2
# rung names the probes it flips FAIL->PASS and this gate asserts
# everything else byte-stable. Fail-closed: any drift (a probe passing
# that must fail, failing that must pass, or failing DIFFERENTLY) exits 1.
#
# Usage: scripts/u2_battery.sh [--bin path/to/clean]
#
# 2026-08-27 RE-SPELLING, not a re-pin of behaviour. `clean check` used to
# render a TOP-LEVEL declaration's failure with `{e:?}` (Debug) and a NAMESPACED
# one with `{e}` (Display) — two rendering paths, and every fixture here is
# top-level, so every FAIL fragment below was read out of a Debug dump. Both
# paths now render through one function, Display in both
# (crates/clean-cli/src/cmd_core.rs::elaboration_error_diagnostic), so six
# fragments are re-spelled to the same facts:
#   p06/p30/p31  TypeMismatch { expected: "Sort u", actual: "Type" }
#                  -> Type mismatch: expected Sort u, got Type
#   p12          TypeMismatch { expected: "Type", actual: "Type 1" }
#                  -> Type mismatch: expected Type, got Type 1
#   p47          TypeMismatch { expected: "Sort u_0", actual: "Type" }
#                  -> Type mismatch: expected Sort u_0, got Type
#   p51          ReservedUniverseName  (the VARIANT NAME, which Display drops)
#                  -> `?u_0` is not a universe parameter name: the `?` space is reserved
# The other five FAIL fragments already pinned text INSIDE a field (the rigid
# refusal string, the level-conflict string, the closed-list message) and are
# byte-identical across the change. The rendering unification moved NO pass/fail
# verdict anywhere in tests/fixtures or demos (258 runs, both preludes,
# measured) and therefore no PASS pin here — the 2026-08-26b pass-pin moves
# below are the mint-namespace reservation's, not the rendering's.
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
BIN="${REPO_ROOT}/target/release/clean"
if [[ "${1:-}" == "--bin" ]]; then
  BIN="${2:?--bin requires a path argument}"
fi

FIX="${REPO_ROOT}/tests/fixtures/universes"
OUT_JSON="${REPO_ROOT}/reports/u2-battery.json"
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT

# PROVENANCE FIRST, BEFORE THE BINARY CHECK.
#
# Both refusals are unconditional; only their ORDER is a choice, and it is
# load-bearing for this gate's own demonstration. The registry replays
# `u2_battery`'s arm in a sandbox assembled from the working tree, and since
# 2026-09-15 that sandbox gets a cargo target dir of its OWN — so
# `target/release/clean` does not exist there, and with the binary check first
# the arm died on a missing binary before it could exercise the guard it exists
# to demonstrate. `--demonstrate` correctly refused the result: "the UNMUTATED
# gate already exits 1 — a red arm on a red tree proves nothing".
#
# Provenance does not need the binary, so checking it first costs nothing and
# makes the guard demonstrable without a release build. It is also the right
# order on its own terms: whether the inputs are trustworthy is prior to whether
# we are equipped to measure them.
for f in "$FIX"/*.lean "scripts/u2_battery.sh"; do
  rel="${f#"$REPO_ROOT"/}"
  git -C "$REPO_ROOT" ls-files --error-unmatch "$rel" > /dev/null 2>&1 \
    || { echo "[u2-battery] FAIL: gate input not tracked: $rel" >&2; exit 1; }
done
DIRTY="$(git -C "$REPO_ROOT" status --porcelain -- "$FIX" scripts/u2_battery.sh)"
[[ -z "$DIRTY" ]] || { echo "[u2-battery] FAIL: gate inputs dirty:"$'\n'"$DIRTY" >&2; exit 1; }

[[ -x "$BIN" ]] || { echo "[u2-battery] FAIL: no executable clean binary at $BIN" >&2; exit 1; }

pass_probe() { # file expected_pass_count
  local f="$1" want="$2"
  local out
  # The summary line exactly. A bare `grep passed | tail -1` read the LAST line
  # mentioning "passed", and since 29de4ae8b (2026-09-25) `clean check` follows
  # the summary with "  N passed declaration(s) rest on non-foundational
  # axiom(s) ..." whenever a file declares an axiom: p52's 5/5 read as a FAIL
  # (measured 2026-10-16).
  out="$("$BIN" check --prelude builtin "$FIX/$f" 2>&1 | grep -E "^ *[0-9]+ passed, [0-9]+ failed" | tail -1)"
  [[ "$out" == *" $want passed, 0 failed"* ]] \
    || { echo "[u2-battery] FAIL: $f expected '$want passed, 0 failed', got: $out" >&2; exit 1; }
  echo "  PASS-pinned  $f ($want decls)"
}

fail_probe() { # file expected_error_fragment
  local f="$1" frag="$2"
  local out rc=0
  out="$("$BIN" check --prelude builtin "$FIX/$f" 2>&1)" || rc=$?
  [[ "$rc" -ne 0 ]] \
    || { echo "[u2-battery] FAIL: $f must FAIL today but passed — a rung flipped it; update the battery deliberately" >&2; exit 1; }
  grep -qF "$frag" <<<"$out" \
    || { echo "[u2-battery] FAIL: $f failed with an UNPINNED shape (expected fragment '$frag'):"$'\n'"$out" >&2; exit 1; }
  echo "  FAIL-pinned  $f ($frag)"
}

echo "[u2-battery] declaration-side polymorphism (must PASS):"
pass_probe p01_poly_def_two_uses.lean 3
pass_probe p02_autobound.lean 1
pass_probe p03_struct_explicit_max.lean 1
pass_probe p04_struct_no_ascription.lean 1
pass_probe p05_inductive_explicit_sort.lean 1
pass_probe p07_explicit_mk.lean 3
pass_probe p08_implicit_mk.lean 2
pass_probe p09_concrete_solve.lean 2
pass_probe p13_poly_mtower_corec.lean 21
pass_probe p14_at_explicit_universe_inst.lean 6
# p11 RE-PINNED 5 -> 19 on 2026-10-16, a count change and not a behaviour
# change: b452e97c8 (2026-09-25) made every codata/codef command return the
# declarations it registers instead of `Skipped`, so `clean check` now checks
# and counts `codata GP`'s 14 generated declarations (GP, GP.head, GP.tail,
# GP.corec, GP.mk and their companions and computation laws) beside the five
# it counted before. All 19 pass; nothing in the fixture moved.
pass_probe p11_codata_upoly.lean 19
pass_probe p15_sigma_over_type.lean 2
pass_probe p10_inductive_default.lean 6
pass_probe p16_two_universe_mcore.lean 13
pass_probe p17_hk_functor_args.lean 7
pass_probe p19_cmp_arrow_precedence.lean 7
pass_probe p18_hk_poly_const_arg.lean 2
pass_probe p20_level_generalization.lean 7
# p46 (2026-08-25, U2 rung-4 explicitness channel) is a PASS companion to the
# written-list refusal (p54 since 2026-10-19), and it is not optional: a
# MUST_FAIL probe cannot tell a precise refusal from an over-broad one, because
# both satisfy it. Four neighbouring shapes — a complete written `.{u, v}`, a
# DETERMINED `Type _` hole under a written list, no written list at all
# (p21's `leak` minus the `.{u}`), and the `universe`-merged case the rung-4
# scope cut existed for. Each is followed by an `@f.{...}` use site that
# forces the registered ARITY.
pass_probe p46_explicit_list_complete.lean 8
# p21 FLIPPED BACK 2026-10-19 from a FAIL pin to a PASS pin, and renamed back
# from `p21_explicit_list_closed_MUST_FAIL.lean`. A refusal-REMOVING re-pin,
# landed on its own with its MUST_FAIL twin p54 (below). The 2026-08-25 flip
# read Lean's `sortDeclLevelParams` as treating a written list as exhaustive;
# it appends every used level the list does not name, and
# `levelMVarToParamTypesPreDecls` (Lean/Elab/MutualDef.lean:1406) makes a
# level metavariable left in the declaration's TYPE such a level. The pinned
# v4.30.0-rc2 accepts this file with no error (`leak.{u, u_1}`,
# `noAns.{u, u_1}`), and its use sites force arity 2. BEFORE (tip 6ef3be510,
# this gate): FAIL with 'the explicit universe list `.{u}` is closed'. The
# history is docs/FRONTEND_CLASS_LEDGER.md class (164).
pass_probe p21_explicit_list_autoextends.lean 5
pass_probe p22_exists_working_forms.lean 5
pass_probe p23_exists_intro.lean 3
pass_probe p24_prelude_fidelity.lean 23
pass_probe p25_nat_homogeneous_instances.lean 7
pass_probe p26_rfl_match_pattern.lean 3
pass_probe p27_quotient_setoid.lean 8
pass_probe p28_bare_ctor_expected_type.lean 4

# Auto-bound universes (2026-08-14). p29 pins that legitimate auto-bound
# POLYMORPHISM still works — `u` is never forced, so it survives as a real
# parameter and `@k.{0}` accepts a universe argument. Its FAIL-pinned sibling
# p30 is below.
pass_probe p29_autobound_undeclared.lean 2
pass_probe p32_mutual_poly_ok.lean 2
# p33 FLIPPED 2026-08-14: universe-polymorphic `class ... extends` now
# elaborates. p35 pins that it also RESOLVES AND COMPUTES — elaborating is
# not the same as working, and a probe that only checks the former would be
# satisfied by a declaration no user can use.
pass_probe p33_class_extends_upoly.lean 2
pass_probe p35_class_extends_upoly_resolves.lean 6
# p36 FLIPPED 2026-08-14: the `Type _` hole spelling of class-extends. Its
# `level_params` drifted from the expressions because canonicalization renames
# minted params AFTER the list is fixed; a declared param is its own
# representative, which is why only this spelling broke.
pass_probe p36_class_extends_hole.lean 2
pass_probe p34_structure_extends_upoly_ok.lean 2
pass_probe p37_hole_universe_polymorphic.lean 8
pass_probe p38_hole_type_argument_levels.lean 5
# p41 (2026-08-25, U2 stage 1): level identity across the ElabCtx↔ProofState
# bridge. rw/apply/cases through `.{u}`-polymorphic lemmas inside `Sort u`/
# `Sort v` goals — the tactic layer's fresh level params can no longer alias
# the declaration's by name, its kernel checks resolve solved levels, and the
# exit path realizes tactic-side solutions. All were sub-class-A loud rejects
# (`expected Sort(Param(u_X)), inferred Sort(Param(u_0))`) or spurious
# RewriteNoMatch before the bridge fix.
pass_probe p41_tactic_bridge_level_identity.lean 8
# p43 (2026-08-25, U2 stage 2): a Sort-typed metavariable assigned a PI TYPE
# gets its level equation generated — `infer_level_for_type` covers Pi. All
# were sub-class-B loud rejects at the decl-close kernel re-check before
# (`expected Sort(Param(u_N)), got Sort(Max(Succ(..), Succ(..)))` — the
# Function.hasUncurryBase / Set.SeparatesPoints / Pi.map_id class), except
# the marked in-file controls. The rigid-conflict twin is p44 below.
pass_probe p43_pi_sort_meta_level.lean 9
# p45 (2026-08-25, U2 stage 3): the level-mint registry. Every declaration
# here was MEASURED double-minting one `u_N` across the ElabCtx and the
# ProofState inside a single tactic block, with the two authorities holding
# DIFFERENT values for that name at the bridge exit (elabctx=S(0) vs
# proofstate=u/v, and the abstract-vs-concrete direction) — the stage-1
# residual, exhibited. One shared monotone counter makes the aliasing
# impossible. All seven kernel-check before AND after: this is a REGRESSION
# pin on the shapes, not a flip pin. The identity property itself is pinned
# structurally by `infer::tests::tactic_bridge_levels`.
pass_probe p45_bridge_mint_registry.lean 7
# p48 (2026-08-26, U2 stage-3 deferral 1) is the PRECISION companion to p47's
# refusal below, and it is not optional: a MUST_FAIL probe cannot tell a
# precise refusal from an over-broad one, because an elaborator that rejected
# every `u_N`-spelled universe — or that made every `Sort _` hole rigid —
# would satisfy p47 exactly as well as the real fix. Four shapes, one per way
# a `u_N` spelling legitimately reaches a declaration: the collision itself
# used polymorphically, a bare level hole (holes must stay SOLVABLE), a
# written `u_1` with no mint in the declaration, and a declared `.{u_2}` —
# plus p49's rename control, which is p49's own declaration with one
# identifier renamed and must keep PASSING or p49 stops being about the
# spelling.
#
# 5 -> 7 on 2026-08-26b, with the mint-namespace reservation. Two shapes were
# ADDED, neither cosmetic: `useIdCollide` is the ARITY witness for shape 1
# (`idCollide` now carries TWO universe parameters where the conflated reading
# gave one — `@idCollide.{1}` reports `expected: 2, actual: 1` — and a
# declaration that merely elaborates proves nothing about how many universes
# survived), and `guillemetUniverse` is p51's precision control (a guillemet
# universe name containing a `?` must keep elaborating, or p51's refusal is
# "guillemets are rejected" rather than "the `?`-leading space is reserved").
pass_probe p48_mint_name_collision_precision.lean 7
# p49 FLIPPED 2026-08-26b from a FAIL pin to a PASS pin, and was renamed from
# `p49_mint_collision_overconstraint_MUST_FAIL.lean` — the old name states the
# behaviour that just went away. This is the flip the deferral ledger
# designated (`data/u2_stage3_deferrals.PENDING.md`, "Follow-up this work NAMES
# but does not do", route 1: reserve the mint namespace).
#
# BEFORE (release binary at 2ce2cf2c1, this same gate): `0 passed, 1 failed` —
# `def n3 (β : Sort _) (γ : Sort u_0) (y : γ) (l : List β) : Nat := 0` was
# refused with `cannot assign rigid universe parameter u_0 := u_1 + 1`, while
# the same declaration spelled `Sort w` passed. Lean accepts both. p47's cure
# for the silent-monomorphization defect (classify the name by ROLE and promote
# a WRITTEN one to rigid) could not make the two levels DISTINCT, so it
# resolved the clash by making both occurrences one RIGID level — loud instead
# of silent, but still a refusal Lean does not make, and still spelling-
# dependent.
#
# Universe metavariables are now minted into a reserved namespace the surface
# grammar cannot produce (`?u_0`, `?u_1`, …), so a written name and a minted
# one are never the same string and the collision cannot be constructed. The
# solver, the rigid set and `clean_kernel::Level` are all untouched.
#
# The fixture is the positive shape, not a deletion: three spellings (two
# holes / hole + `w` / hole + `u_0`) each with an ARITY witness that
# instantiates it at two DIFFERENT levels, which typechecks only if two
# independent parameters reached registration. p47 must keep failing with its
# fragment byte-identical — that is what proves the reservation removed the
# cost WITHOUT relaxing the refusal.
pass_probe p49_mint_collision_independence.lean 6
# p50 (2026-08-26) is a TRIPWIRE, not a flip: it pins the direction p47 does
# NOT cover — "should be ASSIGNABLE, treated as RIGID". That class was probed
# the same day and found UNREACHABLE, so nothing was implemented for it; these
# six declarations fail if it ever becomes reachable. The hazard is a rigid
# name surviving into the NEXT declaration while the shared mint reissues the
# same `u_N`, which would make a fresh metavariable born rigid and produce
# `cannot assign rigid universe parameter u_0 := …` on a declaration that
# never wrote `u_0`. The bridge's DELIBERATE rigidity inside a tactic block is
# a different thing and is p42's.
pass_probe p50_rigid_does_not_leak_across_decls.lean 6
# p53 ADDED 2026-09-10: `universe u v w` declares NAMES, and a declaration's
# level parameters are the ones that OCCUR in it (Lean's collectLevelParams).
# preprocess.rs used to merge EVERY declared universe into EVERY declaration,
# so `class Cls (α : Type u)` registered as `Cls.{u, v, w}` and each later
# `[Cls α]` binder minted two level metavariables nothing could constrain --
# `useIt`/`clsThm2` died at the kernel with `Type mismatch: expected Cls α,
# got Cls α` (levels differ). Measured 4/2 before, 6/0 after; the controls
# (`universe u` alone; `Type*` everywhere) were 6/0 throughout, so the only
# variable is the unused declared names. The walk is syntactic and fail-closed
# (crates/clean-elab/src/universe_occurrence.rs): a tactic block anywhere
# outside a field default falls back to the old over-inclusive merge.
pass_probe p53_unused_declared_universe.lean 6

echo "[u2-battery] pinned failures (the solver gap + defaults + gates):"
fail_probe p06_rigid_refusal_MUST_FAIL.lean 'Type mismatch: expected Sort u, got Type'
fail_probe p12_sigma_over_type_MUST_FAIL.lean 'Type mismatch: expected Type, got Type 1'
# p30 is p06's body with the `.{u}` REMOVED, and it must fail IDENTICALLY: an
# auto-bound universe name is a genuine parameter, so the rigid refusal has to
# fire whether the name was declared or inferred. It did NOT before 2026-08-14
# — `u` solved to 1 and the decl registered monomorphic with empty
# level_params. Same pinned shape as p06 is the point of this probe.
fail_probe p30_autobound_rigid_refusal_MUST_FAIL.lean 'Type mismatch: expected Sort u, got Type'
# p31 is p06's body wrapped in `mutual`, and must fail IDENTICALLY. The mutual
# and inductive paths bypassed `set_decl_universe_params` (6 sites), so a
# DECLARED `.{u}` was not rigid there — worse than p30, where the universe was
# merely inferred. p32 pins that the fix did not become over-strict.
fail_probe p31_mutual_rigid_refusal_MUST_FAIL.lean 'Type mismatch: expected Sort u, got Type'
fail_probe p39_hole_rigid_refusal_MUST_FAIL.lean "cannot assign rigid universe parameter u := 1"
# 2026-09-10 rendering-only correction: 954a9ea94e (2026-08-31) replaced
# Debug levels in unify_meta's concrete-conflict diagnostic with
# error_render::level (Display). The ground-level checks and Level::leq guard
# did not change: p40 still refuses expected level 0 versus inferred level 1.
# Keep both ordered levels and the nonzero-exit check, not a generic conflict
# substring. p37's eight passing declarations retain the permitted direction.
fail_probe p40_hole_level_conflict_MUST_FAIL.lean "universe level conflict: 0 vs 1"
# p42 is p41's genuinely-conflicting twin: a Type-monomorphic lemma applied
# inside a rigid `Sort u` goal needs `u := 1`, and the SEEDED rigid set now
# refuses it inside the tactic block with the same message the declaration
# layer uses (p39). If this fragment degrades into a raw Sort(Param) mismatch,
# the bridge has regressed to level-blind checking.
fail_probe p42_tactic_bridge_rigid_refusal_MUST_FAIL.lean "cannot assign rigid universe parameter u := 1"
# p44 is p43's genuinely-conflicting twin: monoSolve's shape over DECLARED
# (rigid) universes. The stage-2 Pi arm generates `max(succ u, succ v) =?= 1`,
# which needs `u := 0` — refused rigid, INSIDE unification, with the same
# message family as p39/p42. Before stage 2 this fixture also failed, but
# blind: an opaque decl-close kernel mismatch (`expected Sort(Succ(Zero)),
# got Sort(Max(Succ(..), Succ(..)))`) because the equation was never
# generated. If this fragment degrades back into that raw Sort mismatch,
# the Pi arm of `infer_level_for_type` has regressed to generating nothing.
fail_probe p44_pi_sort_meta_rigid_MUST_FAIL.lean "cannot assign rigid universe parameter u := 0"
# p54 ADDED 2026-10-19, p21's MUST_FAIL twin: the written-list refusal that
# remains. A level left ONLY in a declaration's value is never generalized;
# Lean refuses it ("declaration `useZ` contains universe level metavariables
# ... in the declaration body", pinned v4.30.0-rc2), and Clean refuses it when
# the declaration wrote a `.{...}` list. With no written list Clean still
# generalizes it (the OPEN half of class (164)). If this probe ever passes, the
# value-only refusal regressed; read p21 and p46 before assuming a new refusal
# here is precise.
fail_probe p54_explicit_list_value_only_level_MUST_FAIL.lean \
  'that its type does not mention and the explicit universe list `.{u}` does not name'
# p47 ADDED 2026-08-26 (U2 stage-3 deferral 1). This is p30's
# silent-monomorphization class reached through the MINT-NAME door, and it is
# a refusal-ADDING re-pin of a shape that PASSED before — a new FAIL pin, not
# a flip of an existing one, so it lands with its own dated note.
#
# BEFORE (release binary at 9cd4f68f6): `def badAutoCollide (β : Sort _) :
# Sort u_0 := Nat` → `1 passed, 0 failed`, while the SAME declaration spelled
# `Sort w` was correctly refused. `ElabCtx::universe_params` is the UNION of
# the rigid names and the MINTED ones (`fresh_universe_param` pushes there so
# the next mint skips the name), and the auto-bind path tested membership in
# it to decide "already a parameter". The `Sort _` hole minted `u_0` first, so
# the WRITTEN `u_0` never reached the rigid set and solved to 1. p30's own
# tell followed verbatim: `def asType : Type := badAutoCollide Nat`
# typechecked, and `@badAutoCollide.{0}` reported
# `UniverseLevelMismatch { name: "badAutoCollide", expected: 0, actual: 1 }` —
# ZERO universe parameters survived. Lean rejects the declaration.
#
# The fixture carries the `Sort w` rename control on the line above the
# collision, so the pinned fragment below (`Sort u_0`) is what proves the
# collision half. If it ever passes again, the role classifier
# (`crate::level_role`) has regressed to using the union as a rigidity proxy;
# read p48 before assuming any new refusal here is precise.
fail_probe p47_autobound_mint_name_collision_MUST_FAIL.lean 'Type mismatch: expected Sort u_0, got Type'
# p51 ADDED 2026-08-26b with the mint-namespace reservation, and it is what
# makes that reservation a CHECKED property rather than a lexer accident.
# Metavariable names are spelled `?u_N`, and `?` is not an identifier-start
# character, so `Sort ?u_0` has no production in the level grammar. But a
# guillemet identifier passes its contents through verbatim — measured at
# 2ce2cf2c1, before the reservation, `def gq (γ : Sort «my?weird») (y : γ) :
# γ := y` reported `1 passed, 0 failed` — so `Sort «?u_0»` was a door straight
# back into the namespace, and with it the whole p47/p49 collision class.
# `elab_level` now refuses any written universe name in the `?` space.
#
# The refusal is scoped to names that BEGIN with `?`. p48's
# `guillemetUniverse` is the control that says so and must keep passing;
# without it this probe would be satisfied by "reject guillemet universes" or
# "reject any `?` in a universe name".
fail_probe p51_reserved_mint_namespace_MUST_FAIL.lean \
  '`?u_0` is not a universe parameter name: the `?` space is reserved'

# p52 ADDED here 2026-09-19, not by the commit that added the FIXTURE. The simp
# binder-domain fix landed `tests/fixtures/universes/p52_simp_binder_domain.lean`
# without a probe line, and this battery's `split` is built from the probes that
# RUN while its `fixtures` map is globbed from the directory — so the file was in
# one and not the other and `parity_tiers --check` went FAIL-CLOSED on
# `in fixtures only: ['p52']`, blocking every lane's push. That the two halves
# disagree at all is the useful part: a fixture cannot be added here without
# being pinned.
#
# What it pins: simp must not bind a `Prop`-declared lemma binder to a `Sort u`
# term. Simp mints one metavariable per lemma binder with the PLACEHOLDER type
# `Expr::type_()` and `MetaState::assign` never type-checks, so `capRhs`'s
# `(p : Prop)` binder used to capture `γ : Sort v` and the ill-typed `@capRhs γ`
# reached `close_goal`'s `infer_type_strict`. The third declaration is the one
# that matters — both lemmas are offered, and the honest universe-polymorphic
# one only gets its turn if the ill-typed match is refused first. The two
# controls either side of it keep the guard from being satisfied by refusing
# everything. Measured today: 5 passed, 0 failed.
pass_probe p52_simp_binder_domain.lean 5


GIT_SHA="$(git -C "$REPO_ROOT" rev-parse HEAD)"
python3 - "$OUT_JSON" "$GIT_SHA" "$BIN" "$FIX" "${BASH_SOURCE[0]}" <<'PY'
import json, sys, hashlib, glob, os, re
out, sha, bin_path, fix, script = sys.argv[1:6]
def sha256(p):
    return hashlib.sha256(open(p, "rb").read()).hexdigest()
# Stage-0 repair (2026-08-25, U2 stage 1): the split is DERIVED from the
# probe calls in this script, never hand-maintained — the 2026-08-23
# artifact shipped a hardcoded 32/4 split while the gate ran 34/6
# (docs/analysis/u2-implementation-plan-2026-08-24.md §4.1).
script_text = open(script).read()
split_pass = sorted(set(re.findall(r"^pass_probe (p\d+)", script_text, re.M)))
split_fail = sorted(set(re.findall(r"^fail_probe (p\d+)", script_text, re.M)))
report = {
    "schema": "u2-battery-v1",
    "commit": sha,
    "clean_binary_sha256": sha256(bin_path),
    "fixtures": {os.path.basename(p): sha256(p) for p in sorted(glob.glob(f"{fix}/*.lean"))},
    "split": {
        "pass": split_pass,
        "fail_pinned": split_fail,
    },
    "note": "P6 is a SOUND loud reject (rigid refusal) and stays a FAIL pin "
            "forever; P8/P9 FLIPPED at rung 2 (structure-ctor params were "
            "explicit, not a solver gap); P13 pins the rung-6 lane OPEN: the "
            ".{u}-polymorphic indexed M-tower + coherence + Subtype carrier + "
            "IMcorec + rfl head law (21 decls) all elaborate+kernel-check on "
            "the rung-2+1a+3a elaborator. P10 FLIPPED at rung 5 "
            "(omitted-sort inference from ctor fields, .{u}-declared only); "
            "P11 FLIPPED at rung 7 part 2 "
            "(codata .{u} live, rfl-computing at u=0 and u=1); P12's `: Type` "
            "large-Sigma is a SOUND forever-reject like P6 (ill-typed in Lean "
            "too) with P15 pinning the working Type-1 forms; "
            "P14 FLIPPED same day: "
            "the parser bound argument-position .{} to the application head "
            "(f.{u+1} PUnit instead of PUnit.{u+1}) — fixed like projection "
            "attachment — see the U2 ladder doc. "
            "P41/P42 added 2026-08-25 (U2 stage 1, the ElabCtx-ProofState "
            "level-identity bridge): p41 pins the flipped sub-class-A shapes "
            "(rw/apply/cases through .{u}-polymorphic lemmas in Sort u/v "
            "goals), p42 pins that a genuine tactic-level conflict still "
            "refuses with the p39 rigid-refusal message. "
            "P43/P44 added 2026-08-25 (U2 stage 2, sub-class B): p43 pins "
            "that a Sort-typed metavariable assigned a PI TYPE gets its "
            "level equation generated (infer_level_for_type covers Pi; the "
            "hasUncurryBase/arrow-id/Sort*-imax/Prop-imp/dependent-Pi faces "
            "all kernel-check), p44 pins that the newly-generated equation "
            "refuses LOUDLY at the constraint site when it needs a rigid "
            "param (u := 0), instead of the old blind decl-close mismatch. "
            "P45 added 2026-08-25 (U2 stage 3, the level-mint registry): the "
            "five measured double-mint shapes — an ElabCtx mint and a "
            "ProofState mint of the SAME u_N inside one tactic block, holding "
            "different values at the bridge exit — now draw from one shared "
            "monotone counter and cannot alias. A REGRESSION pin (all seven "
            "kernel-check before and after); the identity property is pinned "
            "structurally in infer::tests::tactic_bridge_levels. "
            "P21 FLIPPED 2026-08-25 (U2 rung-4 explicitness channel) from a "
            "PASS pin to a FAIL pin, and was renamed "
            "p21_explicit_list_autoextends.lean -> "
            "p21_explicit_list_closed_MUST_FAIL.lean, on the reading that an "
            "explicit `.{...}` universe list is exhaustive in Lean's "
            "sortDeclLevelParams; it FLIPPED BACK 2026-10-19 (renamed back, "
            "PASS pin, 5 decls), because Lean appends every used level the "
            "list does not name and generalizes a level metavariable left in "
            "the declaration's TYPE into one (v4.30.0-rc2: leak.{u, u_1}, "
            "noAns.{u, u_1}; FRONTEND_CLASS_LEDGER class (164)). P54 added "
            "the same day pins the refusal that remains: a level left only "
            "in the VALUE under a written list, which Lean refuses too. The "
            "channel is ElabCtx::file_universe_params: "
            "preprocess merges file-scope `universe` names into the same "
            "vector as the written list, and subtracting them is what "
            "recovers the written list, which is precisely the distinction "
            "the 2026-08-09 rung-4 scope cut lacked. P46 added the same day "
            "as the mandatory PASS companion (four neighbouring shapes, "
            "arity-forcing use sites): a refusal with no companion cannot be "
            "distinguished from an over-refusal. "
            "P47/P48/P50 added 2026-08-26 (U2 stage-3 deferral 1): p47 pins "
            "p30's silent-monomorphization class reached through the "
            "MINT-NAME door (a written universe name that collided with a "
            "name its own declaration had minted read as already-a-parameter, "
            "never became rigid, and solved away), closed by the total "
            "LevelParamRole classification; p48 is its precision companion; "
            "p50 is a permanent tripwire for the direction p47 does NOT "
            "cover (assignable-treated-as-rigid), probed the same day and "
            "found unreachable. "
            "P49 FLIPPED 2026-08-26b from a FAIL pin to a PASS pin and was "
            "renamed p49_mint_collision_overconstraint_MUST_FAIL.lean -> "
            "p49_mint_collision_independence.lean. It pinned the MEASURED "
            "COST of closing p47 without a LevelMVarId: because level "
            "identity is Level::Param(Name), promoting a written name to "
            "rigid made the hole and the written u_N ONE rigid level, so "
            "`def n3 (b : Sort _) (g : Sort u_0) (y : g) (l : List b) : Nat "
            ":= 0` was refused (cannot assign rigid universe parameter u_0 "
            ":= u_1 + 1) where the identical `Sort w` spelling passed — a "
            "refusal Lean does not make. Universe METAVARIABLES are now "
            "minted into a RESERVED namespace the surface grammar cannot "
            "produce (?u_0, ?u_1, ...; crate::level_mint::MINT_PREFIX), so a "
            "written name and a minted one are never the same string and the "
            "collision cannot be constructed at all. No solver, rigid-set or "
            "clean_kernel::Level change. Registered names did not move: a "
            "surviving mint is renamed into the writable space at "
            "declaration close by fresh_generalized_universe_param, drawing "
            "from the same counter (holeOnly kept u_1 at 2ce2cf2c1 and keeps "
            "u_1 now). P51 added the same day makes the reservation a "
            "CHECKED property rather than a lexer accident — a guillemet "
            "identifier (Sort <<?u_0>>) bypasses the lexer's identifier "
            "rules and is refused with ReservedUniverseName — and p48 grew "
            "the two controls that keep both new pins precise: an ARITY "
            "witness (idCollide now carries TWO universe parameters) and a "
            "non-reserved guillemet universe that must keep passing.",
    "gate_command": "scripts/u2_battery.sh",
}
json.dump(report, open(out, "w"), indent=2)
print(f"[u2-battery] GREEN — wrote {out}")
PY
