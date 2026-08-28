// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! R9 of the candidate-model construction ladder — the DELTA rung: build item
//! **B3**, the δ-rank witness for the REAL reflected environment, is landed
//! **COMPUTED** rather than carried; the `const` rule joins the judgment as
//! `SynTyC`; and the blocker that four earlier rungs mis-named is PROVED to be
//! somewhere else entirely.
//!
//! ## A — B3: the rank is COMPUTED, not assumed
//!
//! R2, R4, R7 and R8 all closed with the same sentence: the δ/`redConst` rung
//! "needs a `WfEnv`/`EnvAcyclic` rank witness for the real reflected env", and
//! R2 spelled the shape it would have to be assumed in:
//!
//! ```text
//! delta_step (red_def the_red_env) (const c us) body -> const_occurs c2 body
//!   -> Lt (rk c2) (rk c)
//! ```
//!
//! It does not have to be assumed. `the_red_env` is `kernel_core_red_env`, a
//! CONCRETE, FIXED, FINITE reflected environment, so the rank can be computed
//! for the actual environment and the decrease proved the way R3/R4 proved
//! ι-deadness and δ-deadness at concrete heads: by kernel computation.
//! Measured here on the generated env (`generated/kernel_core_red_env.defs.txt`):
//! the `DefEnv` is a **50-entry** `DefEnv.addDef` chain over 127 interned names,
//! its δ-dependency graph has **67 edges**, it is **ACYCLIC**, and its longest
//! δ-chain is **7** — so `rk` ranges over `0..8`. It is acyclic for a structural
//! reason worth recording: the reflection compiles every recursive kernel
//! definition through the corresponding `.rec`, so not one of the 50 bodies
//! mentions its own name.
//!
//! The route is the established one-rfl checker pattern (`env_closed_checkers.rs`
//! §"Why checkers"), not a 50-way case analysis:
//!
//! 1. `rk : Name -> Nat` — a 127-entry rank TABLE indexed by the interned
//!    numeral of a `Name.str Name.anonymous k`, `Nat.zero` for every other name.
//!    Table-lookup rather than a `name_eqb` cascade on purpose: the checker
//!    evaluates `rk` once per const occurrence and there are **963** of them
//!    across the 50 bodies, so a 50-deep decidable-equality cascade over unary
//!    numerals up to 126 would be ~10^7 reduction steps where a list walk is
//!    ~10^5.
//! 2. `const_occurs : Name -> KExpr -> Bool` — the corpus's `Tm.mentions`
//!    (`LetDeltaSN.lean`), Bool-valued to match the surrounding checker style.
//!    Checked first: no `const_occurs`/`mentions` analogue existed in
//!    `core_spec`; `occurs_in` (`env_extensions.rs`) is about de Bruijn
//!    self-reference, not const names.
//! 3. `rank_dominates_b r e` — every const occurring in `e` has `rk` below `r`.
//! 4. `def_env_ranked_b env` — the fold of (3) at each entry's own rank.
//! 5. `the_red_env_ranked : def_env_ranked_b (red_def the_red_env) = true`, ONE
//!    `Eq.refl`. **That is B3.**
//! 6. Two generic soundness lemmas (`def_env_ranked_b_sound` by `DefEnv.rec`,
//!    `rank_dominates_occurs` by `KExpr.rec`) plus the bare-const δ inversion
//!    `delta_step_defval_inv` compose (5) into
//!    `the_red_env_delta_rank_decrease` — **R2's statement character for
//!    character, DISCHARGED**.
//!
//! `the_red_env_no_delta_cycle` is the corollary that names what B3 actually
//! buys: no constant of the real kernel foundation core δ-unfolds to a term
//! mentioning itself. That is `EnvAcyclic` for `the_red_env`, proved.
//!
//! ## B — the `const` rule, and the blocker that was never the rank
//!
//! With the rank in hand the δ const rule was supposed to follow. It does not,
//! and the reason is measured, not guessed:
//!
//! - **The engine exists and is landed.** `candInterp_delta_expand_sort` is
//!   R2's `candExp_delta` at a SORT-typed slot — legitimate for exactly R8's
//!   `candInterp_zeta_expand_sort` reason: `candInterp (sort m) e` REDUCES to
//!   `whnf_acc e`, the base whole-SN set, which IS an `IsCandSet`.
//! - **At a Pi-typed slot it is BLOCKED, and not by acyclicity.** R5's
//!   interpretation is only `IsCandHF` — its cr3 additionally demands
//!   `HeadFree e`, i.e. `kexpr_const_name (kapp_fn e) = none` — and R5 PROVED
//!   that restriction necessary at the real env (`piSet_cr3_headFree_necessary`,
//!   whose counterexample is a stuck `Nat.rec` spine). A bare const is the
//!   canonical NON-head-free term: `r9_const_is_neutral` shows unrestricted cr3
//!   would apply, `r9_const_headfree_absurd` shows the head-free face does not,
//!   and `r9_const_obstruction_located` pairs them in one kernel-checked
//!   constant.
//! - **At a sort-typed slot the δ rule is landed and is VACUOUS OVER THIS ENV,
//!   proved.** `SynTyC.konstDelta` types `const c us` at `sort m` from a
//!   derivation of its unfolding at `sort m`. Over `the_red_env` no such
//!   derivation exists, because **all 50 real definition bodies are `KExpr.lam`**
//!   (`r9_the_red_env_all_lam`, one `Eq.refl` over the real env) and `SynTyC`
//!   types no `lam` at a `sort` (`synTyC_no_lam_at_sort`). The two compose into
//!   `r9_konstDelta_no_real_instance`. This is a labeled by-design vacuity in
//!   the design's §6.3 sense — measured, not asserted — and the rule is kept
//!   because it is the sound general clause and its engine is the deliverable.
//! - **What IS non-vacuous is the DEAD half.** `SynTyC.konstDead` types
//!   `const c us` at any sort when `defval_for (red_def the_red_env) c = none`:
//!   such a const is whnf-STUCK (no β at a const head, no ι at a bare const, no
//!   δ), so `whnfAcc_const_dead` gives it membership outright. Over the real env
//!   that is every name outside the 50 — every reflected inductive type,
//!   constructor and recursor. `synTyC_konst_dead_witness` types the REAL
//!   reflected `DefEnv` constant and `synTyC_sn_konst_witness` gets its SN
//!   THROUGH the capstone. This is the first rung of the ladder whose judgment
//!   reaches `KExpr.const` at all.
//!
//! **So the honest verdict of the rung: the rank was never the blocker.** It is
//! computable, and computing it costs one `Eq.refl`. What blocks `redConst` at
//! the Pi-typed slot is head-freeness — R5's already-measured wall — and what
//! blocks it at the sort-typed slot is that real definition bodies are functions
//! while the fragment's sort-typed terms are not.
//!
//! ## Premise freedom, guarded exactly as R6/R7/R8 guard theirs
//!
//! ```text
//! synTyC_fundamental : SynTyC G e T -> forall s, SubstOK s G -> candInterp T (psubst s e)
//! synTyC_sn_subst    : SynTyC G e T -> forall s, SubstOK s G -> whnf_acc (psubst s e)
//! synTyC_sn          : SynTyC G e T -> whnf_acc e
//! synTyC_sn_closed   : SynTyC nil e T -> whnf_acc e
//! ```
//!
//! carry NO premise — no `CandModel`, no `RecEnvClosed`, no `RecEnvLiftClosed`,
//! no `DefEnvClosed`, and (the one that matters here) **no `EnvAcyclic`**: the
//! acyclicity B3 establishes is a discharged theorem about a fixed env, never a
//! hypothesis of the capstone chain. The shape guard refuses every one of those
//! names in the statements and in `SynTyC`'s own source.
//!
//! `SynTyC` does mention `the_red_env` — through `defval_for` in `konstDead` and
//! `delta_step` in `konstDelta` — and that is unavoidable rather than sloppy: δ
//! is env-relative, so a const rule that named no environment would be a rule
//! about no reduction. Both side conditions are discharged per-constant by
//! `Eq.refl`, so they cost the capstone nothing.
//!
//! ## The bridge, and its direction
//!
//! `synTyL_to_synTyC : SynTyL G e T -> SynTyC G e T`, with NO hypothesis (R8's
//! bridge needed `CtxSimple G`; this one does not, because R9 changes no rule of
//! R8's — it only adds two). The CONVERSE is FALSE and is proved so:
//! `synTyL_no_const` shows no `SynTyL` derivation concludes at a `const`
//! EXPRESSION in any context at any type, while `synTyC_konst_dead_witness` is
//! one. `synTyL_sn_via_synTyC` re-derives R8's capstone through R9's; R8's own
//! `synTyL_sn` is NOT superseded.
//!
//! ## Honesty notes (read before quoting)
//!
//! - **Nothing here discharges `M : CandModel tenv`.** `synTyC_sn` is SN for
//!   `SynTyC`, NOT for `TypingCtx`, and must never be described as advancing
//!   `whnf_terminates_well_typed_dependent` (design §6.2).
//! - **B3 is a fact about ONE environment.** `the_red_env_delta_rank_decrease`
//!   quantifies over every `c`, `us`, `body`, `c2`, but its content is
//!   `the_red_env`'s; the generic halves (`def_env_ranked_b_sound`,
//!   `rank_dominates_occurs`) hold at every env, the `Eq.refl` does not. A
//!   regeneration of the reflection that introduced a δ-cycle would fail
//!   `the_red_env_ranked` CLOSED rather than drift.
//! - **`rk` is a rank, not a semantics.** Any `Name -> Nat` making the checker
//!   pass would do; this one is the longest-δ-chain depth plus one for the 50
//!   defined names and `Nat.zero` elsewhere, which is why an undefined name
//!   (rank 0) is below every defined one. It reads only the interned numeral of
//!   a `Name.str Name.anonymous k` and is `Nat.zero` on every other `Name`
//!   shape; correctness of the decrease does not depend on that choice, because
//!   `rank_dominates_occurs` recovers the occurring name itself through
//!   `name_eqb_eq` before applying `rk`.
//! - **What still separates `SynTyC` from `TypingCtx`, after this rung:**
//!   (1) the const rules are of a DIFFERENT KIND. `TypingCtx.const` is
//!   `Eq (tenv n) (some A) -> TypingCtx tenv G (const n us) A` — a declared type
//!   read off a `tenv`, at ANY `A`, Pi types included. `SynTyC` has no `tenv`
//!   at all: it reaches a const only at a SORT, only when the const is δ-DEAD,
//!   plus a δ clause that is vacuous over this env (§B). Closing THAT gap is
//!   not a rank problem either — it is the head-free wall again, since a
//!   `tenv`-declared constant at a Pi type is precisely the case cr3 cannot
//!   introduce;
//!   (2) `app` is NON-DEPENDENT and `lam` still carries `SimpleTy A`, both
//!   forced by R5's non-dependent Pi clause, whose dependent version is PROVED
//!   non-portable (`r6_dependent_pi_self_reachable`);
//!   (3) the `let_` rule is the sort-annotated fragment only (R8 §B);
//!   (4) `lam` has no `TypingCtx G A (sort u)` premise and `SynTyC` has no
//!   conversion rule;
//!   (5) NEW, and named for the first time here: no rule reaches a const at a
//!   PI type at all, and R5's `piSet_cr3_headFree_necessary` says none can
//!   without an UNRESTRICTED cr3 for `PiSet` — which that constant refutes at
//!   the real env.
//! - **The judgment is not total.** `synTyC_not_total`: `r5_omegaLam` — a
//!   strongly normalizing term — is not `SynTyC`-derivable at
//!   `pi (sort 0) (sort 0)` in ANY context. The `micro_has_type` total-predicate
//!   trap guard; no automated gate performs it.
//! - **Every predicate R9 introduces in hypothesis position is WITNESSED here.**
//!   `SynTyC` is concluded by `synTyC_id`, `synTyC_sort_witness` and
//!   `synTyC_konst_dead_witness`; constructors do not count on the supply side,
//!   which is why those are registered definitions and why the ladder guard
//!   `test_candmodel_ladder_premises_are_witnessed` names `SynTyC`. The Bool
//!   predicates enter hypothesis position as `Eq Bool _ Bool.true`, whose head
//!   is `Eq`; `r9_rank_decrease_witness` supplies a concrete `const_occurs`
//!   true-instance at a real `kcre_*` pair anyway.
//! - **Recursor conventions are taken from landed consumers, not guessed.**
//!   ALL FIELDS FIRST, THEN ALL IHs, in constructor order. `SynTyC.pi`,
//!   `SynTyC.app` and `SynTyC.letTy` have TWO recursive premises,
//!   `SynTyC.lam` and `SynTyC.konstDelta` one, `SynTyC.var`, `SynTyC.sort` and
//!   `SynTyC.konstDead` none. Pinned by the shape guard. A `.rec` IH binder is
//!   typed at what the MOTIVE produces at that premise, never at the underlying
//!   type (R8's measured 2026-08-25 failure). R9 adds the sequel measured
//!   2026-08-26: when the motive's result also has to sit in a Pi CODOMAIN, an
//!   inline `KExpr.rec` discriminator is not a sort the elaborator accepts
//!   there, so `r9_sort_discr` / `r9_const_discr` are registered defs with a
//!   declared `Type` result rather than inline applications.
//! - **No `fixedIndicesToParams` promotion.** The leading `(G : ListType KExpr)`
//!   is uniform across the eight conclusions, but the `pi`, `lam` and `letTy`
//!   recursive premises conclude at `ListType.cons KExpr _ G`, so the first
//!   index is not fixed.
//! - **Prop/Type discipline.** `Eq`, `delta_step` and `HeadFree` are Prop;
//!   `candInterp T`, `SynTyC`, `SimpleTy`, `SubstOK`, `Neutral`, `whnf_acc`,
//!   `Lt` and `Empty` are Type. `AndType (A : Type) (B : Type)` is `Type 0` and
//!   the kernel is NON-CUMULATIVE, so `r9_const_obstruction_located` pairs
//!   `Neutral` with an ARROW into `Empty` rather than with the `Eq` itself.
//!   `opt_bind_some_inv` and `opt_pick_some_inv` take `(C : Prop)` and are
//!   therefore used only at `Eq`-shaped goals; `bool_false_ne_true_t`,
//!   `option_none_ne_some_type` and `bor_eq_true_inv` take `(C : Type)` and are
//!   used only at Type-shaped ones.
//!
//! ## Census
//!
//! ZERO new axioms: one genuine inductive via `add_inductive`, six plain defs
//! via `add_recursive_def`, everything else a value-bearing theorem via
//! `add_definition` with kernel `add_decl` checking. Census-neutral.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

// ==== R9 SOURCES BEGIN (pure string builders; every source in this region is ====
// ==== pre-validated through the clean-parser / scratch-spec harness).        ====

/// `bvar 0`.
const V0: &str = "(KExpr.bvar Nat.zero)";
/// `sort 0`, the fragment's base type.
const S0: &str = "(KExpr.sort Level.zero)";
/// `sort 1`.
const S1: &str = "(KExpr.sort (Level.succ Level.zero))";
/// The non-dependent function type `pi (sort 0) (sort 0)`.
const PI00: &str = "(KExpr.pi (KExpr.sort Level.zero) (KExpr.sort Level.zero))";
/// The fragment's identity function, annotated at the base type.
const IDLAM0: &str = "(KExpr.lam (KExpr.sort Level.zero) (KExpr.bvar Nat.zero))";
/// The empty context.
const NILCTX: &str = "(ListType.nil KExpr)";
/// The empty universe-parameter list.
const NILUS: &str = "(ListType.nil Level)";
/// The fixed definition environment every δ statement here is relative to.
const DENV: &str = "(red_def the_red_env)";
/// A REAL reflected kernel name with NO definitional value: `DefEnv`, the
/// inductive type. `defval_for (red_def the_red_env) kcre_name_12` computes to
/// `none`.
const DEADNAME: &str = "kcre_name_12";
/// The bare const at that name.
const DEADCONST: &str = "(KExpr.const kcre_name_12 (ListType.nil Level))";
/// A REAL reflected kernel name that IS delta-defined — the outermost `DefEnv`
/// entry `def_env_lift_closed_b` (R2's `kcre_witness_delta_head`), whose value
/// is `kcre_witness_delta_value`.
const LIVECONST: &str = "(KExpr.const kcre_witness_delta_head (ListType.nil Level))";
/// The name occurring in that value: `def_env_closed_b` (rank 4 against the
/// head's rank 5).
const LIVEREF: &str = "kcre_name_90";

// ================================================================
// Group A — B3: `const_occurs`, the COMPUTED rank, and the δ-decrease.
// ================================================================

/// The δ-rank table over the 127 interned reflected names, index-aligned to
/// `kcre_name_<i>`.
///
/// `0` means "not a definition of `the_red_env`" — every reflected inductive
/// type, constructor and recursor. A defined name gets `1 + d` where `d` is the
/// length of the longest δ-chain out of it, so a defined name always outranks an
/// undefined one and the whole table is bounded by `8`. Derived mechanically
/// from `generated/kernel_core_red_env.defs.txt` (50 entries, 67 edges,
/// acyclic); the kernel re-derives its adequacy in one step through
/// `the_red_env_ranked`, so a table that stopped matching the env would fail
/// CLOSED rather than be believed.
const R9_RANKS: [u8; 127] = [
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, //   0- 9
    0, 0, 0, 0, 0, 1, 0, 0, 0, 0, //  10-19  (15 Nat.add)
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, //  20-29
    0, 2, 0, 1, 2, 0, 0, 0, 0, 0, //  30-39  (31 Nat.sub, 33 opt_bind, 34 kapp_args)
    0, 0, 0, 0, 4, 1, 0, 0, 0, 0, //  40-49  (44 name_eqb, 45 Bool.and)
    1, 1, 0, 0, 0, 0, 1, 1, 2, 3, //  50-59  (50 apply_spine .. 59 nat_eqb)
    1, 1, 1, 0, 0, 0, 0, 0, 0, 0, //  60-69  (60-62 recmeta_num_*)
    0, 0, 0, 0, 0, 0, 0, 2, 1, 1, //  70-79  (77 bvar_ceiling, 78, 79)
    0, 0, 0, 0, 1, 0, 0, 0, 0, 1, //  80-89  (84 Nat.pred, 89 bool_pick)
    4, 5, 7, 6, 5, 4, 3, 1, 1, 1, //  90-99  (90 def_env_closed_b .. 96 lift_bvar_at)
    1, 1, 1, 5, 4, 5, 1, 6, 5, 1, // 100-109
    5, 0, 0, 0, 0, 0, 0, 0, 5, 6, // 110-119 (118 def_env_lift_closed_b, 119 delta_reduct)
    8, 7, 5, 6, 1, 1, 1, // 120-126 (120 instantiate, 121 iota_reduct)
];

/// A unary `Nat` literal.
fn nat_lit(n: u8) -> String {
    let mut s = "Nat.zero".to_string();
    for _ in 0..n {
        s = format!("(Nat.succ {s})");
    }
    s
}

/// How many table entries live in one chunk def.
///
/// The table CANNOT be one 127-deep `ListType.cons` spine: the parser refuses
/// at nesting depth 129 (`max 128`, measured 2026-08-26 — the first cut of this
/// rung died exactly there). Chunking into 16-entry defs, each ending in a
/// reference to the next chunk, keeps every source under depth ~25 while the
/// VALUE is the same 127-element list, because a chunk def is a plain
/// definitional alias the kernel unfolds.
const R9_TBL_CHUNK: usize = 16;

/// The chunk defs, innermost (last) first — the order they must be registered
/// in, since each names the next.
pub(super) fn src_r9_rank_tbl_chunks() -> Vec<(String, String)> {
    let n = R9_RANKS.len();
    let starts: Vec<usize> = (0..n).step_by(R9_TBL_CHUNK).collect();
    let mut out: Vec<(String, String)> = Vec::new();
    for (idx, start) in starts.iter().enumerate().rev() {
        let end = (start + R9_TBL_CHUNK).min(n);
        let tail = if idx + 1 == starts.len() {
            "(ListType.nil Nat)".to_string()
        } else {
            format!("r9_rank_tbl_{}", starts[idx + 1])
        };
        let mut acc = tail;
        for r in R9_RANKS[*start..end].iter().rev() {
            acc = format!("(ListType.cons Nat {} {acc})", nat_lit(*r));
        }
        let name = format!("r9_rank_tbl_{start}");
        out.push((name.clone(), format!("def {name} : ListType Nat := {acc}")));
    }
    out
}

pub(super) fn src_r9_rank_tbl() -> String {
    "def r9_rank_tbl : ListType Nat := r9_rank_tbl_0".to_string()
}

/// `r9_rank_nth k l` — the `k`-th entry of `l`, `Nat.zero` past the end.
///
/// An explicit `Nat.rec` with a `ListType Nat -> Nat` motive (the `nat_lt_b`
/// idiom) rather than a `match`, so the reduction behaviour on a concrete index
/// is the one the checker needs and nothing depends on match compilation.
pub(super) const SRC_R9_RANK_NTH: &str = "def r9_rank_nth (k : Nat) (l : ListType Nat) : Nat := Nat.rec (fun (_ : Nat) => ListType Nat -> Nat) (fun (l0 : ListType Nat) => ListType.rec Nat (fun (_ : ListType Nat) => Nat) Nat.zero (fun (x : Nat) (_ : ListType Nat) (_ : Nat) => x) l0) (fun (_ : Nat) (ih : ListType Nat -> Nat) => fun (l0 : ListType Nat) => ListType.rec Nat (fun (_ : ListType Nat) => Nat) Nat.zero (fun (_ : Nat) (rest : ListType Nat) (_ : Nat) => ih rest) l0) k l";

pub(super) const SRC_RK: &str = "def rk (c : Name) : Nat := Name.rec (fun (_ : Name) => Nat) Nat.zero (fun (p : Name) (k : Nat) (_ : Nat) => Name.rec (fun (_ : Name) => Nat) (r9_rank_nth k r9_rank_tbl) (fun (_ : Name) (_ : Nat) (_ : Nat) => Nat.zero) p) c";

pub(super) const SRC_CONST_OCCURS: &str = r"def const_occurs (c : Name) (e : KExpr) : Bool := match e with
| KExpr.sort n => Bool.false
| KExpr.bvar i => Bool.false
| KExpr.app f a => Bool.or (const_occurs c f) (const_occurs c a)
| KExpr.lam ty b => Bool.or (const_occurs c ty) (const_occurs c b)
| KExpr.pi ty b => Bool.or (const_occurs c ty) (const_occurs c b)
| KExpr.const n us => name_eqb c n
| KExpr.let_ ty v b => Bool.or (const_occurs c ty) (Bool.or (const_occurs c v) (const_occurs c b))
| KExpr.proj s i sub => const_occurs c sub
| KExpr.lit n => Bool.false";

pub(super) const SRC_RANK_DOMINATES_B: &str = r"def rank_dominates_b (r : Nat) (e : KExpr) : Bool := match e with
| KExpr.sort n => Bool.true
| KExpr.bvar i => Bool.true
| KExpr.app f a => Bool.and (rank_dominates_b r f) (rank_dominates_b r a)
| KExpr.lam ty b => Bool.and (rank_dominates_b r ty) (rank_dominates_b r b)
| KExpr.pi ty b => Bool.and (rank_dominates_b r ty) (rank_dominates_b r b)
| KExpr.const n us => nat_lt_b (rk n) r
| KExpr.let_ ty v b => Bool.and (rank_dominates_b r ty) (Bool.and (rank_dominates_b r v) (rank_dominates_b r b))
| KExpr.proj s i sub => rank_dominates_b r sub
| KExpr.lit n => Bool.true";

pub(super) const SRC_DEF_ENV_RANKED_B: &str = r"def def_env_ranked_b (env : DefEnv) : Bool := match env with
| DefEnv.empty => Bool.true
| DefEnv.addDef tail dname val => Bool.and (rank_dominates_b (rk dname) val) (def_env_ranked_b tail)";

pub(super) fn ty_the_red_env_ranked() -> String {
    format!("Eq Bool (def_env_ranked_b {DENV}) Bool.true")
}

pub(super) const VAL_THE_RED_ENV_RANKED: &str = "Eq.refl Bool Bool.true";

pub(super) const TY_BOOL_CASES_EQ: &str =
    "forall (p : Bool) (C : Type), (Eq Bool p Bool.true -> C) -> (Eq Bool p Bool.false -> C) -> C";

/// CASE ANALYSIS BY REFLECTION, and the shape matters.
///
/// The obvious spelling — `Bool.rec` with a motive that GENERALIZES the
/// continuations (`fun b => (Eq Bool b Bool.true -> C) -> …`) — is what the
/// first cut of this rung used, and the elaborator refused it on 2026-08-26:
/// `expected Eq Bool <fvar> Bool.true, got cannot unify … Discriminant(3) vs
/// Discriminant(1)`, i.e. it would not instantiate the motive's binder against
/// a minor whose declared type names `Bool.false` where the motive names the
/// binder BARE. `band_eq_true_left` / `band_eq_true_right` (the landed, working
/// Bool inversions) never do that: their motive mentions the binder only INSIDE
/// `Bool.and zp q`, and their minors take ONE binder.
///
/// So this uses the reflection motive `fun zp => Eq Bool p zp -> C`, where the
/// binder likewise appears only as an argument of `Eq`, each minor takes one
/// binder, and the recursor is applied to `p` and then to `Eq.refl Bool p`.
pub(super) const VAL_BOOL_CASES_EQ: &str = "fun (p : Bool) (C : Type) (kt : Eq Bool p Bool.true -> C) (kf : Eq Bool p Bool.false -> C) => Bool.rec (fun (zp : Bool) => Eq Bool p zp -> C) (fun (hf : Eq Bool p Bool.false) => kf hf) (fun (ht : Eq Bool p Bool.true) => kt ht) p (Eq.refl Bool p)";

pub(super) const TY_BOR_FALSE_CASE: &str = "forall (q : Bool) (p : Bool), Eq Bool p Bool.false -> Eq Bool (Bool.or p q) Bool.true -> Eq Bool q Bool.true";

/// No `Bool.rec` at all: rewrite `p` to `Bool.false` inside the hypothesis and
/// let the RETURN-position ascription do the `Bool.or Bool.false q` reduction —
/// which is `band_eq_true_right`'s true arm verbatim in shape, the one place
/// the elaborator is measured to perform this reduction.
pub(super) const VAL_BOR_FALSE_CASE: &str = "fun (q : Bool) (p : Bool) (hp : Eq Bool p Bool.false) (h : Eq Bool (Bool.or p q) Bool.true) => Eq.subst Bool (fun (w : Bool) => Eq Bool (Bool.or w q) Bool.true) p Bool.false hp h";

pub(super) const TY_BOR_EQ_TRUE_INV: &str = "forall (p : Bool) (q : Bool) (C : Type), Eq Bool (Bool.or p q) Bool.true -> (Eq Bool p Bool.true -> C) -> (Eq Bool q Bool.true -> C) -> C";

pub(super) const VAL_BOR_EQ_TRUE_INV: &str = "fun (p : Bool) (q : Bool) (C : Type) (h : Eq Bool (Bool.or p q) Bool.true) (kl : Eq Bool p Bool.true -> C) (kr : Eq Bool q Bool.true -> C) => bool_cases_eq p C kl (fun (hf : Eq Bool p Bool.false) => kr (bor_false_case q p hf h))";

pub(super) const TY_DEF_ENV_RANKED_B_SOUND: &str = "forall (env : DefEnv) (dname : Name) (defval : KExpr), Eq (OptionType KExpr) (defval_for env dname) (OptionType.some KExpr defval) -> Eq Bool (def_env_ranked_b env) Bool.true -> Eq Bool (rank_dominates_b (rk dname) defval) Bool.true";

pub(super) fn val_def_env_ranked_b_sound() -> String {
    let goal = "Eq Bool (rank_dominates_b (rk dname) defval) Bool.true";
    let motive = format!("(fun (e : DefEnv) => Eq (OptionType KExpr) (defval_for e dname) (OptionType.some KExpr defval) -> Eq Bool (def_env_ranked_b e) Bool.true -> {goal})");
    let m_empty = format!("(fun (hlk : Eq (OptionType KExpr) (defval_for DefEnv.empty dname) (OptionType.some KExpr defval)) (_hb : Eq Bool (def_env_ranked_b DefEnv.empty) Bool.true) => option_none_ne_some KExpr defval ({goal}) hlk)");
    // The FIRE branch is where this differs from def_env_closed_b_sound: the
    // per-entry test mentions the entry's OWN name, so the rank has to be
    // transported along name_eqb_eq before the value is.
    let m_add = format!(
        "(fun (tail : DefEnv) (dn : Name) (dv : KExpr) (ih : Eq (OptionType KExpr) (defval_for tail dname) (OptionType.some KExpr defval) -> Eq Bool (def_env_ranked_b tail) Bool.true -> {goal}) (hlk : Eq (OptionType KExpr) (defval_for (DefEnv.addDef tail dn dv) dname) (OptionType.some KExpr defval)) (hb : Eq Bool (def_env_ranked_b (DefEnv.addDef tail dn dv)) Bool.true) => opt_pick_some_inv KExpr (name_eqb dn dname) dv (defval_for tail dname) defval ({goal}) hlk (fun (ht : Eq Bool (name_eqb dn dname) Bool.true) (hval : Eq KExpr dv defval) => Eq.subst KExpr (fun (w : KExpr) => Eq Bool (rank_dominates_b (rk dname) w) Bool.true) dv defval hval (Eq.subst Name (fun (w : Name) => Eq Bool (rank_dominates_b (rk w) dv) Bool.true) dn dname (name_eqb_eq dn dname ht) (band_eq_true_left (rank_dominates_b (rk dn) dv) (def_env_ranked_b tail) hb))) (fun (_hf : Eq Bool (name_eqb dn dname) Bool.false) (htail : Eq (OptionType KExpr) (defval_for tail dname) (OptionType.some KExpr defval)) => ih htail (band_eq_true_right (rank_dominates_b (rk dn) dv) (def_env_ranked_b tail) hb)))"
    );
    format!("fun (env : DefEnv) (dname : Name) (defval : KExpr) => DefEnv.rec {motive} {m_empty} {m_add} env")
}

pub(super) const TY_RANK_DOMINATES_OCCURS: &str = "forall (r : Nat) (c2 : Name) (e : KExpr), Eq Bool (rank_dominates_b r e) Bool.true -> Eq Bool (const_occurs c2 e) Bool.true -> Lt (rk c2) r";

pub(super) fn val_rank_dominates_occurs() -> String {
    let goal = "Lt (rk c2) r";
    let ih = |x: &str| {
        format!("Eq Bool (rank_dominates_b r {x}) Bool.true -> Eq Bool (const_occurs c2 {x}) Bool.true -> {goal}")
    };
    let motive = format!("(fun (qe : KExpr) => Eq Bool (rank_dominates_b r qe) Bool.true -> Eq Bool (const_occurs c2 qe) Bool.true -> {goal})");
    // A leaf mentions no const at all, so its occurrence hypothesis is
    // Eq Bool Bool.false Bool.true.
    let leaf = |binders: &str, subj: &str| {
        format!("(fun {binders} (_hd : Eq Bool (rank_dominates_b r {subj}) Bool.true) (ho : Eq Bool (const_occurs c2 {subj}) Bool.true) => bool_false_ne_true_t ({goal}) ho)")
    };
    let a_sort = leaf("(qn : Level)", "(KExpr.sort qn)");
    let a_bvar = leaf("(qi : Nat)", "(KExpr.bvar qi)");
    let a_lit = leaf("(qv : Nat)", "(KExpr.lit qv)");
    // A binary former splits the Bool.or on the occurrence and projects the
    // matching Bool.and conjunct out of the domination hypothesis.
    let binary = |ctor: &str, l: &str, rr: &str| {
        let subj = format!("(KExpr.{ctor} {l} {rr})");
        format!(
            "(fun ({l} : KExpr) ({rr} : KExpr) (qih1 : {}) (qih2 : {}) (hd : Eq Bool (rank_dominates_b r {subj}) Bool.true) (ho : Eq Bool (const_occurs c2 {subj}) Bool.true) => bor_eq_true_inv (const_occurs c2 {l}) (const_occurs c2 {rr}) ({goal}) ho (fun (h1 : Eq Bool (const_occurs c2 {l}) Bool.true) => qih1 (band_eq_true_left (rank_dominates_b r {l}) (rank_dominates_b r {rr}) hd) h1) (fun (h2 : Eq Bool (const_occurs c2 {rr}) Bool.true) => qih2 (band_eq_true_right (rank_dominates_b r {l}) (rank_dominates_b r {rr}) hd) h2))",
            ih(l),
            ih(rr)
        )
    };
    let a_app = binary("app", "qf", "qa");
    let a_lam = binary("lam", "qlty", "qlb");
    let a_pi = binary("pi", "qpty", "qpb");
    // THE ARM THAT DOES THE WORK: the domination test at a const IS
    // nat_lt_b (rk n) r, and the occurrence test IS name_eqb c2 n, so
    // name_eqb_eq turns the second into the identification that lets the first
    // be read at c2.
    let a_const = "(fun (qn : Name) (qus : ListType Level) (hd : Eq Bool (rank_dominates_b r (KExpr.const qn qus)) Bool.true) (ho : Eq Bool (const_occurs c2 (KExpr.const qn qus)) Bool.true) => Eq.substType Name (fun (w : Name) => Lt (rk w) r) qn c2 (Eq.symm Name c2 qn (name_eqb_eq c2 qn ho)) (nat_lt_b_sound (rk qn) r hd))".to_string();
    let a_let = format!(
        "(fun (qlty : KExpr) (qlv : KExpr) (qlb : KExpr) (qih1 : {}) (qih2 : {}) (qih3 : {}) (hd : Eq Bool (rank_dominates_b r (KExpr.let_ qlty qlv qlb)) Bool.true) (ho : Eq Bool (const_occurs c2 (KExpr.let_ qlty qlv qlb)) Bool.true) => bor_eq_true_inv (const_occurs c2 qlty) (Bool.or (const_occurs c2 qlv) (const_occurs c2 qlb)) ({goal}) ho (fun (h1 : Eq Bool (const_occurs c2 qlty) Bool.true) => qih1 (band_eq_true_left (rank_dominates_b r qlty) (Bool.and (rank_dominates_b r qlv) (rank_dominates_b r qlb)) hd) h1) (fun (hrest : Eq Bool (Bool.or (const_occurs c2 qlv) (const_occurs c2 qlb)) Bool.true) => bor_eq_true_inv (const_occurs c2 qlv) (const_occurs c2 qlb) ({goal}) hrest (fun (h2 : Eq Bool (const_occurs c2 qlv) Bool.true) => qih2 (band_eq_true_left (rank_dominates_b r qlv) (rank_dominates_b r qlb) (band_eq_true_right (rank_dominates_b r qlty) (Bool.and (rank_dominates_b r qlv) (rank_dominates_b r qlb)) hd)) h2) (fun (h3 : Eq Bool (const_occurs c2 qlb) Bool.true) => qih3 (band_eq_true_right (rank_dominates_b r qlv) (rank_dominates_b r qlb) (band_eq_true_right (rank_dominates_b r qlty) (Bool.and (rank_dominates_b r qlv) (rank_dominates_b r qlb)) hd)) h3)))",
        ih("qlty"),
        ih("qlv"),
        ih("qlb")
    );
    let a_proj = format!(
        "(fun (qps : Name) (qpidx : Nat) (qsub : KExpr) (qihs : {}) (hd : Eq Bool (rank_dominates_b r (KExpr.proj qps qpidx qsub)) Bool.true) (ho : Eq Bool (const_occurs c2 (KExpr.proj qps qpidx qsub)) Bool.true) => qihs hd ho)",
        ih("qsub")
    );
    format!("fun (r : Nat) (c2 : Name) (e : KExpr) => KExpr.rec {motive} {a_sort} {a_bvar} {a_app} {a_lam} {a_pi} {a_const} {a_let} {a_proj} {a_lit} e")
}

pub(super) const TY_DELTA_STEP_DEFVAL_INV: &str = "forall (env : DefEnv) (c : Name) (us : ListType Level) (body : KExpr), delta_step env (KExpr.const c us) body -> Eq (OptionType KExpr) (defval_for env c) (OptionType.some KExpr body)";

pub(super) const VAL_DELTA_STEP_DEFVAL_INV: &str = "fun (env : DefEnv) (c : Name) (us : ListType Level) (body : KExpr) (hd : delta_step env (KExpr.const c us) body) => opt_bind_some_inv KExpr KExpr (defval_for env c) (fun (v : KExpr) => OptionType.some KExpr v) body (Eq (OptionType KExpr) (defval_for env c) (OptionType.some KExpr body)) hd (fun (w : KExpr) (hw : Eq (OptionType KExpr) (defval_for env c) (OptionType.some KExpr w)) (hfw : Eq (OptionType KExpr) (OptionType.some KExpr w) (OptionType.some KExpr body)) => Eq.trans (OptionType KExpr) (defval_for env c) (OptionType.some KExpr w) (OptionType.some KExpr body) hw hfw)";

pub(super) fn ty_the_red_env_delta_rank_decrease() -> String {
    format!("forall (c : Name) (us : ListType Level) (body : KExpr) (c2 : Name), delta_step {DENV} (KExpr.const c us) body -> Eq Bool (const_occurs c2 body) Bool.true -> Lt (rk c2) (rk c)")
}

pub(super) fn val_the_red_env_delta_rank_decrease() -> String {
    format!("fun (c : Name) (us : ListType Level) (body : KExpr) (c2 : Name) (hd : delta_step {DENV} (KExpr.const c us) body) (ho : Eq Bool (const_occurs c2 body) Bool.true) => rank_dominates_occurs (rk c) c2 body (def_env_ranked_b_sound {DENV} c body (delta_step_defval_inv {DENV} c us body hd) the_red_env_ranked) ho")
}

pub(super) const TY_R9_LT_IRREFL: &str = "forall (n : Nat), Lt n n -> Empty";

pub(super) const VAL_R9_LT_IRREFL: &str = "fun (n : Nat) (h : Lt n n) => Lt.rec (fun (qa : Nat) (qb : Nat) (_ : Lt qa qb) => Eq Nat qa qb -> Empty) (fun (qn : Nat) (hq : Eq Nat Nat.zero (Nat.succ qn)) => Eq.substType Nat (fun (w : Nat) => Nat.rec (fun (_ : Nat) => Type) Nat (fun (_ : Nat) (_ : Type) => Empty) w) Nat.zero (Nat.succ qn) hq Nat.zero) (fun (qn : Nat) (qm : Nat) (_qh : Lt qn qm) (qih : Eq Nat qn qm -> Empty) (hq : Eq Nat (Nat.succ qn) (Nat.succ qm)) => qih (Eq.cong Nat Nat (fun (w : Nat) => Nat.rec (fun (_ : Nat) => Nat) Nat.zero (fun (p : Nat) (_ : Nat) => p) w) (Nat.succ qn) (Nat.succ qm) hq)) n n h (Eq.refl Nat n)";

pub(super) fn ty_the_red_env_no_delta_cycle() -> String {
    format!("forall (c : Name) (us : ListType Level) (body : KExpr), delta_step {DENV} (KExpr.const c us) body -> Eq Bool (const_occurs c body) Bool.true -> Empty")
}

pub(super) fn val_the_red_env_no_delta_cycle() -> String {
    format!("fun (c : Name) (us : ListType Level) (body : KExpr) (hd : delta_step {DENV} (KExpr.const c us) body) (ho : Eq Bool (const_occurs c body) Bool.true) => r9_lt_irrefl (rk c) (the_red_env_delta_rank_decrease c us body c hd ho)")
}

// ================================================================
// Group B — the const engine, the dead-const clause, and the LOCATED
// obstruction at the Pi-typed slot.
// ================================================================

pub(super) fn ty_r9_const_delta_dead() -> String {
    format!("forall (c : Name) (us : ListType Level), Eq (OptionType KExpr) (defval_for {DENV} c) (OptionType.none KExpr) -> forall (g2 : KExpr) (C : Type), delta_step {DENV} (KExpr.const c us) g2 -> C")
}

pub(super) fn val_r9_const_delta_dead() -> String {
    let dead = format!("(Eq.cong (OptionType KExpr) (OptionType KExpr) (fun (o : OptionType KExpr) => opt_bind KExpr KExpr o (fun (v : KExpr) => OptionType.some KExpr v)) (defval_for {DENV} c) (OptionType.none KExpr) hn)");
    format!("fun (c : Name) (us : ListType Level) (hn : Eq (OptionType KExpr) (defval_for {DENV} c) (OptionType.none KExpr)) (g2 : KExpr) (C : Type) (hd : delta_step {DENV} (KExpr.const c us) g2) => option_none_ne_some_type KExpr g2 C (Eq.trans (OptionType KExpr) (OptionType.none KExpr) (delta_reduct {DENV} (KExpr.const c us)) (OptionType.some KExpr g2) (Eq.symm (OptionType KExpr) (delta_reduct {DENV} (KExpr.const c us)) (OptionType.none KExpr) {dead}) hd)")
}

pub(super) fn ty_whnfacc_const_dead() -> String {
    format!("forall (c : Name) (us : ListType Level), Eq (OptionType KExpr) (defval_for {DENV} c) (OptionType.none KExpr) -> whnf_acc (KExpr.const c us)")
}

pub(super) fn val_whnfacc_const_dead() -> String {
    format!("fun (c : Name) (us : ListType Level) (hn : Eq (OptionType KExpr) (defval_for {DENV} c) (OptionType.none KExpr)) => whnf_acc.intro (KExpr.const c us) (fun (e2 : KExpr) (hs : whnf_step (KExpr.const c us) e2) => constRedex_whnf_inv c us e2 (whnf_acc e2) hs (fun (hdl : delta_step {DENV} (KExpr.const c us) e2) => r9_const_delta_dead c us hn e2 (whnf_acc e2) hdl))")
}

pub(super) fn ty_candinterp_delta_expand_sort() -> String {
    format!("forall (m : Level) (c : Name) (us : ListType Level) (body : KExpr), delta_step {DENV} (KExpr.const c us) body -> candInterp (KExpr.sort m) body -> candInterp (KExpr.sort m) (KExpr.const c us)")
}

pub(super) fn val_candinterp_delta_expand_sort() -> String {
    format!("fun (m : Level) (c : Name) (us : ListType Level) (body : KExpr) (hd : delta_step {DENV} (KExpr.const c us) body) (hb : candInterp (KExpr.sort m) body) => candExp_delta (fun (e : KExpr) => whnf_acc e) isCand_whnfAcc c us body hd hb")
}

pub(super) const TY_R9_CONST_IS_NEUTRAL: &str =
    "forall (c : Name) (us : ListType Level), Neutral (KExpr.const c us)";

pub(super) const VAL_R9_CONST_IS_NEUTRAL: &str =
    "fun (c : Name) (us : ListType Level) => ConstFreeUnit.triv";

pub(super) const TY_R9_CONST_HEADFREE_ABSURD: &str = "forall (c : Name) (us : ListType Level), Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.const c us))) (OptionType.none Name) -> Empty";

pub(super) const VAL_R9_CONST_HEADFREE_ABSURD: &str = "fun (c : Name) (us : ListType Level) (h : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.const c us))) (OptionType.none Name)) => option_none_ne_some_type Name c Empty (Eq.symm (OptionType Name) (OptionType.some Name c) (OptionType.none Name) h)";

pub(super) const TY_R9_CONST_OBSTRUCTION_LOCATED: &str = "forall (c : Name) (us : ListType Level), AndType (Neutral (KExpr.const c us)) (Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.const c us))) (OptionType.none Name) -> Empty)";

pub(super) const VAL_R9_CONST_OBSTRUCTION_LOCATED: &str = "fun (c : Name) (us : ListType Level) => AndType.intro (Neutral (KExpr.const c us)) (Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.const c us))) (OptionType.none Name) -> Empty) ConstFreeUnit.triv (r9_const_headfree_absurd c us)";

// ================================================================
// Group C — the judgment.
// ================================================================

/// `TypingCtx.var`'s rule, transcribed (R8's, unchanged).
const VAR_RULE_LIFTED: &str = "| var : forall (G : ListType KExpr) (i : Nat) (A : KExpr), Eq (OptionType KExpr) (ctx_lookup G i) (OptionType.some KExpr A) -> SynTyC G (KExpr.bvar i) (lift_at A Nat.zero (Nat.succ i))";

/// `TypingCtx.pi`'s formation rule, transcribed (R8's, unchanged).
const PI_RULE_IMAX: &str = "| pi : forall (G : ListType KExpr) (A : KExpr) (B : KExpr) (n : Level) (m : Level), SynTyC G A (KExpr.sort n) -> SynTyC (ListType.cons KExpr A G) B (KExpr.sort m) -> SynTyC G (KExpr.pi A B) (KExpr.sort (Level.imax n m))";

/// The zeta rule at R8's sort-annotated fragment.
const LET_RULE_SORT: &str = "| letTy : forall (G : ListType KExpr) (n : Level) (m : Level) (v : KExpr) (b : KExpr), SynTyC G v (KExpr.sort n) -> SynTyC (ListType.cons KExpr (KExpr.sort n) G) b (KExpr.sort m) -> SynTyC G (KExpr.let_ (KExpr.sort n) v b) (KExpr.sort m)";

/// THE DEAD-CONST RULE: a constant with no definitional value in the real
/// reflected env is whnf-STUCK, hence in the base candidate at any sort.
const KONST_DEAD_RULE: &str = "| konstDead : forall (G : ListType KExpr) (c : Name) (us : ListType Level) (m : Level), Eq (OptionType KExpr) (defval_for (red_def the_red_env) c) (OptionType.none KExpr) -> SynTyC G (KExpr.const c us) (KExpr.sort m)";

/// THE DELTA RULE: a constant is at `sort m` if its real δ-unfolding is.
const KONST_DELTA_RULE: &str = "| konstDelta : forall (G : ListType KExpr) (c : Name) (us : ListType Level) (m : Level) (body : KExpr), delta_step (red_def the_red_env) (KExpr.const c us) body -> SynTyC G body (KExpr.sort m) -> SynTyC G (KExpr.const c us) (KExpr.sort m)";

pub(super) fn src_syn_ty_c() -> String {
    format!(
        "inductive SynTyC : ListType KExpr -> KExpr -> KExpr -> Type\n\
         {VAR_RULE_LIFTED}\n\
         | sort : forall (G : ListType KExpr) (n : Level), SynTyC G (KExpr.sort n) (KExpr.sort (Level.succ n))\n\
         {PI_RULE_IMAX}\n\
         | app : forall (G : ListType KExpr) (A : KExpr) (B : KExpr) (f : KExpr) (a : KExpr), SynTyC G f (KExpr.pi A B) -> SynTyC G a A -> SynTyC G (KExpr.app f a) B\n\
         | lam : forall (G : ListType KExpr) (A : KExpr) (B : KExpr) (b : KExpr), SimpleTy A -> SynTyC (ListType.cons KExpr A G) b B -> SynTyC G (KExpr.lam A b) (KExpr.pi A B)\n\
         {LET_RULE_SORT}\n\
         {KONST_DEAD_RULE}\n\
         {KONST_DELTA_RULE}"
    )
}

// ================================================================
// Group D — the fundamental theorem and the capstones.
// ================================================================

pub(super) const TY_SYNTYC_FUNDAMENTAL: &str = "forall (G : ListType KExpr) (e : KExpr) (T : KExpr), SynTyC G e T -> forall (s : Nat -> KExpr), SubstOK s G -> candInterp T (psubst s e)";

/// The recursor's indices and major premise, applied last in EVERY
/// `SynTyC.rec` spine assembled in this rung. It is named so that R11 can
/// splice additional motive cases in FRONT of it by construction, instead of
/// stripping it back off an already-assembled term (which forced a fallible
/// `strip_suffix` on a total operation).
pub(super) const REC_APPLICAND: &str = " G e T h";

/// `val_syntyc_fundamental` without [`REC_APPLICAND`] — the recursor spine up
/// to and including its last motive case.
pub(super) fn val_syntyc_fundamental_head() -> String {
    let motive = "(fun (qG : ListType KExpr) (qe : KExpr) (qT : KExpr) (_ : SynTyC qG qe qT) => forall (qs : Nat -> KExpr), SubstOK qs qG -> candInterp qT (psubst qs qe))";
    let m_var = "(fun (qG : ListType KExpr) (qi : Nat) (qA : KExpr) (qhget : Eq (OptionType KExpr) (ctx_lookup qG qi) (OptionType.some KExpr qA)) (qs : Nat -> KExpr) (qhs : SubstOK qs qG) => candInterp_lift qA Nat.zero (Nat.succ qi) (qs qi) (qhs qi qA qhget))";
    let m_sort = "(fun (qG : ListType KExpr) (qn : Level) (qs : Nat -> KExpr) (_qhs : SubstOK qs qG) => candInterp_sort_mem (Level.succ qn) (KExpr.sort qn) (whnfAcc_sort qn))";
    let fresh_ext = |dom: &str| {
        format!("(substOK_extend qs qG {dom} (KExpr.bvar Nat.zero) (candInterp_var {dom} Nat.zero) qhs)")
    };
    let body_acc = |ihname: &str, cod: &str, body: &str, dom: &str| {
        format!(
            "(whnfAcc_of_instantiate_bvar0 (psubst (up qs) {body}) (Eq.substType KExpr (fun (qw : KExpr) => whnf_acc qw) (psubst (scons (KExpr.bvar Nat.zero) qs) {body}) (instantiate (psubst (up qs) {body}) (KExpr.bvar Nat.zero)) (psubst_scons_instantiate {body} (KExpr.bvar Nat.zero) qs) (candInterp_cr1 {cod} (psubst (scons (KExpr.bvar Nat.zero) qs) {body}) ({ihname} (scons (KExpr.bvar Nat.zero) qs) {ext}))))",
            ext = fresh_ext(dom)
        )
    };
    let ih_pi_a =
        "forall (qs2 : Nat -> KExpr), SubstOK qs2 qG -> candInterp (KExpr.sort qn) (psubst qs2 qA)";
    let ih_pi_b = "forall (qs2 : Nat -> KExpr), SubstOK qs2 (ListType.cons KExpr qA qG) -> candInterp (KExpr.sort qm) (psubst qs2 qB)";
    let m_pi = format!(
        "(fun (qG : ListType KExpr) (qA : KExpr) (qB : KExpr) (qn : Level) (qm : Level) (_qhA : SynTyC qG qA (KExpr.sort qn)) (_qhB : SynTyC (ListType.cons KExpr qA qG) qB (KExpr.sort qm)) (qihA : {ih_pi_a}) (qihB : {ih_pi_b}) (qs : Nat -> KExpr) (qhs : SubstOK qs qG) => candInterp_sort_mem (Level.imax qn qm) (KExpr.pi (psubst qs qA) (psubst (up qs) qB)) (whnfAcc_pi (psubst qs qA) (psubst (up qs) qB) (candInterp_cr1 (KExpr.sort qn) (psubst qs qA) (qihA qs qhs)) {codacc}))",
        codacc = body_acc("qihB", "(KExpr.sort qm)", "qB", "qA")
    );
    let m_app = "(fun (qG : ListType KExpr) (qA : KExpr) (qB : KExpr) (qf : KExpr) (qa : KExpr) (_qhf : SynTyC qG qf (KExpr.pi qA qB)) (_qha : SynTyC qG qa qA) (qihf : forall (qs : Nat -> KExpr), SubstOK qs qG -> candInterp (KExpr.pi qA qB) (psubst qs qf)) (qiha : forall (qs : Nat -> KExpr), SubstOK qs qG -> candInterp qA (psubst qs qa)) (qs : Nat -> KExpr) (qhs : SubstOK qs qG) => candInterp_app qA qB (psubst qs qf) (psubst qs qa) (qihf qs qhs) (qiha qs qhs))";
    let ih_lam = "forall (qs2 : Nat -> KExpr), SubstOK qs2 (ListType.cons KExpr qA qG) -> candInterp qB (psubst qs2 qb)";
    let hty = "(Eq.substType KExpr (fun (qw : KExpr) => whnf_acc qw) qA (psubst qs qA) (Eq.symm KExpr (psubst qs qA) qA (simpleTy_psubst qA qhA qs)) (simpleTy_whnfAcc qA qhA))";
    let hfam = "(fun (qb2 : KExpr) (qstar : betaStar (psubst (up qs) qb) qb2) (qa : KExpr) (qha : candInterp qA qa) => candInterp_betaStar_closed qB (instantiate (psubst (up qs) qb) qa) (instantiate qb2 qa) (betaStar_inst_transport_env (psubst (up qs) qb) qb2 qstar qa) (Eq.substType KExpr (fun (qw : KExpr) => candInterp qB qw) (psubst (scons qa qs) qb) (instantiate (psubst (up qs) qb) qa) (psubst_scons_instantiate qb qa qs) (qih (scons qa qs) (substOK_extend qs qG qA qa qha qhs))))";
    let m_lam = format!(
        "(fun (qG : ListType KExpr) (qA : KExpr) (qB : KExpr) (qb : KExpr) (qhA : SimpleTy qA) (_qhb : SynTyC (ListType.cons KExpr qA qG) qb qB) (qih : {ih_lam}) (qs : Nat -> KExpr) (qhs : SubstOK qs qG) => candInterp_lam qA qB (psubst qs qA) (psubst (up qs) qb) {hty} {bodyacc} {hfam})",
        bodyacc = body_acc("qih", "qB", "qb", "qA")
    );
    let ih_let_v =
        "forall (qs2 : Nat -> KExpr), SubstOK qs2 qG -> candInterp (KExpr.sort qn) (psubst qs2 qv)";
    let ih_let_b = "forall (qs2 : Nat -> KExpr), SubstOK qs2 (ListType.cons KExpr (KExpr.sort qn) qG) -> candInterp (KExpr.sort qm) (psubst qs2 qb)";
    let let_fam = "(fun (qb2 : KExpr) (qstar : betaStar (psubst (up qs) qb) qb2) (qv2 : KExpr) (qhv2 : whnf_acc qv2) => candInterp_betaStar_closed (KExpr.sort qm) (instantiate (psubst (up qs) qb) qv2) (instantiate qb2 qv2) (betaStar_inst_transport_env (psubst (up qs) qb) qb2 qstar qv2) (Eq.substType KExpr (fun (qw : KExpr) => candInterp (KExpr.sort qm) qw) (psubst (scons qv2 qs) qb) (instantiate (psubst (up qs) qb) qv2) (psubst_scons_instantiate qb qv2 qs) (qihb (scons qv2 qs) (substOK_extend qs qG (KExpr.sort qn) qv2 qhv2 qhs))))";
    let m_let = format!(
        "(fun (qG : ListType KExpr) (qn : Level) (qm : Level) (qv : KExpr) (qb : KExpr) (_qhv : SynTyC qG qv (KExpr.sort qn)) (_qhb : SynTyC (ListType.cons KExpr (KExpr.sort qn) qG) qb (KExpr.sort qm)) (qihv : {ih_let_v}) (qihb : {ih_let_b}) (qs : Nat -> KExpr) (qhs : SubstOK qs qG) => whnfAcc_zeta_expand (KExpr.sort qn) (whnfAcc_sort qn) (psubst (up qs) qb) {bodyacc} {let_fam} (psubst qs qv) (qihv qs qhs))",
        bodyacc = body_acc("qihb", "(KExpr.sort qm)", "qb", "(KExpr.sort qn)")
    );
    // konstDead: psubst is inert on a const, and candInterp at a sort IS the
    // base whole-SN set, so the arm is the stuck-const accessibility outright.
    let m_konst_dead = format!("(fun (qG : ListType KExpr) (qc : Name) (qus : ListType Level) (qm : Level) (qhn : Eq (OptionType KExpr) (defval_for {DENV} qc) (OptionType.none KExpr)) (qs : Nat -> KExpr) (_qhs : SubstOK qs qG) => whnfAcc_const_dead qc qus qhn)");
    // konstDelta: THE DELTA ARM. The body IH is instantiated at idsubst and
    // collapsed by psubst_id, because the engine wants membership of the body
    // ITSELF and psubst is inert on the const the rule concludes at.
    let ih_konst = "forall (qs2 : Nat -> KExpr), SubstOK qs2 qG -> candInterp (KExpr.sort qm) (psubst qs2 qbody)";
    let m_konst_delta = format!(
        "(fun (qG : ListType KExpr) (qc : Name) (qus : ListType Level) (qm : Level) (qbody : KExpr) (qhd : delta_step {DENV} (KExpr.const qc qus) qbody) (_qhb : SynTyC qG qbody (KExpr.sort qm)) (qih : {ih_konst}) (qs : Nat -> KExpr) (qhs : SubstOK qs qG) => candInterp_delta_expand_sort qm qc qus qbody qhd (Eq.substType KExpr (fun (qw : KExpr) => candInterp (KExpr.sort qm) qw) (psubst idsubst qbody) qbody (psubst_id qbody) (qih idsubst (substOK_idsubst qG))))"
    );
    format!(
        "fun (G : ListType KExpr) (e : KExpr) (T : KExpr) (h : SynTyC G e T) => SynTyC.rec {motive} {m_var} {m_sort} {m_pi} {m_app} {m_lam} {m_let} {m_konst_dead} {m_konst_delta}"
    )
}

pub(super) fn val_syntyc_fundamental() -> String {
    format!("{}{REC_APPLICAND}", val_syntyc_fundamental_head())
}

pub(super) const TY_SYNTYC_SN_SUBST: &str = "forall (G : ListType KExpr) (e : KExpr) (T : KExpr), SynTyC G e T -> forall (s : Nat -> KExpr), SubstOK s G -> whnf_acc (psubst s e)";

pub(super) const VAL_SYNTYC_SN_SUBST: &str = "fun (G : ListType KExpr) (e : KExpr) (T : KExpr) (h : SynTyC G e T) (s : Nat -> KExpr) (hs : SubstOK s G) => candInterp_cr1 T (psubst s e) (synTyC_fundamental G e T h s hs)";

pub(super) const TY_SYNTYC_SN: &str =
    "forall (G : ListType KExpr) (e : KExpr) (T : KExpr), SynTyC G e T -> whnf_acc e";

pub(super) const VAL_SYNTYC_SN: &str = "fun (G : ListType KExpr) (e : KExpr) (T : KExpr) (h : SynTyC G e T) => Eq.substType KExpr (fun (qw : KExpr) => whnf_acc qw) (psubst idsubst e) e (psubst_id e) (synTyC_sn_subst G e T h idsubst (substOK_idsubst G))";

pub(super) const TY_SYNTYC_SN_CLOSED: &str =
    "forall (e : KExpr) (T : KExpr), SynTyC (ListType.nil KExpr) e T -> whnf_acc e";

pub(super) const VAL_SYNTYC_SN_CLOSED: &str = "fun (e : KExpr) (T : KExpr) (h : SynTyC (ListType.nil KExpr) e T) => synTyC_sn (ListType.nil KExpr) e T h";

// ================================================================
// Group E — the δ rule's vacuity over the REAL env, PROVED.
// ================================================================

pub(super) const SRC_KEXPR_IS_LAM_B: &str = r"def kexpr_is_lam_b (e : KExpr) : Bool := match e with
| KExpr.sort n => Bool.false
| KExpr.bvar i => Bool.false
| KExpr.app f a => Bool.false
| KExpr.lam ty b => Bool.true
| KExpr.pi ty b => Bool.false
| KExpr.const n us => Bool.false
| KExpr.let_ ty v b => Bool.false
| KExpr.proj s i sub => Bool.false
| KExpr.lit n => Bool.false";

pub(super) const SRC_DEF_ENV_ALL_LAM_B: &str = r"def def_env_all_lam_b (env : DefEnv) : Bool := match env with
| DefEnv.empty => Bool.true
| DefEnv.addDef tail dname val => Bool.and (kexpr_is_lam_b val) (def_env_all_lam_b tail)";

pub(super) fn ty_r9_the_red_env_all_lam() -> String {
    format!("Eq Bool (def_env_all_lam_b {DENV}) Bool.true")
}

pub(super) const VAL_R9_THE_RED_ENV_ALL_LAM: &str = "Eq.refl Bool Bool.true";

pub(super) const TY_DEF_ENV_ALL_LAM_B_SOUND: &str = "forall (env : DefEnv) (dname : Name) (defval : KExpr), Eq (OptionType KExpr) (defval_for env dname) (OptionType.some KExpr defval) -> Eq Bool (def_env_all_lam_b env) Bool.true -> Eq Bool (kexpr_is_lam_b defval) Bool.true";

pub(super) fn val_def_env_all_lam_b_sound() -> String {
    let goal = "Eq Bool (kexpr_is_lam_b defval) Bool.true";
    let motive = format!("(fun (e : DefEnv) => Eq (OptionType KExpr) (defval_for e dname) (OptionType.some KExpr defval) -> Eq Bool (def_env_all_lam_b e) Bool.true -> {goal})");
    let m_empty = format!("(fun (hlk : Eq (OptionType KExpr) (defval_for DefEnv.empty dname) (OptionType.some KExpr defval)) (_hb : Eq Bool (def_env_all_lam_b DefEnv.empty) Bool.true) => option_none_ne_some KExpr defval ({goal}) hlk)");
    let m_add = format!(
        "(fun (tail : DefEnv) (dn : Name) (dv : KExpr) (ih : Eq (OptionType KExpr) (defval_for tail dname) (OptionType.some KExpr defval) -> Eq Bool (def_env_all_lam_b tail) Bool.true -> {goal}) (hlk : Eq (OptionType KExpr) (defval_for (DefEnv.addDef tail dn dv) dname) (OptionType.some KExpr defval)) (hb : Eq Bool (def_env_all_lam_b (DefEnv.addDef tail dn dv)) Bool.true) => opt_pick_some_inv KExpr (name_eqb dn dname) dv (defval_for tail dname) defval ({goal}) hlk (fun (_ht : Eq Bool (name_eqb dn dname) Bool.true) (hval : Eq KExpr dv defval) => Eq.subst KExpr (fun (w : KExpr) => Eq Bool (kexpr_is_lam_b w) Bool.true) dv defval hval (band_eq_true_left (kexpr_is_lam_b dv) (def_env_all_lam_b tail) hb)) (fun (_hf : Eq Bool (name_eqb dn dname) Bool.false) (htail : Eq (OptionType KExpr) (defval_for tail dname) (OptionType.some KExpr defval)) => ih htail (band_eq_true_right (kexpr_is_lam_b dv) (def_env_all_lam_b tail) hb)))"
    );
    format!("fun (env : DefEnv) (dname : Name) (defval : KExpr) => DefEnv.rec {motive} {m_empty} {m_add} env")
}

pub(super) fn ty_r9_real_delta_body_is_lam() -> String {
    format!("forall (c : Name) (us : ListType Level) (body : KExpr), delta_step {DENV} (KExpr.const c us) body -> Eq Bool (kexpr_is_lam_b body) Bool.true")
}

pub(super) fn val_r9_real_delta_body_is_lam() -> String {
    format!("fun (c : Name) (us : ListType Level) (body : KExpr) (hd : delta_step {DENV} (KExpr.const c us) body) => def_env_all_lam_b_sound {DENV} c body (delta_step_defval_inv {DENV} c us body hd) r9_the_red_env_all_lam")
}

/// The two constructor discriminators, as REGISTERED defs rather than inline
/// `KExpr.rec` applications.
///
/// R8's `synTyT_no_pi_formation` writes its discriminator inline and that
/// works, because there it only ever appears as a recursor MOTIVE result and as
/// a binder type. `synTyC_no_lam_at_sort` additionally needs it as the CODOMAIN
/// of an arrow inside its motive, and an inline `(fun (_ : KExpr) => Type) qT`
/// beta-redex is not a sort the elaborator will accept there — measured
/// 2026-08-26: `Type mismatch: expected valid type, got ExpectedSort(App(Lam(…,
/// KExpr, Sort 1), FVar))`. A def with the declared result type `Type` has a
/// definite sort at every use site, so both discriminators are registered.
pub(super) const SRC_R9_SORT_DISCR: &str = "def r9_sort_discr (T : KExpr) : Type := KExpr.rec (fun (_ : KExpr) => Type) (fun (_ : Level) => Empty) (fun (_ : Nat) => Nat) (fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) (fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) (fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) (fun (_ : Name) (_ : ListType Level) => Nat) (fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) (_ : Type) => Nat) (fun (_ : Name) (_ : Nat) (_ : KExpr) (_ : Type) => Nat) (fun (_ : Nat) => Nat) T";

pub(super) const SRC_R9_CONST_DISCR: &str = "def r9_const_discr (e : KExpr) : Type := KExpr.rec (fun (_ : KExpr) => Type) (fun (_ : Level) => Nat) (fun (_ : Nat) => Nat) (fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) (fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) (fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) (fun (_ : Name) (_ : ListType Level) => Empty) (fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) (_ : Type) => Nat) (fun (_ : Name) (_ : Nat) (_ : KExpr) (_ : Type) => Nat) (fun (_ : Nat) => Nat) e";

fn kexpr_discr_sort() -> String {
    "r9_sort_discr".to_string()
}

fn kexpr_discr_const() -> String {
    "r9_const_discr".to_string()
}

pub(super) const TY_SYNTYC_NO_LAM_AT_SORT: &str = "forall (G : ListType KExpr) (e : KExpr) (m : Level), SynTyC G e (KExpr.sort m) -> Eq Bool (kexpr_is_lam_b e) Bool.true -> Empty";

pub(super) fn val_syntyc_no_lam_at_sort() -> String {
    let d = kexpr_discr_sort();
    let motive = format!("(fun (qG : ListType KExpr) (qe : KExpr) (qT : KExpr) (_ : SynTyC qG qe qT) => Eq Bool (kexpr_is_lam_b qe) Bool.true -> {d} qT)");
    // The IH binders are the MOTIVE at each recursive premise's subject and
    // type — a STUCK discriminator wherever the type is a variable, never `Nat`.
    let ih =
        |subj: &str, ty: &str| format!("Eq Bool (kexpr_is_lam_b {subj}) Bool.true -> {d} {ty}");
    // Every rule but `lam` concludes at a subject that is not a lam, so its
    // is-lam hypothesis is Bool.false = Bool.true.
    let refute = |binders: &str, subj: &str, concl: &str| {
        format!("(fun {binders} (hl : Eq Bool (kexpr_is_lam_b {subj}) Bool.true) => bool_false_ne_true_t ({d} {concl}) hl)")
    };
    let m_var = refute(
        "(qG : ListType KExpr) (qi : Nat) (qA : KExpr) (_qhget : Eq (OptionType KExpr) (ctx_lookup qG qi) (OptionType.some KExpr qA))",
        "(KExpr.bvar qi)",
        "(lift_at qA Nat.zero (Nat.succ qi))",
    );
    let m_sort = refute(
        "(qG : ListType KExpr) (qn : Level)",
        "(KExpr.sort qn)",
        "(KExpr.sort (Level.succ qn))",
    );
    let m_pi = format!(
        "(fun (qG : ListType KExpr) (qA : KExpr) (qB : KExpr) (qn : Level) (qm : Level) (_qhA : SynTyC qG qA (KExpr.sort qn)) (_qhB : SynTyC (ListType.cons KExpr qA qG) qB (KExpr.sort qm)) (_qihA : {}) (_qihB : {}) (hl : Eq Bool (kexpr_is_lam_b (KExpr.pi qA qB)) Bool.true) => bool_false_ne_true_t ({d} (KExpr.sort (Level.imax qn qm))) hl)",
        ih("qA", "(KExpr.sort qn)"),
        ih("qB", "(KExpr.sort qm)")
    );
    let m_app = format!(
        "(fun (qG : ListType KExpr) (qA : KExpr) (qB : KExpr) (qf : KExpr) (qa : KExpr) (_qhf : SynTyC qG qf (KExpr.pi qA qB)) (_qha : SynTyC qG qa qA) (_qihf : {}) (_qiha : {}) (hl : Eq Bool (kexpr_is_lam_b (KExpr.app qf qa)) Bool.true) => bool_false_ne_true_t ({d} qB) hl)",
        ih("qf", "(KExpr.pi qA qB)"),
        ih("qa", "qA")
    );
    // THE ONE ARM THAT IS NOT A REFUTATION: a lam IS a lam, and its type is a
    // pi, where the discriminator is Nat.
    let m_lam = format!(
        "(fun (qG : ListType KExpr) (qA : KExpr) (qB : KExpr) (qb : KExpr) (_qhA : SimpleTy qA) (_qhb : SynTyC (ListType.cons KExpr qA qG) qb qB) (_qih : {}) (_hl : Eq Bool (kexpr_is_lam_b (KExpr.lam qA qb)) Bool.true) => Nat.zero)",
        ih("qb", "qB")
    );
    let m_let = format!(
        "(fun (qG : ListType KExpr) (qn : Level) (qm : Level) (qv : KExpr) (qb : KExpr) (_qhv : SynTyC qG qv (KExpr.sort qn)) (_qhb : SynTyC (ListType.cons KExpr (KExpr.sort qn) qG) qb (KExpr.sort qm)) (_qihv : {}) (_qihb : {}) (hl : Eq Bool (kexpr_is_lam_b (KExpr.let_ (KExpr.sort qn) qv qb)) Bool.true) => bool_false_ne_true_t ({d} (KExpr.sort qm)) hl)",
        ih("qv", "(KExpr.sort qn)"),
        ih("qb", "(KExpr.sort qm)")
    );
    let m_konst_dead = format!("(fun (qG : ListType KExpr) (qc : Name) (qus : ListType Level) (qm : Level) (_qhn : Eq (OptionType KExpr) (defval_for {DENV} qc) (OptionType.none KExpr)) (hl : Eq Bool (kexpr_is_lam_b (KExpr.const qc qus)) Bool.true) => bool_false_ne_true_t ({d} (KExpr.sort qm)) hl)");
    let m_konst_delta = format!(
        "(fun (qG : ListType KExpr) (qc : Name) (qus : ListType Level) (qm : Level) (qbody : KExpr) (_qhd : delta_step {DENV} (KExpr.const qc qus) qbody) (_qhb : SynTyC qG qbody (KExpr.sort qm)) (_qih : {}) (hl : Eq Bool (kexpr_is_lam_b (KExpr.const qc qus)) Bool.true) => bool_false_ne_true_t ({d} (KExpr.sort qm)) hl)",
        ih("qbody", "(KExpr.sort qm)")
    );
    format!(
        "fun (G : ListType KExpr) (e : KExpr) (m : Level) (h : SynTyC G e (KExpr.sort m)) => SynTyC.rec {motive} {m_var} {m_sort} {m_pi} {m_app} {m_lam} {m_let} {m_konst_dead} {m_konst_delta} G e (KExpr.sort m) h"
    )
}

pub(super) fn ty_r9_konstdelta_no_real_instance() -> String {
    format!("forall (G : ListType KExpr) (c : Name) (us : ListType Level) (m : Level) (body : KExpr), delta_step {DENV} (KExpr.const c us) body -> SynTyC G body (KExpr.sort m) -> Empty")
}

pub(super) fn val_r9_konstdelta_no_real_instance() -> String {
    format!("fun (G : ListType KExpr) (c : Name) (us : ListType Level) (m : Level) (body : KExpr) (hd : delta_step {DENV} (KExpr.const c us) body) (hb : SynTyC G body (KExpr.sort m)) => synTyC_no_lam_at_sort G body m hb (r9_real_delta_body_is_lam c us body hd)")
}

// ================================================================
// Group F — the bridge from R8 (and the proof that the converse is FALSE).
// ================================================================

pub(super) const TY_SYNTYL_TO_SYNTYC: &str =
    "forall (G : ListType KExpr) (e : KExpr) (T : KExpr), SynTyL G e T -> SynTyC G e T";

pub(super) fn val_syntyl_to_syntyc() -> String {
    let motive = "(fun (qG : ListType KExpr) (qe : KExpr) (qT : KExpr) (_ : SynTyL qG qe qT) => SynTyC qG qe qT)";
    let m_var = "(fun (qG : ListType KExpr) (qi : Nat) (qA : KExpr) (qhget : Eq (OptionType KExpr) (ctx_lookup qG qi) (OptionType.some KExpr qA)) => SynTyC.var qG qi qA qhget)";
    let m_sort = "(fun (qG : ListType KExpr) (qn : Level) => SynTyC.sort qG qn)";
    let m_pi = "(fun (qG : ListType KExpr) (qA : KExpr) (qB : KExpr) (qn : Level) (qm : Level) (_qhA : SynTyL qG qA (KExpr.sort qn)) (_qhB : SynTyL (ListType.cons KExpr qA qG) qB (KExpr.sort qm)) (qihA : SynTyC qG qA (KExpr.sort qn)) (qihB : SynTyC (ListType.cons KExpr qA qG) qB (KExpr.sort qm)) => SynTyC.pi qG qA qB qn qm qihA qihB)";
    let m_app = "(fun (qG : ListType KExpr) (qA : KExpr) (qB : KExpr) (qf : KExpr) (qa : KExpr) (_qhf : SynTyL qG qf (KExpr.pi qA qB)) (_qha : SynTyL qG qa qA) (qihf : SynTyC qG qf (KExpr.pi qA qB)) (qiha : SynTyC qG qa qA) => SynTyC.app qG qA qB qf qa qihf qiha)";
    let m_lam = "(fun (qG : ListType KExpr) (qA : KExpr) (qB : KExpr) (qb : KExpr) (qhA : SimpleTy qA) (_qhb : SynTyL (ListType.cons KExpr qA qG) qb qB) (qih : SynTyC (ListType.cons KExpr qA qG) qb qB) => SynTyC.lam qG qA qB qb qhA qih)";
    let m_let = "(fun (qG : ListType KExpr) (qn : Level) (qm : Level) (qv : KExpr) (qb : KExpr) (_qhv : SynTyL qG qv (KExpr.sort qn)) (_qhb : SynTyL (ListType.cons KExpr (KExpr.sort qn) qG) qb (KExpr.sort qm)) (qihv : SynTyC qG qv (KExpr.sort qn)) (qihb : SynTyC (ListType.cons KExpr (KExpr.sort qn) qG) qb (KExpr.sort qm)) => SynTyC.letTy qG qn qm qv qb qihv qihb)";
    format!(
        "fun (G : ListType KExpr) (e : KExpr) (T : KExpr) (h : SynTyL G e T) => SynTyL.rec {motive} {m_var} {m_sort} {m_pi} {m_app} {m_lam} {m_let} G e T h"
    )
}

pub(super) const TY_SYNTYL_SN_VIA_SYNTYC: &str =
    "forall (G : ListType KExpr) (e : KExpr) (T : KExpr), SynTyL G e T -> whnf_acc e";

pub(super) const VAL_SYNTYL_SN_VIA_SYNTYC: &str = "fun (G : ListType KExpr) (e : KExpr) (T : KExpr) (h : SynTyL G e T) => synTyC_sn G e T (synTyL_to_synTyC G e T h)";

pub(super) const TY_SYNTYL_NO_CONST: &str = "forall (G : ListType KExpr) (c : Name) (us : ListType Level) (T : KExpr), SynTyL G (KExpr.const c us) T -> Empty";

pub(super) fn val_syntyl_no_const() -> String {
    let d = kexpr_discr_const();
    let motive = format!(
        "(fun (qG : ListType KExpr) (qe : KExpr) (qT : KExpr) (_ : SynTyL qG qe qT) => {d} qe)"
    );
    let ih = |subj: &str| format!("{d} {subj}");
    let m_var = "(fun (qG : ListType KExpr) (qi : Nat) (qA : KExpr) (_qhget : Eq (OptionType KExpr) (ctx_lookup qG qi) (OptionType.some KExpr qA)) => Nat.zero)".to_string();
    let m_sort = "(fun (qG : ListType KExpr) (qn : Level) => Nat.zero)".to_string();
    let m_pi = format!(
        "(fun (qG : ListType KExpr) (qA : KExpr) (qB : KExpr) (qn : Level) (qm : Level) (_qhA : SynTyL qG qA (KExpr.sort qn)) (_qhB : SynTyL (ListType.cons KExpr qA qG) qB (KExpr.sort qm)) (_qihA : {}) (_qihB : {}) => Nat.zero)",
        ih("qA"),
        ih("qB")
    );
    let m_app = format!(
        "(fun (qG : ListType KExpr) (qA : KExpr) (qB : KExpr) (qf : KExpr) (qa : KExpr) (_qhf : SynTyL qG qf (KExpr.pi qA qB)) (_qha : SynTyL qG qa qA) (_qihf : {}) (_qiha : {}) => Nat.zero)",
        ih("qf"),
        ih("qa")
    );
    let m_lam = format!(
        "(fun (qG : ListType KExpr) (qA : KExpr) (qB : KExpr) (qb : KExpr) (_qhA : SimpleTy qA) (_qhb : SynTyL (ListType.cons KExpr qA qG) qb qB) (_qih : {}) => Nat.zero)",
        ih("qb")
    );
    let m_let = format!(
        "(fun (qG : ListType KExpr) (qn : Level) (qm : Level) (qv : KExpr) (qb : KExpr) (_qhv : SynTyL qG qv (KExpr.sort qn)) (_qhb : SynTyL (ListType.cons KExpr (KExpr.sort qn) qG) qb (KExpr.sort qm)) (_qihv : {}) (_qihb : {}) => Nat.zero)",
        ih("qv"),
        ih("qb")
    );
    format!(
        "fun (G : ListType KExpr) (c : Name) (us : ListType Level) (T : KExpr) (h : SynTyL G (KExpr.const c us) T) => SynTyL.rec {motive} {m_var} {m_sort} {m_pi} {m_app} {m_lam} {m_let} G (KExpr.const c us) T h"
    )
}

// ================================================================
// Group G — witnesses and the non-degeneracy guard.
// ================================================================

pub(super) fn ty_synty_c_id() -> String {
    format!("forall (G : ListType KExpr), SynTyC G {IDLAM0} {PI00}")
}

pub(super) fn val_synty_c_id() -> String {
    format!(
        "fun (G : ListType KExpr) => SynTyC.lam G {S0} {S0} {V0} (SimpleTy.base Level.zero) (SynTyC.var (ListType.cons KExpr {S0} G) Nat.zero {S0} (Eq.refl (OptionType KExpr) (OptionType.some KExpr {S0})))"
    )
}

pub(super) fn ty_synty_c_sort_witness() -> String {
    format!("SynTyC {NILCTX} {S0} {S1}")
}

pub(super) fn val_synty_c_sort_witness() -> String {
    format!("SynTyC.sort {NILCTX} Level.zero")
}

/// THE CONST WITNESS: a REAL reflected kernel name, typed by the ladder's
/// judgment for the first time.
pub(super) fn ty_synty_c_konst_dead_witness() -> String {
    format!("SynTyC {NILCTX} {DEADCONST} {S0}")
}

pub(super) fn val_synty_c_konst_dead_witness() -> String {
    format!("SynTyC.konstDead {NILCTX} {DEADNAME} {NILUS} Level.zero (Eq.refl (OptionType KExpr) (OptionType.none KExpr))")
}

pub(super) fn ty_synty_c_sn_konst_witness() -> String {
    format!("whnf_acc {DEADCONST}")
}

pub(super) fn val_synty_c_sn_konst_witness() -> String {
    format!("synTyC_sn {NILCTX} {DEADCONST} {S0} synTyC_konst_dead_witness")
}

/// THE RANK-DECREASE WITNESS at a real `kcre_*` pair, obtained THROUGH the
/// theorem: the outermost `DefEnv` entry (rank 5) δ-unfolds to a value that
/// mentions `def_env_closed_b` (rank 4).
pub(super) fn ty_r9_rank_decrease_witness() -> String {
    format!("Lt (rk {LIVEREF}) (rk kcre_witness_delta_head)")
}

pub(super) fn val_r9_rank_decrease_witness() -> String {
    format!("the_red_env_delta_rank_decrease kcre_witness_delta_head {NILUS} kcre_witness_delta_value {LIVEREF} the_red_env_delta_nonvacuous (Eq.refl Bool Bool.true)")
}

/// ...and at the OTHER kind of occurrence: a name that is in no `DefEnv` entry
/// at all (`DefEnv`, the inductive type) has rank 0, below every defined name.
pub(super) fn ty_r9_rank_decrease_witness_undefined() -> String {
    format!("Lt (rk {DEADNAME}) (rk kcre_witness_delta_head)")
}

pub(super) fn val_r9_rank_decrease_witness_undefined() -> String {
    format!("the_red_env_delta_rank_decrease kcre_witness_delta_head {NILUS} kcre_witness_delta_value {DEADNAME} the_red_env_delta_nonvacuous (Eq.refl Bool Bool.true)")
}

/// NECESSITY of `konstDead`'s premise, half one: at a name that IS defined the
/// const is a LIVE redex, so the rule without its side condition would be false.
pub(super) fn ty_r9_konstdead_premise_necessary() -> String {
    format!("whnf_step {LIVECONST} kcre_witness_delta_value")
}

pub(super) fn val_r9_konstdead_premise_necessary() -> String {
    format!("whnf_step.delta {LIVECONST} kcre_witness_delta_value (delta_step_to_reduces {LIVECONST} kcre_witness_delta_value the_red_env_delta_nonvacuous)")
}

/// ...half two: that name's lookup is demonstrably NOT `none`, so the witness
/// above is not reachable by `konstDead` at all.
pub(super) fn ty_r9_live_const_not_dead() -> String {
    format!("Eq (OptionType KExpr) (defval_for {DENV} kcre_witness_delta_head) (OptionType.none KExpr) -> Empty")
}

pub(super) fn val_r9_live_const_not_dead() -> String {
    format!("fun (h : Eq (OptionType KExpr) (defval_for {DENV} kcre_witness_delta_head) (OptionType.none KExpr)) => option_none_ne_some_type KExpr kcre_witness_delta_value Empty (Eq.trans (OptionType KExpr) (OptionType.none KExpr) (defval_for {DENV} kcre_witness_delta_head) (OptionType.some KExpr kcre_witness_delta_value) (Eq.symm (OptionType KExpr) (defval_for {DENV} kcre_witness_delta_head) (OptionType.none KExpr) h) (delta_step_defval_inv {DENV} kcre_witness_delta_head {NILUS} kcre_witness_delta_value the_red_env_delta_nonvacuous))")
}

pub(super) fn ty_synty_c_not_total() -> String {
    format!("forall (G : ListType KExpr), SynTyC G r5_omegaLam {PI00} -> Empty")
}

pub(super) fn val_synty_c_not_total() -> String {
    format!(
        "fun (G : ListType KExpr) (h : SynTyC G r5_omegaLam {PI00}) => candInterp_pi_not_total (Eq.substType KExpr (fun (qw : KExpr) => candInterp {PI00} qw) (psubst idsubst r5_omegaLam) r5_omegaLam (psubst_id r5_omegaLam) (synTyC_fundamental G r5_omegaLam {PI00} h idsubst (substOK_idsubst G)))"
    )
}

// ==== R9 SOURCES END ====

/// Register one value-bearing theorem (R6/R7/R8's helper, verbatim).
fn add_thm(
    spec: &mut Specification,
    name: &str,
    ty: String,
    val: String,
    deps: &[&str],
    desc: &str,
) -> Result<(), SpecError> {
    spec.add_definition(SpecDefinition {
        name: name.to_string(),
        type_src: ty,
        value_src: Some(val),
        is_axiom: false,
        description: desc.to_string(),
        category: AxiomCategory::DerivedLemma,
        proof_status: ProofStatus::DerivedProved,
        elaborated_type: None,
        elaborated_value: None,
        dependencies: Some(
            deps.iter()
                .map(|d| (*d).to_string())
                .collect::<HashSet<_>>(),
        ),
        axiom_deps: HashSet::new(),
    })
}

impl Specification {
    /// Register R9: build item B3 (the COMPUTED δ-rank for the real reflected
    /// environment, its decrease theorem in R2's exact shape, and the
    /// acyclicity corollary), the `const` rule as the judgment `SynTyC`, its
    /// unconditional SN capstones, the PROVED obstruction at the Pi-typed slot
    /// and the PROVED vacuity of the δ clause over this environment, the bridge
    /// subsuming R8, and the discriminating witnesses.
    ///
    /// MUST be registered AFTER `add_candmodel_construct_r8` (`SynTyL` and its
    /// tower), which itself sits after `add_the_red_env_faithful_discharge`.
    /// Also requires `add_candmodel_construct_r0..r7` (`IsCandSet`,
    /// `isCand_whnfAcc`, `candExp_delta`, `constRedex_whnf_inv`, the
    /// `candInterp` layer, `SimpleTy`, `SubstOK`, `r5_omegaLam`,
    /// `candInterp_pi_not_total`, `betaStar_inst_transport_env`),
    /// `add_env_closed_checkers_depth` (`nat_lt_b`, `nat_lt_b_sound`,
    /// `bool_false_ne_true_t`), `add_faithful_red_env` (`name_eqb_eq`,
    /// `opt_pick_some_inv`, `band_eq_true_left`/`_right`), `add_iota_subst`
    /// (`opt_bind_some_inv`, `option_none_ne_some`), `add_delta_step`
    /// (`defval_for`, `delta_reduct`, `delta_step`), `add_the_red_env`
    /// (`the_red_env`, `the_red_env_delta_nonvacuous`) and the generated
    /// `kernel_core_red_env` atoms.
    pub(super) fn add_candmodel_construct_r9(&mut self) -> Result<(), SpecError> {
        // --- Group A: B3, the COMPUTED rank ---
        for (name, src) in src_r9_rank_tbl_chunks() {
            self.add_recursive_def(
                &src,
                &format!(
                    "{name} — one 16-entry slice of the delta-rank table for the real reflected \
                     environment, ending in a reference to the next slice. The table is chunked \
                     rather than written as one spine because the parser refuses at nesting depth \
                     129 (max 128), which a single 127-deep ListType.cons literal exceeds \
                     (measured 2026-08-26). The chunk defs are plain aliases, so the VALUE is the \
                     same 127-element list and the kernel unfolds through them when the rank \
                     checker runs."
                ),
            )?;
        }
        self.add_recursive_def(
            &src_r9_rank_tbl(),
            "r9_rank_tbl — THE COMPUTED delta-RANK TABLE for the real reflected environment, one \
             entry per interned name of kernel_core_red_env (127 of them, index-aligned to \
             kcre_name_<i>). An entry is Nat.zero when the name has no definitional value in \
             the_red_env — every reflected inductive type, constructor and recursor — and 1 + d \
             when it does, where d is the length of the longest delta-chain out of it. Derived \
             mechanically from the generated env: 50 DefEnv entries, 67 delta edges, ACYCLIC, \
             longest chain 7, so the table is bounded by 8. It is acyclic for a structural reason \
             worth recording — the reflection compiles every recursive kernel definition through \
             the matching .rec, so not one of the 50 bodies mentions its own name. NOTHING is \
             trusted about this table: the_red_env_ranked makes the kernel re-derive its adequacy \
             in one Eq.refl, so a table that stopped matching the environment fails CLOSED. \
             Value-bearing plain def; zero axioms.",
        )?;
        self.add_recursive_def(
            SRC_R9_RANK_NTH,
            "r9_rank_nth k l — the k-th entry of a Nat list, Nat.zero past the end. An explicit \
             Nat.rec with a ListType Nat -> Nat motive (the nat_lt_b idiom) rather than a match, \
             so the reduction behaviour on a concrete index is exactly the one the rank checker \
             needs and nothing depends on match compilation. A list walk rather than a decidable- \
             equality cascade is the load-bearing choice: the checker evaluates rk once per const \
             occurrence and the 50 real bodies contain 963 of them, so a 50-deep name_eqb cascade \
             over unary numerals up to 126 would be ~10^7 reduction steps where this is ~10^5.",
        )?;
        self.add_recursive_def(
            SRC_RK,
            "rk c — THE DELTA RANK of a name, in the exact spelling R2 projected for the const \
             rung (rk : Name -> Nat). Reads the interned numeral of a Name.str Name.anonymous k \
             out of r9_rank_tbl and is Nat.zero on every other Name shape. It is a RANK, not a \
             semantics: any Name -> Nat making the checker pass would serve, and correctness of \
             the decrease does not depend on this choice, because rank_dominates_occurs recovers \
             the occurring name ITSELF through name_eqb_eq before applying rk. The point of this \
             particular choice is that an undefined name sits at 0, strictly below every defined \
             one, which is what makes the decrease true at the many body occurrences that are \
             inductive types, constructors and recursors rather than definitions.",
        )?;
        self.add_recursive_def(
            SRC_CONST_OCCURS,
            "const_occurs c e — does the constant c occur anywhere in e? The corpus's Tm.mentions \
             (LetDeltaSN.lean), and the second half of build item B3, which R2 recorded as \
             unlanded. Checked before writing: no const_occurs / mentions analogue existed \
             anywhere in core_spec, and occurs_in (env_extensions.rs) is about de Bruijn \
             self-reference, not const names. Bool-valued to match the surrounding checker style, \
             so it enters hypothesis position as Eq Bool (const_occurs c e) Bool.true and is \
             discharged at any concrete pair by Eq.refl. Congruence is Bool.or through every \
             former; the const arm is name_eqb, so the predicate is exactly as fine as the spec's \
             decidable name equality — and name_eqb_eq makes that faithful.",
        )?;
        self.add_recursive_def(
            SRC_RANK_DOMINATES_B,
            "rank_dominates_b r e — every constant occurring in e has rank strictly below r. The \
             per-entry test of the rank checker, written as a term walk rather than a \
             quantification over names so that it is decidable and kernel-evaluable: at a const it \
             is nat_lt_b (rk n) r, elsewhere the conjunction of its subterms. This is the piece \
             that turns 'the environment is acyclic' from a statement about a graph into one \
             Eq.refl over a concrete term.",
        )?;
        self.add_recursive_def(
            SRC_DEF_ENV_RANKED_B,
            "def_env_ranked_b env — the rank checker: every registered definition's value is \
             dominated by the definition's OWN rank. Same fold shape as def_env_closed_b \
             (env_closed_checkers.rs), with the per-element test upgraded and — the one structural \
             difference — depending on the entry's name as well as its value, which is what makes \
             the soundness lemma below carry a name transport that def_env_closed_b_sound does \
             not need.",
        )?;
        add_thm(
            self,
            "the_red_env_ranked",
            ty_the_red_env_ranked(),
            VAL_THE_RED_ENV_RANKED.to_string(),
            &["def_env_ranked_b", "rk", "red_def", "the_red_env"],
            "BUILD ITEM B3, LANDED AND COMPUTED: the rank checker returns true on the REAL \
             reflected environment, by a single Eq.refl — the kernel whnf-evaluates the fold over \
             all 50 DefEnv entries and all 963 const occurrences in their values. Four rungs (R2, \
             R4, R7, R8) recorded that the delta/redConst rung 'needs a WfEnv/EnvAcyclic rank \
             witness for the real reflected env' and R2 specified it as a CARRIED premise. It does \
             not have to be carried: the_red_env is a concrete, fixed, finite reflected \
             environment, so the rank is computable for the actual environment and the decrease is \
             provable by kernel computation — exactly the way R3/R4 proved iota-deadness and \
             delta-deadness at concrete heads. This is the designated-discharge posture of \
             the_red_env.rs Guard 3: the constant computes over the real env value, so a \
             regeneration of the reflection that introduced a delta-cycle fails this proof CLOSED \
             rather than drifting. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "bool_cases_eq",
            TY_BOOL_CASES_EQ.to_string(),
            VAL_BOOL_CASES_EQ.to_string(),
            &["Bool.rec", "Eq.refl"],
            "CASE ANALYSIS ON A Bool BY REFLECTION, delivered to continuations: either p = true or \
             p = false, and each branch gets the EQUATION rather than a substituted goal. The \
             motive is fun zp => Eq Bool p zp -> C and the recursor is closed with Eq.refl Bool p. \
             THE SHAPE IS FORCED, not stylistic: the obvious spelling — a motive that GENERALIZES \
             the continuations, fun zp => (Eq Bool zp Bool.true -> C) -> ... — is what this rung's \
             first cut used and the elaborator refused it on 2026-08-26 (expected Eq Bool <fvar> \
             Bool.true, got 'cannot unify expressions of different shape'), because it would not \
             instantiate a motive binder that occurs BARE against a minor naming Bool.false. The \
             landed Bool inversions band_eq_true_left / band_eq_true_right never do that: their \
             motive mentions the binder only inside Bool.and zp q and their minors take ONE binder. \
             This follows them. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "bor_false_case",
            TY_BOR_FALSE_CASE.to_string(),
            VAL_BOR_FALSE_CASE.to_string(),
            &["Eq.subst", "Bool.or"],
            "The false branch of a true disjunction: if p is false and Bool.or p q is true then q \
             is true. NO recursor — rewrite p to Bool.false inside the hypothesis with Eq.subst and \
             let the RETURN-position ascription perform the Bool.or Bool.false q reduction, which \
             is band_eq_true_right's true arm verbatim in shape and the one place the elaborator is \
             measured to do it. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "bor_eq_true_inv",
            TY_BOR_EQ_TRUE_INV.to_string(),
            VAL_BOR_EQ_TRUE_INV.to_string(),
            &["bool_cases_eq", "bor_false_case", "Bool.or"],
            "CPS inversion of a true disjunction: Bool.or p q = true gives p = true or q = true, \
             delivered to a continuation (no Sigma, no Or). Assembled from the two pieces above so \
             that neither the motive nor an application site ever has to unify Bool.or with one of \
             its arguments. The Bool.and counterparts (band_eq_true_left / band_eq_true_right) \
             already existed; this one did not, and rank_dominates_occurs needs it at every \
             congruence arm because const_occurs is a disjunction where rank_dominates_b is a \
             conjunction. C is a Type here, not a Prop: the goal it lands in is Lt, which is \
             Type-valued. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "def_env_ranked_b_sound",
            TY_DEF_ENV_RANKED_B_SOUND.to_string(),
            val_def_env_ranked_b_sound(),
            &[
                "DefEnv.rec",
                "defval_for",
                "def_env_ranked_b",
                "rank_dominates_b",
                "rk",
                "opt_pick_some_inv",
                "option_none_ne_some",
                "band_eq_true_left",
                "band_eq_true_right",
                "name_eqb_eq",
                "Eq.subst",
            ],
            "Fold-membership for the rank checker: a successful defval_for lookup on a \
             checker-true environment returns a value dominated by the LOOKED-UP name's rank. \
             DefEnv.rec in def_env_closed_b_sound's shape — empty lookup absurd by \
             option_none_ne_some, addDef splitting the opt_pick fire / fall-through — with ONE \
             structural difference that is the whole reason it could not be reused: the per-entry \
             test mentions the entry's own name, so the fire branch must transport the rank along \
             name_eqb_eq (the entry's name IS the looked-up name) before transporting the value \
             along the opt_pick payload equation. GENERIC: holds at every DefEnv, and carries \
             none of the_red_env's content. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "rank_dominates_occurs",
            TY_RANK_DOMINATES_OCCURS.to_string(),
            val_rank_dominates_occurs(),
            &[
                "KExpr.rec",
                "rank_dominates_b",
                "const_occurs",
                "rk",
                "nat_lt_b_sound",
                "bor_eq_true_inv",
                "band_eq_true_left",
                "band_eq_true_right",
                "bool_false_ne_true_t",
                "name_eqb_eq",
                "Eq.substType",
                "Lt",
            ],
            "The Bool checker's meaning, as a Type-valued order fact: if every const in e is \
             rank-dominated by r and c2 occurs in e, then Lt (rk c2) r. One KExpr.rec; the three \
             leaf arms are absurd because const_occurs at a leaf is Bool.false; the congruence \
             arms split the occurrence disjunction with bor_eq_true_inv and project the matching \
             domination conjunct with band_eq_true_left / band_eq_true_right; and THE CONST ARM IS \
             THE ONE THAT DOES WORK — domination there IS nat_lt_b (rk n) r and occurrence IS \
             name_eqb c2 n, so name_eqb_eq identifies c2 with n and nat_lt_b_sound converts the \
             Bool test into the inductive Lt. That identification is why rk's blindness to \
             anything but the interned numeral costs nothing: the theorem never guesses which name \
             occurred, it recovers it. GENERIC: no environment appears. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "delta_step_defval_inv",
            TY_DELTA_STEP_DEFVAL_INV.to_string(),
            VAL_DELTA_STEP_DEFVAL_INV.to_string(),
            &[
                "delta_step",
                "delta_reduct",
                "defval_for",
                "opt_bind_some_inv",
                "Eq.trans",
            ],
            "THE BARE-CONST DELTA INVERSION: a delta step from const c us to body means the \
             environment maps c to body, exactly. delta_reduct at a bare const REDUCES to \
             opt_bind (defval_for env c) (fun v => some v) — kapp_fn of a const is the const, its \
             const name is some c, its kapp_args is nil and apply_spine nil v is v — so \
             opt_bind_some_inv recovers the looked-up value and option injectivity is not even \
             needed, the two some-equations compose. This is the hinge between the delta relation \
             the ladder reduces with and the DefEnv the rank checker folds over; without it B3 \
             would be a fact about a lookup table with no bearing on reduction. GENERIC in env. \
             Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "the_red_env_delta_rank_decrease",
            ty_the_red_env_delta_rank_decrease(),
            val_the_red_env_delta_rank_decrease(),
            &[
                "the_red_env_ranked",
                "def_env_ranked_b_sound",
                "rank_dominates_occurs",
                "delta_step_defval_inv",
                "rk",
                "const_occurs",
                "Lt",
            ],
            "BUILD ITEM B3 IN R2'S EXACT SHAPE, DISCHARGED RATHER THAN CARRIED: whenever const c \
             us delta-unfolds to body in the REAL reflected environment and c2 occurs in body, \
             Lt (rk c2) (rk c). R2 wrote this statement down as the premise the const rung 'must \
             take EXPLICITLY', citing the wf/ac discipline where such side conditions are carried, \
             proved jointly satisfiable and independently necessary, never discharged globally. \
             That discipline is right for an ARBITRARY environment and unnecessary for this one: \
             the_red_env is concrete, so the premise is a theorem. The proof is three generic \
             lemmas over one Eq.refl — invert the delta step into a defval_for lookup, run the \
             checker's fold-membership at that lookup, read the resulting Bool domination at the \
             occurring name. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "r9_lt_irrefl",
            TY_R9_LT_IRREFL.to_string(),
            VAL_R9_LT_IRREFL.to_string(),
            &["Lt.rec", "Nat.rec", "Eq.substType", "Eq.cong", "Empty"],
            "Irreflexivity of the inductive Lt, minted here because core_spec had no such lemma \
             under any spelling (checked by grep). Lt.rec against the motive Eq Nat a b -> Empty: \
             the zero_lt_succ arm discriminates 0 = succ n with a Nat.rec into Type, and the \
             succ_lt_succ arm strips both successors with a predecessor congruence and hands the \
             result to its IH. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "the_red_env_no_delta_cycle",
            ty_the_red_env_no_delta_cycle(),
            val_the_red_env_no_delta_cycle(),
            &[
                "the_red_env_delta_rank_decrease",
                "r9_lt_irrefl",
                "const_occurs",
                "Empty",
            ],
            "WHAT B3 ACTUALLY BUYS, stated as its own theorem: NO constant of the real kernel \
             foundation core delta-unfolds to a term that mentions itself. This is EnvAcyclic for \
             the_red_env — the second half of the WfEnv/EnvAcyclic pair the corpus carries as a \
             hypothesis of konst_red_aux (LetDeltaSN.lean:910) and that four rungs of this ladder \
             recorded as unlanded — proved, at the self-application instance of the rank decrease \
             plus irreflexivity. It is also the structural fact behind the acyclicity: the \
             reflection compiles recursive kernel definitions through their recursors, so a \
             definition's reflected value never names the definition. Zero axiom_deps.",
        )?;

        // --- Group B: the const engine and the located obstruction ---
        add_thm(
            self,
            "r9_const_delta_dead",
            ty_r9_const_delta_dead(),
            val_r9_const_delta_dead(),
            &[
                "delta_step",
                "delta_reduct",
                "defval_for",
                "opt_bind",
                "option_none_ne_some_type",
                "Eq.cong",
                "Eq.trans",
                "Eq.symm",
            ],
            "A constant with no definitional value takes NO delta step, at any universe argument \
             list. delta_reduct at a bare const reduces to opt_bind over the lookup, so rewriting \
             the lookup to none by Eq.cong collapses the whole reduct to none, and none = some g2 \
             is eliminated into any Type. The CPS shape (a (C : Type) continuation rather than an \
             Empty) is what lets the accessibility proof below use it directly inside a step \
             eliminator. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "whnfAcc_const_dead",
            ty_whnfacc_const_dead(),
            val_whnfacc_const_dead(),
            &[
                "whnf_acc.intro",
                "constRedex_whnf_inv",
                "r9_const_delta_dead",
                "defval_for",
            ],
            "A DELTA-DEAD CONSTANT IS STRONGLY NORMALIZING, by vacuous accessibility: R2's \
             constRedex_whnf_inv is the COMPLETE classification of whnf steps out of a bare const \
             (no beta at a const head, no iota at a bare const since the major-premise slot of an \
             empty spine is none unconditionally, delta only at the root), so the single surviving \
             leg is a delta step, and r9_const_delta_dead refutes it. Over the real reflected \
             environment this covers every name outside the 50 DefEnv entries — every reflected \
             inductive type, constructor and recursor — which is what makes SynTyC.konstDead a \
             rule with content rather than a labeled vacuity. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "candInterp_delta_expand_sort",
            ty_candinterp_delta_expand_sort(),
            val_candinterp_delta_expand_sort(),
            &[
                "candExp_delta",
                "isCand_whnfAcc",
                "candInterp",
                "delta_step",
            ],
            "THE DELTA CLAUSE THROUGH THE CONTRACTUM, at a SORT-TYPED slot: const c us inhabits \
             candInterp (sort m) whenever its real delta-unfolding does. It is R2's per-set \
             candExp_delta retyped and nothing more — candInterp (sort m) e REDUCES to whnf_acc e, \
             the base whole-SN set, which IS an IsCandSet — the exact structural move R8 made for \
             the zeta clause (candInterp_zeta_expand_sort). THE ANNOTATION IS A SORT FOR A REASON \
             THAT IS NOT COSMETIC: candExp_delta introduces membership through the UNRESTRICTED \
             cr3, and R5's candInterp only has the HEAD-FREE face candCr3HF, whose premise a bare \
             const cannot satisfy — see r9_const_obstruction_located. At a Pi-typed slot this \
             clause is therefore unavailable, and R5 already PROVED the head-free restriction \
             necessary at the real env (piSet_cr3_headFree_necessary). Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "r9_const_is_neutral",
            TY_R9_CONST_IS_NEUTRAL.to_string(),
            VAL_R9_CONST_IS_NEUTRAL.to_string(),
            &["Neutral", "ConstFreeUnit.triv"],
            "THE CONST OBSTRUCTION, half one: a bare const IS Neutral — Neutral's const arm is \
             unconditionally ConstFreeUnit — so the UNRESTRICTED cr3 of an IsCandSet applies to it \
             and R2's engine goes through at the base set. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "r9_const_headfree_absurd",
            TY_R9_CONST_HEADFREE_ABSURD.to_string(),
            VAL_R9_CONST_HEADFREE_ABSURD.to_string(),
            &["kexpr_const_name", "kapp_fn", "option_none_ne_some_type"],
            "THE CONST OBSTRUCTION, half two: a bare const is NEVER head-free. kapp_fn of a const \
             is the const and its kexpr_const_name is some c, so the HeadFree premise \
             kexpr_const_name (kapp_fn e) = none is refutable at every c and us. That premise is \
             exactly what R5's candCr3HF — the only cr3 face candInterp has, and the one R5 PROVED \
             necessary with a stuck Nat.rec counterexample at the real env \
             (piSet_cr3_headFree_necessary) — demands of the term it introduces. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "r9_const_obstruction_located",
            TY_R9_CONST_OBSTRUCTION_LOCATED.to_string(),
            VAL_R9_CONST_OBSTRUCTION_LOCATED.to_string(),
            &[
                "AndType.intro",
                "Neutral",
                "ConstFreeUnit.triv",
                "r9_const_headfree_absurd",
            ],
            "THE OBSTRUCTION AS ONE KERNEL-CHECKED CONSTANT, so the scope of the const rule is a \
             fact rather than prose: at every c and us the bare const IS Neutral and is NOT \
             head-free. Read together, they say the delta clause is blocked at a Pi-typed slot for \
             a reason that has NOTHING to do with acyclicity or with the rank — cr3 in its \
             unrestricted form would introduce it, and the head-free-restricted cr3 that R5's \
             interpretation actually carries cannot. THAT IS THE HEADLINE CORRECTION OF THIS RUNG: \
             R2, R4, R7 and R8 all named the missing rank as the blocker for redConst; the rank is \
             computable in one Eq.refl (the_red_env_ranked) and the blocker is R5's already- \
             measured head-free wall. Both AndType slots are Type — Neutral is Type-valued and the \
             second is an arrow into Empty, NOT the Eq itself, because a non-cumulative AndType \
             slot may hold neither a Prop nor a Type-1 term. Zero axiom_deps.",
        )?;

        // --- Group C: the judgment ---
        self.add_inductive(
            &src_syn_ty_c(),
            "SynTyC G e T — THE CONST RUNG'S JUDGMENT: R8's SynTyL with a const rule, in two \
             clauses. konstDead types const c us at any sort when the real reflected environment \
             maps c to NOTHING — such a const is whnf-stuck, and over the_red_env that is every \
             name outside the 50 DefEnv entries, i.e. every reflected inductive type, constructor \
             and recursor. konstDelta types it when its real delta-unfolding is typed at the same \
             sort; that clause is SOUND and its engine (candInterp_delta_expand_sort) is the \
             deliverable R2/R4/R7/R8 asked for, but it is VACUOUS over this environment and that \
             is PROVED here rather than asserted (r9_konstDelta_no_real_instance: all 50 real \
             definition bodies are KExpr.lam, and SynTyC types no lam at a sort). Registering it \
             anyway is the design's section 6.3 labeled by-design vacuity, measured. The other six \
             rules are R8's, unchanged: var lifts exactly as TypingCtx.var, pi is TypingCtx.pi's \
             formation rule at the LITERAL Level.imax, letTy is the sort-annotated zeta rule, and \
             sort/app/lam are R7's with app NON-DEPENDENT and lam carrying SimpleTy A. The \
             judgment mentions NO candInterp, NO CandModel, no closedness premise and NO \
             EnvAcyclic; the shape guard refuses all of them. It DOES mention the_red_env, through \
             defval_for and delta_step, and that is unavoidable rather than sloppy — delta is \
             env-relative, so a const rule naming no environment would be a rule about no \
             reduction — and both side conditions are discharged per-constant by Eq.refl. Strict \
             positivity is immediate (every recursive premise is a bare SynTyC). No \
             fixedIndicesToParams promotion: the leading (G : ListType KExpr) is uniform across \
             the eight conclusions but the pi, lam and letTy premises conclude at ListType.cons \
             KExpr _ G. SCOPE: still narrower than TypingCtx — no const at a PI type at all, \
             non-dependent app, SimpleTy lam domains, sort-annotated let only, no conversion rule \
             — and nothing about it advances M : CandModel tenv. Not total: synTyC_not_total. \
             ZERO new axioms.",
        )?;

        // --- Group D: the fundamental theorem and the capstones ---
        add_thm(
            self,
            "synTyC_fundamental",
            TY_SYNTYC_FUNDAMENTAL.to_string(),
            val_syntyc_fundamental(),
            &[
                "SynTyC.rec",
                "SubstOK",
                "candInterp_lift",
                "candInterp_sort_mem",
                "candInterp_app",
                "candInterp_lam",
                "candInterp_cr1",
                "candInterp_var",
                "candInterp_betaStar_closed",
                "candInterp_delta_expand_sort",
                "whnfAcc_const_dead",
                "betaStar_inst_transport_env",
                "whnfAcc_zeta_expand",
                "whnfAcc_pi",
                "whnfAcc_sort",
                "whnfAcc_of_instantiate_bvar0",
                "simpleTy_psubst",
                "simpleTy_whnfAcc",
                "substOK_extend",
                "substOK_idsubst",
                "psubst_id",
                "psubst_scons_instantiate",
                "Eq.substType",
            ],
            "THE FUNDAMENTAL THEOREM for the const rung: every SynTyC-derivable term inhabits its \
             type's interpretation at every closing substitution. One SynTyC.rec with a full \
             four-binder motive and EIGHT minors. Six of them are R8's synTyL_fundamental \
             verbatim. THE TWO NEW ARMS: konstDead is whnfAcc_const_dead outright, because psubst \
             is INERT on a const (psubst's const arm returns the const) and candInterp at a sort \
             IS the base whole-SN set, so the goal is literally accessibility of a stuck term; \
             konstDelta feeds candInterp_delta_expand_sort with the body IH instantiated at \
             IDSUBST and collapsed by psubst_id — the engine wants membership of the body ITSELF, \
             not of a substituted copy, and instantiating at idsubst is exactly how the capstone \
             already recovers an unsubstituted term. That is also why the delta rule needs no \
             closedness side condition on the body, which was the first shape tried and is not \
             necessary. Carries NO premise: no CandModel, no RecEnvClosed, no RecEnvLiftClosed, no \
             DefEnvClosed, and no EnvAcyclic — the acyclicity B3 establishes is a discharged \
             theorem about a fixed environment, never a hypothesis here. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "synTyC_sn_subst",
            TY_SYNTYC_SN_SUBST.to_string(),
            VAL_SYNTYC_SN_SUBST.to_string(),
            &["synTyC_fundamental", "candInterp_cr1"],
            "SN OF EVERY CLOSING INSTANCE for the const rung: SynTyC G e T implies whnf_acc \
             (psubst s e) for every s that closes G — the fundamental theorem composed with R5's \
             cr1 projection. UNCONDITIONAL. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "synTyC_sn",
            TY_SYNTYC_SN.to_string(),
            VAL_SYNTYC_SN.to_string(),
            &["synTyC_sn_subst", "substOK_idsubst", "psubst_id"],
            "THE R9 CAPSTONE — UNCONDITIONAL strong normalization for the judgment with a const \
             rule: SynTyC G e T implies whnf_acc e, at an ARBITRARY context, for the spec's FULL \
             env-fixed one-step reduction (beta, zeta, iota at red_rec the_red_env with full \
             congruence, and delta at red_def the_red_env). NO carried premise of any kind — in \
             particular NO EnvAcyclic, which is the premise the corpus's konst_red_aux carries and \
             which four earlier rungs projected this capstone would have to carry too; here it is \
             a discharged theorem (the_red_env_ranked / the_red_env_no_delta_cycle) about a fixed \
             environment and the capstone never sees it. WHAT IS NEW OVER R8: the terms this \
             reaches include KExpr.const expressions at REAL reflected kernel names \
             (synTyC_konst_dead_witness — and synTyL_no_const proves R8's judgment reaches none of \
             them, in any context at any type). HONESTY: this is SN for SynTyC, NOT for TypingCtx \
             — it neither discharges nor advances the M : CandModel tenv hypothesis of \
             whnf_terminates_well_typed_dependent, and must never be described as doing so (design \
             section 6.2). Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "synTyC_sn_closed",
            TY_SYNTYC_SN_CLOSED.to_string(),
            VAL_SYNTYC_SN_CLOSED.to_string(),
            &["synTyC_sn"],
            "The closed-term corollary: SynTyC nil e T implies whnf_acc e. A one-line \
             specialization of synTyC_sn, which already holds at every context. Zero axiom_deps.",
        )?;

        // --- Group E: the delta clause's vacuity over the REAL env, proved ---
        self.add_recursive_def(
            SRC_R9_SORT_DISCR,
            "r9_sort_discr T — the constructor discriminator that sends a sort to Empty and every \
             other former to Nat. A registered def rather than an inline KExpr.rec because \
             synTyC_no_lam_at_sort needs it as the CODOMAIN of an arrow inside a recursor motive, \
             and an inline beta-redex is not a sort the elaborator accepts there (measured \
             2026-08-26: ExpectedSort(App(Lam(KExpr, Sort 1), FVar))). With the result type \
             declared, every use site has a definite sort.",
        )?;
        self.add_recursive_def(
            SRC_R9_CONST_DISCR,
            "r9_const_discr e — the same idiom at the const slot, for synTyL_no_const. Registered \
             for the same reason and so the two strictness proofs of this rung read the same way.",
        )?;
        self.add_recursive_def(
            SRC_KEXPR_IS_LAM_B,
            "kexpr_is_lam_b e — is e a lambda? The one-bit shape test the vacuity proof folds over \
             the real environment. Registered rather than inlined because it appears on both sides \
             of that proof: inside a DefEnv fold (def_env_all_lam_b) and inside a SynTyC.rec \
             motive (synTyC_no_lam_at_sort), and the two must be the SAME predicate for them to \
             compose.",
        )?;
        self.add_recursive_def(
            SRC_DEF_ENV_ALL_LAM_B,
            "def_env_all_lam_b env — every registered definition's value is a lambda. The \
             env_closed_checkers fold shape with the per-element test swapped for the shape test. \
             This is a MEASUREMENT instrument, not a soundness one: it exists so the vacuity of \
             the delta const clause over the real environment can be a kernel-checked fact instead \
             of a prose claim.",
        )?;
        add_thm(
            self,
            "r9_the_red_env_all_lam",
            ty_r9_the_red_env_all_lam(),
            VAL_R9_THE_RED_ENV_ALL_LAM.to_string(),
            &["def_env_all_lam_b", "red_def", "the_red_env"],
            "ALL 50 REAL DEFINITION BODIES ARE LAMBDAS, by one Eq.refl over the real reflected \
             environment. Independently interesting — it says the reflected foundation core \
             contains no reflected CONSTANT of non-function shape — and load-bearing here: it is \
             the first half of the proof that the delta const clause has no instance over this \
             environment. Same designated-discharge posture as the_red_env_ranked: a regeneration \
             that added a non-lambda definition fails this CLOSED. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "def_env_all_lam_b_sound",
            TY_DEF_ENV_ALL_LAM_B_SOUND.to_string(),
            val_def_env_all_lam_b_sound(),
            &[
                "DefEnv.rec",
                "defval_for",
                "def_env_all_lam_b",
                "kexpr_is_lam_b",
                "opt_pick_some_inv",
                "option_none_ne_some",
                "band_eq_true_left",
                "band_eq_true_right",
                "Eq.subst",
            ],
            "Fold-membership for the shape checker: a successful defval_for lookup on a \
             checker-true environment returns a lambda. def_env_closed_b_sound's proof shape \
             exactly — the per-element test does not mention the entry's name, so unlike \
             def_env_ranked_b_sound this one needs no name transport. GENERIC in env. Zero \
             axiom_deps.",
        )?;
        add_thm(
            self,
            "r9_real_delta_body_is_lam",
            ty_r9_real_delta_body_is_lam(),
            val_r9_real_delta_body_is_lam(),
            &[
                "delta_step_defval_inv",
                "def_env_all_lam_b_sound",
                "r9_the_red_env_all_lam",
                "kexpr_is_lam_b",
            ],
            "EVERY delta step of the real reflected environment lands on a LAMBDA. The bare-const \
             delta inversion into a defval_for lookup, composed with the shape checker's \
             fold-membership at that lookup and the one-Eq.refl discharge. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "synTyC_no_lam_at_sort",
            TY_SYNTYC_NO_LAM_AT_SORT.to_string(),
            val_syntyc_no_lam_at_sort(),
            &[
                "SynTyC.rec",
                "KExpr.rec",
                "kexpr_is_lam_b",
                "bool_false_ne_true_t",
            ],
            "NO SynTyC DERIVATION TYPES A LAMBDA AT A SORT. SynTyC.rec against a KExpr.rec \
             discriminator on the TYPE that sends sort to Empty and every other former to Nat, \
             with the subject's shape carried as a Bool hypothesis: seven of the eight rules \
             conclude at a subject that is not a lambda, so their hypothesis is Bool.false = \
             Bool.true and dies; the lam rule concludes at a PI type, where the discriminator is \
             Nat. Every IH binder is the MOTIVE at its premise's subject and type — a STUCK \
             KExpr.rec application wherever that type is a variable, NEVER Nat, which is the \
             measured 2026-08-25 failure mode of exactly this construction. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "r9_konstDelta_no_real_instance",
            ty_r9_konstdelta_no_real_instance(),
            val_r9_konstdelta_no_real_instance(),
            &[
                "r9_real_delta_body_is_lam",
                "synTyC_no_lam_at_sort",
                "delta_step",
                "Empty",
            ],
            "THE DELTA CONST CLAUSE IS VACUOUS OVER THIS ENVIRONMENT, PROVED: there is NO c, us, \
             body, m and G with a real delta step from const c us to body and a SynTyC derivation \
             of body at sort m. The two halves are measurements, not guesses — every real \
             definition body is a lambda (one Eq.refl over the env) and the judgment types no \
             lambda at a sort (one SynTyC.rec) — and neither of them is about acyclicity. So the \
             rule SynTyC.konstDelta is kept as the sound general clause with its engine, and \
             labeled: this is the design's section 6.3 by-design vacuity, with satisfiability and \
             necessity MEASURED in the wf/ac tradition rather than asserted. WHAT THE MEASUREMENT \
             SAYS ABOUT THE LADDER: to reach a real defined constant the judgment would have to \
             type its body, a lambda, hence at a PI type — where r9_const_obstruction_located and \
             R5's piSet_cr3_headFree_necessary say the const clause cannot go. The two obstructions \
             are the same wall seen from two sides. Zero axiom_deps.",
        )?;

        // --- Group F: the bridge from R8 ---
        add_thm(
            self,
            "synTyL_to_synTyC",
            TY_SYNTYL_TO_SYNTYC.to_string(),
            val_syntyl_to_syntyc(),
            &[
                "SynTyL.rec",
                "SynTyC.var",
                "SynTyC.sort",
                "SynTyC.pi",
                "SynTyC.app",
                "SynTyC.lam",
                "SynTyC.letTy",
            ],
            "THE BRIDGE: every R8 derivation is an R9 derivation, with NO hypothesis at all — R8's \
             own bridge from R7 needed CtxSimple G because R8 CHANGED the var rule, and R9 changes \
             no rule of R8's, it only adds two. SynTyL.rec mapping constructor for constructor. \
             THE CONVERSE IS FALSE, not merely unproved: synTyC_konst_dead_witness is a SynTyC \
             derivation of a const EXPRESSION and synTyL_no_const proves SynTyL has none, in any \
             context at any type. R8's own synTyL_sn is NOT superseded. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "synTyL_sn_via_synTyC",
            TY_SYNTYL_SN_VIA_SYNTYC.to_string(),
            VAL_SYNTYL_SN_VIA_SYNTYC.to_string(),
            &["synTyC_sn", "synTyL_to_synTyC"],
            "R8's capstone RE-DERIVED THROUGH R9's, at every context and with no side condition — \
             registered so the subsumption is a kernel-checked fact rather than a claim about two \
             developments that look alike. Unlike R8's synTyT_sn_via_synTyL, this one is exactly \
             as strong as the theorem it re-derives. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "synTyL_no_const",
            TY_SYNTYL_NO_CONST.to_string(),
            val_syntyl_no_const(),
            &["SynTyL.rec", "KExpr.rec"],
            "R9 IS STRICTLY WIDER, PROVED: NO SynTyL derivation concludes at a const EXPRESSION, \
             in any context, at any type. SynTyL.rec against a KExpr.rec discriminator that sends \
             the const constructor to Empty and every other constructor to Nat; each of R8's six \
             rules concludes at a bvar, a sort, a pi, an app, a lam or a let_, so every minor is \
             Nat.zero and the recursor lands in Empty at a const. Read with \
             synTyC_konst_dead_witness this settles the bridge direction as a fact: SynTyL embeds \
             into SynTyC unconditionally, and SynTyC does not embed into SynTyL at all. It is also \
             the precise sense in which 'no const rule' was the ladder's outstanding gap. Zero \
             axiom_deps.",
        )?;

        // --- Group G: witnesses and the non-degeneracy guard ---
        add_thm(
            self,
            "synTyC_id",
            ty_synty_c_id(),
            val_synty_c_id(),
            &["SynTyC.lam", "SynTyC.var", "SimpleTy.base"],
            "The fragment's identity function is typed by the const rung's judgment, in every \
             context: lam (sort 0) (bvar 0) : pi (sort 0) (sort 0). Also a PREMISE-SATISFIABILITY \
             WITNESS for SynTyC — constructors do not count on the supply side, which is why this \
             is a registered definition and why the ladder guard names SynTyC. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "synTyC_sort_witness",
            ty_synty_c_sort_witness(),
            val_synty_c_sort_witness(),
            &["SynTyC.sort"],
            "sort 0 : sort 1 in the empty context — the judgment's non-vacuity at its simplest \
             rule, and a closed-conclusion premise-satisfiability witness for SynTyC. Zero \
             axiom_deps.",
        )?;
        add_thm(
            self,
            "synTyC_konst_dead_witness",
            ty_synty_c_konst_dead_witness(),
            val_synty_c_konst_dead_witness(),
            &["SynTyC.konstDead", "defval_for", "the_red_env", "Eq.refl"],
            "THE CONST WITNESS, AND THE FIRST TIME THE LADDER'S JUDGMENT REACHES A KExpr.const AT \
             ALL: the REAL reflected kernel name kcre_name_12 (the inductive type DefEnv) is typed \
             at sort 0 in the empty context, by SynTyC.konstDead over a side condition the kernel \
             COMPUTES — defval_for (red_def the_red_env) kcre_name_12 whnf-evaluates to none by \
             walking the real 50-entry DefEnv chain, so the Eq.refl is a genuine measurement of \
             the reflected environment and not a syntactic identity. Designated-discharge posture: \
             a regeneration of the reflection that gave that name a definitional value fails this \
             CLOSED. Also a premise-satisfiability witness for SynTyC at the new rule. Zero \
             axiom_deps.",
        )?;
        add_thm(
            self,
            "synTyC_sn_konst_witness",
            ty_synty_c_sn_konst_witness(),
            val_synty_c_sn_konst_witness(),
            &["synTyC_sn", "synTyC_konst_dead_witness"],
            "THE POSITIVE WITNESS, obtained THROUGH the capstone: whnf_acc of a REAL reflected \
             kernel constant, derived as synTyC_sn applied to synTyC_konst_dead_witness — i.e. \
             through SynTyC.konstDead, the fundamental theorem's dead-const arm \
             (whnfAcc_const_dead over R2's complete const-step classification) and the cr1 \
             projection. Not by a direct whnfAcc_const_dead. Strictly outside R8's reach: \
             synTyL_no_const. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "r9_rank_decrease_witness",
            ty_r9_rank_decrease_witness(),
            val_r9_rank_decrease_witness(),
            &[
                "the_red_env_delta_rank_decrease",
                "the_red_env_delta_nonvacuous",
                "const_occurs",
                "rk",
                "Lt",
            ],
            "THE RANK-DECREASE WITNESS AT A REAL kcre_* PAIR, obtained THROUGH the theorem rather \
             than by direct computation: the outermost DefEnv entry def_env_lift_closed_b \
             delta-unfolds (R2's Guard-4 witness the_red_env_delta_nonvacuous, reused — no new step \
             computation) to a value that mentions def_env_closed_b, and the rank strictly drops \
             (5 to 4). The occurrence premise is Eq.refl, i.e. the kernel computes const_occurs \
             over the real reflected value. This is what makes B3 a fact about the real \
             environment and not about an empty quantifier. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "r9_rank_decrease_witness_undefined",
            ty_r9_rank_decrease_witness_undefined(),
            val_r9_rank_decrease_witness_undefined(),
            &[
                "the_red_env_delta_rank_decrease",
                "the_red_env_delta_nonvacuous",
                "const_occurs",
                "rk",
                "Lt",
            ],
            "THE SECOND KIND OF OCCURRENCE, at the SAME real delta step: the value also mentions \
             kcre_name_12, a name with no DefEnv entry at all, whose rank is 0 — below every \
             defined name. Registered beside the first because the two are the reason the rank is \
             defined the way it is: most const occurrences in real definition bodies are inductive \
             types, constructors and recursors, and a rank scheme that did not put them strictly \
             below every definition would make the decrease FALSE rather than merely unprovable. \
             Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "r9_konstDead_premise_necessary",
            ty_r9_konstdead_premise_necessary(),
            val_r9_konstdead_premise_necessary(),
            &[
                "whnf_step.delta",
                "delta_step_to_reduces",
                "the_red_env_delta_nonvacuous",
            ],
            "NECESSITY OF konstDead'S SIDE CONDITION, half one: at a name that IS defined the bare \
             const is a LIVE whnf redex — def_env_lift_closed_b steps to its reflected value under \
             the real environment. So the rule without its defval_for = none premise would assert \
             accessibility by vacuous introduction for a term that genuinely reduces, which is \
             false in general. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "r9_live_const_not_dead",
            ty_r9_live_const_not_dead(),
            val_r9_live_const_not_dead(),
            &[
                "delta_step_defval_inv",
                "the_red_env_delta_nonvacuous",
                "defval_for",
                "option_none_ne_some_type",
            ],
            "NECESSITY OF konstDead'S SIDE CONDITION, half two: that same name's lookup is \
             demonstrably NOT none, so konstDead cannot reach the live redex above and the two \
             clauses of the const rule are genuinely disjoint. Proved by inverting the Guard-4 \
             delta step into its lookup, so the refutation is anchored to the real environment \
             rather than to a computation restated. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "synTyC_not_total",
            ty_synty_c_not_total(),
            val_synty_c_not_total(),
            &[
                "synTyC_fundamental",
                "substOK_idsubst",
                "psubst_id",
                "candInterp_pi_not_total",
            ],
            "THE NON-DEGENERACY GUARD (design section 6.1; the micro_has_type total-predicate \
             trap): r5_omegaLam — a STRONGLY NORMALIZING term — is NOT SynTyC-derivable at pi \
             (sort 0) (sort 0), in ANY context. The fundamental theorem at idsubst would place it \
             in candInterp (pi (sort 0) (sort 0)), which R5's candInterp_pi_not_total refutes. So \
             adding a const rule did NOT widen the judgment to the total relation, and since the \
             excluded term IS whnf_acc the judgment is not a disguised restatement of strong \
             normalization either. No automated gate performs this discrimination. Zero \
             axiom_deps.",
        )?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_utils::parse_check;

    /// Every (name, type, value) triple registered via `add_definition`, in
    /// registration order.
    fn theorem_sources() -> Vec<(String, String, String)> {
        vec![
            (
                "the_red_env_ranked".to_string(),
                ty_the_red_env_ranked(),
                VAL_THE_RED_ENV_RANKED.to_string(),
            ),
            (
                "bool_cases_eq".to_string(),
                TY_BOOL_CASES_EQ.to_string(),
                VAL_BOOL_CASES_EQ.to_string(),
            ),
            (
                "bor_false_case".to_string(),
                TY_BOR_FALSE_CASE.to_string(),
                VAL_BOR_FALSE_CASE.to_string(),
            ),
            (
                "bor_eq_true_inv".to_string(),
                TY_BOR_EQ_TRUE_INV.to_string(),
                VAL_BOR_EQ_TRUE_INV.to_string(),
            ),
            (
                "def_env_ranked_b_sound".to_string(),
                TY_DEF_ENV_RANKED_B_SOUND.to_string(),
                val_def_env_ranked_b_sound(),
            ),
            (
                "rank_dominates_occurs".to_string(),
                TY_RANK_DOMINATES_OCCURS.to_string(),
                val_rank_dominates_occurs(),
            ),
            (
                "delta_step_defval_inv".to_string(),
                TY_DELTA_STEP_DEFVAL_INV.to_string(),
                VAL_DELTA_STEP_DEFVAL_INV.to_string(),
            ),
            (
                "the_red_env_delta_rank_decrease".to_string(),
                ty_the_red_env_delta_rank_decrease(),
                val_the_red_env_delta_rank_decrease(),
            ),
            (
                "r9_lt_irrefl".to_string(),
                TY_R9_LT_IRREFL.to_string(),
                VAL_R9_LT_IRREFL.to_string(),
            ),
            (
                "the_red_env_no_delta_cycle".to_string(),
                ty_the_red_env_no_delta_cycle(),
                val_the_red_env_no_delta_cycle(),
            ),
            (
                "r9_const_delta_dead".to_string(),
                ty_r9_const_delta_dead(),
                val_r9_const_delta_dead(),
            ),
            (
                "whnfAcc_const_dead".to_string(),
                ty_whnfacc_const_dead(),
                val_whnfacc_const_dead(),
            ),
            (
                "candInterp_delta_expand_sort".to_string(),
                ty_candinterp_delta_expand_sort(),
                val_candinterp_delta_expand_sort(),
            ),
            (
                "r9_const_is_neutral".to_string(),
                TY_R9_CONST_IS_NEUTRAL.to_string(),
                VAL_R9_CONST_IS_NEUTRAL.to_string(),
            ),
            (
                "r9_const_headfree_absurd".to_string(),
                TY_R9_CONST_HEADFREE_ABSURD.to_string(),
                VAL_R9_CONST_HEADFREE_ABSURD.to_string(),
            ),
            (
                "r9_const_obstruction_located".to_string(),
                TY_R9_CONST_OBSTRUCTION_LOCATED.to_string(),
                VAL_R9_CONST_OBSTRUCTION_LOCATED.to_string(),
            ),
            (
                "synTyC_fundamental".to_string(),
                TY_SYNTYC_FUNDAMENTAL.to_string(),
                val_syntyc_fundamental(),
            ),
            (
                "synTyC_sn_subst".to_string(),
                TY_SYNTYC_SN_SUBST.to_string(),
                VAL_SYNTYC_SN_SUBST.to_string(),
            ),
            (
                "synTyC_sn".to_string(),
                TY_SYNTYC_SN.to_string(),
                VAL_SYNTYC_SN.to_string(),
            ),
            (
                "synTyC_sn_closed".to_string(),
                TY_SYNTYC_SN_CLOSED.to_string(),
                VAL_SYNTYC_SN_CLOSED.to_string(),
            ),
            (
                "r9_the_red_env_all_lam".to_string(),
                ty_r9_the_red_env_all_lam(),
                VAL_R9_THE_RED_ENV_ALL_LAM.to_string(),
            ),
            (
                "def_env_all_lam_b_sound".to_string(),
                TY_DEF_ENV_ALL_LAM_B_SOUND.to_string(),
                val_def_env_all_lam_b_sound(),
            ),
            (
                "r9_real_delta_body_is_lam".to_string(),
                ty_r9_real_delta_body_is_lam(),
                val_r9_real_delta_body_is_lam(),
            ),
            (
                "synTyC_no_lam_at_sort".to_string(),
                TY_SYNTYC_NO_LAM_AT_SORT.to_string(),
                val_syntyc_no_lam_at_sort(),
            ),
            (
                "r9_konstDelta_no_real_instance".to_string(),
                ty_r9_konstdelta_no_real_instance(),
                val_r9_konstdelta_no_real_instance(),
            ),
            (
                "synTyL_to_synTyC".to_string(),
                TY_SYNTYL_TO_SYNTYC.to_string(),
                val_syntyl_to_syntyc(),
            ),
            (
                "synTyL_sn_via_synTyC".to_string(),
                TY_SYNTYL_SN_VIA_SYNTYC.to_string(),
                VAL_SYNTYL_SN_VIA_SYNTYC.to_string(),
            ),
            (
                "synTyL_no_const".to_string(),
                TY_SYNTYL_NO_CONST.to_string(),
                val_syntyl_no_const(),
            ),
            ("synTyC_id".to_string(), ty_synty_c_id(), val_synty_c_id()),
            (
                "synTyC_sort_witness".to_string(),
                ty_synty_c_sort_witness(),
                val_synty_c_sort_witness(),
            ),
            (
                "synTyC_konst_dead_witness".to_string(),
                ty_synty_c_konst_dead_witness(),
                val_synty_c_konst_dead_witness(),
            ),
            (
                "synTyC_sn_konst_witness".to_string(),
                ty_synty_c_sn_konst_witness(),
                val_synty_c_sn_konst_witness(),
            ),
            (
                "r9_rank_decrease_witness".to_string(),
                ty_r9_rank_decrease_witness(),
                val_r9_rank_decrease_witness(),
            ),
            (
                "r9_rank_decrease_witness_undefined".to_string(),
                ty_r9_rank_decrease_witness_undefined(),
                val_r9_rank_decrease_witness_undefined(),
            ),
            (
                "r9_konstDead_premise_necessary".to_string(),
                ty_r9_konstdead_premise_necessary(),
                val_r9_konstdead_premise_necessary(),
            ),
            (
                "r9_live_const_not_dead".to_string(),
                ty_r9_live_const_not_dead(),
                val_r9_live_const_not_dead(),
            ),
            (
                "synTyC_not_total".to_string(),
                ty_synty_c_not_total(),
                val_synty_c_not_total(),
            ),
        ]
    }

    /// The one inductive and every plain def, as full declaration sources.
    fn decl_sources() -> Vec<(String, String)> {
        let mut v: Vec<(String, String)> = src_r9_rank_tbl_chunks();
        v.extend(vec![
            ("r9_rank_tbl".to_string(), src_r9_rank_tbl()),
            ("r9_rank_nth".to_string(), SRC_R9_RANK_NTH.to_string()),
            ("rk".to_string(), SRC_RK.to_string()),
            ("const_occurs".to_string(), SRC_CONST_OCCURS.to_string()),
            (
                "rank_dominates_b".to_string(),
                SRC_RANK_DOMINATES_B.to_string(),
            ),
            (
                "def_env_ranked_b".to_string(),
                SRC_DEF_ENV_RANKED_B.to_string(),
            ),
            ("SynTyC".to_string(), src_syn_ty_c()),
            ("r9_sort_discr".to_string(), SRC_R9_SORT_DISCR.to_string()),
            ("r9_const_discr".to_string(), SRC_R9_CONST_DISCR.to_string()),
            ("kexpr_is_lam_b".to_string(), SRC_KEXPR_IS_LAM_B.to_string()),
            (
                "def_env_all_lam_b".to_string(),
                SRC_DEF_ENV_ALL_LAM_B.to_string(),
            ),
        ]);
        v
    }

    /// Parse-check every generated source — the fast guard for the commonest
    /// failure class (assembly mistakes invisible to `cargo check`).
    #[test]
    fn test_candmodel_r9_sources_parse() {
        for (name, ty, val) in theorem_sources() {
            let assembled = format!("def {name} : {ty} := {val}");
            parse_check(&assembled)
                .unwrap_or_else(|e| panic!("{name} should parse as a def: {e}\n{assembled}"));
        }
        for (name, src) in decl_sources() {
            parse_check(&src).unwrap_or_else(|e| panic!("{name} should parse: {e}\n{src}"));
        }
    }

    /// PER-STRING paren balance on every source.
    #[test]
    fn test_candmodel_r9_sources_paren_balanced() {
        let mut all: Vec<(String, String)> = Vec::new();
        for (n, ty, val) in theorem_sources() {
            all.push((format!("{n}::ty"), ty));
            all.push((format!("{n}::val"), val));
        }
        for (n, src) in decl_sources() {
            all.push((format!("{n}::decl"), src));
        }
        for (name, src) in &all {
            let mut depth: i64 = 0;
            for ch in src.chars() {
                match ch {
                    '(' => depth += 1,
                    ')' => depth -= 1,
                    _ => {}
                }
                assert!(depth >= 0, "close paren before its open in {name}: {src}");
            }
            assert_eq!(depth, 0, "unbalanced parens in {name}: {src}");
        }
    }

    /// Skip a run of parenthesised binder groups starting at `i`, returning
    /// (index after the groups, how many groups were skipped).
    fn skip_binder_groups(b: &[char], mut i: usize) -> (usize, usize) {
        let mut n = 0usize;
        loop {
            while i < b.len() && b[i] == ' ' {
                i += 1;
            }
            if i >= b.len() || b[i] != '(' {
                break;
            }
            let mut d = 0i64;
            while i < b.len() {
                if b[i] == '(' {
                    d += 1;
                } else if b[i] == ')' {
                    d -= 1;
                    if d == 0 {
                        i += 1;
                        break;
                    }
                }
                i += 1;
            }
            n += 1;
        }
        while i < b.len() && b[i] == ' ' {
            i += 1;
        }
        (i, n)
    }

    /// STRUCTURAL GUARD: a `forall` binder run must be terminated by a COMMA
    /// and a `fun` binder run by `=>`.
    #[test]
    fn test_candmodel_r9_binder_runs_terminated() {
        let mut all: Vec<(String, String)> = Vec::new();
        for (n, ty, val) in theorem_sources() {
            all.push((format!("{n}::ty"), ty));
            all.push((format!("{n}::val"), val));
        }
        for (name, src) in &all {
            let b: Vec<char> = src.chars().collect();
            for (kw, close) in [("forall ", ","), ("fun ", "=>")] {
                let mut from = 0usize;
                while let Some(rel) = src[from..].find(kw) {
                    let start = from + rel;
                    from = start + 1;
                    let ci = src[..start].chars().count() + kw.chars().count();
                    let (after, groups) = skip_binder_groups(&b, ci);
                    assert!(groups > 0, "{name}: `{kw}` with no parenthesised binder");
                    let tail: String = b[after..(after + 2).min(b.len())].iter().collect();
                    assert!(
                        tail.starts_with(close),
                        "{name}: `{kw}` binder run is not terminated by `{close}` — found \
                         `{tail}`"
                    );
                }
            }
        }
    }

    /// The rank table is the one the environment justifies: 127 entries,
    /// bounded by 8, with exactly 50 non-zero ones (the DefEnv entries).
    #[test]
    fn test_candmodel_r9_rank_table_shape() {
        assert_eq!(R9_RANKS.len(), 127, "one entry per interned reflected name");
        assert!(
            R9_RANKS.iter().all(|r| *r <= 8),
            "the measured longest delta-chain is 7, so no rank exceeds 8"
        );
        assert_eq!(
            R9_RANKS.iter().filter(|r| **r > 0).count(),
            50,
            "exactly the 50 DefEnv entries have a definitional value, and only those get a \
             non-zero rank — an undefined name must sit strictly below every defined one or the \
             decrease theorem is FALSE, not merely unprovable"
        );
        // Spot-pins on the two witness pairs, so a silent re-ordering of the
        // table cannot leave the witnesses reading a different fact.
        assert_eq!(
            R9_RANKS[120], 8,
            "instantiate is the DEEPEST definition of the reflected core, not \
             def_env_lift_closed_b — the 2026-08-26 first-cut pin got that wrong and the table \
             (which is generated) was right"
        );
        assert_eq!(R9_RANKS[118], 5, "def_env_lift_closed_b, the witness head");
        assert_eq!(R9_RANKS[90], 4, "def_env_closed_b sits one below it");
        assert_eq!(R9_RANKS[12], 0, "DefEnv is an inductive type, not a def");
        assert_eq!(R9_RANKS[84], 1, "Nat.pred bottoms out at the recursors");
        assert_eq!(R9_RANKS[31], 2, "Nat.sub goes through Nat.pred");
    }

    /// Shape guards.
    #[test]
    fn test_candmodel_r9_shape_guards() {
        let syntyc = src_syn_ty_c();

        // (1) THE HEADLINE PROPERTY OF THE LADDER: the judgment is SYNTACTIC.
        for forbidden in [
            "candInterp",
            "CandModel",
            "cm_Red",
            "RecEnvClosed",
            "RecEnvLiftClosed",
            "DefEnvClosed",
            "EnvAcyclic",
            "IsCandHF",
            "IsCandSet",
            "PiSet",
            "whnf_acc",
            "rk ",
        ] {
            assert!(
                !syntyc.contains(forbidden),
                "SynTyC must not mention {forbidden} — the judgment is SYNTACTIC, and in \
                 particular the RANK is never a hypothesis of a rule"
            );
        }

        // (2) THE RUNG: a const rule, in two clauses.
        assert!(
            syntyc.contains(KONST_DEAD_RULE),
            "SynTyC must carry the dead-const rule `{KONST_DEAD_RULE}`"
        );
        assert!(
            syntyc.contains(KONST_DELTA_RULE),
            "SynTyC must carry the delta-const rule `{KONST_DELTA_RULE}`"
        );
        assert!(
            syntyc.contains("SynTyC G (KExpr.const c us) (KExpr.sort m)"),
            "both const clauses must conclude at a SORT-typed slot — at a Pi-typed slot the \
             engine is unavailable (r9_const_obstruction_located)"
        );

        // (3) R8's six rules survive unchanged, which is what makes the bridge
        // hypothesis-free.
        assert!(syntyc.contains(VAR_RULE_LIFTED), "var must be R8's rule");
        assert!(syntyc.contains(PI_RULE_IMAX), "pi must be R8's rule");
        assert!(syntyc.contains(LET_RULE_SORT), "letTy must be R8's rule");
        for needle in [
            "| sort : forall (G : ListType KExpr) (n : Level), SynTyC G (KExpr.sort n) \
             (KExpr.sort (Level.succ n))",
            "SynTyC G f (KExpr.pi A B) -> SynTyC G a A -> SynTyC G (KExpr.app f a) B",
            "SimpleTy A -> SynTyC (ListType.cons KExpr A G) b B -> SynTyC G (KExpr.lam A b) \
             (KExpr.pi A B)",
        ] {
            assert!(
                syntyc.contains(needle),
                "SynTyC must carry the rule `{needle}`"
            );
        }

        // (4) RECURSOR-SHAPE PIN: no fixedIndicesToParams promotion.
        for extended in [
            "SynTyC (ListType.cons KExpr A G) B (KExpr.sort m)",
            "SynTyC (ListType.cons KExpr A G) b B",
            "SynTyC (ListType.cons KExpr (KExpr.sort n) G) b (KExpr.sort m)",
        ] {
            assert!(
                syntyc.contains(extended),
                "a recursive premise must conclude at the EXTENDED context (`{extended}`), or the \
                 leading index becomes fixed and fixedIndicesToParams promotes it"
            );
        }

        // (5) ARM-ARITY PIN: fields-then-IHs in constructor order, including
        // the two new minors.
        let fund = val_syntyc_fundamental();
        assert!(
            fund.contains(
                "(_qhA : SynTyC qG qA (KExpr.sort qn)) (_qhB : SynTyC (ListType.cons KExpr qA qG) \
                 qB (KExpr.sort qm)) (qihA :"
            ),
            "the pi minor must bind BOTH recursive fields before the first IH"
        );
        assert!(
            fund.contains(
                "(qhA : SimpleTy qA) (_qhb : SynTyC (ListType.cons KExpr qA qG) qb qB) (qih :"
            ),
            "the lam minor must bind the SimpleTy field, then the recursive field, then the IH"
        );
        assert!(
            fund.contains("(qm : Level) (qhn : Eq (OptionType KExpr) (defval_for"),
            "the konstDead minor must bind its lookup field and has NO IH (no recursive premise)"
        );
        assert!(
            fund.contains("(qhd : delta_step")
                && fund.contains("(_qhb : SynTyC qG qbody (KExpr.sort qm)) (qih :"),
            "the konstDelta minor must bind the delta field, then the recursive field, then the \
             single IH"
        );

        // (6) THE TWO NEW ARMS ARE THE RUNG, and each must consume its own
        // engine rather than re-deriving something weaker.
        assert!(
            fund.contains("whnfAcc_const_dead qc qus qhn"),
            "the konstDead arm must be the stuck-const accessibility outright"
        );
        assert!(
            fund.contains("candInterp_delta_expand_sort qm qc qus qbody qhd"),
            "the konstDelta arm must go through the landed delta engine"
        );
        assert!(
            fund.contains("(psubst idsubst qbody) qbody (psubst_id qbody)"),
            "the konstDelta arm must feed the body IH at IDSUBST and collapse it with psubst_id — \
             the engine wants membership of the body ITSELF, and that is why the rule needs no \
             closedness side condition"
        );

        // (7) PREMISE-FREEDOM GUARD, with EnvAcyclic first among equals: this
        // is the rung where a carried acyclicity premise would have been the
        // expected outcome, and it is not what happened.
        for (name, ty) in [
            ("synTyC_sn", TY_SYNTYC_SN.to_string()),
            ("synTyC_sn_closed", TY_SYNTYC_SN_CLOSED.to_string()),
            ("synTyC_sn_subst", TY_SYNTYC_SN_SUBST.to_string()),
            ("synTyC_fundamental", TY_SYNTYC_FUNDAMENTAL.to_string()),
            ("synTyL_to_synTyC", TY_SYNTYL_TO_SYNTYC.to_string()),
            ("synTyL_sn_via_synTyC", TY_SYNTYL_SN_VIA_SYNTYC.to_string()),
            ("SynTyC", syntyc.clone()),
        ] {
            for forbidden in [
                "EnvAcyclic",
                "WfEnv",
                "RecEnvClosed",
                "DefEnvClosed",
                "RecEnvLiftClosed",
                "CandModel",
                "cm_Red",
                "rank_dominates_b",
                "def_env_ranked_b",
            ] {
                assert!(
                    !ty.contains(forbidden),
                    "{name} must carry no {forbidden} premise — the R9 capstone is unconditional \
                     and the rank is DISCHARGED, never carried"
                );
            }
        }
        assert!(
            TY_SYNTYC_SN.contains("forall (G : ListType KExpr)"),
            "synTyC_sn must hold at an ARBITRARY context (idsubst models every context)"
        );

        // (8) B3 IS COMPUTED, NOT CARRIED: the decrease theorem must be closed
        // (no rank hypothesis) and must be the statement R2 wrote down.
        let dec = ty_the_red_env_delta_rank_decrease();
        assert!(
            dec.contains("delta_step (red_def the_red_env) (KExpr.const c us) body")
                && dec.contains("Eq Bool (const_occurs c2 body) Bool.true")
                && dec.contains("Lt (rk c2) (rk c)"),
            "the_red_env_delta_rank_decrease must be R2's projected shape: \
             delta_step (red_def the_red_env) (const c us) body -> const_occurs c2 body -> \
             Lt (rk c2) (rk c)"
        );
        assert!(
            !dec.contains("EnvAcyclic")
                && !dec.contains("WfEnv")
                && !dec.contains("def_env_ranked_b")
                && !dec.contains("rank_dominates_b"),
            "the decrease must carry NO acyclicity, well-formedness or checker premise — it is \
             discharged from the_red_env_ranked, which is one Eq.refl"
        );
        assert!(
            dec.ends_with("Lt (rk c2) (rk c)"),
            "the decrease's CONCLUSION is the rank drop; a trailing hypothesis after it would mean \
             something was re-hoisted"
        );
        assert_eq!(
            VAL_THE_RED_ENV_RANKED, "Eq.refl Bool Bool.true",
            "B3 is one kernel computation over the real reflected environment; anything else \
             means the rank stopped being computed"
        );
        assert_eq!(
            VAL_R9_THE_RED_ENV_ALL_LAM, "Eq.refl Bool Bool.true",
            "the vacuity measurement is likewise one kernel computation"
        );

        // (9) THE OBSTRUCTION IS LOCATED, and it is NOT the rank.
        assert!(
            TY_R9_CONST_IS_NEUTRAL.contains("Neutral (KExpr.const c us)")
                && TY_R9_CONST_HEADFREE_ABSURD.contains(
                    "Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.const c us))) \
                     (OptionType.none Name) -> Empty"
                ),
            "the obstruction must be LOCATED: unrestricted cr3 applicable at a const, the \
             head-free cr3 that candInterp actually has NOT"
        );
        // (10) AndType SLOT PIN (the universe trap R6 measured, R8 re-pinned).
        assert!(
            !TY_R9_CONST_OBSTRUCTION_LOCATED.contains("(C : Type)"),
            "r9_const_obstruction_located: an AndType slot may hold neither a Prop nor a Type-1 \
             quantification — the second slot is an ARROW into Empty for exactly that reason"
        );
        assert!(
            TY_R9_CONST_OBSTRUCTION_LOCATED.contains("-> Empty)"),
            "the second AndType slot must be the arrow into Empty, not the Eq itself"
        );

        // (11) The witnesses must exercise what they claim: both rank
        // witnesses go THROUGH the theorem, and the const witness is at a REAL
        // reflected name with a COMPUTED side condition.
        assert!(
            val_r9_rank_decrease_witness().starts_with("the_red_env_delta_rank_decrease ")
                && val_r9_rank_decrease_witness_undefined()
                    .starts_with("the_red_env_delta_rank_decrease "),
            "both rank witnesses must be obtained by applying the decrease theorem, not by \
             computing rk twice"
        );
        assert!(
            val_r9_rank_decrease_witness().contains("the_red_env_delta_nonvacuous"),
            "the rank witness must reuse the Guard-4 delta step rather than mint a new one"
        );
        assert!(
            ty_synty_c_konst_dead_witness().contains("kcre_name_12")
                && val_synty_c_konst_dead_witness().contains("Eq.refl (OptionType KExpr)"),
            "the const witness must be at a REAL reflected name with a kernel-COMPUTED lookup"
        );
        assert!(
            val_synty_c_sn_konst_witness().starts_with("synTyC_sn "),
            "the SN witness must be obtained by applying the capstone"
        );
    }

    /// The declarations in REGISTRATION ORDER, as
    /// `(kind, name, source)` where `kind` is `def` / `inductive` / `thm` and a
    /// `thm` source is the assembled `def <name> : <ty> := <val>`.
    ///
    /// Drives the scratch elaboration below; the real registration is
    /// `add_candmodel_construct_r9`, and the shape guard
    /// `test_candmodel_r9_plan_matches_registration` pins that this list names
    /// the same constants.
    fn registration_plan() -> Vec<(&'static str, String, String)> {
        let mut v: Vec<(&'static str, String, String)> = src_r9_rank_tbl_chunks()
            .into_iter()
            .map(|(n, src)| ("def", n, src))
            .collect();
        v.extend(vec![
            ("def", "r9_rank_tbl".to_string(), src_r9_rank_tbl()),
            (
                "def",
                "r9_rank_nth".to_string(),
                SRC_R9_RANK_NTH.to_string(),
            ),
            ("def", "rk".to_string(), SRC_RK.to_string()),
            (
                "def",
                "const_occurs".to_string(),
                SRC_CONST_OCCURS.to_string(),
            ),
            (
                "def",
                "rank_dominates_b".to_string(),
                SRC_RANK_DOMINATES_B.to_string(),
            ),
            (
                "def",
                "def_env_ranked_b".to_string(),
                SRC_DEF_ENV_RANKED_B.to_string(),
            ),
        ]);
        let thm = |name: &str, ty: String, val: String| {
            (
                "thm",
                name.to_string(),
                format!("def {name} : {ty} := {val}"),
            )
        };
        let all = theorem_sources();
        let get = |n: &str| {
            all.iter()
                .find(|(name, _, _)| name == n)
                .map(|(name, ty, val)| thm(name, ty.clone(), val.clone()))
                .unwrap_or_else(|| panic!("{n} should be in theorem_sources()"))
        };
        for n in [
            "the_red_env_ranked",
            "bool_cases_eq",
            "bor_false_case",
            "bor_eq_true_inv",
            "def_env_ranked_b_sound",
            "rank_dominates_occurs",
            "delta_step_defval_inv",
            "the_red_env_delta_rank_decrease",
            "r9_lt_irrefl",
            "the_red_env_no_delta_cycle",
            "r9_const_delta_dead",
            "whnfAcc_const_dead",
            "candInterp_delta_expand_sort",
            "r9_const_is_neutral",
            "r9_const_headfree_absurd",
            "r9_const_obstruction_located",
        ] {
            v.push(get(n));
        }
        v.push(("inductive", "SynTyC".to_string(), src_syn_ty_c()));
        for n in [
            "synTyC_fundamental",
            "synTyC_sn_subst",
            "synTyC_sn",
            "synTyC_sn_closed",
        ] {
            v.push(get(n));
        }
        v.push((
            "def",
            "r9_sort_discr".to_string(),
            SRC_R9_SORT_DISCR.to_string(),
        ));
        v.push((
            "def",
            "r9_const_discr".to_string(),
            SRC_R9_CONST_DISCR.to_string(),
        ));
        v.push((
            "def",
            "kexpr_is_lam_b".to_string(),
            SRC_KEXPR_IS_LAM_B.to_string(),
        ));
        v.push((
            "def",
            "def_env_all_lam_b".to_string(),
            SRC_DEF_ENV_ALL_LAM_B.to_string(),
        ));
        for n in [
            "r9_the_red_env_all_lam",
            "def_env_all_lam_b_sound",
            "r9_real_delta_body_is_lam",
            "synTyC_no_lam_at_sort",
            "r9_konstDelta_no_real_instance",
            "synTyL_to_synTyC",
            "synTyL_sn_via_synTyC",
            "synTyL_no_const",
            "synTyC_id",
            "synTyC_sort_witness",
            "synTyC_konst_dead_witness",
            "synTyC_sn_konst_witness",
            "r9_rank_decrease_witness",
            "r9_rank_decrease_witness_undefined",
            "r9_konstDead_premise_necessary",
            "r9_live_const_not_dead",
            "synTyC_not_total",
        ] {
            v.push(get(n));
        }
        v
    }

    /// The plan and the source tables name the same constants — so the scratch
    /// run below cannot silently check a subset.
    #[test]
    fn test_candmodel_r9_plan_matches_registration() {
        let planned: std::collections::BTreeSet<String> =
            registration_plan().into_iter().map(|(_, n, _)| n).collect();
        let mut declared: std::collections::BTreeSet<String> =
            theorem_sources().into_iter().map(|(n, _, _)| n).collect();
        for (n, _) in decl_sources() {
            declared.insert(n);
        }
        assert_eq!(
            planned, declared,
            "registration_plan and the source tables must name the same constants"
        );
    }

    /// SCRATCH ELABORATION — the iteration tool for this rung.
    ///
    /// Builds the substitution spec ONCE and appends every R9 declaration in
    /// registration order, reporting each independently instead of stopping at
    /// the first error. It is the `tests/spec_scratchpad.rs` contract at the
    /// substitution bundle: cheap enough to run per edit, and unlike the real
    /// stage it diagnoses a whole chain per build. This is NOT a replacement
    /// for `test_candmodel_r9_registered_and_reverifies`, which is what proves
    /// the stage is wired and the kernel re-checks every constant in place.
    #[test]
    fn test_candmodel_r9_scratch_elaborates() {
        let mut spec = crate::test_utils::build_substitution_spec_with_stack();
        // Already registered by the stage: nothing to re-append.
        if spec.definitions().contains_key("SynTyC") {
            return;
        }
        let mut failures: Vec<String> = Vec::new();
        for (kind, name, src) in registration_plan() {
            let desc = "R9 scratch candidate";
            let result = match kind {
                "inductive" => spec.add_inductive(&src, desc),
                _ => spec.add_recursive_def(&src, desc),
            };
            if let Err(e) = result {
                failures.push(format!("{name}: {e}"));
            }
        }
        assert!(
            failures.is_empty(),
            "R9 scratch elaboration failures ({}):\n{}",
            failures.len(),
            failures.join("\n")
        );
    }

    /// Registration + kernel re-verification against the substitution bundle.
    #[test]
    fn test_candmodel_r9_registered_and_reverifies() {
        let spec = crate::test_utils::build_substitution_spec_with_stack();
        let mut names: Vec<String> = theorem_sources().into_iter().map(|(n, _, _)| n).collect();
        for (n, _) in decl_sources() {
            names.push(n);
        }
        for name in &names {
            assert!(
                spec.definitions().contains_key(name),
                "{name} should be registered by the candmodel_construct_r9 stage"
            );
        }
        for (name, _, _) in theorem_sources() {
            spec.verify_definition(&name).unwrap_or_else(|e| {
                panic!("{name} should re-typecheck in the spec environment: {e:?}")
            });
        }
    }
}
