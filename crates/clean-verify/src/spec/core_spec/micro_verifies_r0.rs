// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bricks 1-2 of the faithful micro-checker spec: the FRESH-NAME
//! context-indexed verification relation `MicroVerifies`, its kernel-agreement
//! theorems for the three arms it has, ground positive witnesses, an
//! empty-context bvar REJECTION witness, and a Pi witness that pins the
//! CONTEXT PUSH.
//!
//! Per `designs/2026-08-23-micro-faithful-spec-scoping.md` (the faithful-spec
//! plan) and the Brick-6 fresh-names constraint of `micro_soundness.rs:33-38`:
//! the existing `micro_has_type` is a TOTAL (degenerate) predicate kept as the
//! tripwired historical band; THIS family is its honest successor and therefore
//! uses fresh names throughout, and NO existing producer
//! (`micro_sort_typing`/`kernel_to_micro_typing`/...) is re-pointed at it — a
//! retained producer over a non-total family would derive `Empty`.
//!
//! ## Honesty notes (read before quoting)
//!
//! - **PARTIAL relation: 3 arms (sort, bvar, pi) ONLY.** `MicroVerifies G c e T`
//!   models "`verify_impl(cert c, expr e)` returns `Ok(T)` under context `G`"
//!   (`crates/clean-kernel/src/micro/checker.rs::verify_impl`) arm-for-arm,
//!   but this brick carries ONLY the Sort rule (checker.rs:319-327), the
//!   BVar rule (checker.rs:363-381) and the Pi rule (checker.rs:464-510).
//!   lam/app/let arms are LATER bricks;
//!   const/opaque/lit/proj are out-of-fragment per the plan. Absence of a
//!   derivation for those shapes means "outside the modeled fragment", NOT
//!   "the checker rejects".
//! - **The def-eq side condition is the REFLECTED `micro_def_eq`, a NARROWER
//!   fragment than the Rust one.** `micro_def_eq` (micro_checker.rs, Brick 3)
//!   is structural equality after a size-fueled beta+zeta weak-head loop, and
//!   its level comparison (`micro_level_eqb` inside `micro_structural_eq`) is
//!   level-EXACT. The Rust `def_eq_impl` whnfs with an env-aware reducer
//!   (beta + zeta + delta + native iota, closed allowlists — micro/mod.rs) and
//!   is universe-BLIND. So the bvar arm is faithful on the beta/zeta,
//!   level-exact, env-free fragment: pairs the Rust def_eq equates only via
//!   delta/iota/universe-blindness have NO derivation here. That is an honest
//!   under-approximation, never an over-claim.
//! - **`universe_blind` IS A CHECKER MODE, and the Pi arm is where it starts
//!   to bite — measured 2026-09-17.** `MicroChecker` carries a `universe_blind: bool`
//!   (checker.rs:172). `MicroChecker::new()` sets it FALSE (checker.rs:194);
//!   `MicroChecker::with_env()` — the env-aware constructor — sets it TRUE
//!   (checker.rs:207), and says so in its own doc: "Runs universe-blind for
//!   typing. The load-bearing reduction re-check is universe-independent."
//!   The flag guards exactly three sites: the Pi rule's two level checks
//!   (checker.rs:481, :499) and the `Sort`/`Sort` def-eq case
//!   (checker.rs:914).
//!
//!   **The Sort rule's own level check (checker.rs:320) is NOT guarded**, so
//!   `MicroVerifies.sort` is faithful in BOTH modes — and the BVar rule has no
//!   level check of its own. That was luck, not design, and it expired at the
//!   Pi arm exactly as predicted: **`MicroVerifies.pi`'s two level premises
//!   model the `new()` checker ONLY**, and OVER-approximate the `with_env()`
//!   one, which accepts any levels there. So the "honest under-approximation,
//!   never an over-claim" sentence below does NOT cover the Pi arm, and must
//!   not be quoted as if it did. This is the band's first two-sided narrowing.
//! - **The sort arm's level equality is exactly faithful.** Rust
//!   `MicroLevel::level_eq` is derived structural `PartialEq`
//!   (micro/types.rs:1453); `micro_level_eqb` is the reflected structural
//!   equality. The conclusion `sort (succ cl)` uses the CERT level, exactly as
//!   checker.rs:326 returns `Sort(succ(level))`.
//! - **The bvar arm mirrors checker.rs:363-381 on acceptance.** One index `i`
//!   serves cert and expr (the Rust arm errors on `idx != i`, so accepting
//!   runs have them equal); `mv_ctx_lookup G i` succeeding IS the Rust
//!   `idx < depth` bound plus the `context[depth - 1 - idx]` access (head of
//!   the cons-list = innermost binder = de Bruijn 0); the lift is
//!   `micro_lift A 0 (succ i)` — the Rust `ctx_ty.lift(0, depth - ctx_pos)`
//!   with `depth - ctx_pos = idx + 1`; the conclusion is the cert-carried type
//!   `cty`, exactly what the Rust arm returns. Like the Rust arm, NO context
//!   well-formedness is checked.
//! - **Agreement is per-arm and fragment-scoped; nothing claims the Rust
//!   checker itself.** `micro_kernel_bvar_agree`'s conclusion type
//!   `kernel_to_micro (lift_at A 0 (succ i))` is literally `kernel_to_micro`
//!   of the type `KernelInfers.bvar` / `TypingCtx.var` conclude
//!   (dependent_sn_richmodel.rs:109/:230) — the exact-translation agreement on
//!   the bvar arm. The model<->Rust bridge can never be a kernel theorem.
//! - **Level erasure rides along.** `level_to_microlevel` erases `Level.param`
//!   to zero, so the sort agreement is exact on param-free levels and
//!   level-erased on parameters (both sides erase identically, so the theorem
//!   is true as stated — but it does not distinguish params).
//!
//! ## Census
//!
//! ZERO new axioms: one genuine `add_inductive` (lowers to
//! Inductive/Constructor/Recursor), five plain defs, ten kernel-checked
//! theorems/witnesses. Census-neutral.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

// ================================================================
// Group A — substrate defs: the micro-side context lookup, the
// kernel->micro context/option translations, and a head discriminator.
// ================================================================

/// Micro-side context lookup; byte-mirror of the kernel-side `ctx_lookup`
/// (dependent_sn_richmodel.rs) at `MicroExpr`. Head of the cons-list is the
/// innermost binder (de Bruijn index 0), so `mv_ctx_lookup G i` is exactly the
/// Rust `context[depth - 1 - idx]` access guarded by `idx < depth`
/// (checker.rs:367-372): out of range returns `none`.
pub(super) const SRC_MV_CTX_LOOKUP: &str = "def mv_ctx_lookup (g : ListType MicroExpr) : Nat -> OptionType MicroExpr := @ListType.rec MicroExpr (fun (_ : ListType MicroExpr) => Nat -> OptionType MicroExpr) (fun (_ : Nat) => @OptionType.none MicroExpr) (fun (a : MicroExpr) (rest : ListType MicroExpr) (ih : Nat -> OptionType MicroExpr) => fun (i : Nat) => @Nat.rec (fun (_ : Nat) => OptionType MicroExpr) (@OptionType.some MicroExpr a) (fun (n : Nat) (_ : OptionType MicroExpr) => ih n) i) g";

/// Pointwise `kernel_to_micro` over a kernel context.
pub(super) const SRC_MV_KCTX_TO_MICRO: &str = "def mv_kctx_to_micro (g : ListType KExpr) : ListType MicroExpr := @ListType.rec KExpr (fun (_ : ListType KExpr) => ListType MicroExpr) (@ListType.nil MicroExpr) (fun (a : KExpr) (rest : ListType KExpr) (ih : ListType MicroExpr) => @ListType.cons MicroExpr (kernel_to_micro a) ih) g";

/// `kernel_to_micro` mapped through `OptionType`.
pub(super) const SRC_MV_OPT_MAP_MICRO: &str = "def mv_opt_map_micro (o : OptionType KExpr) : OptionType MicroExpr := @OptionType.rec KExpr (fun (_ : OptionType KExpr) => OptionType MicroExpr) (@OptionType.none MicroExpr) (fun (a : KExpr) => @OptionType.some MicroExpr (kernel_to_micro a)) o";

/// Head discriminator for the rejection proof: `sort` heads map to an
/// inhabited type (`Nat`), every other head to `Empty` — the `MicroExpr`
/// analogue of `opt_is_none` (iota_subst.rs). Minor-premise order:
/// bvar, sort, app, lam, pi, let_, opaque_.
pub(super) const SRC_MV_SORT_HEAD_TYPE: &str = "def mv_sort_head_type (e : MicroExpr) : Type := @MicroExpr.rec (fun (_ : MicroExpr) => Type) (fun (i : Nat) => Empty) (fun (l : MicroLevel) => Nat) (fun (f : MicroExpr) (a : MicroExpr) (_ : Type) (_ : Type) => Empty) (fun (t : MicroExpr) (b : MicroExpr) (_ : Type) (_ : Type) => Empty) (fun (t : MicroExpr) (b : MicroExpr) (_ : Type) (_ : Type) => Empty) (fun (t : MicroExpr) (v : MicroExpr) (b : MicroExpr) (_ : Type) (_ : Type) (_ : Type) => Empty) (fun (t : MicroExpr) (_ : Type) => Empty) e";

/// Head discriminator for the Pi arm of the rejection proof: `pi` heads map to
/// an inhabited type (`Nat`), every other head to `Empty`.
///
/// `mv_sort_head_type` cannot serve here — it sends BOTH `pi` and `bvar` to
/// `Empty`, so it kills the sort minor and nothing else. Adding the Pi arm to
/// `MicroVerifies` adds a third minor to its recursor, and that minor needs a
/// discriminator that separates `pi` from `bvar`. Minor-premise order, as
/// above: bvar, sort, app, lam, pi, let_, opaque_.
pub(super) const SRC_MV_PI_HEAD_TYPE: &str = "def mv_pi_head_type (e : MicroExpr) : Type := @MicroExpr.rec (fun (_z : MicroExpr) => Type) (fun (bi : Nat) => Empty) (fun (sl : MicroLevel) => Empty) (fun (af : MicroExpr) (aa : MicroExpr) (_cf : Type) (_ca : Type) => Empty) (fun (lty : MicroExpr) (lb : MicroExpr) (_cty : Type) (_cb : Type) => Empty) (fun (pty : MicroExpr) (pb : MicroExpr) (_cty : Type) (_cb : Type) => Nat) (fun (zty : MicroExpr) (zv : MicroExpr) (zb : MicroExpr) (_c1 : Type) (_c2 : Type) (_c3 : Type) => Empty) (fun (ot : MicroExpr) (_ct : Type) => Empty) e";

// ================================================================
// Group B — the relation: FRESH-NAME, context-indexed, HONESTLY PARTIAL
// (sort + bvar arms only in this brick).
// ================================================================

// RECURSOR-SHAPE PIN (measured, do not "clean up"): the bvar arm deliberately
// leads with `(i : Nat)` and binds `G` FOURTH, while the sort arm leads with
// `G`. If every constructor led with a `(G : ListType MicroExpr)` passed
// unchanged to index 0, the inductive compiler would promote that uniform
// prefix to an IMPLICIT recursor parameter (measured on the first build of
// this brick: the sort minor lost its G binder and the motive became an
// implicit to be inferred, which broke the rejection inversion). With the
// leading binder types differing across arms, no promotion fires: the
// generated MicroVerifies.rec keeps G as an explicit INDEX with an explicit
// motive over all four indices — the KernelInfers.rec shape the inversion
// below and the later pi/lam bricks (extended-context recursive fields) both
// require.
pub(super) const SRC_MICRO_VERIFIES: &str = r"inductive MicroVerifies : ListType MicroExpr -> MicroCert -> MicroExpr -> MicroExpr -> Type
| sort : forall (G : ListType MicroExpr) (cl : MicroLevel) (l : MicroLevel), @Eq Bool (micro_level_eqb cl l) Bool.true -> MicroVerifies G (MicroCert.sort cl) (MicroExpr.sort l) (MicroExpr.sort (MicroLevel.succ cl))
| bvar : forall (i : Nat) (cty : MicroExpr) (A : MicroExpr) (G : ListType MicroExpr), @Eq (OptionType MicroExpr) (mv_ctx_lookup G i) (@OptionType.some MicroExpr A) -> @Eq Bool (micro_def_eq cty (micro_lift A Nat.zero (Nat.succ i))) Bool.true -> MicroVerifies G (MicroCert.bvar i cty) (MicroExpr.bvar i) cty
| pi : forall (G : ListType MicroExpr) (A : MicroExpr) (B : MicroExpr) (ca : MicroCert) (cb : MicroCert) (cl1 : MicroLevel) (cl2 : MicroLevel) (SA : MicroExpr) (l1 : MicroLevel) (SB : MicroExpr) (l2 : MicroLevel), MicroVerifies G ca A SA -> @Eq MicroExpr (micro_whnf_iter (micro_size SA) SA) (MicroExpr.sort l1) -> @Eq Bool (micro_level_eqb l1 cl1) Bool.true -> MicroVerifies (@ListType.cons MicroExpr A G) cb B SB -> @Eq MicroExpr (micro_whnf_iter (micro_size SB) SB) (MicroExpr.sort l2) -> @Eq Bool (micro_level_eqb l2 cl2) Bool.true -> MicroVerifies G (MicroCert.pi ca cl1 cb cl2) (MicroExpr.pi A B) (MicroExpr.sort (MicroLevel.imax cl1 cl2))";

// ================================================================
// Group C — the ctx_lookup/translation commutation lemma (minted here, as
// the plan directs) and the two per-arm kernel agreement theorems.
// ================================================================

pub(super) const TY_MV_CTX_LOOKUP_COMMUTE: &str = "forall (G : ListType KExpr) (i : Nat), @Eq (OptionType MicroExpr) (mv_ctx_lookup (mv_kctx_to_micro G) i) (mv_opt_map_micro (ctx_lookup G i))";
pub(super) const VAL_MV_CTX_LOOKUP_COMMUTE: &str = "fun (G : ListType KExpr) (i : Nat) => @ListType.rec KExpr (fun (g : ListType KExpr) => forall (j : Nat), @Eq (OptionType MicroExpr) (mv_ctx_lookup (mv_kctx_to_micro g) j) (mv_opt_map_micro (ctx_lookup g j))) (fun (j : Nat) => @Eq.refl (OptionType MicroExpr) (@OptionType.none MicroExpr)) (fun (a : KExpr) (rest : ListType KExpr) (ih : forall (j : Nat), @Eq (OptionType MicroExpr) (mv_ctx_lookup (mv_kctx_to_micro rest) j) (mv_opt_map_micro (ctx_lookup rest j))) => fun (j : Nat) => @Nat.rec (fun (k : Nat) => @Eq (OptionType MicroExpr) (mv_ctx_lookup (mv_kctx_to_micro (@ListType.cons KExpr a rest)) k) (mv_opt_map_micro (ctx_lookup (@ListType.cons KExpr a rest) k))) (@Eq.refl (OptionType MicroExpr) (@OptionType.some MicroExpr (kernel_to_micro a))) (fun (n : Nat) (_ihn : @Eq (OptionType MicroExpr) (mv_ctx_lookup (mv_kctx_to_micro (@ListType.cons KExpr a rest)) n) (mv_opt_map_micro (ctx_lookup (@ListType.cons KExpr a rest) n))) => ih n) j) G i";

pub(super) const TY_MICRO_KERNEL_SORT_AGREE: &str = "forall (G : ListType KExpr) (l : Level), MicroVerifies (mv_kctx_to_micro G) (MicroCert.sort (level_to_microlevel l)) (kernel_to_micro (KExpr.sort l)) (kernel_to_micro (KExpr.sort (Level.succ l)))";
pub(super) const VAL_MICRO_KERNEL_SORT_AGREE: &str = "fun (G : ListType KExpr) (l : Level) => MicroVerifies.sort (mv_kctx_to_micro G) (level_to_microlevel l) (level_to_microlevel l) (micro_level_eqb_refl (level_to_microlevel l))";

pub(super) const TY_MICRO_KERNEL_BVAR_AGREE: &str = "forall (G : ListType KExpr) (i : Nat) (A : KExpr), @Eq (OptionType KExpr) (ctx_lookup G i) (@OptionType.some KExpr A) -> MicroVerifies (mv_kctx_to_micro G) (MicroCert.bvar i (kernel_to_micro (lift_at A Nat.zero (Nat.succ i)))) (MicroExpr.bvar i) (kernel_to_micro (lift_at A Nat.zero (Nat.succ i)))";
pub(super) const VAL_MICRO_KERNEL_BVAR_AGREE: &str = "fun (G : ListType KExpr) (i : Nat) (A : KExpr) (hlk : @Eq (OptionType KExpr) (ctx_lookup G i) (@OptionType.some KExpr A)) => MicroVerifies.bvar i (kernel_to_micro (lift_at A Nat.zero (Nat.succ i))) (kernel_to_micro A) (mv_kctx_to_micro G) (@Eq.trans (OptionType MicroExpr) (mv_ctx_lookup (mv_kctx_to_micro G) i) (mv_opt_map_micro (ctx_lookup G i)) (@OptionType.some MicroExpr (kernel_to_micro A)) (mv_ctx_lookup_commute G i) (@Eq.cong (OptionType KExpr) (OptionType MicroExpr) (fun (o : OptionType KExpr) => mv_opt_map_micro o) (ctx_lookup G i) (@OptionType.some KExpr A) hlk)) (@Eq.trans Bool (micro_def_eq (kernel_to_micro (lift_at A Nat.zero (Nat.succ i))) (micro_lift (kernel_to_micro A) Nat.zero (Nat.succ i))) (micro_def_eq (micro_lift (kernel_to_micro A) Nat.zero (Nat.succ i)) (micro_lift (kernel_to_micro A) Nat.zero (Nat.succ i))) Bool.true (@Eq.cong MicroExpr Bool (fun (z : MicroExpr) => micro_def_eq z (micro_lift (kernel_to_micro A) Nat.zero (Nat.succ i))) (kernel_to_micro (lift_at A Nat.zero (Nat.succ i))) (micro_lift (kernel_to_micro A) Nat.zero (Nat.succ i)) (kernel_to_micro_lift_commute A Nat.zero (Nat.succ i))) (micro_def_eq_refl (micro_lift (kernel_to_micro A) Nat.zero (Nat.succ i))))";

/// The Pi arm's kernel-agreement theorem.
///
/// Three iota steps carry it, all on genuine constructor applications so they
/// fire with `A`, `B`, `G`, `u`, `v` still variables: `mv_kctx_to_micro (cons A
/// G)` to `cons (kernel_to_micro A) (mv_kctx_to_micro G)`, `kernel_to_micro
/// (KExpr.pi A B)` to `MicroExpr.pi …`, and `kernel_to_micro (KExpr.sort
/// (Level.imax u v))` to `MicroExpr.sort (MicroLevel.imax …)`.
pub(super) const TY_MICRO_KERNEL_PI_AGREE: &str = "forall (G : ListType KExpr) (A : KExpr) (B : KExpr) (ca : MicroCert) (cb : MicroCert) (u : Level) (v : Level) (SA : MicroExpr) (SB : MicroExpr), MicroVerifies (mv_kctx_to_micro G) ca (kernel_to_micro A) SA -> @Eq MicroExpr (micro_whnf_iter (micro_size SA) SA) (MicroExpr.sort (level_to_microlevel u)) -> MicroVerifies (mv_kctx_to_micro (@ListType.cons KExpr A G)) cb (kernel_to_micro B) SB -> @Eq MicroExpr (micro_whnf_iter (micro_size SB) SB) (MicroExpr.sort (level_to_microlevel v)) -> MicroVerifies (mv_kctx_to_micro G) (MicroCert.pi ca (level_to_microlevel u) cb (level_to_microlevel v)) (kernel_to_micro (KExpr.pi A B)) (kernel_to_micro (KExpr.sort (Level.imax u v)))";
pub(super) const VAL_MICRO_KERNEL_PI_AGREE: &str = "fun (G : ListType KExpr) (A : KExpr) (B : KExpr) (ca : MicroCert) (cb : MicroCert) (u : Level) (v : Level) (SA : MicroExpr) (SB : MicroExpr) (dA : MicroVerifies (mv_kctx_to_micro G) ca (kernel_to_micro A) SA) (hwA : @Eq MicroExpr (micro_whnf_iter (micro_size SA) SA) (MicroExpr.sort (level_to_microlevel u))) (dB : MicroVerifies (mv_kctx_to_micro (@ListType.cons KExpr A G)) cb (kernel_to_micro B) SB) (hwB : @Eq MicroExpr (micro_whnf_iter (micro_size SB) SB) (MicroExpr.sort (level_to_microlevel v))) => MicroVerifies.pi (mv_kctx_to_micro G) (kernel_to_micro A) (kernel_to_micro B) ca cb (level_to_microlevel u) (level_to_microlevel v) SA (level_to_microlevel u) SB (level_to_microlevel v) dA hwA (micro_level_eqb_refl (level_to_microlevel u)) dB hwB (micro_level_eqb_refl (level_to_microlevel v))";

// ================================================================
// Group D — witnesses: two ground positive derivations, a lift-arithmetic
// pin, and the empty-context bvar REJECTION.
// ================================================================

pub(super) const TY_MV_SORT_GROUND_WITNESS: &str = "MicroVerifies (@ListType.nil MicroExpr) (MicroCert.sort MicroLevel.zero) (MicroExpr.sort MicroLevel.zero) (MicroExpr.sort (MicroLevel.succ MicroLevel.zero))";
pub(super) const VAL_MV_SORT_GROUND_WITNESS: &str = "MicroVerifies.sort (@ListType.nil MicroExpr) MicroLevel.zero MicroLevel.zero (@Eq.refl Bool Bool.true)";

pub(super) const TY_MV_BVAR_GROUND_WITNESS: &str = "MicroVerifies (@ListType.cons MicroExpr (MicroExpr.sort MicroLevel.zero) (@ListType.nil MicroExpr)) (MicroCert.bvar Nat.zero (MicroExpr.sort MicroLevel.zero)) (MicroExpr.bvar Nat.zero) (MicroExpr.sort MicroLevel.zero)";
pub(super) const VAL_MV_BVAR_GROUND_WITNESS: &str = "MicroVerifies.bvar Nat.zero (MicroExpr.sort MicroLevel.zero) (MicroExpr.sort MicroLevel.zero) (@ListType.cons MicroExpr (MicroExpr.sort MicroLevel.zero) (@ListType.nil MicroExpr)) (@Eq.refl (OptionType MicroExpr) (@OptionType.some MicroExpr (MicroExpr.sort MicroLevel.zero))) (@Eq.refl Bool Bool.true)";

pub(super) const TY_MV_BVAR_LIFT_FIRES_WITNESS: &str = "MicroVerifies (@ListType.cons MicroExpr (MicroExpr.sort MicroLevel.zero) (@ListType.cons MicroExpr (MicroExpr.bvar Nat.zero) (@ListType.nil MicroExpr))) (MicroCert.bvar (Nat.succ Nat.zero) (MicroExpr.bvar (Nat.succ (Nat.succ Nat.zero)))) (MicroExpr.bvar (Nat.succ Nat.zero)) (MicroExpr.bvar (Nat.succ (Nat.succ Nat.zero)))";
pub(super) const VAL_MV_BVAR_LIFT_FIRES_WITNESS: &str = "MicroVerifies.bvar (Nat.succ Nat.zero) (MicroExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (MicroExpr.bvar Nat.zero) (@ListType.cons MicroExpr (MicroExpr.sort MicroLevel.zero) (@ListType.cons MicroExpr (MicroExpr.bvar Nat.zero) (@ListType.nil MicroExpr))) (@Eq.refl (OptionType MicroExpr) (@OptionType.some MicroExpr (MicroExpr.bvar Nat.zero))) (@Eq.refl Bool Bool.true)";

/// `(Sort 0) -> (Sort 0) : Sort (imax 1 1)`, at the empty context.
///
/// Both whnf premises are `Eq.refl`: `micro_size (MicroExpr.sort l)` reduces to
/// `Nat.succ Nat.zero`, `micro_whnf_iter (Nat.succ Nat.zero) e` to
/// `micro_whnf e`, and `micro_whnf` leaves a sort alone.
pub(super) const TY_MV_PI_GROUND_WITNESS: &str = "MicroVerifies (@ListType.nil MicroExpr) (MicroCert.pi (MicroCert.sort MicroLevel.zero) (MicroLevel.succ MicroLevel.zero) (MicroCert.sort MicroLevel.zero) (MicroLevel.succ MicroLevel.zero)) (MicroExpr.pi (MicroExpr.sort MicroLevel.zero) (MicroExpr.sort MicroLevel.zero)) (MicroExpr.sort (MicroLevel.imax (MicroLevel.succ MicroLevel.zero) (MicroLevel.succ MicroLevel.zero)))";
pub(super) const VAL_MV_PI_GROUND_WITNESS: &str = "MicroVerifies.pi (@ListType.nil MicroExpr) (MicroExpr.sort MicroLevel.zero) (MicroExpr.sort MicroLevel.zero) (MicroCert.sort MicroLevel.zero) (MicroCert.sort MicroLevel.zero) (MicroLevel.succ MicroLevel.zero) (MicroLevel.succ MicroLevel.zero) (MicroExpr.sort (MicroLevel.succ MicroLevel.zero)) (MicroLevel.succ MicroLevel.zero) (MicroExpr.sort (MicroLevel.succ MicroLevel.zero)) (MicroLevel.succ MicroLevel.zero) (MicroVerifies.sort (@ListType.nil MicroExpr) MicroLevel.zero MicroLevel.zero (@Eq.refl Bool Bool.true)) (@Eq.refl MicroExpr (MicroExpr.sort (MicroLevel.succ MicroLevel.zero))) (@Eq.refl Bool Bool.true) (MicroVerifies.sort (@ListType.cons MicroExpr (MicroExpr.sort MicroLevel.zero) (@ListType.nil MicroExpr)) MicroLevel.zero MicroLevel.zero (@Eq.refl Bool Bool.true)) (@Eq.refl MicroExpr (MicroExpr.sort (MicroLevel.succ MicroLevel.zero))) (@Eq.refl Bool Bool.true)";

/// `(X : Sort 0) -> X`, at the empty context — and this one PINS THE PUSH.
///
/// The ground witness above never reads the pushed binder, so it says nothing
/// about `checker.rs`'s `self.context.push(arg_ty)` (line 488). This one's body
/// derivation is exactly `mv_bvar_ground_witness`, which is IMPOSSIBLE at `nil`
/// — that is `mv_bvar_nil_reject` — so it kernel-checks only if
/// `ListType.cons MicroExpr A G` genuinely models the push.
pub(super) const TY_MV_PI_PUSH_FIRES_WITNESS: &str = "MicroVerifies (@ListType.nil MicroExpr) (MicroCert.pi (MicroCert.sort MicroLevel.zero) (MicroLevel.succ MicroLevel.zero) (MicroCert.bvar Nat.zero (MicroExpr.sort MicroLevel.zero)) MicroLevel.zero) (MicroExpr.pi (MicroExpr.sort MicroLevel.zero) (MicroExpr.bvar Nat.zero)) (MicroExpr.sort (MicroLevel.imax (MicroLevel.succ MicroLevel.zero) MicroLevel.zero))";
pub(super) const VAL_MV_PI_PUSH_FIRES_WITNESS: &str = "MicroVerifies.pi (@ListType.nil MicroExpr) (MicroExpr.sort MicroLevel.zero) (MicroExpr.bvar Nat.zero) (MicroCert.sort MicroLevel.zero) (MicroCert.bvar Nat.zero (MicroExpr.sort MicroLevel.zero)) (MicroLevel.succ MicroLevel.zero) MicroLevel.zero (MicroExpr.sort (MicroLevel.succ MicroLevel.zero)) (MicroLevel.succ MicroLevel.zero) (MicroExpr.sort MicroLevel.zero) MicroLevel.zero (MicroVerifies.sort (@ListType.nil MicroExpr) MicroLevel.zero MicroLevel.zero (@Eq.refl Bool Bool.true)) (@Eq.refl MicroExpr (MicroExpr.sort (MicroLevel.succ MicroLevel.zero))) (@Eq.refl Bool Bool.true) (MicroVerifies.bvar Nat.zero (MicroExpr.sort MicroLevel.zero) (MicroExpr.sort MicroLevel.zero) (@ListType.cons MicroExpr (MicroExpr.sort MicroLevel.zero) (@ListType.nil MicroExpr)) (@Eq.refl (OptionType MicroExpr) (@OptionType.some MicroExpr (MicroExpr.sort MicroLevel.zero))) (@Eq.refl Bool Bool.true)) (@Eq.refl MicroExpr (MicroExpr.sort MicroLevel.zero)) (@Eq.refl Bool Bool.true)";

pub(super) const TY_MV_BVAR_NIL_REJECT: &str = "forall (cty : MicroExpr) (T : MicroExpr), MicroVerifies (@ListType.nil MicroExpr) (MicroCert.bvar Nat.zero cty) (MicroExpr.bvar Nat.zero) T -> Empty";
pub(super) const VAL_MV_BVAR_NIL_REJECT: &str = "fun (cty : MicroExpr) (T : MicroExpr) (d : MicroVerifies (@ListType.nil MicroExpr) (MicroCert.bvar Nat.zero cty) (MicroExpr.bvar Nat.zero) T) => @MicroVerifies.rec (fun (G2 : ListType MicroExpr) (c2 : MicroCert) (e2 : MicroExpr) (T2 : MicroExpr) (_d2 : MicroVerifies G2 c2 e2 T2) => @Eq (ListType MicroExpr) G2 (@ListType.nil MicroExpr) -> @Eq MicroExpr e2 (MicroExpr.bvar Nat.zero) -> Empty) (fun (G2 : ListType MicroExpr) (cl : MicroLevel) (l : MicroLevel) (_hl : @Eq Bool (micro_level_eqb cl l) Bool.true) (_hG : @Eq (ListType MicroExpr) G2 (@ListType.nil MicroExpr)) (he : @Eq MicroExpr (MicroExpr.sort l) (MicroExpr.bvar Nat.zero)) => @Eq.substType MicroExpr mv_sort_head_type (MicroExpr.sort l) (MicroExpr.bvar Nat.zero) he Nat.zero) (fun (i2 : Nat) (cty2 : MicroExpr) (A2 : MicroExpr) (G2 : ListType MicroExpr) (hlk : @Eq (OptionType MicroExpr) (mv_ctx_lookup G2 i2) (@OptionType.some MicroExpr A2)) (_hdeq : @Eq Bool (micro_def_eq cty2 (micro_lift A2 Nat.zero (Nat.succ i2))) Bool.true) (hG : @Eq (ListType MicroExpr) G2 (@ListType.nil MicroExpr)) (_he : @Eq MicroExpr (MicroExpr.bvar i2) (MicroExpr.bvar Nat.zero)) => option_none_ne_some_type MicroExpr A2 Empty (@Eq.substType (ListType MicroExpr) (fun (g : ListType MicroExpr) => @Eq (OptionType MicroExpr) (mv_ctx_lookup g i2) (@OptionType.some MicroExpr A2)) G2 (@ListType.nil MicroExpr) hG hlk)) (fun (G2 : ListType MicroExpr) (A2 : MicroExpr) (B2 : MicroExpr) (ca2 : MicroCert) (cb2 : MicroCert) (cl1 : MicroLevel) (cl2 : MicroLevel) (SA : MicroExpr) (l1 : MicroLevel) (SB : MicroExpr) (l2 : MicroLevel) (_dA : MicroVerifies G2 ca2 A2 SA) (_hwA : @Eq MicroExpr (micro_whnf_iter (micro_size SA) SA) (MicroExpr.sort l1)) (_hlA : @Eq Bool (micro_level_eqb l1 cl1) Bool.true) (_dB : MicroVerifies (@ListType.cons MicroExpr A2 G2) cb2 B2 SB) (_hwB : @Eq MicroExpr (micro_whnf_iter (micro_size SB) SB) (MicroExpr.sort l2)) (_hlB : @Eq Bool (micro_level_eqb l2 cl2) Bool.true) (_ihA : @Eq (ListType MicroExpr) G2 (@ListType.nil MicroExpr) -> @Eq MicroExpr A2 (MicroExpr.bvar Nat.zero) -> Empty) (_ihB : @Eq (ListType MicroExpr) (@ListType.cons MicroExpr A2 G2) (@ListType.nil MicroExpr) -> @Eq MicroExpr B2 (MicroExpr.bvar Nat.zero) -> Empty) (_hG : @Eq (ListType MicroExpr) G2 (@ListType.nil MicroExpr)) (he : @Eq MicroExpr (MicroExpr.pi A2 B2) (MicroExpr.bvar Nat.zero)) => @Eq.substType MicroExpr mv_pi_head_type (MicroExpr.pi A2 B2) (MicroExpr.bvar Nat.zero) he Nat.zero) (@ListType.nil MicroExpr) (MicroCert.bvar Nat.zero cty) (MicroExpr.bvar Nat.zero) T d (@Eq.refl (ListType MicroExpr) (@ListType.nil MicroExpr)) (@Eq.refl MicroExpr (MicroExpr.bvar Nat.zero))";

impl Specification {
    /// Register Brick 1 of the faithful micro-checker verification relation:
    /// the fresh-name `MicroVerifies` (sort, bvar AND pi arms — the "sort +
    /// bvar ONLY" this line carried was falsified by the `pi` constructor in
    /// this file's own inductive, corrected 2026-09-20), its substrate
    /// defs, the ctx_lookup/translation commutation, the per-arm kernel
    /// agreement theorems, the ground witnesses, and the empty-context bvar
    /// rejection.
    ///
    /// MUST be registered AFTER `add_micro_checker` (`MicroExpr` / `MicroCert`
    /// / `micro_lift` / `micro_def_eq` / `micro_level_eqb` /
    /// `micro_def_eq_refl` / `micro_level_eqb_refl`), `add_micro_soundness`
    /// (`kernel_to_micro` / `kernel_to_micro_lift_commute`),
    /// `add_dependent_sn_richmodel` (`ctx_lookup`), `add_iota_subst`
    /// (`opt_is_none` via `option_none_ne_some_type`), `add_par_reduces_c`
    /// (`option_none_ne_some_type`), `add_rec_env` (`OptionType`) and
    /// `add_expr_model` (`KExpr` / `ListType` / `lift_at`). The micro band is
    /// ImplementationSoundness-bundle-only while `ctx_lookup` is
    /// Substitution-bundle-only, so this stage is Full-bundle-only.
    ///
    /// FRESH NAMES ONLY (micro_soundness.rs:33-38): no existing producer is
    /// touched or re-pointed; `micro_has_type` and its corollaries stay
    /// exactly as they are.
    ///
    /// # Errors
    /// Returns `SpecError` if any declaration fails to elaborate or
    /// kernel-check.
    pub(super) fn add_micro_verifies_r0(&mut self) -> Result<(), SpecError> {
        // --- Group A: substrate defs ---
        self.add_recursive_def(
            SRC_MV_CTX_LOOKUP,
            "Micro-side context lookup (fresh name, byte-mirror of the kernel-side \
             ctx_lookup at MicroExpr): head of the cons-list = innermost binder = de \
             Bruijn 0. mv_ctx_lookup G i = some A is exactly checker.rs:367-372's \
             idx < depth bound plus the context[depth-1-idx] access; out of range is \
             none. Substrate for the MicroVerifies bvar arm (Brick 1 of the faithful \
             micro spec).",
        )?;
        self.add_recursive_def(
            SRC_MV_KCTX_TO_MICRO,
            "Pointwise kernel_to_micro over a kernel context (ListType KExpr -> \
             ListType MicroExpr). The context half of the micro-agreement statements. \
             Part of Brick 1 of the faithful micro spec.",
        )?;
        self.add_recursive_def(
            SRC_MV_OPT_MAP_MICRO,
            "kernel_to_micro mapped through OptionType (none -> none, some a -> some \
             (kernel_to_micro a)). Lets the lookup commutation be stated as one \
             equation. Part of Brick 1 of the faithful micro spec.",
        )?;
        self.add_recursive_def(
            SRC_MV_SORT_HEAD_TYPE,
            "Head discriminator: sort heads -> Nat (inhabited), every other MicroExpr \
             head -> Empty. MicroExpr analogue of opt_is_none; feeds the sort-arm case \
             of the mv_bvar_nil_reject inversion. Part of Brick 1 of the faithful \
             micro spec.",
        )?;
        self.add_recursive_def(
            SRC_MV_PI_HEAD_TYPE,
            "Head discriminator for the Pi arm: pi heads -> Nat (inhabited), every other \
             MicroExpr head -> Empty. mv_sort_head_type cannot serve, sending BOTH pi and bvar \
             to Empty; adding the Pi arm adds a third minor to MicroVerifies.rec, and that minor \
             needs a discriminator separating pi from bvar. Brick 2 of the faithful micro spec.",
        )?;

        // --- Group B: the relation ---
        self.add_inductive(
            SRC_MICRO_VERIFIES,
            "FRESH-NAME faithful micro-checker verification relation (Brick 1): \
             MicroVerifies G c e T models 'verify_impl(cert c, expr e) = Ok(T) under \
             context G' (micro/checker.rs). HONESTLY PARTIAL: exactly THREE arms in this \
             brick — sort (checker.rs:319-327: cert level structurally equals the expr \
             level via micro_level_eqb, the reflected mirror of the Rust structural \
             level_eq; concludes sort (succ cert-level)) and bvar (checker.rs:363-381: \
             one index for cert and expr, mv_ctx_lookup success = the in-bounds \
             context[depth-1-idx] access, cert type micro_def_eq-equal to \
             micro_lift A 0 (succ i), concludes the cert-carried type). Pi/lam/app/let \
             arms are LATER bricks; const/opaque/lit/proj are out-of-fragment. The \
             def-eq side condition is the REFLECTED micro_def_eq (beta+zeta size-fueled \
             whnf then LEVEL-EXACT structural compare) — NARROWER than the Rust \
             def_eq_impl (env-aware beta+zeta+delta+native-iota, universe-blind), so \
             the bvar arm is scoped to that fragment. The bvar arm's binder order \
             (index first, context fourth) is a deliberate recursor-shape pin: a \
             uniform leading G across all arms would be promoted to an implicit \
             recursor parameter, breaking explicit-motive inversion and the later \
             extended-context bricks. NOT the degenerate micro_has_type (which stays \
             untouched, per the Brick-6 fresh-names constraint); no claim about the \
             Rust checker itself.",
        )?;

        // --- Group C: commutation + per-arm agreement ---
        self.add_definition(SpecDefinition {
            name: "mv_ctx_lookup_commute".to_string(),
            type_src: TY_MV_CTX_LOOKUP_COMMUTE.to_string(),
            value_src: Some(VAL_MV_CTX_LOOKUP_COMMUTE.to_string()),
            is_axiom: false,
            description: "Context lookup commutes with the kernel->micro translation: \
                 mv_ctx_lookup (mv_kctx_to_micro G) i = mv_opt_map_micro (ctx_lookup G i). \
                 DerivedProved by ListType.rec with an index-universalized motive (nil: both \
                 sides reduce to none; cons at 0: both reduce to some (kernel_to_micro a); \
                 cons at succ n: definitionally the rest/n instance, closed by the outer IH). \
                 The one commutation lemma the bvar agreement needs, minted here per the \
                 plan. Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "mv_ctx_lookup".to_string(),
                "mv_kctx_to_micro".to_string(),
                "mv_opt_map_micro".to_string(),
                "ctx_lookup".to_string(),
                "kernel_to_micro".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        self.add_definition(SpecDefinition {
            name: "micro_kernel_sort_agree".to_string(),
            type_src: TY_MICRO_KERNEL_SORT_AGREE.to_string(),
            value_src: Some(VAL_MICRO_KERNEL_SORT_AGREE.to_string()),
            is_axiom: false,
            description: "Sort-arm agreement: for every kernel Level l and translated \
                 context, the MicroVerifies sort derivation exists at kernel_to_micro \
                 (KExpr.sort l) and concludes kernel_to_micro (KExpr.sort (Level.succ l)) \
                 — the translation of the kernel sort-typing conclusion. DerivedProved: \
                 MicroVerifies.sort at level_to_microlevel l, side condition closed by \
                 micro_level_eqb_refl; both kernel_to_micro spines reduce definitionally. \
                 FRAGMENT SCOPE: level_to_microlevel erases Level.param to zero, so the \
                 statement is exact on param-free levels and level-erased on parameters. \
                 Per-arm agreement only; no claim about the Rust checker. Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "MicroVerifies".to_string(),
                "MicroVerifies.sort".to_string(),
                "mv_kctx_to_micro".to_string(),
                "level_to_microlevel".to_string(),
                "kernel_to_micro".to_string(),
                "micro_level_eqb_refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        self.add_definition(SpecDefinition {
            name: "micro_kernel_bvar_agree".to_string(),
            type_src: TY_MICRO_KERNEL_BVAR_AGREE.to_string(),
            value_src: Some(VAL_MICRO_KERNEL_BVAR_AGREE.to_string()),
            is_axiom: false,
            description: "THE BRICK-1 AGREEMENT THEOREM (bvar arm): if ctx_lookup G i = \
                 some A on the kernel side, the MicroVerifies bvar derivation exists at the \
                 translated context mv_kctx_to_micro G with conclusion kernel_to_micro \
                 (lift_at A 0 (succ i)) — literally kernel_to_micro of the type \
                 KernelInfers.bvar / TypingCtx.var conclude. DerivedProved: \
                 MicroVerifies.bvar with the lookup premise closed by mv_ctx_lookup_commute \
                 + Eq.cong over the hypothesis, and the def-eq premise closed by the \
                 already-proved kernel_to_micro_lift_commute transported through \
                 micro_def_eq (first argument) into micro_def_eq_refl. Per-arm, \
                 fragment-scoped (reflected beta+zeta level-exact micro_def_eq); nothing \
                 claims the Rust checker itself. Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "MicroVerifies".to_string(),
                "MicroVerifies.bvar".to_string(),
                "mv_ctx_lookup_commute".to_string(),
                "ctx_lookup".to_string(),
                "kernel_to_micro".to_string(),
                "kernel_to_micro_lift_commute".to_string(),
                "micro_def_eq_refl".to_string(),
                "micro_lift".to_string(),
                "lift_at".to_string(),
                "Eq.trans".to_string(),
                "Eq.cong".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        self.add_definition(SpecDefinition {
            name: "micro_kernel_pi_agree".to_string(),
            type_src: TY_MICRO_KERNEL_PI_AGREE.to_string(),
            value_src: Some(VAL_MICRO_KERNEL_PI_AGREE.to_string()),
            is_axiom: false,
            description:
                "THE BRICK-2 AGREEMENT THEOREM (pi arm): given kernel-side sub-derivations \
                 for the domain and, at the EXTENDED context, the codomain, the MicroVerifies pi \
                 derivation exists at the translated context with conclusion kernel_to_micro \
                 (KExpr.sort (Level.imax u v)) — literally kernel_to_micro of the type \
                 KernelInfers.pi concludes. Three iota steps carry it, all on genuine constructor \
                 applications so they fire with A, B, G, u, v still variables. \
                 \
                 FAITHFULNESS CAVEAT, AND IT IS NEW AT THIS ARM: the deployed Pi rule's two level \
                 checks (checker.rs:481, :499) are guarded by universe_blind, which \
                 MicroChecker::with_env sets TRUE. The level premises here therefore model the \
                 MicroChecker::new checker ONLY, and OVER-approximate the env-aware one, which \
                 accepts any levels there. The Sort rule's own level check is NOT guarded and BVar \
                 has none, so the first two arms were faithful in both modes by luck. The band's \
                 standing 'honest under-approximation, never an over-claim' framing does not \
                 inherit past bvar, and this is where it stops. Zero axiom_deps."
                    .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "MicroVerifies".to_string(),
                "MicroVerifies.pi".to_string(),
                "kernel_to_micro".to_string(),
                "level_to_microlevel".to_string(),
                "micro_level_eqb_refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // --- Group D: witnesses ---
        self.add_definition(SpecDefinition {
            name: "mv_sort_ground_witness".to_string(),
            type_src: TY_MV_SORT_GROUND_WITNESS.to_string(),
            value_src: Some(VAL_MV_SORT_GROUND_WITNESS.to_string()),
            is_axiom: false,
            description: "Ground positive witness (sort arm): nil |- cert (sort 0) checks \
                 sort 0 : sort 1 THROUGH the relation. The side condition micro_level_eqb \
                 0 0 computes to true (Eq.refl), so this kernel-checks only because the \
                 arm's premise genuinely computes. Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "MicroVerifies".to_string(),
                "MicroVerifies.sort".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        self.add_definition(SpecDefinition {
            name: "mv_bvar_ground_witness".to_string(),
            type_src: TY_MV_BVAR_GROUND_WITNESS.to_string(),
            value_src: Some(VAL_MV_BVAR_GROUND_WITNESS.to_string()),
            is_axiom: false,
            description: "Ground positive witness (bvar arm): [sort 0] |- cert (bvar 0 : \
                 sort 0) checks bvar 0 : sort 0 THROUGH the relation. Both premises \
                 compute: mv_ctx_lookup fires (some (sort 0)) and micro_def_eq (sort 0) \
                 (micro_lift (sort 0) 0 1) reduces to true. Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "MicroVerifies".to_string(),
                "MicroVerifies.bvar".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        self.add_definition(SpecDefinition {
            name: "mv_bvar_lift_fires_witness".to_string(),
            type_src: TY_MV_BVAR_LIFT_FIRES_WITNESS.to_string(),
            value_src: Some(VAL_MV_BVAR_LIFT_FIRES_WITNESS.to_string()),
            is_axiom: false,
            description: "Lift-arithmetic pin (bvar arm): in the depth-2 context \
                 [sort 0, bvar 0], the bvar-1 derivation carries cert type bvar 2 — the \
                 entry bvar 0 lifted by succ i = 2 (checker.rs:373's depth - ctx_pos). \
                 Kernel-checks only because micro_lift genuinely fires (0 -> 2); an arm \
                 with the wrong lift amount (e.g. i instead of succ i) would make this \
                 Eq.refl fail. Like the Rust arm, context well-formedness is NOT checked \
                 — the context here is a raw syntactic list. Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "MicroVerifies".to_string(),
                "MicroVerifies.bvar".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        self.add_definition(SpecDefinition {
            name: "mv_pi_ground_witness".to_string(),
            type_src: TY_MV_PI_GROUND_WITNESS.to_string(),
            value_src: Some(VAL_MV_PI_GROUND_WITNESS.to_string()),
            is_axiom: false,
            description:
                "GROUND POSITIVE WITNESS for the pi arm: (Sort 0) -> (Sort 0) verifies at \
                 the empty context against a concrete MicroCert.pi, concluding Sort (imax 1 1). \
                 Both whnf premises are Eq.refl by computation — micro_size of a sort is one, \
                 micro_whnf_iter at one is micro_whnf, and micro_whnf leaves a sort alone. \
                 It shows the arm is INHABITED, which a conditional rule cannot show about \
                 itself. Zero axiom_deps."
                    .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "MicroVerifies.pi".to_string(),
                "MicroVerifies.sort".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        self.add_definition(SpecDefinition {
            name: "mv_pi_push_fires_witness".to_string(),
            type_src: TY_MV_PI_PUSH_FIRES_WITNESS.to_string(),
            value_src: Some(VAL_MV_PI_PUSH_FIRES_WITNESS.to_string()),
            is_axiom: false,
            description: "THE WITNESS THAT PINS THE CONTEXT PUSH: (X : Sort 0) -> X, at the EMPTY \
                 context. mv_pi_ground_witness never reads the pushed binder, so it says nothing \
                 about checker.rs:488's self.context.push(arg_ty). This one's body derivation IS \
                 mv_bvar_ground_witness, and a bvar derivation at nil is IMPOSSIBLE — that is \
                 exactly mv_bvar_nil_reject — so it kernel-checks only if ListType.cons MicroExpr \
                 A G genuinely models the push, with the head as de Bruijn zero. \
                 micro_lift of a sort is the sort, so the bvar arm's def-eq premise is Eq.refl. \
                 Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "MicroVerifies.pi".to_string(),
                "MicroVerifies.sort".to_string(),
                "MicroVerifies.bvar".to_string(),
                "mv_ctx_lookup".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        self.add_definition(SpecDefinition {
            name: "mv_bvar_nil_reject".to_string(),
            type_src: TY_MV_BVAR_NIL_REJECT.to_string(),
            value_src: Some(VAL_MV_BVAR_NIL_REJECT.to_string()),
            is_axiom: false,
            description: "REJECTION witness: NO MicroVerifies derivation types bvar 0 in \
                 the empty context, for ANY cert-carried type and ANY claimed conclusion \
                 — mirroring checker.rs:368-370's idx >= depth refusal. DerivedProved by \
                 MicroVerifies.rec inversion with an equality-generalized motive: the sort \
                 arm dies on sort = bvar (mv_sort_head_type transported along the false \
                 equation), the bvar arm dies on its own lookup premise transported to the \
                 nil context (none = some, option_none_ne_some_type). This is the \
                 discriminating half that the degenerate micro_has_type cannot state: the \
                 fresh family genuinely REFUSES. Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "MicroVerifies".to_string(),
                "MicroVerifies.rec".to_string(),
                "mv_ctx_lookup".to_string(),
                "mv_sort_head_type".to_string(),
                "option_none_ne_some_type".to_string(),
                "Eq.substType".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_utils::parse_check;

    /// Every plain-def source in registration order.
    const DEF_SOURCES: [&str; 5] = [
        SRC_MV_CTX_LOOKUP,
        SRC_MV_KCTX_TO_MICRO,
        SRC_MV_OPT_MAP_MICRO,
        SRC_MV_SORT_HEAD_TYPE,
        SRC_MV_PI_HEAD_TYPE,
    ];

    /// Every (name, type, value) triple registered via `add_definition`, in
    /// registration order.
    const THEOREM_SOURCES: [(&str, &str, &str); 10] = [
        (
            "mv_ctx_lookup_commute",
            TY_MV_CTX_LOOKUP_COMMUTE,
            VAL_MV_CTX_LOOKUP_COMMUTE,
        ),
        (
            "micro_kernel_sort_agree",
            TY_MICRO_KERNEL_SORT_AGREE,
            VAL_MICRO_KERNEL_SORT_AGREE,
        ),
        (
            "micro_kernel_bvar_agree",
            TY_MICRO_KERNEL_BVAR_AGREE,
            VAL_MICRO_KERNEL_BVAR_AGREE,
        ),
        (
            "mv_sort_ground_witness",
            TY_MV_SORT_GROUND_WITNESS,
            VAL_MV_SORT_GROUND_WITNESS,
        ),
        (
            "mv_bvar_ground_witness",
            TY_MV_BVAR_GROUND_WITNESS,
            VAL_MV_BVAR_GROUND_WITNESS,
        ),
        (
            "mv_bvar_lift_fires_witness",
            TY_MV_BVAR_LIFT_FIRES_WITNESS,
            VAL_MV_BVAR_LIFT_FIRES_WITNESS,
        ),
        (
            "mv_bvar_nil_reject",
            TY_MV_BVAR_NIL_REJECT,
            VAL_MV_BVAR_NIL_REJECT,
        ),
        (
            "micro_kernel_pi_agree",
            TY_MICRO_KERNEL_PI_AGREE,
            VAL_MICRO_KERNEL_PI_AGREE,
        ),
        (
            "mv_pi_ground_witness",
            TY_MV_PI_GROUND_WITNESS,
            VAL_MV_PI_GROUND_WITNESS,
        ),
        (
            "mv_pi_push_fires_witness",
            TY_MV_PI_PUSH_FIRES_WITNESS,
            VAL_MV_PI_PUSH_FIRES_WITNESS,
        ),
    ];

    /// Parse-check every generated source — the fast guard for the commonest
    /// failure class (syntax-level assembly mistakes invisible to cargo check).
    #[test]
    fn test_micro_verifies_r0_sources_parse() {
        parse_check(SRC_MICRO_VERIFIES).unwrap_or_else(|e| {
            panic!("MicroVerifies inductive should parse: {e}\n{SRC_MICRO_VERIFIES}")
        });
        for src in DEF_SOURCES {
            parse_check(src).unwrap_or_else(|e| panic!("def source should parse: {e}\n{src}"));
        }
        for (name, ty, val) in THEOREM_SOURCES {
            let assembled = format!("def {name} : {ty} := {val}");
            parse_check(&assembled)
                .unwrap_or_else(|e| panic!("{name} should parse as a def: {e}\n{assembled}"));
        }
    }

    /// Paren balance on every source (a cheap structural guard for the long
    /// single-line proof terms).
    #[test]
    fn test_micro_verifies_r0_sources_paren_balanced() {
        let mut all: Vec<String> = DEF_SOURCES.iter().map(|s| (*s).to_string()).collect();
        all.push(SRC_MICRO_VERIFIES.to_string());
        for (_, ty, val) in THEOREM_SOURCES {
            all.push(ty.to_string());
            all.push(val.to_string());
        }
        for src in &all {
            let mut depth: i64 = 0;
            for ch in src.chars() {
                match ch {
                    '(' => depth += 1,
                    ')' => depth -= 1,
                    _ => {}
                }
                assert!(depth >= 0, "close paren before its open in: {src}");
            }
            assert_eq!(depth, 0, "unbalanced parens in: {src}");
        }
    }

    /// Faithfulness-shape guard: the load-bearing spellings that make the two
    /// arms mirror checker.rs. A drive-by edit that changed the lift amount,
    /// the lookup, the level equality, or grew the relation a third arm
    /// without updating the honesty story should fail HERE, in milliseconds.
    #[test]
    fn test_micro_verifies_r0_arm_shapes_faithful() {
        // Exactly THREE arms in this brick — sort, bvar, pi. The relation is
        // still honestly partial: lam/app/let are later bricks, and
        // const/opaque/lit/proj are out of fragment.
        assert_eq!(
            SRC_MICRO_VERIFIES.matches("\n| ").count(),
            3,
            "MicroVerifies must carry exactly three arms here — sort, bvar and pi. A fourth \
             without updating this module's doc, its census and certificate item 7 would make \
             the band claim more coverage than it measures."
        );

        // Sort arm: reflected structural level equality, cert-level successor
        // conclusion (checker.rs:319-327).
        assert!(
            SRC_MICRO_VERIFIES.contains("micro_level_eqb cl l"),
            "sort arm must use the reflected structural level equality"
        );
        assert!(
            SRC_MICRO_VERIFIES.contains("MicroExpr.sort (MicroLevel.succ cl)"),
            "sort arm must conclude succ of the CERT level (checker.rs:326)"
        );
        // Bvar arm: the lookup and the exact lift spelling
        // (checker.rs:371-373: context[depth-1-idx] lifted by depth-ctx_pos =
        // idx+1 at cutoff 0).
        assert!(
            SRC_MICRO_VERIFIES.contains("mv_ctx_lookup G i"),
            "bvar arm must consult the micro-side context lookup"
        );
        // Recursor-shape pin: the bvar arm must NOT lead with G. A uniform
        // leading (G : ListType MicroExpr) across all arms gets promoted to an
        // IMPLICIT recursor parameter (measured), which breaks explicit-motive
        // inversion (mv_bvar_nil_reject) and the later extended-context arms.
        assert!(
            SRC_MICRO_VERIFIES.contains("| bvar : forall (i : Nat)"),
            "bvar arm must lead with the index so G stays a recursor INDEX"
        );
        assert!(
            SRC_MICRO_VERIFIES.contains("micro_lift A Nat.zero (Nat.succ i)"),
            "bvar arm must lift the context entry by succ i at cutoff 0"
        );
        assert!(
            SRC_MICRO_VERIFIES.contains("micro_def_eq cty"),
            "bvar arm's side condition must be the reflected micro_def_eq"
        );
        // The agreement theorem concludes kernel_to_micro of EXACTLY the
        // KernelInfers.bvar / TypingCtx.var type spelling.
        assert!(
            TY_MICRO_KERNEL_BVAR_AGREE.contains("lift_at A Nat.zero (Nat.succ i)"),
            "bvar agreement must target the KernelInfers.bvar lift spelling"
        );
        assert!(
            TY_MICRO_KERNEL_BVAR_AGREE.contains("ctx_lookup G i"),
            "bvar agreement must hypothesize the kernel-side ctx_lookup"
        );
    }

    /// Registration + kernel re-verification against the FULL bundle: the
    /// stage registers every constant, and the relation, commutation,
    /// agreements, witnesses and rejection re-typecheck in the live kernel
    /// environment.
    ///
    /// FULL bundle (not a subset): the micro band (`add_micro_checker` /
    /// `add_micro_soundness`) is ImplementationSoundness-only while
    /// `ctx_lookup` (`add_dependent_sn_richmodel`) is Substitution-only, so
    /// the only bundle containing this stage's whole dependency closure is
    /// Full — same situation as `add_closedness_bundle`.
    #[test]
    fn test_micro_verifies_r0_registered_and_reverifies() {
        let spec = crate::test_utils::build_spec_with_stack();
        for name in [
            "mv_ctx_lookup",
            "mv_kctx_to_micro",
            "mv_opt_map_micro",
            "mv_sort_head_type",
            "mv_pi_head_type",
            "MicroVerifies",
            "MicroVerifies.sort",
            "MicroVerifies.bvar",
            "MicroVerifies.pi",
            "MicroVerifies.rec",
            "mv_ctx_lookup_commute",
            "micro_kernel_sort_agree",
            "micro_kernel_bvar_agree",
            "mv_sort_ground_witness",
            "mv_bvar_ground_witness",
            "mv_bvar_lift_fires_witness",
            "mv_bvar_nil_reject",
            "micro_kernel_pi_agree",
            "mv_pi_ground_witness",
            "mv_pi_push_fires_witness",
        ] {
            assert!(
                spec.definitions().contains_key(name),
                "{name} should be registered by the micro_verifies_r0 stage"
            );
        }
        // The relation is a genuine kernel inductive, not an axiom.
        assert!(
            spec.env()
                .get_const(&clean_kernel::Name::from_string("MicroVerifies"))
                .is_some(),
            "MicroVerifies should be in the kernel environment"
        );
        // Zero new axioms: every theorem is DerivedProved with an empty
        // (foundational) axiom closure.
        for (name, _, _) in THEOREM_SOURCES {
            let def = spec
                .definitions()
                .get(name)
                .unwrap_or_else(|| panic!("{name} should be registered"));
            assert!(!def.is_axiom, "{name} must not be an axiom");
            assert_eq!(
                def.proof_status,
                ProofStatus::DerivedProved,
                "{name} must be DerivedProved"
            );
            assert!(
                def.axiom_deps.is_empty(),
                "{name} must have an empty axiom closure, got {:?}",
                def.axiom_deps
            );
        }
        for (name, _, _) in THEOREM_SOURCES {
            spec.verify_definition(name).unwrap_or_else(|e| {
                panic!("{name} should re-typecheck in the spec environment: {e:?}")
            });
        }
    }
}
