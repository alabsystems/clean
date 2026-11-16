// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The Hurkens/Girard paradox route is BLOCKED for the reflected stratified
//! judgment `TypingCtx` — kernel-checked by clean-kernel itself.
//!
//! Port of the corpus rung
//! `proofs/aristotle-whnf-model-guides/stratified-whnf-conversion/solution/Stratified/Blocking.lean`
//! (Lean 4, Nat-level calculus) to the reflected spec judgment `TypingCtx`
//! (`dependent_sn_richmodel.rs`): Hurkens' powerful universe
//! `U0 = Pi X : sort 0. ((PPX -> X) -> PPX)` with `PX = X -> sort 0` EXISTS one
//! level up (`typingctx_U0_formable`, semantic level 1 by the `hk_level_val`
//! pins) and can NEVER be small (`typingctx_U0_not_small`:
//! `TypingCtx tenv G U0 (sort 0) -> Empty`, for EVERY context and const-env).
//!
//! ## Honesty notes (read before quoting)
//!
//! - **`TypingCtx` is CONV-FREE** (rules var/sort/pi/lam/app/const/let_ only;
//!   no conversion rule). That makes the block STRONGER-for-cheaper than the
//!   corpus theorem: there is no conv rescue to refute, so rule inversion is
//!   purely structural.
//! - **Levels are LITERAL constructor terms here.** The spec's `Level.imax` is
//!   a plain constructor, not the production smart-constructor, and `TypingCtx`
//!   has no level normalization. So the pi rule's conclusion carries a literal
//!   `Level.imax n m`, which is NEVER the literal `Level.zero` — the
//!   impredicative clause `imax n 0 = 0` exists only in the SEMANTICS. Two
//!   consequences, both stated honestly:
//!   1. The block's engine (`typingctx_pi_small_inv`) is COARSER than the
//!      corpus engine `powr2_not_small`: in this judgment NO pi whatsoever
//!      types at the literal `sort Level.zero`, whether or not the codomain
//!      component is a `succ`. The `Level.imax _ _ != Level.zero` constructor
//!      disequality (`level_imax_ne_zero`) closes every instance.
//!   2. `typingctx_U0_formable`'s stated sort is the LITERAL Level tree the pi
//!      rule produces (`U0_level`, a nested imax), NOT `succ zero`. The spec
//!      has no level-normalization equalities to collapse it, so we do not
//!      force one; instead the denotational pins (`hk_level_val`, parameters
//!      under an arbitrary assignment `rho`) verify BY `Eq.refl` computation
//!      that `U0_level` evaluates to 1 (`U0_level_val_one`) — the corpus's
//!      `.sort 1` — and that the inner arrow's level `U0_arrow_level`
//!      evaluates to 0 (`U0_arrow_level_val_zero`) — the one place the corpus
//!      fires `imax 1 0 = 0`.
//! - **`TypingCtxConv` is NOT covered.** The conversion-closed judgment
//!   (`dependent_sn_richmodel.rs`) would need the DefEq-level sort
//!   no-confusion story — `def_eq_joinable` + `par_cd_sort_injectivity` (the
//!   confluence lane) under a `RedEnvFaithful` discharge, plus a pi-vs-sort
//!   DefEq refutation for the lam arm — machinery that registers at LATER
//!   stages than this one. The Eq-level sort injectivity used here is the
//!   already-landed `sort_universe_consistency` (typing_universe_levels.rs).
//!
//! ## Census
//!
//! ZERO new axioms: every constant is value-bearing (plain defs via
//! `add_recursive_def`, theorems/witnesses via `add_definition` with kernel
//! `add_decl` checking). Census-neutral.

use crate::spec::error::SpecError;
use crate::spec::Specification;

// ================================================================
// Group A — the Hurkens objects as closed KExpr constructions.
// De Bruijn indices translated faithfully from Blocking.lean:82-92.
// ================================================================

pub(super) const SRC_POWR: &str =
    "def powr (X : KExpr) : KExpr := KExpr.pi X (KExpr.sort Level.zero)";

pub(super) const SRC_POWR2: &str = "def powr2 (X : KExpr) : KExpr := powr (powr X)";

pub(super) const SRC_U0_ARROW: &str = "def U0_arrow : KExpr := KExpr.pi (powr2 (KExpr.bvar Nat.zero)) (KExpr.bvar (Nat.succ Nat.zero))";

pub(super) const SRC_U0_BODY: &str =
    "def U0_body : KExpr := KExpr.pi U0_arrow (powr2 (KExpr.bvar (Nat.succ Nat.zero)))";

pub(super) const SRC_U0: &str = "def U0 : KExpr := KExpr.pi (KExpr.sort Level.zero) U0_body";

// ================================================================
// Group B — the literal Level terms the pi rule produces.
// ================================================================

pub(super) const SRC_POWR_LEVEL: &str =
    "def powr_level : Level := Level.imax Level.zero (Level.succ Level.zero)";

pub(super) const SRC_POWR2_LEVEL: &str =
    "def powr2_level : Level := Level.imax powr_level (Level.succ Level.zero)";

pub(super) const SRC_U0_ARROW_LEVEL: &str =
    "def U0_arrow_level : Level := Level.imax powr2_level Level.zero";

pub(super) const SRC_U0_LEVEL: &str = "def U0_level : Level := Level.imax (Level.succ Level.zero) (Level.imax U0_arrow_level powr2_level)";

// ================================================================
// Group C — denotational level semantics + the Eq.refl value pins.
// ================================================================

pub(super) const SRC_HK_MAX_NAT: &str =
    "def hk_max_nat (n : Nat) (m : Nat) : Nat := Nat.add n (Nat.sub m n)";

pub(super) const SRC_HK_LEVEL_VAL: &str = "def hk_level_val (rho : Name -> Nat) (l : Level) : Nat := @Level.rec (fun (_ : Level) => Nat) Nat.zero (fun (_ : Level) (ih : Nat) => Nat.succ ih) (fun (_ : Level) (_ : Level) (iha : Nat) (ihb : Nat) => hk_max_nat iha ihb) (fun (_ : Level) (_ : Level) (iha : Nat) (ihb : Nat) => imax_nat iha ihb) (fun (nm : Name) => rho nm) l";

pub(super) const TY_POWR_LEVEL_VAL_ONE: &str =
    "forall (rho : Name -> Nat), @Eq Nat (hk_level_val rho powr_level) (Nat.succ Nat.zero)";
pub(super) const VAL_POWR_LEVEL_VAL_ONE: &str =
    "fun (rho : Name -> Nat) => @Eq.refl Nat (Nat.succ Nat.zero)";

pub(super) const TY_POWR2_LEVEL_VAL_ONE: &str =
    "forall (rho : Name -> Nat), @Eq Nat (hk_level_val rho powr2_level) (Nat.succ Nat.zero)";
pub(super) const VAL_POWR2_LEVEL_VAL_ONE: &str =
    "fun (rho : Name -> Nat) => @Eq.refl Nat (Nat.succ Nat.zero)";

pub(super) const TY_U0_ARROW_LEVEL_VAL_ZERO: &str =
    "forall (rho : Name -> Nat), @Eq Nat (hk_level_val rho U0_arrow_level) Nat.zero";
pub(super) const VAL_U0_ARROW_LEVEL_VAL_ZERO: &str =
    "fun (rho : Name -> Nat) => @Eq.refl Nat Nat.zero";

pub(super) const TY_U0_LEVEL_VAL_ONE: &str =
    "forall (rho : Name -> Nat), @Eq Nat (hk_level_val rho U0_level) (Nat.succ Nat.zero)";
pub(super) const VAL_U0_LEVEL_VAL_ONE: &str =
    "fun (rho : Name -> Nat) => @Eq.refl Nat (Nat.succ Nat.zero)";

// ================================================================
// Group D — Level and KExpr no-confusion (transport probes).
// ================================================================

pub(super) const SRC_HK_LEVEL_ZERO_FLAG: &str = "def hk_level_zero_flag (l : Level) : Type := @Level.rec (fun (_ : Level) => Type) Empty (fun (_ : Level) (_ : Type) => ConstFreeUnit) (fun (_ : Level) (_ : Level) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_ : Level) (_ : Level) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_ : Name) => ConstFreeUnit) l";

pub(super) const TY_LEVEL_SUCC_NE_ZERO: &str =
    "forall (a : Level), @Eq Level (Level.succ a) Level.zero -> Empty";
pub(super) const VAL_LEVEL_SUCC_NE_ZERO: &str = "fun (a : Level) (h : @Eq Level (Level.succ a) Level.zero) => @Eq.substType Level (fun (z : Level) => hk_level_zero_flag z) (Level.succ a) Level.zero h ConstFreeUnit.triv";

pub(super) const TY_LEVEL_IMAX_NE_ZERO: &str =
    "forall (a : Level) (b : Level), @Eq Level (Level.imax a b) Level.zero -> Empty";
pub(super) const VAL_LEVEL_IMAX_NE_ZERO: &str = "fun (a : Level) (b : Level) (h : @Eq Level (Level.imax a b) Level.zero) => @Eq.substType Level (fun (z : Level) => hk_level_zero_flag z) (Level.imax a b) Level.zero h ConstFreeUnit.triv";

pub(super) const SRC_HK_NONPI_FLAG: &str = "def hk_nonpi_flag (e : KExpr) : Type := @KExpr.rec (fun (_ : KExpr) => Type) (fun (_ : Level) => ConstFreeUnit) (fun (_ : Nat) => ConstFreeUnit) (fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Empty) (fun (_ : Name) (_ : ListType Level) => ConstFreeUnit) (fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_ : Name) (_ : Nat) (_ : KExpr) (_ : Type) => ConstFreeUnit) (fun (_ : Nat) => ConstFreeUnit) e";

/// The premise-satisfiability witness for the probe. `hk_kill_nonpi` ASSUMES
/// `hk_nonpi_flag x` and nothing concluded it: the six inversion arms pass
/// `ConstFreeUnit.triv` inline, where the flag computes, but an inline argument
/// is not a registered conclusion and the gate (rightly) cannot see it. At a
/// sort the flag REDUCES to `ConstFreeUnit`, so the witness is one constructor.
pub(super) const TY_HK_NONPI_FLAG_WITNESS: &str = "hk_nonpi_flag (KExpr.sort Level.zero)";
pub(super) const VAL_HK_NONPI_FLAG_WITNESS: &str = "ConstFreeUnit.triv";

pub(super) const TY_HK_KILL_NONPI: &str = "forall (x : KExpr) (PA : KExpr) (PB : KExpr), @Eq KExpr x (KExpr.pi PA PB) -> hk_nonpi_flag x -> Empty";
pub(super) const VAL_HK_KILL_NONPI: &str = "fun (x : KExpr) (PA : KExpr) (PB : KExpr) (h : @Eq KExpr x (KExpr.pi PA PB)) (w : hk_nonpi_flag x) => @Eq.substType KExpr (fun (z : KExpr) => hk_nonpi_flag z) x (KExpr.pi PA PB) h w";

// ================================================================
// Group E — the positive half: powr / powr2 / U0 typings.
// ================================================================

pub(super) const TY_TYPINGCTX_POWR_TY: &str = "forall (tenv : KDeclEnv) (G : ListType KExpr) (X : KExpr), TypingCtx tenv G X (KExpr.sort Level.zero) -> TypingCtx tenv G (powr X) (KExpr.sort powr_level)";
pub(super) const VAL_TYPINGCTX_POWR_TY: &str = "fun (tenv : KDeclEnv) (G : ListType KExpr) (X : KExpr) (hX : TypingCtx tenv G X (KExpr.sort Level.zero)) => @TypingCtx.pi tenv G X (KExpr.sort Level.zero) Level.zero (Level.succ Level.zero) hX (@TypingCtx.sort tenv (@ListType.cons KExpr X G) Level.zero)";

pub(super) const TY_TYPINGCTX_POWR2_TY: &str = "forall (tenv : KDeclEnv) (G : ListType KExpr) (X : KExpr), TypingCtx tenv G X (KExpr.sort Level.zero) -> TypingCtx tenv G (powr2 X) (KExpr.sort powr2_level)";
pub(super) const VAL_TYPINGCTX_POWR2_TY: &str = "fun (tenv : KDeclEnv) (G : ListType KExpr) (X : KExpr) (hX : TypingCtx tenv G X (KExpr.sort Level.zero)) => @TypingCtx.pi tenv G (powr X) (KExpr.sort Level.zero) powr_level (Level.succ Level.zero) (typingctx_powr_ty tenv G X hX) (@TypingCtx.sort tenv (@ListType.cons KExpr (powr X) G) Level.zero)";

pub(super) const TY_TYPINGCTX_U0_FORMABLE: &str =
    "forall (tenv : KDeclEnv), TypingCtx tenv (@ListType.nil KExpr) U0 (KExpr.sort U0_level)";
pub(super) const VAL_TYPINGCTX_U0_FORMABLE: &str = "fun (tenv : KDeclEnv) => @TypingCtx.pi tenv (@ListType.nil KExpr) (KExpr.sort Level.zero) U0_body (Level.succ Level.zero) (Level.imax U0_arrow_level powr2_level) (@TypingCtx.sort tenv (@ListType.nil KExpr) Level.zero) (@TypingCtx.pi tenv (@ListType.cons KExpr (KExpr.sort Level.zero) (@ListType.nil KExpr)) U0_arrow (powr2 (KExpr.bvar (Nat.succ Nat.zero))) U0_arrow_level powr2_level (@TypingCtx.pi tenv (@ListType.cons KExpr (KExpr.sort Level.zero) (@ListType.nil KExpr)) (powr2 (KExpr.bvar Nat.zero)) (KExpr.bvar (Nat.succ Nat.zero)) powr2_level Level.zero (typingctx_powr2_ty tenv (@ListType.cons KExpr (KExpr.sort Level.zero) (@ListType.nil KExpr)) (KExpr.bvar Nat.zero) (@TypingCtx.var tenv (@ListType.cons KExpr (KExpr.sort Level.zero) (@ListType.nil KExpr)) Nat.zero (KExpr.sort Level.zero) (@Eq.refl (OptionType KExpr) (@OptionType.some KExpr (KExpr.sort Level.zero))))) (@TypingCtx.var tenv (@ListType.cons KExpr (powr2 (KExpr.bvar Nat.zero)) (@ListType.cons KExpr (KExpr.sort Level.zero) (@ListType.nil KExpr))) (Nat.succ Nat.zero) (KExpr.sort Level.zero) (@Eq.refl (OptionType KExpr) (@OptionType.some KExpr (KExpr.sort Level.zero))))) (typingctx_powr2_ty tenv (@ListType.cons KExpr U0_arrow (@ListType.cons KExpr (KExpr.sort Level.zero) (@ListType.nil KExpr))) (KExpr.bvar (Nat.succ Nat.zero)) (@TypingCtx.var tenv (@ListType.cons KExpr U0_arrow (@ListType.cons KExpr (KExpr.sort Level.zero) (@ListType.nil KExpr))) (Nat.succ Nat.zero) (KExpr.sort Level.zero) (@Eq.refl (OptionType KExpr) (@OptionType.some KExpr (KExpr.sort Level.zero))))))";

// ================================================================
// Group F — the block: structural rule inversion.
// ================================================================

/// The seven minor premises of `TypingCtx.rec` for the inversion, in
/// constructor DECLARATION order (var sort pi lam app const let_ —
/// `dependent_sn_richmodel.rs:109-115`). Each binds the constructor fields,
/// then ALL induction hypotheses (motive at the recursive premises), then the
/// motive's own binders `(PA PB he ht)`. Six arms have a non-pi SUBJECT and die
/// on `he` via `hk_kill_nonpi`; the pi arm is the only one whose subject is a
/// pi, and it dies on `ht` — its conclusion sort is the LITERAL
/// `Level.imax n m`, never `Level.zero` (`sort_universe_consistency` +
/// `level_imax_ne_zero`).
pub(super) const SRC_TYPINGCTX_PI_SMALL_INV: &str = concat!(
    "def typingctx_pi_small_inv (tenv : KDeclEnv) (G : ListType KExpr) (e : KExpr) (T : KExpr) (h : TypingCtx tenv G e T) : forall (PA : KExpr) (PB : KExpr), @Eq KExpr e (KExpr.pi PA PB) -> @Eq KExpr T (KExpr.sort Level.zero) -> Empty := ",
    "@TypingCtx.rec tenv ",
    "(fun (G0 : ListType KExpr) (e0 : KExpr) (T0 : KExpr) (_h : TypingCtx tenv G0 e0 T0) => forall (PA : KExpr) (PB : KExpr), @Eq KExpr e0 (KExpr.pi PA PB) -> @Eq KExpr T0 (KExpr.sort Level.zero) -> Empty) ",
    // var
    "(fun (G0 : ListType KExpr) (i : Nat) (A : KExpr) (hget : @Eq (OptionType KExpr) (ctx_lookup G0 i) (@OptionType.some KExpr A)) (PA : KExpr) (PB : KExpr) (he : @Eq KExpr (KExpr.bvar i) (KExpr.pi PA PB)) (ht : @Eq KExpr (lift_at A Nat.zero (Nat.succ i)) (KExpr.sort Level.zero)) => hk_kill_nonpi (KExpr.bvar i) PA PB he ConstFreeUnit.triv) ",
    // sort
    "(fun (G0 : ListType KExpr) (n : Level) (PA : KExpr) (PB : KExpr) (he : @Eq KExpr (KExpr.sort n) (KExpr.pi PA PB)) (ht : @Eq KExpr (KExpr.sort (Level.succ n)) (KExpr.sort Level.zero)) => hk_kill_nonpi (KExpr.sort n) PA PB he ConstFreeUnit.triv) ",
    // pi — THE ARM THAT CARRIES THE MATHEMATICS
    "(fun (G0 : ListType KExpr) (A : KExpr) (B : KExpr) (n : Level) (m : Level) (hA : TypingCtx tenv G0 A (KExpr.sort n)) (hB : TypingCtx tenv (@ListType.cons KExpr A G0) B (KExpr.sort m)) (ihA : forall (PA : KExpr) (PB : KExpr), @Eq KExpr A (KExpr.pi PA PB) -> @Eq KExpr (KExpr.sort n) (KExpr.sort Level.zero) -> Empty) (ihB : forall (PA : KExpr) (PB : KExpr), @Eq KExpr B (KExpr.pi PA PB) -> @Eq KExpr (KExpr.sort m) (KExpr.sort Level.zero) -> Empty) (PA : KExpr) (PB : KExpr) (he : @Eq KExpr (KExpr.pi A B) (KExpr.pi PA PB)) (ht : @Eq KExpr (KExpr.sort (Level.imax n m)) (KExpr.sort Level.zero)) => level_imax_ne_zero n m (sort_universe_consistency (Level.imax n m) Level.zero ht)) ",
    // lam
    "(fun (G0 : ListType KExpr) (A : KExpr) (b : KExpr) (B : KExpr) (u : Level) (hA : TypingCtx tenv G0 A (KExpr.sort u)) (hb : TypingCtx tenv (@ListType.cons KExpr A G0) b B) (ihA : forall (PA : KExpr) (PB : KExpr), @Eq KExpr A (KExpr.pi PA PB) -> @Eq KExpr (KExpr.sort u) (KExpr.sort Level.zero) -> Empty) (ihb : forall (PA : KExpr) (PB : KExpr), @Eq KExpr b (KExpr.pi PA PB) -> @Eq KExpr B (KExpr.sort Level.zero) -> Empty) (PA : KExpr) (PB : KExpr) (he : @Eq KExpr (KExpr.lam A b) (KExpr.pi PA PB)) (ht : @Eq KExpr (KExpr.pi A B) (KExpr.sort Level.zero)) => hk_kill_nonpi (KExpr.lam A b) PA PB he ConstFreeUnit.triv) ",
    // app
    "(fun (G0 : ListType KExpr) (f : KExpr) (a : KExpr) (A : KExpr) (B : KExpr) (hf : TypingCtx tenv G0 f (KExpr.pi A B)) (ha : TypingCtx tenv G0 a A) (ihf : forall (PA : KExpr) (PB : KExpr), @Eq KExpr f (KExpr.pi PA PB) -> @Eq KExpr (KExpr.pi A B) (KExpr.sort Level.zero) -> Empty) (iha : forall (PA : KExpr) (PB : KExpr), @Eq KExpr a (KExpr.pi PA PB) -> @Eq KExpr A (KExpr.sort Level.zero) -> Empty) (PA : KExpr) (PB : KExpr) (he : @Eq KExpr (KExpr.app f a) (KExpr.pi PA PB)) (ht : @Eq KExpr (instantiate B a) (KExpr.sort Level.zero)) => hk_kill_nonpi (KExpr.app f a) PA PB he ConstFreeUnit.triv) ",
    // const
    "(fun (G0 : ListType KExpr) (cn : Name) (us : ListType Level) (A : KExpr) (hget : @Eq (OptionType KExpr) (kdecl_type_at tenv cn us) (@OptionType.some KExpr A)) (PA : KExpr) (PB : KExpr) (he : @Eq KExpr (KExpr.const cn us) (KExpr.pi PA PB)) (ht : @Eq KExpr A (KExpr.sort Level.zero)) => hk_kill_nonpi (KExpr.const cn us) PA PB he ConstFreeUnit.triv) ",
    // let_
    "(fun (G0 : ListType KExpr) (lty : KExpr) (lv : KExpr) (lb : KExpr) (B : KExpr) (u : Level) (hty : TypingCtx tenv G0 lty (KExpr.sort u)) (hv : TypingCtx tenv G0 lv lty) (hb : TypingCtx tenv (@ListType.cons KExpr lty G0) lb B) (ihty : forall (PA : KExpr) (PB : KExpr), @Eq KExpr lty (KExpr.pi PA PB) -> @Eq KExpr (KExpr.sort u) (KExpr.sort Level.zero) -> Empty) (ihv : forall (PA : KExpr) (PB : KExpr), @Eq KExpr lv (KExpr.pi PA PB) -> @Eq KExpr lty (KExpr.sort Level.zero) -> Empty) (ihb : forall (PA : KExpr) (PB : KExpr), @Eq KExpr lb (KExpr.pi PA PB) -> @Eq KExpr B (KExpr.sort Level.zero) -> Empty) (PA : KExpr) (PB : KExpr) (he : @Eq KExpr (KExpr.let_ lty lv lb) (KExpr.pi PA PB)) (ht : @Eq KExpr (instantiate B lv) (KExpr.sort Level.zero)) => hk_kill_nonpi (KExpr.let_ lty lv lb) PA PB he ConstFreeUnit.triv) ",
    "G e T h"
);

pub(super) const TY_TYPINGCTX_PI_NOT_SMALL: &str = "forall (tenv : KDeclEnv) (G : ListType KExpr) (A : KExpr) (B : KExpr), TypingCtx tenv G (KExpr.pi A B) (KExpr.sort Level.zero) -> Empty";
pub(super) const VAL_TYPINGCTX_PI_NOT_SMALL: &str = "fun (tenv : KDeclEnv) (G : ListType KExpr) (A : KExpr) (B : KExpr) (h : TypingCtx tenv G (KExpr.pi A B) (KExpr.sort Level.zero)) => typingctx_pi_small_inv tenv G (KExpr.pi A B) (KExpr.sort Level.zero) h A B (@Eq.refl KExpr (KExpr.pi A B)) (@Eq.refl KExpr (KExpr.sort Level.zero))";

pub(super) const TY_TYPINGCTX_POWR2_NOT_SMALL: &str = "forall (tenv : KDeclEnv) (G : ListType KExpr) (X : KExpr), TypingCtx tenv G (powr2 X) (KExpr.sort Level.zero) -> Empty";
pub(super) const VAL_TYPINGCTX_POWR2_NOT_SMALL: &str = "fun (tenv : KDeclEnv) (G : ListType KExpr) (X : KExpr) (h : TypingCtx tenv G (powr2 X) (KExpr.sort Level.zero)) => typingctx_pi_not_small tenv G (powr X) (KExpr.sort Level.zero) h";

pub(super) const TY_TYPINGCTX_U0_NOT_SMALL: &str = "forall (tenv : KDeclEnv) (G : ListType KExpr), TypingCtx tenv G U0 (KExpr.sort Level.zero) -> Empty";
pub(super) const VAL_TYPINGCTX_U0_NOT_SMALL: &str = "fun (tenv : KDeclEnv) (G : ListType KExpr) (h : TypingCtx tenv G U0 (KExpr.sort Level.zero)) => typingctx_pi_not_small tenv G (KExpr.sort Level.zero) U0_body h";

pub(super) const TY_TYPINGCTX_POWR2_NEVER_SMALL: &str = "forall (tenv : KDeclEnv) (G : ListType KExpr) (X : KExpr) (k : Level), TypingCtx tenv G (powr2 X) (KExpr.sort k) -> @Eq Level k Level.zero -> Empty";
pub(super) const VAL_TYPINGCTX_POWR2_NEVER_SMALL: &str = "fun (tenv : KDeclEnv) (G : ListType KExpr) (X : KExpr) (k : Level) (h : TypingCtx tenv G (powr2 X) (KExpr.sort k)) (hk : @Eq Level k Level.zero) => typingctx_powr2_not_small tenv G X (@Eq.substType Level (fun (z : Level) => TypingCtx tenv G (powr2 X) (KExpr.sort z)) k Level.zero hk h)";

pub(super) const TY_TYPINGCTX_U0_NEVER_SMALL: &str = "forall (tenv : KDeclEnv) (G : ListType KExpr) (k : Level), TypingCtx tenv G U0 (KExpr.sort k) -> @Eq Level k Level.zero -> Empty";
pub(super) const VAL_TYPINGCTX_U0_NEVER_SMALL: &str = "fun (tenv : KDeclEnv) (G : ListType KExpr) (k : Level) (h : TypingCtx tenv G U0 (KExpr.sort k)) (hk : @Eq Level k Level.zero) => typingctx_U0_not_small tenv G (@Eq.substType Level (fun (z : Level) => TypingCtx tenv G U0 (KExpr.sort z)) k Level.zero hk h)";

// ================================================================
// Group G — ground non-vacuity witnesses (empty const-env).
// ================================================================

pub(super) const TY_TYPINGCTX_POWR_WITNESS: &str = "TypingCtx (fun (nm : Name) => @OptionType.none KConstSig) (@ListType.cons KExpr (KExpr.sort Level.zero) (@ListType.nil KExpr)) (powr (KExpr.bvar Nat.zero)) (KExpr.sort powr_level)";
pub(super) const VAL_TYPINGCTX_POWR_WITNESS: &str = "typingctx_powr_ty (fun (nm : Name) => @OptionType.none KConstSig) (@ListType.cons KExpr (KExpr.sort Level.zero) (@ListType.nil KExpr)) (KExpr.bvar Nat.zero) (@TypingCtx.var (fun (nm : Name) => @OptionType.none KConstSig) (@ListType.cons KExpr (KExpr.sort Level.zero) (@ListType.nil KExpr)) Nat.zero (KExpr.sort Level.zero) (@Eq.refl (OptionType KExpr) (@OptionType.some KExpr (KExpr.sort Level.zero))))";

pub(super) const TY_TYPINGCTX_U0_WITNESS: &str = "TypingCtx (fun (nm : Name) => @OptionType.none KConstSig) (@ListType.nil KExpr) U0 (KExpr.sort U0_level)";
pub(super) const VAL_TYPINGCTX_U0_WITNESS: &str =
    "typingctx_U0_formable (fun (nm : Name) => @OptionType.none KConstSig)";

mod block;
mod objects;

#[cfg(test)]
mod tests;

impl Specification {
    /// Register the stratified Hurkens/Girard blocking theorems over the
    /// reflected conv-free `TypingCtx` judgment.
    ///
    /// MUST be registered AFTER `add_dependent_sn_richmodel` (`TypingCtx` /
    /// `ctx_lookup`), `add_expr_model` (`KExpr`/`Level`/`lift_at`/`instantiate`),
    /// `add_typing_universe_levels` (`imax_nat`/`sort_universe_consistency`),
    /// `add_whnf_progress` (`ConstFreeUnit`) and the foundation types
    /// (`Eq`/`Nat`/`Empty`/`OptionType`/`ListType`/`Name`).
    ///
    /// Port of `Stratified/Blocking.lean` (corpus rung
    /// `stratified-whnf-conversion`); see the module docs for the two
    /// literal-Level honesty notes and the `TypingCtxConv` scope note.
    ///
    /// The registrations themselves live in `objects.rs` (groups A-D) and
    /// `block.rs` (groups E-G); this driver fixes their order.
    pub(super) fn add_stratified_hurkens_block(&mut self) -> Result<(), SpecError> {
        self.add_hurkens_objects()?;
        self.add_hurkens_block()?;
        Ok(())
    }
}
