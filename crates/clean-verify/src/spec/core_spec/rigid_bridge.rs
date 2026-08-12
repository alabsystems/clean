// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The rigid-spine bridge, the lam descent, and ten of eleven rows.
//!
//! # The bridge nobody had noticed was missing
//!
//! `hnf3_app_residual_of_rigid` wants `rigid_app_head r0` for the WHOLE term.
//! The case analysis produces a fact about the SPINE HEAD, `kapp_fn r0`. The
//! only inversion in tree, `rigid_app_head_app_inv`, runs the other way — so
//! the residual's five rigid rows did not actually close, and had not since they
//! were written.
//!
//! `rigid_app_head_of_kapp_fn` is that bridge, and it is nine lines: eight arms
//! return the hypothesis unchanged, and the `app` arm is `rigid_app_head.app` on
//! the IH.
//!
//! # Where the lam exclusion really stops
//!
//! *A stuck term's spine head is never a lam* is **FALSE** — a bare lambda is
//! wh3-stuck at every budget and is its own spine head
//! (`wh3_stuck_kapp_fn_not_lam_is_false`).
//!
//! That is not a counterexample to the residual, and the distinction is the
//! point: the residual is only invoked at a term carrying an equation to
//! `KExpr.app`, and a bare lam is not an application. The TRUE statement is that
//! a stuck term whose spine head is a lam *is* that lam — from which the
//! corollary the residual needs follows at an application.
//!
//! # Ten of eleven
//!
//! `hnf3_app_residual_covered` closes sort/pi/lit/proj/bvar via the bridge;
//! app, lam and let_ as impossible; delta-LIVE const as excluded by stuckness;
//! and delta-dead recmeta-free const via the existing supplier. Only the
//! delta-dead RECURSOR-headed class is carried, as `rec_res`.
//!
//! It also *derives* the delta-deadness and const-name facts that
//! `hnf3_app_residual_of_dead_const_head` used to demand from its caller.
//!
//! # Why `rec_res` is not narrowed further
//!
//! The obstruction is not in the open rows — it is in the **dispatch**.
//! Selecting among under-applied / at-boundary / past-the-major needs a Nat
//! trichotomy. Two of those four sub-rows already have suppliers; they simply
//! cannot be selected between here.
//!
//! CORRECTION (`residual_narrowing.rs`): an earlier version of this note said
//! `core_spec` had no trichotomy — "no `le_total`, no `le_dec`, no `le_or_gt`,
//! no `le_antisymm`". Those four NAMES are absent, but the THING was already
//! there: `nat_lt_le_dichotomy`, already used for this exact split in
//! `wh_step_mono_proof.rs`. Only `le_antisymm` was genuinely missing, and
//! `residual_narrowing.rs` now does the selection.
//!
//! `DerivedProved`, empty axiom closures.

use crate::spec::error::SpecError;
use crate::spec::Specification;

impl Specification {
    /// The bridge, the descent, and the ten-row supplier.
    pub(super) fn add_rigid_bridge(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            SRC_RIGID_APP_HEAD_OF_KAPP_FN,
            "rigid_app_head_of_kapp_fn: a rigid SPINE HEAD makes the whole spine rigid. THE MISSING BRIDGE. \\
\\
Without it the residual's five rigid rows do not close, and that had gone unnoticed: the case analysis produces a fact about kapp_fn r0, while hnf3_app_residual_of_rigid demands one about r0, and the only inversion in tree — rigid_app_head_app_inv — runs the other way. \\
\\
Nine-arm KExpr.rec. Eight arms return the hypothesis unchanged because kapp_fn X is definitionally X there; the app arm is rigid_app_head.app on the induction hypothesis, needing no transport because kapp_fn (app f a) unfolds to kapp_fn f definitionally. DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(
            SRC_RIGID_APP_HEAD_OF_KAPP_FN_SORT_WITNESS,
            "rigid_app_head_of_kapp_fn_sort_witness (NON-VACUITY): the bridge applied to the term of wh3_rigid_app_is_stuck. DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(
            SRC_RIGID_APP_HEAD_OF_KAPP_FN_BVAR_WITNESS,
            "rigid_app_head_of_kapp_fn_bvar_witness (NON-VACUITY): the bridge at a bvar-headed spine — and the FIRST USE of rigid_app_head.bvar anywhere. That constructor landed to repair a false premise and had zero consumers until now; this exercises it. DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(
            SRC_WH3_STUCK_LAM,
            "wh3_stuck_lam: a BARE lambda is wh3-stuck, at every budget. One Eq.refl — reduce_once_red_wh3's lam arm is unconditionally wstuck. DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(
            SRC_WH3_STUCK_KAPP_FN_NOT_LAM_IS_FALSE,
            "wh3_stuck_kapp_fn_not_lam_is_false: A REFUTATION. The natural generalisation of wh3_stuck_app_head_not_lam — a stuck term's spine head is never a lam — is FALSE, witnessed by a bare lambda, whose spine head is itself. \\
\\
It is NOT a counterexample to hnf3's residual, and the distinction matters: the residual is only ever invoked at a term carrying an equation to KExpr.app, and a bare lam is not an application. This records exactly where the lam exclusion stops, so the next person does not assume the general form and build on sand. DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(
            SRC_WH3_STUCK_KAPP_FN_LAM_IS_LAM,
            "wh3_stuck_kapp_fn_lam_is_lam: the TRUE repaired statement — a stuck term whose spine head is a lam IS that lam. Eight arms return the hypothesis; the app arm descends through wh3_stuck_app_fn_stuck and dies on wh3_stuck_app_head_not_lam. So the lam exclusion does survive the descent, in the collapses-to-a-bare-lam form. DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(
            SRC_WH3_STUCK_APP_KAPP_FN_NOT_LAM,
            "wh3_stuck_app_kapp_fn_not_lam: the corollary the residual actually needs — a stuck APPLICATION never has a lam at its spine head. DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(
            SRC_KAPP_FN_NOT_APP,
            "kapp_fn_not_app: a spine head is never an application. Nothing in the tree said so, and the case analysis over head shapes is not exhaustive without it. DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(
            SRC_HNF3_APP_RESIDUAL_COVERED,
            "hnf3_app_residual_covered: hnf3's application residual, discharged for TEN of its eleven head shapes, with the eleventh isolated as an explicit premise. \\
\\
Case analysis on the SPINE HEAD under stuckness. sort, pi, lit, proj and bvar close through the new bridge; app, lam and let_ are impossible; a delta-LIVE const is impossible because stuckness excludes it; a delta-dead recmeta-free const closes through the existing supplier. Only the delta-dead RECURSOR-headed class is carried, as rec_res. \\
\\
A real gain beyond the rigid rows: the delta-deadness and const-name hypotheses that hnf3_app_residual_of_dead_const_head demanded FROM ITS CALLER are now DERIVED from stuckness inside the supplier. \\
\\
WHY rec_res IS NOT NARROWED to the two genuinely open sub-rows, which is the honest part: the obstruction is not in those rows but in the DISPATCH. Selecting among under-applied / at-boundary / past-the-major needs Nat trichotomy, and core_spec has none — no le_total, no le_dec, no le_or_gt, no le_antisymm. Two of the four sub-rows already have suppliers; they simply cannot be selected between. Stating rec_res at the whole recursor class is the narrowest premise that is honestly dischargeable today. DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(
            SRC_NF_HEAD_BVARAPP_VIA_KAPP_FN,
            "nf_head_bvarapp_via_kapp_fn: nf_head at the very term that refuted the residual one commit ago, now derived through the bridge. The counterexample class is closed. DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }
}

const SRC_RIGID_APP_HEAD_OF_KAPP_FN: &str = "def rigid_app_head_of_kapp_fn (e : KExpr) : rigid_app_head (kapp_fn e) -> rigid_app_head e := KExpr.rec (fun (x : KExpr) => rigid_app_head (kapp_fn x) -> rigid_app_head x) (fun (sl : Level) (h : rigid_app_head (kapp_fn (KExpr.sort sl))) => h) (fun (bi : Nat) (h : rigid_app_head (kapp_fn (KExpr.bvar bi))) => h) (fun (af : KExpr) (aa : KExpr) (ihaf : rigid_app_head (kapp_fn af) -> rigid_app_head af) (_ihaa : rigid_app_head (kapp_fn aa) -> rigid_app_head aa) (h : rigid_app_head (kapp_fn (KExpr.app af aa))) => rigid_app_head.app af aa (ihaf h)) (fun (lt2 : KExpr) (lb2 : KExpr) (_ihlt : rigid_app_head (kapp_fn lt2) -> rigid_app_head lt2) (_ihlb : rigid_app_head (kapp_fn lb2) -> rigid_app_head lb2) (h : rigid_app_head (kapp_fn (KExpr.lam lt2 lb2))) => h) (fun (pt2 : KExpr) (pb2 : KExpr) (_ihpt : rigid_app_head (kapp_fn pt2) -> rigid_app_head pt2) (_ihpb : rigid_app_head (kapp_fn pb2) -> rigid_app_head pb2) (h : rigid_app_head (kapp_fn (KExpr.pi pt2 pb2))) => h) (fun (cn : Name) (cus : ListType Level) (h : rigid_app_head (kapp_fn (KExpr.const cn cus))) => h) (fun (zt2 : KExpr) (zv2 : KExpr) (zb2 : KExpr) (_ihzt : rigid_app_head (kapp_fn zt2) -> rigid_app_head zt2) (_ihzv : rigid_app_head (kapp_fn zv2) -> rigid_app_head zv2) (_ihzb : rigid_app_head (kapp_fn zb2) -> rigid_app_head zb2) (h : rigid_app_head (kapp_fn (KExpr.let_ zt2 zv2 zb2))) => h) (fun (ps2 : Name) (pi2 : Nat) (psub2 : KExpr) (_ihsub : rigid_app_head (kapp_fn psub2) -> rigid_app_head psub2) (h : rigid_app_head (kapp_fn (KExpr.proj ps2 pi2 psub2))) => h) (fun (lv : Nat) (h : rigid_app_head (kapp_fn (KExpr.lit lv))) => h) e";

const SRC_RIGID_APP_HEAD_OF_KAPP_FN_SORT_WITNESS: &str = "def rigid_app_head_of_kapp_fn_sort_witness : rigid_app_head (KExpr.app (KExpr.sort Level.zero) (KExpr.sort Level.zero)) := rigid_app_head_of_kapp_fn (KExpr.app (KExpr.sort Level.zero) (KExpr.sort Level.zero)) (rigid_app_head.sort Level.zero)";

const SRC_RIGID_APP_HEAD_OF_KAPP_FN_BVAR_WITNESS: &str = "def rigid_app_head_of_kapp_fn_bvar_witness : rigid_app_head (KExpr.app (KExpr.bvar Nat.zero) (KExpr.sort Level.zero)) := rigid_app_head_of_kapp_fn (KExpr.app (KExpr.bvar Nat.zero) (KExpr.sort Level.zero)) (rigid_app_head.bvar Nat.zero)";

const SRC_WH3_STUCK_LAM: &str = "def wh3_stuck_lam (k : Nat) (lty : KExpr) (lb : KExpr) : wh3_stuck_at k (KExpr.lam lty lb) := Eq.refl WhStepR WhStepR.wstuck";

const SRC_WH3_STUCK_KAPP_FN_NOT_LAM_IS_FALSE: &str = "def wh3_stuck_kapp_fn_not_lam_is_false (hbad : forall (k : Nat) (x : KExpr) (lt2 : KExpr) (lb2 : KExpr), wh3_stuck_at k x -> Eq KExpr (kapp_fn x) (KExpr.lam lt2 lb2) -> Empty) : Empty := hbad Nat.zero (KExpr.lam (KExpr.sort Level.zero) (KExpr.bvar Nat.zero)) (KExpr.sort Level.zero) (KExpr.bvar Nat.zero) (wh3_stuck_lam Nat.zero (KExpr.sort Level.zero) (KExpr.bvar Nat.zero)) (Eq.refl KExpr (KExpr.lam (KExpr.sort Level.zero) (KExpr.bvar Nat.zero)))";

const SRC_WH3_STUCK_KAPP_FN_LAM_IS_LAM: &str = "def wh3_stuck_kapp_fn_lam_is_lam (k : Nat) (lty : KExpr) (lb : KExpr) (e : KExpr) : wh3_stuck_at k e -> Eq KExpr (kapp_fn e) (KExpr.lam lty lb) -> Eq KExpr e (KExpr.lam lty lb) := KExpr.rec (fun (x : KExpr) => wh3_stuck_at k x -> Eq KExpr (kapp_fn x) (KExpr.lam lty lb) -> Eq KExpr x (KExpr.lam lty lb)) (fun (sl : Level) (_hs : wh3_stuck_at k (KExpr.sort sl)) (hh : Eq KExpr (kapp_fn (KExpr.sort sl)) (KExpr.lam lty lb)) => hh) (fun (bi : Nat) (_hs : wh3_stuck_at k (KExpr.bvar bi)) (hh : Eq KExpr (kapp_fn (KExpr.bvar bi)) (KExpr.lam lty lb)) => hh) (fun (af : KExpr) (aa : KExpr) (ihaf : wh3_stuck_at k af -> Eq KExpr (kapp_fn af) (KExpr.lam lty lb) -> Eq KExpr af (KExpr.lam lty lb)) (_ihaa : wh3_stuck_at k aa -> Eq KExpr (kapp_fn aa) (KExpr.lam lty lb) -> Eq KExpr aa (KExpr.lam lty lb)) (hsa : wh3_stuck_at k (KExpr.app af aa)) (hh : Eq KExpr (kapp_fn (KExpr.app af aa)) (KExpr.lam lty lb)) => Empty.rec (fun (_ : Empty) => Eq KExpr (KExpr.app af aa) (KExpr.lam lty lb)) (wh3_stuck_app_head_not_lam k lty lb aa (Eq.subst KExpr (fun (z : KExpr) => wh3_stuck_at k (KExpr.app z aa)) af (KExpr.lam lty lb) (ihaf (wh3_stuck_app_fn_stuck k af aa hsa) hh) hsa))) (fun (lt2 : KExpr) (lb2 : KExpr) (_ihlt : wh3_stuck_at k lt2 -> Eq KExpr (kapp_fn lt2) (KExpr.lam lty lb) -> Eq KExpr lt2 (KExpr.lam lty lb)) (_ihlb : wh3_stuck_at k lb2 -> Eq KExpr (kapp_fn lb2) (KExpr.lam lty lb) -> Eq KExpr lb2 (KExpr.lam lty lb)) (_hs : wh3_stuck_at k (KExpr.lam lt2 lb2)) (hh : Eq KExpr (kapp_fn (KExpr.lam lt2 lb2)) (KExpr.lam lty lb)) => hh) (fun (pt2 : KExpr) (pb2 : KExpr) (_ihpt : wh3_stuck_at k pt2 -> Eq KExpr (kapp_fn pt2) (KExpr.lam lty lb) -> Eq KExpr pt2 (KExpr.lam lty lb)) (_ihpb : wh3_stuck_at k pb2 -> Eq KExpr (kapp_fn pb2) (KExpr.lam lty lb) -> Eq KExpr pb2 (KExpr.lam lty lb)) (_hs : wh3_stuck_at k (KExpr.pi pt2 pb2)) (hh : Eq KExpr (kapp_fn (KExpr.pi pt2 pb2)) (KExpr.lam lty lb)) => hh) (fun (cn : Name) (cus : ListType Level) (_hs : wh3_stuck_at k (KExpr.const cn cus)) (hh : Eq KExpr (kapp_fn (KExpr.const cn cus)) (KExpr.lam lty lb)) => hh) (fun (zt2 : KExpr) (zv2 : KExpr) (zb2 : KExpr) (_ihzt : wh3_stuck_at k zt2 -> Eq KExpr (kapp_fn zt2) (KExpr.lam lty lb) -> Eq KExpr zt2 (KExpr.lam lty lb)) (_ihzv : wh3_stuck_at k zv2 -> Eq KExpr (kapp_fn zv2) (KExpr.lam lty lb) -> Eq KExpr zv2 (KExpr.lam lty lb)) (_ihzb : wh3_stuck_at k zb2 -> Eq KExpr (kapp_fn zb2) (KExpr.lam lty lb) -> Eq KExpr zb2 (KExpr.lam lty lb)) (_hs : wh3_stuck_at k (KExpr.let_ zt2 zv2 zb2)) (hh : Eq KExpr (kapp_fn (KExpr.let_ zt2 zv2 zb2)) (KExpr.lam lty lb)) => hh) (fun (ps2 : Name) (pi2 : Nat) (psub2 : KExpr) (_ihsub : wh3_stuck_at k psub2 -> Eq KExpr (kapp_fn psub2) (KExpr.lam lty lb) -> Eq KExpr psub2 (KExpr.lam lty lb)) (_hs : wh3_stuck_at k (KExpr.proj ps2 pi2 psub2)) (hh : Eq KExpr (kapp_fn (KExpr.proj ps2 pi2 psub2)) (KExpr.lam lty lb)) => hh) (fun (lv : Nat) (_hs : wh3_stuck_at k (KExpr.lit lv)) (hh : Eq KExpr (kapp_fn (KExpr.lit lv)) (KExpr.lam lty lb)) => hh) e";

const SRC_WH3_STUCK_APP_KAPP_FN_NOT_LAM: &str = "def wh3_stuck_app_kapp_fn_not_lam (k : Nat) (lty : KExpr) (lb : KExpr) (f : KExpr) (a : KExpr) (hs : wh3_stuck_at k (KExpr.app f a)) (hh : Eq KExpr (kapp_fn (KExpr.app f a)) (KExpr.lam lty lb)) : Empty := wh3_stuck_app_head_not_lam k lty lb a (Eq.subst KExpr (fun (z : KExpr) => wh3_stuck_at k (KExpr.app z a)) f (KExpr.lam lty lb) (wh3_stuck_kapp_fn_lam_is_lam k lty lb f (wh3_stuck_app_fn_stuck k f a hs) hh) hs)";

const SRC_KAPP_FN_NOT_APP: &str = "def kapp_fn_not_app (C : Type) (e : KExpr) : forall (gf : KExpr) (ga : KExpr), Eq KExpr (kapp_fn e) (KExpr.app gf ga) -> C := KExpr.rec (fun (x : KExpr) => forall (gf : KExpr) (ga : KExpr), Eq KExpr (kapp_fn x) (KExpr.app gf ga) -> C) (fun (sl : Level) (gf : KExpr) (ga : KExpr) (hq : Eq KExpr (kapp_fn (KExpr.sort sl)) (KExpr.app gf ga)) => kexpr_discr_t C (KExpr.sort sl) (KExpr.app gf ga) hq (Eq.refl Bool Bool.false)) (fun (bi : Nat) (gf : KExpr) (ga : KExpr) (hq : Eq KExpr (kapp_fn (KExpr.bvar bi)) (KExpr.app gf ga)) => kexpr_discr_t C (KExpr.bvar bi) (KExpr.app gf ga) hq (Eq.refl Bool Bool.false)) (fun (af : KExpr) (aa : KExpr) (ihaf : forall (gf : KExpr) (ga : KExpr), Eq KExpr (kapp_fn af) (KExpr.app gf ga) -> C) (_ihaa : forall (gf : KExpr) (ga : KExpr), Eq KExpr (kapp_fn aa) (KExpr.app gf ga) -> C) => ihaf) (fun (lt2 : KExpr) (lb2 : KExpr) (_ihlt : forall (gf : KExpr) (ga : KExpr), Eq KExpr (kapp_fn lt2) (KExpr.app gf ga) -> C) (_ihlb : forall (gf : KExpr) (ga : KExpr), Eq KExpr (kapp_fn lb2) (KExpr.app gf ga) -> C) (gf : KExpr) (ga : KExpr) (hq : Eq KExpr (kapp_fn (KExpr.lam lt2 lb2)) (KExpr.app gf ga)) => kexpr_discr_t C (KExpr.lam lt2 lb2) (KExpr.app gf ga) hq (Eq.refl Bool Bool.false)) (fun (pt2 : KExpr) (pb2 : KExpr) (_ihpt : forall (gf : KExpr) (ga : KExpr), Eq KExpr (kapp_fn pt2) (KExpr.app gf ga) -> C) (_ihpb : forall (gf : KExpr) (ga : KExpr), Eq KExpr (kapp_fn pb2) (KExpr.app gf ga) -> C) (gf : KExpr) (ga : KExpr) (hq : Eq KExpr (kapp_fn (KExpr.pi pt2 pb2)) (KExpr.app gf ga)) => kexpr_discr_t C (KExpr.pi pt2 pb2) (KExpr.app gf ga) hq (Eq.refl Bool Bool.false)) (fun (cn : Name) (cus : ListType Level) (gf : KExpr) (ga : KExpr) (hq : Eq KExpr (kapp_fn (KExpr.const cn cus)) (KExpr.app gf ga)) => kexpr_discr_t C (KExpr.const cn cus) (KExpr.app gf ga) hq (Eq.refl Bool Bool.false)) (fun (zt2 : KExpr) (zv2 : KExpr) (zb2 : KExpr) (_ihzt : forall (gf : KExpr) (ga : KExpr), Eq KExpr (kapp_fn zt2) (KExpr.app gf ga) -> C) (_ihzv : forall (gf : KExpr) (ga : KExpr), Eq KExpr (kapp_fn zv2) (KExpr.app gf ga) -> C) (_ihzb : forall (gf : KExpr) (ga : KExpr), Eq KExpr (kapp_fn zb2) (KExpr.app gf ga) -> C) (gf : KExpr) (ga : KExpr) (hq : Eq KExpr (kapp_fn (KExpr.let_ zt2 zv2 zb2)) (KExpr.app gf ga)) => kexpr_discr_t C (KExpr.let_ zt2 zv2 zb2) (KExpr.app gf ga) hq (Eq.refl Bool Bool.false)) (fun (ps2 : Name) (pi2 : Nat) (psub2 : KExpr) (_ihsub : forall (gf : KExpr) (ga : KExpr), Eq KExpr (kapp_fn psub2) (KExpr.app gf ga) -> C) (gf : KExpr) (ga : KExpr) (hq : Eq KExpr (kapp_fn (KExpr.proj ps2 pi2 psub2)) (KExpr.app gf ga)) => kexpr_discr_t C (KExpr.proj ps2 pi2 psub2) (KExpr.app gf ga) hq (Eq.refl Bool Bool.false)) (fun (lv : Nat) (gf : KExpr) (ga : KExpr) (hq : Eq KExpr (kapp_fn (KExpr.lit lv)) (KExpr.app gf ga)) => kexpr_discr_t C (KExpr.lit lv) (KExpr.app gf ga) hq (Eq.refl Bool Bool.false)) e";

const SRC_HNF3_APP_RESIDUAL_COVERED: &str = "def hnf3_app_residual_covered (rec_res : forall (r1 : KExpr) (k1 : Nat) (zf1 : KExpr) (za1 : KExpr) (nm : Name) (meta : RecMeta), Eq (OptionType KExpr) (defval_for (red_def the_red_env) nm) (OptionType.none KExpr) -> Eq (OptionType RecMeta) (recmeta_for (red_rec the_red_env) nm) (OptionType.some RecMeta meta) -> Eq (OptionType Name) (kexpr_const_name (kapp_fn r1)) (OptionType.some Name nm) -> wh3_stuck_at k1 r1 -> Eq KExpr r1 (KExpr.app zf1 za1) -> nf_head r1) (r0 : KExpr) (k0 : Nat) (zf : KExpr) (za : KExpr) (hs : wh3_stuck_at k0 r0) (heq : Eq KExpr r0 (KExpr.app zf za)) : nf_head r0 := KExpr.rec (fun (hd : KExpr) => Eq KExpr (kapp_fn r0) hd -> nf_head r0) (fun (sl : Level) (hq : Eq KExpr (kapp_fn r0) (KExpr.sort sl)) => nf_head.rigid r0 (rigid_app_head_of_kapp_fn r0 (Eq.substType KExpr (fun (z : KExpr) => rigid_app_head z) (KExpr.sort sl) (kapp_fn r0) (Eq.symm KExpr (kapp_fn r0) (KExpr.sort sl) hq) (rigid_app_head.sort sl)))) (fun (bi : Nat) (hq : Eq KExpr (kapp_fn r0) (KExpr.bvar bi)) => nf_head.rigid r0 (rigid_app_head_of_kapp_fn r0 (Eq.substType KExpr (fun (z : KExpr) => rigid_app_head z) (KExpr.bvar bi) (kapp_fn r0) (Eq.symm KExpr (kapp_fn r0) (KExpr.bvar bi) hq) (rigid_app_head.bvar bi)))) (fun (af : KExpr) (aa : KExpr) (_ihaf : Eq KExpr (kapp_fn r0) af -> nf_head r0) (_ihaa : Eq KExpr (kapp_fn r0) aa -> nf_head r0) (hq : Eq KExpr (kapp_fn r0) (KExpr.app af aa)) => kapp_fn_not_app (nf_head r0) r0 af aa hq) (fun (lt2 : KExpr) (lb2 : KExpr) (_ihlt : Eq KExpr (kapp_fn r0) lt2 -> nf_head r0) (_ihlb : Eq KExpr (kapp_fn r0) lb2 -> nf_head r0) (hq : Eq KExpr (kapp_fn r0) (KExpr.lam lt2 lb2)) => kexpr_discr_t (nf_head r0) (KExpr.app zf za) (KExpr.lam lt2 lb2) (Eq.trans KExpr (KExpr.app zf za) r0 (KExpr.lam lt2 lb2) (Eq.symm KExpr r0 (KExpr.app zf za) heq) (wh3_stuck_kapp_fn_lam_is_lam k0 lt2 lb2 r0 hs hq)) (Eq.refl Bool Bool.false)) (fun (pt2 : KExpr) (pb2 : KExpr) (_ihpt : Eq KExpr (kapp_fn r0) pt2 -> nf_head r0) (_ihpb : Eq KExpr (kapp_fn r0) pb2 -> nf_head r0) (hq : Eq KExpr (kapp_fn r0) (KExpr.pi pt2 pb2)) => nf_head.rigid r0 (rigid_app_head_of_kapp_fn r0 (Eq.substType KExpr (fun (z : KExpr) => rigid_app_head z) (KExpr.pi pt2 pb2) (kapp_fn r0) (Eq.symm KExpr (kapp_fn r0) (KExpr.pi pt2 pb2) hq) (rigid_app_head.pi pt2 pb2)))) (fun (cn : Name) (cus : ListType Level) (hq : Eq KExpr (kapp_fn r0) (KExpr.const cn cus)) => OptionType.rec KExpr (fun (o : OptionType KExpr) => Eq (OptionType KExpr) (defval_for (red_def the_red_env) cn) o -> nf_head r0) (fun (hdn : Eq (OptionType KExpr) (defval_for (red_def the_red_env) cn) (OptionType.none KExpr)) => OptionType.rec RecMeta (fun (om : OptionType RecMeta) => Eq (OptionType RecMeta) (recmeta_for (red_rec the_red_env) cn) om -> nf_head r0) (fun (hrn : Eq (OptionType RecMeta) (recmeta_for (red_rec the_red_env) cn) (OptionType.none RecMeta)) => hnf3_app_residual_of_dead_const_head r0 k0 zf za cn hdn hrn (Eq.cong KExpr (OptionType Name) kexpr_const_name (kapp_fn r0) (KExpr.const cn cus) hq) hs heq) (fun (meta : RecMeta) (hrm : Eq (OptionType RecMeta) (recmeta_for (red_rec the_red_env) cn) (OptionType.some RecMeta meta)) => rec_res r0 k0 zf za cn meta hdn hrm (Eq.cong KExpr (OptionType Name) kexpr_const_name (kapp_fn r0) (KExpr.const cn cus) hq) hs heq) (recmeta_for (red_rec the_red_env) cn) (Eq.refl (OptionType RecMeta) (recmeta_for (red_rec the_red_env) cn))) (fun (dv : KExpr) (hdv : Eq (OptionType KExpr) (defval_for (red_def the_red_env) cn) (OptionType.some KExpr dv)) => Empty.rec (fun (_ : Empty) => nf_head r0) (wh3_stuck_const_name_no_delta k0 cn dv hdv (kapp_fn r0) (Eq.cong KExpr (OptionType Name) kexpr_const_name (kapp_fn r0) (KExpr.const cn cus) hq) (wh3_stuck_kapp_fn_stuck k0 r0 hs))) (defval_for (red_def the_red_env) cn) (Eq.refl (OptionType KExpr) (defval_for (red_def the_red_env) cn))) (fun (zt2 : KExpr) (zv2 : KExpr) (zb2 : KExpr) (_ihzt : Eq KExpr (kapp_fn r0) zt2 -> nf_head r0) (_ihzv : Eq KExpr (kapp_fn r0) zv2 -> nf_head r0) (_ihzb : Eq KExpr (kapp_fn r0) zb2 -> nf_head r0) (hq : Eq KExpr (kapp_fn r0) (KExpr.let_ zt2 zv2 zb2)) => Empty.rec (fun (_ : Empty) => nf_head r0) (wh3_stuck_kapp_fn_not_let k0 r0 zt2 zv2 zb2 hq hs)) (fun (ps2 : Name) (pi2 : Nat) (psub2 : KExpr) (_ihsub : Eq KExpr (kapp_fn r0) psub2 -> nf_head r0) (hq : Eq KExpr (kapp_fn r0) (KExpr.proj ps2 pi2 psub2)) => nf_head.rigid r0 (rigid_app_head_of_kapp_fn r0 (Eq.substType KExpr (fun (z : KExpr) => rigid_app_head z) (KExpr.proj ps2 pi2 psub2) (kapp_fn r0) (Eq.symm KExpr (kapp_fn r0) (KExpr.proj ps2 pi2 psub2) hq) (rigid_app_head.proj ps2 pi2 psub2)))) (fun (lv : Nat) (hq : Eq KExpr (kapp_fn r0) (KExpr.lit lv)) => nf_head.rigid r0 (rigid_app_head_of_kapp_fn r0 (Eq.substType KExpr (fun (z : KExpr) => rigid_app_head z) (KExpr.lit lv) (kapp_fn r0) (Eq.symm KExpr (kapp_fn r0) (KExpr.lit lv) hq) (rigid_app_head.lit lv)))) (kapp_fn r0) (Eq.refl KExpr (kapp_fn r0))";

const SRC_NF_HEAD_BVARAPP_VIA_KAPP_FN: &str = "def nf_head_bvarapp_via_kapp_fn : nf_head (KExpr.app (KExpr.bvar Nat.zero) (KExpr.sort Level.zero)) := nf_head.rigid (KExpr.app (KExpr.bvar Nat.zero) (KExpr.sort Level.zero)) rigid_app_head_of_kapp_fn_bvar_witness";
