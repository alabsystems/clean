// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Source builders for R10 of the candidate-model construction ladder — the
//! pure string half of the KEYSTONE rung.
//!
//! A sibling module rather than a region of `candmodel_construct_r10.rs`, on
//! the convention `candmodel_construct_r7_tests.rs` already set here: the
//! registration half, the source half and the battery that reads them back are
//! three subjects, and keeping them one file crossed the 1000-line paragon
//! ratchet. Every source in this file is pre-validated through the clean-parser
//! scratch harness (`candmodel_construct_r10_tests.rs`).
//!
//! Read `candmodel_construct_r10.rs` first: it carries the rung's verdict, the
//! counterexample and the honesty notes.

// ==== is pre-validated through the clean-parser scratch harness).          ====

use super::candmodel_construct_r3::{
    ap, beta_inv_body, conts_at, sp, zcontract, Cont, NZERO, RHSZ,
};
use super::candmodel_construct_r5::{
    ty_apphf_beta_inv, ty_apphf_whnf_inv, ty_piset_cr3, ty_piset_cr3_aux, val_candinterp_iscandhf,
    val_piset_cr3, val_piset_cr3_aux, SRC_CAND_CR3HF, SRC_IS_CAND_HF, TY_CANDINTERP_ISCANDHF,
    TY_ISCANDHF_CR1, TY_ISCANDHF_CR2, TY_ISCANDHF_CR3, TY_ISCANDHF_INTRO, VAL_ISCANDHF_CR1,
    VAL_ISCANDHF_CR2, VAL_ISCANDHF_CR3, VAL_ISCANDHF_INTRO,
};

/// `bvar 0` — the inert filler in the counterexample's motive and successor
/// slots.
pub(super) const V0: &str = "(KExpr.bvar Nat.zero)";
/// The self-application body `app (bvar 0) (bvar 0)`, R5's spelling.
pub(super) const SELF_BODY: &str = "(KExpr.app (KExpr.bvar Nat.zero) (KExpr.bvar Nat.zero))";
/// R5's looping lambda. It is STEP-FREE (so it may sit inside a step-free
/// spine) and yet self-application of it diverges — the exact pair of
/// properties the counterexample needs.
pub(super) const OM: &str = "r5_omegaLam";
/// The non-dependent function type `pi (sort 0) (sort 0)`.
pub(super) const PI00: &str = "(KExpr.pi (KExpr.sort Level.zero) (KExpr.sort Level.zero))";
/// The base candidate, spelled as R5's interpretation spells it.
pub(super) const TOPSET: &str = "(fun (e : KExpr) => whnf_acc e)";
/// The fixed definition environment.
pub(super) const DENV: &str = "(red_def the_red_env)";
/// The fixed recursor environment.
pub(super) const RENV: &str = "(red_rec the_red_env)";
/// The bare const at `fixture_def_env_name` — a REAL reflected kernel name that is
/// neither δ-defined nor a recursor (the inductive type `DefEnv`, R9's
/// `DEADNAME`).
pub(super) const DEADCONST: &str = "(KExpr.const fixture_def_env_name (ListType.nil Level))";

// ================================================================
// Group A — THE SETTLEMENT: unrestricted cr3 for `PiSet` is FALSE.
// ================================================================

/// The `KExpr.rec` arm list at motive `fun _ => KExpr`, with the `lam` arm
/// replaced by `pick`. Constructor order: sort, bvar, app, lam, pi, const,
/// let_, proj, lit.
pub(super) fn kexpr_lam_proj(pick: &str) -> String {
    format!(
        "KExpr.rec (fun (_ : KExpr) => KExpr) \
         (fun (_ : Level) => e) \
         (fun (_ : Nat) => e) \
         (fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => e) \
         {pick} \
         (fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => e) \
         (fun (_ : Name) (_ : ListType Level) => e) \
         (fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => e) \
         (fun (_ : Name) (_ : Nat) (_ : KExpr) (_ : KExpr) => e) \
         (fun (_ : Nat) => e) e"
    )
}

pub(super) fn src_r10_lam_ty() -> String {
    format!(
        "def r10_lamTy (e : KExpr) : KExpr := {}",
        kexpr_lam_proj("(fun (zt : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => zt)")
    )
}

pub(super) fn src_r10_lam_body() -> String {
    format!(
        "def r10_lamBody (e : KExpr) : KExpr := {}",
        kexpr_lam_proj("(fun (_ : KExpr) (zb : KExpr) (_ : KExpr) (_ : KExpr) => zb)")
    )
}

pub(super) const TY_R10_BETA_LAM_HEAD: &str = "forall (f : KExpr) (a : KExpr), Eq KExpr f (KExpr.lam (r10_lamTy f) (r10_lamBody f)) -> beta_reduces (KExpr.app f a) (instantiate (r10_lamBody f) a)";

pub(super) const VAL_R10_BETA_LAM_HEAD: &str = "fun (f : KExpr) (a : KExpr) (h : Eq KExpr f (KExpr.lam (r10_lamTy f) (r10_lamBody f))) => Eq.substType KExpr (fun (zw : KExpr) => beta_reduces (KExpr.app zw a) (instantiate (r10_lamBody f) a)) (KExpr.lam (r10_lamTy f) (r10_lamBody f)) f (Eq.symm KExpr f (KExpr.lam (r10_lamTy f) (r10_lamBody f)) h) (beta_reduces.beta (r10_lamTy f) (r10_lamBody f) a)";

pub(super) const TY_R10_OMEGALAM_NO_BETA: &str =
    "forall (g2 : KExpr) (C : Type), beta_reduces r5_omegaLam g2 -> C";

pub(super) fn val_r10_omegalam_no_beta() -> String {
    format!(
        "fun (g2 : KExpr) (C : Type) (qhbr : beta_reduces r5_omegaLam g2) => lamHead_beta_inv {V0} {SELF_BODY} g2 C qhbr (fun (qt2 : KExpr) (qst : beta_reduces {V0} qt2) (_qeq : Eq KExpr g2 (KExpr.lam qt2 {SELF_BODY})) => no_whnf_step_bvar Nat.zero qt2 C (whnf_step.beta {V0} qt2 qst)) (fun (qb2 : KExpr) (qsb : beta_reduces {SELF_BODY} qb2) (_qeq : Eq KExpr g2 (KExpr.lam {V0} qb2)) => r5_bvarApp_no_beta qb2 C qsb)"
    )
}

/// The counterexample's stuck neutral: the THREE-argument `Nat.rec` spine
/// whose zero-minor is the looping lambda.
pub(super) fn e_stuck() -> String {
    sp(&[V0, OM, V0])
}

/// That spine saturated at the real `Nat.zero` constructor — the term whose ι
/// fire cr3 has no information about.
pub(super) fn sp4() -> String {
    sp(&[V0, OM, V0, NZERO])
}

/// The real zero-rule contractum at those three arguments.
pub(super) fn zc0() -> String {
    zcontract(V0, OM, V0)
}

/// The three β reducts of `rhsZero`, each written as the kernel's own
/// computation rather than as a hard-coded reflected term.
pub(super) fn b1() -> String {
    format!("(instantiate (r10_lamBody {RHSZ}) {V0})")
}
pub(super) fn b2() -> String {
    format!("(instantiate (r10_lamBody {}) {OM})", b1())
}
pub(super) fn b3() -> String {
    format!("(instantiate (r10_lamBody {}) {V0})", b2())
}

/// `rhsZero` partially reduced: after one β and after two.
pub(super) fn z1() -> String {
    ap(&ap(&b1(), OM), V0)
}
pub(super) fn z2() -> String {
    ap(&b2(), V0)
}

/// The five terms of the divergence chain, `w0` being the one the refuted cr3
/// would have to place in the base candidate.
pub(super) fn w0() -> String {
    ap(&sp4(), OM)
}
pub(super) fn w1() -> String {
    ap(&zc0(), OM)
}
pub(super) fn w2() -> String {
    ap(&z1(), OM)
}
pub(super) fn w3() -> String {
    ap(&z2(), OM)
}
pub(super) fn w4() -> String {
    ap(&b3(), OM)
}

pub(super) fn ty_r10_stuckomega_delta_none() -> String {
    format!(
        "Eq (OptionType KExpr) (delta_reduct {DENV} {}) (OptionType.none KExpr)",
        e_stuck()
    )
}

pub(super) const VAL_R10_STUCKOMEGA_DELTA_NONE: &str =
    "Eq.refl (OptionType KExpr) (OptionType.none KExpr)";

pub(super) fn ty_r10_stuckomega_no_whnf_step() -> String {
    format!("forall (g2 : KExpr), whnf_step {} g2 -> Empty", e_stuck())
}

pub(super) fn val_r10_stuckomega_no_whnf_step() -> String {
    let redex = e_stuck();
    // The head's ι-deadness at arities 1..3 over the real env: a four-argument
    // recursor's major-premise slot is absent, so each is one `Eq.refl` with
    // the argument slots free (R5's `dead` helper, verbatim in shape).
    let dead = |k: usize| {
        let binders = (1..=k)
            .map(|i| format!("(qy{i} : KExpr) "))
            .collect::<Vec<_>>()
            .join("");
        format!("(fun {binders}=> Eq.refl (OptionType KExpr) (OptionType.none KExpr))")
    };
    // Slot continuations: slots 1 and 3 hold `bvar 0`, slot 2 holds the
    // step-free looping lambda.
    let cont = |i: usize| {
        let mut slots: Vec<&str> = vec![V0, OM, V0];
        slots[i] = "qy";
        let src = if i == 1 { OM } else { V0 };
        let kill = if i == 1 {
            "r10_omegaLam_no_beta qy Empty qst".to_string()
        } else {
            format!("no_whnf_step_bvar Nat.zero qy Empty (whnf_step.beta {V0} qy qst)")
        };
        format!(
            "(fun (qy : KExpr) (qst : beta_reduces {src} qy) (_qeq : Eq KExpr g2 {}) => {kill})",
            sp(&slots)
        )
    };
    let delta_arm = format!(
        "(fun (qhdr : delta_reduces {redex} g2) => option_none_ne_some_type KExpr g2 Empty (Eq.trans (OptionType KExpr) (OptionType.none KExpr) (delta_reduct {DENV} {redex}) (OptionType.some KExpr g2) (Eq.symm (OptionType KExpr) (delta_reduct {DENV} {redex}) (OptionType.none KExpr) r10_stuckOmega_delta_none) (delta_reduces_to_step {redex} g2 qhdr)))"
    );
    let beta_arm = format!(
        "(fun (qhbr : beta_reduces {redex} g2) => constSpine3_beta_inv fixture_nat_rec_name kcre_witness_rec_levels {d1} {d2} {d3} {V0} {OM} {V0} g2 Empty qhbr {k1} {k2} {k3})",
        d1 = dead(1),
        d2 = dead(2),
        d3 = dead(3),
        k1 = cont(0),
        k2 = cont(1),
        k3 = cont(2),
    );
    format!(
        "fun (g2 : KExpr) (qhs : whnf_step {redex} g2) => whnf_step.rec {redex} g2 (fun (_ : whnf_step {redex} g2) => Empty) {beta_arm} {delta_arm} qhs"
    )
}

pub(super) fn ty_r10_natzero_whnfacc() -> String {
    format!("whnf_acc {NZERO}")
}

pub(super) const VAL_R10_NATZERO_WHNFACC: &str = "whnfAcc_const_dead fixture_nat_zero_name (ListType.nil Level) (Eq.refl (OptionType KExpr) (OptionType.none KExpr))";

pub(super) fn ty_r10_zc_collapse() -> String {
    format!("Eq KExpr {} r5_omegaLam", b3())
}

pub(super) const VAL_R10_ZC_COLLAPSE: &str = "Eq.refl KExpr r5_omegaLam";

pub(super) fn ty_r10_appstuck_not_whnfacc() -> String {
    format!("whnf_acc {} -> Empty", w0())
}

pub(super) fn val_r10_appstuck_not_whnfacc() -> String {
    let s4 = sp4();
    let zc = zc0();
    let (t1, t2, t3) = (b1(), b2(), b3());
    let (y1, y2) = (z1(), z2());
    let (x0, x1, x2, x3, x4) = (w0(), w1(), w2(), w3(), w4());
    // Step 0: the real ι fire, lifted under the outer application.
    let st0 = format!(
        "(whnfStep_app_left {s4} {zc} {OM} (whnf_step.beta {s4} {zc} (beta_reduces.iota {s4} {zc} (iota_step_to_reduces {s4} {zc} (natRecZ_iota_fires {V0} {OM} {V0})))))"
    );
    // Steps 1-3: the three head betas of `rhsZero`, each lifted through the
    // remaining application spine and then under the outer application.
    let bh = |f: &str, a: &str| format!("(r10_beta_lam_head {f} {a} (Eq.refl KExpr {f}))");
    let head0 = ap(RHSZ, V0);
    let head1 = ap(&head0, OM);
    let t1om = ap(&t1, OM);
    let inner1 = format!(
        "(beta_reduces.app_left {head1} {t1om} {V0} (beta_reduces.app_left {head0} {t1} {OM} {}))",
        bh(RHSZ, V0)
    );
    let st1 = format!("(whnfStep_app_left {zc} {y1} {OM} (whnf_step.beta {zc} {y1} {inner1}))");
    let inner2 = format!("(beta_reduces.app_left {t1om} {t2} {V0} {})", bh(&t1, OM));
    let st2 = format!("(whnfStep_app_left {y1} {y2} {OM} (whnf_step.beta {y1} {y2} {inner2}))");
    let st3 = format!(
        "(whnfStep_app_left {y2} {t3} {OM} (whnf_step.beta {y2} {t3} {}))",
        bh(&t2, V0)
    );
    let acc = format!(
        "(whnfAcc_inv_step {x3} (whnfAcc_inv_step {x2} (whnfAcc_inv_step {x1} (whnfAcc_inv_step {x0} h {x1} {st0}) {x2} {st1}) {x3} {st2}) {x4} {st3})"
    );
    format!(
        "fun (h : whnf_acc {x0}) => r5_omegaV_not_whnfAcc (Eq.substType KExpr (fun (zw : KExpr) => whnf_acc (KExpr.app zw r5_omegaLam)) {t3} r5_omegaLam r10_zc_collapse {acc})"
    )
}

/// The unrestricted cr3 face of the Pi-candidate, with EVERY side condition
/// `isCandHF_piSet` asks for. This is the statement R5 left open.
pub(super) fn full_cr3_hyp(concl: &str) -> String {
    format!(
        "forall (CA : KExpr -> Type) (CB : KExpr -> KExpr -> Type), IsCandHF CA -> (forall (a : KExpr), CA a -> IsCandHF (CB a)) -> candStepInv CA CB -> {concl} (PiSet CA CB)"
    )
}

pub(super) fn ty_r10_piset_cr3_unrestricted_refuted() -> String {
    format!("({}) -> Empty", full_cr3_hyp("candCr3"))
}

pub(super) fn val_r10_piset_cr3_unrestricted_refuted() -> String {
    let cbk = format!("(fun (_ : KExpr) => candInterp {PI00})");
    let hred = format!(
        "(fun (ze2 : KExpr) (zhs : whnf_step {e} ze2) => Empty.rec (fun (_ : Empty) => PiSet {TOPSET} {cbk} ze2) (r10_stuckOmega_no_whnf_step ze2 zhs))",
        e = e_stuck()
    );
    format!(
        "fun (hfull : {hyp}) => r10_appStuck_not_whnfAcc (hfull {TOPSET} {cbk} isCandHF_whnfAcc (fun (za : KExpr) (_zh : whnf_acc za) => candInterp_isCandHF {PI00}) (candStepInv_const {TOPSET} (candInterp {PI00})) {e} ConstFreeUnit.triv {hred} {NZERO} r10_natZero_whnfAcc r5_omegaLam r5_whnfAcc_omegaLam)",
        hyp = full_cr3_hyp("candCr3"),
        e = e_stuck()
    )
}

pub(super) fn ty_r10_iscandset_piset_refuted() -> String {
    format!("({}) -> Empty", full_cr3_hyp("IsCandSet"))
}

pub(super) fn val_r10_iscandset_piset_refuted() -> String {
    format!(
        "fun (h : {hyp}) => r10_piSet_cr3_unrestricted_refuted (fun (CA : KExpr -> Type) (CB : KExpr -> KExpr -> Type) (hCA : IsCandHF CA) (hCB : forall (a : KExpr), CA a -> IsCandHF (CB a)) (hinv : candStepInv CA CB) => isCandSet_cr3 (PiSet CA CB) (h CA CB hCA hCB hinv))",
        hyp = full_cr3_hyp("IsCandSet")
    )
}

pub(super) fn ty_r10_cr3_gap_is_real() -> String {
    let nostep = format!("(forall (g2 : KExpr), whnf_step {} g2 -> Empty)", e_stuck());
    let notacc = format!("(whnf_acc {} -> Empty)", w0());
    format!("AndType (whnf_acc r5_omegaLam) (AndType {nostep} {notacc})")
}

pub(super) fn val_r10_cr3_gap_is_real() -> String {
    let nostep = format!("(forall (g2 : KExpr), whnf_step {} g2 -> Empty)", e_stuck());
    let notacc = format!("(whnf_acc {} -> Empty)", w0());
    format!(
        "AndType.intro (whnf_acc r5_omegaLam) (AndType {nostep} {notacc}) r5_whnfAcc_omegaLam (AndType.intro {nostep} {notacc} r10_stuckOmega_no_whnf_step r10_appStuck_not_whnfAcc)"
    )
}

// ================================================================
// Group B — the honest strongest cr3 face: `HeadInert`.
// ================================================================

/// The head-name side condition of the inert branch, at an arbitrary head term.
pub(super) fn head_eq(e: &str, n: &str) -> String {
    format!("Eq (OptionType Name) (kexpr_const_name (kapp_fn {e})) (OptionType.some Name {n})")
}
pub(super) fn defval_none(n: &str) -> String {
    format!("Eq (OptionType KExpr) (defval_for {DENV} {n}) (OptionType.none KExpr)")
}
pub(super) fn recmeta_none(n: &str) -> String {
    format!("Eq (OptionType RecMeta) (recmeta_for {RENV} {n}) (OptionType.none RecMeta)")
}

pub(super) fn src_head_inert() -> String {
    format!(
        "inductive HeadInert : KExpr -> Type\n\
         | free : forall (e : KExpr), HeadFree e -> HeadInert e\n\
         | inert : forall (n : Name) (e : KExpr), {} -> {} -> {} -> HeadInert e",
        head_eq("e", "n"),
        defval_none("n"),
        recmeta_none("n")
    )
}

pub(super) const TY_HEADINERT_APP: &str =
    "forall (e : KExpr) (a : KExpr), HeadInert e -> HeadInert (KExpr.app e a)";

pub(super) fn val_headinert_app() -> String {
    format!(
        "fun (e : KExpr) (a : KExpr) (h : HeadInert e) => HeadInert.rec (fun (ze : KExpr) (_ : HeadInert ze) => HeadInert (KExpr.app ze a)) (fun (ze : KExpr) (zhf : HeadFree ze) => HeadInert.free (KExpr.app ze a) zhf) (fun (zn : Name) (ze : KExpr) (zh : {}) (zd : {}) (zr : {}) => HeadInert.inert zn (KExpr.app ze a) zh zd zr) e h",
        head_eq("ze", "zn"),
        defval_none("zn"),
        recmeta_none("zn")
    )
}

pub(super) const TY_HEADFREE_HEADINERT: &str = "forall (e : KExpr), HeadFree e -> HeadInert e";
pub(super) const VAL_HEADFREE_HEADINERT: &str =
    "fun (e : KExpr) (h : HeadFree e) => HeadInert.free e h";

pub(super) fn ty_inertconst_headinert() -> String {
    format!(
        "forall (n : Name) (us : ListType Level), {} -> {} -> HeadInert (KExpr.const n us)",
        defval_none("n"),
        recmeta_none("n")
    )
}

pub(super) fn val_inertconst_headinert() -> String {
    format!(
        "fun (n : Name) (us : ListType Level) (hd : {}) (hr : {}) => HeadInert.inert n (KExpr.const n us) (Eq.refl (OptionType Name) (OptionType.some Name n)) hd hr",
        defval_none("n"),
        recmeta_none("n")
    )
}

/// The three continuations of the applied-head inversion, at an arbitrary head
/// spelling. `hi_conts("e")` must render EXACTLY R5's `app_conts()` — the shape
/// guard pins that by rebuilding R5's own type from these.
pub(super) fn hi_conts(head: &str) -> Vec<Cont> {
    vec![
        Cont {
            name: "kLam",
            ty: format!("forall (zA : KExpr) (zb : KExpr), Eq KExpr {head} (KExpr.lam zA zb) -> C"),
        },
        Cont {
            name: "kFn",
            ty: format!(
                "forall (zy : KExpr), beta_reduces {head} zy -> Eq KExpr @R@ (KExpr.app zy a) -> C"
            ),
        },
        Cont {
            name: "kArg",
            ty: format!(
                "forall (zy : KExpr), beta_reduces a zy -> Eq KExpr @R@ (KExpr.app {head} zy) -> C"
            ),
        },
    ]
}

/// The inert-const premises, spliced in where R5's type carries `HeadFree e`.
pub(super) fn ic_premises() -> String {
    format!("{} -> {} ->", head_eq("e", "nm"), recmeta_none("nm"))
}

pub(super) fn ty_appic_beta_inv() -> String {
    ty_apphf_beta_inv()
        .replacen("forall (e : KExpr)", "forall (nm : Name) (e : KExpr)", 1)
        .replacen("HeadFree e ->", &ic_premises(), 1)
}

pub(super) fn val_appic_beta_inv() -> String {
    let redex = "(KExpr.app e a)";
    let inj_f = "(app_inj_fst qf qa e a heq)";
    let inj_a = "(app_inj_snd qf qa e a heq)";
    let live_beta = "kLam qA qb (Eq.symm KExpr (KExpr.lam qA qb) e (app_inj_fst (KExpr.lam qA qb) qarg e a heq))".to_string();
    let live_appl = format!(
        "kFn qf2 (Eq.substType KExpr (fun (qz : KExpr) => beta_reduces qz qf2) qf e {inj_f} qstep) (Eq.cong KExpr KExpr (fun (qz : KExpr) => KExpr.app qf2 qz) qa a {inj_a})"
    );
    let live_appr = format!(
        "kArg qa2 (Eq.substType KExpr (fun (qz : KExpr) => beta_reduces qz qa2) qa a {inj_a} qstep) (Eq.cong KExpr KExpr (fun (qz : KExpr) => KExpr.app qz qa2) qf e {inj_f})"
    );
    // THE ONE ARM THAT DIFFERS FROM R5's HEAD-FREE INVERSION: the head is a
    // const, so head-freeness is unavailable and the ι leg dies on the head
    // const having no recursor metadata instead.
    let live_iota = format!(
        "iota_step_no_recmeta_absurd {RENV} {redex} qe2 nm C hhead hrec (iota_reduces_to_step {redex} qe2 (Eq.substType KExpr (fun (qz : KExpr) => iota_reduces qz qe2) qe {redex} heq qio))"
    );
    let body = beta_inv_body(
        redex,
        "e",
        "a",
        &hi_conts("e"),
        &live_beta,
        &live_appl,
        &live_appr,
        &live_iota,
    );
    format!(
        "fun (nm : Name) (e : KExpr) (a : KExpr) (g2 : KExpr) (C : Type) (hhead : {}) (hrec : {}) (hb : beta_reduces {redex} g2){} => {body}",
        head_eq("e", "nm"),
        recmeta_none("nm"),
        conts_at(&hi_conts("e"), "g2", "")
    )
}

pub(super) fn ty_appic_whnf_inv() -> String {
    ty_apphf_whnf_inv()
        .replacen("forall (e : KExpr)", "forall (nm : Name) (e : KExpr)", 1)
        .replacen(
            "HeadFree e ->",
            &format!(
                "{} -> {} -> {} ->",
                head_eq("e", "nm"),
                defval_none("nm"),
                recmeta_none("nm")
            ),
            1,
        )
}

pub(super) fn val_appic_whnf_inv() -> String {
    let redex = "(KExpr.app e a)";
    let delta_arm = format!(
        "(fun (hdr : delta_reduces {redex} g2) => option_none_ne_some_type KExpr g2 C (Eq.trans (OptionType KExpr) (OptionType.none KExpr) (delta_reduct {DENV} {redex}) (OptionType.some KExpr g2) (Eq.symm (OptionType KExpr) (delta_reduct {DENV} {redex}) (OptionType.none KExpr) (delta_reduct_eq_none_of_defval_none {DENV} {redex} nm hhead hdef)) (delta_reduces_to_step {redex} g2 hdr)))"
    );
    format!(
        "fun (nm : Name) (e : KExpr) (a : KExpr) (g2 : KExpr) (C : Type) (hhead : {}) (hdef : {}) (hrec : {}) (hs : whnf_step {redex} g2){} => whnf_step.rec {redex} g2 (fun (_ : whnf_step {redex} g2) => C) (fun (hbr : beta_reduces {redex} g2) => appIC_beta_inv nm e a g2 C hhead hrec hbr kLam kFn kArg) {delta_arm} hs",
        head_eq("e", "nm"),
        defval_none("nm"),
        recmeta_none("nm"),
        conts_at(&hi_conts("e"), "g2", "")
    )
}

pub(super) fn ty_apphi_whnf_inv() -> String {
    ty_apphf_whnf_inv().replacen("HeadFree e ->", "HeadInert e ->", 1)
}

pub(super) fn val_apphi_whnf_inv() -> String {
    let mot_conts = hi_conts("ze")
        .iter()
        .map(|c| format!("({}) -> ", c.ty.replace("@R@", "g2")))
        .collect::<Vec<_>>()
        .join("");
    let mot = format!(
        "(fun (ze : KExpr) (_ : HeadInert ze) => whnf_step (KExpr.app ze a) g2 -> {mot_conts}C)"
    );
    let bind = |head: &str| conts_at(&hi_conts(head), "g2", "z");
    let free_arm = format!(
        "(fun (ze : KExpr) (zhf : HeadFree ze) => fun (zs : whnf_step (KExpr.app ze a) g2){} => appHF_whnf_inv ze a g2 C zhf zs zkLam zkFn zkArg)",
        bind("ze")
    );
    let inert_arm = format!(
        "(fun (zn : Name) (ze : KExpr) (zh : {}) (zd : {}) (zr : {}) => fun (zs : whnf_step (KExpr.app ze a) g2){} => appIC_whnf_inv zn ze a g2 C zh zd zr zs zkLam zkFn zkArg)",
        head_eq("ze", "zn"),
        defval_none("zn"),
        recmeta_none("zn"),
        bind("ze")
    );
    format!(
        "fun (e : KExpr) (a : KExpr) (g2 : KExpr) (C : Type) (hhi : HeadInert e) (hs : whnf_step (KExpr.app e a) g2){} => HeadInert.rec {mot} {free_arm} {inert_arm} e hhi hs kLam kFn kArg",
        conts_at(&hi_conts("e"), "g2", "")
    )
}

/// R5's textual-weakening idiom (`hf_weaken`) at the NEXT interface: every
/// head-free spelling becomes its head-INERT counterpart. Applied to R5's own
/// builders so the two Pi-candidate proofs cannot drift apart.
///
/// It is ONE replacement short of purely textual, and the exception is
/// load-bearing (measured 2026-08-27, the rung's first heavy run): `HeadFree`
/// is a `def` that unfolds to an `Eq` about `kapp_fn e`, so `HeadFree e` and
/// `HeadFree (app e a)` are the SAME type and R5 passes `hhf` straight into the
/// codomain candidate's cr3 at `app e qa0`. `HeadInert` is an inductive FAMILY
/// indexed by the term, so those are different types even though every side
/// condition inside them is definitionally the same; the elaborator refuses
/// with `expected HeadInert (KExpr.app _ _) ... Discriminant(1) vs
/// Discriminant(4)`. The transport `headInert_app` is therefore genuinely
/// applied at that one site, and the shape guard pins that it still is.
pub(super) fn hi_weaken(src: &str) -> String {
    src.replace(
        "isCandHF_cr3 (CB qa0) (hCB qa0 qhca) (KExpr.app e qa0) hhf",
        "isCandHI_cr3 (CB qa0) (hCB qa0 qhca) (KExpr.app e qa0) (headInert_app e qa0 hhf)",
    )
    .replace("appHF_whnf_inv", "appHI_whnf_inv")
    .replace("piSet_cr3_aux", "piSet_cr3HI_aux")
    .replace("candInterp_isCandHF", "candInterp_isCandHI")
    .replace("isCandHF_whnfAcc", "isCandHI_whnfAcc")
    .replace("isCandHF_piSet", "isCandHI_piSet")
    .replace("isCandHF_intro", "isCandHI_intro")
    .replace("isCandHF_cr", "isCandHI_cr")
    .replace("candCr3HF", "candCr3HI")
    .replace("IsCandHF", "IsCandHI")
    .replace("HeadFree e", "HeadInert e")
}

pub(super) fn src_cand_cr3hi() -> String {
    hi_weaken(SRC_CAND_CR3HF)
}

pub(super) fn src_is_cand_hi() -> String {
    hi_weaken(SRC_IS_CAND_HF)
}

pub(super) fn ty_iscandhi_intro() -> String {
    hi_weaken(TY_ISCANDHF_INTRO)
}
pub(super) fn val_iscandhi_intro() -> String {
    hi_weaken(VAL_ISCANDHF_INTRO)
}
pub(super) fn ty_iscandhi_cr1() -> String {
    hi_weaken(TY_ISCANDHF_CR1)
}
pub(super) fn val_iscandhi_cr1() -> String {
    hi_weaken(VAL_ISCANDHF_CR1)
}
pub(super) fn ty_iscandhi_cr2() -> String {
    hi_weaken(TY_ISCANDHF_CR2)
}
pub(super) fn val_iscandhi_cr2() -> String {
    hi_weaken(VAL_ISCANDHF_CR2)
}
pub(super) fn ty_iscandhi_cr3() -> String {
    hi_weaken(TY_ISCANDHF_CR3)
}
pub(super) fn val_iscandhi_cr3() -> String {
    hi_weaken(VAL_ISCANDHF_CR3)
}

pub(super) const TY_ISCANDHI_WEAKEN: &str = "forall (S : KExpr -> Type), IsCandHI S -> IsCandHF S";
pub(super) const VAL_ISCANDHI_WEAKEN: &str = "fun (S : KExpr -> Type) (hS : IsCandHI S) => isCandHF_intro S (isCandHI_cr1 S hS) (isCandHI_cr2 S hS) (fun (e : KExpr) (zhf : HeadFree e) (hne : Neutral e) (hred : forall (e2 : KExpr), whnf_step e e2 -> S e2) => isCandHI_cr3 S hS e (headFree_headInert e zhf) hne hred)";

pub(super) const TY_ISCANDSET_WEAKENHI: &str =
    "forall (S : KExpr -> Type), IsCandSet S -> IsCandHI S";
pub(super) const VAL_ISCANDSET_WEAKENHI: &str = "fun (S : KExpr -> Type) (hS : IsCandSet S) => isCandHI_intro S (isCandSet_cr1 S hS) (isCandSet_cr2 S hS) (fun (e : KExpr) (_zhi : HeadInert e) (hne : Neutral e) (hred : forall (e2 : KExpr), whnf_step e e2 -> S e2) => isCandSet_cr3 S hS e hne hred)";

pub(super) const TY_ISCANDHI_WHNFACC: &str = "IsCandHI (fun (e : KExpr) => whnf_acc e)";
pub(super) const VAL_ISCANDHI_WHNFACC: &str =
    "isCandSet_weakenHI (fun (e : KExpr) => whnf_acc e) isCand_whnfAcc";

pub(super) fn ty_piset_cr3hi_aux() -> String {
    hi_weaken(&ty_piset_cr3_aux())
}
pub(super) fn val_piset_cr3hi_aux() -> String {
    hi_weaken(&val_piset_cr3_aux())
}
pub(super) fn ty_piset_cr3hi() -> String {
    hi_weaken(&ty_piset_cr3())
}
pub(super) fn val_piset_cr3hi() -> String {
    hi_weaken(&val_piset_cr3())
}

pub(super) const TY_ISCANDHI_PISET: &str = "forall (CA : KExpr -> Type) (CB : KExpr -> KExpr -> Type), IsCandHI CA -> (forall (a : KExpr), CA a -> IsCandHI (CB a)) -> candStepInv CA CB -> IsCandHI (PiSet CA CB)";

pub(super) const VAL_ISCANDHI_PISET: &str = "fun (CA : KExpr -> Type) (CB : KExpr -> KExpr -> Type) (hCA : IsCandHI CA) (hCB : forall (a : KExpr), CA a -> IsCandHI (CB a)) (hinv : candStepInv CA CB) => isCandHI_intro (PiSet CA CB) (piSet_cr1 CA CB (isCandHI_weaken CA hCA) (fun (za : KExpr) (zh : CA za) => isCandHI_weaken (CB za) (hCB za zh))) (piSet_cr2 CA CB (fun (za : KExpr) (zh : CA za) => isCandHI_weaken (CB za) (hCB za zh))) (piSet_cr3HI CA CB hCA hCB hinv)";

pub(super) fn ty_candinterp_iscandhi() -> String {
    hi_weaken(TY_CANDINTERP_ISCANDHF)
}
pub(super) fn val_candinterp_iscandhi() -> String {
    hi_weaken(&val_candinterp_iscandhf())
}

// ================================================================
// Group C — the const unlock, the tightness proof, and the witnesses.
// ================================================================

pub(super) fn ty_r10_deadconst_headinert() -> String {
    format!("HeadInert {DEADCONST}")
}

pub(super) const VAL_R10_DEADCONST_HEADINERT: &str = "inertConst_headInert fixture_def_env_name (ListType.nil Level) (Eq.refl (OptionType KExpr) (OptionType.none KExpr)) (Eq.refl (OptionType RecMeta) (OptionType.none RecMeta))";

pub(super) fn ty_r10_deadconst_cand_mem() -> String {
    format!(
        "forall (S : KExpr -> Type), IsCandHI S -> forall (c : Name) (us : ListType Level), {} -> {} -> S (KExpr.const c us)",
        defval_none("c"),
        recmeta_none("c")
    )
}

pub(super) fn val_r10_deadconst_cand_mem() -> String {
    format!(
        "fun (S : KExpr -> Type) (hS : IsCandHI S) (c : Name) (us : ListType Level) (hd : {}) (hr : {}) => isCandHI_cr3 S hS (KExpr.const c us) (inertConst_headInert c us hd hr) ConstFreeUnit.triv (fun (ze2 : KExpr) (zhs : whnf_step (KExpr.const c us) ze2) => constRedex_whnf_inv c us ze2 (S ze2) zhs (fun (zhdl : delta_step {DENV} (KExpr.const c us) ze2) => r9_const_delta_dead c us hd ze2 (S ze2) zhdl))",
        defval_none("c"),
        recmeta_none("c")
    )
}

pub(super) fn ty_r10_interp_const_pi_witness() -> String {
    format!("candInterp {PI00} {DEADCONST}")
}

pub(super) fn val_r10_interp_const_pi_witness() -> String {
    format!(
        "r10_deadConst_cand_mem (candInterp {PI00}) (candInterp_isCandHI {PI00}) fixture_def_env_name (ListType.nil Level) (Eq.refl (OptionType KExpr) (OptionType.none KExpr)) (Eq.refl (OptionType RecMeta) (OptionType.none RecMeta))"
    )
}

pub(super) fn ty_r10_headinert_strictly_weaker() -> String {
    format!("AndType (HeadInert {DEADCONST}) (HeadFree {DEADCONST} -> Empty)")
}

pub(super) fn val_r10_headinert_strictly_weaker() -> String {
    format!(
        "AndType.intro (HeadInert {DEADCONST}) (HeadFree {DEADCONST} -> Empty) r10_deadConst_headInert (r9_const_headfree_absurd fixture_def_env_name (ListType.nil Level))"
    )
}

pub(super) fn ty_r10_natrec3_not_headinert() -> String {
    format!(
        "forall (x1 : KExpr) (x2 : KExpr) (x3 : KExpr), HeadInert {} -> Empty",
        sp(&["x1", "x2", "x3"])
    )
}

pub(super) fn val_r10_natrec3_not_headinert() -> String {
    let e = sp(&["x1", "x2", "x3"]);
    let redex4 = sp(&["x1", "x2", "x3", NZERO]);
    let contract = zcontract("x1", "x2", "x3");
    let free_arm = format!(
        "(fun (ze : KExpr) (zhf : HeadFree ze) (zeq : Eq KExpr ze {e}) => r9_const_headfree_absurd fixture_nat_rec_name kcre_witness_rec_levels (Eq.substType KExpr (fun (zw : KExpr) => HeadFree zw) ze {e} zeq zhf))"
    );
    let head_at_e = format!(
        "(Eq.substType KExpr (fun (zw : KExpr) => {}) ze {e} zeq zh)",
        head_eq("zw", "zn")
    );
    let inert_arm = format!(
        "(fun (zn : Name) (ze : KExpr) (zh : {}) (zd : {}) (zr : {}) (zeq : Eq KExpr ze {e}) => iota_step_no_recmeta_absurd {RENV} {redex4} {contract} zn Empty {head_at_e} zr (natRecZ_iota_fires x1 x2 x3))",
        head_eq("ze", "zn"),
        defval_none("zn"),
        recmeta_none("zn")
    );
    format!(
        "fun (x1 : KExpr) (x2 : KExpr) (x3 : KExpr) (h : HeadInert {e}) => HeadInert.rec (fun (ze : KExpr) (_ : HeadInert ze) => Eq KExpr ze {e} -> Empty) {free_arm} {inert_arm} {e} h (Eq.refl KExpr {e})"
    )
}

pub(super) fn ty_r10_r5_term_excluded() -> String {
    format!("HeadInert {} -> Empty", sp(&[V0, V0, V0]))
}

pub(super) fn val_r10_r5_term_excluded() -> String {
    format!("r10_natRec3_not_headInert {V0} {V0} {V0}")
}

pub(super) fn ty_r10_counterexample_excluded() -> String {
    format!("HeadInert {} -> Empty", e_stuck())
}

pub(super) fn val_r10_counterexample_excluded() -> String {
    format!("r10_natRec3_not_headInert {V0} {OM} {V0}")
}

pub(super) fn ty_r10_const_unlock_proper() -> String {
    format!("AndType (candInterp {PI00} {DEADCONST}) (candInterp {PI00} r5_omegaLam -> Empty)")
}

pub(super) fn val_r10_const_unlock_proper() -> String {
    format!(
        "AndType.intro (candInterp {PI00} {DEADCONST}) (candInterp {PI00} r5_omegaLam -> Empty) r10_interp_const_pi_witness candInterp_pi_not_total"
    )
}
