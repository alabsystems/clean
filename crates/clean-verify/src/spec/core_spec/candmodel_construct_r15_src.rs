// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! R15 sources — **subject reduction for shapes** (`wk_step`) and the
//! `val_step` arms it unlocks.
//!
//! Read `candmodel_construct_r15.rs` first: it carries the rung's verdict, the
//! scope of what landed, and the obstruction this rung names.
//!
//! **This module deliberately imports nothing** — the R14 convention, so the
//! whole file can be `#[path]`-included into a scratch crate that depends only
//! on `clean-parser` and parse-checked in a second.
//!
//! ## The idiom that made the rung cheap
//!
//! Every inversion here is a **computed motive**: a `KExpr.rec` (sometimes
//! nested with a `Sk.rec`) that maps the SUBJECT's head constructor to the
//! continuation-passing statement it deserves, and every other constructor to
//! the trivially-inhabited `ConstFreeUnit`. That is R12's `Neutral`
//! (`dependent_sn_richmodel.rs:378`) read as an inversion principle, and it
//! deletes the entire `X_ne_Y` / `X_inj_*` bookkeeping that R1/R3/R5's
//! `beta_inv_body` scaffold needs: an arm whose subject is not the target shape
//! discharges by `ConstFreeUnit.triv` rather than by a discrimination lemma, and
//! a LIVE arm hands its own constructor fields straight to the continuation with
//! `Eq.refl` instead of recovering them through injectivity.

// ================================================================
// Shared spellings.
// ================================================================

/// `bvar 0`.
pub(super) const V0: &str = "(KExpr.bvar Nat.zero)";
/// `sort 0`.
pub(super) const S0: &str = "(KExpr.sort Level.zero)";
/// The shape of a semantic type-of-types.
pub(super) const KDTY: &str = "(Sk.kd Sk.ty)";
/// The head-free proof of any non-`const`-headed spine, by computation.
pub(super) const HF_REFL: &str = "(@Eq.refl (OptionType Name) (@OptionType.none Name))";

// ================================================================
// Group A — head-freeness of every shape-typed term.
// ================================================================

/// **`WK` NEVER TYPES A CONST-HEADED SPINE.** `WK` has five constructors
/// (`var`/`sort`/`pi`/`lam`/`app`) and `KExpr.const` is not among them, so the
/// head of a shape-typed application spine is a `bvar`, a `sort`, a `pi` or a
/// `lam` — never a constant. That single fact is what kills the δ and ι arms of
/// `whnf_step` at a `WK`-typed subject, and it is the reason subject reduction
/// needs no reasoning about `the_red_env` at all.
pub(super) const TY_HEADFREE_WK: &str =
    "forall (D : Nat -> Sk) (e : KExpr) (s : Sk), WK D e s -> HeadFree e";

pub(super) fn val_headfree_wk() -> String {
    let motive = "(fun (qD : Nat -> Sk) (qe : KExpr) (qs : Sk) (qh : WK qD qe qs) => HeadFree qe)";
    let m_var = format!("(fun (qD : Nat -> Sk) (qi : Nat) => {HF_REFL})");
    let m_sort = format!("(fun (qD : Nat -> Sk) (qn : Level) => {HF_REFL})");
    let m_pi = format!(
        "(fun (qD : Nat -> Sk) (qA : KExpr) (qB : KExpr) (qsA : Sk) (qsB : Sk) (qhA : WK qD qA qsA) (qhB : WK (skcons (domSk qsA) qD) qB qsB) (qihA : HeadFree qA) (qihB : HeadFree qB) => {HF_REFL})"
    );
    let m_lam = format!(
        "(fun (qD : Nat -> Sk) (qA : KExpr) (qb : KExpr) (qsA : Sk) (qc : Sk) (qhA : WK qD qA qsA) (qhb : WK (skcons (domSk qsA) qD) qb qc) (qihA : HeadFree qA) (qihb : HeadFree qb) => {HF_REFL})"
    );
    let m_app = "(fun (qD : Nat -> Sk) (qf : KExpr) (qa : KExpr) (qd : Sk) (qcc : Sk) (qhf : WK qD qf (Sk.arr qd qcc)) (qha : WK qD qa qd) (qihf : HeadFree qf) (qiha : HeadFree qa) => headFree_app qf qa qihf)";
    format!(
        "fun (D : Nat -> Sk) (e : KExpr) (s : Sk) (h : WK D e s) => @WK.rec {motive} {m_var} {m_sort} {m_pi} {m_lam} {m_app} D e s h"
    )
}

// ================================================================
// Group B — THE ONE STEP INVERSION, as a computed motive.
//
// `r15_stepT C e g2` is the complete case analysis of a one-step reduct of `e`,
// read off `e`'s HEAD CONSTRUCTOR:
//   * `bvar` / `sort` — no rule fires, so the statement is `C` outright, and
//     the inversion IS `no_whnf_step_bvar` / its missing `sort` counterpart;
//   * `app` — head-beta (with the contractum spelled as `beta_reduces.beta`
//     produces it), `app_left`, `app_right`;
//   * `lam` — `lam_ty`, `lam_body`;
//   * `pi` — `pi_dom`, `pi_cod`, which the `forall_` congruences reduce into
//     because `KExpr.forall_` is a REDUCIBLE alias for `KExpr.pi`;
//   * `const` / `let_` / `proj` / `lit` — outside `WK`'s reach, so
//     `ConstFreeUnit`, which is what lets the corresponding `beta_reduces` arms
//     discharge without a single discrimination lemma.
// ================================================================

/// The three continuations at an application subject.
fn app_k(f: &str, a: &str, g: &str) -> [String; 3] {
    [
        format!("forall (zA : KExpr) (zb : KExpr), @Eq KExpr {f} (KExpr.lam zA zb) -> @Eq KExpr {g} (instantiate zb {a}) -> C"),
        format!("forall (zy : KExpr), beta_reduces {f} zy -> @Eq KExpr {g} (KExpr.app zy {a}) -> C"),
        format!("forall (zy : KExpr), beta_reduces {a} zy -> @Eq KExpr {g} (KExpr.app {f} zy) -> C"),
    ]
}

/// The two continuations at a lambda subject.
fn lam_k(a: &str, b: &str, g: &str) -> [String; 2] {
    [
        format!(
            "forall (zy : KExpr), beta_reduces {a} zy -> @Eq KExpr {g} (KExpr.lam zy {b}) -> C"
        ),
        format!(
            "forall (zy : KExpr), beta_reduces {b} zy -> @Eq KExpr {g} (KExpr.lam {a} zy) -> C"
        ),
    ]
}

/// The two continuations at a Π subject.
fn pi_k(a: &str, b: &str, g: &str) -> [String; 2] {
    [
        format!("forall (zy : KExpr), beta_reduces {a} zy -> @Eq KExpr {g} (KExpr.pi zy {b}) -> C"),
        format!("forall (zy : KExpr), beta_reduces {b} zy -> @Eq KExpr {g} (KExpr.pi {a} zy) -> C"),
    ]
}

pub(super) fn src_step_t() -> String {
    let ka = app_k("qf", "qa", "qg");
    let kl = lam_k("qA", "qb", "qg");
    let kp = pi_k("qA", "qB", "qg");
    let ih = "KExpr -> Type";
    format!(
        "def r15_stepT (C : Type) (e : KExpr) (g2 : KExpr) : Type := @KExpr.rec (fun (qe : KExpr) => KExpr -> Type) \
         (fun (qn : Level) (qg : KExpr) => C) \
         (fun (qi : Nat) (qg : KExpr) => C) \
         (fun (qf : KExpr) (qa : KExpr) (qihf : {ih}) (qiha : {ih}) (qg : KExpr) => ({}) -> ({}) -> ({}) -> C) \
         (fun (qA : KExpr) (qb : KExpr) (qihA : {ih}) (qihb : {ih}) (qg : KExpr) => ({}) -> ({}) -> C) \
         (fun (qA : KExpr) (qB : KExpr) (qihA : {ih}) (qihB : {ih}) (qg : KExpr) => ({}) -> ({}) -> C) \
         (fun (qn : Name) (qus : ListType Level) (qg : KExpr) => ConstFreeUnit) \
         (fun (qt : KExpr) (qv : KExpr) (qb : KExpr) (qiht : {ih}) (qihv : {ih}) (qihb : {ih}) (qg : KExpr) => ConstFreeUnit) \
         (fun (qsn : Name) (qpi : Nat) (qsub : KExpr) (qihs : {ih}) (qg : KExpr) => ConstFreeUnit) \
         (fun (qv : Nat) (qg : KExpr) => ConstFreeUnit) e g2",
        ka[0], ka[1], ka[2], kl[0], kl[1], kp[0], kp[1]
    )
}

/// Continuation BINDERS at a target, `z`-prefixed so a template binder can
/// never capture a `q`-prefixed substituted subject (the R3 capture rule).
fn binders(ks: &[String], names: &[&str]) -> String {
    ks.iter()
        .zip(names)
        .map(|(t, n)| format!(" ({n} : {t})"))
        .collect::<Vec<_>>()
        .join("")
}

/// A structurally dead arm: its subject is `const`/`let_`/`proj`/`lit`, which
/// `r15_stepT` sends to `ConstFreeUnit`. No discrimination lemma is involved —
/// the type simply computes away.
fn dead(fields: &str, prem: Option<(&str, &str)>) -> String {
    let p = match prem {
        Some((s, d)) => {
            format!(" (qstep : beta_reduces {s} {d}) (qih : HeadFree {s} -> r15_stepT C {s} {d})")
        }
        None => String::new(),
    };
    format!(
        "(fun {fields}{p} (qhh : HeadFree {}) => ConstFreeUnit.triv)",
        "@SRC@"
    )
}

/// The generic 15-arm `beta_reduces` inversion. Fourteen of the fifteen arms are
/// a single token; the only real work is the ι arm, killed computationally by
/// the head-free hypothesis.
#[allow(clippy::too_many_lines)]
pub(super) fn val_beta_step_inv() -> String {
    let mot = "(fun (qs : KExpr) (qt : KExpr) (qh : beta_reduces qs qt) => HeadFree qs -> r15_stepT C qs qt)";
    let ih = |s: &str, d: &str| format!("(qih : HeadFree {s} -> r15_stepT C {s} {d})");
    let prem = |s: &str, d: &str| format!("(qstep : beta_reduces {s} {d}) {}", ih(s, d));

    // 1 beta: the subject is `app (lam qA qb) qarg` and the reduct is the
    // kernel's own `instantiate qb qarg`.
    let kb = app_k("(KExpr.lam qA qb)", "qarg", "(instantiate qb qarg)");
    let a_beta = format!(
        "(fun (qA : KExpr) (qb : KExpr) (qarg : KExpr) (qhh : HeadFree (KExpr.app (KExpr.lam qA qb) qarg)){} => zk1 qA qb (@Eq.refl KExpr (KExpr.lam qA qb)) (@Eq.refl KExpr (instantiate qb qarg)))",
        binders(&kb, &["zk1", "zk2", "zk3"])
    );

    // 2 app_left / 3 app_right.
    let kl2 = app_k("qf", "qa", "(KExpr.app qf2 qa)");
    let a_appl = format!(
        "(fun (qf : KExpr) (qf2 : KExpr) (qa : KExpr) {} (qhh : HeadFree (KExpr.app qf qa)){} => zk2 qf2 qstep (@Eq.refl KExpr (KExpr.app qf2 qa)))",
        prem("qf", "qf2"),
        binders(&kl2, &["zk1", "zk2", "zk3"])
    );
    let kr2 = app_k("qf", "qa", "(KExpr.app qf qa2)");
    let a_appr = format!(
        "(fun (qf : KExpr) (qa : KExpr) (qa2 : KExpr) {} (qhh : HeadFree (KExpr.app qf qa)){} => zk3 qa2 qstep (@Eq.refl KExpr (KExpr.app qf qa2)))",
        prem("qa", "qa2"),
        binders(&kr2, &["zk1", "zk2", "zk3"])
    );

    // 4 lam_ty / 5 lam_body.
    let klt = lam_k("qty", "qbody", "(KExpr.lam qty2 qbody)");
    let a_lamty = format!(
        "(fun (qty : KExpr) (qty2 : KExpr) (qbody : KExpr) {} (qhh : HeadFree (KExpr.lam qty qbody)){} => zk1 qty2 qstep (@Eq.refl KExpr (KExpr.lam qty2 qbody)))",
        prem("qty", "qty2"),
        binders(&klt, &["zk1", "zk2"])
    );
    let klb = lam_k("qty", "qbody", "(KExpr.lam qty qbody2)");
    let a_lambd = format!(
        "(fun (qty : KExpr) (qbody : KExpr) (qbody2 : KExpr) {} (qhh : HeadFree (KExpr.lam qty qbody)){} => zk2 qbody2 qstep (@Eq.refl KExpr (KExpr.lam qty qbody2)))",
        prem("qbody", "qbody2"),
        binders(&klb, &["zk1", "zk2"])
    );

    // 6 pi_dom / 7 pi_cod, and 8/9 the `forall_` congruences, which land in the
    // SAME arm of `r15_stepT` because `KExpr.forall_` is a reducible alias.
    let mk_pi = |src_dom: &str,
                 src_body: &str,
                 tgt: &str,
                 live: &str,
                 fields: &str,
                 s: &str,
                 d: &str,
                 subj: &str| {
        let ks = pi_k(src_dom, src_body, tgt);
        format!(
            "(fun {fields} {} (qhh : HeadFree {subj}){} => {live})",
            prem(s, d),
            binders(&ks, &["zk1", "zk2"])
        )
    };
    let a_pidom = mk_pi(
        "qdom",
        "qbody",
        "(KExpr.pi qdom2 qbody)",
        "zk1 qdom2 qstep (@Eq.refl KExpr (KExpr.pi qdom2 qbody))",
        "(qdom : KExpr) (qdom2 : KExpr) (qbody : KExpr)",
        "qdom",
        "qdom2",
        "(KExpr.pi qdom qbody)",
    );
    let a_picod = mk_pi(
        "qdom",
        "qbody",
        "(KExpr.pi qdom qbody2)",
        "zk2 qbody2 qstep (@Eq.refl KExpr (KExpr.pi qdom qbody2))",
        "(qdom : KExpr) (qbody : KExpr) (qbody2 : KExpr)",
        "qbody",
        "qbody2",
        "(KExpr.pi qdom qbody)",
    );
    let a_fadom = mk_pi(
        "qdom",
        "qbody",
        "(KExpr.forall_ qdom2 qbody)",
        "zk1 qdom2 qstep (@Eq.refl KExpr (KExpr.pi qdom2 qbody))",
        "(qdom : KExpr) (qdom2 : KExpr) (qbody : KExpr)",
        "qdom",
        "qdom2",
        "(KExpr.forall_ qdom qbody)",
    );
    let a_facod = mk_pi(
        "qdom",
        "qbody",
        "(KExpr.forall_ qdom qbody2)",
        "zk2 qbody2 qstep (@Eq.refl KExpr (KExpr.pi qdom qbody2))",
        "(qdom : KExpr) (qbody : KExpr) (qbody2 : KExpr)",
        "qbody",
        "qbody2",
        "(KExpr.forall_ qdom qbody)",
    );

    // 10-13 the four `let_` arms and 15 `proj`: `WK` types neither, so
    // `r15_stepT` sends both heads to `ConstFreeUnit`.
    let a_zeta = dead("(qty : KExpr) (qval : KExpr) (qbody : KExpr)", None)
        .replace("@SRC@", "(KExpr.let_ qty qval qbody)");
    let a_letty = dead(
        "(qty : KExpr) (qty2 : KExpr) (qval : KExpr) (qbody : KExpr)",
        Some(("qty", "qty2")),
    )
    .replace("@SRC@", "(KExpr.let_ qty qval qbody)");
    let a_letval = dead(
        "(qty : KExpr) (qval : KExpr) (qval2 : KExpr) (qbody : KExpr)",
        Some(("qval", "qval2")),
    )
    .replace("@SRC@", "(KExpr.let_ qty qval qbody)");
    let a_letbd = dead(
        "(qty : KExpr) (qval : KExpr) (qbody : KExpr) (qbody2 : KExpr)",
        Some(("qbody", "qbody2")),
    )
    .replace("@SRC@", "(KExpr.let_ qty qval qbody)");
    let a_proj = dead(
        "(qps : Name) (qpi : Nat) (qsub : KExpr) (qsub2 : KExpr)",
        Some(("qsub", "qsub2")),
    )
    .replace("@SRC@", "(KExpr.proj qps qpi qsub)");

    // 14 iota: the ONLY arm whose subject is a variable, so the only one the
    // computed motive cannot discharge. `WK`'s head-freeness kills it.
    let a_iota = "(fun (qe : KExpr) (qe2 : KExpr) (qio : iota_reduces qe qe2) (qhh : HeadFree qe) => iota_step_head_none_absurd_type (red_rec the_red_env) qe qe2 (r15_stepT C qe qe2) qhh (iota_reduces_to_step qe qe2 qio))";

    format!(
        "fun (C : Type) (e : KExpr) (g2 : KExpr) (hhf : HeadFree e) (hb : beta_reduces e g2) => @beta_reduces.rec {mot} {a_beta} {a_appl} {a_appr} {a_lamty} {a_lambd} {a_pidom} {a_picod} {a_fadom} {a_facod} {a_zeta} {a_letty} {a_letval} {a_letbd} {a_iota} {a_proj} e g2 hb hhf"
    )
}

pub(super) const TY_BETA_STEP_INV: &str =
    "forall (C : Type) (e : KExpr) (g2 : KExpr), HeadFree e -> beta_reduces e g2 -> r15_stepT C e g2";

pub(super) const TY_WHNF_STEP_INV: &str =
    "forall (C : Type) (e : KExpr) (g2 : KExpr), HeadFree e -> whnf_step e g2 -> r15_stepT C e g2";

pub(super) const VAL_WHNF_STEP_INV: &str = "fun (C : Type) (e : KExpr) (g2 : KExpr) (hhf : HeadFree e) (hs : whnf_step e g2) => @whnf_step.rec e g2 (fun (qz : whnf_step e g2) => r15_stepT C e g2) (fun (qbr : beta_reduces e g2) => r15_beta_stepT_inv C e g2 hhf qbr) (fun (qdr : delta_reduces e g2) => delta_step_head_none_absurd_type (red_def the_red_env) e g2 (r15_stepT C e g2) hhf (delta_reduces_to_step e g2 qdr)) hs";

// ================================================================
// Group C — the two `WK` inversions at a lambda, likewise computed.
// ================================================================

/// The `WK`-only lambda inversion, used by `wk_step`. `KExpr.rec` picks the
/// `lam` head, and a nested `Sk.rec` picks the `arr` shape; every other pair is
/// `ConstFreeUnit`, so all four non-lam arms of `WK.rec` are one token.
pub(super) const SRC_WK_LAM_T: &str = "def r15_wkLamT (D : Nat -> Sk) (C : Type) (e : KExpr) (s : Sk) : Type := @KExpr.rec (fun (qe : KExpr) => Sk -> Type) (fun (qn : Level) (qs : Sk) => ConstFreeUnit) (fun (qi : Nat) (qs : Sk) => ConstFreeUnit) (fun (qf : KExpr) (qa : KExpr) (qihf : Sk -> Type) (qiha : Sk -> Type) (qs : Sk) => ConstFreeUnit) (fun (qA : KExpr) (qb : KExpr) (qihA : Sk -> Type) (qihb : Sk -> Type) => @Sk.rec (fun (qz : Sk) => Type) ConstFreeUnit (fun (qs1 : Sk) (qih : Type) => ConstFreeUnit) (fun (qd : Sk) (qc : Sk) (qihd : Type) (qihc : Type) => (WK (skcons qd D) qb qc -> C) -> C)) (fun (qA : KExpr) (qB : KExpr) (qihA : Sk -> Type) (qihB : Sk -> Type) (qs : Sk) => ConstFreeUnit) (fun (qn : Name) (qus : ListType Level) (qs : Sk) => ConstFreeUnit) (fun (qt : KExpr) (qv : KExpr) (qb : KExpr) (qiht : Sk -> Type) (qihv : Sk -> Type) (qihb : Sk -> Type) (qs : Sk) => ConstFreeUnit) (fun (qsn : Name) (qpi : Nat) (qsub : KExpr) (qihs : Sk -> Type) (qs : Sk) => ConstFreeUnit) (fun (qv : Nat) (qs : Sk) => ConstFreeUnit) e s";

/// Registered as a `def`, not a theorem: `wk_step` must REDUCE through it in
/// its beta arm, and an `add_definition` registration lowers to `Opaque`
/// (R12's measured elaborator fact).
pub(super) fn src_wk_lam_inv() -> String {
    let motive =
        "(fun (qD : Nat -> Sk) (qe : KExpr) (qs : Sk) (qh : WK qD qe qs) => r15_wkLamT qD C qe qs)";
    let m_var = "(fun (qD : Nat -> Sk) (qi : Nat) => ConstFreeUnit.triv)";
    let m_sort = "(fun (qD : Nat -> Sk) (qn : Level) => ConstFreeUnit.triv)";
    let m_pi = "(fun (qD : Nat -> Sk) (qA : KExpr) (qB : KExpr) (qsA : Sk) (qsB : Sk) (qhA : WK qD qA qsA) (qhB : WK (skcons (domSk qsA) qD) qB qsB) (qihA : r15_wkLamT qD C qA qsA) (qihB : r15_wkLamT (skcons (domSk qsA) qD) C qB qsB) => ConstFreeUnit.triv)";
    let m_lam = "(fun (qD : Nat -> Sk) (qA : KExpr) (qb : KExpr) (qsA : Sk) (qc : Sk) (qhA : WK qD qA qsA) (qhb : WK (skcons (domSk qsA) qD) qb qc) (qihA : r15_wkLamT qD C qA qsA) (qihb : r15_wkLamT (skcons (domSk qsA) qD) C qb qc) (zk : WK (skcons (domSk qsA) qD) qb qc -> C) => zk qhb)";
    let m_app = "(fun (qD : Nat -> Sk) (qf : KExpr) (qa : KExpr) (qd : Sk) (qcc : Sk) (qhf : WK qD qf (Sk.arr qd qcc)) (qha : WK qD qa qd) (qihf : r15_wkLamT qD C qf (Sk.arr qd qcc)) (qiha : r15_wkLamT qD C qa qd) => ConstFreeUnit.triv)";
    format!(
        "def r15_wk_lam_inv (D : Nat -> Sk) (C : Type) (e : KExpr) (s : Sk) (h : WK D e s) : r15_wkLamT D C e s := @WK.rec {motive} {m_var} {m_sort} {m_pi} {m_lam} {m_app} D e s h"
    )
}

/// The SEMANTIC lambda inversion: the same case analysis, but the continuation
/// also receives the interpretation of the lambda as the semantic function it
/// denotes, AT EVERY valuation. Quantifying the valuation INSIDE the
/// continuation (rather than fixing one outside) is what lets `r15_val_step_sem`
/// hand its own caller a single derivation good for every `r`.
pub(super) const SRC_SVAL_LAM_T: &str = "def r15_svalLamT (D : Nat -> Sk) (C : Type) (e : KExpr) (s : Sk) (F : VEnvD D -> VD s) : Type := @KExpr.rec (fun (qe : KExpr) => forall (qs : Sk), (VEnvD D -> VD qs) -> Type) (fun (qn : Level) (qs : Sk) (qF : VEnvD D -> VD qs) => ConstFreeUnit) (fun (qi : Nat) (qs : Sk) (qF : VEnvD D -> VD qs) => ConstFreeUnit) (fun (qf : KExpr) (qa : KExpr) (qihf : forall (qs : Sk), (VEnvD D -> VD qs) -> Type) (qiha : forall (qs : Sk), (VEnvD D -> VD qs) -> Type) (qs : Sk) (qF : VEnvD D -> VD qs) => ConstFreeUnit) (fun (qA : KExpr) (qb : KExpr) (qihA : forall (qs : Sk), (VEnvD D -> VD qs) -> Type) (qihb : forall (qs : Sk), (VEnvD D -> VD qs) -> Type) => @Sk.rec (fun (qz : Sk) => (VEnvD D -> VD qz) -> Type) (fun (qF : VEnvD D -> VD Sk.ty) => ConstFreeUnit) (fun (qs1 : Sk) (qih : (VEnvD D -> VD qs1) -> Type) (qF : VEnvD D -> VD (Sk.kd qs1)) => ConstFreeUnit) (fun (qd : Sk) (qc : Sk) (qihd : (VEnvD D -> VD qd) -> Type) (qihc : (VEnvD D -> VD qc) -> Type) (qF : VEnvD D -> VD (Sk.arr qd qc)) => (forall (zhb : WK (skcons qd D) qb qc), (forall (zr : VEnvD D) (zx : VD qd), @Eq (VD qc) (qF zr zx) (sval (skcons qd D) qb qc zhb (vconsD qd D zx zr))) -> C) -> C)) (fun (qA : KExpr) (qB : KExpr) (qihA : forall (qs : Sk), (VEnvD D -> VD qs) -> Type) (qihB : forall (qs : Sk), (VEnvD D -> VD qs) -> Type) (qs : Sk) (qF : VEnvD D -> VD qs) => ConstFreeUnit) (fun (qn : Name) (qus : ListType Level) (qs : Sk) (qF : VEnvD D -> VD qs) => ConstFreeUnit) (fun (qt : KExpr) (qv : KExpr) (qb : KExpr) (qiht : forall (qs : Sk), (VEnvD D -> VD qs) -> Type) (qihv : forall (qs : Sk), (VEnvD D -> VD qs) -> Type) (qihb : forall (qs : Sk), (VEnvD D -> VD qs) -> Type) (qs : Sk) (qF : VEnvD D -> VD qs) => ConstFreeUnit) (fun (qsn : Name) (qpi : Nat) (qsub : KExpr) (qihs : forall (qs : Sk), (VEnvD D -> VD qs) -> Type) (qs : Sk) (qF : VEnvD D -> VD qs) => ConstFreeUnit) (fun (qv : Nat) (qs : Sk) (qF : VEnvD D -> VD qs) => ConstFreeUnit) e s F";

pub(super) fn src_sval_lam_inv() -> String {
    let motive = "(fun (qD : Nat -> Sk) (qe : KExpr) (qs : Sk) (qh : WK qD qe qs) => r15_svalLamT qD C qe qs (sval qD qe qs qh))";
    let m_var = "(fun (qD : Nat -> Sk) (qi : Nat) => ConstFreeUnit.triv)";
    let m_sort = "(fun (qD : Nat -> Sk) (qn : Level) => ConstFreeUnit.triv)";
    let m_pi = "(fun (qD : Nat -> Sk) (qA : KExpr) (qB : KExpr) (qsA : Sk) (qsB : Sk) (qhA : WK qD qA qsA) (qhB : WK (skcons (domSk qsA) qD) qB qsB) (qihA : r15_svalLamT qD C qA qsA (sval qD qA qsA qhA)) (qihB : r15_svalLamT (skcons (domSk qsA) qD) C qB qsB (sval (skcons (domSk qsA) qD) qB qsB qhB)) => ConstFreeUnit.triv)";
    let dsa = "(skcons (domSk qsA) qD)";
    let cont = format!("(zk : forall (zhb : WK {dsa} qb qc), (forall (zr : VEnvD qD) (zx : VD (domSk qsA)), @Eq (VD qc) (sval qD (KExpr.lam qA qb) (Sk.arr (domSk qsA) qc) (WK.lam qD qA qb qsA qc qhA qhb) zr zx) (sval {dsa} qb qc zhb (vconsD (domSk qsA) qD zx zr))) -> C)");
    let m_lam = format!(
        "(fun (qD : Nat -> Sk) (qA : KExpr) (qb : KExpr) (qsA : Sk) (qc : Sk) (qhA : WK qD qA qsA) (qhb : WK {dsa} qb qc) (qihA : r15_svalLamT qD C qA qsA (sval qD qA qsA qhA)) (qihb : r15_svalLamT {dsa} C qb qc (sval {dsa} qb qc qhb)) {cont} => zk qhb (fun (zr : VEnvD qD) (zx : VD (domSk qsA)) => @Eq.refl (VD qc) (sval {dsa} qb qc qhb (vconsD (domSk qsA) qD zx zr))))"
    );
    let m_app = "(fun (qD : Nat -> Sk) (qf : KExpr) (qa : KExpr) (qd : Sk) (qcc : Sk) (qhf : WK qD qf (Sk.arr qd qcc)) (qha : WK qD qa qd) (qihf : r15_svalLamT qD C qf (Sk.arr qd qcc) (sval qD qf (Sk.arr qd qcc) qhf)) (qiha : r15_svalLamT qD C qa qd (sval qD qa qd qha)) => ConstFreeUnit.triv)";
    format!(
        "def r15_sval_lam_inv (D : Nat -> Sk) (C : Type) (e : KExpr) (s : Sk) (h : WK D e s) : r15_svalLamT D C e s (sval D e s h) := @WK.rec {motive} {m_var} {m_sort} {m_pi} {m_lam} {m_app} D e s h"
    )
}

// ================================================================
// Group D — SUBJECT REDUCTION FOR SHAPES.
// ================================================================

/// **`wk_step`** — the constant this rung exists for. `WK D e s` and one
/// `whnf_step e e2` give `WK D e2 s`: the shape is PRESERVED, not merely
/// related. Registered as a `def` so a later rung can reduce through it.
///
/// It is a `WK.rec` whose every arm calls the single computed step inversion:
/// `bvar` and `sort` because no rule fires there at all, `pi`/`lam`/`app`
/// because the congruence arms hand back the stepped component and the
/// induction hypothesis re-types it at the SAME shape. The head-beta arm is the
/// only one that changes the term's shape derivation structurally, and it is
/// exactly R14's `wk_inst`.
#[allow(clippy::too_many_lines)]
pub(super) fn src_wk_step() -> String {
    let mot = "(fun (qD : Nat -> Sk) (qe : KExpr) (qs : Sk) (qh : WK qD qe qs) => forall (qe2 : KExpr), whnf_step qe qe2 -> WK qD qe2 qs)";
    let m_var = format!(
        "(fun (qD : Nat -> Sk) (qi : Nat) (qe2 : KExpr) (qst : whnf_step (KExpr.bvar qi) qe2) => r15_whnf_stepT_inv (WK qD qe2 (qD qi)) (KExpr.bvar qi) qe2 {HF_REFL} qst)"
    );
    let m_sort = format!(
        "(fun (qD : Nat -> Sk) (qn : Level) (qe2 : KExpr) (qst : whnf_step (KExpr.sort qn) qe2) => r15_whnf_stepT_inv (WK qD qe2 (Sk.kd Sk.ty)) (KExpr.sort qn) qe2 {HF_REFL} qst)"
    );

    // pi
    let ihp_a = "(qihA : forall (qz : KExpr), whnf_step qA qz -> WK qD qz qsA)";
    let ihp_b =
        "(qihB : forall (qz : KExpr), whnf_step qB qz -> WK (skcons (domSk qsA) qD) qz qsB)";
    let p1 = "(fun (zy : KExpr) (zst : beta_reduces qA zy) (zeq : @Eq KExpr qe2 (KExpr.pi zy qB)) => r14_wkCastT qD (KExpr.pi zy qB) qe2 (piShape qsA qsB) (@Eq.symm KExpr qe2 (KExpr.pi zy qB) zeq) (WK.pi qD zy qB qsA qsB (qihA zy (@whnf_step.beta qA zy zst)) qhB))";
    let p2 = "(fun (zy : KExpr) (zst : beta_reduces qB zy) (zeq : @Eq KExpr qe2 (KExpr.pi qA zy)) => r14_wkCastT qD (KExpr.pi qA zy) qe2 (piShape qsA qsB) (@Eq.symm KExpr qe2 (KExpr.pi qA zy) zeq) (WK.pi qD qA zy qsA qsB qhA (qihB zy (@whnf_step.beta qB zy zst))))";
    let m_pi = format!(
        "(fun (qD : Nat -> Sk) (qA : KExpr) (qB : KExpr) (qsA : Sk) (qsB : Sk) (qhA : WK qD qA qsA) (qhB : WK (skcons (domSk qsA) qD) qB qsB) {ihp_a} {ihp_b} (qe2 : KExpr) (qst : whnf_step (KExpr.pi qA qB) qe2) => r15_whnf_stepT_inv (WK qD qe2 (piShape qsA qsB)) (KExpr.pi qA qB) qe2 {HF_REFL} qst {p1} {p2})"
    );

    // lam
    let ihl_a = "(qihA : forall (qz : KExpr), whnf_step qA qz -> WK qD qz qsA)";
    let ihl_b = "(qihb : forall (qz : KExpr), whnf_step qb qz -> WK (skcons (domSk qsA) qD) qz qc)";
    let l1 = "(fun (zy : KExpr) (zst : beta_reduces qA zy) (zeq : @Eq KExpr qe2 (KExpr.lam zy qb)) => r14_wkCastT qD (KExpr.lam zy qb) qe2 (Sk.arr (domSk qsA) qc) (@Eq.symm KExpr qe2 (KExpr.lam zy qb) zeq) (WK.lam qD zy qb qsA qc (qihA zy (@whnf_step.beta qA zy zst)) qhb))";
    let l2 = "(fun (zy : KExpr) (zst : beta_reduces qb zy) (zeq : @Eq KExpr qe2 (KExpr.lam qA zy)) => r14_wkCastT qD (KExpr.lam qA zy) qe2 (Sk.arr (domSk qsA) qc) (@Eq.symm KExpr qe2 (KExpr.lam qA zy) zeq) (WK.lam qD qA zy qsA qc qhA (qihb zy (@whnf_step.beta qb zy zst))))";
    let m_lam = format!(
        "(fun (qD : Nat -> Sk) (qA : KExpr) (qb : KExpr) (qsA : Sk) (qc : Sk) (qhA : WK qD qA qsA) (qhb : WK (skcons (domSk qsA) qD) qb qc) {ihl_a} {ihl_b} (qe2 : KExpr) (qst : whnf_step (KExpr.lam qA qb) qe2) => r15_whnf_stepT_inv (WK qD qe2 (Sk.arr (domSk qsA) qc)) (KExpr.lam qA qb) qe2 {HF_REFL} qst {l1} {l2})"
    );

    // app
    let iha_f = "(qihf : forall (qz : KExpr), whnf_step qf qz -> WK qD qz (Sk.arr qd qcc))";
    let iha_a = "(qiha : forall (qz : KExpr), whnf_step qa qz -> WK qD qz qd)";
    let hf = "(headFree_app qf qa (r15_headFree_wk qD qf (Sk.arr qd qcc) qhf))";
    let a1 = "(fun (zA : KExpr) (zb : KExpr) (zlam : @Eq KExpr qf (KExpr.lam zA zb)) (zcon : @Eq KExpr qe2 (instantiate zb qa)) => r15_wk_lam_inv qD (WK qD qe2 qcc) (KExpr.lam zA zb) (Sk.arr qd qcc) (r14_wkCastT qD qf (KExpr.lam zA zb) (Sk.arr qd qcc) zlam qhf) (fun (zhb : WK (skcons qd qD) zb qcc) => r14_wkCastT qD (instantiate zb qa) qe2 qcc (@Eq.symm KExpr qe2 (instantiate zb qa) zcon) (wk_inst qD zb qa qd qcc zhb qha)))";
    let a2 = "(fun (zy : KExpr) (zst : beta_reduces qf zy) (zeq : @Eq KExpr qe2 (KExpr.app zy qa)) => r14_wkCastT qD (KExpr.app zy qa) qe2 qcc (@Eq.symm KExpr qe2 (KExpr.app zy qa) zeq) (WK.app qD zy qa qd qcc (qihf zy (@whnf_step.beta qf zy zst)) qha))";
    let a3 = "(fun (zy : KExpr) (zst : beta_reduces qa zy) (zeq : @Eq KExpr qe2 (KExpr.app qf zy)) => r14_wkCastT qD (KExpr.app qf zy) qe2 qcc (@Eq.symm KExpr qe2 (KExpr.app qf zy) zeq) (WK.app qD qf zy qd qcc qhf (qiha zy (@whnf_step.beta qa zy zst))))";
    let m_app = format!(
        "(fun (qD : Nat -> Sk) (qf : KExpr) (qa : KExpr) (qd : Sk) (qcc : Sk) (qhf : WK qD qf (Sk.arr qd qcc)) (qha : WK qD qa qd) {iha_f} {iha_a} (qe2 : KExpr) (qst : whnf_step (KExpr.app qf qa) qe2) => r15_whnf_stepT_inv (WK qD qe2 qcc) (KExpr.app qf qa) qe2 {hf} qst {a1} {a2} {a3})"
    );

    format!(
        "def wk_step (D : Nat -> Sk) (e : KExpr) (s : Sk) (h : WK D e s) (e2 : KExpr) (st : whnf_step e e2) : WK D e2 s := @WK.rec {mot} {m_var} {m_sort} {m_pi} {m_lam} {m_app} D e s h e2 st"
    )
}

// ================================================================
// Group E — the six NAMED arms of the corpus's `val_step`, each stated at
// GIVEN derivations. These are the arms R14 recorded as not landed; they need
// no inversion at all, only R13/R14's congruence engine.
// ================================================================

const VB_JUNK: &str =
    "(sval (skcons (domSk sA) D) B sB hB (vconsD (domSk sA) D (junkD (domSk sA)) r))";

pub(super) fn ty_val_step_pia() -> String {
    "forall (D : Nat -> Sk) (A : KExpr) (A2 : KExpr) (B : KExpr) (sA : Sk) (sB : Sk) (hA : WK D A sA) (hA2 : WK D A2 sA) (hB : WK (skcons (domSk sA) D) B sB) (r : VEnvD D), @Eq (VD sA) (sval D A2 sA hA2 r) (sval D A sA hA r) -> @Eq (VD (piShape sA sB)) (sval D (KExpr.pi A2 B) (piShape sA sB) (WK.pi D A2 B sA sB hA2 hB) r) (sval D (KExpr.pi A B) (piShape sA sB) (WK.pi D A B sA sB hA hB) r)".to_string()
}
pub(super) fn val_val_step_pia() -> String {
    format!("fun (D : Nat -> Sk) (A : KExpr) (A2 : KExpr) (B : KExpr) (sA : Sk) (sB : Sk) (hA : WK D A sA) (hA2 : WK D A2 sA) (hB : WK (skcons (domSk sA) D) B sB) (r : VEnvD D) (hv : @Eq (VD sA) (sval D A2 sA hA2 r) (sval D A sA hA r)) => r14_sval_pi_congr sA sB (sval D A2 sA hA2 r) (sval D A sA hA r) {VB_JUNK} {VB_JUNK} hv (@Eq.refl (VD sB) {VB_JUNK})")
}

pub(super) fn ty_val_step_pib() -> String {
    "forall (D : Nat -> Sk) (A : KExpr) (B : KExpr) (B2 : KExpr) (sA : Sk) (sB : Sk) (hA : WK D A sA) (hB : WK (skcons (domSk sA) D) B sB) (hB2 : WK (skcons (domSk sA) D) B2 sB) (r : VEnvD D), (forall (zr : VEnvD (skcons (domSk sA) D)), @Eq (VD sB) (sval (skcons (domSk sA) D) B2 sB hB2 zr) (sval (skcons (domSk sA) D) B sB hB zr)) -> @Eq (VD (piShape sA sB)) (sval D (KExpr.pi A B2) (piShape sA sB) (WK.pi D A B2 sA sB hA hB2) r) (sval D (KExpr.pi A B) (piShape sA sB) (WK.pi D A B sA sB hA hB) r)".to_string()
}
pub(super) fn val_val_step_pib() -> String {
    let jenv = "(vconsD (domSk sA) D (junkD (domSk sA)) r)";
    let vb2 = format!("(sval (skcons (domSk sA) D) B2 sB hB2 {jenv})");
    let va = "(sval D A sA hA r)";
    format!("fun (D : Nat -> Sk) (A : KExpr) (B : KExpr) (B2 : KExpr) (sA : Sk) (sB : Sk) (hA : WK D A sA) (hB : WK (skcons (domSk sA) D) B sB) (hB2 : WK (skcons (domSk sA) D) B2 sB) (r : VEnvD D) (hv : forall (zr : VEnvD (skcons (domSk sA) D)), @Eq (VD sB) (sval (skcons (domSk sA) D) B2 sB hB2 zr) (sval (skcons (domSk sA) D) B sB hB zr)) => r14_sval_pi_congr sA sB {va} {va} {vb2} {VB_JUNK} (@Eq.refl (VD sA) {va}) (hv {jenv})")
}

/// **THE ANNOTATION IS SEMANTICALLY INERT.** The `lam` clause of `sval` never
/// mentions the domain annotation's value, so this arm needs no hypothesis at
/// all: it is `Eq.refl`. The corpus's `lamA` case carries a `val_step`
/// hypothesis it does not use either; here the fact is machine-visible.
pub(super) fn ty_val_step_lama() -> String {
    "forall (D : Nat -> Sk) (A : KExpr) (A2 : KExpr) (b : KExpr) (sA : Sk) (c : Sk) (hA : WK D A sA) (hA2 : WK D A2 sA) (hb : WK (skcons (domSk sA) D) b c) (r : VEnvD D), @Eq (VD (Sk.arr (domSk sA) c)) (sval D (KExpr.lam A2 b) (Sk.arr (domSk sA) c) (WK.lam D A2 b sA c hA2 hb) r) (sval D (KExpr.lam A b) (Sk.arr (domSk sA) c) (WK.lam D A b sA c hA hb) r)".to_string()
}
pub(super) fn val_val_step_lama() -> String {
    "fun (D : Nat -> Sk) (A : KExpr) (A2 : KExpr) (b : KExpr) (sA : Sk) (c : Sk) (hA : WK D A sA) (hA2 : WK D A2 sA) (hb : WK (skcons (domSk sA) D) b c) (r : VEnvD D) => @Eq.refl (VD (Sk.arr (domSk sA) c)) (sval D (KExpr.lam A b) (Sk.arr (domSk sA) c) (WK.lam D A b sA c hA hb) r)".to_string()
}

pub(super) fn ty_val_step_lamb() -> String {
    "forall (D : Nat -> Sk) (A : KExpr) (b : KExpr) (b2 : KExpr) (sA : Sk) (c : Sk) (hA : WK D A sA) (hb : WK (skcons (domSk sA) D) b c) (hb2 : WK (skcons (domSk sA) D) b2 c) (r : VEnvD D), (forall (zr : VEnvD (skcons (domSk sA) D)), @Eq (VD c) (sval (skcons (domSk sA) D) b2 c hb2 zr) (sval (skcons (domSk sA) D) b c hb zr)) -> @Eq (VD (Sk.arr (domSk sA) c)) (sval D (KExpr.lam A b2) (Sk.arr (domSk sA) c) (WK.lam D A b2 sA c hA hb2) r) (sval D (KExpr.lam A b) (Sk.arr (domSk sA) c) (WK.lam D A b sA c hA hb) r)".to_string()
}
pub(super) fn val_val_step_lamb() -> String {
    let f = "(sval D (KExpr.lam A b2) (Sk.arr (domSk sA) c) (WK.lam D A b2 sA c hA hb2) r)";
    let g = "(sval D (KExpr.lam A b) (Sk.arr (domSk sA) c) (WK.lam D A b sA c hA hb) r)";
    format!("fun (D : Nat -> Sk) (A : KExpr) (b : KExpr) (b2 : KExpr) (sA : Sk) (c : Sk) (hA : WK D A sA) (hb : WK (skcons (domSk sA) D) b c) (hb2 : WK (skcons (domSk sA) D) b2 c) (r : VEnvD D) (hv : forall (zr : VEnvD (skcons (domSk sA) D)), @Eq (VD c) (sval (skcons (domSk sA) D) b2 c hb2 zr) (sval (skcons (domSk sA) D) b c hb zr)) => r13_vd_arr_funext (domSk sA) c {f} {g} (fun (zx : VD (domSk sA)) => hv (vconsD (domSk sA) D zx r))")
}

pub(super) fn ty_val_step_appl() -> String {
    "forall (D : Nat -> Sk) (f : KExpr) (f2 : KExpr) (a : KExpr) (d : Sk) (c : Sk) (hf : WK D f (Sk.arr d c)) (hf2 : WK D f2 (Sk.arr d c)) (ha : WK D a d) (r : VEnvD D), @Eq (VD (Sk.arr d c)) (sval D f2 (Sk.arr d c) hf2 r) (sval D f (Sk.arr d c) hf r) -> @Eq (VD c) (sval D (KExpr.app f2 a) c (WK.app D f2 a d c hf2 ha) r) (sval D (KExpr.app f a) c (WK.app D f a d c hf ha) r)".to_string()
}
pub(super) fn val_val_step_appl() -> String {
    let x = "(sval D a d ha r)";
    format!("fun (D : Nat -> Sk) (f : KExpr) (f2 : KExpr) (a : KExpr) (d : Sk) (c : Sk) (hf : WK D f (Sk.arr d c)) (hf2 : WK D f2 (Sk.arr d c)) (ha : WK D a d) (r : VEnvD D) (hv : @Eq (VD (Sk.arr d c)) (sval D f2 (Sk.arr d c) hf2 r) (sval D f (Sk.arr d c) hf r)) => r14_vapply_congr d c (sval D f2 (Sk.arr d c) hf2 r) (sval D f (Sk.arr d c) hf r) {x} {x} hv (@Eq.refl (VD d) {x})")
}

pub(super) fn ty_val_step_appr() -> String {
    "forall (D : Nat -> Sk) (f : KExpr) (a : KExpr) (a2 : KExpr) (d : Sk) (c : Sk) (hf : WK D f (Sk.arr d c)) (ha : WK D a d) (ha2 : WK D a2 d) (r : VEnvD D), @Eq (VD d) (sval D a2 d ha2 r) (sval D a d ha r) -> @Eq (VD c) (sval D (KExpr.app f a2) c (WK.app D f a2 d c hf ha2) r) (sval D (KExpr.app f a) c (WK.app D f a d c hf ha) r)".to_string()
}
pub(super) fn val_val_step_appr() -> String {
    let ff = "(sval D f (Sk.arr d c) hf r)";
    format!("fun (D : Nat -> Sk) (f : KExpr) (a : KExpr) (a2 : KExpr) (d : Sk) (c : Sk) (hf : WK D f (Sk.arr d c)) (ha : WK D a d) (ha2 : WK D a2 d) (r : VEnvD D) (hv : @Eq (VD d) (sval D a2 d ha2 r) (sval D a d ha r)) => r14_vapply_congr d c {ff} {ff} (sval D a2 d ha2 r) (sval D a d ha r) (@Eq.refl (VD (Sk.arr d c)) {ff}) hv")
}

// ================================================================
// Group F — THE FUSED THEOREM. Subject reduction AND semantic invariance in one
// recursion, which is the only way to have both: a CPS inversion is opaque in
// its result, so `sval` at `wk_step`'s output does not reduce and a SEPARATE
// semantic lemma about it is unstatable without derivation irrelevance.
// ================================================================

/// The continuation of the fused statement, at a shape environment, a reduct, a
/// shape and the derivation being stepped.
fn sem_k(d: &str, e2: &str, s: &str, src: &str, c: &str) -> String {
    format!("forall (zh2 : WK {d} {e2} {s}), (forall (zr : VEnvD {d}), @Eq (VD {s}) (sval {d} {e2} {s} zh2 zr) ({src} zr)) -> {c}")
}

pub(super) fn ty_val_step_sem() -> String {
    format!(
        "forall (D : Nat -> Sk) (e : KExpr) (s : Sk) (h : WK D e s) (e2 : KExpr) (st : whnf_step e e2) (C : Type), ({}) -> C",
        sem_k("D", "e2", "s", "(sval D e s h)", "C")
    )
}

#[allow(clippy::too_many_lines)]
pub(super) fn val_val_step_sem() -> String {
    let mot = format!(
        "(fun (qD : Nat -> Sk) (qe : KExpr) (qs : Sk) (qh : WK qD qe qs) => forall (qe2 : KExpr) (qst : whnf_step qe qe2) (qC : Type), ({}) -> qC)",
        sem_k("qD", "qe2", "qs", "(sval qD qe qs qh)", "qC")
    );

    let m_var = format!(
        "(fun (qD : Nat -> Sk) (qi : Nat) (qe2 : KExpr) (qst : whnf_step (KExpr.bvar qi) qe2) (qC : Type) (qk : {}) => r15_whnf_stepT_inv qC (KExpr.bvar qi) qe2 {HF_REFL} qst)",
        sem_k("qD", "qe2", "(qD qi)", "(sval qD (KExpr.bvar qi) (qD qi) (WK.var qD qi))", "qC")
    );
    let m_sort = format!(
        "(fun (qD : Nat -> Sk) (qn : Level) (qe2 : KExpr) (qst : whnf_step (KExpr.sort qn) qe2) (qC : Type) (qk : {}) => r15_whnf_stepT_inv qC (KExpr.sort qn) qe2 {HF_REFL} qst)",
        sem_k("qD", "qe2", "(Sk.kd Sk.ty)", "(sval qD (KExpr.sort qn) (Sk.kd Sk.ty) (WK.sort qD qn))", "qC")
    );

    // ---- pi ----
    let dsa = "(skcons (domSk qsA) qD)";
    let pshape = "(piShape qsA qsB)";
    let pderiv = "(WK.pi qD qA qB qsA qsB qhA qhB)";
    let ih_a = format!(
        "(qihA : forall (qz : KExpr) (qzs : whnf_step qA qz) (qzC : Type), ({}) -> qzC)",
        sem_k("qD", "qz", "qsA", "(sval qD qA qsA qhA)", "qzC")
    );
    let ih_pb = format!(
        "(qihB : forall (qz : KExpr) (qzs : whnf_step qB qz) (qzC : Type), ({}) -> qzC)",
        sem_k(dsa, "qz", "qsB", &format!("(sval {dsa} qB qsB qhB)"), "qzC")
    );
    let kpi = sem_k(
        "qD",
        "qe2",
        pshape,
        &format!("(sval qD (KExpr.pi qA qB) {pshape} {pderiv})"),
        "qC",
    );
    let jenv = "(vconsD (domSk qsA) qD (junkD (domSk qsA)) zr)";
    let vb = format!("(sval {dsa} qB qsB qhB {jenv})");
    // pi_dom
    let nd1 = "(WK.pi qD zy qB qsA qsB zh2 qhB)";
    let cast1 = format!("(r14_wkCastT qD (KExpr.pi zy qB) qe2 {pshape} (@Eq.symm KExpr qe2 (KExpr.pi zy qB) zeq) {nd1})");
    let lhs1 = format!("(sval qD qe2 {pshape} {cast1} zr)");
    let mid1 = format!("(sval qD (KExpr.pi zy qB) {pshape} {nd1} zr)");
    let rhs1 = format!("(sval qD (KExpr.pi qA qB) {pshape} {pderiv} zr)");
    let step1 = format!("(r14_sval_cast_term qD (KExpr.pi zy qB) qe2 {pshape} (@Eq.symm KExpr qe2 (KExpr.pi zy qB) zeq) {nd1} zr)");
    let cong1 = format!("(r14_sval_pi_congr qsA qsB (sval qD zy qsA zh2 zr) (sval qD qA qsA qhA zr) {vb} {vb} (zhv zr) (@Eq.refl (VD qsB) {vb}))");
    let p1 = format!(
        "(fun (zy : KExpr) (zst : beta_reduces qA zy) (zeq : @Eq KExpr qe2 (KExpr.pi zy qB)) => qihA zy (@whnf_step.beta qA zy zst) qC (fun (zh2 : WK qD zy qsA) (zhv : forall (zr : VEnvD qD), @Eq (VD qsA) (sval qD zy qsA zh2 zr) (sval qD qA qsA qhA zr)) => qk {cast1} (fun (zr : VEnvD qD) => @Eq.trans (VD {pshape}) {lhs1} {mid1} {rhs1} {step1} {cong1})))"
    );
    // pi_cod
    let nd2 = "(WK.pi qD qA zy qsA qsB qhA zh2)";
    let cast2 = format!("(r14_wkCastT qD (KExpr.pi qA zy) qe2 {pshape} (@Eq.symm KExpr qe2 (KExpr.pi qA zy) zeq) {nd2})");
    let lhs2 = format!("(sval qD qe2 {pshape} {cast2} zr)");
    let mid2 = format!("(sval qD (KExpr.pi qA zy) {pshape} {nd2} zr)");
    let step2 = format!("(r14_sval_cast_term qD (KExpr.pi qA zy) qe2 {pshape} (@Eq.symm KExpr qe2 (KExpr.pi qA zy) zeq) {nd2} zr)");
    let va = "(sval qD qA qsA qhA zr)";
    let vb2 = format!("(sval {dsa} zy qsB zh2 {jenv})");
    let cong2 = format!(
        "(r14_sval_pi_congr qsA qsB {va} {va} {vb2} {vb} (@Eq.refl (VD qsA) {va}) (zhv {jenv}))"
    );
    let p2 = format!(
        "(fun (zy : KExpr) (zst : beta_reduces qB zy) (zeq : @Eq KExpr qe2 (KExpr.pi qA zy)) => qihB zy (@whnf_step.beta qB zy zst) qC (fun (zh2 : WK {dsa} zy qsB) (zhv : forall (zr : VEnvD {dsa}), @Eq (VD qsB) (sval {dsa} zy qsB zh2 zr) (sval {dsa} qB qsB qhB zr)) => qk {cast2} (fun (zr : VEnvD qD) => @Eq.trans (VD {pshape}) {lhs2} {mid2} {rhs1} {step2} {cong2})))"
    );
    let m_pi = format!(
        "(fun (qD : Nat -> Sk) (qA : KExpr) (qB : KExpr) (qsA : Sk) (qsB : Sk) (qhA : WK qD qA qsA) (qhB : WK {dsa} qB qsB) {ih_a} {ih_pb} (qe2 : KExpr) (qst : whnf_step (KExpr.pi qA qB) qe2) (qC : Type) (qk : {kpi}) => r15_whnf_stepT_inv qC (KExpr.pi qA qB) qe2 {HF_REFL} qst {p1} {p2})"
    );

    // ---- lam ----
    let lshape = "(Sk.arr (domSk qsA) qc)";
    let lderiv = "(WK.lam qD qA qb qsA qc qhA qhb)";
    let ih_la = format!(
        "(qihA : forall (qz : KExpr) (qzs : whnf_step qA qz) (qzC : Type), ({}) -> qzC)",
        sem_k("qD", "qz", "qsA", "(sval qD qA qsA qhA)", "qzC")
    );
    let ih_lb = format!(
        "(qihb : forall (qz : KExpr) (qzs : whnf_step qb qz) (qzC : Type), ({}) -> qzC)",
        sem_k(dsa, "qz", "qc", &format!("(sval {dsa} qb qc qhb)"), "qzC")
    );
    let klam = sem_k(
        "qD",
        "qe2",
        lshape,
        &format!("(sval qD (KExpr.lam qA qb) {lshape} {lderiv})"),
        "qC",
    );
    let lnd1 = "(WK.lam qD zy qb qsA qc zh2 qhb)";
    let lcast1 = format!("(r14_wkCastT qD (KExpr.lam zy qb) qe2 {lshape} (@Eq.symm KExpr qe2 (KExpr.lam zy qb) zeq) {lnd1})");
    let llhs1 = format!("(sval qD qe2 {lshape} {lcast1} zr)");
    let lmid1 = format!("(sval qD (KExpr.lam zy qb) {lshape} {lnd1} zr)");
    let lrhs = format!("(sval qD (KExpr.lam qA qb) {lshape} {lderiv} zr)");
    let lstep1 = format!("(r14_sval_cast_term qD (KExpr.lam zy qb) qe2 {lshape} (@Eq.symm KExpr qe2 (KExpr.lam zy qb) zeq) {lnd1} zr)");
    let l1 = format!(
        "(fun (zy : KExpr) (zst : beta_reduces qA zy) (zeq : @Eq KExpr qe2 (KExpr.lam zy qb)) => qihA zy (@whnf_step.beta qA zy zst) qC (fun (zh2 : WK qD zy qsA) (zhv : forall (zr : VEnvD qD), @Eq (VD qsA) (sval qD zy qsA zh2 zr) (sval qD qA qsA qhA zr)) => qk {lcast1} (fun (zr : VEnvD qD) => @Eq.trans (VD {lshape}) {llhs1} {lmid1} {lrhs} {lstep1} (@Eq.refl (VD {lshape}) {lrhs}))))"
    );
    let lnd2 = "(WK.lam qD qA zy qsA qc qhA zh2)";
    let lcast2 = format!("(r14_wkCastT qD (KExpr.lam qA zy) qe2 {lshape} (@Eq.symm KExpr qe2 (KExpr.lam qA zy) zeq) {lnd2})");
    let llhs2 = format!("(sval qD qe2 {lshape} {lcast2} zr)");
    let lmid2 = format!("(sval qD (KExpr.lam qA zy) {lshape} {lnd2} zr)");
    let lstep2 = format!("(r14_sval_cast_term qD (KExpr.lam qA zy) qe2 {lshape} (@Eq.symm KExpr qe2 (KExpr.lam qA zy) zeq) {lnd2} zr)");
    let lfun = format!("(r13_vd_arr_funext (domSk qsA) qc {lmid2} {lrhs} (fun (zx : VD (domSk qsA)) => zhv (vconsD (domSk qsA) qD zx zr)))");
    let l2 = format!(
        "(fun (zy : KExpr) (zst : beta_reduces qb zy) (zeq : @Eq KExpr qe2 (KExpr.lam qA zy)) => qihb zy (@whnf_step.beta qb zy zst) qC (fun (zh2 : WK {dsa} zy qc) (zhv : forall (zr : VEnvD {dsa}), @Eq (VD qc) (sval {dsa} zy qc zh2 zr) (sval {dsa} qb qc qhb zr)) => qk {lcast2} (fun (zr : VEnvD qD) => @Eq.trans (VD {lshape}) {llhs2} {lmid2} {lrhs} {lstep2} {lfun})))"
    );
    let m_lam = format!(
        "(fun (qD : Nat -> Sk) (qA : KExpr) (qb : KExpr) (qsA : Sk) (qc : Sk) (qhA : WK qD qA qsA) (qhb : WK {dsa} qb qc) {ih_la} {ih_lb} (qe2 : KExpr) (qst : whnf_step (KExpr.lam qA qb) qe2) (qC : Type) (qk : {klam}) => r15_whnf_stepT_inv qC (KExpr.lam qA qb) qe2 {HF_REFL} qst {l1} {l2})"
    );

    // ---- app ----
    let aderiv = "(WK.app qD qf qa qd qcc qhf qha)";
    let ih_f = format!(
        "(qihf : forall (qz : KExpr) (qzs : whnf_step qf qz) (qzC : Type), ({}) -> qzC)",
        sem_k(
            "qD",
            "qz",
            "(Sk.arr qd qcc)",
            "(sval qD qf (Sk.arr qd qcc) qhf)",
            "qzC"
        )
    );
    let ih_ar = format!(
        "(qiha : forall (qz : KExpr) (qzs : whnf_step qa qz) (qzC : Type), ({}) -> qzC)",
        sem_k("qD", "qz", "qd", "(sval qD qa qd qha)", "qzC")
    );
    let kapp = sem_k(
        "qD",
        "qe2",
        "qcc",
        &format!("(sval qD (KExpr.app qf qa) qcc {aderiv})"),
        "qC",
    );
    let hf = "(headFree_app qf qa (r15_headFree_wk qD qf (Sk.arr qd qcc) qhf))";
    let xv = "(sval qD qa qd qha zr)";
    let arhs = format!("(sval qD (KExpr.app qf qa) qcc {aderiv} zr)");
    // beta
    let hfl = "(r14_wkCastT qD qf (KExpr.lam zA zb) (Sk.arr qd qcc) zlam qhf)";
    let hinst = "(wk_inst qD zb qa qd qcc zhb qha)";
    let h2b = format!("(r14_wkCastT qD (instantiate zb qa) qe2 qcc (@Eq.symm KExpr qe2 (instantiate zb qa) zcon) {hinst})");
    let bx1 = format!("(sval qD qe2 qcc {h2b} zr)");
    let bx2 = format!("(sval qD (instantiate zb qa) qcc {hinst} zr)");
    let bx3 = format!("(sval (skcons qd qD) zb qcc zhb (vconsD qd qD {xv} zr))");
    let bx4 = format!("(sval qD (KExpr.lam zA zb) (Sk.arr qd qcc) {hfl} zr {xv})");
    let bs1 = format!("(r14_sval_cast_term qD (instantiate zb qa) qe2 qcc (@Eq.symm KExpr qe2 (instantiate zb qa) zcon) {hinst} zr)");
    let bs2 = "(r14_val_inst qD zb qa qd qcc zhb qha zr)";
    let bs3 = format!("(@Eq.symm (VD qcc) {bx4} {bx3} (zsem zr {xv}))");
    let bs4 = format!("(@Eq.cong (VD (Sk.arr qd qcc)) (VD qcc) (fun (zF : VD (Sk.arr qd qcc)) => zF {xv}) (sval qD (KExpr.lam zA zb) (Sk.arr qd qcc) {hfl} zr) (sval qD qf (Sk.arr qd qcc) qhf zr) (r14_sval_cast_term qD qf (KExpr.lam zA zb) (Sk.arr qd qcc) zlam qhf zr))");
    let bchain = format!("(@Eq.trans (VD qcc) {bx1} {bx3} {arhs} (@Eq.trans (VD qcc) {bx1} {bx2} {bx3} {bs1} {bs2}) (@Eq.trans (VD qcc) {bx3} {bx4} {arhs} {bs3} {bs4}))");
    let semcont = format!("(zsem : forall (zr : VEnvD qD) (zx : VD qd), @Eq (VD qcc) (sval qD (KExpr.lam zA zb) (Sk.arr qd qcc) {hfl} zr zx) (sval (skcons qd qD) zb qcc zhb (vconsD qd qD zx zr)))");
    let a1 = format!(
        "(fun (zA : KExpr) (zb : KExpr) (zlam : @Eq KExpr qf (KExpr.lam zA zb)) (zcon : @Eq KExpr qe2 (instantiate zb qa)) => r15_sval_lam_inv qD qC (KExpr.lam zA zb) (Sk.arr qd qcc) {hfl} (fun (zhb : WK (skcons qd qD) zb qcc) {semcont} => qk {h2b} (fun (zr : VEnvD qD) => {bchain})))"
    );
    // app_left
    let and2 = "(WK.app qD zy qa qd qcc zh2 qha)";
    let acast2 = format!("(r14_wkCastT qD (KExpr.app zy qa) qe2 qcc (@Eq.symm KExpr qe2 (KExpr.app zy qa) zeq) {and2})");
    let al1 = format!("(sval qD qe2 qcc {acast2} zr)");
    let al2 = format!("(sval qD (KExpr.app zy qa) qcc {and2} zr)");
    let as1 = format!("(r14_sval_cast_term qD (KExpr.app zy qa) qe2 qcc (@Eq.symm KExpr qe2 (KExpr.app zy qa) zeq) {and2} zr)");
    let ac1 = format!("(r14_vapply_congr qd qcc (sval qD zy (Sk.arr qd qcc) zh2 zr) (sval qD qf (Sk.arr qd qcc) qhf zr) {xv} {xv} (zhv zr) (@Eq.refl (VD qd) {xv}))");
    let a2 = format!(
        "(fun (zy : KExpr) (zst : beta_reduces qf zy) (zeq : @Eq KExpr qe2 (KExpr.app zy qa)) => qihf zy (@whnf_step.beta qf zy zst) qC (fun (zh2 : WK qD zy (Sk.arr qd qcc)) (zhv : forall (zr : VEnvD qD), @Eq (VD (Sk.arr qd qcc)) (sval qD zy (Sk.arr qd qcc) zh2 zr) (sval qD qf (Sk.arr qd qcc) qhf zr)) => qk {acast2} (fun (zr : VEnvD qD) => @Eq.trans (VD qcc) {al1} {al2} {arhs} {as1} {ac1})))"
    );
    // app_right
    let and3 = "(WK.app qD qf zy qd qcc qhf zh2)";
    let acast3 = format!("(r14_wkCastT qD (KExpr.app qf zy) qe2 qcc (@Eq.symm KExpr qe2 (KExpr.app qf zy) zeq) {and3})");
    let ar1 = format!("(sval qD qe2 qcc {acast3} zr)");
    let ar2 = format!("(sval qD (KExpr.app qf zy) qcc {and3} zr)");
    let as2 = format!("(r14_sval_cast_term qD (KExpr.app qf zy) qe2 qcc (@Eq.symm KExpr qe2 (KExpr.app qf zy) zeq) {and3} zr)");
    let ffv = "(sval qD qf (Sk.arr qd qcc) qhf zr)";
    let ac2 = format!("(r14_vapply_congr qd qcc {ffv} {ffv} (sval qD zy qd zh2 zr) {xv} (@Eq.refl (VD (Sk.arr qd qcc)) {ffv}) (zhv zr))");
    let a3 = format!(
        "(fun (zy : KExpr) (zst : beta_reduces qa zy) (zeq : @Eq KExpr qe2 (KExpr.app qf zy)) => qiha zy (@whnf_step.beta qa zy zst) qC (fun (zh2 : WK qD zy qd) (zhv : forall (zr : VEnvD qD), @Eq (VD qd) (sval qD zy qd zh2 zr) (sval qD qa qd qha zr)) => qk {acast3} (fun (zr : VEnvD qD) => @Eq.trans (VD qcc) {ar1} {ar2} {arhs} {as2} {ac2})))"
    );
    let m_app = format!(
        "(fun (qD : Nat -> Sk) (qf : KExpr) (qa : KExpr) (qd : Sk) (qcc : Sk) (qhf : WK qD qf (Sk.arr qd qcc)) (qha : WK qD qa qd) {ih_f} {ih_ar} (qe2 : KExpr) (qst : whnf_step (KExpr.app qf qa) qe2) (qC : Type) (qk : {kapp}) => r15_whnf_stepT_inv qC (KExpr.app qf qa) qe2 {hf} qst {a1} {a2} {a3})"
    );

    format!(
        "fun (D : Nat -> Sk) (e : KExpr) (s : Sk) (h : WK D e s) => @WK.rec {mot} {m_var} {m_sort} {m_pi} {m_lam} {m_app} D e s h"
    )
}

// ================================================================
// Group G — the reduction-sequence closure and the conversion payoff.
// ================================================================

pub(super) fn ty_val_star_sem() -> String {
    format!(
        "forall (D : Nat -> Sk) (e : KExpr) (w : KExpr), whnfStar e w -> forall (s : Sk) (h : WK D e s) (C : Type), ({}) -> C",
        sem_k("D", "w", "s", "(sval D e s h)", "C")
    )
}

pub(super) fn val_val_star_sem() -> String {
    let mot = format!(
        "(fun (qe : KExpr) (qw : KExpr) (qh : whnfStar qe qw) => forall (qs : Sk) (qd : WK D qe qs) (qC : Type), ({}) -> qC)",
        sem_k("D", "qw", "qs", "(sval D qe qs qd)", "qC")
    );
    let m_refl = format!(
        "(fun (qe : KExpr) (qs : Sk) (qd : WK D qe qs) (qC : Type) (qk : {}) => qk qd (fun (zr : VEnvD D) => @Eq.refl (VD qs) (sval D qe qs qd zr)))",
        sem_k("D", "qe", "qs", "(sval D qe qs qd)", "qC")
    );
    let ih = format!(
        "(qih : forall (qs : Sk) (qd : WK D qe2 qs) (qC : Type), ({}) -> qC)",
        sem_k("D", "qe3", "qs", "(sval D qe2 qs qd)", "qC")
    );
    let m_step = format!(
        "(fun (qe : KExpr) (qe2 : KExpr) (qe3 : KExpr) (qst : whnf_step qe qe2) (qrest : whnfStar qe2 qe3) {ih} (qs : Sk) (qd : WK D qe qs) (qC : Type) (qk : {}) => r15_val_step_sem D qe qs qd qe2 qst qC (fun (zh2 : WK D qe2 qs) (zhv : forall (zr : VEnvD D), @Eq (VD qs) (sval D qe2 qs zh2 zr) (sval D qe qs qd zr)) => qih qs zh2 qC (fun (zhw : WK D qe3 qs) (zhv2 : forall (zr : VEnvD D), @Eq (VD qs) (sval D qe3 qs zhw zr) (sval D qe2 qs zh2 zr)) => qk zhw (fun (zr : VEnvD D) => @Eq.trans (VD qs) (sval D qe3 qs zhw zr) (sval D qe2 qs zh2 zr) (sval D qe qs qd zr) (zhv2 zr) (zhv zr)))))",
        sem_k("D", "qe3", "qs", "(sval D qe qs qd)", "qC")
    );
    format!(
        "fun (D : Nat -> Sk) (e : KExpr) (w : KExpr) (hstar : whnfStar e w) => @whnfStar.rec {mot} {m_refl} {m_step} e w hstar"
    )
}

/// **THE CONTRAST WITH R11, AT AN ARBITRARY STEP.** `sval`-membership survives
/// ONE `whnf_step` at ANY shape-typed subject, not only at a head-beta redex
/// (R14's `r14_sval_transports_real_beta`). This is the class
/// `r11_candInterp_step_conv_refuted` proves `candInterp` cannot do even once.
///
/// The type is written inline rather than through a named `Type`: it quantifies
/// over a valuation, and `VEnvD D` is `Type 1`, so ANY generic statement of
/// this rung lands one universe up and cannot be a component of `AndType`
/// (measured 2026-08-27, first cycle: `def … : Type` was refused with
/// *"expected Type, got Type 1"*). That universe fact is why `r12_conv_contrast`
/// pairs CONCRETE statements, and why `r15_conv_contrast` does too.
pub(super) const TY_TRANSPORTS_ANY_STEP: &str = "forall (D : Nat -> Sk) (e : KExpr) (s : Sk) (h : WK D e s) (e2 : KExpr) (st : whnf_step e e2) (r : VEnvD D) (w : KExpr) (C : Type), vcarD s (sval D e s h r) w -> (forall (zh2 : WK D e2 s), vcarD s (sval D e2 s zh2 r) w -> C) -> C";
pub(super) const VAL_TRANSPORTS_ANY_STEP: &str = "fun (D : Nat -> Sk) (e : KExpr) (s : Sk) (h : WK D e s) (e2 : KExpr) (st : whnf_step e e2) (r : VEnvD D) (w : KExpr) (C : Type) (hm : vcarD s (sval D e s h r) w) (k : forall (zh2 : WK D e2 s), vcarD s (sval D e2 s zh2 r) w -> C) => r15_val_step_sem D e s h e2 st C (fun (zh2 : WK D e2 s) (zhv : forall (zr : VEnvD D), @Eq (VD s) (sval D e2 s zh2 zr) (sval D e s h zr)) => k zh2 (@Eq.substType (VD s) (fun (zv : VD s) => vcarD s zv w) (sval D e s h r) (sval D e2 s zh2 r) (@Eq.symm (VD s) (sval D e2 s zh2 r) (sval D e s h r) (zhv r)) hm))";

/// The same along a whole reduction SEQUENCE.
pub(super) const TY_TRANSPORTS_STAR: &str = "forall (D : Nat -> Sk) (e : KExpr) (w : KExpr) (hstar : whnfStar e w) (s : Sk) (h : WK D e s) (r : VEnvD D) (t : KExpr) (C : Type), vcarD s (sval D e s h r) t -> (forall (zhw : WK D w s), vcarD s (sval D w s zhw r) t -> C) -> C";
pub(super) const VAL_TRANSPORTS_STAR: &str = "fun (D : Nat -> Sk) (e : KExpr) (w : KExpr) (hstar : whnfStar e w) (s : Sk) (h : WK D e s) (r : VEnvD D) (t : KExpr) (C : Type) (hm : vcarD s (sval D e s h r) t) (k : forall (zhw : WK D w s), vcarD s (sval D w s zhw r) t -> C) => r15_val_star_sem D e w hstar s h C (fun (zhw : WK D w s) (zhv : forall (zr : VEnvD D), @Eq (VD s) (sval D w s zhw zr) (sval D e s h zr)) => k zhw (@Eq.substType (VD s) (fun (zv : VD s) => vcarD s zv t) (sval D e s h r) (sval D w s zhw r) (@Eq.symm (VD s) (sval D w s zhw r) (sval D e s h r) (zhv r)) hm))";

/// **`val_conv`, EXACTLY AS FAR AS IT GOES.** Two shape-typed terms with a
/// COMMON reduct have the same membership — conditionally on `sval` being
/// independent of which derivation witnesses a term's shape. That hypothesis is
/// the named gap of this rung; the conditional is registered so the boundary is
/// machine-visible rather than prose.
pub(super) const TY_VAL_CONV_FROM_IRREL: &str = "forall (D : Nat -> Sk), (forall (ze : KExpr) (zs : Sk) (zh1 : WK D ze zs) (zh2 : WK D ze zs) (zr : VEnvD D), @Eq (VD zs) (sval D ze zs zh1 zr) (sval D ze zs zh2 zr)) -> forall (e1 : KExpr) (e2 : KExpr) (w : KExpr) (s : Sk) (h1 : WK D e1 s) (h2 : WK D e2 s) (r : VEnvD D) (t : KExpr), whnfStar e1 w -> whnfStar e2 w -> vcarD s (sval D e1 s h1 r) t -> vcarD s (sval D e2 s h2 r) t";

pub(super) const VAL_VAL_CONV_FROM_IRREL: &str = "fun (D : Nat -> Sk) (hirr : forall (ze : KExpr) (zs : Sk) (zh1 : WK D ze zs) (zh2 : WK D ze zs) (zr : VEnvD D), @Eq (VD zs) (sval D ze zs zh1 zr) (sval D ze zs zh2 zr)) (e1 : KExpr) (e2 : KExpr) (w : KExpr) (s : Sk) (h1 : WK D e1 s) (h2 : WK D e2 s) (r : VEnvD D) (t : KExpr) (s1 : whnfStar e1 w) (s2 : whnfStar e2 w) (hm : vcarD s (sval D e1 s h1 r) t) => r15_val_star_sem D e1 w s1 s h1 (vcarD s (sval D e2 s h2 r) t) (fun (zw1 : WK D w s) (zv1 : forall (zr : VEnvD D), @Eq (VD s) (sval D w s zw1 zr) (sval D e1 s h1 zr)) => r15_val_star_sem D e2 w s2 s h2 (vcarD s (sval D e2 s h2 r) t) (fun (zw2 : WK D w s) (zv2 : forall (zr : VEnvD D), @Eq (VD s) (sval D w s zw2 zr) (sval D e2 s h2 zr)) => @Eq.substType (VD s) (fun (zv : VD s) => vcarD s zv t) (sval D e1 s h1 r) (sval D e2 s h2 r) (@Eq.trans (VD s) (sval D e1 s h1 r) (sval D w s zw2 r) (sval D e2 s h2 r) (@Eq.trans (VD s) (sval D e1 s h1 r) (sval D w s zw1 r) (sval D w s zw2 r) (@Eq.symm (VD s) (sval D w s zw1 r) (sval D e1 s h1 r) (zv1 r)) (hirr w s zw1 zw2 r)) (zv2 r)) hm))";

// ---- the CONCRETE congruence step the contrast is stated at ----
//
// R14's contrast is at a head-β redex, which is the one arm R14 already had.
// What R15 adds is the CONGRUENCE arms, so the contrast is stated at a real
// `pi_dom` step: `pi r12_betaRedex (sort 0)` steps in its DOMAIN, and
// `r15_val_step_piA` carries membership across it.

/// The shape of `Sk.kd Sk.ty`'s own kind — R12's `r12_betaEnv` slot shape.
pub(super) const KDKDTY: &str = "(Sk.kd (Sk.kd Sk.ty))";
/// The Π shape both sides of the congruence carry.
pub(super) const PSH: &str = "(piShape (Sk.kd Sk.ty) (Sk.kd Sk.ty))";

pub(super) fn src_inst_deriv() -> String {
    format!("def r15_instDeriv : WK r12_betaEnv (instantiate {V0} {S0}) {KDTY} := wk_inst r12_betaEnv {V0} {S0} {KDTY} {KDTY} (WK.var (skcons {KDTY} r12_betaEnv) Nat.zero) (WK.sort r12_betaEnv Level.zero)")
}

pub(super) const SRC_PI_COD_DERIV: &str = "def r15_piCodDeriv : WK (skcons Sk.ty r12_betaEnv) (KExpr.sort Level.zero) (Sk.kd Sk.ty) := WK.sort (skcons Sk.ty r12_betaEnv) Level.zero";

pub(super) fn src_pi_redex_deriv() -> String {
    format!("def r15_piRedexDeriv : WK r12_betaEnv (KExpr.pi r12_betaRedex {S0}) {PSH} := WK.pi r12_betaEnv r12_betaRedex {S0} {KDTY} {KDTY} r12_betaDeriv r15_piCodDeriv")
}

pub(super) fn src_pi_reduct_deriv() -> String {
    format!("def r15_piReductDeriv : WK r12_betaEnv (KExpr.pi (instantiate {V0} {S0}) {S0}) {PSH} := WK.pi r12_betaEnv (instantiate {V0} {S0}) {S0} {KDTY} {KDTY} r15_instDeriv r15_piCodDeriv")
}

/// The real CONGRUENCE step: the Π's domain is R12's shape-typed β redex, and
/// `beta_reduces.pi_dom` carries the inner contraction to the whole Π. This is
/// the arm class R14 could not touch.
pub(super) fn ty_pi_congr_step() -> String {
    format!("whnf_step (KExpr.pi r12_betaRedex {S0}) (KExpr.pi (instantiate {V0} {S0}) {S0})")
}
pub(super) fn val_pi_congr_step() -> String {
    format!("@whnf_step.beta (KExpr.pi r12_betaRedex {S0}) (KExpr.pi (instantiate {V0} {S0}) {S0}) (beta_reduces.pi_dom r12_betaRedex (instantiate {V0} {S0}) {S0} (beta_reduces.beta {V0} {V0} {S0}))")
}

/// The membership transport across that congruence step, at R12's registered
/// valuation. CONCRETE, so it lands in `Type` and can be an `AndType` component.
pub(super) fn src_step_transports() -> String {
    format!("def r15_svalStepTransports : Type := forall (qe : KExpr), vcarD {PSH} (sval r12_betaEnv (KExpr.pi r12_betaRedex {S0}) {PSH} r15_piRedexDeriv r12_betaJunkEnv) qe -> vcarD {PSH} (sval r12_betaEnv (KExpr.pi (instantiate {V0} {S0}) {S0}) {PSH} r15_piReductDeriv r12_betaJunkEnv) qe")
}

pub(super) const TY_TRANSPORTS_CONGR: &str = "r15_svalStepTransports";
pub(super) fn val_transports_congr() -> String {
    let hv = format!("(@Eq.symm (VD {KDTY}) (sval r12_betaEnv r12_betaRedex {KDTY} r12_betaDeriv r12_betaJunkEnv) (sval r12_betaEnv (instantiate {V0} {S0}) {KDTY} r15_instDeriv r12_betaJunkEnv) (r14_val_beta r12_betaEnv {V0} {V0} {S0} {KDKDTY} {KDTY} (WK.var r12_betaEnv Nat.zero) (WK.var (skcons {KDTY} r12_betaEnv) Nat.zero) (WK.sort r12_betaEnv Level.zero) r12_betaJunkEnv))");
    let arm = format!("(r15_val_step_piA r12_betaEnv r12_betaRedex (instantiate {V0} {S0}) {S0} {KDTY} {KDTY} r12_betaDeriv r15_instDeriv r15_piCodDeriv r12_betaJunkEnv {hv})");
    format!("fun (qe : KExpr) (hm : vcarD {PSH} (sval r12_betaEnv (KExpr.pi r12_betaRedex {S0}) {PSH} r15_piRedexDeriv r12_betaJunkEnv) qe) => @Eq.substType (VD {PSH}) (fun (zv : VD {PSH}) => vcarD {PSH} zv qe) (sval r12_betaEnv (KExpr.pi r12_betaRedex {S0}) {PSH} r15_piRedexDeriv r12_betaJunkEnv) (sval r12_betaEnv (KExpr.pi (instantiate {V0} {S0}) {S0}) {PSH} r15_piReductDeriv r12_betaJunkEnv) (@Eq.symm (VD {PSH}) (sval r12_betaEnv (KExpr.pi (instantiate {V0} {S0}) {S0}) {PSH} r15_piReductDeriv r12_betaJunkEnv) (sval r12_betaEnv (KExpr.pi r12_betaRedex {S0}) {PSH} r15_piRedexDeriv r12_betaJunkEnv) {arm}) hm")
}

/// R12's `r12_conv_contrast` shape, one rung on: R11's refutation of
/// conversion-invariance for `candInterp` and this rung's transport for `sval`
/// across a real CONGRUENCE step, paired in one kernel-checked constant.
pub(super) const TY_CONV_CONTRAST: &str =
    "AndType (r12_candInterpStepConv -> Empty) r15_svalStepTransports";
pub(super) const VAL_CONV_CONTRAST: &str = "@AndType.intro (r12_candInterpStepConv -> Empty) r15_svalStepTransports r11_candInterp_step_conv_refuted r15_sval_transports_congr_step";

// ================================================================
// Group H — witnesses. Every one applies subject reduction at a REGISTERED
// R12 object and pins the result.
// ================================================================

/// `wk_step` at R12's own shape-typed redex and R14's real head-beta step.
pub(super) fn src_wk_step_witness() -> String {
    format!("def r15_wk_step_witness : WK r12_betaEnv (instantiate {V0} {S0}) {KDTY} := wk_step r12_betaEnv r12_betaRedex {KDTY} r12_betaDeriv (instantiate {V0} {S0}) (r14_beta_step {V0} {V0} {S0})")
}

/// ...and the DISCRIMINATING form: the contractum really is `sort 0`, and it
/// really carries the kind-of-kinds shape. A `wk_step` that returned junk, or
/// that changed the shape, does not typecheck here.
pub(super) fn ty_wk_step_sort() -> String {
    format!("WK r12_betaEnv {S0} {KDTY}")
}
pub(super) fn val_wk_step_sort() -> String {
    format!("r14_wkCastT r12_betaEnv (instantiate {V0} {S0}) {S0} {KDTY} (r12_beta_contractum_is_arg {S0}) r15_wk_step_witness")
}

/// The NEGATIVE control, not registered: the same subject reduction claimed at
/// the WRONG shape. The refusal test feeds this to the kernel.
#[cfg(test)]
pub(super) fn probe_wk_step_wrong_shape() -> String {
    format!("def r15_wk_step_wrong_shape_probe : WK r12_betaEnv (instantiate {V0} {S0}) Sk.ty := wk_step r12_betaEnv r12_betaRedex {KDTY} r12_betaDeriv (instantiate {V0} {S0}) (r14_beta_step {V0} {V0} {S0})")
}

/// A step at a subject `WK` does NOT type: `let_` is outside the shape system,
/// so `wk_step` cannot even be stated there. Registered as a probe rather than
/// a constant, since the point is the refusal.
#[cfg(test)]
pub(super) fn probe_wk_step_at_let() -> String {
    format!("def r15_wk_step_let_probe : WK r12_piEnv (KExpr.let_ {S0} {S0} {V0}) Sk.ty := WK.var r12_piEnv Nat.zero")
}

/// NON-VACUITY of the fused theorem: membership really does transport across
/// the real head-beta step at R12's registered redex, COMPUTED through
/// `r15_val_step_sem` rather than assumed.
pub(super) fn ty_step_transport_witness() -> String {
    format!("forall (qe : KExpr) (C : Type), vcarD {KDTY} (sval r12_betaEnv r12_betaRedex {KDTY} r12_betaDeriv r12_betaJunkEnv) qe -> (forall (zh2 : WK r12_betaEnv (instantiate {V0} {S0}) {KDTY}), vcarD {KDTY} (sval r12_betaEnv (instantiate {V0} {S0}) {KDTY} zh2 r12_betaJunkEnv) qe -> C) -> C")
}
pub(super) fn val_step_transport_witness() -> String {
    format!("fun (qe : KExpr) (C : Type) (hm : vcarD {KDTY} (sval r12_betaEnv r12_betaRedex {KDTY} r12_betaDeriv r12_betaJunkEnv) qe) (k : forall (zh2 : WK r12_betaEnv (instantiate {V0} {S0}) {KDTY}), vcarD {KDTY} (sval r12_betaEnv (instantiate {V0} {S0}) {KDTY} zh2 r12_betaJunkEnv) qe -> C) => r15_sval_transports_any_step r12_betaEnv r12_betaRedex {KDTY} r12_betaDeriv (instantiate {V0} {S0}) (r14_beta_step {V0} {V0} {S0}) r12_betaJunkEnv qe C hm k")
}

// ================================================================
// The single ORDERED table.
// ================================================================

/// One registration item, in dependency order.
pub(super) enum R15Item {
    /// `add_recursive_def` — a constant later proofs must REDUCE THROUGH.
    Def { name: String, src: String },
    /// `add_definition` — a theorem whose proof term the kernel type-checks.
    Thm {
        name: String,
        ty: String,
        val: String,
    },
}

#[cfg(test)]
impl R15Item {
    pub(super) fn name(&self) -> &str {
        match self {
            R15Item::Def { name, .. } | R15Item::Thm { name, .. } => name,
        }
    }

    /// The item as ONE parse-checkable `def`, for the parse gate.
    pub(super) fn decl_source(&self) -> String {
        match self {
            R15Item::Def { src, .. } => src.clone(),
            R15Item::Thm { name, ty, val } => format!("def {name} : {ty} := {val}"),
        }
    }
}

fn d(name: &str, src: String) -> R15Item {
    R15Item::Def {
        name: name.to_string(),
        src,
    }
}

fn t(name: &str, ty: String, val: String) -> R15Item {
    R15Item::Thm {
        name: name.to_string(),
        ty,
        val,
    }
}

/// Every R15 constant, in registration order.
pub(super) fn r15_items() -> Vec<R15Item> {
    vec![
        t(
            "r15_headFree_wk",
            TY_HEADFREE_WK.to_string(),
            val_headfree_wk(),
        ),
        d("r15_stepT", src_step_t()),
        t(
            "r15_beta_stepT_inv",
            TY_BETA_STEP_INV.to_string(),
            val_beta_step_inv(),
        ),
        t(
            "r15_whnf_stepT_inv",
            TY_WHNF_STEP_INV.to_string(),
            VAL_WHNF_STEP_INV.to_string(),
        ),
        d("r15_wkLamT", SRC_WK_LAM_T.to_string()),
        d("r15_wk_lam_inv", src_wk_lam_inv()),
        d("wk_step", src_wk_step()),
        t("r15_val_step_piA", ty_val_step_pia(), val_val_step_pia()),
        t("r15_val_step_piB", ty_val_step_pib(), val_val_step_pib()),
        t("r15_val_step_lamA", ty_val_step_lama(), val_val_step_lama()),
        t("r15_val_step_lamB", ty_val_step_lamb(), val_val_step_lamb()),
        t("r15_val_step_appL", ty_val_step_appl(), val_val_step_appl()),
        t("r15_val_step_appR", ty_val_step_appr(), val_val_step_appr()),
        d("r15_svalLamT", SRC_SVAL_LAM_T.to_string()),
        d("r15_sval_lam_inv", src_sval_lam_inv()),
        t("r15_val_step_sem", ty_val_step_sem(), val_val_step_sem()),
        t("r15_val_star_sem", ty_val_star_sem(), val_val_star_sem()),
        t(
            "r15_sval_transports_any_step",
            TY_TRANSPORTS_ANY_STEP.to_string(),
            VAL_TRANSPORTS_ANY_STEP.to_string(),
        ),
        t(
            "r15_sval_transports_star",
            TY_TRANSPORTS_STAR.to_string(),
            VAL_TRANSPORTS_STAR.to_string(),
        ),
        t(
            "r15_val_conv_from_irrel",
            TY_VAL_CONV_FROM_IRREL.to_string(),
            VAL_VAL_CONV_FROM_IRREL.to_string(),
        ),
        d("r15_instDeriv", src_inst_deriv()),
        d("r15_piCodDeriv", SRC_PI_COD_DERIV.to_string()),
        d("r15_piRedexDeriv", src_pi_redex_deriv()),
        d("r15_piReductDeriv", src_pi_reduct_deriv()),
        t("r15_piCongr_step", ty_pi_congr_step(), val_pi_congr_step()),
        d("r15_svalStepTransports", src_step_transports()),
        t(
            "r15_sval_transports_congr_step",
            TY_TRANSPORTS_CONGR.to_string(),
            val_transports_congr(),
        ),
        t(
            "r15_conv_contrast",
            TY_CONV_CONTRAST.to_string(),
            VAL_CONV_CONTRAST.to_string(),
        ),
        d("r15_wk_step_witness", src_wk_step_witness()),
        t("r15_wk_step_sort", ty_wk_step_sort(), val_wk_step_sort()),
        t(
            "r15_step_transport_witness",
            ty_step_transport_witness(),
            val_step_transport_witness(),
        ),
    ]
}

/// Every R15 source as a parse-checkable declaration, for the parse gate, the
/// drift-proof premise test and the scratch harness.
#[cfg(test)]
pub(super) fn r15_all_sources() -> Vec<(String, String)> {
    r15_items()
        .into_iter()
        .map(|it| (it.name().to_string(), it.decl_source()))
        .collect()
}
