// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! R29 sources — **THE TERM JUDGMENT AND ITS FUNDAMENTAL THEOREM** on the
//! `WKC`/`xval` lineage.
//!
//! See the module doc of [`super::candmodel_construct_r29`] for the argument,
//! and `designs/2026-09-17-r28-term-judgment-on-the-wkc-lineage.md` §10 for the
//! ten-step `lam` chain this implements.

// **This module deliberately imports nothing** — the R12-R28 convention.

/// The reducibility of one index of a substitution, spelled once because every
/// statement below needs it and the derivation argument is long.
fn red_at(ty: &str, deriv: &str, tm: &str) -> String {
    format!("r24_RedAt D {ty} {deriv} r {tm}")
}

// ================================================================
// Group A — the context, pointwise.
// ================================================================

/// `skcons` at `KExpr`. The term context is a TOTAL function `Nat -> KExpr`,
/// matching `VEnvD`/`GoodEnvD`/`wkc_up` — every context-like object from R12
/// onward on this lineage is `Nat -> X` with a pointwise `forall (qi : Nat)`
/// hypothesis, and `ListType` appears only as `ListType Level` in `WKC.konst`.
///
/// The cost, stated so it is not discovered later: a total context cannot say
/// "the context ends", so nothing here can say CLOSED TERM. R6's
/// `synTy_sn_closed` has no analogue without a separate finiteness notion. It
/// is not needed — the SN statement this aims at is at a reducible
/// substitution, and R6's own `synTy_sn` is stated at `idsubst`, not at a
/// closed context.
pub(super) fn src_tcons() -> String {
    "def r29_tcons (A : KExpr) (G : Nat -> KExpr) (i : Nat) : KExpr := \
     @Nat.rec (fun (qi : Nat) => KExpr) A (fun (qn : Nat) (qih : KExpr) => G qn) i"
        .to_string()
}

/// A context is well-formed when every slot is an inert type.
///
/// `InertTy` and not `WKC D _ Sk.ty`: `r28_inertTy_wkc` produces the latter at
/// ANY shape environment, so the judgment needs no shape environment at all —
/// which is why `TmC` below is indexed by `Nat -> KExpr` alone and `D` appears
/// only in the fundamental theorem, bound outside the induction.
pub(super) fn src_ctx_ok() -> String {
    "def r29_ctxOK (G : Nat -> KExpr) : Type := forall (qi : Nat), InertTy (G qi)".to_string()
}

/// Extending a well-formed context with an inert type keeps it well-formed.
/// Pointwise `Nat.rec`, the `vconsD` shape.
pub(super) fn src_ctx_ok_cons() -> String {
    "def r29_ctxOK_cons (A : KExpr) (G : Nat -> KExpr) (hA : InertTy A) (hG : r29_ctxOK G) \
     (i : Nat) : InertTy (r29_tcons A G i) := \
     @Nat.rec (fun (qi : Nat) => InertTy (r29_tcons A G qi)) hA \
     (fun (qn : Nat) (qih : InertTy (r29_tcons A G qn)) => hG qn) i"
        .to_string()
}

// ================================================================
// Group B — the judgment.
// ================================================================

/// **`TmC`** — the term typing judgment the ladder has been missing since R12
/// left the `SynTy` lineage behind.
///
/// Three rules, and the fragment is exactly the one the semantic rules that
/// exist actually cover: **ζ-free and NON-DEPENDENT**. `r25_arrow A B` is
/// `KExpr.pi A (lift_at B 0 1)`, non-dependence faked inside a dependent `pi`;
/// there is no `let_` rule because R1 PROVED no per-set engine reaches a `let_`
/// redex (`Neutral (let_ …)` is `Empty`); there is no `sort` rule because
/// `WKC.sort` concludes at `Sk.kd Sk.ty` and a sort is therefore not a
/// `ty`-shaped type here.
///
/// The type derivations are `InertTy` fields rather than `WKC` ones because
/// `r28_inertTy_wkc` recovers a `WKC` at any `D` — carrying `WKC` would fix a
/// shape environment the judgment has no other use for, and would let two
/// different derivations of one judgment sit in a single derivation tree.
/// R6 does the same thing one size down: `SynTy.lam` carries `SimpleTy A`.
pub(super) fn src_tmc() -> String {
    "inductive TmC : (Nat -> KExpr) -> KExpr -> KExpr -> Type\n\
     | var : forall (G : Nat -> KExpr) (i : Nat), TmC G (KExpr.bvar i) (G i)\n\
     | app : forall (G : Nat -> KExpr) (f : KExpr) (a : KExpr) (A : KExpr) (B : KExpr), \
     InertTy A -> InertTy B -> TmC G f (r25_arrow A B) -> TmC G a A -> \
     TmC G (KExpr.app f a) B\n\
     | lam : forall (G : Nat -> KExpr) (b : KExpr) (A : KExpr) (B : KExpr), \
     InertTy A -> InertTy B -> TmC (r29_tcons A G) b B -> \
     TmC G (KExpr.lam A b) (r25_arrow A B)"
        .to_string()
}

/// **`r29_RedSub`** — a substitution is reducible when every slot is reducible
/// at its context type. R6's `SubstOK`, pointwise instead of through a lookup
/// equation.
pub(super) fn src_redsub() -> String {
    let mem = red_at("(G qi)", "(r28_inertTy_wkc D (G qi) (hG qi))", "(s qi)");
    format!(
        "def r29_RedSub (D : Nat -> Sk) (G : Nat -> KExpr) (hG : r29_ctxOK G) (r : VEnvD D) \
         (s : Nat -> KExpr) : Type := forall (qi : Nat), {mem}"
    )
}

/// **`r29_redsub_id`** — the identity substitution is reducible, at every
/// well-formed context.
///
/// This is `r27_red_var` at every index, and it is the SECOND thing R27 bought:
/// not visible from R27's own statement, and the reason a fundamental theorem
/// on this lineage can read an SN side condition off its own instance.
pub(super) fn src_redsub_id() -> String {
    "def r29_redsub_id (D : Nat -> Sk) (G : Nat -> KExpr) (hG : r29_ctxOK G) (r : VEnvD D) \
     (hr : GoodEnvD D r) : r29_RedSub D G hG r idsubst := \
     fun (i : Nat) => r27_red_var D (G i) (r28_inertTy_wkc D (G i) (hG i)) r hr i"
        .to_string()
}

/// **`r29_redsub_extend`** — `scons` of a reducible term onto a reducible
/// substitution. Pointwise `Nat.rec`: the zero arm is the new witness, the
/// successor arm the old one.
pub(super) fn src_redsub_extend() -> String {
    let at = |i: &str| {
        red_at(
            &format!("(r29_tcons A G {i})"),
            &format!("(r28_inertTy_wkc D (r29_tcons A G {i}) (r29_ctxOK_cons A G hA hG {i}))"),
            &format!("(scons a s {i})"),
        )
    };
    format!(
        "def r29_redsub_extend (D : Nat -> Sk) (G : Nat -> KExpr) (hG : r29_ctxOK G) \
         (A : KExpr) (hA : InertTy A) (r : VEnvD D) (s : Nat -> KExpr) \
         (hs : r29_RedSub D G hG r s) (a : KExpr) \
         (ha : {ha}) : \
         r29_RedSub D (r29_tcons A G) (r29_ctxOK_cons A G hA hG) r (scons a s) := \
         fun (i : Nat) => @Nat.rec (fun (qi : Nat) => {motive}) ha \
         (fun (qn : Nat) (qih : {ih}) => hs qn) i",
        ha = red_at("A", "(r28_inertTy_wkc D A hA)", "a"),
        motive = at("qi"),
        ih = at("qn"),
    )
}

// ================================================================
// Group C — the fundamental theorem.
// ================================================================

fn motive_at(g: &str, e: &str, tt: &str, ht: &str) -> String {
    format!(
        "forall (hG0 : r29_ctxOK {g}) (hT0 : InertTy {tt}) (s : Nat -> KExpr), \
         r29_RedSub D {g} hG0 r s -> {concl}",
        concl = red_at(tt, ht, &format!("(psubst s {e})")),
    )
}

pub(super) fn ty_fundamental() -> String {
    format!(
        "forall (D : Nat -> Sk) (r : VEnvD D), GoodEnvD D r -> \
         RecEnvClosed (red_rec the_red_env) -> \
         forall (G : Nat -> KExpr) (e : KExpr) (T : KExpr), TmC G e T -> \
         forall (hG : r29_ctxOK G) (hT : InertTy T) (s : Nat -> KExpr), \
         r29_RedSub D G hG r s -> {concl}",
        concl = red_at("T", "(r28_inertTy_wkc D T hT)", "(psubst s e)"),
    )
}

pub(super) fn val_fundamental() -> String {
    // The motive, stated at the recursor's own binders.
    let motive = format!(
        "(fun (G0 : Nat -> KExpr) (e0 : KExpr) (T0 : KExpr) (_d0 : TmC G0 e0 T0) => {m})",
        m = motive_at("G0", "e0", "T0", "(r28_inertTy_wkc D T0 hT0)"),
    );

    // var: the substitution hypothesis AT i, reconciled with the motive's own
    // derivation. `psubst s (bvar i)` is `s i` definitionally.
    let m_var = "(fun (G0 : Nat -> KExpr) (i : Nat) (hG0 : r29_ctxOK G0) (hT0 : InertTy (G0 i)) \
         (s : Nat -> KExpr) (hs : r29_RedSub D G0 hG0 r s) => \
         r27_red_irrel D (G0 i) (r28_inertTy_wkc D (G0 i) (hG0 i)) \
         (r28_inertTy_wkc D (G0 i) hT0) r (s i) (hs i))"
        .to_string();

    // app: r25_red_app on the two IHs. It needs no GoodEnvD and no
    // RecEnvClosed; the two r27_red_irrel uses reconcile the arrow's
    // derivation and the conclusion's.
    let arrow_inert = "(InertTy.arrow A B hA hB)";
    let m_app = format!(
        "(fun (G0 : Nat -> KExpr) (f : KExpr) (a : KExpr) (A : KExpr) (B : KExpr) \
         (hA : InertTy A) (hB : InertTy B) \
         (_df : TmC G0 f (r25_arrow A B)) (_da : TmC G0 a A) \
         (ihf : {ih_f}) (iha : {ih_a}) \
         (hG0 : r29_ctxOK G0) (hT0 : InertTy B) (s : Nat -> KExpr) \
         (hs : r29_RedSub D G0 hG0 r s) => \
         r27_red_irrel D B (r28_inertTy_wkc D B hB) (r28_inertTy_wkc D B hT0) r \
         (KExpr.app (psubst s f) (psubst s a)) \
         (r25_red_app D A B (r28_inertTy_wkc D A hA) (r28_inertTy_wkc D B hB) r \
         (psubst s f) (psubst s a) \
         (r27_red_irrel D (r25_arrow A B) \
         (r28_inertTy_wkc D (r25_arrow A B) {arrow_inert}) \
         (r25_arrowWkc D A B (r28_inertTy_wkc D A hA) (r28_inertTy_wkc D B hB)) \
         r (psubst s f) (ihf hG0 {arrow_inert} s hs)) \
         (iha hG0 hA s hs)))",
        ih_f = motive_at(
            "G0",
            "f",
            "(r25_arrow A B)",
            "(r28_inertTy_wkc D (r25_arrow A B) hT0)"
        ),
        ih_a = motive_at("G0", "a", "A", "(r28_inertTy_wkc D A hT0)"),
    );

    // lam: the ten-step chain of the design doc's §10.
    let hac = "(r28_inertTy_wkc D A hA)";
    let hbc = "(r28_inertTy_wkc D B hB)";
    let hgc = "(r29_ctxOK_cons A G0 hA hG0)";
    // The family, at an arbitrary reducible argument.
    let family = |a2: &str, ha2: &str| {
        format!(
            "(r26_lam_premise_is_the_induction_hypothesis D B {hbc} r b s {a2} \
             (ihb {hgc} hB (scons {a2} s) \
             (r29_redsub_extend D G0 hG0 A hA r s hs {a2} {ha2})))"
        )
    };
    // SN of the substituted body, read off the family's own instance at bvar 0.
    let h_sn = format!(
        "(whnfAcc_of_instantiate_bvar0 (psubst (up s) b) \
         (isCandHF_cr1 (r24_RedAt D B {hbc} r) (r24_red_isCandHF D B {hbc} r hr) \
         (instantiate (psubst (up s) b) (KExpr.bvar Nat.zero)) \
         {fam0}))",
        fam0 = family(
            "(KExpr.bvar Nat.zero)",
            &format!("(r27_red_var D A {hac} r hr Nat.zero)")
        ),
    );
    // SN of the substituted annotation, through InertTy.
    let h_ann = "(@Eq.substType KExpr (fun (z : KExpr) => whnf_acc z) A (psubst s A) \
         (@Eq.symm KExpr (psubst s A) A (r28_inertTy_psubst A hA s)) \
         (r28_inertTy_whnfAcc A hA))"
        .to_string();
    let m_lam = format!(
        "(fun (G0 : Nat -> KExpr) (b : KExpr) (A : KExpr) (B : KExpr) \
         (hA : InertTy A) (hB : InertTy B) \
         (_db : TmC (r29_tcons A G0) b B) (ihb : {ih_b}) \
         (hG0 : r29_ctxOK G0) (hT0 : InertTy (r25_arrow A B)) (s : Nat -> KExpr) \
         (hs : r29_RedSub D G0 hG0 r s) => \
         r27_red_irrel D (r25_arrow A B) (r25_arrowWkc D A B {hac} {hbc}) \
         (r28_inertTy_wkc D (r25_arrow A B) hT0) r \
         (KExpr.lam (psubst s A) (psubst (up s) b)) \
         (r26_red_lam_one D A B {hac} {hbc} r hr hrec (psubst s A) {h_ann} \
         (psubst (up s) b) {h_sn} \
         (fun (a2 : KExpr) (ha2 : {red_a2}) => {fam})))",
        ih_b = motive_at("(r29_tcons A G0)", "b", "B", "(r28_inertTy_wkc D B hT0)"),
        red_a2 = red_at("A", hac, "a2"),
        fam = family("a2", "ha2"),
    );

    format!(
        "fun (D : Nat -> Sk) (r : VEnvD D) (hr : GoodEnvD D r) \
         (hrec : RecEnvClosed (red_rec the_red_env)) \
         (G : Nat -> KExpr) (e : KExpr) (T : KExpr) (d : TmC G e T) => \
         @TmC.rec {motive} {m_var} {m_app} {m_lam} G e T d"
    )
}

/// **`r29_sn`** — THE CAPSTONE: every `TmC`-derivable term is strongly
/// normalizing, unconditionally in the term.
///
/// The fundamental theorem at `idsubst` (reducible by `r29_redsub_id`, which is
/// `r27_red_var` at every index), then `isCandHF_cr1` to read SN out of
/// membership, then `psubst_id` to drop the identity substitution — R6's
/// `synTy_sn` is the same three steps. What it still carries is `GoodEnvD D r`,
/// `RecEnvClosed (red_rec the_red_env)` and a well-formed context: the first two
/// because the `lam` path needs them and the spec threads `RecEnvClosed` as a
/// premise in 39 places rather than discharging it, the third because `TmC`'s
/// `var` rule reads the context.
pub(super) fn ty_sn() -> String {
    "forall (D : Nat -> Sk) (r : VEnvD D), GoodEnvD D r -> \
     RecEnvClosed (red_rec the_red_env) -> \
     forall (G : Nat -> KExpr) (e : KExpr) (T : KExpr), TmC G e T -> \
     forall (hG : r29_ctxOK G) (hT : InertTy T), whnf_acc e"
        .to_string()
}

pub(super) fn val_sn() -> String {
    "fun (D : Nat -> Sk) (r : VEnvD D) (hr : GoodEnvD D r) \
     (hrec : RecEnvClosed (red_rec the_red_env)) \
     (G : Nat -> KExpr) (e : KExpr) (T : KExpr) (d : TmC G e T) \
     (hG : r29_ctxOK G) (hT : InertTy T) => \
     @Eq.substType KExpr (fun (z : KExpr) => whnf_acc z) (psubst idsubst e) e (psubst_id e) \
     (isCandHF_cr1 (r24_RedAt D T (r28_inertTy_wkc D T hT) r) \
     (r24_red_isCandHF D T (r28_inertTy_wkc D T hT) r hr) (psubst idsubst e) \
     (r29_fundamental D r hr hrec G e T d hG hT idsubst (r29_redsub_id D G hG r hr)))"
        .to_string()
}

// ================================================================
// Negative controls — none of these is registered.
// ================================================================

/// The fundamental theorem WITHOUT the reducible-substitution hypothesis,
/// claimed by the same term. It must be refused: `hs` is what the `var` arm
/// returns, so without it the induction has nothing at a variable.
#[cfg(test)]
pub(super) fn probe_no_redsub() -> String {
    format!(
        "def r29_probe_no_redsub : forall (D : Nat -> Sk) (r : VEnvD D), GoodEnvD D r -> \
         RecEnvClosed (red_rec the_red_env) -> \
         forall (G : Nat -> KExpr) (e : KExpr) (T : KExpr), TmC G e T -> \
         forall (hG : r29_ctxOK G) (hT : InertTy T) (s : Nat -> KExpr), {concl} := {val}",
        concl = red_at("T", "(r28_inertTy_wkc D T hT)", "(psubst s e)"),
        val = val_fundamental(),
    )
}

// ================================================================
// The item table.
// ================================================================

pub(super) enum R29Item {
    Ind {
        name: String,
        src: String,
    },
    Def {
        name: String,
        src: String,
    },
    Thm {
        name: String,
        ty: String,
        val: String,
    },
}

/// Test-only, like R27's: `name` and `decl_source` are read by the scratch
/// harness and by nothing in a normal build, so an ungated impl is a
/// `never used` warning and `-D warnings` denies it.
#[cfg(test)]
impl R29Item {
    pub(super) fn name(&self) -> &str {
        match self {
            R29Item::Ind { name, .. } | R29Item::Def { name, .. } | R29Item::Thm { name, .. } => {
                name
            }
        }
    }

    #[cfg(test)]
    pub(super) fn decl_source(&self) -> String {
        match self {
            R29Item::Ind { src, .. } | R29Item::Def { src, .. } => src.clone(),
            R29Item::Thm { name, ty, val } => format!("def {name} : {ty} := {val}"),
        }
    }
}

fn i(name: &str, src: String) -> R29Item {
    R29Item::Ind {
        name: name.to_string(),
        src,
    }
}

fn d(name: &str, src: String) -> R29Item {
    R29Item::Def {
        name: name.to_string(),
        src,
    }
}

fn t(name: &str, ty: String, val: String) -> R29Item {
    R29Item::Thm {
        name: name.to_string(),
        ty,
        val,
    }
}

/// Every R29 constant, in registration order.
pub(super) fn r29_items() -> Vec<R29Item> {
    vec![
        d("r29_tcons", src_tcons()),
        d("r29_ctxOK", src_ctx_ok()),
        d("r29_ctxOK_cons", src_ctx_ok_cons()),
        i("TmC", src_tmc()),
        d("r29_RedSub", src_redsub()),
        d("r29_redsub_id", src_redsub_id()),
        d("r29_redsub_extend", src_redsub_extend()),
        t("r29_fundamental", ty_fundamental(), val_fundamental()),
        t("r29_sn", ty_sn(), val_sn()),
    ]
}

#[cfg(test)]
pub(super) fn r29_all_sources() -> Vec<(String, String)> {
    r29_items()
        .into_iter()
        .map(|it| (it.name().to_string(), it.decl_source()))
        .collect()
}
