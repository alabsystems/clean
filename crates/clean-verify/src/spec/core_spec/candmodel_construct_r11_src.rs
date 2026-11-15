// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Source builders for R11 of the candidate-model construction ladder — the
//! pure string half of the CONST-AT-PI rung and of the conversion settlement.
//!
//! A sibling module rather than a region of `candmodel_construct_r11.rs`, on
//! the convention `candmodel_construct_r10_src.rs` set: the registration half,
//! the source half and the battery that reads them back are three subjects, and
//! keeping them one file crosses the 1000-line paragon ratchet. Every source in
//! this file is pre-validated through the clean-parser scratch harness
//! (`candmodel_construct_r11_tests.rs`).
//!
//! Read `candmodel_construct_r11.rs` first: it carries the rung's verdict, the
//! conversion refutation and the honesty notes.

use super::candmodel_construct_r9::{
    src_syn_ty_c, ty_synty_c_id, ty_synty_c_not_total, ty_synty_c_sort_witness, val_synty_c_id,
    val_synty_c_not_total, val_synty_c_sort_witness, val_syntyc_fundamental_head, REC_APPLICAND,
    TY_SYNTYC_FUNDAMENTAL, TY_SYNTYC_SN, TY_SYNTYC_SN_CLOSED, TY_SYNTYC_SN_SUBST, VAL_SYNTYC_SN,
    VAL_SYNTYC_SN_CLOSED, VAL_SYNTYC_SN_SUBST,
};

/// `bvar 0`.
pub(super) const V0: &str = "(KExpr.bvar Nat.zero)";
/// `sort 0`, the fragment's base type.
pub(super) const S0: &str = "(KExpr.sort Level.zero)";
/// The non-dependent function type `pi (sort 0) (sort 0)`.
pub(super) const PI00: &str = "(KExpr.pi (KExpr.sort Level.zero) (KExpr.sort Level.zero))";
/// `pi (sort 0) (bvar 0)` — a Pi type whose CODOMAIN is a variable. Its
/// interpretation is `candInterp PI00`'s (both codomains are non-Pi formers, so
/// both go to the top candidate) while its syntax is not, which is what makes
/// it the honest witness of the semantic conversion rule.
pub(super) const PI0V0: &str = "(KExpr.pi (KExpr.sort Level.zero) (KExpr.bvar Nat.zero))";
/// The fragment's identity function, annotated at the base type.
pub(super) const IDLAM0: &str = "(KExpr.lam (KExpr.sort Level.zero) (KExpr.bvar Nat.zero))";
/// The empty context.
pub(super) const NILCTX: &str = "(ListType.nil KExpr)";
/// The empty universe-parameter list.
pub(super) const NILUS: &str = "(ListType.nil Level)";
/// The fixed definition environment.
pub(super) const DENV: &str = "(red_def the_red_env)";
/// The fixed recursor environment.
pub(super) const RENV: &str = "(red_rec the_red_env)";
/// A REAL reflected kernel name that is neither δ-defined nor a recursor — the
/// inductive type `DefEnv` (R9's `DEADNAME`, R10's unlock entry point).
pub(super) const DEADNAME: &str = "fixture_def_env_name";
/// The bare const at that name.
pub(super) const DEADCONST: &str = "(KExpr.const fixture_def_env_name (ListType.nil Level))";
/// **THE CONVERSION COUNTEREXAMPLE'S TYPE.** `app (lam (sort 0) (bvar 0))
/// (pi (sort 0) (sort 0))` — a β-redex AT THE TYPE LEVEL whose contractum is
/// `PI00`. `candInterp` reads the head former of a type, and this one is `app`,
/// so its interpretation is the TOP candidate while its β-reduct's is a proper
/// subset. That single step is the whole refutation.
pub(super) const CONV_REDEX: &str =
    "(KExpr.app (KExpr.lam (KExpr.sort Level.zero) (KExpr.bvar Nat.zero)) (KExpr.pi (KExpr.sort Level.zero) (KExpr.sort Level.zero)))";

// ================================================================
// Group A — the judgment `SynTyP`.
// ================================================================

/// R9's textual-weakening idiom at the NEXT judgment: every `SynTyC` spelling
/// becomes its `SynTyP` counterpart, in the TYPE name and in the theorem names
/// alike. Applied to R9's own builders so the eight shared rules and their eight
/// fundamental-theorem arms cannot drift from R9's.
pub(super) fn p_weaken(src: &str) -> String {
    src.replace("SynTyC", "SynTyP")
        .replace("synTyC_", "synTyP_")
}

/// THE CONST-AT-ANY-TYPE RULE — the rung's deliverable. A constant that the
/// real reflected environment gives neither a definitional value nor recursor
/// metadata is `HeadInert`, hence in EVERY `IsCandHI` candidate
/// (`r10_deadConst_cand_mem`), hence in `candInterp A` for EVERY untyped `A`
/// (`candInterp_isCandHI`) — Pi types included. R9's `konstDead` is the same
/// constant restricted to `A = sort m`; this is the general clause, and it is
/// the first rule of the ladder that reaches a const at a Pi type.
const KONST_INERT_RULE: &str = "| konstInert : forall (G : ListType KExpr) (c : Name) (us : ListType Level) (A : KExpr), Eq (OptionType KExpr) (defval_for (red_def the_red_env) c) (OptionType.none KExpr) -> Eq (OptionType RecMeta) (recmeta_for (red_rec the_red_env) c) (OptionType.none RecMeta) -> SynTyP G (KExpr.const c us) A";

/// THE SEMANTIC CONVERSION RULE. `TypingCtxConv.conv` converts along `DefEq`;
/// that is REFUTED for this interpretation (`r11_candInterp_conv_eq_refuted`),
/// so the rule converts along equality of the two types' INTERPRETATIONS
/// instead — the strongest premise `candInterp` can support. It is not
/// vacuous and not `Eq.refl`-only: `candInterp_lift_eq` supplies it at an
/// ARBITRARY type (`r11_synTyP_unlift_type`).
const CONV_INTERP_RULE: &str = "| convI : forall (G : ListType KExpr) (e : KExpr) (A : KExpr) (B : KExpr), SynTyP G e A -> Eq (KExpr -> Type) (candInterp A) (candInterp B) -> SynTyP G e B";

pub(super) fn src_syn_ty_p() -> String {
    format!(
        "{}\n{KONST_INERT_RULE}\n{CONV_INTERP_RULE}",
        p_weaken(&src_syn_ty_c())
    )
}

pub(super) fn ty_syntyp_fundamental() -> String {
    p_weaken(TY_SYNTYC_FUNDAMENTAL)
}

/// The `konstInert` arm: `psubst` is definitionally inert on a `const`, so the
/// goal IS `candInterp qA (const qc qus)` and R10's membership lemma closes it
/// outright at the interpretation's own `IsCandHI` proof.
fn m_konst_inert() -> String {
    format!(
        "(fun (qG : ListType KExpr) (qc : Name) (qus : ListType Level) (qA : KExpr) (qhd : Eq (OptionType KExpr) (defval_for {DENV} qc) (OptionType.none KExpr)) (qhr : Eq (OptionType RecMeta) (recmeta_for {RENV} qc) (OptionType.none RecMeta)) (qs : Nat -> KExpr) (_qhs : SubstOK qs qG) => r10_deadConst_cand_mem (candInterp qA) (candInterp_isCandHI qA) qc qus qhd qhr)"
    )
}

/// The `convI` arm: one `Eq.substType` at the POINTWISE motive
/// `fun F => F (psubst s e)`, R8's `candInterp_lift` transport verbatim in
/// shape. The equality is between two `KExpr -> Type` values, i.e. `Eq` at
/// `Sort 2`, which `Eq (α : Sort u)` already covers.
fn m_conv_interp() -> String {
    let ih = "forall (qs2 : Nat -> KExpr), SubstOK qs2 qG -> candInterp qA (psubst qs2 qe)";
    format!(
        "(fun (qG : ListType KExpr) (qe : KExpr) (qA : KExpr) (qB : KExpr) (_qh : SynTyP qG qe qA) (qheq : Eq (KExpr -> Type) (candInterp qA) (candInterp qB)) (qih : {ih}) (qs : Nat -> KExpr) (qhs : SubstOK qs qG) => Eq.substType (KExpr -> Type) (fun (qF : KExpr -> Type) => qF (psubst qs qe)) (candInterp qA) (candInterp qB) qheq (qih qs qhs))"
    )
}

/// R9's eight-minor `SynTyC.rec` term with the judgment renamed and the two new
/// minors spliced in front of the indices — the recursor takes its minors in
/// CONSTRUCTOR ORDER and the two new rules are last, so the splice point is
/// exactly the trailing `G e T h`.
pub(super) fn val_syntyp_fundamental() -> String {
    let head = p_weaken(&val_syntyc_fundamental_head());
    format!(
        "{head} {} {}{REC_APPLICAND}",
        m_konst_inert(),
        m_conv_interp()
    )
}

pub(super) fn ty_syntyp_sn_subst() -> String {
    p_weaken(TY_SYNTYC_SN_SUBST)
}
pub(super) fn val_syntyp_sn_subst() -> String {
    p_weaken(VAL_SYNTYC_SN_SUBST)
}
pub(super) fn ty_syntyp_sn() -> String {
    p_weaken(TY_SYNTYC_SN)
}
pub(super) fn val_syntyp_sn() -> String {
    p_weaken(VAL_SYNTYC_SN)
}
pub(super) fn ty_syntyp_sn_closed() -> String {
    p_weaken(TY_SYNTYC_SN_CLOSED)
}
pub(super) fn val_syntyp_sn_closed() -> String {
    p_weaken(VAL_SYNTYC_SN_CLOSED)
}

// ================================================================
// Group B — the bridge from R9, and the proof that its converse is FALSE.
// ================================================================

pub(super) const TY_SYNTYC_TO_SYNTYP: &str =
    "forall (G : ListType KExpr) (e : KExpr) (T : KExpr), SynTyC G e T -> SynTyP G e T";

pub(super) fn val_syntyc_to_syntyp() -> String {
    let motive = "(fun (qG : ListType KExpr) (qe : KExpr) (qT : KExpr) (_ : SynTyC qG qe qT) => SynTyP qG qe qT)";
    let m_var = "(fun (qG : ListType KExpr) (qi : Nat) (qA : KExpr) (qhget : Eq (OptionType KExpr) (ctx_lookup qG qi) (OptionType.some KExpr qA)) => SynTyP.var qG qi qA qhget)";
    let m_sort = "(fun (qG : ListType KExpr) (qn : Level) => SynTyP.sort qG qn)";
    let m_pi = "(fun (qG : ListType KExpr) (qA : KExpr) (qB : KExpr) (qn : Level) (qm : Level) (_qhA : SynTyC qG qA (KExpr.sort qn)) (_qhB : SynTyC (ListType.cons KExpr qA qG) qB (KExpr.sort qm)) (qihA : SynTyP qG qA (KExpr.sort qn)) (qihB : SynTyP (ListType.cons KExpr qA qG) qB (KExpr.sort qm)) => SynTyP.pi qG qA qB qn qm qihA qihB)";
    let m_app = "(fun (qG : ListType KExpr) (qA : KExpr) (qB : KExpr) (qf : KExpr) (qa : KExpr) (_qhf : SynTyC qG qf (KExpr.pi qA qB)) (_qha : SynTyC qG qa qA) (qihf : SynTyP qG qf (KExpr.pi qA qB)) (qiha : SynTyP qG qa qA) => SynTyP.app qG qA qB qf qa qihf qiha)";
    let m_lam = "(fun (qG : ListType KExpr) (qA : KExpr) (qB : KExpr) (qb : KExpr) (qhA : SimpleTy qA) (_qhb : SynTyC (ListType.cons KExpr qA qG) qb qB) (qih : SynTyP (ListType.cons KExpr qA qG) qb qB) => SynTyP.lam qG qA qB qb qhA qih)";
    let m_let = "(fun (qG : ListType KExpr) (qn : Level) (qm : Level) (qv : KExpr) (qb : KExpr) (_qhv : SynTyC qG qv (KExpr.sort qn)) (_qhb : SynTyC (ListType.cons KExpr (KExpr.sort qn) qG) qb (KExpr.sort qm)) (qihv : SynTyP qG qv (KExpr.sort qn)) (qihb : SynTyP (ListType.cons KExpr (KExpr.sort qn) qG) qb (KExpr.sort qm)) => SynTyP.letTy qG qn qm qv qb qihv qihb)";
    let m_konst_dead = format!("(fun (qG : ListType KExpr) (qc : Name) (qus : ListType Level) (qm : Level) (qhn : Eq (OptionType KExpr) (defval_for {DENV} qc) (OptionType.none KExpr)) => SynTyP.konstDead qG qc qus qm qhn)");
    let m_konst_delta = format!("(fun (qG : ListType KExpr) (qc : Name) (qus : ListType Level) (qm : Level) (qbody : KExpr) (qhd : delta_step {DENV} (KExpr.const qc qus) qbody) (_qhb : SynTyC qG qbody (KExpr.sort qm)) (qih : SynTyP qG qbody (KExpr.sort qm)) => SynTyP.konstDelta qG qc qus qm qbody qhd qih)");
    format!(
        "fun (G : ListType KExpr) (e : KExpr) (T : KExpr) (h : SynTyC G e T) => SynTyC.rec {motive} {m_var} {m_sort} {m_pi} {m_app} {m_lam} {m_let} {m_konst_dead} {m_konst_delta} G e T h"
    )
}

pub(super) const TY_SYNTYC_SN_VIA_SYNTYP: &str =
    "forall (G : ListType KExpr) (e : KExpr) (T : KExpr), SynTyC G e T -> whnf_acc e";

pub(super) const VAL_SYNTYC_SN_VIA_SYNTYP: &str = "fun (G : ListType KExpr) (e : KExpr) (T : KExpr) (h : SynTyC G e T) => synTyP_sn G e T (synTyC_to_synTyP G e T h)";

/// `Bool`-valued "is this a `const`?", the demand-side discriminator of the
/// converse proof. R9's `kexpr_is_lam_b` at the const former.
pub(super) const SRC_KEXPR_IS_CONST_B: &str = r"def kexpr_is_const_b (e : KExpr) : Bool := match e with
| KExpr.sort n => Bool.false
| KExpr.bvar i => Bool.false
| KExpr.app f a => Bool.false
| KExpr.lam ty b => Bool.false
| KExpr.pi ty b => Bool.false
| KExpr.const n us => Bool.true
| KExpr.let_ ty v b => Bool.false
| KExpr.proj s i sub => Bool.false
| KExpr.lit n => Bool.false";

/// The TYPE-side discriminator: `Empty` at a `pi`, inhabited everywhere else.
///
/// A REGISTERED def with a declared `Type` result rather than an inline
/// `KExpr.rec`, for R9's measured reason: the motive of `synTyC_no_const_at_pi`
/// needs it as the CODOMAIN of an arrow, and an inline `(fun (_ : KExpr) =>
/// Type) qT` beta-redex is not a sort the elaborator accepts there.
pub(super) const SRC_R11_PI_DISCR: &str = "def r11_pi_discr (T : KExpr) : Type := KExpr.rec (fun (_ : KExpr) => Type) (fun (_ : Level) => Nat) (fun (_ : Nat) => Nat) (fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) (fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) (fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Empty) (fun (_ : Name) (_ : ListType Level) => Nat) (fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) (_ : Type) => Nat) (fun (_ : Name) (_ : Nat) (_ : KExpr) (_ : Type) => Nat) (fun (_ : Nat) => Nat) T";

pub(super) const TY_SYNTYC_NO_CONST_AT_PI: &str = "forall (G : ListType KExpr) (c : Name) (us : ListType Level) (A : KExpr) (B : KExpr), SynTyC G (KExpr.const c us) (KExpr.pi A B) -> Empty";

pub(super) fn val_syntyc_no_const_at_pi() -> String {
    let d = "r11_pi_discr";
    let motive = format!("(fun (qG : ListType KExpr) (qe : KExpr) (qT : KExpr) (_ : SynTyC qG qe qT) => Eq Bool (kexpr_is_const_b qe) Bool.true -> {d} qT)");
    let ih =
        |subj: &str, ty: &str| format!("Eq Bool (kexpr_is_const_b {subj}) Bool.true -> {d} {ty}");
    let refute = |binders: &str, subj: &str, concl: &str| {
        format!("(fun {binders} (hc : Eq Bool (kexpr_is_const_b {subj}) Bool.true) => bool_false_ne_true_t ({d} {concl}) hc)")
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
        "(fun (qG : ListType KExpr) (qA : KExpr) (qB : KExpr) (qn : Level) (qm : Level) (_qhA : SynTyC qG qA (KExpr.sort qn)) (_qhB : SynTyC (ListType.cons KExpr qA qG) qB (KExpr.sort qm)) (_qihA : {}) (_qihB : {}) (hc : Eq Bool (kexpr_is_const_b (KExpr.pi qA qB)) Bool.true) => bool_false_ne_true_t ({d} (KExpr.sort (Level.imax qn qm))) hc)",
        ih("qA", "(KExpr.sort qn)"),
        ih("qB", "(KExpr.sort qm)")
    );
    let m_app = format!(
        "(fun (qG : ListType KExpr) (qA : KExpr) (qB : KExpr) (qf : KExpr) (qa : KExpr) (_qhf : SynTyC qG qf (KExpr.pi qA qB)) (_qha : SynTyC qG qa qA) (_qihf : {}) (_qiha : {}) (hc : Eq Bool (kexpr_is_const_b (KExpr.app qf qa)) Bool.true) => bool_false_ne_true_t ({d} qB) hc)",
        ih("qf", "(KExpr.pi qA qB)"),
        ih("qa", "qA")
    );
    let m_lam = format!(
        "(fun (qG : ListType KExpr) (qA : KExpr) (qB : KExpr) (qb : KExpr) (_qhA : SimpleTy qA) (_qhb : SynTyC (ListType.cons KExpr qA qG) qb qB) (_qih : {}) (hc : Eq Bool (kexpr_is_const_b (KExpr.lam qA qb)) Bool.true) => bool_false_ne_true_t ({d} (KExpr.pi qA qB)) hc)",
        ih("qb", "qB")
    );
    let m_let = format!(
        "(fun (qG : ListType KExpr) (qn : Level) (qm : Level) (qv : KExpr) (qb : KExpr) (_qhv : SynTyC qG qv (KExpr.sort qn)) (_qhb : SynTyC (ListType.cons KExpr (KExpr.sort qn) qG) qb (KExpr.sort qm)) (_qihv : {}) (_qihb : {}) (hc : Eq Bool (kexpr_is_const_b (KExpr.let_ (KExpr.sort qn) qv qb)) Bool.true) => bool_false_ne_true_t ({d} (KExpr.sort qm)) hc)",
        ih("qv", "(KExpr.sort qn)"),
        ih("qb", "(KExpr.sort qm)")
    );
    // THE TWO ARMS THAT ARE NOT REFUTATIONS: a const IS a const, and R9's two
    // const rules both conclude at a SORT, where the discriminator is `Nat`.
    let m_konst_dead = format!("(fun (qG : ListType KExpr) (qc : Name) (qus : ListType Level) (qm : Level) (_qhn : Eq (OptionType KExpr) (defval_for {DENV} qc) (OptionType.none KExpr)) (_hc : Eq Bool (kexpr_is_const_b (KExpr.const qc qus)) Bool.true) => Nat.zero)");
    let m_konst_delta = format!(
        "(fun (qG : ListType KExpr) (qc : Name) (qus : ListType Level) (qm : Level) (qbody : KExpr) (_qhd : delta_step {DENV} (KExpr.const qc qus) qbody) (_qhb : SynTyC qG qbody (KExpr.sort qm)) (_qih : {}) (_hc : Eq Bool (kexpr_is_const_b (KExpr.const qc qus)) Bool.true) => Nat.zero)",
        ih("qbody", "(KExpr.sort qm)")
    );
    format!(
        "fun (G : ListType KExpr) (c : Name) (us : ListType Level) (A : KExpr) (B : KExpr) (h : SynTyC G (KExpr.const c us) (KExpr.pi A B)) => SynTyC.rec {motive} {m_var} {m_sort} {m_pi} {m_app} {m_lam} {m_let} {m_konst_dead} {m_konst_delta} G (KExpr.const c us) (KExpr.pi A B) h (Eq.refl Bool Bool.true)"
    )
}

// ================================================================
// Group C — witnesses of the judgment and of its two new rules.
// ================================================================

pub(super) fn ty_synty_p_id() -> String {
    p_weaken(&ty_synty_c_id())
}
pub(super) fn val_synty_p_id() -> String {
    p_weaken(&val_synty_c_id())
}
pub(super) fn ty_synty_p_sort_witness() -> String {
    p_weaken(&ty_synty_c_sort_witness())
}
pub(super) fn val_synty_p_sort_witness() -> String {
    p_weaken(&val_synty_c_sort_witness())
}
pub(super) fn ty_synty_p_not_total() -> String {
    p_weaken(&ty_synty_c_not_total())
}
pub(super) fn val_synty_p_not_total() -> String {
    p_weaken(&val_synty_c_not_total())
}

/// THE DELIVERABLE'S WITNESS: a REAL reflected kernel constant typed at a PI
/// type by the judgment, which no rung before this one could reach.
pub(super) fn ty_synty_p_konst_pi_witness() -> String {
    format!("SynTyP {NILCTX} {DEADCONST} {PI00}")
}

pub(super) fn val_synty_p_konst_pi_witness() -> String {
    format!("SynTyP.konstInert {NILCTX} {DEADNAME} {NILUS} {PI00} (Eq.refl (OptionType KExpr) (OptionType.none KExpr)) (Eq.refl (OptionType RecMeta) (OptionType.none RecMeta))")
}

/// ...and its SN THROUGH the capstone, not around it.
pub(super) fn ty_synty_p_sn_konst_pi_witness() -> String {
    format!("whnf_acc {DEADCONST}")
}

pub(super) fn val_synty_p_sn_konst_pi_witness() -> String {
    format!("synTyP_sn {NILCTX} {DEADCONST} {PI00} synTyP_konst_pi_witness")
}

/// The conversion rule at work: the identity lambda typed at `pi (sort 0)
/// (bvar 0)`, a Pi type whose codomain is a VARIABLE. Both codomains are non-Pi
/// formers, so both interpretations are the top candidate and the premise is
/// one `Eq.refl` — but the two TYPES are different `KExpr`s, which is the point.
pub(super) fn ty_synty_p_convi_witness() -> String {
    format!("SynTyP {NILCTX} {IDLAM0} {PI0V0}")
}

pub(super) fn val_synty_p_convi_witness() -> String {
    format!("SynTyP.convI {NILCTX} {IDLAM0} {PI00} {PI0V0} (synTyP_id {NILCTX}) (Eq.refl (KExpr -> Type) (candInterp {PI00}))")
}

pub(super) fn ty_synty_p_sn_convi_witness() -> String {
    format!("whnf_acc {IDLAM0}")
}

pub(super) fn val_synty_p_sn_convi_witness() -> String {
    format!("synTyP_sn {NILCTX} {IDLAM0} {PI0V0} synTyP_convI_witness")
}

/// THE CONVERSION RULE'S GENERAL CONTENT, and the reason it is not an
/// `Eq.refl`-only decoration: R8's `candInterp_lift_eq` holds at an ARBITRARY
/// type, so the judgment is closed under un-lifting a type — exactly the
/// conversion `TypingCtx.var` needs and `SynTyC` could not perform.
pub(super) const TY_R11_SYNTYP_UNLIFT_TYPE: &str = "forall (G : ListType KExpr) (e : KExpr) (T : KExpr) (d : Nat) (k : Nat), SynTyP G e (lift_at T d k) -> SynTyP G e T";

pub(super) const VAL_R11_SYNTYP_UNLIFT_TYPE: &str = "fun (G : ListType KExpr) (e : KExpr) (T : KExpr) (d : Nat) (k : Nat) (h : SynTyP G e (lift_at T d k)) => SynTyP.convI G e (lift_at T d k) T h (candInterp_lift_eq k T d)";

pub(super) const TY_R11_SYNTYP_LIFT_TYPE: &str = "forall (G : ListType KExpr) (e : KExpr) (T : KExpr) (d : Nat) (k : Nat), SynTyP G e T -> SynTyP G e (lift_at T d k)";

pub(super) const VAL_R11_SYNTYP_LIFT_TYPE: &str = "fun (G : ListType KExpr) (e : KExpr) (T : KExpr) (d : Nat) (k : Nat) (h : SynTyP G e T) => SynTyP.convI G e T (lift_at T d k) h (Eq.symm (KExpr -> Type) (candInterp (lift_at T d k)) (candInterp T) (candInterp_lift_eq k T d))";

/// NON-DEGENERACY of the const rule, the `micro_has_type` trap guard: the real
/// reflected constant IS derivable at the Pi type and R5's looping lambda is
/// still NOT, so admitting constants at every type did not collapse the
/// judgment into the total relation.
pub(super) fn ty_r11_const_pi_rule_proper() -> String {
    format!("AndType (SynTyP {NILCTX} {DEADCONST} {PI00}) (SynTyP {NILCTX} r5_omegaLam {PI00} -> Empty)")
}

pub(super) fn val_r11_const_pi_rule_proper() -> String {
    format!("AndType.intro (SynTyP {NILCTX} {DEADCONST} {PI00}) (SynTyP {NILCTX} r5_omegaLam {PI00} -> Empty) synTyP_konst_pi_witness (synTyP_not_total {NILCTX})")
}

// ================================================================
// Group D — THE CONVERSION SETTLEMENT: `candInterp` is NOT conversion-invariant.
// ================================================================

/// One `DefEq.beta` at the TYPE level. `DefEq` is the very relation
/// `TypingCtxConv.conv` converts along, and this is its cheapest constructor.
pub(super) fn ty_r11_conv_type_defeq() -> String {
    format!("DefEq {CONV_REDEX} {PI00}")
}

pub(super) fn val_r11_conv_type_defeq() -> String {
    format!("DefEq.beta {S0} {V0} {PI00}")
}

/// `candInterp` at an APP-headed type is the top candidate — definitionally,
/// because the `app` arm of its `KExpr.rec` ignores its subterms.
pub(super) const TY_R11_CANDINTERP_TOP_AT_APP: &str =
    "forall (f : KExpr) (a : KExpr) (e : KExpr), whnf_acc e -> candInterp (KExpr.app f a) e";

pub(super) const VAL_R11_CANDINTERP_TOP_AT_APP: &str =
    "fun (f : KExpr) (a : KExpr) (e : KExpr) (h : whnf_acc e) => h";

/// THE ABSTRACT INCOMPATIBILITY: no term-set interpretation of untyped `KExpr`
/// types can be conversion-invariant, top at every app-headed type, and proper
/// at `pi (sort 0) (sort 0)` — three properties, any two of which are fine.
/// Stated over an arbitrary `I` so the refutation below is an INSTANCE rather
/// than an anecdote about one definition.
pub(super) fn ty_r11_conv_top_proper_incompatible() -> String {
    format!("forall (I : KExpr -> KExpr -> Type), (forall (A : KExpr) (B : KExpr) (x : KExpr), DefEq A B -> I A x -> I B x) -> (forall (f : KExpr) (a : KExpr) (x : KExpr), whnf_acc x -> I (KExpr.app f a) x) -> (I {PI00} r5_omegaLam -> Empty) -> Empty")
}

pub(super) fn val_r11_conv_top_proper_incompatible() -> String {
    format!("fun (I : KExpr -> KExpr -> Type) (hconv : forall (A : KExpr) (B : KExpr) (x : KExpr), DefEq A B -> I A x -> I B x) (htop : forall (f : KExpr) (a : KExpr) (x : KExpr), whnf_acc x -> I (KExpr.app f a) x) (hproper : I {PI00} r5_omegaLam -> Empty) => hproper (hconv {CONV_REDEX} {PI00} r5_omegaLam r11_conv_type_defeq (htop {IDLAM0} {PI00} r5_omegaLam r5_whnfAcc_omegaLam))")
}

/// **THE SETTLEMENT.** `candInterp` is NOT conversion-invariant, so the `conv`
/// rule of `TypingCtxConv` has no counterpart in this ladder's interpretation.
pub(super) const TY_R11_CANDINTERP_CONV_REFUTED: &str = "(forall (A : KExpr) (B : KExpr) (e : KExpr), DefEq A B -> candInterp A e -> candInterp B e) -> Empty";

pub(super) fn val_r11_candinterp_conv_refuted() -> String {
    "fun (hconv : forall (A : KExpr) (B : KExpr) (e : KExpr), DefEq A B -> candInterp A e -> candInterp B e) => r11_conv_top_proper_incompatible candInterp hconv r11_candInterp_top_at_app candInterp_pi_not_total".to_string()
}

/// The EQUALITY form — R8's spelling, because `PiSet` is contravariant in its
/// domain and a lifting lemma has to equate the two membership PREDICATES.
/// Refuted for the same single β step.
pub(super) const TY_R11_CANDINTERP_CONV_EQ_REFUTED: &str = "(forall (A : KExpr) (B : KExpr), DefEq A B -> Eq (KExpr -> Type) (candInterp A) (candInterp B)) -> Empty";

pub(super) const VAL_R11_CANDINTERP_CONV_EQ_REFUTED: &str = "fun (heq : forall (A : KExpr) (B : KExpr), DefEq A B -> Eq (KExpr -> Type) (candInterp A) (candInterp B)) => r11_candInterp_conv_refuted (fun (A : KExpr) (B : KExpr) (e : KExpr) (hd : DefEq A B) (hm : candInterp A e) => Eq.substType (KExpr -> Type) (fun (qF : KExpr -> Type) => qF e) (candInterp A) (candInterp B) (heq A B hd) hm)";

/// The SHARPEST form: not even ONE step of the spec's own reduction may be
/// transported through the interpretation. `DefEq` contains `whnf_step`'s β, so
/// this is the same wall met at its narrowest — it says the obstruction is the
/// type-level β redex itself, not the size of the conversion relation.
pub(super) const TY_R11_CANDINTERP_STEP_CONV_REFUTED: &str = "(forall (A : KExpr) (B : KExpr) (e : KExpr), whnf_step A B -> candInterp A e -> candInterp B e) -> Empty";

pub(super) fn val_r11_candinterp_step_conv_refuted() -> String {
    format!("fun (hstep : forall (A : KExpr) (B : KExpr) (e : KExpr), whnf_step A B -> candInterp A e -> candInterp B e) => candInterp_pi_not_total (hstep {CONV_REDEX} {PI00} r5_omegaLam (whnf_step.beta {CONV_REDEX} {PI00} (beta_reduces.beta {S0} {V0} {PI00})) r5_whnfAcc_omegaLam)")
}

/// The three measured facts of the conversion counterexample in one
/// kernel-checked constant: the term IS in the redex type's interpretation, the
/// two types ARE definitionally equal, and the term is NOT in the reduct type's.
pub(super) fn ty_r11_conv_gap_is_real() -> String {
    let defeq = format!("(DefEq {CONV_REDEX} {PI00})");
    let out = format!("(candInterp {PI00} r5_omegaLam -> Empty)");
    format!("AndType (candInterp {CONV_REDEX} r5_omegaLam) (AndType {defeq} {out})")
}

pub(super) fn val_r11_conv_gap_is_real() -> String {
    let defeq = format!("(DefEq {CONV_REDEX} {PI00})");
    let out = format!("(candInterp {PI00} r5_omegaLam -> Empty)");
    format!("AndType.intro (candInterp {CONV_REDEX} r5_omegaLam) (AndType {defeq} {out}) r5_whnfAcc_omegaLam (AndType.intro {defeq} {out} r11_conv_type_defeq candInterp_pi_not_total)")
}

/// The POSITIVE half, and the premise `SynTyP.convI` actually carries:
/// conversion along equality of INTERPRETATIONS is sound at every `A`, `B`, `e`.
pub(super) const TY_R11_INTERPEQ_CONV: &str = "forall (A : KExpr) (B : KExpr) (e : KExpr), Eq (KExpr -> Type) (candInterp A) (candInterp B) -> candInterp A e -> candInterp B e";

pub(super) const VAL_R11_INTERPEQ_CONV: &str = "fun (A : KExpr) (B : KExpr) (e : KExpr) (h : Eq (KExpr -> Type) (candInterp A) (candInterp B)) (m : candInterp A e) => Eq.substType (KExpr -> Type) (fun (qF : KExpr -> Type) => qF e) (candInterp A) (candInterp B) h m";
