// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Witnesses for K-like reduction (`KernelAcceptsTcIn.k_like` /
//! `TypingTcIn.k_like`).
//!
//! The deployed `try_to_cnstr_when_k` (`clean-kernel/src/tc/reduction/mod.rs`)
//! runs before the major's whnf whenever `rec_val.is_k`: it infers the major's
//! type, whnf's it to `I params indices`, requires the head to be the
//! recursor's inductive, builds `ctor params` from the type's arguments, infers
//! that constructor application's type and requires it def-eq to the major's.
//! The K flag and what admission guarantees about it (one field-free
//! constructor of a non-mutual inductive in `Prop`) are `RecKAdmitIn`; the rest
//! are the arm's premises. The major reaching the constructor is a conversion,
//! carried into the recursor spine by `app_cong` and followed by ordinary iota.
//!
//! Every witness runs at `accepts_k_env`: a one-constructor `Prop` inductive
//! `KP` (the anonymous name) with constructor `accepts_k_cn` and a K-flagged
//! recursor `accepts_k_rn`, and the type environment `accepts_k_tenv` that
//! types the constructor. The reflected seed's own K-flagged recursor, `Eq.rec`,
//! carries the admission fact too (`accepts_k_eq_rec_admitted`), so the
//! predicate is not a fixture's invention.

use super::DeclarationInput;

pub(super) const DECLARATIONS: &[DeclarationInput] = &[
    DeclarationInput::Data(
        r"def accepts_k_cn : Name := Name.str Name.anonymous (Nat.succ (Nat.succ Nat.zero))",
    ),
    DeclarationInput::Data(
        r"def accepts_k_rn : Name := Name.str Name.anonymous (Nat.succ (Nat.succ (Nat.succ Nat.zero)))",
    ),
    DeclarationInput::Data(
        r"def accepts_k_type : KExpr := KExpr.const Name.anonymous (@ListType.nil Level)",
    ),
    DeclarationInput::Data(
        r"def accepts_k_ctor : KExpr := KExpr.const accepts_k_cn (@ListType.nil Level)",
    ),
    DeclarationInput::Data(
        r"def accepts_k_ind_meta : KIndMeta := KIndMeta.mk (KConstSig.mk (@ListType.nil Name) (KExpr.sort Level.zero)) Nat.zero Nat.zero (@ListType.cons Name accepts_k_cn (@ListType.nil Name)) (@ListType.cons Name Name.anonymous (@ListType.nil Name))",
    ),
    DeclarationInput::Data(
        r"def accepts_k_ctor_meta : KCtorMeta := KCtorMeta.mk (KConstSig.mk (@ListType.nil Name) accepts_k_type) Name.anonymous Nat.zero Nat.zero Nat.zero",
    ),
    DeclarationInput::Data(
        r"def accepts_k_rhs : KExpr := KExpr.lam (KExpr.pi accepts_k_type (KExpr.sort (Level.param Name.anonymous))) (KExpr.lam (KExpr.app (KExpr.bvar Nat.zero) accepts_k_ctor) (KExpr.bvar Nat.zero))",
    ),
    DeclarationInput::Data(
        r"def accepts_k_rec_sig : KConstSig := KConstSig.mk (@ListType.cons Name Name.anonymous (@ListType.nil Name)) (KExpr.pi (KExpr.pi accepts_k_type (KExpr.sort (Level.param Name.anonymous))) (KExpr.pi (KExpr.app (KExpr.bvar Nat.zero) accepts_k_ctor) (KExpr.pi accepts_k_type (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero)))))",
    ),
    DeclarationInput::Data(
        r"def accepts_k_rec_meta : RecMeta := RecMeta.mk Nat.zero (Nat.succ Nat.zero) (Nat.succ Nat.zero) Nat.zero Bool.true accepts_k_rec_sig (Nat.succ Nat.zero)",
    ),
    DeclarationInput::Data(
        r"def accepts_k_env : RedEnv := RedEnv.mk (RecEnv.addRec RecEnv.empty accepts_k_rn accepts_k_rec_meta (RecRules.cons (RecRule.mk accepts_k_cn Nat.zero accepts_k_rhs) RecRules.nil)) DefEnv.empty (IndCtorEnv.addCtor (IndCtorEnv.addInd IndCtorEnv.empty Name.anonymous accepts_k_ind_meta) accepts_k_cn accepts_k_ctor_meta)",
    ),
    DeclarationInput::Data(
        r"def accepts_k_tenv : KDeclEnv := fun (nm : Name) => opt_pick KConstSig (name_eqb nm accepts_k_cn) (KConstSig.mk (@ListType.nil Name) accepts_k_type) (@OptionType.none KConstSig)",
    ),
    DeclarationInput::Data(
        r"def accepts_k_context : ListType CtxEntryIn := @ListType.cons CtxEntryIn (CtxEntryIn.decl accepts_k_type) (@ListType.nil CtxEntryIn)",
    ),
    DeclarationInput::Proof(
        "accepts_k_admit",
        r"RecKAdmitIn accepts_k_env accepts_k_rn Name.anonymous accepts_k_rec_meta accepts_k_cn",
        r"@RecKAdmitIn.mk accepts_k_env accepts_k_rn Name.anonymous accepts_k_rec_meta accepts_k_cn accepts_k_rhs accepts_k_ctor_meta accepts_k_ind_meta
  (@Eq.refl (OptionType RecMeta) (@OptionType.some RecMeta accepts_k_rec_meta))
  (@Eq.refl Nat (Nat.succ Nat.zero))
  (@Eq.refl (OptionType RecRules) (@OptionType.some RecRules (RecRules.cons (RecRule.mk accepts_k_cn Nat.zero accepts_k_rhs) RecRules.nil)))
  (@Eq.refl (OptionType KCtorMeta) (@OptionType.some KCtorMeta accepts_k_ctor_meta))
  (@Eq.refl Name Name.anonymous)
  (@Eq.refl Nat Nat.zero)
  (@Eq.refl (OptionType KIndMeta) (@OptionType.some KIndMeta accepts_k_ind_meta))
  (@Eq.refl (ListType Name) (@ListType.cons Name accepts_k_cn (@ListType.nil Name)))
  (@Eq.refl (ListType Name) (@ListType.cons Name Name.anonymous (@ListType.nil Name)))
  (@Eq.refl Bool Bool.true)",
    ),
    DeclarationInput::Proof(
        "kernel_accepts_tc_in_k_like",
        r"KernelAcceptsTcIn accepts_k_env accepts_k_tenv Bool.false accepts_k_context (KExpr.bvar Nat.zero) accepts_k_ctor",
        r"@KernelAcceptsTcIn.k_like accepts_k_env accepts_k_tenv accepts_k_context accepts_k_rn Name.anonymous accepts_k_rec_meta accepts_k_cn (@ListType.nil Level)
  (KExpr.bvar Nat.zero) accepts_k_type accepts_k_type accepts_k_type
  accepts_k_admit
  (@KernelAcceptsTcIn.bvar accepts_k_env accepts_k_tenv accepts_k_context Nat.zero (CtxEntryIn.decl accepts_k_type) (@Eq.refl (OptionType CtxEntryIn) (@OptionType.some CtxEntryIn (CtxEntryIn.decl accepts_k_type))))
  (@KernelAcceptsTcIn.cdp accepts_k_env accepts_k_tenv accepts_k_context accepts_k_type accepts_k_type (@DefEqCDPIn.refl accepts_k_env accepts_k_type))
  (@Eq.refl (OptionType Name) (@OptionType.some Name Name.anonymous))
  (@KernelAcceptsTcIn.const accepts_k_env accepts_k_tenv accepts_k_context accepts_k_cn (@ListType.nil Level) accepts_k_type accepts_k_type (@Eq.refl (OptionType KExpr) (@OptionType.some KExpr accepts_k_type)) (KExprUniverseEq.const Name.anonymous (@ListType.nil Level) (@ListType.nil Level) LevelListEqSem.nil))
  (@KernelAcceptsTcIn.cdp accepts_k_env accepts_k_tenv accepts_k_context accepts_k_type accepts_k_type (@DefEqCDPIn.refl accepts_k_env accepts_k_type))",
    ),
    DeclarationInput::Proof(
        "accepts_tc_k_like_sound",
        r"TypingTcIn accepts_k_env accepts_k_tenv Bool.false accepts_k_context (KExpr.bvar Nat.zero) accepts_k_ctor",
        r"kernel_accepts_tc_in_sound accepts_k_env accepts_k_tenv Bool.false accepts_k_context (KExpr.bvar Nat.zero) accepts_k_ctor kernel_accepts_tc_in_k_like",
    ),
    // The rule's instances are proof irrelevance at a proposition: given the
    // major's type is typed at a sort converting to `Sort 0` (regularity plus
    // the admission fact, NOT a premise the deployed step checks), the target
    // derives the same conversion without the K rule.
    DeclarationInput::Proof(
        "typing_tc_in_k_like_is_proof_irrel",
        r"forall (R : RedEnv) (tenv : KDeclEnv) (G : ListType CtxEntryIn) (major : KExpr) (W : KExpr) (ctor : KExpr) (S : KExpr), TypingTcIn R tenv Bool.true G major W -> TypingTcIn R tenv Bool.true G ctor W -> TypingTcIn R tenv Bool.true G W S -> TypingTcIn R tenv Bool.false G S (KExpr.sort Level.zero) -> TypingTcIn R tenv Bool.false G major ctor",
        r"fun (R : RedEnv) (tenv : KDeclEnv) (G : ListType CtxEntryIn) (major : KExpr) (W : KExpr) (ctor : KExpr) (S : KExpr)
  (hm : TypingTcIn R tenv Bool.true G major W) (hc : TypingTcIn R tenv Bool.true G ctor W)
  (hW : TypingTcIn R tenv Bool.true G W S) (hS : TypingTcIn R tenv Bool.false G S (KExpr.sort Level.zero)) =>
@TypingTcIn.proof_irrel R tenv G major W ctor hm (@TypingTcIn.conv R tenv G W S (KExpr.sort Level.zero) hW hS) hc",
    ),
];

/// The iota step after the K conversion, at `accepts_k_env`: the recursor
/// applied to a motive, a minor and the HYPOTHESIS `#0` (not a constructor)
/// reduces to the minor. The constructor is reached only through `k_like`.
pub(super) fn iota_witness() -> (String, String) {
    let motive = "(KExpr.lam accepts_k_type (KExpr.sort Level.zero))";
    let minor = "(KExpr.sort (Level.succ Level.zero))";
    let us = "(@ListType.cons Level Level.zero (@ListType.nil Level))";
    let head = format!("(KExpr.app (KExpr.app (KExpr.const accepts_k_rn {us}) {motive}) {minor})");
    let redex = format!("(KExpr.app {head} (KExpr.bvar Nat.zero))");
    let at_ctor = format!("(KExpr.app {head} accepts_k_ctor)");
    let rhs_inst = format!("(recursor_rhs_instance accepts_k_rec_sig accepts_k_rhs {us})");
    let contractum = format!("(KExpr.app (KExpr.app {rhs_inst} {motive}) {minor})");
    let env = "accepts_k_env";
    let ten = "accepts_k_tenv";
    let g = "accepts_k_context";
    let ty = format!("KernelAcceptsTcIn {env} {ten} Bool.false {g} {redex} {minor}");
    let k_step = format!(
        "(@KernelAcceptsTcIn.app_cong {env} {ten} {g} {head} {head} (KExpr.bvar Nat.zero) accepts_k_ctor (@KernelAcceptsTcIn.cdp {env} {ten} {g} {head} {head} (@DefEqCDPIn.refl {env} {head})) kernel_accepts_tc_in_k_like)"
    );
    let iota = format!(
        "(accepts_tc_iota {env} {ten} {g} {at_ctor} accepts_k_rn accepts_k_rec_meta accepts_k_ctor accepts_k_cn (RecRule.mk accepts_k_cn Nat.zero accepts_k_rhs) {contractum} (@Eq.refl (OptionType Name) (@OptionType.some Name accepts_k_rn)) (@Eq.refl (OptionType RecMeta) (@OptionType.some RecMeta accepts_k_rec_meta)) (@Eq.refl (OptionType KExpr) (@OptionType.some KExpr accepts_k_ctor)) (@Eq.refl (OptionType Name) (@OptionType.some Name accepts_k_cn)) (@Eq.refl (OptionType RecRule) (@OptionType.some RecRule (RecRule.mk accepts_k_cn Nat.zero accepts_k_rhs))) (@Eq.refl (OptionType KExpr) (@OptionType.some KExpr {contractum})))"
    );
    let inner = format!("(KExpr.app {rhs_inst} {motive})");
    let after = format!("(KExpr.lam (KExpr.app {motive} accepts_k_ctor) (KExpr.bvar Nat.zero))");
    let beta1 = format!(
        "(accepts_tc_app_l {env} {ten} {g} {inner} {after} {minor} (accepts_tc_beta {env} {ten} {g} (KExpr.pi accepts_k_type (KExpr.sort Level.zero)) (KExpr.lam (KExpr.app (KExpr.bvar Nat.zero) accepts_k_ctor) (KExpr.bvar Nat.zero)) {motive}))"
    );
    let mid = format!("(KExpr.app {after} {minor})");
    let beta2 = format!(
        "(accepts_tc_beta {env} {ten} {g} (KExpr.app {motive} accepts_k_ctor) (KExpr.bvar Nat.zero) {minor})"
    );
    let value = format!(
        "@KernelAcceptsTcIn.trans {env} {ten} {g} {redex} {at_ctor} {minor} {k_step} (@KernelAcceptsTcIn.trans {env} {ten} {g} {at_ctor} {contractum} {minor} {iota} (@KernelAcceptsTcIn.trans {env} {ten} {g} {contractum} {mid} {minor} {beta1} {beta2}))"
    );
    (ty, value)
}

/// The reflected seed's own K-flagged recursor, `Eq.rec`, satisfies the
/// admission predicate: every fact is a computation over the generated
/// `kernel_core_red_env` (its K flag, its one field-free rule for `Eq.refl`,
/// `Eq`'s non-mutual one-constructor metadata and its signature ending in
/// `Sort 0`). The rule's right-hand side is read off the environment by the
/// model's own lookup, never typed in. Tags are the validated interning
/// table's: `(eq, eq_refl, eq_rec)`.
pub(super) fn seed_witness(eq: u64, eq_refl: u64, eq_rec: u64) -> [(String, String, String); 2] {
    let rule = format!(
        "@OptionType.rec RecRule (fun (_ : OptionType RecRule) => RecRule) (RecRule.mk Name.anonymous Nat.zero (KExpr.sort Level.zero)) (fun (r : RecRule) => r) (recrule_for (red_rec kernel_core_red_env) kcre_name_{eq_rec} kcre_name_{eq_refl})"
    );
    let env = "kernel_core_red_env";
    let value = format!(
        "@RecKAdmitIn.mk {env} kcre_name_{eq_rec} kcre_name_{eq} kcre_rec_meta_{eq_rec} kcre_name_{eq_refl} (recrule_rhs accepts_k_eq_refl_rule) kcre_ctor_meta_{eq_refl} kcre_ind_meta_{eq}
  (@Eq.refl (OptionType RecMeta) (@OptionType.some RecMeta kcre_rec_meta_{eq_rec}))
  (@Eq.refl Nat (Nat.succ Nat.zero))
  (@Eq.refl (OptionType RecRules) (@OptionType.some RecRules (RecRules.cons (RecRule.mk kcre_name_{eq_refl} Nat.zero (recrule_rhs accepts_k_eq_refl_rule)) RecRules.nil)))
  (@Eq.refl (OptionType KCtorMeta) (@OptionType.some KCtorMeta kcre_ctor_meta_{eq_refl}))
  (@Eq.refl Name kcre_name_{eq})
  (@Eq.refl Nat Nat.zero)
  (@Eq.refl (OptionType KIndMeta) (@OptionType.some KIndMeta kcre_ind_meta_{eq}))
  (@Eq.refl (ListType Name) (@ListType.cons Name kcre_name_{eq_refl} (@ListType.nil Name)))
  (@Eq.refl (ListType Name) (@ListType.cons Name kcre_name_{eq} (@ListType.nil Name)))
  (@Eq.refl Bool Bool.true)"
    );
    [
        (
            "accepts_k_eq_refl_rule".to_string(),
            "RecRule".to_string(),
            rule,
        ),
        (
            "accepts_k_eq_rec_admitted".to_string(),
            format!(
                "RecKAdmitIn {env} kcre_name_{eq_rec} kcre_name_{eq} kcre_rec_meta_{eq_rec} kcre_name_{eq_refl}"
            ),
            value,
        ),
    ]
}
