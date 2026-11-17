// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Witnesses for the quotient rules of `KernelAcceptsTcIn` / `TypingTcIn`.
//!
//! The deployed `try_quot_reduction` whnf's the major premise of a `Quot.lift`
//! (argument 5) or `Quot.ind` (argument 4) spine and, when the whnf is a
//! `Quot.mk` application, returns the function argument (argument 3) applied to
//! the quoted value, followed by the spine's trailing arguments. The rules state
//! only the syntactic redex; the major's whnf is a conversion carried into the
//! spine by `app_cong`, and trailing arguments by `app_cong` around the redex.
//! Each witness below needs one of those: a major that is a beta-redex (so the
//! rule fires only after the conversion the deployed whnf performs), a plain
//! `Quot.ind` redex, and a `Quot.lift` redex under a trailing argument.
//!
//! Every witness holds at EVERY environment, because the rules key on the
//! reflected names only, as the deployed branch keys on the kernel names.
//! The six spine positions are distinct context variables, so the witnesses
//! also show the rule picks argument 3 and the major's LAST argument.

/// A proof whose statement is assembled from the shared term fragments above.
pub(super) struct OwnedProof {
    pub(super) name: &'static str,
    pub(super) ty: String,
    pub(super) value: String,
}

/// `Quot.mk.{0} #5 #4 #0`, the major the rules eliminate.
const MK: &str = "(KExpr.app (KExpr.app (KExpr.app (KExpr.const accepts_tc_quot_mk_name (@ListType.cons Level Level.zero (@ListType.nil Level))) (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))))) (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))) (KExpr.bvar Nat.zero))";

/// The same major one binder deeper (every variable lifted by one), so that
/// `instantiate MK_LIFTED (Sort 0)` is `MK` again.
const MK_LIFTED: &str = "(KExpr.app (KExpr.app (KExpr.app (KExpr.const accepts_tc_quot_mk_name (@ListType.cons Level Level.zero (@ListType.nil Level))) (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))))) (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))))) (KExpr.bvar (Nat.succ Nat.zero)))";

/// `Quot.lift.{0,0} #5 #4 #3 #2 #1`, the spine before its major.
const LIFT_HEAD: &str = "(KExpr.app (KExpr.app (KExpr.app (KExpr.app (KExpr.app (KExpr.const accepts_tc_quot_lift_name (@ListType.cons Level Level.zero (@ListType.cons Level Level.zero (@ListType.nil Level)))) (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))))) (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))) (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero))))) (KExpr.bvar (Nat.succ (Nat.succ Nat.zero)))) (KExpr.bvar (Nat.succ Nat.zero)))";

/// `#2 #0`: argument 3 applied to the quoted value.
const RESULT: &str =
    "(KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero))";

pub(super) fn proofs() -> Vec<OwnedProof> {
    let n5 = "(KExpr.bvar (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))))";
    let n4 = "(KExpr.bvar (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))";
    let n3 = "(KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero))))";
    let n2 = "(KExpr.bvar (Nat.succ (Nat.succ Nat.zero)))";
    let n1 = "(KExpr.bvar (Nat.succ Nat.zero))";
    let n0 = "(KExpr.bvar Nat.zero)";
    let l1 = "(@ListType.cons Level Level.zero (@ListType.nil Level))";
    let l2 =
        "(@ListType.cons Level Level.zero (@ListType.cons Level Level.zero (@ListType.nil Level)))";
    let sort0 = "(KExpr.sort Level.zero)";
    let redex_major = format!("(KExpr.app (KExpr.lam {sort0} {MK_LIFTED}) {sort0})");
    let lift_beta = format!("(KExpr.app {LIFT_HEAD} {redex_major})");
    let lift_mk = format!("(KExpr.app {LIFT_HEAD} {MK})");
    let ind_mk = format!(
        "(KExpr.app (KExpr.app (KExpr.app (KExpr.app (KExpr.app (KExpr.const accepts_tc_quot_ind_name {l1}) {n5}) {n4}) {n3}) {n2}) {MK})"
    );
    let lift_rule = format!(
        "@KernelAcceptsTcIn.quot_lift R tenv G {l2} {n5} {n4} {n3} {n2} {n1} {l1} {n5} {n4} {n0}"
    );
    let beta_major = format!(
        "@KernelAcceptsTcIn.cdp R tenv G {redex_major} {MK}
    (@DefEqCDPIn.raw R {redex_major} {MK}
      (@par_reduces_cdp.beta R {sort0} {sort0} {MK_LIFTED} {MK_LIFTED} {sort0} {sort0}
        (@par_reduces_cdp.refl R {sort0}) (@par_reduces_cdp.refl R {MK_LIFTED}) (@par_reduces_cdp.refl R {sort0})))"
    );
    let refl_head = format!(
        "@KernelAcceptsTcIn.cdp R tenv G {LIFT_HEAD} {LIFT_HEAD} (@DefEqCDPIn.refl R {LIFT_HEAD})"
    );
    let lift_ty = format!(
        "forall (R : RedEnv) (tenv : KDeclEnv) (G : ListType CtxEntryIn), KernelAcceptsTcIn R tenv Bool.false G {lift_beta} {RESULT}"
    );
    let lift_value = format!(
        "fun (R : RedEnv) (tenv : KDeclEnv) (G : ListType CtxEntryIn) =>
@KernelAcceptsTcIn.trans R tenv G {lift_beta} {lift_mk} {RESULT}
  (@KernelAcceptsTcIn.app_cong R tenv G {LIFT_HEAD} {LIFT_HEAD} {redex_major} {MK}
    ({refl_head})
    ({beta_major}))
  ({lift_rule})"
    );
    let ind_ty = format!(
        "forall (R : RedEnv) (tenv : KDeclEnv) (G : ListType CtxEntryIn), KernelAcceptsTcIn R tenv Bool.false G {ind_mk} {RESULT}"
    );
    let ind_value = format!(
        "fun (R : RedEnv) (tenv : KDeclEnv) (G : ListType CtxEntryIn) =>
@KernelAcceptsTcIn.quot_ind R tenv G {l1} {n5} {n4} {n3} {n2} {l1} {n5} {n4} {n0}"
    );
    let extra = "(KExpr.sort (Level.succ Level.zero))";
    let lift_extra_ty = format!(
        "forall (R : RedEnv) (tenv : KDeclEnv) (G : ListType CtxEntryIn), KernelAcceptsTcIn R tenv Bool.false G (KExpr.app {lift_mk} {extra}) (KExpr.app {RESULT} {extra})"
    );
    let lift_extra_value = format!(
        "fun (R : RedEnv) (tenv : KDeclEnv) (G : ListType CtxEntryIn) =>
@KernelAcceptsTcIn.app_cong R tenv G {lift_mk} {RESULT} {extra} {extra}
  ({lift_rule})
  (@KernelAcceptsTcIn.cdp R tenv G {extra} {extra} (@DefEqCDPIn.refl R {extra}))"
    );
    let sound = |name: &str, target: &str, result: &str| {
        (
            format!(
                "forall (R : RedEnv) (tenv : KDeclEnv) (G : ListType CtxEntryIn), TypingTcIn R tenv Bool.false G {target} {result}"
            ),
            format!(
                "fun (R : RedEnv) (tenv : KDeclEnv) (G : ListType CtxEntryIn) =>
kernel_accepts_tc_in_sound R tenv Bool.false G {target} {result} (@{name} R tenv G)"
            ),
        )
    };
    let (lift_sound_ty, lift_sound_value) =
        sound("kernel_accepts_tc_in_quot_lift", &lift_beta, RESULT);
    let (ind_sound_ty, ind_sound_value) = sound("kernel_accepts_tc_in_quot_ind", &ind_mk, RESULT);
    let (extra_sound_ty, extra_sound_value) = sound(
        "kernel_accepts_tc_in_quot_lift_extra_arg",
        &format!("(KExpr.app {lift_mk} {extra})"),
        &format!("(KExpr.app {RESULT} {extra})"),
    );
    vec![
        OwnedProof {
            name: "kernel_accepts_tc_in_quot_lift",
            ty: lift_ty,
            value: lift_value,
        },
        OwnedProof {
            name: "accepts_tc_quot_lift_sound",
            ty: lift_sound_ty,
            value: lift_sound_value,
        },
        OwnedProof {
            name: "kernel_accepts_tc_in_quot_ind",
            ty: ind_ty,
            value: ind_value,
        },
        OwnedProof {
            name: "accepts_tc_quot_ind_sound",
            ty: ind_sound_ty,
            value: ind_sound_value,
        },
        OwnedProof {
            name: "kernel_accepts_tc_in_quot_lift_extra_arg",
            ty: lift_extra_ty,
            value: lift_extra_value,
        },
        OwnedProof {
            name: "accepts_tc_quot_lift_extra_arg_sound",
            ty: extra_sound_ty,
            value: extra_sound_value,
        },
    ]
}
