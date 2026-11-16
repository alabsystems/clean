// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Successful actual three-way weak-head computation constructs semantic conversion.
//!
//! Arbitrary RedEnv: no faithfulness, typing, closure, normalization or returned
//! conversion premise. The major pre-pass is justified by the smaller-fuel IH;
//! actual guarded iota tail success is retained throughout swap-and-fire.
//! All nine KExpr cases and all three WhStepR cases use the current operators.
//! Projection here has only the congruence behavior of the current WH3 model;
//! this does not add projection beta or claim production-kernel refinement.
//!
//! Registered after semantic injectivity and the three-way fuel definitions.
//! Independent exact-source proof development is retained in
//! scratch/semantic_wh3_soundness_in.md; current corpus replay remains the gate.

use crate::spec::error::SpecError;
use crate::spec::Specification;

// The six structural proof terms are finite ports of the constrained existing
// chain, not alternative operational definitions. The retained offline port
// script makes the exact environment/name substitutions independently visible.
const DECLARATIONS: &[(&str, &str, &str)] = &[
    (
        "const_delta_step_in",
        r"forall (R : RedEnv) (n : Name) (us : ListType Level) (v : KExpr) (h : @Eq (OptionType KExpr) (kdef_value_at (red_def R) n us) (@OptionType.some KExpr v)),
 delta_step (red_def R) (KExpr.const n us) v",
        r"fun (R : RedEnv) (n : Name) (us : ListType Level) (v : KExpr) (h : @Eq (OptionType KExpr) (kdef_value_at (red_def R) n us) (@OptionType.some KExpr v)) =>
 opt_bind_some_intro Name KExpr (kexpr_const_name (kapp_fn (KExpr.const n us))) (fun (dname : Name) => opt_bind KExpr KExpr (kdef_value_at (red_def R) dname us) (fun (val : KExpr) => @OptionType.some KExpr (apply_spine (kapp_args (KExpr.const n us)) val))) n v (@Eq.refl (OptionType Name) (@OptionType.some Name n)) (opt_bind_some_intro KExpr KExpr (kdef_value_at (red_def R) n us) (fun (val : KExpr) => @OptionType.some KExpr (apply_spine (kapp_args (KExpr.const n us)) val)) v v h (@Eq.refl (OptionType KExpr) (@OptionType.some KExpr v)))",
    ),
    (
        "whc3_iota_sound_at_in",
        r"forall (R : RedEnv) (e : KExpr) (pfx : ListType KExpr) (sfx : ListType KExpr) (kk : KExpr) (e2 : KExpr) (recname : Name) (meta : RecMeta) (major : KExpr) (wmajor : KExpr) (cname : Name) (rule : RecRule) (r : KExpr) (hpfx : @Eq (ListType KExpr) (list_take (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args e)) pfx) (hsfx : @Eq (ListType KExpr) (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args e)) sfx) (hkk : @Eq KExpr (apply_spine pfx (kapp_fn e)) kk) (he2 : @Eq KExpr (apply_spine sfx (KExpr.app kk wmajor)) e2) (hmaj : par_reduces_cd_star R major wmajor) (h1 : @Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (@OptionType.some Name recname)) (h2 : @Eq (OptionType RecMeta) (recmeta_for (red_rec R) recname) (@OptionType.some RecMeta meta)) (h3 : @Eq (OptionType KExpr) (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args e))) (@OptionType.some KExpr major)) (h4 : @Eq (OptionType Name) (kexpr_const_name (kapp_fn wmajor)) (@OptionType.some Name cname)) (h5 : @Eq (OptionType RecRule) (recrule_for (red_rec R) recname cname) (@OptionType.some RecRule rule)) (h7 : @Eq (OptionType KExpr) (iota_contractum_at meta rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args wmajor)) (@OptionType.some KExpr r)),
 par_reduces_cd_star R e r",
        r"fun (R : RedEnv) (e : KExpr) (pfx : ListType KExpr) (sfx : ListType KExpr) (kk : KExpr) (e2 : KExpr) (recname : Name) (meta : RecMeta) (major : KExpr) (wmajor : KExpr) (cname : Name) (rule : RecRule) (r : KExpr) (hpfx : @Eq (ListType KExpr) (list_take (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args e)) pfx) (hsfx : @Eq (ListType KExpr) (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args e)) sfx) (hkk : @Eq KExpr (apply_spine pfx (kapp_fn e)) kk) (he2 : @Eq KExpr (apply_spine sfx (KExpr.app kk wmajor)) e2) (hmaj : par_reduces_cd_star R major wmajor) (h1 : @Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (@OptionType.some Name recname)) (h2 : @Eq (OptionType RecMeta) (recmeta_for (red_rec R) recname) (@OptionType.some RecMeta meta)) (h3 : @Eq (OptionType KExpr) (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args e))) (@OptionType.some KExpr major)) (h4 : @Eq (OptionType Name) (kexpr_const_name (kapp_fn wmajor)) (@OptionType.some Name cname)) (h5 : @Eq (OptionType RecRule) (recrule_for (red_rec R) recname cname) (@OptionType.some RecRule rule)) (h7 : @Eq (OptionType KExpr) (iota_contractum_at meta rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args wmajor)) (@OptionType.some KExpr r)) =>
 par_reduces_cd_star_trans R e e2 r (Eq.substType KExpr (fun (ZZ : KExpr) => par_reduces_cd_star R ZZ e2) (apply_spine sfx (KExpr.app kk major)) e (Eq.trans KExpr (apply_spine sfx (KExpr.app kk major)) (apply_spine (list_append pfx (@ListType.cons KExpr major sfx)) (kapp_fn e)) e (Eq.substType KExpr (fun (ZZ : KExpr) => @Eq KExpr (apply_spine sfx (KExpr.app ZZ major)) (apply_spine (list_append pfx (@ListType.cons KExpr major sfx)) (kapp_fn e))) (apply_spine pfx (kapp_fn e)) kk hkk (Eq.symm KExpr (apply_spine (list_append pfx (@ListType.cons KExpr major sfx)) (kapp_fn e)) (apply_spine (@ListType.cons KExpr major sfx) (apply_spine pfx (kapp_fn e))) (apply_spine_append pfx (@ListType.cons KExpr major sfx) (kapp_fn e)))) (Eq.trans KExpr (apply_spine (list_append pfx (@ListType.cons KExpr major sfx)) (kapp_fn e)) (apply_spine (kapp_args e) (kapp_fn e)) e (Eq.cong (ListType KExpr) KExpr (fun (LL : ListType KExpr) => apply_spine LL (kapp_fn e)) (list_append pfx (@ListType.cons KExpr major sfx)) (kapp_args e) (Eq.substType (ListType KExpr) (fun (LL : ListType KExpr) => @Eq (ListType KExpr) (list_append LL (@ListType.cons KExpr major sfx)) (kapp_args e)) (list_take (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args e)) pfx hpfx (Eq.substType (ListType KExpr) (fun (MM : ListType KExpr) => @Eq (ListType KExpr) (list_append (list_take (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args e)) (@ListType.cons KExpr major MM)) (kapp_args e)) (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args e)) sfx hsfx (list_split_at_head (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args e) major h3)))) (kapp_spine_roundtrip e))) (Eq.substType KExpr (fun (ZZ : KExpr) => par_reduces_cd_star R (apply_spine sfx (KExpr.app kk major)) ZZ) (apply_spine sfx (KExpr.app kk wmajor)) e2 he2 (par_reduces_cd_star_spine R sfx (KExpr.app kk major) (KExpr.app kk wmajor) (par_reduces_cd_star_app R kk kk major wmajor (@par_reduces_cd_star.refl R kk) hmaj)))) (par_subsumes_par_cd_star R e2 r (@par_reduces_cd.iota R e2 r (whc_fires_plain_gen (red_rec R) e2 recname meta wmajor cname rule r (Eq.trans (OptionType Name) (kexpr_const_name (kapp_fn e2)) (kexpr_const_name (kapp_fn e)) (@OptionType.some Name recname) (Eq.cong KExpr (OptionType Name) (fun (ZZ : KExpr) => kexpr_const_name ZZ) (kapp_fn e2) (kapp_fn e) (Eq.substType KExpr (fun (ZZ : KExpr) => @Eq KExpr (kapp_fn ZZ) (kapp_fn e)) (apply_spine sfx (KExpr.app kk wmajor)) e2 he2 (Eq.trans KExpr (kapp_fn (apply_spine sfx (KExpr.app kk wmajor))) (kapp_fn kk) (kapp_fn e) (kapp_fn_apply_spine sfx (KExpr.app kk wmajor)) (Eq.substType KExpr (fun (ZZ : KExpr) => @Eq KExpr (kapp_fn ZZ) (kapp_fn e)) (apply_spine pfx (kapp_fn e)) kk hkk (Eq.trans KExpr (kapp_fn (apply_spine pfx (kapp_fn e))) (kapp_fn (kapp_fn e)) (kapp_fn e) (kapp_fn_apply_spine pfx (kapp_fn e)) (kapp_fn_kapp_fn e)))))) h1) h2 (Eq.cong (ListType KExpr) (OptionType KExpr) (fun (LL : ListType KExpr) => list_head LL) (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args e2)) (@ListType.cons KExpr wmajor sfx) (Eq.trans (ListType KExpr) (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args e2)) (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (list_append pfx (@ListType.cons KExpr wmajor sfx))) (@ListType.cons KExpr wmajor sfx) (Eq.cong (ListType KExpr) (ListType KExpr) (fun (LL : ListType KExpr) => list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) LL) (kapp_args e2) (list_append pfx (@ListType.cons KExpr wmajor sfx)) (Eq.substType KExpr (fun (ZZ : KExpr) => @Eq (ListType KExpr) (kapp_args ZZ) (list_append pfx (@ListType.cons KExpr wmajor sfx))) (apply_spine sfx (KExpr.app kk wmajor)) e2 he2 (Eq.trans (ListType KExpr) (kapp_args (apply_spine sfx (KExpr.app kk wmajor))) (list_append (list_append (kapp_args kk) (@ListType.cons KExpr wmajor (@ListType.nil KExpr))) sfx) (list_append pfx (@ListType.cons KExpr wmajor sfx)) (kapp_args_apply_spine sfx (KExpr.app kk wmajor)) (Eq.trans (ListType KExpr) (list_append (list_append (kapp_args kk) (@ListType.cons KExpr wmajor (@ListType.nil KExpr))) sfx) (list_append (list_append pfx (@ListType.cons KExpr wmajor (@ListType.nil KExpr))) sfx) (list_append pfx (@ListType.cons KExpr wmajor sfx)) (Eq.cong (ListType KExpr) (ListType KExpr) (fun (LL : ListType KExpr) => list_append (list_append LL (@ListType.cons KExpr wmajor (@ListType.nil KExpr))) sfx) (kapp_args kk) pfx (Eq.substType KExpr (fun (ZZ : KExpr) => @Eq (ListType KExpr) (kapp_args ZZ) pfx) (apply_spine pfx (kapp_fn e)) kk hkk (Eq.trans (ListType KExpr) (kapp_args (apply_spine pfx (kapp_fn e))) (list_append (kapp_args (kapp_fn e)) pfx) pfx (kapp_args_apply_spine pfx (kapp_fn e)) (Eq.trans (ListType KExpr) (list_append (kapp_args (kapp_fn e)) pfx) (list_append (@ListType.nil KExpr) pfx) pfx (Eq.cong (ListType KExpr) (ListType KExpr) (fun (LL : ListType KExpr) => list_append LL pfx) (kapp_args (kapp_fn e)) (@ListType.nil KExpr) (kapp_args_kapp_fn_nil e)) (list_append_nil pfx))))) (list_append_assoc pfx (@ListType.cons KExpr wmajor (@ListType.nil KExpr)) sfx))))) (Eq.substType Nat (fun (ZZ : Nat) => @Eq (ListType KExpr) (list_drop ZZ (list_append pfx (@ListType.cons KExpr wmajor sfx))) (@ListType.cons KExpr wmajor sfx)) (list_length pfx) (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (Eq.substType (ListType KExpr) (fun (LL : ListType KExpr) => @Eq Nat (list_length LL) (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (list_take (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args e)) pfx hpfx (list_take_len_of_head (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args e) major h3)) (list_drop_append_gen pfx Nat.zero (@ListType.cons KExpr wmajor sfx))))) h4 h5 (whc_swap_tail e pfx sfx kk e2 recname meta major wmajor cname rule r hpfx hsfx hkk he2 h3 h7))))",
    ),
    (
        "hiotap3_discharged_in",
        r"forall (R : RedEnv) (w : KExpr -> OptionType KExpr) (hw : forall (e : KExpr) (rr : KExpr), @Eq (OptionType KExpr) (w e) (@OptionType.some KExpr rr) -> par_reduces_cd_star R e rr) (g : KExpr) (x : KExpr) (r : KExpr) (h : @Eq WhStepR (iota_reduct_whc3 (red_rec R) w (KExpr.app g x)) (WhStepR.wstep r)),
 par_reduces_cd_star R (KExpr.app g x) r",
        r"fun (R : RedEnv) (w : KExpr -> OptionType KExpr) (hw : forall (e : KExpr) (rr : KExpr), @Eq (OptionType KExpr) (w e) (@OptionType.some KExpr rr) -> par_reduces_cd_star R e rr) (g : KExpr) (x : KExpr) (r : KExpr) (h : @Eq WhStepR (iota_reduct_whc3 (red_rec R) w (KExpr.app g x)) (WhStepR.wstep r)) =>
 iota_reduct_whc3_some_inv_type (red_rec R) w (KExpr.app g x) r (par_reduces_cd_star R (KExpr.app g x) r) h (fun (recname : Name) (meta : RecMeta) (major : KExpr) (wmajor : KExpr) (cname : Name) (rule : RecRule) (q1 : @Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.app g x))) (@OptionType.some Name recname)) (q2 : @Eq (OptionType RecMeta) (recmeta_for (red_rec R) recname) (@OptionType.some RecMeta meta)) (q3 : @Eq (OptionType KExpr) (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args (KExpr.app g x)))) (@OptionType.some KExpr major)) (q4 : @Eq (OptionType KExpr) (w major) (@OptionType.some KExpr wmajor)) (q5 : @Eq (OptionType Name) (kexpr_const_name (kapp_fn wmajor)) (@OptionType.some Name cname)) (q6 : @Eq (OptionType RecRule) (recrule_for (red_rec R) recname cname) (@OptionType.some RecRule rule)) (q7 : @Eq (OptionType KExpr) (iota_contractum_at meta rule (kexpr_const_levels (kapp_fn (KExpr.app g x))) (kapp_args (KExpr.app g x)) (kapp_args wmajor)) (@OptionType.some KExpr r)) => whc3_iota_sound_at_in R (KExpr.app g x) (list_take (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args (KExpr.app g x))) (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args (KExpr.app g x))) (apply_spine (list_take (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args (KExpr.app g x))) (kapp_fn (KExpr.app g x))) (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args (KExpr.app g x))) (KExpr.app (apply_spine (list_take (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args (KExpr.app g x))) (kapp_fn (KExpr.app g x))) wmajor)) recname meta major wmajor cname rule r (@Eq.refl (ListType KExpr) (list_take (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args (KExpr.app g x)))) (@Eq.refl (ListType KExpr) (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args (KExpr.app g x)))) (@Eq.refl KExpr (apply_spine (list_take (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args (KExpr.app g x))) (kapp_fn (KExpr.app g x)))) (@Eq.refl KExpr (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args (KExpr.app g x))) (KExpr.app (apply_spine (list_take (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args (KExpr.app g x))) (kapp_fn (KExpr.app g x))) wmajor))) (hw major wmajor q4) q1 q2 q3 q5 q6 q7)",
    ),
    (
        "reduce_app_head_wh3_par_hw_in",
        r"forall (R : RedEnv) (wh : KExpr -> OptionType KExpr) (hw : forall (e : KExpr) (rr : KExpr), @Eq (OptionType KExpr) (wh e) (@OptionType.some KExpr rr) -> par_reduces_cd_star R e rr) (hiota3 : forall (w : KExpr -> OptionType KExpr), (forall (e : KExpr) (rr : KExpr), @Eq (OptionType KExpr) (w e) (@OptionType.some KExpr rr) -> par_reduces_cd_star R e rr) -> forall (g : KExpr) (x : KExpr) (r : KExpr), @Eq WhStepR (iota_reduct_whc3 (red_rec R) w (KExpr.app g x)) (WhStepR.wstep r) -> par_reduces_cd_star R (KExpr.app g x) r) (a : KExpr) (f : KExpr),
 (forall (y : KExpr), @Eq WhStepR (reduce_once_red_wh3 R wh f) (WhStepR.wstep y) -> par_reduces_cd_star R f y) -> forall (e2 : KExpr), @Eq WhStepR (reduce_app_head_red_wh3 R wh a f (reduce_once_red_wh3 R wh f)) (WhStepR.wstep e2) -> par_reduces_cd_star R (KExpr.app f a) e2",
        r"fun (R : RedEnv) (wh : KExpr -> OptionType KExpr) (hw : forall (e : KExpr) (rr : KExpr), @Eq (OptionType KExpr) (wh e) (@OptionType.some KExpr rr) -> par_reduces_cd_star R e rr) (hiota3 : forall (w : KExpr -> OptionType KExpr), (forall (e : KExpr) (rr : KExpr), @Eq (OptionType KExpr) (w e) (@OptionType.some KExpr rr) -> par_reduces_cd_star R e rr) -> forall (g : KExpr) (x : KExpr) (r : KExpr), @Eq WhStepR (iota_reduct_whc3 (red_rec R) w (KExpr.app g x)) (WhStepR.wstep r) -> par_reduces_cd_star R (KExpr.app g x) r) (a : KExpr) (f : KExpr) =>
 @KExpr.rec (fun (x : KExpr) => (forall (y : KExpr), @Eq WhStepR (reduce_once_red_wh3 R wh x) (WhStepR.wstep y) -> par_reduces_cd_star R x y) -> forall (e2 : KExpr), @Eq WhStepR (reduce_app_head_red_wh3 R wh a x (reduce_once_red_wh3 R wh x)) (WhStepR.wstep e2) -> par_reduces_cd_star R (KExpr.app x a) e2) (fun (n : Level) (ihf : forall (y : KExpr), @Eq WhStepR (reduce_once_red_wh3 R wh (KExpr.sort n)) (WhStepR.wstep y) -> par_reduces_cd_star R (KExpr.sort n) y) (e2 : KExpr) (h : @Eq WhStepR (reduce_app_head_red_wh3 R wh a (KExpr.sort n) (reduce_once_red_wh3 R wh (KExpr.sort n))) (WhStepR.wstep e2)) => @WhStepR.rec (fun (o : WhStepR) => @Eq WhStepR (reduce_once_red_wh3 R wh (KExpr.sort n)) o -> @Eq WhStepR (opt_app_ilift3 R wh (KExpr.sort n) a o) (WhStepR.wstep e2) -> par_reduces_cd_star R (KExpr.app (KExpr.sort n) a) e2) (fun (_hq : @Eq WhStepR (reduce_once_red_wh3 R wh (KExpr.sort n)) WhStepR.wstuck) (h2 : @Eq WhStepR (iota_reduct_whc3 (red_rec R) wh (KExpr.app (KExpr.sort n) a)) (WhStepR.wstep e2)) => hiota3 wh hw (KExpr.sort n) a e2 h2) (fun (_hs : @Eq WhStepR (reduce_once_red_wh3 R wh (KExpr.sort n)) WhStepR.wstarved) (h2 : @Eq WhStepR WhStepR.wstarved (WhStepR.wstep e2)) => wh_starved_ne_step_type e2 (par_reduces_cd_star R (KExpr.app (KExpr.sort n) a) e2) h2) (fun (f2 : KExpr) (hq : @Eq WhStepR (reduce_once_red_wh3 R wh (KExpr.sort n)) (WhStepR.wstep f2)) (h2 : @Eq WhStepR (WhStepR.wstep (KExpr.app f2 a)) (WhStepR.wstep e2)) => Eq.substType KExpr (fun (X : KExpr) => par_reduces_cd_star R (KExpr.app (KExpr.sort n) a) X) (KExpr.app f2 a) e2 (wh_step_inj (KExpr.app f2 a) e2 h2) (par_reduces_cd_star_app R (KExpr.sort n) f2 a a (ihf f2 hq) (@par_reduces_cd_star.refl R a))) (reduce_once_red_wh3 R wh (KExpr.sort n)) (@Eq.refl WhStepR (reduce_once_red_wh3 R wh (KExpr.sort n))) h) (fun (i : Nat) (ihf : forall (y : KExpr), @Eq WhStepR (reduce_once_red_wh3 R wh (KExpr.bvar i)) (WhStepR.wstep y) -> par_reduces_cd_star R (KExpr.bvar i) y) (e2 : KExpr) (h : @Eq WhStepR (reduce_app_head_red_wh3 R wh a (KExpr.bvar i) (reduce_once_red_wh3 R wh (KExpr.bvar i))) (WhStepR.wstep e2)) => @WhStepR.rec (fun (o : WhStepR) => @Eq WhStepR (reduce_once_red_wh3 R wh (KExpr.bvar i)) o -> @Eq WhStepR (opt_app_ilift3 R wh (KExpr.bvar i) a o) (WhStepR.wstep e2) -> par_reduces_cd_star R (KExpr.app (KExpr.bvar i) a) e2) (fun (_hq : @Eq WhStepR (reduce_once_red_wh3 R wh (KExpr.bvar i)) WhStepR.wstuck) (h2 : @Eq WhStepR (iota_reduct_whc3 (red_rec R) wh (KExpr.app (KExpr.bvar i) a)) (WhStepR.wstep e2)) => hiota3 wh hw (KExpr.bvar i) a e2 h2) (fun (_hs : @Eq WhStepR (reduce_once_red_wh3 R wh (KExpr.bvar i)) WhStepR.wstarved) (h2 : @Eq WhStepR WhStepR.wstarved (WhStepR.wstep e2)) => wh_starved_ne_step_type e2 (par_reduces_cd_star R (KExpr.app (KExpr.bvar i) a) e2) h2) (fun (f2 : KExpr) (hq : @Eq WhStepR (reduce_once_red_wh3 R wh (KExpr.bvar i)) (WhStepR.wstep f2)) (h2 : @Eq WhStepR (WhStepR.wstep (KExpr.app f2 a)) (WhStepR.wstep e2)) => Eq.substType KExpr (fun (X : KExpr) => par_reduces_cd_star R (KExpr.app (KExpr.bvar i) a) X) (KExpr.app f2 a) e2 (wh_step_inj (KExpr.app f2 a) e2 h2) (par_reduces_cd_star_app R (KExpr.bvar i) f2 a a (ihf f2 hq) (@par_reduces_cd_star.refl R a))) (reduce_once_red_wh3 R wh (KExpr.bvar i)) (@Eq.refl WhStepR (reduce_once_red_wh3 R wh (KExpr.bvar i))) h) (fun (f : KExpr) (a2 : KExpr) (_c0 : ((forall (y : KExpr), @Eq WhStepR (reduce_once_red_wh3 R wh f) (WhStepR.wstep y) -> par_reduces_cd_star R f y) -> forall (e2 : KExpr), @Eq WhStepR (reduce_app_head_red_wh3 R wh a f (reduce_once_red_wh3 R wh f)) (WhStepR.wstep e2) -> par_reduces_cd_star R (KExpr.app f a) e2)) (_c1 : ((forall (y : KExpr), @Eq WhStepR (reduce_once_red_wh3 R wh a2) (WhStepR.wstep y) -> par_reduces_cd_star R a2 y) -> forall (e2 : KExpr), @Eq WhStepR (reduce_app_head_red_wh3 R wh a a2 (reduce_once_red_wh3 R wh a2)) (WhStepR.wstep e2) -> par_reduces_cd_star R (KExpr.app a2 a) e2)) (ihf : forall (y : KExpr), @Eq WhStepR (reduce_once_red_wh3 R wh (KExpr.app f a2)) (WhStepR.wstep y) -> par_reduces_cd_star R (KExpr.app f a2) y) (e2 : KExpr) (h : @Eq WhStepR (reduce_app_head_red_wh3 R wh a (KExpr.app f a2) (reduce_once_red_wh3 R wh (KExpr.app f a2))) (WhStepR.wstep e2)) => @WhStepR.rec (fun (o : WhStepR) => @Eq WhStepR (reduce_once_red_wh3 R wh (KExpr.app f a2)) o -> @Eq WhStepR (opt_app_ilift3 R wh (KExpr.app f a2) a o) (WhStepR.wstep e2) -> par_reduces_cd_star R (KExpr.app (KExpr.app f a2) a) e2) (fun (_hq : @Eq WhStepR (reduce_once_red_wh3 R wh (KExpr.app f a2)) WhStepR.wstuck) (h2 : @Eq WhStepR (iota_reduct_whc3 (red_rec R) wh (KExpr.app (KExpr.app f a2) a)) (WhStepR.wstep e2)) => hiota3 wh hw (KExpr.app f a2) a e2 h2) (fun (_hs : @Eq WhStepR (reduce_once_red_wh3 R wh (KExpr.app f a2)) WhStepR.wstarved) (h2 : @Eq WhStepR WhStepR.wstarved (WhStepR.wstep e2)) => wh_starved_ne_step_type e2 (par_reduces_cd_star R (KExpr.app (KExpr.app f a2) a) e2) h2) (fun (f2 : KExpr) (hq : @Eq WhStepR (reduce_once_red_wh3 R wh (KExpr.app f a2)) (WhStepR.wstep f2)) (h2 : @Eq WhStepR (WhStepR.wstep (KExpr.app f2 a)) (WhStepR.wstep e2)) => Eq.substType KExpr (fun (X : KExpr) => par_reduces_cd_star R (KExpr.app (KExpr.app f a2) a) X) (KExpr.app f2 a) e2 (wh_step_inj (KExpr.app f2 a) e2 h2) (par_reduces_cd_star_app R (KExpr.app f a2) f2 a a (ihf f2 hq) (@par_reduces_cd_star.refl R a))) (reduce_once_red_wh3 R wh (KExpr.app f a2)) (@Eq.refl WhStepR (reduce_once_red_wh3 R wh (KExpr.app f a2))) h) (fun (ty : KExpr) (b : KExpr) (_c0 : ((forall (y : KExpr), @Eq WhStepR (reduce_once_red_wh3 R wh ty) (WhStepR.wstep y) -> par_reduces_cd_star R ty y) -> forall (e2 : KExpr), @Eq WhStepR (reduce_app_head_red_wh3 R wh a ty (reduce_once_red_wh3 R wh ty)) (WhStepR.wstep e2) -> par_reduces_cd_star R (KExpr.app ty a) e2)) (_c1 : ((forall (y : KExpr), @Eq WhStepR (reduce_once_red_wh3 R wh b) (WhStepR.wstep y) -> par_reduces_cd_star R b y) -> forall (e2 : KExpr), @Eq WhStepR (reduce_app_head_red_wh3 R wh a b (reduce_once_red_wh3 R wh b)) (WhStepR.wstep e2) -> par_reduces_cd_star R (KExpr.app b a) e2)) (ihf : forall (y : KExpr), @Eq WhStepR (reduce_once_red_wh3 R wh (KExpr.lam ty b)) (WhStepR.wstep y) -> par_reduces_cd_star R (KExpr.lam ty b) y) (e2 : KExpr) (h : @Eq WhStepR (reduce_app_head_red_wh3 R wh a (KExpr.lam ty b) (reduce_once_red_wh3 R wh (KExpr.lam ty b))) (WhStepR.wstep e2)) => Eq.substType KExpr (fun (X : KExpr) => par_reduces_cd_star R (KExpr.app (KExpr.lam ty b) a) X) (instantiate b a) e2 (wh_step_inj (instantiate b a) e2 h) (@par_reduces_cd_star.step R (KExpr.app (KExpr.lam ty b) a) (instantiate b a) (instantiate b a) (@par_reduces_cd.beta R ty ty b b a a (@par_reduces_cd.refl R ty) (@par_reduces_cd.refl R b) (@par_reduces_cd.refl R a)) (@par_reduces_cd_star.refl R (instantiate b a)))) (fun (ty : KExpr) (b : KExpr) (_c0 : ((forall (y : KExpr), @Eq WhStepR (reduce_once_red_wh3 R wh ty) (WhStepR.wstep y) -> par_reduces_cd_star R ty y) -> forall (e2 : KExpr), @Eq WhStepR (reduce_app_head_red_wh3 R wh a ty (reduce_once_red_wh3 R wh ty)) (WhStepR.wstep e2) -> par_reduces_cd_star R (KExpr.app ty a) e2)) (_c1 : ((forall (y : KExpr), @Eq WhStepR (reduce_once_red_wh3 R wh b) (WhStepR.wstep y) -> par_reduces_cd_star R b y) -> forall (e2 : KExpr), @Eq WhStepR (reduce_app_head_red_wh3 R wh a b (reduce_once_red_wh3 R wh b)) (WhStepR.wstep e2) -> par_reduces_cd_star R (KExpr.app b a) e2)) (ihf : forall (y : KExpr), @Eq WhStepR (reduce_once_red_wh3 R wh (KExpr.pi ty b)) (WhStepR.wstep y) -> par_reduces_cd_star R (KExpr.pi ty b) y) (e2 : KExpr) (h : @Eq WhStepR (reduce_app_head_red_wh3 R wh a (KExpr.pi ty b) (reduce_once_red_wh3 R wh (KExpr.pi ty b))) (WhStepR.wstep e2)) => @WhStepR.rec (fun (o : WhStepR) => @Eq WhStepR (reduce_once_red_wh3 R wh (KExpr.pi ty b)) o -> @Eq WhStepR (opt_app_ilift3 R wh (KExpr.pi ty b) a o) (WhStepR.wstep e2) -> par_reduces_cd_star R (KExpr.app (KExpr.pi ty b) a) e2) (fun (_hq : @Eq WhStepR (reduce_once_red_wh3 R wh (KExpr.pi ty b)) WhStepR.wstuck) (h2 : @Eq WhStepR (iota_reduct_whc3 (red_rec R) wh (KExpr.app (KExpr.pi ty b) a)) (WhStepR.wstep e2)) => hiota3 wh hw (KExpr.pi ty b) a e2 h2) (fun (_hs : @Eq WhStepR (reduce_once_red_wh3 R wh (KExpr.pi ty b)) WhStepR.wstarved) (h2 : @Eq WhStepR WhStepR.wstarved (WhStepR.wstep e2)) => wh_starved_ne_step_type e2 (par_reduces_cd_star R (KExpr.app (KExpr.pi ty b) a) e2) h2) (fun (f2 : KExpr) (hq : @Eq WhStepR (reduce_once_red_wh3 R wh (KExpr.pi ty b)) (WhStepR.wstep f2)) (h2 : @Eq WhStepR (WhStepR.wstep (KExpr.app f2 a)) (WhStepR.wstep e2)) => Eq.substType KExpr (fun (X : KExpr) => par_reduces_cd_star R (KExpr.app (KExpr.pi ty b) a) X) (KExpr.app f2 a) e2 (wh_step_inj (KExpr.app f2 a) e2 h2) (par_reduces_cd_star_app R (KExpr.pi ty b) f2 a a (ihf f2 hq) (@par_reduces_cd_star.refl R a))) (reduce_once_red_wh3 R wh (KExpr.pi ty b)) (@Eq.refl WhStepR (reduce_once_red_wh3 R wh (KExpr.pi ty b))) h) (fun (n : Name) (us : ListType Level) (ihf : forall (y : KExpr), @Eq WhStepR (reduce_once_red_wh3 R wh (KExpr.const n us)) (WhStepR.wstep y) -> par_reduces_cd_star R (KExpr.const n us) y) (e2 : KExpr) (h : @Eq WhStepR (reduce_app_head_red_wh3 R wh a (KExpr.const n us) (reduce_once_red_wh3 R wh (KExpr.const n us))) (WhStepR.wstep e2)) => @WhStepR.rec (fun (o : WhStepR) => @Eq WhStepR (reduce_once_red_wh3 R wh (KExpr.const n us)) o -> @Eq WhStepR (opt_app_ilift3 R wh (KExpr.const n us) a o) (WhStepR.wstep e2) -> par_reduces_cd_star R (KExpr.app (KExpr.const n us) a) e2) (fun (_hq : @Eq WhStepR (reduce_once_red_wh3 R wh (KExpr.const n us)) WhStepR.wstuck) (h2 : @Eq WhStepR (iota_reduct_whc3 (red_rec R) wh (KExpr.app (KExpr.const n us) a)) (WhStepR.wstep e2)) => hiota3 wh hw (KExpr.const n us) a e2 h2) (fun (_hs : @Eq WhStepR (reduce_once_red_wh3 R wh (KExpr.const n us)) WhStepR.wstarved) (h2 : @Eq WhStepR WhStepR.wstarved (WhStepR.wstep e2)) => wh_starved_ne_step_type e2 (par_reduces_cd_star R (KExpr.app (KExpr.const n us) a) e2) h2) (fun (f2 : KExpr) (hq : @Eq WhStepR (reduce_once_red_wh3 R wh (KExpr.const n us)) (WhStepR.wstep f2)) (h2 : @Eq WhStepR (WhStepR.wstep (KExpr.app f2 a)) (WhStepR.wstep e2)) => Eq.substType KExpr (fun (X : KExpr) => par_reduces_cd_star R (KExpr.app (KExpr.const n us) a) X) (KExpr.app f2 a) e2 (wh_step_inj (KExpr.app f2 a) e2 h2) (par_reduces_cd_star_app R (KExpr.const n us) f2 a a (ihf f2 hq) (@par_reduces_cd_star.refl R a))) (reduce_once_red_wh3 R wh (KExpr.const n us)) (@Eq.refl WhStepR (reduce_once_red_wh3 R wh (KExpr.const n us))) h) (fun (ty : KExpr) (v : KExpr) (b : KExpr) (_c0 : ((forall (y : KExpr), @Eq WhStepR (reduce_once_red_wh3 R wh ty) (WhStepR.wstep y) -> par_reduces_cd_star R ty y) -> forall (e2 : KExpr), @Eq WhStepR (reduce_app_head_red_wh3 R wh a ty (reduce_once_red_wh3 R wh ty)) (WhStepR.wstep e2) -> par_reduces_cd_star R (KExpr.app ty a) e2)) (_c1 : ((forall (y : KExpr), @Eq WhStepR (reduce_once_red_wh3 R wh v) (WhStepR.wstep y) -> par_reduces_cd_star R v y) -> forall (e2 : KExpr), @Eq WhStepR (reduce_app_head_red_wh3 R wh a v (reduce_once_red_wh3 R wh v)) (WhStepR.wstep e2) -> par_reduces_cd_star R (KExpr.app v a) e2)) (_c2 : ((forall (y : KExpr), @Eq WhStepR (reduce_once_red_wh3 R wh b) (WhStepR.wstep y) -> par_reduces_cd_star R b y) -> forall (e2 : KExpr), @Eq WhStepR (reduce_app_head_red_wh3 R wh a b (reduce_once_red_wh3 R wh b)) (WhStepR.wstep e2) -> par_reduces_cd_star R (KExpr.app b a) e2)) (ihf : forall (y : KExpr), @Eq WhStepR (reduce_once_red_wh3 R wh (KExpr.let_ ty v b)) (WhStepR.wstep y) -> par_reduces_cd_star R (KExpr.let_ ty v b) y) (e2 : KExpr) (h : @Eq WhStepR (reduce_app_head_red_wh3 R wh a (KExpr.let_ ty v b) (reduce_once_red_wh3 R wh (KExpr.let_ ty v b))) (WhStepR.wstep e2)) => @WhStepR.rec (fun (o : WhStepR) => @Eq WhStepR (reduce_once_red_wh3 R wh (KExpr.let_ ty v b)) o -> @Eq WhStepR (opt_app_ilift3 R wh (KExpr.let_ ty v b) a o) (WhStepR.wstep e2) -> par_reduces_cd_star R (KExpr.app (KExpr.let_ ty v b) a) e2) (fun (_hq : @Eq WhStepR (reduce_once_red_wh3 R wh (KExpr.let_ ty v b)) WhStepR.wstuck) (h2 : @Eq WhStepR (iota_reduct_whc3 (red_rec R) wh (KExpr.app (KExpr.let_ ty v b) a)) (WhStepR.wstep e2)) => hiota3 wh hw (KExpr.let_ ty v b) a e2 h2) (fun (_hs : @Eq WhStepR (reduce_once_red_wh3 R wh (KExpr.let_ ty v b)) WhStepR.wstarved) (h2 : @Eq WhStepR WhStepR.wstarved (WhStepR.wstep e2)) => wh_starved_ne_step_type e2 (par_reduces_cd_star R (KExpr.app (KExpr.let_ ty v b) a) e2) h2) (fun (f2 : KExpr) (hq : @Eq WhStepR (reduce_once_red_wh3 R wh (KExpr.let_ ty v b)) (WhStepR.wstep f2)) (h2 : @Eq WhStepR (WhStepR.wstep (KExpr.app f2 a)) (WhStepR.wstep e2)) => Eq.substType KExpr (fun (X : KExpr) => par_reduces_cd_star R (KExpr.app (KExpr.let_ ty v b) a) X) (KExpr.app f2 a) e2 (wh_step_inj (KExpr.app f2 a) e2 h2) (par_reduces_cd_star_app R (KExpr.let_ ty v b) f2 a a (ihf f2 hq) (@par_reduces_cd_star.refl R a))) (reduce_once_red_wh3 R wh (KExpr.let_ ty v b)) (@Eq.refl WhStepR (reduce_once_red_wh3 R wh (KExpr.let_ ty v b))) h) (fun (s : Name) (i : Nat) (sub : KExpr) (_c0 : ((forall (y : KExpr), @Eq WhStepR (reduce_once_red_wh3 R wh sub) (WhStepR.wstep y) -> par_reduces_cd_star R sub y) -> forall (e2 : KExpr), @Eq WhStepR (reduce_app_head_red_wh3 R wh a sub (reduce_once_red_wh3 R wh sub)) (WhStepR.wstep e2) -> par_reduces_cd_star R (KExpr.app sub a) e2)) (ihf : forall (y : KExpr), @Eq WhStepR (reduce_once_red_wh3 R wh (KExpr.proj s i sub)) (WhStepR.wstep y) -> par_reduces_cd_star R (KExpr.proj s i sub) y) (e2 : KExpr) (h : @Eq WhStepR (reduce_app_head_red_wh3 R wh a (KExpr.proj s i sub) (reduce_once_red_wh3 R wh (KExpr.proj s i sub))) (WhStepR.wstep e2)) => @WhStepR.rec (fun (o : WhStepR) => @Eq WhStepR (reduce_once_red_wh3 R wh (KExpr.proj s i sub)) o -> @Eq WhStepR (opt_app_ilift3 R wh (KExpr.proj s i sub) a o) (WhStepR.wstep e2) -> par_reduces_cd_star R (KExpr.app (KExpr.proj s i sub) a) e2) (fun (_hq : @Eq WhStepR (reduce_once_red_wh3 R wh (KExpr.proj s i sub)) WhStepR.wstuck) (h2 : @Eq WhStepR (iota_reduct_whc3 (red_rec R) wh (KExpr.app (KExpr.proj s i sub) a)) (WhStepR.wstep e2)) => hiota3 wh hw (KExpr.proj s i sub) a e2 h2) (fun (_hs : @Eq WhStepR (reduce_once_red_wh3 R wh (KExpr.proj s i sub)) WhStepR.wstarved) (h2 : @Eq WhStepR WhStepR.wstarved (WhStepR.wstep e2)) => wh_starved_ne_step_type e2 (par_reduces_cd_star R (KExpr.app (KExpr.proj s i sub) a) e2) h2) (fun (f2 : KExpr) (hq : @Eq WhStepR (reduce_once_red_wh3 R wh (KExpr.proj s i sub)) (WhStepR.wstep f2)) (h2 : @Eq WhStepR (WhStepR.wstep (KExpr.app f2 a)) (WhStepR.wstep e2)) => Eq.substType KExpr (fun (X : KExpr) => par_reduces_cd_star R (KExpr.app (KExpr.proj s i sub) a) X) (KExpr.app f2 a) e2 (wh_step_inj (KExpr.app f2 a) e2 h2) (par_reduces_cd_star_app R (KExpr.proj s i sub) f2 a a (ihf f2 hq) (@par_reduces_cd_star.refl R a))) (reduce_once_red_wh3 R wh (KExpr.proj s i sub)) (@Eq.refl WhStepR (reduce_once_red_wh3 R wh (KExpr.proj s i sub))) h) (fun (v : Nat) (ihf : forall (y : KExpr), @Eq WhStepR (reduce_once_red_wh3 R wh (KExpr.lit v)) (WhStepR.wstep y) -> par_reduces_cd_star R (KExpr.lit v) y) (e2 : KExpr) (h : @Eq WhStepR (reduce_app_head_red_wh3 R wh a (KExpr.lit v) (reduce_once_red_wh3 R wh (KExpr.lit v))) (WhStepR.wstep e2)) => @WhStepR.rec (fun (o : WhStepR) => @Eq WhStepR (reduce_once_red_wh3 R wh (KExpr.lit v)) o -> @Eq WhStepR (opt_app_ilift3 R wh (KExpr.lit v) a o) (WhStepR.wstep e2) -> par_reduces_cd_star R (KExpr.app (KExpr.lit v) a) e2) (fun (_hq : @Eq WhStepR (reduce_once_red_wh3 R wh (KExpr.lit v)) WhStepR.wstuck) (h2 : @Eq WhStepR (iota_reduct_whc3 (red_rec R) wh (KExpr.app (KExpr.lit v) a)) (WhStepR.wstep e2)) => hiota3 wh hw (KExpr.lit v) a e2 h2) (fun (_hs : @Eq WhStepR (reduce_once_red_wh3 R wh (KExpr.lit v)) WhStepR.wstarved) (h2 : @Eq WhStepR WhStepR.wstarved (WhStepR.wstep e2)) => wh_starved_ne_step_type e2 (par_reduces_cd_star R (KExpr.app (KExpr.lit v) a) e2) h2) (fun (f2 : KExpr) (hq : @Eq WhStepR (reduce_once_red_wh3 R wh (KExpr.lit v)) (WhStepR.wstep f2)) (h2 : @Eq WhStepR (WhStepR.wstep (KExpr.app f2 a)) (WhStepR.wstep e2)) => Eq.substType KExpr (fun (X : KExpr) => par_reduces_cd_star R (KExpr.app (KExpr.lit v) a) X) (KExpr.app f2 a) e2 (wh_step_inj (KExpr.app f2 a) e2 h2) (par_reduces_cd_star_app R (KExpr.lit v) f2 a a (ihf f2 hq) (@par_reduces_cd_star.refl R a))) (reduce_once_red_wh3 R wh (KExpr.lit v)) (@Eq.refl WhStepR (reduce_once_red_wh3 R wh (KExpr.lit v))) h) f",
    ),
    (
        "reduce_once_red_wh3_par_hw_in",
        r"forall (R : RedEnv) (wh : KExpr -> OptionType KExpr) (hw : forall (e : KExpr) (rr : KExpr), @Eq (OptionType KExpr) (wh e) (@OptionType.some KExpr rr) -> par_reduces_cd_star R e rr) (hiota3 : forall (w : KExpr -> OptionType KExpr), (forall (e : KExpr) (rr : KExpr), @Eq (OptionType KExpr) (w e) (@OptionType.some KExpr rr) -> par_reduces_cd_star R e rr) -> forall (g : KExpr) (x : KExpr) (r : KExpr), @Eq WhStepR (iota_reduct_whc3 (red_rec R) w (KExpr.app g x)) (WhStepR.wstep r) -> par_reduces_cd_star R (KExpr.app g x) r) (e : KExpr),
 forall (e2 : KExpr), @Eq WhStepR (reduce_once_red_wh3 R wh e) (WhStepR.wstep e2) -> par_reduces_cd_star R e e2",
        r"fun (R : RedEnv) (wh : KExpr -> OptionType KExpr) (hw : forall (e : KExpr) (rr : KExpr), @Eq (OptionType KExpr) (wh e) (@OptionType.some KExpr rr) -> par_reduces_cd_star R e rr) (hiota3 : forall (w : KExpr -> OptionType KExpr), (forall (e : KExpr) (rr : KExpr), @Eq (OptionType KExpr) (w e) (@OptionType.some KExpr rr) -> par_reduces_cd_star R e rr) -> forall (g : KExpr) (x : KExpr) (r : KExpr), @Eq WhStepR (iota_reduct_whc3 (red_rec R) w (KExpr.app g x)) (WhStepR.wstep r) -> par_reduces_cd_star R (KExpr.app g x) r) (e : KExpr) =>
 @KExpr.rec (fun (x : KExpr) => forall (e2 : KExpr), @Eq WhStepR (reduce_once_red_wh3 R wh x) (WhStepR.wstep e2) -> par_reduces_cd_star R x e2) (fun (n : Level) (e2 : KExpr) (h : @Eq WhStepR (reduce_once_red_wh3 R wh (KExpr.sort n)) (WhStepR.wstep e2)) => wh_stuck_ne_step_type e2 (par_reduces_cd_star R (KExpr.sort n) e2) h) (fun (i : Nat) (e2 : KExpr) (h : @Eq WhStepR (reduce_once_red_wh3 R wh (KExpr.bvar i)) (WhStepR.wstep e2)) => wh_stuck_ne_step_type e2 (par_reduces_cd_star R (KExpr.bvar i) e2) h) (fun (f : KExpr) (a2 : KExpr) (_c0 : forall (e2 : KExpr), @Eq WhStepR (reduce_once_red_wh3 R wh f) (WhStepR.wstep e2) -> par_reduces_cd_star R f e2) (_c1 : forall (e2 : KExpr), @Eq WhStepR (reduce_once_red_wh3 R wh a2) (WhStepR.wstep e2) -> par_reduces_cd_star R a2 e2) (e2 : KExpr) (h : @Eq WhStepR (reduce_once_red_wh3 R wh (KExpr.app f a2)) (WhStepR.wstep e2)) => reduce_app_head_wh3_par_hw_in R wh hw hiota3 a2 f _c0 e2 h) (fun (ty : KExpr) (b : KExpr) (_c0 : forall (e2 : KExpr), @Eq WhStepR (reduce_once_red_wh3 R wh ty) (WhStepR.wstep e2) -> par_reduces_cd_star R ty e2) (_c1 : forall (e2 : KExpr), @Eq WhStepR (reduce_once_red_wh3 R wh b) (WhStepR.wstep e2) -> par_reduces_cd_star R b e2) (e2 : KExpr) (h : @Eq WhStepR (reduce_once_red_wh3 R wh (KExpr.lam ty b)) (WhStepR.wstep e2)) => wh_stuck_ne_step_type e2 (par_reduces_cd_star R (KExpr.lam ty b) e2) h) (fun (ty : KExpr) (b : KExpr) (_c0 : forall (e2 : KExpr), @Eq WhStepR (reduce_once_red_wh3 R wh ty) (WhStepR.wstep e2) -> par_reduces_cd_star R ty e2) (_c1 : forall (e2 : KExpr), @Eq WhStepR (reduce_once_red_wh3 R wh b) (WhStepR.wstep e2) -> par_reduces_cd_star R b e2) (e2 : KExpr) (h : @Eq WhStepR (reduce_once_red_wh3 R wh (KExpr.pi ty b)) (WhStepR.wstep e2)) => wh_stuck_ne_step_type e2 (par_reduces_cd_star R (KExpr.pi ty b) e2) h) (fun (n : Name) (us : ListType Level) (e2 : KExpr) (h : @Eq WhStepR (reduce_once_red_wh3 R wh (KExpr.const n us)) (WhStepR.wstep e2)) => @OptionType.rec KExpr (fun (o : OptionType KExpr) => @Eq (OptionType KExpr) (kdef_value_at (red_def R) n us) o -> @Eq WhStepR (opt_step_bind KExpr o WhStepR.wstuck (fun (v : KExpr) => WhStepR.wstep v)) (WhStepR.wstep e2) -> par_reduces_cd_star R (KExpr.const n us) e2) (fun (_hq : @Eq (OptionType KExpr) (kdef_value_at (red_def R) n us) (@OptionType.none KExpr)) (h2 : @Eq WhStepR WhStepR.wstuck (WhStepR.wstep e2)) => wh_stuck_ne_step_type e2 (par_reduces_cd_star R (KExpr.const n us) e2) h2) (fun (dv : KExpr) (hq : @Eq (OptionType KExpr) (kdef_value_at (red_def R) n us) (@OptionType.some KExpr dv)) (h2 : @Eq WhStepR (WhStepR.wstep dv) (WhStepR.wstep e2)) => Eq.substType KExpr (fun (X : KExpr) => par_reduces_cd_star R (KExpr.const n us) X) dv e2 (wh_step_inj dv e2 h2) (@par_reduces_cd_star.step R (KExpr.const n us) dv dv (@par_reduces_cd.delta R (KExpr.const n us) dv (const_delta_step_in R n us dv hq)) (@par_reduces_cd_star.refl R dv))) (kdef_value_at (red_def R) n us) (@Eq.refl (OptionType KExpr) (kdef_value_at (red_def R) n us)) h) (fun (ty : KExpr) (v : KExpr) (b : KExpr) (_c0 : forall (e2 : KExpr), @Eq WhStepR (reduce_once_red_wh3 R wh ty) (WhStepR.wstep e2) -> par_reduces_cd_star R ty e2) (_c1 : forall (e2 : KExpr), @Eq WhStepR (reduce_once_red_wh3 R wh v) (WhStepR.wstep e2) -> par_reduces_cd_star R v e2) (_c2 : forall (e2 : KExpr), @Eq WhStepR (reduce_once_red_wh3 R wh b) (WhStepR.wstep e2) -> par_reduces_cd_star R b e2) (e2 : KExpr) (h : @Eq WhStepR (reduce_once_red_wh3 R wh (KExpr.let_ ty v b)) (WhStepR.wstep e2)) => Eq.substType KExpr (fun (X : KExpr) => par_reduces_cd_star R (KExpr.let_ ty v b) X) (instantiate b v) e2 (wh_step_inj (instantiate b v) e2 h) (@par_reduces_cd_star.step R (KExpr.let_ ty v b) (instantiate b v) (instantiate b v) (@par_reduces_cd.let_ R ty ty v v b b (@par_reduces_cd.refl R ty) (@par_reduces_cd.refl R v) (@par_reduces_cd.refl R b)) (@par_reduces_cd_star.refl R (instantiate b v)))) (fun (s : Name) (i : Nat) (sub : KExpr) (_c0 : forall (e2 : KExpr), @Eq WhStepR (reduce_once_red_wh3 R wh sub) (WhStepR.wstep e2) -> par_reduces_cd_star R sub e2) (e2 : KExpr) (h : @Eq WhStepR (reduce_once_red_wh3 R wh (KExpr.proj s i sub)) (WhStepR.wstep e2)) => @WhStepR.rec (fun (o : WhStepR) => @Eq WhStepR (reduce_once_red_wh3 R wh sub) o -> @Eq WhStepR (@WhStepR.rec (fun (_o : WhStepR) => WhStepR) WhStepR.wstuck WhStepR.wstarved (fun (sub2 : KExpr) => WhStepR.wstep (KExpr.proj s i sub2)) o) (WhStepR.wstep e2) -> par_reduces_cd_star R (KExpr.proj s i sub) e2) (fun (_hq : @Eq WhStepR (reduce_once_red_wh3 R wh sub) WhStepR.wstuck) (h2 : @Eq WhStepR WhStepR.wstuck (WhStepR.wstep e2)) => wh_stuck_ne_step_type e2 (par_reduces_cd_star R (KExpr.proj s i sub) e2) h2) (fun (_hs : @Eq WhStepR (reduce_once_red_wh3 R wh sub) WhStepR.wstarved) (h2 : @Eq WhStepR WhStepR.wstarved (WhStepR.wstep e2)) => wh_starved_ne_step_type e2 (par_reduces_cd_star R (KExpr.proj s i sub) e2) h2) (fun (sub2 : KExpr) (hq : @Eq WhStepR (reduce_once_red_wh3 R wh sub) (WhStepR.wstep sub2)) (h2 : @Eq WhStepR (WhStepR.wstep (KExpr.proj s i sub2)) (WhStepR.wstep e2)) => Eq.substType KExpr (fun (X : KExpr) => par_reduces_cd_star R (KExpr.proj s i sub) X) (KExpr.proj s i sub2) e2 (wh_step_inj (KExpr.proj s i sub2) e2 h2) (par_reduces_cd_star_proj R s i sub sub2 (_c0 sub2 hq))) (reduce_once_red_wh3 R wh sub) (@Eq.refl WhStepR (reduce_once_red_wh3 R wh sub)) h) (fun (v : Nat) (e2 : KExpr) (h : @Eq WhStepR (reduce_once_red_wh3 R wh (KExpr.lit v)) (WhStepR.wstep e2)) => wh_stuck_ne_step_type e2 (par_reduces_cd_star R (KExpr.lit v) e2) h) e",
    ),
    (
        "whnf_fuel_red_wh3_par_hw_in",
        r"forall (R : RedEnv) (hiota3 : forall (w : KExpr -> OptionType KExpr), (forall (e : KExpr) (rr : KExpr), @Eq (OptionType KExpr) (w e) (@OptionType.some KExpr rr) -> par_reduces_cd_star R e rr) -> forall (g : KExpr) (x : KExpr) (r : KExpr), @Eq WhStepR (iota_reduct_whc3 (red_rec R) w (KExpr.app g x)) (WhStepR.wstep r) -> par_reduces_cd_star R (KExpr.app g x) r) (fuel : Nat),
 forall (e : KExpr) (r : KExpr), @Eq (OptionType KExpr) (whnf_fuel_red_wh3 R fuel e) (@OptionType.some KExpr r) -> par_reduces_cd_star R e r",
        r"fun (R : RedEnv) (hiota3 : forall (w : KExpr -> OptionType KExpr), (forall (e : KExpr) (rr : KExpr), @Eq (OptionType KExpr) (w e) (@OptionType.some KExpr rr) -> par_reduces_cd_star R e rr) -> forall (g : KExpr) (x : KExpr) (r : KExpr), @Eq WhStepR (iota_reduct_whc3 (red_rec R) w (KExpr.app g x)) (WhStepR.wstep r) -> par_reduces_cd_star R (KExpr.app g x) r) (fuel : Nat) =>
 @Nat.rec (fun (n : Nat) => forall (e : KExpr) (r : KExpr), @Eq (OptionType KExpr) (whnf_fuel_red_wh3 R n e) (@OptionType.some KExpr r) -> par_reduces_cd_star R e r) (fun (e : KExpr) (r : KExpr) (h : @Eq (OptionType KExpr) (whnf_fuel_red_wh3 R Nat.zero e) (@OptionType.some KExpr r)) => option_none_ne_some_type KExpr r (par_reduces_cd_star R e r) h) (fun (k : Nat) (ih : forall (e0 : KExpr) (r0 : KExpr), @Eq (OptionType KExpr) (whnf_fuel_red_wh3 R k e0) (@OptionType.some KExpr r0) -> par_reduces_cd_star R e0 r0) (e : KExpr) (r : KExpr) (h : @Eq (OptionType KExpr) (whnf_fuel_red_wh3 R (Nat.succ k) e) (@OptionType.some KExpr r)) => @WhStepR.rec (fun (o : WhStepR) => @Eq WhStepR (reduce_once_red_wh3 R (fun (e3 : KExpr) => whnf_fuel_red_wh3 R k e3) e) o -> @Eq (OptionType KExpr) (wh_dispatch3 o e (fun (e3 : KExpr) => whnf_fuel_red_wh3 R k e3)) (@OptionType.some KExpr r) -> par_reduces_cd_star R e r) (fun (_hq : @Eq WhStepR (reduce_once_red_wh3 R (fun (e3 : KExpr) => whnf_fuel_red_wh3 R k e3) e) WhStepR.wstuck) (h2 : @Eq (OptionType KExpr) (wh_dispatch3 WhStepR.wstuck e (fun (e3 : KExpr) => whnf_fuel_red_wh3 R k e3)) (@OptionType.some KExpr r)) => Eq.substType KExpr (fun (X : KExpr) => par_reduces_cd_star R e X) e r (option_some_inj KExpr e r h2) (@par_reduces_cd_star.refl R e)) (fun (_hs : @Eq WhStepR (reduce_once_red_wh3 R (fun (e3 : KExpr) => whnf_fuel_red_wh3 R k e3) e) WhStepR.wstarved) (h2 : @Eq (OptionType KExpr) (wh_dispatch3 WhStepR.wstarved e (fun (e3 : KExpr) => whnf_fuel_red_wh3 R k e3)) (@OptionType.some KExpr r)) => option_none_ne_some_type KExpr r (par_reduces_cd_star R e r) h2) (fun (e2 : KExpr) (hq : @Eq WhStepR (reduce_once_red_wh3 R (fun (e3 : KExpr) => whnf_fuel_red_wh3 R k e3) e) (WhStepR.wstep e2)) (h2 : @Eq (OptionType KExpr) (wh_dispatch3 (WhStepR.wstep e2) e (fun (e3 : KExpr) => whnf_fuel_red_wh3 R k e3)) (@OptionType.some KExpr r)) => par_reduces_cd_star_trans R e e2 r (reduce_once_red_wh3_par_hw_in R (fun (e3 : KExpr) => whnf_fuel_red_wh3 R k e3) ih hiota3 e e2 hq) (ih e2 r h2)) (reduce_once_red_wh3 R (fun (e3 : KExpr) => whnf_fuel_red_wh3 R k e3) e) (@Eq.refl WhStepR (reduce_once_red_wh3 R (fun (e3 : KExpr) => whnf_fuel_red_wh3 R k e3) e)) h) fuel",
    ),
    (
        "whnf_fuel_red_wh3_par_in",
        r"forall (R : RedEnv) (fuel : Nat) (e : KExpr) (r : KExpr)
 (accepted : @Eq (OptionType KExpr) (whnf_fuel_red_wh3 R fuel e) (@OptionType.some KExpr r)),
 par_reduces_cd_star R e r",
        r"fun (R : RedEnv) (fuel : Nat) (e : KExpr) (r : KExpr)
 (accepted : @Eq (OptionType KExpr) (whnf_fuel_red_wh3 R fuel e) (@OptionType.some KExpr r)) =>
 whnf_fuel_red_wh3_par_hw_in R (hiotap3_discharged_in R) fuel e r accepted",
    ),
    (
        "whnf_fuel_red_wh3_sound_in",
        r"forall (R : RedEnv) (fuel : Nat) (e : KExpr) (r : KExpr)
 (accepted : @Eq (OptionType KExpr) (whnf_fuel_red_wh3 R fuel e) (@OptionType.some KExpr r)),
 DefEqIn R e r",
        r"fun (R : RedEnv) (fuel : Nat) (e : KExpr) (r : KExpr)
 (accepted : @Eq (OptionType KExpr) (whnf_fuel_red_wh3 R fuel e) (@OptionType.some KExpr r)) =>
 par_reduces_cd_star_to_def_eq_in R e r (whnf_fuel_red_wh3_par_in R fuel e r accepted)",
    ),
    (
        "wh3_sem_fixture_levels",
        r"ListType Level",
        r"@ListType.cons Level (Level.succ (Level.param Name.anonymous)) (@ListType.nil Level)",
    ),
    (
        "wh3_sem_fixture_env",
        r"RedEnv",
        r"RedEnv.mk
  (RecEnv.addRec RecEnv.empty Name.anonymous
    (RecMeta.mk Nat.zero Nat.zero Nat.zero Nat.zero Bool.true
      (KConstSig.mk (@ListType.cons Name Name.anonymous (@ListType.nil Name)) (KExpr.sort Level.zero)) Nat.zero)
    (RecRules.cons
      (RecRule.mk (Name.str Name.anonymous Nat.zero) Nat.zero
        (KExpr.sort (Level.param Name.anonymous))) RecRules.nil))
  (DefEnv.addDef DefEnv.empty (Name.str Name.anonymous (Nat.succ Nat.zero))
    (KDefSig.mk
      (KConstSig.mk (@ListType.cons Name Name.anonymous (@ListType.nil Name)) (KExpr.sort Level.zero))
      (KExpr.sort (Level.param Name.anonymous))))
  IndCtorEnv.empty",
    ),
    (
        "wh3_sem_fixture_major",
        r"KExpr",
        r"KExpr.app (KExpr.lam (KExpr.sort Level.zero) (KExpr.bvar Nat.zero))
  (KExpr.const (Name.str Name.anonymous Nat.zero) (@ListType.nil Level))",
    ),
    (
        "wh3_sem_fixture_iota",
        r"forall (us : ListType Level),
 KExpr",
        r"fun (us : ListType Level) =>
 KExpr.app (KExpr.const Name.anonymous us) wh3_sem_fixture_major",
    ),
    (
        "wh3_sem_beta_computes",
        r"forall (R : RedEnv),
 @Eq (OptionType KExpr)
  (whnf_fuel_red_wh3 R (Nat.succ (Nat.succ Nat.zero))
    (KExpr.app (KExpr.lam (KExpr.sort Level.zero) (KExpr.bvar Nat.zero)) (KExpr.sort Level.zero)))
  (@OptionType.some KExpr (KExpr.sort Level.zero))",
        r"fun (R : RedEnv) =>
 @Eq.refl (OptionType KExpr) (@OptionType.some KExpr (KExpr.sort Level.zero))",
    ),
    (
        "wh3_sem_beta_caller",
        r"forall (R : RedEnv),
 DefEqIn R
  (KExpr.app (KExpr.lam (KExpr.sort Level.zero) (KExpr.bvar Nat.zero)) (KExpr.sort Level.zero))
  (KExpr.sort Level.zero)",
        r"fun (R : RedEnv) =>
 whnf_fuel_red_wh3_sound_in R (Nat.succ (Nat.succ Nat.zero))
  (KExpr.app (KExpr.lam (KExpr.sort Level.zero) (KExpr.bvar Nat.zero)) (KExpr.sort Level.zero))
  (KExpr.sort Level.zero) (wh3_sem_beta_computes R)",
    ),
    (
        "wh3_sem_let_projection_computes",
        r"forall (R : RedEnv),
 @Eq (OptionType KExpr)
  (whnf_fuel_red_wh3 R (Nat.succ (Nat.succ Nat.zero))
    (KExpr.proj Name.anonymous Nat.zero
      (KExpr.let_ (KExpr.sort Level.zero) (KExpr.sort Level.zero) (KExpr.bvar Nat.zero))))
  (@OptionType.some KExpr (KExpr.proj Name.anonymous Nat.zero (KExpr.sort Level.zero)))",
        r"fun (R : RedEnv) =>
 @Eq.refl (OptionType KExpr) (@OptionType.some KExpr (KExpr.proj Name.anonymous Nat.zero (KExpr.sort Level.zero)))",
    ),
    (
        "wh3_sem_let_projection_caller",
        r"forall (R : RedEnv),
 DefEqIn R
  (KExpr.proj Name.anonymous Nat.zero
    (KExpr.let_ (KExpr.sort Level.zero) (KExpr.sort Level.zero) (KExpr.bvar Nat.zero)))
  (KExpr.proj Name.anonymous Nat.zero (KExpr.sort Level.zero))",
        r"fun (R : RedEnv) =>
 whnf_fuel_red_wh3_sound_in R (Nat.succ (Nat.succ Nat.zero))
  (KExpr.proj Name.anonymous Nat.zero
    (KExpr.let_ (KExpr.sort Level.zero) (KExpr.sort Level.zero) (KExpr.bvar Nat.zero)))
  (KExpr.proj Name.anonymous Nat.zero (KExpr.sort Level.zero)) (wh3_sem_let_projection_computes R)",
    ),
    (
        "wh3_sem_delta_computes",
        r"@Eq (OptionType KExpr)
  (whnf_fuel_red_wh3 wh3_sem_fixture_env (Nat.succ (Nat.succ Nat.zero))
    (KExpr.const (Name.str Name.anonymous (Nat.succ Nat.zero)) wh3_sem_fixture_levels))
  (@OptionType.some KExpr (KExpr.sort (Level.succ (Level.param Name.anonymous))))",
        r"@Eq.refl (OptionType KExpr) (@OptionType.some KExpr (KExpr.sort (Level.succ (Level.param Name.anonymous))))",
    ),
    (
        "wh3_sem_delta_caller",
        r"DefEqIn wh3_sem_fixture_env
  (KExpr.const (Name.str Name.anonymous (Nat.succ Nat.zero)) wh3_sem_fixture_levels)
  (KExpr.sort (Level.succ (Level.param Name.anonymous)))",
        r"whnf_fuel_red_wh3_sound_in wh3_sem_fixture_env (Nat.succ (Nat.succ Nat.zero))
  (KExpr.const (Name.str Name.anonymous (Nat.succ Nat.zero)) wh3_sem_fixture_levels)
  (KExpr.sort (Level.succ (Level.param Name.anonymous))) wh3_sem_delta_computes",
    ),
    (
        "wh3_sem_iota_computes",
        r"@Eq (OptionType KExpr)
  (whnf_fuel_red_wh3 wh3_sem_fixture_env (Nat.succ (Nat.succ (Nat.succ Nat.zero)))
    (wh3_sem_fixture_iota wh3_sem_fixture_levels))
  (@OptionType.some KExpr (KExpr.sort (Level.succ (Level.param Name.anonymous))))",
        r"@Eq.refl (OptionType KExpr) (@OptionType.some KExpr (KExpr.sort (Level.succ (Level.param Name.anonymous))))",
    ),
    (
        "wh3_sem_iota_caller",
        r"DefEqIn wh3_sem_fixture_env (wh3_sem_fixture_iota wh3_sem_fixture_levels)
  (KExpr.sort (Level.succ (Level.param Name.anonymous)))",
        r"whnf_fuel_red_wh3_sound_in wh3_sem_fixture_env (Nat.succ (Nat.succ (Nat.succ Nat.zero)))
  (wh3_sem_fixture_iota wh3_sem_fixture_levels)
  (KExpr.sort (Level.succ (Level.param Name.anonymous))) wh3_sem_iota_computes",
    ),
    (
        "wh3_sem_major_starved",
        r"@Eq (OptionType KExpr)
  (whnf_fuel_red_wh3 wh3_sem_fixture_env (Nat.succ (Nat.succ Nat.zero))
    (wh3_sem_fixture_iota wh3_sem_fixture_levels)) (@OptionType.none KExpr)",
        r"@Eq.refl (OptionType KExpr) (@OptionType.none KExpr)",
    ),
    (
        "wh3_sem_wrong_arity_stuck",
        r"@Eq (OptionType KExpr)
  (whnf_fuel_red_wh3 wh3_sem_fixture_env (Nat.succ (Nat.succ (Nat.succ Nat.zero)))
    (wh3_sem_fixture_iota (@ListType.nil Level)))
  (@OptionType.some KExpr (wh3_sem_fixture_iota (@ListType.nil Level)))",
        r"@Eq.refl (OptionType KExpr) (@OptionType.some KExpr (wh3_sem_fixture_iota (@ListType.nil Level)))",
    ),
];

#[cfg(test)]
const PROOF_ROOTS: &[&str] = &[
    "const_delta_step_in",
    "whc3_iota_sound_at_in",
    "hiotap3_discharged_in",
    "reduce_app_head_wh3_par_hw_in",
    "reduce_once_red_wh3_par_hw_in",
    "whnf_fuel_red_wh3_par_hw_in",
    "whnf_fuel_red_wh3_par_in",
    "whnf_fuel_red_wh3_sound_in",
    "wh3_sem_beta_computes",
    "wh3_sem_beta_caller",
    "wh3_sem_let_projection_computes",
    "wh3_sem_let_projection_caller",
    "wh3_sem_delta_computes",
    "wh3_sem_delta_caller",
    "wh3_sem_iota_computes",
    "wh3_sem_iota_caller",
    "wh3_sem_major_starved",
    "wh3_sem_wrong_arity_stuck",
];

impl Specification {
    pub(super) fn add_semantic_wh3_soundness_in(&mut self) -> Result<(), SpecError> {
        for &(name, type_src, value_src) in DECLARATIONS {
            if matches!(
                name,
                "wh3_sem_fixture_levels"
                    | "wh3_sem_fixture_env"
                    | "wh3_sem_fixture_major"
                    | "wh3_sem_fixture_iota"
            ) {
                // Actual evaluator inputs are transparent computational data;
                // the checked theorem helper deliberately registers Type-valued
                // proof terms opaquely and is not a data registration API.
                self.add_recursive_def(
                    &format!("def {name} : {type_src} := {value_src}"),
                    "Transparent finite WH3 fixture data; no typing or admission claim.",
                )?;
                continue;
            }
            super::acceptance_in::theorem(
                self,
                name,
                type_src,
                value_src,
                "Actual arbitrary-environment guarded WH3 computation yields raw parallel-star reduction and semantic conversion; the smaller-fuel IH discharges the major pre-pass. Fixture environment data is not an admission or typing claim.",
            )?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::spec::types::{AxiomCategory, ProofStatus};
    use crate::test_utils::{build_spec_with_stack, run_with_stack};
    use clean_kernel::{ConstantKind, ExprKind, Name};

    const REFUSALS: &[&str] = &[
        r"def wh3_sem_forged_output :
 DefEqIn wh3_sem_fixture_env (wh3_sem_fixture_iota wh3_sem_fixture_levels) (KExpr.sort Level.zero) :=
 whnf_fuel_red_wh3_sound_in wh3_sem_fixture_env (Nat.succ (Nat.succ (Nat.succ Nat.zero)))
  (wh3_sem_fixture_iota wh3_sem_fixture_levels) (KExpr.sort Level.zero) wh3_sem_iota_computes",
        r"def wh3_sem_forged_exhausted :
 DefEqIn wh3_sem_fixture_env (wh3_sem_fixture_iota wh3_sem_fixture_levels)
  (KExpr.sort (Level.succ (Level.param Name.anonymous))) :=
 whnf_fuel_red_wh3_sound_in wh3_sem_fixture_env (Nat.succ (Nat.succ Nat.zero))
  (wh3_sem_fixture_iota wh3_sem_fixture_levels)
  (KExpr.sort (Level.succ (Level.param Name.anonymous))) wh3_sem_iota_computes",
        r"def wh3_sem_forged_missing_universe :
 DefEqIn wh3_sem_fixture_env (wh3_sem_fixture_iota (@ListType.nil Level))
  (KExpr.sort (Level.succ (Level.param Name.anonymous))) :=
 whnf_fuel_red_wh3_sound_in wh3_sem_fixture_env (Nat.succ (Nat.succ (Nat.succ Nat.zero)))
  (wh3_sem_fixture_iota (@ListType.nil Level))
  (KExpr.sort (Level.succ (Level.param Name.anonymous))) wh3_sem_iota_computes",
    ];

    #[test]
    fn semantic_wh3_soundness_in_records_and_controls_parse() {
        assert_eq!(DECLARATIONS.len(), 22);
        assert_eq!(PROOF_ROOTS.len(), 18);
        assert_eq!(REFUSALS.len(), 3);
        let names: std::collections::HashSet<_> =
            DECLARATIONS.iter().map(|entry| entry.0).collect();
        assert_eq!(names.len(), DECLARATIONS.len());
        for root in PROOF_ROOTS {
            assert!(names.contains(root), "{root}");
            assert!(
                !root.starts_with("wh3_sem_fixture_"),
                "data is not a proof root"
            );
        }
        for &(name, type_src, value_src) in DECLARATIONS {
            clean_parser::parse_decl(&format!("def {name} : {type_src} := {value_src}"))
                .expect("explicit WH3 proof record parses");
            assert!(!type_src.contains("the_red_env"), "{name}");
            assert!(!value_src.contains("the_red_env"), "{name}");
            assert!(!type_src.contains("RedEnvFaithful"), "{name}");
            assert!(!value_src.contains("RedEnvFaithful"), "{name}");
        }
        for source in REFUSALS {
            clean_parser::parse_decl(source).expect("negative WH3 control parses");
        }
    }

    #[test]
    fn semantic_wh3_soundness_in_registered_values_recheck_without_axioms() {
        run_with_stack(|| {
            let spec = build_spec_with_stack();
            for &(name, type_src, value_src) in DECLARATIONS {
                let definition = spec
                    .definitions()
                    .get(name)
                    .expect("registered declaration");
                let kernel_name = Name::from_string(name);
                let constant = spec
                    .env()
                    .get_const(&kernel_name)
                    .expect("actual kernel root");
                let ty = definition.elaborated_type.as_ref().expect("checked type");
                let value = definition.elaborated_value.as_ref().expect("checked value");
                assert!(!definition.is_axiom, "{name}");
                assert_ne!(constant.kind, ConstantKind::Axiom, "{name}");
                assert_eq!(definition.category, AxiomCategory::DerivedLemma, "{name}");
                if name.starts_with("wh3_sem_fixture_") {
                    assert_eq!(constant.kind, ConstantKind::Definition, "{name}");
                    let source = format!("def {name} : {type_src} := {value_src}");
                    assert_eq!(definition.type_src, source, "{name}");
                    assert_eq!(
                        definition.value_src.as_deref(),
                        Some(source.as_str()),
                        "{name}"
                    );
                } else {
                    assert_eq!(
                        definition.proof_status,
                        ProofStatus::DerivedProved,
                        "{name}"
                    );
                    assert_eq!(definition.type_src, type_src, "{name}");
                    assert_eq!(definition.value_src.as_deref(), Some(value_src), "{name}");
                }
                assert_eq!(&constant.type_, ty, "{name}");
                assert_eq!(constant.value.as_ref(), Some(value), "{name}");
                assert!(
                    !matches!(value.kind(), ExprKind::Const(n, _) if n == &kernel_name),
                    "{name}"
                );
                spec.verify_definition(name)
                    .expect("actual registered value rechecks");
                assert!(
                    spec.env()
                        .axiom_deps(&kernel_name)
                        .expect("domain closure")
                        .is_empty(),
                    "{name}"
                );
                assert!(
                    spec.env()
                        .foundational_axiom_deps(&kernel_name)
                        .expect("foundational closure")
                        .is_empty(),
                    "{name}"
                );
                assert!(
                    crate::spec_axiom_closure::computed_axiom_closure(&spec, name).is_empty(),
                    "{name}"
                );
            }
        });
    }

    #[test]
    fn semantic_wh3_soundness_in_rejects_three_forged_callers() {
        run_with_stack(|| {
            let mut spec = build_spec_with_stack();
            for source in REFUSALS {
                let clean_parser::SurfaceDecl::Def { name, .. } =
                    clean_parser::parse_decl(source).expect("negative control parses")
                else {
                    panic!("expected a definition");
                };
                let kernel_name = name.qualify_under(&Default::default()).into_name();
                // Legacy record-key projection only; exact kernel identity is checked separately.
                assert!(
                    !spec.definitions().contains_key(
                        &name
                            .qualify_under(&Default::default())
                            .into_name()
                            .to_string()
                    ),
                    "{name}"
                );
                assert!(spec.env().get_const(&kernel_name).is_none(), "{name}");
                let error = spec
                    .add_recursive_def(source, "Reject forged WH3 result/fuel/universe evidence.")
                    .expect_err("the intended forged caller must not register");
                assert!(format!("{error:?}").contains("Type mismatch"), "{error:?}");
                assert!(
                    !spec.definitions().contains_key(
                        &name
                            .qualify_under(&Default::default())
                            .into_name()
                            .to_string()
                    ),
                    "{name}"
                );
                assert!(spec.env().get_const(&kernel_name).is_none(), "{name}");
            }
        });
    }
}
