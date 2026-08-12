// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The stuck-major classification's **fourth alternative** — the one that used
//! to be circular.
//!
//! `stuck_major_confluence.rs` classifies a stuck major by its spine head and
//! closes three of four cases (rigid, lam, δ-dead *recmeta-free* const). The
//! fourth — a const head **carrying** recmeta — it recorded as **"Circular, not
//! merely incomplete"**, because there `wmajor` is itself a stuck recursor
//! spine and the fact needed is the residual again, one level down.
//!
//! ## How the circle is broken
//!
//! Not by assuming the conclusion. `nf_head wmajor` is taken as an explicit
//! **premise**, and the consumer discharges it from the induction hypothesis at
//! a **strictly smaller budget**:
//!
//! * `whnf_fuel_red_wh3_result_stuck_lt` produces the smaller budget `j < k`
//!   (and its strictness is exactly what makes this well-founded);
//! * `hnf3` at that budget produces `nf_head`.
//!
//! So "one level down" stops being circular and becomes one step of a
//! well-founded recursion. That is the whole point of inducting on the budget
//! rather than on the term.
//!
//! ## The argument, once `nf_head wmajor` is in hand
//!
//! 1. Confluence (`stuck_major_join_ctor_head_at_the_red_env`) yields a common
//!    reduct `v` with `wmajor =>* v`, headed by the constructor `cname`.
//! 2. `nf_head_star_preserves_const_name` forces `CN wmajor = CN v`, so the
//!    recmeta-carrying head `cn2` **is** `cname`.
//! 3. `RecEnvCtorNoRecMeta` says a constructor carries no recmeta —
//!    contradicting the hypothesis that `cn2` does.
//!
//! Registered after `add_nf_head_const_name`, which step 2 needs.
//!
//! `DerivedProved`, empty axiom closure.

use crate::spec::error::SpecError;
use crate::spec::Specification;

const SRC_STUCK_MAJOR_RECMETA: &str = "def stuck_major_recmeta_no_ctor_reduct (nm : Name) (cname : Name) (cn2 : Name) (rule : RecRule) (meta : RecMeta) (major : KExpr) (wmajor : KExpr) (m2 : KExpr) (hnf : nf_head wmajor) (hwh : Eq (OptionType Name) (kexpr_const_name (kapp_fn wmajor)) (OptionType.some Name cn2)) (hrecmeta : Eq (OptionType RecMeta) (recmeta_for (red_rec the_red_env) cn2) (OptionType.some RecMeta meta)) (hA : par_reduces_cd_star the_red_env major wmajor) (hB : par_reduces_cd_star the_red_env major m2) (hm2 : Eq (OptionType Name) (kexpr_const_name (kapp_fn m2)) (OptionType.some Name cname)) (hrule : Eq (OptionType RecRule) (recrule_for (red_rec the_red_env) nm cname) (OptionType.some RecRule rule)) : Empty := stuck_major_join_ctor_head_at_the_red_env Empty nm cname rule major wmajor m2 hA hB hm2 hrule (fun (v : KExpr) (hwv : par_reduces_cd_star the_red_env wmajor v) (hcv : Eq (OptionType Name) (kexpr_const_name (kapp_fn v)) (OptionType.some Name cname)) => option_none_ne_some_type RecMeta meta Empty (Eq.trans (OptionType RecMeta) (OptionType.none RecMeta) (recmeta_for (red_rec the_red_env) cname) (OptionType.some RecMeta meta) (Eq.symm (OptionType RecMeta) (recmeta_for (red_rec the_red_env) cname) (OptionType.none RecMeta) (recenv_ctor_no_recmeta_cname (red_rec the_red_env) nm cname rule m2 the_red_env_ctor_no_recmeta_via_checker hm2 hrule)) (Eq.substType Name (fun (z : Name) => Eq (OptionType RecMeta) (recmeta_for (red_rec the_red_env) z) (OptionType.some RecMeta meta)) cn2 cname (option_some_inj Name cn2 cname (Eq.trans (OptionType Name) (OptionType.some Name cn2) (kexpr_const_name (kapp_fn v)) (OptionType.some Name cname) (Eq.trans (OptionType Name) (OptionType.some Name cn2) (kexpr_const_name (kapp_fn wmajor)) (kexpr_const_name (kapp_fn v)) (Eq.symm (OptionType Name) (kexpr_const_name (kapp_fn wmajor)) (OptionType.some Name cn2) hwh) (nf_head_star_preserves_const_name wmajor hnf v hwv)) hcv)) hrecmeta)))";

const SRC_STUCK_MAJOR_IOTA_ARM: &str = "def stuck_major_iota_arm_absurd (nm : Name) (meta : RecMeta) (maj : KExpr) (mjr : KExpr) (p : KExpr) (q : KExpr) (hno : forall (cname : Name) (rule : RecRule) (m2 : KExpr), par_reduces_cd_star the_red_env maj m2 -> Eq (OptionType Name) (kexpr_const_name (kapp_fn m2)) (OptionType.some Name cname) -> Eq (OptionType RecRule) (recrule_for (red_rec the_red_env) nm cname) (OptionType.some RecRule rule) -> Empty) (hhead : Eq (OptionType Name) (kexpr_const_name (kapp_fn p)) (OptionType.some Name nm)) (hmeta : Eq (OptionType RecMeta) (recmeta_for (red_rec the_red_env) nm) (OptionType.some RecMeta meta)) (hmaj : Eq (OptionType KExpr) (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args p))) (OptionType.some KExpr mjr)) (hr : par_reduces_cd_star the_red_env maj mjr) (hi : iota_step (red_rec the_red_env) p q) : Empty := iota_reduct_some_inv_type (red_rec the_red_env) p q Empty hi (fun (recname2 : Name) (meta2 : RecMeta) (major : KExpr) (cname2 : Name) (rule2 : RecRule) (h1 : Eq (OptionType Name) (kexpr_const_name (kapp_fn p)) (OptionType.some Name recname2)) (h2 : Eq (OptionType RecMeta) (recmeta_for (red_rec the_red_env) recname2) (OptionType.some RecMeta meta2)) (h3 : Eq (OptionType KExpr) (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta2) (recmeta_num_motives meta2)) (recmeta_num_minors meta2)) (recmeta_num_indices meta2)) (kapp_args p))) (OptionType.some KExpr major)) (h4 : Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cname2)) (h5 : Eq (OptionType RecRule) (recrule_for (red_rec the_red_env) recname2 cname2) (OptionType.some RecRule rule2)) (_h5r : Eq (OptionType KExpr) (OptionType.some KExpr (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta2) (recmeta_num_motives meta2)) (recmeta_num_minors meta2)) (recmeta_num_indices meta2))) (kapp_args p)) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule2)) (kapp_args major)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta2) (recmeta_num_motives meta2)) (recmeta_num_minors meta2)) (kapp_args p)) (recrule_rhs rule2))))) (OptionType.some KExpr q)) => hno cname2 rule2 mjr hr (Eq.substType KExpr (fun (X : KExpr) => Eq (OptionType Name) (kexpr_const_name (kapp_fn X)) (OptionType.some Name cname2)) major mjr (option_some_inj KExpr major mjr (Eq.trans (OptionType KExpr) (OptionType.some KExpr major) (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args p))) (OptionType.some KExpr mjr) (Eq.symm (OptionType KExpr) (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args p))) (OptionType.some KExpr major) (Eq.substType RecMeta (fun (M2 : RecMeta) => Eq (OptionType KExpr) (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params M2) (recmeta_num_motives M2)) (recmeta_num_minors M2)) (recmeta_num_indices M2)) (kapp_args p))) (OptionType.some KExpr major)) meta2 meta (option_some_inj RecMeta meta2 meta (Eq.trans (OptionType RecMeta) (OptionType.some RecMeta meta2) (recmeta_for (red_rec the_red_env) nm) (OptionType.some RecMeta meta) (Eq.symm (OptionType RecMeta) (recmeta_for (red_rec the_red_env) nm) (OptionType.some RecMeta meta2) (Eq.substType Name (fun (N : Name) => Eq (OptionType RecMeta) (recmeta_for (red_rec the_red_env) N) (OptionType.some RecMeta meta2)) recname2 nm (option_some_inj Name recname2 nm (Eq.trans (OptionType Name) (OptionType.some Name recname2) (kexpr_const_name (kapp_fn p)) (OptionType.some Name nm) (Eq.symm (OptionType Name) (kexpr_const_name (kapp_fn p)) (OptionType.some Name recname2) h1) hhead)) h2)) hmeta)) h3)) hmaj)) h4) (Eq.substType Name (fun (N : Name) => Eq (OptionType RecRule) (recrule_for (red_rec the_red_env) N cname2) (OptionType.some RecRule rule2)) recname2 nm (option_some_inj Name recname2 nm (Eq.trans (OptionType Name) (OptionType.some Name recname2) (kexpr_const_name (kapp_fn p)) (OptionType.some Name nm) (Eq.symm (OptionType Name) (kexpr_const_name (kapp_fn p)) (OptionType.some Name recname2) h1) hhead)) h5))";

const SRC_STUCK_MAJOR_APP_ARM: &str = "def stuck_major_app_arm (nm : Name) (meta : RecMeta) (maj : KExpr) (hdef : Eq (OptionType KExpr) (defval_for (red_def the_red_env) nm) (OptionType.none KExpr)) (hrec : Eq (OptionType RecMeta) (recmeta_for (red_rec the_red_env) nm) (OptionType.some RecMeta meta)) (C : Type) (af : KExpr) (af2 : KExpr) (aa : KExpr) (aa2 : KExpr) (pf : par_reduces_cd the_red_env af af2) (pa : par_reduces_cd the_red_env aa aa2) (ihf : forall (m1 : KExpr), Eq (OptionType Name) (kexpr_const_name (kapp_fn af)) (OptionType.some Name nm) -> Eq (OptionType KExpr) (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args af))) (OptionType.some KExpr m1) -> par_reduces_cd_star the_red_env maj m1 -> (forall (m2 : KExpr), Eq (OptionType Name) (kexpr_const_name (kapp_fn af2)) (OptionType.some Name nm) -> Eq (OptionType KExpr) (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args af2))) (OptionType.some KExpr m2) -> par_reduces_cd_star the_red_env maj m2 -> C) -> C) (m1 : KExpr) (hh : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.app af aa))) (OptionType.some Name nm)) (hs : Eq (OptionType KExpr) (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args (KExpr.app af aa)))) (OptionType.some KExpr m1)) (hr : par_reduces_cd_star the_red_env maj m1) (k : forall (m2 : KExpr), Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.app af2 aa2))) (OptionType.some Name nm) -> Eq (OptionType KExpr) (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args (KExpr.app af2 aa2)))) (OptionType.some KExpr m2) -> par_reduces_cd_star the_red_env maj m2 -> C) : C := nat_le_trichotomy_t (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (list_length (kapp_args af)) C (fun (hlt : Le (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (list_length (kapp_args af))) => ihf m1 hh (list_head_drop_append_some_inv (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args af) aa m1 hlt hs) hr (fun (m2 : KExpr) (hh2 : Eq (OptionType Name) (kexpr_const_name (kapp_fn af2)) (OptionType.some Name nm)) (hs2 : Eq (OptionType KExpr) (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args af2))) (OptionType.some KExpr m2)) (hr2 : par_reduces_cd_star the_red_env maj m2) => k m2 hh2 (list_head_drop_append_some (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args af2) aa2 m2 hs2) hr2)) (fun (heq : Eq Nat (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (list_length (kapp_args af))) => under_applied_preserved_cd the_red_env nm meta hdef hrec C af af2 pf hh (Eq.subst Nat (fun (z : Nat) => Le (list_length (kapp_args af)) z) (list_length (kapp_args af)) (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (Eq.symm Nat (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (list_length (kapp_args af)) heq) (Le.refl (list_length (kapp_args af)))) (fun (hh2 : Eq (OptionType Name) (kexpr_const_name (kapp_fn af2)) (OptionType.some Name nm)) (hlen2 : Eq Nat (list_length (kapp_args af2)) (list_length (kapp_args af))) => k aa2 hh2 (minimal_major_is_last meta af2 aa2 (Eq.trans Nat (list_length (kapp_args af2)) (list_length (kapp_args af)) (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) hlen2 (Eq.symm Nat (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (list_length (kapp_args af)) heq))) (par_reduces_cd_star_trans the_red_env maj aa aa2 (Eq.substType KExpr (fun (Z : KExpr) => par_reduces_cd_star the_red_env maj Z) m1 aa (option_some_inj KExpr m1 aa (Eq.trans (OptionType KExpr) (OptionType.some KExpr m1) (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args (KExpr.app af aa)))) (OptionType.some KExpr aa) (Eq.symm (OptionType KExpr) (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args (KExpr.app af aa)))) (OptionType.some KExpr m1) hs) (minimal_major_is_last meta af aa (Eq.symm Nat (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (list_length (kapp_args af)) heq)))) hr) (par_reduces_cd_star.step the_red_env aa aa2 aa2 pa (par_reduces_cd_star.refl the_red_env aa2))))) (fun (hgt : Le (Nat.succ (list_length (kapp_args af))) (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) => option_none_ne_some_type KExpr m1 C (Eq.trans (OptionType KExpr) (OptionType.none KExpr) (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args (KExpr.app af aa)))) (OptionType.some KExpr m1) (Eq.symm (OptionType KExpr) (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args (KExpr.app af aa)))) (OptionType.none KExpr) (list_head_drop_none_of_le (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args (KExpr.app af aa)) (Eq.subst Nat (fun (z : Nat) => Le z (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (Nat.succ (list_length (kapp_args af))) (list_length (kapp_args (KExpr.app af aa))) (Eq.symm Nat (list_length (kapp_args (KExpr.app af aa))) (Nat.succ (list_length (kapp_args af))) (list_length_append_singleton (kapp_args af) aa)) hgt))) hs))";

const SRC_DELTA_DEAD_HEAD_NO_DELTA: &str = "def delta_dead_head_no_delta (nm : Name) (hdef : Eq (OptionType KExpr) (defval_for (red_def the_red_env) nm) (OptionType.none KExpr)) (C : Type) (e : KExpr) (e2 : KExpr) (hh : Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name nm)) (hstep : delta_step (red_def the_red_env) e e2) : C := option_none_ne_some_type KExpr e2 C (Eq.trans (OptionType KExpr) (OptionType.none KExpr) (delta_reduct (red_def the_red_env) e) (OptionType.some KExpr e2) (Eq.symm (OptionType KExpr) (delta_reduct (red_def the_red_env) e) (OptionType.none KExpr) (Eq.substType (OptionType Name) (fun (Z : OptionType Name) => Eq (OptionType KExpr) (opt_bind Name KExpr Z (fun (dname : Name) => opt_bind KExpr KExpr (defval_for (red_def the_red_env) dname) (fun (val : KExpr) => OptionType.some KExpr (apply_spine (kapp_args e) val)))) (OptionType.none KExpr)) (OptionType.some Name nm) (kexpr_const_name (kapp_fn e)) (Eq.symm (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name nm) hh) (Eq.substType (OptionType KExpr) (fun (W : OptionType KExpr) => Eq (OptionType KExpr) (opt_bind KExpr KExpr W (fun (val : KExpr) => OptionType.some KExpr (apply_spine (kapp_args e) val))) (OptionType.none KExpr)) (OptionType.none KExpr) (defval_for (red_def the_red_env) nm) (Eq.symm (OptionType KExpr) (defval_for (red_def the_red_env) nm) (OptionType.none KExpr) hdef) (Eq.refl (OptionType KExpr) (OptionType.none KExpr))))) hstep)";

impl Specification {
    /// The fourth alternative, closed.
    pub(super) fn add_stuck_major_recmeta(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(SRC_STUCK_MAJOR_RECMETA, "stuck_major_recmeta_no_ctor_reduct: THE FOURTH ALTERNATIVE -- a stuck major whose spine head is a const CARRYING recmeta has no constructor-headed reduct. This is the case stuck_major_confluence.rs recorded as not closing, and called circular rather than merely incomplete. \
\
It closes because the circularity is broken by a HYPOTHESIS, not by assuming the conclusion: nf_head wmajor is taken as a premise. That is not question-begging, because the consumer supplies it from the induction hypothesis at a STRICTLY SMALLER budget -- whnf_fuel_red_wh3_result_stuck_lt produces the smaller budget, and hnf3 at that budget produces nf_head. The one level down that used to be circular is now one level down in a well-founded recursion. \
\
Given nf_head wmajor, the argument is short: confluence yields a common reduct v headed by the constructor cname, head const-name preservation forces the recmeta-carrying head cn2 to BE cname, and RecEnvCtorNoRecMeta says a constructor carries no recmeta. Contradiction. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_STUCK_MAJOR_IOTA_ARM, "stuck_major_iota_arm_absurd: THE IOTA ARM OF THE COMING INDUCTION, refuted in line. A recursor spine whose major slot holds a REDUCT of maj cannot fire a top-level iota, given that no reduct of maj is constructor-headed with a matching rule. \
\
This is the piece that carries the entanglement. iota_immune_of_stuck_major cannot be split into spine-preservation-then-composition -- par_reduces_cd has iota as a TOP-LEVEL arm, so preservation holds only GIVEN iota never fires, which is what is being proved. The resolution is to refute the iota arm inside the induction, using the invariant established so far. This lemma IS that refutation, isolated so the surrounding recursion is pure bookkeeping. \
\
It reuses iota_step_major_head_none_absurd's recname2 = nm and meta2 = meta alignment verbatim rather than reproving it; the new work is only the last link. Where that lemma contradicts a major with no const head, this one transports h4 and h5 to the caller's major and hands them to hno, which the completed stuck-major classification supplies. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_STUCK_MAJOR_APP_ARM, "stuck_major_app_arm: THE APP CONGRUENCE ARM of the coming induction -- the only arm with real content, and the last piece of the def-eq completeness chain that required proof discovery rather than assembly. \
\
Splits major_idx against the length of the function part's argument list by nat_le_trichotomy_t (the Type-valued form; nat_le_succ_or takes C : Prop and is unusable here). Three branches: \
\
(1) SLOT STRICTLY INSIDE the function part. The trichotomy's klt continuation hands back exactly list_head_drop_append_some_inv's premise, so the slot pushes down with no arithmetic in between, the induction hypothesis runs, and list_head_drop_append_some pushes the result back up. The head passes through untouched because kapp_fn (app f a) unfolds to kapp_fn f. \
\
(2) BOUNDARY -- the slot IS the new argument. This is the branch that looks circular and is not: at exactly the boundary the function part carries major_idx arguments, one short of firing, so it CANNOT iota-step for a purely arithmetic reason. under_applied_preserved_cd therefore supplies both the head equation and the length equation with NO appeal to the induction hypothesis, making this a BASE case. minimal_major_is_last identifies the slot content on both sides, and par_reduces_cd_star_trans extends the major's reduction by the argument's step. \
\
(3) SLOT ABSENT -- under-applied. list_length_append_singleton rewrites the extended spine's length so the trichotomy's kgt branch becomes list_head_drop_none_of_le's premise exactly, and the slot hypothesis is refuted. \
\
DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_DELTA_DEAD_HEAD_NO_DELTA, "delta_dead_head_no_delta: THE DELTA ARM of the coming induction. A spine whose head constant has no def value cannot take a delta step. \
\
No induction is needed, which was NOT the expectation: delta_reduct is already SPINE-AWARE -- it is a two-level opt_bind on kexpr_const_name (kapp_fn e) and then defval_for, re-applying kapp_args e -- so the head hypothesis and the dead-value hypothesis drive the chain to none by two transports, and delta_step is just that function's graph. The nine-arm KExpr.rec this was first scoped as is unnecessary. \
\
Note why the two obvious candidates do NOT fit. delta_step_head_none_absurd_type wants kexpr_const_name (kapp_fn e) = none, but here the head HAS a name and merely lacks a value -- delta-dead is not head-none. iota_neutral_no_delta wants iota_neutral e, which the induction's invariant cannot carry, because iota_neutral's app constructor demands iota_immune, the very thing being proved. DerivedProved, zero axiom_deps.")?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `nf_head wmajor` must be a PREMISE. If this lemma ever derived it
    /// internally it would be assuming the residual it exists to discharge.
    #[test]
    fn test_nf_head_is_taken_as_a_premise() {
        assert!(
            SRC_STUCK_MAJOR_RECMETA.contains("(hnf : nf_head wmajor)"),
            "nf_head must be a premise the caller supplies at a smaller budget"
        );
    }

    /// The recmeta-carrying hypothesis is what makes the case contradictory.
    /// Without it the argument would prove nothing: `cn2 = cname` alone is
    /// consistent.
    #[test]
    fn test_the_recmeta_hypothesis_is_present_and_used() {
        assert!(SRC_STUCK_MAJOR_RECMETA.contains("(hrecmeta : Eq (OptionType RecMeta)"));
        assert!(
            SRC_STUCK_MAJOR_RECMETA.contains("recenv_ctor_no_recmeta_cname"),
            "the contradiction comes from RecEnvCtorNoRecMeta at the constructor"
        );
    }

    /// The head identification must go through const-name preservation, not
    /// through the tag: the tag cannot distinguish two different constants.
    #[test]
    fn test_heads_are_identified_by_name_not_tag() {
        assert!(SRC_STUCK_MAJOR_RECMETA.contains("nf_head_star_preserves_const_name"));
        assert!(!SRC_STUCK_MAJOR_RECMETA.contains("kexpr_tag"));
    }

    /// It must actually use confluence — that is where `i8` entered.
    #[test]
    fn test_it_goes_through_the_confluence_core() {
        assert!(
            SRC_STUCK_MAJOR_RECMETA.contains("stuck_major_join_ctor_head_at_the_red_env"),
            "the common reduct comes from the confluence core"
        );
    }

    /// The iota arm must be refuted USING the invariant (hno applied at the
    /// caller's major), not by a structural defect. A proof that closed without
    /// mentioning hno would be the non-entangled version, which cannot exist:
    /// preservation holds only given that iota never fires.
    #[test]
    fn test_iota_arm_is_refuted_through_hno() {
        assert!(
            SRC_STUCK_MAJOR_IOTA_ARM.contains("hno cname2 rule2 mjr hr"),
            "the iota arm must apply hno at the caller's major, with its reduction"
        );
        assert!(
            SRC_STUCK_MAJOR_IOTA_ARM.contains("iota_reduct_some_inv_type"),
            "the firing data comes from the extraction primitive"
        );
    }

    /// It must take the reduction `maj =>* mjr` — that is what makes hno
    /// applicable and is the whole content of the invariant being threaded.
    #[test]
    fn test_it_carries_the_major_reduction() {
        assert!(
            SRC_STUCK_MAJOR_IOTA_ARM.contains("(hr : par_reduces_cd_star the_red_env maj mjr)"),
            "the slot content must be known to be a REDUCT of the original major"
        );
    }

    /// The boundary branch must close via `under_applied_preserved_cd`, NOT via
    /// the induction hypothesis. That is what makes it a base case; routing it
    /// through the IH would be the circular reading.
    #[test]
    fn test_boundary_branch_is_a_base_case() {
        assert!(
            SRC_STUCK_MAJOR_APP_ARM.contains("under_applied_preserved_cd"),
            "the boundary closes because the function part is one argument short of firing"
        );
        assert!(
            SRC_STUCK_MAJOR_APP_ARM.contains("minimal_major_is_last"),
            "the slot content at the boundary is the last argument, on both sides"
        );
    }

    /// The Type-valued trichotomy. `nat_le_succ_or` takes `C : Prop` and cannot
    /// split this goal — a trap already recorded in `slot_collapse.rs`.
    #[test]
    fn test_split_uses_the_type_valued_trichotomy() {
        assert!(SRC_STUCK_MAJOR_APP_ARM.contains("nat_le_trichotomy_t"));
        assert!(!SRC_STUCK_MAJOR_APP_ARM.contains("nat_le_succ_or"));
    }

    /// All three branches must be present and distinct: push-down, boundary,
    /// and absent-slot. A missing branch would mean the split was not exhaustive.
    #[test]
    fn test_all_three_slot_branches_are_supplied() {
        for lemma in [
            "list_head_drop_append_some_inv",
            "list_head_drop_append_some",
            "list_head_drop_none_of_le",
            "list_length_append_singleton",
        ] {
            assert!(
                SRC_STUCK_MAJOR_APP_ARM.contains(lemma),
                "branch lemma {lemma} missing"
            );
        }
    }

    #[test]
    fn test_source_balanced_ascii_prime_free() {
        for src in [
            SRC_STUCK_MAJOR_RECMETA,
            SRC_STUCK_MAJOR_IOTA_ARM,
            SRC_STUCK_MAJOR_APP_ARM,
            SRC_DELTA_DEAD_HEAD_NO_DELTA,
        ] {
            let mut depth: i64 = 0;
            for ch in src.chars() {
                match ch {
                    '(' => depth += 1,
                    ')' => depth -= 1,
                    _ => {}
                }
                assert!(depth >= 0, "close paren before its open");
            }
            assert_eq!(depth, 0, "unbalanced parens");
            assert!(src.is_ascii());
            assert!(!src.contains('\''));
        }
    }

    /// The delta arm must NOT route through the two near-miss lemmas. Both look
    /// applicable and neither is: `delta_step_head_none_absurd_type` needs a
    /// head with no NAME (here it has one, and lacks a VALUE), and
    /// `iota_neutral_no_delta` needs `iota_neutral`, which the invariant cannot
    /// carry without circularity.
    #[test]
    fn test_delta_arm_avoids_the_near_miss_lemmas() {
        for wrong in ["delta_step_head_none_absurd", "iota_neutral_no_delta"] {
            assert!(
                !SRC_DELTA_DEAD_HEAD_NO_DELTA.contains(wrong),
                "{wrong} does not apply here; delta-dead is not head-none"
            );
        }
        assert!(
            SRC_DELTA_DEAD_HEAD_NO_DELTA.contains("delta_reduct"),
            "it drives delta_reduct's own opt_bind chain to none"
        );
    }

    /// No recursion: `delta_reduct` is spine-aware, so the whole arm is two
    /// transports. A `KExpr.rec` here would mean the spine-awareness was missed.
    #[test]
    fn test_delta_arm_needs_no_recursion() {
        assert!(
            !SRC_DELTA_DEAD_HEAD_NO_DELTA.contains("KExpr.rec"),
            "delta_reduct already looks through the spine; no induction is needed"
        );
    }

    #[test]
    fn test_recmeta_source_balanced() {
        let mut depth: i64 = 0;
        for ch in SRC_STUCK_MAJOR_RECMETA.chars() {
            match ch {
                '(' => depth += 1,
                ')' => depth -= 1,
                _ => {}
            }
            assert!(depth >= 0, "close paren before its open");
        }
        assert_eq!(depth, 0, "unbalanced parens");
        assert!(SRC_STUCK_MAJOR_RECMETA.is_ascii());
        assert!(!SRC_STUCK_MAJOR_RECMETA.contains('\''));
    }
}
