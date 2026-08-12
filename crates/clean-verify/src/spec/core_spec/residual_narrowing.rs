// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Narrowing the residual's last row to its two open sub-cases.
//!
//! # A correction to `rigid_bridge.rs`
//!
//! That module's doc says the dispatch is blocked because `core_spec` has no Nat
//! trichotomy — "no `le_total`, no `le_dec`, no `le_or_gt`, no `le_antisymm`".
//! Those four NAMES are absent, but **the thing was already there**:
//! `nat_lt_le_dichotomy` (`dependent_sn_richmodel.rs`), `DerivedProved`, zero
//! axioms — and already used for this exact under-applied-vs-past-the-major
//! split in `wh_step_mono_proof.rs`. Only `le_antisymm` was genuinely missing.
//!
//! # Why not `OrType (Le a b) (Le b a)`
//!
//! It is ill-typed. `Le` is **Prop**-valued and `OrType` takes **Type**
//! parameters, and this kernel is non-cumulative. `LiftP` would work and is
//! strictly worse. `NatLtLeDichotomy` is already Type-valued with Prop fields,
//! so it large-eliminates into a `nf_head` goal with no lift on either side.
//!
//! # What the narrowing buys
//!
//! The delta-dead recursor class splits four ways on spine length against
//! `MAJOR_IDX`, and **two of the four already had suppliers that could not be
//! selected between**. Now they are selected. What remains is carried as TWO
//! SEPARATE premises rather than one lumped one, so each open obligation is
//! visible on its own.
//!
//! `kexpr_top_not_bvar_bvar_empty` is what makes the narrowing real rather than
//! cosmetic: it proves the carried boundary premise and the discharged bvar row
//! are disjoint, so the former cannot silently absorb the latter.
//!
//! `DerivedProved`, empty axiom closures.

use crate::spec::error::SpecError;
use crate::spec::Specification;

impl Specification {
    /// The missing antisymmetry, the CPS trichotomy, and the narrowed residual.
    pub(super) fn add_residual_narrowing(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            SRC_LE_ANTISYMM,
            "le_antisymm: two Nats that bound each other are equal. THE ONLY GENUINELY MISSING PIECE of the dispatch — the trichotomy itself already existed. Prop target throughout, so Le.rec's subsingleton-elimination is never a problem. DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(
            SRC_LE_ANTISYMM_REFL_WITNESS,
            "le_antisymm_refl_witness (NON-VACUITY): the hypothesis class is inhabited. DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(
            SRC_NAT_LE_TRICHOTOMY_T,
            "nat_le_trichotomy_t: TYPE-VALUED trichotomy in continuation-passing form, so it dispatches directly into a Type goal like nf_head. Two nested NatLtLeDichotomy.rec; the doubly-inr corner is closed by le_antisymm. \\
\\
NOTE what this is NOT built from. The obvious `OrType (Le a b) (Le b a)` is ILL-TYPED: Le is Prop-valued (foundation_types.rs) and OrType takes Type parameters, and this kernel is non-cumulative. LiftP would work but is strictly worse. NatLtLeDichotomy is already Type-valued with Prop fields, so it large-eliminates with no lift on either side. DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(
            SRC_KEXPR_TOP_NOT_BVAR,
            "kexpr_top_not_bvar: a TOP-CONSTRUCTOR discriminator — Empty at bvar, unit elsewhere. \\
\\
Deliberately NOT kapp_head_bvar_absurd, which recurses through app to the SPINE head and would therefore make `app (bvar 0) x` — a perfectly legitimate stuck non-bvar major — unrepresentable. The distinction is the point. DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(
            SRC_KEXPR_TOP_NOT_BVAR_SORT_WITNESS,
            "kexpr_top_not_bvar_sort_witness (NON-VACUITY). DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(
            SRC_KEXPR_TOP_NOT_BVAR_BVARAPP_WITNESS,
            "kexpr_top_not_bvar_bvarapp_witness (NON-VACUITY) at `app (bvar 0) (sort 0)` — the case that distinguishes this discriminator from kapp_head_bvar_absurd. DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(
            SRC_KEXPR_TOP_NOT_BVAR_BVAR_EMPTY,
            "kexpr_top_not_bvar_bvar_empty: the carried boundary premise and the DISCHARGED bvar row are DISJOINT. Without this, bnd_res could silently absorb the row that already has a supplier, and the narrowing would be cosmetic. DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(
            SRC_HNF3_APP_RESIDUAL_REC_NARROWED,
            "hnf3_app_residual_rec_narrowed: rec_res NARROWED from the whole delta-dead recursor class to exactly the two genuinely open sub-cases. \\
\\
The class splits four ways on the spine length against MAJOR_IDX, and TWO OF THE FOUR ALREADY HAD SUPPLIERS that could not be selected between. Now they are: under-applied discharges through hnf3_app_residual_of_under_applied, and the at-boundary bvar-major row through hnf3_app_residual_of_bvar_major, via the trichotomy plus a nine-arm convoy on the major. \\
\\
What remains is carried as TWO SEPARATE premises rather than one lumped one, so each open obligation is visible on its own: bnd_res for a major at the boundary that is not a bvar, over_res for a spine with arguments past the major slot. Both are stated on the function part, so they read as complements of each other and of the discharged case. Neither is vacuous — both antecedent classes are inhabited at the real reflected Nat.rec. DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(
            SRC_HNF3_APP_RESIDUAL_COVERED_NARROWED,
            "hnf3_app_residual_covered_narrowed: the residual with ten of eleven head shapes discharged and the eleventh reduced to its two genuinely open sub-cases. The narrowest honest statement available today. DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }
}

const SRC_LE_ANTISYMM: &str = "def le_antisymm (a : Nat) (b : Nat) (hab : Le a b) (hba : Le b a) : Eq Nat a b := nat_le_succ_or a b hab (Eq Nat a b) (fun (h : Eq Nat a b) => h) (fun (hlt : Le (Nat.succ a) b) => Empty.rec (fun (_e : Empty) => Eq Nat a b) (le_succ_self_empty a (le_trans (Nat.succ a) b a hlt hba)))";

const SRC_LE_ANTISYMM_REFL_WITNESS: &str = "def le_antisymm_refl_witness : Eq Nat Nat.zero Nat.zero := le_antisymm Nat.zero Nat.zero (Le.refl Nat.zero) (Le.refl Nat.zero)";

const SRC_NAT_LE_TRICHOTOMY_T: &str = "def nat_le_trichotomy_t (a : Nat) (b : Nat) (C : Type) (klt : Le (Nat.succ a) b -> C) (keq : Eq Nat a b -> C) (kgt : Le (Nat.succ b) a -> C) : C := NatLtLeDichotomy.rec a b (fun (_d : NatLtLeDichotomy a b) => C) (fun (hlt : Lt a b) => klt (lt_to_le_succ a b hlt)) (fun (hge : Le b a) => NatLtLeDichotomy.rec b a (fun (_d2 : NatLtLeDichotomy b a) => C) (fun (hgt : Lt b a) => kgt (lt_to_le_succ b a hgt)) (fun (hle : Le a b) => keq (le_antisymm a b hle hge)) (nat_lt_le_dichotomy b a)) (nat_lt_le_dichotomy a b)";

const SRC_KEXPR_TOP_NOT_BVAR: &str = "def kexpr_top_not_bvar (e : KExpr) : Type := KExpr.rec (fun (_z : KExpr) => Type) (fun (sl : Level) => ConstFreeUnit) (fun (bi : Nat) => Empty) (fun (af : KExpr) (aa : KExpr) (_cf : Type) (_ca : Type) => ConstFreeUnit) (fun (lt2 : KExpr) (lb2 : KExpr) (_clt : Type) (_clb : Type) => ConstFreeUnit) (fun (pt2 : KExpr) (pb2 : KExpr) (_cpt : Type) (_cpb : Type) => ConstFreeUnit) (fun (cn : Name) (cus : ListType Level) => ConstFreeUnit) (fun (zt2 : KExpr) (zv2 : KExpr) (zb2 : KExpr) (_c1 : Type) (_c2 : Type) (_c3 : Type) => ConstFreeUnit) (fun (ps2 : Name) (pi2 : Nat) (psub2 : KExpr) (_csub : Type) => ConstFreeUnit) (fun (lv : Nat) => ConstFreeUnit) e";

const SRC_KEXPR_TOP_NOT_BVAR_SORT_WITNESS: &str = "def kexpr_top_not_bvar_sort_witness : kexpr_top_not_bvar (KExpr.sort Level.zero) := ConstFreeUnit.triv";

const SRC_KEXPR_TOP_NOT_BVAR_BVARAPP_WITNESS: &str = "def kexpr_top_not_bvar_bvarapp_witness : kexpr_top_not_bvar (KExpr.app (KExpr.bvar Nat.zero) (KExpr.sort Level.zero)) := ConstFreeUnit.triv";

const SRC_KEXPR_TOP_NOT_BVAR_BVAR_EMPTY: &str = "def kexpr_top_not_bvar_bvar_empty (bi : Nat) (h : kexpr_top_not_bvar (KExpr.bvar bi)) : Empty := h";

const SRC_HNF3_APP_RESIDUAL_REC_NARROWED: &str = "def hnf3_app_residual_rec_narrowed (bnd_res : forall (r1 : KExpr) (k1 : Nat) (zf1 : KExpr) (za1 : KExpr) (nm1 : Name) (meta1 : RecMeta), Eq (OptionType KExpr) (defval_for (red_def the_red_env) nm1) (OptionType.none KExpr) -> Eq (OptionType RecMeta) (recmeta_for (red_rec the_red_env) nm1) (OptionType.some RecMeta meta1) -> Eq (OptionType Name) (kexpr_const_name (kapp_fn zf1)) (OptionType.some Name nm1) -> Eq Nat (list_length (kapp_args zf1)) (Nat.add (Nat.add (Nat.add (recmeta_num_params meta1) (recmeta_num_motives meta1)) (recmeta_num_minors meta1)) (recmeta_num_indices meta1)) -> kexpr_top_not_bvar za1 -> wh3_stuck_at k1 r1 -> Eq KExpr r1 (KExpr.app zf1 za1) -> nf_head r1) (over_res : forall (r1 : KExpr) (k1 : Nat) (zf1 : KExpr) (za1 : KExpr) (nm1 : Name) (meta1 : RecMeta), Eq (OptionType KExpr) (defval_for (red_def the_red_env) nm1) (OptionType.none KExpr) -> Eq (OptionType RecMeta) (recmeta_for (red_rec the_red_env) nm1) (OptionType.some RecMeta meta1) -> Eq (OptionType Name) (kexpr_const_name (kapp_fn zf1)) (OptionType.some Name nm1) -> Le (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta1) (recmeta_num_motives meta1)) (recmeta_num_minors meta1)) (recmeta_num_indices meta1))) (list_length (kapp_args zf1)) -> wh3_stuck_at k1 r1 -> Eq KExpr r1 (KExpr.app zf1 za1) -> nf_head r1) (r0 : KExpr) (k0 : Nat) (zf : KExpr) (za : KExpr) (nm : Name) (meta : RecMeta) (hdef : Eq (OptionType KExpr) (defval_for (red_def the_red_env) nm) (OptionType.none KExpr)) (hrec : Eq (OptionType RecMeta) (recmeta_for (red_rec the_red_env) nm) (OptionType.some RecMeta meta)) (hh : Eq (OptionType Name) (kexpr_const_name (kapp_fn r0)) (OptionType.some Name nm)) (hs : wh3_stuck_at k0 r0) (heq : Eq KExpr r0 (KExpr.app zf za)) : nf_head r0 := nat_le_trichotomy_t (list_length (kapp_args zf)) (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (nf_head r0) (fun (hlt : Le (Nat.succ (list_length (kapp_args zf))) (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) => hnf3_app_residual_of_under_applied r0 k0 zf za nm meta hdef hrec hh (Eq.subst Nat (fun (zn : Nat) => Le zn (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (Nat.succ (list_length (kapp_args zf))) (list_length (kapp_args r0)) (Eq.symm Nat (list_length (kapp_args r0)) (Nat.succ (list_length (kapp_args zf))) (Eq.subst KExpr (fun (xl : KExpr) => Eq Nat (list_length (kapp_args xl)) (Nat.succ (list_length (kapp_args zf)))) (KExpr.app zf za) r0 (Eq.symm KExpr r0 (KExpr.app zf za) heq) (kapp_args_length_app zf za))) hlt) hs heq) (fun (hbnd : Eq Nat (list_length (kapp_args zf)) (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) => KExpr.rec (fun (zx : KExpr) => Eq KExpr za zx -> nf_head r0) (fun (sl : Level) (hz : Eq KExpr za (KExpr.sort sl)) => bnd_res r0 k0 zf za nm meta hdef hrec (Eq.subst KExpr (fun (xh : KExpr) => Eq (OptionType Name) (kexpr_const_name (kapp_fn xh)) (OptionType.some Name nm)) r0 (KExpr.app zf za) heq hh) hbnd (Eq.substType KExpr (fun (zy : KExpr) => kexpr_top_not_bvar zy) (KExpr.sort sl) za (Eq.symm KExpr za (KExpr.sort sl) hz) ConstFreeUnit.triv) hs heq) (fun (bi : Nat) (hz : Eq KExpr za (KExpr.bvar bi)) => hnf3_app_residual_of_bvar_major r0 k0 zf za nm meta bi hdef hrec (Eq.subst KExpr (fun (xh : KExpr) => Eq (OptionType Name) (kexpr_const_name (kapp_fn xh)) (OptionType.some Name nm)) r0 (KExpr.app zf za) heq hh) hbnd hz hs heq) (fun (af : KExpr) (aa : KExpr) (_ihaf : Eq KExpr za af -> nf_head r0) (_ihaa : Eq KExpr za aa -> nf_head r0) (hz : Eq KExpr za (KExpr.app af aa)) => bnd_res r0 k0 zf za nm meta hdef hrec (Eq.subst KExpr (fun (xh : KExpr) => Eq (OptionType Name) (kexpr_const_name (kapp_fn xh)) (OptionType.some Name nm)) r0 (KExpr.app zf za) heq hh) hbnd (Eq.substType KExpr (fun (zy : KExpr) => kexpr_top_not_bvar zy) (KExpr.app af aa) za (Eq.symm KExpr za (KExpr.app af aa) hz) ConstFreeUnit.triv) hs heq) (fun (lt2 : KExpr) (lb2 : KExpr) (_ihlt : Eq KExpr za lt2 -> nf_head r0) (_ihlb : Eq KExpr za lb2 -> nf_head r0) (hz : Eq KExpr za (KExpr.lam lt2 lb2)) => bnd_res r0 k0 zf za nm meta hdef hrec (Eq.subst KExpr (fun (xh : KExpr) => Eq (OptionType Name) (kexpr_const_name (kapp_fn xh)) (OptionType.some Name nm)) r0 (KExpr.app zf za) heq hh) hbnd (Eq.substType KExpr (fun (zy : KExpr) => kexpr_top_not_bvar zy) (KExpr.lam lt2 lb2) za (Eq.symm KExpr za (KExpr.lam lt2 lb2) hz) ConstFreeUnit.triv) hs heq) (fun (pt2 : KExpr) (pb2 : KExpr) (_ihpt : Eq KExpr za pt2 -> nf_head r0) (_ihpb : Eq KExpr za pb2 -> nf_head r0) (hz : Eq KExpr za (KExpr.pi pt2 pb2)) => bnd_res r0 k0 zf za nm meta hdef hrec (Eq.subst KExpr (fun (xh : KExpr) => Eq (OptionType Name) (kexpr_const_name (kapp_fn xh)) (OptionType.some Name nm)) r0 (KExpr.app zf za) heq hh) hbnd (Eq.substType KExpr (fun (zy : KExpr) => kexpr_top_not_bvar zy) (KExpr.pi pt2 pb2) za (Eq.symm KExpr za (KExpr.pi pt2 pb2) hz) ConstFreeUnit.triv) hs heq) (fun (cn : Name) (cus : ListType Level) (hz : Eq KExpr za (KExpr.const cn cus)) => bnd_res r0 k0 zf za nm meta hdef hrec (Eq.subst KExpr (fun (xh : KExpr) => Eq (OptionType Name) (kexpr_const_name (kapp_fn xh)) (OptionType.some Name nm)) r0 (KExpr.app zf za) heq hh) hbnd (Eq.substType KExpr (fun (zy : KExpr) => kexpr_top_not_bvar zy) (KExpr.const cn cus) za (Eq.symm KExpr za (KExpr.const cn cus) hz) ConstFreeUnit.triv) hs heq) (fun (zt2 : KExpr) (zv2 : KExpr) (zb2 : KExpr) (_ihzt : Eq KExpr za zt2 -> nf_head r0) (_ihzv : Eq KExpr za zv2 -> nf_head r0) (_ihzb : Eq KExpr za zb2 -> nf_head r0) (hz : Eq KExpr za (KExpr.let_ zt2 zv2 zb2)) => bnd_res r0 k0 zf za nm meta hdef hrec (Eq.subst KExpr (fun (xh : KExpr) => Eq (OptionType Name) (kexpr_const_name (kapp_fn xh)) (OptionType.some Name nm)) r0 (KExpr.app zf za) heq hh) hbnd (Eq.substType KExpr (fun (zy : KExpr) => kexpr_top_not_bvar zy) (KExpr.let_ zt2 zv2 zb2) za (Eq.symm KExpr za (KExpr.let_ zt2 zv2 zb2) hz) ConstFreeUnit.triv) hs heq) (fun (ps2 : Name) (pi2 : Nat) (psub2 : KExpr) (_ihsub : Eq KExpr za psub2 -> nf_head r0) (hz : Eq KExpr za (KExpr.proj ps2 pi2 psub2)) => bnd_res r0 k0 zf za nm meta hdef hrec (Eq.subst KExpr (fun (xh : KExpr) => Eq (OptionType Name) (kexpr_const_name (kapp_fn xh)) (OptionType.some Name nm)) r0 (KExpr.app zf za) heq hh) hbnd (Eq.substType KExpr (fun (zy : KExpr) => kexpr_top_not_bvar zy) (KExpr.proj ps2 pi2 psub2) za (Eq.symm KExpr za (KExpr.proj ps2 pi2 psub2) hz) ConstFreeUnit.triv) hs heq) (fun (lv : Nat) (hz : Eq KExpr za (KExpr.lit lv)) => bnd_res r0 k0 zf za nm meta hdef hrec (Eq.subst KExpr (fun (xh : KExpr) => Eq (OptionType Name) (kexpr_const_name (kapp_fn xh)) (OptionType.some Name nm)) r0 (KExpr.app zf za) heq hh) hbnd (Eq.substType KExpr (fun (zy : KExpr) => kexpr_top_not_bvar zy) (KExpr.lit lv) za (Eq.symm KExpr za (KExpr.lit lv) hz) ConstFreeUnit.triv) hs heq) za (Eq.refl KExpr za)) (fun (hgt : Le (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (list_length (kapp_args zf))) => over_res r0 k0 zf za nm meta hdef hrec (Eq.subst KExpr (fun (xh : KExpr) => Eq (OptionType Name) (kexpr_const_name (kapp_fn xh)) (OptionType.some Name nm)) r0 (KExpr.app zf za) heq hh) hgt hs heq)";

const SRC_HNF3_APP_RESIDUAL_COVERED_NARROWED: &str = "def hnf3_app_residual_covered_narrowed (bnd_res : forall (r1 : KExpr) (k1 : Nat) (zf1 : KExpr) (za1 : KExpr) (nm1 : Name) (meta1 : RecMeta), Eq (OptionType KExpr) (defval_for (red_def the_red_env) nm1) (OptionType.none KExpr) -> Eq (OptionType RecMeta) (recmeta_for (red_rec the_red_env) nm1) (OptionType.some RecMeta meta1) -> Eq (OptionType Name) (kexpr_const_name (kapp_fn zf1)) (OptionType.some Name nm1) -> Eq Nat (list_length (kapp_args zf1)) (Nat.add (Nat.add (Nat.add (recmeta_num_params meta1) (recmeta_num_motives meta1)) (recmeta_num_minors meta1)) (recmeta_num_indices meta1)) -> kexpr_top_not_bvar za1 -> wh3_stuck_at k1 r1 -> Eq KExpr r1 (KExpr.app zf1 za1) -> nf_head r1) (over_res : forall (r1 : KExpr) (k1 : Nat) (zf1 : KExpr) (za1 : KExpr) (nm1 : Name) (meta1 : RecMeta), Eq (OptionType KExpr) (defval_for (red_def the_red_env) nm1) (OptionType.none KExpr) -> Eq (OptionType RecMeta) (recmeta_for (red_rec the_red_env) nm1) (OptionType.some RecMeta meta1) -> Eq (OptionType Name) (kexpr_const_name (kapp_fn zf1)) (OptionType.some Name nm1) -> Le (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta1) (recmeta_num_motives meta1)) (recmeta_num_minors meta1)) (recmeta_num_indices meta1))) (list_length (kapp_args zf1)) -> wh3_stuck_at k1 r1 -> Eq KExpr r1 (KExpr.app zf1 za1) -> nf_head r1) (r0 : KExpr) (k0 : Nat) (zf : KExpr) (za : KExpr) (hs : wh3_stuck_at k0 r0) (heq : Eq KExpr r0 (KExpr.app zf za)) : nf_head r0 := hnf3_app_residual_covered (hnf3_app_residual_rec_narrowed bnd_res over_res) r0 k0 zf za hs heq";
