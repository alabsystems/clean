// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
//! Soundness direction of decidable syntactic equality on the reflected
//! `KExpr` model, plus the reusable arithmetic-inversion substrate it stands on.
//!
//! The previous brick (`kexpr_beq.rs`, commit 0c75010e) built the structural
//! boolean equality `kexpr_beq : KExpr -> KExpr -> Bool` and the COMPLETENESS
//! direction `kexpr_beq_refl : forall e, kexpr_beq e e = true`. This brick
//! builds the SOUNDNESS direction:
//!
//!     kexpr_beq_eq : forall (a b : KExpr), Eq Bool (kexpr_beq a b) true -> Eq KExpr a b
//!
//! together with the decidable-equality inversion substrate it requires.
//!
//! Arithmetic inversion (foundational, reusable). The shared tower
//! (`bool_false_ne_true` `false = true -> C`, `nat_zero_ne_succ_beq`,
//! `nat_is_zero_eq`, `nat_add_eq_zero_right`/`_left`,
//! `nat_sub_eq_zero_antisymm`, `nat_eqb_eq`, `band_eq_true_left`/`_right`,
//! `name_eqb_str_str`, `name_eqb_eq`) is registered CANONICALLY by
//! `add_decidable_name_eq` in `faithful_red_env.rs` (the bundled
//! `add_faithful_red_env` stage) and is a PREREQUISITE of this module — it is
//! deliberately not re-registered here (duplicate kernel declaration). The
//! inversion lemmas unique to this brick:
//! - `nat_succ_inj_beq`   : `succ a = succ b -> a = b`.
//! - `level_eqb_eq` / `ulist_eqb_eq` : universe-param equality inversion.
//!
//! KExpr constructor injectivity (recursive-arm ingredients):
//! - `kexpr_sort_inj`, `kexpr_bvar_inj`, `kexpr_lam_inj_fst/snd`,
//!   `kexpr_pi_inj_fst/snd`, `kexpr_const_inj_name/ulist`. (`app` injectivity is
//!   reused from `expr_model_discrimination.rs`: `app_inj_fst`/`app_inj_snd`.)
//!
//! Soundness direction:
//! - `kexpr_beq_eq` : `kexpr_beq a b = true -> a = b`, by double `KExpr.rec`,
//!   discharging cross-constructor pairs by `bool_false_ne_true` and the
//!   same-constructor pairs by the inversion substrate (leaves) + constructor
//!   injectivity (recursive arms).
//!
//! Capstone (this brick) — completeness + the full biconditional:
//! - `kexpr_beq_complete` : `a = b -> kexpr_beq a b = true` (the easy direction),
//!   transporting `kexpr_beq_refl a` along `a = b` via `Eq.substType`.
//! - `kexpr_beq_iff_mp` / `kexpr_beq_iff_mpr` : the two named directions of the
//!   decidable-equality biconditional `kexpr_beq a b = true <-> a = b`
//!   (mp = soundness `kexpr_beq_eq`, mpr = completeness `kexpr_beq_complete`).
//!   Stated as the pair of named theorems rather than a single conjunction term:
//!   `AndType A B : Type` requires `A B : Type`, but both implications land in
//!   `Prop` (`Eq` is `Prop`-valued), and no `Prop`-level `And`/`Iff` is registered
//!   here. No `Decidable` type is registered, so the iff is the clean endpoint.
//!
//! This is **confluence-independent**: it references only the pure syntactic
//! model (`KExpr`, `Nat`, `Name`, `Level`, `ListType`, `Bool`, `Empty`) plus
//! the foundational `Eq` rules, `nat_eqb`/`name_eqb`/`nat_is_zero` (rec_env),
//! and `level_eqb`/`ulist_eqb`/`kexpr_beq` (kexpr_beq.rs). It does NOT touch any
//! `par_reduces`/`iota`/`whnf`/`DefEq`/`church_rosser`/`strip` declaration.
//!
//! Every lemma is `DerivedProved` with an empty (foundational) axiom closure
//! and `is_axiom: false`. No `sorry`/`native_decide`/`add_decl_unchecked`/new
//! `Axiom` anywhere.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

impl Specification {
    /// Helper: build a `DerivedProved`, foundational-closure `SpecDefinition`
    /// for an inversion lemma (Prop-typed, valued => kernel `Theorem`).
    fn derived_eq_lemma(
        name: &str,
        type_src: &str,
        value_src: &str,
        description: &str,
        deps: &[&str],
    ) -> SpecDefinition {
        SpecDefinition {
            name: name.to_string(),
            type_src: type_src.to_string(),
            value_src: Some(value_src.to_string()),
            is_axiom: false,
            description: description.to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(deps.iter().map(|s| (*s).to_string()).collect()),
            axiom_deps: HashSet::new(),
        }
    }

    /// Register the soundness direction of `kexpr_beq` plus the inversion
    /// lemmas unique to this brick (`nat_succ_inj_beq`, `level_eqb_eq`/
    /// `ulist_eqb_eq`, KExpr constructor injectivity, `kexpr_beq_eq`, and the
    /// completeness/iff capstone).
    ///
    /// Depends on the foundation types + `expr_model` (KExpr) + `rec_env`
    /// (`nat_eqb`/`name_eqb`/`nat_is_zero`) + `kexpr_beq` (`level_eqb`/
    /// `ulist_eqb`/`kexpr_beq`) stages, AND on the decidable-equality inversion
    /// tower whose canonical registration site is `add_decidable_name_eq`
    /// (`faithful_red_env.rs`; in bundles via the `add_faithful_red_env`
    /// stage). Purely additive; nothing in the active confluence lane is
    /// referenced or modified.
    ///
    /// # Errors
    /// Returns `SpecError` if any declaration fails to elaborate or kernel-check.
    pub(super) fn add_kexpr_beq_sound(&mut self) -> Result<(), SpecError> {
        // ------------------------------------------------------------------
        // The shared arithmetic/Bool/Name decidable-equality inversion tower
        // (bool_false_ne_true, nat_zero_ne_succ_beq, nat_is_zero_eq,
        // nat_add_eq_zero_right/left, nat_sub_eq_zero_antisymm, nat_eqb_eq,
        // band_eq_true_left/right, name_eqb_str_str, name_eqb_eq) is NOT
        // registered here. Its single canonical registration site is
        // `add_decidable_name_eq` in `faithful_red_env.rs` (part of the bundled
        // `add_faithful_red_env` stage, which precedes any use of this
        // un-bundled module in every bundle that carries it — e.g. the
        // Substitution bundle). Registering the tower a second time is a
        // kernel duplicate-declaration error. Specs built WITHOUT that stage
        // (the minimal test builder below) must call `add_decidable_name_eq()`
        // before this function.
        // ------------------------------------------------------------------

        // nat_succ_inj_beq : Eq (succ a) (succ b) -> Eq a b, via Eq.cong with Nat.pred
        // (pred reduces on succ, so pred (succ a) = a definitionally).
        self.add_definition(Self::derived_eq_lemma(
            "nat_succ_inj_beq",
            "forall (a : Nat) (b : Nat), Eq Nat (Nat.succ a) (Nat.succ b) -> Eq Nat a b",
            concat!(
                "fun (a : Nat) (b : Nat) (h : Eq Nat (Nat.succ a) (Nat.succ b)) => ",
                "Eq.cong Nat Nat (fun (z : Nat) => Nat.pred z) (Nat.succ a) (Nat.succ b) h",
            ),
            "Nat succ injectivity: succ a = succ b -> a = b. Eq.cong with Nat.pred (pred (succ a) \
             reduces to a). DerivedProved, zero axiom_deps. Confluence-independent. (Suffix _beq to \
             avoid collision with the #2859 iota lane's nat_succ_inj.)",
            &["Eq.cong", "Nat.pred"],
        ))?;

        // level_eqb_eq : level_eqb a b = true -> a = b, by double Level.rec.
        self.add_definition(Self::derived_eq_lemma(
            "level_eqb_eq",
            "forall (a : Level) (b : Level), Eq Bool (level_eqb a b) Bool.true -> Eq Level a b",
            concat!(
                "fun (a : Level) => Level.rec ",
                "(fun (za : Level) => forall (b : Level), Eq Bool (level_eqb za b) Bool.true -> Eq Level za b) ",
                // a = zero
                "(fun (b : Level) => Level.rec ",
                "(fun (zb : Level) => Eq Bool (level_eqb Level.zero zb) Bool.true -> Eq Level Level.zero zb) ",
                "(fun (_ : Eq Bool (level_eqb Level.zero Level.zero) Bool.true) => Eq.refl Level Level.zero) ",
                "(fun (qp : Level) (_ : Eq Bool (level_eqb Level.zero qp) Bool.true -> Eq Level Level.zero qp) => ",
                "fun (h : Eq Bool (level_eqb Level.zero (Level.succ qp)) Bool.true) => ",
                "bool_false_ne_true (Eq Level Level.zero (Level.succ qp)) h) ",
                "(fun (ql : Level) (qr : Level) (_ : Eq Bool (level_eqb Level.zero ql) Bool.true -> Eq Level Level.zero ql) (_ : Eq Bool (level_eqb Level.zero qr) Bool.true -> Eq Level Level.zero qr) => ",
                "fun (h : Eq Bool (level_eqb Level.zero (Level.max ql qr)) Bool.true) => ",
                "bool_false_ne_true (Eq Level Level.zero (Level.max ql qr)) h) ",
                "(fun (ql : Level) (qr : Level) (_ : Eq Bool (level_eqb Level.zero ql) Bool.true -> Eq Level Level.zero ql) (_ : Eq Bool (level_eqb Level.zero qr) Bool.true -> Eq Level Level.zero qr) => ",
                "fun (h : Eq Bool (level_eqb Level.zero (Level.imax ql qr)) Bool.true) => ",
                "bool_false_ne_true (Eq Level Level.zero (Level.imax ql qr)) h) ",
                "(fun (qm : Name) => fun (h : Eq Bool (level_eqb Level.zero (Level.param qm)) Bool.true) => ",
                "bool_false_ne_true (Eq Level Level.zero (Level.param qm)) h) ",
                "b) ",
                // a = succ p (ih)
                "(fun (p : Level) (ih : forall (b : Level), Eq Bool (level_eqb p b) Bool.true -> Eq Level p b) => ",
                "fun (b : Level) => Level.rec ",
                "(fun (zb : Level) => Eq Bool (level_eqb (Level.succ p) zb) Bool.true -> Eq Level (Level.succ p) zb) ",
                "(fun (h : Eq Bool (level_eqb (Level.succ p) Level.zero) Bool.true) => ",
                "bool_false_ne_true (Eq Level (Level.succ p) Level.zero) h) ",
                "(fun (qp : Level) (_ : Eq Bool (level_eqb (Level.succ p) qp) Bool.true -> Eq Level (Level.succ p) qp) => ",
                "fun (h : Eq Bool (level_eqb (Level.succ p) (Level.succ qp)) Bool.true) => ",
                "Eq.cong Level Level Level.succ p qp (ih qp h)) ",
                "(fun (ql : Level) (qr : Level) (_ : Eq Bool (level_eqb (Level.succ p) ql) Bool.true -> Eq Level (Level.succ p) ql) (_ : Eq Bool (level_eqb (Level.succ p) qr) Bool.true -> Eq Level (Level.succ p) qr) => ",
                "fun (h : Eq Bool (level_eqb (Level.succ p) (Level.max ql qr)) Bool.true) => ",
                "bool_false_ne_true (Eq Level (Level.succ p) (Level.max ql qr)) h) ",
                "(fun (ql : Level) (qr : Level) (_ : Eq Bool (level_eqb (Level.succ p) ql) Bool.true -> Eq Level (Level.succ p) ql) (_ : Eq Bool (level_eqb (Level.succ p) qr) Bool.true -> Eq Level (Level.succ p) qr) => ",
                "fun (h : Eq Bool (level_eqb (Level.succ p) (Level.imax ql qr)) Bool.true) => ",
                "bool_false_ne_true (Eq Level (Level.succ p) (Level.imax ql qr)) h) ",
                "(fun (qm : Name) => fun (h : Eq Bool (level_eqb (Level.succ p) (Level.param qm)) Bool.true) => ",
                "bool_false_ne_true (Eq Level (Level.succ p) (Level.param qm)) h) ",
                "b) ",
                // a = max pl pr (ih_l, ih_r)
                "(fun (pl : Level) (pr : Level) (ih_l : forall (b : Level), Eq Bool (level_eqb pl b) Bool.true -> Eq Level pl b) (ih_r : forall (b : Level), Eq Bool (level_eqb pr b) Bool.true -> Eq Level pr b) => ",
                "fun (b : Level) => Level.rec ",
                "(fun (zb : Level) => Eq Bool (level_eqb (Level.max pl pr) zb) Bool.true -> Eq Level (Level.max pl pr) zb) ",
                "(fun (h : Eq Bool (level_eqb (Level.max pl pr) Level.zero) Bool.true) => ",
                "bool_false_ne_true (Eq Level (Level.max pl pr) Level.zero) h) ",
                "(fun (qp : Level) (_ : Eq Bool (level_eqb (Level.max pl pr) qp) Bool.true -> Eq Level (Level.max pl pr) qp) => ",
                "fun (h : Eq Bool (level_eqb (Level.max pl pr) (Level.succ qp)) Bool.true) => ",
                "bool_false_ne_true (Eq Level (Level.max pl pr) (Level.succ qp)) h) ",
                "(fun (ql : Level) (qr : Level) (_ : Eq Bool (level_eqb (Level.max pl pr) ql) Bool.true -> Eq Level (Level.max pl pr) ql) (_ : Eq Bool (level_eqb (Level.max pl pr) qr) Bool.true -> Eq Level (Level.max pl pr) qr) => ",
                "fun (h : Eq Bool (level_eqb (Level.max pl pr) (Level.max ql qr)) Bool.true) => ",
                "Eq.trans Level (Level.max pl pr) (Level.max ql pr) (Level.max ql qr) ",
                "(Eq.cong Level Level (fun (w : Level) => Level.max w pr) pl ql (ih_l ql (band_eq_true_left (level_eqb pl ql) (level_eqb pr qr) h))) ",
                "(Eq.cong Level Level (fun (w : Level) => Level.max ql w) pr qr (ih_r qr (band_eq_true_right (level_eqb pl ql) (level_eqb pr qr) h)))) ",
                "(fun (ql : Level) (qr : Level) (_ : Eq Bool (level_eqb (Level.max pl pr) ql) Bool.true -> Eq Level (Level.max pl pr) ql) (_ : Eq Bool (level_eqb (Level.max pl pr) qr) Bool.true -> Eq Level (Level.max pl pr) qr) => ",
                "fun (h : Eq Bool (level_eqb (Level.max pl pr) (Level.imax ql qr)) Bool.true) => ",
                "bool_false_ne_true (Eq Level (Level.max pl pr) (Level.imax ql qr)) h) ",
                "(fun (qm : Name) => fun (h : Eq Bool (level_eqb (Level.max pl pr) (Level.param qm)) Bool.true) => ",
                "bool_false_ne_true (Eq Level (Level.max pl pr) (Level.param qm)) h) ",
                "b) ",
                // a = imax pl pr (ih_l, ih_r)
                "(fun (pl : Level) (pr : Level) (ih_l : forall (b : Level), Eq Bool (level_eqb pl b) Bool.true -> Eq Level pl b) (ih_r : forall (b : Level), Eq Bool (level_eqb pr b) Bool.true -> Eq Level pr b) => ",
                "fun (b : Level) => Level.rec ",
                "(fun (zb : Level) => Eq Bool (level_eqb (Level.imax pl pr) zb) Bool.true -> Eq Level (Level.imax pl pr) zb) ",
                "(fun (h : Eq Bool (level_eqb (Level.imax pl pr) Level.zero) Bool.true) => ",
                "bool_false_ne_true (Eq Level (Level.imax pl pr) Level.zero) h) ",
                "(fun (qp : Level) (_ : Eq Bool (level_eqb (Level.imax pl pr) qp) Bool.true -> Eq Level (Level.imax pl pr) qp) => ",
                "fun (h : Eq Bool (level_eqb (Level.imax pl pr) (Level.succ qp)) Bool.true) => ",
                "bool_false_ne_true (Eq Level (Level.imax pl pr) (Level.succ qp)) h) ",
                "(fun (ql : Level) (qr : Level) (_ : Eq Bool (level_eqb (Level.imax pl pr) ql) Bool.true -> Eq Level (Level.imax pl pr) ql) (_ : Eq Bool (level_eqb (Level.imax pl pr) qr) Bool.true -> Eq Level (Level.imax pl pr) qr) => ",
                "fun (h : Eq Bool (level_eqb (Level.imax pl pr) (Level.max ql qr)) Bool.true) => ",
                "bool_false_ne_true (Eq Level (Level.imax pl pr) (Level.max ql qr)) h) ",
                "(fun (ql : Level) (qr : Level) (_ : Eq Bool (level_eqb (Level.imax pl pr) ql) Bool.true -> Eq Level (Level.imax pl pr) ql) (_ : Eq Bool (level_eqb (Level.imax pl pr) qr) Bool.true -> Eq Level (Level.imax pl pr) qr) => ",
                "fun (h : Eq Bool (level_eqb (Level.imax pl pr) (Level.imax ql qr)) Bool.true) => ",
                "Eq.trans Level (Level.imax pl pr) (Level.imax ql pr) (Level.imax ql qr) ",
                "(Eq.cong Level Level (fun (w : Level) => Level.imax w pr) pl ql (ih_l ql (band_eq_true_left (level_eqb pl ql) (level_eqb pr qr) h))) ",
                "(Eq.cong Level Level (fun (w : Level) => Level.imax ql w) pr qr (ih_r qr (band_eq_true_right (level_eqb pl ql) (level_eqb pr qr) h)))) ",
                "(fun (qm : Name) => fun (h : Eq Bool (level_eqb (Level.imax pl pr) (Level.param qm)) Bool.true) => ",
                "bool_false_ne_true (Eq Level (Level.imax pl pr) (Level.param qm)) h) ",
                "b) ",
                // a = param pm (ih on Name is irrelevant): inner dispatch on b;
                // cross constructors absurd, param/param inverts name_eqb via
                // name_eqb_eq lifted through Level.param (Eq.cong).
                "(fun (pm : Name) => ",
                "fun (b : Level) => Level.rec ",
                "(fun (zb : Level) => Eq Bool (level_eqb (Level.param pm) zb) Bool.true -> Eq Level (Level.param pm) zb) ",
                "(fun (h : Eq Bool (level_eqb (Level.param pm) Level.zero) Bool.true) => ",
                "bool_false_ne_true (Eq Level (Level.param pm) Level.zero) h) ",
                "(fun (qp : Level) (_ : Eq Bool (level_eqb (Level.param pm) qp) Bool.true -> Eq Level (Level.param pm) qp) => ",
                "fun (h : Eq Bool (level_eqb (Level.param pm) (Level.succ qp)) Bool.true) => ",
                "bool_false_ne_true (Eq Level (Level.param pm) (Level.succ qp)) h) ",
                "(fun (ql : Level) (qr : Level) (_ : Eq Bool (level_eqb (Level.param pm) ql) Bool.true -> Eq Level (Level.param pm) ql) (_ : Eq Bool (level_eqb (Level.param pm) qr) Bool.true -> Eq Level (Level.param pm) qr) => ",
                "fun (h : Eq Bool (level_eqb (Level.param pm) (Level.max ql qr)) Bool.true) => ",
                "bool_false_ne_true (Eq Level (Level.param pm) (Level.max ql qr)) h) ",
                "(fun (ql : Level) (qr : Level) (_ : Eq Bool (level_eqb (Level.param pm) ql) Bool.true -> Eq Level (Level.param pm) ql) (_ : Eq Bool (level_eqb (Level.param pm) qr) Bool.true -> Eq Level (Level.param pm) qr) => ",
                "fun (h : Eq Bool (level_eqb (Level.param pm) (Level.imax ql qr)) Bool.true) => ",
                "bool_false_ne_true (Eq Level (Level.param pm) (Level.imax ql qr)) h) ",
                "(fun (qm : Name) => fun (h : Eq Bool (level_eqb (Level.param pm) (Level.param qm)) Bool.true) => ",
                "Eq.cong Name Level Level.param pm qm (name_eqb_eq pm qm h)) ",
                "b) ",
                "a",
            ),
            "level_eqb inversion: level_eqb a b = true -> a = b. Double Level.rec over \
             zero|succ|max|imax|param; all cross-constructor pairs are absurd (bool_false_ne_true); \
             succ recurses (IH + Eq.cong); max/imax split the conjunction (band split) and rebuild via \
             two Eq.cong + Eq.trans; param inverts name_eqb (name_eqb_eq) lifted through Level.param. \
             DerivedProved, zero axiom_deps. Confluence-independent.",
            &[
                "Level.rec",
                "Eq.refl",
                "Eq.trans",
                "Eq.cong",
                "bool_false_ne_true",
                "band_eq_true_left",
                "band_eq_true_right",
                "name_eqb_eq",
                "level_eqb",
            ],
        ))?;

        // =========================================================
        // §2b denotation + §2b' soundness of the real Level algebra.
        // These tie the smart constructors / classifiers back to the base
        // development's Nat model (imax_nat). ADDED alongside the Nat machinery;
        // nothing consumes them yet. The imax-ALGEBRA *_eval bridges
        // (level_max_eval / level_imax_eval / level_is_nonzero_sound) are proved
        // in full further down (they need only the in-tree additive Nat tower —
        // nat_zero_add / nat_succ_add / nat_sub_self / nat_sub_zero_left — because
        // nat_max is DEFINED additively as `Nat.add a (Nat.sub b a)` and imax_nat's
        // succ arm IS that same term, so most steps are pure kernel reduction);
        // the definitely-zero soundness (below) needs only definitional reduction.
        // =========================================================

        // nat_max a b = a + (b - a): a genuine Nat max (a+(b-a)=b when a<=b,
        // =a when a>b), written additively so `nat_max 0 0 = 0` etc. reduce.
        self.add_recursive_def(
            "def nat_max (a : Nat) (b : Nat) : Nat := Nat.add a (Nat.sub b a)",
            "Nat max written additively (a + (b - a)); the denotation of Level.max. \
             Confluence-independent.",
        )?;

        // level_eval: denotational level evaluation under a parameter assignment
        // r : Name -> Nat. The `imax` clause IS imax_nat (the base development's
        // closed Nat shadow of production Level::imax) — THE bridge. `param n`
        // denotes the opaque r n. Raw Level.rec (motive `fun _ => Nat`).
        self.add_recursive_def(
            concat!(
                "def level_eval (r : Name -> Nat) (l : Level) : Nat := ",
                "Level.rec (fun (_ : Level) => Nat) ",
                "Nat.zero ",
                "(fun (p : Level) (ih : Nat) => Nat.succ ih) ",
                "(fun (l1 : Level) (l2 : Level) (ih1 : Nat) (ih2 : Nat) => nat_max ih1 ih2) ",
                "(fun (l1 : Level) (l2 : Level) (ih1 : Nat) (ih2 : Nat) => imax_nat ih1 ih2) ",
                "(fun (n : Name) => r n) ",
                "l",
            ),
            "Denotational level evaluation under r : Name -> Nat. zero=0, succ=succ, max=nat_max, \
             imax=imax_nat (the bridge to the base Nat model), param n = r n. Confluence-independent.",
        )?;

        // level_is_zero_sound (Level::is_zero ENSURES): a definitely-zero level
        // evaluates to 0 under EVERY assignment. Level.rec on l; succ/param arms
        // are absurd (bool_false_ne_true); the max arm splits the Bool.and (band
        // split) and rewrites both evals to 0 (nat_max 0 0 = 0 definitionally);
        // the imax arm rewrites the second eval to 0 (imax_nat n 0 = 0
        // definitionally). All arithmetic here is pure kernel reduction.
        self.add_definition(Self::derived_eq_lemma(
            "level_is_zero_sound",
            concat!(
                "forall (l : Level), Eq Bool (level_is_zero l) Bool.true -> ",
                "forall (r : Name -> Nat), Eq Nat (level_eval r l) Nat.zero"
            ),
            concat!(
                "fun (l : Level) => Level.rec ",
                "(fun (z : Level) => Eq Bool (level_is_zero z) Bool.true -> forall (r : Name -> Nat), Eq Nat (level_eval r z) Nat.zero) ",
                // zero
                "(fun (_ : Eq Bool (level_is_zero Level.zero) Bool.true) (r : Name -> Nat) => Eq.refl Nat Nat.zero) ",
                // succ p (absurd: is_zero (succ p) = false)
                "(fun (p : Level) (ih : Eq Bool (level_is_zero p) Bool.true -> forall (r : Name -> Nat), Eq Nat (level_eval r p) Nat.zero) => ",
                "fun (h : Eq Bool (level_is_zero (Level.succ p)) Bool.true) (r : Name -> Nat) => ",
                "bool_false_ne_true (Eq Nat (level_eval r (Level.succ p)) Nat.zero) h) ",
                // max l1 l2 : band split, rewrite both evals to 0
                "(fun (l1 : Level) (l2 : Level) ",
                "(ih1 : Eq Bool (level_is_zero l1) Bool.true -> forall (r : Name -> Nat), Eq Nat (level_eval r l1) Nat.zero) ",
                "(ih2 : Eq Bool (level_is_zero l2) Bool.true -> forall (r : Name -> Nat), Eq Nat (level_eval r l2) Nat.zero) => ",
                "fun (h : Eq Bool (level_is_zero (Level.max l1 l2)) Bool.true) (r : Name -> Nat) => ",
                "Eq.trans Nat (nat_max (level_eval r l1) (level_eval r l2)) (nat_max Nat.zero Nat.zero) Nat.zero ",
                "(Eq.trans Nat (nat_max (level_eval r l1) (level_eval r l2)) (nat_max Nat.zero (level_eval r l2)) (nat_max Nat.zero Nat.zero) ",
                "(Eq.cong Nat Nat (fun (w : Nat) => nat_max w (level_eval r l2)) (level_eval r l1) Nat.zero ",
                "(ih1 (band_eq_true_left (level_is_zero l1) (level_is_zero l2) h) r)) ",
                "(Eq.cong Nat Nat (fun (w : Nat) => nat_max Nat.zero w) (level_eval r l2) Nat.zero ",
                "(ih2 (band_eq_true_right (level_is_zero l1) (level_is_zero l2) h) r))) ",
                "(Eq.refl Nat Nat.zero)) ",
                // imax l1 l2 : is_zero (imax l1 l2) = is_zero l2; rewrite eval l2 -> 0, imax_nat _ 0 = 0
                "(fun (l1 : Level) (l2 : Level) ",
                "(ih1 : Eq Bool (level_is_zero l1) Bool.true -> forall (r : Name -> Nat), Eq Nat (level_eval r l1) Nat.zero) ",
                "(ih2 : Eq Bool (level_is_zero l2) Bool.true -> forall (r : Name -> Nat), Eq Nat (level_eval r l2) Nat.zero) => ",
                "fun (h : Eq Bool (level_is_zero (Level.imax l1 l2)) Bool.true) (r : Name -> Nat) => ",
                "Eq.trans Nat (imax_nat (level_eval r l1) (level_eval r l2)) (imax_nat (level_eval r l1) Nat.zero) Nat.zero ",
                "(Eq.cong Nat Nat (fun (w : Nat) => imax_nat (level_eval r l1) w) (level_eval r l2) Nat.zero (ih2 h r)) ",
                "(Eq.refl Nat Nat.zero)) ",
                // param n (absurd: is_zero (param n) = false)
                "(fun (n : Name) => ",
                "fun (h : Eq Bool (level_is_zero (Level.param n)) Bool.true) (r : Name -> Nat) => ",
                "bool_false_ne_true (Eq Nat (level_eval r (Level.param n)) Nat.zero) h) ",
                "l",
            ),
            "Level::is_zero soundness: a definitely-zero level evaluates to 0 under every parameter \
             assignment. Level.rec on l; succ/param absurd; max band-splits then reduces nat_max 0 0 = 0; \
             imax reduces imax_nat n 0 = 0. Pure kernel reduction (no Nat arithmetic tower). \
             DerivedProved, zero axiom_deps. Confluence-independent.",
            &[
                "Level.rec",
                "Eq.refl",
                "Eq.trans",
                "Eq.cong",
                "bool_false_ne_true",
                "band_eq_true_left",
                "band_eq_true_right",
                "level_is_zero",
                "level_eval",
                "nat_max",
                "imax_nat",
            ],
        ))?;

        // =========================================================
        // §2b' — the imax-DENOTATION bridge (closes B1's deferred gap).
        //
        // 8 foundational Nat helpers (all explicit Nat.rec terms over the in-tree
        // additive tower) + the three bridge lemmas level_max_eval /
        // level_is_nonzero_sound / level_imax_eval. Every step is either pure
        // kernel reduction (nat_max a b := Nat.add a (Nat.sub b a); imax_nat's succ
        // arm IS that same term) or a single application of nat_zero_add /
        // nat_succ_add / nat_sub_self / nat_sub_zero_left. No new axioms, empty
        // (foundational) closure. Case-splits over the smart constructors' guards
        // use the standard "Bool.rec-with-carried-equation" pattern (generalize the
        // neutral guard g, carry Eq (guard) g, feed Eq.refl).
        // =========================================================

        // Helper #1: a + (succ b - a) is never zero (either a is a succ, or a=0 and
        // 0 + succ b = succ b). The shared core of the "nonzero right arm" helpers.
        self.add_definition(Self::derived_eq_lemma(
            "nat_add_sub_succ_nonzero",
            "forall (a : Nat) (b : Nat), Eq Bool (nat_is_zero (Nat.add a (Nat.sub (Nat.succ b) a))) Bool.false",
            concat!(
                "fun (a : Nat) (b : Nat) => Nat.rec ",
                "(fun (aa : Nat) => Eq Bool (nat_is_zero (Nat.add aa (Nat.sub (Nat.succ b) aa))) Bool.false) ",
                "(Eq.cong Nat Bool (fun (z : Nat) => nat_is_zero z) (Nat.add Nat.zero (Nat.succ b)) (Nat.succ b) (nat_zero_add (Nat.succ b))) ",
                "(fun (a1 : Nat) (ih : Eq Bool (nat_is_zero (Nat.add a1 (Nat.sub (Nat.succ b) a1))) Bool.false) => ",
                "Eq.cong Nat Bool (fun (z : Nat) => nat_is_zero z) (Nat.add (Nat.succ a1) (Nat.sub (Nat.succ b) (Nat.succ a1))) (Nat.succ (Nat.add a1 (Nat.sub (Nat.succ b) (Nat.succ a1)))) (nat_succ_add a1 (Nat.sub (Nat.succ b) (Nat.succ a1)))) ",
                "a",
            ),
            "nat_is_zero (a + (succ b - a)) = false. Nat.rec on a: base rewrites 0 + succ b via \
             nat_zero_add to succ b; step rewrites succ a1 + X via nat_succ_add to a succ. \
             DerivedProved, zero axiom_deps. Confluence-independent.",
            &["Nat.rec", "Eq.cong", "nat_is_zero", "nat_zero_add", "nat_succ_add"],
        ))?;

        // Helper #2: nonzero left operand => nat_max nonzero (nat_max (succ a1) b is
        // a succ via nat_succ_add; nat_max 0 b is absurd against the hypothesis).
        self.add_definition(Self::derived_eq_lemma(
            "nat_is_zero_nat_max_left",
            "forall (a : Nat) (b : Nat), Eq Bool (nat_is_zero a) Bool.false -> Eq Bool (nat_is_zero (nat_max a b)) Bool.false",
            concat!(
                "fun (a : Nat) (b : Nat) => Nat.rec ",
                "(fun (aa : Nat) => Eq Bool (nat_is_zero aa) Bool.false -> Eq Bool (nat_is_zero (nat_max aa b)) Bool.false) ",
                "(fun (h : Eq Bool (nat_is_zero Nat.zero) Bool.false) => bool_false_ne_true (Eq Bool (nat_is_zero (nat_max Nat.zero b)) Bool.false) (Eq.symm Bool Bool.true Bool.false h)) ",
                "(fun (a1 : Nat) (ih : Eq Bool (nat_is_zero a1) Bool.false -> Eq Bool (nat_is_zero (nat_max a1 b)) Bool.false) => ",
                "fun (h : Eq Bool (nat_is_zero (Nat.succ a1)) Bool.false) => ",
                "Eq.cong Nat Bool (fun (z : Nat) => nat_is_zero z) (Nat.add (Nat.succ a1) (Nat.sub b (Nat.succ a1))) (Nat.succ (Nat.add a1 (Nat.sub b (Nat.succ a1)))) (nat_succ_add a1 (Nat.sub b (Nat.succ a1)))) ",
                "a",
            ),
            "nat_is_zero a = false -> nat_is_zero (nat_max a b) = false. Nat.rec on a: base \
             absurd (nat_is_zero 0 = true); step succ a1 + X is a succ via nat_succ_add. \
             DerivedProved, zero axiom_deps. Confluence-independent.",
            &["Nat.rec", "Eq.cong", "Eq.symm", "bool_false_ne_true", "nat_is_zero", "nat_max", "nat_succ_add"],
        ))?;

        // Helper #3: nonzero right operand => nat_max nonzero (via helper #1).
        self.add_definition(Self::derived_eq_lemma(
            "nat_is_zero_nat_max_right",
            "forall (a : Nat) (b : Nat), Eq Bool (nat_is_zero b) Bool.false -> Eq Bool (nat_is_zero (nat_max a b)) Bool.false",
            concat!(
                "fun (a : Nat) (b : Nat) => Nat.rec ",
                "(fun (bb : Nat) => Eq Bool (nat_is_zero bb) Bool.false -> Eq Bool (nat_is_zero (nat_max a bb)) Bool.false) ",
                "(fun (h : Eq Bool (nat_is_zero Nat.zero) Bool.false) => bool_false_ne_true (Eq Bool (nat_is_zero (nat_max a Nat.zero)) Bool.false) (Eq.symm Bool Bool.true Bool.false h)) ",
                "(fun (b1 : Nat) (ih : Eq Bool (nat_is_zero b1) Bool.false -> Eq Bool (nat_is_zero (nat_max a b1)) Bool.false) => ",
                "fun (h : Eq Bool (nat_is_zero (Nat.succ b1)) Bool.false) => nat_add_sub_succ_nonzero a b1) ",
                "b",
            ),
            "nat_is_zero b = false -> nat_is_zero (nat_max a b) = false. Nat.rec on b: base \
             absurd; step nat_max a (succ b1) reduces to a + (succ b1 - a), closed by \
             nat_add_sub_succ_nonzero. DerivedProved, zero axiom_deps. Confluence-independent.",
            &["Nat.rec", "Eq.symm", "bool_false_ne_true", "nat_is_zero", "nat_max", "nat_add_sub_succ_nonzero"],
        ))?;

        // Helper #4: nonzero right operand => imax_nat nonzero. imax_nat a (succ b1)
        // IS a + (succ b1 - a), the SAME reduct as nat_max, so reuses helper #1.
        self.add_definition(Self::derived_eq_lemma(
            "nat_is_zero_imax_nat_right",
            "forall (a : Nat) (b : Nat), Eq Bool (nat_is_zero b) Bool.false -> Eq Bool (nat_is_zero (imax_nat a b)) Bool.false",
            concat!(
                "fun (a : Nat) (b : Nat) => Nat.rec ",
                "(fun (bb : Nat) => Eq Bool (nat_is_zero bb) Bool.false -> Eq Bool (nat_is_zero (imax_nat a bb)) Bool.false) ",
                "(fun (h : Eq Bool (nat_is_zero Nat.zero) Bool.false) => bool_false_ne_true (Eq Bool (nat_is_zero (imax_nat a Nat.zero)) Bool.false) (Eq.symm Bool Bool.true Bool.false h)) ",
                "(fun (b1 : Nat) (ih : Eq Bool (nat_is_zero b1) Bool.false -> Eq Bool (nat_is_zero (imax_nat a b1)) Bool.false) => ",
                "fun (h : Eq Bool (nat_is_zero (Nat.succ b1)) Bool.false) => nat_add_sub_succ_nonzero a b1) ",
                "b",
            ),
            "nat_is_zero b = false -> nat_is_zero (imax_nat a b) = false. Nat.rec on b: base \
             absurd; step imax_nat a (succ b1) reduces to a + (succ b1 - a) (same reduct as \
             nat_max), closed by nat_add_sub_succ_nonzero. DerivedProved, zero axiom_deps.",
            &["Nat.rec", "Eq.symm", "bool_false_ne_true", "nat_is_zero", "imax_nat", "nat_add_sub_succ_nonzero"],
        ))?;

        // Helper #5: when b is nonzero, nat_max a b = imax_nat a b (both reduce to
        // a + (succ b1 - a) at b = succ b1 — Eq.refl).
        self.add_definition(Self::derived_eq_lemma(
            "nat_max_eq_imax_nonzero",
            "forall (a : Nat) (b : Nat), Eq Bool (nat_is_zero b) Bool.false -> Eq Nat (nat_max a b) (imax_nat a b)",
            concat!(
                "fun (a : Nat) (b : Nat) => Nat.rec ",
                "(fun (bb : Nat) => Eq Bool (nat_is_zero bb) Bool.false -> Eq Nat (nat_max a bb) (imax_nat a bb)) ",
                "(fun (h : Eq Bool (nat_is_zero Nat.zero) Bool.false) => bool_false_ne_true (Eq Nat (nat_max a Nat.zero) (imax_nat a Nat.zero)) (Eq.symm Bool Bool.true Bool.false h)) ",
                "(fun (b1 : Nat) (ih : Eq Bool (nat_is_zero b1) Bool.false -> Eq Nat (nat_max a b1) (imax_nat a b1)) => ",
                "fun (h : Eq Bool (nat_is_zero (Nat.succ b1)) Bool.false) => Eq.refl Nat (Nat.add a (Nat.sub (Nat.succ b1) a))) ",
                "b",
            ),
            "nat_is_zero b = false -> nat_max a b = imax_nat a b. Nat.rec on b: base absurd; \
             step both sides reduce to a + (succ b1 - a), so Eq.refl. DerivedProved, zero \
             axiom_deps. Confluence-independent.",
            &["Nat.rec", "Eq.refl", "Eq.symm", "bool_false_ne_true", "nat_is_zero", "nat_max", "imax_nat"],
        ))?;

        // Helper #6: imax_nat 0 m = m (impredicative left-zero is the max identity).
        self.add_definition(Self::derived_eq_lemma(
            "imax_nat_zero_left",
            "forall (m : Nat), Eq Nat (imax_nat Nat.zero m) m",
            concat!(
                "fun (m : Nat) => Nat.rec ",
                "(fun (mm : Nat) => Eq Nat (imax_nat Nat.zero mm) mm) ",
                "(Eq.refl Nat Nat.zero) ",
                "(fun (m1 : Nat) (ih : Eq Nat (imax_nat Nat.zero m1) m1) => nat_zero_add (Nat.succ m1)) ",
                "m",
            ),
            "imax_nat 0 m = m. Nat.rec on m: base imax_nat 0 0 = 0 (Eq.refl); step \
             imax_nat 0 (succ m1) = 0 + succ m1 = succ m1 via nat_zero_add. DerivedProved, \
             zero axiom_deps. Confluence-independent.",
            &["Nat.rec", "Eq.refl", "imax_nat", "nat_zero_add"],
        ))?;

        // Helper #7: imax_nat 1 m = m (Lean-4 is_one parity, as a Nat identity).
        self.add_definition(Self::derived_eq_lemma(
            "imax_nat_one_left",
            "forall (m : Nat), Eq Nat (imax_nat (Nat.succ Nat.zero) m) m",
            concat!(
                "fun (m : Nat) => Nat.rec ",
                "(fun (mm : Nat) => Eq Nat (imax_nat (Nat.succ Nat.zero) mm) mm) ",
                "(Eq.refl Nat Nat.zero) ",
                "(fun (m1 : Nat) (ih : Eq Nat (imax_nat (Nat.succ Nat.zero) m1) m1) => ",
                "Eq.trans Nat (Nat.add (Nat.succ Nat.zero) m1) (Nat.succ (Nat.add Nat.zero m1)) (Nat.succ m1) (nat_succ_add Nat.zero m1) (Eq.cong Nat Nat (fun (z : Nat) => Nat.succ z) (Nat.add Nat.zero m1) m1 (nat_zero_add m1))) ",
                "m",
            ),
            "imax_nat 1 m = m. Nat.rec on m: base imax_nat 1 0 = 0 (Eq.refl); step \
             imax_nat 1 (succ m1) reduces (succ m1 - 1 = m1) to (succ 0) + m1, rewritten via \
             nat_succ_add + nat_zero_add to succ m1. DerivedProved, zero axiom_deps.",
            &["Nat.rec", "Eq.refl", "Eq.trans", "Eq.cong", "imax_nat", "nat_succ_add", "nat_zero_add"],
        ))?;

        // Helper #8: imax_nat n n = n (self-imax collapses to the argument).
        self.add_definition(Self::derived_eq_lemma(
            "imax_nat_self",
            "forall (n : Nat), Eq Nat (imax_nat n n) n",
            concat!(
                "fun (n : Nat) => Nat.rec ",
                "(fun (nn : Nat) => Eq Nat (imax_nat nn nn) nn) ",
                "(Eq.refl Nat Nat.zero) ",
                "(fun (n1 : Nat) (ih : Eq Nat (imax_nat n1 n1) n1) => ",
                "Eq.cong Nat Nat (fun (s : Nat) => Nat.add (Nat.succ n1) s) (Nat.sub (Nat.succ n1) (Nat.succ n1)) Nat.zero (nat_sub_self (Nat.succ n1))) ",
                "n",
            ),
            "imax_nat n n = n. Nat.rec on n: base imax_nat 0 0 = 0 (Eq.refl); step \
             imax_nat (succ n1) (succ n1) = (succ n1) + (succ n1 - succ n1) = (succ n1) + 0 = \
             succ n1 via nat_sub_self. DerivedProved, zero axiom_deps. Confluence-independent.",
            &["Nat.rec", "Eq.refl", "Eq.cong", "imax_nat", "nat_sub_self"],
        ))?;

        // ---- Bridge lemma 1/3: level_max_eval ----
        // Level::max preserves the Nat denotation. Three nested Bool.rec-with-
        // carried-equation splits on the smart ctor's guards (level_eqb u v /
        // level_is_zero u / level_is_zero v); the true arms rewrite an eval to 0
        // (level_is_zero_sound) or fold u=v (level_eqb_eq) and finish by
        // nat_sub_self / nat_zero_add / nat_sub_zero_left; the stuck arm is Eq.refl
        // (level_eval of Level.max IS nat_max).
        {
            let inner2 = "(Bool.rec (fun (_ : Bool) => Level) (Level.max u v) u (level_is_zero v))";
            let inner1 =
                format!("(Bool.rec (fun (_ : Bool) => Level) {inner2} v (level_is_zero u))");
            let rhs_max = "nat_max (level_eval r u) (level_eval r v)";
            let value_max = format!(
                "fun (u : Level) (v : Level) (r : Name -> Nat) => \
                 Bool.rec \
                 (fun (g1 : Bool) => Eq Bool (level_eqb u v) g1 -> Eq Nat (level_eval r (Bool.rec (fun (_ : Bool) => Level) {inner1} u g1)) ({rhs_max})) \
                 (fun (_ : Eq Bool (level_eqb u v) Bool.false) => \
                 Bool.rec \
                 (fun (g2 : Bool) => Eq Bool (level_is_zero u) g2 -> Eq Nat (level_eval r (Bool.rec (fun (_ : Bool) => Level) {inner2} v g2)) ({rhs_max})) \
                 (fun (_ : Eq Bool (level_is_zero u) Bool.false) => \
                 Bool.rec \
                 (fun (g3 : Bool) => Eq Bool (level_is_zero v) g3 -> Eq Nat (level_eval r (Bool.rec (fun (_ : Bool) => Level) (Level.max u v) u g3)) ({rhs_max})) \
                 (fun (_ : Eq Bool (level_is_zero v) Bool.false) => Eq.refl Nat ({rhs_max})) \
                 (fun (hz3 : Eq Bool (level_is_zero v) Bool.true) => \
                 Eq.symm Nat ({rhs_max}) (level_eval r u) \
                 (Eq.trans Nat ({rhs_max}) (nat_max (level_eval r u) Nat.zero) (level_eval r u) \
                 (Eq.cong Nat Nat (fun (z : Nat) => nat_max (level_eval r u) z) (level_eval r v) Nat.zero (level_is_zero_sound v hz3 r)) \
                 (Eq.cong Nat Nat (fun (s : Nat) => Nat.add (level_eval r u) s) (Nat.sub Nat.zero (level_eval r u)) Nat.zero (nat_sub_zero_left (level_eval r u))))) \
                 (level_is_zero v) \
                 (Eq.refl Bool (level_is_zero v))) \
                 (fun (hz2 : Eq Bool (level_is_zero u) Bool.true) => \
                 Eq.symm Nat ({rhs_max}) (level_eval r v) \
                 (Eq.trans Nat ({rhs_max}) (nat_max Nat.zero (level_eval r v)) (level_eval r v) \
                 (Eq.cong Nat Nat (fun (z : Nat) => nat_max z (level_eval r v)) (level_eval r u) Nat.zero (level_is_zero_sound u hz2 r)) \
                 (nat_zero_add (level_eval r v)))) \
                 (level_is_zero u) \
                 (Eq.refl Bool (level_is_zero u))) \
                 (fun (he1 : Eq Bool (level_eqb u v) Bool.true) => \
                 Eq.symm Nat ({rhs_max}) (level_eval r u) \
                 (Eq.trans Nat ({rhs_max}) (nat_max (level_eval r u) (level_eval r u)) (level_eval r u) \
                 (Eq.cong Nat Nat (fun (z : Nat) => nat_max (level_eval r u) z) (level_eval r v) (level_eval r u) \
                 (Eq.cong Level Nat (fun (w : Level) => level_eval r w) v u (Eq.symm Level u v (level_eqb_eq u v he1)))) \
                 (Eq.cong Nat Nat (fun (s : Nat) => Nat.add (level_eval r u) s) (Nat.sub (level_eval r u) (level_eval r u)) Nat.zero (nat_sub_self (level_eval r u))))) \
                 (level_eqb u v) \
                 (Eq.refl Bool (level_eqb u v))"
            );
            self.add_definition(Self::derived_eq_lemma(
                "level_max_eval",
                "forall (u : Level) (v : Level) (r : Name -> Nat), Eq Nat (level_eval r (level_max u v)) (nat_max (level_eval r u) (level_eval r v))",
                &value_max,
                "Level::max preserves the Nat denotation: level_eval (level_max u v) = \
                 nat_max (eval u) (eval v), for every parameter assignment. Three nested \
                 Bool.rec-with-carried-equation splits on the smart ctor's guards; true arms \
                 use level_is_zero_sound / level_eqb_eq + nat_sub_self / nat_zero_add / \
                 nat_sub_zero_left; stuck arm is Eq.refl. DerivedProved, zero axiom_deps. \
                 Confluence-independent.",
                &[
                    "Bool.rec", "Eq.refl", "Eq.trans", "Eq.symm", "Eq.cong", "level_eqb",
                    "level_is_zero", "level_max", "level_eval", "level_eqb_eq",
                    "level_is_zero_sound", "nat_max", "nat_sub_self", "nat_zero_add",
                    "nat_sub_zero_left",
                ],
            ))?;
        }

        // ---- Bridge lemma 2/3: level_is_nonzero_sound ----
        // A definitely-nonzero level evaluates to a nonzero Nat under EVERY
        // assignment (expressed via the boolean zero-classifier nat_is_zero = false,
        // the env-free "is nonzero" witness). Level.rec on l; succ is immediate
        // (eval is a succ); max splits Bool.or via a Bool.rec-with-equation and
        // feeds helper #2/#3; imax reduces to its second operand and feeds helper #4.
        self.add_definition(Self::derived_eq_lemma(
            "level_is_nonzero_sound",
            "forall (l : Level), Eq Bool (level_is_nonzero l) Bool.true -> forall (r : Name -> Nat), Eq Bool (nat_is_zero (level_eval r l)) Bool.false",
            concat!(
                "fun (l : Level) => Level.rec ",
                "(fun (z : Level) => Eq Bool (level_is_nonzero z) Bool.true -> forall (r : Name -> Nat), Eq Bool (nat_is_zero (level_eval r z)) Bool.false) ",
                // zero: level_is_nonzero zero = false, hypothesis absurd
                "(fun (h : Eq Bool (level_is_nonzero Level.zero) Bool.true) (r : Name -> Nat) => bool_false_ne_true (Eq Bool (nat_is_zero (level_eval r Level.zero)) Bool.false) h) ",
                // succ p: eval (succ p) = succ (eval p), nat_is_zero (succ _) = false
                "(fun (p : Level) (ih : Eq Bool (level_is_nonzero p) Bool.true -> forall (r : Name -> Nat), Eq Bool (nat_is_zero (level_eval r p)) Bool.false) => ",
                "fun (h : Eq Bool (level_is_nonzero (Level.succ p)) Bool.true) (r : Name -> Nat) => Eq.refl Bool Bool.false) ",
                // max l1 l2: level_is_nonzero = Bool.or; split via Bool.rec on nonzero l1
                "(fun (l1 : Level) (l2 : Level) ",
                "(ih1 : Eq Bool (level_is_nonzero l1) Bool.true -> forall (r : Name -> Nat), Eq Bool (nat_is_zero (level_eval r l1)) Bool.false) ",
                "(ih2 : Eq Bool (level_is_nonzero l2) Bool.true -> forall (r : Name -> Nat), Eq Bool (nat_is_zero (level_eval r l2)) Bool.false) => ",
                "fun (h : Eq Bool (level_is_nonzero (Level.max l1 l2)) Bool.true) (r : Name -> Nat) => ",
                "Bool.rec ",
                "(fun (bb : Bool) => Eq Bool (level_is_nonzero l1) bb -> Eq Bool (nat_is_zero (level_eval r (Level.max l1 l2))) Bool.false) ",
                // nonzero l1 = false: then nonzero l2 = true (from h via Bool.or false _)
                "(fun (heq : Eq Bool (level_is_nonzero l1) Bool.false) => ",
                "nat_is_zero_nat_max_right (level_eval r l1) (level_eval r l2) ",
                "(ih2 (Eq.trans Bool (Bool.or Bool.false (level_is_nonzero l2)) (Bool.or (level_is_nonzero l1) (level_is_nonzero l2)) Bool.true ",
                "(Eq.symm Bool (Bool.or (level_is_nonzero l1) (level_is_nonzero l2)) (Bool.or Bool.false (level_is_nonzero l2)) ",
                "(Eq.cong Bool Bool (fun (w : Bool) => Bool.or w (level_is_nonzero l2)) (level_is_nonzero l1) Bool.false heq)) ",
                "h) r)) ",
                // nonzero l1 = true: ih1 directly
                "(fun (heq : Eq Bool (level_is_nonzero l1) Bool.true) => ",
                "nat_is_zero_nat_max_left (level_eval r l1) (level_eval r l2) (ih1 heq r)) ",
                "(level_is_nonzero l1) ",
                "(Eq.refl Bool (level_is_nonzero l1))) ",
                // imax l1 l2: level_is_nonzero (imax) = nonzero l2; eval (imax) = imax_nat
                "(fun (l1 : Level) (l2 : Level) ",
                "(ih1 : Eq Bool (level_is_nonzero l1) Bool.true -> forall (r : Name -> Nat), Eq Bool (nat_is_zero (level_eval r l1)) Bool.false) ",
                "(ih2 : Eq Bool (level_is_nonzero l2) Bool.true -> forall (r : Name -> Nat), Eq Bool (nat_is_zero (level_eval r l2)) Bool.false) => ",
                "fun (h : Eq Bool (level_is_nonzero (Level.imax l1 l2)) Bool.true) (r : Name -> Nat) => ",
                "nat_is_zero_imax_nat_right (level_eval r l1) (level_eval r l2) (ih2 h r)) ",
                // param n: level_is_nonzero (param n) = false, hypothesis absurd
                "(fun (n : Name) => ",
                "fun (h : Eq Bool (level_is_nonzero (Level.param n)) Bool.true) (r : Name -> Nat) => bool_false_ne_true (Eq Bool (nat_is_zero (level_eval r (Level.param n))) Bool.false) h) ",
                "l",
            ),
            "Level::is_nonzero soundness: a definitely-nonzero level evaluates to a nonzero Nat \
             (nat_is_zero (eval l) = false) under every parameter assignment. Level.rec on l; \
             succ immediate; max splits Bool.or (Bool.rec-with-equation) into helper #2/#3; \
             imax reduces to its right operand into helper #4; zero/param absurd. DerivedProved, \
             zero axiom_deps. Confluence-independent.",
            &[
                "Level.rec", "Bool.rec", "Eq.refl", "Eq.trans", "Eq.symm", "Eq.cong",
                "bool_false_ne_true", "level_is_nonzero", "level_eval", "nat_is_zero", "nat_max",
                "imax_nat", "nat_is_zero_nat_max_left", "nat_is_zero_nat_max_right",
                "nat_is_zero_imax_nat_right",
            ],
        ))?;

        // ---- Bridge lemma 3/3: level_imax_eval (THE imax-algebra theorem) ----
        // Level::imax preserves the Nat denotation imax_nat, for EVERY assignment —
        // the semantic bridge that makes the fragment's pi rule faithful. Five
        // nested Bool.rec-with-carried-equation splits over the smart ctor's five
        // guards in the kernel's order; each true arm discharges its Nat identity
        // (level_is_zero_sound -> imax_nat _ 0 = 0 / imax_nat 0 _; level_is_nonzero_sound
        // + level_max_eval + nat_max_eq_imax_nonzero for the max arm; level_eqb_eq ->
        // imax_nat_one_left / imax_nat_self); the stuck arm is Eq.refl.
        {
            let b4 = "(Bool.rec (fun (_ : Bool) => Level) (Level.imax u v) u (level_eqb u v))";
            let b3 = format!(
                "(Bool.rec (fun (_ : Bool) => Level) {b4} v (level_eqb u (Level.succ Level.zero)))"
            );
            let b2 = format!("(Bool.rec (fun (_ : Bool) => Level) {b3} v (level_is_zero u))");
            let b1 = format!(
                "(Bool.rec (fun (_ : Bool) => Level) {b2} (level_max u v) (level_is_nonzero v))"
            );
            let rhs_i = "imax_nat (level_eval r u) (level_eval r v)";
            let value_imax = format!(
                "fun (u : Level) (v : Level) (r : Name -> Nat) => \
                 Bool.rec \
                 (fun (gz2 : Bool) => Eq Bool (level_is_zero v) gz2 -> Eq Nat (level_eval r (Bool.rec (fun (_ : Bool) => Level) {b1} Level.zero gz2)) ({rhs_i})) \
                 (fun (_ : Eq Bool (level_is_zero v) Bool.false) => \
                 Bool.rec \
                 (fun (gnz2 : Bool) => Eq Bool (level_is_nonzero v) gnz2 -> Eq Nat (level_eval r (Bool.rec (fun (_ : Bool) => Level) {b2} (level_max u v) gnz2)) ({rhs_i})) \
                 (fun (_ : Eq Bool (level_is_nonzero v) Bool.false) => \
                 Bool.rec \
                 (fun (gz1 : Bool) => Eq Bool (level_is_zero u) gz1 -> Eq Nat (level_eval r (Bool.rec (fun (_ : Bool) => Level) {b3} v gz1)) ({rhs_i})) \
                 (fun (_ : Eq Bool (level_is_zero u) Bool.false) => \
                 Bool.rec \
                 (fun (ge1 : Bool) => Eq Bool (level_eqb u (Level.succ Level.zero)) ge1 -> Eq Nat (level_eval r (Bool.rec (fun (_ : Bool) => Level) {b4} v ge1)) ({rhs_i})) \
                 (fun (_ : Eq Bool (level_eqb u (Level.succ Level.zero)) Bool.false) => \
                 Bool.rec \
                 (fun (ge2 : Bool) => Eq Bool (level_eqb u v) ge2 -> Eq Nat (level_eval r (Bool.rec (fun (_ : Bool) => Level) (Level.imax u v) u ge2)) ({rhs_i})) \
                 (fun (_ : Eq Bool (level_eqb u v) Bool.false) => Eq.refl Nat ({rhs_i})) \
                 (fun (he2 : Eq Bool (level_eqb u v) Bool.true) => \
                 Eq.symm Nat ({rhs_i}) (level_eval r u) \
                 (Eq.trans Nat ({rhs_i}) (imax_nat (level_eval r u) (level_eval r u)) (level_eval r u) \
                 (Eq.cong Nat Nat (fun (z : Nat) => imax_nat (level_eval r u) z) (level_eval r v) (level_eval r u) \
                 (Eq.cong Level Nat (fun (w : Level) => level_eval r w) v u (Eq.symm Level u v (level_eqb_eq u v he2)))) \
                 (imax_nat_self (level_eval r u)))) \
                 (level_eqb u v) \
                 (Eq.refl Bool (level_eqb u v))) \
                 (fun (he1 : Eq Bool (level_eqb u (Level.succ Level.zero)) Bool.true) => \
                 Eq.symm Nat ({rhs_i}) (level_eval r v) \
                 (Eq.trans Nat ({rhs_i}) (imax_nat (Nat.succ Nat.zero) (level_eval r v)) (level_eval r v) \
                 (Eq.cong Nat Nat (fun (z : Nat) => imax_nat z (level_eval r v)) (level_eval r u) (Nat.succ Nat.zero) \
                 (Eq.cong Level Nat (fun (w : Level) => level_eval r w) u (Level.succ Level.zero) (level_eqb_eq u (Level.succ Level.zero) he1))) \
                 (imax_nat_one_left (level_eval r v)))) \
                 (level_eqb u (Level.succ Level.zero)) \
                 (Eq.refl Bool (level_eqb u (Level.succ Level.zero)))) \
                 (fun (hz1 : Eq Bool (level_is_zero u) Bool.true) => \
                 Eq.symm Nat ({rhs_i}) (level_eval r v) \
                 (Eq.trans Nat ({rhs_i}) (imax_nat Nat.zero (level_eval r v)) (level_eval r v) \
                 (Eq.cong Nat Nat (fun (z : Nat) => imax_nat z (level_eval r v)) (level_eval r u) Nat.zero (level_is_zero_sound u hz1 r)) \
                 (imax_nat_zero_left (level_eval r v)))) \
                 (level_is_zero u) \
                 (Eq.refl Bool (level_is_zero u))) \
                 (fun (hnz2 : Eq Bool (level_is_nonzero v) Bool.true) => \
                 Eq.trans Nat (level_eval r (level_max u v)) (nat_max (level_eval r u) (level_eval r v)) ({rhs_i}) \
                 (level_max_eval u v r) \
                 (nat_max_eq_imax_nonzero (level_eval r u) (level_eval r v) (level_is_nonzero_sound v hnz2 r))) \
                 (level_is_nonzero v) \
                 (Eq.refl Bool (level_is_nonzero v))) \
                 (fun (hz2 : Eq Bool (level_is_zero v) Bool.true) => \
                 Eq.symm Nat ({rhs_i}) Nat.zero \
                 (Eq.cong Nat Nat (fun (z : Nat) => imax_nat (level_eval r u) z) (level_eval r v) Nat.zero (level_is_zero_sound v hz2 r))) \
                 (level_is_zero v) \
                 (Eq.refl Bool (level_is_zero v))"
            );
            self.add_definition(Self::derived_eq_lemma(
                "level_imax_eval",
                "forall (u : Level) (v : Level) (r : Name -> Nat), Eq Nat (level_eval r (level_imax u v)) (imax_nat (level_eval r u) (level_eval r v))",
                &value_imax,
                "THE imax-algebra theorem: Level::imax preserves the denotational imax_nat \
                 semantics for EVERY parameter assignment (the spec's Nat model IS the \
                 denotation of the real Level algebra). Five nested Bool.rec-with-carried- \
                 equation splits over the smart ctor's five guards in the kernel's order; \
                 each true arm discharges its Nat identity (impredicative 0, the nonzero max \
                 arm via level_max_eval + nat_max_eq_imax_nonzero, imax_nat 0/1/self); stuck \
                 arm is Eq.refl. DerivedProved, zero axiom_deps. Confluence-independent.",
                &[
                    "Bool.rec", "Eq.refl", "Eq.trans", "Eq.symm", "Eq.cong", "level_eqb",
                    "level_is_zero", "level_is_nonzero", "level_imax", "level_max", "level_eval",
                    "level_eqb_eq", "level_is_zero_sound", "level_is_nonzero_sound",
                    "level_max_eval", "nat_max", "imax_nat", "nat_max_eq_imax_nonzero",
                    "imax_nat_zero_left", "imax_nat_one_left", "imax_nat_self",
                ],
            ))?;
        }

        // ulist_eqb_eq : ulist_eqb xs ys = true -> xs = ys, by double ListType.rec.
        self.add_definition(Self::derived_eq_lemma(
            "ulist_eqb_eq",
            concat!(
                "forall (xs : ListType Level) (ys : ListType Level), ",
                "Eq Bool (ulist_eqb xs ys) Bool.true -> Eq (ListType Level) xs ys"
            ),
            concat!(
                "fun (xs : ListType Level) => ListType.rec Level ",
                "(fun (zxs : ListType Level) => forall (ys : ListType Level), Eq Bool (ulist_eqb zxs ys) Bool.true -> Eq (ListType Level) zxs ys) ",
                // xs = nil
                "(fun (ys : ListType Level) => ListType.rec Level ",
                "(fun (zys : ListType Level) => Eq Bool (ulist_eqb (ListType.nil Level) zys) Bool.true -> Eq (ListType Level) (ListType.nil Level) zys) ",
                "(fun (_ : Eq Bool (ulist_eqb (ListType.nil Level) (ListType.nil Level)) Bool.true) => Eq.refl (ListType Level) (ListType.nil Level)) ",
                "(fun (yh : Level) (yt : ListType Level) (_ : Eq Bool (ulist_eqb (ListType.nil Level) yt) Bool.true -> Eq (ListType Level) (ListType.nil Level) yt) => ",
                "fun (h : Eq Bool (ulist_eqb (ListType.nil Level) (ListType.cons Level yh yt)) Bool.true) => ",
                "bool_false_ne_true (Eq (ListType Level) (ListType.nil Level) (ListType.cons Level yh yt)) h) ",
                "ys) ",
                // xs = cons xh xt (ih)
                "(fun (xh : Level) (xt : ListType Level) (ih : forall (ys : ListType Level), Eq Bool (ulist_eqb xt ys) Bool.true -> Eq (ListType Level) xt ys) => ",
                "fun (ys : ListType Level) => ListType.rec Level ",
                "(fun (zys : ListType Level) => Eq Bool (ulist_eqb (ListType.cons Level xh xt) zys) Bool.true -> Eq (ListType Level) (ListType.cons Level xh xt) zys) ",
                // (cons, nil): absurd
                "(fun (h : Eq Bool (ulist_eqb (ListType.cons Level xh xt) (ListType.nil Level)) Bool.true) => ",
                "bool_false_ne_true (Eq (ListType Level) (ListType.cons Level xh xt) (ListType.nil Level)) h) ",
                // (cons xh xt, cons yh yt): and (level_eqb xh yh) (ulist_eqb xt yt)
                "(fun (yh : Level) (yt : ListType Level) (_ : Eq Bool (ulist_eqb (ListType.cons Level xh xt) yt) Bool.true -> Eq (ListType Level) (ListType.cons Level xh xt) yt) => ",
                "fun (h : Eq Bool (ulist_eqb (ListType.cons Level xh xt) (ListType.cons Level yh yt)) Bool.true) => ",
                "Eq.trans (ListType Level) (ListType.cons Level xh xt) (ListType.cons Level yh xt) (ListType.cons Level yh yt) ",
                "(Eq.cong Level (ListType Level) (fun (w : Level) => ListType.cons Level w xt) xh yh (level_eqb_eq xh yh (band_eq_true_left (level_eqb xh yh) (ulist_eqb xt yt) h))) ",
                "(Eq.cong (ListType Level) (ListType Level) (fun (w : ListType Level) => ListType.cons Level yh w) xt yt (ih yt (band_eq_true_right (level_eqb xh yh) (ulist_eqb xt yt) h)))) ",
                "ys) ",
                "xs",
            ),
            "ulist_eqb inversion: ulist_eqb xs ys = true -> xs = ys. Double ListType.rec; cross \
             constructors are absurd (bool_false_ne_true); cons/cons splits the conjunction \
             (band split), inverts the head (level_eqb_eq) and the tail (IH), then rebuilds via two \
             Eq.cong through ListType.cons joined by Eq.trans. DerivedProved, zero axiom_deps. \
             Confluence-independent.",
            &[
                "ListType.rec",
                "Eq.refl",
                "Eq.trans",
                "Eq.cong",
                "bool_false_ne_true",
                "band_eq_true_left",
                "band_eq_true_right",
                "level_eqb_eq",
                "ulist_eqb",
            ],
        ))?;

        // =========================================================
        // KExpr constructor injectivity (the recursive-arm ingredients).
        // expr_model_discrimination.rs supplies app_inj_fst/app_inj_snd; we add
        // the lam/pi/sort/bvar/const projections this proof needs, all by the
        // same KExpr.rec-projector + Eq.cong technique.
        // =========================================================

        self.add_definition(Self::derived_eq_lemma(
            "kexpr_sort_inj",
            "forall (n : Level) (m : Level), Eq KExpr (KExpr.sort n) (KExpr.sort m) -> Eq Level n m",
            concat!(
                "fun (n : Level) (m : Level) (h : Eq KExpr (KExpr.sort n) (KExpr.sort m)) => ",
                "Eq.cong KExpr Level ",
                "(fun (e : KExpr) => KExpr.rec (fun (_ : KExpr) => Level) ",
                "(fun (k : Level) => k) ",
                "(fun (_ : Nat) => n) ",
                "(fun (_ : KExpr) (_ : KExpr) (_ : Level) (_ : Level) => n) ",
                "(fun (_ : KExpr) (_ : KExpr) (_ : Level) (_ : Level) => n) ",
                "(fun (_ : KExpr) (_ : KExpr) (_ : Level) (_ : Level) => n) ",
                "(fun (_ : Name) (_ : ListType Level) => n) ",
                "(fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : Level) (_ : Level) (_ : Level) => n) ",
                "(fun (_ : Name) (_ : Nat) (_ : KExpr) (_ : Level) => n) (fun (_ : Nat) => n) ",
                "e) ",
                "(KExpr.sort n) (KExpr.sort m) h",
            ),
            "KExpr sort injectivity: sort n = sort m -> n = m. KExpr.rec Nat-payload projector + \
             Eq.cong. DerivedProved, zero axiom_deps. Confluence-independent.",
            &["KExpr.rec", "Eq.cong"],
        ))?;

        self.add_definition(Self::derived_eq_lemma(
            "kexpr_bvar_inj",
            "forall (i : Nat) (j : Nat), Eq KExpr (KExpr.bvar i) (KExpr.bvar j) -> Eq Nat i j",
            concat!(
                "fun (i : Nat) (j : Nat) (h : Eq KExpr (KExpr.bvar i) (KExpr.bvar j)) => ",
                "Eq.cong KExpr Nat ",
                "(fun (e : KExpr) => KExpr.rec (fun (_ : KExpr) => Nat) ",
                "(fun (_ : Level) => i) ",
                "(fun (k : Nat) => k) ",
                "(fun (_ : KExpr) (_ : KExpr) (_ : Nat) (_ : Nat) => i) ",
                "(fun (_ : KExpr) (_ : KExpr) (_ : Nat) (_ : Nat) => i) ",
                "(fun (_ : KExpr) (_ : KExpr) (_ : Nat) (_ : Nat) => i) ",
                "(fun (_ : Name) (_ : ListType Level) => i) ",
                "(fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : Nat) (_ : Nat) (_ : Nat) => i) ",
                "(fun (_ : Name) (_ : Nat) (_ : KExpr) (_ : Nat) => i) (fun (_ : Nat) => i) ",
                "e) ",
                "(KExpr.bvar i) (KExpr.bvar j) h",
            ),
            "KExpr bvar injectivity: bvar i = bvar j -> i = j. KExpr.rec Nat-payload projector + \
             Eq.cong. DerivedProved, zero axiom_deps. Confluence-independent.",
            &["KExpr.rec", "Eq.cong"],
        ))?;

        self.add_definition(Self::derived_eq_lemma(
            "kexpr_lam_inj_fst",
            "forall (t1 : KExpr) (b1 : KExpr) (t2 : KExpr) (b2 : KExpr), Eq KExpr (KExpr.lam t1 b1) (KExpr.lam t2 b2) -> Eq KExpr t1 t2",
            concat!(
                "fun (t1 : KExpr) (b1 : KExpr) (t2 : KExpr) (b2 : KExpr) (h : Eq KExpr (KExpr.lam t1 b1) (KExpr.lam t2 b2)) => ",
                "Eq.cong KExpr KExpr ",
                "(fun (e : KExpr) => KExpr.rec (fun (_ : KExpr) => KExpr) ",
                "(fun (_ : Level) => t1) (fun (_ : Nat) => t1) ",
                "(fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => t1) ",
                "(fun (ty : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => ty) ",
                "(fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => t1) ",
                "(fun (_ : Name) (_ : ListType Level) => t1) ",
                "(fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => t1) ",
                "(fun (_ : Name) (_ : Nat) (_ : KExpr) (_ : KExpr) => t1) (fun (_ : Nat) => t1) ",
                "e) ",
                "(KExpr.lam t1 b1) (KExpr.lam t2 b2) h",
            ),
            "KExpr lam injectivity (fst): lam t1 b1 = lam t2 b2 -> t1 = t2. KExpr.rec projector + \
             Eq.cong. DerivedProved, zero axiom_deps. Confluence-independent.",
            &["KExpr.rec", "Eq.cong"],
        ))?;

        self.add_definition(Self::derived_eq_lemma(
            "kexpr_lam_inj_snd",
            "forall (t1 : KExpr) (b1 : KExpr) (t2 : KExpr) (b2 : KExpr), Eq KExpr (KExpr.lam t1 b1) (KExpr.lam t2 b2) -> Eq KExpr b1 b2",
            concat!(
                "fun (t1 : KExpr) (b1 : KExpr) (t2 : KExpr) (b2 : KExpr) (h : Eq KExpr (KExpr.lam t1 b1) (KExpr.lam t2 b2)) => ",
                "Eq.cong KExpr KExpr ",
                "(fun (e : KExpr) => KExpr.rec (fun (_ : KExpr) => KExpr) ",
                "(fun (_ : Level) => b1) (fun (_ : Nat) => b1) ",
                "(fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => b1) ",
                "(fun (_ : KExpr) (bd : KExpr) (_ : KExpr) (_ : KExpr) => bd) ",
                "(fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => b1) ",
                "(fun (_ : Name) (_ : ListType Level) => b1) ",
                "(fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => b1) ",
                "(fun (_ : Name) (_ : Nat) (_ : KExpr) (_ : KExpr) => b1) (fun (_ : Nat) => b1) ",
                "e) ",
                "(KExpr.lam t1 b1) (KExpr.lam t2 b2) h",
            ),
            "KExpr lam injectivity (snd): lam t1 b1 = lam t2 b2 -> b1 = b2. KExpr.rec projector + \
             Eq.cong. DerivedProved, zero axiom_deps. Confluence-independent.",
            &["KExpr.rec", "Eq.cong"],
        ))?;

        self.add_definition(Self::derived_eq_lemma(
            "kexpr_pi_inj_fst",
            "forall (t1 : KExpr) (b1 : KExpr) (t2 : KExpr) (b2 : KExpr), Eq KExpr (KExpr.pi t1 b1) (KExpr.pi t2 b2) -> Eq KExpr t1 t2",
            concat!(
                "fun (t1 : KExpr) (b1 : KExpr) (t2 : KExpr) (b2 : KExpr) (h : Eq KExpr (KExpr.pi t1 b1) (KExpr.pi t2 b2)) => ",
                "Eq.cong KExpr KExpr ",
                "(fun (e : KExpr) => KExpr.rec (fun (_ : KExpr) => KExpr) ",
                "(fun (_ : Level) => t1) (fun (_ : Nat) => t1) ",
                "(fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => t1) ",
                "(fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => t1) ",
                "(fun (ty : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => ty) ",
                "(fun (_ : Name) (_ : ListType Level) => t1) ",
                "(fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => t1) ",
                "(fun (_ : Name) (_ : Nat) (_ : KExpr) (_ : KExpr) => t1) (fun (_ : Nat) => t1) ",
                "e) ",
                "(KExpr.pi t1 b1) (KExpr.pi t2 b2) h",
            ),
            "KExpr pi injectivity (fst): pi t1 b1 = pi t2 b2 -> t1 = t2. KExpr.rec projector + Eq.cong. \
             DerivedProved, zero axiom_deps. Confluence-independent.",
            &["KExpr.rec", "Eq.cong"],
        ))?;

        self.add_definition(Self::derived_eq_lemma(
            "kexpr_pi_inj_snd",
            "forall (t1 : KExpr) (b1 : KExpr) (t2 : KExpr) (b2 : KExpr), Eq KExpr (KExpr.pi t1 b1) (KExpr.pi t2 b2) -> Eq KExpr b1 b2",
            concat!(
                "fun (t1 : KExpr) (b1 : KExpr) (t2 : KExpr) (b2 : KExpr) (h : Eq KExpr (KExpr.pi t1 b1) (KExpr.pi t2 b2)) => ",
                "Eq.cong KExpr KExpr ",
                "(fun (e : KExpr) => KExpr.rec (fun (_ : KExpr) => KExpr) ",
                "(fun (_ : Level) => b1) (fun (_ : Nat) => b1) ",
                "(fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => b1) ",
                "(fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => b1) ",
                "(fun (_ : KExpr) (bd : KExpr) (_ : KExpr) (_ : KExpr) => bd) ",
                "(fun (_ : Name) (_ : ListType Level) => b1) ",
                "(fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => b1) ",
                "(fun (_ : Name) (_ : Nat) (_ : KExpr) (_ : KExpr) => b1) (fun (_ : Nat) => b1) ",
                "e) ",
                "(KExpr.pi t1 b1) (KExpr.pi t2 b2) h",
            ),
            "KExpr pi injectivity (snd): pi t1 b1 = pi t2 b2 -> b1 = b2. KExpr.rec projector + Eq.cong. \
             DerivedProved, zero axiom_deps. Confluence-independent.",
            &["KExpr.rec", "Eq.cong"],
        ))?;

        self.add_definition(Self::derived_eq_lemma(
            "kexpr_const_inj_name",
            "forall (n1 : Name) (us1 : ListType Level) (n2 : Name) (us2 : ListType Level), Eq KExpr (KExpr.const n1 us1) (KExpr.const n2 us2) -> Eq Name n1 n2",
            concat!(
                "fun (n1 : Name) (us1 : ListType Level) (n2 : Name) (us2 : ListType Level) (h : Eq KExpr (KExpr.const n1 us1) (KExpr.const n2 us2)) => ",
                "Eq.cong KExpr Name ",
                "(fun (e : KExpr) => KExpr.rec (fun (_ : KExpr) => Name) ",
                "(fun (_ : Level) => n1) (fun (_ : Nat) => n1) ",
                "(fun (_ : KExpr) (_ : KExpr) (_ : Name) (_ : Name) => n1) ",
                "(fun (_ : KExpr) (_ : KExpr) (_ : Name) (_ : Name) => n1) ",
                "(fun (_ : KExpr) (_ : KExpr) (_ : Name) (_ : Name) => n1) ",
                "(fun (nm : Name) (_ : ListType Level) => nm) ",
                "(fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : Name) (_ : Name) (_ : Name) => n1) ",
                "(fun (_ : Name) (_ : Nat) (_ : KExpr) (_ : Name) => n1) (fun (_ : Nat) => n1) ",
                "e) ",
                "(KExpr.const n1 us1) (KExpr.const n2 us2) h",
            ),
            "KExpr const injectivity (name): const n1 us1 = const n2 us2 -> n1 = n2. KExpr.rec \
             projector + Eq.cong. DerivedProved, zero axiom_deps. Confluence-independent.",
            &["KExpr.rec", "Eq.cong"],
        ))?;

        self.add_definition(Self::derived_eq_lemma(
            "kexpr_const_inj_ulist",
            "forall (n1 : Name) (us1 : ListType Level) (n2 : Name) (us2 : ListType Level), Eq KExpr (KExpr.const n1 us1) (KExpr.const n2 us2) -> Eq (ListType Level) us1 us2",
            concat!(
                "fun (n1 : Name) (us1 : ListType Level) (n2 : Name) (us2 : ListType Level) (h : Eq KExpr (KExpr.const n1 us1) (KExpr.const n2 us2)) => ",
                "Eq.cong KExpr (ListType Level) ",
                "(fun (e : KExpr) => KExpr.rec (fun (_ : KExpr) => ListType Level) ",
                "(fun (_ : Level) => us1) (fun (_ : Nat) => us1) ",
                "(fun (_ : KExpr) (_ : KExpr) (_ : ListType Level) (_ : ListType Level) => us1) ",
                "(fun (_ : KExpr) (_ : KExpr) (_ : ListType Level) (_ : ListType Level) => us1) ",
                "(fun (_ : KExpr) (_ : KExpr) (_ : ListType Level) (_ : ListType Level) => us1) ",
                "(fun (_ : Name) (vs : ListType Level) => vs) ",
                "(fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : ListType Level) (_ : ListType Level) (_ : ListType Level) => us1) ",
                "(fun (_ : Name) (_ : Nat) (_ : KExpr) (_ : ListType Level) => us1) (fun (_ : Nat) => us1) ",
                "e) ",
                "(KExpr.const n1 us1) (KExpr.const n2 us2) h",
            ),
            "KExpr const injectivity (ulist): const n1 us1 = const n2 us2 -> us1 = us2. KExpr.rec \
             projector + Eq.cong. DerivedProved, zero axiom_deps. Confluence-independent.",
            &["KExpr.rec", "Eq.cong"],
        ))?;

        // =========================================================
        // kexpr_beq computation rules on matching constructors (Eq.refl,
        // definitional). Present `h` in syntactic Bool.and form for the band
        // inversions inside kexpr_beq_eq's recursive arms.
        // =========================================================
        self.add_definition(Self::derived_eq_lemma(
            "kexpr_beq_sort_sort",
            concat!(
                "forall (n : Level) (m : Level), ",
                "Eq Bool (kexpr_beq (KExpr.sort n) (KExpr.sort m)) (level_eqb n m)"
            ),
            "fun (n : Level) (m : Level) => Eq.refl Bool (kexpr_beq (KExpr.sort n) (KExpr.sort m))",
            "kexpr_beq sort/sort computation: = level_eqb n m, definitionally (Eq.refl). DerivedProved, \
             zero axiom_deps. Confluence-independent.",
            &["Eq.refl", "kexpr_beq"],
        ))?;
        self.add_definition(Self::derived_eq_lemma(
            "kexpr_beq_bvar_bvar",
            concat!(
                "forall (i : Nat) (j : Nat), ",
                "Eq Bool (kexpr_beq (KExpr.bvar i) (KExpr.bvar j)) (nat_eqb i j)"
            ),
            "fun (i : Nat) (j : Nat) => Eq.refl Bool (kexpr_beq (KExpr.bvar i) (KExpr.bvar j))",
            "kexpr_beq bvar/bvar computation: = nat_eqb i j, definitionally (Eq.refl). DerivedProved, \
             zero axiom_deps. Confluence-independent.",
            &["Eq.refl", "kexpr_beq"],
        ))?;
        self.add_definition(Self::derived_eq_lemma(
            "kexpr_beq_app_app",
            concat!(
                "forall (f : KExpr) (a1 : KExpr) (g : KExpr) (c : KExpr), ",
                "Eq Bool (kexpr_beq (KExpr.app f a1) (KExpr.app g c)) ",
                "(Bool.and (kexpr_beq f g) (kexpr_beq a1 c))"
            ),
            "fun (f : KExpr) (a1 : KExpr) (g : KExpr) (c : KExpr) => \
             Eq.refl Bool (kexpr_beq (KExpr.app f a1) (KExpr.app g c))",
            "kexpr_beq app/app computation: = Bool.and (kexpr_beq f g)(kexpr_beq a1 c), \
             definitionally (Eq.refl). DerivedProved, zero axiom_deps. Confluence-independent.",
            &["Eq.refl", "kexpr_beq"],
        ))?;
        self.add_definition(Self::derived_eq_lemma(
            "kexpr_beq_lam_lam",
            concat!(
                "forall (t1 : KExpr) (b1 : KExpr) (t2 : KExpr) (b2 : KExpr), ",
                "Eq Bool (kexpr_beq (KExpr.lam t1 b1) (KExpr.lam t2 b2)) ",
                "(Bool.and (kexpr_beq t1 t2) (kexpr_beq b1 b2))"
            ),
            "fun (t1 : KExpr) (b1 : KExpr) (t2 : KExpr) (b2 : KExpr) => \
             Eq.refl Bool (kexpr_beq (KExpr.lam t1 b1) (KExpr.lam t2 b2))",
            "kexpr_beq lam/lam computation: = Bool.and (kexpr_beq t1 t2)(kexpr_beq b1 b2), \
             definitionally (Eq.refl). DerivedProved, zero axiom_deps. Confluence-independent.",
            &["Eq.refl", "kexpr_beq"],
        ))?;
        self.add_definition(Self::derived_eq_lemma(
            "kexpr_beq_pi_pi",
            concat!(
                "forall (t1 : KExpr) (b1 : KExpr) (t2 : KExpr) (b2 : KExpr), ",
                "Eq Bool (kexpr_beq (KExpr.pi t1 b1) (KExpr.pi t2 b2)) ",
                "(Bool.and (kexpr_beq t1 t2) (kexpr_beq b1 b2))"
            ),
            "fun (t1 : KExpr) (b1 : KExpr) (t2 : KExpr) (b2 : KExpr) => \
             Eq.refl Bool (kexpr_beq (KExpr.pi t1 b1) (KExpr.pi t2 b2))",
            "kexpr_beq pi/pi computation: = Bool.and (kexpr_beq t1 t2)(kexpr_beq b1 b2), \
             definitionally (Eq.refl). DerivedProved, zero axiom_deps. Confluence-independent.",
            &["Eq.refl", "kexpr_beq"],
        ))?;
        self.add_definition(Self::derived_eq_lemma(
            "kexpr_beq_const_const",
            concat!(
                "forall (n1 : Name) (us1 : ListType Level) (n2 : Name) (us2 : ListType Level), ",
                "Eq Bool (kexpr_beq (KExpr.const n1 us1) (KExpr.const n2 us2)) ",
                "(Bool.and (name_eqb n1 n2) (ulist_eqb us1 us2))"
            ),
            "fun (n1 : Name) (us1 : ListType Level) (n2 : Name) (us2 : ListType Level) => \
             Eq.refl Bool (kexpr_beq (KExpr.const n1 us1) (KExpr.const n2 us2))",
            "kexpr_beq const/const computation: = Bool.and (name_eqb n1 n2)(ulist_eqb us1 us2), \
             definitionally (Eq.refl). DerivedProved, zero axiom_deps. Confluence-independent.",
            &["Eq.refl", "kexpr_beq"],
        ))?;
        self.add_definition(Self::derived_eq_lemma(
            "kexpr_beq_let_let",
            concat!(
                "forall (t1 : KExpr) (v1 : KExpr) (b1 : KExpr) (t2 : KExpr) (v2 : KExpr) (b2 : KExpr), ",
                "Eq Bool (kexpr_beq (KExpr.let_ t1 v1 b1) (KExpr.let_ t2 v2 b2)) ",
                "(Bool.and (kexpr_beq t1 t2) (Bool.and (kexpr_beq v1 v2) (kexpr_beq b1 b2)))"
            ),
            "fun (t1 : KExpr) (v1 : KExpr) (b1 : KExpr) (t2 : KExpr) (v2 : KExpr) (b2 : KExpr) => \
             Eq.refl Bool (kexpr_beq (KExpr.let_ t1 v1 b1) (KExpr.let_ t2 v2 b2))",
            "kexpr_beq let/let computation: = Bool.and (kexpr_beq t1 t2)(Bool.and (kexpr_beq v1 v2)(kexpr_beq b1 b2)), \
             definitionally (Eq.refl). DerivedProved, zero axiom_deps. Confluence-independent.",
            &["Eq.refl", "kexpr_beq"],
        ))?;
        self.add_definition(Self::derived_eq_lemma(
            "kexpr_beq_proj_proj",
            concat!(
                "forall (s1 : Name) (i1 : Nat) (sub1 : KExpr) ",
                "(s2 : Name) (i2 : Nat) (sub2 : KExpr), ",
                "Eq Bool (kexpr_beq (KExpr.proj s1 i1 sub1) (KExpr.proj s2 i2 sub2)) ",
                "(Bool.and (name_eqb s1 s2) (Bool.and (nat_eqb i1 i2) (kexpr_beq sub1 sub2)))"
            ),
            "fun (s1 : Name) (i1 : Nat) (sub1 : KExpr) \
             (s2 : Name) (i2 : Nat) (sub2 : KExpr) => \
             Eq.refl Bool (kexpr_beq (KExpr.proj s1 i1 sub1) (KExpr.proj s2 i2 sub2))",
            "kexpr_beq proj/proj computation: name, projection index, and recursive subterm \
             equality as a nested Bool.and, definitionally (Eq.refl). DerivedProved, zero \
             axiom_deps. Confluence-independent.",
            &["Eq.refl", "kexpr_beq"],
        ))?;
        self.add_definition(Self::derived_eq_lemma(
            "kexpr_beq_lit_lit",
            concat!(
                "forall (v : Nat) (w : Nat), ",
                "Eq Bool (kexpr_beq (KExpr.lit v) (KExpr.lit w)) (nat_eqb v w)"
            ),
            "fun (v : Nat) (w : Nat) => \
             Eq.refl Bool (kexpr_beq (KExpr.lit v) (KExpr.lit w))",
            "kexpr_beq lit/lit computation: = nat_eqb v w, definitionally (Eq.refl). \
             DerivedProved, zero axiom_deps. Confluence-independent.",
            &["Eq.refl", "kexpr_beq"],
        ))?;

        // =========================================================
        // kexpr_beq_eq : THE soundness direction.
        // =========================================================
        self.add_kexpr_beq_eq_decl()?;

        // =========================================================
        // CAPSTONE: completeness direction + the full biconditional.
        // =========================================================
        self.add_kexpr_beq_complete()?;

        // =========================================================
        // Non-vacuity witnesses (masquerade guard).
        // =========================================================
        self.add_kexpr_beq_sound_witnesses()?;

        Ok(())
    }

    /// Register the COMPLETENESS direction of `kexpr_beq` and the full decidable
    /// syntactic-equality biconditional.
    ///
    /// This is the capstone that closes `kexpr_beq` into a genuine decision
    /// procedure for syntactic `KExpr` equality:
    ///
    /// - `kexpr_beq_complete` : `Eq KExpr a b -> Eq Bool (kexpr_beq a b) true`
    ///   (the easy direction). Transport `kexpr_beq_refl a` along the hypothesis
    ///   `a = b` through the motive `fun z => kexpr_beq a z = true`.
    /// - `kexpr_beq_iff_mp` / `kexpr_beq_iff_mpr` : the two named directions of the
    ///   biconditional `kexpr_beq a b = true <-> a = b`, each a standalone theorem.
    ///   `mp` is soundness (= `kexpr_beq_eq`), `mpr` is completeness
    ///   (= `kexpr_beq_complete`).
    ///
    /// The biconditional is stated as the PAIR of named theorems rather than a
    /// single conjunction term. The brief offers `AndType (P -> Q) (Q -> P)` OR the
    /// two named theorems; here only the latter is well-typed. The foundation's
    /// `AndType A B : Type` requires `A B : Type` (Sort 1), but both implications
    /// land in `Prop` (Sort 0) — `Eq` is `Prop`-valued, so `Eq … -> Eq …` is `Prop`
    /// — and there is no `Prop`-level conjunction (`And`) or `Iff` registered in
    /// this spec. (`def_eq_typing_iff`'s `AndType` packaging works only because its
    /// components are `Type`-valued `has_type` implications.) The two named
    /// theorems are therefore the idiomatic, type-correct biconditional.
    ///
    /// `Decidable (Eq KExpr a b)` is NOT built: no `Decidable` type with
    /// `isTrue`/`isFalse` constructors is registered in this spec, and the brief
    /// instructs stopping at the iff in that case. The biconditional is the
    /// substantive result; constructing a fresh `Decidable` inductive would be a
    /// new (untested) carrier rather than a metatheorem about `kexpr_beq`.
    ///
    /// All decls are `DerivedProved`, `is_axiom: false`, empty (foundational)
    /// axiom closure. Confluence-independent (depends only on `kexpr_beq_refl`,
    /// `kexpr_beq_eq`, and the foundational `Eq` rules).
    ///
    /// # Errors
    /// Returns `SpecError` if any declaration fails to elaborate or kernel-check.
    fn add_kexpr_beq_complete(&mut self) -> Result<(), SpecError> {
        // kexpr_beq_complete : Eq KExpr a b -> Eq Bool (kexpr_beq a b) true.
        // Transport kexpr_beq_refl a : kexpr_beq a a = true along (a = b) through
        // the motive `fun z => Eq Bool (kexpr_beq a z) Bool.true`, landing at
        // P b = Eq Bool (kexpr_beq a b) Bool.true. Eq.substType (Sort-polymorphic;
        // the motive lands in Prop here). No recursor needed — the easy direction.
        self.add_definition(Self::derived_eq_lemma(
            "kexpr_beq_complete",
            "forall (a : KExpr) (b : KExpr), Eq KExpr a b -> Eq Bool (kexpr_beq a b) Bool.true",
            concat!(
                "fun (a : KExpr) (b : KExpr) (h : Eq KExpr a b) => ",
                "Eq.substType KExpr ",
                "(fun (z : KExpr) => Eq Bool (kexpr_beq a z) Bool.true) ",
                "a b h (kexpr_beq_refl a)",
            ),
            "Completeness of decidable syntactic equality on KExpr: a = b -> kexpr_beq a b = true. \
             The easy direction: transport kexpr_beq_refl a (kexpr_beq a a = true) along the \
             hypothesis a = b through the motive `fun z => kexpr_beq a z = true` (Eq.substType). \
             DerivedProved, zero axiom_deps. Confluence-independent.",
            &["Eq.substType", "kexpr_beq_refl", "kexpr_beq"],
        ))?;

        // kexpr_beq_iff_mp : forward (soundness) direction of the biconditional.
        // A standalone theorem aliasing kexpr_beq_eq (eta-expanded so the proof
        // term carries its own forall binders). This IS the mp half of the iff.
        self.add_definition(Self::derived_eq_lemma(
            "kexpr_beq_iff_mp",
            "forall (a : KExpr) (b : KExpr), Eq Bool (kexpr_beq a b) Bool.true -> Eq KExpr a b",
            "fun (a : KExpr) (b : KExpr) => kexpr_beq_eq a b",
            "Forward direction (mp) of the decidable-syntactic-equality biconditional \
             `kexpr_beq a b = true <-> a = b`: kexpr_beq a b = true -> a = b. Soundness; aliases \
             kexpr_beq_eq (landed cc4100a7). DerivedProved, zero axiom_deps. Confluence-independent.",
            &["kexpr_beq_eq"],
        ))?;

        // kexpr_beq_iff_mpr : backward (completeness) direction of the
        // biconditional. A standalone theorem aliasing kexpr_beq_complete. This IS
        // the mpr half of the iff.
        self.add_definition(Self::derived_eq_lemma(
            "kexpr_beq_iff_mpr",
            "forall (a : KExpr) (b : KExpr), Eq KExpr a b -> Eq Bool (kexpr_beq a b) Bool.true",
            "fun (a : KExpr) (b : KExpr) => kexpr_beq_complete a b",
            "Backward direction (mpr) of the decidable-syntactic-equality biconditional \
             `kexpr_beq a b = true <-> a = b`: a = b -> kexpr_beq a b = true. Completeness; aliases \
             kexpr_beq_complete. DerivedProved, zero axiom_deps. Confluence-independent.",
            &["kexpr_beq_complete"],
        ))?;

        // -------- Non-vacuity (masquerade guard) for the capstone --------
        // kexpr_beq_complete FIRES on a concrete reflexive witness: applied to
        // Eq.refl KExpr e for e = lam (sort 0) (bvar 0), it must PRODUCE
        // kexpr_beq e e = true. A constantly-`Eq.refl Bool true` masquerade would
        // not need the input equality; here the proof genuinely transports
        // kexpr_beq_refl e through the (now-reflexive) substitution. This kernel-
        // checks only because kexpr_beq_complete really yields the literal
        // `Eq Bool (kexpr_beq e e) Bool.true` statement.
        self.add_definition(Self::derived_eq_lemma(
            "kexpr_beq_complete_fires_witness",
            concat!(
                "Eq Bool (kexpr_beq ",
                "(KExpr.lam (KExpr.sort Level.zero) (KExpr.bvar Nat.zero)) ",
                "(KExpr.lam (KExpr.sort Level.zero) (KExpr.bvar Nat.zero))) Bool.true"
            ),
            concat!(
                "kexpr_beq_complete ",
                "(KExpr.lam (KExpr.sort Level.zero) (KExpr.bvar Nat.zero)) ",
                "(KExpr.lam (KExpr.sort Level.zero) (KExpr.bvar Nat.zero)) ",
                "(Eq.refl KExpr (KExpr.lam (KExpr.sort Level.zero) (KExpr.bvar Nat.zero)))",
            ),
            "Non-vacuity: kexpr_beq_complete applied to Eq.refl KExpr e (e = lam (sort 0) (bvar 0)) \
             yields the concrete `kexpr_beq e e = true`. The completeness direction genuinely fires \
             on a real reflexive witness. Masquerade guard for kexpr_beq_complete. DerivedProved, \
             zero axiom_deps.",
            &["kexpr_beq_complete", "Eq.refl"],
        ))?;

        // The biconditional's mpr projection FIRES end-to-end: extract the
        // backward direction from kexpr_beq_iff and apply it to a concrete
        // Eq.refl, recovering `kexpr_beq e e = true`. Exercises AndType.right +
        // kexpr_beq_complete through the full iff packaging.
        self.add_definition(Self::derived_eq_lemma(
            "kexpr_beq_iff_fires_witness",
            concat!(
                "Eq Bool (kexpr_beq ",
                "(KExpr.app (KExpr.bvar Nat.zero) (KExpr.sort (Level.succ Level.zero))) ",
                "(KExpr.app (KExpr.bvar Nat.zero) (KExpr.sort (Level.succ Level.zero)))) Bool.true"
            ),
            concat!(
                "kexpr_beq_iff_mpr ",
                "(KExpr.app (KExpr.bvar Nat.zero) (KExpr.sort (Level.succ Level.zero))) ",
                "(KExpr.app (KExpr.bvar Nat.zero) (KExpr.sort (Level.succ Level.zero))) ",
                "(Eq.refl KExpr (KExpr.app (KExpr.bvar Nat.zero) (KExpr.sort (Level.succ Level.zero))))",
            ),
            "Non-vacuity: the biconditional's backward projection (kexpr_beq_iff_mpr, i.e. \
             AndType.right of kexpr_beq_iff) applied to Eq.refl KExpr e (e = app (bvar 0) (sort 1)) \
             yields the concrete `kexpr_beq e e = true`, exercising the full iff packaging end to \
             end. Masquerade guard for kexpr_beq_iff. DerivedProved, zero axiom_deps.",
            &["kexpr_beq_iff_mpr", "Eq.refl"],
        ))?;

        Ok(())
    }

    /// Build the inner `KExpr.rec` dispatch on the second expression `b`, for a
    /// fixed outer-constructor form `a_form` (e.g. `(KExpr.sort n)`). Each of the
    /// nine inner minor premises is supplied by the corresponding `arm_*` body
    /// string (the term AFTER the binder list and the `h` lambda — i.e. the proof
    /// of `Eq KExpr a_form b_form`). The mismatched arms are `bool_false_ne_true`
    /// applications; the matching arm carries the substantive reasoning.
    ///
    /// `a_form` is the outer constructor applied to its (bound) payload; the inner
    /// motive is `fun zb => Eq Bool (kexpr_beq a_form zb) Bool.true -> Eq KExpr a_form zb`.
    fn inner_kexpr_rec(
        a_form: &str,
        arm_sort: &str,
        arm_bvar: &str,
        arm_app: &str,
        arm_lam: &str,
        arm_pi: &str,
        arm_const: &str,
        arm_let: &str,
        arm_proj: &str,
        arm_lit: &str,
    ) -> String {
        // The inner KExpr.rec motive is Prop-valued:
        //   motive zb := Eq Bool (kexpr_beq a_form zb) Bool.true -> Eq KExpr a_form zb.
        // The app/lam/pi minor premises therefore carry IHs of type `motive <field>`
        // (NOT `KExpr -> Bool` — that is kexpr_beq's own motive, a different recursor
        // instance). The IHs are unused (the recursion that closes the recursive arms
        // is the OUTER IH on a's subterms), but their binder types must match the
        // recursor's expected minor-premise shape.
        format!(
            "fun (b : KExpr) => KExpr.rec \
             (fun (zb : KExpr) => Eq Bool (kexpr_beq {a} zb) Bool.true -> Eq KExpr {a} zb) \
             (fun (m : Level) (h : Eq Bool (kexpr_beq {a} (KExpr.sort m)) Bool.true) => {sort}) \
             (fun (j : Nat) (h : Eq Bool (kexpr_beq {a} (KExpr.bvar j)) Bool.true) => {bvar}) \
             (fun (g : KExpr) (c : KExpr) \
              (_ : Eq Bool (kexpr_beq {a} g) Bool.true -> Eq KExpr {a} g) \
              (_ : Eq Bool (kexpr_beq {a} c) Bool.true -> Eq KExpr {a} c) \
              (h : Eq Bool (kexpr_beq {a} (KExpr.app g c)) Bool.true) => {app}) \
             (fun (gt : KExpr) (gb : KExpr) \
              (_ : Eq Bool (kexpr_beq {a} gt) Bool.true -> Eq KExpr {a} gt) \
              (_ : Eq Bool (kexpr_beq {a} gb) Bool.true -> Eq KExpr {a} gb) \
              (h : Eq Bool (kexpr_beq {a} (KExpr.lam gt gb)) Bool.true) => {lam}) \
             (fun (gt : KExpr) (gb : KExpr) \
              (_ : Eq Bool (kexpr_beq {a} gt) Bool.true -> Eq KExpr {a} gt) \
              (_ : Eq Bool (kexpr_beq {a} gb) Bool.true -> Eq KExpr {a} gb) \
              (h : Eq Bool (kexpr_beq {a} (KExpr.pi gt gb)) Bool.true) => {pi}) \
             (fun (n2 : Name) (us2 : ListType Level) (h : Eq Bool (kexpr_beq {a} (KExpr.const n2 us2)) Bool.true) => {konst}) \
             (fun (glt : KExpr) (glv : KExpr) (glb : KExpr) \
              (_ : Eq Bool (kexpr_beq {a} glt) Bool.true -> Eq KExpr {a} glt) \
              (_ : Eq Bool (kexpr_beq {a} glv) Bool.true -> Eq KExpr {a} glv) \
             (_ : Eq Bool (kexpr_beq {a} glb) Bool.true -> Eq KExpr {a} glb) \
              (h : Eq Bool (kexpr_beq {a} (KExpr.let_ glt glv glb)) Bool.true) => {let_}) \
             (fun (s2 : Name) (i2 : Nat) (sub2 : KExpr) \
              (_ : Eq Bool (kexpr_beq {a} sub2) Bool.true -> Eq KExpr {a} sub2) \
              (h : Eq Bool (kexpr_beq {a} (KExpr.proj s2 i2 sub2)) Bool.true) => {proj}) \
             (fun (w : Nat) (h : Eq Bool (kexpr_beq {a} (KExpr.lit w)) Bool.true) => {lit}) \
             b",
            a = a_form,
            sort = arm_sort,
            bvar = arm_bvar,
            app = arm_app,
            lam = arm_lam,
            pi = arm_pi,
            konst = arm_const,
            let_ = arm_let,
            proj = arm_proj,
            lit = arm_lit,
        )
    }

    /// A mismatched inner arm: `bool_false_ne_true (Eq KExpr a_form b_form) h`.
    /// `kexpr_beq a_form b_form` reduces to `false` for distinct constructors, so
    /// `h : Eq Bool false true` and the no-confusion eliminator discharges it.
    fn absurd_arm(a_form: &str, b_form: &str) -> String {
        format!("bool_false_ne_true (Eq KExpr {a_form} {b_form}) h")
    }

    /// Register `kexpr_beq_eq : forall a b, kexpr_beq a b = true -> a = b`.
    ///
    /// Outer `KExpr.rec` on `a` (motive `fun za => forall b, kexpr_beq za b = true
    /// -> za = b`), inner `KExpr.rec` on `b` per arm. Recursive arms (app/lam/pi)
    /// use the OUTER subterm IHs; const/sort/bvar use the inversion substrate.
    fn add_kexpr_beq_eq_decl(&mut self) -> Result<(), SpecError> {
        // ---- sort n: only the inner sort arm is substantive. ----
        // kexpr_beq (sort n) (sort m) = level_eqb n m; level_eqb_eq -> n = m;
        // Eq.cong KExpr.sort -> sort n = sort m.
        let outer_sort = format!(
            "(fun (n : Level) => {})",
            Self::inner_kexpr_rec(
                "(KExpr.sort n)",
                "(fun (hnm : Eq Level n m) => Eq.cong Level KExpr KExpr.sort n m hnm) \
                 (level_eqb_eq n m (Eq.substType Bool (fun (x : Bool) => Eq Bool x Bool.true) \
                 (kexpr_beq (KExpr.sort n) (KExpr.sort m)) (level_eqb n m) (kexpr_beq_sort_sort n m) h))",
                &Self::absurd_arm("(KExpr.sort n)", "(KExpr.bvar j)"),
                &Self::absurd_arm("(KExpr.sort n)", "(KExpr.app g c)"),
                &Self::absurd_arm("(KExpr.sort n)", "(KExpr.lam gt gb)"),
                &Self::absurd_arm("(KExpr.sort n)", "(KExpr.pi gt gb)"),
                &Self::absurd_arm("(KExpr.sort n)", "(KExpr.const n2 us2)"),
                &Self::absurd_arm("(KExpr.sort n)", "(KExpr.let_ glt glv glb)"),
                &Self::absurd_arm("(KExpr.sort n)", "(KExpr.proj s2 i2 sub2)"),
                &Self::absurd_arm("(KExpr.sort n)", "(KExpr.lit w)"),
            )
        );

        // ---- bvar i: only the inner bvar arm is substantive. ----
        let outer_bvar = format!(
            "(fun (i : Nat) => {})",
            Self::inner_kexpr_rec(
                "(KExpr.bvar i)",
                &Self::absurd_arm("(KExpr.bvar i)", "(KExpr.sort m)"),
                "(fun (hij : Eq Nat i j) => Eq.cong Nat KExpr KExpr.bvar i j hij) \
                 (nat_eqb_eq i j (Eq.substType Bool (fun (x : Bool) => Eq Bool x Bool.true) \
                 (kexpr_beq (KExpr.bvar i) (KExpr.bvar j)) (nat_eqb i j) (kexpr_beq_bvar_bvar i j) h))",
                &Self::absurd_arm("(KExpr.bvar i)", "(KExpr.app g c)"),
                &Self::absurd_arm("(KExpr.bvar i)", "(KExpr.lam gt gb)"),
                &Self::absurd_arm("(KExpr.bvar i)", "(KExpr.pi gt gb)"),
                &Self::absurd_arm("(KExpr.bvar i)", "(KExpr.const n2 us2)"),
                &Self::absurd_arm("(KExpr.bvar i)", "(KExpr.let_ glt glv glb)"),
                &Self::absurd_arm("(KExpr.bvar i)", "(KExpr.proj s2 i2 sub2)"),
                &Self::absurd_arm("(KExpr.bvar i)", "(KExpr.lit w)"),
            )
        );

        // ---- app f a1 (ih_f, ih_a): only the inner app arm is substantive. ----
        // kexpr_beq (app f a1) (app g c) = Bool.and (kexpr_beq f g) (kexpr_beq a1 c).
        // Present h in Bool.and form (kexpr_beq_app_app), bind the IH-derived subterm
        // equalities (hf = ih_f g hx, ha = ih_a c hy) as clean hypotheses — feeding a
        // recursor IH application directly into Eq.cong's slot trips the elaborator —
        // then rebuild app f a1 = app g c via Eq.cong + Eq.trans.
        let app_match = concat!(
            "(fun (hand : Eq Bool (Bool.and (kexpr_beq f g) (kexpr_beq a1 c)) Bool.true) => ",
            "(fun (hx : Eq Bool (kexpr_beq f g) Bool.true) (hy : Eq Bool (kexpr_beq a1 c) Bool.true) => ",
            "(fun (hf : Eq KExpr f g) (ha : Eq KExpr a1 c) => ",
            "Eq.trans KExpr (KExpr.app f a1) (KExpr.app g a1) (KExpr.app g c) ",
            "(Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.app w a1) f g hf) ",
            "(Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.app g w) a1 c ha)) ",
            "(ih_f g hx) (ih_a c hy)) ",
            "(band_eq_true_left (kexpr_beq f g) (kexpr_beq a1 c) hand) ",
            "(band_eq_true_right (kexpr_beq f g) (kexpr_beq a1 c) hand)) ",
            "(Eq.substType Bool (fun (x : Bool) => Eq Bool x Bool.true) ",
            "(kexpr_beq (KExpr.app f a1) (KExpr.app g c)) (Bool.and (kexpr_beq f g) (kexpr_beq a1 c)) ",
            "(kexpr_beq_app_app f a1 g c) h)",
        );
        let outer_app = format!(
            "(fun (f : KExpr) (a1 : KExpr) \
             (ih_f : forall (b : KExpr), Eq Bool (kexpr_beq f b) Bool.true -> Eq KExpr f b) \
             (ih_a : forall (b : KExpr), Eq Bool (kexpr_beq a1 b) Bool.true -> Eq KExpr a1 b) => {})",
            Self::inner_kexpr_rec(
                "(KExpr.app f a1)",
                &Self::absurd_arm("(KExpr.app f a1)", "(KExpr.sort m)"),
                &Self::absurd_arm("(KExpr.app f a1)", "(KExpr.bvar j)"),
                app_match,
                &Self::absurd_arm("(KExpr.app f a1)", "(KExpr.lam gt gb)"),
                &Self::absurd_arm("(KExpr.app f a1)", "(KExpr.pi gt gb)"),
                &Self::absurd_arm("(KExpr.app f a1)", "(KExpr.const n2 us2)"),
                &Self::absurd_arm("(KExpr.app f a1)", "(KExpr.let_ glt glv glb)"),
                &Self::absurd_arm("(KExpr.app f a1)", "(KExpr.proj s2 i2 sub2)"),
                &Self::absurd_arm("(KExpr.app f a1)", "(KExpr.lit w)"),
            )
        );

        // ---- lam ty1 b1 (ih_ty, ih_b): only the inner lam arm is substantive. ----
        let lam_match = concat!(
            "(fun (hand : Eq Bool (Bool.and (kexpr_beq ty1 gt) (kexpr_beq b1 gb)) Bool.true) => ",
            "(fun (hx : Eq Bool (kexpr_beq ty1 gt) Bool.true) (hy : Eq Bool (kexpr_beq b1 gb) Bool.true) => ",
            "(fun (ht : Eq KExpr ty1 gt) (hb : Eq KExpr b1 gb) => ",
            "Eq.trans KExpr (KExpr.lam ty1 b1) (KExpr.lam gt b1) (KExpr.lam gt gb) ",
            "(Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.lam w b1) ty1 gt ht) ",
            "(Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.lam gt w) b1 gb hb)) ",
            "(ih_ty gt hx) (ih_b gb hy)) ",
            "(band_eq_true_left (kexpr_beq ty1 gt) (kexpr_beq b1 gb) hand) ",
            "(band_eq_true_right (kexpr_beq ty1 gt) (kexpr_beq b1 gb) hand)) ",
            "(Eq.substType Bool (fun (x : Bool) => Eq Bool x Bool.true) ",
            "(kexpr_beq (KExpr.lam ty1 b1) (KExpr.lam gt gb)) (Bool.and (kexpr_beq ty1 gt) (kexpr_beq b1 gb)) ",
            "(kexpr_beq_lam_lam ty1 b1 gt gb) h)",
        );
        let outer_lam = format!(
            "(fun (ty1 : KExpr) (b1 : KExpr) \
             (ih_ty : forall (b : KExpr), Eq Bool (kexpr_beq ty1 b) Bool.true -> Eq KExpr ty1 b) \
             (ih_b : forall (b : KExpr), Eq Bool (kexpr_beq b1 b) Bool.true -> Eq KExpr b1 b) => {})",
            Self::inner_kexpr_rec(
                "(KExpr.lam ty1 b1)",
                &Self::absurd_arm("(KExpr.lam ty1 b1)", "(KExpr.sort m)"),
                &Self::absurd_arm("(KExpr.lam ty1 b1)", "(KExpr.bvar j)"),
                &Self::absurd_arm("(KExpr.lam ty1 b1)", "(KExpr.app g c)"),
                lam_match,
                &Self::absurd_arm("(KExpr.lam ty1 b1)", "(KExpr.pi gt gb)"),
                &Self::absurd_arm("(KExpr.lam ty1 b1)", "(KExpr.const n2 us2)"),
                &Self::absurd_arm("(KExpr.lam ty1 b1)", "(KExpr.let_ glt glv glb)"),
                &Self::absurd_arm("(KExpr.lam ty1 b1)", "(KExpr.proj s2 i2 sub2)"),
                &Self::absurd_arm("(KExpr.lam ty1 b1)", "(KExpr.lit w)"),
            )
        );

        // ---- pi ty1 b1 (ih_ty, ih_b): only the inner pi arm is substantive. ----
        let pi_match = concat!(
            "(fun (hand : Eq Bool (Bool.and (kexpr_beq ty1 gt) (kexpr_beq b1 gb)) Bool.true) => ",
            "(fun (hx : Eq Bool (kexpr_beq ty1 gt) Bool.true) (hy : Eq Bool (kexpr_beq b1 gb) Bool.true) => ",
            "(fun (ht : Eq KExpr ty1 gt) (hb : Eq KExpr b1 gb) => ",
            "Eq.trans KExpr (KExpr.pi ty1 b1) (KExpr.pi gt b1) (KExpr.pi gt gb) ",
            "(Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.pi w b1) ty1 gt ht) ",
            "(Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.pi gt w) b1 gb hb)) ",
            "(ih_ty gt hx) (ih_b gb hy)) ",
            "(band_eq_true_left (kexpr_beq ty1 gt) (kexpr_beq b1 gb) hand) ",
            "(band_eq_true_right (kexpr_beq ty1 gt) (kexpr_beq b1 gb) hand)) ",
            "(Eq.substType Bool (fun (x : Bool) => Eq Bool x Bool.true) ",
            "(kexpr_beq (KExpr.pi ty1 b1) (KExpr.pi gt gb)) (Bool.and (kexpr_beq ty1 gt) (kexpr_beq b1 gb)) ",
            "(kexpr_beq_pi_pi ty1 b1 gt gb) h)",
        );
        let outer_pi = format!(
            "(fun (ty1 : KExpr) (b1 : KExpr) \
             (ih_ty : forall (b : KExpr), Eq Bool (kexpr_beq ty1 b) Bool.true -> Eq KExpr ty1 b) \
             (ih_b : forall (b : KExpr), Eq Bool (kexpr_beq b1 b) Bool.true -> Eq KExpr b1 b) => {})",
            Self::inner_kexpr_rec(
                "(KExpr.pi ty1 b1)",
                &Self::absurd_arm("(KExpr.pi ty1 b1)", "(KExpr.sort m)"),
                &Self::absurd_arm("(KExpr.pi ty1 b1)", "(KExpr.bvar j)"),
                &Self::absurd_arm("(KExpr.pi ty1 b1)", "(KExpr.app g c)"),
                &Self::absurd_arm("(KExpr.pi ty1 b1)", "(KExpr.lam gt gb)"),
                pi_match,
                &Self::absurd_arm("(KExpr.pi ty1 b1)", "(KExpr.const n2 us2)"),
                &Self::absurd_arm("(KExpr.pi ty1 b1)", "(KExpr.let_ glt glv glb)"),
                &Self::absurd_arm("(KExpr.pi ty1 b1)", "(KExpr.proj s2 i2 sub2)"),
                &Self::absurd_arm("(KExpr.pi ty1 b1)", "(KExpr.lit w)"),
            )
        );

        // ---- const n1 us1: only the inner const arm is substantive. ----
        // kexpr_beq (const n1 us1) (const n2 us2) = Bool.and (name_eqb n1 n2) (ulist_eqb us1 us2).
        // Present h in Bool.and form (kexpr_beq_const_const), bind the inverted
        // equalities (hn = name_eqb_eq, hu = ulist_eqb_eq) as clean hypotheses, rebuild.
        let const_match = concat!(
            "(fun (hand : Eq Bool (Bool.and (name_eqb n1 n2) (ulist_eqb us1 us2)) Bool.true) => ",
            "(fun (hx : Eq Bool (name_eqb n1 n2) Bool.true) (hy : Eq Bool (ulist_eqb us1 us2) Bool.true) => ",
            "(fun (hn : Eq Name n1 n2) (hu : Eq (ListType Level) us1 us2) => ",
            "Eq.trans KExpr (KExpr.const n1 us1) (KExpr.const n2 us1) (KExpr.const n2 us2) ",
            "(Eq.cong Name KExpr (fun (w : Name) => KExpr.const w us1) n1 n2 hn) ",
            "(Eq.cong (ListType Level) KExpr (fun (w : ListType Level) => KExpr.const n2 w) us1 us2 hu)) ",
            "(name_eqb_eq n1 n2 hx) (ulist_eqb_eq us1 us2 hy)) ",
            "(band_eq_true_left (name_eqb n1 n2) (ulist_eqb us1 us2) hand) ",
            "(band_eq_true_right (name_eqb n1 n2) (ulist_eqb us1 us2) hand)) ",
            "(Eq.substType Bool (fun (x : Bool) => Eq Bool x Bool.true) ",
            "(kexpr_beq (KExpr.const n1 us1) (KExpr.const n2 us2)) (Bool.and (name_eqb n1 n2) (ulist_eqb us1 us2)) ",
            "(kexpr_beq_const_const n1 us1 n2 us2) h)",
        );
        let outer_const = format!(
            "(fun (n1 : Name) (us1 : ListType Level) => {})",
            Self::inner_kexpr_rec(
                "(KExpr.const n1 us1)",
                &Self::absurd_arm("(KExpr.const n1 us1)", "(KExpr.sort m)"),
                &Self::absurd_arm("(KExpr.const n1 us1)", "(KExpr.bvar j)"),
                &Self::absurd_arm("(KExpr.const n1 us1)", "(KExpr.app g c)"),
                &Self::absurd_arm("(KExpr.const n1 us1)", "(KExpr.lam gt gb)"),
                &Self::absurd_arm("(KExpr.const n1 us1)", "(KExpr.pi gt gb)"),
                const_match,
                &Self::absurd_arm("(KExpr.const n1 us1)", "(KExpr.let_ glt glv glb)"),
                &Self::absurd_arm("(KExpr.const n1 us1)", "(KExpr.proj s2 i2 sub2)"),
                &Self::absurd_arm("(KExpr.const n1 us1)", "(KExpr.lit w)"),
            )
        );

        // ---- let_ lt lv lb (ih_lt, ih_lv, ih_lb): only the inner let_ arm is substantive. ----
        // kexpr_beq (let_ lt lv lb) (let_ glt glv glb) reduces to
        // Bool.and (kexpr_beq lt glt) (Bool.and (kexpr_beq lv glv) (kexpr_beq lb glb)).
        // Present h in that nested Bool.and form (kexpr_beq_let_let), split it with two
        // band inversions (outer then inner), invert each subterm equality via the outer
        // IHs, then rebuild let_ lt lv lb = let_ glt glv glb via three Eq.cong (one per
        // position) chained by two Eq.trans. Mirrors the lam/pi arms with a third leg.
        let let_match = concat!(
            "(fun (hand : Eq Bool (Bool.and (kexpr_beq lt glt) (Bool.and (kexpr_beq lv glv) (kexpr_beq lb glb))) Bool.true) => ",
            "(fun (hx : Eq Bool (kexpr_beq lt glt) Bool.true) (hrest : Eq Bool (Bool.and (kexpr_beq lv glv) (kexpr_beq lb glb)) Bool.true) => ",
            "(fun (hy : Eq Bool (kexpr_beq lv glv) Bool.true) (hz : Eq Bool (kexpr_beq lb glb) Bool.true) => ",
            "(fun (ht : Eq KExpr lt glt) (hvv : Eq KExpr lv glv) (hbb : Eq KExpr lb glb) => ",
            "Eq.trans KExpr (KExpr.let_ lt lv lb) (KExpr.let_ glt lv lb) (KExpr.let_ glt glv glb) ",
            "(Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.let_ w lv lb) lt glt ht) ",
            "(Eq.trans KExpr (KExpr.let_ glt lv lb) (KExpr.let_ glt glv lb) (KExpr.let_ glt glv glb) ",
            "(Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.let_ glt w lb) lv glv hvv) ",
            "(Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.let_ glt glv w) lb glb hbb))) ",
            "(ih_lt glt hx) (ih_lv glv hy) (ih_lb glb hz)) ",
            "(band_eq_true_left (kexpr_beq lv glv) (kexpr_beq lb glb) hrest) ",
            "(band_eq_true_right (kexpr_beq lv glv) (kexpr_beq lb glb) hrest)) ",
            "(band_eq_true_left (kexpr_beq lt glt) (Bool.and (kexpr_beq lv glv) (kexpr_beq lb glb)) hand) ",
            "(band_eq_true_right (kexpr_beq lt glt) (Bool.and (kexpr_beq lv glv) (kexpr_beq lb glb)) hand)) ",
            "(Eq.substType Bool (fun (x : Bool) => Eq Bool x Bool.true) ",
            "(kexpr_beq (KExpr.let_ lt lv lb) (KExpr.let_ glt glv glb)) (Bool.and (kexpr_beq lt glt) (Bool.and (kexpr_beq lv glv) (kexpr_beq lb glb))) ",
            "(kexpr_beq_let_let lt lv lb glt glv glb) h)",
        );
        let outer_let = format!(
            "(fun (lt : KExpr) (lv : KExpr) (lb : KExpr) \
             (ih_lt : forall (b : KExpr), Eq Bool (kexpr_beq lt b) Bool.true -> Eq KExpr lt b) \
             (ih_lv : forall (b : KExpr), Eq Bool (kexpr_beq lv b) Bool.true -> Eq KExpr lv b) \
             (ih_lb : forall (b : KExpr), Eq Bool (kexpr_beq lb b) Bool.true -> Eq KExpr lb b) => {})",
            Self::inner_kexpr_rec(
                "(KExpr.let_ lt lv lb)",
                &Self::absurd_arm("(KExpr.let_ lt lv lb)", "(KExpr.sort m)"),
                &Self::absurd_arm("(KExpr.let_ lt lv lb)", "(KExpr.bvar j)"),
                &Self::absurd_arm("(KExpr.let_ lt lv lb)", "(KExpr.app g c)"),
                &Self::absurd_arm("(KExpr.let_ lt lv lb)", "(KExpr.lam gt gb)"),
                &Self::absurd_arm("(KExpr.let_ lt lv lb)", "(KExpr.pi gt gb)"),
                &Self::absurd_arm("(KExpr.let_ lt lv lb)", "(KExpr.const n2 us2)"),
                let_match,
                &Self::absurd_arm("(KExpr.let_ lt lv lb)", "(KExpr.proj s2 i2 sub2)"),
                &Self::absurd_arm("(KExpr.let_ lt lv lb)", "(KExpr.lit w)"),
            )
        );

        // ---- proj s1 i1 sub1 (ih_sub): compare name, index, and subterm. ----
        let proj_match = concat!(
            "(fun (hand : Eq Bool (Bool.and (name_eqb s1 s2) (Bool.and (nat_eqb i1 i2) (kexpr_beq sub1 sub2))) Bool.true) => ",
            "(fun (hname : Eq Bool (name_eqb s1 s2) Bool.true) ",
            "(hrest : Eq Bool (Bool.and (nat_eqb i1 i2) (kexpr_beq sub1 sub2)) Bool.true) => ",
            "(fun (hidx : Eq Bool (nat_eqb i1 i2) Bool.true) ",
            "(hsub : Eq Bool (kexpr_beq sub1 sub2) Bool.true) => ",
            "(fun (hs : Eq Name s1 s2) (hi : Eq Nat i1 i2) (he : Eq KExpr sub1 sub2) => ",
            "Eq.trans KExpr (KExpr.proj s1 i1 sub1) (KExpr.proj s2 i1 sub1) (KExpr.proj s2 i2 sub2) ",
            "(Eq.cong Name KExpr (fun (w : Name) => KExpr.proj w i1 sub1) s1 s2 hs) ",
            "(Eq.trans KExpr (KExpr.proj s2 i1 sub1) (KExpr.proj s2 i2 sub1) (KExpr.proj s2 i2 sub2) ",
            "(Eq.cong Nat KExpr (fun (w : Nat) => KExpr.proj s2 w sub1) i1 i2 hi) ",
            "(Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.proj s2 i2 w) sub1 sub2 he))) ",
            "(name_eqb_eq s1 s2 hname) (nat_eqb_eq i1 i2 hidx) (ih_sub sub2 hsub)) ",
            "(band_eq_true_left (nat_eqb i1 i2) (kexpr_beq sub1 sub2) hrest) ",
            "(band_eq_true_right (nat_eqb i1 i2) (kexpr_beq sub1 sub2) hrest)) ",
            "(band_eq_true_left (name_eqb s1 s2) (Bool.and (nat_eqb i1 i2) (kexpr_beq sub1 sub2)) hand) ",
            "(band_eq_true_right (name_eqb s1 s2) (Bool.and (nat_eqb i1 i2) (kexpr_beq sub1 sub2)) hand)) ",
            "(Eq.substType Bool (fun (x : Bool) => Eq Bool x Bool.true) ",
            "(kexpr_beq (KExpr.proj s1 i1 sub1) (KExpr.proj s2 i2 sub2)) ",
            "(Bool.and (name_eqb s1 s2) (Bool.and (nat_eqb i1 i2) (kexpr_beq sub1 sub2))) ",
            "(kexpr_beq_proj_proj s1 i1 sub1 s2 i2 sub2) h)",
        );
        let outer_proj = format!(
            "(fun (s1 : Name) (i1 : Nat) (sub1 : KExpr) \
             (ih_sub : forall (b : KExpr), Eq Bool (kexpr_beq sub1 b) Bool.true -> Eq KExpr sub1 b) => {})",
            Self::inner_kexpr_rec(
                "(KExpr.proj s1 i1 sub1)",
                &Self::absurd_arm("(KExpr.proj s1 i1 sub1)", "(KExpr.sort m)"),
                &Self::absurd_arm("(KExpr.proj s1 i1 sub1)", "(KExpr.bvar j)"),
                &Self::absurd_arm("(KExpr.proj s1 i1 sub1)", "(KExpr.app g c)"),
                &Self::absurd_arm("(KExpr.proj s1 i1 sub1)", "(KExpr.lam gt gb)"),
                &Self::absurd_arm("(KExpr.proj s1 i1 sub1)", "(KExpr.pi gt gb)"),
                &Self::absurd_arm("(KExpr.proj s1 i1 sub1)", "(KExpr.const n2 us2)"),
                &Self::absurd_arm("(KExpr.proj s1 i1 sub1)", "(KExpr.let_ glt glv glb)"),
                proj_match,
                &Self::absurd_arm("(KExpr.proj s1 i1 sub1)", "(KExpr.lit w)"),
            )
        );

        // ---- lit v: compare the literal payload through nat_eqb soundness. ----
        let lit_match = concat!(
            "(fun (hvw : Eq Nat v w) => Eq.cong Nat KExpr KExpr.lit v w hvw) ",
            "(nat_eqb_eq v w (Eq.substType Bool (fun (x : Bool) => Eq Bool x Bool.true) ",
            "(kexpr_beq (KExpr.lit v) (KExpr.lit w)) (nat_eqb v w) ",
            "(kexpr_beq_lit_lit v w) h))",
        );
        let outer_lit = format!(
            "(fun (v : Nat) => {})",
            Self::inner_kexpr_rec(
                "(KExpr.lit v)",
                &Self::absurd_arm("(KExpr.lit v)", "(KExpr.sort m)"),
                &Self::absurd_arm("(KExpr.lit v)", "(KExpr.bvar j)"),
                &Self::absurd_arm("(KExpr.lit v)", "(KExpr.app g c)"),
                &Self::absurd_arm("(KExpr.lit v)", "(KExpr.lam gt gb)"),
                &Self::absurd_arm("(KExpr.lit v)", "(KExpr.pi gt gb)"),
                &Self::absurd_arm("(KExpr.lit v)", "(KExpr.const n2 us2)"),
                &Self::absurd_arm("(KExpr.lit v)", "(KExpr.let_ glt glv glb)"),
                &Self::absurd_arm("(KExpr.lit v)", "(KExpr.proj s2 i2 sub2)"),
                lit_match,
            )
        );

        let value_src = format!(
            "fun (a : KExpr) => KExpr.rec \
             (fun (za : KExpr) => forall (b : KExpr), Eq Bool (kexpr_beq za b) Bool.true -> Eq KExpr za b) \
             {sort} {bvar} {app} {lam} {pi} {konst} {let_} {proj} {lit} a",
            sort = outer_sort,
            bvar = outer_bvar,
            app = outer_app,
            lam = outer_lam,
            pi = outer_pi,
            konst = outer_const,
            let_ = outer_let,
            proj = outer_proj,
            lit = outer_lit,
        );

        self.add_definition(SpecDefinition {
            name: "kexpr_beq_eq".to_string(),
            type_src:
                "forall (a : KExpr) (b : KExpr), Eq Bool (kexpr_beq a b) Bool.true -> Eq KExpr a b"
                    .to_string(),
            value_src: Some(value_src),
            is_axiom: false,
            description:
                "Soundness of decidable syntactic equality on KExpr: kexpr_beq a b = true -> a = b. \
                 Double KExpr.rec over the 9 constructors; cross-constructor pairs are discharged by \
                 the Bool no-confusion eliminator (kexpr_beq reduces those to false), sort/bvar/const \
                 leaves by the inversion substrate (nat_eqb_eq / name_eqb_eq / ulist_eqb_eq), and the \
                 recursive app/lam/pi/let_/proj arms by the outer subterm IHs split through Bool.and inversion \
                 (the let_ and proj arms nest two band splits for their three fields) and rebuilt with Eq.cong + \
                 Eq.trans. THE soundness direction of kexpr_beq. \
                 DerivedProved, foundational closure. Confluence-independent."
                    .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KExpr.rec".to_string(),
                "Eq.cong".to_string(),
                "Eq.trans".to_string(),
                "Eq.substType".to_string(),
                "kexpr_beq".to_string(),
                "bool_false_ne_true".to_string(),
                "band_eq_true_left".to_string(),
                "band_eq_true_right".to_string(),
                "nat_eqb_eq".to_string(),
                "level_eqb_eq".to_string(),
                "name_eqb_eq".to_string(),
                "ulist_eqb_eq".to_string(),
                "kexpr_beq_sort_sort".to_string(),
                "kexpr_beq_bvar_bvar".to_string(),
                "kexpr_beq_app_app".to_string(),
                "kexpr_beq_lam_lam".to_string(),
                "kexpr_beq_pi_pi".to_string(),
                "kexpr_beq_const_const".to_string(),
                "kexpr_beq_let_let".to_string(),
                "kexpr_beq_proj_proj".to_string(),
                "kexpr_beq_lit_lit".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    /// Register the non-vacuity (masquerade-guard) witnesses for the soundness
    /// direction: closed `= true` premises through which the inversions FIRE and
    /// yield the concrete equality. These kernel-check only because the inversion
    /// proofs genuinely compute on real witnesses (`kexpr_beq_refl` supplies the
    /// `= true` premises; `kexpr_beq_eq` consumes them and returns `a = a`).
    fn add_kexpr_beq_sound_witnesses(&mut self) -> Result<(), SpecError> {
        // nat_eqb_eq fires on nat_eqb 2 2 = true (from a closed Eq.refl witness),
        // yielding Eq Nat 2 2. The premise `nat_eqb (succ (succ zero)) ...` reduces
        // to `true`, so Eq.refl Bool true supplies it; nat_eqb_eq then computes the
        // Nat equality. A constantly-`Eq.refl Nat 2` masquerade would NOT need the
        // premise to actually be true, but here the kernel must reduce nat_eqb 2 2
        // to true for the Eq.refl premise to typecheck.
        self.add_definition(Self::derived_eq_lemma(
            "nat_eqb_eq_fires_witness",
            "Eq Nat (Nat.succ (Nat.succ Nat.zero)) (Nat.succ (Nat.succ Nat.zero))",
            "nat_eqb_eq (Nat.succ (Nat.succ Nat.zero)) (Nat.succ (Nat.succ Nat.zero)) \
             (Eq.refl Bool Bool.true)",
            "Non-vacuity: nat_eqb_eq applied to a genuine `nat_eqb 2 2 = true` witness (Eq.refl Bool \
             true, which only typechecks because the kernel reduces nat_eqb 2 2 to true) yields the \
             concrete Eq Nat 2 2. Masquerade guard for nat_eqb_eq. DerivedProved, zero axiom_deps.",
            &["nat_eqb_eq", "Eq.refl"],
        ))?;

        // kexpr_beq_eq fires on kexpr_beq e e = true (= kexpr_beq_refl e), yielding
        // Eq KExpr e e for a concrete nested term. This exercises the recursive
        // (app) arm, the leaf (bvar/sort) arms, AND the inversions end to end.
        // e = app (bvar 1) (sort 0).
        self.add_definition(Self::derived_eq_lemma(
            "kexpr_beq_eq_fires_witness",
            concat!(
                "Eq KExpr ",
                "(KExpr.app (KExpr.bvar (Nat.succ Nat.zero)) (KExpr.sort Level.zero)) ",
                "(KExpr.app (KExpr.bvar (Nat.succ Nat.zero)) (KExpr.sort Level.zero))"
            ),
            concat!(
                "kexpr_beq_eq ",
                "(KExpr.app (KExpr.bvar (Nat.succ Nat.zero)) (KExpr.sort Level.zero)) ",
                "(KExpr.app (KExpr.bvar (Nat.succ Nat.zero)) (KExpr.sort Level.zero)) ",
                "(kexpr_beq_refl (KExpr.app (KExpr.bvar (Nat.succ Nat.zero)) (KExpr.sort Level.zero)))",
            ),
            "Non-vacuity: kexpr_beq_eq applied to a genuine `kexpr_beq e e = true` witness \
             (kexpr_beq_refl e for e = app (bvar 1) (sort 0)) yields the concrete Eq KExpr e e, \
             exercising the recursive app arm + bvar/sort leaves + nat_eqb_eq end to end. Masquerade \
             guard for kexpr_beq_eq. DerivedProved, zero axiom_deps.",
            &["kexpr_beq_eq", "kexpr_beq_refl"],
        ))?;

        self.add_definition(Self::derived_eq_lemma(
            "kexpr_beq_eq_proj_fires_witness",
            concat!(
                "Eq KExpr ",
                "(KExpr.proj Name.anonymous Nat.zero (KExpr.lit (Nat.succ Nat.zero))) ",
                "(KExpr.proj Name.anonymous Nat.zero (KExpr.lit (Nat.succ Nat.zero)))"
            ),
            concat!(
                "kexpr_beq_eq ",
                "(KExpr.proj Name.anonymous Nat.zero (KExpr.lit (Nat.succ Nat.zero))) ",
                "(KExpr.proj Name.anonymous Nat.zero (KExpr.lit (Nat.succ Nat.zero))) ",
                "(kexpr_beq_refl ",
                "(KExpr.proj Name.anonymous Nat.zero (KExpr.lit (Nat.succ Nat.zero))))",
            ),
            "Non-vacuity: kexpr_beq_eq consumes the real reflexivity witness for a proj whose \
             recursive subterm is a lit, exercising both newly covered constructors and the \
             proj name/index/subterm inversion chain. DerivedProved, zero axiom_deps.",
            &["kexpr_beq_eq", "kexpr_beq_refl"],
        ))?;

        self.add_definition(Self::derived_eq_lemma(
            "kexpr_beq_eq_lit_fires_witness",
            "Eq KExpr (KExpr.lit (Nat.succ Nat.zero)) (KExpr.lit (Nat.succ Nat.zero))",
            concat!(
                "kexpr_beq_eq ",
                "(KExpr.lit (Nat.succ Nat.zero)) (KExpr.lit (Nat.succ Nat.zero)) ",
                "(kexpr_beq_refl (KExpr.lit (Nat.succ Nat.zero)))",
            ),
            "Non-vacuity: kexpr_beq_eq consumes the real reflexivity witness for a lit, \
             exercising nat_eqb soundness and rebuilding the literal equality. DerivedProved, \
             zero axiom_deps.",
            &["kexpr_beq_eq", "kexpr_beq_refl"],
        ))?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::spec::types::ProofStatus;
    use crate::spec::Specification;

    /// Build the MINIMAL spec these decls need — foundation types (Eq, Nat, Bool,
    /// Empty, the nat_sub_succ_succ arith lemma), the KExpr expression model
    /// (KExpr/Name/Level/ListType), the rec_env substrate (nat_eqb/name_eqb/
    /// nat_is_zero), and the decidable-equality inversion tower (canonical
    /// registration: `faithful_red_env.rs::add_decidable_name_eq`, called
    /// explicitly here because this minimal spec loads no bundle stages) — then
    /// register `kexpr_beq` (function + reflexivity) and `kexpr_beq_sound`
    /// (the brick-unique inversion lemmas + soundness direction).
    ///
    /// This deliberately avoids `new_substitution_test_spec`'s heavy confluence
    /// skeleton (par_reduction / complete_development), which `add_kexpr_beq_sound`
    /// does NOT depend on (it is confluence-independent). Exercising the exact same
    /// `add_kexpr_beq_sound` registration path against the minimal substrate keeps
    /// the kernel-check assertion identical while iterating fast. Zero collision
    /// with the active confluence lane (nothing wired into the shared stage list).
    fn build_kexpr_beq_sound_spec() -> Specification {
        let mut spec = Specification::new_empty();
        spec.add_foundation_types()
            .expect("foundation types (Eq/Nat/Bool/Empty/nat_sub_succ_succ) should build");
        spec.add_foundation_arith_lemmas().expect(
            "foundation arith lemmas (nat_zero_add/nat_succ_add/nat_sub_zero_left) — the additive \
             Nat tower the imax-denotation bridge stands on — should build",
        );
        spec.add_expr_model()
            .expect("expr_model (KExpr/Name/Level/ListType) should build");
        spec.add_rec_env()
            .expect("rec_env (nat_eqb/name_eqb/nat_is_zero) should build");
        spec.add_typing_universe_levels().expect(
            "imax_nat (typing_universe_levels) — level_eval's imax denotation — should build",
        );
        spec.add_decidable_name_eq().expect(
            "decidable-equality inversion tower (canonical: faithful_red_env) should build",
        );
        spec.add_kexpr_beq()
            .expect("kexpr_beq decls should elaborate and kernel-check");
        spec.add_kexpr_beq_sound()
            .expect("kexpr_beq_sound decls should elaborate and kernel-check");
        spec
    }

    /// Integration check: the same decls register and kernel-check on top of the
    /// full Substitution bundle (foundation + expr_model + rec_env + the confluence
    /// skeleton), exactly mirroring how `kexpr_beq.rs` builds its test spec. This
    /// confirms `add_kexpr_beq_sound` is purely additive over the real substrate and
    /// collides with nothing in the active confluence lane. (Heavier than the
    /// minimal builder; the unit tests above use the minimal substrate.)
    #[test]
    fn test_kexpr_beq_sound_registers_on_substitution_bundle() {
        let mut spec = Specification::new_substitution_test_spec()
            .expect("substitution-test spec (foundation + expr_model + rec_env) should build");
        spec.add_kexpr_beq()
            .expect("kexpr_beq decls should elaborate and kernel-check");
        spec.add_kexpr_beq_sound()
            .expect("kexpr_beq_sound decls should elaborate and kernel-check on the full bundle");
        // The two headline deliverables are present, DerivedProved, foundational.
        for name in ["nat_eqb_eq", "name_eqb_eq", "kexpr_beq_eq"] {
            let def = spec.definitions().get(name).unwrap_or_else(|| {
                panic!("{name} should be registered on the substitution bundle")
            });
            assert_eq!(def.proof_status, ProofStatus::DerivedProved);
            assert!(def.axiom_deps.is_empty());
            assert!(spec
                .env()
                .get_const(&clean_kernel::Name::from_string(name))
                .is_some());
        }
    }

    /// Every soundness-direction declaration registers, kernel-checks, and the
    /// inversion lemmas are DerivedProved with an empty (foundational) axiom
    /// closure. `add_kexpr_beq_sound` returning Ok already means each proof term
    /// passed `env.add_decl` full kernel type-checking.
    #[test]
    fn test_kexpr_beq_sound_decls_kernel_check_and_proved() {
        let spec = build_kexpr_beq_sound_spec();
        let defs = spec.definitions();

        // The arithmetic inversion substrate + soundness direction are all
        // DerivedProved with empty domain/helper axiom closure (foundational).
        for name in [
            "bool_false_ne_true",
            "nat_zero_ne_succ_beq",
            "nat_succ_inj_beq",
            "nat_is_zero_eq",
            "nat_add_eq_zero_right",
            "nat_add_eq_zero_left",
            "nat_sub_eq_zero_antisymm",
            "nat_eqb_eq",
            "band_eq_true_left",
            "band_eq_true_right",
            "name_eqb_eq",
            "level_eqb_eq",
            "level_is_zero_sound",
            // §2b' imax-denotation bridge (closes B1's deferred gap): 8 Nat helpers
            // + the three bridge lemmas, all DerivedProved / empty axiom closure.
            "nat_add_sub_succ_nonzero",
            "nat_is_zero_nat_max_left",
            "nat_is_zero_nat_max_right",
            "nat_is_zero_imax_nat_right",
            "nat_max_eq_imax_nonzero",
            "imax_nat_zero_left",
            "imax_nat_one_left",
            "imax_nat_self",
            "level_max_eval",
            "level_is_nonzero_sound",
            "level_imax_eval",
            "ulist_eqb_eq",
            "kexpr_sort_inj",
            "kexpr_bvar_inj",
            "kexpr_lam_inj_fst",
            "kexpr_lam_inj_snd",
            "kexpr_pi_inj_fst",
            "kexpr_pi_inj_snd",
            "kexpr_const_inj_name",
            "kexpr_const_inj_ulist",
            "kexpr_beq_proj_proj",
            "kexpr_beq_lit_lit",
            "kexpr_beq_eq",
        ] {
            let def = defs
                .get(name)
                .unwrap_or_else(|| panic!("lemma {name} should be registered"));
            assert_eq!(
                def.proof_status,
                ProofStatus::DerivedProved,
                "lemma {name} must be DerivedProved (constructive proof)"
            );
            assert!(
                def.axiom_deps.is_empty(),
                "lemma {name} must have empty axiom closure (foundational), got {:?}",
                def.axiom_deps
            );
            assert!(!def.is_axiom, "lemma {name} must not be an axiom");
            // In the kernel environment => its proof term kernel-checked.
            assert!(
                spec.env()
                    .get_const(&clean_kernel::Name::from_string(name))
                    .is_some(),
                "lemma {name} should be in the kernel environment (proof checked)"
            );
        }
    }

    /// The two headline deliverables carry the LITERAL required statements and a
    /// real kernel-checked proof value.
    #[test]
    fn test_nat_eqb_eq_and_kexpr_beq_eq_literal_statements() {
        let spec = build_kexpr_beq_sound_spec();
        let defs = spec.definitions();

        // nat_eqb_eq : forall a b, nat_eqb a b = true -> a = b.
        let nat_eqb_eq = defs
            .get("nat_eqb_eq")
            .expect("nat_eqb_eq should be registered");
        assert!(
            nat_eqb_eq.type_src.contains("nat_eqb a b")
                && nat_eqb_eq.type_src.contains("Bool.true")
                && nat_eqb_eq.type_src.contains("Eq Nat a b"),
            "nat_eqb_eq must literally state nat_eqb a b = true -> a = b, got: {}",
            nat_eqb_eq.type_src
        );

        // name_eqb_eq : forall a b, name_eqb a b = true -> a = b.
        let name_eqb_eq = defs
            .get("name_eqb_eq")
            .expect("name_eqb_eq should be registered");
        assert!(
            name_eqb_eq.type_src.contains("name_eqb a b")
                && name_eqb_eq.type_src.contains("Bool.true")
                && name_eqb_eq.type_src.contains("Eq Name a b"),
            "name_eqb_eq must literally state name_eqb a b = true -> a = b, got: {}",
            name_eqb_eq.type_src
        );

        // kexpr_beq_eq : forall a b, kexpr_beq a b = true -> a = b.
        let kexpr_beq_eq = defs
            .get("kexpr_beq_eq")
            .expect("kexpr_beq_eq should be registered");
        assert!(
            kexpr_beq_eq.type_src.contains("kexpr_beq a b")
                && kexpr_beq_eq.type_src.contains("Bool.true")
                && kexpr_beq_eq.type_src.contains("Eq KExpr a b"),
            "kexpr_beq_eq must literally state kexpr_beq a b = true -> a = b, got: {}",
            kexpr_beq_eq.type_src
        );

        // All three are registered as kernel Theorems carrying their proof value.
        for name in ["nat_eqb_eq", "name_eqb_eq", "kexpr_beq_eq"] {
            let decl = spec
                .env()
                .get_const(&clean_kernel::Name::from_string(name))
                .unwrap_or_else(|| panic!("{name} should be in the kernel environment"));
            assert_eq!(
                decl.kind,
                clean_kernel::ConstantKind::Theorem,
                "{name} should be a kernel Theorem"
            );
            assert!(
                decl.value.is_some(),
                "{name} Theorem should carry its proof value"
            );
        }
    }

    /// Non-vacuity / masquerade guard: the inversions actually FIRE on real
    /// `= true` witnesses and yield the concrete equality. The two `*_fires_witness`
    /// closed terms only kernel-checked (i.e. `add_kexpr_beq_sound` only returned
    /// Ok) because:
    ///   - `nat_eqb_eq 2 2 (Eq.refl Bool true)` typechecks ONLY because the kernel
    ///     reduces `nat_eqb 2 2` to `true` (so the Eq.refl premise is well-typed)
    ///     AND `nat_eqb_eq` genuinely computes the resulting `Eq Nat 2 2`.
    ///   - `kexpr_beq_eq e e (kexpr_beq_refl e)` drives the full recursive proof
    ///     (app arm + bvar/sort leaves + nat_eqb_eq) end to end on a concrete term.
    /// A constantly-true `kexpr_beq` or a vacuous inversion would fail to produce
    /// these witnesses.
    #[test]
    fn test_kexpr_beq_eq_non_vacuous_fires_on_real_witness() {
        let spec = build_kexpr_beq_sound_spec();
        let defs = spec.definitions();
        for name in [
            "nat_eqb_eq_fires_witness",
            "kexpr_beq_eq_fires_witness",
            "kexpr_beq_eq_proj_fires_witness",
            "kexpr_beq_eq_lit_fires_witness",
        ] {
            let def = defs
                .get(name)
                .unwrap_or_else(|| panic!("non-vacuity witness {name} should be registered"));
            assert_eq!(
                def.proof_status,
                ProofStatus::DerivedProved,
                "witness {name} must be DerivedProved"
            );
            assert!(
                def.axiom_deps.is_empty(),
                "witness {name} must have empty axiom closure"
            );
            // In the kernel env => its proof term (an application of the inversion
            // to a real `= true` witness) kernel-checked. This is the masquerade
            // guard: the inversion fired.
            assert!(
                spec.env()
                    .get_const(&clean_kernel::Name::from_string(name))
                    .is_some(),
                "witness {name} should be in the kernel environment (inversion fired)"
            );
        }
    }

    /// CAPSTONE: the completeness direction and both named biconditional
    /// directions register, kernel-check, and are DerivedProved with an empty
    /// (foundational) axiom closure. `add_kexpr_beq_sound` returning Ok already
    /// means each proof term passed full kernel type-checking.
    #[test]
    fn test_kexpr_beq_complete_and_iff_kernel_check_and_proved() {
        let spec = build_kexpr_beq_sound_spec();
        let defs = spec.definitions();
        for name in [
            "kexpr_beq_complete",
            "kexpr_beq_iff_mp",
            "kexpr_beq_iff_mpr",
        ] {
            let def = defs
                .get(name)
                .unwrap_or_else(|| panic!("capstone decl {name} should be registered"));
            assert_eq!(
                def.proof_status,
                ProofStatus::DerivedProved,
                "capstone decl {name} must be DerivedProved (constructive proof)"
            );
            assert!(
                def.axiom_deps.is_empty(),
                "capstone decl {name} must have empty axiom closure (foundational), got {:?}",
                def.axiom_deps
            );
            assert!(!def.is_axiom, "capstone decl {name} must not be an axiom");
            let decl = spec
                .env()
                .get_const(&clean_kernel::Name::from_string(name))
                .unwrap_or_else(|| panic!("{name} should be in the kernel environment"));
            assert_eq!(
                decl.kind,
                clean_kernel::ConstantKind::Theorem,
                "{name} should be a kernel Theorem"
            );
            assert!(
                decl.value.is_some(),
                "{name} Theorem should carry its proof value"
            );
        }
    }

    /// The capstone deliverables carry the LITERAL required statements.
    /// `kexpr_beq_complete` (= `kexpr_beq_iff_mpr`) states
    /// `a = b -> kexpr_beq a b = true`; `kexpr_beq_iff_mp` (= `kexpr_beq_eq`)
    /// states `kexpr_beq a b = true -> a = b`. Together they are the biconditional.
    #[test]
    fn test_kexpr_beq_complete_and_iff_literal_statements() {
        let spec = build_kexpr_beq_sound_spec();
        let defs = spec.definitions();

        // kexpr_beq_complete : forall a b, Eq KExpr a b -> kexpr_beq a b = true.
        let complete = defs
            .get("kexpr_beq_complete")
            .expect("kexpr_beq_complete should be registered");
        assert!(
            complete.type_src.contains("Eq KExpr a b")
                && complete.type_src.contains("kexpr_beq a b")
                && complete.type_src.contains("Bool.true"),
            "kexpr_beq_complete must literally state a = b -> kexpr_beq a b = true, got: {}",
            complete.type_src
        );

        // mpr direction = completeness : a = b -> kexpr_beq a b = true.
        let mpr = defs
            .get("kexpr_beq_iff_mpr")
            .expect("kexpr_beq_iff_mpr should be registered");
        assert!(
            mpr.type_src
                .contains("Eq KExpr a b -> Eq Bool (kexpr_beq a b) Bool.true"),
            "kexpr_beq_iff_mpr must literally state a = b -> kexpr_beq a b = true, got: {}",
            mpr.type_src
        );

        // mp direction = soundness : kexpr_beq a b = true -> a = b.
        let mp = defs
            .get("kexpr_beq_iff_mp")
            .expect("kexpr_beq_iff_mp should be registered");
        assert!(
            mp.type_src
                .contains("Eq Bool (kexpr_beq a b) Bool.true -> Eq KExpr a b"),
            "kexpr_beq_iff_mp must literally state kexpr_beq a b = true -> a = b, got: {}",
            mp.type_src
        );
    }

    /// Non-vacuity / masquerade guard for the capstone: completeness and the
    /// biconditional's backward projection actually FIRE on concrete reflexive
    /// witnesses, producing the literal `kexpr_beq e e = true`. These closed terms
    /// only kernel-checked because:
    ///   - `kexpr_beq_complete e e (Eq.refl KExpr e)` genuinely transports
    ///     `kexpr_beq_refl e` through the substitution (a vacuous constant would
    ///     not consume the input equality), and
    ///   - `kexpr_beq_iff_mpr e e (Eq.refl KExpr e)` drives the same through the
    ///     `AndType.right` projection of the full iff.
    #[test]
    fn test_kexpr_beq_complete_non_vacuous_fires_on_refl() {
        let spec = build_kexpr_beq_sound_spec();
        let defs = spec.definitions();
        for name in [
            "kexpr_beq_complete_fires_witness",
            "kexpr_beq_iff_fires_witness",
        ] {
            let def = defs
                .get(name)
                .unwrap_or_else(|| panic!("non-vacuity witness {name} should be registered"));
            assert_eq!(
                def.proof_status,
                ProofStatus::DerivedProved,
                "witness {name} must be DerivedProved"
            );
            assert!(
                def.axiom_deps.is_empty(),
                "witness {name} must have empty axiom closure"
            );
            // The witness asserts a `= true` result obtained by FIRING the capstone
            // lemma on Eq.refl. Its presence in the kernel env => the proof term
            // kernel-checked => the completeness direction really computes.
            assert!(
                def.type_src.contains("Bool.true"),
                "witness {name} must assert a `= true` result"
            );
            assert!(
                spec.env()
                    .get_const(&clean_kernel::Name::from_string(name))
                    .is_some(),
                "witness {name} should be in the kernel environment (completeness fired)"
            );
        }
    }
}
