// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Fuel monotonicity for the structural conversion algorithm.
//!
//! The completeness capstone compares two terms by recursing into their
//! components, and the components come back with *different* fuels. To assemble
//! a single acceptance for the composite they must all be raised to a common
//! bound, which is what this module supplies:
//!
//! ```text
//! def_eq_struct_mono : (forall x y, cmp1 x y = true -> cmp2 x y = true)
//!                      -> def_eq_struct cmp1 a b = true -> def_eq_struct cmp2 a b = true
//! def_eq_fuel_succ_mono : def_eq_fuel the_red_env k a b = true
//!                      -> def_eq_fuel the_red_env (k+1) a b = true
//! def_eq_fuel_le : Le k m -> def_eq_fuel the_red_env k a b = true
//!                      -> def_eq_fuel the_red_env m a b = true
//! ```
//!
//! `def_eq_struct_mono` is the same 9x9 double `KExpr.rec` as
//! `def_eq_struct_sound`, sharing its constructor tables, but the four leaf
//! arms are *lighter*: `sort` / `bvar` / `const` / `lit` compare their payloads
//! with `level_eqb` / `nat_eqb` / `name_eqb` / `ulist_eqb` and never touch the
//! comparator at all, so at those heads the two grids are literally the same
//! Boolean and the hypothesis passes straight through. Only the five recursive
//! heads do work, and each is `band_intro` over `hm`-mapped conjuncts.
//!
//! The cross-constructor arms use the **Prop**-CPS `bool_false_ne_true` here,
//! not the `Type`-CPS `bool_false_ne_true_t` that `defeq_struct_sound.rs`
//! needs: the goal there is `DefEq a b`, which lives in `Type`, while the goal
//! here is an `Eq`, which is `Prop`.
//!
//! `def_eq_fuel_succ_mono` is `Nat.rec` on the fuel. Fuel 0 accepts nothing so
//! its case is absurd; at `k+1` the two whnf legs are raised by
//! `whnf_fuel_red_monotone` and the grid by `def_eq_struct_mono` applied to the
//! induction hypothesis, then `def_eq_fuel_of_struct` rebuilds the acceptance
//! one fuel level up. `def_eq_fuel_le` iterates that along `Le.rec`.
//!
//! All at the fixed `the_red_env`, inherited from `def_eq_fuel_of_struct`.
//! `DerivedProved`, empty axiom closures.

use crate::spec::core_spec::defeq_struct_sound::{INNER_BINDERS, INNER_FORMS, INNER_REC_FIELDS};
use crate::spec::error::SpecError;
use crate::spec::Specification;

impl Specification {
    /// Monotonicity of the grid in its comparator, and of the algorithm in its
    /// fuel.
    pub(super) fn add_defeq_fuel_mono(&mut self) -> Result<(), SpecError> {
        self.add_defeq_struct_mono_decl()?;
        self.add_defeq_fuel_mono_decls()?;
        Ok(())
    }

    /// The inner `KExpr.rec` on `b` at a fixed outer form, with the
    /// monotonicity motive.
    fn mono_inner_rec(a_form: &str, arms: &[String; 9]) -> String {
        let motive = |zb: &str| {
            format!(
                "Eq Bool (def_eq_struct cmp1 {a_form} {zb}) Bool.true -> \
                 Eq Bool (def_eq_struct cmp2 {a_form} {zb}) Bool.true"
            )
        };
        let mut minors = String::new();
        for (idx, (_ctor, binders)) in INNER_BINDERS.iter().enumerate() {
            let form = INNER_FORMS[idx];
            let mut ih_binders = String::new();
            for field in INNER_REC_FIELDS[idx] {
                ih_binders.push_str(&format!("(_ : {}) ", motive(field)));
            }
            minors.push_str(&format!(
                "(fun {binders} {ih_binders}\
                 (h : Eq Bool (def_eq_struct cmp1 {a_form} {form}) Bool.true) => {arm}) ",
                arm = arms[idx]
            ));
        }
        format!(
            "fun (b : KExpr) => KExpr.rec (fun (zb : KExpr) => {m}) {minors}b",
            m = motive("zb")
        )
    }

    /// A cross-constructor arm: the `cmp1` grid entry is `Bool.false`, so the
    /// hypothesis is absurd. Prop-CPS, because the goal is an `Eq`.
    fn mono_absurd_arm(a_form: &str, b_form: &str) -> String {
        format!("bool_false_ne_true (Eq Bool (def_eq_struct cmp2 {a_form} {b_form}) Bool.true) h")
    }

    /// Present `h` in the reduced `cmp1` form via the matching computation rule.
    fn mono_present(a_form: &str, b_form: &str, rhs: &str, rule: &str) -> String {
        format!(
            "(Eq.substType Bool (fun (x : Bool) => Eq Bool x Bool.true) \
             (def_eq_struct cmp1 {a_form} {b_form}) {rhs} ({rule}) h)"
        )
    }

    fn mono_arms(a_form: &str, diag: usize, arm: String) -> [String; 9] {
        let mut out: [String; 9] =
            std::array::from_fn(|idx| Self::mono_absurd_arm(a_form, INNER_FORMS[idx]));
        out[diag] = arm;
        out
    }

    /// `def_eq_struct_mono`: the grid is monotone in its comparator.
    fn add_defeq_struct_mono_decl(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            &Self::def_eq_struct_mono_src(),
            "def_eq_struct_mono: the 9x9 structural grid is MONOTONE in its comparator — if cmp2 \
             accepts everything cmp1 accepts, then the grid built on cmp2 accepts everything the \
             grid on cmp1 accepts. Same double KExpr.rec as def_eq_struct_sound, sharing its \
             constructor tables; the 72 cross-constructor arms are absurd via bool_false_ne_true \
             (the Prop-CPS no-confusion this time, since the goal is an Eq rather than a DefEq). \
             The four LEAF heads pass the hypothesis straight through: sort / bvar / const / lit \
             compare payloads with level_eqb / nat_eqb / name_eqb / ulist_eqb and never consult \
             the comparator, so the two grids are literally the same Boolean there. Only the \
             five recursive heads do work, each band_intro over hm-mapped conjuncts. This is \
             what lets per-component fuels be raised to a common bound. DerivedProved, zero \
             axiom_deps.",
        )?;
        Ok(())
    }

    /// The `def_eq_struct_mono` source term (split out for the shape tests).
    fn def_eq_struct_mono_src() -> String {
        // Leaf heads: the grid entry does not mention the comparator, so the
        // hypothesis IS the conclusion up to unfolding.
        let leaf = "h".to_string();

        let outer_sort = format!(
            "(fun (n : Level) => {})",
            Self::mono_inner_rec(
                "(KExpr.sort n)",
                &Self::mono_arms("(KExpr.sort n)", 0, leaf.clone())
            )
        );
        let outer_bvar = format!(
            "(fun (i : Nat) => {})",
            Self::mono_inner_rec(
                "(KExpr.bvar i)",
                &Self::mono_arms("(KExpr.bvar i)", 1, leaf.clone())
            )
        );
        let outer_const = format!(
            "(fun (nm : Name) (us : ListType Level) => {})",
            Self::mono_inner_rec(
                "(KExpr.const nm us)",
                &Self::mono_arms("(KExpr.const nm us)", 5, leaf.clone())
            )
        );
        let outer_lit = format!(
            "(fun (w : Nat) => {})",
            Self::mono_inner_rec("(KExpr.lit w)", &Self::mono_arms("(KExpr.lit w)", 8, leaf))
        );

        // Recursive heads: split the cmp1 conjunction, map each conjunct
        // through hm, rebuild with band_intro.
        let app_arm = format!(
            "(fun (hand : Eq Bool (Bool.and (cmp1 f g) (cmp1 a1 c)) Bool.true) => \
             band_intro (cmp2 f g) (cmp2 a1 c) \
             (hm f g (band_eq_true_left (cmp1 f g) (cmp1 a1 c) hand)) \
             (hm a1 c (band_eq_true_right (cmp1 f g) (cmp1 a1 c) hand))) {p}",
            p = Self::mono_present(
                "(KExpr.app f a1)",
                "(KExpr.app g c)",
                "(Bool.and (cmp1 f g) (cmp1 a1 c))",
                "def_eq_struct_app_app cmp1 f a1 g c"
            )
        );
        let outer_app = format!(
            "(fun (f : KExpr) (a1 : KExpr) \
             (_ : forall (b : KExpr), Eq Bool (def_eq_struct cmp1 f b) Bool.true -> \
             Eq Bool (def_eq_struct cmp2 f b) Bool.true) \
             (_ : forall (b : KExpr), Eq Bool (def_eq_struct cmp1 a1 b) Bool.true -> \
             Eq Bool (def_eq_struct cmp2 a1 b) Bool.true) => {})",
            Self::mono_inner_rec(
                "(KExpr.app f a1)",
                &Self::mono_arms("(KExpr.app f a1)", 2, app_arm)
            )
        );

        let binder_arm = |head: &str, rule: &str| {
            format!(
                "(fun (hand : Eq Bool (Bool.and (cmp1 ty1 gt) (cmp1 b1 gb)) Bool.true) => \
                 band_intro (cmp2 ty1 gt) (cmp2 b1 gb) \
                 (hm ty1 gt (band_eq_true_left (cmp1 ty1 gt) (cmp1 b1 gb) hand)) \
                 (hm b1 gb (band_eq_true_right (cmp1 ty1 gt) (cmp1 b1 gb) hand))) {p}",
                p = Self::mono_present(
                    &format!("(KExpr.{head} ty1 b1)"),
                    &format!("(KExpr.{head} gt gb)"),
                    "(Bool.and (cmp1 ty1 gt) (cmp1 b1 gb))",
                    rule
                )
            )
        };
        let binder_outer = |head: &str, diag: usize, arm: String| {
            format!(
                "(fun (ty1 : KExpr) (b1 : KExpr) \
                 (_ : forall (b : KExpr), Eq Bool (def_eq_struct cmp1 ty1 b) Bool.true -> \
                 Eq Bool (def_eq_struct cmp2 ty1 b) Bool.true) \
                 (_ : forall (b : KExpr), Eq Bool (def_eq_struct cmp1 b1 b) Bool.true -> \
                 Eq Bool (def_eq_struct cmp2 b1 b) Bool.true) => {})",
                Self::mono_inner_rec(
                    &format!("(KExpr.{head} ty1 b1)"),
                    &Self::mono_arms(&format!("(KExpr.{head} ty1 b1)"), diag, arm)
                )
            )
        };
        let outer_lam = binder_outer(
            "lam",
            3,
            binder_arm("lam", "def_eq_struct_lam_lam cmp1 ty1 b1 gt gb"),
        );
        let outer_pi = binder_outer(
            "pi",
            4,
            binder_arm("pi", "def_eq_struct_pi_pi cmp1 ty1 b1 gt gb"),
        );

        let let_arm = format!(
            "(fun (hand : Eq Bool (Bool.and (cmp1 lty glt) \
             (Bool.and (cmp1 lv glv) (cmp1 lb glb))) Bool.true) => \
             (fun (hrest : Eq Bool (Bool.and (cmp1 lv glv) (cmp1 lb glb)) Bool.true) => \
             band_intro (cmp2 lty glt) (Bool.and (cmp2 lv glv) (cmp2 lb glb)) \
             (hm lty glt (band_eq_true_left (cmp1 lty glt) \
             (Bool.and (cmp1 lv glv) (cmp1 lb glb)) hand)) \
             (band_intro (cmp2 lv glv) (cmp2 lb glb) \
             (hm lv glv (band_eq_true_left (cmp1 lv glv) (cmp1 lb glb) hrest)) \
             (hm lb glb (band_eq_true_right (cmp1 lv glv) (cmp1 lb glb) hrest)))) \
             (band_eq_true_right (cmp1 lty glt) \
             (Bool.and (cmp1 lv glv) (cmp1 lb glb)) hand)) {p}",
            p = Self::mono_present(
                "(KExpr.let_ lty lv lb)",
                "(KExpr.let_ glt glv glb)",
                "(Bool.and (cmp1 lty glt) (Bool.and (cmp1 lv glv) (cmp1 lb glb)))",
                "def_eq_struct_let_let cmp1 lty lv lb glt glv glb"
            )
        );
        let outer_let = format!(
            "(fun (lty : KExpr) (lv : KExpr) (lb : KExpr) \
             (_ : forall (b : KExpr), Eq Bool (def_eq_struct cmp1 lty b) Bool.true -> \
             Eq Bool (def_eq_struct cmp2 lty b) Bool.true) \
             (_ : forall (b : KExpr), Eq Bool (def_eq_struct cmp1 lv b) Bool.true -> \
             Eq Bool (def_eq_struct cmp2 lv b) Bool.true) \
             (_ : forall (b : KExpr), Eq Bool (def_eq_struct cmp1 lb b) Bool.true -> \
             Eq Bool (def_eq_struct cmp2 lb b) Bool.true) => {})",
            Self::mono_inner_rec(
                "(KExpr.let_ lty lv lb)",
                &Self::mono_arms("(KExpr.let_ lty lv lb)", 6, let_arm)
            )
        );

        // proj: the name/index conjunct is comparator-free and carries over
        // unchanged; only the subject conjunct is mapped.
        let proj_arm = format!(
            "(fun (hand : Eq Bool (Bool.and (Bool.and (name_eqb ps s2) (nat_eqb pidx i2)) \
             (cmp1 psub sub2)) Bool.true) => \
             band_intro (Bool.and (name_eqb ps s2) (nat_eqb pidx i2)) (cmp2 psub sub2) \
             (band_eq_true_left (Bool.and (name_eqb ps s2) (nat_eqb pidx i2)) \
             (cmp1 psub sub2) hand) \
             (hm psub sub2 (band_eq_true_right \
             (Bool.and (name_eqb ps s2) (nat_eqb pidx i2)) (cmp1 psub sub2) hand))) {p}",
            p = Self::mono_present(
                "(KExpr.proj ps pidx psub)",
                "(KExpr.proj s2 i2 sub2)",
                "(Bool.and (Bool.and (name_eqb ps s2) (nat_eqb pidx i2)) (cmp1 psub sub2))",
                "def_eq_struct_proj_proj cmp1 ps pidx psub s2 i2 sub2"
            )
        );
        let outer_proj = format!(
            "(fun (ps : Name) (pidx : Nat) (psub : KExpr) \
             (_ : forall (b : KExpr), Eq Bool (def_eq_struct cmp1 psub b) Bool.true -> \
             Eq Bool (def_eq_struct cmp2 psub b) Bool.true) => {})",
            Self::mono_inner_rec(
                "(KExpr.proj ps pidx psub)",
                &Self::mono_arms("(KExpr.proj ps pidx psub)", 7, proj_arm)
            )
        );

        format!(
            "def def_eq_struct_mono (cmp1 : KExpr -> KExpr -> Bool) \
             (cmp2 : KExpr -> KExpr -> Bool) \
             (hm : forall (x : KExpr) (y : KExpr), Eq Bool (cmp1 x y) Bool.true -> \
             Eq Bool (cmp2 x y) Bool.true) : \
             forall (a : KExpr) (b : KExpr), Eq Bool (def_eq_struct cmp1 a b) Bool.true -> \
             Eq Bool (def_eq_struct cmp2 a b) Bool.true := \
             fun (a : KExpr) => KExpr.rec \
             (fun (za : KExpr) => forall (b : KExpr), \
             Eq Bool (def_eq_struct cmp1 za b) Bool.true -> \
             Eq Bool (def_eq_struct cmp2 za b) Bool.true) \
             {outer_sort} {outer_bvar} {outer_app} {outer_lam} {outer_pi} {outer_const} \
             {outer_let} {outer_proj} {outer_lit} a"
        )
    }

    /// Fuel monotonicity: one step, then along `Le`.
    fn add_defeq_fuel_mono_decls(&mut self) -> Result<(), SpecError> {
        // One fuel level. Nat.rec on the fuel: 0 is absurd (fails closed);
        // succ raises the legs with whnf_fuel_red_monotone and the grid with
        // def_eq_struct_mono applied to the induction hypothesis, then
        // def_eq_fuel_of_struct rebuilds one level up.
        self.add_recursive_def(
            &Self::def_eq_fuel_succ_mono_src(),
            "def_eq_fuel_succ_mono: the structural conversion algorithm is monotone in its fuel \
             by one level — what it accepts at fuel k it still accepts at k+1. Nat.rec on the \
             fuel: fuel 0 accepts nothing so that case is absurd (fail-closed again doing real \
             work); at k+1 the two whnf legs are raised by whnf_fuel_red_monotone and the grid \
             by def_eq_struct_mono applied to the induction hypothesis, after which \
             def_eq_fuel_of_struct rebuilds the acceptance one level up. Needed because the \
             completeness recursion returns per-component fuels that must be unioned. \
             DerivedProved, zero axiom_deps.",
        )?;

        // Along Le, by iterating the single step.
        self.add_recursive_def(
            "def def_eq_fuel_le (k : Nat) (m : Nat) (hle : Le k m) : \
             forall (a : KExpr) (b : KExpr), \
             Eq Bool (def_eq_fuel the_red_env k a b) Bool.true -> \
             Eq Bool (def_eq_fuel the_red_env m a b) Bool.true := \
             Le.rec k (fun (j : Nat) (_hj : Le k j) => forall (a : KExpr) (b : KExpr), \
             Eq Bool (def_eq_fuel the_red_env k a b) Bool.true -> \
             Eq Bool (def_eq_fuel the_red_env j a b) Bool.true) \
             (fun (a : KExpr) (b : KExpr) \
             (h : Eq Bool (def_eq_fuel the_red_env k a b) Bool.true) => h) \
             (fun (j : Nat) (_hj : Le k j) \
             (ihj : forall (a : KExpr) (b : KExpr), \
             Eq Bool (def_eq_fuel the_red_env k a b) Bool.true -> \
             Eq Bool (def_eq_fuel the_red_env j a b) Bool.true) \
             (a : KExpr) (b : KExpr) \
             (h : Eq Bool (def_eq_fuel the_red_env k a b) Bool.true) => \
             def_eq_fuel_succ_mono j a b (ihj a b h)) m hle",
            "def_eq_fuel_le: fuel monotonicity in Le form — an acceptance at fuel k survives \
             raising the fuel to any Le-greater bound. Le.rec iterating def_eq_fuel_succ_mono, \
             the same shape whnf_fuel_red_le uses over whnf_fuel_red_monotone. This is what lets \
             the per-component fuels produced by the completeness recursion be raised to a \
             common bound before they are combined. DerivedProved, zero axiom_deps.",
        )?;

        Ok(())
    }

    /// The `def_eq_fuel_succ_mono` source term (split out so the shape tests
    /// can see which universe variant of the option inversion it uses).
    fn def_eq_fuel_succ_mono_src() -> String {
        "def def_eq_fuel_succ_mono : forall (k : Nat) (a : KExpr) (b : KExpr), \
             Eq Bool (def_eq_fuel the_red_env k a b) Bool.true -> \
             Eq Bool (def_eq_fuel the_red_env (Nat.succ k) a b) Bool.true := \
             Nat.rec (fun (z : Nat) => forall (a : KExpr) (b : KExpr), \
             Eq Bool (def_eq_fuel the_red_env z a b) Bool.true -> \
             Eq Bool (def_eq_fuel the_red_env (Nat.succ z) a b) Bool.true) \
             (fun (a : KExpr) (b : KExpr) \
             (h : Eq Bool (def_eq_fuel the_red_env Nat.zero a b) Bool.true) => \
             bool_false_ne_true \
             (Eq Bool (def_eq_fuel the_red_env (Nat.succ Nat.zero) a b) Bool.true) \
             (Eq.trans Bool Bool.false (def_eq_fuel the_red_env Nat.zero a b) Bool.true \
             (Eq.symm Bool (def_eq_fuel the_red_env Nat.zero a b) Bool.false \
             (def_eq_fuel_zero the_red_env a b)) h)) \
             (fun (j : Nat) \
             (ih : forall (a : KExpr) (b : KExpr), \
             Eq Bool (def_eq_fuel the_red_env j a b) Bool.true -> \
             Eq Bool (def_eq_fuel the_red_env (Nat.succ j) a b) Bool.true) \
             (a : KExpr) (b : KExpr) \
             (h : Eq Bool (def_eq_fuel the_red_env (Nat.succ j) a b) Bool.true) => \
             opt_rec_bool_true_inv_p (whnf_fuel_red the_red_env j a) \
             (fun (nx : KExpr) => OptionType.rec KExpr \
             (fun (_ : OptionType KExpr) => Bool) Bool.false \
             (fun (ny : KExpr) => def_eq_struct (def_eq_fuel the_red_env j) nx ny) \
             (whnf_fuel_red the_red_env j b)) \
             (Eq Bool (def_eq_fuel the_red_env (Nat.succ (Nat.succ j)) a b) Bool.true) \
             (fun (na : KExpr) \
             (hna : Eq (OptionType KExpr) (whnf_fuel_red the_red_env j a) \
             (OptionType.some KExpr na)) \
             (hin : Eq Bool (OptionType.rec KExpr (fun (_ : OptionType KExpr) => Bool) \
             Bool.false \
             (fun (ny : KExpr) => def_eq_struct (def_eq_fuel the_red_env j) na ny) \
             (whnf_fuel_red the_red_env j b)) Bool.true) => \
             opt_rec_bool_true_inv_p (whnf_fuel_red the_red_env j b) \
             (fun (ny : KExpr) => def_eq_struct (def_eq_fuel the_red_env j) na ny) \
             (Eq Bool (def_eq_fuel the_red_env (Nat.succ (Nat.succ j)) a b) Bool.true) \
             (fun (nb : KExpr) \
             (hnb : Eq (OptionType KExpr) (whnf_fuel_red the_red_env j b) \
             (OptionType.some KExpr nb)) \
             (hg : Eq Bool (def_eq_struct (def_eq_fuel the_red_env j) na nb) Bool.true) => \
             def_eq_fuel_of_struct (Nat.succ j) a b na nb \
             (whnf_fuel_red_monotone the_red_env j a na hna) \
             (whnf_fuel_red_monotone the_red_env j b nb hnb) \
             (def_eq_struct_mono (def_eq_fuel the_red_env j) \
             (def_eq_fuel the_red_env (Nat.succ j)) ih na nb hg)) hin) \
             (Eq.substType Bool (fun (x : Bool) => Eq Bool x Bool.true) \
             (def_eq_fuel the_red_env (Nat.succ j) a b) \
             (OptionType.rec KExpr (fun (_ : OptionType KExpr) => Bool) Bool.false \
             (fun (nx : KExpr) => OptionType.rec KExpr \
             (fun (_ : OptionType KExpr) => Bool) Bool.false \
             (fun (ny : KExpr) => def_eq_struct (def_eq_fuel the_red_env j) nx ny) \
             (whnf_fuel_red the_red_env j b)) \
             (whnf_fuel_red the_red_env j a)) \
             (def_eq_fuel_succ the_red_env j a b) h))"
            .to_string()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_def_eq_struct_mono_src_parens_balanced() {
        let src = Specification::def_eq_struct_mono_src();
        let mut depth: i64 = 0;
        for ch in src.chars() {
            match ch {
                '(' => depth += 1,
                ')' => depth -= 1,
                _ => {}
            }
            assert!(depth >= 0, "close paren before its open");
        }
        assert_eq!(depth, 0, "term must be paren-balanced");
    }

    /// 72 cross-constructor arms, as in every other traversal of this grid.
    #[test]
    fn test_def_eq_struct_mono_src_has_exactly_72_absurd_arms() {
        let src = Specification::def_eq_struct_mono_src();
        let absurd = src.matches("bool_false_ne_true (Eq Bool ").count();
        assert_eq!(
            absurd, 72,
            "expected 72 cross-constructor absurd arms, got {absurd}"
        );
    }

    /// The goal here is an `Eq`, which is `Prop`-valued, so the Prop-CPS
    /// no-confusion is the right one — the opposite choice from
    /// `defeq_struct_sound.rs`, whose goal is the `Type`-valued `DefEq`.
    #[test]
    fn test_def_eq_struct_mono_src_uses_prop_cps_no_confusion() {
        let src = Specification::def_eq_struct_mono_src();
        assert_eq!(
            src.matches("bool_false_ne_true_t").count(),
            0,
            "the monotonicity goal is an Eq (Prop), so it must use the Prop-CPS \
             bool_false_ne_true, not the Type-CPS mirror"
        );
    }

    /// Exactly five arms consult `hm`: the recursive heads. If a leaf arm
    /// started routing through the comparator the term would still typecheck
    /// but would be doing pointless work, and — more to the point — if a
    /// recursive arm STOPPED routing through it, the lemma would be false.
    #[test]
    fn test_def_eq_struct_mono_src_maps_exactly_the_recursive_heads() {
        let src = Specification::def_eq_struct_mono_src();
        // app 2, lam 2, pi 2, let_ 3, proj 1 = 10 comparator-mapped conjuncts.
        // Subtract the binding occurrence `(hm : forall …)` in the signature,
        // which matches the same prefix.
        let mapped = src.matches("(hm ").count() - src.matches("(hm :").count();
        assert_eq!(
            mapped, 10,
            "expected 10 hm-mapped conjuncts (app 2 + lam 2 + pi 2 + let 3 + proj 1), got {mapped}"
        );
    }

    /// Ten recursors: one outer plus nine inner.
    #[test]
    fn test_def_eq_struct_mono_src_has_ten_kexpr_recs() {
        let src = Specification::def_eq_struct_mono_src();
        assert_eq!(src.matches("KExpr.rec ").count(), 10);
    }

    /// `def_eq_fuel_succ_mono` proves an EQUATION, and `Eq` is `Prop`-valued,
    /// so it must use the `Prop` variant of the option inversion. Passing an
    /// `Eq` to the `Type` version is a universe conflict, not a coercion — and
    /// it is invisible to `cargo check`, since these are source strings the
    /// Rust compiler never sees. The first version of this module got it wrong
    /// and the kernel caught it 1268 seconds into a spec build; this catches it
    /// in microseconds.
    #[test]
    fn test_def_eq_fuel_succ_mono_uses_the_prop_option_inversion() {
        let src = Specification::def_eq_fuel_succ_mono_src();
        let typed = src.matches("opt_rec_bool_true_inv (").count();
        assert_eq!(
            typed, 0,
            "the goal here is an Eq (Prop): every option inversion must be \
             opt_rec_bool_true_inv_p, never the Type-valued opt_rec_bool_true_inv"
        );
        assert_eq!(
            src.matches("opt_rec_bool_true_inv_p ").count(),
            2,
            "both whnf legs must be inverted"
        );
    }

    /// The successor case must actually raise BOTH legs and the grid — dropping
    /// any one of the three would leave a term that still looks plausible.
    #[test]
    fn test_def_eq_fuel_succ_mono_raises_both_legs_and_the_grid() {
        let src = Specification::def_eq_fuel_succ_mono_src();
        assert_eq!(
            src.matches("whnf_fuel_red_monotone the_red_env j ").count(),
            2,
            "both whnf legs must be raised one fuel level"
        );
        assert!(
            src.contains("def_eq_struct_mono (def_eq_fuel the_red_env j) "),
            "the grid must be raised by def_eq_struct_mono applied to the induction hypothesis"
        );
        assert!(
            src.contains("def_eq_fuel_zero the_red_env a b"),
            "the fuel-0 case must be discharged by fail-closedness, not assumed"
        );
    }

    /// No reserved word may be used as a binder.
    #[test]
    fn test_def_eq_struct_mono_src_has_no_reserved_binders() {
        let src = Specification::def_eq_struct_mono_src();
        for word in [
            "rec", "fun", "let", "match", "with", "where", "do", "from", "by", "have", "show",
            "end", "open", "if", "then", "else",
        ] {
            assert!(
                !src.contains(&format!("({word} :")),
                "reserved word `{word}` used as a binder name"
            );
        }
    }
}
