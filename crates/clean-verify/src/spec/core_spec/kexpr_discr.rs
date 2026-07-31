// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Generic `KExpr` constructor discrimination, and the rigid-normal-form
//! reduction inversions it unlocks.
//!
//! ## Why a tag rather than more `_ne_` lemmas
//!
//! The tree has a hand-written discrimination family — `app_ne_lam`,
//! `pi_ne_proj`, `sort_ne_app` and so on (`expr_model_discrimination*.rs`) —
//! but it covers only 23 of the 72 ordered pairs, and in particular has
//! **nothing for `lit` or `bvar`**, which are exactly the two heads the
//! completeness capstone still needs. Filling the family in by hand means
//! sixteen more near-identical lemmas.
//!
//! Instead: one tag function and one absurdity eliminator cover all 72 pairs.
//! `kexpr_tag` sends each constructor to a distinct numeral, and
//!
//! ```text
//! kexpr_discr_t : Eq KExpr x y -> nat_eqb (kexpr_tag x) (kexpr_tag y) = false -> C
//! ```
//!
//! discharges any goal from a constructor mismatch. At a concrete pair of
//! distinct constructors the tags *compute*, so the second premise is always
//! `Eq.refl Bool Bool.false` — the caller writes nothing. This is the same
//! shape `bool_false_ne_true` uses for `Bool`, lifted to a nine-constructor
//! type.
//!
//! Both universes are provided (`_t` into `Type`, `_p` into `Prop`) as a
//! matched pair, following `bool_false_ne_true` / `bool_false_ne_true_t`. That
//! pairing is not decoration: a `C : Type` eliminator cannot discharge an `Eq`
//! goal, which is a universe conflict rather than a coercion, and getting it
//! wrong costs a full spec build to discover.
//!
//! ## The inversions
//!
//! `lit` and `bvar` are **rigid normal forms**: no `par_reduces_cd`
//! constructor can move them.
//!
//! - The nine structural constructors (`beta`, `app`, `lam`, `pi`, `forall_`,
//!   `let_`, `let_cong`, `proj`, and `refl`'s non-matching instances) conclude
//!   at a *different* head, so `kexpr_discr_p` kills them.
//! - `iota` and `delta` carry `iota_step` / `delta_step`, both of which look up
//!   `kexpr_const_name (kapp_fn e)`. For a `lit` or a `bvar` that is `none`
//!   definitionally, so `iota_step_head_none_absurd` /
//!   `delta_step_head_none_absurd` kill them with `Eq.refl` as the head
//!   premise.
//! - `refl` is the only survivor, and it gives exactly the conclusion.
//!
//! Lifting single-step to `par_reduces_cd_star` is then an induction that never
//! leaves the term.
//!
//! These are two of the three head-rigidity inversions the completeness
//! capstone needs; `proj` is the third and is genuinely harder, since `proj`
//! *can* reduce inside its subject.
//!
//! `DerivedProved` throughout, empty axiom closures.

use crate::spec::error::SpecError;
use crate::spec::Specification;

/// `(constructor form, tag)` for each of the nine `KExpr` constructors, in
/// recursor minor-premise order. The tag values only have to be distinct.
const TAG_ARMS: [(&str, &str); 9] = [
    ("(fun (_x : Level) => ", "Nat.zero"),
    ("(fun (_x : Nat) => ", "(Nat.succ Nat.zero)"),
    (
        "(fun (_x : KExpr) (_y : KExpr) (_ : Nat) (_ : Nat) => ",
        "(Nat.succ (Nat.succ Nat.zero))",
    ),
    (
        "(fun (_x : KExpr) (_y : KExpr) (_ : Nat) (_ : Nat) => ",
        "(Nat.succ (Nat.succ (Nat.succ Nat.zero)))",
    ),
    (
        "(fun (_x : KExpr) (_y : KExpr) (_ : Nat) (_ : Nat) => ",
        "(Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))",
    ),
    (
        "(fun (_x : Name) (_y : ListType Level) => ",
        "(Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))",
    ),
    (
        "(fun (_x : KExpr) (_y : KExpr) (_z : KExpr) (_ : Nat) (_ : Nat) (_ : Nat) => ",
        "(Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))))",
    ),
    (
        "(fun (_s : Name) (_i : Nat) (_sub : KExpr) (_ : Nat) => ",
        "(Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))))",
    ),
    (
        "(fun (_w : Nat) => ",
        "(Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))))))",
    ),
];

/// The `par_reduces_cd` constructors whose conclusion pins a specific head:
/// `(payload binders, recursive premise (source, target) pairs, pinned source
/// form)`.
///
/// The recursor's minor premise for a constructor with `n` recursive premises
/// binds **all `n` proofs and then all `n` induction hypotheses** — the IHs are
/// the motive applied to each premise's endpoints. Omitting them shifts every
/// later binder, which is how the first version of this module was rejected;
/// keeping the pairs here means the two binder groups are generated from one
/// source and cannot drift apart.
///
/// `refl`, `iota` and `delta` are handled separately: `refl` is the surviving
/// arm and has no recursive premise, and `iota` / `delta` carry `iota_step` /
/// `delta_step`, which are not recursive occurrences and so contribute no IH.
pub(super) const CD_STRUCTURAL_ARMS: [(&str, &[(&str, &str)], &str, &str); 8] = [
    (
        "(bA : KExpr) (bA2 : KExpr) (bbody : KExpr) (bbody2 : KExpr) (barg : KExpr) \
         (barg2 : KExpr)",
        &[("bA", "bA2"), ("bbody", "bbody2"), ("barg", "barg2")],
        "(KExpr.app (KExpr.lam bA bbody) barg)",
        "(instantiate bbody2 barg2)",
    ),
    (
        "(af : KExpr) (af2 : KExpr) (aa : KExpr) (aa2 : KExpr)",
        &[("af", "af2"), ("aa", "aa2")],
        "(KExpr.app af aa)",
        "(KExpr.app af2 aa2)",
    ),
    (
        "(lty : KExpr) (lty2 : KExpr) (lbody : KExpr) (lbody2 : KExpr)",
        &[("lty", "lty2"), ("lbody", "lbody2")],
        "(KExpr.lam lty lbody)",
        "(KExpr.lam lty2 lbody2)",
    ),
    (
        "(pdom : KExpr) (pdom2 : KExpr) (pbody : KExpr) (pbody2 : KExpr)",
        &[("pdom", "pdom2"), ("pbody", "pbody2")],
        "(KExpr.pi pdom pbody)",
        "(KExpr.pi pdom2 pbody2)",
    ),
    (
        "(qdom : KExpr) (qdom2 : KExpr) (qbody : KExpr) (qbody2 : KExpr)",
        &[("qdom", "qdom2"), ("qbody", "qbody2")],
        "(KExpr.forall_ qdom qbody)",
        "(KExpr.forall_ qdom2 qbody2)",
    ),
    (
        "(zty : KExpr) (zty2 : KExpr) (zval : KExpr) (zval2 : KExpr) (zbody : KExpr) \
         (zbody2 : KExpr)",
        &[("zty", "zty2"), ("zval", "zval2"), ("zbody", "zbody2")],
        "(KExpr.let_ zty zval zbody)",
        "(instantiate zbody2 zval2)",
    ),
    (
        "(cty : KExpr) (cty2 : KExpr) (cval : KExpr) (cval2 : KExpr) (cbody : KExpr) \
         (cbody2 : KExpr)",
        &[("cty", "cty2"), ("cval", "cval2"), ("cbody", "cbody2")],
        "(KExpr.let_ cty cval cbody)",
        "(KExpr.let_ cty2 cval2 cbody2)",
    ),
    (
        "(ps : Name) (pi2 : Nat) (psub : KExpr) (psub2 : KExpr)",
        &[("psub", "psub2")],
        "(KExpr.proj ps pi2 psub)",
        "(KExpr.proj ps pi2 psub2)",
    ),
];

impl Specification {
    /// Constructor tag, generic discrimination, and the `lit` / `bvar`
    /// reduction inversions.
    pub(super) fn add_kexpr_discr(&mut self) -> Result<(), SpecError> {
        self.add_kexpr_tag()?;
        self.add_kexpr_discriminators()?;
        self.add_rigid_inversions()?;
        Ok(())
    }

    fn add_kexpr_tag(&mut self) -> Result<(), SpecError> {
        let mut arms = String::new();
        for (binders, tag) in TAG_ARMS {
            arms.push_str(binders);
            arms.push_str(tag);
            arms.push_str(") ");
        }
        self.add_recursive_def(
            &format!(
                "def kexpr_tag (e : KExpr) : Nat := \
                 KExpr.rec (fun (_ : KExpr) => Nat) {arms}e"
            ),
            "kexpr_tag e: the index of e's head constructor, 0..8 in recursor order. Exists so \
             that constructor discrimination is ONE lemma instead of 72: the hand-written \
             _ne_ family in expr_model_discrimination covers 23 ordered pairs and has nothing \
             for lit or bvar, which are precisely the heads the completeness capstone needs. \
             DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }

    /// The two universe variants of the discriminator.
    fn add_kexpr_discriminators(&mut self) -> Result<(), SpecError> {
        // From x = y, transporting `nat_eqb_refl (kexpr_tag x)` along the
        // equation gives `nat_eqb (tag x) (tag y) = true`, contradicting the
        // caller's `= false`.
        let body = |absurd: &str| {
            format!(
                "{absurd} C \
                 (Eq.trans Bool Bool.false (nat_eqb (kexpr_tag x) (kexpr_tag y)) Bool.true \
                 (Eq.symm Bool (nat_eqb (kexpr_tag x) (kexpr_tag y)) Bool.false hne) \
                 (Eq.substType KExpr \
                 (fun (z : KExpr) => Eq Bool (nat_eqb (kexpr_tag x) (kexpr_tag z)) Bool.true) \
                 x y h (nat_eqb_refl (kexpr_tag x))))"
            )
        };

        self.add_recursive_def(
            &format!(
                "def kexpr_discr_t (C : Type) (x : KExpr) (y : KExpr) (h : Eq KExpr x y) \
                 (hne : Eq Bool (nat_eqb (kexpr_tag x) (kexpr_tag y)) Bool.false) : C := \
                 {}",
                body("bool_false_ne_true_t")
            ),
            "kexpr_discr_t: GENERIC constructor discrimination into Type — distinct head \
             constructors cannot be equal, so any goal follows. At a concrete pair the tags \
             compute, making the mismatch premise literally `Eq.refl Bool Bool.false`, so callers \
             supply nothing. One lemma in place of the 72 ordered _ne_ pairs. DerivedProved, zero \
             axiom_deps.",
        )?;

        self.add_recursive_def(
            &format!(
                "def kexpr_discr_p (C : Prop) (x : KExpr) (y : KExpr) (h : Eq KExpr x y) \
                 (hne : Eq Bool (nat_eqb (kexpr_tag x) (kexpr_tag y)) Bool.false) : C := \
                 {}",
                body("bool_false_ne_true")
            ),
            "kexpr_discr_p: the Prop twin of kexpr_discr_t. Supplied as a matched pair because a \
             Type-valued eliminator cannot discharge an Eq goal — that is a universe conflict, \
             not a coercion, and it costs a full spec build to find. Same discipline as \
             bool_false_ne_true / bool_false_ne_true_t. DerivedProved, zero axiom_deps.",
        )?;

        Ok(())
    }

    /// The eleven `par_reduces_cd` minor premises for a rigidity inversion at
    /// the given payload binder and constructor form.
    ///
    /// Split out so the shape tests can count binder groups. Each structural
    /// arm binds its payload, then **all** its recursive proofs, then **all**
    /// their induction hypotheses; omitting the IH group shifts every later
    /// binder, which is precisely how the first version of this module was
    /// rejected by the kernel 1277 seconds into a build.
    fn rigid_inv_arms(binder: &str, form: &str) -> String {
        // refl: the source equation IS the goal.
        let refl_arm = format!("(fun (e0 : KExpr) {binder} (heq : Eq KExpr e0 {form}) => heq) ");

        let structural = |idx: usize| {
            let (payload_binders, rec_pairs, src, tgt) = CD_STRUCTURAL_ARMS[idx];
            let mut proofs = String::new();
            let mut ihs = String::new();
            for (from, to) in rec_pairs {
                proofs.push_str(&format!("(_ : par_reduces_cd env {from} {to}) "));
                ihs.push_str(&format!(
                    "(_ : forall {binder}, Eq KExpr {from} {form} -> Eq KExpr {to} {form}) "
                ));
            }
            format!(
                "(fun {payload_binders} {proofs}{ihs}{binder} \
                 (heq : Eq KExpr {src} {form}) => \
                 kexpr_discr_p (Eq KExpr {tgt} {form}) {src} {form} heq \
                 (Eq.refl Bool Bool.false)) "
            )
        };

        // iota and delta: the head-name lookup is none on a rigid form, and
        // neither premise is a recursive occurrence, so neither contributes an
        // induction hypothesis.
        let iota_arm = format!(
            "(fun (ie : KExpr) (ie2 : KExpr) (hst : iota_step (red_rec env) ie ie2) \
             {binder} (heq : Eq KExpr ie {form}) => \
             iota_step_head_none_absurd (red_rec env) {form} ie2 \
             (Eq KExpr ie2 {form}) (Eq.refl (OptionType Name) (OptionType.none Name)) \
             (Eq.substType KExpr (fun (z : KExpr) => iota_step (red_rec env) z ie2) \
             ie {form} heq hst)) "
        );
        let delta_arm = format!(
            "(fun (de : KExpr) (de2 : KExpr) (hst : delta_step (red_def env) de de2) \
             {binder} (heq : Eq KExpr de {form}) => \
             delta_step_head_none_absurd (red_def env) {form} de2 \
             (Eq KExpr de2 {form}) (Eq.refl (OptionType Name) (OptionType.none Name)) \
             (Eq.substType KExpr (fun (z : KExpr) => delta_step (red_def env) z de2) \
             de {form} heq hst)) "
        );

        // MINOR PREMISES MUST FOLLOW THE DECLARATION ORDER of par_reduces_cd
        // (par_reduces_cd.rs:187-198), which is
        //
        //   refl beta app lam pi forall_ let_ IOTA DELTA let_cong proj
        //
        // Note that iota and delta sit at positions 8 and 9, BEFORE let_cong
        // and proj. Emitting all eight structural arms and then the two step
        // arms — the obvious grouping, and the first version of this module —
        // transposes the last four premises. The arm COUNT is still 11, so a
        // count check cannot catch it; `test_rigid_inv_arms_declaration_order`
        // pins the sequence itself.
        let mut arms = refl_arm;
        for idx in 0..6 {
            arms.push_str(&structural(idx)); // beta app lam pi forall_ let_
        }
        arms.push_str(&iota_arm);
        arms.push_str(&delta_arm);
        arms.push_str(&structural(6)); // let_cong
        arms.push_str(&structural(7)); // proj
        arms
    }

    /// `lit` and `bvar` are rigid: nothing reduces them.
    fn add_rigid_inversions(&mut self) -> Result<(), SpecError> {
        for (label, form, binder, payload) in [
            ("lit", "(KExpr.lit lw)", "(lw : Nat)", "lw"),
            ("bvar", "(KExpr.bvar bi)", "(bi : Nat)", "bi"),
        ] {
            let _ = payload;
            let motive = format!(
                "fun (p : KExpr) (q : KExpr) (_h : par_reduces_cd env p q) => \
                 forall {binder}, Eq KExpr p {form} -> Eq KExpr q {form}"
            );

            let arms = Self::rigid_inv_arms(binder, form);

            self.add_recursive_def(
                &format!(
                    "def par_reduces_cd_{label}_inv_eq (env : RedEnv) (p : KExpr) (q : KExpr) \
                     (h : par_reduces_cd env p q) : \
                     forall {binder}, Eq KExpr p {form} -> Eq KExpr q {form} := \
                     par_reduces_cd.rec env ({motive}) {arms}p q h"
                ),
                &format!(
                    "par_reduces_cd_{label}_inv_eq: {label} is a RIGID NORMAL FORM for parallel \
                     reduction — one step out of a {label} lands back on the same {label}. The \
                     eight head-pinning constructors conclude at a different head and die by \
                     kexpr_discr_p; iota and delta look up kexpr_const_name (kapp_fn e), which is \
                     none on a {label} definitionally, so their head-none absurdity lemmas apply \
                     with Eq.refl as the premise; refl is the only survivor and gives exactly the \
                     conclusion. One of the head-rigidity inversions the completeness capstone \
                     needs. DerivedProved, zero axiom_deps."
                ),
            )?;

            self.add_recursive_def(
                &format!(
                    "def par_reduces_cd_star_{label}_inv_eq (env : RedEnv) {binder} (t : KExpr) \
                     (h : par_reduces_cd_star env {form} t) : Eq KExpr t {form} := \
                     par_reduces_cd_star.rec env \
                     (fun (p : KExpr) (q : KExpr) (_h : par_reduces_cd_star env p q) => \
                     forall {binder}, Eq KExpr p {form} -> Eq KExpr q {form}) \
                     (fun (e0 : KExpr) {binder} (heq : Eq KExpr e0 {form}) => heq) \
                     (fun (e0 : KExpr) (e1 : KExpr) (e2 : KExpr) \
                     (hstep : par_reduces_cd env e0 e1) \
                     (_hstar : par_reduces_cd_star env e1 e2) \
                     (ih : forall {binder}, Eq KExpr e1 {form} -> Eq KExpr e2 {form}) \
                     {binder} (heq : Eq KExpr e0 {form}) => \
                     ih {payload} (par_reduces_cd_{label}_inv_eq env e0 e1 hstep {payload} heq)) \
                     {form} t h {payload} (Eq.refl KExpr {form})"
                ),
                &format!(
                    "par_reduces_cd_star_{label}_inv_eq: MULTI-STEP rigidity — anything reachable \
                     from a {label} by parallel reduction IS that {label}. Induction on the \
                     closure, each step held in place by the single-step inversion. Joins the \
                     landed sort / lam / pi / neutral-app / dead-const star inversions; with \
                     these two only proj remains, and proj is the hard one because it genuinely \
                     reduces inside its subject. DerivedProved, zero axiom_deps."
                ),
            )?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `par_reduces_cd` has eleven constructors, so the recursor takes eleven
    /// minor premises. Miscounting shifts the scrutinee arguments.
    #[test]
    fn test_rigid_inv_arms_has_eleven_minor_premises() {
        let arms = Specification::rigid_inv_arms("(lw : Nat)", "(KExpr.lit lw)");
        let minors = arms.matches("(fun ").count() - arms.matches("(fun (z : KExpr)").count();
        assert_eq!(
            minors, 11,
            "par_reduces_cd has 11 constructors: refl, beta, app, lam, pi, forall_, let_, \
             iota, delta, let_cong, proj — got {minors} minor premises"
        );
    }

    /// THE REGRESSION GUARD. Every recursive premise contributes BOTH a proof
    /// binder and an induction-hypothesis binder. The first version of this
    /// module bound only the proofs; the kernel rejected it 1277 seconds into a
    /// spec build with a shape mismatch on the `beta` arm.
    ///
    /// beta 3 + app 2 + lam 2 + pi 2 + forall_ 2 + let_ 3 + let_cong 3 +
    /// proj 1 = 18 recursive premises, hence 18 of each binder.
    #[test]
    fn test_rigid_inv_arms_binds_an_ih_for_every_recursive_premise() {
        let total: usize = CD_STRUCTURAL_ARMS
            .iter()
            .map(|(_, pairs, _, _)| pairs.len())
            .sum();
        assert_eq!(
            total, 18,
            "expected 18 recursive premises across the eight arms"
        );

        let arms = Specification::rigid_inv_arms("(lw : Nat)", "(KExpr.lit lw)");
        let proofs = arms.matches("(_ : par_reduces_cd env ").count();
        let ihs = arms.matches("(_ : forall (lw : Nat), Eq KExpr ").count();
        assert_eq!(proofs, total, "one proof binder per recursive premise");
        assert_eq!(
            ihs, total,
            "one induction-hypothesis binder per recursive premise — omitting this group is \
             what the kernel rejected"
        );
    }

    /// The two step arms carry `iota_step` / `delta_step`, which are not
    /// recursive occurrences, so they must NOT gain induction hypotheses.
    #[test]
    fn test_rigid_inv_arms_step_arms_have_no_induction_hypotheses() {
        let arms = Specification::rigid_inv_arms("(bi : Nat)", "(KExpr.bvar bi)");
        assert!(arms.contains("iota_step_head_none_absurd (red_rec env)"));
        assert!(arms.contains("delta_step_head_none_absurd (red_def env)"));
        assert_eq!(
            arms.matches("(hst : ").count(),
            2,
            "exactly two step arms, each binding its step premise and no IH"
        );
    }

    #[test]
    fn test_rigid_inv_arms_parens_balanced() {
        for (binder, form) in [
            ("(lw : Nat)", "(KExpr.lit lw)"),
            ("(bi : Nat)", "(KExpr.bvar bi)"),
        ] {
            let arms = Specification::rigid_inv_arms(binder, form);
            let mut depth: i64 = 0;
            for ch in arms.chars() {
                match ch {
                    '(' => depth += 1,
                    ')' => depth -= 1,
                    _ => {}
                }
                assert!(depth >= 0, "close paren before its open in {form}");
            }
            assert_eq!(depth, 0, "arms for {form} must be paren-balanced");
        }
    }

    /// THE ORDER GUARD. A recursor's minor premises must follow the
    /// constructor DECLARATION order, which for par_reduces_cd
    /// (par_reduces_cd.rs:187-198) is
    ///
    ///   refl beta app lam pi forall_ let_ iota delta let_cong proj
    ///
    /// iota and delta sit at positions 8 and 9, BEFORE let_cong and proj. The
    /// first version of this module emitted all eight structural arms and then
    /// the two step arms, transposing the last four premises. The arm count was
    /// still 11, so no count check could see it — this pins the sequence.
    #[test]
    fn test_rigid_inv_arms_declaration_order() {
        let arms = Specification::rigid_inv_arms("(lw : Nat)", "(KExpr.lit lw)");
        // One landmark per arm, in declaration order.
        let landmarks = [
            "(fun (e0 : KExpr)",                     // refl
            "(KExpr.app (KExpr.lam bA bbody) barg)", // beta
            "(KExpr.app af aa)",                     // app
            "(KExpr.lam lty lbody)",                 // lam
            "(KExpr.pi pdom pbody)",                 // pi
            "(KExpr.forall_ qdom qbody)",            // forall_
            "(KExpr.let_ zty zval zbody)",           // let_
            "iota_step_head_none_absurd",            // iota
            "delta_step_head_none_absurd",           // delta
            "(KExpr.let_ cty cval cbody)",           // let_cong
            "(KExpr.proj ps pi2 psub)",              // proj
        ];
        let mut cursor = 0usize;
        for (position, mark) in landmarks.iter().enumerate() {
            let found = arms[cursor..].find(mark).unwrap_or_else(|| {
                panic!("minor premise {position} ({mark}) missing or out of order")
            });
            cursor += found + mark.len();
        }
    }

    /// THE GOAL GUARD. In each absurd arm the recursor's goal is the motive at
    /// the constructor's TARGET, not at its source: the `beta` arm must prove
    /// `Eq KExpr (instantiate body' arg') (lit lw)`, while its hypothesis is
    /// about `app (lam A body) arg`. `kexpr_discr_p` produces ANY `C` from the
    /// absurd equation, so passing the source equation as `C` typechecks
    /// locally and then fails to match the arm — which is exactly how the
    /// second version of this module was rejected, 1280 seconds in.
    ///
    /// So: the discriminator's `C` must name the arm's target, and every arm's
    /// source and target must actually differ.
    #[test]
    fn test_rigid_inv_arms_discriminate_into_the_target_equation() {
        let form = "(KExpr.lit lw)";
        let arms = Specification::rigid_inv_arms("(lw : Nat)", form);
        for (_, _, src, tgt) in CD_STRUCTURAL_ARMS {
            assert_ne!(
                src, tgt,
                "an arm whose source and target coincide would hide this error"
            );
            assert!(
                arms.contains(&format!("kexpr_discr_p (Eq KExpr {tgt} {form})")),
                "arm with target {tgt} must discriminate INTO its target equation, not its \
                 source equation"
            );
            assert!(
                !arms.contains(&format!("kexpr_discr_p (Eq KExpr {src} {form})")),
                "arm with source {src} must not use the source equation as the goal"
            );
        }
    }

    /// All nine tags must be distinct, or discrimination proves nothing.
    #[test]
    fn test_kexpr_tags_are_pairwise_distinct() {
        let tags: Vec<&str> = TAG_ARMS.iter().map(|(_, t)| *t).collect();
        for (i, a) in tags.iter().enumerate() {
            for b in tags.iter().skip(i + 1) {
                assert_ne!(a, b, "kexpr_tag must be injective on constructors");
            }
        }
        assert_eq!(tags.len(), 9);
    }
}
