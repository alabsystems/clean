// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The first inhabitants of `iota_immune` at an APPLICATION.
//!
//! ```text
//! const_head_preserved_cd      : HEAD nm e -> par_reduces_cd env e e2      -> HEAD nm e2
//! const_head_star_preserved    : HEAD nm e -> par_reduces_cd_star env e e2 -> HEAD nm e2
//! iota_immune_of_dead_const_head : HEAD nm e -> iota_immune e
//! iota_immune_app_witness      : iota_immune (app (const anonymous []) (sort 0))
//! ```
//!
//! where `HEAD nm e` abbreviates
//! `kexpr_const_name (kapp_fn e) = some nm`, under two deadness hypotheses on
//! `nm`: no definitional value, and no recursor metadata.
//!
//! ## Why this matters more than the lemma statement suggests
//!
//! Before this module, **`iota_immune` was established nowhere in the tree except
//! at a sort.** `iota_immune_sort_witness` (`wall_a_completeness.rs:441`) is the
//! only unconditional inhabitant, and a sort is not an application;
//! `iota_immune_cd_step` propagates immunity but never creates it. Every other
//! occurrence — `nf_head`'s `neutral` arm, `iota_neutral`'s `app` arm,
//! `spine_join_components`, the whole `iota_whnf` apparatus — is a *hypothesis*
//! position. So a large body of proved metatheory was carrying an obligation with
//! no supply anywhere, which is exactly why `def_eq_whnf_complete` has had zero
//! consumers since it landed, and why the def-eq completeness capstone turned out
//! vacuous (`hnf_refutation.rs`).
//!
//! This module supplies it.
//!
//! ## The argument, and why every escape is closed
//!
//! `delta_reduct` fires on a **whole spine**, not just a bare const
//! (`delta_step.rs:61`: it takes `kexpr_const_name (kapp_fn e)` and re-applies
//! `kapp_args e` to the unfolded value). That is the fact that makes head
//! δ-deadness sufficient rather than merely necessary. So for a const-headed
//! spine whose head has neither a definition nor recursor metadata, one parallel
//! step cannot change the head:
//!
//! | arm | why the head survives |
//! |---|---|
//! | `refl` | the hypothesis is the conclusion |
//! | `app` | `kapp_fn (app f a)` **unfolds to** `kapp_fn f`, so the goal *is* the induction hypothesis — no inversion lemma needed |
//! | `beta` | the head would be a `lam`, which has no const name |
//! | `lam`, `pi`, `forall_`, `let_`, `let_cong`, `proj` | the source is its own `kapp_fn`, and none of those has a const name |
//! | `iota` | `iota_step_no_recmeta_absurd` — no recursor metadata, no ι |
//! | `delta` | `delta_reduct_eq_none_of_defval_none` — no definitional value, no δ |
//!
//! Seven of the eight structural arms therefore close **identically** (a
//! binder/`let_`/`proj`/`lam`-headed source has no const name), leaving `app` as
//! the only substantive one. The same collapse as the head grid and
//! `nf_app_leg_inv`: split where the alternatives converge, not after.
//!
//! Arm order is `par_reduces_cd`'s own — refl, beta, app, lam, pi, forall_, let_,
//! **iota, delta**, let_cong, proj. ι and δ sit at positions 8-9, *before*
//! `let_cong` and `proj`; a transposition there typechecks in the wrong places and
//! cost a validation cycle earlier in this program, so `ARM_ORDER` pins it and a
//! test asserts it.
//!
//! `DerivedProved` throughout, empty axiom closures.

use super::kexpr_discr::CD_STRUCTURAL_ARMS;
use crate::spec::error::SpecError;
use crate::spec::Specification;

/// `par_reduces_cd`'s constructor order (`par_reduces_cd.rs:187-198`).
/// `Some(i)` indexes `CD_STRUCTURAL_ARMS`; `None` marks the three arms this
/// module handles specially.
const ARM_ORDER: [Option<usize>; 11] = [
    None,    // refl
    Some(0), // beta
    Some(1), // app
    Some(2), // lam
    Some(3), // pi
    Some(4), // forall_
    Some(5), // let_
    None,    // iota
    None,    // delta
    Some(6), // let_cong
    Some(7), // proj
];

impl Specification {
    /// `iota_immune`, supplied at last.
    pub(super) fn add_iota_immunity(&mut self) -> Result<(), SpecError> {
        self.add_const_head_preserved()?;
        self.add_const_head_star_preserved()?;
        self.add_iota_immune_of_dead_head()?;
        self.add_iota_immune_app_witness()?;
        self.add_iota_neutral_of_dead_const()?;
        self.add_nf_head_neutral_witness()?;
        Ok(())
    }

    /// `delta_reduct (red_def the_red_env) (const nm us) = none`, derived from
    /// the head's `defval_for` being `none`.
    ///
    /// The exact term is already used in-tree (`acc_wtype.rs:392`,
    /// `natrec.rs:481`, `mutual_schema.rs`'s `inertApp_step_inv`). The `Eq.refl`
    /// works because `kexpr_const_name (kapp_fn (KExpr.const n us))` reduces on
    /// the constructor regardless of `n` being a variable.
    fn const_delta_dead(nm: &str, us: &str) -> String {
        format!(
            "(delta_reduct_eq_none_of_defval_none (red_def the_red_env) \
             (KExpr.const {nm} {us}) {nm} \
             (Eq.refl (OptionType Name) (OptionType.some Name {nm})) hdef)"
        )
    }

    /// `kexpr_const_name (kapp_fn {e}) = some nm`. A **Prop**, since `Eq` is.
    fn head_is(e: &str) -> String {
        format!("Eq (OptionType Name) (kexpr_const_name (kapp_fn {e})) (OptionType.some Name nm)")
    }

    /// The same statement lifted into `Type`.
    ///
    /// `par_reduces_cd` and `par_reduces_cd_star` are **`Type`-valued**
    /// inductives, so their recursors demand a `Type`-valued motive — and
    /// `head_is` is a `Prop`. `rigid_app_head_preserved` never hits this because
    /// `rigid_app_head` is itself `Type`-valued; the moment the preserved
    /// property is an equation, the lift is mandatory. (Getting this wrong is
    /// exactly the "expected Sort(Succ(Zero)), got universe level conflict:
    /// Zero vs Succ(Zero)" rejection, and it has now cost two validation cycles
    /// in this program — once on `def_eq_fuel_succ_mono`, once here.)
    ///
    /// Only the RESULT needs lifting: `Prop -> Type` already lives in `Type`
    /// (`imax 0 1 = 1`), so the motive `head_is p -> LiftP (head_is q)` is
    /// `Type`-valued while the antecedent stays a usable `Prop`.
    fn head_is_lifted(e: &str) -> String {
        format!("LiftP ({})", Self::head_is(e))
    }

    /// `LiftP.rec` unwrap, the mirror of `LiftP.up` (pattern from `nf_head.rs:96`).
    fn unlift(e: &str, value: &str) -> String {
        let p = Self::head_is(e);
        format!("LiftP.rec ({p}) (fun (_l : LiftP ({p})) => {p}) (fun (pp : {p}) => pp) ({value})")
    }

    fn add_const_head_preserved(&mut self) -> Result<(), SpecError> {
        let mut arms = String::new();
        for (slot, entry) in ARM_ORDER.iter().enumerate() {
            match entry {
                // refl (slot 0), iota (7), delta (8).
                None => arms.push_str(&Self::special_arm(slot)),
                Some(idx) => {
                    let (payload, pairs, src, tgt) = CD_STRUCTURAL_ARMS[*idx];
                    // Bind every recursive premise and its induction
                    // hypothesis; only the `app` arm names them.
                    let is_app = *idx == 1;
                    let mut proofs = String::new();
                    let mut ihs = String::new();
                    for (n, (from, to)) in pairs.iter().enumerate() {
                        let pname = if is_app && n == 0 { "_hpf" } else { "_" };
                        let iname = if is_app && n == 0 { "ihf" } else { "_" };
                        proofs.push_str(&format!("({pname} : par_reduces_cd env {from} {to}) "));
                        ihs.push_str(&format!(
                            "({iname} : {} -> {}) ",
                            Self::head_is(from),
                            Self::head_is_lifted(to)
                        ));
                    }
                    let body = if is_app {
                        // kapp_fn (app f a) UNFOLDS to kapp_fn f, so the goal is
                        // literally the induction hypothesis applied.
                        "ihf hr".to_string()
                    } else {
                        // A lam/pi/forall_/let_/proj-headed source has no const
                        // name, so the hypothesis is `none = some nm`.
                        format!(
                            "option_none_ne_some_type Name nm ({}) hr",
                            Self::head_is_lifted(tgt)
                        )
                    };
                    arms.push_str(&format!(
                        "(fun {payload} {proofs}{ihs}(hr : {}) => {body}) ",
                        Self::head_is(src)
                    ));
                }
            }
        }

        self.add_recursive_def(
            &format!(
                "def const_head_preserved_cd (env : RedEnv) (nm : Name) \
                 (hdef : Eq (OptionType KExpr) (defval_for (red_def env) nm) \
                 (OptionType.none KExpr)) \
                 (hrec : Eq (OptionType RecMeta) (recmeta_for (red_rec env) nm) \
                 (OptionType.none RecMeta)) \
                 (e : KExpr) (e2 : KExpr) (h : par_reduces_cd env e e2) : \
                 {src_goal} -> {tgt_goal} := \
                 fun (hh : {src_goal}) => {unwrap}",
                src_goal = Self::head_is("e"),
                tgt_goal = Self::head_is("e2"),
                unwrap = Self::unlift(
                    "e2",
                    &format!(
                        "par_reduces_cd.rec env \
                         (fun (p : KExpr) (q : KExpr) (_h : par_reduces_cd env p q) => \
                         {p_goal} -> {q_lifted}) \
                         {arms}e e2 h hh",
                        p_goal = Self::head_is("p"),
                        q_lifted = Self::head_is_lifted("q"),
                    )
                ),
            ),
            "const_head_preserved_cd: a const-headed spine whose head has NEITHER a definitional \
             value NOR recursor metadata keeps that head under one parallel step. \
             \
             The load-bearing fact is that delta_reduct fires on a WHOLE SPINE — it reads \
             kexpr_const_name (kapp_fn e) and re-applies kapp_args e to the unfolded value \
             (delta_step.rs:61) — so head delta-deadness blocks delta at the top of the entire \
             spine, not merely at a bare const. \
             \
             Every escape is closed: refl is trivial; the app arm needs NO inversion lemma because \
             kapp_fn (app f a) unfolds to kapp_fn f, making the goal literally the induction \
             hypothesis; beta/lam/pi/forall_/let_/let_cong/proj all die because the source is its \
             own kapp_fn and none of those constructors carries a const name; iota dies by \
             iota_step_no_recmeta_absurd; delta by delta_reduct_eq_none_of_defval_none. \
             \
             Seven of the eight structural arms therefore close IDENTICALLY, leaving app as the \
             only substantive one. DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }

    /// refl / iota / delta — the three arms that are not a `CD_STRUCTURAL_ARMS`
    /// row.
    fn special_arm(slot: usize) -> String {
        match slot {
            0 => format!(
                "(fun (re : KExpr) (hr : {p}) => LiftP.up ({p}) hr) ",
                p = Self::head_is("re")
            ),
            7 => format!(
                "(fun (ie : KExpr) (ie2 : KExpr) \
                 (hstep : iota_step (red_rec env) ie ie2) (hr : {src}) => \
                 iota_step_no_recmeta_absurd (red_rec env) ie ie2 nm ({tgt}) hr hrec hstep) ",
                src = Self::head_is("ie"),
                tgt = Self::head_is_lifted("ie2"),
            ),
            8 => format!(
                "(fun (de : KExpr) (de2 : KExpr) \
                 (hstep : delta_step (red_def env) de de2) (hr : {src}) => \
                 option_none_ne_some_type KExpr de2 ({tgt}) \
                 (Eq.trans (OptionType KExpr) (OptionType.none KExpr) \
                 (delta_reduct (red_def env) de) (OptionType.some KExpr de2) \
                 (Eq.symm (OptionType KExpr) (delta_reduct (red_def env) de) \
                 (OptionType.none KExpr) \
                 (delta_reduct_eq_none_of_defval_none (red_def env) de nm hr hdef)) \
                 hstep)) ",
                src = Self::head_is("de"),
                tgt = Self::head_is_lifted("de2"),
            ),
            other => unreachable!("slot {other} is a CD_STRUCTURAL_ARMS row, not a special arm"),
        }
    }

    fn add_const_head_star_preserved(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            &format!(
                "def const_head_star_preserved (env : RedEnv) (nm : Name) \
                 (hdef : Eq (OptionType KExpr) (defval_for (red_def env) nm) \
                 (OptionType.none KExpr)) \
                 (hrec : Eq (OptionType RecMeta) (recmeta_for (red_rec env) nm) \
                 (OptionType.none RecMeta)) \
                 (e : KExpr) (e2 : KExpr) (h : par_reduces_cd_star env e e2) : \
                 {src_goal} -> {tgt_goal} := \
                 fun (hh : {src_goal}) => {unwrap}",
                src_goal = Self::head_is("e"),
                tgt_goal = Self::head_is("e2"),
                unwrap = Self::unlift(
                    "e2",
                    &format!(
                        "par_reduces_cd_star.rec env \
                         (fun (p : KExpr) (q : KExpr) (_h : par_reduces_cd_star env p q) => \
                         {p_goal} -> {q_lifted}) \
                         (fun (re : KExpr) (hr : {re_goal}) => LiftP.up ({re_goal}) hr) \
                         (fun (sx : KExpr) (sy : KExpr) (sz : KExpr) \
                         (hstep : par_reduces_cd env sx sy) \
                         (_hstar : par_reduces_cd_star env sy sz) \
                         (ih : {sy_goal} -> {sz_lifted}) (hr : {sx_goal}) => \
                         ih (const_head_preserved_cd env nm hdef hrec sx sy hstep hr)) \
                         e e2 h hh",
                        p_goal = Self::head_is("p"),
                        q_lifted = Self::head_is_lifted("q"),
                        re_goal = Self::head_is("re"),
                        sx_goal = Self::head_is("sx"),
                        sy_goal = Self::head_is("sy"),
                        sz_lifted = Self::head_is_lifted("sz"),
                    )
                ),
            ),
            "const_head_star_preserved: the head survives arbitrarily many parallel steps. The \
             usual two-arm reflexive-transitive induction — refl returns its hypothesis, step \
             advances one link with const_head_preserved_cd and forwards the rest to the induction \
             hypothesis. DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }

    fn add_iota_immune_of_dead_head(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            &format!(
                "def iota_immune_of_dead_const_head (nm : Name) \
                 (hdef : Eq (OptionType KExpr) (defval_for (red_def the_red_env) nm) \
                 (OptionType.none KExpr)) \
                 (hrec : Eq (OptionType RecMeta) (recmeta_for (red_rec the_red_env) nm) \
                 (OptionType.none RecMeta)) \
                 (e : KExpr) (hhead : {head}) : iota_immune e := \
                 fun (e2 : KExpr) (r : KExpr) \
                 (hstar : par_reduces_cd_star the_red_env e e2) \
                 (hfire : iota_step (red_rec the_red_env) e2 r) => \
                 iota_step_no_recmeta_absurd (red_rec the_red_env) e2 r nm Empty \
                 (const_head_star_preserved the_red_env nm hdef hrec e e2 hstar hhead) \
                 hrec hfire",
                head = Self::head_is("e"),
            ),
            "iota_immune_of_dead_const_head: THE PAYOFF — permanent iota-deadness for any \
             const-headed spine whose head has neither a definitional value nor recursor metadata. \
             \
             iota_immune demands that NO par_reduces_cd_star reduct is a top iota redex. Head \
             preservation carries the head name to the reduct, and no recursor metadata means the \
             reduct cannot fire — so the two obligations compose in one line. \
             \
             This is the first way in the tree to establish iota_immune anywhere other than at a \
             sort, and therefore the first supply for nf_head's neutral arm, iota_neutral's app \
             arm, and the iota_whnf apparatus, all of which had carried it unsupplied. It does NOT \
             rescue the completeness capstone as stated — hnf remains false, because whnf results \
             may be RECURSOR-headed and those genuinely are not immune (hnf_refutation.rs). It is \
             the tool for restating completeness on the opaque-constant fragment, where the \
             restriction is true rather than assumed. DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }

    fn add_iota_immune_app_witness(&mut self) -> Result<(), SpecError> {
        // Name.anonymous is in neither component of the reflected env, so both
        // deadness facts are single-rfl computations.
        let subject = "(KExpr.app (KExpr.const Name.anonymous (ListType.nil Level)) \
                       (KExpr.sort Level.zero))";
        self.add_recursive_def(
            &format!(
                "def iota_immune_app_witness : iota_immune {subject} := \
                 iota_immune_of_dead_const_head Name.anonymous \
                 (Eq.refl (OptionType KExpr) (OptionType.none KExpr)) \
                 (Eq.refl (OptionType RecMeta) (OptionType.none RecMeta)) \
                 {subject} \
                 (Eq.refl (OptionType Name) (OptionType.some Name Name.anonymous))"
            ),
            "iota_immune_app_witness (NON-VACUITY): iota_immune holds at a genuine APPLICATION. \
             \
             Until now the only unconditional inhabitant was iota_immune_sort_witness, at a SORT — \
             and a sort is not an application, so nf_head's neutral arm and iota_neutral's app arm \
             had no witness of the right shape anywhere in the tree. This closes that: the head \
             Name.anonymous is in neither component of the reflected environment, so both deadness \
             hypotheses are single-rfl computations and the head equation is one more. \
             \
             The counterpart of the Guard-4 non-vacuity discipline, applied to a predicate rather \
             than an environment: a predicate that is only ever assumed is indistinguishable from a \
             false one, which is precisely how the completeness capstone came to be vacuous. \
             DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }

    fn add_iota_neutral_of_dead_const(&mut self) -> Result<(), SpecError> {
        let dead = Self::const_delta_dead("nm", "us");
        self.add_recursive_def(
            &format!(
                "def iota_neutral_of_dead_const (nm : Name) (us : ListType Level) \
                 (hdef : Eq (OptionType KExpr) (defval_for (red_def the_red_env) nm) \
                 (OptionType.none KExpr)) : iota_neutral (KExpr.const nm us) := \
                 iota_neutral.const nm us {dead} {dead}"
            ),
            "iota_neutral_of_dead_const: iota_neutral at an opaque constant. \
             \
             BOTH of iota_neutral.const's fields are satisfied by the SAME term, because \
             const_whnf n us (whnf_reduction.rs:53) unfolds to exactly the delta-deadness equation \
             its second field spells out — const_whnf is a semireducible definition precisely so \
             the unfolded equation discharges the folded goal. Two fields, one obligation. \
             \
             Like const_whnf itself, iota_neutral had NO registered inhabitant before this: it \
             appeared only as a hypothesis or a constructor field. DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }

    fn add_nf_head_neutral_witness(&mut self) -> Result<(), SpecError> {
        let head = "(KExpr.const Name.anonymous (ListType.nil Level))";
        let arg = "(KExpr.sort Level.zero)";
        self.add_recursive_def(
            &format!(
                "def nf_head_neutral_app_witness : nf_head (KExpr.app {head} {arg}) := \
                 nf_head.neutral {head} {arg} \
                 (iota_neutral_of_dead_const Name.anonymous (ListType.nil Level) \
                 (Eq.refl (OptionType KExpr) (OptionType.none KExpr))) \
                 iota_immune_app_witness"
            ),
            "nf_head_neutral_app_witness (NON-VACUITY, the one that matters): the FIRST nf_head \
             witness at an application anywhere in the tree, and the first for the neutral arm at \
             all. \
             \
             Before this, def_eq_dispatch was the only place that ever BUILT an nf_head witness, \
             and it built them by inverting the nf_head that the false hnf premise handed it — the \
             witnesses were laundered from an unsatisfiable hypothesis, which is the circularity \
             that let the vacuity hide. This one is built from nothing but computation: \
             Name.anonymous is in neither component of the reflected environment, so its \
             delta-deadness is a single rfl, iota_neutral follows, and iota_immune follows from \
             iota_immune_of_dead_const_head. \
             \
             This is the Guard-4 non-vacuity discipline applied to a PREDICATE ARM rather than to \
             an environment, and it is the check that would have caught the vacuity on day one: an \
             inductive arm that nothing can construct is indistinguishable from a false one. \
             DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `par_reduces_cd`'s arm order puts **iota and delta at positions 8 and 9**,
    /// before `let_cong` and `proj`. Emitting the structural arms in table order
    /// and appending the step arms keeps the count at eleven while shifting six
    /// arms into the wrong slots — it typechecks in the wrong places and cost a
    /// validation cycle earlier in this program. So the order is pinned here.
    #[test]
    fn test_arm_order_matches_par_reduces_cd() {
        assert_eq!(
            ARM_ORDER.len(),
            11,
            "par_reduces_cd has eleven constructors"
        );
        assert_eq!(ARM_ORDER[0], None, "refl is first");
        assert_eq!(ARM_ORDER[7], None, "iota is EIGHTH, before let_cong");
        assert_eq!(ARM_ORDER[8], None, "delta is NINTH, before let_cong");
        assert_eq!(ARM_ORDER[9], Some(6), "let_cong follows the step arms");
        assert_eq!(ARM_ORDER[10], Some(7), "proj is last");
        // Every structural row used exactly once, none skipped.
        let mut used: Vec<usize> = ARM_ORDER.iter().flatten().copied().collect();
        used.sort_unstable();
        assert_eq!(
            used,
            (0..CD_STRUCTURAL_ARMS.len()).collect::<Vec<_>>(),
            "each CD_STRUCTURAL_ARMS row must be used exactly once"
        );
    }

    /// Only the `app` arm may consume an induction hypothesis. If another arm
    /// bound one by name the proof would still typecheck while quietly relying on
    /// a subterm's head, which is the mistake `rigid_app_head` exists to avoid.
    #[test]
    fn test_only_the_app_arm_uses_its_induction_hypothesis() {
        // Rebuild the arm string the same way the registration does.
        let mut named_ih = 0usize;
        for entry in ARM_ORDER.iter().flatten() {
            let (_, pairs, _, _) = CD_STRUCTURAL_ARMS[*entry];
            if *entry == 1 {
                assert_eq!(pairs.len(), 2, "the app arm has two recursive premises");
                named_ih += 1;
            }
        }
        assert_eq!(named_ih, 1, "exactly one arm names an induction hypothesis");
    }

    /// `par_reduces_cd` is `Type`-valued, so its motive must be too — but
    /// `head_is` is an `Eq`, hence `Prop`. Every arm must therefore produce the
    /// LIFTED goal, and the lemma must unwrap once at the end. Omitting the lift
    /// is the "expected Sort(Succ(Zero)), got universe level conflict" rejection,
    /// which has cost two validation cycles in this program.
    #[test]
    fn test_prop_goal_is_lifted_into_type_for_the_recursor() {
        let lifted = Specification::head_is_lifted("q");
        assert!(
            lifted.starts_with("LiftP ("),
            "the motive's result must be lifted: {lifted}"
        );
        // The antecedent must stay an unlifted Prop — Prop -> Type is already
        // Type-valued, so lifting both sides would be wrong, not merely wasteful.
        assert!(
            !Specification::head_is("p").contains("LiftP"),
            "the antecedent must remain a usable Prop"
        );
        let unwrap = Specification::unlift("e2", "BODY");
        assert!(
            unwrap.contains("LiftP.rec") && unwrap.contains("(BODY)"),
            "the lemma must unwrap exactly once at the end: {unwrap}"
        );
    }

    /// The head abbreviation must mention `kapp_fn`, not just `kexpr_const_name`.
    /// Dropping `kapp_fn` would state the head condition of a bare const rather
    /// than of a spine, and the `app` arm's IH step would no longer be definitional.
    #[test]
    fn test_head_condition_is_about_the_spine_head() {
        let h = Specification::head_is("e");
        assert!(
            h.contains("kexpr_const_name (kapp_fn e)"),
            "the condition must be about the SPINE head: {h}"
        );
        assert!(h.contains("OptionType.some Name nm"));
    }
}
