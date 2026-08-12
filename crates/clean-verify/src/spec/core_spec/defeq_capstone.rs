// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **The capstone**: completeness of the structural conversion algorithm
//! against `DefEq`.
//!
//! ```text
//! def_eq_fuel_complete :
//!   i1..i8 -> (hnf) -> DefEq a b
//!     -> rbelow_plus_acc a -> rbelow_plus_acc b
//!     -> DefEqFuelAccepts a b
//! ```
//!
//! Two declarations. `def_eq_dispatch` is the eight-leaf case analysis that
//! selects a round; `def_eq_fuel_complete` is the `rbelow_plus_acc` induction
//! that supplies `recur` to it.
//!
//! ## The premises, and why each is there
//!
//! | premise | why it cannot be dropped |
//! |---|---|
//! | `i1..i8` | `def_eq_joinable`; dischargeable at `the_red_env` via `the_red_env_faithful` |
//! | `rbelow_plus_acc a` **and** `b` | `DefEq` does not preserve strong normalisation and the algorithm reduces both sides, so one accessibility witness does not imply the other |
//! | `hnf` | every whnf result has a normal-form head — hereditary, because the recursion meets new normal forms at every level |
//!
//! `hnf` is the honest cost of the `const` case. A constant-headed spine can
//! ι-fire once its arguments become constructor-headed, so its head stability is
//! genuinely conditional; `nf_head`'s `neutral` arm carries `iota_neutral` and
//! `iota_immune` as fields precisely so that the obligation is *visible* rather
//! than absent. Discharging it in general is the open sub-problem the program's
//! scoping audit recorded, and it is not closed here.
//!
//! ## What this does and does not say
//!
//! It says: **complete against `DefEq`** — the twelve-constructor β/δ/ι/ζ
//! congruence-equivalence closure (`typing_def_eq.rs:74-86`) — at the fixed
//! reflected environment, conditional on the premises above.
//!
//! `DefEq` contains no η, no proof irrelevance, no structure-eta, no
//! universe/level conversion and no literal computation, all of which the
//! shipping Rust kernel's `is_def_eq` implements. So this says **nothing** about
//! the completeness of the deployed checker, and per
//! `docs/SELF_VERIFICATION_CERTIFICATE.md` §2b it is registered as a conditional
//! theorem and never an axiom.
//!
//! Soundness (`def_eq_fuel_sound`) is the companion, and the pair is what makes
//! either meaningful: completeness alone is satisfied by `fun _ _ => true`.
//!
//! `DerivedProved`, empty axiom closures.

use super::nf_head::HNF;
use crate::spec::error::SpecError;
use crate::spec::Specification;

/// The eight faithful-interface binders, in `def_eq_joinable`'s order.
const I_BINDERS: &str = "(i1 : RecEnvReductNotRedex (red_rec the_red_env)) \
     (i2 : RecEnvCtorNoRecMeta (red_rec the_red_env)) \
     (i3 : RecEnvClosed (red_rec the_red_env)) \
     (i4 : RecEnvLiftClosed (red_rec the_red_env)) \
     (i5 : DefEnvClosed (red_def the_red_env)) \
     (i6 : DefEnvLiftClosed (red_def the_red_env)) \
     (i7 : RecEnvDefEnvDisjoint the_red_env) \
     (i8 : RecEnvCtorNoDefVal the_red_env) ";

const RECUR: &str = "(recur : forall (c1 : KExpr) (c2 : KExpr), rbelow_plus c1 x -> \
     DefEq c1 c2 -> rbelow_plus_acc c2 -> DefEqFuelAccepts c1 c2) ";

/// The eight `the_red_env_*_via_checker` witnesses, in `I_BINDERS` order.
///
/// Each is a `DerivedProved` single-`rfl` term registered by
/// `add_the_red_env_faithful_discharge` (`bundles.rs:993`, far ahead of
/// `add_defeq_fuel` at 1424, so all eight are in scope here). Their registered
/// types are *verbatim* `I_BINDERS`' — same phrasing, same order — so the
/// discharge is a direct positional application: no `RedEnvFaithful` projection,
/// no conversion step, nothing to prove.
///
/// That is the whole point. The capstone's comment asserted i1..i8 were
/// "dischargeable at the_red_env"; asserting it and doing it are different
/// things, and the difference is what this constant closes.
const I_WITNESSES: [&str; 8] = [
    "the_red_env_reduct_not_redex_via_checker",
    "the_red_env_ctor_no_recmeta_via_checker",
    "the_red_env_rec_closed_via_checker_b2",
    "the_red_env_rec_lift_closed_via_checker_b2",
    "the_red_env_def_closed_via_checker_b2",
    "the_red_env_def_lift_closed_via_checker_b2",
    "the_red_env_defenv_disjoint_via_checker",
    "the_red_env_ctor_no_defval_via_checker",
];

impl Specification {
    /// The dispatch, the capstone, and the capstone with i1..i8 discharged.
    pub(super) fn add_defeq_capstone(&mut self) -> Result<(), SpecError> {
        self.add_dispatch()?;
        self.add_capstone()?;
        self.add_capstone_at_the_red_env()?;
        Ok(())
    }

    fn add_dispatch(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            &Self::dispatch_src(),
            "def_eq_dispatch: select and run the completeness round matching the first normal \
             form's head. Nine leaves — nf_head's four arms with rigid fanning out to six — of \
             which six are one-line calls and the two application leaves shape-force the other \
             side, invert both legs with nf_app_leg_inv and hand the witnesses to the \
             evidence-agnostic application round. \
             \
             The motive generalises the first normal form, because it is the index the case \
             analysis runs on; the leg and the join are therefore threaded through the motive \
             rather than captured. DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }

    fn dispatch_src() -> String {
        let goal = "DefEqFuelAccepts x bb";
        let motive = |z: &str| {
            format!(
                "Eq (OptionType KExpr) (whnf_fuel_red the_red_env n x) (OptionType.some KExpr {z}) \
                 -> par_strips_witness_cd_star the_red_env {z} nb -> {goal}"
            )
        };

        // The two application leaves, which must shape-force the other side.
        let app_leaf = |binders: &str, form: &str, f1: &str, a1: &str, wit1: &str| {
            format!(
                "(fun {binders} (hxz : Eq (OptionType KExpr) \
                 (whnf_fuel_red the_red_env n x) (OptionType.some KExpr {form})) \
                 (hjz : par_strips_witness_cd_star the_red_env {form} nb) => \
                 @par_strips_witness_cd_star.rec the_red_env {form} nb \
                 (fun (_j : par_strips_witness_cd_star the_red_env {form} nb) => {goal}) \
                 (fun (w : KExpr) (hlw : par_reduces_cd_star the_red_env {form} w) \
                 (hrw : par_reduces_cd_star the_red_env nb w) => \
                 AppShape.rec nb (fun (_s : AppShape nb) => {goal}) \
                 (fun (f2 : KExpr) (a2 : KExpr) (hshape : Eq KExpr nb (KExpr.app f2 a2)) => \
                 def_eq_round_app n x bb {f1} {a1} f2 a2 w hxz \
                 (Eq.substType KExpr \
                 (fun (z : KExpr) => Eq (OptionType KExpr) (whnf_fuel_red the_red_env n bb) \
                 (OptionType.some KExpr z)) nb (KExpr.app f2 a2) hshape hb) \
                 ({wit1}) \
                 (nf_app_leg_inv w nb (hnf n bb nb hb) f2 a2 hshape hrw) \
                 accb recur) \
                 (nf_tag_forces_app {f1} {a1} nb (hnf n bb nb hb) \
                 (nf_join_same_tag {form} nb w (hnf n x {form} hxz) (hnf n bb nb hb) \
                 hlw hrw))) hjz) "
            )
        };

        let rigid_app_form = "(KExpr.app raf raa)";
        let neutral_form = "(KExpr.app nfh nag)";

        let rigid_arms = format!(
            "(fun (rn : Level) (hxz : Eq (OptionType KExpr) (whnf_fuel_red the_red_env n x) \
             (OptionType.some KExpr (KExpr.sort rn))) \
             (hjz : par_strips_witness_cd_star the_red_env (KExpr.sort rn) nb) => \
             def_eq_round_sort hnf n x bb nb rn hxz hb hjz) \
             (fun (rpty : KExpr) (rpbody : KExpr) \
             (hxz : Eq (OptionType KExpr) (whnf_fuel_red the_red_env n x) \
             (OptionType.some KExpr (KExpr.pi rpty rpbody))) \
             (hjz : par_strips_witness_cd_star the_red_env (KExpr.pi rpty rpbody) nb) => \
             def_eq_round_pi hnf n x bb nb rpty rpbody hxz hb hjz accb recur) \
             (fun (rv : Nat) (hxz : Eq (OptionType KExpr) (whnf_fuel_red the_red_env n x) \
             (OptionType.some KExpr (KExpr.lit rv))) \
             (hjz : par_strips_witness_cd_star the_red_env (KExpr.lit rv) nb) => \
             def_eq_round_lit hnf n x bb nb rv hxz hb hjz) \
             {app} \
             (fun (rs : Name) (ri : Nat) (rsub : KExpr) \
             (hxz : Eq (OptionType KExpr) (whnf_fuel_red the_red_env n x) \
             (OptionType.some KExpr (KExpr.proj rs ri rsub))) \
             (hjz : par_strips_witness_cd_star the_red_env (KExpr.proj rs ri rsub) nb) => \
             def_eq_round_proj hnf n x bb nb rs ri rsub hxz hb hjz accb recur) \
             (fun (rbi : Nat) \
             (hxz : Eq (OptionType KExpr) (whnf_fuel_red the_red_env n x) \
             (OptionType.some KExpr (KExpr.bvar rbi))) \
             (hjz : par_strips_witness_cd_star the_red_env (KExpr.bvar rbi) nb) => \
             def_eq_round_bvar hnf n x bb nb rbi hxz hb hjz) ",
            app = app_leaf(
                "(raf : KExpr) (raa : KExpr) (hraf : rigid_app_head raf) \
                 (_ihr : Eq (OptionType KExpr) (whnf_fuel_red the_red_env n x) \
                 (OptionType.some KExpr raf) -> \
                 par_strips_witness_cd_star the_red_env raf nb -> DefEqFuelAccepts x bb)",
                rigid_app_form,
                "raf",
                "raa",
                "nf_app_leg_inv w (KExpr.app raf raa) \
                 (nf_head.rigid (KExpr.app raf raa) (rigid_app_head.app raf raa hraf)) \
                 raf raa (Eq.refl KExpr (KExpr.app raf raa)) hlw",
            ),
        )
        // Strip the readability markers.
        .replace("// pi\n", "")
        .replace("// lit\n", "")
        .replace("// proj\n", "")
        .replace("// sort", "");

        format!(
            "def def_eq_dispatch {HNF}(n : Nat) (x : KExpr) (bb : KExpr) (nx : KExpr) \
             (nb : KExpr) \
             (hx : Eq (OptionType KExpr) (whnf_fuel_red the_red_env n x) \
             (OptionType.some KExpr nx)) \
             (hb : Eq (OptionType KExpr) (whnf_fuel_red the_red_env n bb) \
             (OptionType.some KExpr nb)) \
             (hj : par_strips_witness_cd_star the_red_env nx nb) \
             (accb : rbelow_plus_acc bb) {RECUR}: {goal} := \
             nf_head.rec (fun (z : KExpr) (_h : nf_head z) => {mz}) \
             (fun (qty : KExpr) (qbody : KExpr) \
             (hxz : Eq (OptionType KExpr) (whnf_fuel_red the_red_env n x) \
             (OptionType.some KExpr (KExpr.lam qty qbody))) \
             (hjz : par_strips_witness_cd_star the_red_env (KExpr.lam qty qbody) nb) => \
             def_eq_round_lam hnf n x bb nb qty qbody hxz hb hjz accb recur) \
             (fun (e0 : KExpr) (hr : rigid_app_head e0) => \
             rigid_app_head.rec (fun (z : KExpr) (_h : rigid_app_head z) => {mz}) \
             {rigid_arms}e0 hr) \
             {neutral} \
             (fun (cn : Name) (cus : ListType Level) \
             (_hdd : Eq (OptionType KExpr) \
             (delta_reduct (red_def the_red_env) (KExpr.const cn cus)) (OptionType.none KExpr)) \
             (hxz : Eq (OptionType KExpr) (whnf_fuel_red the_red_env n x) \
             (OptionType.some KExpr (KExpr.const cn cus))) \
             (hjz : par_strips_witness_cd_star the_red_env (KExpr.const cn cus) nb) => \
             def_eq_round_const hnf n x bb nb cn cus hxz hb hjz) \
             (fun (bi : Nat) \
             (hxz : Eq (OptionType KExpr) (whnf_fuel_red the_red_env n x) \
             (OptionType.some KExpr (KExpr.bvar bi))) \
             (hjz : par_strips_witness_cd_star the_red_env (KExpr.bvar bi) nb) => \
             def_eq_round_bvar hnf n x bb nb bi hxz hb hjz) \
             nx (hnf n x nx hx) hx hj",
            mz = motive("z"),
            neutral = app_leaf(
                "(nfh : KExpr) (nag : KExpr) (hin : iota_neutral nfh) \
                 (hii : iota_immune (KExpr.app nfh nag))",
                neutral_form,
                "nfh",
                "nag",
                "nf_app_leg_inv w (KExpr.app nfh nag) \
                 (nf_head.neutral nfh nag hin hii) \
                 nfh nag (Eq.refl KExpr (KExpr.app nfh nag)) hlw",
            ),
        )
    }

    fn add_capstone(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            &format!(
                "def def_eq_fuel_complete {I_BINDERS}{HNF}(a : KExpr) \
                 (acca : rbelow_plus_acc a) : \
                 forall (b : KExpr), DefEq a b -> rbelow_plus_acc b -> DefEqFuelAccepts a b := \
                 rbelow_plus_acc.rec \
                 (fun (z : KExpr) (_h : rbelow_plus_acc z) => \
                 forall (b : KExpr), DefEq z b -> rbelow_plus_acc b -> DefEqFuelAccepts z b) \
                 (fun (x : KExpr) \
                 (hfield : forall (y : KExpr), rbelow_plus y x -> rbelow_plus_acc y) \
                 (ih : forall (y : KExpr), rbelow_plus y x -> \
                 forall (b : KExpr), DefEq y b -> rbelow_plus_acc b -> DefEqFuelAccepts y b) \
                 (bb : KExpr) (hde : DefEq x bb) (accb : rbelow_plus_acc bb) => \
                 WhnfFuelPair.rec x bb \
                 (fun (_p : WhnfFuelPair x bb) => DefEqFuelAccepts x bb) \
                 (fun (n : Nat) (nx : KExpr) (nb : KExpr) \
                 (hx : Eq (OptionType KExpr) (whnf_fuel_red the_red_env n x) \
                 (OptionType.some KExpr nx)) \
                 (hb : Eq (OptionType KExpr) (whnf_fuel_red the_red_env n bb) \
                 (OptionType.some KExpr nb)) => \
                 def_eq_dispatch hnf n x bb nx nb hx hb \
                 (def_eq_whnf_join i1 i2 i3 i4 i5 i6 i7 i8 n x bb nx nb hde hx hb) \
                 accb \
                 (fun (c1 : KExpr) (c2 : KExpr) (hbelow : rbelow_plus c1 x) \
                 (hdec : DefEq c1 c2) (accc : rbelow_plus_acc c2) => \
                 ih c1 hbelow c2 hdec accc)) \
                 (whnf_fuel_pair x bb \
                 (whnf_fuel_from_acc x (rbelow_plus_acc.intro x hfield)) \
                 (whnf_fuel_from_acc bb accb))) \
                 a acca"
            ),
            "def_eq_fuel_complete: THE CAPSTONE — the structural conversion algorithm is COMPLETE \
             against DefEq. If a and b are definitionally equal and both are accessible in the \
             algorithm's own order, then some fuel suffices for def_eq_fuel to accept them. \
             \
             Well-founded recursion on rbelow_plus_acc a, with the motive quantified over the \
             SECOND term so the induction hypothesis applies to component pairs. Each round: fuel \
             both sides from their accessibility witnesses and pair to a common bound, join the \
             two normal forms by confluence, dispatch on the first one's head, descend. \
             \
             PREMISES, and why none is removable. i1..i8 are def_eq_joinable's faithful \
             interfaces, dischargeable at the_red_env via the_red_env_faithful. BOTH accessibility \
             witnesses are needed: DefEq does not preserve strong normalisation and the algorithm \
             reduces both sides, so neither implies the other. hnf — every whnf result has a \
             normal-form head — is hereditary because the recursion meets new normal forms at \
             every level, and it is the honest cost of the const case: a const-headed spine can \
             iota-fire once its arguments become constructor-headed, so its head stability is \
             genuinely conditional. \
             \
             SCOPE. Complete against DefEq, the twelve-constructor beta/delta/iota/zeta \
             congruence-equivalence closure, at the fixed reflected environment. DefEq contains no \
             eta, no proof irrelevance, no structure-eta, no universe conversion and no literal \
             computation, ALL of which the shipping Rust kernel's is_def_eq implements — so this \
             says NOTHING about the completeness of the deployed checker, and is registered as a \
             conditional theorem, never an axiom, per SELF_VERIFICATION_CERTIFICATE.md 2b. \
             \
             def_eq_fuel_sound is the companion, and the pair is what makes either meaningful: \
             completeness alone is satisfied by the constant-true comparator. DerivedProved, zero \
             axiom_deps.",
        )?;
        Ok(())
    }

    /// The capstone with i1..i8 gone: eleven premises down to three.
    fn add_capstone_at_the_red_env(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            &Self::capstone_at_src(),
            "def_eq_fuel_complete_at_the_red_env: the capstone with the eight faithful-interface \
             hypotheses DISCHARGED, not carried. Eleven premises become three. \
             \
             def_eq_fuel_complete's comment claimed i1..i8 were 'dischargeable at the_red_env via \
             the_red_env_faithful'. Claiming and doing are different, and this is the doing: each \
             binder is fed the corresponding the_red_env_*_via_checker witness, every one a \
             DerivedProved single-rfl term in which the kernel whnf-EVALUATES a checker fold over \
             the real reflected environment down to Bool.true. The registered witness types are \
             verbatim I_BINDERS', in the same order, so this is a direct positional application — \
             no RedEnvFaithful projection, no conversion, nothing left to prove. \
             \
             WHAT REMAINS, and why it is the honest floor rather than laziness. Two accessibility \
             witnesses: these CANNOT be discharged, because strong normalisation is FALSE for this \
             calculus as reflected — the sort structure admits Girard's paradox, so an SN campaign \
             would not be hard but unprovable. Carrying accessibility is therefore the correct shape \
             for the theorem, not a gap in it. And hnf, the const case's genuine cost, which is \
             open. \
             \
             SCOPE is inherited unchanged from def_eq_fuel_complete and must travel with any public \
             statement: complete against DefEq, which has no eta, no proof irrelevance, no \
             structure-eta, no universe conversion and no literal computation, all of which the \
             shipping is_def_eq implements. Conditional theorem, never an axiom. DerivedProved, \
             zero axiom_deps.",
        )?;
        Ok(())
    }

    fn capstone_at_src() -> String {
        format!(
            "def def_eq_fuel_complete_at_the_red_env {HNF}(a : KExpr) \
             (acca : rbelow_plus_acc a) : \
             forall (b : KExpr), DefEq a b -> rbelow_plus_acc b -> DefEqFuelAccepts a b := \
             def_eq_fuel_complete {ws} hnf a acca",
            ws = I_WITNESSES.join(" "),
        )
    }
}

#[cfg(test)]
mod at_the_red_env_tests {
    use super::*;

    /// The discharge is positional, so witness ORDER is load-bearing in a way no
    /// type error would necessarily catch: i3/i4 (`RecEnvClosed` /
    /// `RecEnvLiftClosed`) and i5/i6 (`DefEnvClosed` / `DefEnvLiftClosed`) are
    /// distinct types, but a transposition inside a pair of same-shaped
    /// interfaces is exactly the class of mistake that cost three validation
    /// cycles earlier in this program.
    ///
    /// So: assert each witness appears, and that they appear in `I_BINDERS`
    /// order, by checking their byte offsets are strictly increasing.
    #[test]
    fn test_witnesses_appear_in_i_binders_order() {
        let src = Specification::capstone_at_src();
        let mut last = 0usize;
        for (idx, w) in I_WITNESSES.iter().enumerate() {
            let at = src
                .find(w)
                .unwrap_or_else(|| panic!("witness {idx} ({w}) missing from the discharge"));
            assert!(
                at > last,
                "witness {idx} ({w}) is out of I_BINDERS order: found at {at}, previous at {last}"
            );
            last = at;
        }
    }

    /// The whole point is that i1..i8 are GONE. If any `i<n> :` binder survived,
    /// the corollary would still typecheck and would have discharged nothing.
    #[test]
    fn test_no_faithful_binder_survives() {
        let src = Specification::capstone_at_src();
        for n in 1..=8 {
            assert!(
                !src.contains(&format!("(i{n} :")),
                "i{n} is still a binder — the discharge discharged nothing"
            );
        }
    }

    /// `hnf` and both accessibility premises must survive. Silently discharging
    /// one of these would be a soundness-relevant overclaim, and accessibility
    /// in particular cannot be discharged at all.
    #[test]
    fn test_the_honest_premises_survive() {
        let src = Specification::capstone_at_src();
        assert!(src.contains("(hnf :"), "hnf must remain a hypothesis");
        assert!(
            src.contains("(acca : rbelow_plus_acc a)"),
            "the first accessibility witness must remain"
        );
        assert!(
            src.contains("rbelow_plus_acc b -> DefEqFuelAccepts a b"),
            "the second accessibility witness must remain in the conclusion"
        );
    }

    /// The corollary must be an application of the capstone, not a re-proof.
    #[test]
    fn test_delegates_to_the_capstone() {
        let src = Specification::capstone_at_src();
        assert_eq!(
            src.matches("def_eq_fuel_complete ").count(),
            1,
            "exactly one application of the capstone"
        );
        assert!(
            !src.contains("rbelow_plus_acc.rec"),
            "must delegate, not re-run the induction"
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The dispatch must call every round exactly once — eight leaves, and the
    /// two application leaves share the one evidence-agnostic round.
    #[test]
    fn test_dispatch_covers_every_head() {
        let src = Specification::dispatch_src();
        for round in [
            "def_eq_round_lam",
            "def_eq_round_sort",
            "def_eq_round_pi",
            "def_eq_round_lit",
            "def_eq_round_proj",
            "def_eq_round_const",
        ] {
            assert_eq!(
                src.matches(round).count(),
                1,
                "{round} must be called exactly once"
            );
        }
        assert_eq!(
            src.matches("def_eq_round_app").count(),
            2,
            "both application leaves route to the single evidence-agnostic round"
        );
        assert_eq!(
            src.matches("nf_app_leg_inv").count(),
            4,
            "each application leaf inverts both legs"
        );
    }

    /// Only the heads with components may pass `recur`. A leaf that forwarded it
    /// would compile and mislead.
    #[test]
    fn test_only_recursive_heads_receive_the_recursion() {
        let src = Specification::dispatch_src();
        for (round, recursive) in [
            ("def_eq_round_lam", true),
            ("def_eq_round_pi", true),
            ("def_eq_round_proj", true),
            ("def_eq_round_sort", false),
            ("def_eq_round_lit", false),
            ("def_eq_round_const", false),
        ] {
            let at = src.find(round).expect("round is called");
            // Clamp: the last round's call site sits near the end of the term,
            // so a fixed-width window runs past it.
            let tail = &src[at..(at + 140).min(src.len())];
            assert_eq!(
                tail.contains("accb recur"),
                recursive,
                "{round}: passes recur iff its head has components"
            );
        }
    }

    #[test]
    fn test_dispatch_parens_balanced() {
        let src = Specification::dispatch_src();
        let mut depth: i64 = 0;
        for ch in src.chars() {
            match ch {
                '(' => depth += 1,
                ')' => depth -= 1,
                _ => {}
            }
            assert!(depth >= 0, "close paren before its open");
        }
        assert_eq!(depth, 0);
    }
}
