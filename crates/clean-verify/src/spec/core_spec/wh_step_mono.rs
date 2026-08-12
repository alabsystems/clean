// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Confining the faithful step's dependence on the pre-pass.
//!
//! ## The question these answer
//!
//! Step monotonicity — a step that fires at one budget fires the same way at
//! the next — is the premise the whole fuel-adequacy layer is parameterised by.
//! Its only real difficulty is that `opt_app_ilift` branches on the head-reduct
//! `cf`: `none` tries ι, `some f2` takes the congruence instead. If `cf` could
//! flip `none → some` with more budget, the step would return a *different*
//! result and monotonicity would be false.
//!
//! `cf` genuinely does flip in general — that is exactly what starvation does.
//! The work is showing it cannot flip where it matters.
//!
//! ## Where the pre-pass can reach
//!
//! `wh` is threaded into exactly one place: the ι slot of `opt_app_ilift`.
//! Every other rule — β, δ, ζ, projection, congruence — is budget-independent.
//! So the step depends on the budget only when the head-reduct is `none` *and*
//! ι can actually fire, and these lemmas fence off everything else:
//!
//! - `reduce_app_head_no_name_wh_indep` — a head that is not a constant. ι stops
//!   at level one, so both budgets agree. Note the lambda case is not ι at all:
//!   β ignores `cf` and `wh` together.
//! - `under_applied_step_congr` — a const spine one argument short of its major
//!   premise. ι stops at level three, at *every* budget, because the shortfall
//!   is arithmetic and fuel cannot change it.
//!
//! What survives is a const-headed spine, long enough, with a `none`
//! head-reduct: precisely the ι slot, which is where the transport argument
//! (invert, move the pre-pass, re-assemble) does its work.
//!
//! ## Seven of nine arms are free
//!
//! `under_applied_step_congr` recurses on the expression, and only `app` does
//! anything: `sort`/`bvar`/`lam`/`pi`/`lit` give `none` on both sides, `const`
//! gives the same value lookup, `let_` the same ζ-contraction, and `proj` is
//! impossible because a projection carries no head name. That concentration is
//! not luck — it is the same fact stated a second way, that the budget reaches
//! only the ι slot.
//!
//! `DerivedProved`, empty axiom closures.

use super::iota_prepass::MAJOR_IDX;
use crate::spec::error::SpecError;
use crate::spec::Specification;

const O: &str = "OptionType KExpr";
const RR: &str = "(red_rec the_red_env)";

fn head_is(x: &str) -> String {
    format!("Eq (OptionType Name) (kexpr_const_name (kapp_fn {x})) (OptionType.some Name nm)")
}

fn head_none(x: &str) -> String {
    format!("Eq (OptionType Name) (kexpr_const_name (kapp_fn {x})) (OptionType.none Name)")
}

fn ilift(w: &str, x: &str, o: &str) -> String {
    format!("(opt_app_ilift_wh the_red_env {w} {x} a {o})")
}

fn step(w: &str, x: &str) -> String {
    format!("(reduce_once_red_wh the_red_env {w} {x})")
}

impl Specification {
    /// The two fences, and the congruences they rest on.
    pub(super) fn add_wh_step_mono(&mut self) -> Result<(), SpecError> {
        self.add_ilift_congruences()?;
        self.add_no_name_indep()?;
        self.add_under_applied_congr()?;
        Ok(())
    }

    /// `opt_app_ilift` is pre-pass-independent whenever ι cannot fire.
    ///
    /// Two instances of one shape: the `some` branch never consults `wh` at all,
    /// and the `none` branch is ι, which the relevant short-circuit kills at
    /// both budgets. They differ only in which exit of the chain they use — no
    /// head name, or no major premise.
    fn add_ilift_congruences(&mut self) -> Result<(), SpecError> {
        for (name, extra, hyp, exit, why) in [
            (
                "opt_app_ilift_no_head_congr",
                String::new(),
                format!("(hn : {})", head_none("(KExpr.app f a)")),
                (|w: &str| format!("(iota_reduct_whc_none_of_no_head {RR} {w} (KExpr.app f a) hn)"))
                    as fn(&str) -> String,
                "the head is not a constant, so iota stops at level one",
            ),
            (
                "opt_app_ilift_no_major_congr",
                " (nm : Name) (meta : RecMeta)".to_string(),
                format!(
                    "(hh : {hh}) (hrm : Eq (OptionType RecMeta) (recmeta_for {RR} nm) \
                     (OptionType.some RecMeta meta)) (hno : Eq ({O}) \
                     (list_head (list_drop {MAJOR_IDX} (kapp_args (KExpr.app f a)))) \
                     (OptionType.none KExpr))",
                    hh = head_is("(KExpr.app f a)"),
                ),
                |w: &str| {
                    format!(
                        "(iota_reduct_whc_none_of_no_major {RR} {w} (KExpr.app f a) nm meta \
                         hh hrm hno)"
                    )
                },
                "the spine is one argument short, so iota stops at level three",
            ),
        ] {
            let goal =
                |o: &str| format!("Eq ({O}) {} {}", ilift("wh1", "f", o), ilift("wh2", "f", o));
            let none_arm = format!(
                "(Eq.trans ({O}) {l1} (OptionType.none KExpr) {l2} {e1} \
                 (Eq.symm ({O}) {l2} (OptionType.none KExpr) {e2}))",
                l1 = ilift("wh1", "f", "(OptionType.none KExpr)"),
                l2 = ilift("wh2", "f", "(OptionType.none KExpr)"),
                e1 = exit("wh1"),
                e2 = exit("wh2"),
            );
            let src = format!(
                "def {name} (wh1 : KExpr -> OptionType KExpr) \
                 (wh2 : KExpr -> OptionType KExpr){extra} (f : KExpr) (a : KExpr) {hyp} \
                 (o : {O}) : {g} := \
                 OptionType.rec KExpr (fun (z : {O}) => {gz}) {none_arm} \
                 (fun (f2 : KExpr) => Eq.refl ({O}) (OptionType.some KExpr (KExpr.app f2 a))) o",
                g = goal("o"),
                gz = goal("z"),
            );
            debug_assert!(Self::balanced(&src), "{name} parens");
            self.add_recursive_def(
                &src,
                &format!(
                    "{name}: opt_app_ilift does not consult the pre-pass here. The some branch \
                     never mentions wh, and the none branch is iota, which cannot fire because \
                     {why} — at either budget. One of the two fences that confine the step's \
                     budget-dependence to a const-headed spine with a none head-reduct. \
                     DerivedProved, zero axiom_deps."
                ),
            )?;
        }
        Ok(())
    }

    /// A head that is not a constant: the step is budget-independent outright.
    fn add_no_name_indep(&mut self) -> Result<(), SpecError> {
        let goal = |x: &str| {
            format!(
                "Eq ({O}) (reduce_app_head_red_wh the_red_env wh1 a {x} cf) \
                 (reduce_app_head_red_wh the_red_env wh2 a {x} cf)"
            )
        };
        let mot = |x: &str| format!("({} -> {})", head_none(x), goal(x));
        let via = |term: &str, binders: &str| {
            format!(
                "(fun {binders} (h : {hn}) => \
                 opt_app_ilift_no_head_congr wh1 wh2 {term} a h cf)",
                hn = head_none(term),
            )
        };
        let arms = [
            via("(KExpr.sort n)", "(n : Level)"),
            via("(KExpr.bvar i)", "(i : Nat)"),
            via(
                "(KExpr.app g b)",
                &format!(
                    "(g : KExpr) (b : KExpr) (_c1 : {}) (_c2 : {})",
                    mot("g"),
                    mot("b")
                ),
            ),
            // Beta, not iota: this arm ignores cf and wh together.
            format!(
                "(fun (ty : KExpr) (b : KExpr) (_c1 : {mty}) (_c2 : {mb}) (_h : {hl}) => \
                 Eq.refl ({O}) (OptionType.some KExpr (instantiate b a)))",
                mty = mot("ty"),
                mb = mot("b"),
                hl = head_none("(KExpr.lam ty b)"),
            ),
            via(
                "(KExpr.pi ty b)",
                &format!(
                    "(ty : KExpr) (b : KExpr) (_c1 : {}) (_c2 : {})",
                    mot("ty"),
                    mot("b")
                ),
            ),
            // A bare constant DOES have a head name, contradicting the branch.
            format!(
                "(fun (cn : Name) (us : ListType Level) (h : {hc}) => \
                 option_none_ne_some Name cn ({g}) \
                 (Eq.symm (OptionType Name) (OptionType.some Name cn) (OptionType.none Name) h))",
                hc = head_none("(KExpr.const cn us)"),
                g = goal("(KExpr.const cn us)"),
            ),
            via(
                "(KExpr.let_ ty v b)",
                &format!(
                    "(ty : KExpr) (v : KExpr) (b : KExpr) (_c1 : {}) (_c2 : {}) (_c3 : {})",
                    mot("ty"),
                    mot("v"),
                    mot("b")
                ),
            ),
            via(
                "(KExpr.proj s i sub)",
                &format!("(s : Name) (i : Nat) (sub : KExpr) (_cs : {})", mot("sub")),
            ),
            via("(KExpr.lit v)", "(v : Nat)"),
        ];
        let src = format!(
            "def reduce_app_head_no_name_wh_indep (wh1 : KExpr -> OptionType KExpr) \
             (wh2 : KExpr -> OptionType KExpr) (a : KExpr) (cf : {O}) (f : KExpr) : {motf} := \
             KExpr.rec (fun (x : KExpr) => {motx}) {arms} f",
            motf = mot("f"),
            motx = mot("x"),
            arms = arms.join(" "),
        );
        debug_assert!(Self::balanced(&src), "no-name indep parens");
        self.add_recursive_def(
            &src,
            "reduce_app_head_no_name_wh_indep: when the head is not a constant, the step is \
             budget-independent. Nine arms: the lam arm is BETA, which ignores the head-reduct \
             and the pre-pass alike; the const arm contradicts the branch hypothesis, since a \
             bare constant does carry a head name; the remaining seven route through the \
             level-one iota exit. \
             \
             The first of the two fences. Together with under_applied_step_congr it leaves only a \
             const-headed spine, long enough to have a major premise, with a none head-reduct — \
             which is exactly the iota slot. DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }

    /// A const spine one argument short: the step is budget-independent.
    fn add_under_applied_congr(&mut self) -> Result<(), SpecError> {
        let congr = |x: &str| format!("Eq ({O}) {} {}", step("wh1", x), step("wh2", x));
        let bound = |x: &str| format!("Le (list_length (kapp_args {x})) {MAJOR_IDX}");
        let mot = |x: &str| format!("({} -> {} -> {})", head_is(x), bound(x), congr(x));
        let refl = |binders: &str, val: &str, term: &str| {
            format!(
                "(fun {binders} (_h : {h}) (_hl : {b}) => Eq.refl ({O}) {val})",
                h = head_is(term),
                b = bound(term),
            )
        };
        let none = "(OptionType.none KExpr)";
        let lenf = "(list_length (kapp_args f))";
        // The bound descends to the head: one more argument is one more length.
        let hlf = format!(
            "(le_succ_weaken {lenf} {MAJOR_IDX} (Eq.substType Nat \
             (fun (z : Nat) => Le z {MAJOR_IDX}) \
             (list_length (kapp_args (KExpr.app f a))) (Nat.succ {lenf}) \
             (kapp_args_length_app f a) hl))"
        );
        let app_arm = format!(
            "(fun (f : KExpr) (a : KExpr) (ihf : {motf}) (_iha : {mota}) (h : {hh}) (hl : {hb}) => \
             Eq.trans ({O}) {s1} {i1} {s2} \
             (reduce_app_head_const_is_ilift wh1 a {sf1} nm f h) \
             (Eq.trans ({O}) {i1} {i2} {s2} \
             (Eq.cong ({O}) ({O}) (fun (z : {O}) => {iz}) {sf1} {sf2} (ihf h {hlf})) \
             (Eq.trans ({O}) {i2} {i3} {s2} \
             (opt_app_ilift_no_major_congr wh1 wh2 nm meta f a h hrm \
             (list_head_drop_none_of_le {MAJOR_IDX} (kapp_args (KExpr.app f a)) hl) {sf2}) \
             (Eq.symm ({O}) {s2} {i3} \
             (reduce_app_head_const_is_ilift wh2 a {sf2} nm f h)))))",
            motf = mot("f"),
            mota = mot("a"),
            hh = head_is("(KExpr.app f a)"),
            hb = bound("(KExpr.app f a)"),
            s1 = step("wh1", "(KExpr.app f a)"),
            s2 = step("wh2", "(KExpr.app f a)"),
            sf1 = step("wh1", "f"),
            sf2 = step("wh2", "f"),
            i1 = ilift("wh1", "f", &step("wh1", "f")),
            i2 = ilift("wh1", "f", &step("wh2", "f")),
            i3 = ilift("wh2", "f", &step("wh2", "f")),
            iz = ilift("wh1", "f", "z"),
        );
        let arms = [
            refl("(n : Level)", none, "(KExpr.sort n)"),
            refl("(i : Nat)", none, "(KExpr.bvar i)"),
            app_arm,
            refl(
                &format!(
                    "(ty : KExpr) (b : KExpr) (_c1 : {}) (_c2 : {})",
                    mot("ty"),
                    mot("b")
                ),
                none,
                "(KExpr.lam ty b)",
            ),
            refl(
                &format!(
                    "(ty : KExpr) (b : KExpr) (_c1 : {}) (_c2 : {})",
                    mot("ty"),
                    mot("b")
                ),
                none,
                "(KExpr.pi ty b)",
            ),
            refl(
                "(cn : Name) (us : ListType Level)",
                "(defval_for (red_def the_red_env) cn)",
                "(KExpr.const cn us)",
            ),
            refl(
                &format!(
                    "(ty : KExpr) (v : KExpr) (b : KExpr) (_c1 : {}) (_c2 : {}) (_c3 : {})",
                    mot("ty"),
                    mot("v"),
                    mot("b")
                ),
                "(OptionType.some KExpr (instantiate b v))",
                "(KExpr.let_ ty v b)",
            ),
            // A projection carries no head name, so this branch is impossible.
            format!(
                "(fun (s : Name) (i : Nat) (sub : KExpr) (_cs : {ms}) (h : {hp}) (_hl : {bp}) => \
                 option_none_ne_some Name nm ({cp}) h)",
                ms = mot("sub"),
                hp = head_is("(KExpr.proj s i sub)"),
                bp = bound("(KExpr.proj s i sub)"),
                cp = congr("(KExpr.proj s i sub)"),
            ),
            refl("(v : Nat)", none, "(KExpr.lit v)"),
        ];
        let src = format!(
            "def under_applied_step_congr (wh1 : KExpr -> OptionType KExpr) \
             (wh2 : KExpr -> OptionType KExpr) (nm : Name) (meta : RecMeta) \
             (hrm : Eq (OptionType RecMeta) (recmeta_for {RR} nm) \
             (OptionType.some RecMeta meta)) (e : KExpr) : {mote} := \
             KExpr.rec (fun (x : KExpr) => {motx}) {arms} e",
            mote = mot("e"),
            motx = mot("x"),
            arms = arms.join(" "),
        );
        debug_assert!(Self::balanced(&src), "under-applied congr parens");
        self.add_recursive_def(
            &src,
            "under_applied_step_congr: on a const spine one argument short of its major premise, \
             the step ignores the pre-pass entirely. \
             \
             Seven of nine arms are free — sort, bvar, lam, pi and lit give none on both sides, \
             const gives the same value lookup, let_ the same zeta-contraction, and proj is \
             impossible because a projection carries no head name. Only app does work, and there \
             the content is that opt_app_ilift's some branch never consults the pre-pass while \
             its none branch is iota, which an under-applied spine cannot fire at ANY budget. The \
             bound descends from (app f a) to f by kapp_args_length_app and le_succ_weaken, which \
             is how the recursion reaches the head. \
             \
             The second fence. This is what kills the dangerous case of step monotonicity: when \
             the major premise is the outermost argument, the shorter spine is under-applied \
             however much fuel the pre-pass is given, so its head-reduct cannot flip from none to \
             some and send the step down a different branch. DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {

    /// Every goal here concludes in `Eq`, so the `Sort 1` helpers are wrong.
    #[test]
    fn test_no_sort_one_helpers() {
        let src = include_str!("wh_step_mono.rs");
        let body = src.split("mod tests").next().expect("module body");
        let code = body
            .lines()
            .filter(|l| !l.trim_start().starts_with("//"))
            .collect::<Vec<_>>()
            .join("\n");
        assert!(
            !code.contains("option_none_ne_some_type"),
            "goals here are Eq (Sort 0); the _type helper demands Sort 1"
        );
    }

    /// Both fences must be present. Dropping either would leave a case of step
    /// monotonicity where the head-reduct can flip and the step change answer.
    #[test]
    fn test_both_fences_exist() {
        let src = include_str!("wh_step_mono.rs");
        for fence in [
            "reduce_app_head_no_name_wh_indep",
            "under_applied_step_congr",
        ] {
            assert!(src.contains(fence), "missing fence: {fence}");
        }
    }

    /// The ι exits must be APPLIED. An earlier staging carried the level-one
    /// exit as a hypothesis so the shape could be validated before it existed;
    /// shipping that would leave an assumed premise in the tree for no reason.
    #[test]
    fn test_iota_exits_are_applied_not_assumed() {
        let src = include_str!("wh_step_mono.rs");
        let body = src.split("mod tests").next().expect("module body");
        for exit in [
            "iota_reduct_whc_none_of_no_head",
            "iota_reduct_whc_none_of_no_major",
        ] {
            assert!(body.contains(exit), "the {exit} exit must be applied here");
        }
        assert!(
            !body.contains("(hnoh :"),
            "the level-one exit is proved; it must not be carried as a hypothesis"
        );
    }
}
