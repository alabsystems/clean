// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The under-application boundary, at the list level.
//!
//! ## What this is for
//!
//! Step monotonicity — a step that fires at one budget fires the same way at
//! the next — turns on one awkward case. `opt_app_ilift` branches on the
//! head-reduct `cf`: `none` tries ι, `some f2` takes the congruence instead. If
//! `cf` could flip `none → some` when the budget grows, the step would return a
//! *different* result and monotonicity would be false.
//!
//! `cf` does flip in general — that is exactly what starvation does. It cannot
//! flip *here*, and the reason is arithmetic rather than semantic: `f` and
//! `app f a` share a spine head, hence share `recmeta`, hence share
//! `MAJOR_IDX`. Either the major premise sits inside `f`'s own arguments — in
//! which case ι firing on `app f a` at a budget means it fired on `f` at that
//! budget too, so `cf` was never `none` — or the major *is* the outermost
//! argument, in which case `f` is one argument short at **every** budget and
//! `cf` cannot move.
//!
//! This module carries the second half: what it means to be one argument short.
//!
//! ## Why a new list lemma was needed
//!
//! The tree already knows about the boundary from *above*: `list_drop_append_ge`
//! and `list_drop_append_gen` both describe dropping at or past the split point,
//! and `list_head_drop_some_le_succ` reads a length bound out of a successful
//! lookup. Nothing described dropping *below* the split, which is what
//! identifies `app f a`'s major premise with `f`'s own — the two lists differ
//! only by an argument appended at the far end, well past the index being read.
//!
//! `DerivedProved`, empty axiom closures.

use crate::spec::error::SpecError;
use crate::spec::Specification;

/// The lookup at the boundary index.
const HD: &str = "(list_head (list_drop k xs))";

impl Specification {
    /// The list-level boundary facts.
    pub(super) fn add_wh_under_applied(&mut self) -> Result<(), SpecError> {
        self.add_head_drop_none_of_le()?;
        self.add_drop_append_lt()?;
        self.add_spine_length_app()?;
        self.add_app_head_shape()?;
        Ok(())
    }

    /// Dropping BELOW the split point commutes with append.
    ///
    /// The tree knows the boundary only from above — `list_drop_append_ge` and
    /// `list_drop_append_gen` both drop at or past the split. This is the other
    /// side, and it is what identifies `app f a`'s major premise with `f`'s own:
    /// the two argument lists differ by one element appended at the far end,
    /// well past the index being read, so the lookup cannot tell them apart.
    ///
    /// Induction on the index with the list universally quantified, so the
    /// hypothesis is available at the tail. Both sides step past the head
    /// definitionally — `list_append` recurses on its first argument and
    /// `list_drop` on its index — so the cons case IS the induction hypothesis,
    /// modulo turning `Le (succ (succ m)) (succ (length rest))` into
    /// `Le (succ m) (length rest)` with `le_pred_pred`.
    fn add_drop_append_lt(&mut self) -> Result<(), SpecError> {
        let l = "ListType KExpr";
        let goal = |k: &str, xs: &str| {
            format!(
                "Eq ({l}) (list_drop {k} (list_append {xs} ys)) \
                 (list_append (list_drop {k} {xs}) ys)"
            )
        };
        let mot = format!(
            "forall (xs : {l}) (ys : {l}), Le (Nat.succ m) (list_length xs) -> {g}",
            g = goal("m", "xs"),
        );
        let inner = format!(
            "(fun (l : {l}) => Le (Nat.succ (Nat.succ m)) (list_length l) -> {g})",
            g = goal("(Nat.succ m)", "l"),
        );
        let nil_arm = format!(
            "(fun (h0 : Le (Nat.succ (Nat.succ m)) (list_length (ListType.nil KExpr))) => \
             Empty.rec (fun (_ : Empty) => {g}) (le_succ_zero_empty (Nat.succ m) h0))",
            g = goal("(Nat.succ m)", "(ListType.nil KExpr)"),
        );
        let cons_arm = format!(
            "(fun (x : KExpr) (rest : {l}) \
             (_ihr : Le (Nat.succ (Nat.succ m)) (list_length rest) -> {g}) \
             (h1 : Le (Nat.succ (Nat.succ m)) (list_length (ListType.cons KExpr x rest))) => \
             ih rest ys (le_pred_pred (Nat.succ m) (list_length rest) h1))",
            g = goal("(Nat.succ m)", "rest"),
        );
        let src = format!(
            "def list_drop_append_lt (k : Nat) : forall (xs : {l}) (ys : {l}), \
             Le (Nat.succ k) (list_length xs) -> {gk} := \
             Nat.rec (fun (m : Nat) => {mot}) \
             (fun (xs : {l}) (ys : {l}) (_h : Le (Nat.succ Nat.zero) (list_length xs)) => \
             Eq.refl ({l}) (list_append xs ys)) \
             (fun (m : Nat) (ih : {mot}) (xs : {l}) (ys : {l}) \
             (h : Le (Nat.succ (Nat.succ m)) (list_length xs)) => \
             ListType.rec KExpr {inner} {nil_arm} {cons_arm} xs h) k",
            gk = goal("k", "xs"),
        );
        debug_assert!(Self::balanced(&src), "drop append lt parens");
        self.add_recursive_def(
            &src,
            "list_drop_append_lt: dropping BELOW the split point commutes with append. The tree \
             had only the at-or-past-split direction (list_drop_append_ge, list_drop_append_gen); \
             this is the other side. \
             \
             It is what lets the major premise of (app f a) be identified with f's own: the two \
             argument lists differ by a single element appended at the far end, and the index \
             being read sits before it, so the lookup cannot distinguish them. That identification \
             is the first half of the boundary argument step monotonicity needs — if the major \
             lies inside f's arguments then iota firing on (app f a) at a budget means it fired on \
             f at that budget too. DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }

    /// One more argument makes the spine one longer.
    ///
    /// `kapp_args_app` says the argument list of `app f a` is `f`'s with `a`
    /// appended; this reads the length off that. It is what lets the
    /// under-application bound descend from `app f a` to `f` (via
    /// `le_succ_weaken`), which is how the spine recursion keeps its hypothesis.
    fn add_spine_length_app(&mut self) -> Result<(), SpecError> {
        let snoc = "(list_append (kapp_args f) (ListType.cons KExpr a (ListType.nil KExpr)))";
        let src = format!(
            "def kapp_args_length_app (f : KExpr) (a : KExpr) : Eq Nat \
             (list_length (kapp_args (KExpr.app f a))) (Nat.succ (list_length (kapp_args f))) := \
             Eq.trans Nat (list_length (kapp_args (KExpr.app f a))) (list_length {snoc}) \
             (Nat.succ (list_length (kapp_args f))) \
             (Eq.cong (ListType KExpr) Nat (fun (l : ListType KExpr) => list_length l) \
             (kapp_args (KExpr.app f a)) {snoc} (kapp_args_app f a)) \
             (list_append_length (kapp_args f) (ListType.cons KExpr a (ListType.nil KExpr)))"
        );
        debug_assert!(Self::balanced(&src), "spine length app parens");
        self.add_recursive_def(
            &src,
            "kapp_args_length_app: applying one more argument lengthens the spine by one. Reads \
             the length off kapp_args_app through list_append_length. This is what lets the \
             under-application bound descend from (app f a) to f by le_succ_weaken, which is how \
             the spine recursion carries its hypothesis to the head. DerivedProved, zero \
             axiom_deps.",
        )?;
        Ok(())
    }

    /// How the step treats an application, by the shape of its head.
    ///
    /// Two facts, both nine-arm recursions on the head, both closing almost
    /// everywhere by reflexivity. Together they say the step's dependence on the
    /// pre-pass is confined to one place: a `none` head-reduct under a
    /// const-shaped head, which is exactly the ι slot.
    fn add_app_head_shape(&mut self) -> Result<(), SpecError> {
        let o = "OptionType KExpr";
        let head = |x: &str| {
            format!(
                "Eq (OptionType Name) (kexpr_const_name (kapp_fn {x})) (OptionType.some Name nm)"
            )
        };
        let goal = |x: &str| {
            format!(
                "Eq ({o}) (reduce_app_head_red_wh the_red_env wh a {x} cf) \
                 (opt_app_ilift_wh the_red_env wh {x} a cf)"
            )
        };
        let mot = |x: &str| format!("({} -> {})", head(x), goal(x));
        let dead = |term: &str, binders: &str| {
            format!(
                "(fun {binders} (h : {hd}) => option_none_ne_some Name nm ({g}) h)",
                hd = head(term),
                g = goal(term),
            )
        };
        // Keyed on the HEAD NAME, not on neutrality: the congruence below needs
        // this for spines whose head may well have a defval, where is_neutral_red
        // does not apply. The lam arm is beta and genuinely differs, which is why
        // it must go through the head-lookup being impossible rather than refl.
        let arms = [
            dead("(KExpr.sort n)", "(n : Level)"),
            dead("(KExpr.bvar i)", "(i : Nat)"),
            format!(
                "(fun (g : KExpr) (b : KExpr) (_c1 : {mg}) (_c2 : {mb}) (_h : {hab}) => \
                 Eq.refl ({o}) (opt_app_ilift_wh the_red_env wh (KExpr.app g b) a cf))",
                mg = mot("g"),
                mb = mot("b"),
                hab = head("(KExpr.app g b)"),
            ),
            dead(
                "(KExpr.lam ty b)",
                &format!(
                    "(ty : KExpr) (b : KExpr) (_c1 : {}) (_c2 : {})",
                    mot("ty"),
                    mot("b")
                ),
            ),
            dead(
                "(KExpr.pi ty b)",
                &format!(
                    "(ty : KExpr) (b : KExpr) (_c1 : {}) (_c2 : {})",
                    mot("ty"),
                    mot("b")
                ),
            ),
            format!(
                "(fun (cn : Name) (us : ListType Level) (_h : {hc}) => \
                 Eq.refl ({o}) (opt_app_ilift_wh the_red_env wh (KExpr.const cn us) a cf))",
                hc = head("(KExpr.const cn us)"),
            ),
            dead(
                "(KExpr.let_ ty v b)",
                &format!(
                    "(ty : KExpr) (v : KExpr) (b : KExpr) (_c1 : {}) (_c2 : {}) (_c3 : {})",
                    mot("ty"),
                    mot("v"),
                    mot("b")
                ),
            ),
            dead(
                "(KExpr.proj s i sub)",
                &format!("(s : Name) (i : Nat) (sub : KExpr) (_cs : {})", mot("sub")),
            ),
            dead("(KExpr.lit v)", "(v : Nat)"),
        ];
        let src = format!(
            "def reduce_app_head_const_is_ilift (wh : KExpr -> OptionType KExpr) (a : KExpr) \
             (cf : {o}) (nm : Name) (f : KExpr) : {motf} := \
             KExpr.rec (fun (x : KExpr) => {motx}) {arms} f",
            motf = mot("f"),
            motx = mot("x"),
            arms = arms.join(" "),
        );
        debug_assert!(Self::balanced(&src), "app head ilift parens");
        self.add_recursive_def(
            &src,
            "reduce_app_head_const_is_ilift: a CONST-HEADED application takes the opt_app_ilift \
             branch. Nine-arm recursion on the head; const and app close by reflexivity and the \
             other seven because a head name is impossible there. Keyed on the head NAME rather \
             than on neutrality, because the spine congruence needs it for heads that may still \
             carry a definitional value, where is_neutral_red does not apply. The lam arm is beta \
             and genuinely differs from ilift, which is why it too goes through the impossible \
             head lookup. DerivedProved, zero axiom_deps.",
        )?;

        // When the head-reduct is SOME the step never consults the pre-pass:
        // every non-lam arm takes the congruence branch and lam is beta.
        let gsome = |x: &str| {
            format!(
                "Eq ({o}) (reduce_app_head_red_wh the_red_env wh1 a {x} (OptionType.some KExpr f2)) \
                 (reduce_app_head_red_wh the_red_env wh2 a {x} (OptionType.some KExpr f2))"
            )
        };
        let cong = format!("Eq.refl ({o}) (OptionType.some KExpr (KExpr.app f2 a))");
        let arms2 = [
            format!("(fun (n : Level) => {cong})"),
            format!("(fun (i : Nat) => {cong})"),
            format!("(fun (g : KExpr) (b : KExpr) (_c1 : {}) (_c2 : {}) => {cong})", gsome("g"), gsome("b")),
            format!(
                "(fun (ty : KExpr) (b : KExpr) (_c1 : {}) (_c2 : {}) => \
                 Eq.refl ({o}) (OptionType.some KExpr (instantiate b a)))",
                gsome("ty"), gsome("b"),
            ),
            format!("(fun (ty : KExpr) (b : KExpr) (_c1 : {}) (_c2 : {}) => {cong})", gsome("ty"), gsome("b")),
            format!("(fun (cn : Name) (us : ListType Level) => {cong})"),
            format!(
                "(fun (ty : KExpr) (v : KExpr) (b : KExpr) (_c1 : {}) (_c2 : {}) (_c3 : {}) => {cong})",
                gsome("ty"), gsome("v"), gsome("b"),
            ),
            format!("(fun (s : Name) (i : Nat) (sub : KExpr) (_cs : {}) => {cong})", gsome("sub")),
            format!("(fun (v : Nat) => {cong})"),
        ];
        let src = format!(
            "def reduce_app_head_some_cf_wh_indep (wh1 : KExpr -> OptionType KExpr) \
             (wh2 : KExpr -> OptionType KExpr) (a : KExpr) (f2 : KExpr) (f : KExpr) : {gf} := \
             KExpr.rec (fun (x : KExpr) => {gx}) {arms} f",
            gf = gsome("f"),
            gx = gsome("x"),
            arms = arms2.join(" "),
        );
        debug_assert!(Self::balanced(&src), "app head some-cf parens");
        self.add_recursive_def(
            &src,
            "reduce_app_head_some_cf_wh_indep: when the head-reduct is SOME, the step does not \
             consult the pre-pass at all. Every non-lam arm takes opt_app_ilift's congruence \
             branch, some (app f2 a), and the lam arm is beta — neither mentions wh, so all nine \
             arms are reflexivity. \
             \
             This is the easy half of the app arm of step monotonicity: once the head-reduct is \
             known to be some, raising the budget cannot change what the step returns. The hard \
             half is the none case, where iota is reachable. DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }

    /// Nothing sits at or past the end: a spine shorter than the index has no
    /// argument there.
    ///
    /// The converse reading of `list_head_drop_some_le_succ`, obtained by
    /// convoy rather than by a second induction — if the lookup succeeded it
    /// would force `Le (succ k) (length xs)`, which with the under-application
    /// bound gives `Le (succ k) k`.
    fn add_head_drop_none_of_le(&mut self) -> Result<(), SpecError> {
        let o = "OptionType KExpr";
        let goal = format!("Eq ({o}) {HD} (OptionType.none KExpr)");
        let src = format!(
            "def list_head_drop_none_of_le (k : Nat) (xs : ListType KExpr) \
             (hle : Le (list_length xs) k) : {goal} := \
             OptionType.rec KExpr (fun (o : {o}) => Eq ({o}) {HD} o -> {goal}) \
             (fun (h : Eq ({o}) {HD} (OptionType.none KExpr)) => h) \
             (fun (y : KExpr) (h : Eq ({o}) {HD} (OptionType.some KExpr y)) => \
             Empty.rec (fun (_ : Empty) => {goal}) \
             (le_succ_self_empty k (le_trans (Nat.succ k) (list_length xs) k \
             (list_head_drop_some_le_succ k xs y h) hle))) \
             {HD} (Eq.refl ({o}) {HD})"
        );
        debug_assert!(Self::balanced(&src), "head drop none parens");
        self.add_recursive_def(
            &src,
            "list_head_drop_none_of_le: a list at or shorter than the index has nothing there. \
             Convoy on the lookup: none is already the goal, and some y would force \
             Le (succ k) (list_length xs) by list_head_drop_some_le_succ, which against the \
             under-application bound Le (list_length xs) k transits to Le (succ k) k and is \
             absurd. \
             \
             This is the list-level statement of `one argument short`, which is what makes an \
             under-applied recursor spine unable to fire iota at ANY budget — the property step \
             monotonicity needs when the major premise is the outermost argument, since a spine \
             one argument shorter than the boundary stays that way however much fuel the pre-pass \
             is given. DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {

    /// `Eq`-valued goals take the `Sort 0` helpers.
    #[test]
    fn test_no_sort_one_helpers() {
        let src = include_str!("wh_under_applied.rs");
        let body = src.split("mod tests").next().expect("module body");
        let code = body
            .lines()
            .filter(|l| !l.trim_start().starts_with("//"))
            .collect::<Vec<_>>()
            .join("\n");
        for banned in ["option_none_ne_some_type", "Eq.substType"] {
            assert!(
                !code.contains(banned),
                "{banned} demands Sort 1; every goal here concludes in Eq (Sort 0)"
            );
        }
    }

    /// The bound must be consumed, not merely carried. A version that ignored
    /// `hle` would be claiming the lookup is empty at every index.
    #[test]
    fn test_the_length_bound_is_used() {
        let src = include_str!("wh_under_applied.rs");
        let body = src.split("mod tests").next().expect("module body");
        assert!(
            body.contains("(list_head_drop_some_le_succ k xs y h) hle"),
            "the under-application bound must feed the transitivity that closes the some case"
        );
    }
}
