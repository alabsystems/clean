// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The first layer that was blocked by FALSITY, now reachable.
//!
//! `def_eq_fuel_succ_mono` closes its critical step with
//! `whnf_fuel_red_monotone` applied to both whnf legs. For the two-way faithful
//! loop that lemma is REFUTED (`whnf_fuel_red_wh_monotone_is_false`), so the
//! layer could not be ported — not because it was hard, but because what it
//! needed does not exist.
//!
//! For the three-way loop it does: `whnf_fuel_red_wh3_monotone`. So this module
//! DERIVES the algorithm-side monotonicity from the original source by
//! identifier substitution, changing nothing about the argument.
//!
//! ## Why it is derived rather than retrofitted
//!
//! The original declaration is read and left alone. An earlier attempt today
//! parameterised a long-proved declaration in place to emit both variants from
//! one source, and broke the original — the blast radius of a retrofit is the
//! existing proof, not the new one. Deriving into a NEW declaration keeps that
//! risk at zero.
//!
//! The substitution is a SINGLE simultaneous regex pass over whole identifiers,
//! longest-first. A sequential pass would double-apply: rewriting
//! `def_eq_fuel_succ` to `def_eq_fuel_wh3_succ` and then `def_eq_fuel` to
//! `def_eq_fuel_wh3` yields `def_eq_fuel_wh3_wh3_succ`. Assertions afterwards
//! check that no two-way identifier survives and that the monotonicity call was
//! actually redirected — the one substitution the whole layer turns on.
//!
//! `DerivedProved`, empty axiom closure.

use crate::spec::error::SpecError;
use crate::spec::Specification;

impl Specification {
    /// Algorithm-side fuel monotonicity, over the three-way loop.
    pub(super) fn add_defeq_fuel_wh3_mono(&mut self) -> Result<(), SpecError> {
        self.add_wh3_of_struct()?;
        let src = Self::retarget_to_wh3(&Self::def_eq_fuel_succ_mono_src());
        assert!(
            src.contains("whnf_fuel_red_wh3_monotone"),
            "the whole point of this layer is redirecting the monotonicity call"
        );
        assert!(
            !src.contains("whnf_fuel_red_monotone"),
            "no call to the REFUTED two-way monotonicity may survive"
        );
        debug_assert!(Self::balanced(&src), "wh3 succ-mono parens");
        self.add_recursive_def(
            &src,
            "def_eq_fuel_wh3_succ_mono: what the conversion algorithm accepts at one fuel it still \
             accepts at the next — over the THREE-WAY loop. \
             \
             The argument is the original's, unchanged: Nat.rec on the fuel, the zero arm absurd \
             by failing closed, and the successor arm inverting both whnf legs, raising them one \
             fuel, and refolding with def_eq_fuel_of_struct while def_eq_struct_mono carries the \
             comparator. Seven of its eight moving parts were always substitution-clean. \
             \
             The eighth was not. It applies fuel monotonicity to each whnf leg, and for the \
             two-way faithful loop that lemma is refuted by computation — some at one budget, none \
             at the next, because a starved pre-pass is indistinguishable from genuine stuckness. \
             This layer was blocked by FALSITY. Separating wstarved from wstuck makes \
             whnf_fuel_red_wh3_monotone true, and the step closes. \
             \
             def_eq_struct_mono needs no port at all: it is parametric in its comparator. \
             DerivedProved, zero axiom_deps.",
        )?;
        self.add_wh3_le()?;
        self.add_wh3_pairing()?;
        // BEFORE the steps: these are the recursion's base cases, and without
        // them the three-way acceptance predicate has no introduction rule that
        // does not already consume one.
        self.add_wh3_complete_leaves()?;
        self.add_wh3_complete_steps()?;
        Ok(())
    }

    /// The four LEAVES, over the three-way algorithm — the recursion's base
    /// cases, and the reason the four steps above it are not decorations.
    ///
    /// Every `def_eq_complete_step_wh3_*` consumes a `DefEqFuelAcceptsWh3` and
    /// produces one. On their own that is consistent with the predicate being
    /// **empty**, in which case all four are theorems about nothing — and no
    /// axiom ratchet detects it, because a theorem about an uninhabited
    /// predicate has an impeccably empty axiom closure. These are the
    /// introduction rules that do not presuppose their own conclusion.
    ///
    /// Retargeted from `complete_leaf_decls` rather than rewritten, so the two
    /// families cannot drift and a fix to a leaf's transport lands in both.
    fn add_wh3_complete_leaves(&mut self) -> Result<(), SpecError> {
        for src in Self::wh3_complete_leaf_srcs() {
            let head = src
                .split_whitespace()
                .nth(1)
                .and_then(|n| n.rsplit('_').next().map(str::to_owned))
                .unwrap_or_default();
            self.add_recursive_def(
                &src,
                &format!(
                    "def_eq_complete_leaf_wh3_{head}: the completeness recursion's {head} LEAF \
                     over the THREE-WAY algorithm — a head with nothing to recurse into, and so \
                     an introduction rule for DefEqFuelAcceptsWh3 that does not already consume \
                     one. \
                     \
                     Mechanically retargeted from the two-way leaf: same proof, same transports, \
                     with whnf_fuel_red_wh3 for whnf_fuel_red and def_eq_fuel_wh3_of_struct for \
                     def_eq_fuel_of_struct. The grid compares {head} payloads SYNTACTICALLY, so \
                     completeness here needs them to agree, and that equality is a hypothesis \
                     rather than derived — deriving it needs the common reduct and both legs, \
                     which are in scope at the capstone's call site and not here. \
                     \
                     The struct layer is parametric in its comparator, which is why \
                     def_eq_struct_intro_{head} needs no three-way counterpart and is cited \
                     unchanged. DerivedProved, zero axiom_deps."
                ),
            )?;
        }
        Ok(())
    }

    /// The four completeness steps, over the three-way algorithm.
    ///
    /// Registered here rather than beside the two-way steps: these cite
    /// `whnf_fuel_red_wh3_le` and the five names above, none of which exist at
    /// the point `add_defeq_complete_steps` runs. Placing them there would fail
    /// on undefined names — the ordering failure that broke `main` earlier in
    /// this programme.
    ///
    /// The shape table's congruence field has no three-way counterpart, and none
    /// was invented: `def_eq_fuel_pi_cong` is itself a one-line composition of
    /// `def_eq_fuel_of_struct` with a comparator-parametric introduction rule, so
    /// the composition is inlined at the common bound. Both routes are the same
    /// proof.
    fn add_wh3_complete_steps(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            SRC_WH3_STEP_PI,
            "def_eq_complete_step_wh3_pi: the pi completeness step over the three-way algorithm. Both whnf legs are raised from n to n + k, both component acceptances from k to n + k, and \
             the structural introduction rule closes at the common bound. \
             \
             The leg raise uses whnf_fuel_red_wh3_le, which carries NO stuckness premise \
             — the two-way counterpart does, and discharging it is free at pi and lam but not at \
             app or proj, which is what made this layer unportable. DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(
            SRC_WH3_STEP_LAM,
            "def_eq_complete_step_wh3_lam: the lam completeness step over the three-way algorithm. Both whnf legs are raised from n to n + k, both component acceptances from k to n + k, and \
             the structural introduction rule closes at the common bound. \
             \
             The leg raise uses whnf_fuel_red_wh3_le, which carries NO stuckness premise \
             — the two-way counterpart does, and discharging it is free at pi and lam but not at \
             app or proj, which is what made this layer unportable. DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(
            SRC_WH3_STEP_APP,
            "def_eq_complete_step_wh3_app: the app completeness step over the three-way algorithm. Both whnf legs are raised from n to n + k, both component acceptances from k to n + k, and \
             the structural introduction rule closes at the common bound. \
             \
             The leg raise uses whnf_fuel_red_wh3_le, which carries NO stuckness premise \
             — the two-way counterpart does, and discharging it is free at pi and lam but not at \
             app or proj, which is what made this layer unportable. DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(
            SRC_WH3_STEP_PROJ,
            "def_eq_complete_step_wh3_proj: the proj completeness step over the three-way algorithm. Both whnf legs are raised from n to n + k, both component acceptances from k to n + k, and \
             the structural introduction rule closes at the common bound. \
             \
             The leg raise uses whnf_fuel_red_wh3_le, which carries NO stuckness premise \
             — the two-way counterpart does, and discharging it is free at pi and lam but not at \
             app or proj, which is what made this layer unportable. DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }

    /// Fuel pairing, over the three-way algorithm.
    ///
    /// Two acceptances obtained independently arrive at unrelated fuels; the
    /// completeness recursion needs them at one. The bound is n1 + n2 rather
    /// than a maximum, for the same reason the original gives: the two addition
    /// bounds already exist where a maximum would be a small development, and
    /// fuel is a bound, not a measure.
    ///
    /// This is the half of fuel_pairing that could NOT be ported. It pivots on
    /// def_eq_fuel_le, which rests on the successor step, which rests on whnf-leg
    /// monotonicity — refuted for the two-way loop.
    fn add_wh3_pairing(&mut self) -> Result<(), SpecError> {
        self.add_inductive(
            SRC_WH3_ACCEPTS,
            "DefEqFuelAcceptsWh3 a b: some fuel is enough for the three-way algorithm to accept a \
             against b. Unlike DefEqFuelAcceptsWh, this witness IS upward-closed, because \
             def_eq_fuel_wh3_le can raise it — the two-way version is not, and any layer that \
             read it as upward-closed was assuming a false statement. Census-neutral.",
        )?;
        self.add_inductive(
            SRC_WH3_ACCEPTS_PAIR,
            "DefEqFuelAcceptsPairWh3: two acceptances at ONE shared fuel. The paired witness type \
             exists because each single witness hides its own fuel inside a constructor, so the \
             common bound cannot be supplied by the caller. Census-neutral.",
        )?;
        debug_assert!(Self::balanced(SRC_WH3_PAIR), "wh3 pairing parens");
        self.add_recursive_def(
            SRC_WH3_PAIR,
            "def_eq_fuel_wh3_accepts_pair: two independent acceptances yield ONE fuel that works \
             for both, by raising each to n1 + n2 with def_eq_fuel_wh3_le. \
             \
             THE HALF OF fuel_pairing THAT COULD NOT BE PORTED. It pivots on the Le form, which \
             iterates the successor step, which applies monotonicity to each whnf leg — refuted \
             for the two-way loop by computation. Available here because the three-way loop is \
             monotone. DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }

    /// The Le form, iterating the successor step.
    ///
    /// This is what fuel pairing consumes: two independently-obtained
    /// acceptances arrive at unrelated fuels and must be raised to a common
    /// bound. For the two-way algorithm that raise is impossible, because the
    /// successor step it iterates rests on a refuted lemma.
    fn add_wh3_le(&mut self) -> Result<(), SpecError> {
        debug_assert!(Self::balanced(SRC_WH3_LE), "wh3 le parens");
        self.add_recursive_def(
            SRC_WH3_LE,
            "def_eq_fuel_wh3_le: acceptance survives raising the fuel to any Le-greater bound, by \
             Le.rec iterating def_eq_fuel_wh3_succ_mono. \
             \
             The form fuel pairing wants: two acceptances obtained independently come back at \
             unrelated fuels, and the completeness recursion needs them at one. That raise is \
             exactly what the two-way algorithm cannot do. DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }

    /// The introduction rule, at the three-way algorithm.
    ///
    /// Written as its OWN declaration against def_eq_fuel_wh3 and
    /// whnf_fuel_red_wh3, reading the original as a template. Not a retrofit of
    /// the original: parameterising a long-proved declaration in place is what
    /// broke it earlier today, and the blast radius there is the existing proof.
    fn add_wh3_of_struct(&mut self) -> Result<(), SpecError> {
        debug_assert!(Self::balanced(SRC_WH3_OF_STRUCT), "wh3 of_struct parens");
        self.add_recursive_def(
            SRC_WH3_OF_STRUCT,
            "def_eq_fuel_wh3_of_struct: if the three-way loop takes a to na and b to nb at fuel k, \
             and the structural grid accepts na against nb with the fuel-k algorithm as \
             comparator, then the algorithm accepts a against b at fuel k+1. Two OptionType \
             rewrites put the scrutinees in constructor form so both eliminators fire, then \
             def_eq_fuel_wh3_succ folds the layer back up. \
             \
             The introduction direction, dual to soundness, and a prerequisite of the \
             algorithm-side monotonicity below. DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }

    /// One simultaneous pass over whole identifiers. Sequential replacement
    /// double-applies; this cannot.
    ///
    /// `table` is scanned in order and the FIRST match wins, so it must be
    /// longest-first: a prefix entry placed above the identifier containing it
    /// would shadow it. The two callers share this scanner precisely so a fix to
    /// the whole-identifier logic cannot land in one family and miss the other.
    fn retarget_idents(src: &str, table: &[(&str, &str)]) -> String {
        let mut out = String::with_capacity(src.len() + 256);
        let bytes = src.as_bytes();
        let mut i = 0usize;
        let ident = |c: u8| c.is_ascii_alphanumeric() || c == b'_';
        'outer: while i < bytes.len() {
            if i == 0 || !ident(bytes[i - 1]) {
                for (from, to) in table {
                    if src[i..].starts_with(from) {
                        let end = i + from.len();
                        if end >= bytes.len() || !ident(bytes[end]) {
                            out.push_str(to);
                            i = end;
                            continue 'outer;
                        }
                    }
                }
            }
            out.push(bytes[i] as char);
            i += 1;
        }
        out
    }

    /// The algorithm-side retarget, for terms that cite the monotonicity lemma.
    fn retarget_to_wh3(src: &str) -> String {
        // Longest first so a prefix never wins over the identifier containing it.
        // `whnf_fuel_red` is LAST for that reason: above `_monotone` it would
        // rewrite the prefix and orphan the suffix.
        let table: [(&str, &str); 7] = [
            ("whnf_fuel_red_monotone", "whnf_fuel_red_wh3_monotone"),
            ("def_eq_fuel_of_struct", "def_eq_fuel_wh3_of_struct"),
            ("def_eq_fuel_succ_mono", "def_eq_fuel_wh3_succ_mono"),
            ("def_eq_fuel_succ", "def_eq_fuel_wh3_succ"),
            ("def_eq_fuel_zero", "def_eq_fuel_wh3_zero"),
            ("def_eq_fuel", "def_eq_fuel_wh3"),
            ("whnf_fuel_red", "whnf_fuel_red_wh3"),
        ];
        let out = Self::retarget_idents(src, &table);
        // The two monotonicity lemmas differ in ARITY, not just name: the
        // original takes the reduction environment explicitly, whnf_fuel_red3's
        // bakes in the_red_env. So the environment argument at that call site
        // must be dropped, or it lands where `fuel : Nat` is expected — which
        // the kernel reports as RedEnv vs Nat.
        let n_before = out
            .matches("whnf_fuel_red_wh3_monotone the_red_env ")
            .count();
        let out = out.replace(
            "whnf_fuel_red_wh3_monotone the_red_env ",
            "whnf_fuel_red_wh3_monotone ",
        );
        assert!(
            n_before > 0,
            "the monotonicity call site was not found; the substitution table has drifted"
        );
        assert!(
            !out.contains("whnf_fuel_red_wh3_monotone the_red_env"),
            "every monotonicity call must have shed the environment argument"
        );
        out
    }

    /// The LEAF retarget: same scanner, different table, and no monotonicity
    /// fixup — leaves cite no monotonicity lemma, so `retarget_to_wh3`'s
    /// `n_before > 0` assertion would fire on every one of them.
    ///
    /// The declaration's own NAME cannot go through the scanner. Whole-identifier
    /// matching requires a non-identifier byte on both sides, and
    /// `def_eq_complete_leaf_sort` has an identifier byte immediately after every
    /// prefix you might try to match — so the rename is done as a separate,
    /// counted literal substitution on the `def` header.
    fn retarget_leaf_to_wh3(src: &str) -> String {
        let table: [(&str, &str); 4] = [
            ("def_eq_fuel_of_struct", "def_eq_fuel_wh3_of_struct"),
            ("def_eq_fuel", "def_eq_fuel_wh3"),
            ("DefEqFuelAccepts", "DefEqFuelAcceptsWh3"),
            ("whnf_fuel_red", "whnf_fuel_red_wh3"),
        ];
        let renamed = src.replacen(
            "def def_eq_complete_leaf_",
            "def def_eq_complete_leaf_wh3_",
            1,
        );
        assert_eq!(
            src.matches("def def_eq_complete_leaf_").count(),
            1,
            "a leaf source must declare exactly one leaf, or the rename hits the wrong one"
        );
        let out = Self::retarget_idents(&renamed, &table);
        // The point of the port is that NOTHING still refers to the two-way
        // family. `whnf_fuel_red_wh3` contains `whnf_fuel_red`, so test for the
        // two-way name followed by a space — the only way it appears applied.
        assert!(
            !out.contains("whnf_fuel_red the_red_env"),
            "a leaf still reduces with the TWO-way loop: {out}"
        );
        assert!(
            !out.contains("def_eq_fuel the_red_env"),
            "a leaf still compares with the TWO-way algorithm: {out}"
        );
        assert!(
            !out.contains("DefEqFuelAccepts a b"),
            "a leaf still concludes at the TWO-way acceptance predicate: {out}"
        );
        out
    }

    /// The four leaves, retargeted — the completeness recursion's BASE CASES.
    ///
    /// Without these the wh3 family is inductive-only: every
    /// `def_eq_complete_step_wh3_*` consumes a `DefEqFuelAcceptsWh3` and produces
    /// one, so absent a base case the predicate could be uninhabited and all four
    /// steps would be decorations. That is the exact shape of vacuity this
    /// program has been bitten by twice, and it is not caught by any axiom
    /// ratchet — a theorem about an empty predicate has an empty axiom closure.
    fn wh3_complete_leaf_srcs() -> Vec<String> {
        Self::complete_leaf_decls()
            .iter()
            .map(|(src, _)| Self::retarget_leaf_to_wh3(src))
            .collect()
    }
}

const SRC_WH3_OF_STRUCT: &str = "def def_eq_fuel_wh3_of_struct (k : Nat) (a : KExpr) (b : KExpr) (na : KExpr) (nb : KExpr) (ha : Eq (OptionType KExpr) (whnf_fuel_red_wh3 the_red_env k a) (OptionType.some KExpr na)) (hb : Eq (OptionType KExpr) (whnf_fuel_red_wh3 the_red_env k b) (OptionType.some KExpr nb)) (hg : Eq Bool (def_eq_struct (def_eq_fuel_wh3 the_red_env k) na nb) Bool.true) : Eq Bool (def_eq_fuel_wh3 the_red_env (Nat.succ k) a b) Bool.true := Eq.substType Bool (fun (x : Bool) => Eq Bool x Bool.true) (OptionType.rec KExpr (fun (_ : OptionType KExpr) => Bool) Bool.false (fun (nx : KExpr) => OptionType.rec KExpr (fun (_ : OptionType KExpr) => Bool) Bool.false (fun (ny : KExpr) => def_eq_struct (def_eq_fuel_wh3 the_red_env k) nx ny) (whnf_fuel_red_wh3 the_red_env k b)) (whnf_fuel_red_wh3 the_red_env k a)) (def_eq_fuel_wh3 the_red_env (Nat.succ k) a b) (Eq.symm Bool (def_eq_fuel_wh3 the_red_env (Nat.succ k) a b) (OptionType.rec KExpr (fun (_ : OptionType KExpr) => Bool) Bool.false (fun (nx : KExpr) => OptionType.rec KExpr (fun (_ : OptionType KExpr) => Bool) Bool.false (fun (ny : KExpr) => def_eq_struct (def_eq_fuel_wh3 the_red_env k) nx ny) (whnf_fuel_red_wh3 the_red_env k b)) (whnf_fuel_red_wh3 the_red_env k a)) (def_eq_fuel_wh3_succ the_red_env k a b)) (Eq.substType (OptionType KExpr) (fun (o : OptionType KExpr) => Eq Bool (OptionType.rec KExpr (fun (_ : OptionType KExpr) => Bool) Bool.false (fun (nx : KExpr) => OptionType.rec KExpr (fun (_ : OptionType KExpr) => Bool) Bool.false (fun (ny : KExpr) => def_eq_struct (def_eq_fuel_wh3 the_red_env k) nx ny) (whnf_fuel_red_wh3 the_red_env k b)) o) Bool.true) (OptionType.some KExpr na) (whnf_fuel_red_wh3 the_red_env k a) (Eq.symm (OptionType KExpr) (whnf_fuel_red_wh3 the_red_env k a) (OptionType.some KExpr na) ha) (Eq.substType (OptionType KExpr) (fun (o2 : OptionType KExpr) => Eq Bool (OptionType.rec KExpr (fun (_ : OptionType KExpr) => Bool) Bool.false (fun (ny : KExpr) => def_eq_struct (def_eq_fuel_wh3 the_red_env k) na ny) o2) Bool.true) (OptionType.some KExpr nb) (whnf_fuel_red_wh3 the_red_env k b) (Eq.symm (OptionType KExpr) (whnf_fuel_red_wh3 the_red_env k b) (OptionType.some KExpr nb) hb) hg))";

const SRC_WH3_LE: &str = "def def_eq_fuel_wh3_le (k : Nat) (m : Nat) (hle : Le k m) : forall (a : KExpr) (b : KExpr), Eq Bool (def_eq_fuel_wh3 the_red_env k a b) Bool.true -> Eq Bool (def_eq_fuel_wh3 the_red_env m a b) Bool.true := Le.rec k (fun (j : Nat) (_hj : Le k j) => forall (a : KExpr) (b : KExpr), Eq Bool (def_eq_fuel_wh3 the_red_env k a b) Bool.true -> Eq Bool (def_eq_fuel_wh3 the_red_env j a b) Bool.true) (fun (a : KExpr) (b : KExpr) (h : Eq Bool (def_eq_fuel_wh3 the_red_env k a b) Bool.true) => h) (fun (j : Nat) (_hj : Le k j) (ihj : forall (a : KExpr) (b : KExpr), Eq Bool (def_eq_fuel_wh3 the_red_env k a b) Bool.true -> Eq Bool (def_eq_fuel_wh3 the_red_env j a b) Bool.true) (a : KExpr) (b : KExpr) (h : Eq Bool (def_eq_fuel_wh3 the_red_env k a b) Bool.true) => def_eq_fuel_wh3_succ_mono j a b (ihj a b h)) m hle";

const SRC_WH3_ACCEPTS: &str = "inductive DefEqFuelAcceptsWh3 (a : KExpr) (b : KExpr) : Type
| mk : forall (n : Nat), Eq Bool (def_eq_fuel_wh3 the_red_env n a b) Bool.true -> DefEqFuelAcceptsWh3 a b";

const SRC_WH3_ACCEPTS_PAIR: &str = "inductive DefEqFuelAcceptsPairWh3 (x1 : KExpr) (y1 : KExpr) (x2 : KExpr) (y2 : KExpr) : Type
| mk : forall (n : Nat), Eq Bool (def_eq_fuel_wh3 the_red_env n x1 y1) Bool.true -> Eq Bool (def_eq_fuel_wh3 the_red_env n x2 y2) Bool.true -> DefEqFuelAcceptsPairWh3 x1 y1 x2 y2";

const SRC_WH3_PAIR: &str = "def def_eq_fuel_wh3_accepts_pair (x1 : KExpr) (y1 : KExpr) (x2 : KExpr) (y2 : KExpr) (w1 : DefEqFuelAcceptsWh3 x1 y1) (w2 : DefEqFuelAcceptsWh3 x2 y2) : DefEqFuelAcceptsPairWh3 x1 y1 x2 y2 := DefEqFuelAcceptsWh3.rec x1 y1 (fun (_a : DefEqFuelAcceptsWh3 x1 y1) => DefEqFuelAcceptsPairWh3 x1 y1 x2 y2) (fun (n1 : Nat) (h1 : Eq Bool (def_eq_fuel_wh3 the_red_env n1 x1 y1) Bool.true) => DefEqFuelAcceptsWh3.rec x2 y2 (fun (_b : DefEqFuelAcceptsWh3 x2 y2) => DefEqFuelAcceptsPairWh3 x1 y1 x2 y2) (fun (n2 : Nat) (h2 : Eq Bool (def_eq_fuel_wh3 the_red_env n2 x2 y2) Bool.true) => DefEqFuelAcceptsPairWh3.mk x1 y1 x2 y2 (Nat.add n1 n2) (def_eq_fuel_wh3_le n1 (Nat.add n1 n2) (le_add_self_left n1 n2) x1 y1 h1) (def_eq_fuel_wh3_le n2 (Nat.add n1 n2) (le_add_self_right n1 n2) x2 y2 h2)) w2) w1";

const SRC_WH3_STEP_PI: &str = "def def_eq_complete_step_wh3_pi (n : Nat) (a : KExpr) (b : KExpr) (ty1 : KExpr) (bd1 : KExpr) (ty2 : KExpr) (bd2 : KExpr) (ha : Eq (OptionType KExpr) (whnf_fuel_red_wh3 the_red_env n a) (OptionType.some KExpr (KExpr.pi ty1 bd1))) (hb : Eq (OptionType KExpr) (whnf_fuel_red_wh3 the_red_env n b) (OptionType.some KExpr (KExpr.pi ty2 bd2))) (w0 : DefEqFuelAcceptsWh3 ty1 ty2) (w1 : DefEqFuelAcceptsWh3 bd1 bd2) : DefEqFuelAcceptsWh3 a b := DefEqFuelAcceptsPairWh3.rec ty1 ty2 bd1 bd2 (fun (_p : DefEqFuelAcceptsPairWh3 ty1 ty2 bd1 bd2) => DefEqFuelAcceptsWh3 a b) (fun (k : Nat) (hc0 : Eq Bool (def_eq_fuel_wh3 the_red_env k ty1 ty2) Bool.true) (hc1 : Eq Bool (def_eq_fuel_wh3 the_red_env k bd1 bd2) Bool.true) => DefEqFuelAcceptsWh3.mk a b (Nat.succ (Nat.add n k)) (def_eq_fuel_wh3_of_struct (Nat.add n k) a b (KExpr.pi ty1 bd1) (KExpr.pi ty2 bd2) (whnf_fuel_red_wh3_le n (Nat.add n k) (le_add_self_left n k) a (KExpr.pi ty1 bd1) ha) (whnf_fuel_red_wh3_le n (Nat.add n k) (le_add_self_left n k) b (KExpr.pi ty2 bd2) hb) (def_eq_struct_intro_pi (def_eq_fuel_wh3 the_red_env (Nat.add n k)) ty1 bd1 ty2 bd2 (def_eq_fuel_wh3_le k (Nat.add n k) (le_add_self_right n k) ty1 ty2 hc0) (def_eq_fuel_wh3_le k (Nat.add n k) (le_add_self_right n k) bd1 bd2 hc1)))) (def_eq_fuel_wh3_accepts_pair ty1 ty2 bd1 bd2 w0 w1)";

const SRC_WH3_STEP_LAM: &str = "def def_eq_complete_step_wh3_lam (n : Nat) (a : KExpr) (b : KExpr) (ty1 : KExpr) (bd1 : KExpr) (ty2 : KExpr) (bd2 : KExpr) (ha : Eq (OptionType KExpr) (whnf_fuel_red_wh3 the_red_env n a) (OptionType.some KExpr (KExpr.lam ty1 bd1))) (hb : Eq (OptionType KExpr) (whnf_fuel_red_wh3 the_red_env n b) (OptionType.some KExpr (KExpr.lam ty2 bd2))) (w0 : DefEqFuelAcceptsWh3 ty1 ty2) (w1 : DefEqFuelAcceptsWh3 bd1 bd2) : DefEqFuelAcceptsWh3 a b := DefEqFuelAcceptsPairWh3.rec ty1 ty2 bd1 bd2 (fun (_p : DefEqFuelAcceptsPairWh3 ty1 ty2 bd1 bd2) => DefEqFuelAcceptsWh3 a b) (fun (k : Nat) (hc0 : Eq Bool (def_eq_fuel_wh3 the_red_env k ty1 ty2) Bool.true) (hc1 : Eq Bool (def_eq_fuel_wh3 the_red_env k bd1 bd2) Bool.true) => DefEqFuelAcceptsWh3.mk a b (Nat.succ (Nat.add n k)) (def_eq_fuel_wh3_of_struct (Nat.add n k) a b (KExpr.lam ty1 bd1) (KExpr.lam ty2 bd2) (whnf_fuel_red_wh3_le n (Nat.add n k) (le_add_self_left n k) a (KExpr.lam ty1 bd1) ha) (whnf_fuel_red_wh3_le n (Nat.add n k) (le_add_self_left n k) b (KExpr.lam ty2 bd2) hb) (def_eq_struct_intro_lam (def_eq_fuel_wh3 the_red_env (Nat.add n k)) ty1 bd1 ty2 bd2 (def_eq_fuel_wh3_le k (Nat.add n k) (le_add_self_right n k) ty1 ty2 hc0) (def_eq_fuel_wh3_le k (Nat.add n k) (le_add_self_right n k) bd1 bd2 hc1)))) (def_eq_fuel_wh3_accepts_pair ty1 ty2 bd1 bd2 w0 w1)";

const SRC_WH3_STEP_APP: &str = "def def_eq_complete_step_wh3_app (n : Nat) (a : KExpr) (b : KExpr) (fn1 : KExpr) (ag1 : KExpr) (fn2 : KExpr) (ag2 : KExpr) (ha : Eq (OptionType KExpr) (whnf_fuel_red_wh3 the_red_env n a) (OptionType.some KExpr (KExpr.app fn1 ag1))) (hb : Eq (OptionType KExpr) (whnf_fuel_red_wh3 the_red_env n b) (OptionType.some KExpr (KExpr.app fn2 ag2))) (w0 : DefEqFuelAcceptsWh3 fn1 fn2) (w1 : DefEqFuelAcceptsWh3 ag1 ag2) : DefEqFuelAcceptsWh3 a b := DefEqFuelAcceptsPairWh3.rec fn1 fn2 ag1 ag2 (fun (_p : DefEqFuelAcceptsPairWh3 fn1 fn2 ag1 ag2) => DefEqFuelAcceptsWh3 a b) (fun (k : Nat) (hc0 : Eq Bool (def_eq_fuel_wh3 the_red_env k fn1 fn2) Bool.true) (hc1 : Eq Bool (def_eq_fuel_wh3 the_red_env k ag1 ag2) Bool.true) => DefEqFuelAcceptsWh3.mk a b (Nat.succ (Nat.add n k)) (def_eq_fuel_wh3_of_struct (Nat.add n k) a b (KExpr.app fn1 ag1) (KExpr.app fn2 ag2) (whnf_fuel_red_wh3_le n (Nat.add n k) (le_add_self_left n k) a (KExpr.app fn1 ag1) ha) (whnf_fuel_red_wh3_le n (Nat.add n k) (le_add_self_left n k) b (KExpr.app fn2 ag2) hb) (def_eq_struct_intro_app (def_eq_fuel_wh3 the_red_env (Nat.add n k)) fn1 ag1 fn2 ag2 (def_eq_fuel_wh3_le k (Nat.add n k) (le_add_self_right n k) fn1 fn2 hc0) (def_eq_fuel_wh3_le k (Nat.add n k) (le_add_self_right n k) ag1 ag2 hc1)))) (def_eq_fuel_wh3_accepts_pair fn1 fn2 ag1 ag2 w0 w1)";

const SRC_WH3_STEP_PROJ: &str = "def def_eq_complete_step_wh3_proj (n : Nat) (a : KExpr) (b : KExpr) (ps : Name) (pidx : Nat) (sub1 : KExpr) (sub2 : KExpr) (ha : Eq (OptionType KExpr) (whnf_fuel_red_wh3 the_red_env n a) (OptionType.some KExpr (KExpr.proj ps pidx sub1))) (hb : Eq (OptionType KExpr) (whnf_fuel_red_wh3 the_red_env n b) (OptionType.some KExpr (KExpr.proj ps pidx sub2))) (w0 : DefEqFuelAcceptsWh3 sub1 sub2) : DefEqFuelAcceptsWh3 a b := DefEqFuelAcceptsWh3.rec sub1 sub2 (fun (_p : DefEqFuelAcceptsWh3 sub1 sub2) => DefEqFuelAcceptsWh3 a b) (fun (k : Nat) (hc0 : Eq Bool (def_eq_fuel_wh3 the_red_env k sub1 sub2) Bool.true) => DefEqFuelAcceptsWh3.mk a b (Nat.succ (Nat.add n k)) (def_eq_fuel_wh3_of_struct (Nat.add n k) a b (KExpr.proj ps pidx sub1) (KExpr.proj ps pidx sub2) (whnf_fuel_red_wh3_le n (Nat.add n k) (le_add_self_left n k) a (KExpr.proj ps pidx sub1) ha) (whnf_fuel_red_wh3_le n (Nat.add n k) (le_add_self_left n k) b (KExpr.proj ps pidx sub2) hb) (def_eq_struct_intro_proj (def_eq_fuel_wh3 the_red_env (Nat.add n k)) ps pidx sub1 sub2 (def_eq_fuel_wh3_le k (Nat.add n k) (le_add_self_right n k) sub1 sub2 hc0)))) w0";

#[cfg(test)]
mod wh3_leaf_tests {
    use super::*;

    /// The retarget is mechanical, so the checks are mechanical: four leaves,
    /// balanced, each concluding at the three-way acceptance predicate, and none
    /// still naming the two-way family.
    ///
    /// Prints the sources under a `WH3LEAF ` marker so a scratchpad batch can be
    /// assembled from them without hand-copying 4 × ~1.5kB of proof term — the
    /// kind of copying that introduced a dropped `fun` keyword earlier in this
    /// program and cost a 26-minute cycle to find.
    #[test]
    fn test_wh3_leaves_retarget_cleanly() {
        let srcs = Specification::wh3_complete_leaf_srcs();
        assert_eq!(srcs.len(), 4, "four leaves: sort, lit, bvar, const");
        for src in &srcs {
            assert!(Specification::balanced(src), "unbalanced leaf: {src}");
            assert!(
                src.contains(": DefEqFuelAcceptsWh3 a b :="),
                "leaf must conclude at the three-way predicate: {src}"
            );
            assert!(
                src.starts_with("def def_eq_complete_leaf_wh3_"),
                "leaf must be renamed, or it collides with the two-way one: {src}"
            );
            eprintln!("WH3LEAF {src}");
        }
    }
}
