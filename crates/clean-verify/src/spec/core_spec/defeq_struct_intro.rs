// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Link 3 of the def-eq completeness chain: **matching heads ⇒ the algorithm
//! accepts**.
//!
//! The chain, as corrected on 2026-07-25 (see the correction section of
//! `docs/plans/DEFEQ_COMPLETENESS_PROGRAM_2026-07-25.md`):
//!
//! | # | link | state |
//! |---|---|---|
//! | 1 | `DefEq a b` → common reduct (`def_eq_joinable`) | proven |
//! | 2 | common reduct → matching whnf heads (`def_eq_whnf_complete`) | proven |
//! | 3 | matching heads → the Boolean grid accepts | **here** |
//! | 4 | fuel adequacy / termination | still open, and larger than 3 |
//!
//! This module builds link 3 and nothing else. It does **not** close the
//! capstone, and no declaration here should be read as doing so: link 4 has no
//! artifact at all — `below_plus_acc` still has zero consumers, nothing relates
//! accessibility to a fuel bound, and `whnf_red_step` is not known to be
//! contained in `whnf_step`.
//!
//! Two halves:
//!
//! - **The grid half.** `def_eq_struct_intro_*`, one per constructor: if the
//!   comparator accepts the components then the 9x9 grid accepts the composite.
//!   The recursive cases (`app` / `lam` / `pi` / `let_` / `proj`) need
//!   `band_intro`, the `Bool.and` *introduction* rule — only the two
//!   eliminations (`band_eq_true_left` / `_right`) were in tree. The leaf cases
//!   (`sort` / `bvar` / `const` / `lit`) are the reflexivity lemmas
//!   `level_eqb_refl` / `nat_eqb_refl` / `name_eqb_refl` / `ulist_eqb_refl`,
//!   and are stated at a *single* term rather than two, because the grid
//!   compares those payloads syntactically — there is nothing weaker to
//!   assume.
//!
//! - **The fuel half.** `def_eq_fuel_of_struct`: given both whnf legs and grid
//!   acceptance of the two normal forms, the algorithm accepts at `fuel+1`.
//!   Stating this once, generically, is what keeps the per-constructor
//!   congruences to one line each; the alternative — nine separate fuel-level
//!   lemmas each re-deriving the same two `OptionType` rewrites — is the same
//!   proof nine times.
//!
//! Composing the two gives the congruence shape the capstone induction will
//! consume, e.g. for `pi`:
//!
//! ```text
//! whnf a = pi A B  ->  whnf b = pi A2 B2
//!   ->  def_eq_fuel renv k A A2 = true  ->  def_eq_fuel renv k B B2 = true
//!   ->  def_eq_fuel renv (k+1) a b = true
//! ```
//!
//! Direction note: this is the **introduction** direction throughout, dual to
//! `defeq_struct_sound.rs`, which is elimination. Neither implies the other and
//! both are needed — soundness to make an acceptance meaningful, introduction
//! to make one derivable.
//!
//! Every declaration is `DerivedProved` with an empty axiom closure.

use crate::spec::error::SpecError;
use crate::spec::Specification;

impl Specification {
    /// Link 3: matching heads imply the structural algorithm accepts.
    pub(super) fn add_defeq_struct_intro(&mut self) -> Result<(), SpecError> {
        self.add_band_intro()?;
        self.add_defeq_struct_intro_rules()?;
        self.add_defeq_fuel_of_struct()?;
        Ok(())
    }

    /// `Bool.and` introduction. Only the eliminations were in tree
    /// (`band_eq_true_left` / `_right`, `faithful_red_env.rs:174`), because
    /// every prior consumer was taking conjunctions apart. Link 3 is the first
    /// one that builds them.
    fn add_band_intro(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            "def band_intro (p : Bool) (q : Bool) (hp : Eq Bool p Bool.true) \
             (hq : Eq Bool q Bool.true) : Eq Bool (Bool.and p q) Bool.true := \
             Eq.substType Bool (fun (z : Bool) => Eq Bool (Bool.and z q) Bool.true) \
             Bool.true p (Eq.symm Bool p Bool.true hp) \
             (Eq.substType Bool (fun (z : Bool) => Eq Bool (Bool.and Bool.true z) Bool.true) \
             Bool.true q (Eq.symm Bool q Bool.true hq) (Eq.refl Bool Bool.true))",
            "band_intro: Bool.and introduction — p = true and q = true give Bool.and p q = true. \
             Rewrite both conjuncts to Bool.true, where Bool.and reduces definitionally. The dual \
             of the in-tree band_eq_true_left / band_eq_true_right, which were the only Bool.and \
             rules present because every earlier consumer was ELIMINATING conjunctions; the \
             completeness direction is the first that has to build them. DerivedProved, zero \
             axiom_deps.",
        )?;
        Ok(())
    }

    /// The nine grid-introduction rules, one per `KExpr` constructor.
    fn add_defeq_struct_intro_rules(&mut self) -> Result<(), SpecError> {
        let cmp = "(cmp : KExpr -> KExpr -> Bool)";

        // ---- Leaves: the grid compares payloads syntactically, so these are
        // reflexivity at a single term, not a two-term hypothesis. Stating them
        // with two terms and an equality premise would be strictly weaker
        // dressed up as stronger.
        self.add_recursive_def(
            &format!(
                "def def_eq_struct_intro_sort {cmp} (n : Level) : \
                 Eq Bool (def_eq_struct cmp (KExpr.sort n) (KExpr.sort n)) Bool.true := \
                 level_eqb_refl n"
            ),
            "def_eq_struct_intro_sort: the grid accepts a sort against itself (level_eqb_refl). \
             Stated at one level rather than two because def_eq_struct compares sort payloads \
             with level_eqb — syntactically — so there is no weaker premise available. \
             DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            &format!(
                "def def_eq_struct_intro_bvar {cmp} (i : Nat) : \
                 Eq Bool (def_eq_struct cmp (KExpr.bvar i) (KExpr.bvar i)) Bool.true := \
                 nat_eqb_refl i"
            ),
            "def_eq_struct_intro_bvar: the grid accepts a bvar against itself (nat_eqb_refl). \
             DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            &format!(
                "def def_eq_struct_intro_const {cmp} (nm : Name) (us : ListType Level) : \
                 Eq Bool (def_eq_struct cmp (KExpr.const nm us) (KExpr.const nm us)) Bool.true := \
                 band_intro (name_eqb nm nm) (ulist_eqb us us) (name_eqb_refl nm) \
                 (ulist_eqb_refl us)"
            ),
            "def_eq_struct_intro_const: the grid accepts a const against itself — name and \
             universe-argument list each by reflexivity, combined with band_intro. \
             DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            &format!(
                "def def_eq_struct_intro_lit {cmp} (w : Nat) : \
                 Eq Bool (def_eq_struct cmp (KExpr.lit w) (KExpr.lit w)) Bool.true := \
                 nat_eqb_refl w"
            ),
            "def_eq_struct_intro_lit: the grid accepts a literal against itself (nat_eqb_refl). \
             DerivedProved, zero axiom_deps.",
        )?;

        // ---- Recursive: the interesting half. These are the congruence steps
        // the capstone induction consumes — the components are compared by the
        // supplied comparator, so they may be convertible-but-not-equal, which
        // is exactly what def_eq_whnf_fuel could not express.
        self.add_recursive_def(
            &format!(
                "def def_eq_struct_intro_app {cmp} (f : KExpr) (a1 : KExpr) (g : KExpr) \
                 (c : KExpr) (hf : Eq Bool (cmp f g) Bool.true) \
                 (ha : Eq Bool (cmp a1 c) Bool.true) : \
                 Eq Bool (def_eq_struct cmp (KExpr.app f a1) (KExpr.app g c)) Bool.true := \
                 band_intro (cmp f g) (cmp a1 c) hf ha"
            ),
            "def_eq_struct_intro_app: APP CONGRUENCE for the grid — componentwise acceptance \
             implies acceptance of the application. The components go through the supplied \
             comparator, so they may be convertible without being syntactically equal; that is \
             precisely the case def_eq_whnf_fuel cannot express and the reason the structural \
             algorithm exists. DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            &format!(
                "def def_eq_struct_intro_lam {cmp} (ty1 : KExpr) (b1 : KExpr) (gt : KExpr) \
                 (gb : KExpr) (ht : Eq Bool (cmp ty1 gt) Bool.true) \
                 (hb : Eq Bool (cmp b1 gb) Bool.true) : \
                 Eq Bool (def_eq_struct cmp (KExpr.lam ty1 b1) (KExpr.lam gt gb)) Bool.true := \
                 band_intro (cmp ty1 gt) (cmp b1 gb) ht hb"
            ),
            "def_eq_struct_intro_lam: LAM CONGRUENCE for the grid — domain and body accepted \
             componentwise implies the lambda is accepted. DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            &format!(
                "def def_eq_struct_intro_pi {cmp} (ty1 : KExpr) (b1 : KExpr) (gt : KExpr) \
                 (gb : KExpr) (ht : Eq Bool (cmp ty1 gt) Bool.true) \
                 (hb : Eq Bool (cmp b1 gb) Bool.true) : \
                 Eq Bool (def_eq_struct cmp (KExpr.pi ty1 b1) (KExpr.pi gt gb)) Bool.true := \
                 band_intro (cmp ty1 gt) (cmp b1 gb) ht hb"
            ),
            "def_eq_struct_intro_pi: PI CONGRUENCE for the grid — domain and codomain accepted \
             componentwise implies the pi is accepted. This is the canonical instance of the \
             gap: `pi A B` against `pi A' B'` with A convertible to but not syntactically equal \
             to A' is exactly what def_eq_whnf_fuel rejects and what completeness against DefEq \
             requires. DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            &format!(
                "def def_eq_struct_intro_let {cmp} (lty : KExpr) (lv : KExpr) (lb : KExpr) \
                 (glt : KExpr) (glv : KExpr) (glb : KExpr) \
                 (h1 : Eq Bool (cmp lty glt) Bool.true) (h2 : Eq Bool (cmp lv glv) Bool.true) \
                 (h3 : Eq Bool (cmp lb glb) Bool.true) : \
                 Eq Bool (def_eq_struct cmp (KExpr.let_ lty lv lb) (KExpr.let_ glt glv glb)) \
                 Bool.true := \
                 band_intro (cmp lty glt) (Bool.and (cmp lv glv) (cmp lb glb)) h1 \
                 (band_intro (cmp lv glv) (cmp lb glb) h2 h3)"
            ),
            "def_eq_struct_intro_let: LET CONGRUENCE for the grid — type, value and body \
             accepted componentwise implies the let is accepted. The conjunction is \
             right-nested, matching def_eq_struct's own shape. DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            &format!(
                "def def_eq_struct_intro_proj {cmp} (ps : Name) (pidx : Nat) (psub : KExpr) \
                 (sub2 : KExpr) (hs : Eq Bool (cmp psub sub2) Bool.true) : \
                 Eq Bool (def_eq_struct cmp (KExpr.proj ps pidx psub) \
                 (KExpr.proj ps pidx sub2)) Bool.true := \
                 band_intro (Bool.and (name_eqb ps ps) (nat_eqb pidx pidx)) (cmp psub sub2) \
                 (band_intro (name_eqb ps ps) (nat_eqb pidx pidx) (name_eqb_refl ps) \
                 (nat_eqb_refl pidx)) hs"
            ),
            "def_eq_struct_intro_proj: PROJ CONGRUENCE for the grid — same struct name and field \
             index (compared syntactically by the grid, discharged by reflexivity), subject \
             accepted by the comparator. Matches DefEq.proj_cong, which likewise fixes name and \
             index on both sides. DerivedProved, zero axiom_deps.",
        )?;

        Ok(())
    }

    /// The fuel half of link 3: grid acceptance of the two normal forms lifts
    /// to algorithm acceptance of the originals at one more unit of fuel.
    fn add_defeq_fuel_of_struct(&mut self) -> Result<(), SpecError> {
        // Written out rather than abbreviated: the spec source language has no
        // `let`, so the two nested option eliminators appear in full in the
        // motives. `inner` is the b-side eliminator with `na` fixed; `outer`
        // wraps it over the a-side.
        let inner = "(fun (ny : KExpr) => def_eq_struct (def_eq_fuel the_red_env k) na ny)";
        let outer = format!(
            "(fun (nx : KExpr) => OptionType.rec KExpr (fun (_ : OptionType KExpr) => Bool) \
             Bool.false (fun (ny : KExpr) => def_eq_struct (def_eq_fuel the_red_env k) nx ny) \
             (whnf_fuel_red the_red_env k b))"
        );

        // Step 2: rewrite the b-side scrutinee from `whnf_fuel_red … b` back to
        // `some nb`, where the inner eliminator fires and leaves exactly `hg`.
        let step_b = format!(
            "(Eq.substType (OptionType KExpr) \
             (fun (o2 : OptionType KExpr) => \
             Eq Bool (OptionType.rec KExpr (fun (_ : OptionType KExpr) => Bool) Bool.false \
             {inner} o2) Bool.true) \
             (OptionType.some KExpr nb) (whnf_fuel_red the_red_env k b) \
             (Eq.symm (OptionType KExpr) (whnf_fuel_red the_red_env k b) \
             (OptionType.some KExpr nb) hb) hg)"
        );

        // Step 1: same move on the a-side scrutinee.
        let step_a = format!(
            "(Eq.substType (OptionType KExpr) \
             (fun (o : OptionType KExpr) => \
             Eq Bool (OptionType.rec KExpr (fun (_ : OptionType KExpr) => Bool) Bool.false \
             {outer} o) Bool.true) \
             (OptionType.some KExpr na) (whnf_fuel_red the_red_env k a) \
             (Eq.symm (OptionType KExpr) (whnf_fuel_red the_red_env k a) \
             (OptionType.some KExpr na) ha) {step_b})"
        );

        // Step 0: fold the unfolded fuel layer back into `def_eq_fuel … (succ k)`.
        let src = format!(
            "def def_eq_fuel_of_struct (k : Nat) (a : KExpr) (b : KExpr) (na : KExpr) \
             (nb : KExpr) \
             (ha : Eq (OptionType KExpr) (whnf_fuel_red the_red_env k a) \
             (OptionType.some KExpr na)) \
             (hb : Eq (OptionType KExpr) (whnf_fuel_red the_red_env k b) \
             (OptionType.some KExpr nb)) \
             (hg : Eq Bool (def_eq_struct (def_eq_fuel the_red_env k) na nb) Bool.true) : \
             Eq Bool (def_eq_fuel the_red_env (Nat.succ k) a b) Bool.true := \
             Eq.substType Bool (fun (x : Bool) => Eq Bool x Bool.true) \
             (OptionType.rec KExpr (fun (_ : OptionType KExpr) => Bool) Bool.false {outer} \
             (whnf_fuel_red the_red_env k a)) \
             (def_eq_fuel the_red_env (Nat.succ k) a b) \
             (Eq.symm Bool (def_eq_fuel the_red_env (Nat.succ k) a b) \
             (OptionType.rec KExpr (fun (_ : OptionType KExpr) => Bool) Bool.false {outer} \
             (whnf_fuel_red the_red_env k a)) (def_eq_fuel_succ the_red_env k a b)) \
             {step_a}"
        );

        self.add_recursive_def(
            &src,
            "def_eq_fuel_of_struct: THE FUEL HALF OF LINK 3 — if the executable loop takes a to \
             na and b to nb at fuel k, and the structural grid accepts na against nb with the \
             fuel-k algorithm as comparator, then the algorithm accepts a against b at fuel \
             k+1. Two OptionType rewrites (via Eq.symm on each leg) put the scrutinees in \
             constructor form so both eliminators fire, then def_eq_fuel_succ folds the layer \
             back up. Stated once and generically so each per-constructor congruence is one line \
             composing it with the matching def_eq_struct_intro_* rule, rather than nine copies \
             of the same two rewrites. This is the INTRODUCTION direction, dual to \
             def_eq_fuel_sound. It does NOT close completeness: link 4 (fuel adequacy — \
             producing the two whnf legs from a well-foundedness premise) has no artifact yet. \
             DerivedProved, zero axiom_deps.",
        )?;

        Ok(())
    }

    /// The five congruences at the fuel level, in the shape the capstone
    /// induction consumes: both sides weak-head reduce to the same head at fuel
    /// `k`, the algorithm accepts the components at fuel `k`, therefore it
    /// accepts the originals at fuel `k+1`.
    ///
    /// Each is one line composing `def_eq_fuel_of_struct` with the matching
    /// `def_eq_struct_intro_*` rule. They are written out per constructor rather
    /// than left as "compose them yourself" because these are exactly the
    /// inductive steps the capstone will cite, and a capstone that has to
    /// re-derive them inline is where transcription errors hide.
    pub(super) fn add_defeq_fuel_congruences(&mut self) -> Result<(), SpecError> {
        for (name, src) in Self::defeq_fuel_congruence_srcs() {
            self.add_recursive_def(
                &src,
                &format!(
                    "{name}: congruence step for the structural conversion algorithm — if both \
                     sides weak-head reduce to this head at fuel k and the algorithm accepts \
                     the components at fuel k, it accepts the originals at fuel k+1. One of the \
                     five inductive steps the completeness capstone consumes. Note the \
                     components go through the ALGORITHM, so they may be convertible without \
                     being syntactically equal — the case def_eq_whnf_fuel rejects and the whole \
                     reason the structural algorithm exists. DerivedProved, zero axiom_deps."
                ),
            )?;
        }
        Ok(())
    }

    /// The five fuel-congruence source terms, as `(name, src)`. Split out from
    /// registration so the shape tests operate on the generated strings rather
    /// than on this file's text — `include_str!` includes the test module, so a
    /// literal used in an assertion counts itself.
    fn defeq_fuel_congruence_srcs() -> Vec<(String, String)> {
        // (name, extra binders, na form, nb form, component premises, intro call)
        let congruences: [(&str, &str, &str, &str, &str, &str); 5] = [
            (
                "def_eq_fuel_pi_cong",
                "(dom1 : KExpr) (cod1 : KExpr) (dom2 : KExpr) (cod2 : KExpr)",
                "(KExpr.pi dom1 cod1)",
                "(KExpr.pi dom2 cod2)",
                "(hd : Eq Bool (def_eq_fuel the_red_env k dom1 dom2) Bool.true) \
                 (hc : Eq Bool (def_eq_fuel the_red_env k cod1 cod2) Bool.true)",
                "def_eq_struct_intro_pi (def_eq_fuel the_red_env k) dom1 cod1 dom2 cod2 hd hc",
            ),
            (
                "def_eq_fuel_lam_cong",
                "(ty1 : KExpr) (bd1 : KExpr) (ty2 : KExpr) (bd2 : KExpr)",
                "(KExpr.lam ty1 bd1)",
                "(KExpr.lam ty2 bd2)",
                "(hd : Eq Bool (def_eq_fuel the_red_env k ty1 ty2) Bool.true) \
                 (hc : Eq Bool (def_eq_fuel the_red_env k bd1 bd2) Bool.true)",
                "def_eq_struct_intro_lam (def_eq_fuel the_red_env k) ty1 bd1 ty2 bd2 hd hc",
            ),
            (
                "def_eq_fuel_app_cong",
                "(fn1 : KExpr) (arg1 : KExpr) (fn2 : KExpr) (arg2 : KExpr)",
                "(KExpr.app fn1 arg1)",
                "(KExpr.app fn2 arg2)",
                "(hd : Eq Bool (def_eq_fuel the_red_env k fn1 fn2) Bool.true) \
                 (hc : Eq Bool (def_eq_fuel the_red_env k arg1 arg2) Bool.true)",
                "def_eq_struct_intro_app (def_eq_fuel the_red_env k) fn1 arg1 fn2 arg2 hd hc",
            ),
            (
                "def_eq_fuel_let_cong",
                "(lty1 : KExpr) (lv1 : KExpr) (lb1 : KExpr) (lty2 : KExpr) (lv2 : KExpr) \
                 (lb2 : KExpr)",
                "(KExpr.let_ lty1 lv1 lb1)",
                "(KExpr.let_ lty2 lv2 lb2)",
                "(hd : Eq Bool (def_eq_fuel the_red_env k lty1 lty2) Bool.true) \
                 (hc : Eq Bool (def_eq_fuel the_red_env k lv1 lv2) Bool.true) \
                 (he : Eq Bool (def_eq_fuel the_red_env k lb1 lb2) Bool.true)",
                "def_eq_struct_intro_let (def_eq_fuel the_red_env k) lty1 lv1 lb1 lty2 lv2 lb2 \
                 hd hc he",
            ),
            (
                "def_eq_fuel_proj_cong",
                "(ps : Name) (pidx : Nat) (psub1 : KExpr) (psub2 : KExpr)",
                "(KExpr.proj ps pidx psub1)",
                "(KExpr.proj ps pidx psub2)",
                "(hd : Eq Bool (def_eq_fuel the_red_env k psub1 psub2) Bool.true)",
                "def_eq_struct_intro_proj (def_eq_fuel the_red_env k) ps pidx psub1 psub2 hd",
            ),
        ];

        congruences
            .into_iter()
            .map(|(name, binders, na, nb, premises, intro)| {
                let src = format!(
                    "def {name} (k : Nat) (a : KExpr) (b : KExpr) {binders} \
                     (ha : Eq (OptionType KExpr) (whnf_fuel_red the_red_env k a) \
                     (OptionType.some KExpr {na})) \
                     (hb : Eq (OptionType KExpr) (whnf_fuel_red the_red_env k b) \
                     (OptionType.some KExpr {nb})) {premises} : \
                     Eq Bool (def_eq_fuel the_red_env (Nat.succ k) a b) Bool.true := \
                     def_eq_fuel_of_struct k a b {na} {nb} ha hb ({intro})"
                );
                (name.to_string(), src)
            })
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The introduction rules must exist for all nine constructors; a missing
    /// one is a hole in link 3 that no build error would reveal, since each is
    /// registered independently.
    #[test]
    fn test_intro_rules_cover_all_nine_constructors() {
        let src = include_str!("defeq_struct_intro.rs");
        for ctor in [
            "def_eq_struct_intro_sort",
            "def_eq_struct_intro_bvar",
            "def_eq_struct_intro_app",
            "def_eq_struct_intro_lam",
            "def_eq_struct_intro_pi",
            "def_eq_struct_intro_const",
            "def_eq_struct_intro_let",
            "def_eq_struct_intro_proj",
            "def_eq_struct_intro_lit",
        ] {
            assert!(
                src.contains(&format!("def {ctor} ")),
                "link 3 grid rule missing for: {ctor}"
            );
        }
    }

    /// All five fuel-level congruences must be registered, not just `pi`.
    /// These are the inductive steps the capstone cites; a missing one is a
    /// hole the capstone would have to paper over inline.
    ///
    /// Operates on the GENERATED terms, not on this file's text. The first
    /// version of this suite used `include_str!`, which pulls in the test
    /// module — so a literal appearing in an assertion counted itself and the
    /// test failed against its own body. Generated-string tests cannot do that.
    #[test]
    fn test_all_five_fuel_congruences_registered() {
        let srcs = Specification::defeq_fuel_congruence_srcs();
        assert_eq!(srcs.len(), 5, "expected five fuel-level congruences");
        let names: Vec<&str> = srcs.iter().map(|(n, _)| n.as_str()).collect();
        for name in [
            "def_eq_fuel_pi_cong",
            "def_eq_fuel_lam_cong",
            "def_eq_fuel_app_cong",
            "def_eq_fuel_let_cong",
            "def_eq_fuel_proj_cong",
        ] {
            assert!(
                names.contains(&name),
                "fuel-level congruence missing: {name}"
            );
        }
    }

    /// Every fuel congruence must route through `def_eq_fuel_of_struct`, the
    /// single place the two `OptionType` scrutinee rewrites are done, and must
    /// cite the matching `def_eq_struct_intro_*` rule. A congruence that
    /// open-coded the rewrites would be a second copy to keep in sync; one
    /// citing the wrong intro rule would prove a different congruence.
    #[test]
    fn test_fuel_congruences_route_through_the_shared_bridge() {
        for (name, src) in Specification::defeq_fuel_congruence_srcs() {
            assert!(
                src.contains("def_eq_fuel_of_struct k a b "),
                "{name} must go through the shared bridge, not open-code the rewrites"
            );
            assert!(
                !src.contains("Eq.substType"),
                "{name} must not perform its own scrutinee rewrite"
            );
            let head = name
                .strip_prefix("def_eq_fuel_")
                .and_then(|s| s.strip_suffix("_cong"))
                .expect("congruence names are def_eq_fuel_<head>_cong");
            assert!(
                src.contains(&format!("def_eq_struct_intro_{head} ")),
                "{name} must cite def_eq_struct_intro_{head}, its matching grid rule"
            );
        }
    }

    /// Each congruence's two whnf legs must land on the SAME head constructor
    /// on both sides — that is what makes it a congruence rather than a claim
    /// about unrelated terms.
    #[test]
    fn test_fuel_congruences_match_heads_on_both_legs() {
        for (name, src) in Specification::defeq_fuel_congruence_srcs() {
            let head = name
                .strip_prefix("def_eq_fuel_")
                .and_then(|s| s.strip_suffix("_cong"))
                .expect("congruence names are def_eq_fuel_<head>_cong");
            // The `let_` constructor carries a trailing underscore (`let` is a
            // reserved word in the spec parser); the lemma name does not.
            let ctor = if head == "let" {
                "KExpr.let_ ".to_string()
            } else {
                format!("KExpr.{head} ")
            };
            assert!(
                src.matches(&ctor).count() >= 4,
                "{name} must mention KExpr.{head} on both legs of both the hypotheses and the \
                 bridge call"
            );
        }
    }

    /// The five recursive constructors are the ones carrying real content —
    /// their premises must go through the comparator `cmp`, not through a
    /// syntactic equality. If one of them silently compared components with
    /// `kexpr_beq` instead, the rule would still typecheck and would still be
    /// true, but it would be the weak criterion this program exists to escape.
    #[test]
    fn test_recursive_intro_rules_take_comparator_premises() {
        let src = include_str!("defeq_struct_intro.rs");
        for premise in [
            "(hf : Eq Bool (cmp f g) Bool.true)",
            "(ht : Eq Bool (cmp ty1 gt) Bool.true)",
            "(h1 : Eq Bool (cmp lty glt) Bool.true)",
            "(hs : Eq Bool (cmp psub sub2) Bool.true)",
        ] {
            assert!(
                src.contains(premise),
                "recursive intro rule must take its premise through the comparator: {premise}"
            );
        }
    }
}
