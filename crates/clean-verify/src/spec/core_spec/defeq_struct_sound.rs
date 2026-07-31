// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! SOUNDNESS of the structural conversion algorithm (`def_eq_struct` /
//! `def_eq_fuel`) against `DefEq`.
//!
//! This lands BEFORE any completeness statement, deliberately. Completeness on
//! its own is not a property worth having: `fun _ _ => Bool.true` is complete
//! against every relation. A completeness theorem is only informative about an
//! algorithm that is already known not to accept junk, so soundness is the
//! prerequisite, not the follow-up.
//!
//! Two theorems:
//!
//! - `def_eq_struct_sound` — one structural layer. Given a comparator `cmp`
//!   that is itself sound (`cmp x y = true -> DefEq x y`), if the 9x9 grid
//!   accepts `a` against `b` then `DefEq a b`. The proof is a double
//!   `KExpr.rec`, exactly the shape `kexpr_beq_eq` uses
//!   (`kexpr_beq_sound.rs:1340`): 72 cross-constructor arms are discharged by
//!   `bool_false_ne_true_t` (the *Type*-CPS no-confusion — `DefEq` is
//!   `Type`-valued, so the Prop-CPS `bool_false_ne_true` does not apply here),
//!   and the 9 diagonal arms use the matching `DefEq` congruence constructor
//!   (`app_cong` / `lam_cong` / `pi_cong` / `let_cong` / `proj_cong`) or, at the
//!   leaves, the decidable-equality inversion substrate plus `def_eq_of_eq`.
//!
//! - `def_eq_fuel_sound` — the whole fuel-indexed algorithm:
//!   `def_eq_fuel the_red_env n a b = true -> DefEq a b`, by `Nat.rec` on the
//!   fuel. Fuel 0 accepts nothing, so the base case is absurd; the successor
//!   case recovers the two whnf legs, converts each side to its normal form via
//!   `whnf_fuel_red_conv` + `whnf_red_conv_to_def_eq`, and closes the middle
//!   with `def_eq_struct_sound` applied to the induction hypothesis.
//!
//! `the_red_env` is FIXED rather than a general `renv`: `whnf_red_conv_to_def_eq`
//! is fixed there by necessity (`DefEq.delta` / `DefEq.iota` consume
//! `delta_reduces` / `iota_reduces`, which are relations at the literal
//! `the_red_env`), and `defeq_fuel.rs:203-213` already records why the
//! general-environment statement is not available.
//!
//! Supporting lemma introduced here: `opt_rec_bool_true_inv`, the
//! `OptionType`-scrutinee inversion that turns
//! `OptionType.rec … Bool.false f o = true` into a witness `o = some x`
//! together with `f x = true`. It is what lets `def_eq_fuel_sound` be stated in
//! the honest `= true -> DefEq a b` form instead of the "legs" form
//! `def_eq_whnf_fuel_sound` had to use (`defeq_fuel.rs:60-66` explains that
//! detour: the Bool form needs a dependent case analysis on two `OptionType`s).
//! Proving that inversion once, generically, is what removes the detour.
//!
//! Every declaration here is `DerivedProved` with an empty axiom closure. No
//! new axioms, no `add_decl_unchecked`, no `sorry`.
//!
//! ORDERING: called from the tail of `add_defeq_fuel` (stage 139) rather than
//! registered as its own `STAGES` entry, so its position relative to
//! `def_eq_struct` / `def_eq_fuel` cannot drift.

use crate::spec::error::SpecError;
use crate::spec::Specification;

/// The nine `KExpr` constructors, in recursor-minor-premise order, paired with
/// the inner-arm binder list each contributes when it is the *second* scrutinee.
/// `IH_INNER` slots are filled with the inner motive instantiated at the field.
pub(super) const INNER_BINDERS: [(&str, &str); 9] = [
    ("sort", "(m : Level)"),
    ("bvar", "(j : Nat)"),
    ("app", "(g : KExpr) (c : KExpr)"),
    ("lam", "(gt : KExpr) (gb : KExpr)"),
    ("pi", "(gt : KExpr) (gb : KExpr)"),
    ("const", "(n2 : Name) (us2 : ListType Level)"),
    ("let_", "(glt : KExpr) (glv : KExpr) (glb : KExpr)"),
    ("proj", "(s2 : Name) (i2 : Nat) (sub2 : KExpr)"),
    ("lit", "(w2 : Nat)"),
];

/// The applied form of each inner constructor, matching `INNER_BINDERS`.
pub(super) const INNER_FORMS: [&str; 9] = [
    "(KExpr.sort m)",
    "(KExpr.bvar j)",
    "(KExpr.app g c)",
    "(KExpr.lam gt gb)",
    "(KExpr.pi gt gb)",
    "(KExpr.const n2 us2)",
    "(KExpr.let_ glt glv glb)",
    "(KExpr.proj s2 i2 sub2)",
    "(KExpr.lit w2)",
];

/// The recursive fields of each inner constructor (they carry unused IH
/// binders that must still be present for the minor premise to typecheck).
pub(super) const INNER_REC_FIELDS: [&[&str]; 9] = [
    &[],
    &[],
    &["g", "c"],
    &["gt", "gb"],
    &["gt", "gb"],
    &[],
    &["glt", "glv", "glb"],
    &["sub2"],
    &[],
];

impl Specification {
    /// Soundness of `def_eq_struct` and `def_eq_fuel` against `DefEq`.
    pub(super) fn add_defeq_struct_sound(&mut self) -> Result<(), SpecError> {
        self.add_defeq_sound_substrate()?;
        self.add_defeq_struct_computation_rules()?;
        self.add_defeq_struct_sound_decl()?;
        self.add_defeq_fuel_sound_decl()?;
        Ok(())
    }

    /// Small reusable bricks: `Eq KExpr` transport into `DefEq` on either side,
    /// and the `OptionType`-scrutinee Boolean inversion.
    fn add_defeq_sound_substrate(&mut self) -> Result<(), SpecError> {
        // Syntactic equality is definitional equality: transport DefEq.refl.
        // Used by every leaf arm (sort / bvar / const / lit), where the grid
        // compares payloads with a decidable-equality test rather than `cmp`.
        self.add_recursive_def(
            "def def_eq_of_eq (x : KExpr) (y : KExpr) (h : Eq KExpr x y) : DefEq x y := \
             Eq.substType KExpr (fun (z : KExpr) => DefEq x z) x y h (DefEq.refl x)",
            "def_eq_of_eq: syntactically equal terms are definitionally equal — transport \
             DefEq.refl along the equation. The leaf arms of def_eq_struct_sound produce an \
             Eq KExpr from the decidable-equality inversion substrate and need it as a DefEq. \
             DerivedProved, zero axiom_deps.",
        )?;

        // Rewrite the RIGHT side of a DefEq along a syntactic equation. Needed
        // by the proj arm: DefEq.proj_cong can only relate projections at the
        // SAME struct name and index, so the name/index equalities recovered
        // from name_eqb / nat_eqb have to be applied after the congruence.
        self.add_recursive_def(
            "def def_eq_cast_right (x : KExpr) (y : KExpr) (z : KExpr) (d : DefEq x y) \
             (h : Eq KExpr y z) : DefEq x z := \
             Eq.substType KExpr (fun (q : KExpr) => DefEq x q) y z h d",
            "def_eq_cast_right: rewrite the right-hand side of a DefEq along a syntactic \
             equation. The proj arm of def_eq_struct_sound needs it because DefEq.proj_cong \
             fixes the struct name and field index on both sides, while the grid compares them \
             with name_eqb / nat_eqb. DerivedProved, zero axiom_deps.",
        )?;

        // THE INVERSION that lets def_eq_fuel_sound be stated in `= true` form.
        //
        // `def_eq_fuel` scrutinises two `OptionType KExpr` values that are NOT
        // constructor applications (they are `whnf_fuel_red` calls), so the
        // hypothesis `… = true` cannot be case-split directly. Generalising the
        // scrutinee — the standard convoy — is done ONCE here rather than
        // inlined twice inside the fuel induction.
        self.add_recursive_def(
            "def opt_rec_bool_true_inv (o : OptionType KExpr) (f : KExpr -> Bool) (C : Type) \
             (k : forall (x : KExpr), Eq (OptionType KExpr) o (OptionType.some KExpr x) -> \
             Eq Bool (f x) Bool.true -> C) \
             (h : Eq Bool (OptionType.rec KExpr (fun (_ : OptionType KExpr) => Bool) Bool.false f o) \
             Bool.true) : C := \
             OptionType.rec KExpr \
             (fun (z : OptionType KExpr) => \
             (forall (x : KExpr), Eq (OptionType KExpr) z (OptionType.some KExpr x) -> \
             Eq Bool (f x) Bool.true -> C) -> \
             Eq Bool (OptionType.rec KExpr (fun (_ : OptionType KExpr) => Bool) Bool.false f z) \
             Bool.true -> C) \
             (fun (_k0 : forall (x : KExpr), \
             Eq (OptionType KExpr) (OptionType.none KExpr) (OptionType.some KExpr x) -> \
             Eq Bool (f x) Bool.true -> C) \
             (h0 : Eq Bool Bool.false Bool.true) => bool_false_ne_true_t C h0) \
             (fun (x0 : KExpr) \
             (k1 : forall (x : KExpr), \
             Eq (OptionType KExpr) (OptionType.some KExpr x0) (OptionType.some KExpr x) -> \
             Eq Bool (f x) Bool.true -> C) \
             (h1 : Eq Bool (f x0) Bool.true) => \
             k1 x0 (Eq.refl (OptionType KExpr) (OptionType.some KExpr x0)) h1) \
             o k h",
            "opt_rec_bool_true_inv: OptionType-scrutinee Boolean inversion. If the fail-closed \
             option eliminator `OptionType.rec _ false f o` evaluates to true then o really is \
             `some x` for some x AND `f x = true`; both are handed to the continuation. This is \
             the convoy that lets def_eq_fuel_sound be stated in the honest `= true -> DefEq a b` \
             form rather than the legs form def_eq_whnf_fuel_sound had to use — the none arm is \
             absurd precisely BECAUSE the algorithm fails closed on exhausted fuel. \
             DerivedProved, zero axiom_deps.",
        )?;

        // The Prop-valued twin. `Eq` is Prop-valued, so any consumer whose goal
        // is an equation — fuel monotonicity, for one — cannot use the Type
        // version above: passing an `Eq` where a `Type` is expected is a
        // universe conflict, not a coercion. This mirrors the
        // `bool_false_ne_true` / `bool_false_ne_true_t` pair that exists for
        // exactly the same reason (`faithful_red_env.rs:141`,
        // `env_closed_checkers_depth.rs:232`), and its none arm accordingly uses
        // the Prop-CPS no-confusion.
        self.add_recursive_def(
            "def opt_rec_bool_true_inv_p (o : OptionType KExpr) (f : KExpr -> Bool) (C : Prop) \
             (k : forall (x : KExpr), Eq (OptionType KExpr) o (OptionType.some KExpr x) -> \
             Eq Bool (f x) Bool.true -> C) \
             (h : Eq Bool (OptionType.rec KExpr (fun (_ : OptionType KExpr) => Bool) Bool.false f o) \
             Bool.true) : C := \
             OptionType.rec KExpr \
             (fun (z : OptionType KExpr) => \
             (forall (x : KExpr), Eq (OptionType KExpr) z (OptionType.some KExpr x) -> \
             Eq Bool (f x) Bool.true -> C) -> \
             Eq Bool (OptionType.rec KExpr (fun (_ : OptionType KExpr) => Bool) Bool.false f z) \
             Bool.true -> C) \
             (fun (_k0 : forall (x : KExpr), \
             Eq (OptionType KExpr) (OptionType.none KExpr) (OptionType.some KExpr x) -> \
             Eq Bool (f x) Bool.true -> C) \
             (h0 : Eq Bool Bool.false Bool.true) => bool_false_ne_true C h0) \
             (fun (x0 : KExpr) \
             (k1 : forall (x : KExpr), \
             Eq (OptionType KExpr) (OptionType.some KExpr x0) (OptionType.some KExpr x) -> \
             Eq Bool (f x) Bool.true -> C) \
             (h1 : Eq Bool (f x0) Bool.true) => \
             k1 x0 (Eq.refl (OptionType KExpr) (OptionType.some KExpr x0)) h1) \
             o k h",
            "opt_rec_bool_true_inv_p: the Prop-valued twin of opt_rec_bool_true_inv. Identical \
             content; it exists because Eq is Prop-valued, so a consumer proving an EQUATION \
             cannot instantiate the Type version — that is a universe conflict, not a coercion. \
             The same split as bool_false_ne_true / bool_false_ne_true_t, and its none arm uses \
             the Prop-CPS member of that pair. DerivedProved, zero axiom_deps.",
        )?;

        Ok(())
    }

    /// The nine `def_eq_struct` computation rules on matching constructors, and
    /// the two `def_eq_fuel` fuel-layer rules. All hold by `Eq.refl` (iota on
    /// the double recursor); they exist so the soundness arms can present the
    /// `= true` hypothesis in the syntactic form the inversion lemmas expect,
    /// which is the same discipline `kexpr_beq_sound.rs:986` follows.
    fn add_defeq_struct_computation_rules(&mut self) -> Result<(), SpecError> {
        let cmp = "(cmp : KExpr -> KExpr -> Bool)";
        let rules: [(&str, &str, &str, &str); 9] = [
            (
                "def_eq_struct_sort_sort",
                "(n : Level) (m : Level)",
                "(KExpr.sort n) (KExpr.sort m)",
                "(level_eqb n m)",
            ),
            (
                "def_eq_struct_bvar_bvar",
                "(i : Nat) (j : Nat)",
                "(KExpr.bvar i) (KExpr.bvar j)",
                "(nat_eqb i j)",
            ),
            (
                "def_eq_struct_app_app",
                "(f : KExpr) (a1 : KExpr) (g : KExpr) (c : KExpr)",
                "(KExpr.app f a1) (KExpr.app g c)",
                "(Bool.and (cmp f g) (cmp a1 c))",
            ),
            (
                "def_eq_struct_lam_lam",
                "(ty1 : KExpr) (b1 : KExpr) (gt : KExpr) (gb : KExpr)",
                "(KExpr.lam ty1 b1) (KExpr.lam gt gb)",
                "(Bool.and (cmp ty1 gt) (cmp b1 gb))",
            ),
            (
                "def_eq_struct_pi_pi",
                "(ty1 : KExpr) (b1 : KExpr) (gt : KExpr) (gb : KExpr)",
                "(KExpr.pi ty1 b1) (KExpr.pi gt gb)",
                "(Bool.and (cmp ty1 gt) (cmp b1 gb))",
            ),
            (
                "def_eq_struct_const_const",
                "(nm : Name) (us : ListType Level) (n2 : Name) (us2 : ListType Level)",
                "(KExpr.const nm us) (KExpr.const n2 us2)",
                "(Bool.and (name_eqb nm n2) (ulist_eqb us us2))",
            ),
            (
                "def_eq_struct_let_let",
                "(lty : KExpr) (lv : KExpr) (lb : KExpr) (glt : KExpr) (glv : KExpr) (glb : KExpr)",
                "(KExpr.let_ lty lv lb) (KExpr.let_ glt glv glb)",
                "(Bool.and (cmp lty glt) (Bool.and (cmp lv glv) (cmp lb glb)))",
            ),
            (
                "def_eq_struct_proj_proj",
                "(ps : Name) (pidx : Nat) (psub : KExpr) (s2 : Name) (i2 : Nat) (sub2 : KExpr)",
                "(KExpr.proj ps pidx psub) (KExpr.proj s2 i2 sub2)",
                "(Bool.and (Bool.and (name_eqb ps s2) (nat_eqb pidx i2)) (cmp psub sub2))",
            ),
            (
                "def_eq_struct_lit_lit",
                "(w : Nat) (w2 : Nat)",
                "(KExpr.lit w) (KExpr.lit w2)",
                "(nat_eqb w w2)",
            ),
        ];

        for (name, binders, forms, rhs) in rules {
            self.add_recursive_def(
                &format!(
                    "def {name} {cmp} {binders} : \
                     Eq Bool (def_eq_struct cmp {forms}) {rhs} := \
                     Eq.refl Bool (def_eq_struct cmp {forms})"
                ),
                &format!(
                    "{name}: def_eq_struct computation rule on matching constructors — the 9x9 \
                     grid's diagonal entry reduces to {rhs} definitionally (Eq.refl, by iota on \
                     the double KExpr.rec). Presents the `= true` hypothesis in the syntactic \
                     form the band / eqb inversions consume. DerivedProved, zero axiom_deps."
                ),
            )?;
        }

        // Fuel layer. Fuel 0 is the fail-closed base; succ unfolds to the two
        // nested option eliminators that opt_rec_bool_true_inv then inverts.
        self.add_recursive_def(
            "def def_eq_fuel_zero (renv : RedEnv) (a : KExpr) (b : KExpr) : \
             Eq Bool (def_eq_fuel renv Nat.zero a b) Bool.false := \
             Eq.refl Bool (def_eq_fuel renv Nat.zero a b)",
            "def_eq_fuel_zero: the algorithm accepts NOTHING at fuel 0 — it fails closed \
             (Eq.refl, definitional). This is what makes the base case of def_eq_fuel_sound \
             absurd rather than requiring an argument. DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            "def def_eq_fuel_succ (renv : RedEnv) (k : Nat) (a : KExpr) (b : KExpr) : \
             Eq Bool (def_eq_fuel renv (Nat.succ k) a b) \
             (OptionType.rec KExpr (fun (_ : OptionType KExpr) => Bool) Bool.false \
             (fun (na : KExpr) => OptionType.rec KExpr (fun (_ : OptionType KExpr) => Bool) \
             Bool.false (fun (nb : KExpr) => def_eq_struct (def_eq_fuel renv k) na nb) \
             (whnf_fuel_red renv k b)) \
             (whnf_fuel_red renv k a)) := \
             Eq.refl Bool (def_eq_fuel renv (Nat.succ k) a b)",
            "def_eq_fuel_succ: one fuel layer unfolds to whnf both sides then compare \
             structurally at fuel k (Eq.refl, definitional). Exposes the two nested option \
             eliminators so opt_rec_bool_true_inv can invert them. DerivedProved, zero \
             axiom_deps.",
        )?;

        Ok(())
    }

    /// A cross-constructor inner arm: the grid entry is `Bool.false`, so the
    /// `= true` hypothesis is absurd. `bool_false_ne_true_t` (Type-CPS) rather
    /// than `bool_false_ne_true` (Prop-CPS) because `DefEq` lands in `Type`.
    fn defeq_absurd_arm(a_form: &str, b_form: &str) -> String {
        format!("bool_false_ne_true_t (DefEq {a_form} {b_form}) h")
    }

    /// The inner `KExpr.rec` on `b`, at a fixed outer form `a_form`. Motive:
    /// `fun zb => def_eq_struct cmp a_form zb = true -> DefEq a_form zb`.
    fn defeq_inner_rec(a_form: &str, arms: &[String; 9]) -> String {
        let mut minors = String::new();
        for (idx, (_ctor, binders)) in INNER_BINDERS.iter().enumerate() {
            let form = INNER_FORMS[idx];
            let mut ih_binders = String::new();
            for field in INNER_REC_FIELDS[idx] {
                ih_binders.push_str(&format!(
                    "(_ : Eq Bool (def_eq_struct cmp {a_form} {field}) Bool.true -> \
                     DefEq {a_form} {field}) "
                ));
            }
            minors.push_str(&format!(
                "(fun {binders} {ih_binders}\
                 (h : Eq Bool (def_eq_struct cmp {a_form} {form}) Bool.true) => {arm}) ",
                arm = arms[idx]
            ));
        }
        format!(
            "fun (b : KExpr) => KExpr.rec \
             (fun (zb : KExpr) => Eq Bool (def_eq_struct cmp {a_form} zb) Bool.true -> \
             DefEq {a_form} zb) {minors}b"
        )
    }

    /// Present the `= true` hypothesis `h` in the grid's reduced form via the
    /// matching computation rule.
    fn defeq_present(a_form: &str, b_form: &str, rhs: &str, rule: &str) -> String {
        format!(
            "(Eq.substType Bool (fun (x : Bool) => Eq Bool x Bool.true) \
             (def_eq_struct cmp {a_form} {b_form}) {rhs} ({rule}) h)"
        )
    }

    /// `def_eq_struct_sound`: one structural layer is sound against `DefEq`.
    fn add_defeq_struct_sound_decl(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            &Self::def_eq_struct_sound_src(),
            "def_eq_struct_sound: SOUNDNESS of one structural layer. If the comparator cmp is \
             itself sound for DefEq, then the 9x9 grid accepting a against b implies DefEq a b. \
             Double KExpr.rec in the shape of kexpr_beq_eq: the 72 cross-constructor entries are \
             Bool.false so their `= true` hypotheses are absurd (bool_false_ne_true_t — the \
             Type-CPS no-confusion, since DefEq is Type-valued); the 9 diagonal entries use the \
             matching DefEq congruence constructor (app_cong / lam_cong / pi_cong / let_cong / \
             proj_cong) or, at sort / bvar / const / lit, the decidable-equality inversion \
             substrate composed with def_eq_of_eq. proj additionally casts because proj_cong \
             fixes the struct name and index. This is the half that must exist BEFORE any \
             completeness claim: completeness alone is satisfied by the constant-true \
             comparator. DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }

    /// The `def_eq_struct_sound` source term. Split out from registration so the
    /// unit tests below can check its shape (arm counts, paren balance) in
    /// milliseconds — a malformed term here is otherwise only discovered by a
    /// full spec build, which is ~40 minutes.
    fn def_eq_struct_sound_src() -> String {
        // ---- sort n ----
        let sort_arm = format!(
            "def_eq_of_eq (KExpr.sort n) (KExpr.sort m) \
             (Eq.cong Level KExpr KExpr.sort n m \
             (level_eqb_eq n m {presented}))",
            presented = Self::defeq_present(
                "(KExpr.sort n)",
                "(KExpr.sort m)",
                "(level_eqb n m)",
                "def_eq_struct_sort_sort cmp n m"
            )
        );
        let outer_sort = format!(
            "(fun (n : Level) => {})",
            Self::defeq_inner_rec(
                "(KExpr.sort n)",
                &Self::arms_with("(KExpr.sort n)", 0, sort_arm)
            )
        );

        // ---- bvar i ----
        let bvar_arm = format!(
            "def_eq_of_eq (KExpr.bvar i) (KExpr.bvar j) \
             (Eq.cong Nat KExpr KExpr.bvar i j \
             (nat_eqb_eq i j {presented}))",
            presented = Self::defeq_present(
                "(KExpr.bvar i)",
                "(KExpr.bvar j)",
                "(nat_eqb i j)",
                "def_eq_struct_bvar_bvar cmp i j"
            )
        );
        let outer_bvar = format!(
            "(fun (i : Nat) => {})",
            Self::defeq_inner_rec(
                "(KExpr.bvar i)",
                &Self::arms_with("(KExpr.bvar i)", 1, bvar_arm)
            )
        );

        // ---- app f a1 ----  DefEq.app_cong f g a1 c
        let app_arm = format!(
            "(fun (hand : Eq Bool (Bool.and (cmp f g) (cmp a1 c)) Bool.true) => \
             (fun (hf : DefEq f g) (ha : DefEq a1 c) => DefEq.app_cong f g a1 c hf ha) \
             (hcmp f g (band_eq_true_left (cmp f g) (cmp a1 c) hand)) \
             (hcmp a1 c (band_eq_true_right (cmp f g) (cmp a1 c) hand))) \
             {presented}",
            presented = Self::defeq_present(
                "(KExpr.app f a1)",
                "(KExpr.app g c)",
                "(Bool.and (cmp f g) (cmp a1 c))",
                "def_eq_struct_app_app cmp f a1 g c"
            )
        );
        let outer_app = format!(
            "(fun (f : KExpr) (a1 : KExpr) \
             (_ : forall (b : KExpr), Eq Bool (def_eq_struct cmp f b) Bool.true -> DefEq f b) \
             (_ : forall (b : KExpr), Eq Bool (def_eq_struct cmp a1 b) Bool.true -> DefEq a1 b) \
             => {})",
            Self::defeq_inner_rec(
                "(KExpr.app f a1)",
                &Self::arms_with("(KExpr.app f a1)", 2, app_arm)
            )
        );

        // ---- lam ty1 b1 ----  DefEq.lam_cong ty1 gt b1 gb
        let lam_arm = format!(
            "(fun (hand : Eq Bool (Bool.and (cmp ty1 gt) (cmp b1 gb)) Bool.true) => \
             (fun (ht : DefEq ty1 gt) (hb : DefEq b1 gb) => DefEq.lam_cong ty1 gt b1 gb ht hb) \
             (hcmp ty1 gt (band_eq_true_left (cmp ty1 gt) (cmp b1 gb) hand)) \
             (hcmp b1 gb (band_eq_true_right (cmp ty1 gt) (cmp b1 gb) hand))) \
             {presented}",
            presented = Self::defeq_present(
                "(KExpr.lam ty1 b1)",
                "(KExpr.lam gt gb)",
                "(Bool.and (cmp ty1 gt) (cmp b1 gb))",
                "def_eq_struct_lam_lam cmp ty1 b1 gt gb"
            )
        );
        let outer_lam = format!(
            "(fun (ty1 : KExpr) (b1 : KExpr) \
             (_ : forall (b : KExpr), Eq Bool (def_eq_struct cmp ty1 b) Bool.true -> DefEq ty1 b) \
             (_ : forall (b : KExpr), Eq Bool (def_eq_struct cmp b1 b) Bool.true -> DefEq b1 b) \
             => {})",
            Self::defeq_inner_rec(
                "(KExpr.lam ty1 b1)",
                &Self::arms_with("(KExpr.lam ty1 b1)", 3, lam_arm)
            )
        );

        // ---- pi ty1 b1 ----  DefEq.pi_cong ty1 gt b1 gb
        let pi_arm = format!(
            "(fun (hand : Eq Bool (Bool.and (cmp ty1 gt) (cmp b1 gb)) Bool.true) => \
             (fun (ht : DefEq ty1 gt) (hb : DefEq b1 gb) => DefEq.pi_cong ty1 gt b1 gb ht hb) \
             (hcmp ty1 gt (band_eq_true_left (cmp ty1 gt) (cmp b1 gb) hand)) \
             (hcmp b1 gb (band_eq_true_right (cmp ty1 gt) (cmp b1 gb) hand))) \
             {presented}",
            presented = Self::defeq_present(
                "(KExpr.pi ty1 b1)",
                "(KExpr.pi gt gb)",
                "(Bool.and (cmp ty1 gt) (cmp b1 gb))",
                "def_eq_struct_pi_pi cmp ty1 b1 gt gb"
            )
        );
        let outer_pi = format!(
            "(fun (ty1 : KExpr) (b1 : KExpr) \
             (_ : forall (b : KExpr), Eq Bool (def_eq_struct cmp ty1 b) Bool.true -> DefEq ty1 b) \
             (_ : forall (b : KExpr), Eq Bool (def_eq_struct cmp b1 b) Bool.true -> DefEq b1 b) \
             => {})",
            Self::defeq_inner_rec(
                "(KExpr.pi ty1 b1)",
                &Self::arms_with("(KExpr.pi ty1 b1)", 4, pi_arm)
            )
        );

        // ---- const nm us ----  name + universe-list equality, then transport
        let const_arm = format!(
            "(fun (hand : Eq Bool (Bool.and (name_eqb nm n2) (ulist_eqb us us2)) Bool.true) => \
             (fun (hn : Eq Name nm n2) (hu : Eq (ListType Level) us us2) => \
             def_eq_of_eq (KExpr.const nm us) (KExpr.const n2 us2) \
             (Eq.trans KExpr (KExpr.const nm us) (KExpr.const n2 us) (KExpr.const n2 us2) \
             (Eq.cong Name KExpr (fun (q : Name) => KExpr.const q us) nm n2 hn) \
             (Eq.cong (ListType Level) KExpr (fun (q : ListType Level) => KExpr.const n2 q) \
             us us2 hu))) \
             (name_eqb_eq nm n2 (band_eq_true_left (name_eqb nm n2) (ulist_eqb us us2) hand)) \
             (ulist_eqb_eq us us2 (band_eq_true_right (name_eqb nm n2) (ulist_eqb us us2) hand))) \
             {presented}",
            presented = Self::defeq_present(
                "(KExpr.const nm us)",
                "(KExpr.const n2 us2)",
                "(Bool.and (name_eqb nm n2) (ulist_eqb us us2))",
                "def_eq_struct_const_const cmp nm us n2 us2"
            )
        );
        let outer_const = format!(
            "(fun (nm : Name) (us : ListType Level) => {})",
            Self::defeq_inner_rec(
                "(KExpr.const nm us)",
                &Self::arms_with("(KExpr.const nm us)", 5, const_arm)
            )
        );

        // ---- let_ lty lv lb ----  DefEq.let_cong, right-nested conjunction
        let let_arm = format!(
            "(fun (hand : Eq Bool (Bool.and (cmp lty glt) \
             (Bool.and (cmp lv glv) (cmp lb glb))) Bool.true) => \
             (fun (hrest : Eq Bool (Bool.and (cmp lv glv) (cmp lb glb)) Bool.true) => \
             (fun (h1 : DefEq lty glt) (h2 : DefEq lv glv) (h3 : DefEq lb glb) => \
             DefEq.let_cong lty glt lv glv lb glb h1 h2 h3) \
             (hcmp lty glt (band_eq_true_left (cmp lty glt) \
             (Bool.and (cmp lv glv) (cmp lb glb)) hand)) \
             (hcmp lv glv (band_eq_true_left (cmp lv glv) (cmp lb glb) hrest)) \
             (hcmp lb glb (band_eq_true_right (cmp lv glv) (cmp lb glb) hrest))) \
             (band_eq_true_right (cmp lty glt) (Bool.and (cmp lv glv) (cmp lb glb)) hand)) \
             {presented}",
            presented = Self::defeq_present(
                "(KExpr.let_ lty lv lb)",
                "(KExpr.let_ glt glv glb)",
                "(Bool.and (cmp lty glt) (Bool.and (cmp lv glv) (cmp lb glb)))",
                "def_eq_struct_let_let cmp lty lv lb glt glv glb"
            )
        );
        let outer_let = format!(
            "(fun (lty : KExpr) (lv : KExpr) (lb : KExpr) \
             (_ : forall (b : KExpr), Eq Bool (def_eq_struct cmp lty b) Bool.true -> DefEq lty b) \
             (_ : forall (b : KExpr), Eq Bool (def_eq_struct cmp lv b) Bool.true -> DefEq lv b) \
             (_ : forall (b : KExpr), Eq Bool (def_eq_struct cmp lb b) Bool.true -> DefEq lb b) \
             => {})",
            Self::defeq_inner_rec(
                "(KExpr.let_ lty lv lb)",
                &Self::arms_with("(KExpr.let_ lty lv lb)", 6, let_arm)
            )
        );

        // ---- proj ps pidx psub ----  proj_cong fixes name+index, so cast after
        let proj_arm = format!(
            "(fun (hand : Eq Bool (Bool.and (Bool.and (name_eqb ps s2) (nat_eqb pidx i2)) \
             (cmp psub sub2)) Bool.true) => \
             (fun (hns : Eq Bool (Bool.and (name_eqb ps s2) (nat_eqb pidx i2)) Bool.true) => \
             (fun (hn : Eq Name ps s2) (hi : Eq Nat pidx i2) (hs : DefEq psub sub2) => \
             def_eq_cast_right (KExpr.proj ps pidx psub) (KExpr.proj ps pidx sub2) \
             (KExpr.proj s2 i2 sub2) (DefEq.proj_cong ps pidx psub sub2 hs) \
             (Eq.trans KExpr (KExpr.proj ps pidx sub2) (KExpr.proj s2 pidx sub2) \
             (KExpr.proj s2 i2 sub2) \
             (Eq.cong Name KExpr (fun (q : Name) => KExpr.proj q pidx sub2) ps s2 hn) \
             (Eq.cong Nat KExpr (fun (q : Nat) => KExpr.proj s2 q sub2) pidx i2 hi))) \
             (name_eqb_eq ps s2 (band_eq_true_left (name_eqb ps s2) (nat_eqb pidx i2) hns)) \
             (nat_eqb_eq pidx i2 (band_eq_true_right (name_eqb ps s2) (nat_eqb pidx i2) hns)) \
             (hcmp psub sub2 (band_eq_true_right \
             (Bool.and (name_eqb ps s2) (nat_eqb pidx i2)) (cmp psub sub2) hand))) \
             (band_eq_true_left (Bool.and (name_eqb ps s2) (nat_eqb pidx i2)) \
             (cmp psub sub2) hand)) \
             {presented}",
            presented = Self::defeq_present(
                "(KExpr.proj ps pidx psub)",
                "(KExpr.proj s2 i2 sub2)",
                "(Bool.and (Bool.and (name_eqb ps s2) (nat_eqb pidx i2)) (cmp psub sub2))",
                "def_eq_struct_proj_proj cmp ps pidx psub s2 i2 sub2"
            )
        );
        let outer_proj = format!(
            "(fun (ps : Name) (pidx : Nat) (psub : KExpr) \
             (_ : forall (b : KExpr), Eq Bool (def_eq_struct cmp psub b) Bool.true -> \
             DefEq psub b) => {})",
            Self::defeq_inner_rec(
                "(KExpr.proj ps pidx psub)",
                &Self::arms_with("(KExpr.proj ps pidx psub)", 7, proj_arm)
            )
        );

        // ---- lit w ----
        let lit_arm = format!(
            "def_eq_of_eq (KExpr.lit w) (KExpr.lit w2) \
             (Eq.cong Nat KExpr KExpr.lit w w2 \
             (nat_eqb_eq w w2 {presented}))",
            presented = Self::defeq_present(
                "(KExpr.lit w)",
                "(KExpr.lit w2)",
                "(nat_eqb w w2)",
                "def_eq_struct_lit_lit cmp w w2"
            )
        );
        let outer_lit = format!(
            "(fun (w : Nat) => {})",
            Self::defeq_inner_rec(
                "(KExpr.lit w)",
                &Self::arms_with("(KExpr.lit w)", 8, lit_arm)
            )
        );

        format!(
            "def def_eq_struct_sound (cmp : KExpr -> KExpr -> Bool) \
             (hcmp : forall (x : KExpr) (y : KExpr), Eq Bool (cmp x y) Bool.true -> DefEq x y) : \
             forall (a : KExpr) (b : KExpr), \
             Eq Bool (def_eq_struct cmp a b) Bool.true -> DefEq a b := \
             fun (a : KExpr) => KExpr.rec \
             (fun (za : KExpr) => forall (b : KExpr), \
             Eq Bool (def_eq_struct cmp za b) Bool.true -> DefEq za b) \
             {outer_sort} {outer_bvar} {outer_app} {outer_lam} {outer_pi} {outer_const} \
             {outer_let} {outer_proj} {outer_lit} a"
        )
    }

    /// Build the nine inner arms for outer form `a_form`, with the substantive
    /// arm at `diag` and `bool_false_ne_true_t` everywhere else.
    fn arms_with(a_form: &str, diag: usize, arm: String) -> [String; 9] {
        let mut out: [String; 9] =
            std::array::from_fn(|idx| Self::defeq_absurd_arm(a_form, INNER_FORMS[idx]));
        out[diag] = arm;
        out
    }

    /// `def_eq_fuel_sound`: the whole fuel-indexed algorithm is sound.
    fn add_defeq_fuel_sound_decl(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            &Self::def_eq_fuel_sound_src(),
            "def_eq_fuel_sound: SOUNDNESS OF THE STRUCTURAL CONVERSION ALGORITHM — if \
             def_eq_fuel the_red_env n a b = true then DefEq a b, for every fuel n. Nat.rec on \
             the fuel. Fuel 0 accepts nothing (def_eq_fuel_zero) so the base case is absurd — \
             failing closed is what makes it absurd rather than a proof obligation. The \
             successor case unfolds one layer (def_eq_fuel_succ), recovers both whnf legs with \
             opt_rec_bool_true_inv, converts each side to its normal form (whnf_fuel_red_conv \
             then whnf_red_conv_to_def_eq) and closes the middle with def_eq_struct_sound \
             applied to the induction hypothesis: a ~ na ~ nb ~ b. Fixed at the_red_env because \
             whnf_red_conv_to_def_eq is (DefEq.delta / DefEq.iota consume relations at the \
             literal environment). This is the companion soundness theorem that any completeness \
             statement about def_eq_fuel needs in order to say anything at all. DerivedProved, \
             zero axiom_deps.",
        )?;
        Ok(())
    }

    /// The `def_eq_fuel_sound` source term (split out for the shape tests).
    fn def_eq_fuel_sound_src() -> String {
        // The successor body, after the fuel layer has been unfolded by
        // def_eq_fuel_succ: invert the outer option (a's whnf), then the inner
        // one (b's), then chain a ~ na ~ nb ~ b.
        let inner_fn = "(fun (nb : KExpr) => def_eq_struct (def_eq_fuel the_red_env k) na nb)";
        let outer_fn = format!(
            "(fun (na : KExpr) => OptionType.rec KExpr \
             (fun (_ : OptionType KExpr) => Bool) Bool.false {inner_fn} \
             (whnf_fuel_red the_red_env k b))"
        );

        let chain = "DefEq.trans a na b \
             (whnf_red_conv_to_def_eq a na (whnf_fuel_red_conv the_red_env k a na hna)) \
             (DefEq.trans na nb b \
             (def_eq_struct_sound (def_eq_fuel the_red_env k) ih na nb hgrid) \
             (DefEq.symm b nb \
             (whnf_red_conv_to_def_eq b nb (whnf_fuel_red_conv the_red_env k b nb hnb))))";

        let succ_body = format!(
            "opt_rec_bool_true_inv (whnf_fuel_red the_red_env k a) {outer_fn} (DefEq a b) \
             (fun (na : KExpr) \
             (hna : Eq (OptionType KExpr) (whnf_fuel_red the_red_env k a) \
             (OptionType.some KExpr na)) \
             (hin : Eq Bool (OptionType.rec KExpr (fun (_ : OptionType KExpr) => Bool) \
             Bool.false {inner_fn} (whnf_fuel_red the_red_env k b)) Bool.true) => \
             opt_rec_bool_true_inv (whnf_fuel_red the_red_env k b) {inner_fn} (DefEq a b) \
             (fun (nb : KExpr) \
             (hnb : Eq (OptionType KExpr) (whnf_fuel_red the_red_env k b) \
             (OptionType.some KExpr nb)) \
             (hgrid : Eq Bool (def_eq_struct (def_eq_fuel the_red_env k) na nb) Bool.true) => \
             {chain}) hin) \
             (Eq.substType Bool (fun (x : Bool) => Eq Bool x Bool.true) \
             (def_eq_fuel the_red_env (Nat.succ k) a b) \
             (OptionType.rec KExpr (fun (_ : OptionType KExpr) => Bool) Bool.false {outer_fn} \
             (whnf_fuel_red the_red_env k a)) \
             (def_eq_fuel_succ the_red_env k a b) h)"
        );

        format!(
            "def def_eq_fuel_sound : forall (n : Nat) (a : KExpr) (b : KExpr), \
             Eq Bool (def_eq_fuel the_red_env n a b) Bool.true -> DefEq a b := \
             Nat.rec (fun (z : Nat) => forall (a : KExpr) (b : KExpr), \
             Eq Bool (def_eq_fuel the_red_env z a b) Bool.true -> DefEq a b) \
             (fun (a : KExpr) (b : KExpr) \
             (h : Eq Bool (def_eq_fuel the_red_env Nat.zero a b) Bool.true) => \
             bool_false_ne_true_t (DefEq a b) \
             (Eq.trans Bool Bool.false (def_eq_fuel the_red_env Nat.zero a b) Bool.true \
             (Eq.symm Bool (def_eq_fuel the_red_env Nat.zero a b) Bool.false \
             (def_eq_fuel_zero the_red_env a b)) h)) \
             (fun (k : Nat) \
             (ih : forall (a : KExpr) (b : KExpr), \
             Eq Bool (def_eq_fuel the_red_env k a b) Bool.true -> DefEq a b) \
             (a : KExpr) (b : KExpr) \
             (h : Eq Bool (def_eq_fuel the_red_env (Nat.succ k) a b) Bool.true) => {succ_body})"
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Parenthesis balance, scanning left to right. Returns the running depth at
    /// the end, or `None` if it ever went negative (a close before its open).
    fn paren_depth(src: &str) -> Option<i64> {
        let mut depth: i64 = 0;
        for ch in src.chars() {
            match ch {
                '(' => depth += 1,
                ')' => {
                    depth -= 1;
                    if depth < 0 {
                        return None;
                    }
                }
                _ => {}
            }
        }
        Some(depth)
    }

    #[test]
    fn test_def_eq_struct_sound_src_parens_balanced() {
        let src = Specification::def_eq_struct_sound_src();
        assert_eq!(
            paren_depth(&src),
            Some(0),
            "def_eq_struct_sound term must be paren-balanced"
        );
    }

    #[test]
    fn test_def_eq_fuel_sound_src_parens_balanced() {
        let src = Specification::def_eq_fuel_sound_src();
        assert_eq!(
            paren_depth(&src),
            Some(0),
            "def_eq_fuel_sound term must be paren-balanced"
        );
    }

    /// The 9x9 grid has exactly 72 off-diagonal entries, each discharged by the
    /// Type-CPS no-confusion. If a diagonal arm were accidentally left as an
    /// absurd arm — or an absurd arm overwritten — this count moves.
    #[test]
    fn test_def_eq_struct_sound_src_has_exactly_72_absurd_arms() {
        let src = Specification::def_eq_struct_sound_src();
        let absurd = src.matches("bool_false_ne_true_t (DefEq ").count();
        assert_eq!(
            absurd, 72,
            "expected 72 cross-constructor absurd arms (81 grid entries minus 9 diagonal), got {absurd}"
        );
    }

    /// The Prop-CPS `bool_false_ne_true` cannot discharge a `DefEq` goal
    /// (`DefEq` is `Type`-valued). Using it would be a type error found only by
    /// a full spec build, so pin the choice here.
    #[test]
    fn test_def_eq_struct_sound_src_uses_type_cps_no_confusion_only() {
        let src = Specification::def_eq_struct_sound_src();
        let prop_cps = src.matches("bool_false_ne_true (").count();
        assert_eq!(
            prop_cps, 0,
            "DefEq is Type-valued: every absurd arm must use bool_false_ne_true_t, not the \
             Prop-CPS bool_false_ne_true"
        );
    }

    /// Each of the nine diagonal entries must actually appear, via its
    /// computation rule. A missing one means an arm silently stayed absurd,
    /// which would make the theorem vacuous on that constructor.
    #[test]
    fn test_def_eq_struct_sound_src_covers_all_nine_diagonals() {
        let src = Specification::def_eq_struct_sound_src();
        for rule in [
            "def_eq_struct_sort_sort",
            "def_eq_struct_bvar_bvar",
            "def_eq_struct_app_app",
            "def_eq_struct_lam_lam",
            "def_eq_struct_pi_pi",
            "def_eq_struct_const_const",
            "def_eq_struct_let_let",
            "def_eq_struct_proj_proj",
            "def_eq_struct_lit_lit",
        ] {
            assert!(
                src.contains(rule),
                "diagonal arm missing: {rule} never appears, so that constructor pair is \
                 discharged as absurd instead of proved"
            );
        }
    }

    /// The five recursive diagonals must invoke the matching `DefEq` congruence
    /// constructor — that is where the soundness content lives.
    #[test]
    fn test_def_eq_struct_sound_src_uses_the_defeq_congruences() {
        let src = Specification::def_eq_struct_sound_src();
        for ctor in [
            "DefEq.app_cong",
            "DefEq.lam_cong",
            "DefEq.pi_cong",
            "DefEq.let_cong",
            "DefEq.proj_cong",
        ] {
            assert!(src.contains(ctor), "missing congruence constructor: {ctor}");
        }
    }

    /// Ten outer/inner recursor motives (one outer + nine inner) — the shape
    /// that caught the 81-arm generator's transposition risk in `def_eq_struct`.
    #[test]
    fn test_def_eq_struct_sound_src_has_ten_kexpr_recs() {
        let src = Specification::def_eq_struct_sound_src();
        let recs = src.matches("KExpr.rec ").count();
        assert_eq!(
            recs, 10,
            "expected 1 outer KExpr.rec + 9 inner ones, got {recs}"
        );
    }

    /// `def_eq_fuel_sound` must invert BOTH option scrutinees (a's whnf and
    /// b's). One inversion would mean one side was never case-split.
    #[test]
    fn test_def_eq_fuel_sound_src_inverts_both_whnf_legs() {
        let src = Specification::def_eq_fuel_sound_src();
        let inversions = src.matches("opt_rec_bool_true_inv ").count();
        assert_eq!(
            inversions, 2,
            "expected one option inversion per side, got {inversions}"
        );
        assert!(
            src.contains("whnf_fuel_red the_red_env k a")
                && src.contains("whnf_fuel_red the_red_env k b"),
            "both whnf legs must be scrutinised"
        );
        assert!(
            src.contains("def_eq_struct_sound (def_eq_fuel the_red_env k) ih"),
            "the middle step must feed the induction hypothesis to def_eq_struct_sound"
        );
    }

    /// The fuel-0 base case is absurd only because the algorithm fails closed.
    #[test]
    fn test_def_eq_fuel_sound_src_base_case_uses_fail_closed() {
        let src = Specification::def_eq_fuel_sound_src();
        assert!(
            src.contains("def_eq_fuel_zero the_red_env a b"),
            "the fuel-0 arm must discharge via def_eq_fuel_zero (fail-closed), not by assumption"
        );
    }

    /// No reserved word may be used as a binder. The spec parser reserves `rec`
    /// (among others); a binder named `rec` cost a full ~50-minute build cycle
    /// to diagnose, since these are source strings the Rust compiler never sees.
    #[test]
    fn test_generated_terms_use_no_reserved_words_as_binders() {
        let reserved = [
            "rec", "fun", "let", "match", "with", "where", "do", "from", "by", "have", "show",
            "end", "open", "if", "then", "else",
        ];
        for src in [
            Specification::def_eq_struct_sound_src(),
            Specification::def_eq_fuel_sound_src(),
        ] {
            for word in reserved {
                assert!(
                    !src.contains(&format!("({word} :")),
                    "reserved word `{word}` used as a binder name"
                );
            }
        }
    }
}
