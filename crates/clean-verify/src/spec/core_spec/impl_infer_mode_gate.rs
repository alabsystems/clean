// Copyright 2026 Andrew Yates.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! The mode-gate side lemma and the arm-coverage ledger (job C1 / migration
//! step M5 of `designs/2026-07-29-unified-implinfer-relation.md`).
//!
//! # What this discharges
//!
//! `ImplInfer` carries a rule for 10 of the release dispatcher's 24 arms. The
//! other 14 are accounted for HERE, and the accounting is *checked*, not
//! asserted in prose:
//!
//! * **13 extension arms** are discharged by ONE side lemma. Under
//!   `mode = CleanMode::Constructive` — the `#[default]` (`mode.rs:29-36`) —
//!   every one of them hits an unconditional gate and returns
//!   `Err(ModeRequired)` **before any recursion**. Verified at source, gate by
//!   gate:
//!   - the 8 cubical arms test `self.mode.has_cubical_layer()`
//!     (`infer_cubical.rs:25,38,55,122,162,199,289,360`), which is
//!     `matches!(self, Cubical | Directed)` (`mode.rs:311-313`);
//!   - the 3 ZFC arms test `self.mode != CleanMode::SetTheoretic`
//!     (`infer_zfc.rs:31,93,127`);
//!   - `SProp` and `Squash` test membership in
//!     `{Impredicative, Classical, SetTheoretic}` (`infer_zfc.rs:159-164`,
//!     `:177-182`).
//! * **1 arm is excluded outright and named individually**: `Proj`
//!   (`tc/infer.rs:651`).
//!
//! # Standing rule 3, as a theorem instead of a sentence
//!
//! "Coverage is stated as a fraction, never rounded up. Excluded arms are named
//! individually." `ReleaseArm` enumerates all 24 arms in source order, and three
//! kernel-checked theorems pin the partition:
//!
//! * `impl_infer_arm_partition` — every arm is modelled, mode-gated, or `Proj`;
//! * `impl_infer_proj_is_the_only_exclusion` — `Proj` is *exactly* the arm that
//!   is neither modelled nor mode-gated;
//! * `impl_expr_arm_never_extension` / `impl_expr_arm_never_proj` — the layer-1
//!   syntax's image lands only in the modelled arms, so the fraction is a fact
//!   about `ImplExpr` and not a claim about a comment.
//!
//! `impl_infer_mode_gate_cubical_opens` is the non-vacuity guard on the gate
//! model itself: without it, an `arm_gate` that returned `false` everywhere
//! would satisfy the side lemma trivially.
//!
//! ZERO new axioms; every proof is `Eq.refl` on a computed Boolean.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::Specification;

/// The 24 release dispatch arms, in the exact order they appear in
/// `infer_type_fast_inner`'s `match` (`tc/infer.rs:349-683`).
const ARMS: [&str; 24] = [
    "bvar",
    "fvar",
    "sort",
    "const",
    "app",
    "lam",
    "pi",
    "let_",
    "lit",
    "proj",
    "mdata",
    "cubicalInterval",
    "cubicalEndpoint",
    "cubicalPath",
    "cubicalPathLam",
    "cubicalPathApp",
    "cubicalHComp",
    "cubicalTransp",
    "cubicalCoe",
    "zfcSet",
    "zfcMem",
    "zfcComprehension",
    "sprop",
    "squash",
];

/// Arms with NO mode gate at all — the 11 core arms (`bvar` .. `mdata`).
const CORE_ARMS: usize = 11;

/// The release dispatcher's arm names, for the C1 acceptance test's ledger-width
/// check (the fraction must not be able to shrink silently).
#[cfg(test)]
pub(super) fn release_arm_names() -> &'static [&'static str] {
    &ARMS
}

impl Specification {
    /// M5: the arm ledger, the mode gates, and the side lemma.
    pub(super) fn add_impl_infer_mode_gate(&mut self) -> Result<(), SpecError> {
        self.add_mode_gate_types()?;
        self.add_mode_gate_theorems()?;
        Ok(())
    }

    fn add_mode_gate_types(&mut self) -> Result<(), SpecError> {
        // CleanMode, transcribed. Only the six logical modes exist
        // (mode.rs:36,45,61,87,97,106); the later enums in that file are
        // export targets and axiom tags, not checker modes.
        self.add_inductive(
            r"inductive CleanModeM : Type
| constructive : CleanModeM
| impredicative : CleanModeM
| cubical : CleanModeM
| directed : CleanModeM
| classical : CleanModeM
| setTheoretic : CleanModeM",
            "The kernel's logical mode, transcribing clean_kernel::CleanMode \
             (mode.rs:36,45,61,87,97,106). `constructive` is the #[default] — the \
             mode every declaration is admitted under unless explicitly changed, \
             which is why the side lemma below is stated at exactly that mode.",
        )?;

        let arm_ctors = ARMS
            .iter()
            .map(|a| format!("| {a} : ReleaseArm"))
            .collect::<Vec<_>>()
            .join("\n");
        self.add_inductive(
            &format!("inductive ReleaseArm : Type\n{arm_ctors}"),
            "The 24 dispatch arms of the release body infer_type_fast_inner \
             (tc/infer.rs:349-683), in source order. `cubicalEndpoint` is ONE arm \
             because CubicalI0 and CubicalI1 share an or-pattern (:667). This \
             enumeration exists so coverage can be a kernel-checked FRACTION rather \
             than a sentence in a comment.",
        )?;

        // The three gate predicates, transcribed from mode.rs / infer_zfc.rs.
        self.add_recursive_def(
            r"def mode_has_cubical_layer (m : CleanModeM) : Bool := match m with
| CleanModeM.constructive => Bool.false
| CleanModeM.impredicative => Bool.false
| CleanModeM.cubical => Bool.true
| CleanModeM.directed => Bool.true
| CleanModeM.classical => Bool.false
| CleanModeM.setTheoretic => Bool.false",
            "CleanMode::has_cubical_layer (mode.rs:311-313): \
             `matches!(self, CleanMode::Cubical | CleanMode::Directed)` — the 2LTT \
             bridge makes Directed carry the cubical capability. This is the gate \
             all EIGHT cubical inference arms test.",
        )?;
        self.add_recursive_def(
            r"def mode_is_set_theoretic (m : CleanModeM) : Bool := match m with
| CleanModeM.constructive => Bool.false
| CleanModeM.impredicative => Bool.false
| CleanModeM.cubical => Bool.false
| CleanModeM.directed => Bool.false
| CleanModeM.classical => Bool.false
| CleanModeM.setTheoretic => Bool.true",
            "The ZFC gate: `self.mode != CleanMode::SetTheoretic` rejects \
             (infer_zfc.rs:31,93,127), so the arm proceeds exactly at SetTheoretic.",
        )?;
        self.add_recursive_def(
            r"def mode_has_sprop (m : CleanModeM) : Bool := match m with
| CleanModeM.constructive => Bool.false
| CleanModeM.impredicative => Bool.true
| CleanModeM.cubical => Bool.false
| CleanModeM.directed => Bool.false
| CleanModeM.classical => Bool.true
| CleanModeM.setTheoretic => Bool.true",
            "The SProp/Squash gate: the arm rejects unless the mode is \
             Impredicative, Classical or SetTheoretic (infer_zfc.rs:159-164, \
             :177-182).",
        )?;

        // arm_gate m a : does arm `a` get past its mode gate in mode `m`?
        // The 11 core arms have NO gate, so they are unconditionally open.
        let gate_arms = ARMS
            .iter()
            .enumerate()
            .map(|(i, a)| {
                let rhs = if i < CORE_ARMS {
                    "Bool.true".to_string()
                } else if a.starts_with("cubical") {
                    "mode_has_cubical_layer m".to_string()
                } else if a.starts_with("zfc") {
                    "mode_is_set_theoretic m".to_string()
                } else {
                    "mode_has_sprop m".to_string()
                };
                format!("| ReleaseArm.{a} => {rhs}")
            })
            .collect::<Vec<_>>()
            .join("\n");
        self.add_recursive_def(
            &format!("def arm_gate (m : CleanModeM) (a : ReleaseArm) : Bool := match a with\n{gate_arms}"),
            "Does a dispatch arm get past its mode gate in a given mode? The 11 core \
             arms (bvar..mdata) have NO gate and are unconditionally open; the 8 \
             cubical arms test has_cubical_layer, the 3 ZFC arms test SetTheoretic, \
             and SProp/Squash test the impredicative family. Each gate is \
             UNCONDITIONAL and fires BEFORE any recursion, which is what makes one \
             lemma enough for all 13.",
        )?;

        let ext_arms = ARMS
            .iter()
            .enumerate()
            .map(|(i, a)| {
                let rhs = if i < CORE_ARMS {
                    "Bool.false"
                } else {
                    "Bool.true"
                };
                format!("| ReleaseArm.{a} => {rhs}")
            })
            .collect::<Vec<_>>()
            .join("\n");
        self.add_recursive_def(
            &format!("def arm_is_extension (a : ReleaseArm) : Bool := match a with\n{ext_arms}"),
            "The 13 mode-gated EXTENSION arms (cubicalInterval..squash), as opposed \
             to the 11 core arms. Named individually by construction — the \
             enumeration IS the list.",
        )?;

        let proj_arms = ARMS
            .iter()
            .map(|a| {
                let rhs = if *a == "proj" {
                    "Bool.true"
                } else {
                    "Bool.false"
                };
                format!("| ReleaseArm.{a} => {rhs}")
            })
            .collect::<Vec<_>>()
            .join("\n");
        self.add_recursive_def(
            &format!("def arm_is_proj (a : ReleaseArm) : Bool := match a with\n{proj_arms}"),
            "The single arm EXCLUDED OUTRIGHT: Proj (tc/infer.rs:651). It calls \
             is_prop, which calls infer_type_infer_only — a mode switch INSIDE the \
             arm — plus a proj_type_cache keyed on a rebuilt node and a full \
             constructor-telescope walk (infer_proj.rs:243-341).",
        )?;

        let modelled_arms = ARMS
            .iter()
            .enumerate()
            .map(|(i, a)| {
                let rhs = if i < CORE_ARMS && *a != "proj" {
                    "Bool.true"
                } else {
                    "Bool.false"
                };
                format!("| ReleaseArm.{a} => {rhs}")
            })
            .collect::<Vec<_>>()
            .join("\n");
        self.add_recursive_def(
            &format!("def arm_modelled (a : ReleaseArm) : Bool := match a with\n{modelled_arms}"),
            "The 10 arms ImplInfer carries a rule for: the 9 successful-inference \
             constructors (sort, fvar, const, app, lam, pi, let_, lit, mdata) plus \
             `bvar`, whose rule is the REFUTATION impl_infer_bvar_rejects.",
        )?;

        // The bridge from the layer-1 syntax to the arm ledger: which dispatch
        // arm does each ImplExpr constructor land in?
        self.add_recursive_def(
            r"def impl_expr_arm (e : ImplExpr) : ReleaseArm := match e with
| ImplExpr.bvar i => ReleaseArm.bvar
| ImplExpr.fvar y => ReleaseArm.fvar
| ImplExpr.sort l => ReleaseArm.sort
| ImplExpr.const nm us => ReleaseArm.const
| ImplExpr.app f a => ReleaseArm.app
| ImplExpr.lam bd ty b => ReleaseArm.lam
| ImplExpr.pi bd ty b => ReleaseArm.pi
| ImplExpr.let_ nm ty v b => ReleaseArm.let_
| ImplExpr.lit lt => ReleaseArm.lit
| ImplExpr.mdata inner => ReleaseArm.mdata",
            "Which release dispatch arm an ImplExpr node lands in. This is the bridge \
             that turns the coverage fraction into a fact about the SYNTAX rather \
             than a claim about a comment: see impl_expr_arm_never_extension and \
             impl_expr_arm_never_proj.",
        )?;

        Ok(())
    }

    fn add_mode_gate_theorems(&mut self) -> Result<(), SpecError> {
        // ── THE SIDE LEMMA ─────────────────────────────────────────────────
        // Stated as `and (extension a) (gate constructive a) = false`, i.e.
        // "no extension arm's gate is open in Constructive mode". Every one of
        // the 24 cases is Eq.refl on a computed Boolean:
        //   core arm      -> and false true  = false
        //   extension arm -> and true  false = false
        self.register_arm_rec_theorem(
            "impl_infer_mode_gate_constructive",
            "Eq Bool (Bool.and (arm_is_extension a) (arm_gate CleanModeM.constructive a)) Bool.false",
            "Eq.refl Bool Bool.false",
            concat!(
                "THE MODE-GATE SIDE LEMMA: in Constructive mode — the #[default], and the ",
                "mode every declaration is admitted under unless explicitly changed — NO ",
                "extension arm's gate is open. Read as an implication: an arm being an ",
                "extension arm forces its Constructive gate closed, so all 13 return ",
                "Err(ModeRequired) BEFORE any recursion (infer_cubical.rs:25,38,55,122,162,",
                "199,289,360; infer_zfc.rs:31,93,127,164,181). That is what lets ONE lemma ",
                "discharge 13 of the 24 dispatch arms, and why ImplExpr carries no ",
                "extension constructor. Proved by ReleaseArm.rec with 24 Eq.refl minors — ",
                "each side COMPUTES. Zero axiom_deps."
            ),
            &[
                "ReleaseArm",
                "arm_is_extension",
                "arm_gate",
                "CleanModeM",
                "Eq.refl",
            ],
        )?;

        // ── NON-VACUITY OF THE GATE MODEL ──────────────────────────────────
        // Without this, an `arm_gate` that was constantly false would satisfy
        // the side lemma trivially and prove nothing about the deployed gates.
        self.add_definition(SpecDefinition {
            name: "impl_infer_mode_gate_cubical_opens".to_string(),
            type_src: "Eq Bool (arm_gate CleanModeM.cubical ReleaseArm.cubicalPath) Bool.true"
                .to_string(),
            value_src: Some("Eq.refl Bool Bool.true".to_string()),
            is_axiom: false,
            description: "NON-VACUITY GUARD on the mode-gate model: the cubical Path arm's \
                          gate DOES open in Cubical mode. Without this, an arm_gate that \
                          returned false everywhere would satisfy \
                          impl_infer_mode_gate_constructive trivially while modelling nothing \
                          — the exact failure shape the vacuity firewall exists to catch. \
                          Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "arm_gate".to_string(),
                "CleanModeM".to_string(),
                "ReleaseArm".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ── THE COVERAGE PARTITION (standing rule 3, as a theorem) ──────────
        self.register_arm_rec_theorem(
            "impl_infer_arm_partition",
            "Eq Bool (Bool.or (arm_modelled a) (Bool.or (arm_is_extension a) (arm_is_proj a))) Bool.true",
            "Eq.refl Bool Bool.true",
            concat!(
                "COVERAGE, as a kernel-checked fraction: every one of the 24 release ",
                "dispatch arms is either MODELLED by an ImplInfer rule (10), discharged by ",
                "the mode-gate side lemma (13), or the single named exclusion Proj (1). ",
                "10 + 13 + 1 = 24, and 23 of 24 are accounted for by a rule or a proof. ",
                "Proved by ReleaseArm.rec with 24 Eq.refl minors. Zero axiom_deps."
            ),
            &[
                "ReleaseArm",
                "arm_modelled",
                "arm_is_extension",
                "arm_is_proj",
                "Eq.refl",
            ],
        )?;

        self.register_arm_rec_theorem(
            "impl_infer_proj_is_the_only_exclusion",
            "Eq Bool (arm_is_proj a) (Bool.and (Bool.not (arm_modelled a)) (Bool.not (arm_is_extension a)))",
            "Eq.refl Bool (arm_is_proj a)",
            concat!(
                "Proj is EXACTLY the arm that is neither modelled nor mode-gated — the ",
                "excluded arm named individually, as standing rule 3 requires, and proved ",
                "rather than asserted. Any future rule that silently dropped an arm would ",
                "break this equation. Proved by ReleaseArm.rec, every minor Eq.refl. ",
                "Zero axiom_deps."
            ),
            &[
                "ReleaseArm",
                "arm_is_proj",
                "arm_modelled",
                "arm_is_extension",
                "Eq.refl",
            ],
        )?;

        // ── THE SYNTAX BRIDGE ──────────────────────────────────────────────
        // ImplExpr's image lands only in the modelled arms — so the coverage
        // fraction is a fact about the syntax, not about a comment.
        self.register_implexpr_rec_theorem(
            "impl_expr_arm_never_extension",
            "Eq Bool (arm_is_extension (impl_expr_arm e)) Bool.false",
            concat!(
                "The layer-1 syntax NEVER lands in a mode-gated arm: every ImplExpr ",
                "constructor maps to one of the 11 core dispatch arms. This is the bridge ",
                "that makes the 13-arm mode-gate discharge a structural fact about ImplExpr ",
                "rather than a promise — the extension constructors are absent by ",
                "construction, and here that absence is checked. Proved by ImplExpr.rec, ",
                "every minor Eq.refl. Zero axiom_deps."
            ),
            &["ImplExpr", "impl_expr_arm", "arm_is_extension", "Eq.refl"],
        )?;

        self.register_implexpr_rec_theorem(
            "impl_expr_arm_never_proj",
            "Eq Bool (arm_is_proj (impl_expr_arm e)) Bool.false",
            concat!(
                "The layer-1 syntax NEVER lands in the excluded Proj arm. Together with ",
                "impl_expr_arm_never_extension this pins ImplExpr's image to exactly the 10 ",
                "arms ImplInfer carries a rule for — the coverage fraction, checked. ",
                "Proved by ImplExpr.rec, every minor Eq.refl. Zero axiom_deps."
            ),
            &["ImplExpr", "impl_expr_arm", "arm_is_proj", "Eq.refl"],
        )?;

        Ok(())
    }

    /// Register `forall (a : ReleaseArm), <goal>` proved by `ReleaseArm.rec`
    /// with one identical `Eq.refl` minor per arm.
    ///
    /// `ReleaseArm` has 24 nullary constructors, so every minor is a closed
    /// term and the recursion is a pure case split — the whole proof is "each
    /// of the 24 sides computes to the same Boolean".
    fn register_arm_rec_theorem(
        &mut self,
        name: &str,
        goal: &str,
        minor_template: &str,
        description: &str,
        deps: &[&str],
    ) -> Result<(), SpecError> {
        let minors = ARMS
            .iter()
            .map(|a| {
                // `Eq.refl Bool (arm_is_proj a)` needs `a` replaced by the
                // literal constructor in each minor; the other templates are
                // already closed.
                format!(
                    "({}) ",
                    minor_template.replace(" a)", &format!(" ReleaseArm.{a})"))
                )
            })
            .collect::<String>();
        let value = format!(
            "fun (a : ReleaseArm) => ReleaseArm.rec (fun (z : ReleaseArm) => {}) {minors}a",
            goal.replace(" a)", " z)")
        );
        self.add_definition(SpecDefinition {
            name: name.to_string(),
            type_src: format!("forall (a : ReleaseArm), {goal}"),
            value_src: Some(value),
            is_axiom: false,
            description: description.to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(deps.iter().map(|d| (*d).to_string()).collect()),
            axiom_deps: HashSet::new(),
        })
    }

    /// Register `forall (e : ImplExpr), <goal>` proved by `ImplExpr.rec` with
    /// one `Eq.refl Bool Bool.false` minor per constructor.
    ///
    /// Minor shapes follow `ImplExpr`'s declaration order and arity, with the
    /// induction hypotheses for recursive fields appended last.
    fn register_implexpr_rec_theorem(
        &mut self,
        name: &str,
        goal: &str,
        description: &str,
        deps: &[&str],
    ) -> Result<(), SpecError> {
        // Per constructor: the field binders, then the names of the RECURSIVE
        // fields (whose induction hypotheses the recursor appends last, in field
        // order). Each IH is typed at the motive INSTANTIATED at that field —
        // spelling it as a closed `Eq Bool Bool.false Bool.false` would not
        // typecheck, because `arm_is_extension (impl_expr_arm x)` cannot reduce
        // while `x` is a variable.
        const MINORS: [(&str, &[&str]); 10] = [
            ("(i : Nat)", &[]),
            ("(y : Nat)", &[]),
            ("(l : Level)", &[]),
            ("(nm : Name) (us : ListType Level)", &[]),
            ("(f : ImplExpr) (a : ImplExpr)", &["f", "a"]),
            (
                "(bd : BinderData) (ty : ImplExpr) (b : ImplExpr)",
                &["ty", "b"],
            ),
            (
                "(bd : BinderData) (ty : ImplExpr) (b : ImplExpr)",
                &["ty", "b"],
            ),
            (
                "(nm : Name) (ty : ImplExpr) (v : ImplExpr) (b : ImplExpr)",
                &["ty", "v", "b"],
            ),
            ("(lt : ImplLit)", &[]),
            ("(inner : ImplExpr)", &["inner"]),
        ];
        let minors = MINORS
            .iter()
            .map(|(binders, recs)| {
                let ihs = recs
                    .iter()
                    .map(|field| {
                        format!(
                            " (ih_{field} : {})",
                            goal.replace(" e)", &format!(" {field})"))
                        )
                    })
                    .collect::<String>();
                format!("(fun {binders}{ihs} => Eq.refl Bool Bool.false) ")
            })
            .collect::<String>();
        let value = format!(
            "fun (e : ImplExpr) => ImplExpr.rec (fun (z : ImplExpr) => {}) {minors}e",
            goal.replace(" e)", " z)")
        );
        self.add_definition(SpecDefinition {
            name: name.to_string(),
            type_src: format!("forall (e : ImplExpr), {goal}"),
            value_src: Some(value),
            is_axiom: false,
            description: description.to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(deps.iter().map(|d| (*d).to_string()).collect()),
            axiom_deps: HashSet::new(),
        })
    }
}
