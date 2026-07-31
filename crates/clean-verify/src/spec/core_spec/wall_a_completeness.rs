// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Wall-A COMPLETION — `def_eq_whnf_complete` over the FULL β+ι+δ+ζ reduction
//! (Aristotle port; strategy guide `scratch/aristotle-harvest/
//! aristotle-walla-iota/aristotle-walla-iota_aristotle/WallAIota.lean`, namespace
//! `WallAIota` — IN THE TREE as of the 2026-07-26 second rescue. TREAT IT AS
//! UNVERIFIED: elaborated under leanprover/lean4:v4.30.0-rc2 it exits 1 with 2
//! errors and 1 `sorry`, so the "[propext, Quot.sound]-only closure" this comment
//! used to assert of it is NOT established — the file does not currently compile.
//! It is a strategy sketch, not a checked proof; see
//! scratch/aristotle-harvest/UNRESCUED_CENSUS_2026-07-26.md.
//! ZETA extension per the validated `scratch/aristotle-harvest/
//! aristotle-conf-zeta/aristotle-conf-zeta_aristotle/ConfZeta.lean` guide —
//! `KExpr.let_` is a GENUINE constructor, and
//! `par_reduces_cd` carries the let_ (zeta) contraction plus the trailing
//! let_cong congruence; a let_ is its own spine head, never an iota/delta
//! redex and never neutral/whnf, so the rigidity family survives with
//! let_-headed no-confusion refutation arms — `let_ne_app` and the inline
//! let_ discriminator). Successor of the landed `wall_a_headmatch.rs`
//! statement machinery:
//! this module lands the completeness theorem itself, plus exactly the
//! machinery the follow-up note there named as missing — the WHNF
//! head-rigidity star-inversion family over `par_reduces_cd_star` and the
//! iota-aware neutrality vocabulary.
//!
//! ## Reuse map (mirror -> in-tree; verified lemma-by-lemma)
//!
//! * `Tm`/`lift`/`subst`/`inst` -> `KExpr`/`lift_at`/`instantiate_at`/
//!   `instantiate` (`expr_model.rs`).
//! * `Beta`+`DeltaStep`+`IotaStep` -> `beta_reduces` (iota folded inside) /
//!   `delta_step` / `iota_step` (both graphs of their total reduct functions).
//! * `Step`/`Star`/`Join` -> `par_reduces_cd` / `par_reduces_cd_star` /
//!   `par_strips_witness_cd_star` (the in-tree "steps" are PARALLEL cd steps;
//!   the RT-closures coincide, so all rigidity lemmas here invert the parallel
//!   step directly).
//! * `EnvFaithful` (i1..i8) -> the carried `I_BINDERS` interfaces (verbatim
//!   from `def_eq_joinable.rs`; bundled as `RedEnvFaithful`,
//!   `par_reduces_cd_sound.rs`). CARRIED hypotheses, never discharged here,
//!   never axiomatized.
//! * The mirror's SORRY 3/4/5 confluence core (`par_spine_dead`,
//!   `par_fire_cases`, `dev`/`par_dev`, `par_diamond`) -> NOT re-ported: the
//!   in-tree lane already banked the equivalent strength as the LANDED
//!   unconditional 3-way star diamond `par_reduces_cd_star_diamond`
//!   (`par_reduces_iota_delta.rs`, Hindley-Rosen assembly + the p-relation
//!   topdev/complete-development spine machinery). `star_confluent` = that
//!   diamond; `def_eq_joinable_mirror` = the landed `def_eq_joinable`.
//! * Head rigidity, sort/lam/pi -> REUSED: `par_reduces_cd_sort_inv_eq` (+
//!   `_star_`), `par_reduces_cd_star_lam_inv_eq`, `par_reduces_cd_star_pi_inv_eq`
//!   (`par_reduces_cd_injectivity.rs`).
//! * Head rigidity, const/neutral-spine -> PORTED HERE (did not exist):
//!   dead-const rigidity, the neutral-spine cd/cd_star inversions, and
//!   neutral-vs-neutral `HeadMatch` extraction.
//! * `WhnfTo` -> the trusted `whnf_to`, bridged here into the cd lane
//!   (`whnf_to_cd_star`, also new — no operational->cd injection existed).
//! * `HeadMatch` / `join_defEq` -> the landed `HeadMatch`
//!   (`wall_a_headmatch.rs`) / `join_to_def_eq` (`par_reduces_cd_sound.rs`).
//!
//! ## THE IOTA-AWARE NEUTRALITY DESIGN (the one design decision — lead's call)
//!
//! The trusted `is_neutral` excludes only delta (`const_whnf`). Over β+ι that
//! is NOT enough for completeness: a recursor spine whose major premise merely
//! REDUCES to a constructor (e.g. `R ((fun x => x) C)`) is delta-neutral and
//! not presently an iota redex, yet it is `DefEq` to the fired (binder-headed)
//! reduct — `HeadMatch` at the heads would be FALSE. The trusted
//! `is_neutral`/`is_whnf` are left UNTOUCHED; this module adds PARALLEL
//! predicates as objects of study:
//!
//! * `iota_immune e` — no `par_reduces_cd_star`-reduct of `e` is a top iota
//!   redex (the weakest correct strengthening; mirror `IotaImmune`).
//! * `iota_neutral` — mirror `Neutral`: non-unfolding const heads and their
//!   application spines with every spine node iota-immune.
//! * `iota_whnf` — mirror `Whnf`: sort/lam/pi/iota-neutral.
//!
//! `def_eq_whnf_complete` is stated over `whnf_to` legs whose targets are
//! ADDITIONALLY `iota_whnf` (the strengthened hypothesis). This is FAITHFUL to
//! the real kernel: the kernel's whnf loop whnf-s the major premise before
//! trying iota (the major pre-pass, deferred in `iota_step.rs`'s model), so a
//! term the kernel returns as a whnf has no top iota redex now or ever —
//! iota-immunity holds for genuine kernel whnf results. Structural sufficient
//! conditions (head const without recmeta / under-applied spine / stuck
//! neutral major with no rule) each imply it. This is a STATEMENT-level
//! strengthening beyond i1..i8, not a new env interface.
//!
//! ## The redundant raw delta-dead field (compatibility note)
//!
//! `const_whnf n us` is a semireducible Definition, so the kernel unfolds it
//! during default-transparency definitional equality to
//! `delta_reduct (red_def the_red_env) (const n us) = none`. Consequently the
//! `const_whnf` field and `iota_neutral.const`'s raw equation are definitionally
//! the same fact. The raw field remains as redundant compatibility data: it
//! preserves the mirror/constructor shape and lets the delta-refutation arms
//! consume the equation directly, while `const_whnf` remains pass-through glue
//! for the landed `HeadMatch.const` / trusted `is_neutral.const`. A concrete
//! neutral-const witness is constructible only when the kernel computes that
//! delta reduct to `none`; a delta-reducing constant still fails closed.
//!
//! Zero new axioms: the two new inductives lower to Inductive/Constructor/
//! Recursor; every lemma is DerivedProved with an explicit kernel-checked term
//! and empty axiom closure. `the_red_env` is the literal environment
//! everywhere; i1..i8 enter only through the landed diamond/joinability.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

/// The eight carried faithful-interface hypotheses, as a binder prefix —
/// verbatim from `def_eq_joinable.rs` (specialized to `the_red_env`).
const I_BINDERS: &str = concat!(
    "(i1 : RecEnvReductNotRedex (red_rec the_red_env)) (i2 : RecEnvCtorNoRecMeta (red_rec the_red_env)) ",
    "(i3 : RecEnvClosed (red_rec the_red_env)) (i4 : RecEnvLiftClosed (red_rec the_red_env)) ",
    "(i5 : DefEnvClosed (red_def the_red_env)) (i6 : DefEnvLiftClosed (red_def the_red_env)) ",
    "(i7 : RecEnvDefEnvDisjoint the_red_env) (i8 : RecEnvCtorNoDefVal the_red_env) "
);

/// Inline `KExpr.rec` discriminator: `sort` maps to `Nat` (inhabited), every
/// other head to `Empty`. KExpr ctor order: sort, bvar, app, lam, pi, const,
/// let_, proj, lit.
const KEXPR_IS_SORT: &str = concat!(
    "(KExpr.rec (fun (_ : KExpr) => Type) ",
    "(fun (_ : Level) => Nat) ",
    "(fun (_ : Nat) => Empty) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Empty) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Empty) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Empty) ",
    "(fun (_ : Name) (_ : ListType Level) => Empty) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) (_ : Type) => Empty) ",
    "(fun (_ : Name) (_ : Nat) (_ : KExpr) (_ : Type) => Empty) ",
    "(fun (_ : Nat) => Empty))"
);

/// Inline discriminator: `app` maps to `Nat`, every other head to `Empty`.
const KEXPR_IS_APP: &str = concat!(
    "(KExpr.rec (fun (_ : KExpr) => Type) ",
    "(fun (_ : Level) => Empty) ",
    "(fun (_ : Nat) => Empty) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Empty) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Empty) ",
    "(fun (_ : Name) (_ : ListType Level) => Empty) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) (_ : Type) => Empty) ",
    "(fun (_ : Name) (_ : Nat) (_ : KExpr) (_ : Type) => Empty) ",
    "(fun (_ : Nat) => Empty))"
);

/// Inline discriminator: `lam` maps to `Nat`, every other head to `Empty`.
const KEXPR_IS_LAM: &str = concat!(
    "(KExpr.rec (fun (_ : KExpr) => Type) ",
    "(fun (_ : Level) => Empty) ",
    "(fun (_ : Nat) => Empty) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Empty) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Empty) ",
    "(fun (_ : Name) (_ : ListType Level) => Empty) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) (_ : Type) => Empty) ",
    "(fun (_ : Name) (_ : Nat) (_ : KExpr) (_ : Type) => Empty) ",
    "(fun (_ : Nat) => Empty))"
);

/// Inline discriminator: `pi` maps to `Nat`, every other head to `Empty`.
const KEXPR_IS_PI: &str = concat!(
    "(KExpr.rec (fun (_ : KExpr) => Type) ",
    "(fun (_ : Level) => Empty) ",
    "(fun (_ : Nat) => Empty) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Empty) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Empty) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) ",
    "(fun (_ : Name) (_ : ListType Level) => Empty) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) (_ : Type) => Empty) ",
    "(fun (_ : Name) (_ : Nat) (_ : KExpr) (_ : Type) => Empty) ",
    "(fun (_ : Nat) => Empty))"
);

/// Inline discriminator: `sort` maps to `Empty`, every other head to `Nat`
/// (the complement of `KEXPR_IS_SORT` — kills a sort-vs-nonsort equation in
/// the direction that needs no `Eq.symm`).
const KEXPR_NOT_SORT: &str = concat!(
    "(KExpr.rec (fun (_ : KExpr) => Type) ",
    "(fun (_ : Level) => Empty) ",
    "(fun (_ : Nat) => Nat) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) ",
    "(fun (_ : Name) (_ : ListType Level) => Nat) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) (_ : Type) => Nat) ",
    "(fun (_ : Name) (_ : Nat) (_ : KExpr) (_ : Type) => Nat) ",
    "(fun (_ : Nat) => Nat))"
);

/// Inline discriminator: `const` maps to `Nat`, every other head to `Empty`.
const KEXPR_IS_CONST: &str = concat!(
    "(KExpr.rec (fun (_ : KExpr) => Type) ",
    "(fun (_ : Level) => Empty) ",
    "(fun (_ : Nat) => Empty) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Empty) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Empty) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Empty) ",
    "(fun (_ : Name) (_ : ListType Level) => Nat) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) (_ : Type) => Empty) ",
    "(fun (_ : Name) (_ : Nat) (_ : KExpr) (_ : Type) => Empty) ",
    "(fun (_ : Nat) => Empty))"
);

/// Inline discriminator: `let_` maps to `Nat`, every other head to `Empty`.
/// The let_-headed shape witness — a `let_` node is never a `sort`/`app`/
/// `lam`/`pi`/`const`, so this refutes any equation aligning a let_ with a
/// rigid head (the genuine 7th ctor is its own spine head, never app-headed).
const KEXPR_IS_LET: &str = concat!(
    "(KExpr.rec (fun (_ : KExpr) => Type) ",
    "(fun (_ : Level) => Empty) ",
    "(fun (_ : Nat) => Empty) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Empty) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Empty) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Empty) ",
    "(fun (_ : Name) (_ : ListType Level) => Empty) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) (_ : Type) => Nat) ",
    "(fun (_ : Name) (_ : Nat) (_ : KExpr) (_ : Type) => Empty) ",
    "(fun (_ : Nat) => Empty))"
);

/// Inline discriminator: `proj` maps to `Nat`, every other head to `Empty`.
const KEXPR_IS_PROJ: &str = concat!(
    "(KExpr.rec (fun (_ : KExpr) => Type) ",
    "(fun (_ : Level) => Empty) ",
    "(fun (_ : Nat) => Empty) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Empty) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Empty) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Empty) ",
    "(fun (_ : Name) (_ : ListType Level) => Empty) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) (_ : Type) => Empty) ",
    "(fun (_ : Name) (_ : Nat) (_ : KExpr) (_ : Type) => Nat) ",
    "(fun (_ : Nat) => Empty))"
);

/// `Empty.rec` discharge of an impossible shape equation: from
/// `heq : Eq KExpr X Y` where `discr X` computes to `Nat` and `discr Y` to
/// `Empty`, conclude `goal` (any sort — `Empty.rec` is universe-flexible).
fn shape_discharge(discr: &str, x: &str, y: &str, heq: &str, goal: &str) -> String {
    format!(
        "(Empty.rec (fun (_ : Empty) => {goal}) (Eq.substType KExpr {discr} {x} {y} {heq} Nat.zero))"
    )
}

/// The raw delta-dead equation for a const head — the mirror's literal
/// `denv c = none`. This is definitionally equal to semireducible `const_whnf`;
/// the explicit field is retained as redundant constructor-shape compatibility
/// data for consumers that use the equation directly.
fn delta_dead_eq(n: &str, us: &str) -> String {
    format!(
        "Eq (OptionType KExpr) (delta_reduct (red_def the_red_env) (KExpr.const {n} {us})) (OptionType.none KExpr)"
    )
}

impl Specification {
    /// Register the Wall-A completion: the iota-aware WHNF vocabulary, the
    /// whnf_to->cd_star bridge, the const/neutral head-rigidity star-inversion
    /// family, and `def_eq_whnf_complete` itself.
    ///
    /// MUST run AFTER `add_wall_a_headmatch` (HeadMatch), `add_def_eq_joinable`
    /// (join half + I_BINDERS convention), `add_par_reduces_iota_delta` (the
    /// landed star diamond), `add_par_reduces_cd_injectivity` (sort/lam/pi
    /// star inversions) and `add_par_reduces_cd_sound` (`join_to_def_eq`).
    pub(super) fn add_wall_a_completeness(&mut self) -> Result<(), SpecError> {
        self.add_wall_a_iota_vocabulary()?;
        self.add_wall_a_shape_absurds()?;
        self.add_wall_a_whnf_to_bridge()?;
        self.add_wall_a_const_rigidity()?;
        self.add_wall_a_neutral_rigidity()?;
        self.add_wall_a_whnf_shape()?;
        self.add_wall_a_completeness_target()?;
        Ok(())
    }

    /// Brick 1: `iota_immune` / `iota_neutral` / `iota_whnf` + the
    /// subsumption anchors into the trusted surface + non-vacuity witnesses.
    fn add_wall_a_iota_vocabulary(&mut self) -> Result<(), SpecError> {
        // iota_immune e: no par_reduces_cd_star-reduct of e is a top iota
        // redex (mirror WallAIota.IotaImmune, in the directly-consumable
        // refutation form). Registered as a semireducible Definition (NOT
        // Opaque) so the kernel unfolds it when intro-ing/applying immunity
        // witnesses (#464 pattern, like terminates_whnf).
        self.add_definition_reducible(SpecDefinition {
            name: "iota_immune".to_string(),
            type_src: "KExpr -> Type".to_string(),
            value_src: Some(
                concat!(
                    "fun (e : KExpr) => forall (e2 : KExpr) (r : KExpr), ",
                    "par_reduces_cd_star the_red_env e e2 -> ",
                    "iota_step (red_rec the_red_env) e2 r -> Empty"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "iota_immune e — permanently iota-dead at the head: no par_reduces_cd_star-reduct of e ",
                "is a top iota redex (mirror WallAIota.IotaImmune, the weakest correct neutrality ",
                "strengthening over β+ι+δ+ζ). The real kernel guarantees it for its whnf results via the ",
                "major-premise whnf pre-pass; structural conditions (head without recmeta / under-applied ",
                "spine / stuck neutral major with no rule) each imply it. Semireducible definition ",
                "(unfoldable, #464 pattern). Wall-A completion."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_cd_star".to_string(),
                "iota_step".to_string(),
                "red_rec".to_string(),
                "the_red_env".to_string(),
                "Empty".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // iota_neutral: the iota-aware neutral heads (mirror WallAIota.Neutral).
        // PARALLEL predicate — the trusted is_neutral is untouched. The const
        // arm carries const_whnf (HeadMatch/is_neutral glue) AND the redundant
        // raw delta-dead equation (the mirror's `denv c = none`, usable directly
        // by the delta-refutation arms) — see the module-header compatibility note.
        self.add_inductive(
            &format!(
                concat!(
                    "inductive iota_neutral : KExpr -> Type\n",
                    "| const : forall (n : Name) (us : ListType Level), const_whnf n us -> {dd} -> ",
                    "iota_neutral (KExpr.const n us)\n",
                    "| app : forall (f : KExpr) (a : KExpr), iota_neutral f -> ",
                    "iota_immune (KExpr.app f a) -> iota_neutral (KExpr.app f a)"
                ),
                dd = delta_dead_eq("n", "us"),
            ),
            "iota_neutral e — iota-aware neutral WHNF heads (mirror WallAIota.Neutral): a const head \
             that does not delta-unfold (semireducible const_whnf plus the definitionally-equal raw \
             delta_reduct-none equation retained as compatibility data), or an application spine of a neutral head \
             with the spine node permanently iota-dead (iota_immune). PARALLEL predicate: the trusted \
             is_neutral (delta-only) is untouched; iota_neutral_subsumes_is_neutral anchors it. \
             Wall-A completion.",
        )?;

        // iota_whnf: the iota-aware bounded WHNF predicate (mirror WallAIota.Whnf).
        self.add_inductive(
            concat!(
                "inductive iota_whnf : KExpr -> Type\n",
                "| sort : forall (n : Level), iota_whnf (KExpr.sort n)\n",
                "| lam : forall (ty : KExpr) (body : KExpr), iota_whnf (KExpr.lam ty body)\n",
                "| pi : forall (dom : KExpr) (body : KExpr), iota_whnf (KExpr.pi dom body)\n",
                "| neutral : forall (e : KExpr), iota_neutral e -> iota_whnf e"
            ),
            "iota_whnf e — iota-aware bounded WHNF (mirror WallAIota.Whnf): sort/lam/pi or an \
             iota-neutral spine. PARALLEL predicate over the untouched trusted is_whnf; \
             def_eq_whnf_complete's strengthened whnf-target hypothesis. Faithful to the real \
             kernel's whnf results (major pre-pass). Wall-A completion.",
        )?;

        // Subsumption anchor: iota-aware neutrality implies the trusted
        // delta-only neutrality (drop the immunity/equation fields).
        self.add_definition(SpecDefinition {
            name: "iota_neutral_subsumes_is_neutral".to_string(),
            type_src: "forall (e : KExpr), iota_neutral e -> is_neutral e".to_string(),
            value_src: Some(format!(
                concat!(
                    "fun (e : KExpr) (h : iota_neutral e) => ",
                    "iota_neutral.rec ",
                    "(fun (x : KExpr) (_h : iota_neutral x) => is_neutral x) ",
                    "(fun (n : Name) (us : ListType Level) (hw : const_whnf n us) (_hnd : {dd}) => ",
                    "is_neutral.const n us hw) ",
                    "(fun (f : KExpr) (a : KExpr) (_hf : iota_neutral f) ",
                    "(_him : iota_immune (KExpr.app f a)) (ihf : is_neutral f) => ",
                    "is_neutral.app f a ihf) ",
                    "e h"
                ),
                dd = delta_dead_eq("n", "us"),
            )),
            is_axiom: false,
            description: concat!(
                "Subsumption anchor: iota_neutral e -> is_neutral e (the iota-aware neutrality is a ",
                "strengthening of the trusted delta-only is_neutral; drop the immunity/raw-equation ",
                "fields). DerivedProved via iota_neutral.rec, zero axiom_deps. Wall-A completion."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "iota_neutral".to_string(),
                "iota_neutral.rec".to_string(),
                "is_neutral".to_string(),
                "const_whnf".to_string(),
                "iota_immune".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "iota_whnf_subsumes_is_whnf".to_string(),
            type_src: "forall (e : KExpr), iota_whnf e -> is_whnf e".to_string(),
            value_src: Some(
                concat!(
                    "fun (e : KExpr) (h : iota_whnf e) => ",
                    "iota_whnf.rec ",
                    "(fun (x : KExpr) (_h : iota_whnf x) => is_whnf x) ",
                    "(fun (n : Level) => is_whnf.sort n) ",
                    "(fun (ty : KExpr) (body : KExpr) => is_whnf.lam ty body) ",
                    "(fun (dom : KExpr) (body : KExpr) => is_whnf.pi dom body) ",
                    "(fun (x : KExpr) (hn : iota_neutral x) => ",
                    "is_whnf.neutral x (iota_neutral_subsumes_is_neutral x hn)) ",
                    "e h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Subsumption anchor: iota_whnf e -> is_whnf e (the iota-aware WHNF predicate is a ",
                "strengthening of the trusted is_whnf). DerivedProved via iota_whnf.rec + ",
                "iota_neutral_subsumes_is_neutral, zero axiom_deps. Wall-A completion."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "iota_whnf".to_string(),
                "iota_whnf.rec".to_string(),
                "is_whnf".to_string(),
                "iota_neutral_subsumes_is_neutral".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // Non-vacuity witness (Guard 4): iota_immune holds at a sort head —
        // every star-reduct of Sort 0 is Sort 0 (star sort rigidity) and a
        // sort never top-iota-fires (head const name = none).
        self.add_definition(SpecDefinition {
            name: "iota_immune_sort_witness".to_string(),
            type_src: "iota_immune (KExpr.sort Level.zero)".to_string(),
            value_src: Some(
                concat!(
                    "fun (e2 : KExpr) (r : KExpr) ",
                    "(hstar : par_reduces_cd_star the_red_env (KExpr.sort Level.zero) e2) ",
                    "(hfire : iota_step (red_rec the_red_env) e2 r) => ",
                    "iota_step_head_none_absurd_type (red_rec the_red_env) (KExpr.sort Level.zero) r Empty ",
                    "(Eq.refl (OptionType Name) (OptionType.none Name)) ",
                    "(Eq.substType KExpr (fun (x : KExpr) => iota_step (red_rec the_red_env) x r) ",
                    "e2 (KExpr.sort Level.zero) ",
                    "(par_reduces_cd_star_sort_inv_eq the_red_env Level.zero e2 hstar) hfire)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Non-vacuity witness (Guard 4): iota_immune (sort 0). Every cd_star-reduct of a sort ",
                "is the sort itself (par_reduces_cd_star_sort_inv_eq) and a sort-headed term never ",
                "top-iota-fires (iota_step_head_none_absurd_type; head const name none by Eq.refl). ",
                "DerivedProved, zero axiom_deps. Wall-A completion."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "iota_immune".to_string(),
                "par_reduces_cd_star".to_string(),
                "iota_step".to_string(),
                "iota_step_head_none_absurd_type".to_string(),
                "par_reduces_cd_star_sort_inv_eq".to_string(),
                "Eq.substType".to_string(),
                "Eq.refl".to_string(),
                "the_red_env".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // Non-vacuity witness (Guard 4): iota_whnf at a sort head.
        self.add_definition(SpecDefinition {
            name: "iota_whnf_sort_witness".to_string(),
            type_src: "iota_whnf (KExpr.sort Level.zero)".to_string(),
            value_src: Some("iota_whnf.sort Level.zero".to_string()),
            is_axiom: false,
            description: concat!(
                "Non-vacuity witness (Guard 4): iota_whnf holds at a sort head. A concrete ",
                "iota_neutral const witness is also constructible exactly when the kernel computes ",
                "delta_reduct (red_def the_red_env) for that const to none; semireducible const_whnf ",
                "then unfolds to the carried raw equation. A delta-reducing const cannot supply either ",
                "field and fails closed. DerivedProved, zero ",
                "axiom_deps. Wall-A completion."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from(["iota_whnf".to_string()])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    /// Brick 2: shape-discrimination absurds for `iota_neutral` at non-spine
    /// heads (mirror: `Neutral` inversion refutations). Prop and Type variants
    /// where consumed (the kernel is non-cumulative).
    fn add_wall_a_shape_absurds(&mut self) -> Result<(), SpecError> {
        // Shared proof-body generator: iota_neutral.rec with the index-equation
        // motive `Eq x TARGET -> C`; the const arm discriminates const-vs-TARGET,
        // the app arm app-vs-TARGET, both via inline KExpr.rec discriminators +
        // Empty.rec (universe-flexible, so one generator serves the Prop and
        // Type variants identically — only the declared C sort differs).
        let absurd_proof = |target: &str| -> String {
            format!(
                concat!(
                    "iota_neutral.rec ",
                    "(fun (x : KExpr) (_h : iota_neutral x) => Eq KExpr x {target} -> C) ",
                    "(fun (m : Name) (vs : ListType Level) (_hw : const_whnf m vs) (_hnd : {dd}) ",
                    "(heq : Eq KExpr (KExpr.const m vs) {target}) => {const_discharge}) ",
                    "(fun (f : KExpr) (a : KExpr) (_hf : iota_neutral f) ",
                    "(_him : iota_immune (KExpr.app f a)) (_ih : Eq KExpr f {target} -> C) ",
                    "(heq : Eq KExpr (KExpr.app f a) {target}) => {app_discharge}) ",
                    "{target} h (Eq.refl KExpr {target})"
                ),
                target = target,
                dd = delta_dead_eq("m", "vs"),
                const_discharge =
                    shape_discharge(KEXPR_IS_CONST, "(KExpr.const m vs)", target, "heq", "C"),
                app_discharge =
                    shape_discharge(KEXPR_IS_APP, "(KExpr.app f a)", target, "heq", "C"),
            )
        };

        for (name, binders, target, c_sort) in [
            (
                "iota_neutral_sort_absurd",
                "(n : Level)",
                "(KExpr.sort n)",
                "Prop",
            ),
            (
                "iota_neutral_sort_absurd_type",
                "(n : Level)",
                "(KExpr.sort n)",
                "Type",
            ),
            (
                "iota_neutral_lam_absurd_type",
                "(ty : KExpr) (body : KExpr)",
                "(KExpr.lam ty body)",
                "Type",
            ),
            (
                "iota_neutral_pi_absurd_type",
                "(dom : KExpr) (body : KExpr)",
                "(KExpr.pi dom body)",
                "Type",
            ),
        ] {
            self.add_definition(SpecDefinition {
                name: name.to_string(),
                type_src: format!(
                    "forall {binders} (C : {c_sort}), iota_neutral {target} -> C"
                ),
                value_src: Some(format!(
                    "fun {binders} (C : {c_sort}) (h : iota_neutral {target}) => {body}",
                    binders = binders,
                    c_sort = c_sort,
                    target = target,
                    body = absurd_proof(target),
                )),
                is_axiom: false,
                description: format!(
                    concat!(
                        "Shape discrimination: iota_neutral never holds at {target} (its ctors index only ",
                        "const/app heads). iota_neutral.rec with an index-equation motive; both arms ",
                        "discharge via an inline KExpr.rec discriminator + Empty.rec into C : {c}. Mirror of ",
                        "the WallAIota Neutral-inversion refutations. DerivedProved, zero axiom_deps. ",
                        "Wall-A completion."
                    ),
                    target = target,
                    c = c_sort,
                ),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "iota_neutral".to_string(),
                    "iota_neutral.rec".to_string(),
                    "KExpr.rec".to_string(),
                    "Empty".to_string(),
                    "Empty.rec".to_string(),
                    "Eq.substType".to_string(),
                    "Eq.refl".to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }

        Ok(())
    }

    /// Brick 3: the operational->confluence-lane bridge. `whnf_to` legs (the
    /// kernel's SN/termination oracle vocabulary) inject into
    /// `par_reduces_cd_star the_red_env` — no such bridge existed in-tree.
    fn add_wall_a_whnf_to_bridge(&mut self) -> Result<(), SpecError> {
        // beta_reduces -> cd_star: structural beta_reduces.rec; every arm maps
        // to the matching cd_star congruence / single cd step. The zeta arm
        // fires the single cd let_ (zeta) contraction; the let_ty/let_val/
        // let_body positional congruences ride one-sided cd_star inductions
        // over par_reduces_cd.let_cong; the iota arm reverse-bridges the
        // tightened family (iota_reduces_to_step) into par_reduces_cd.iota.
        self.add_definition(SpecDefinition {
            name: "beta_reduces_to_cd_star".to_string(),
            type_src: concat!(
                "forall (e : KExpr) (e2 : KExpr), beta_reduces e e2 -> ",
                "par_reduces_cd_star the_red_env e e2"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (e : KExpr) (e2 : KExpr) (h : beta_reduces e e2) => ",
                    "beta_reduces.rec ",
                    "(fun (x : KExpr) (y : KExpr) (_h : beta_reduces x y) => par_reduces_cd_star the_red_env x y) ",
                    // beta
                    "(fun (A : KExpr) (body : KExpr) (arg : KExpr) => ",
                    "par_subsumes_par_cd_star the_red_env (KExpr.app (KExpr.lam A body) arg) (instantiate body arg) ",
                    "(par_reduces_cd.beta the_red_env A A body body arg arg ",
                    "(par_reduces_cd.refl the_red_env A) (par_reduces_cd.refl the_red_env body) ",
                    "(par_reduces_cd.refl the_red_env arg))) ",
                    // app_left
                    "(fun (f : KExpr) (f2 : KExpr) (a : KExpr) (_hf : beta_reduces f f2) ",
                    "(ih : par_reduces_cd_star the_red_env f f2) => ",
                    "par_reduces_cd_star_app the_red_env f f2 a a ih (par_reduces_cd_star.refl the_red_env a)) ",
                    // app_right
                    "(fun (f : KExpr) (a : KExpr) (a2 : KExpr) (_ha : beta_reduces a a2) ",
                    "(ih : par_reduces_cd_star the_red_env a a2) => ",
                    "par_reduces_cd_star_app the_red_env f f a a2 (par_reduces_cd_star.refl the_red_env f) ih) ",
                    // lam_ty
                    "(fun (ty : KExpr) (ty2 : KExpr) (body : KExpr) (_hty : beta_reduces ty ty2) ",
                    "(ih : par_reduces_cd_star the_red_env ty ty2) => ",
                    "par_reduces_cd_star_lam the_red_env ty ty2 body body ih (par_reduces_cd_star.refl the_red_env body)) ",
                    // lam_body
                    "(fun (ty : KExpr) (body : KExpr) (body2 : KExpr) (_hb : beta_reduces body body2) ",
                    "(ih : par_reduces_cd_star the_red_env body body2) => ",
                    "par_reduces_cd_star_lam the_red_env ty ty body body2 (par_reduces_cd_star.refl the_red_env ty) ih) ",
                    // pi_dom
                    "(fun (dom : KExpr) (dom2 : KExpr) (body : KExpr) (_hd : beta_reduces dom dom2) ",
                    "(ih : par_reduces_cd_star the_red_env dom dom2) => ",
                    "par_reduces_cd_star_pi the_red_env dom dom2 body body ih (par_reduces_cd_star.refl the_red_env body)) ",
                    // pi_cod
                    "(fun (dom : KExpr) (body : KExpr) (body2 : KExpr) (_hb : beta_reduces body body2) ",
                    "(ih : par_reduces_cd_star the_red_env body body2) => ",
                    "par_reduces_cd_star_pi the_red_env dom dom body body2 (par_reduces_cd_star.refl the_red_env dom) ih) ",
                    // forall_congr_dom
                    "(fun (dom : KExpr) (dom2 : KExpr) (body : KExpr) (_hd : beta_reduces dom dom2) ",
                    "(ih : par_reduces_cd_star the_red_env dom dom2) => ",
                    "par_reduces_cd_star_forall the_red_env dom dom2 body body ih (par_reduces_cd_star.refl the_red_env body)) ",
                    // forall_congr_cod
                    "(fun (dom : KExpr) (body : KExpr) (body2 : KExpr) (_hb : beta_reduces body body2) ",
                    "(ih : par_reduces_cd_star the_red_env body body2) => ",
                    "par_reduces_cd_star_forall the_red_env dom dom body body2 (par_reduces_cd_star.refl the_red_env dom) ih) ",
                    // zeta (top-level let unfolding): one cd let_ (zeta) step to
                    // instantiate body val, embedded via par_subsumes_par_cd_star.
                    "(fun (ty : KExpr) (val : KExpr) (body : KExpr) => ",
                    "par_subsumes_par_cd_star the_red_env (KExpr.let_ ty val body) (instantiate body val) ",
                    "(par_reduces_cd.let_ the_red_env ty ty val val body body ",
                    "(par_reduces_cd.refl the_red_env ty) (par_reduces_cd.refl the_red_env val) ",
                    "(par_reduces_cd.refl the_red_env body))) ",
                    // let_ty congruence: one-sided cd_star induction in the ty
                    // position, lifting each step via par_reduces_cd.let_cong with
                    // reflexive val/body companions.
                    "(fun (ty : KExpr) (ty2 : KExpr) (val : KExpr) (body : KExpr) ",
                    "(_hty : beta_reduces ty ty2) (ih : par_reduces_cd_star the_red_env ty ty2) => ",
                    "par_reduces_cd_star.rec the_red_env ",
                    "(fun (x : KExpr) (y : KExpr) (_ : par_reduces_cd_star the_red_env x y) => ",
                    "par_reduces_cd_star the_red_env (KExpr.let_ x val body) (KExpr.let_ y val body)) ",
                    "(fun (x : KExpr) => par_reduces_cd_star.refl the_red_env (KExpr.let_ x val body)) ",
                    "(fun (x : KExpr) (x2 : KExpr) (x3 : KExpr) ",
                    "(hstep : par_reduces_cd the_red_env x x2) (_htail : par_reduces_cd_star the_red_env x2 x3) ",
                    "(ih2 : par_reduces_cd_star the_red_env (KExpr.let_ x2 val body) (KExpr.let_ x3 val body)) => ",
                    "par_reduces_cd_star.step the_red_env (KExpr.let_ x val body) (KExpr.let_ x2 val body) (KExpr.let_ x3 val body) ",
                    "(par_reduces_cd.let_cong the_red_env x x2 val val body body hstep ",
                    "(par_reduces_cd.refl the_red_env val) (par_reduces_cd.refl the_red_env body)) ih2) ",
                    "ty ty2 ih) ",
                    // let_val congruence: one-sided cd_star induction in the val
                    // position.
                    "(fun (ty : KExpr) (val : KExpr) (val2 : KExpr) (body : KExpr) ",
                    "(_hv : beta_reduces val val2) (ih : par_reduces_cd_star the_red_env val val2) => ",
                    "par_reduces_cd_star.rec the_red_env ",
                    "(fun (x : KExpr) (y : KExpr) (_ : par_reduces_cd_star the_red_env x y) => ",
                    "par_reduces_cd_star the_red_env (KExpr.let_ ty x body) (KExpr.let_ ty y body)) ",
                    "(fun (x : KExpr) => par_reduces_cd_star.refl the_red_env (KExpr.let_ ty x body)) ",
                    "(fun (x : KExpr) (x2 : KExpr) (x3 : KExpr) ",
                    "(hstep : par_reduces_cd the_red_env x x2) (_htail : par_reduces_cd_star the_red_env x2 x3) ",
                    "(ih2 : par_reduces_cd_star the_red_env (KExpr.let_ ty x2 body) (KExpr.let_ ty x3 body)) => ",
                    "par_reduces_cd_star.step the_red_env (KExpr.let_ ty x body) (KExpr.let_ ty x2 body) (KExpr.let_ ty x3 body) ",
                    "(par_reduces_cd.let_cong the_red_env ty ty x x2 body body ",
                    "(par_reduces_cd.refl the_red_env ty) hstep (par_reduces_cd.refl the_red_env body)) ih2) ",
                    "val val2 ih) ",
                    // let_body congruence: one-sided cd_star induction in the body
                    // position.
                    "(fun (ty : KExpr) (val : KExpr) (body : KExpr) (body2 : KExpr) ",
                    "(_hb : beta_reduces body body2) (ih : par_reduces_cd_star the_red_env body body2) => ",
                    "par_reduces_cd_star.rec the_red_env ",
                    "(fun (x : KExpr) (y : KExpr) (_ : par_reduces_cd_star the_red_env x y) => ",
                    "par_reduces_cd_star the_red_env (KExpr.let_ ty val x) (KExpr.let_ ty val y)) ",
                    "(fun (x : KExpr) => par_reduces_cd_star.refl the_red_env (KExpr.let_ ty val x)) ",
                    "(fun (x : KExpr) (x2 : KExpr) (x3 : KExpr) ",
                    "(hstep : par_reduces_cd the_red_env x x2) (_htail : par_reduces_cd_star the_red_env x2 x3) ",
                    "(ih2 : par_reduces_cd_star the_red_env (KExpr.let_ ty val x2) (KExpr.let_ ty val x3)) => ",
                    "par_reduces_cd_star.step the_red_env (KExpr.let_ ty val x) (KExpr.let_ ty val x2) (KExpr.let_ ty val x3) ",
                    "(par_reduces_cd.let_cong the_red_env ty ty val val x x2 ",
                    "(par_reduces_cd.refl the_red_env ty) (par_reduces_cd.refl the_red_env val) hstep) ih2) ",
                    "body body2 ih) ",
                    // iota
                    "(fun (x : KExpr) (y : KExpr) (hi : iota_reduces x y) => ",
                    "par_subsumes_par_cd_star the_red_env x y ",
                    "(par_reduces_cd.iota the_red_env x y (iota_reduces_to_step x y hi))) ",
                    // proj: positional congruence lifted through the cd_star chain.
                    "(fun (s : Name) (i : Nat) (sub : KExpr) (sub2 : KExpr) (_hs : beta_reduces sub sub2) ",
                    "(ih : par_reduces_cd_star the_red_env sub sub2) => ",
                    "par_reduces_cd_star_proj the_red_env s i sub sub2 ih) ",
                    "e e2 h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Operational->confluence-lane bridge: every single beta_reduces step (incl. the folded ",
                "iota arm, the forall_ alias congruences, and the genuine-let_ zeta/let_ty/let_val/",
                "let_body arms) embeds into par_reduces_cd_star the_red_env. Structural ",
                "beta_reduces.rec over the cd_star congruences (app/lam/pi/forall; the three let ",
                "positions via one-sided star inductions over par_reduces_cd.let_cong) + the single cd ",
                "beta/let_(zeta)/iota steps (iota via iota_reduces_to_step). No such injection existed ",
                "in-tree. DerivedProved, zero axiom_deps. Wall-A completion."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "beta_reduces".to_string(),
                "beta_reduces.rec".to_string(),
                "par_reduces_cd".to_string(),
                "par_reduces_cd.refl".to_string(),
                "par_reduces_cd.beta".to_string(),
                "par_reduces_cd.let_".to_string(),
                "par_reduces_cd.let_cong".to_string(),
                "par_reduces_cd.iota".to_string(),
                "par_reduces_cd_star".to_string(),
                "par_reduces_cd_star.refl".to_string(),
                "par_reduces_cd_star.step".to_string(),
                "par_reduces_cd_star.rec".to_string(),
                "par_reduces_cd_star_app".to_string(),
                "par_reduces_cd_star_lam".to_string(),
                "par_reduces_cd_star_pi".to_string(),
                "par_reduces_cd_star_forall".to_string(),
                "par_reduces_cd_star_proj".to_string(),
                "par_subsumes_par_cd_star".to_string(),
                "iota_reduces_to_step".to_string(),
                "instantiate".to_string(),
                "the_red_env".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // Semireducible motive alias for the whnf_step dispatcher — the
        // kernel-generated whnf_step.rec is indices-first and the motive must
        // be a NAMED reducible constant (the whnf_step_preserves_def_eq /
        // subject_reduction_ctx pattern).
        self.add_definition_reducible(SpecDefinition {
            name: "whnf_step_cd_star_goal".to_string(),
            type_src: "forall (e : KExpr) (e2 : KExpr), whnf_step e e2 -> Type".to_string(),
            value_src: Some(
                concat!(
                    "fun (e : KExpr) (e2 : KExpr) (_h : whnf_step e e2) => ",
                    "par_reduces_cd_star the_red_env e e2"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "Semireducible motive alias for the whnf_step->cd_star bridge \
                          (whnf_step.rec is indices-first; the motive must be a named reducible \
                          constant). Wall-A completion."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "whnf_step".to_string(),
                "par_reduces_cd_star".to_string(),
                "the_red_env".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // whnf_step -> cd_star: beta leg via the bridge above, delta leg via
        // the reverse bridge into the single cd delta step. Structural
        // registration (the recursor-motive false-negative bypass, exactly as
        // whnf_step_preserves_def_eq).
        self.add_definition_structural(SpecDefinition {
            name: "whnf_step_to_cd_star".to_string(),
            type_src: concat!(
                "forall (e : KExpr) (e2 : KExpr), whnf_step e e2 -> ",
                "par_reduces_cd_star the_red_env e e2"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (e : KExpr) (e2 : KExpr) (h : whnf_step e e2) => ",
                    "whnf_step.rec e e2 ",
                    "(whnf_step_cd_star_goal e e2) ",
                    "(fun (hb : beta_reduces e e2) => beta_reduces_to_cd_star e e2 hb) ",
                    "(fun (hd : delta_reduces e e2) => ",
                    "par_subsumes_par_cd_star the_red_env e e2 ",
                    "(par_reduces_cd.delta the_red_env e e2 (delta_reduces_to_step e e2 hd))) ",
                    "h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Operational->confluence-lane bridge: a single whnf_step embeds into ",
                "par_reduces_cd_star the_red_env (beta leg via beta_reduces_to_cd_star, delta leg via ",
                "delta_reduces_to_step + par_reduces_cd.delta; whnf_step.rec is indices-first with the ",
                "named semireducible motive whnf_step_cd_star_goal). DerivedProved, zero axiom_deps. ",
                "Wall-A completion."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "whnf_step".to_string(),
                "whnf_step.rec".to_string(),
                "whnf_step_cd_star_goal".to_string(),
                "beta_reduces_to_cd_star".to_string(),
                "delta_reduces_to_step".to_string(),
                "par_reduces_cd.delta".to_string(),
                "par_subsumes_par_cd_star".to_string(),
                "the_red_env".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // Semireducible motive alias for the whnf_to induction (same
        // recursor-motive pattern as whnf_to_def_eq_goal).
        self.add_definition_reducible(SpecDefinition {
            name: "whnf_to_cd_star_goal".to_string(),
            type_src: "forall (e : KExpr) (v : KExpr), whnf_to e v -> Type".to_string(),
            value_src: Some(
                concat!(
                    "fun (e : KExpr) (v : KExpr) (_h : whnf_to e v) => ",
                    "par_reduces_cd_star the_red_env e v"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "Semireducible motive alias for the whnf_to->cd_star bridge (keeps the \
                          recursor result reducible to par_reduces_cd_star during declaration \
                          checking). Wall-A completion."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "whnf_to".to_string(),
                "par_reduces_cd_star".to_string(),
                "the_red_env".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // whnf_to -> cd_star: fold the trace through cd_star transitivity.
        self.add_definition_structural(SpecDefinition {
            name: "whnf_to_cd_star".to_string(),
            type_src: concat!(
                "forall (e : KExpr) (v : KExpr), whnf_to e v -> ",
                "par_reduces_cd_star the_red_env e v"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (e : KExpr) (v : KExpr) (h : whnf_to e v) => ",
                    "whnf_to.rec ",
                    "whnf_to_cd_star_goal ",
                    "(fun (e0 : KExpr) (_hw : is_whnf e0) => par_reduces_cd_star.refl the_red_env e0) ",
                    "(fun (e0 : KExpr) (e1 : KExpr) (v0 : KExpr) (hs : whnf_step e0 e1) ",
                    "(hrest : whnf_to e1 v0) ",
                    "(ih : whnf_to_cd_star_goal e1 v0 hrest) => ",
                    "par_reduces_cd_star_trans the_red_env e0 e1 v0 (whnf_step_to_cd_star e0 e1 hs) ih) ",
                    "e v h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Operational->confluence-lane bridge: a whole whnf_to trace (the kernel's ",
                "SN/termination oracle leg) embeds into par_reduces_cd_star the_red_env, by folding ",
                "whnf_step_to_cd_star through par_reduces_cd_star_trans (whnf_to.rec with the named ",
                "semireducible motive whnf_to_cd_star_goal). Mirror of WallAIota.whnfTo_star. ",
                "DerivedProved, zero axiom_deps. Wall-A completion."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "whnf_to".to_string(),
                "whnf_to.rec".to_string(),
                "whnf_to_cd_star_goal".to_string(),
                "whnf_step_to_cd_star".to_string(),
                "par_reduces_cd_star.refl".to_string(),
                "par_reduces_cd_star_trans".to_string(),
                "is_whnf".to_string(),
                "the_red_env".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    /// Brick 4: dead-const rigidity — a const head that neither delta-unfolds
    /// (raw equation) nor iota-fires (bare const, `iota_reduct_const_none`) is
    /// rigid under `par_reduces_cd` and its star (mirror
    /// `step_const_none_absurd` / `star_const_none_eq`).
    fn add_wall_a_const_rigidity(&mut self) -> Result<(), SpecError> {
        let goal = |reduct: &str| format!("Eq KExpr {reduct} (KExpr.const n us)");
        // Structural (non-const-headed source) arm discharge into the Prop goal.
        let mk_struct_arm = |binders: &str, hyps: &str, discr: &str, source: &str, reduct: &str| {
            format!(
                "(fun {binders} {hyps} (heq : Eq KExpr {source} (KExpr.const n us)) => {discharge}) ",
                binders = binders,
                hyps = hyps,
                discharge = shape_discharge(discr, source, "(KExpr.const n us)", "heq", &goal(reduct)),
            )
        };

        let motive = concat!(
            "(fun (x : KExpr) (y : KExpr) (_h : par_reduces_cd the_red_env x y) => ",
            "Eq KExpr x (KExpr.const n us) -> Eq KExpr y (KExpr.const n us))"
        );
        let refl_arm = "(fun (x : KExpr) (heq : Eq KExpr x (KExpr.const n us)) => heq) ";
        let beta_arm = mk_struct_arm(
            "(A : KExpr) (A2 : KExpr) (b0 : KExpr) (b02 : KExpr) (arg : KExpr) (arg2 : KExpr)",
            concat!(
                "(_hA : par_reduces_cd the_red_env A A2) (_hb0 : par_reduces_cd the_red_env b0 b02) ",
                "(_harg : par_reduces_cd the_red_env arg arg2) ",
                "(_ihA : Eq KExpr A (KExpr.const n us) -> Eq KExpr A2 (KExpr.const n us)) ",
                "(_ihb0 : Eq KExpr b0 (KExpr.const n us) -> Eq KExpr b02 (KExpr.const n us)) ",
                "(_iharg : Eq KExpr arg (KExpr.const n us) -> Eq KExpr arg2 (KExpr.const n us))"
            ),
            KEXPR_IS_APP,
            "(KExpr.app (KExpr.lam A b0) arg)",
            "(instantiate b02 arg2)",
        );
        let app_arm = mk_struct_arm(
            "(g : KExpr) (g2 : KExpr) (b : KExpr) (b2 : KExpr)",
            concat!(
                "(_hg : par_reduces_cd the_red_env g g2) (_hb : par_reduces_cd the_red_env b b2) ",
                "(_ihg : Eq KExpr g (KExpr.const n us) -> Eq KExpr g2 (KExpr.const n us)) ",
                "(_ihb : Eq KExpr b (KExpr.const n us) -> Eq KExpr b2 (KExpr.const n us))"
            ),
            KEXPR_IS_APP,
            "(KExpr.app g b)",
            "(KExpr.app g2 b2)",
        );
        let lam_arm = mk_struct_arm(
            "(t0 : KExpr) (t02 : KExpr) (b0 : KExpr) (b02 : KExpr)",
            concat!(
                "(_ht : par_reduces_cd the_red_env t0 t02) (_hb : par_reduces_cd the_red_env b0 b02) ",
                "(_iht : Eq KExpr t0 (KExpr.const n us) -> Eq KExpr t02 (KExpr.const n us)) ",
                "(_ihb : Eq KExpr b0 (KExpr.const n us) -> Eq KExpr b02 (KExpr.const n us))"
            ),
            KEXPR_IS_LAM,
            "(KExpr.lam t0 b0)",
            "(KExpr.lam t02 b02)",
        );
        let pi_arm = mk_struct_arm(
            "(d0 : KExpr) (d02 : KExpr) (b0 : KExpr) (b02 : KExpr)",
            concat!(
                "(_hd : par_reduces_cd the_red_env d0 d02) (_hb : par_reduces_cd the_red_env b0 b02) ",
                "(_ihd : Eq KExpr d0 (KExpr.const n us) -> Eq KExpr d02 (KExpr.const n us)) ",
                "(_ihb : Eq KExpr b0 (KExpr.const n us) -> Eq KExpr b02 (KExpr.const n us))"
            ),
            KEXPR_IS_PI,
            "(KExpr.pi d0 b0)",
            "(KExpr.pi d02 b02)",
        );
        let forall_arm = mk_struct_arm(
            "(d0 : KExpr) (d02 : KExpr) (b0 : KExpr) (b02 : KExpr)",
            concat!(
                "(_hd : par_reduces_cd the_red_env d0 d02) (_hb : par_reduces_cd the_red_env b0 b02) ",
                "(_ihd : Eq KExpr d0 (KExpr.const n us) -> Eq KExpr d02 (KExpr.const n us)) ",
                "(_ihb : Eq KExpr b0 (KExpr.const n us) -> Eq KExpr b02 (KExpr.const n us))"
            ),
            KEXPR_IS_PI,
            "(KExpr.forall_ d0 b0)",
            "(KExpr.forall_ d02 b02)",
        );
        let let_arm = mk_struct_arm(
            "(t0 : KExpr) (t02 : KExpr) (v0 : KExpr) (v02 : KExpr) (b0 : KExpr) (b02 : KExpr)",
            concat!(
                "(_ht : par_reduces_cd the_red_env t0 t02) (_hv : par_reduces_cd the_red_env v0 v02) ",
                "(_hb : par_reduces_cd the_red_env b0 b02) ",
                "(_iht : Eq KExpr t0 (KExpr.const n us) -> Eq KExpr t02 (KExpr.const n us)) ",
                "(_ihv : Eq KExpr v0 (KExpr.const n us) -> Eq KExpr v02 (KExpr.const n us)) ",
                "(_ihb : Eq KExpr b0 (KExpr.const n us) -> Eq KExpr b02 (KExpr.const n us))"
            ),
            KEXPR_IS_LET,
            "(KExpr.let_ t0 v0 b0)",
            "(instantiate b02 v02)",
        );
        // Trailing let_cong minor (positional congruence over a genuine let_
        // node): same let_-headed source, let_-shaped reduct.
        let let_cong_arm = mk_struct_arm(
            "(t0 : KExpr) (t02 : KExpr) (v0 : KExpr) (v02 : KExpr) (b0 : KExpr) (b02 : KExpr)",
            concat!(
                "(_ht : par_reduces_cd the_red_env t0 t02) (_hv : par_reduces_cd the_red_env v0 v02) ",
                "(_hb : par_reduces_cd the_red_env b0 b02) ",
                "(_iht : Eq KExpr t0 (KExpr.const n us) -> Eq KExpr t02 (KExpr.const n us)) ",
                "(_ihv : Eq KExpr v0 (KExpr.const n us) -> Eq KExpr v02 (KExpr.const n us)) ",
                "(_ihb : Eq KExpr b0 (KExpr.const n us) -> Eq KExpr b02 (KExpr.const n us))"
            ),
            KEXPR_IS_LET,
            "(KExpr.let_ t0 v0 b0)",
            "(KExpr.let_ t02 v02 b02)",
        );
        // iota arm: transport the fire onto the const head; a BARE const never
        // fires (iota_reduct_const_none), so some = none is absurd.
        let iota_arm = concat!(
            "(fun (x0 : KExpr) (y0 : KExpr) (hi : iota_step (red_rec the_red_env) x0 y0) ",
            "(heq : Eq KExpr x0 (KExpr.const n us)) => ",
            "option_none_ne_some KExpr y0 (Eq KExpr y0 (KExpr.const n us)) ",
            "(Eq.trans (OptionType KExpr) (OptionType.none KExpr) ",
            "(iota_reduct (red_rec the_red_env) (KExpr.const n us)) (OptionType.some KExpr y0) ",
            "(Eq.symm (OptionType KExpr) (iota_reduct (red_rec the_red_env) (KExpr.const n us)) ",
            "(OptionType.none KExpr) (iota_reduct_const_none (red_rec the_red_env) n us)) ",
            "(Eq.substType KExpr (fun (z : KExpr) => iota_step (red_rec the_red_env) z y0) ",
            "x0 (KExpr.const n us) heq hi))) "
        );
        // delta arm: transport the unfold onto the const head; the carried raw
        // delta-dead equation makes some = none absurd.
        let delta_arm = concat!(
            "(fun (x0 : KExpr) (y0 : KExpr) (hd : delta_step (red_def the_red_env) x0 y0) ",
            "(heq : Eq KExpr x0 (KExpr.const n us)) => ",
            "option_none_ne_some KExpr y0 (Eq KExpr y0 (KExpr.const n us)) ",
            "(Eq.trans (OptionType KExpr) (OptionType.none KExpr) ",
            "(delta_reduct (red_def the_red_env) (KExpr.const n us)) (OptionType.some KExpr y0) ",
            "(Eq.symm (OptionType KExpr) (delta_reduct (red_def the_red_env) (KExpr.const n us)) ",
            "(OptionType.none KExpr) hnd) ",
            "(Eq.substType KExpr (fun (z : KExpr) => delta_step (red_def the_red_env) z y0) ",
            "x0 (KExpr.const n us) heq hd)))"
        );
        // proj arm (trailing 11th ctor): a proj-headed source is never const, so
        // the source equation is absurd — same shape-discharge as let_/app/lam/pi.
        let proj_arm = mk_struct_arm(
            "(s : Name) (i : Nat) (sub0 : KExpr) (sub02 : KExpr)",
            concat!(
                "(_hsub : par_reduces_cd the_red_env sub0 sub02) ",
                "(_ihsub : Eq KExpr sub0 (KExpr.const n us) -> Eq KExpr sub02 (KExpr.const n us))"
            ),
            KEXPR_IS_PROJ,
            "(KExpr.proj s i sub0)",
            "(KExpr.proj s i sub02)",
        );

        self.add_definition(SpecDefinition {
            name: "par_reduces_cd_const_dead_inv_eq".to_string(),
            type_src: format!(
                concat!(
                    "forall (n : Name) (us : ListType Level) (t : KExpr), {dd} -> ",
                    "par_reduces_cd the_red_env (KExpr.const n us) t -> Eq KExpr t (KExpr.const n us)"
                ),
                dd = delta_dead_eq("n", "us"),
            ),
            value_src: Some(format!(
                concat!(
                    "fun (n : Name) (us : ListType Level) (t : KExpr) (hnd : {dd}) ",
                    "(h : par_reduces_cd the_red_env (KExpr.const n us) t) => ",
                    "par_reduces_cd.rec the_red_env {motive} ",
                    "{refl_arm}{beta_arm}{app_arm}{lam_arm}{pi_arm}{forall_arm}{let_arm}{iota_arm}{delta_arm} {let_cong_arm}{proj_arm}",
                    "(KExpr.const n us) t h (Eq.refl KExpr (KExpr.const n us))"
                ),
                dd = delta_dead_eq("n", "us"),
                motive = motive,
                refl_arm = refl_arm,
                beta_arm = beta_arm,
                app_arm = app_arm,
                lam_arm = lam_arm,
                pi_arm = pi_arm,
                forall_arm = forall_arm,
                let_arm = let_arm,
                iota_arm = iota_arm,
                delta_arm = delta_arm,
                let_cong_arm = let_cong_arm,
                proj_arm = proj_arm,
            )),
            is_axiom: false,
            description: concat!(
                "Single-step dead-const rigidity (mirror WallAIota.step_const_none_absurd): a ",
                "par_reduces_cd reduct of a const head that does not delta-unfold (the raw ",
                "delta_reduct-none equation) is the const itself. par_reduces_cd.rec with the ",
                "source-equation Prop motive; structural arms (incl. the genuine-let_ zeta and the ",
                "trailing let_cong congruence, both let_-headed) discharge via inline KExpr.rec ",
                "discriminators + Empty.rec; the atomic iota arm is refuted by iota_reduct_const_none ",
                "(a bare const never fires) + option_none_ne_some; the delta arm by the carried ",
                "equation + option_none_ne_some. DerivedProved, zero axiom_deps. Wall-A completion."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_cd".to_string(),
                "par_reduces_cd.rec".to_string(),
                "iota_step".to_string(),
                "delta_step".to_string(),
                "iota_reduct".to_string(),
                "delta_reduct".to_string(),
                "iota_reduct_const_none".to_string(),
                "option_none_ne_some".to_string(),
                "KExpr.rec".to_string(),
                "Empty".to_string(),
                "Empty.rec".to_string(),
                "red_rec".to_string(),
                "red_def".to_string(),
                "instantiate".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
                "Eq.trans".to_string(),
                "Eq.refl".to_string(),
                "the_red_env".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // Star-level dead-const rigidity (sort-template star induction).
        self.add_definition(SpecDefinition {
            name: "par_reduces_cd_star_const_dead_inv_eq".to_string(),
            type_src: format!(
                concat!(
                    "forall (n : Name) (us : ListType Level) (w : KExpr), {dd} -> ",
                    "par_reduces_cd_star the_red_env (KExpr.const n us) w -> Eq KExpr w (KExpr.const n us)"
                ),
                dd = delta_dead_eq("n", "us"),
            ),
            value_src: Some(format!(
                concat!(
                    "fun (n : Name) (us : ListType Level) (w : KExpr) (hnd : {dd}) ",
                    "(h : par_reduces_cd_star the_red_env (KExpr.const n us) w) => ",
                    "par_reduces_cd_star.rec the_red_env ",
                    "(fun (s : KExpr) (r : KExpr) (_h : par_reduces_cd_star the_red_env s r) => ",
                    "Eq KExpr s (KExpr.const n us) -> Eq KExpr r (KExpr.const n us)) ",
                    "(fun (x : KExpr) (heq : Eq KExpr x (KExpr.const n us)) => heq) ",
                    "(fun (x : KExpr) (y : KExpr) (z : KExpr) ",
                    "(hstep : par_reduces_cd the_red_env x y) ",
                    "(_htail : par_reduces_cd_star the_red_env y z) ",
                    "(ih : Eq KExpr y (KExpr.const n us) -> Eq KExpr z (KExpr.const n us)) ",
                    "(heq : Eq KExpr x (KExpr.const n us)) => ",
                    "ih (par_reduces_cd_const_dead_inv_eq n us y hnd ",
                    "(Eq.substType KExpr (fun (q : KExpr) => par_reduces_cd the_red_env q y) ",
                    "x (KExpr.const n us) heq hstep))) ",
                    "(KExpr.const n us) w h (Eq.refl KExpr (KExpr.const n us))"
                ),
                dd = delta_dead_eq("n", "us"),
            )),
            is_axiom: false,
            description: concat!(
                "Star-level dead-const rigidity (mirror WallAIota.star_const_none_eq): a ",
                "par_reduces_cd_star reduct of a non-unfolding const head is the const itself. ",
                "Star induction threading par_reduces_cd_const_dead_inv_eq through each step ",
                "(the sort-rigidity template). DerivedProved, zero axiom_deps. Wall-A completion."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_cd".to_string(),
                "par_reduces_cd_star".to_string(),
                "par_reduces_cd_star.rec".to_string(),
                "par_reduces_cd_const_dead_inv_eq".to_string(),
                "Eq.substType".to_string(),
                "Eq.refl".to_string(),
                "the_red_env".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    /// Brick 5: neutral-spine rigidity — the mirror's Neutral bookkeeping over
    /// the PARALLEL cd step: delta refutation, single-step app inversion,
    /// step/star preservation, star-level app inversion, star-to-const and
    /// star-to-app extraction (mirror `neutral_no_delta` / `neutral_step` /
    /// `star_neutral` / `step/star_app_neutral_inv` / `neutral_star_const_eq` /
    /// `neutral_star_app_inv`).
    fn add_wall_a_neutral_rigidity(&mut self) -> Result<(), SpecError> {
        // iota_neutral_no_delta: a neutral spine never delta-steps — the head
        // const's delta_reduct is none (const arm, via the raw carried
        // equation), and delta descends spines (app arm, delta_step_app_inv_type).
        self.add_definition(SpecDefinition {
            name: "iota_neutral_no_delta".to_string(),
            type_src: concat!(
                "forall (e : KExpr) (e2 : KExpr) (C : Type), iota_neutral e -> ",
                "delta_step (red_def the_red_env) e e2 -> C"
            )
            .to_string(),
            value_src: Some(format!(
                concat!(
                    "fun (e : KExpr) (e2 : KExpr) (C : Type) (hn : iota_neutral e) ",
                    "(hd : delta_step (red_def the_red_env) e e2) => ",
                    "iota_neutral.rec ",
                    "(fun (x : KExpr) (_h : iota_neutral x) => ",
                    "forall (y : KExpr), delta_step (red_def the_red_env) x y -> C) ",
                    "(fun (m : Name) (vs : ListType Level) (_hw : const_whnf m vs) (hnd : {dd}) => ",
                    "fun (y : KExpr) (hdc : delta_step (red_def the_red_env) (KExpr.const m vs) y) => ",
                    "option_none_ne_some_type KExpr y C ",
                    "(Eq.trans (OptionType KExpr) (OptionType.none KExpr) ",
                    "(delta_reduct (red_def the_red_env) (KExpr.const m vs)) (OptionType.some KExpr y) ",
                    "(Eq.symm (OptionType KExpr) (delta_reduct (red_def the_red_env) (KExpr.const m vs)) ",
                    "(OptionType.none KExpr) hnd) hdc)) ",
                    "(fun (f : KExpr) (a : KExpr) (_hf : iota_neutral f) ",
                    "(_him : iota_immune (KExpr.app f a)) ",
                    "(ihf : forall (y : KExpr), delta_step (red_def the_red_env) f y -> C) => ",
                    "fun (y : KExpr) (hda : delta_step (red_def the_red_env) (KExpr.app f a) y) => ",
                    "delta_step_app_inv_type (red_def the_red_env) f a y C hda ",
                    "(fun (f0 : KExpr) (hdf : delta_step (red_def the_red_env) f f0) ",
                    "(_heq : Eq KExpr y (KExpr.app f0 a)) => ihf f0 hdf)) ",
                    "e hn e2 hd"
                ),
                dd = delta_dead_eq("m", "vs"),
            )),
            is_axiom: false,
            description: concat!(
                "Neutral spines never delta-step (mirror WallAIota.neutral_no_delta): induction on ",
                "iota_neutral — at the const head the carried raw delta_reduct-none equation refutes ",
                "the unfold (option_none_ne_some_type); at an app node delta descends the spine ",
                "(delta_step_app_inv_type) into the IH. DerivedProved, zero axiom_deps. Wall-A completion."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "iota_neutral".to_string(),
                "iota_neutral.rec".to_string(),
                "delta_step".to_string(),
                "delta_reduct".to_string(),
                "delta_step_app_inv_type".to_string(),
                "option_none_ne_some_type".to_string(),
                "iota_immune".to_string(),
                "Eq.symm".to_string(),
                "Eq.trans".to_string(),
                "red_def".to_string(),
                "the_red_env".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_reduces_cd_neutral_app_inv: THE single-step workhorse — a cd step
        // from a neutral app spine is an app of component cd steps (every head
        // fire is refuted: beta by the lam-headed source contradicting
        // neutrality, let_ (zeta) and let_cong by let-vs-app no-confusion
        // (a genuine let_ is never app-headed — let_ne_app), iota by the
        // carried immunity at the refl prefix, delta by
        // iota_neutral_no_delta).
        {
            let kont = |reduct: &str| -> String {
                format!(
                    concat!(
                        "(forall (f2 : KExpr) (a2 : KExpr), Eq KExpr {reduct} (KExpr.app f2 a2) -> ",
                        "par_reduces_cd the_red_env f f2 -> par_reduces_cd the_red_env a a2 -> C)"
                    ),
                    reduct = reduct,
                )
            };
            let motive = format!(
                concat!(
                    "(fun (x : KExpr) (y : KExpr) (_h : par_reduces_cd the_red_env x y) => ",
                    "Eq KExpr x (KExpr.app f a) -> {kont} -> C)"
                ),
                kont = kont("y"),
            );
            let refl_arm = format!(
                concat!(
                    "(fun (x : KExpr) (heq : Eq KExpr x (KExpr.app f a)) (k0 : {kont}) => ",
                    "k0 f a heq (par_reduces_cd.refl the_red_env f) (par_reduces_cd.refl the_red_env a)) "
                ),
                kont = kont("x"),
            );
            // beta: the source app (lam A b0) arg forces f = lam A b0 — refute
            // neutrality of f.
            let beta_arm = format!(
                concat!(
                    "(fun (A : KExpr) (A2 : KExpr) (b0 : KExpr) (b02 : KExpr) (arg : KExpr) (arg2 : KExpr) ",
                    "(_hA : par_reduces_cd the_red_env A A2) (_hb0 : par_reduces_cd the_red_env b0 b02) ",
                    "(_harg : par_reduces_cd the_red_env arg arg2) ",
                    "(_ihA : Eq KExpr A (KExpr.app f a) -> {kont_a2} -> C) ",
                    "(_ihb0 : Eq KExpr b0 (KExpr.app f a) -> {kont_b02} -> C) ",
                    "(_iharg : Eq KExpr arg (KExpr.app f a) -> {kont_arg2} -> C) ",
                    "(heq : Eq KExpr (KExpr.app (KExpr.lam A b0) arg) (KExpr.app f a)) ",
                    "(_k : {kont_red}) => ",
                    "iota_neutral_lam_absurd_type A b0 C ",
                    "(Eq.substType KExpr (fun (z : KExpr) => iota_neutral z) f (KExpr.lam A b0) ",
                    "(Eq.symm KExpr (KExpr.lam A b0) f (app_inj_fst (KExpr.lam A b0) arg f a heq)) hnf)) "
                ),
                kont_a2 = kont("A2"),
                kont_b02 = kont("b02"),
                kont_arg2 = kont("arg2"),
                kont_red = kont("(instantiate b02 arg2)"),
            );
            let app_arm = format!(
                concat!(
                    "(fun (g : KExpr) (g2 : KExpr) (b : KExpr) (b2 : KExpr) ",
                    "(hg : par_reduces_cd the_red_env g g2) (hb : par_reduces_cd the_red_env b b2) ",
                    "(_ihg : Eq KExpr g (KExpr.app f a) -> {kont_g2} -> C) ",
                    "(_ihb : Eq KExpr b (KExpr.app f a) -> {kont_b2} -> C) ",
                    "(heq : Eq KExpr (KExpr.app g b) (KExpr.app f a)) ",
                    "(k0 : {kont_red}) => ",
                    "k0 g2 b2 (Eq.refl KExpr (KExpr.app g2 b2)) ",
                    "(Eq.substType KExpr (fun (z : KExpr) => par_reduces_cd the_red_env z g2) g f ",
                    "(app_inj_fst g b f a heq) hg) ",
                    "(Eq.substType KExpr (fun (z : KExpr) => par_reduces_cd the_red_env z b2) b a ",
                    "(app_inj_snd g b f a heq) hb)) "
                ),
                kont_g2 = kont("g2"),
                kont_b2 = kont("b2"),
                kont_red = kont("(KExpr.app g2 b2)"),
            );
            let lam_arm = format!(
                concat!(
                    "(fun (t0 : KExpr) (t02 : KExpr) (b0 : KExpr) (b02 : KExpr) ",
                    "(_ht : par_reduces_cd the_red_env t0 t02) (_hb : par_reduces_cd the_red_env b0 b02) ",
                    "(_iht : Eq KExpr t0 (KExpr.app f a) -> {kont_t02} -> C) ",
                    "(_ihb : Eq KExpr b0 (KExpr.app f a) -> {kont_b02} -> C) ",
                    "(heq : Eq KExpr (KExpr.lam t0 b0) (KExpr.app f a)) ",
                    "(_k : {kont_red}) => ",
                    "app_ne_lam f a t0 b0 C (Eq.symm KExpr (KExpr.lam t0 b0) (KExpr.app f a) heq)) "
                ),
                kont_t02 = kont("t02"),
                kont_b02 = kont("b02"),
                kont_red = kont("(KExpr.lam t02 b02)"),
            );
            let pi_arm = format!(
                concat!(
                    "(fun (d0 : KExpr) (d02 : KExpr) (b0 : KExpr) (b02 : KExpr) ",
                    "(_hd : par_reduces_cd the_red_env d0 d02) (_hb : par_reduces_cd the_red_env b0 b02) ",
                    "(_ihd : Eq KExpr d0 (KExpr.app f a) -> {kont_d02} -> C) ",
                    "(_ihb : Eq KExpr b0 (KExpr.app f a) -> {kont_b02} -> C) ",
                    "(heq : Eq KExpr (KExpr.pi d0 b0) (KExpr.app f a)) ",
                    "(_k : {kont_red}) => ",
                    "app_ne_pi f a d0 b0 C (Eq.symm KExpr (KExpr.pi d0 b0) (KExpr.app f a) heq)) "
                ),
                kont_d02 = kont("d02"),
                kont_b02 = kont("b02"),
                kont_red = kont("(KExpr.pi d02 b02)"),
            );
            let forall_arm = format!(
                concat!(
                    "(fun (d0 : KExpr) (d02 : KExpr) (b0 : KExpr) (b02 : KExpr) ",
                    "(_hd : par_reduces_cd the_red_env d0 d02) (_hb : par_reduces_cd the_red_env b0 b02) ",
                    "(_ihd : Eq KExpr d0 (KExpr.app f a) -> {kont_d02} -> C) ",
                    "(_ihb : Eq KExpr b0 (KExpr.app f a) -> {kont_b02} -> C) ",
                    "(heq : Eq KExpr (KExpr.forall_ d0 b0) (KExpr.app f a)) ",
                    "(_k : {kont_red}) => ",
                    "app_ne_pi f a d0 b0 C (Eq.symm KExpr (KExpr.forall_ d0 b0) (KExpr.app f a) heq)) "
                ),
                kont_d02 = kont("d02"),
                kont_b02 = kont("b02"),
                kont_red = kont("(KExpr.forall_ d02 b02)"),
            );
            // let_ (zeta) arm: the source is a genuine let_ node — never an
            // app. let-vs-app no-confusion refutes heq outright (under the old
            // alias this arm extracted a lam head via app_inj_fst; the genuine
            // ctor is shape-disjoint instead).
            let let_arm = format!(
                concat!(
                    "(fun (t0 : KExpr) (t02 : KExpr) (v0 : KExpr) (v02 : KExpr) (b0 : KExpr) (b02 : KExpr) ",
                    "(_ht : par_reduces_cd the_red_env t0 t02) (_hv : par_reduces_cd the_red_env v0 v02) ",
                    "(_hb : par_reduces_cd the_red_env b0 b02) ",
                    "(_iht : Eq KExpr t0 (KExpr.app f a) -> {kont_t02} -> C) ",
                    "(_ihv : Eq KExpr v0 (KExpr.app f a) -> {kont_v02} -> C) ",
                    "(_ihb : Eq KExpr b0 (KExpr.app f a) -> {kont_b02} -> C) ",
                    "(heq : Eq KExpr (KExpr.let_ t0 v0 b0) (KExpr.app f a)) ",
                    "(_k : {kont_red}) => ",
                    "let_ne_app t0 v0 b0 f a C heq) "
                ),
                kont_t02 = kont("t02"),
                kont_v02 = kont("v02"),
                kont_b02 = kont("b02"),
                kont_red = kont("(instantiate b02 v02)"),
            );
            let iota_arm = format!(
                concat!(
                    "(fun (x0 : KExpr) (y0 : KExpr) (hi : iota_step (red_rec the_red_env) x0 y0) ",
                    "(heq : Eq KExpr x0 (KExpr.app f a)) ",
                    "(_k : {kont_red}) => ",
                    "Empty.rec (fun (_ : Empty) => C) ",
                    "(him (KExpr.app f a) y0 (par_reduces_cd_star.refl the_red_env (KExpr.app f a)) ",
                    "(Eq.substType KExpr (fun (z : KExpr) => iota_step (red_rec the_red_env) z y0) ",
                    "x0 (KExpr.app f a) heq hi))) "
                ),
                kont_red = kont("y0"),
            );
            let delta_arm = format!(
                concat!(
                    "(fun (x0 : KExpr) (y0 : KExpr) (hd : delta_step (red_def the_red_env) x0 y0) ",
                    "(heq : Eq KExpr x0 (KExpr.app f a)) ",
                    "(_k : {kont_red}) => ",
                    "iota_neutral_no_delta (KExpr.app f a) y0 C (iota_neutral.app f a hnf him) ",
                    "(Eq.substType KExpr (fun (z : KExpr) => delta_step (red_def the_red_env) z y0) ",
                    "x0 (KExpr.app f a) heq hd))"
                ),
                kont_red = kont("y0"),
            );
            // Trailing let_cong minor: a let_-headed source again — refuted by
            // let-vs-app no-confusion exactly like the zeta arm.
            let let_cong_arm = format!(
                concat!(
                    "(fun (t0 : KExpr) (t02 : KExpr) (v0 : KExpr) (v02 : KExpr) (b0 : KExpr) (b02 : KExpr) ",
                    "(_ht : par_reduces_cd the_red_env t0 t02) (_hv : par_reduces_cd the_red_env v0 v02) ",
                    "(_hb : par_reduces_cd the_red_env b0 b02) ",
                    "(_iht : Eq KExpr t0 (KExpr.app f a) -> {kont_t02} -> C) ",
                    "(_ihv : Eq KExpr v0 (KExpr.app f a) -> {kont_v02} -> C) ",
                    "(_ihb : Eq KExpr b0 (KExpr.app f a) -> {kont_b02} -> C) ",
                    "(heq : Eq KExpr (KExpr.let_ t0 v0 b0) (KExpr.app f a)) ",
                    "(_k : {kont_red}) => ",
                    "let_ne_app t0 v0 b0 f a C heq)"
                ),
                kont_t02 = kont("t02"),
                kont_v02 = kont("v02"),
                kont_b02 = kont("b02"),
                kont_red = kont("(KExpr.let_ t02 v02 b02)"),
            );
            // Trailing proj minor: a proj-headed source is never app — refuted
            // by proj-vs-app no-confusion (proj_ne_app).
            let proj_arm = format!(
                concat!(
                    "(fun (s : Name) (i : Nat) (sub0 : KExpr) (sub02 : KExpr) ",
                    "(_hsub : par_reduces_cd the_red_env sub0 sub02) ",
                    "(_ihsub : Eq KExpr sub0 (KExpr.app f a) -> {kont_sub02} -> C) ",
                    "(heq : Eq KExpr (KExpr.proj s i sub0) (KExpr.app f a)) ",
                    "(_k : {kont_red}) => ",
                    "proj_ne_app s i sub0 f a C heq)"
                ),
                kont_sub02 = kont("sub02"),
                kont_red = kont("(KExpr.proj s i sub02)"),
            );

            self.add_definition(SpecDefinition {
                name: "par_reduces_cd_neutral_app_inv".to_string(),
                type_src: format!(
                    concat!(
                        "forall (f : KExpr) (a : KExpr) (t : KExpr) (C : Type), ",
                        "iota_neutral f -> iota_immune (KExpr.app f a) -> ",
                        "par_reduces_cd the_red_env (KExpr.app f a) t -> ",
                        "{kont} -> C"
                    ),
                    kont = kont("t"),
                ),
                value_src: Some(format!(
                    concat!(
                        "fun (f : KExpr) (a : KExpr) (t : KExpr) (C : Type) ",
                        "(hnf : iota_neutral f) (him : iota_immune (KExpr.app f a)) ",
                        "(h : par_reduces_cd the_red_env (KExpr.app f a) t) ",
                        "(k : {kont_t}) => ",
                        "par_reduces_cd.rec the_red_env {motive} ",
                        "{refl_arm}{beta_arm}{app_arm}{lam_arm}{pi_arm}{forall_arm}{let_arm}{iota_arm}{delta_arm} {let_cong_arm} {proj_arm} ",
                        "(KExpr.app f a) t h (Eq.refl KExpr (KExpr.app f a)) k"
                    ),
                    kont_t = kont("t"),
                    motive = motive,
                    refl_arm = refl_arm,
                    beta_arm = beta_arm,
                    app_arm = app_arm,
                    lam_arm = lam_arm,
                    pi_arm = pi_arm,
                    forall_arm = forall_arm,
                    let_arm = let_arm,
                    iota_arm = iota_arm,
                    delta_arm = delta_arm,
                    let_cong_arm = let_cong_arm,
                    proj_arm = proj_arm,
                )),
                is_axiom: false,
                description: concat!(
                    "Single-step neutral-spine inversion (mirror WallAIota.step_app_neutral_inv, over ",
                    "the PARALLEL cd step): a par_reduces_cd step from an iota-neutral, iota-immune app ",
                    "spine is an app of component cd steps. Source-equation par_reduces_cd.rec: the ",
                    "beta arm forces a lam head on the neutral f (app_inj_fst + ",
                    "iota_neutral_lam_absurd_type); the let_ (zeta) and trailing let_cong arms have ",
                    "genuine let_-headed sources — never app-headed — refuted by let_ne_app; the iota ",
                    "arm is killed by the carried immunity at the refl prefix (Empty.rec); the delta ",
                    "arm by iota_neutral_no_delta; lam/pi/forall_ sources are impossible ",
                    "(app_ne_lam/app_ne_pi). DerivedProved, zero axiom_deps. Wall-A completion."
                )
                .to_string(),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "par_reduces_cd".to_string(),
                    "par_reduces_cd.rec".to_string(),
                    "par_reduces_cd.refl".to_string(),
                    "par_reduces_cd_star.refl".to_string(),
                    "iota_neutral".to_string(),
                    "iota_neutral.app".to_string(),
                    "iota_immune".to_string(),
                    "iota_neutral_no_delta".to_string(),
                    "iota_neutral_lam_absurd_type".to_string(),
                    "proj_ne_app".to_string(),
                    "app_inj_fst".to_string(),
                    "app_inj_snd".to_string(),
                    "app_ne_lam".to_string(),
                    "app_ne_pi".to_string(),
                    "let_ne_app".to_string(),
                    "iota_step".to_string(),
                    "delta_step".to_string(),
                    "Empty".to_string(),
                    "Empty.rec".to_string(),
                    "Eq.substType".to_string(),
                    "Eq.symm".to_string(),
                    "Eq.refl".to_string(),
                    "instantiate".to_string(),
                    "red_rec".to_string(),
                    "red_def".to_string(),
                    "the_red_env".to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }

        // iota_immune_cd_step: immunity is preserved along a cd step (prepend
        // the step to the offending star trace).
        self.add_definition(SpecDefinition {
            name: "iota_immune_cd_step".to_string(),
            type_src: concat!(
                "forall (e : KExpr) (e2 : KExpr), iota_immune e -> ",
                "par_reduces_cd the_red_env e e2 -> iota_immune e2"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (e : KExpr) (e2 : KExpr) (him : iota_immune e) ",
                    "(hstep : par_reduces_cd the_red_env e e2) ",
                    "(e3 : KExpr) (r : KExpr) (hstar : par_reduces_cd_star the_red_env e2 e3) ",
                    "(hfire : iota_step (red_rec the_red_env) e3 r) => ",
                    "him e3 r (par_reduces_cd_star.step the_red_env e e2 e3 hstep hstar) hfire"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Iota-immunity is preserved along a single par_reduces_cd step (mirror ",
                "WallAIota.iotaImmune_step): prepend the step to the offending star trace. ",
                "DerivedProved, zero axiom_deps. Wall-A completion."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "iota_immune".to_string(),
                "par_reduces_cd".to_string(),
                "par_reduces_cd_star".to_string(),
                "par_reduces_cd_star.step".to_string(),
                "iota_step".to_string(),
                "red_rec".to_string(),
                "the_red_env".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // iota_neutral_cd_step: neutrality is preserved along a cd step.
        self.add_definition(SpecDefinition {
            name: "iota_neutral_cd_step".to_string(),
            type_src: concat!(
                "forall (e : KExpr) (t : KExpr), iota_neutral e -> ",
                "par_reduces_cd the_red_env e t -> iota_neutral t"
            )
            .to_string(),
            value_src: Some(format!(
                concat!(
                    "fun (e : KExpr) (t : KExpr) (hn : iota_neutral e) ",
                    "(h : par_reduces_cd the_red_env e t) => ",
                    "iota_neutral.rec ",
                    "(fun (x : KExpr) (_h : iota_neutral x) => ",
                    "forall (y : KExpr), par_reduces_cd the_red_env x y -> iota_neutral y) ",
                    // const arm: dead-const rigidity pins y = const, transport
                    // the const ctor back.
                    "(fun (m : Name) (vs : ListType Level) (hw : const_whnf m vs) (hnd : {dd}) => ",
                    "fun (y : KExpr) (hstep : par_reduces_cd the_red_env (KExpr.const m vs) y) => ",
                    "Eq.substType KExpr (fun (z : KExpr) => iota_neutral z) (KExpr.const m vs) y ",
                    "(Eq.symm KExpr y (KExpr.const m vs) (par_reduces_cd_const_dead_inv_eq m vs y hnd hstep)) ",
                    "(iota_neutral.const m vs hw hnd)) ",
                    // app arm: invert the step, rebuild neutrality of the reduct.
                    "(fun (f : KExpr) (a : KExpr) (hf : iota_neutral f) ",
                    "(him : iota_immune (KExpr.app f a)) ",
                    "(ihf : forall (y : KExpr), par_reduces_cd the_red_env f y -> iota_neutral y) => ",
                    "fun (y : KExpr) (hstep : par_reduces_cd the_red_env (KExpr.app f a) y) => ",
                    "par_reduces_cd_neutral_app_inv f a y (iota_neutral y) hf him hstep ",
                    "(fun (f2 : KExpr) (a2 : KExpr) (heq : Eq KExpr y (KExpr.app f2 a2)) ",
                    "(hff2 : par_reduces_cd the_red_env f f2) (haa2 : par_reduces_cd the_red_env a a2) => ",
                    "Eq.substType KExpr (fun (z : KExpr) => iota_neutral z) (KExpr.app f2 a2) y ",
                    "(Eq.symm KExpr y (KExpr.app f2 a2) heq) ",
                    "(iota_neutral.app f2 a2 (ihf f2 hff2) ",
                    "(iota_immune_cd_step (KExpr.app f a) (KExpr.app f2 a2) him ",
                    "(par_reduces_cd.app the_red_env f f2 a a2 hff2 haa2))))) ",
                    "e hn t h"
                ),
                dd = delta_dead_eq("m", "vs"),
            )),
            is_axiom: false,
            description: concat!(
                "Iota-aware neutrality is preserved along a single par_reduces_cd step (mirror ",
                "WallAIota.neutral_step): const heads are rigid (par_reduces_cd_const_dead_inv_eq), app ",
                "spines invert componentwise (par_reduces_cd_neutral_app_inv) and rebuild via the IH + ",
                "iota_immune_cd_step. DerivedProved, zero axiom_deps. Wall-A completion."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "iota_neutral".to_string(),
                "iota_neutral.rec".to_string(),
                "iota_neutral.const".to_string(),
                "iota_neutral.app".to_string(),
                "par_reduces_cd".to_string(),
                "par_reduces_cd.app".to_string(),
                "par_reduces_cd_const_dead_inv_eq".to_string(),
                "par_reduces_cd_neutral_app_inv".to_string(),
                "iota_immune_cd_step".to_string(),
                "const_whnf".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
                "the_red_env".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // iota_neutral_cd_star: neutrality is preserved along a star.
        self.add_definition(SpecDefinition {
            name: "iota_neutral_cd_star".to_string(),
            type_src: concat!(
                "forall (e : KExpr) (w : KExpr), iota_neutral e -> ",
                "par_reduces_cd_star the_red_env e w -> iota_neutral w"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (e : KExpr) (w : KExpr) (hn : iota_neutral e) ",
                    "(h : par_reduces_cd_star the_red_env e w) => ",
                    "par_reduces_cd_star.rec the_red_env ",
                    "(fun (s : KExpr) (r : KExpr) (_h : par_reduces_cd_star the_red_env s r) => ",
                    "iota_neutral s -> iota_neutral r) ",
                    "(fun (x : KExpr) (hx : iota_neutral x) => hx) ",
                    "(fun (x : KExpr) (y : KExpr) (z : KExpr) ",
                    "(hstep : par_reduces_cd the_red_env x y) ",
                    "(_htail : par_reduces_cd_star the_red_env y z) ",
                    "(ih : iota_neutral y -> iota_neutral z) (hx : iota_neutral x) => ",
                    "ih (iota_neutral_cd_step x y hx hstep)) ",
                    "e w h hn"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Iota-aware neutrality is preserved along par_reduces_cd_star (mirror ",
                "WallAIota.star_neutral): star induction over iota_neutral_cd_step. DerivedProved, ",
                "zero axiom_deps. Wall-A completion."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "iota_neutral".to_string(),
                "par_reduces_cd_star".to_string(),
                "par_reduces_cd_star.rec".to_string(),
                "iota_neutral_cd_step".to_string(),
                "the_red_env".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // Named one-step cast/join utilities. The surface elaborator's
        // application checker rejects certain DEEPLY-NESTED compound argument
        // shapes in context (an emergent false negative — every fragment
        // checks standalone); routing every transport through these named
        // helpers keeps all downstream proof terms at the empirically-robust
        // nesting depth.
        for (name, type_src, value_src, desc) in [
            (
                "par_reduces_cd_star_target_cast",
                concat!(
                    "forall (x : KExpr) (y : KExpr) (t : KExpr), Eq KExpr y t -> ",
                    "par_reduces_cd_star the_red_env x y -> par_reduces_cd_star the_red_env x t"
                )
                .to_string(),
                concat!(
                    "fun (x : KExpr) (y : KExpr) (t : KExpr) (e : Eq KExpr y t) ",
                    "(h : par_reduces_cd_star the_red_env x y) => ",
                    "Eq.substType KExpr (fun (z : KExpr) => par_reduces_cd_star the_red_env x z) ",
                    "y t e h"
                )
                .to_string(),
                "Cast the target of a par_reduces_cd_star along a propositional equality \
                 (forward direction). Named transport utility (elaborator nesting-depth \
                 discipline). DerivedProved, zero axiom_deps. Wall-A completion.",
            ),
            (
                "par_reduces_cd_star_target_cast_rev",
                concat!(
                    "forall (x : KExpr) (y : KExpr) (t : KExpr), Eq KExpr t y -> ",
                    "par_reduces_cd_star the_red_env x y -> par_reduces_cd_star the_red_env x t"
                )
                .to_string(),
                concat!(
                    "fun (x : KExpr) (y : KExpr) (t : KExpr) (e : Eq KExpr t y) ",
                    "(h : par_reduces_cd_star the_red_env x y) => ",
                    "Eq.substType KExpr (fun (z : KExpr) => par_reduces_cd_star the_red_env x z) ",
                    "y t (Eq.symm KExpr t y e) h"
                )
                .to_string(),
                "Cast the target of a par_reduces_cd_star along a propositional equality \
                 (reversed equation). Named transport utility (elaborator nesting-depth \
                 discipline). DerivedProved, zero axiom_deps. Wall-A completion.",
            ),
            (
                "head_match_target_cast_rev",
                concat!(
                    "forall (x : KExpr) (y : KExpr) (t : KExpr), Eq KExpr t y -> ",
                    "HeadMatch x y -> HeadMatch x t"
                )
                .to_string(),
                concat!(
                    "fun (x : KExpr) (y : KExpr) (t : KExpr) (e : Eq KExpr t y) ",
                    "(h : HeadMatch x y) => ",
                    "Eq.substType KExpr (fun (z : KExpr) => HeadMatch x z) ",
                    "y t (Eq.symm KExpr t y e) h"
                )
                .to_string(),
                "Cast the right-hand side of a HeadMatch along a propositional equality \
                 (reversed equation). Named transport utility (elaborator nesting-depth \
                 discipline). DerivedProved, zero axiom_deps. Wall-A completion.",
            ),
            (
                "cd_star_join_to_def_eq",
                concat!(
                    "forall (x : KExpr) (y : KExpr) (m : KExpr), ",
                    "par_reduces_cd_star the_red_env x m -> par_reduces_cd_star the_red_env y m -> ",
                    "DefEq x y"
                )
                .to_string(),
                concat!(
                    "fun (x : KExpr) (y : KExpr) (m : KExpr) ",
                    "(hx : par_reduces_cd_star the_red_env x m) ",
                    "(hy : par_reduces_cd_star the_red_env y m) => ",
                    "join_to_def_eq x y (par_strips_witness_cd_star.intro the_red_env x y m hx hy)"
                )
                .to_string(),
                "Two terms meeting at a common cd_star reduct are DefEq (join_to_def_eq over \
                 the packaged witness). Named join utility (elaborator nesting-depth \
                 discipline). DerivedProved, zero axiom_deps. Wall-A completion.",
            ),
        ] {
            self.add_definition(SpecDefinition {
                name: name.to_string(),
                type_src,
                value_src: Some(value_src),
                is_axiom: false,
                description: desc.to_string(),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "par_reduces_cd_star".to_string(),
                    "HeadMatch".to_string(),
                    "DefEq".to_string(),
                    "join_to_def_eq".to_string(),
                    "par_strips_witness_cd_star.intro".to_string(),
                    "Eq.substType".to_string(),
                    "Eq.symm".to_string(),
                    "the_red_env".to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }

        // par_reduces_cd_star_neutral_app_inv: star-level neutral-spine
        // inversion with an accumulator motive (the cd_star_lam_inv template),
        // carrying the target's neutrality + immunity.
        self.add_definition(SpecDefinition {
            name: "par_reduces_cd_star_neutral_app_inv".to_string(),
            type_src: concat!(
                "forall (f : KExpr) (a : KExpr) (w : KExpr) (C : KExpr -> Type), ",
                "iota_neutral f -> iota_immune (KExpr.app f a) -> ",
                "par_reduces_cd_star the_red_env (KExpr.app f a) w -> ",
                "(forall (f2 : KExpr) (a2 : KExpr), ",
                "par_reduces_cd_star the_red_env f f2 -> par_reduces_cd_star the_red_env a a2 -> ",
                "iota_neutral f2 -> iota_immune (KExpr.app f2 a2) -> C (KExpr.app f2 a2)) -> ",
                "C w"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (f : KExpr) (a : KExpr) (w : KExpr) (C : KExpr -> Type) ",
                    "(hnf : iota_neutral f) (him : iota_immune (KExpr.app f a)) ",
                    "(h : par_reduces_cd_star the_red_env (KExpr.app f a) w) ",
                    "(k : forall (f2 : KExpr) (a2 : KExpr), ",
                    "par_reduces_cd_star the_red_env f f2 -> par_reduces_cd_star the_red_env a a2 -> ",
                    "iota_neutral f2 -> iota_immune (KExpr.app f2 a2) -> C (KExpr.app f2 a2)) => ",
                    "par_reduces_cd_star.rec the_red_env ",
                    "(fun (s : KExpr) (r : KExpr) (_h : par_reduces_cd_star the_red_env s r) => ",
                    "forall (F : KExpr) (A : KExpr), Eq KExpr s (KExpr.app F A) -> ",
                    "iota_neutral F -> iota_immune (KExpr.app F A) -> ",
                    "par_reduces_cd_star the_red_env f F -> par_reduces_cd_star the_red_env a A -> C r) ",
                    // refl arm
                    "(fun (x : KExpr) => ",
                    "fun (F : KExpr) (A : KExpr) (heq : Eq KExpr x (KExpr.app F A)) ",
                    "(hF : iota_neutral F) (hIm : iota_immune (KExpr.app F A)) ",
                    "(hfF : par_reduces_cd_star the_red_env f F) (haA : par_reduces_cd_star the_red_env a A) => ",
                    "Eq.substType KExpr C (KExpr.app F A) x (Eq.symm KExpr x (KExpr.app F A) heq) ",
                    "(k F A hfF haA hF hIm)) ",
                    // step arm
                    "(fun (x : KExpr) (y : KExpr) (z : KExpr) ",
                    "(hstep : par_reduces_cd the_red_env x y) ",
                    "(_htail : par_reduces_cd_star the_red_env y z) ",
                    "(ih : forall (F : KExpr) (A : KExpr), Eq KExpr y (KExpr.app F A) -> ",
                    "iota_neutral F -> iota_immune (KExpr.app F A) -> ",
                    "par_reduces_cd_star the_red_env f F -> par_reduces_cd_star the_red_env a A -> C z) => ",
                    "fun (F : KExpr) (A : KExpr) (heq : Eq KExpr x (KExpr.app F A)) ",
                    "(hF : iota_neutral F) (hIm : iota_immune (KExpr.app F A)) ",
                    "(hfF : par_reduces_cd_star the_red_env f F) (haA : par_reduces_cd_star the_red_env a A) => ",
                    "par_reduces_cd_neutral_app_inv F A y (C z) hF hIm ",
                    "(Eq.substType KExpr (fun (q : KExpr) => par_reduces_cd the_red_env q y) ",
                    "x (KExpr.app F A) heq hstep) ",
                    "(fun (F2 : KExpr) (A2 : KExpr) (heq2 : Eq KExpr y (KExpr.app F2 A2)) ",
                    "(hFF2 : par_reduces_cd the_red_env F F2) (hAA2 : par_reduces_cd the_red_env A A2) => ",
                    "ih F2 A2 heq2 ",
                    "(iota_neutral_cd_step F F2 hF hFF2) ",
                    "(iota_immune_cd_step (KExpr.app F A) (KExpr.app F2 A2) hIm ",
                    "(par_reduces_cd.app the_red_env F F2 A A2 hFF2 hAA2)) ",
                    "(par_reduces_cd_star_trans the_red_env f F F2 hfF ",
                    "(par_subsumes_par_cd_star the_red_env F F2 hFF2)) ",
                    "(par_reduces_cd_star_trans the_red_env a A A2 haA ",
                    "(par_subsumes_par_cd_star the_red_env A A2 hAA2)))) ",
                    "(KExpr.app f a) w h ",
                    "f a (Eq.refl KExpr (KExpr.app f a)) hnf him ",
                    "(par_reduces_cd_star.refl the_red_env f) (par_reduces_cd_star.refl the_red_env a)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Star-level neutral-spine inversion (mirror WallAIota.star_app_neutral_inv): a ",
                "par_reduces_cd_star reduct of an iota-neutral iota-immune app spine is an app spine ",
                "of component stars, still neutral and immune. Accumulator star induction (the ",
                "cd_star lam/pi-inversion template) over par_reduces_cd_neutral_app_inv, extending ",
                "prefixes via par_reduces_cd_star_trans + par_subsumes_par_cd_star and neutrality via ",
                "iota_neutral_cd_step / iota_immune_cd_step. DerivedProved, zero axiom_deps. ",
                "Wall-A completion."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_cd_star".to_string(),
                "par_reduces_cd_star.rec".to_string(),
                "par_reduces_cd_star.refl".to_string(),
                "par_reduces_cd_star_trans".to_string(),
                "par_subsumes_par_cd_star".to_string(),
                "par_reduces_cd.app".to_string(),
                "par_reduces_cd_neutral_app_inv".to_string(),
                "iota_neutral_cd_step".to_string(),
                "iota_immune_cd_step".to_string(),
                "iota_neutral".to_string(),
                "iota_immune".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
                "Eq.refl".to_string(),
                "the_red_env".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // Eq-data sibling (reduct equality handed back; C : Type) — derived by
        // instantiating the motive at M(ww) := Eq w ww -> C at Eq.refl w.
        self.add_definition(SpecDefinition {
            name: "par_reduces_cd_star_neutral_app_inv_eq".to_string(),
            type_src: concat!(
                "forall (f : KExpr) (a : KExpr) (w : KExpr) (C : Type), ",
                "iota_neutral f -> iota_immune (KExpr.app f a) -> ",
                "par_reduces_cd_star the_red_env (KExpr.app f a) w -> ",
                "(forall (f2 : KExpr) (a2 : KExpr), Eq KExpr w (KExpr.app f2 a2) -> ",
                "par_reduces_cd_star the_red_env f f2 -> par_reduces_cd_star the_red_env a a2 -> ",
                "iota_neutral f2 -> iota_immune (KExpr.app f2 a2) -> C) -> ",
                "C"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (f : KExpr) (a : KExpr) (w : KExpr) (C : Type) ",
                    "(hnf : iota_neutral f) (him : iota_immune (KExpr.app f a)) ",
                    "(h : par_reduces_cd_star the_red_env (KExpr.app f a) w) ",
                    "(k : forall (f2 : KExpr) (a2 : KExpr), Eq KExpr w (KExpr.app f2 a2) -> ",
                    "par_reduces_cd_star the_red_env f f2 -> par_reduces_cd_star the_red_env a a2 -> ",
                    "iota_neutral f2 -> iota_immune (KExpr.app f2 a2) -> C) => ",
                    "par_reduces_cd_star_neutral_app_inv f a w ",
                    "(fun (ww : KExpr) => Eq KExpr w ww -> C) hnf him h ",
                    "(fun (f2 : KExpr) (a2 : KExpr) ",
                    "(hff2 : par_reduces_cd_star the_red_env f f2) ",
                    "(haa2 : par_reduces_cd_star the_red_env a a2) ",
                    "(hn2 : iota_neutral f2) (him2 : iota_immune (KExpr.app f2 a2)) => ",
                    "fun (eqw : Eq KExpr w (KExpr.app f2 a2)) => k f2 a2 eqw hff2 haa2 hn2 him2) ",
                    "(Eq.refl KExpr w)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Eq-data sibling of par_reduces_cd_star_neutral_app_inv (the reduct equality handed ",
                "back as data), derived by instantiating its motive at M(ww) := Eq w ww -> C applied ",
                "at Eq.refl w — the standard _inv_eq derivation. DerivedProved, zero axiom_deps. ",
                "Wall-A completion."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_cd_star_neutral_app_inv".to_string(),
                "par_reduces_cd_star".to_string(),
                "iota_neutral".to_string(),
                "iota_immune".to_string(),
                "Eq.refl".to_string(),
                "the_red_env".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // iota_neutral_star_const_inv_eq: a neutral term that star-reduces to
        // a const IS that const (mirror neutral_star_const_eq).
        self.add_definition(SpecDefinition {
            name: "iota_neutral_star_const_inv_eq".to_string(),
            type_src: concat!(
                "forall (e : KExpr) (n : Name) (us : ListType Level), iota_neutral e -> ",
                "par_reduces_cd_star the_red_env e (KExpr.const n us) -> Eq KExpr e (KExpr.const n us)"
            )
            .to_string(),
            value_src: Some(format!(
                concat!(
                    "fun (e : KExpr) (n : Name) (us : ListType Level) (hn : iota_neutral e) ",
                    "(h : par_reduces_cd_star the_red_env e (KExpr.const n us)) => ",
                    "iota_neutral.rec ",
                    "(fun (x : KExpr) (_h : iota_neutral x) => ",
                    "par_reduces_cd_star the_red_env x (KExpr.const n us) -> Eq KExpr x (KExpr.const n us)) ",
                    // const arm: dead-const rigidity gives (const n us) = (const m vs).
                    "(fun (m : Name) (vs : ListType Level) (_hw : const_whnf m vs) (hnd : {dd}) => ",
                    "fun (hstar : par_reduces_cd_star the_red_env (KExpr.const m vs) (KExpr.const n us)) => ",
                    "Eq.symm KExpr (KExpr.const n us) (KExpr.const m vs) ",
                    "(par_reduces_cd_star_const_dead_inv_eq m vs (KExpr.const n us) hnd hstar)) ",
                    // app arm: star inversion pins the const target to an app shape — absurd
                    // (route through C := Empty, then Empty.rec into the Prop goal).
                    "(fun (f : KExpr) (a : KExpr) (hf : iota_neutral f) ",
                    "(him : iota_immune (KExpr.app f a)) ",
                    "(_ihf : par_reduces_cd_star the_red_env f (KExpr.const n us) -> ",
                    "Eq KExpr f (KExpr.const n us)) => ",
                    "fun (hstar : par_reduces_cd_star the_red_env (KExpr.app f a) (KExpr.const n us)) => ",
                    "Empty.rec (fun (_ : Empty) => Eq KExpr (KExpr.app f a) (KExpr.const n us)) ",
                    "(par_reduces_cd_star_neutral_app_inv_eq f a (KExpr.const n us) Empty hf him hstar ",
                    "(fun (f2 : KExpr) (a2 : KExpr) (eqw : Eq KExpr (KExpr.const n us) (KExpr.app f2 a2)) ",
                    "(_hff2 : par_reduces_cd_star the_red_env f f2) ",
                    "(_haa2 : par_reduces_cd_star the_red_env a a2) ",
                    "(_hn2 : iota_neutral f2) (_him2 : iota_immune (KExpr.app f2 a2)) => ",
                    "Eq.substType KExpr {is_const} (KExpr.const n us) (KExpr.app f2 a2) eqw Nat.zero))) ",
                    "e hn h"
                ),
                dd = delta_dead_eq("m", "vs"),
                is_const = KEXPR_IS_CONST,
            )),
            is_axiom: false,
            description: concat!(
                "Neutral-to-const star extraction (mirror WallAIota.neutral_star_const_eq): an ",
                "iota-neutral term whose cd_star reduct is a const IS that const. Const heads by ",
                "dead-const star rigidity; app spines are refuted (the star inversion pins the const ",
                "target to an app shape — Empty via the inline const/app discriminator, routed through ",
                "C := Empty into the Prop goal). DerivedProved, zero axiom_deps. Wall-A completion."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "iota_neutral".to_string(),
                "iota_neutral.rec".to_string(),
                "par_reduces_cd_star".to_string(),
                "par_reduces_cd_star_const_dead_inv_eq".to_string(),
                "par_reduces_cd_star_neutral_app_inv_eq".to_string(),
                "KExpr.rec".to_string(),
                "Empty".to_string(),
                "Empty.rec".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
                "the_red_env".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // Named continuation for the app arm of iota_neutral_star_to_app_inv:
        // aligns the inverted spine components with the target's via app
        // injectivity + the named target casts, and re-enters the caller's
        // continuation at the spine itself (Eq.refl). Passed as a PARTIAL
        // APPLICATION (elaborator nesting-depth discipline).
        self.add_definition(SpecDefinition {
            name: "iota_neutral_star_to_app_kont".to_string(),
            type_src: concat!(
                "forall (P : KExpr) (Q : KExpr) (f : KExpr) (a : KExpr) (C : Type), ",
                "(forall (g : KExpr) (d : KExpr), Eq KExpr (KExpr.app f a) (KExpr.app g d) -> ",
                "iota_neutral g -> iota_immune (KExpr.app g d) -> ",
                "par_reduces_cd_star the_red_env g P -> par_reduces_cd_star the_red_env d Q -> C) -> ",
                "iota_neutral f -> iota_immune (KExpr.app f a) -> ",
                "forall (f2 : KExpr) (a2 : KExpr), Eq KExpr (KExpr.app P Q) (KExpr.app f2 a2) -> ",
                "par_reduces_cd_star the_red_env f f2 -> par_reduces_cd_star the_red_env a a2 -> ",
                "iota_neutral f2 -> iota_immune (KExpr.app f2 a2) -> C"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (P : KExpr) (Q : KExpr) (f : KExpr) (a : KExpr) (C : Type) ",
                    "(k0 : forall (g : KExpr) (d : KExpr), Eq KExpr (KExpr.app f a) (KExpr.app g d) -> ",
                    "iota_neutral g -> iota_immune (KExpr.app g d) -> ",
                    "par_reduces_cd_star the_red_env g P -> par_reduces_cd_star the_red_env d Q -> C) ",
                    "(hf : iota_neutral f) (him : iota_immune (KExpr.app f a)) ",
                    "(f2 : KExpr) (a2 : KExpr) (eqw : Eq KExpr (KExpr.app P Q) (KExpr.app f2 a2)) ",
                    "(hff2 : par_reduces_cd_star the_red_env f f2) ",
                    "(haa2 : par_reduces_cd_star the_red_env a a2) ",
                    "(_hn2 : iota_neutral f2) (_him2 : iota_immune (KExpr.app f2 a2)) => ",
                    // Applied-lambda double-bind (nesting discipline): bind the
                    // injectivity equations, then the cast legs, so every
                    // application site carries atoms or one-level compounds.
                    "(fun (eA : Eq KExpr P f2) (eB : Eq KExpr Q a2) => ",
                    "(fun (legP : par_reduces_cd_star the_red_env f P) ",
                    "(legQ : par_reduces_cd_star the_red_env a Q) => ",
                    "k0 f a (Eq.refl KExpr (KExpr.app f a)) hf him legP legQ) ",
                    "(par_reduces_cd_star_target_cast_rev f f2 P eA hff2) ",
                    "(par_reduces_cd_star_target_cast_rev a a2 Q eB haa2)) ",
                    "(app_inj_fst P Q f2 a2 eqw) ",
                    "(app_inj_snd P Q f2 a2 eqw)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Named continuation of iota_neutral_star_to_app_inv's app arm: the inverted spine ",
                "components are aligned with the target's by app injectivity + the named target ",
                "casts, and the caller's continuation re-enters at the spine itself (Eq.refl). ",
                "Extracted as a named lemma and consumed as a partial application (elaborator ",
                "nesting-depth discipline). DerivedProved, zero axiom_deps. Wall-A completion."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "iota_neutral".to_string(),
                "iota_immune".to_string(),
                "par_reduces_cd_star".to_string(),
                "par_reduces_cd_star_target_cast_rev".to_string(),
                "app_inj_fst".to_string(),
                "app_inj_snd".to_string(),
                "Eq.refl".to_string(),
                "the_red_env".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // iota_neutral_star_to_app_inv: a neutral term star-reducing to an app
        // is itself a neutral app spine whose components star to the target's
        // (mirror neutral_star_app_inv).
        self.add_definition(SpecDefinition {
            name: "iota_neutral_star_to_app_inv".to_string(),
            type_src: concat!(
                "forall (nb : KExpr) (P : KExpr) (Q : KExpr) (C : Type), iota_neutral nb -> ",
                "par_reduces_cd_star the_red_env nb (KExpr.app P Q) -> ",
                "(forall (g : KExpr) (d : KExpr), Eq KExpr nb (KExpr.app g d) -> ",
                "iota_neutral g -> iota_immune (KExpr.app g d) -> ",
                "par_reduces_cd_star the_red_env g P -> par_reduces_cd_star the_red_env d Q -> C) -> ",
                "C"
            )
            .to_string(),
            value_src: Some(format!(
                concat!(
                    "fun (nb : KExpr) (P : KExpr) (Q : KExpr) (C : Type) (hn : iota_neutral nb) ",
                    "(h : par_reduces_cd_star the_red_env nb (KExpr.app P Q)) ",
                    "(k : forall (g : KExpr) (d : KExpr), Eq KExpr nb (KExpr.app g d) -> ",
                    "iota_neutral g -> iota_immune (KExpr.app g d) -> ",
                    "par_reduces_cd_star the_red_env g P -> par_reduces_cd_star the_red_env d Q -> C) => ",
                    // Kont-through-the-motive shape (the single-step-inversion
                    // pattern): the continuation is parameterized by the motive
                    // variable, so the nb-equation is produced at Eq.refl in the
                    // app arm rather than carried as an accumulator.
                    "iota_neutral.rec ",
                    "(fun (x : KExpr) (_h : iota_neutral x) => ",
                    "par_reduces_cd_star the_red_env x (KExpr.app P Q) -> ",
                    "(forall (g : KExpr) (d : KExpr), Eq KExpr x (KExpr.app g d) -> ",
                    "iota_neutral g -> iota_immune (KExpr.app g d) -> ",
                    "par_reduces_cd_star the_red_env g P -> par_reduces_cd_star the_red_env d Q -> C) -> ",
                    "C) ",
                    // const arm: dead-const rigidity pins app P Q = const — absurd.
                    "(fun (m : Name) (vs : ListType Level) (_hw : const_whnf m vs) (hnd : {dd}) => ",
                    "fun (hstar : par_reduces_cd_star the_red_env (KExpr.const m vs) (KExpr.app P Q)) ",
                    "(_k0 : forall (g : KExpr) (d : KExpr), Eq KExpr (KExpr.const m vs) (KExpr.app g d) -> ",
                    "iota_neutral g -> iota_immune (KExpr.app g d) -> ",
                    "par_reduces_cd_star the_red_env g P -> par_reduces_cd_star the_red_env d Q -> C) => ",
                    "Empty.rec (fun (_ : Empty) => C) ",
                    "(Eq.substType KExpr {is_app} (KExpr.app P Q) (KExpr.const m vs) ",
                    "(par_reduces_cd_star_const_dead_inv_eq m vs (KExpr.app P Q) hnd hstar) Nat.zero)) ",
                    // app arm: star app inversion aligns the components.
                    "(fun (f : KExpr) (a : KExpr) (hf : iota_neutral f) ",
                    "(him : iota_immune (KExpr.app f a)) ",
                    "(_ihf : par_reduces_cd_star the_red_env f (KExpr.app P Q) -> ",
                    "(forall (g : KExpr) (d : KExpr), Eq KExpr f (KExpr.app g d) -> ",
                    "iota_neutral g -> iota_immune (KExpr.app g d) -> ",
                    "par_reduces_cd_star the_red_env g P -> par_reduces_cd_star the_red_env d Q -> C) -> ",
                    "C) => ",
                    "fun (hstar : par_reduces_cd_star the_red_env (KExpr.app f a) (KExpr.app P Q)) ",
                    "(k0 : forall (g : KExpr) (d : KExpr), Eq KExpr (KExpr.app f a) (KExpr.app g d) -> ",
                    "iota_neutral g -> iota_immune (KExpr.app g d) -> ",
                    "par_reduces_cd_star the_red_env g P -> par_reduces_cd_star the_red_env d Q -> C) => ",
                    "par_reduces_cd_star_neutral_app_inv_eq f a (KExpr.app P Q) C hf him hstar ",
                    "(iota_neutral_star_to_app_kont P Q f a C k0 hf him)) ",
                    "nb hn h k"
                ),
                dd = delta_dead_eq("m", "vs"),
                is_app = KEXPR_IS_APP,
            )),
            is_axiom: false,
            description: concat!(
                "Neutral-to-app star extraction (mirror WallAIota.neutral_star_app_inv): an ",
                "iota-neutral term whose cd_star reduct is an app is itself a neutral app spine (same ",
                "immunity), components star-reducing to the target's (app_inj aligns them). Const heads ",
                "are refuted by dead-const star rigidity + the inline app/const discriminator. ",
                "DerivedProved, zero axiom_deps. Wall-A completion."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "iota_neutral".to_string(),
                "iota_neutral.rec".to_string(),
                "par_reduces_cd_star".to_string(),
                "par_reduces_cd_star_const_dead_inv_eq".to_string(),
                "par_reduces_cd_star_neutral_app_inv_eq".to_string(),
                "app_inj_fst".to_string(),
                "app_inj_snd".to_string(),
                "KExpr.rec".to_string(),
                "Empty".to_string(),
                "Empty.rec".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
                "Eq.refl".to_string(),
                "the_red_env".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // Named inner continuation for the head-match app arm: transport the
        // recovered spine equation onto y and build HeadMatch.app from the
        // structural IH (heads) + the argument join.
        self.add_definition(SpecDefinition {
            name: "iota_neutral_head_match_kont_inner".to_string(),
            type_src: concat!(
                "forall (f : KExpr) (a : KExpr) (y : KExpr) (f2 : KExpr) (a2 : KExpr), ",
                "(forall (y2 : KExpr) (v2 : KExpr), iota_neutral y2 -> ",
                "par_reduces_cd_star the_red_env f v2 -> par_reduces_cd_star the_red_env y2 v2 -> ",
                "HeadMatch f y2) -> ",
                "par_reduces_cd_star the_red_env f f2 -> par_reduces_cd_star the_red_env a a2 -> ",
                "forall (g : KExpr) (d : KExpr), Eq KExpr y (KExpr.app g d) -> ",
                "iota_neutral g -> iota_immune (KExpr.app g d) -> ",
                "par_reduces_cd_star the_red_env g f2 -> par_reduces_cd_star the_red_env d a2 -> ",
                "HeadMatch (KExpr.app f a) y"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (f : KExpr) (a : KExpr) (y : KExpr) (f2 : KExpr) (a2 : KExpr) ",
                    "(ihf : forall (y2 : KExpr) (v2 : KExpr), iota_neutral y2 -> ",
                    "par_reduces_cd_star the_red_env f v2 -> par_reduces_cd_star the_red_env y2 v2 -> ",
                    "HeadMatch f y2) ",
                    "(hff2 : par_reduces_cd_star the_red_env f f2) ",
                    "(haa2 : par_reduces_cd_star the_red_env a a2) ",
                    "(g : KExpr) (d : KExpr) (heqy : Eq KExpr y (KExpr.app g d)) ",
                    "(hg : iota_neutral g) (_himgd : iota_immune (KExpr.app g d)) ",
                    "(hgf2 : par_reduces_cd_star the_red_env g f2) ",
                    "(hda2 : par_reduces_cd_star the_red_env d a2) => ",
                    "head_match_target_cast_rev (KExpr.app f a) (KExpr.app g d) y heqy ",
                    "(HeadMatch.app f g a d (ihf g f2 hg hff2 hgf2) ",
                    "(cd_star_join_to_def_eq a d a2 haa2 hda2))"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Named inner continuation of iota_neutral_head_match's app arm: transport the ",
                "recovered spine equation onto the neutral counterpart and build HeadMatch.app from ",
                "the structural IH on the heads plus the argument join (cd_star_join_to_def_eq). ",
                "Consumed as a partial application (elaborator nesting-depth discipline). ",
                "DerivedProved, zero axiom_deps. Wall-A completion."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "iota_neutral".to_string(),
                "iota_immune".to_string(),
                "HeadMatch".to_string(),
                "HeadMatch.app".to_string(),
                "head_match_target_cast_rev".to_string(),
                "cd_star_join_to_def_eq".to_string(),
                "par_reduces_cd_star".to_string(),
                "the_red_env".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // Named outer continuation for the head-match app arm: push the
        // counterpart's star leg onto the recovered spine and extract its own
        // spine shape via iota_neutral_star_to_app_inv, finishing with the
        // inner continuation.
        self.add_definition(SpecDefinition {
            name: "iota_neutral_head_match_kont".to_string(),
            type_src: concat!(
                "forall (f : KExpr) (a : KExpr) (y : KExpr) (v : KExpr), ",
                "(forall (y2 : KExpr) (v2 : KExpr), iota_neutral y2 -> ",
                "par_reduces_cd_star the_red_env f v2 -> par_reduces_cd_star the_red_env y2 v2 -> ",
                "HeadMatch f y2) -> ",
                "iota_neutral y -> par_reduces_cd_star the_red_env y v -> ",
                "forall (f2 : KExpr) (a2 : KExpr), Eq KExpr v (KExpr.app f2 a2) -> ",
                "par_reduces_cd_star the_red_env f f2 -> par_reduces_cd_star the_red_env a a2 -> ",
                "iota_neutral f2 -> iota_immune (KExpr.app f2 a2) -> ",
                "HeadMatch (KExpr.app f a) y"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (f : KExpr) (a : KExpr) (y : KExpr) (v : KExpr) ",
                    "(ihf : forall (y2 : KExpr) (v2 : KExpr), iota_neutral y2 -> ",
                    "par_reduces_cd_star the_red_env f v2 -> par_reduces_cd_star the_red_env y2 v2 -> ",
                    "HeadMatch f y2) ",
                    "(hy : iota_neutral y) (hyv : par_reduces_cd_star the_red_env y v) ",
                    "(f2 : KExpr) (a2 : KExpr) (eqv : Eq KExpr v (KExpr.app f2 a2)) ",
                    "(hff2 : par_reduces_cd_star the_red_env f f2) ",
                    "(haa2 : par_reduces_cd_star the_red_env a a2) ",
                    "(_hn2 : iota_neutral f2) (_him2 : iota_immune (KExpr.app f2 a2)) => ",
                    "iota_neutral_star_to_app_inv y f2 a2 (HeadMatch (KExpr.app f a) y) hy ",
                    "(par_reduces_cd_star_target_cast y v (KExpr.app f2 a2) eqv hyv) ",
                    "(iota_neutral_head_match_kont_inner f a y f2 a2 ihf hff2 haa2)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Named outer continuation of iota_neutral_head_match's app arm: cast the ",
                "counterpart's star leg onto the recovered spine (par_reduces_cd_star_target_cast), ",
                "extract the counterpart's own spine shape (iota_neutral_star_to_app_inv) and finish ",
                "with the inner continuation. Consumed as a partial application (elaborator ",
                "nesting-depth discipline). DerivedProved, zero axiom_deps. Wall-A completion."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "iota_neutral".to_string(),
                "iota_immune".to_string(),
                "HeadMatch".to_string(),
                "iota_neutral_star_to_app_inv".to_string(),
                "iota_neutral_head_match_kont_inner".to_string(),
                "par_reduces_cd_star_target_cast".to_string(),
                "par_reduces_cd_star".to_string(),
                "the_red_env".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // iota_neutral_head_match: two neutral terms meeting at a common
        // cd_star reduct HeadMatch (mirror neutral_headMatch) — the neutral
        // half of the completeness case split.
        self.add_definition(SpecDefinition {
            name: "iota_neutral_head_match".to_string(),
            type_src: concat!(
                "forall (na : KExpr) (nb : KExpr) (w : KExpr), iota_neutral na -> iota_neutral nb -> ",
                "par_reduces_cd_star the_red_env na w -> par_reduces_cd_star the_red_env nb w -> ",
                "HeadMatch na nb"
            )
            .to_string(),
            value_src: Some(format!(
                concat!(
                    "fun (na : KExpr) (nb : KExpr) (w : KExpr) (hna : iota_neutral na) ",
                    "(hnb : iota_neutral nb) ",
                    "(hnaw : par_reduces_cd_star the_red_env na w) ",
                    "(hnbw : par_reduces_cd_star the_red_env nb w) => ",
                    "iota_neutral.rec ",
                    "(fun (x : KExpr) (_h : iota_neutral x) => ",
                    "forall (y : KExpr) (v : KExpr), iota_neutral y -> ",
                    "par_reduces_cd_star the_red_env x v -> par_reduces_cd_star the_red_env y v -> ",
                    "HeadMatch x y) ",
                    // const arm: v = const (dead-const rigidity), y = const
                    // (neutral-to-const extraction), HeadMatch.const cast onto y.
                    // Intermediate equations bound via applied lambdas (nesting
                    // discipline).
                    "(fun (m : Name) (vs : ListType Level) (hw : const_whnf m vs) (hnd : {dd}) => ",
                    "fun (y : KExpr) (v : KExpr) (hy : iota_neutral y) ",
                    "(hxv : par_reduces_cd_star the_red_env (KExpr.const m vs) v) ",
                    "(hyv : par_reduces_cd_star the_red_env y v) => ",
                    "(fun (hveq : Eq KExpr v (KExpr.const m vs)) => ",
                    "(fun (hyeq : Eq KExpr y (KExpr.const m vs)) => ",
                    "head_match_target_cast_rev (KExpr.const m vs) (KExpr.const m vs) y hyeq ",
                    "(HeadMatch.const m vs hw)) ",
                    "(iota_neutral_star_const_inv_eq y m vs hy ",
                    "(par_reduces_cd_star_target_cast y v (KExpr.const m vs) hveq hyv))) ",
                    "(par_reduces_cd_star_const_dead_inv_eq m vs v hnd hxv)) ",
                    // app arm: invert the x-leg at the shared reduct and finish
                    // with the named outer continuation (partial application).
                    "(fun (f : KExpr) (a : KExpr) (hf : iota_neutral f) ",
                    "(him : iota_immune (KExpr.app f a)) ",
                    "(ihf : forall (y2 : KExpr) (v2 : KExpr), iota_neutral y2 -> ",
                    "par_reduces_cd_star the_red_env f v2 -> par_reduces_cd_star the_red_env y2 v2 -> ",
                    "HeadMatch f y2) => ",
                    "fun (y : KExpr) (v : KExpr) (hy : iota_neutral y) ",
                    "(hxv : par_reduces_cd_star the_red_env (KExpr.app f a) v) ",
                    "(hyv : par_reduces_cd_star the_red_env y v) => ",
                    "par_reduces_cd_star_neutral_app_inv_eq f a v (HeadMatch (KExpr.app f a) y) ",
                    "hf him hxv ",
                    "(iota_neutral_head_match_kont f a y v ihf hy hyv)) ",
                    "na hna nb w hnb hnaw hnbw"
                ),
                dd = delta_dead_eq("m", "vs"),
            )),
            is_axiom: false,
            description: concat!(
                "Neutral-vs-neutral HeadMatch extraction (mirror WallAIota.neutral_headMatch): two ",
                "iota-neutral terms meeting at a common cd_star reduct match head-for-head — const ",
                "heads collapse by dead-const rigidity + neutral-to-const extraction; app spines ",
                "invert on both legs at the shared reduct (named kont helpers, partial-application ",
                "discipline), recurse on the heads (structural IH) and join the arguments into DefEq. ",
                "The neutral half of def_eq_whnf_complete. DerivedProved, zero axiom_deps. ",
                "Wall-A completion."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "iota_neutral".to_string(),
                "iota_neutral.rec".to_string(),
                "HeadMatch".to_string(),
                "HeadMatch.const".to_string(),
                "par_reduces_cd_star".to_string(),
                "par_reduces_cd_star_const_dead_inv_eq".to_string(),
                "par_reduces_cd_star_neutral_app_inv_eq".to_string(),
                "par_reduces_cd_star_target_cast".to_string(),
                "head_match_target_cast_rev".to_string(),
                "iota_neutral_star_const_inv_eq".to_string(),
                "iota_neutral_head_match_kont".to_string(),
                "const_whnf".to_string(),
                "the_red_env".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    /// Brick 6: the iota-aware WHNF shape lemmas — the mirror's
    /// `whnf_star_sort/lam/pi` and `whnf_star_to_neutral` over
    /// `par_reduces_cd_star` (case split on `iota_whnf` + the reused
    /// sort/lam/pi star inversions + the Brick-5 neutral machinery).
    fn add_wall_a_whnf_shape(&mut self) -> Result<(), SpecError> {
        // iota_whnf_star_sort_inv_eq.
        self.add_definition(SpecDefinition {
            name: "iota_whnf_star_sort_inv_eq".to_string(),
            type_src: concat!(
                "forall (e : KExpr) (n : Level), iota_whnf e -> ",
                "par_reduces_cd_star the_red_env e (KExpr.sort n) -> Eq KExpr e (KExpr.sort n)"
            )
            .to_string(),
            value_src: Some(format!(
                concat!(
                    "fun (e : KExpr) (n : Level) (hw : iota_whnf e) ",
                    "(h : par_reduces_cd_star the_red_env e (KExpr.sort n)) => ",
                    "iota_whnf.rec ",
                    "(fun (x : KExpr) (_h : iota_whnf x) => ",
                    "par_reduces_cd_star the_red_env x (KExpr.sort n) -> Eq KExpr x (KExpr.sort n)) ",
                    // sort
                    "(fun (m : Level) => ",
                    "fun (hstar : par_reduces_cd_star the_red_env (KExpr.sort m) (KExpr.sort n)) => ",
                    "Eq.symm KExpr (KExpr.sort n) (KExpr.sort m) ",
                    "(par_reduces_cd_star_sort_inv_eq the_red_env m (KExpr.sort n) hstar)) ",
                    // lam
                    "(fun (ty : KExpr) (body : KExpr) => ",
                    "fun (hstar : par_reduces_cd_star the_red_env (KExpr.lam ty body) (KExpr.sort n)) => ",
                    "Empty.rec (fun (_ : Empty) => Eq KExpr (KExpr.lam ty body) (KExpr.sort n)) ",
                    "(par_reduces_cd_star_lam_inv_eq the_red_env ty body (KExpr.sort n) Empty hstar ",
                    "(fun (ty2 : KExpr) (body2 : KExpr) ",
                    "(eqw : Eq KExpr (KExpr.sort n) (KExpr.lam ty2 body2)) ",
                    "(_h1 : par_reduces_cd_star the_red_env ty ty2) ",
                    "(_h2 : par_reduces_cd_star the_red_env body body2) => ",
                    "Eq.substType KExpr {is_sort} (KExpr.sort n) (KExpr.lam ty2 body2) eqw Nat.zero))) ",
                    // pi
                    "(fun (dom : KExpr) (body : KExpr) => ",
                    "fun (hstar : par_reduces_cd_star the_red_env (KExpr.pi dom body) (KExpr.sort n)) => ",
                    "Empty.rec (fun (_ : Empty) => Eq KExpr (KExpr.pi dom body) (KExpr.sort n)) ",
                    "(par_reduces_cd_star_pi_inv_eq the_red_env dom body (KExpr.sort n) Empty hstar ",
                    "(fun (dom2 : KExpr) (body2 : KExpr) ",
                    "(eqw : Eq KExpr (KExpr.sort n) (KExpr.pi dom2 body2)) ",
                    "(_h1 : par_reduces_cd_star the_red_env dom dom2) ",
                    "(_h2 : par_reduces_cd_star the_red_env body body2) => ",
                    "Eq.substType KExpr {is_sort} (KExpr.sort n) (KExpr.pi dom2 body2) eqw Nat.zero))) ",
                    // neutral
                    "(fun (x : KExpr) (hn : iota_neutral x) => ",
                    "fun (hstar : par_reduces_cd_star the_red_env x (KExpr.sort n)) => ",
                    "iota_neutral_sort_absurd n (Eq KExpr x (KExpr.sort n)) ",
                    "(iota_neutral_cd_star x (KExpr.sort n) hn hstar)) ",
                    "e hw h"
                ),
                is_sort = KEXPR_IS_SORT,
            )),
            is_axiom: false,
            description: concat!(
                "Iota-aware WHNF shape rigidity at sort (mirror WallAIota.whnf_star_sort): an ",
                "iota_whnf whose cd_star reduct is a sort IS that sort. Sort heads by star sort ",
                "rigidity; lam/pi refuted through their star inversions + inline discriminators; ",
                "neutral heads via neutrality preservation + iota_neutral_sort_absurd. DerivedProved, ",
                "zero axiom_deps. Wall-A completion."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "iota_whnf".to_string(),
                "iota_whnf.rec".to_string(),
                "par_reduces_cd_star_sort_inv_eq".to_string(),
                "par_reduces_cd_star_lam_inv_eq".to_string(),
                "par_reduces_cd_star_pi_inv_eq".to_string(),
                "iota_neutral_cd_star".to_string(),
                "iota_neutral_sort_absurd".to_string(),
                "KExpr.rec".to_string(),
                "Empty".to_string(),
                "Empty.rec".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
                "the_red_env".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // iota_whnf_star_lam_inv_eq / iota_whnf_star_pi_inv_eq — the two
        // binder shapes, generated symmetrically.
        for (name, head, other_head, own_inv, other_inv, inj_fst, inj_snd, other_ne, absurd) in [
            (
                "iota_whnf_star_lam_inv_eq",
                "KExpr.lam",
                "KExpr.pi",
                "par_reduces_cd_star_lam_inv_eq",
                "par_reduces_cd_star_pi_inv_eq",
                "lam_inj_fst",
                "lam_inj_snd",
                "pi_ne_lam",
                "iota_neutral_lam_absurd_type",
            ),
            (
                "iota_whnf_star_pi_inv_eq",
                "KExpr.pi",
                "KExpr.lam",
                "par_reduces_cd_star_pi_inv_eq",
                "par_reduces_cd_star_lam_inv_eq",
                "pi_inj_fst",
                "pi_inj_snd",
                "lam_ne_pi",
                "iota_neutral_pi_absurd_type",
            ),
        ] {
            // Named continuation for the genuine binder arm (partial-application
            // discipline): align the inverted components with the target's via
            // binder injectivity + the named target casts.
            let kont_name = format!("{name}_kont");
            self.add_definition(SpecDefinition {
                name: kont_name.clone(),
                type_src: format!(
                    concat!(
                        "forall (A : KExpr) (b : KExpr) (ty : KExpr) (body : KExpr) (C : Type), ",
                        "(forall (A2 : KExpr) (b2 : KExpr), ",
                        "Eq KExpr ({head} ty body) ({head} A2 b2) -> ",
                        "par_reduces_cd_star the_red_env A2 A -> par_reduces_cd_star the_red_env b2 b -> C) -> ",
                        "forall (ty2 : KExpr) (body2 : KExpr), ",
                        "Eq KExpr ({head} A b) ({head} ty2 body2) -> ",
                        "par_reduces_cd_star the_red_env ty ty2 -> ",
                        "par_reduces_cd_star the_red_env body body2 -> C"
                    ),
                    head = head,
                ),
                value_src: Some(format!(
                    concat!(
                        "fun (A : KExpr) (b : KExpr) (ty : KExpr) (body : KExpr) (C : Type) ",
                        "(k0 : forall (A2 : KExpr) (b2 : KExpr), ",
                        "Eq KExpr ({head} ty body) ({head} A2 b2) -> ",
                        "par_reduces_cd_star the_red_env A2 A -> par_reduces_cd_star the_red_env b2 b -> C) ",
                        "(ty2 : KExpr) (body2 : KExpr) ",
                        "(eqw : Eq KExpr ({head} A b) ({head} ty2 body2)) ",
                        "(hty : par_reduces_cd_star the_red_env ty ty2) ",
                        "(hbody : par_reduces_cd_star the_red_env body body2) => ",
                        // Applied-lambda double-bind (nesting discipline).
                        "(fun (eA : Eq KExpr A ty2) (eB : Eq KExpr b body2) => ",
                        "(fun (legA : par_reduces_cd_star the_red_env ty A) ",
                        "(legB : par_reduces_cd_star the_red_env body b) => ",
                        "k0 ty body (Eq.refl KExpr ({head} ty body)) legA legB) ",
                        "(par_reduces_cd_star_target_cast_rev ty ty2 A eA hty) ",
                        "(par_reduces_cd_star_target_cast_rev body body2 b eB hbody)) ",
                        "({inj_fst} A b ty2 body2 eqw) ",
                        "({inj_snd} A b ty2 body2 eqw)"
                    ),
                    head = head,
                    inj_fst = inj_fst,
                    inj_snd = inj_snd,
                )),
                is_axiom: false,
                description: format!(
                    concat!(
                        "Named continuation of {name}'s genuine {head} arm: align the inverted binder ",
                        "components with the target's via {inj_fst}/{inj_snd} + the named target casts, ",
                        "re-entering the caller's continuation at the binder itself (Eq.refl). Consumed as ",
                        "a partial application (elaborator nesting-depth discipline). DerivedProved, zero ",
                        "axiom_deps. Wall-A completion."
                    ),
                    name = name,
                    head = head,
                    inj_fst = inj_fst,
                    inj_snd = inj_snd,
                ),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "par_reduces_cd_star".to_string(),
                    "par_reduces_cd_star_target_cast_rev".to_string(),
                    inj_fst.to_string(),
                    inj_snd.to_string(),
                    "Eq.refl".to_string(),
                    "the_red_env".to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;

            // Arm bodies: the whnf case split. For the lam lemma the genuine
            // arm is lam and the refuted binder arm is pi (and vice versa).
            let genuine_arm = format!(
                concat!(
                    "(fun (ty : KExpr) (body : KExpr) => ",
                    "fun (hstar : par_reduces_cd_star the_red_env ({head} ty body) ({head} A b)) ",
                    "(k0 : forall (A2 : KExpr) (b2 : KExpr), ",
                    "Eq KExpr ({head} ty body) ({head} A2 b2) -> ",
                    "par_reduces_cd_star the_red_env A2 A -> par_reduces_cd_star the_red_env b2 b -> C) => ",
                    "{own_inv} the_red_env ty body ({head} A b) C hstar ",
                    "({kont_name} A b ty body C k0)) "
                ),
                head = head,
                own_inv = own_inv,
                kont_name = kont_name,
            );
            let other_binder_arm = format!(
                concat!(
                    "(fun (dom : KExpr) (body : KExpr) => ",
                    "fun (hstar : par_reduces_cd_star the_red_env ({other_head} dom body) ({head} A b)) ",
                    "(_k : forall (A2 : KExpr) (b2 : KExpr), ",
                    "Eq KExpr ({other_head} dom body) ({head} A2 b2) -> ",
                    "par_reduces_cd_star the_red_env A2 A -> par_reduces_cd_star the_red_env b2 b -> C) => ",
                    "{other_inv} the_red_env dom body ({head} A b) C hstar ",
                    "(fun (dom2 : KExpr) (body2 : KExpr) ",
                    "(eqw : Eq KExpr ({head} A b) ({other_head} dom2 body2)) ",
                    "(_h1 : par_reduces_cd_star the_red_env dom dom2) ",
                    "(_h2 : par_reduces_cd_star the_red_env body body2) => ",
                    "{other_ne} dom2 body2 A b C ",
                    "(Eq.symm KExpr ({head} A b) ({other_head} dom2 body2) eqw))) "
                ),
                head = head,
                other_head = other_head,
                other_inv = other_inv,
                other_ne = other_ne,
            );
            let sort_arm = format!(
                concat!(
                    "(fun (m : Level) => ",
                    "fun (hstar : par_reduces_cd_star the_red_env (KExpr.sort m) ({head} A b)) ",
                    "(_k : forall (A2 : KExpr) (b2 : KExpr), ",
                    "Eq KExpr (KExpr.sort m) ({head} A2 b2) -> ",
                    "par_reduces_cd_star the_red_env A2 A -> par_reduces_cd_star the_red_env b2 b -> C) => ",
                    "Empty.rec (fun (_ : Empty) => C) ",
                    "(Eq.substType KExpr {not_sort} ({head} A b) (KExpr.sort m) ",
                    "(par_reduces_cd_star_sort_inv_eq the_red_env m ({head} A b) hstar) Nat.zero)) "
                ),
                head = head,
                not_sort = KEXPR_NOT_SORT,
            );
            let neutral_arm = format!(
                concat!(
                    "(fun (x : KExpr) (hn : iota_neutral x) => ",
                    "fun (hstar : par_reduces_cd_star the_red_env x ({head} A b)) ",
                    "(_k : forall (A2 : KExpr) (b2 : KExpr), ",
                    "Eq KExpr x ({head} A2 b2) -> ",
                    "par_reduces_cd_star the_red_env A2 A -> par_reduces_cd_star the_red_env b2 b -> C) => ",
                    "{absurd} A b C (iota_neutral_cd_star x ({head} A b) hn hstar))"
                ),
                head = head,
                absurd = absurd,
            );
            // Assemble in iota_whnf ctor order: sort, lam, pi, neutral.
            let (lam_slot, pi_slot) = if head == "KExpr.lam" {
                (genuine_arm, other_binder_arm)
            } else {
                (other_binder_arm, genuine_arm)
            };

            self.add_definition(SpecDefinition {
                name: name.to_string(),
                type_src: format!(
                    concat!(
                        "forall (e : KExpr) (A : KExpr) (b : KExpr) (C : Type), iota_whnf e -> ",
                        "par_reduces_cd_star the_red_env e ({head} A b) -> ",
                        "(forall (A2 : KExpr) (b2 : KExpr), Eq KExpr e ({head} A2 b2) -> ",
                        "par_reduces_cd_star the_red_env A2 A -> par_reduces_cd_star the_red_env b2 b -> C) -> ",
                        "C"
                    ),
                    head = head,
                ),
                value_src: Some(format!(
                    concat!(
                        "fun (e : KExpr) (A : KExpr) (b : KExpr) (C : Type) (hw : iota_whnf e) ",
                        "(h : par_reduces_cd_star the_red_env e ({head} A b)) ",
                        "(k : forall (A2 : KExpr) (b2 : KExpr), Eq KExpr e ({head} A2 b2) -> ",
                        "par_reduces_cd_star the_red_env A2 A -> par_reduces_cd_star the_red_env b2 b -> C) => ",
                        "iota_whnf.rec ",
                        "(fun (x : KExpr) (_h : iota_whnf x) => ",
                        "par_reduces_cd_star the_red_env x ({head} A b) -> ",
                        "(forall (A2 : KExpr) (b2 : KExpr), Eq KExpr x ({head} A2 b2) -> ",
                        "par_reduces_cd_star the_red_env A2 A -> par_reduces_cd_star the_red_env b2 b -> C) -> ",
                        "C) ",
                        "{sort_arm}{lam_slot}{pi_slot}{neutral_arm} ",
                        "e hw h k"
                    ),
                    head = head,
                    sort_arm = sort_arm,
                    lam_slot = lam_slot,
                    pi_slot = pi_slot,
                    neutral_arm = neutral_arm,
                )),
                is_axiom: false,
                description: format!(
                    concat!(
                        "Iota-aware WHNF shape inversion at a {head} target (mirror ",
                        "WallAIota.whnf_star_{{lam,pi}}): an iota_whnf whose cd_star reduct is a {head} is ",
                        "itself that binder, components star-reducing to the target's (via {own_inv} + binder ",
                        "injectivity). Sort/other-binder arms refuted by rigidity + discriminators; neutral ",
                        "arm by neutrality preservation + {absurd}. DerivedProved, zero axiom_deps. ",
                        "Wall-A completion."
                    ),
                    head = head,
                    own_inv = own_inv,
                    absurd = absurd,
                ),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "iota_whnf".to_string(),
                    "iota_whnf.rec".to_string(),
                    own_inv.to_string(),
                    other_inv.to_string(),
                    kont_name,
                    "par_reduces_cd_star_sort_inv_eq".to_string(),
                    other_ne.to_string(),
                    absurd.to_string(),
                    "iota_neutral_cd_star".to_string(),
                    "KExpr.rec".to_string(),
                    "Empty".to_string(),
                    "Empty.rec".to_string(),
                    "Eq.substType".to_string(),
                    "Eq.symm".to_string(),
                    "the_red_env".to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }

        // iota_whnf_star_to_neutral: whnf-shape preservation back from a
        // neutral reduct (mirror whnf_star_to_neutral).
        self.add_definition(SpecDefinition {
            name: "iota_whnf_star_to_neutral".to_string(),
            type_src: concat!(
                "forall (e : KExpr) (w : KExpr), iota_whnf e -> ",
                "par_reduces_cd_star the_red_env e w -> iota_neutral w -> iota_neutral e"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (e : KExpr) (w : KExpr) (hw : iota_whnf e) ",
                    "(h : par_reduces_cd_star the_red_env e w) (hnw : iota_neutral w) => ",
                    "iota_whnf.rec ",
                    "(fun (x : KExpr) (_h : iota_whnf x) => ",
                    "forall (v : KExpr), par_reduces_cd_star the_red_env x v -> iota_neutral v -> ",
                    "iota_neutral x) ",
                    // sort: the reduct is the sort — a neutral sort is absurd.
                    "(fun (m : Level) => ",
                    "fun (v : KExpr) (hstar : par_reduces_cd_star the_red_env (KExpr.sort m) v) ",
                    "(hnv : iota_neutral v) => ",
                    "iota_neutral_sort_absurd_type m (iota_neutral (KExpr.sort m)) ",
                    "(Eq.substType KExpr (fun (z : KExpr) => iota_neutral z) v (KExpr.sort m) ",
                    "(par_reduces_cd_star_sort_inv_eq the_red_env m v hstar) hnv)) ",
                    // lam: the reduct is a lam — a neutral lam is absurd.
                    "(fun (ty : KExpr) (body : KExpr) => ",
                    "fun (v : KExpr) (hstar : par_reduces_cd_star the_red_env (KExpr.lam ty body) v) ",
                    "(hnv : iota_neutral v) => ",
                    "par_reduces_cd_star_lam_inv_eq the_red_env ty body v (iota_neutral (KExpr.lam ty body)) hstar ",
                    "(fun (ty2 : KExpr) (body2 : KExpr) (eqv : Eq KExpr v (KExpr.lam ty2 body2)) ",
                    "(_h1 : par_reduces_cd_star the_red_env ty ty2) ",
                    "(_h2 : par_reduces_cd_star the_red_env body body2) => ",
                    "iota_neutral_lam_absurd_type ty2 body2 (iota_neutral (KExpr.lam ty body)) ",
                    "(Eq.substType KExpr (fun (z : KExpr) => iota_neutral z) v (KExpr.lam ty2 body2) eqv hnv))) ",
                    // pi: symmetric.
                    "(fun (dom : KExpr) (body : KExpr) => ",
                    "fun (v : KExpr) (hstar : par_reduces_cd_star the_red_env (KExpr.pi dom body) v) ",
                    "(hnv : iota_neutral v) => ",
                    "par_reduces_cd_star_pi_inv_eq the_red_env dom body v (iota_neutral (KExpr.pi dom body)) hstar ",
                    "(fun (dom2 : KExpr) (body2 : KExpr) (eqv : Eq KExpr v (KExpr.pi dom2 body2)) ",
                    "(_h1 : par_reduces_cd_star the_red_env dom dom2) ",
                    "(_h2 : par_reduces_cd_star the_red_env body body2) => ",
                    "iota_neutral_pi_absurd_type dom2 body2 (iota_neutral (KExpr.pi dom body)) ",
                    "(Eq.substType KExpr (fun (z : KExpr) => iota_neutral z) v (KExpr.pi dom2 body2) eqv hnv))) ",
                    // neutral: already neutral.
                    "(fun (x : KExpr) (hn : iota_neutral x) => ",
                    "fun (v : KExpr) (_hstar : par_reduces_cd_star the_red_env x v) ",
                    "(_hnv : iota_neutral v) => hn) ",
                    "e hw w h hnw"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Iota-aware WHNF-to-neutral transfer (mirror WallAIota.whnf_star_to_neutral): if an ",
                "iota_whnf star-reduces to an iota-neutral term, the whnf was neutral to begin with ",
                "(sort/lam/pi cases refuted by rigidity/inversion + the shape absurds). DerivedProved, ",
                "zero axiom_deps. Wall-A completion."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "iota_whnf".to_string(),
                "iota_whnf.rec".to_string(),
                "iota_neutral".to_string(),
                "par_reduces_cd_star_sort_inv_eq".to_string(),
                "par_reduces_cd_star_lam_inv_eq".to_string(),
                "par_reduces_cd_star_pi_inv_eq".to_string(),
                "iota_neutral_sort_absurd_type".to_string(),
                "iota_neutral_lam_absurd_type".to_string(),
                "iota_neutral_pi_absurd_type".to_string(),
                "Eq.substType".to_string(),
                "the_red_env".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    /// Brick 7: THE TARGET — `def_eq_whnf_complete` (mirror
    /// `WallAIota.def_eq_whnf_complete`): completeness of the algorithmic
    /// def-eq decision over the FULL β+ι+δ+ζ reduction, on `whnf_to` legs whose
    /// targets are iota-aware whnfs.
    fn add_wall_a_completeness_target(&mut self) -> Result<(), SpecError> {
        // Named binder-arm continuations for the completeness case split
        // (partial-application discipline): inner = build the HeadMatch from
        // the two component joins and cast onto nb; outer = push nb's star leg
        // onto the recovered binder and extract nb's own binder shape.
        for (label, head, ctor, own_whnf_inv) in [
            (
                "lam",
                "KExpr.lam",
                "HeadMatch.lam",
                "iota_whnf_star_lam_inv_eq",
            ),
            ("pi", "KExpr.pi", "HeadMatch.pi", "iota_whnf_star_pi_inv_eq"),
        ] {
            let inner_name = format!("def_eq_whnf_complete_{label}_kont_inner");
            let outer_name = format!("def_eq_whnf_complete_{label}_kont");
            self.add_definition(SpecDefinition {
                name: inner_name.clone(),
                type_src: format!(
                    concat!(
                        "forall (ty : KExpr) (body : KExpr) (nb : KExpr) (A1 : KExpr) (b1 : KExpr), ",
                        "par_reduces_cd_star the_red_env ty A1 -> ",
                        "par_reduces_cd_star the_red_env body b1 -> ",
                        "forall (A2 : KExpr) (b2 : KExpr), Eq KExpr nb ({head} A2 b2) -> ",
                        "par_reduces_cd_star the_red_env A2 A1 -> par_reduces_cd_star the_red_env b2 b1 -> ",
                        "HeadMatch ({head} ty body) nb"
                    ),
                    head = head,
                ),
                value_src: Some(format!(
                    concat!(
                        "fun (ty : KExpr) (body : KExpr) (nb : KExpr) (A1 : KExpr) (b1 : KExpr) ",
                        "(hA : par_reduces_cd_star the_red_env ty A1) ",
                        "(hb1 : par_reduces_cd_star the_red_env body b1) ",
                        "(A2 : KExpr) (b2 : KExpr) (eqnb : Eq KExpr nb ({head} A2 b2)) ",
                        "(hA2 : par_reduces_cd_star the_red_env A2 A1) ",
                        "(hb2 : par_reduces_cd_star the_red_env b2 b1) => ",
                        "head_match_target_cast_rev ({head} ty body) ({head} A2 b2) nb eqnb ",
                        "({ctor} ty A2 body b2 ",
                        "(cd_star_join_to_def_eq ty A2 A1 hA hA2) ",
                        "(cd_star_join_to_def_eq body b2 b1 hb1 hb2))"
                    ),
                    head = head,
                    ctor = ctor,
                )),
                is_axiom: false,
                description: format!(
                    concat!(
                        "Named inner continuation of def_eq_whnf_complete's {label} arm: both sides' ",
                        "binder components join at the meet (cd_star_join_to_def_eq), building ",
                        "{ctor}; the result is cast onto nb. Consumed as a partial application ",
                        "(elaborator nesting-depth discipline). DerivedProved, zero axiom_deps. ",
                        "Wall-A completion."
                    ),
                    label = label,
                    ctor = ctor,
                ),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "HeadMatch".to_string(),
                    ctor.to_string(),
                    "head_match_target_cast_rev".to_string(),
                    "cd_star_join_to_def_eq".to_string(),
                    "par_reduces_cd_star".to_string(),
                    "the_red_env".to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;

            self.add_definition(SpecDefinition {
                name: outer_name,
                type_src: format!(
                    concat!(
                        "forall (ty : KExpr) (body : KExpr) (nb : KExpr), iota_whnf nb -> ",
                        "forall (v : KExpr), par_reduces_cd_star the_red_env nb v -> ",
                        "forall (A1 : KExpr) (b1 : KExpr), Eq KExpr v ({head} A1 b1) -> ",
                        "par_reduces_cd_star the_red_env ty A1 -> ",
                        "par_reduces_cd_star the_red_env body b1 -> ",
                        "HeadMatch ({head} ty body) nb"
                    ),
                    head = head,
                ),
                value_src: Some(format!(
                    concat!(
                        "fun (ty : KExpr) (body : KExpr) (nb : KExpr) (wb : iota_whnf nb) ",
                        "(v : KExpr) (hnbv : par_reduces_cd_star the_red_env nb v) ",
                        "(A1 : KExpr) (b1 : KExpr) (eqv : Eq KExpr v ({head} A1 b1)) ",
                        "(hA : par_reduces_cd_star the_red_env ty A1) ",
                        "(hb1 : par_reduces_cd_star the_red_env body b1) => ",
                        "{own_whnf_inv} nb A1 b1 (HeadMatch ({head} ty body) nb) wb ",
                        "(par_reduces_cd_star_target_cast nb v ({head} A1 b1) eqv hnbv) ",
                        "({inner} ty body nb A1 b1 hA hb1)"
                    ),
                    head = head,
                    own_whnf_inv = own_whnf_inv,
                    inner = inner_name,
                )),
                is_axiom: false,
                description: format!(
                    concat!(
                        "Named outer continuation of def_eq_whnf_complete's {label} arm: cast nb's star ",
                        "leg onto the recovered binder shape, extract nb's own {label} shape ",
                        "({own_whnf_inv}) and finish with the inner continuation. Consumed as a partial ",
                        "application (elaborator nesting-depth discipline). DerivedProved, zero ",
                        "axiom_deps. Wall-A completion."
                    ),
                    label = label,
                    own_whnf_inv = own_whnf_inv,
                ),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "HeadMatch".to_string(),
                    "iota_whnf".to_string(),
                    own_whnf_inv.to_string(),
                    inner_name,
                    "par_reduces_cd_star_target_cast".to_string(),
                    "par_reduces_cd_star".to_string(),
                    "the_red_env".to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }

        // The case-split body: iota_whnf.rec on the na-side whnf shape, run at
        // the meet w with the two star legs na =>* w, nb =>* w.
        let body: String = concat!(
                // Bind the two composed star legs as VARIABLES before the
                // iota_whnf.rec application (applied-lambda binding), so the
                // recursor's trailing extras are variables — the empirically
                // robust shape for the elaborator's recursor handling.
                "(fun (naw : par_reduces_cd_star the_red_env na w) ",
                "(nbw : par_reduces_cd_star the_red_env nb w) => ",
                "iota_whnf.rec ",
                "(fun (x : KExpr) (_h : iota_whnf x) => ",
                "forall (v : KExpr), par_reduces_cd_star the_red_env x v -> ",
                "par_reduces_cd_star the_red_env nb v -> HeadMatch x nb) ",
                // sort arm (applied-lambda-bound intermediate equations)
                "(fun (sn : Level) => ",
                "fun (v : KExpr) (hxv : par_reduces_cd_star the_red_env (KExpr.sort sn) v) ",
                "(hnbv : par_reduces_cd_star the_red_env nb v) => ",
                "(fun (hveq : Eq KExpr v (KExpr.sort sn)) => ",
                "(fun (hnbs : par_reduces_cd_star the_red_env nb (KExpr.sort sn)) => ",
                "(fun (hnbeq : Eq KExpr nb (KExpr.sort sn)) => ",
                "head_match_target_cast_rev (KExpr.sort sn) (KExpr.sort sn) nb hnbeq ",
                "(HeadMatch.sort sn)) ",
                "(iota_whnf_star_sort_inv_eq nb sn wb hnbs)) ",
                "(par_reduces_cd_star_target_cast nb v (KExpr.sort sn) hveq hnbv)) ",
                "(par_reduces_cd_star_sort_inv_eq the_red_env sn v hxv)) ",
                // lam arm (named kont, partial application)
                "(fun (ty : KExpr) (body : KExpr) => ",
                "fun (v : KExpr) (hxv : par_reduces_cd_star the_red_env (KExpr.lam ty body) v) ",
                "(hnbv : par_reduces_cd_star the_red_env nb v) => ",
                "par_reduces_cd_star_lam_inv_eq the_red_env ty body v (HeadMatch (KExpr.lam ty body) nb) hxv ",
                "(def_eq_whnf_complete_lam_kont ty body nb wb v hnbv)) ",
                // pi arm (named kont, partial application)
                "(fun (dom : KExpr) (body : KExpr) => ",
                "fun (v : KExpr) (hxv : par_reduces_cd_star the_red_env (KExpr.pi dom body) v) ",
                "(hnbv : par_reduces_cd_star the_red_env nb v) => ",
                "par_reduces_cd_star_pi_inv_eq the_red_env dom body v (HeadMatch (KExpr.pi dom body) nb) hxv ",
                "(def_eq_whnf_complete_pi_kont dom body nb wb v hnbv)) ",
                // neutral arm (applied-lambda-bound neutrality of the meet)
                "(fun (x : KExpr) (hn : iota_neutral x) => ",
                "fun (v : KExpr) (hxv : par_reduces_cd_star the_red_env x v) ",
                "(hnbv : par_reduces_cd_star the_red_env nb v) => ",
                "(fun (hwn : iota_neutral v) => ",
                "iota_neutral_head_match x nb v hn ",
                "(iota_whnf_star_to_neutral nb v wb hnbv hwn) hxv hnbv) ",
                "(iota_neutral_cd_star x v hn hxv)) ",
                "na wa w naw nbw) ",
                "(par_reduces_cd_star_trans the_red_env na p1 w hnap1 hp1w) ",
                "(par_reduces_cd_star_trans the_red_env nb p2 w hnbp2 hp2w)"
        )
        .to_string();

        self.add_definition(SpecDefinition {
            name: "def_eq_whnf_complete".to_string(),
            type_src: format!(
                concat!(
                    "forall {ib}",
                    "(a : KExpr) (b : KExpr) (na : KExpr) (nb : KExpr), ",
                    "DefEq a b -> whnf_to a na -> whnf_to b nb -> ",
                    "iota_whnf na -> iota_whnf nb -> ",
                    "HeadMatch na nb"
                ),
                ib = I_BINDERS,
            ),
            value_src: Some(format!(
                concat!(
                    "fun {ib}",
                    "(a : KExpr) (b : KExpr) (na : KExpr) (nb : KExpr) ",
                    "(h : DefEq a b) (ha : whnf_to a na) (hb : whnf_to b nb) ",
                    "(wa : iota_whnf na) (wb : iota_whnf nb) => ",
                    // join a b from the landed def_eq_joinable
                    "@par_strips_witness_cd_star.rec the_red_env a b ",
                    "(fun (_w : par_strips_witness_cd_star the_red_env a b) => HeadMatch na nb) ",
                    "(fun (m : KExpr) (ham : par_reduces_cd_star the_red_env a m) ",
                    "(hbm : par_reduces_cd_star the_red_env b m) => ",
                    // join na m: diamond on the two a-legs
                    "@par_strips_witness_cd_star.rec the_red_env na m ",
                    "(fun (_w2 : par_strips_witness_cd_star the_red_env na m) => HeadMatch na nb) ",
                    "(fun (p1 : KExpr) (hnap1 : par_reduces_cd_star the_red_env na p1) ",
                    "(hmp1 : par_reduces_cd_star the_red_env m p1) => ",
                    // join nb m: diamond on the two b-legs
                    "@par_strips_witness_cd_star.rec the_red_env nb m ",
                    "(fun (_w3 : par_strips_witness_cd_star the_red_env nb m) => HeadMatch na nb) ",
                    "(fun (p2 : KExpr) (hnbp2 : par_reduces_cd_star the_red_env nb p2) ",
                    "(hmp2 : par_reduces_cd_star the_red_env m p2) => ",
                    // join p1 p2: diamond on the two m-legs -> the common meet w
                    "@par_strips_witness_cd_star.rec the_red_env p1 p2 ",
                    "(fun (_w4 : par_strips_witness_cd_star the_red_env p1 p2) => HeadMatch na nb) ",
                    "(fun (w : KExpr) (hp1w : par_reduces_cd_star the_red_env p1 w) ",
                    "(hp2w : par_reduces_cd_star the_red_env p2 w) => ",
                    "{body}) ",
                    "(par_reduces_cd_star_diamond the_red_env i1 i2 i3 i4 i5 i6 i7 i8 m p1 p2 hmp1 hmp2)) ",
                    "(par_reduces_cd_star_diamond the_red_env i1 i2 i3 i4 i5 i6 i7 i8 b nb m ",
                    "(whnf_to_cd_star b nb hb) hbm)) ",
                    "(par_reduces_cd_star_diamond the_red_env i1 i2 i3 i4 i5 i6 i7 i8 a na m ",
                    "(whnf_to_cd_star a na ha) ham)) ",
                    "(def_eq_joinable i1 i2 i3 i4 i5 i6 i7 i8 a b h)"
                ),
                ib = I_BINDERS,
                body = body,
            )),
            is_axiom: false,
            description: concat!(
                "WALL-A COMPLETION (mirror WallAIota.def_eq_whnf_complete): COMPLETENESS of the ",
                "algorithmic def-eq decision over the FULL β+ι+δ+ζ reduction. If DefEq a b and the ",
                "kernel's whnf loop returned na / nb (whnf_to legs = the SN/termination ORACLE) with ",
                "the targets iota-aware whnfs (iota_whnf — the strengthened hypothesis the real kernel ",
                "guarantees via its major-premise whnf pre-pass; see the module header), then one round ",
                "of the structural comparison SUCCEEDS: HeadMatch na nb. Proof: def_eq_joinable (the ",
                "landed join half) + three applications of the landed 3-way diamond ",
                "par_reduces_cd_star_diamond push na and nb to a common reduct w; the iota_whnf case ",
                "split + the head-rigidity family extract the matching heads (join_to_def_eq lands the ",
                "DefEq components). i1..i8 are CARRIED hypotheses (never discharged from the_red_env, ",
                "never axiomatized); the retired-as-FALSE church_rosser_whnf shape (a shared whnf_to ",
                "target) is deliberately NOT the statement. DerivedProved, zero axiom_deps. ",
                "Wall-A COMPLETE."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "DefEq".to_string(),
                "whnf_to".to_string(),
                "iota_whnf".to_string(),
                "iota_whnf.rec".to_string(),
                "HeadMatch".to_string(),
                "HeadMatch.sort".to_string(),
                "HeadMatch.lam".to_string(),
                "HeadMatch.pi".to_string(),
                "def_eq_joinable".to_string(),
                "par_reduces_cd_star_diamond".to_string(),
                "par_strips_witness_cd_star".to_string(),
                "par_strips_witness_cd_star.rec".to_string(),
                "par_strips_witness_cd_star.intro".to_string(),
                "par_reduces_cd_star_trans".to_string(),
                "par_reduces_cd_star_sort_inv_eq".to_string(),
                "par_reduces_cd_star_lam_inv_eq".to_string(),
                "par_reduces_cd_star_pi_inv_eq".to_string(),
                "iota_whnf_star_sort_inv_eq".to_string(),
                "iota_whnf_star_to_neutral".to_string(),
                "iota_neutral_cd_star".to_string(),
                "iota_neutral_head_match".to_string(),
                "def_eq_whnf_complete_lam_kont".to_string(),
                "def_eq_whnf_complete_pi_kont".to_string(),
                "par_reduces_cd_star_target_cast".to_string(),
                "head_match_target_cast_rev".to_string(),
                "whnf_to_cd_star".to_string(),
                "RecEnvReductNotRedex".to_string(),
                "RecEnvCtorNoRecMeta".to_string(),
                "RecEnvClosed".to_string(),
                "RecEnvLiftClosed".to_string(),
                "DefEnvClosed".to_string(),
                "DefEnvLiftClosed".to_string(),
                "RecEnvDefEnvDisjoint".to_string(),
                "RecEnvCtorNoDefVal".to_string(),
                "red_rec".to_string(),
                "red_def".to_string(),
                "the_red_env".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::test_utils::build_spec_with_stack;

    /// Every Wall-A-completion declaration registers, is DerivedProved with
    /// empty axiom closure, and re-typechecks against the live kernel env.
    #[test]
    fn test_wall_a_completeness_registers_and_reverifies() {
        let spec = build_spec_with_stack();
        // The two new inductives (+ ctors/recursors).
        for name in [
            "iota_neutral",
            "iota_neutral.rec",
            "iota_neutral.const",
            "iota_neutral.app",
            "iota_whnf",
            "iota_whnf.rec",
            "iota_whnf.sort",
            "iota_whnf.lam",
            "iota_whnf.pi",
            "iota_whnf.neutral",
        ] {
            assert!(
                spec.definitions().contains_key(name),
                "{name} should be registered by the Wall-A completion stage"
            );
        }
        // Every ported lemma: non-axiom, valued, empty declared closure,
        // kernel-reverified.
        for name in [
            "iota_immune",
            "iota_neutral_subsumes_is_neutral",
            "iota_whnf_subsumes_is_whnf",
            "iota_immune_sort_witness",
            "iota_whnf_sort_witness",
            "iota_neutral_sort_absurd",
            "iota_neutral_sort_absurd_type",
            "iota_neutral_lam_absurd_type",
            "iota_neutral_pi_absurd_type",
            "beta_reduces_to_cd_star",
            "whnf_step_cd_star_goal",
            "whnf_step_to_cd_star",
            "whnf_to_cd_star_goal",
            "whnf_to_cd_star",
            "par_reduces_cd_const_dead_inv_eq",
            "par_reduces_cd_star_const_dead_inv_eq",
            "iota_neutral_no_delta",
            "par_reduces_cd_neutral_app_inv",
            "iota_immune_cd_step",
            "iota_neutral_cd_step",
            "iota_neutral_cd_star",
            "par_reduces_cd_star_neutral_app_inv",
            "par_reduces_cd_star_neutral_app_inv_eq",
            "par_reduces_cd_star_target_cast",
            "par_reduces_cd_star_target_cast_rev",
            "head_match_target_cast_rev",
            "cd_star_join_to_def_eq",
            "iota_neutral_star_const_inv_eq",
            "iota_neutral_star_to_app_kont",
            "iota_neutral_star_to_app_inv",
            "iota_neutral_head_match_kont_inner",
            "iota_neutral_head_match_kont",
            "iota_neutral_head_match",
            "iota_whnf_star_sort_inv_eq",
            "iota_whnf_star_lam_inv_eq_kont",
            "iota_whnf_star_lam_inv_eq",
            "iota_whnf_star_pi_inv_eq_kont",
            "iota_whnf_star_pi_inv_eq",
            "iota_whnf_star_to_neutral",
            "def_eq_whnf_complete_lam_kont_inner",
            "def_eq_whnf_complete_lam_kont",
            "def_eq_whnf_complete_pi_kont_inner",
            "def_eq_whnf_complete_pi_kont",
            "def_eq_whnf_complete",
        ] {
            let def = spec
                .definitions()
                .get(name)
                .unwrap_or_else(|| panic!("{name} should be registered"));
            assert!(!def.is_axiom, "{name} must not be an axiom");
            assert!(def.value_src.is_some(), "{name} must carry a proof term");
            assert!(
                def.axiom_deps.is_empty(),
                "{name} must declare empty axiom closure: {:?}",
                def.axiom_deps
            );
            spec.verify_definition(name)
                .unwrap_or_else(|e| panic!("{name} should re-typecheck in the spec env: {e:?}"));
        }
    }
}
