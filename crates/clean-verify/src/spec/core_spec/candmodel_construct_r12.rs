// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! R12 of the candidate-model construction ladder — **the SHAPE / DENOTATION
//! SPLIT**, the rung R6's and R11's walls both point at.
//!
//! ## Why this rung
//!
//! Two proved walls, one cause:
//!
//! * **R6** — the dependent Pi clause `candInterp (pi A B) := PiSet (candInterp
//!   A) (fun a => candInterp (instantiate B a))` is NON-PORTABLE:
//!   `r6_dependent_pi_self_reachable` exhibits `T := pi (sort 0) (bvar 0)` at
//!   `a := T`, where the recursive call is `candInterp T` itself.
//! * **R11** — `candInterp` is NOT conversion-invariant:
//!   `r11_candInterp_step_conv_refuted` shows not even ONE `whnf_step` of the
//!   type transports, because `candInterp` is `KExpr.rec` ON THE TYPE.
//!
//! Both say: do not recurse on the type's syntax. The corpus's answer, proved
//! and landed by this project, is to recurse on the **shape** — which does not
//! move when the type does — and to interpret a lambda as a SEMANTIC FUNCTION
//! rather than as a set of terms
//! (`proofs/aristotle-whnf-model-guides/stratified-sn/solution/Stratified/`
//! `Shapes.lean`, `FInterp.lean`, `FWK.lean`, `FGood.lean`).
//!
//! ## A — the shape domain (LANDED, complete)
//!
//! `Sk` (`ty` / `kd s` / `arr d c`), `domSk`, `piShape`, and the large
//! elimination `VD : Sk -> Type 1` with `VD (arr d c) = VD d -> VD c` — the
//! definition that makes a semantic function representable at all, since an
//! inductive `SVal | fn : (SVal -> SVal) -> SVal` is not strictly positive.
//! `vcarD` reads the candidate out, `mkTyD` packages one at a Pi-shape
//! (`vcarD_mkTyD`), `junkD` is the junk value of every shape and `goodD_junkD`
//! proves `GoodD` inhabited at every shape. The packaged value type `Val` is the
//! corpus's `Sigma s : Sk, VD s` as a one-constructor inductive, with `valS` /
//! `valD` / `valCar` / `valGood` / `valJunk` / `isCandHI_valCar` beside it.
//!
//! **One universe throughout, but not the corpus's one.** The corpus's `VD s`
//! is `Type 0` because its candidates are `Tm -> Prop`; the spec's are
//! `KExpr -> Type` because `whnf_acc` is `Acc`-shaped, so `VD s : Type 1` and
//! `GoodD : (s : Sk) -> VD s -> Type 1`. `GoodSet` is the resulting one-line
//! universe lift of R10's `IsCandHI` — a constant function out of a `Sort 2`
//! domain, no new inductive, since the kernel is NON-CUMULATIVE and
//! `IsCandHI S : Type 0` cannot be a `Type 1` clause directly.
//!
//! **`coeD` and decidable equality on `Sk` are not needed and not built.** The
//! corpus's `val : Tm -> VEnv -> Val` is total on raw syntax and pays for it
//! with a coercion at every application. Here the valuation is DEPENDENT
//! (`VEnvD D := forall i, VD (D i)`) and the interpretation recurses on the
//! SHAPE DERIVATION, so shapes match by construction: `MatchEnv`, `coeD`,
//! `coeD_self`, `coeD_mk` and the `Sk` decision procedure they need all
//! disappear.
//!
//! ## B — the shape-indexed interpretation (LANDED, with conversion-invariance)
//!
//! `WK : (Nat -> Sk) -> KExpr -> Sk -> Type` is the corpus's shape typing
//! (`FWK.lean:73`) on `KExpr`/`Level`; levels are semantically INERT (every sort
//! gets `kd ty`), which is why `Level`'s `param`/`max`/`imax` trees cost this
//! route nothing where they killed the coupled route.
//!
//! `sval D e s h r : VD s` is the interpretation. `lam` denotes a semantic
//! function, `app` denotes semantic application, and therefore:
//!
//! * **(i) candidate-hood** — `sval_good` proves `GoodD s (sval ... )` at every
//!   good valuation, through the LANDED interface: R10's `isCandHI_piSet` for
//!   the Pi clause, `isCandHI_vcarD` to read a candidate out of a good value.
//!   `isCandHI_sval` is the corollary `IsCandHI (vcarD s (sval ...))` and
//!   `sval_members_sn` its cr1.
//! * **(ii) CONVERSION-INVARIANCE — ACHIEVED.** `r12_sval_beta` is `Eq.refl`:
//!   the interpretation of a beta redex IS the interpretation of the body under
//!   the extended valuation, at EVERY shape-typed redex, in EVERY valuation.
//!   `r12_sval_beta_contractum` turns that into the transport statement proper —
//!   at an ARBITRARY shape environment, annotation, argument and valuation, the
//!   redex's interpretation EQUALS the interpretation of the term it
//!   `whnf_step`s to, and `r12_beta_step_general` is that step. That is exactly
//!   the class `r11_candInterp_step_conv_refuted` proves `candInterp` cannot
//!   transport even once.
//!
//!   One measured trap on the way (2026-08-27): `instantiate (bvar 0) a` is
//!   **not** definitionally `a`. `instantiate_bvar_geq` substitutes the LIFTED
//!   value, so it reduces to `lift_at a 0 0`, which is stuck on a variable. The
//!   link is `r12_beta_contractum_is_arg`, one application of the landed
//!   `lift_zero_identity`; assuming it cost this rung an elaboration cycle.
//!
//! **The contrast with R11 is registered.** `r12_betaRedex :=
//! app (lam (bvar 0) (bvar 0)) (sort 0)` is R11's counterexample SHAPE — an
//! identity lambda applied at the TYPE level — made shape-typeable by annotating
//! at a kind-of-kinds variable. `r12_beta_step_witness` is the very `whnf_step`
//! R11 refuted transport for, and `r12_conv_contrast` is ONE kernel-checked
//! constant pairing `r11_candInterp_step_conv_refuted` with the same step
//! transported through `sval`: same calculus, same environment, one
//! interpretation refuted and the other proved.
//!
//! ## C — the dependent Pi clause (LANDED as a construction; TWO horns PROVED)
//!
//! `wkPiDep` is what R6 proved non-portable for `candInterp`: the codomain
//! interpreted in the valuation EXTENDED BY THE ARGUMENT'S OWN VALUE. R6's
//! unmeasurable recursion `candInterp (instantiate B a)` becomes an environment
//! extension on the structurally smaller `B`, so the self-reachability
//! counterexample has nothing to bite. `isCandHI_wkPiDep` proves it is a
//! candidate and `wkPiDep_elim` is the DEPENDENT elimination:
//!
//! ```text
//! wkPiDep .. t -> [[A]] a -> forall (ha : WK D a (domSk sA)),
//!     vcarD sB (sval B (vconsD (sval a ha r) r)) (app t a)
//! ```
//!
//! It is a construction ON TOP of `sval`, **not** a clause of `sval`'s own
//! recursion, and that is forced by two independent obstructions — the reason
//! this rung's honest deliverable is C-as-a-construction:
//!
//! **HORN 1 — the universe horn (predicativity).** The corpus's clause
//! (`FInterp.lean:63` `piVal`) intersects over the WHOLE value domain of the
//! domain shape. `piCandV` is exactly that clause, registered, with its
//! dependent elimination `piCandV_elim` proved — and its type is
//! `KExpr -> Type 1`, one universe ABOVE the `KExpr -> Type` that `VD Sk.ty` is,
//! because `VD d : Type 1` and `Type` is PREDICATIVE. The corpus lands the same
//! clause in `Prop`, which is IMPREDICATIVE; the spec cannot, because
//! `whnf_acc` is `Acc`-shaped and every rung R0-R11 is built on
//! `KExpr -> Type`. **Shifting does not close it**: at `VD ty := KExpr -> Type
//! 1` the clause lands at `Type 2`, and so on at every level — the offset is
//! invariant. `test_candmodel_r12_value_quantified_pi_clause_is_refused` is the
//! machine-visible half: the kernel REFUSES the same clause written at
//! `KExpr -> Type`.
//!
//! **HORN 2 — the recursion horn.** The Type-0 way to recover the dependency is
//! to intersect over shape DERIVATIONS instead of over values —
//! `piCodDepIdx D d sB GB r w := forall y (hy : WK D y d),
//! vcarD sB (GB (sval D y d hy r)) w` — which is what `piCandDep` does and why
//! it stays in `Type 0`. But that clause CALLS `sval` at derivations `hy` of
//! terms unrelated to the term being interpreted, so it cannot be a minor of
//! `sval`'s own `WK.rec`: the call is not structural. `sval`'s `pi` clause is
//! therefore the JUNK-PROBE candidate, and the dependent one is built after the
//! fact. `test_candmodel_r12_sval_is_not_self_referential` pins the
//! stratification.
//!
//! ## What did NOT land, and why — read before quoting
//!
//! * **No SN capstone.** `sval_good` gives candidate-hood, not `whnf_acc e` for
//!   a shape-typed `e`: `WK` is a SHAPE system, and turning it into SN needs its
//!   own fundamental theorem (the corpus gets SN from `CC`/`CCSN`, never from
//!   `WK` alone). Every earlier rung's capstone is `SynTy*`-shaped and R12 adds
//!   none; nothing here advances `whnf_terminates_well_typed_dependent` or
//!   discharges `M : CandModel tenv`.
//! * **No substitution lemma, and it is BLOCKED, not skipped.** *[SUPERSEDED
//!   2026-08-27 by R13 — read the next bullet as history. `funext` IS derivable
//!   in the spec from `Quot.sound` and IS now registered as `spec_funext`
//!   (`candmodel_construct_r13.rs`), with ZERO new axioms, and the congruence
//!   lemmas named below have landed. What blocks `val_psub`/`val_lift` today is
//!   different: R12 built no substitution or weakening OPERATION on `WK`
//!   derivations. The `propext` remark is also retired — the `piB` congruence
//!   needs none.]* The corpus's
//!   `val_psub`/`val_lift` (FInterp.lean:209/159) equate two SEMANTIC FUNCTIONS
//!   that agree pointwise, i.e. they are `funext` applications. **The spec has
//!   no `funext`** — by design (`dependent_sn_richmodel.rs:664`, which replaces
//!   every corpus `funext` with a pointwise congruence). Pointwise congruence
//!   does not substitute here: the objects being equated ARE functions
//!   (`VD (arr d c)`), not substitutions. The same wall blocks the general
//!   one-step invariance `val_step` (FWK.lean:290) at its `piB`/`lamB`
//!   congruence cases, whose corpus proofs are `piVal_congr`/`lamVal_congr` —
//!   `funext`, and in `piVal_congr`'s case `propext` as well, which a
//!   Type-valued candidate cannot use either. What R12 proves instead is the
//!   HEAD beta case, which needs neither: `r12_sval_beta` at every instance and
//!   `r12_sval_beta_contractum` where the syntactic contractum is reached.
//! * **`sval` is PARTIAL where `candInterp` is total.** It interprets only
//!   shape-typed terms. R11's own redex `app (lam (sort 0) (bvar 0)) (pi (sort
//!   0) (sort 0))` is NOT shape-typed — the lambda is annotated at `sort 0`, so
//!   it takes an argument of shape `ty`, while `pi (sort 0) (sort 0)` has shape
//!   `kd (arr ty ty)` — which is why the contrast is registered at the
//!   shape-typed member of the same family and never claimed at R11's literal
//!   term. A `CandModel` field quantifies over all untyped `T`; `sval` does not
//!   reach there and this rung does not pretend it does.
//! * **cr3 is HEAD-INERT, not unrestricted.** `GoodD`'s base clause is R10's
//!   `IsCandHI`, because R10 PROVED unrestricted cr3 false for the Pi-candidate
//!   over the real reflected environment. The corpus's `isCand_piSet` has full
//!   cr3 only because its calculus is beta-only with saturated constructors.
//!
//! ## Non-degeneracy (no automated gate performs this)
//!
//! `r12_sval_pi_proper` — `r5_omegaLam`, R5's and R11's own strongly
//! normalizing lambda, is NOT in the interpretation of `pi (sort 0) (sort 0)`;
//! `r12_sval_pi_var_witness` — `bvar 0` IS. So the interpretation is neither the
//! total predicate (the `micro_has_type` trap) nor the empty one.
//! `r12_sval_excludes_omega` is the same fact at every shape-typed type.
//! `WK` is witnessed by three registered definitions (`r12_wk_sort_witness`,
//! `r12_wk_id_witness`, `r12_wk_pi_witness`), `GoodD` by `goodD_junkD`,
//! `GoodSet` by `goodSet_whnfAcc`, `GoodEnvD` by `goodEnvD_junk`, `VD` by
//! `junkD`, `piCodDep` by `piCodDep_intro` and `piCandDep` by
//! `piCandDep_intro` — a CONSTRUCTOR does not count on the supply side, so each
//! is a definition, and `test_candmodel_ladder_premises_are_witnessed` names
//! them.
//!
//! ## Census
//!
//! ZERO new axioms: 72 constants — three genuine inductives via `add_inductive`,
//! 34 plain defs via `add_recursive_def`, and 35 value-bearing theorems via
//! `add_definition` with kernel `add_decl` checking. Census-neutral.

use std::collections::HashSet;

use super::candmodel_construct_r12_src::*;
use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

/// Register one value-bearing theorem (R6-R11's helper, verbatim).
fn add_thm(
    spec: &mut Specification,
    name: &str,
    ty: String,
    val: String,
    deps: &[&str],
    desc: &str,
) -> Result<(), SpecError> {
    spec.add_definition(SpecDefinition {
        name: name.to_string(),
        type_src: ty,
        value_src: Some(val),
        is_axiom: false,
        description: desc.to_string(),
        category: AxiomCategory::DerivedLemma,
        proof_status: ProofStatus::DerivedProved,
        elaborated_type: None,
        elaborated_value: None,
        dependencies: Some(
            deps.iter()
                .map(|d| (*d).to_string())
                .collect::<HashSet<_>>(),
        ),
        axiom_deps: HashSet::new(),
    })
}

/// One-line meanings for the rung's plain declarations, keyed by name. Kept
/// beside the sources so the registration loop stays a loop and every constant
/// still carries its own description into the spec.
fn decl_description(name: &str) -> &'static str {
    match name {
        "Sk" => {
            "Sk — THE SHAPE ALGEBRA: a semantic type, a semantic kind tagged with the shape of \
                 its inhabitants, a semantic constructor. Corpus Stratified/Shapes.lean:36 \
                 verbatim. Recursion on THIS is what R6 and R11 both point at: a shape does not \
                 move when the type does."
        }
        "domSk" => {
            "domSk s — the shape of the inhabitants of a kind; junk (ty) off the kinds. \
                    Corpus Shapes.lean:48."
        }
        "piShape" => {
            "piShape s t — the shape of a Pi: a Pi of kinds is a kind, anything else is a \
                      type. Corpus FInterp.lean:57. A DOUBLE Sk.rec, because the outer recursion \
                      leaves piShape (kd s1) t stuck on a variable t."
        }
        "VD" => {
            "VD s — THE LARGE ELIMINATION and the heart of the rung: the domain of values of a \
                 shape, with VD (arr d c) = VD d -> VD c. Corpus Shapes.lean:58. This is what \
                 makes a semantic function representable at all — an inductive \
                 SVal | fn : (SVal -> SVal) -> SVal is not strictly positive and the kernel \
                 refuses it. Type 1, one universe above the corpus's Type 0, because the spec's \
                 candidates are KExpr -> Type where the corpus's are Tm -> Prop."
        }
        "vcarD" => {
            "vcarD s v — the candidate a value denotes: itself at a type or a kind, the top \
                    candidate at a constructor. Corpus vcar (Shapes.lean:161), indexed rather than \
                    packaged."
        }
        "mkTyD" => {
            "mkTyD s t C — package a candidate at a Pi-shape. Corpus mkTy (Shapes.lean:91) \
                    with the shape taken from the two shape-typing premises instead of from a junk \
                    probe: the derivation-indexed interpretation already knows both shapes."
        }
        "junkD" => {
            "junkD s — the junk value of every shape (whnf_acc at a type or kind, a \
                    constant function at a constructor). Corpus Shapes.lean:67 with SN := \
                    whnf_acc. Its existence is what makes GoodD inhabited at EVERY shape, which \
                    the dependent Pi-candidate's cr1 needs."
        }
        "GoodSet" => {
            "GoodSet S — the Type 1 lift of R10's IsCandHI, with NO new inductive: a \
                      constant function out of a Sort 2 domain IS a universe lift. GoodD must land \
                      in Type 1 because its arr clause quantifies over VD d : Type 1, and the \
                      kernel is NON-CUMULATIVE, so IsCandHI S : Type 0 cannot be the base clause \
                      directly."
        }
        "GoodD" => {
            "GoodD s v — a value is GOOD when every candidate buried in it really is one. \
                    Corpus Shapes.lean:126 at R10's HEAD-INERT interface, not at the unrestricted \
                    one: R10 PROVED unrestricted cr3 false for the Pi-candidate over the real \
                    reflected environment, so IsCandHI is the widest available base clause."
        }
        "Val" => {
            "Val — THE PACKAGED VALUE TYPE: the corpus's Sigma s : Sk, VD s (Shapes.lean:64) \
                  as a one-constructor inductive, since the spec has no sigma. Type 1 because its \
                  second field is. The derivation-indexed interpretation does not need it — every \
                  value it produces is at a known shape — so it is registered for the corpus's \
                  interface, not consumed by sval."
        }
        "valS" => "valS v — the shape of a packaged value (corpus .1).",
        "valD" => {
            "valD v — the payload of a packaged value (corpus .2), a DEPENDENT projection \
                   whose Val.rec motive is fun qv => VD (valS qv)."
        }
        "valCar" => "valCar v — the candidate a packaged value denotes (corpus vcar).",
        "valGood" => "valGood v — a good packaged value (corpus Good).",
        "valJunk" => "valJunk s — the junk value of a shape, packaged (corpus junkV).",
        "skcons" => {
            "skcons s D — extending a shape environment under a binder. Corpus \
                     FWK.lean:33."
        }
        "VEnvD" => {
            "VEnvD D — a DEPENDENT valuation: a value of the RIGHT SHAPE for every de \
                    Bruijn index. The corpus's VEnv (FInterp.lean:36) is untyped and needs \
                    MatchEnv (FWK.lean:218) beside it; indexing the valuation by the shape \
                    environment makes MatchEnv hold by construction and deletes it — and with it \
                    every coeD coercion, the decidable equality on Sk those coercions need, and \
                    every shape side condition in the Pi clause."
        }
        "vconsD" => {
            "vconsD s D v r — extending a dependent valuation, with the Nat.rec motive \
                     carrying the shape so both branches typecheck. Corpus vcons \
                     (FInterp.lean:39)."
        }
        "GoodEnvD" => {
            "GoodEnvD D r — a valuation is good when all its values are. Corpus GoodEnv \
                       (FInterp.lean:45)."
        }
        "WK" => {
            "WK D e s — SHAPE TYPING: a simple type system on the raw syntax that assigns to a \
                 term the SHAPE of its value. Corpus FWK.lean:73 on KExpr/Level. Levels are \
                 semantically INERT — every sort gets kd ty — which is why Level's \
                 param/max/imax trees cost this route nothing where they killed the coupled \
                 (universe-indexed) route. Not total: WK is a shape discipline, so sval is PARTIAL \
                 where candInterp is total, and no claim on CandModel's untyped laws follows."
        }
        "sval" => {
            "sval D e s h r — THE SHAPE-INDEXED INTERPRETATION, corpus val \
                   (FInterp.lean:72), by recursion on the SHAPE DERIVATION rather than on the \
                   term, which is what keeps it coercion-free and junk-free. lam denotes a \
                   SEMANTIC FUNCTION and app denotes semantic application, so the semantic beta \
                   law is DEFINITIONAL (r12_sval_beta) — the law R11 proved candInterp cannot \
                   have. The pi clause is the JUNK-PROBE Girard candidate; the dependent one is \
                   piCandDep, built on top, for the two obstructions in the module docs."
        }
        "piCodDepIdx" => {
            "piCodDepIdx — the intersection index of the dependent codomain: the \
                          codomain interpretation at the value of EVERY shape-typed term of the \
                          domain shape. A KExpr/WK-indexed intersection, which is what keeps it in \
                          Type 0 where the corpus's value-indexed one would not be."
        }
        "piCodDep" => {
            "piCodDep — the dependent codomain candidate: the junk probe (which supplies \
                       cr1 when the intersection index is empty, exactly as the corpus's \
                       good_junkV does) intersected with the derivation-indexed family."
        }
        "piCandDep" => {
            "piCandDep — THE DEPENDENT PI CANDIDATE, what R6 proved non-portable for \
                        candInterp. The codomain is interpreted in the valuation EXTENDED BY THE \
                        ARGUMENT'S OWN VALUE, so R6's unmeasurable recursion \
                        candInterp (instantiate B a) becomes an environment extension on the \
                        structurally smaller B and the self-reachability counterexample has \
                        nothing to bite."
        }
        "wkPiDep" => {
            "wkPiDep — piCandDep at a REAL shape-typing premise pair: the domain \
                      candidate is the domain type's interpretation, the codomain family is the \
                      codomain type's under the extended valuation."
        }
        "piCandV" => {
            "piCandV — THE UNIVERSE OBSTRUCTION, REGISTERED AT ITS TRUE UNIVERSE. The \
                      corpus's Pi clause (FInterp.lean:63 piVal) intersects over the WHOLE value \
                      domain of the domain shape; this is that clause, and it lands in \
                      KExpr -> Type 1, one universe ABOVE the KExpr -> Type that VD Sk.ty is, \
                      because VD d : Type 1 and Type is PREDICATIVE. The corpus lands the same \
                      clause in Prop, which is IMPREDICATIVE. Shifting does not close it: at \
                      VD ty := KExpr -> Type 1 the clause lands at Type 2. Its content is intact \
                      (piCandV_elim) — only its universe is wrong."
        }
        "r12_betaEnv" => {
            "The contrast rung's shape environment: every index a KIND OF KINDS. A \
                          variable of that shape is the only way to annotate a lambda whose bound \
                          variable is itself a TYPE, since every sort has shape kd ty."
        }
        "r12_betaRedex" => {
            "THE TYPE-LEVEL BETA REDEX, SHAPE-TYPED: app (lam (bvar 0) (bvar 0)) \
                            (sort 0). R11's counterexample SHAPE — an identity lambda applied at \
                            the type level — with the annotation moved to a kind-of-kinds variable \
                            so a WK derivation exists. R11's own redex is NOT shape-typed, and the \
                            module docs say exactly why."
        }
        "r12_betaJunkEnv" => "The all-junk valuation of the contrast environment.",
        "r12_betaDeriv" => {
            "The shape derivation of the contrast redex — one WK.app over a WK.lam \
                            over two WK.vars and a WK.sort."
        }
        "r12_candInterpStepConv" => {
            "The premise R11 refuted, as a named Type so it can sit inside \
                                     an AndType without a parenthesised forall in argument \
                                     position (which this parser rejects)."
        }
        "r12_svalTransportsBeta" => {
            "...and the same transport for sval at the concrete \
                                     shape-typed redex. The two are paired by r12_conv_contrast."
        }
        "r12_piEnv" => "The properness witness's shape environment — every index a plain type.",
        "r12_junkEnv" => {
            "The all-junk dependent valuation at an ARBITRARY shape environment — the \
                          premise gate's supply for VEnvD, and the proof that a valuation always \
                          exists, so every GoodEnvD-premised statement of the rung is \
                          non-vacuous."
        }
        "r12_wk_sort_witness" => {
            "THE PREMISE GATE'S SUPPLY FOR WK: every sort is shape-typed, at every shape \
             environment, at kd ty — the clause that makes levels semantically inert. A \
             CONSTRUCTOR does not count on the supply side, which is why this is a registered \
             definition."
        }
        "r12_wk_id_witness" => {
            "...and the identity lambda at arr ty ty, the shape-level counterpart of R9's/R11's \
             synTy*_id."
        }
        "r12_wk_pi_witness" => {
            "...and pi (sort 0) (sort 0) at kd (arr ty ty) — R11's own PI00, shape-typed, and the \
             subject of both halves of the non-degeneracy guard. Registered as a DEF and not a \
             theorem on purpose: a witness a later proof must REDUCE THROUGH has to delta-unfold, \
             and a theorem does not — measured 2026-08-27, when r12_sval_pi_proper died with `Too \
             many arguments' on a WK.rec spine that stayed stuck."
        }
        _ => "R12 shape/denotation split.",
    }
}

/// One-line meanings for the rung's theorems, and their declared dependencies.
fn thm_meta(name: &str) -> (&'static [&'static str], &'static str) {
    match name {
        "goodSet_up" => (
            &["GoodSet", "IsCandHI"],
            "Enter the Type 1 lift of IsCandHI. Identity plus a discarded Sort 2 binder.",
        ),
        "goodSet_down" => (
            &["GoodSet", "IsCandHI"],
            "...and leave it, at the top candidate. The pair is why GoodSet is a def and not a new \
             inductive: it costs no constructor and no recursor.",
        ),
        "goodSet_whnfAcc" => (
            &["GoodSet", "goodSet_up", "isCandHI_whnfAcc"],
            "THE PREMISE GATE'S SUPPLY FOR GoodSet: the top candidate is a good set. A def, \
             because a def has no constructors and every witness must be a registered definition.",
        ),
        "vcarD_mkTyD" => (
            &["vcarD", "mkTyD", "piShape"],
            "The read-back law: packaging a candidate at a Pi-shape and reading it out again is \
             the identity, at EVERY pair of shapes. A double Sk.rec whose five leaves are each one \
             Eq.refl — the double induction is needed because piShape (kd s1) t does not reduce \
             for a variable t.",
        ),
        "goodD_mkTyD" => (
            &["GoodD", "mkTyD", "piShape", "goodSet_up"],
            "...and the packaged candidate is a GOOD value whenever the candidate is one. Same \
             double Sk.rec; every leaf is a type-like shape, so every leaf is goodSet_up.",
        ),
        "goodD_junkD" => (
            &["GoodD", "junkD", "goodSet_whnfAcc"],
            "GoodD IS INHABITED AT EVERY SHAPE — the corpus's good_junkD (Shapes.lean:134) and the \
             premise gate's supply for GoodD. It is also what lets the dependent Pi-candidate have \
             cr1 when its derivation index is empty.",
        ),
        "isCandHI_vcarD" => (
            &["GoodD", "vcarD", "IsCandHI", "goodSet_down", "isCandHI_whnfAcc"],
            "THE BRIDGE TO THE LANDED INTERFACE: the candidate a good value denotes really is an \
             IsCandHI candidate. Corpus isCand_carrier (Shapes.lean:172). At a constructor shape \
             the carrier is the top candidate, so that arm is isCandHI_whnfAcc.",
        ),
        "goodEnvD_vconsD" => (
            &["GoodEnvD", "vconsD", "skcons", "GoodD"],
            "Extending a good valuation by a good value keeps it good. Corpus goodEnv_vcons \
             (FInterp.lean:47), by Nat.rec on the index with the shape carried in the motive.",
        ),
        "goodEnvD_junk" => (
            &["GoodEnvD", "junkD", "goodD_junkD"],
            "THE PREMISE GATE'S SUPPLY FOR GoodEnvD: the all-junk valuation is good at every shape \
             environment. Also the fact that makes every statement below non-vacuous — a good \
             valuation always exists.",
        ),
        "valGood_junk" => (
            &["valGood", "valJunk", "goodD_junkD"],
            "The packaged junk value is good — the supply side of the packaged interface, and the \
             proof that Val's projections compute (the goal reduces through valS and valD to \
             goodD_junkD's statement).",
        ),
        "isCandHI_valCar" => (
            &["valGood", "valCar", "IsCandHI", "isCandHI_vcarD"],
            "isCandHI_vcarD at the packaged value type: corpus isCand_carrier verbatim.",
        ),
        "sval_good" => (
            &[
                "sval",
                "WK",
                "WK.rec",
                "GoodD",
                "GoodEnvD",
                "goodD_mkTyD",
                "isCandHI_vcarD",
                "isCandHI_piSet",
                "goodEnvD_vconsD",
                "goodD_junkD",
                "goodSet_whnfAcc",
            ],
            "**DELIVERABLE B(i): CANDIDATE-HOOD.** Every shape-typed term's interpretation is a \
             GOOD value at every good valuation. Corpus val_good (FGood.lean:59). One WK.rec with \
             five minors; the pi minor is R10's landed isCandHI_piSet applied to the domain's \
             candidate and the codomain's at the junk value, with candStepInv discharged by the \
             IDENTITY because the junk-probe codomain does not depend on the argument term at all. \
             ZERO carried premises beyond GoodEnvD, which goodEnvD_junk supplies.",
        ),
        "isCandHI_sval" => (
            &["sval", "isCandHI_vcarD", "sval_good", "IsCandHI"],
            "The corollary the rest of the ladder consumes: the candidate of a shape-typed term is \
             an IsCandHI candidate. Corpus isCand_val (FGood.lean:87).",
        ),
        "sval_members_sn" => (
            &["isCandHI_sval", "isCandHI_cr1"],
            "cr1 of that candidate: every member of a shape-typed type's interpretation is \
             strongly normalizing for the spec's FULL beta+zeta+iota+delta relation at the REAL \
             reflected environment. HONESTY: this is SN of the MEMBERS, not of the shape-typed \
             term itself — WK is a shape system and turning it into SN needs its own fundamental \
             theorem, which this rung does not build.",
        ),
        "r12_sval_excludes_omega" => (
            &["sval_members_sn", "r5_omegaV_not_whnfAcc"],
            "NON-DEGENERACY AT EVERY SHAPE-TYPED TYPE: R5's looping application is in NO \
             interpretation this rung produces. The interpretation is not the total predicate.",
        ),
        "r12_sval_beta" => (
            &["sval", "WK", "vconsD", "skcons", "domSk"],
            "**DELIVERABLE B(ii): THE SEMANTIC BETA LAW.** The interpretation of a beta redex IS \
             the interpretation of the body under the valuation extended by the argument's value — \
             at EVERY shape-typed redex, in EVERY valuation, and it is Eq.refl. Corpus val_beta \
             (FInterp.lean:248), which the corpus needs coeD_mk and val_body_shape for and this \
             formulation gets for free, because the dependent valuation makes the shapes match by \
             construction. THIS IS THE LAW R11 PROVED candInterp CANNOT HAVE.",
        ),
        "r12_beta_contractum_is_arg" => (
            &["instantiate", "lift_zero_identity"],
            "instantiate (bvar 0) a IS a, at an ARBITRARY a — and it is NOT Eq.refl: \
             instantiate_bvar_geq substitutes the LIFTED value, so the contractum reduces to \
             lift_at a 0 0, which is stuck on a variable. lift_zero_identity is exactly that \
             lemma. Measured 2026-08-27: the first shape of this rung's contractum statement \
             assumed the reduction and was rejected by the elaborator.",
        ),
        "r12_beta_step_general" => (
            &[
                "whnf_step",
                "beta_reduces",
                "r12_beta_contractum_is_arg",
                "Eq.substType",
            ],
            "The head beta step of the identity redex at an ARBITRARY annotation and an ARBITRARY \
             argument, stated at the contractum a itself. Paired with r12_sval_beta_contractum \
             this is the SUBJECT of the general conversion-invariance claim: the redex really does \
             step to a, in the spec's own whnf_step.",
        ),
        "r12_sval_beta_contractum" => (
            &["r12_sval_beta", "sval", "vconsD"],
            "**THE GENERAL CONVERSION-INVARIANCE STATEMENT**, and the one that makes this rung's \
             claim general rather than exhibited: at an ARBITRARY shape environment, annotation, \
             argument and valuation, the interpretation of the beta redex EQUALS the \
             interpretation of the term it whnf_steps to (r12_beta_step_general). That is exactly \
             the class r11_candInterp_step_conv_refuted proves candInterp cannot transport — not \
             even once — and it is Eq.refl here. The remaining general form, at an arbitrary BODY \
             rather than the identity body, needs the semantic substitution lemma, which is \
             funext-blocked; see the module docs.",
        ),
        "r12_beta_step_witness" => (
            &["whnf_step", "beta_reduces", "r12_betaRedex"],
            "The contrast redex really does take the step: one whnf_step.beta, spelled exactly as \
             R11's r11_candInterp_step_conv_refuted spells the step it refutes transport for.",
        ),
        "r12_sval_beta_transports" => (
            &["sval", "r12_betaDeriv", "r12_betaEnv"],
            "THE CONTRAST, at the concrete shape-typed type-level redex and at EVERY valuation: \
             the interpretation of the redex and of its whnf_step contractum are EQUAL. One \
             Eq.refl.",
        ),
        "r12_conv_contrast" => (
            &[
                "AndType",
                "r11_candInterp_step_conv_refuted",
                "r12_candInterpStepConv",
                "r12_svalTransportsBeta",
            ],
            "**THE CONTRAST, MACHINE-VISIBLE, IN ONE KERNEL-CHECKED CONSTANT**: R11's refutation \
             that ANY single whnf_step of the type transports through candInterp, paired with the \
             same step transported through sval. Same calculus, same reduction relation, same real \
             environment — one interpretation refuted and the other proved. SCOPE: sval is defined \
             only on shape-typed terms, so this is not a drop-in replacement for candInterp in \
             CandModel's untyped laws; the module docs state the gap.",
        ),
        "piCodDep_intro" => (
            &["piCodDep", "piCodDepIdx", "AndType.intro"],
            "THE PREMISE GATE'S SUPPLY FOR piCodDep: the two conjuncts build one. A registered \
             definition because piCodDep is a def and has no constructors.",
        ),
        "isCandHI_piCodDep" => (
            &[
                "piCodDep",
                "piCodDepIdx",
                "isCandHI_intro",
                "isCandHI_vcarD",
                "sval_good",
                "goodD_junkD",
            ],
            "The dependent codomain is an IsCandHI candidate. cr1 comes from the junk conjunct — \
             which is exactly why the junk probe is there, since the derivation index may be empty \
             in a shape environment where no term has the domain shape — and cr2/cr3 are taken \
             conjunct-wise and index-wise. An intersection of candidates over a Type 0 index.",
        ),
        "isCandHI_piCandDep" => (
            &["piCandDep", "isCandHI_piSet", "isCandHI_piCodDep"],
            "...and so is the dependent Pi candidate, through R10's landed isCandHI_piSet. \
             candStepInv is the IDENTITY here: the derivation-indexed codomain quantifies over ALL \
             shape-typed terms of the domain shape, so it does not depend on the argument term — \
             which is the Girard intersection trick, and it is what makes R5's step-invariance \
             side condition free.",
        ),
        "piCandDep_intro" => (
            &["piCandDep", "piCodDep", "PiSet"],
            "THE PREMISE GATE'S SUPPLY FOR piCandDep, and pi_intro for the dependent candidate: \
             membership is exactly the codomain condition at every argument. Definitional.",
        ),
        "piCandDep_elim" => (
            &["piCandDep", "piCodDepIdx", "sval", "AndType.right"],
            "pi_elim FOR THE DEPENDENT CANDIDATE: given a member and an argument WITH A SHAPE \
             DERIVATION, the application lands in the codomain at THAT ARGUMENT'S OWN \
             interpretation. The derivation index is instantiated at the argument itself.",
        ),
        "isCandHI_wkPiDep" => (
            &["wkPiDep", "isCandHI_piCandDep", "isCandHI_sval", "sval_good", "goodEnvD_vconsD"],
            "The dependent Pi candidate at a real shape-typing premise pair is a candidate. The \
             codomain family's goodness is sval_good under the extended valuation.",
        ),
        "wkPiDep_elim" => (
            &["wkPiDep", "piCandDep_elim", "sval", "vconsD"],
            "**DELIVERABLE C: THE DEPENDENT PI ELIMINATION.** What R6 proved non-portable for \
             candInterp, proved here: app t a inhabits the CODOMAIN TYPE'S INTERPRETATION IN THE \
             VALUATION EXTENDED BY THE ARGUMENT'S OWN VALUE. R6's unmeasurable recursive call \
             candInterp (instantiate B a) is replaced by an environment extension on the \
             structurally smaller B, so the self-reachability counterexample has nothing to bite. \
             HONESTY: wkPiDep is built ON TOP of sval, not as a clause of sval's own recursion; \
             the two obstructions that force that are in the module docs and one of them is \
             machine-refuted in the test battery.",
        ),
        "piCodDepIdx_var_witness" => (
            &[
                "piCodDepIdx",
                "candHF_var_mem",
                "isCandHI_weaken",
                "isCandHI_vcarD",
                "sval_good",
            ],
            "THE PREMISE GATE'S SUPPLY FOR piCodDepIdx, and a genuine non-vacuity witness for the \
             derivation-indexed intersection: a VARIABLE is in the codomain candidate at EVERY \
             derivation-value at once, so the intersection is neither empty nor (by \
             r12_sval_excludes_omega) the total set.",
        ),
        "wkPiDep_intro" => (
            &["wkPiDep", "piCodDep", "PiSet"],
            "THE PREMISE GATE'S SUPPLY FOR wkPiDep, and pi_intro at the real shape-typing premise \
             pair: membership is exactly the dependent codomain condition at every argument of the \
             domain type's interpretation. Definitional.",
        ),
        "piCandV_intro" => (
            &["piCandV", "GoodD", "vcarD"],
            "THE PREMISE GATE'S SUPPLY FOR piCandV: the corpus's value-quantified clause is \
             inhabited by exactly its defining condition. Definitional, and at Type 1 like the \
             clause itself — which is the obstruction, not a defect of the clause.",
        ),
        "piCandV_elim" => (
            &["piCandV", "GoodD", "vcarD"],
            "The corpus's value-quantified Pi clause has its dependent elimination too — at EVERY \
             good value of the domain shape, which is strictly more than piCandDep gives. Its \
             content is intact; only its UNIVERSE is wrong (KExpr -> Type 1 where VD Sk.ty is \
             KExpr -> Type), which is R12's first obstruction and is not fixable by shifting.",
        ),
        "r12_sval_pi_proper" => (
            &["sval", "vcarD", "r12_wk_pi_witness", "r5_omegaLam", "r5_omegaV_not_whnfAcc"],
            "THE NON-DEGENERACY GUARD, R5's candInterp_pi_not_total at this interpretation: \
             r5_omegaLam — the SAME strongly normalizing lambda R5 and R11 use — is NOT in the \
             interpretation of pi (sort 0) (sort 0), in ANY valuation. The micro_has_type \
             total-predicate trap; no automated gate performs this check.",
        ),
        "r12_sval_pi_var_witness" => (
            &["sval", "isCandHI_sval", "isCandHI_weaken", "candHF_var_mem", "r12_wk_pi_witness"],
            "...and the positive half: bvar 0 IS in it, through R5's candHF_var_mem at the \
             candidate isCandHI_sval produces. The interpretation is neither total nor empty.",
        ),
        _ => (&[], "R12 shape/denotation split."),
    }
}

impl Specification {
    /// Register R12: the shape algebra `Sk`, the shape-indexed value domain
    /// `VD`/`Val`, the shape typing `WK`, the shape-indexed interpretation
    /// `sval` with its candidate-hood and its SEMANTIC BETA LAW, the DEPENDENT
    /// Pi candidate `piCandDep`/`wkPiDep` with its dependent elimination, and
    /// the two obstructions that keep the dependent clause off `sval`'s own
    /// recursion.
    ///
    /// MUST be registered AFTER `add_candmodel_construct_r11`
    /// (`r11_candInterp_step_conv_refuted`, for the conversion contrast) and
    /// therefore after R0-R10; it additionally needs R10's `IsCandHI`
    /// interface (`isCandHI_intro`/`_cr1`/`_cr2`/`_cr3`/`isCandHI_whnfAcc`/
    /// `isCandHI_piSet`/`isCandHI_weaken`), R5's `PiSet`, `candHF_var_mem`,
    /// `r5_omegaLam`, `r5_whnfAcc_omegaLam` and `r5_omegaV_not_whnfAcc`, and the
    /// foundation types (`Nat`, `Empty`, `Eq`, `AndType`).
    pub(super) fn add_candmodel_construct_r12(&mut self) -> Result<(), SpecError> {
        for (kind, name, src) in r12_decl_sources() {
            let desc = decl_description(&name);
            match kind {
                "inductive" => self.add_inductive(&src, desc)?,
                _ => self.add_recursive_def(&src, desc)?,
            }
        }
        for (name, ty, val) in r12_theorem_sources() {
            let (deps, desc) = thm_meta(&name);
            add_thm(self, &name, ty, val, deps, desc)?;
        }
        Ok(())
    }
}

#[cfg(test)]
#[path = "candmodel_construct_r12_tests.rs"]
mod tests;
