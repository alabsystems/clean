// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bounded dependent projection telescope computations, not projection typing.
//!
//! This bounded slice starts after one-constructor metadata resolution and
//! subject-type WHNF. It uses the existing three-way modeled WHNF evaluator at
//! an explicit fuel for each call. Its graph predicates are equations to those
//! computations, not arbitrary reduction traces or caller-supplied field types.
//! The parameter walk preserves the source's premature non-Pi stop, while the
//! field walk substitutes projections of preceding fields. Indices count toward
//! exact TYPE arity but are not consumed as constructor parameters.
//!
//! Separate inductive and constructor universe parameter lists are retained:
//! inference instantiates with the INDUCTIVE list; agreement with the stored
//! constructor signature requires ordered equality, not merely equal lengths.
//! This module neither adds that equality as an invented runtime guard nor
//! proves arbitrary declaration metadata coherent. Prop checking, caches,
//! subject-type/name validation, projection beta, dependent field typing,
//! preservation and production Rust refinement remain outside this slice.
//! In particular, the reused WHNF model has no new projection-head extraction:
//! these are honest computations in that partial model, not a source-complete
//! Pi-view evaluator for expressions requiring projection beta.

use crate::spec::error::SpecError;
use crate::spec::Specification;

impl Specification {
    /// Requires the existing whnf_fuel_red_wh3, signature, telescope/list,
    /// closed_at_b soundness, and parallel-substitution closedness stages.
    /// Registered in the full bundle, not the smaller substitution bundle.
    pub(super) fn add_projection_telescope(&mut self) -> Result<(), SpecError> {
        self.add_inductive(
            r"inductive ProjectionPiView : Type
| nonPi : ProjectionPiView
| pi : KExpr -> KExpr -> ProjectionPiView",
            "A completed Pi view distinguishes non-Pi from a Pi domain and body. The surrounding Option separately records WHNF exhaustion.",
        )?;
        for (source, description) in [
            (
                r"def projection_raw_pi (t : KExpr) : ProjectionPiView := match t with
| KExpr.sort u => ProjectionPiView.nonPi
| KExpr.bvar i => ProjectionPiView.nonPi
| KExpr.app f a => ProjectionPiView.nonPi
| KExpr.lam A b => ProjectionPiView.nonPi
| KExpr.pi A B => ProjectionPiView.pi A B
| KExpr.const n us => ProjectionPiView.nonPi
| KExpr.let_ A v b => ProjectionPiView.nonPi
| KExpr.proj S i e => ProjectionPiView.nonPi
| KExpr.lit n => ProjectionPiView.nonPi",
                "Raw syntactic Pi inspection; this does not normalize or infer a field type.",
            ),
            (
                r"def projection_whnf_pi (R : RedEnv) (fuel : Nat) (t : KExpr) : OptionType ProjectionPiView :=
opt_bind KExpr ProjectionPiView (whnf_fuel_red_wh3 R fuel t)
 (fun (w : KExpr) => @OptionType.some ProjectionPiView (projection_raw_pi w))",
                "An actual finite call to the existing three-way modeled WHNF evaluator, followed by raw Pi inspection. None means exhaustion, not successful non-Pi.",
            ),
            (
                r"def projection_pi_view (R : RedEnv) (fuel : Nat) (t : KExpr) : OptionType ProjectionPiView :=
@ProjectionPiView.rec (fun (_ : ProjectionPiView) => OptionType ProjectionPiView)
 (projection_whnf_pi R fuel t)
 (fun (A : KExpr) (B : KExpr) => @OptionType.some ProjectionPiView (ProjectionPiView.pi A B))
 (projection_raw_pi t)",
                "Source-shaped field Pi view: raw Pi fast-path; only other shapes call WHNF. A raw Pi therefore succeeds even at zero WHNF fuel.",
            ),
            (
                r"def projection_parameter_step (original : KExpr) (arg : KExpr)
 (next : KExpr -> OptionType KExpr) (view : ProjectionPiView) : OptionType KExpr :=
@ProjectionPiView.rec (fun (_ : ProjectionPiView) => OptionType KExpr)
 (@OptionType.some KExpr original)
 (fun (_A : KExpr) (B : KExpr) => next (instantiate B arg)) view",
                "Parameter step: a completed non-Pi stops and returns the ORIGINAL current expression; a Pi consumes one parameter and continues with its instantiated body.",
            ),
            (
                r"def projection_parameter_prefix (R : RedEnv) (fuel : Nat) (t : KExpr)
 (args : ListType KExpr) : OptionType KExpr :=
@ListType.rec KExpr (fun (_ : ListType KExpr) => KExpr -> OptionType KExpr)
 (fun (current : KExpr) => @OptionType.some KExpr current)
 (fun (arg : KExpr) (_rest : ListType KExpr) (next : KExpr -> OptionType KExpr)
 (current : KExpr) => opt_bind ProjectionPiView KExpr (projection_whnf_pi R fuel current)
   (projection_parameter_step current arg next)) args t",
                "Finite source-shaped instantiate_params loop. Unlike field Pi views, it calls WHNF even for a raw Pi. Exhaustion is retained; premature non-Pi discards the remaining parameter requests.",
            ),
            (
                r"def projection_field_body (B : KExpr) (p : KExpr) : KExpr :=
@Bool.rec (fun (_ : Bool) => KExpr) (instantiate B p) B (closed_at_b B Nat.zero)",
                "Dependent body update, retaining the source's no-loose-bound-variable shortcut via the existing modeled depth-aware closedness test.",
            ),
            (
                r"def projection_field_step (S : Name) (e : KExpr) (j : Nat) (remaining : Nat)
 (next : Nat -> KExpr -> OptionType (ListType KExpr))
 (view : ProjectionPiView) : OptionType (ListType KExpr) :=
@ProjectionPiView.rec (fun (_ : ProjectionPiView) => OptionType (ListType KExpr))
 (@OptionType.none (ListType KExpr))
 (fun (A : KExpr) (B : KExpr) => @Nat.rec
   (fun (_ : Nat) => OptionType (ListType KExpr))
   (@OptionType.some (ListType KExpr) (@ListType.cons KExpr A (@ListType.nil KExpr)))
   (fun (_k : Nat) (_unused : OptionType (ListType KExpr)) =>
     opt_bind (ListType KExpr) (ListType KExpr)
       (next (Nat.succ j) (projection_field_body B (KExpr.proj S j e)))
       (fun (tail : ListType KExpr) => @OptionType.some (ListType KExpr) (@ListType.cons KExpr A tail)))
   remaining) view",
                "One field-prefix step: non-Pi refuses; the final visited field returns its domain without a tail update; preceding fields substitute Proj(S,j,e), then prepend the actual domain.",
            ),
            (
                r"def projection_field_prefix (R : RedEnv) (fuel : Nat) (S : Name) (e : KExpr)
 (count : Nat) (j : Nat) (t : KExpr) : OptionType (ListType KExpr) :=
@Nat.rec (fun (_ : Nat) => Nat -> KExpr -> OptionType (ListType KExpr))
 (fun (_j : Nat) (_current : KExpr) => @OptionType.some (ListType KExpr) (@ListType.nil KExpr))
 (fun (remaining : Nat) (next : Nat -> KExpr -> OptionType (ListType KExpr))
   (index : Nat) (current : KExpr) =>
   opt_bind ProjectionPiView (ListType KExpr) (projection_pi_view R fuel current)
     (projection_field_step S e index remaining next)) count j t",
                "Computed finite field-domain prefix. Count is a visited-prefix length, not a claim about complete metadata, Prop eligibility, cache writes or field typing.",
            ),
            (
                r"def projection_ctor_type (indParams : ListType Name) (ctor : KConstSig)
 (us : ListType Level) : KExpr :=
@ListType.rec Name (fun (_ : ListType Name) => KExpr) (kconst_type ctor)
 (fun (_p : Name) (_ps : ListType Name) (_unused : KExpr) =>
   instLevels indParams (kconst_type ctor) us) indParams",
                "Instantiate with the inductive's ordered universe parameters, preserving the source's empty-parameter fast-path. The constructor signature's own list remains separately available.",
            ),
            (
                r"def projection_count_guard (expected : Nat) (actual : Nat) (next : OptionType KExpr) : OptionType KExpr :=
@Bool.rec (fun (_ : Bool) => OptionType KExpr) (@OptionType.none KExpr) next (nat_eqb expected actual)",
                "Computed exact-count guard, used independently for universe arguments and TYPE arguments.",
            ),
            (
                r"def projection_telescope_start (R : RedEnv) (fuel : Nat)
 (indParams : ListType Name) (ctor : KConstSig) (ctorNumParams : Nat) (indNumIndices : Nat)
 (us : ListType Level) (typeArgs : ListType KExpr) : OptionType KExpr :=
projection_count_guard (name_list_len indParams) (level_list_len us)
 (projection_count_guard (Nat.add ctorNumParams indNumIndices) (list_length typeArgs)
   (projection_parameter_prefix R fuel (projection_ctor_type indParams ctor us)
     (list_take ctorNumParams typeArgs)))",
                "Guarded telescope start after metadata resolution: exact inductive universe arity and ctor-parameter-plus-inductive-index TYPE arity; only ctor parameters are consumed, never indices.",
            ),
            (
                r"def projection_telescope_fields (R : RedEnv) (fuel : Nat) (S : Name) (e : KExpr)
 (indParams : ListType Name) (ctor : KConstSig) (np : Nat) (ni : Nat)
 (us : ListType Level) (args : ListType KExpr) (count : Nat) : OptionType (ListType KExpr) :=
opt_bind KExpr (ListType KExpr) (projection_telescope_start R fuel indParams ctor np ni us args)
 (fun (t : KExpr) => projection_field_prefix R fuel S e count Nat.zero t)",
                "Connected guarded-start and dependent field-prefix computation. The requested count is an explicit prefix length; field-bound metadata checking, Prop validation and caching are not claimed.",
            ),
            (
                r"def ProjectionUniverseCoherence (indParams : ListType Name) (ctor : KConstSig) : Prop :=
@Eq (ListType Name) indParams (kconst_params ctor)",
                "Explicit ordered inductive/constructor parameter coherence. It is a declaration invariant, not an additional guard claimed to exist in Rust.",
            ),
            (
                r"def ProjectionParameterGraph (R : RedEnv) (fuel : Nat) (t : KExpr)
 (args : ListType KExpr) (out : KExpr) : Prop :=
@Eq (OptionType KExpr) (projection_parameter_prefix R fuel t args) (@OptionType.some KExpr out)",
                "Graph of the actual fixed-fuel parameter computation, not a caller-supplied typing oracle or arbitrary reduction trace.",
            ),
            (
                r"def ProjectionFieldGraph (R : RedEnv) (fuel : Nat) (S : Name) (e : KExpr)
 (count : Nat) (j : Nat) (t : KExpr) (domains : ListType KExpr) : Prop :=
@Eq (OptionType (ListType KExpr)) (projection_field_prefix R fuel S e count j t)
 (@OptionType.some (ListType KExpr) domains)",
                "Graph of the actual computed field-domain prefix. Fixing fuel makes the computation deterministic without assuming arbitrary WHNF trace uniqueness.",
            ),
            (
                r"def projection_pi_raw_fastpath (R : RedEnv) (fuel : Nat) (A : KExpr) (B : KExpr) :
@Eq (OptionType ProjectionPiView) (projection_pi_view R fuel (KExpr.pi A B))
 (@OptionType.some ProjectionPiView (ProjectionPiView.pi A B)) :=
@Eq.refl (OptionType ProjectionPiView) (@OptionType.some ProjectionPiView (ProjectionPiView.pi A B))",
                "Every raw Pi bypasses the actual WHNF evaluator, including at fuel zero.",
            ),
            (
                r"def projection_parameter_prefix_cons_inv (R : RedEnv) (fuel : Nat) (t : KExpr)
 (arg : KExpr) (rest : ListType KExpr) (out : KExpr)
 (h : ProjectionParameterGraph R fuel t (@ListType.cons KExpr arg rest) out)
 (C : Type) (consume : forall (view : ProjectionPiView),
   @Eq (OptionType ProjectionPiView) (projection_whnf_pi R fuel t) (@OptionType.some ProjectionPiView view) ->
   @Eq (OptionType KExpr)
     (projection_parameter_step t arg (fun (next : KExpr) => projection_parameter_prefix R fuel next rest) view)
     (@OptionType.some KExpr out) -> C) : C :=
opt_bind_some_inv_type ProjectionPiView KExpr (projection_whnf_pi R fuel t)
 (projection_parameter_step t arg (fun (next : KExpr) => projection_parameter_prefix R fuel next rest))
 out C h consume",
                "A successful nonempty parameter graph exposes its ACTUAL completed WHNF/Pi-view call and step equation, preserving both Pi continuation and premature non-Pi stop cases.",
            ),
            (
                r"def projection_field_prefix_succ_inv (R : RedEnv) (fuel : Nat) (S : Name) (e : KExpr)
 (remaining : Nat) (j : Nat) (t : KExpr) (domains : ListType KExpr)
 (h : ProjectionFieldGraph R fuel S e (Nat.succ remaining) j t domains)
 (C : Type) (consume : forall (A : KExpr) (B : KExpr),
   @Eq (OptionType ProjectionPiView) (projection_pi_view R fuel t)
     (@OptionType.some ProjectionPiView (ProjectionPiView.pi A B)) ->
   @Eq (OptionType (ListType KExpr))
     (projection_field_step S e j remaining
       (fun (index : Nat) (current : KExpr) => projection_field_prefix R fuel S e remaining index current)
       (ProjectionPiView.pi A B)) (@OptionType.some (ListType KExpr) domains) -> C) : C :=
opt_bind_some_inv_type ProjectionPiView (ListType KExpr) (projection_pi_view R fuel t)
 (projection_field_step S e j remaining
   (fun (index : Nat) (current : KExpr) => projection_field_prefix R fuel S e remaining index current))
 domains C h
 (fun (view : ProjectionPiView) =>
   @ProjectionPiView.rec (fun (v : ProjectionPiView) =>
     @Eq (OptionType ProjectionPiView) (projection_pi_view R fuel t) (@OptionType.some ProjectionPiView v) ->
     @Eq (OptionType (ListType KExpr))
       (projection_field_step S e j remaining
         (fun (index : Nat) (current : KExpr) => projection_field_prefix R fuel S e remaining index current) v)
       (@OptionType.some (ListType KExpr) domains) -> C)
   (fun (_hq : @Eq (OptionType ProjectionPiView) (projection_pi_view R fuel t)
       (@OptionType.some ProjectionPiView ProjectionPiView.nonPi))
     (hn : @Eq (OptionType (ListType KExpr)) (@OptionType.none (ListType KExpr))
       (@OptionType.some (ListType KExpr) domains)) => option_none_ne_some_type (ListType KExpr) domains C hn)
   (fun (A : KExpr) (B : KExpr) => consume A B) view)",
                "A successful nonempty field graph yields real Pi domain/body and its computed Pi-view equation; completed non-Pi is eliminated by its actual none result, not a field-typing premise.",
            ),
            (
                r"def projection_parameter_graph_unique (R : RedEnv) (fuel : Nat) (t : KExpr)
 (args : ListType KExpr) (a : KExpr) (b : KExpr)
 (ha : ProjectionParameterGraph R fuel t args a) (hb : ProjectionParameterGraph R fuel t args b) : @Eq KExpr a b :=
option_some_inj KExpr a b (Eq.trans (OptionType KExpr) (@OptionType.some KExpr a)
 (projection_parameter_prefix R fuel t args) (@OptionType.some KExpr b)
 (Eq.symm (OptionType KExpr) (projection_parameter_prefix R fuel t args) (@OptionType.some KExpr a) ha) hb)",
                "Only same-input, same-fuel graph uniqueness; no uniqueness assumption about arbitrary modeled reduction traces.",
            ),
            (
                r"def projection_field_graph_unique (R : RedEnv) (fuel : Nat) (S : Name) (e : KExpr)
 (count : Nat) (j : Nat) (t : KExpr) (domainsA : ListType KExpr) (domainsB : ListType KExpr)
 (ha : ProjectionFieldGraph R fuel S e count j t domainsA)
 (hb : ProjectionFieldGraph R fuel S e count j t domainsB) : @Eq (ListType KExpr) domainsA domainsB :=
option_some_inj (ListType KExpr) domainsA domainsB
 (Eq.trans (OptionType (ListType KExpr)) (@OptionType.some (ListType KExpr) domainsA)
 (projection_field_prefix R fuel S e count j t) (@OptionType.some (ListType KExpr) domainsB)
 (Eq.symm (OptionType (ListType KExpr)) (projection_field_prefix R fuel S e count j t)
   (@OptionType.some (ListType KExpr) domainsA) ha) hb)",
                "Computed field-domain prefixes are unique at the same explicit call budget; no cross-fuel or nondeterministic-trace theorem is asserted.",
            ),
            (
                r"def projection_field_body_closed (B : KExpr) (p : KExpr)
 (h : @Eq Bool (closed_at_b B Nat.zero) Bool.true) : @Eq KExpr (instantiate B p) B :=
Eq.trans KExpr (instantiate B p) (psubst (scons p idsubst) B) B
 (instantiate_eq_psubst B p)
 (psubst_closed_id (scons p idsubst) B (closed_at_b_sound B Nat.zero h))",
                "The shortcut's true branch is justified by existing checker soundness and closed parallel-substitution identity, rather than a no-occurrence-of-index-zero approximation.",
            ),
            (
                r"def projection_field_body_eq_instantiate (B : KExpr) (p : KExpr) :
@Eq KExpr (projection_field_body B p) (instantiate B p) :=
@Bool.rec (fun (b : Bool) => @Eq Bool (closed_at_b B Nat.zero) b ->
 @Eq KExpr (@Bool.rec (fun (_ : Bool) => KExpr) (instantiate B p) B b) (instantiate B p))
 (fun (_h : @Eq Bool (closed_at_b B Nat.zero) Bool.false) => @Eq.refl KExpr (instantiate B p))
 (fun (h : @Eq Bool (closed_at_b B Nat.zero) Bool.true) =>
   Eq.symm KExpr (instantiate B p) B (projection_field_body_closed B p h))
 (closed_at_b B Nat.zero) (@Eq.refl Bool (closed_at_b B Nat.zero))",
                "For every body, the computed shortcut equals actual instantiate, including loose variables other than index zero.",
            ),
            (
                r"def projection_count_guard_inv (expected : Nat) (actual : Nat) (next : OptionType KExpr)
 (out : KExpr) (h : @Eq (OptionType KExpr) (projection_count_guard expected actual next) (@OptionType.some KExpr out))
 (C : Type) (consume : @Eq Nat expected actual -> @Eq (OptionType KExpr) next (@OptionType.some KExpr out) -> C) : C :=
@Bool.rec (fun (b : Bool) => @Eq Bool (nat_eqb expected actual) b ->
 @Eq (OptionType KExpr) (@Bool.rec (fun (_ : Bool) => OptionType KExpr) (@OptionType.none KExpr) next b)
 (@OptionType.some KExpr out) -> C)
 (fun (_hb : @Eq Bool (nat_eqb expected actual) Bool.false)
   (hn : @Eq (OptionType KExpr) (@OptionType.none KExpr) (@OptionType.some KExpr out)) =>
   option_none_ne_some_type KExpr out C hn)
 (fun (hb : @Eq Bool (nat_eqb expected actual) Bool.true)
   (hs : @Eq (OptionType KExpr) next (@OptionType.some KExpr out)) =>
   consume (nat_eqb_eq expected actual hb) hs)
 (nat_eqb expected actual) (@Eq.refl Bool (nat_eqb expected actual)) h",
                "A successful computed count guard entails exact Nat equality and preserves the continuation's actual successful equation.",
            ),
            (
                r"def projection_count_guard_wrong (expected : Nat) (actual : Nat) (next : OptionType KExpr)
 (bad : @Eq Nat expected actual -> Empty) :
@Eq (OptionType KExpr) (projection_count_guard expected actual next) (@OptionType.none KExpr) :=
@Bool.rec (fun (b : Bool) => @Eq Bool (nat_eqb expected actual) b ->
 @Eq (OptionType KExpr) (@Bool.rec (fun (_ : Bool) => OptionType KExpr) (@OptionType.none KExpr) next b)
   (@OptionType.none KExpr))
 (fun (_hb : @Eq Bool (nat_eqb expected actual) Bool.false) => @Eq.refl (OptionType KExpr) (@OptionType.none KExpr))
 (fun (hb : @Eq Bool (nat_eqb expected actual) Bool.true) =>
   @Empty.rec (fun (_ : Empty) => @Eq (OptionType KExpr) next (@OptionType.none KExpr))
     (bad (nat_eqb_eq expected actual hb)))
 (nat_eqb expected actual) (@Eq.refl Bool (nat_eqb expected actual))",
                "Every refuted exact count forces the computed guard to none, using proved Boolean equality reflection.",
            ),
            (
                r"def projection_count_guard_none (expected : Nat) (actual : Nat) :
@Eq (OptionType KExpr) (projection_count_guard expected actual (@OptionType.none KExpr)) (@OptionType.none KExpr) :=
@Bool.rec (fun (b : Bool) => @Eq (OptionType KExpr)
 (@Bool.rec (fun (_ : Bool) => OptionType KExpr) (@OptionType.none KExpr) (@OptionType.none KExpr) b)
 (@OptionType.none KExpr))
 (@Eq.refl (OptionType KExpr) (@OptionType.none KExpr))
 (@Eq.refl (OptionType KExpr) (@OptionType.none KExpr)) (nat_eqb expected actual)",
                "An already failed continuation cannot become success through either count-guard branch.",
            ),
            (
                r"def projection_telescope_wrong_universe_arity (R : RedEnv) (fuel : Nat)
 (indParams : ListType Name) (ctor : KConstSig) (np : Nat) (ni : Nat)
 (us : ListType Level) (args : ListType KExpr)
 (bad : @Eq Nat (name_list_len indParams) (level_list_len us) -> Empty) :
@Eq (OptionType KExpr) (projection_telescope_start R fuel indParams ctor np ni us args) (@OptionType.none KExpr) :=
projection_count_guard_wrong (name_list_len indParams) (level_list_len us)
 (projection_count_guard (Nat.add np ni) (list_length args)
   (projection_parameter_prefix R fuel (projection_ctor_type indParams ctor us) (list_take np args))) bad",
                "Universal universe-arity refusal, independent of the constructor type, reduction environment, fuel and supplied TYPE arguments.",
            ),
            (
                r"def projection_telescope_wrong_type_arity (R : RedEnv) (fuel : Nat)
 (indParams : ListType Name) (ctor : KConstSig) (np : Nat) (ni : Nat)
 (us : ListType Level) (args : ListType KExpr)
 (bad : @Eq Nat (Nat.add np ni) (list_length args) -> Empty) :
@Eq (OptionType KExpr) (projection_telescope_start R fuel indParams ctor np ni us args) (@OptionType.none KExpr) :=
Eq.trans (OptionType KExpr) (projection_telescope_start R fuel indParams ctor np ni us args)
 (projection_count_guard (name_list_len indParams) (level_list_len us) (@OptionType.none KExpr)) (@OptionType.none KExpr)
 (Eq.cong (OptionType KExpr) (OptionType KExpr)
   (projection_count_guard (name_list_len indParams) (level_list_len us))
   (projection_count_guard (Nat.add np ni) (list_length args)
     (projection_parameter_prefix R fuel (projection_ctor_type indParams ctor us) (list_take np args)))
   (@OptionType.none KExpr)
   (projection_count_guard_wrong (Nat.add np ni) (list_length args)
     (projection_parameter_prefix R fuel (projection_ctor_type indParams ctor us) (list_take np args)) bad))
 (projection_count_guard_none (name_list_len indParams) (level_list_len us))",
                "Universal TYPE-arity refusal checks ctor parameters PLUS inductive indices; it holds regardless of the universe guard and cannot be bypassed by a premature parameter stop.",
            ),
            (
                r"def projection_telescope_start_inv (R : RedEnv) (fuel : Nat)
 (indParams : ListType Name) (ctor : KConstSig) (np : Nat) (ni : Nat)
 (us : ListType Level) (args : ListType KExpr) (out : KExpr)
 (h : @Eq (OptionType KExpr) (projection_telescope_start R fuel indParams ctor np ni us args)
   (@OptionType.some KExpr out)) (C : Type)
 (consume : @Eq Nat (name_list_len indParams) (level_list_len us) ->
   @Eq Nat (Nat.add np ni) (list_length args) ->
   ProjectionParameterGraph R fuel (projection_ctor_type indParams ctor us) (list_take np args) out -> C) : C :=
projection_count_guard_inv (name_list_len indParams) (level_list_len us)
 (projection_count_guard (Nat.add np ni) (list_length args)
   (projection_parameter_prefix R fuel (projection_ctor_type indParams ctor us) (list_take np args))) out h C
 (fun (hu : @Eq Nat (name_list_len indParams) (level_list_len us))
   (ht : @Eq (OptionType KExpr) (projection_count_guard (Nat.add np ni) (list_length args)
     (projection_parameter_prefix R fuel (projection_ctor_type indParams ctor us) (list_take np args)))
       (@OptionType.some KExpr out)) =>
   projection_count_guard_inv (Nat.add np ni) (list_length args)
     (projection_parameter_prefix R fuel (projection_ctor_type indParams ctor us) (list_take np args)) out ht C
     (fun (ha : @Eq Nat (Nat.add np ni) (list_length args))
       (hp : ProjectionParameterGraph R fuel (projection_ctor_type indParams ctor us) (list_take np args) out) =>
       consume hu ha hp))",
                "Invert a successful guarded telescope start into both exact arities and the real parameter-prefix graph, without assuming output typing.",
            ),
            (
                r"def projection_ordered_instantiation_coherent (indParams : ListType Name) (ctor : KConstSig)
 (us : ListType Level) (h : ProjectionUniverseCoherence indParams ctor) :
@Eq KExpr (instLevels indParams (kconst_type ctor) us) (kconst_inst_type ctor us) :=
Eq.cong (ListType Name) KExpr (fun (ps : ListType Name) => instLevels ps (kconst_type ctor) us)
 indParams (kconst_params ctor) h",
                "Ordered parameter-list coherence justifies using the inductive substitution for a constructor signature. Equal lengths alone do not justify this transport.",
            ),
        ] {
            self.add_recursive_def(source, description)?;
        }
        self.add_projection_telescope_witnesses()
    }

    fn add_projection_telescope_witnesses(&mut self) -> Result<(), SpecError> {
        for (source, description) in [
            (
                r"def projection_fixture_R : RedEnv := RedEnv.mk RecEnv.empty DefEnv.empty IndCtorEnv.empty",
                "An explicit empty reduction environment for concrete computations; no environment typing/coherence claim.",
            ),
            (
                r"def projection_fixture_one : Nat := Nat.succ Nat.zero",
                "One, as a transparent model numeral.",
            ),
            (
                r"def projection_fixture_two : Nat := Nat.succ projection_fixture_one",
                "Two, as a transparent model numeral.",
            ),
            (
                r"def projection_fixture_subject : KExpr := KExpr.bvar Nat.zero",
                "A symbolic subject; the computation does not claim the subject is well typed.",
            ),
            (
                r"def projection_fixture_nat : KExpr := KExpr.const (Name.str Name.anonymous Nat.zero) (@ListType.nil Level)",
                "Model-local Nat-shaped name, not a reflected source-name correspondence claim.",
            ),
            (
                r"def projection_fixture_dep_pair : KConstSig := KConstSig.mk (@ListType.nil Name)
 (KExpr.pi (KExpr.sort (Level.succ Level.zero))
   (KExpr.pi (KExpr.bvar Nat.zero) (KExpr.const Name.anonymous (@ListType.nil Level))))",
                "DepPair.mk : (A : Type) -> A -> DepPair. Its second field domain depends on the first field.",
            ),
            (
                r"def projection_dep_pair_field1 : ProjectionFieldGraph projection_fixture_R Nat.zero
 Name.anonymous projection_fixture_subject projection_fixture_two Nat.zero
 (kconst_type projection_fixture_dep_pair)
 (@ListType.cons KExpr (KExpr.sort (Level.succ Level.zero))
   (@ListType.cons KExpr (KExpr.proj Name.anonymous Nat.zero projection_fixture_subject) (@ListType.nil KExpr))) :=
@Eq.refl (OptionType (ListType KExpr)) (@OptionType.some (ListType KExpr)
 (@ListType.cons KExpr (KExpr.sort (Level.succ Level.zero))
   (@ListType.cons KExpr (KExpr.proj Name.anonymous Nat.zero projection_fixture_subject) (@ListType.nil KExpr))))",
                "Actual computed DepPair field1 is Proj(DepPair,0,e), not an oracle-provided type or an already reduced Nat. Raw Pi views need no WHNF fuel.",
            ),
            (
                r"def projection_dep_pair_connected : @Eq (OptionType (ListType KExpr))
 (projection_telescope_fields projection_fixture_R Nat.zero Name.anonymous projection_fixture_subject
   (@ListType.nil Name) projection_fixture_dep_pair Nat.zero Nat.zero (@ListType.nil Level)
   (@ListType.nil KExpr) projection_fixture_two)
 (@OptionType.some (ListType KExpr)
   (@ListType.cons KExpr (KExpr.sort (Level.succ Level.zero))
     (@ListType.cons KExpr (KExpr.proj Name.anonymous Nat.zero projection_fixture_subject) (@ListType.nil KExpr)))) :=
projection_dep_pair_field1",
                "The dependent DepPair result is reached through the connected exact-arity guard, actual parameter-prefix computation and field-prefix walk.",
            ),
            (
                r"def projection_fixture_family : KExpr := KExpr.const (Name.str Name.anonymous projection_fixture_one) (@ListType.nil Level)",
                "A symbolic dependent family F; no family-typing assumption is used in the computation.",
            ),
            (
                r"def projection_fixture_succ : KExpr := KExpr.const (Name.str Name.anonymous projection_fixture_two) (@ListType.nil Level)",
                "A symbolic succ constant used to retain the indexed result I(succ n).",
            ),
            (
                r"def projection_fixture_indexed : KConstSig := KConstSig.mk (@ListType.nil Name)
 (KExpr.pi projection_fixture_nat
   (KExpr.pi (KExpr.app projection_fixture_family (KExpr.bvar Nat.zero))
     (KExpr.app (KExpr.const Name.anonymous (@ListType.nil Level))
       (KExpr.app projection_fixture_succ (KExpr.bvar projection_fixture_one)))))",
                "Indexed constructor: (n : Nat) -> F n -> I(succ n). Zero constructor parameters, one inductive index, two fields; the constructor result keeps its binder-depth-one n.",
            ),
            (
                r"def projection_indexed_start_keeps_index (index : KExpr) :
@Eq (OptionType KExpr)
 (projection_telescope_start projection_fixture_R Nat.zero (@ListType.nil Name)
   projection_fixture_indexed Nat.zero projection_fixture_one (@ListType.nil Level)
   (@ListType.cons KExpr index (@ListType.nil KExpr)))
 (@OptionType.some KExpr (kconst_type projection_fixture_indexed)) :=
@Eq.refl (OptionType KExpr) (@OptionType.some KExpr (kconst_type projection_fixture_indexed))",
                "The supplied TYPE index satisfies exact p+k arity but is not consumed as a constructor parameter; the complete two-field telescope is retained.",
            ),
            (
                r"def projection_indexed_field1 : ProjectionFieldGraph projection_fixture_R Nat.zero
 Name.anonymous projection_fixture_subject projection_fixture_two Nat.zero
 (kconst_type projection_fixture_indexed)
 (@ListType.cons KExpr projection_fixture_nat
   (@ListType.cons KExpr (KExpr.app projection_fixture_family
     (KExpr.proj Name.anonymous Nat.zero projection_fixture_subject)) (@ListType.nil KExpr))) :=
@Eq.refl (OptionType (ListType KExpr)) (@OptionType.some (ListType KExpr)
 (@ListType.cons KExpr projection_fixture_nat
   (@ListType.cons KExpr (KExpr.app projection_fixture_family
     (KExpr.proj Name.anonymous Nat.zero projection_fixture_subject)) (@ListType.nil KExpr))))",
                "The indexed dependent field1 computes to F(Proj(I,0,e)); substituting the TYPE index as a constructor parameter would give a different result.",
            ),
            (
                r"def projection_indexed_connected (n : KExpr) : @Eq (OptionType (ListType KExpr))
 (projection_telescope_fields projection_fixture_R Nat.zero Name.anonymous projection_fixture_subject
   (@ListType.nil Name) projection_fixture_indexed Nat.zero projection_fixture_one (@ListType.nil Level)
   (@ListType.cons KExpr (KExpr.app projection_fixture_succ n) (@ListType.nil KExpr)) projection_fixture_two)
 (@OptionType.some (ListType KExpr)
   (@ListType.cons KExpr projection_fixture_nat
     (@ListType.cons KExpr (KExpr.app projection_fixture_family
       (KExpr.proj Name.anonymous Nat.zero projection_fixture_subject)) (@ListType.nil KExpr)))) :=
projection_indexed_field1",
                "Connected computation at the indexed TYPE I(succ n): that index is counted but not substituted as a parameter, and field1 is F(Proj(I,0,e)).",
            ),
            (
                r"def projection_parameter_and_index_distinct (index : KExpr) :
@Eq (OptionType (ListType KExpr))
 (projection_telescope_fields projection_fixture_R projection_fixture_one Name.anonymous projection_fixture_subject
   (@ListType.nil Name)
   (KConstSig.mk (@ListType.nil Name)
     (KExpr.pi (KExpr.sort (Level.succ Level.zero))
       (KExpr.pi (KExpr.bvar Nat.zero)
         (KExpr.pi (KExpr.bvar projection_fixture_one) (KExpr.const Name.anonymous (@ListType.nil Level))))))
   projection_fixture_one projection_fixture_one (@ListType.nil Level)
   (@ListType.cons KExpr projection_fixture_nat (@ListType.cons KExpr index (@ListType.nil KExpr)))
   projection_fixture_two)
 (@OptionType.some (ListType KExpr)
   (@ListType.cons KExpr projection_fixture_nat (@ListType.cons KExpr projection_fixture_nat (@ListType.nil KExpr)))) :=
@Eq.refl (OptionType (ListType KExpr)) (@OptionType.some (ListType KExpr)
 (@ListType.cons KExpr projection_fixture_nat (@ListType.cons KExpr projection_fixture_nat (@ListType.nil KExpr))))",
                "A nonempty parameter prefix actually invokes WHNF and consumes the supplied Nat type, while a separate supplied index is only counted. Both resulting field domains are computed Nat.",
            ),
            (
                r"def projection_type_missing_refused :
@Eq (OptionType KExpr) (projection_telescope_start projection_fixture_R Nat.zero
 (@ListType.nil Name) projection_fixture_indexed Nat.zero projection_fixture_one
 (@ListType.nil Level) (@ListType.nil KExpr)) (@OptionType.none KExpr) :=
@Eq.refl (OptionType KExpr) (@OptionType.none KExpr)",
                "Concrete missing TYPE argument refusal in the same indexed declaration.",
            ),
            (
                r"def projection_type_extra_refused (a : KExpr) (b : KExpr) :
@Eq (OptionType KExpr) (projection_telescope_start projection_fixture_R Nat.zero
 (@ListType.nil Name) projection_fixture_indexed Nat.zero projection_fixture_one
 (@ListType.nil Level) (@ListType.cons KExpr a (@ListType.cons KExpr b (@ListType.nil KExpr))))
 (@OptionType.none KExpr) := @Eq.refl (OptionType KExpr) (@OptionType.none KExpr)",
                "Concrete extra TYPE argument refusal, not merely a missing-argument guard.",
            ),
            (
                r"def projection_fixture_poly : KConstSig := KConstSig.mk
 (@ListType.cons Name Name.anonymous (@ListType.nil Name))
 (KExpr.pi (KExpr.sort (Level.param Name.anonymous))
   (KExpr.pi (KExpr.bvar Nat.zero) (KExpr.sort Level.zero)))",
                "Polymorphic two-field telescope with one stored ordered universe parameter.",
            ),
            (
                r"def projection_poly_ordered_coherence : ProjectionUniverseCoherence
 (@ListType.cons Name Name.anonymous (@ListType.nil Name)) projection_fixture_poly :=
@Eq.refl (ListType Name) (@ListType.cons Name Name.anonymous (@ListType.nil Name))",
                "The positive polymorphic fixture explicitly discharges inductive-versus-constructor ordered parameter coherence.",
            ),
            (
                r"def projection_universe_missing_refused : @Eq (OptionType KExpr)
 (projection_telescope_start projection_fixture_R Nat.zero
   (@ListType.cons Name Name.anonymous (@ListType.nil Name)) projection_fixture_poly
   Nat.zero Nat.zero (@ListType.nil Level) (@ListType.nil KExpr)) (@OptionType.none KExpr) :=
@Eq.refl (OptionType KExpr) (@OptionType.none KExpr)",
                "Missing universe argument is refused before total instantiation's positional default can become a successful telescope result.",
            ),
            (
                r"def projection_universe_extra_refused (u : Level) (v : Level) : @Eq (OptionType KExpr)
 (projection_telescope_start projection_fixture_R Nat.zero
   (@ListType.cons Name Name.anonymous (@ListType.nil Name)) projection_fixture_poly
   Nat.zero Nat.zero (@ListType.cons Level u (@ListType.cons Level v (@ListType.nil Level)))
   (@ListType.nil KExpr)) (@OptionType.none KExpr) :=
@Eq.refl (OptionType KExpr) (@OptionType.none KExpr)",
                "Extra universe argument is also refused in the same stored declaration.",
            ),
            (
                r"def projection_polymorphic_start (u : Level) : @Eq (OptionType KExpr)
 (projection_telescope_start projection_fixture_R Nat.zero
   (@ListType.cons Name Name.anonymous (@ListType.nil Name)) projection_fixture_poly
   Nat.zero Nat.zero (@ListType.cons Level u (@ListType.nil Level)) (@ListType.nil KExpr))
 (@OptionType.some KExpr (KExpr.pi (KExpr.sort u)
   (KExpr.pi (KExpr.bvar Nat.zero) (KExpr.sort Level.zero)))) :=
@Eq.refl (OptionType KExpr) (@OptionType.some KExpr (KExpr.pi (KExpr.sort u)
 (KExpr.pi (KExpr.bvar Nat.zero) (KExpr.sort Level.zero))))",
                "Positive exact-arity computation uses the inductive parameter list; constructor-list agreement is separately witnessed above.",
            ),
            (
                r"def projection_fixture_two_params : ListType Name :=
@ListType.cons Name Name.anonymous (@ListType.cons Name (Name.str Name.anonymous Nat.zero) (@ListType.nil Name))",
                "Two distinct ordered universe parameter names for the order-sensitive control.",
            ),
            (
                r"def projection_fixture_reordered_params : ListType Name :=
@ListType.cons Name (Name.str Name.anonymous Nat.zero) (@ListType.cons Name Name.anonymous (@ListType.nil Name))",
                "The same two universe parameter names in reversed order; equal lengths are not ordered coherence.",
            ),
            (
                r"def projection_fixture_order_sensitive : KConstSig :=
KConstSig.mk projection_fixture_two_params (KExpr.sort (Level.param Name.anonymous))",
                "A stored constructor signature whose type observes the first original universe parameter.",
            ),
            (
                r"def projection_universe_reordered_computation : @Eq (OptionType KExpr)
 (projection_telescope_start projection_fixture_R Nat.zero projection_fixture_reordered_params
   projection_fixture_order_sensitive Nat.zero Nat.zero
   (@ListType.cons Level Level.zero (@ListType.cons Level (Level.succ Level.zero) (@ListType.nil Level)))
   (@ListType.nil KExpr)) (@OptionType.some KExpr (KExpr.sort (Level.succ Level.zero))) :=
@Eq.refl (OptionType KExpr) (@OptionType.some KExpr (KExpr.sort (Level.succ Level.zero)))",
                "The runtime-shaped guard permits equal-length reordered metadata and uses INDUCTIVE order, returning Sort1. No nonexistent coherence check is invented.",
            ),
            (
                r"def projection_universe_constructor_order_computation : @Eq KExpr
 (kconst_inst_type projection_fixture_order_sensitive
   (@ListType.cons Level Level.zero (@ListType.cons Level (Level.succ Level.zero) (@ListType.nil Level))))
 (KExpr.sort Level.zero) := @Eq.refl KExpr (KExpr.sort Level.zero)",
                "The SAME stored constructor signature and universe arguments use constructor order to give Sort0. This concrete contrast shows why ordered metadata coherence is a real separate premise.",
            ),
            (
                r"def projection_parameter_stop_original (arg : KExpr) (rest : ListType KExpr) :
ProjectionParameterGraph projection_fixture_R projection_fixture_two
 (KExpr.let_ (KExpr.sort Level.zero) (KExpr.sort Level.zero) (KExpr.bvar Nat.zero))
 (@ListType.cons KExpr arg rest)
 (KExpr.let_ (KExpr.sort Level.zero) (KExpr.sort Level.zero) (KExpr.bvar Nat.zero)) :=
@Eq.refl (OptionType KExpr) (@OptionType.some KExpr
 (KExpr.let_ (KExpr.sort Level.zero) (KExpr.sort Level.zero) (KExpr.bvar Nat.zero)))",
                "Nontrivial WHNF computes the let to a non-Pi Sort, yet the parameter loop returns the ORIGINAL let and ignores all remaining requests, exactly preserving the premature-stop behavior.",
            ),
            (
                r"def projection_parameter_exhaustion_refused (A : KExpr) (B : KExpr) (arg : KExpr) :
@Eq (OptionType KExpr) (projection_parameter_prefix projection_fixture_R Nat.zero
 (KExpr.pi A B) (@ListType.cons KExpr arg (@ListType.nil KExpr))) (@OptionType.none KExpr) :=
@Eq.refl (OptionType KExpr) (@OptionType.none KExpr)",
                "The parameter walk really calls WHNF even for raw Pi: zero fuel is not silently converted into a successful stop.",
            ),
            (
                r"def projection_field_nonpi_refused : @Eq (OptionType (ListType KExpr))
 (projection_field_prefix projection_fixture_R projection_fixture_one Name.anonymous
   projection_fixture_subject projection_fixture_one Nat.zero (KExpr.sort Level.zero))
 (@OptionType.none (ListType KExpr)) :=
@Eq.refl (OptionType (ListType KExpr)) (@OptionType.none (ListType KExpr))",
                "Completed non-Pi is a refusal in the FIELD loop, in contrast to the parameter loop's successful premature stop.",
            ),
            (
                r"def projection_field_body_loose_one (p : KExpr) :
@Eq KExpr (projection_field_body (KExpr.bvar projection_fixture_one) p) (KExpr.bvar Nat.zero) :=
@Eq.refl KExpr (KExpr.bvar Nat.zero)",
                "Loose bvar 1 must shift despite no occurrence of bvar 0; the computed shortcut uses full top-level closedness and does not incorrectly skip this update.",
            ),
        ] {
            self.add_recursive_def(source, description)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn projection_telescope_actual_declarations_parse() {
        let file = include_str!("projection_telescope.rs");
        let production = file
            .split("#[cfg(test)]")
            .next()
            .expect("production source");
        let mut declarations = 0;
        for piece in production.split("r\"").skip(1) {
            let source = piece.split('"').next().expect("raw declaration literal");
            assert!(source.starts_with("def ") || source.starts_with("inductive "));
            crate::test_utils::parse_check(source)
                .expect("projection telescope declaration parses");
            declarations += 1;
        }
        assert_eq!(declarations, 61);
        assert!(production.contains("whnf_fuel_red_wh3 R fuel t"));
        assert!(production.contains("KExpr.proj S j e"));
        assert!(!production.contains("par_reduces_cd_star_proj_inv"));
    }

    #[test]
    fn projection_telescope_equations_and_guard_controls_are_checked() {
        let mut spec = crate::test_utils::build_spec_with_stack();
        // This also permits a focused pre-registration invocation, without
        // accidentally adding duplicate declarations after bundle integration.
        if !spec
            .definitions()
            .contains_key("projection_telescope_start")
        {
            spec.add_projection_telescope()
                .expect("bounded projection slice");
        }
        for name in [
            "projection_pi_raw_fastpath",
            "projection_parameter_prefix_cons_inv",
            "projection_field_prefix_succ_inv",
            "projection_parameter_graph_unique",
            "projection_field_graph_unique",
            "projection_field_body_closed",
            "projection_field_body_eq_instantiate",
            "projection_count_guard_inv",
            "projection_count_guard_wrong",
            "projection_count_guard_none",
            "projection_telescope_wrong_universe_arity",
            "projection_telescope_wrong_type_arity",
            "projection_telescope_start_inv",
            "projection_ordered_instantiation_coherent",
            "projection_dep_pair_field1",
            "projection_dep_pair_connected",
            "projection_indexed_start_keeps_index",
            "projection_indexed_field1",
            "projection_indexed_connected",
            "projection_parameter_and_index_distinct",
            "projection_type_missing_refused",
            "projection_type_extra_refused",
            "projection_poly_ordered_coherence",
            "projection_universe_missing_refused",
            "projection_universe_extra_refused",
            "projection_polymorphic_start",
            "projection_universe_reordered_computation",
            "projection_universe_constructor_order_computation",
            "projection_parameter_stop_original",
            "projection_parameter_exhaustion_refused",
            "projection_field_nonpi_refused",
            "projection_field_body_loose_one",
        ] {
            let definition = spec
                .definitions()
                .get(name)
                .expect("checked projection declaration");
            assert!(!definition.is_axiom, "{name}");
            assert!(definition.elaborated_value.is_some(), "{name}");
            assert!(
                crate::spec_axiom_closure::computed_axiom_closure(&spec, name).is_empty(),
                "{name}"
            );
        }
        for source in [
            "def projection_forged_field_type : ProjectionFieldGraph projection_fixture_R Nat.zero Name.anonymous projection_fixture_subject projection_fixture_two Nat.zero (kconst_type projection_fixture_dep_pair) (@ListType.cons KExpr (KExpr.sort (Level.succ Level.zero)) (@ListType.cons KExpr projection_fixture_nat (@ListType.nil KExpr))) := @Eq.refl (OptionType (ListType KExpr)) (@OptionType.some (ListType KExpr) (@ListType.cons KExpr (KExpr.sort (Level.succ Level.zero)) (@ListType.cons KExpr projection_fixture_nat (@ListType.nil KExpr))))",
            "def projection_forged_order_coherence : ProjectionUniverseCoherence projection_fixture_reordered_params projection_fixture_order_sensitive := @Eq.refl (ListType Name) projection_fixture_reordered_params",
            "def projection_forged_exhaustion : ProjectionParameterGraph projection_fixture_R Nat.zero (KExpr.pi (KExpr.sort Level.zero) (KExpr.bvar Nat.zero)) (@ListType.cons KExpr projection_fixture_nat (@ListType.nil KExpr)) projection_fixture_nat := @Eq.refl (OptionType KExpr) (@OptionType.some KExpr projection_fixture_nat)",
        ] {
            assert!(
                spec.add_recursive_def(source, "Negative bounded projection control.").is_err(),
                "forged field type, ordered coherence or successful exhausted call must be refused"
            );
        }
    }
}
