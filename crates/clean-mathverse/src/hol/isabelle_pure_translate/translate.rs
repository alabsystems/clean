// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `translate_theorem` — the closure-replay entry point. Moved verbatim from the
//! original single-file module; behaviour is byte-identical.

use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Declaration, Expr};

use super::super::isabelle_pure::{IsaProof, IsaProvenTheorem};
use super::*;

/// Node cap on a ROOT proof for enabling the stage-3 Miller lane
/// ([`Ctx::bidir_redex`]). A large root proof produces a big assembled candidate
/// whose kernel re-check is expensive when the Miller solve makes it
/// "almost-right" (measured: multi-CPU-minute roots on the discharge-chain tail),
/// so above this the root keeps the stage-3 flag OFF and takes the pre-stage-3
/// (stage-1/2) path BYTE-IDENTICALLY — the redex-lane stage-2 β-redex expectation
/// still runs (it is gated on [`Ctx::bidir_tower`], unchanged). Small roots — the
/// genuine short discharge-chain flips — keep the Miller solve. Strictly additive
/// either way; the kernel re-check is the arbiter.
const MILLER_MAX_ROOT_PROOF_NODES: usize = 6000;

/// `true` iff proof `p` has at most `limit` structural nodes (spine + hypothesis
/// abstractions), with an EARLY EXIT once the count exceeds `limit` — an
/// `O(limit)` bound, never a full traversal of a huge proof. Only the recursive
/// proof children are counted (`AbsP`/`Abst` bodies, `AppP` both sides, `AppT`
/// function); embedded terms are not, since the kernel-check cost tracks the
/// proof's applicative structure.
pub(crate) fn isa_proof_within_size(p: &IsaProof, limit: usize) -> bool {
    fn go(p: &IsaProof, budget: &mut usize) -> bool {
        if *budget == 0 {
            return false;
        }
        *budget -= 1;
        match p {
            IsaProof::AbsP { b, .. } | IsaProof::Abst { b, .. } => go(b, budget),
            IsaProof::AppP { f, a } => go(f, budget) && go(a, budget),
            IsaProof::AppT { f, .. } => go(f, budget),
            _ => true,
        }
    }
    let mut budget = limit;
    go(p, &mut budget)
}

/// Translate a parsed theorem to a closed clean `Declaration::Theorem`.
///
/// Quantifies over discovered free type/term parameters so the result is closed
/// and (for the supported axioms) axiom-free. `closure` maps PThm serials to the
/// clean constant names of already-verified dependencies; `registry` maps
/// already-registered structured type classes to their clean def-consts, so
/// `OFCLASS('a, c_class)` premises embed to the real membership proposition.
///
/// This is the thin wrapper over [`translate_theorem_with_meta`] that drops the
/// discovered leading type-param keys (the metadata a verified-theorem closure
/// entry records so later fully-typed `PThm` references can specialize it
/// directly). Callers that build a [`ClosureEntry`] should prefer
/// [`translate_theorem_with_meta`] so the keys are recorded.
///
/// # Errors
/// Returns [`TranslateError`] if any node is unsupported, an axiom is unmapped,
/// or a PThm dependency is unresolved.
#[allow(clippy::too_many_arguments)]
pub fn translate_theorem(
    thm: &IsaProvenTheorem,
    closure: &Closure,
    registry: &ClassRegistry,
    method_registry: &MethodRegistry,
    instance_op_registry: &InstanceOpRegistry,
    list_fn_registry: &ListFnRegistry,
    poly_inst_registry: &PolyInstRegistry,
    membership: ClassMembership,
    method_embed: MethodEmbed,
    instance_embed: InstanceEmbed,
) -> Result<Declaration, TranslateError> {
    translate_theorem_with_meta(
        thm,
        closure,
        registry,
        method_registry,
        instance_op_registry,
        list_fn_registry,
        poly_inst_registry,
        membership,
        method_embed,
        instance_embed,
    )
    .map(|(decl, _meta)| decl)
}

/// Like [`translate_theorem_with_meta`] but with the namespace-crossed root
/// lane selectable ([`RootLane`]): `Off` is byte-identical to the historical
/// pipeline; `On` is used only by the driver's dedicated trailing escalation
/// modes (see [`Ctx::root_lane`]).
///
/// # Errors
/// Returns [`TranslateError`] if any node is unsupported, an axiom is unmapped,
/// or a PThm dependency is unresolved.
#[allow(clippy::too_many_arguments)]
pub fn translate_theorem_with_meta_lane(
    thm: &IsaProvenTheorem,
    closure: &Closure,
    registry: &ClassRegistry,
    method_registry: &MethodRegistry,
    instance_op_registry: &InstanceOpRegistry,
    list_fn_registry: &ListFnRegistry,
    poly_inst_registry: &PolyInstRegistry,
    membership: ClassMembership,
    method_embed: MethodEmbed,
    instance_embed: InstanceEmbed,
    root_lane: RootLane,
) -> Result<(Declaration, TranslatedMeta), TranslateError> {
    translate_theorem_with_meta_impl(
        thm,
        closure,
        registry,
        method_registry,
        instance_op_registry,
        list_fn_registry,
        poly_inst_registry,
        membership,
        method_embed,
        instance_embed,
        root_lane,
    )
}

/// The leading-binder embedding keys of a translated theorem's closed type, in
/// binder order (outermost first) — the metadata a [`ClosureEntry`] records so a
/// later fully-typed (`zproof`) `PThm` reference can specialize this theorem's
/// type directly from its explicit `tyinst`/`tminst` tables (each entry's
/// `(n, i)` key indexes a position in the matching list).
#[derive(Clone, Debug, Default)]
pub struct TranslatedMeta {
    /// Keys of the leading `∀(T:Type)` binders, in order — `ctx.type_params`'
    /// first-seen order, which the quantification loop pi-wraps outermost-first.
    pub type_param_keys: Vec<String>,
    /// Keys of the `∀(x:T)` schematic-term-variable binders that follow the type
    /// binders, in order — `ctx.term_params`' first-seen order.
    pub term_param_keys: Vec<String>,
    /// The **honest origin error** when the recorded proof failed to translate and
    /// we fell back to a *fabricated reflexivity* short-circuit (`Eq.refl` over the
    /// real `lhs = rhs` statement). The fabricated proof is kept ONLY because the
    /// kernel re-checks it: it is accepted (→ `KernelVerified`) exactly when the two
    /// sides genuinely coincide definitionally, and rejected otherwise. When it is
    /// rejected, the honest reason is *not* "the kernel refused our proof" but the
    /// underlying translate failure (commonly an unresolved dependency), so the
    /// verifier buckets the reject by THIS error rather than the fabricated-proof
    /// `kernel-reject`. `None` on every path that either translated the recorded
    /// proof or proved the statement by a structurally-valid (non-fabricated) arm.
    pub fallback_origin: Option<TranslateError>,
}

/// Like [`translate_theorem`] but also returns the leading-binder embedding keys
/// ([`TranslatedMeta`]) a caller records in a [`ClosureEntry`] so a later
/// fully-typed (`zproof`) `PThm` reference can specialize this theorem's type
/// directly from its explicit `tyinst`/`tminst` tables. The keys are exactly
/// `ctx.type_params`/`ctx.term_params`' first-seen order, which the final
/// quantification loop pi-wraps outermost-first, so the k-th key names the k-th
/// leading binder of the corresponding kind.
///
/// # Errors
/// Returns [`TranslateError`] if any node is unsupported, an axiom is unmapped,
/// or a PThm dependency is unresolved.
#[allow(clippy::too_many_arguments)]
pub fn translate_theorem_with_meta(
    thm: &IsaProvenTheorem,
    closure: &Closure,
    registry: &ClassRegistry,
    method_registry: &MethodRegistry,
    instance_op_registry: &InstanceOpRegistry,
    list_fn_registry: &ListFnRegistry,
    poly_inst_registry: &PolyInstRegistry,
    membership: ClassMembership,
    method_embed: MethodEmbed,
    instance_embed: InstanceEmbed,
) -> Result<(Declaration, TranslatedMeta), TranslateError> {
    translate_theorem_with_meta_impl(
        thm,
        closure,
        registry,
        method_registry,
        instance_op_registry,
        list_fn_registry,
        poly_inst_registry,
        membership,
        method_embed,
        instance_embed,
        RootLane::Off,
    )
}

#[allow(clippy::too_many_arguments)]
fn translate_theorem_with_meta_impl(
    thm: &IsaProvenTheorem,
    closure: &Closure,
    registry: &ClassRegistry,
    method_registry: &MethodRegistry,
    instance_op_registry: &InstanceOpRegistry,
    list_fn_registry: &ListFnRegistry,
    poly_inst_registry: &PolyInstRegistry,
    membership: ClassMembership,
    method_embed: MethodEmbed,
    instance_embed: InstanceEmbed,
    root_lane: RootLane,
) -> Result<(Declaration, TranslatedMeta), TranslateError> {
    // A `ZNop` (or Min/oracle) hole in the recorded proof forecloses proof
    // translation. By default we fast-reject here. The **reprove lane**
    // ([`crate::hol::isabelle_reprove`], env-gated `ISA_REPROVE=1`) instead lets
    // the line fall through: the recorded-proof translation then fails on the
    // hole node (`translate_proof` returns `TranslateError::Hole`), routing to
    // the statement-level proof arms below (telescoped `Eq.refl`, `propext`
    // bridges, premise-identity, …). Their fabricated proof is kernel-re-checked
    // against the embedded statement and foundational-gated by `verify_one`, so
    // this only ADDS `KernelVerified` verdicts (hole lines are 100% rejects
    // today) and can never stamp anything the kernel did not accept. Default-OFF
    // ⇒ byte-identical to HEAD.
    if thm.proof.has_hole() && !crate::hol::isabelle_reprove::reprove_enabled() {
        return Err(TranslateError::Hole("statement proof contains a hole"));
    }
    // A **bare, identity-instantiated `Thm` reference** — the whole recorded proof
    // is a single `ZConstp(ZThm dep)` whose `tyinst`/`tminst` tables map every
    // schematic variable to ITSELF (`?'a.0 ↦ ?'a.0`, `?x.0 ↦ ?x.0` / the unvarified
    // `Free x`). Isabelle emits these as *promoted duplicates / re-exports*: the
    // node's proposition IS the dependency's proposition (same statement, same
    // schematics — the identity instantiation changes nothing). The faithful
    // translation is therefore the dependency ITSELF: store the dependency's
    // already-kernel-verified closed type and prove it by the dependency constant.
    //
    // Re-embedding the consumer's (identical) statement instead — the previous
    // behaviour — REJECTED whenever the dependency's stored type was produced by a
    // faithful statement-override arm (a `…_class_def` registered class definition,
    // a `…_def` def-const reflexivity, …) or under a different escalation mode: the
    // two embeddings of the same prop then differ structurally (`Pi[3]` vs `Pi[5]`
    // telescopes), the value (the applied dependency) never matches the re-embedded
    // type, and the node — plus every downstream reference to its serial — was lost
    // (the dominant `mismatch Pi[N]->Eq got=Pi[M]->Eq @ Thm` kernel-reject cluster).
    //
    // FAITHFUL: the stored type is the dependency's kernel-verified embedding of
    // the SAME Isabelle statement (identity instantiation ⇒ the two props coincide
    // up to schematic-variable flavor), never a fabricated shape; the kernel
    // re-checks `Const(dep) : dep.ty` and the axiom closure is inherited from the
    // verified dependency, so nothing is stamped that the kernel did not accept.
    // The closure-entry binder keys are copied from the dependency so later
    // fully-typed references specialize this node exactly as they would the dep.
    // A NON-identity instantiation (a genuine specialization) or an unresolved
    // dependency falls through to the ordinary translation path unchanged.
    if let IsaProof::Thm {
        id, tyinst, tminst, ..
    } = &thm.proof
    {
        if insts_all_identity(tyinst, tminst) {
            if let Some(entry) = closure.get(id) {
                let meta = TranslatedMeta {
                    type_param_keys: entry.type_param_keys.clone(),
                    term_param_keys: entry.term_param_keys.clone(),
                    fallback_origin: None,
                };
                return Ok((
                    Declaration::Theorem {
                        name: Name::from_string(&thm.name),
                        level_params: Vec::new(),
                        type_: entry.ty.clone(),
                        value: Expr::const_str(entry.name.as_str()),
                    },
                    meta,
                ));
            }
        }
    }
    // Recover the statement's leading binders (outermost-first) so a raw-proof
    // body `AbsP { h: None }` / `Abst { ty: None }` can take its discharged
    // hypothesis / bound-variable type from the matching leading `Pure.imp` /
    // `Pure.all` binder (the raw form omits both). The leading spine is active
    // from the proof root.
    let premise_queue = leading_premises(&thm.prop);
    let stmt_premises: Vec<_> = premise_queue
        .iter()
        .filter_map(|b| match b {
            LeadingBinder::Hyp(t) => Some(t.clone()),
            LeadingBinder::AllTy(_) => None,
        })
        .collect();
    let mut ctx = Ctx {
        premise_queue,
        stmt_premises,
        leading_active: true,
        class_registry: registry.clone(),
        class_membership: membership == ClassMembership::Real,
        nonempty_erase: membership == ClassMembership::NonemptyErase,
        method_registry: method_registry.clone(),
        method_unfold: method_embed == MethodEmbed::DictUnfold,
        instance_op_registry: instance_op_registry.clone(),
        instance_unfold: instance_embed == InstanceEmbed::Unfold,
        list_fn_registry: list_fn_registry.clone(),
        poly_inst_registry: poly_inst_registry.clone(),
        zproof_mode: proof_has_inst_tables(&thm.proof),
        root_lane: root_lane == RootLane::On,
        stmt_fallback: root_lane == RootLane::StmtFallback,
        bidir_tower: root_lane == RootLane::BidirEqTower,
        ..Default::default()
    };
    // Embed statement first so term/type params are discovered, then the proof.
    let mut binders: Vec<Binder> = Vec::new();
    let prop = ctx.embed_term(&thm.prop, &mut binders)?;
    // A statement-level arm may replace the stored theorem type with a faithful
    // reflexive form (e.g. a `…_def` definitional axiom, whose LHS constant
    // denotes its body by definition — see [`def_axiom_body`]). The kernel
    // re-checks the proof against this type, so the override is sound.
    let mut ty_override: Option<Expr> = None;
    // Set when the recorded proof failed to translate and we fall back to a
    // FABRICATED reflexivity short-circuit (`Eq.refl` over the real `lhs = rhs`).
    // The fabricated proof is kernel-re-checked, so it is accepted only when the
    // equation is genuinely reflexive; when it is rejected the honest reason is the
    // recorded-proof failure recorded here — see [`TranslatedMeta::fallback_origin`].
    let mut fallback_origin: Option<TranslateError> = None;
    let mut proof = if let Some((pf_ty, pf_proof)) =
        ctx.prove_pointfree_def_raw(thm, &mut binders)?
    {
        // A **point-free** HOL logical definitional axiom `Pure.eq C (λargs. body)`
        // whose LHS is the BARE constant `C` (`HOL.All`/`HOL.Ex`/`HOL.Uniq`/
        // `HOL.Ex1`/`HOL.Let`/`HOL.induct_forall`/`HOL.induct_equal`/`HOL.NO_MATCH`).
        // These `…_def_raw` equations re-state each definition point-free inside an
        // unnamed consumer whose recorded proof bottoms out at the un-mappable
        // `…_def_raw` PAxm leaf. [`Ctx::prove_pointfree_def_raw`] proves the whole
        // embedded equation directly: `lhs_sem` is the embedded η-expansion
        // `λargs. C args` (`C`'s faithful semantic meaning, via the existing applied
        // arms) and `rhs` is the embedded body — DISTINCT source terms (never a
        // `B = B` tautology). Reflexive for every case except `HOL.All`, where the
        // semantic `λP. ∀x. P x` is only propositionally equal to `λP. P = (λx.True)`
        // and the proof lifts the pointwise `all_def_bridge_proof` across `funext`.
        // The kernel re-checks the proof against `pf_ty`, so a mis-embedding is
        // rejected — never miscounted. `HOL.All`/`HOL.Ex` also unblock their many
        // foundational dependents (the `∀`/`∃`-quantifier cascade).
        ty_override = Some(pf_ty);
        pf_proof
    } else if let Some(p_tm) = all_def_predicate(&thm.prop) {
        // HOL's `All_def` (`(∀x. P x) ≡ (P = (λx. True))`). The recorded proof
        // bottoms out at the `All_def_raw` PAxm leaf (un-mappable standalone), so
        // we prove the embedded statement directly with the BRIDGE
        // [`all_def_bridge_proof`] (propext/funext/congrFun/Eq.{refl,mpr}), then
        // discharge each leading `type_class` sort constraint (embedded as a
        // `True` premise) with an enclosing `fun (_:True) => …`. The kernel
        // re-checks the result against the embedded statement type `prop`, so a
        // wrong bridge is rejected — never miscounted.
        let p_e = ctx.embed_term(p_tm, &mut binders)?;
        // P's domain α: from its type `α ⇒ bool` (the predicate type).
        let p_ty = ctx.infer_type(p_tm, &binders)?;
        let (alpha, _) = split_arrow(&p_ty).ok_or(TranslateError::Unsupported(
            "All_def predicate not a function",
        ))?;
        let bridge = all_def_bridge_proof(&alpha, &p_e);
        // Wrap one `fun (_:True) =>` per leading sort-constraint premise.
        let n_premises = leading_premises(&thm.prop).len();
        let mut e = bridge;
        for _ in 0..n_premises {
            e = Expr::lam(BinderInfo::Default, Expr::const_str("True"), e);
        }
        e
    } else if let Some(p_tm) = ex_def_predicate(&thm.prop) {
        // HOL's `Ex_def` (`(∃x. P x) ≡ (∀Q. (∀x. P x ⟶ Q) ⟶ Q)`). Under the
        // semantic embedding the RHS *is* the encoding of `HOL.Ex P`, and the
        // η-expanded `HOL.Ex P` LHS embeds to the same `∀Q.…` form, so the
        // equation is reflexive: `@Eq.refl Prop (rhs)`. The kernel re-checks that
        // both sides are definitionally equal (rejecting otherwise), then we
        // discharge the leading sort-constraint premise(s). `p_tm` is embedded so
        // its parameter is discovered for quantification.
        let _ = ctx.embed_term(p_tm, &mut binders)?;
        // The conclusion's embedded form is `@Eq Prop lhs rhs`; prove by Eq.refl
        // when lhs/rhs coincide definitionally. Recover lhs from the embedded
        // statement conclusion.
        let concl = strip_leading_imps(&thm.prop);
        let (lhs_tm, _) = pure_eq_parts(concl).ok_or(TranslateError::Unsupported(
            "Ex_def conclusion not an equation",
        ))?;
        let lhs_e = ctx.embed_term(lhs_tm, &mut binders)?;
        let refl = Expr::apps(
            Expr::const_str_levels("Eq.refl", vec![obj_level()]),
            [Expr::prop(), lhs_e],
        );
        let n_premises = leading_premises(&thm.prop).len();
        let mut e = refl;
        for _ in 0..n_premises {
            e = Expr::lam(BinderInfo::Default, Expr::const_str("True"), e);
        }
        e
    } else if is_true_def_const(&prop) {
        // `HOL.TrueI` (`Trueprop True`): the statement embeds to the `True`
        // definition const `isabelle.def.HOL.True`, which unfolds (via defeq) to
        // the encoding `((λx:Prop.x) = (λx:Prop.x))`. Its inhabitant is the
        // reflexivity proof `Eq.refl.{1} (Prop→Prop) (λx.x)`; the kernel re-checks
        // it against the `True` def-const through definitional unfolding, so a
        // wrong term is rejected. (Pre-def-const, `True` embedded *inline* to a
        // syntactic `Eq`, so the reflexive short-circuit below caught this — the
        // def-const form needs this explicit arm.)
        true_enc_and_proof().1
    } else if is_pure_term_app(&prop) {
        // A bare Pure judgement `Pure.term x` (the meta-logic "`x` is a well-formed
        // term" marker). It embeds to `@isabelle.def.Pure.term α x`, which δβ-unfolds
        // to the trivially-inhabited meta-truth `∀A. A → A`, so its canonical
        // inhabitant is the polymorphic identity `λ(A:Prop)(h:A). h`
        // ([`pure_term_proof`]). We prove it DIRECTLY here instead of translating the
        // recorded `equal_elim (symmetric term_def) …` proof, whose spine references a
        // long `Pure.termI`/`sort_constraintI` closure chain that is frequently
        // unresolved (or reconstructs the wrong bound-variable identity). This node is
        // the *root* of the `Pure.term`/`sort_constraint` cascade — verifying it
        // unblocks `Pure.termI`, `sort_constraintI`, `sort_constraint_eq`, and their
        // many downstream consumers. The kernel re-checks the identity against the
        // stored `Pure.term x` type by def-unfolding, so a mis-detection is rejected —
        // never miscounted.
        pure_term_proof()
    } else if is_true_const(&prop) {
        // A bare sort-constraint judgement `Pure.sort_constraint TYPE('a)`, which
        // `embed_class_membership` erases to the vacuous `True`. Its recorded proof is
        // an `equal_elim (symmetric sort_constraint_def) …` spine (a long
        // `sort_constraintI`/`termI` closure chain, often unresolved), but the erased
        // statement IS just `True`, proved directly by `True.intro`. This clears the
        // standalone `sort_constraint TYPE` nodes that seed the sort-constraint
        // cascade. Kernel-re-checked (`True.intro : True`), so soundness-neutral.
        Expr::const_str("True.intro")
    } else if let (InstanceEmbed::Unfold, Some((_method_name, eq_ty, rhs_tm))) =
        (instance_embed, instance_op_def_axiom(thm))
    {
        // A **monomorphic ground-type instance-operation definition**
        // (`Nat.plus_nat_def`, `Nat.times_nat_def`, `Nat.One_nat_def`, …): a
        // `Pure.eq (c@ground) B` whose LHS is an overloaded class operation at a
        // closed ground type and whose recorded proof is an intricate
        // `Pure.transitive` unfolding chain (so neither `def_axiom_body`'s
        // proof-head test nor the set arm fires — detection is by statement shape;
        // see [`instance_op_def_axiom`]). When the operation is registered as an
        // instance def-const, `embed_term` emits the LHS `c@ground` as that
        // def-const, which δ-unfolds to `embed B`, so the equation is GENUINELY
        // reflexive. We store the REAL statement `@Eq α (embed lhs) (embed rhs)` and
        // prove it by `Eq.refl α (embed lhs)`, which the kernel accepts ONLY when
        // `embed lhs` δ-reduces to `embed rhs` (FAITHFUL — not a `B=B` tautology:
        // the stored proposition keeps the real `c@ground = B` shape, and the proof
        // is sound exactly because the def-const unfolds to the body). If the
        // operation is NOT registered (its body did not close), `embed lhs` is the
        // opaque `const:` param and the `Eq.refl` kernel-rejects (`TypeMismatch`) —
        // so this never miscounts. Leading sort premises discharged as vacuous
        // `True →` in lockstep on type and proof.
        let body = ctx.embed_term(rhs_tm, &mut binders)?;
        let concl = strip_leading_imps(&thm.prop);
        let (lhs_tm, _) = pure_eq_parts(concl).ok_or(TranslateError::Unsupported(
            "instance_op_def: statement not a Pure.eq",
        ))?;
        let lhs = ctx.embed_term(lhs_tm, &mut binders)?;
        let alpha = ctx.embed_type(eq_ty)?;
        let mut over = Expr::apps(
            Expr::const_str_levels("Eq", vec![obj_level()]),
            [alpha.clone(), lhs.clone(), body],
        );
        let mut e = Expr::apps(
            Expr::const_str_levels("Eq.refl", vec![obj_level()]),
            [alpha, lhs],
        );
        let n_premises = leading_premises(&thm.prop).len();
        for _ in 0..n_premises {
            e = Expr::lam(BinderInfo::Default, Expr::const_str("True"), e);
            over = Expr::arrow(Expr::const_str("True"), over);
        }
        ty_override = Some(over);
        e
    } else if let (InstanceEmbed::Unfold, Some((fn_name, eq_ty, _tv, rhs_tm))) = (
        instance_embed,
        list_fn_def_axiom(thm).filter(|(n, ..)| ctx.list_fn_registry.contains_key(*n)),
    ) {
        // A **plain polymorphic list-function definition** (`List.append_def`,
        // `List.rev_def`, `List.list.map_def`, …): a `Pure.eq c B` whose LHS is a
        // single-`'a` list function and whose recorded proof is an intricate
        // `Pure.transitive` unfolding chain (so neither `def_axiom_body`'s
        // proof-head test nor the set arm fires — detection is by statement shape;
        // see [`list_fn_def_axiom`]). When the function is registered as a list-fn
        // def-const, `embed_term` emits the LHS `c` as `@isabelle.listfn.<c> α`,
        // which δ-unfolds to `embed B`, so the equation is GENUINELY reflexive. We
        // store the REAL statement `@Eq α (embed lhs) (embed rhs)` and prove it by
        // `Eq.refl α (embed lhs)`, which the kernel accepts ONLY when `embed lhs`
        // δ-reduces to `embed rhs` (FAITHFUL — not a `B=B` tautology: the stored
        // proposition keeps the real `c = B` shape, sound exactly because the
        // def-const unfolds to the body). If the function is NOT registered (its
        // body did not close), this arm is not taken (the guard requires the
        // registry to contain it). Leading sort premises discharged as vacuous
        // `True →` in lockstep on type and proof.
        let _ = fn_name;
        let body = ctx.embed_term(rhs_tm, &mut binders)?;
        let concl = strip_leading_imps(&thm.prop);
        let (lhs_tm, _) = pure_eq_parts(concl).ok_or(TranslateError::Unsupported(
            "list_fn_def: statement not a Pure.eq",
        ))?;
        let lhs = ctx.embed_term(lhs_tm, &mut binders)?;
        let alpha = ctx.embed_type(eq_ty)?;
        let mut over = Expr::apps(
            Expr::const_str_levels("Eq", vec![obj_level()]),
            [alpha.clone(), lhs.clone(), body],
        );
        let mut e = Expr::apps(
            Expr::const_str_levels("Eq.refl", vec![obj_level()]),
            [alpha, lhs],
        );
        let n_premises = leading_premises(&thm.prop).len();
        for _ in 0..n_premises {
            e = Expr::lam(BinderInfo::Default, Expr::const_str("True"), e);
            over = Expr::arrow(Expr::const_str("True"), over);
        }
        ty_override = Some(over);
        e
    } else if let (InstanceEmbed::Unfold, Some((fn_name, _, _, _, rhs_tm))) = (
        instance_embed,
        poly_inst_def_axiom(thm).filter(|(n, ..)| ctx.poly_inst_registry.contains_key(*n)),
    ) {
        // A **polymorphic instance-operation definition** (`Int.power_int_def`, …): a
        // `Pure.eq (c ?args) B` whose LHS is a bare polymorphic constant applied to
        // schematic argument variables and whose body uses overloaded class operations
        // over `'a` (so neither the ground `instance_op` nor the plain `list_fn` arm
        // fires — see [`poly_inst_def_axiom`]). When `c` is registered as a poly-inst
        // def-const, `embed_term` emits the LHS `c ?args` as
        // `(isabelle.polyinst.<c> α op₁ … opₘ) (embed ?args)`, which δ/β-unfolds to
        // `embed B`, so the equation is GENUINELY reflexive. We store the REAL
        // statement `@Eq α (embed lhs) (embed rhs)` and prove it by
        // `Eq.refl α (embed lhs)`, which the kernel accepts ONLY when `embed lhs`
        // δ-reduces to `embed rhs` (FAITHFUL — not a `B=B` tautology: the stored
        // proposition keeps the real `c ?args = B` shape, sound exactly because the
        // def-const unfolds to the body). The Eq operand type is the constant's RESULT
        // type (`'a` for `power_int ?x ?n : 'a`). Leading `OFCLASS ⟹` sort premises
        // discharged as vacuous `True →` in lockstep on type and proof.
        let _ = fn_name;
        let body = ctx.embed_term(rhs_tm, &mut binders)?;
        let concl = strip_leading_imps(&thm.prop);
        let (lhs_tm, _) = pure_eq_parts(concl).ok_or(TranslateError::Unsupported(
            "poly_inst_def: statement not a Pure.eq",
        ))?;
        let eq_ty = pure_eq_operand_ty(concl).ok_or(TranslateError::Unsupported(
            "poly_inst_def: missing Pure.eq operand type",
        ))?;
        let lhs = ctx.embed_term(lhs_tm, &mut binders)?;
        let alpha = ctx.embed_type(eq_ty)?;
        let mut over = Expr::apps(
            Expr::const_str_levels("Eq", vec![obj_level()]),
            [alpha.clone(), lhs.clone(), body],
        );
        let mut e = Expr::apps(
            Expr::const_str_levels("Eq.refl", vec![obj_level()]),
            [alpha, lhs],
        );
        let n_premises = leading_premises(&thm.prop).len();
        for _ in 0..n_premises {
            e = Expr::lam(BinderInfo::Default, Expr::const_str("True"), e);
            over = Expr::arrow(Expr::const_str("True"), over);
        }
        ty_override = Some(over);
        e
    } else if let (InstanceEmbed::Unfold, Some((_method, _mt, _tvs, _avs, rhs_tm))) = (
        instance_embed,
        method_inst_def_axiom(thm).filter(|(m, t, ..)| {
            ctx.poly_inst_registry
                .contains_key(&method_inst_registry_key(m, &isa_shape_key(t)))
        }),
    ) {
        // A **method-at-constructor instance definition** (`Enum.enum_fun_def`,
        // `Filter.le_filter_def`, `Product_Type.equal_prod_def`, …): a
        // `Pure.eq`/`HOL.eq` whose LHS is an overloaded `_class.` method applied
        // to schematic args at a NON-ground constructor-instance type — the G4
        // third registration shape ([`method_inst_def_axiom`]), REGISTERED under
        // the composite `(method, shape)` key ([`register_method_inst_def`]).
        // The recorded proof is an `AbsP(OFCLASS…)`-guarded reference to the
        // anonymous premise-spelling bridge, whose stored membership-mode flavor
        // rarely matches the consumer's pass (the same mode-seam wall the
        // dict-impl round measured) — but the STATEMENT is definitional: with
        // the registration in place, `embed_term` emits the LHS
        // `method @ instance-type args` as the `isabelle.instk.<m>@<shape>`
        // def-const applied to the solved instantiation tvars and the
        // re-embedded class operations, which δβ-unfolds to `embed B` — every
        // operation supplied through the SAME full `Const` dispatch the RHS's
        // own occurrences take in this pass, so the two sides coincide
        // definitionally. We store the REAL statement `@Eq α (embed lhs)
        // (embed rhs)` (two DISTINCT operands — faithful, never a `B=B`
        // tautology) and prove it by `Eq.refl α (embed lhs)`, which the kernel
        // accepts ONLY when the unfold genuinely reaches the RHS (a flavor gap
        // rejects — never miscounted). Mirrors the poly-inst arm above exactly;
        // gated on `InstanceEmbed::Unfold` (final escalating passes → strictly
        // additive) + the registry filter (an unregistered instance keeps its
        // recorded-proof path unchanged). Leading sort premises discharged as
        // vacuous `True →` in lockstep on type and proof.
        let body = ctx.embed_term(rhs_tm, &mut binders)?;
        let concl = strip_leading_imps(&thm.prop);
        let (lhs_tm, _) = pure_eq_parts(concl).ok_or(TranslateError::Unsupported(
            "method_inst_def: statement not a Pure.eq",
        ))?;
        let eq_ty = pure_eq_operand_ty(concl).ok_or(TranslateError::Unsupported(
            "method_inst_def: missing Pure.eq operand type",
        ))?;
        let lhs = ctx.embed_term(lhs_tm, &mut binders)?;
        let alpha = ctx.embed_type(eq_ty)?;
        let mut over = Expr::apps(
            Expr::const_str_levels("Eq", vec![obj_level()]),
            [alpha.clone(), lhs.clone(), body],
        );
        let mut e = Expr::apps(
            Expr::const_str_levels("Eq.refl", vec![obj_level()]),
            [alpha, lhs],
        );
        let n_premises = leading_premises(&thm.prop).len();
        for _ in 0..n_premises {
            e = Expr::lam(BinderInfo::Default, Expr::const_str("True"), e);
            over = Expr::arrow(Expr::const_str("True"), over);
        }
        ty_override = Some(over);
        e
    } else if let Some(p) = prove_pure_conjunction_def(&thm.name, &prop) {
        // Pure's meta-conjunction **definition** axiom `Pure.conjunction_def`
        // (`A &&& B ≡ ⋀C. (A⟹B⟹C)⟹C`). Under the embedding `Pure.conjunction → And`
        // the statement is `@Eq Prop (And A B) E`, `E` the impredicative encoding
        // `∀C.(A→B→C)→C`. `And` is the inductive conjunction, NOT definitionally
        // equal to `E`, so `def_axiom_body`'s reflexive `Eq.refl (And A B)` would
        // kernel-reject — this arm is placed BEFORE it and proves the genuine
        // equality via `propext` of the constructive `And ↔ E` isomorphism
        // (`And.{intro,left,right}` + `propext`, all foundational). The `propext`
        // operands are read from the SAME embedded `prop` that becomes the stored
        // type, so the proof's inferred type is bit-identical and FAITHFUL (the real
        // `And A B = E`, never a `B=B` tautology). The kernel re-checks it against
        // the embedded statement, so a mis-shape is rejected — never miscounted.
        // `Pure.conjunction` is the conjunction in EVERY structured type-class
        // `…c_class_def` body, so landing this def unblocks its many dependents.
        p
    } else if let Some(p) = prove_atomize_conj(&prop) {
        // HOL's `atomize_conj` (`(A &&& B) ≡ Trueprop (A ∧ B)`) and its anonymous
        // derivation-box twins: the meta↔object conjunction bridge every
        // locale-predicate projection (`class.order → class.preorder`, …) routes
        // through, whose recorded proof bottoms out in an unmappable box chain.
        // SHAPE-gated (`@Eq Prop (And A B) (conj_def A B)` — never a tautology)
        // and proved by `propext` of the constructive isomorphism, exactly like
        // `Pure.conjunction_def` above. Kernel-re-checked against the embedded
        // statement. See [`prove_atomize_conj`].
        p
    } else if let Some((value, ty)) = ctx.prove_locale_projection(thm)? {
        // A **locale-predicate projection** node
        // (`type_class α ⟹ class.C args ⟹ class.subpredᵢ subargs`): under
        // `InstanceEmbed::Unfold` the hypothesis `class.C args` embeds to its
        // `isabelle.polyinst.<c>` def-const, which δ-unfolds to the conjunction
        // of superclass locale predicates whose i-th conjunct is the conclusion.
        // We discharge it DEFINITIONALLY by the impredicative `conj_def`
        // projection (descend the right spine, select the matched conjunct)
        // rather than reconstructing the recorded `atomize_conj`+`Pure.combination`
        // congruence chain (which the deeper 3-way+ nestings — `semiring`,
        // `comm_ring`, the Rings/Fields families — do not reconstruct). The stored
        // type is the REAL projection statement (distinct hypothesis/conclusion,
        // never a tautology) and the kernel re-checks `value : type` δβ-reducing
        // the def-const, so a wrong extraction is rejected — never miscounted.
        // Gated on `instance_unfold` inside the method → strictly additive. See
        // [`Ctx::prove_locale_projection`].
        ty_override = Some(ty);
        value
    } else if let Some((value, ty)) = ctx.prove_locale_construction(thm)? {
        // The **dual** of the projection: a locale-predicate CONSTRUCTION node
        // (`type_class α ⟹ axiom₀ ⟹ … ⟹ axiomₙ ⟹ class.C_axioms args`, the
        // `class.C_axioms.intro` bundling a class's own assumptions into its
        // axioms predicate). Under `InstanceEmbed::Unfold` the conclusion embeds
        // to the `isabelle.polyinst.<c>` def-const, δ-unfolding to the
        // right-nested `conj_def` of the axiom premises; the proof is the
        // impredicative conjunction INTRO built from the premise hypotheses. The
        // stored type is the REAL construction statement (distinct axiom
        // premises / class-predicate conclusion, never a tautology); the kernel
        // re-checks `value : type` δβ-reducing the def-const, so a mismatch is
        // rejected — never miscounted. Gated on `instance_unfold` → strictly
        // additive. See [`Ctx::prove_locale_construction`].
        ty_override = Some(ty);
        value
    } else if let Some((value, ty)) = ctx.prove_locale_to_locale(thm)? {
        // A **locale-to-locale** projection node
        // (`type_class α ⟹ class.C args ⟹ pred_D dargs`) whose conclusion is a
        // registered locale predicate `pred_D` (a weaker structure predicate —
        // `Orderings.preordering`, `Groups.semigroup` — derived from the stronger
        // class hypothesis) whose EVERY conjunct is projectable from a
        // locale-predicate premise. Unlike `prove_locale_projection` (conclusion =
        // a SINGLE conjunct of the premise), the whole conclusion predicate is
        // REASSEMBLED: each of `pred_D`'s δ-unfolded conjuncts is extracted from the
        // premise `class.C` by the impredicative `conj_def` projection, then the
        // conjuncts are recombined by the `conj_def` INTRO — whose type δ= the
        // conclusion def-const `polyinst.pred_D dargs`. Its recorded proof bottoms
        // in the `atomize_conj`/`Pure.combination` congruence tower
        // (`expected=isabelle.def.HOL.Not got=FVar` / `expected=Eq got=Eq`), so
        // keying on the statement shape sidesteps it. The stored type is the REAL
        // projection statement (distinct `class.C` premise / `pred_D` conclusion,
        // never a tautology) and the kernel re-checks `value : type` δβ-reducing
        // every def-const, so a wrong assembly is rejected — never miscounted.
        // Gated on `instance_unfold` → strictly additive (placed AFTER
        // `prove_locale_projection`/`prove_locale_construction`, so it fires only on
        // the whole-predicate reassembly they decline). See
        // [`Ctx::prove_locale_to_locale`].
        ty_override = Some(ty);
        value
    } else if let Some(p) = prove_sort_constraint_def(&thm.name, &prop) {
        // Pure's sort-constraint **definition** axiom `Pure.sort_constraint_def`
        // (`sort_constraint TYPE('a) ≡ term TYPE('a)`). The LHS is a sort constraint
        // erased to `True`; the RHS `Pure.term TYPE('a)` embeds (via the `Pure.term`
        // def-const) to a term δβ-equal to `∀A. A → A`. `True` is NOT defeq to that,
        // so `def_axiom_body`'s reflexive `Eq.refl` would kernel-reject — this arm is
        // placed BEFORE it and proves the genuine `True = R` equality via `propext`
        // of the trivial `True ↔ R` isomorphism (both inhabited; foundational
        // `propext` + `True.intro`). The `propext` operands are read from the SAME
        // embedded `prop` that becomes the stored type, so the proof's inferred type
        // is bit-identical and FAITHFUL (the real `sort_constraint = term`, never a
        // `B=B` tautology). Kernel-re-checked — a mis-shape is rejected.
        p
    } else if let Some((eq_ty, lhs_tm, rhs_tm)) = set_instance_def_body(thm) {
        // A **set-instance definitional axiom** (`bot_set_def`, `inf_set_def`,
        // `less_eq_set_def`, `Inf_set_def`, …) — see [`set_instance_def_body`].
        // Under the `'a set = 'a → Prop` model the LHS `op_set` and the RHS
        // `Collect(op_fun …)` embed to definitionally-equal clean terms (the set
        // and function instances unify; `Collect`/`member` are identity /
        // application), so the equation is reflexive. We store the REAL statement
        // `@Eq α (embed lhs) (embed rhs)` and prove it by `Eq.refl α (embed lhs)`,
        // which the kernel accepts ONLY when `embed lhs` is definitionally equal to
        // `embed rhs`. This is FAITHFUL (not a `B=B` tautology): the stored
        // proposition keeps the real `op_set = RHS` shape, and the proof is sound
        // exactly because the type-copy model makes the two genuinely equal. A
        // non-reflexive case kernel-rejects (`TypeMismatch`), so it cannot
        // miscount. Leading `OFCLASS ⟹` sort premises are discharged as vacuous
        // `True →` in lockstep on the type and proof.
        let body = ctx.embed_term(rhs_tm, &mut binders)?;
        let lhs = ctx.embed_term(lhs_tm, &mut binders)?;
        let alpha = ctx.embed_type(eq_ty)?;
        let mut over = Expr::apps(
            Expr::const_str_levels("Eq", vec![obj_level()]),
            [alpha.clone(), lhs.clone(), body],
        );
        let mut e = Expr::apps(
            Expr::const_str_levels("Eq.refl", vec![obj_level()]),
            [alpha, lhs],
        );
        let n_premises = leading_premises(&thm.prop).len();
        for _ in 0..n_premises {
            e = Expr::lam(BinderInfo::Default, Expr::const_str("True"), e);
            over = Expr::arrow(Expr::const_str("True"), over);
        }
        ty_override = Some(over);
        e
    } else if let (MethodEmbed::DictUnfold, Some((eq_ty, rhs_tm))) =
        (method_embed, dict_axiom_body(thm))
    {
        // A **method dictionary axiom** `…_dict : c_class.method ≡ c.method ops`
        // (see [`dict_axiom_body`]) — the overloaded class method equated with
        // its dictionary form. Some methods (`Orderings.ord_class.max`/`min`/
        // `Least`) export this as a standalone named theorem whose recorded proof
        // is the bare unmapped `…_dict` `PAxm`; the method is registered from this
        // same statement ([`register_method_defs`] via `dict_equation_from_prop`).
        // With `MethodEmbed::DictUnfold` active, the LHS `c_class.method` embeds to
        // its dictionary def-const `isabelle.method.<c> α impl ops`, which
        // δ-unfolds to exactly the RHS `c.method ops` embedding, so the equation
        // is GENUINELY reflexive (LHS δ-reduces to RHS). We store the REAL
        // statement `@Eq α (embed lhs) (embed rhs)` — two structurally DISTINCT
        // operands (faithful, not a `B=B` tautology: the LHS is a def-const
        // application, the RHS the direct dictionary form) — and prove it by
        // `Eq.refl α (embed lhs)`, which the kernel accepts ONLY when `embed lhs`
        // δ-reduces to `embed rhs` (i.e. the method genuinely registered). Gated on
        // `MethodEmbed::DictUnfold` (the escalating pass that unfolds registered
        // methods) so it is strictly additive: an earlier opaque pass leaves the
        // method opaque and this arm does not fire. The impl/ops on BOTH sides embed
        // opaquely under `InstanceEmbed::Opaque` (this pass), so `Least`'s
        // `HOL.The`-bodied `ord.Least` never needs unfolding — the two sides
        // coincide as opaque `const:` applications. Leading `OFCLASS ⟹` sort
        // premises discharged as vacuous `True →` in lockstep on type and proof.
        let body = ctx.embed_term(rhs_tm, &mut binders)?;
        let (lhs_tm, _) = pure_eq_parts(strip_leading_imps(&thm.prop)).ok_or(
            TranslateError::Unsupported("dict_axiom: statement not a Pure.eq"),
        )?;
        let lhs = ctx.embed_term(lhs_tm, &mut binders)?;
        let alpha = ctx.embed_type(eq_ty)?;
        let mut over = Expr::apps(
            Expr::const_str_levels("Eq", vec![obj_level()]),
            [alpha.clone(), lhs.clone(), body],
        );
        let mut e = Expr::apps(
            Expr::const_str_levels("Eq.refl", vec![obj_level()]),
            [alpha, lhs],
        );
        let n_premises = leading_premises(&thm.prop).len();
        for _ in 0..n_premises {
            e = Expr::lam(BinderInfo::Default, Expr::const_str("True"), e);
            over = Expr::arrow(Expr::const_str("True"), over);
        }
        ty_override = Some(over);
        e
    } else if let Some((eq_ty, rhs)) = def_axiom_body(thm) {
        // A **definitional axiom** `…c_def : c args ≡ B` (see [`def_axiom_body`]),
        // possibly under leading `OFCLASS ⟹ …` sort-constraint premises. The
        // defined constant `c args` denotes its body `B` by definition, so the
        // faithful embedded statement (after discharging the vacuous sort
        // premises) is the reflexive equation `@Eq α (embed B) (embed B)`. We
        // prove it directly by `Eq.refl` over the embedded body, replacing the
        // stored type with this reflexive form (the LHS's faithful meaning IS
        // `B`). This discharges the otherwise-unmapped `…_def` axiom leaf; the
        // kernel re-checks `Eq.refl α B : @Eq α B B`, so a wrong embedding is
        // rejected — never miscounted. Free types/operations in `B` are
        // discovered as the usual quantified parameters during embedding.
        // FAITHFULNESS EXPERIMENT: store the REAL statement `@Eq α (embed lhs)
        // (embed rhs)` and prove it by `Eq.refl α (embed lhs)`. The kernel accepts
        // this ONLY when `c args` genuinely δ-reduces to `B` (i.e. `c` is a
        // registered definition); otherwise it `TypeMismatch`-rejects. The count
        // delta vs the old `B = B` override measures how many entries were
        // tautologies (`∀c. B = B`) rather than faithful `c args = B`.
        let body = ctx.embed_term(rhs, &mut binders)?;
        let (lhs_tm, _) = pure_eq_parts(strip_leading_imps(&thm.prop)).ok_or(
            TranslateError::Unsupported("def_axiom: statement not a Pure.eq"),
        )?;
        let lhs = ctx.embed_term(lhs_tm, &mut binders)?;
        let alpha = ctx.embed_type(eq_ty)?;
        let mut over = Expr::apps(
            Expr::const_str_levels("Eq", vec![obj_level()]),
            [alpha.clone(), lhs.clone(), body],
        );
        let mut e = Expr::apps(
            Expr::const_str_levels("Eq.refl", vec![obj_level()]),
            [alpha, lhs],
        );
        // Discharge each leading sort-constraint premise (`OFCLASS`, embedded as a
        // vacuous `True`) with an enclosing `fun (_:True) =>` on the proof and a
        // matching `True →` arrow on the stored type, keeping them in lockstep.
        let n_premises = leading_premises(&thm.prop).len();
        for _ in 0..n_premises {
            e = Expr::lam(BinderInfo::Default, Expr::const_str("True"), e);
            over = Expr::arrow(Expr::const_str("True"), over);
        }
        ty_override = Some(over);
        e
    } else if let Some((alpha, a)) = reflexive_eq_parts(&prop) {
        // The embedded statement is *syntactically* `@Eq α a a` (a reflexive
        // equation). In this embedding that arises both for genuine `a = a`
        // theorems and for HOL constants that unfold to one (e.g. `True` is
        // `(λx.x) = (λx.x)`). Such a theorem IS reflexivity in clean's model, so
        // `@Eq.refl α a` proves it regardless of how Isabelle recorded the proof
        // (which may reference export-absent nodes). Sound: the kernel re-checks
        // `@Eq.refl α a : @Eq α a a` against this exact statement.
        Expr::apps(
            Expr::const_str_levels("Eq.refl", vec![obj_level()]),
            [alpha, a],
        )
    } else if let Some(p) = (ctx.instance_unfold && is_pointwise_instance_def(thm))
        .then(|| prove_scoped_telescoped_eq_refl(&prop))
        .flatten()
    {
        // A **pointwise / type-constructor instance-operation definition** under
        // leading sort premises — a `…_fun_inst.…_fun_def` lattice/order instance
        // def (`(f ⊓ g) = λx. f x ⊓ g x`, `⊥ = λx. ⊥`, `(f ≤ g) = ∀x. f x ≤ g x`,
        // …), `equal_itself_def` (`equal x y = (x = y)`), or `ord.max`/`min`
        // (`max le a b = if le a b then b else a`). Its LHS class op / function now
        // embeds to the faithful pointwise / equality / if-lambda
        // ([`pointwise_fun_instance_op`]) whose element operation is the SAME
        // abstract head the RHS uses, so the embedded statement
        // `Π(_:True/⋀…). @Eq α lhs rhs` has `lhs` β/δ-reducing to `rhs`. We prove
        // the whole telescoped equation directly by `λ…. Eq.refl α lhs`, gated on
        // both `instance_unfold` (final escalating pass → strictly additive) and
        // the [`is_pointwise_instance_def`] statement-shape recognizer (so ONLY
        // these instance defs take this arm — never an unrelated `_def` equation,
        // keeping the shared closure undisturbed). Attempted BEFORE the recorded
        // proof (whose `…_fun_inst.…_def` / `…_def_raw` PAxm leaf is unmapped, so
        // it never translates and would otherwise short-circuit through a
        // kernel-rejected reflexivity). The kernel re-checks
        // `Eq.refl α lhs : @Eq α lhs rhs`, accepting **iff** the two sides genuinely
        // coincide definitionally — faithful (never a `B=B` tautology), never
        // miscounted.
        p
    } else if let Some(p) = (ctx.instance_unfold && is_bnf_def(thm))
        .then(|| prove_scoped_telescoped_eq_refl(&prop))
        .flatten()
    {
        // A **BNF combinator definitional axiom** — `convol_def`/`rel_fun_def`/
        // `rel_set_def`/`eq_onp_def`/`vimage2p_def`/`Grp_def`/`Gr_def`/
        // `csquare_def`/`id_bnf_def` (and their `…_def_raw` point-free companions),
        // whose recorded proof bottoms out in the un-mappable `…_def_raw` PAxm leaf.
        // The LHS constant now embeds to its registered def-const
        // ([`Ctx::embed_bnf_combinator`]), which δβ-reduces to exactly the embedded
        // RHS body (the `∀`/`Ball`/`Bex`/`∃`/`∧`/`@Eq`/`Prod.mk` encoding), so the
        // embedded statement `Π(_:…). @Eq α lhs rhs` is reflexive. We prove it
        // directly by `λ…. Eq.refl α lhs`, gated on both `instance_unfold` (final
        // escalating pass → strictly additive) and the [`is_bnf_def`] statement-shape
        // recognizer (so ONLY these BNF defs take this arm). Attempted BEFORE the
        // recorded proof. The kernel re-checks `Eq.refl α lhs : @Eq α lhs rhs`,
        // accepting **iff** the two sides genuinely coincide definitionally —
        // faithful (never a `B=B` tautology, two DISTINCT operands), never miscounted.
        p
    } else if let Some(p) = (ctx.instance_unfold && is_wo_the_def(thm))
        .then(|| prove_scoped_telescoped_eq_refl(&prop))
        .flatten()
    {
        // A **`wo_rel` `The`-threaded definitional axiom** — `minim_def`/`supr_def`/
        // `suc_def` (`minim r A = THE b. isMinim r A b`, `supr r A = minim r (Above r
        // A)`, `suc r A = minim r (AboveS r A)`), whose recorded proof bottoms out in
        // the un-mappable `…_def_raw` PAxm leaf. The LHS constant now embeds to its
        // registered `HOL.The`-threaded def-const ([`Ctx::embed_wo_the_const`]), which
        // δβ-reduces to exactly the embedded RHS (the shared `Nonempty α` witness and
        // — for `supr`/`suc` — the same `Relation.Field` supply the RHS's `Above`/
        // `AboveS` occurrence mints), so the (premise-guarded) equation is reflexive.
        // We prove it directly by `λ premises. Eq.refl α lhs`, gated on both
        // `instance_unfold` (final escalating pass → strictly additive) and the
        // [`is_wo_the_def`] statement-shape recognizer (so ONLY these three defs take
        // this arm). Attempted BEFORE the recorded proof. The kernel re-checks
        // `Eq.refl α lhs : @Eq α lhs rhs`, accepting **iff** the two sides coincide
        // definitionally — faithful (two DISTINCT operands, real premise preserved),
        // never miscounted.
        p
    } else if let Some(p) = prove_not_atomize(&prop) {
        // Isabelle's `Metis.not_atomize` (`(¬A ⟹ False) ≡ A`): a propositional
        // equality between two genuinely *different* (but classically equivalent)
        // props, so the recorded def-raw proof does not translate and the only
        // standing fallback is the wrong `eq_statement_lhs` reflexivity. We prove
        // the embedded statement directly via `propext` of a `Classical.em`-proved
        // `Iff` (foundational closure), attempted before the recorded proof. The
        // kernel re-checks the result against the embedded statement, so a wrong
        // match is rejected — never miscounted. `not_atomize` is a very high
        // fan-out Metis meta-logic lemma, so flipping it unblocks a large cascade.
        p
    } else if let Some(p) = prove_eq_refl_true(&prop) {
        // HOL's `simp_thms_6` (`(x = x) = True`), a high fan-out simp normal-form
        // rewrite whose recorded proof references export-absent nodes. Proved
        // directly via `propext` of `(x=x) ↔ True` (`eqTrueI` over reflexivity),
        // attempted before the recorded proof. Kernel-re-checked against the
        // embedded statement, so a wrong match is rejected — never miscounted.
        p
    } else if let Some(p) = prove_pure_conjunction_rule_first(&mut ctx, thm)? {
        // The Pure meta-conjunction rules `conjunctionD1`/`D2`/`I`, attempted
        // **before** the recorded proof (which bottoms out in the unmappable
        // `Pure.conjunction_def` def-raw chain). Under our `Pure.conjunction → And`
        // embedding they are clean's `And.left`/`And.right`/`And.intro`; verifying
        // them lands them in the closure so the many `c_class.super`/`.axioms`/
        // `.intro` projections that reference them resolve. Kernel-re-checked.
        p
    } else if let Some(p) = prove_connective_law(&prop) {
        // The basic HOL **connective intro/elim laws** at the meta level —
        // `disjI1`/`disjI2`/`conjI`/`FalseE` and their anonymous derivation-box
        // twins (`#(P ⟹ P∨Q)`, `#(Q ⟹ P∨Q)`, `#(P ⟹ Q ⟹ P∧Q)`,
        // `#(False ⟹ C)`). Their recorded proofs reconstruct the impredicative
        // connective *definition* through an `equal_elim` congruence tower whose
        // generic-reference legs leak an unsolved schematic (the `Pi[1]->Sort` vs
        // `Pi[1]->FVar` phantom-parameter reject — the single biggest remaining
        // equal_elim/AppP cascade family). Under the connective embedding the
        // conclusion is the reducible def-const (`isabelle.def.HOL.disj`/`conj`/
        // `False`), so each law has a direct impredicative λ-inhabitant supplied
        // from the SAME embedded `prop` that becomes the stored type
        // ([`prove_connective_law`]) — foundational (no axioms), faithful (the
        // real premise/def-const-conclusion statement, never a tautology), and the
        // kernel re-checks it δ-unfolding the def-const, so a mis-shape is rejected
        // — never miscounted. SHAPE-gated (exact def-const + matching premise
        // operands), so it fires only on these laws and their box twins; landing
        // them (heavily depended upon — `FalseE` sole-blocks thousands) unblocks a
        // large cascade. Mirrors the r11 conjunct-discharge sidestep of the same
        // congruence-tower wall.
        p
    } else if let Some(p) = prove_conjunction_bundle(&prop) {
        // A **`Pure.conjunction` simp-law bundle** — `simp_thms` / `all_simps` and
        // their kin: a run of erased `OFCLASS(_,type)` premises (`True →`) guarding
        // an `And`-tree whose leaves are standard propositional simp laws
        // (`(P∧True)=P`, `¬¬P=P`, `(P∨¬P)`-style identities, the `True`/`False`
        // `→`/`∧`/`∨` units, the `=True`/`=False`/`¬`-congruence rewrites). The
        // recorded proof is pathological (the `simp_thms` box is 1.35M nodes and
        // `BudgetExceeds` even at 200M), so it never translates. [`prove_conjunction_bundle`]
        // flattens the tree, discharges every leaf from the foundational leaf library
        // ([`prove_simp_leaf`] — `propext`/`Classical.em`/`Eq.{mp,mpr}` only), chains
        // the leaves with `And.intro`, and binds the leading `True` premises. It is
        // ALL-OR-NOTHING: an unrecognized leaf returns `None` (→ recorded path). The
        // kernel re-checks the whole assembled term against the stored bundle type,
        // so a wrong leaf rejects the entire bundle — never miscounted. Attempted
        // BEFORE the recorded proof. Foundational; strictly additive; `hol/**` only.
        p
    } else if let Some(p) = ctx
        .nonempty_erase
        .then(|| prove_conjunction_bundle_tree(&prop))
        .flatten()
    {
        // A **non-right-associated** `Pure.conjunction` simp-law bundle — the exact
        // same `simp_thms` / `all_simps` / `ex_simps` families as the arm above, but
        // exported as a NON-right-associated `Pure.conjunction` tree (a left child is
        // itself a conjunction). The right-spine [`prove_conjunction_bundle`] above
        // walks only the right spine, so it treats such a left conjunction as one
        // opaque non-equational leaf and declines; the recorded proof is the 1.35M-node
        // `simp_thms` box that never translates, so the line dies at `node=AbsP`.
        // [`prove_conjunction_bundle_tree`] discharges the tree STRUCTURALLY (recursing
        // into both `And` children), reproducing the stored tree shape exactly so the
        // kernel re-check succeeds. Gated on `ctx.nonempty_erase` (the trailing
        // faithfulness-restoring mode, which supplies the `Nonempty α` witnesses the
        // vacuous-`∀`/`∃` and `∧`-miniscoping leaves need) so it fires ONLY on lines
        // every historical mode rejected — strictly additive, never preempts an
        // accepted line, and each historical mode stays byte-identical. All-or-nothing
        // and kernel-re-checked, so a wrong leaf rejects the whole bundle — never
        // miscounted. Foundational; `hol/**` only.
        p
    } else if let Some(p) = ctx
        .nonempty_erase
        .then(|| prove_nonempty_single_leaf(&prop))
        .flatten()
    {
        // A **standalone** (non-bundle) quantifier simp law under an erased sort
        // premise — the single-leaf sibling of [`prove_conjunction_bundle`]: a
        // vacuous `(∀x. P) = P` / `(∃x. P) = P`, a one-point rule, or a `∨`/`⟶`
        // miniscoping law whose whole conclusion is that ONE equation rather than a
        // `Pure.conjunction` tree. Gated on `ctx.nonempty_erase` (the trailing
        // faithfulness-restoring mode) so it only fires on lines every historical
        // mode rejected — the `Nonempty α` premise supplies the witness the vacuous
        // laws need. [`prove_nonempty_single_leaf`] peels the premises, discharges the
        // single leaf ([`prove_simp_leaf_wit`] — `propext`/`Classical.{em,choice}`/
        // `Eq.{refl,symm,subst,mp,mpr}` only), and re-binds them. The kernel re-checks
        // the term against the stored statement, so a mis-shape rejects — never
        // miscounted. Foundational; strictly additive; `hol/**` only.
        p
    } else if let Some((ext_ty, ext_proof)) = ctx.prove_extremum_def(thm, &mut binders)? {
        // HOL's order-extremum defining axioms `Least/Greatest le P =
        // (THE x. P x ∧ (∀y. P y → x ≼ y))`. `Least`/`Greatest` are DEFINED as
        // those `The`-expressions, so we embed the LHS to its registered def-const
        // (`isabelle.def.Orderings.ord.Least`, …) which δ-unfolds to exactly the
        // epsilon `The` the RHS spells (both threaded with a shared, quantified
        // `Nonempty α` — HOL types are nonempty; clean makes it explicit). The
        // stored equation has two DISTINCT but definitionally-equal operands (never
        // a `B = B` tautology), proved by `Eq.refl`; the kernel accepts it iff the
        // def-const genuinely unfolds to the RHS. See
        // [`super::def_axioms::hilbert`]. Attempted before the recorded proof
        // (whose `…_def_raw` PAxm leaf is unmapped).
        ty_override = Some(ext_ty);
        ext_proof
    } else if let Some((if_ty, if_proof)) = ctx.prove_hol_if_def(thm, &mut binders)? {
        // HOL's `If_def` (`If P x y ≡ THE z. (P=True ⟶ z=x) ∧ (P=False ⟶ z=y)`)
        // — the sole characterising axiom of if-then-else, whose recorded proof
        // is the bare un-mappable `If_def_raw` PAxm leaf. The two sides embed to
        // genuinely DIFFERENT classical programs (`ite` over a classical
        // `Decidable` vs the guard-subtype epsilon), so no reflexive arm can
        // land it; [`Ctx::prove_hol_if_def`] proves the real equation by
        // excluded middle (`Classical.em` + `propext` + the epsilon's defining
        // property — foundational closure). The kernel re-checks the proof
        // against the stored equation (two DISTINCT operands — never a `B = B`
        // tautology), so a wrong bridge is rejected — never miscounted.
        ty_override = Some(if_ty);
        if_proof
    } else if let Some(p) = prove_the_eq_trivial(&prop) {
        // HOL's `the_eq_trivial` (`(THE x. x = a) = a`) — the sole characterising
        // axiom of the definite-description operator `HOL.The`. Its recorded proof
        // bottoms out at the un-mappable `the_eq_trivial_def_raw` PAxm leaf, so we
        // prove the embedded statement DIRECTLY from clean's classical epsilon
        // (`HOL.The` mapped onto `Classical.choice`; see
        // [`super::def_axioms::hilbert`]): `Subtype.property` of the guard-subtype
        // choice, applied to the existence proof `∃y. y = a`. `embed_term` routes
        // the LHS `THE x. x = a` to `isabelle.def.HOL.The α (Nonempty.intro α a)
        // (λx. x = a)` (witness `a`), so the equation's operands are genuinely
        // distinct (a `The`-application vs `a`, never a `B = B` tautology). The
        // kernel re-checks the proof (foundational closure) against `prop`, so a
        // wrong match is rejected — never miscounted. Unblocks `the_eq_trivial`'s
        // dependents (a high-fan-out definite-description root).
        p
    } else if let Some(p) = prove_classical_rule_first(&mut ctx, thm)? {
        // CLASSICAL-reasoning statement-level proof, attempted **before** the
        // recorded proof: HOL's `ccontr` / `classical` / `swap` / `eqTrueI`, whose
        // recorded proofs are intricate def-raw chains rooted at classical-EM /
        // `propext` lemmas (often referencing export-absent nodes). The statement
        // shape alone determines a direct clean proof built from `Classical.em` +
        // `propext` (whose transitive axiom closure is ⊆ the three foundationals).
        // The kernel re-checks the result against the embedded statement, so a
        // wrong guess is rejected — never miscounted.
        p
    } else if let Some(p) = prove_from_premises_first(&mut ctx, thm)? {
        // PURE statement-level proof, attempted **before** the recorded proof: an
        // implication chain `A₁ ⟹ … ⟹ Aₙ ⟹ C` whose conclusion `C` embeds
        // *identically* to one of the premises `Aᵢ` (premise-identity) or to a
        // syntactically reflexive equation. These shapes are structurally valid
        // regardless of how Isabelle recorded the proof, and are strictly more
        // reliable than translating an intricate `equal_elim`/`combination` chain
        // that references definitional lemmas (e.g. HOL's `allI`, which under this
        // embedding is the identity `(⋀x. P x) ⟹ (∀x. P x)` since `⋀` and `∀`
        // both embed to clean `Pi`). The kernel re-checks the result, so a wrong
        // guess is rejected — never miscounted. Only the premise-identity /
        // conclusion-reflexivity arms run here; the definitional-unfold arm stays
        // on the post-`translate_proof` fallback (it is less certain and the
        // recorded proof is preferred when it translates).
        p
    } else {
        // Snapshot the parameters discovered by embedding the *statement*: these
        // are the only legitimate quantifier binders. A failed proof-translation
        // attempt may register *phantom* parameters (e.g. a bare `Pure.eq`/`HOL.All`
        // constant embedded while walking a proof body that ultimately fails to
        // translate). If we then prove the theorem by a statement-level fallback,
        // those phantom params must NOT leak into the quantified type, or they
        // appear as spurious leading binders (which also breaks any later `PThm`
        // reference whose spine cannot fill them). So on the fallback path we
        // restore the param lists to this snapshot.
        let snap_types = ctx.type_params.clone();
        let snap_terms = ctx.term_params.clone();
        let snap_hyps = ctx.hyp_params.clone();
        // The proof ROOT's expected proposition is the embedded statement
        // itself. When the statement has no leading binders (empty premise
        // queue — so the expecting walk cannot desync the queue-based
        // recovery) and the root's spine head is a GENERIC (identity-tminst)
        // zproof reference ([`spine_head_generic_inst`]) — whose term
        // instantiation is recorded nowhere and is pinned only by the
        // statement — translate the root bidirectionally against `prop`.
        // Everything else keeps the plain path unchanged; a failed expecting
        // attempt falls through to the same fallback chain, and the kernel
        // re-checks the result either way.
        let root_expecting = ctx.premise_queue.is_empty() && spine_head_generic_inst(&thm.proof);
        // Box-internal-free → statement-schematic param aliasing is active ONLY
        // for this recorded-proof translation (see [`Ctx::term_param_free`]):
        // the statement `prop` above and every stored-type override embed with
        // it OFF, so the stored theorem type is byte-identical to the
        // historical embedding — a wrong aliasing can only make the VALUE
        // kernel-reject, never change what is stated.
        ctx.alias_frees = true;
        let attempt = if ctx.stmt_fallback {
            // **Statement-fallback escalation mode** ([`RootLane::
            // StmtFallback`]): skip the recorded proof entirely — the
            // synthetic error routes straight to the statement-level
            // fallback arms below (`prove_from_premises`, the definitional
            // reflexivity short-circuit), exactly the path the historical
            // pipeline took when the recorded proof failed to translate.
            // Runs only as the LAST escalation modes, after every
            // proof-translating mode kernel-rejected; the kernel re-checks
            // the fallback derivation, so a wrong guess is rejected — never
            // miscounted.
            Err(TranslateError::Unsupported(
                "statement-fallback escalation mode",
            ))
        } else if root_expecting {
            ctx.translate_proof_expecting(&thm.proof, &prop, closure, &mut binders)
        } else if let Some(e) = if ctx.bidir_tower && eq_tower_applicable(&thm.proof) {
            ctx.try_root_eq_tower_expecting(&thm.proof, &thm.prop, closure, &mut binders)?
        } else {
            None
        } {
            // **Root eq-tower via the Isabelle-level channel** (the primary
            // `BidirEqTower` routing): a `transitive`/`combination`/… tower
            // proving the statement equation `A ≡ B` is driven through the
            // Isabelle-level [`Ctx::translate_eq_expecting`] with the statement's
            // own `A`/`B` operands — which decomposes `Pure.combination`
            // congruence over meta-connectives (`Pure.imp`/`Pure.eq`, which embed
            // to clean `Pi`/special forms invisible to the clean-level `App`
            // congruence split). Only when this declines does the plain
            // clean-level expecting path run below (byte-identically). See
            // [`Ctx::try_root_eq_tower_expecting`].
            Ok(e)
        } else if ctx.bidir_tower && eq_tower_applicable(&thm.proof) {
            // **Recursive expectation propagation over the equational-tower
            // fragment** (`RootLane::BidirEqTower`): translate the recorded proof
            // ROOT bidirectionally against the embedded statement `prop`. The
            // expectation then propagates recursively down every interior
            // `equal_elim`/`transitive`/`symmetric`/`combination`/`reflexive`/
            // `AbsP`/`Abst`/`AppT`/`AppP` node — each operand is pinned by its
            // EXPECTED TYPE (the consumer's own statement namespace) rather than
            // by the recorded (crossed-namespace) instantiation table, fixing the
            // free-vs-schematic operand-desync the reject census decoded. Unlike
            // `root_expecting` (empty premise queue + generic spine head) this
            // fires for proofs WITH leading premises (the AbsP/Abst chain is
            // re-derived from the expected `Pi`) and for non-generic tower roots.
            // Runs only on the trailing `BidirEqTower` modes (after every
            // historical mode and the other lanes kernel-rejected), and the
            // kernel re-checks the assembled term against the stored statement,
            // so it can only ADD verifications — a wrong recovery is rejected,
            // never miscounted. A translate failure falls through to the same
            // fallback chain below, byte-identically.
            ctx.translate_proof_expecting(&thm.proof, &prop, closure, &mut binders)
        } else if ctx.bidir_tower && thm_spine_root_applicable(&thm.proof) {
            // **General Thm-spine / proof-redex expectation** (bidir stage 2):
            // a non-equational root — a `Thm`-headed spine or a `let`-style
            // proof β-redex chain — carrying LEADING `Pure.imp`/`⋀` premises,
            // which `root_expecting` (empty premise queue) and the equational
            // `eq_tower` lane (equational-axiom head) both decline. Translate the
            // whole recorded proof ROOT bidirectionally against the embedded
            // statement `prop`: [`Ctx::translate_proof_expecting`] peels the
            // leading premises against the expected `Pi`, reduces each interior
            // proof β-redex threading the expectation into its body, and solves
            // each interior `Thm` leg from its now-known expected proposition
            // (instead of the plain path's generic-table fill that manufactures
            // the phantom `expected=Sort got=FVar` operands the census decoded on
            // the discharge-chain twins). Runs only on the trailing
            // `BidirEqTower` modes, after every historical mode and the other
            // lanes kernel-rejected, and the kernel re-checks the assembled term
            // against the stored statement — so it can only ADD verifications; a
            // wrong recovery is rejected, never miscounted. A translate failure
            // falls through to the same fallback chain below, byte-identically.
            //
            // **Stage-3 HO isolation:** `bidir_redex` is enabled for the DURATION
            // of this single redex-lane call only, so the interior
            // `subst`/`ssubst`-family `Thm` legs' premise-driven + Miller-pattern
            // operand solve ([`Ctx::redex_premise_solve`]) is reachable
            // exclusively here. The eq-tower lane (and every historical path)
            // keeps `bidir_redex == false`, so the stage-1 `+5`/`+84` eq-tower
            // gains stay byte-identical.
            {
                // Stage-3 Miller lane only for SMALL roots: a large root's
                // "almost-right" Miller candidate is pathologically expensive for
                // the kernel to reduce/refute, so above the node cap keep the flag
                // OFF and take the pre-stage-3 (stage-1/2) path byte-identically —
                // the stage-2 β-redex expectation still runs (`bidir_tower`).
                ctx.bidir_redex = isa_proof_within_size(&thm.proof, MILLER_MAX_ROOT_PROOF_NODES);
                ctx.redex_miller_solves = 0;
                let r = ctx.translate_proof_expecting(&thm.proof, &prop, closure, &mut binders);
                ctx.bidir_redex = false;
                r
            }
        } else if let Some(e) =
            ctx.try_root_sort_absp_expecting(&thm.proof, &prop, closure, &mut binders)
        {
            // **Namespace-crossed root lane** (binder-order round): leading
            // implicit sort-hypothesis `AbsP`s over a GENERIC (identity-table)
            // `Thm` reference — the `<c>_class.<m>_def` hub export whose prop
            // and proof spell the object tvars in CROSSED namespaces, so the
            // plain path's verbatim identity fill instantiates the dependency
            // at swapped types (the multi-tvar `method.<m> α β` vs
            // `method.<m> β α` kernel-reject). The lane succeeds only when the
            // embedded statement pinned EVERY binder of the dependency
            // (namespace-free); otherwise the plain path below runs
            // byte-identically. See [`Ctx::try_root_sort_absp_expecting`].
            Ok(e)
        } else {
            ctx.translate_proof(&thm.proof, closure, &mut binders)
        };
        ctx.alias_frees = false;
        match attempt {
            Ok(p) => p,
            Err(e) => {
                ctx.type_params = snap_types;
                ctx.term_params = snap_terms;
                ctx.hyp_params = snap_hyps;
                // **Reprove-lane eliminator arm** ([`crate::hol::isabelle_reprove`],
                // env-gated `ISA_REPROVE=1`, default-OFF). A `ZNop`-hole tool-internal
                // lemma of the datatype-exhaust / eliminator shape
                // `⋀P y. … ⟹ (caseᵢ ⟹ P) ⟹ … ⟹ P` has no recorded proof to
                // translate (the `Err(e)` above is the hole), but its STATEMENT is
                // foundationally provable: a classical dichotomy / boolean exhaust
                // (`propext` / `Classical.em` / `Or.rec`, see [`prove_eliminator`]),
                // or — when the case premises are the constructor equations
                // `y = Cᵢ args` of a registered kernel inductive — a
                // **constructor-exhaust** via `T.casesOn` with the motive
                // `fun x => (y = x) → P` (see [`prove_ctor_exhaust`]). Both closures
                // are `⊆ FOUNDATIONAL_AXIOMS`. Gated on `reprove_enabled()` so the control
                // (`ISA_REPROVE` unset) is byte-identical to HEAD; strictly additive
                // (hole lines are 100% rejects today). The kernel re-checks the built
                // term against the embedded statement, so a wrong build is rejected —
                // never miscounted. `fallback_origin = e` keeps a reject bucketed by
                // the recorded-proof failure, not a fabricated `kernel-reject`.
                if let Some(p) = crate::hol::isabelle_reprove::reprove_enabled()
                    .then(|| prove_eliminator(&prop).or_else(|| prove_ctor_exhaust(&prop)))
                    .flatten()
                {
                    fallback_origin = Some(e.clone());
                    p
                } else if let Some(p) = ctx.prove_from_premises(&thm.prop)? {
                    // This statement-level derivation is a GUESS attempted only
                    // because the recorded proof failed (`e`). Its structural
                    // arms (premise-identity, conclusion-reflexivity) are
                    // usually right, but the `subst`/`def-unfold` arms can
                    // mis-fire on a statement whose real proof needed the
                    // (untranslatable) recorded derivation — the kernel then
                    // rejects the guess. In that case the HONEST reason is the
                    // recorded-proof failure `e` (typically an unresolved
                    // dependency), NOT "the kernel refused our proof": record
                    // it so the verifier buckets the reject honestly instead of
                    // inflating `kernel-reject` with dependency cascades.
                    fallback_origin = Some(e.clone());
                    p
                } else if let Some(p) = ctx.prove_class_membership_intro(&thm.prop)? {
                    // MEMBERSHIP-INTRODUCTION seam ([`Ctx::
                    // prove_class_membership_intro`]): the recorded proof failed
                    // (`e`), and this theorem concludes the real class membership
                    // `c_class α ops` of a registered structured class (the
                    // `<c>.intro_of_class` family, whose recorded arity proof
                    // reconstructs to the vacuous `True` — the dominant
                    // `expected=Pi[k]->isabelle.def.<c>_class got=Pi[k]->True`
                    // reject wall). The class def-const δ-unfolds to a
                    // conjunction of exactly the intro's discharged premises, so
                    // we assemble the membership witness from them
                    // (`And.intro`/`True.intro`, foundational closure) — a
                    // faithful proof of the strong conclusion, so the stored
                    // entry carries the real membership every downstream
                    // consumer needs. The kernel re-checks the assembly against
                    // the stored statement (δ-unfolding the def-const), so a
                    // wrong build is rejected; on a reject the honest reason is
                    // the recorded-proof failure `e` — recorded for honest
                    // bucketing. Strictly additive (fallback-only).
                    fallback_origin = Some(e.clone());
                    p
                } else if let Some((alpha_ty, lhs)) = eq_statement_lhs(&thm.prop) {
                    // FABRICATED reflexivity: the recorded proof failed (`e`), so
                    // we short-circuit an equation-shaped statement to
                    // `Eq.refl α lhs : @Eq α lhs rhs`. The kernel re-checks this,
                    // accepting ONLY when `lhs ≡ rhs` definitionally (a genuinely
                    // reflexive equation → `KernelVerified`). When it REJECTS, the
                    // honest reason is the recorded-proof failure `e` (typically an
                    // unresolved dependency), NOT "the kernel refused our proof";
                    // we record `e` so the verifier buckets the reject honestly
                    // instead of inflating `kernel-reject` with this artifact.
                    fallback_origin = Some(e.clone());
                    let alpha = ctx.embed_type_or_infer(alpha_ty, lhs, &mut binders)?;
                    let lhs_e = ctx.embed_term(lhs, &mut binders)?;
                    Expr::apps(
                        Expr::const_str_levels("Eq.refl", vec![obj_level()]),
                        [alpha, lhs_e],
                    )
                } else if let Some((n_premises, alpha_ty, lhs, _rhs)) =
                    eq_under_sort_premises(&thm.prop)
                {
                    // An equation gated ONLY by leading sort-constraint premises —
                    // `OFCLASS('a, c) ⟹ … ⟹ (lhs = rhs)` (see
                    // [`eq_under_sort_premises`]). The plain `eq_statement_lhs` arm
                    // above sees through `Trueprop` but NOT a leading `Pure.imp` sort
                    // constraint, so equations like HOL's `Set.Collect_mem_eq`
                    // (`OFCLASS('a, type) ⟹ Collect (λx. x ∈ A) = A`, whose recorded
                    // proof is a bare unmapped `…_mem_eq` axm) never reached the
                    // `Eq.refl` fallback. Each sort premise embeds to the vacuous
                    // `True`, so we discharge it with an enclosing `fun (_:True) =>`
                    // and prove the residual equation by `Eq.refl α (embed lhs)`. The
                    // stored type is the full embedded statement `prop`
                    // (`True → … → @Eq α (embed lhs) (embed rhs)` — the REAL equation,
                    // two DISTINCT operands, faithful), and the kernel accepts the
                    // `Eq.refl` ONLY when `embed lhs ≡ embed rhs` definitionally
                    // (here `Collect (λx. member x A)` β-η-reduces to `A`), rejecting a
                    // genuinely-different equation — never miscounted. Attempted only
                    // AFTER the recorded proof fails (strictly additive) and after the
                    // 0-premise `eq_statement_lhs` arm (which it never shadows).
                    // Like that arm, this is a FABRICATED reflexivity: the kernel
                    // re-checks it and accepts only when the residual equation is
                    // genuinely reflexive, so on a reject the honest reason is the
                    // recorded-proof failure `e` — recorded for honest bucketing.
                    fallback_origin = Some(e.clone());
                    let alpha = ctx.embed_type_or_infer(alpha_ty, lhs, &mut binders)?;
                    let lhs_e = ctx.embed_term(lhs, &mut binders)?;
                    let mut refl = Expr::apps(
                        Expr::const_str_levels("Eq.refl", vec![obj_level()]),
                        [alpha, lhs_e],
                    );
                    for _ in 0..n_premises {
                        refl = Expr::lam(BinderInfo::Default, Expr::const_str("True"), refl);
                    }
                    refl
                } else if let Some(p) = ctx
                    .instance_unfold
                    .then(|| {
                        let refl = prove_telescoped_eq_refl(&prop);
                        // Same honest-bucketing contract as the `Eq.refl` arms
                        // above: this telescoped reflexivity is FABRICATED after the
                        // recorded proof failed. The kernel re-checks it (accepting
                        // only a genuine datatype computation rule), so on a reject
                        // the honest reason is the recorded-proof failure `e`.
                        if refl.is_some() {
                            fallback_origin = Some(e.clone());
                        }
                        refl
                    })
                    .flatten()
                {
                    // The recorded proof did not translate (typically an intractable
                    // HOL-`typedef`/Hilbert-choice def-raw chain), but the embedded
                    // statement is a `Π… . lhs = rhs` whose LHS is **definitionally**
                    // the RHS under our datatype mappings — a HOL datatype
                    // *computation rule* (`case_sum f g (Inl a) = f a`,
                    // `case_option`, `rec_*`, `map_*.simps`) where
                    // `case_sum`/`Inl` map to the clean recursor/constructor and the
                    // LHS ι/β-reduces to the RHS. We prove it by the telescoped
                    // `λ…. Eq.refl lhs`, attempted only AFTER the recorded proof
                    // fails (strictly additive — never displaces a recorded-proof
                    // success). The kernel re-checks `Eq.refl lhs : lhs = rhs`,
                    // accepting iff the two sides genuinely coincide definitionally,
                    // so a non-reducible equation is rejected — never miscounted.
                    p
                } else {
                    return Err(e);
                }
            }
        }
    };
    let mut ty = ty_override.unwrap_or(prop);

    // Abstract innermost-first: hypotheses, then term params, then type params.
    for (_, p) in ctx.hyp_params.iter().rev() {
        ty = Expr::pi(BinderInfo::Default, p.ty.clone(), ty.abstract_fvar(p.fvar));
        proof = Expr::lam(
            BinderInfo::Default,
            p.ty.clone(),
            proof.abstract_fvar(p.fvar),
        );
    }
    for (_, p) in ctx.term_params.iter().rev() {
        ty = Expr::pi(BinderInfo::Default, p.ty.clone(), ty.abstract_fvar(p.fvar));
        proof = Expr::lam(
            BinderInfo::Default,
            p.ty.clone(),
            proof.abstract_fvar(p.fvar),
        );
    }
    for (_, p) in ctx.type_params.iter().rev() {
        ty = Expr::pi(BinderInfo::Default, p.ty.clone(), ty.abstract_fvar(p.fvar));
        proof = Expr::lam(
            BinderInfo::Default,
            p.ty.clone(),
            proof.abstract_fvar(p.fvar),
        );
    }

    // The leading object-`Type` binders of `ty` are exactly `ctx.type_params` in
    // first-seen order (the final loop pi-wraps them outermost-first), followed by
    // the `∀(x:T)` term-param binders (`ctx.term_params`, same order). Their
    // embedding keys, in those orders, name the leading binders outermost-first.
    // Recorded in the closure entry so a later fully-typed `PThm` reference can
    // map each explicit `tyinst`/`tminst` entry's `(n, i)` key to a binder
    // position and specialize this theorem directly.
    let meta = TranslatedMeta {
        type_param_keys: ctx.type_params.iter().map(|(k, _)| k.clone()).collect(),
        term_param_keys: ctx.term_params.iter().map(|(k, _)| k.clone()).collect(),
        fallback_origin,
    };

    Ok((
        Declaration::Theorem {
            name: Name::from_string(&thm.name),
            level_params: Vec::new(),
            type_: ty,
            value: proof,
        },
        meta,
    ))
}
