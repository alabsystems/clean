// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Carried-dependency record sections of the graduation record schema:
//! `carried_definitions` (v2), `carried_inductives` (v3), and
//! `carried_theorems` (v3.1). Split from [`super::record`] (one concern per
//! file); re-exported there so `record::CarriedX` paths stay stable.

use serde::{Deserialize, Serialize};

use super::record::{AxiomClosure, KernelFacts, NoveltyFacts};

/// v2: a definition-valued dependency carried into the graduated shard.
///
/// Carried definitions go through the SAME kernel discipline as theorems:
/// `Environment::add_decl` with the defining value in the fresh recheck
/// environment (dependency-ordered, definitions before their users), and an
/// honest axiom-closure contribution. A definition is only written to the
/// shard when at least one ACCEPTED theorem transitively requires it — and an
/// accepted theorem's foundational-only closure already subsumes its carried
/// definitions' closures, so every shard-resident definition is necessarily
/// foundational-only (the cake gate re-earns this by replay).
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub(crate) struct CarriedDefinition {
    pub(crate) name: String,
    /// Always `"definition"` in v2 (other kinds remain out of scope).
    pub(crate) decl_kind: String,
    /// `blake3:<hex>` canonical FlatExpr digest of the TYPE.
    pub(crate) statement_hash: String,
    /// Same encoding over the defining VALUE.
    pub(crate) value_hash: String,
    /// Reducibility hint carried from the source environment so the cake
    /// gate replays the definition exactly as the intake re-checked it.
    /// (Kernel def-eq unfolds all non-opaque definitions regardless, so this
    /// is replay fidelity, not a trust knob.)
    pub(crate) is_reducible: bool,
    /// Kernel re-check facts — recomputed by the intake, same as theorems.
    pub(crate) kernel: KernelFacts,
    /// This definition's own transitive axiom-closure contribution.
    pub(crate) axiom_closure: AxiomClosure,
    /// Accepted theorems that transitively require this definition.
    pub(crate) required_by: Vec<String>,
}

/// v3.1: a theorem-valued dependency carried into the graduated shard.
///
/// Carried theorems go through the SAME kernel discipline as candidates:
/// `Environment::add_decl` with the proof value in the fresh recheck
/// environment (dependency-ordered, interleaved with carried definitions and
/// families by topological order), and an honest axiom-closure contribution
/// (closure composes transitively — a dependent candidate's closure includes
/// every carried theorem's closure, so an axiom smuggled through a carried
/// proof still rejects the candidate). A carried theorem is **supporting
/// material, never a graduating candidate**: it does not appear in
/// `result.accepted`, it is not counted in graduation metrics, and the
/// `on_duplicate` policy does not apply to it — its `novelty` field is an
/// HONEST observation against the pinned baseline (a carried mathlib lemma
/// is expected to be `duplicate`), recorded, never used to reject.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub(crate) struct CarriedTheorem {
    pub(crate) name: String,
    /// Always `"theorem"` in v3.1.
    pub(crate) decl_kind: String,
    /// `blake3:<hex>` canonical FlatExpr digest of the TYPE.
    pub(crate) statement_hash: String,
    /// Same encoding over the proof VALUE.
    pub(crate) proof_hash: String,
    /// Kernel re-check facts — recomputed by the intake, same as candidates.
    pub(crate) kernel: KernelFacts,
    /// This theorem's own transitive axiom-closure contribution.
    pub(crate) axiom_closure: AxiomClosure,
    /// Honest baseline novelty of the carried statement (informational —
    /// `duplicate` is FINE for carried material; see struct doc).
    pub(crate) novelty: NoveltyFacts,
    /// Accepted theorems that transitively require this carried theorem.
    pub(crate) required_by: Vec<String>,
}

/// v3: a constructor of a carried inductive family (audit identity).
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub(crate) struct CarriedInductiveConstructor {
    pub(crate) name: String,
    /// `blake3:<hex>` canonical FlatExpr digest of the constructor TYPE.
    pub(crate) statement_hash: String,
}

/// v3: one family member written into the shard (shard order).
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub(crate) struct CarriedInductiveMember {
    pub(crate) name: String,
    /// `"inductive"`, `"constructor"`, or `"recursor"`.
    pub(crate) decl_kind: String,
    /// `blake3:<hex>` canonical FlatExpr digest of the member TYPE.
    pub(crate) statement_hash: String,
}

/// v3: a value-less inductive-family dependency carried into the graduated
/// shard under the kernel's full `add_inductive` discipline.
///
/// A carried family's kernel certificate is its checked `InductiveDecl`
/// re-check (positivity, nested positivity, universe constraints, recursor
/// generation) in the fresh recheck environment — the same certificate the
/// kernel itself trusts for `Nat` and `Eq`. Its honest axiom-closure
/// contribution is the union over ALL member types (inductive type + every
/// constructor type) and must be foundational-only — a poisoned constructor
/// rejects the whole family even if no accepted theorem references it
/// (design §6, surface a4). v3.0 fence: single-type, non-nested, non-mutual
/// families only; everything else fails closed at intake.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub(crate) struct CarriedInductive {
    /// Family-root (inductive type) name.
    pub(crate) name: String,
    /// Universe level parameter names of the family.
    pub(crate) level_params: Vec<String>,
    /// `InductiveDecl.num_params` as re-checked (post fixed-index promotion).
    pub(crate) num_params: u32,
    /// `blake3:<hex>` canonical FlatExpr digest of the inductive TYPE.
    pub(crate) statement_hash: String,
    /// The family's constructors, declaration order.
    pub(crate) constructors: Vec<CarriedInductiveConstructor>,
    /// Every family constant written into the shard, in shard order: the
    /// root, every constructor, plus exactly the generated recursors
    /// (`rec` / `casesOn` / `recOn`) the accepted shard content references.
    pub(crate) members_in_shard: Vec<CarriedInductiveMember>,
    /// Kernel re-check facts: `family_checked: true`,
    /// `value_typechecked: false` (honest — there is no value).
    pub(crate) kernel: KernelFacts,
    /// Union closure over all member types; must be foundational-only.
    pub(crate) axiom_closure: AxiomClosure,
    /// Optional structure field names (elaborator fidelity for downstream
    /// importers only — never replayed for trust; kernel `Expr::proj` typing
    /// reads the side tables `add_inductive` populates).
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub(crate) structure_fields: Vec<String>,
    /// Accepted theorems that transitively require this family.
    pub(crate) required_by: Vec<String>,
}
