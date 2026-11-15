// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The [`ProofFormula`] schemas trust-ir OWNS, and the one text a formula in
//! each of them states.
//!
//! A formula IS its `payload`, read in its `schema`; `smtlib` is a rendering
//! of it, never a second formula. Which text the payload states depends on
//! the schema, so the one-formula rule is decided per schema, and only for a
//! schema trust-ir can read — every schema in [`OwnedFormulaSchema`], matched
//! exhaustively, with no wildcard arm anywhere a schema is decided:
//!
//! | schema | the payload | its one SMT-LIB2 text |
//! |---|---|---|
//! | [`SMTLIB2_FORMULA_SCHEMA`] | an SMT-LIB2 term | the payload |
//! | [`PRED_FORMULA_SCHEMA`] | `pred.N`, citing the module's predicate table | [`PredTable::smtlib_of`] of `N` |
//! | [`BVBLAST_GOAL_SCHEMA`] | a bit-blast goal claim (site, kind, goal digest) | none |
//! | [`SATRES_FORMULA_SCHEMA`] | a SAT-refutation claim (rule, clause-list digest) | none |
//! | [`LINEAGE_TRANSFORM_BINDING_SCHEMA`] | a lineage transform-binding digest | none |
//!
//! A formula states TWO texts — refused by both validators wherever a module
//! states it ([`crate::Module::formulas_stating_two_texts`]) — when its
//! `smtlib` rendering is present and is not its payload's one SMT-LIB2 text:
//! a rendering beside a claim (which states none), beside a `pred.N` citation
//! that resolves to another predicate or to none, or beside a different
//! `smtlib2` payload. A router may index a formula by its rendering and hand
//! it to a solver, so a rendering that is not the formula would have a
//! verdict on one text attributed to another.
//!
//! A schema NOT in the registry is opaque: trust-ir cannot read its payload,
//! so it never compares a rendering with it and never grounds, proves or
//! compares either as the formula (a router may still dispatch on the
//! rendering; nothing proves or certifies it). The registry is DERIVED, not
//! kept by hand: the `every_formula_schema_trust_ir_spells_is_registered`
//! census (crates/trust-ir/tests/formula_schema_census.rs) reads the wire
//! registry (`wire-allocations.toml`) and the sources and refuses a schema
//! in trust-ir's namespace that a `ProofFormula` carries without a variant
//! here, and a variant nothing carries.

use std::borrow::Cow;

use super::{
    BVBLAST_GOAL_SCHEMA, LINEAGE_TRANSFORM_BINDING_SCHEMA, ProofFormula, SMTLIB2_FORMULA_SCHEMA,
    bvblast_goal_formula_parts,
    satres::{SATRES_FORMULA_SCHEMA, satres_formula_parts},
};
use crate::pred::{PRED_FORMULA_SCHEMA, PredTable};
use crate::value::PredId;

mod observed;

/// A [`ProofFormula::schema`] trust-ir owns: it defines the schema and reads
/// its payload. Every other schema is opaque to trust-ir.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum OwnedFormulaSchema {
    /// [`SMTLIB2_FORMULA_SCHEMA`]: the payload IS an SMT-LIB2 term.
    Smtlib2,
    /// [`PRED_FORMULA_SCHEMA`]: the payload `pred.N` cites predicate `N` of
    /// the module's own table ([`crate::Module::predicates`]).
    Pred,
    /// [`BVBLAST_GOAL_SCHEMA`]: a bit-blast goal claim
    /// ([`bvblast_goal_formula_parts`]).
    BvBlastGoal,
    /// [`SATRES_FORMULA_SCHEMA`]: a SAT-refutation claim
    /// ([`satres_formula_parts`]).
    SatRes,
    /// [`LINEAGE_TRANSFORM_BINDING_SCHEMA`]: the digest binding a
    /// translation-validation obligation to one lineage edge.
    LineageTransformBinding,
}

impl OwnedFormulaSchema {
    /// Every owned schema, in declaration order.
    pub const ALL: [Self; 5] = [
        Self::Smtlib2,
        Self::Pred,
        Self::BvBlastGoal,
        Self::SatRes,
        Self::LineageTransformBinding,
    ];

    /// The schema's wire spelling.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::Smtlib2 => SMTLIB2_FORMULA_SCHEMA,
            Self::Pred => PRED_FORMULA_SCHEMA,
            Self::BvBlastGoal => BVBLAST_GOAL_SCHEMA,
            Self::SatRes => SATRES_FORMULA_SCHEMA,
            Self::LineageTransformBinding => LINEAGE_TRANSFORM_BINDING_SCHEMA,
        }
    }

    /// The owned schema spelled `schema`, or `None` for an opaque one.
    #[must_use]
    pub fn of(schema: &str) -> Option<Self> {
        Self::ALL.into_iter().find(|owned| owned.name() == schema)
    }
}

/// What the payload of a formula in an owned schema states, read in that
/// schema ([`ProofFormula::owned_text`]).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum OwnedFormulaText<'a> {
    /// Exactly this SMT-LIB2 text: an `smtlib2` payload, or the rendering of
    /// the predicate a `pred.N` citation resolves to.
    Smtlib(Cow<'a, str>),
    /// A claim trust-ir reads with its own strict parser; it states no
    /// SMT-LIB2 text.
    Claim,
    /// The payload does not read in its schema — a citation of no predicate
    /// the table renders, a claim that does not parse — so it states no
    /// formula at all, and every reader of it fails closed.
    Unread,
}

/// `pred.N`, `N` a canonical decimal (no sign, no leading zero) that fits a
/// [`PredId`] — the spelling [`PredTable::proof_formula`] writes, and no other.
fn pred_citation(payload: &str) -> Option<PredId> {
    let digits = payload.strip_prefix("pred.")?;
    let canonical = !digits.is_empty()
        && digits.bytes().all(|b| b.is_ascii_digit())
        && (digits == "0" || !digits.starts_with('0'));
    canonical
        .then(|| digits.parse::<u32>().ok())
        .flatten()
        .map(PredId::new)
}

/// `sha256:` then 64 lowercase hex digits — the spelling a
/// [`super::lineage_transform_binding_formula`] payload has, and no other.
fn is_sha256_digest_text(payload: &str) -> bool {
    payload.strip_prefix("sha256:").is_some_and(|hex| {
        hex.len() == 64
            && hex
                .bytes()
                .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
    })
}

impl ProofFormula {
    /// The owned schema this formula is in, or `None` when trust-ir cannot
    /// read its payload.
    #[must_use]
    pub fn owned_schema(&self) -> Option<OwnedFormulaSchema> {
        OwnedFormulaSchema::of(&self.schema)
    }

    /// What this formula's payload states, read in its owned schema; `None`
    /// for an opaque schema. `predicates` resolves a `pred.N` citation: the
    /// module's table ([`crate::Module::pred_table`]), or an empty table for a
    /// formula read without its module, where every citation dangles.
    ///
    /// A citation's text is rendered whole ([`PredTable::smtlib_of`]), and its
    /// length can be exponential in the table's. Comparing it with a text in
    /// hand is [`Self::states_two_texts`], which renders no further than that
    /// text.
    #[must_use]
    pub fn owned_text<'a>(&'a self, predicates: &PredTable<'_>) -> Option<OwnedFormulaText<'a>> {
        let schema = self.owned_schema()?;
        Some(match schema {
            OwnedFormulaSchema::Smtlib2 => OwnedFormulaText::Smtlib(Cow::Borrowed(&self.payload)),
            OwnedFormulaSchema::Pred => pred_citation(&self.payload)
                .and_then(|id| predicates.smtlib_of(id))
                .map_or(OwnedFormulaText::Unread, |text| {
                    OwnedFormulaText::Smtlib(Cow::Owned(text))
                }),
            OwnedFormulaSchema::BvBlastGoal => {
                if bvblast_goal_formula_parts(self).is_some() {
                    OwnedFormulaText::Claim
                } else {
                    OwnedFormulaText::Unread
                }
            }
            OwnedFormulaSchema::SatRes => {
                if satres_formula_parts(self).is_some() {
                    OwnedFormulaText::Claim
                } else {
                    OwnedFormulaText::Unread
                }
            }
            OwnedFormulaSchema::LineageTransformBinding => {
                if is_sha256_digest_text(&self.payload) {
                    OwnedFormulaText::Claim
                } else {
                    OwnedFormulaText::Unread
                }
            }
        })
    }

    /// This formula states TWO texts: it is in an owned schema, it carries an
    /// `smtlib` rendering, and that rendering is not its payload's one
    /// SMT-LIB2 text ([`Self::owned_text`]) — a claim states none, and a
    /// payload that does not read states nothing. What both validators refuse
    /// wherever a module states a formula. An opaque schema's rendering is
    /// never compared (and never read as the formula either).
    #[must_use]
    pub fn states_two_texts(&self, predicates: &PredTable<'_>) -> bool {
        let Some(rendering) = self.smtlib.as_deref() else {
            return false;
        };
        // A citation is rendered only up to the rendering's own length: a
        // longer text is not the rendering, and the predicate DAG's rendering
        // is not shared (fib(k) leaves for `pred.k = Conj([k-2, k-1])`), so
        // an unbounded render let a 65-entry validator-legal table ask both
        // validators for ~5*10^14 bytes (41.8 MB measured at 31 entries).
        if self.owned_schema() == Some(OwnedFormulaSchema::Pred) {
            return pred_citation(&self.payload)
                .and_then(|id| predicates.smtlib_of_within(id, rendering.len()))
                .is_none_or(|text| text != rendering);
        }
        match self.owned_text(predicates) {
            None => false,
            Some(OwnedFormulaText::Smtlib(text)) => text != rendering,
            Some(OwnedFormulaText::Claim | OwnedFormulaText::Unread) => true,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pred::{Pred, Space, Universe};
    use crate::value::UnivId;

    #[test]
    fn the_registry_spells_each_schema_once() {
        for owned in OwnedFormulaSchema::ALL {
            assert_eq!(OwnedFormulaSchema::of(owned.name()), Some(owned));
        }
        let mut names: Vec<_> = OwnedFormulaSchema::ALL.map(OwnedFormulaSchema::name).into();
        names.sort_unstable();
        names.dedup();
        assert_eq!(names.len(), OwnedFormulaSchema::ALL.len());
        assert_eq!(OwnedFormulaSchema::of("trust-types.Formula@1"), None);
        assert_eq!(OwnedFormulaSchema::of("SMTLIB2"), None);
    }

    #[test]
    fn a_pred_citation_states_the_cited_predicate_and_nothing_else() {
        let predicates = [Pred::InUniverse(UnivId::new(0), Space::Member)];
        let universes = [Universe::IntRange { lo: 1, hi: 8 }];
        let table = PredTable::new(&predicates, &universes);
        let honest = table.proof_formula(PredId::new(0)).unwrap();
        assert_eq!(
            honest.owned_text(&table),
            Some(OwnedFormulaText::Smtlib(Cow::Borrowed(
                "(and (<= 1 self) (<= self 8))"
            )))
        );
        assert!(!honest.states_two_texts(&table));
        let mut unrendered = honest.clone();
        unrendered.smtlib = None;
        assert!(!unrendered.states_two_texts(&table));
        let mut drifted = honest.clone();
        drifted.smtlib = Some("true".into());
        assert!(drifted.states_two_texts(&table));
        // Read without its module every citation dangles: a rendering is then
        // a text nothing shows the payload states.
        assert!(honest.states_two_texts(&PredTable::new(&[], &[])));
        for payload in ["pred.1", "pred.00", "pred.+0", "pred.", "pred.0 ", "pred0"] {
            let mut bad = honest.clone();
            bad.payload = payload.into();
            assert_eq!(
                bad.owned_text(&table),
                Some(OwnedFormulaText::Unread),
                "{payload}"
            );
            assert!(bad.states_two_texts(&table), "{payload}");
        }
    }

    #[test]
    fn a_claim_states_no_smtlib_text() {
        let digest = format!("sha256:{}", "ab".repeat(32));
        let claims = [
            ProofFormula::new(
                BVBLAST_GOAL_SCHEMA,
                format!("site=1:2:3\nkind=BoundsCheck\ngoal={}", "a".repeat(64)),
            ),
            ProofFormula::new(SATRES_FORMULA_SCHEMA, "rule=r\ncnf=sha256:00"),
            ProofFormula::new(LINEAGE_TRANSFORM_BINDING_SCHEMA, digest),
        ];
        let table = PredTable::new(&[], &[]);
        for claim in claims {
            assert_eq!(claim.owned_text(&table), Some(OwnedFormulaText::Claim));
            assert!(!claim.states_two_texts(&table));
            let mut rendered = claim.clone();
            rendered.smtlib = Some("true".into());
            assert!(rendered.states_two_texts(&table), "{}", claim.schema);
            let mut garbled = claim.clone();
            garbled.payload.push_str("\nextra=1");
            assert_eq!(garbled.owned_text(&table), Some(OwnedFormulaText::Unread));
        }
    }

    #[test]
    fn an_opaque_schema_is_never_compared() {
        let table = PredTable::new(&[], &[]);
        let opaque = ProofFormula::trust_types_json("{\"claim\":1}", "false", "Bool");
        assert_eq!(opaque.owned_text(&table), None);
        assert!(!opaque.states_two_texts(&table));
        let mut smt = ProofFormula::smtlib2("(>= 5 0)", "Bool");
        assert!(!smt.states_two_texts(&table));
        smt.smtlib = Some("(>= 0 5)".into());
        assert!(smt.states_two_texts(&table));
    }
}
