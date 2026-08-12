// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Pure proof-term AST + parser for native kernel re-verification of real
//! Isabelle/HOL library theorems (closure replay).
//!
//! The Isabelle side (`scripts/isabelle/export_pure_proofs.ML`) serializes each
//! theorem's full Pure proof term (from `record_proofs=2`) as JSON. This module
//! parses that JSON into [`IsaProof`] / [`IsaTerm`] / [`IsaType`]. A separate
//! translator (closure-replay) maps each proof to a clean kernel `Expr`:
//!
//! - [`IsaProof::Thm`] (a `PThm` reference, keyed by stable proof-term serial)
//!   resolves to an already-verified clean declaration (the closure);
//! - [`IsaProof::Axm`] (a `PAxm` leaf) maps to its clean bootstrap proof;
//! - the structural nodes (`AbsP`/`Abst`/`AppP`/`AppT`/`Hyp`/`Bound`) translate
//!   directly to clean lambdas / applications / bound variables.
//!
//! Parsing only — translation + the bootstrap axiom map live alongside and are
//! gated on the kernel actually accepting each result (nothing is `KernelVerified`
//! the kernel did not check).

use serde::Deserialize;

/// Isabelle type (mirrors the JSON `{"k":..}` tagged shapes).
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, Deserialize)]
#[serde(tag = "k")]
pub enum IsaType {
    #[serde(rename = "Type")]
    Type {
        n: String,
        #[serde(default)]
        a: Vec<IsaType>,
    },
    #[serde(rename = "TFree")]
    TFree { n: String },
    #[serde(rename = "TVar")]
    TVar { n: String, i: i64 },
}

/// Isabelle term.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, Deserialize)]
#[serde(tag = "k")]
pub enum IsaTerm {
    #[serde(rename = "Const")]
    Const { n: String, t: IsaType },
    #[serde(rename = "Free")]
    Free { n: String, t: IsaType },
    #[serde(rename = "Var")]
    Var { n: String, i: i64, t: IsaType },
    #[serde(rename = "Bound")]
    Bound { i: i64 },
    #[serde(rename = "Abs")]
    Abs {
        n: String,
        t: IsaType,
        b: Box<IsaTerm>,
    },
    #[serde(rename = "App")]
    App { f: Box<IsaTerm>, a: Box<IsaTerm> },
}

/// One schematic **type**-variable instantiation carried by a fully-typed
/// (`zproof`) `Thm`/`Axm`/`Oracle` reference: substitute the referenced
/// theorem's schematic type var `(n, i)` (a `TVar { n, i }`) with `ty`. Absent
/// from the legacy export (which records no schematic instantiations), so
/// `#[serde(default)]` on the carrying field keeps legacy JSON deserializing.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, Deserialize)]
pub struct IsaTypeInst {
    /// Schematic type-var base name (e.g. `'a`).
    pub n: String,
    /// Schematic type-var index.
    pub i: i64,
    /// The concrete type substituted for it.
    pub ty: IsaType,
}

/// One schematic **term**-variable instantiation carried by a fully-typed
/// (`zproof`) `Thm`/`Axm`/`Oracle` reference: substitute the referenced
/// theorem's schematic var `(n, i)` (a `Var { n, i }`) with `t`. Absent from the
/// legacy export.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, Deserialize)]
pub struct IsaTermInst {
    /// Schematic var base name.
    pub n: String,
    /// Schematic var index.
    pub i: i64,
    /// The concrete term substituted for it.
    pub t: IsaTerm,
}

/// Isabelle Pure proof term.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, Deserialize)]
#[serde(tag = "k")]
pub enum IsaProof {
    /// `PThm` — reference to another theorem, keyed by its proof-term serial.
    ///
    /// The fully-typed (`zproof`) export additionally carries the referenced
    /// theorem's schematic **type** and **term** instantiation tables
    /// (`tyinst`/`tminst`) — the explicit specialization Isabelle applies to the
    /// polymorphic theorem at this use site. The legacy export records neither
    /// (the implicit type instantiation was reconstructed from the term spine),
    /// so both fields default to empty and legacy JSON still deserializes.
    #[serde(rename = "thm")]
    Thm {
        id: i64,
        thy: String,
        #[serde(default)]
        tyinst: Vec<IsaTypeInst>,
        #[serde(default)]
        tminst: Vec<IsaTermInst>,
    },
    /// `PAxm` — a Pure/HOL base axiom leaf. The fully-typed export carries the
    /// axiom's schematic instantiation tables (`tyinst`/`tminst`); legacy omits
    /// them (defaulting empty).
    #[serde(rename = "axm")]
    Axm {
        name: String,
        #[serde(default)]
        tyinst: Vec<IsaTypeInst>,
        #[serde(default)]
        tminst: Vec<IsaTermInst>,
    },
    /// `AbsP` — abstraction over a hypothesis (proof of `h`).
    #[serde(rename = "absp")]
    AbsP {
        #[serde(default)]
        h: Option<IsaTerm>,
        b: Box<IsaProof>,
    },
    /// `Abst` — abstraction over a term variable.
    #[serde(rename = "abst")]
    Abst {
        #[serde(default)]
        ty: Option<IsaType>,
        b: Box<IsaProof>,
    },
    /// `p %% q` — proof applied to proof.
    #[serde(rename = "appp")]
    AppP { f: Box<IsaProof>, a: Box<IsaProof> },
    /// `p % t` — proof applied to term.
    #[serde(rename = "appt")]
    AppT {
        f: Box<IsaProof>,
        #[serde(default)]
        a: Option<IsaTerm>,
    },
    /// `Hyp` — a discharged hypothesis reference.
    #[serde(rename = "hyp")]
    Hyp { p: IsaTerm },
    /// `PBound` — de Bruijn proof/term variable.
    #[serde(rename = "bound")]
    Bound { i: i64 },
    /// `PClass (T, c)` — a type-class / sort membership witness (e.g.
    /// `'a :: HOL.type`). For the universal `type` sort this is benign and
    /// carries no logical content; the translator drops it. NOT a hole.
    #[serde(rename = "ofclass")]
    OfClass { ty: IsaType, c: String },
    /// `MinProof` — an unverifiable hole (sorry / oracle / unrecorded). These
    /// can never be `KernelVerified`.
    #[serde(rename = "min")]
    Min,
    /// `ZConstp ZOracle` — a fully-typed-export oracle hole. An oracle is an
    /// unverified external assertion, so this can never be `KernelVerified`
    /// (treated exactly like [`IsaProof::Min`]). The instantiation tables are
    /// carried for shape symmetry but unused (a hole translates to nothing).
    #[serde(rename = "oracle")]
    Oracle {
        name: String,
        #[serde(default)]
        tyinst: Vec<IsaTypeInst>,
        #[serde(default)]
        tminst: Vec<IsaTermInst>,
    },
    /// `ZNop` — a fully-typed-export empty/placeholder node. It only appears for
    /// nodes built below `Proofterm.proofs := 6` (a not-yet-recorded library
    /// dependency in a partial heap), so it is an unverifiable hole, treated
    /// exactly like [`IsaProof::Min`].
    #[serde(rename = "nop")]
    Nop,
    /// Any other node we don't model yet (e.g. `OfClass`).
    #[serde(rename = "other")]
    Other,
}

/// One exported theorem: name, statement, and Pure proof.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, Deserialize)]
pub struct IsaProvenTheorem {
    pub name: String,
    /// The theorem's own proof-term serial — the stable key other theorems'
    /// `PThm` nodes reference. `0` when the export omits it (legacy/synthetic).
    #[serde(default)]
    pub serial: i64,
    pub prop: IsaTerm,
    pub proof: IsaProof,
}

/// Parse one exported theorem's JSON.
///
/// # Errors
/// Returns the serde error if the JSON does not match the schema.
pub fn parse_proven_theorem(json: &str) -> Result<IsaProvenTheorem, serde_json::Error> {
    // Deeply-nested proof terms (large anonymous intermediate proof-spine nodes,
    // referenced by serial as dependencies) exceed serde_json's default 128-level
    // recursion cap and would otherwise be lost to `parse-error`, cascading their
    // dependents into `unresolved-dep`. Disable the cap so they parse. The streaming
    // replay parses on a single thread; run it with a large `RUST_MIN_STACK` so the
    // recursive descent over deep nodes does not overflow the stack.
    let mut de = serde_json::Deserializer::from_str(json);
    de.disable_recursion_limit();
    let thm = <IsaProvenTheorem as Deserialize>::deserialize(&mut de)?;
    de.end()?;
    Ok(thm)
}

impl IsaProof {
    /// Whether this proof tree contains an unverifiable hole (`MinProof`/oracle),
    /// which forecloses `KernelVerified` — such theorems can only be
    /// `SourceVerified`.
    #[must_use]
    pub fn has_hole(&self) -> bool {
        match self {
            IsaProof::Min | IsaProof::Oracle { .. } | IsaProof::Nop | IsaProof::Other => true,
            IsaProof::Thm { .. }
            | IsaProof::Axm { .. }
            | IsaProof::Hyp { .. }
            | IsaProof::OfClass { .. }
            | IsaProof::Bound { .. } => false,
            IsaProof::AbsP { b, .. } | IsaProof::Abst { b, .. } | IsaProof::AppT { f: b, .. } => {
                b.has_hole()
            }
            IsaProof::AppP { f, a } => f.has_hole() || a.has_hole(),
        }
    }

    /// Collect the serials of every `PThm` dependency (for topological closure
    /// ordering).
    pub fn thm_deps(&self, out: &mut Vec<i64>) {
        match self {
            IsaProof::Thm { id, .. } => out.push(*id),
            IsaProof::Axm { .. }
            | IsaProof::Hyp { .. }
            | IsaProof::OfClass { .. }
            | IsaProof::Bound { .. }
            | IsaProof::Min
            | IsaProof::Oracle { .. }
            | IsaProof::Nop
            | IsaProof::Other => {}
            IsaProof::AbsP { b, .. } | IsaProof::Abst { b, .. } | IsaProof::AppT { f: b, .. } => {
                b.thm_deps(out);
            }
            IsaProof::AppP { f, a } => {
                f.thm_deps(out);
                a.thm_deps(out);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const REAL_AEQA: &str = r#"{"name":"Demo.a_eq_a","prop":{"k":"App","f":{"k":"Const","n":"HOL.Trueprop","t":{"k":"Type","n":"fun","a":[{"k":"Type","n":"HOL.bool","a":[]},{"k":"Type","n":"prop","a":[]}]}},"a":{"k":"App","f":{"k":"App","f":{"k":"Const","n":"HOL.eq","t":{"k":"Type","n":"fun","a":[]}},"a":{"k":"Free","n":"a","t":{"k":"Type","n":"Nat.nat","a":[]}}},"a":{"k":"Free","n":"a","t":{"k":"Type","n":"Nat.nat","a":[]}}}},"proof":{"k":"appt","f":{"k":"axm","name":"Pure.reflexive"},"a":{"k":"Free","n":"a","t":{"k":"Type","n":"Nat.nat","a":[]}}}}"#;

    #[test]
    fn parses_real_exported_theorem() {
        let t = parse_proven_theorem(REAL_AEQA).expect("should parse real export");
        assert_eq!(t.name, "Demo.a_eq_a");
        // statement is Trueprop (eq a a)
        assert!(matches!(t.prop, IsaTerm::App { .. }));
        // proof is reflexive axiom applied to a term
        assert!(matches!(t.proof, IsaProof::AppT { .. }));
        assert!(!t.proof.has_hole());
        let mut deps = Vec::new();
        t.proof.thm_deps(&mut deps);
        assert!(deps.is_empty(), "this leaf proof has no PThm deps");
    }

    #[test]
    fn detects_holes_and_deps() {
        let p = IsaProof::AppP {
            f: Box::new(IsaProof::Thm {
                id: 42,
                thy: "HOL".into(),
                tyinst: Vec::new(),
                tminst: Vec::new(),
            }),
            a: Box::new(IsaProof::Min),
        };
        assert!(p.has_hole());
        let mut deps = Vec::new();
        p.thm_deps(&mut deps);
        assert_eq!(deps, vec![42]);
    }

    /// A legacy `thm`/`axm` node (NO `tyinst`/`tminst` keys, as the legacy export
    /// emits) must still deserialize — the new fields default to empty `Vec`s.
    #[test]
    fn legacy_thm_axm_without_insts_default_to_empty() {
        let legacy_thm = r#"{"k":"thm","id":7,"thy":"HOL"}"#;
        let p: IsaProof = serde_json::from_str(legacy_thm).expect("legacy thm parses");
        match p {
            IsaProof::Thm {
                id, tyinst, tminst, ..
            } => {
                assert_eq!(id, 7);
                assert!(tyinst.is_empty() && tminst.is_empty());
            }
            other => panic!("expected Thm, got {other:?}"),
        }
        let legacy_axm = r#"{"k":"axm","name":"Pure.reflexive"}"#;
        let p: IsaProof = serde_json::from_str(legacy_axm).expect("legacy axm parses");
        assert!(
            matches!(p, IsaProof::Axm { tyinst, tminst, .. } if tyinst.is_empty() && tminst.is_empty())
        );
    }

    /// A fully-typed (`zproof`) `thm` node carrying explicit `tyinst`/`tminst`
    /// tables parses with the populated instantiations.
    #[test]
    fn zproof_thm_with_insts_parses() {
        let zproof_thm = r#"{"k":"thm","id":9,"thy":"HOL","tyinst":[{"n":"'a","i":0,"ty":{"k":"Type","n":"Nat.nat","a":[]}}],"tminst":[{"n":"x","i":0,"t":{"k":"Free","n":"a","t":{"k":"Type","n":"Nat.nat","a":[]}}}]}"#;
        let p: IsaProof = serde_json::from_str(zproof_thm).expect("zproof thm parses");
        match p {
            IsaProof::Thm { tyinst, tminst, .. } => {
                assert_eq!(tyinst.len(), 1);
                assert_eq!(tyinst[0].n, "'a");
                assert_eq!(tyinst[0].i, 0);
                assert_eq!(tminst.len(), 1);
                assert_eq!(tminst[0].n, "x");
            }
            other => panic!("expected Thm, got {other:?}"),
        }
    }

    /// The new `oracle` and `nop` fully-typed-export tags parse and are holes
    /// (never `KernelVerified`), exactly like `min`.
    #[test]
    fn oracle_and_nop_are_holes() {
        let oracle = r#"{"k":"oracle","name":"some_oracle","tyinst":[],"tminst":[]}"#;
        let p: IsaProof = serde_json::from_str(oracle).expect("oracle parses");
        assert!(matches!(p, IsaProof::Oracle { .. }));
        assert!(p.has_hole());

        let nop = r#"{"k":"nop"}"#;
        let p: IsaProof = serde_json::from_str(nop).expect("nop parses");
        assert!(matches!(p, IsaProof::Nop));
        assert!(p.has_hole());

        // A proof containing an oracle/nop anywhere is a hole.
        let nested = IsaProof::AppT {
            f: Box::new(IsaProof::Nop),
            a: None,
        };
        assert!(nested.has_hole());
    }
}
