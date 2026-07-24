// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Core types for importing dependent type theory systems (Agda, Idris 2, F*).
//!
//! These types represent the intermediate format between system-specific
//! parsers and the Mathverse shard writer. Each DTT system exports declarations
//! in a slightly different format, but they share a common core: named
//! declarations with type expressions, optional value expressions, and
//! axiom profile tracking for features that cannot be directly embedded
//! (cubical types, QTT, effect types).

use serde::{Deserialize, Serialize};

use crate::types::{AxiomProfile, SourceSystem};

// ---------------------------------------------------------------------------
// DttSystem
// ---------------------------------------------------------------------------

/// Which DTT system a declaration originates from.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum DttSystem {
    /// Agda (cubical, HoTT, standard).
    Agda,
    /// Idris 2 (QTT, linear types).
    Idris2,
    /// F* (effects, refinement types, extraction).
    Fstar,
}

impl DttSystem {
    /// Map to the corresponding [`SourceSystem`] variant.
    #[must_use]
    pub fn to_source_system(self) -> SourceSystem {
        match self {
            Self::Agda => SourceSystem::Agda,
            Self::Idris2 => SourceSystem::Idris2,
            Self::Fstar => SourceSystem::FStar,
        }
    }

    /// Short label for display and logging.
    #[must_use]
    pub fn label(self) -> &'static str {
        match self {
            Self::Agda => "agda",
            Self::Idris2 => "idris2",
            Self::Fstar => "fstar",
        }
    }
}

// ---------------------------------------------------------------------------
// DttExpr — lightweight expression representation
// ---------------------------------------------------------------------------

/// Lightweight expression representation for DTT imports.
///
/// This is not the full kernel `Expr` — it is a serializable surface-level
/// representation that gets lowered to `FlatExpr` during shard writing.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum DttExpr {
    /// A named reference (constant, variable, constructor).
    Var(String),
    /// Universe at a given level.
    Sort(u32),
    /// Function type / Pi: `(name : domain) -> codomain`.
    Pi {
        binder_name: String,
        domain: Box<DttExpr>,
        codomain: Box<DttExpr>,
    },
    /// Lambda: `fun (name : ty) => body`.
    Lam {
        binder_name: String,
        binder_type: Box<DttExpr>,
        body: Box<DttExpr>,
    },
    /// Application.
    App(Box<DttExpr>, Box<DttExpr>),
    /// Opaque / unparsed expression (preserved as a string for diagnostics).
    Opaque(String),
}

impl DttExpr {
    /// Convenience: create a named variable reference.
    #[must_use]
    pub fn var(name: &str) -> Self {
        Self::Var(name.to_owned())
    }

    /// Convenience: create Sort(0) — `Prop` / `Type` level 0.
    #[must_use]
    pub fn sort0() -> Self {
        Self::Sort(0)
    }

    /// Convenience: wrap an unparsed string.
    #[must_use]
    pub fn opaque(s: &str) -> Self {
        Self::Opaque(s.to_owned())
    }
}

// ---------------------------------------------------------------------------
// DttDeclaration
// ---------------------------------------------------------------------------

/// A single declaration extracted from a DTT system.
///
/// This is the unit of import: one named constant with a type, optional
/// value, and metadata about which axioms it depends on.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct DttDeclaration {
    /// Fully qualified name (e.g., `Agda.Builtin.Nat.Nat`).
    pub name: String,
    /// Type expression (always present for well-formed declarations).
    pub type_expr: DttExpr,
    /// Value expression (None for axioms / postulates / opaques).
    pub value_expr: Option<DttExpr>,
    /// Originating system.
    pub system: DttSystem,
    /// Axiom profile bits for features that are axiomatized in clean.
    pub axiom_profile: AxiomProfile,
    /// Whether this was an axiom/postulate in the source system.
    pub is_axiom: bool,
    /// Source file path (for provenance tracking).
    pub source_file: Option<String>,
    /// Original module name in the source system.
    pub module_name: Option<String>,
}

impl DttDeclaration {
    /// Check if this declaration has a proof/definition body.
    #[must_use]
    pub fn has_value(&self) -> bool {
        self.value_expr.is_some()
    }

    /// Check if cubical axioms are present.
    #[must_use]
    pub fn is_cubical(&self) -> bool {
        self.axiom_profile.has(AxiomProfile::AGDA_CUBICAL)
    }

    /// Check if QTT axioms are present.
    #[must_use]
    pub fn is_qtt(&self) -> bool {
        self.axiom_profile.has(AxiomProfile::IDRIS_QTT)
    }
}

// ---------------------------------------------------------------------------
// DttModule
// ---------------------------------------------------------------------------

/// A module of declarations from a single DTT system.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct DttModule {
    /// Module name (e.g., `Agda.Builtin.Nat`).
    pub name: String,
    /// Declarations in this module.
    pub declarations: Vec<DttDeclaration>,
    /// Imported module names.
    pub imports: Vec<String>,
    /// Originating system.
    pub system: DttSystem,
}

impl DttModule {
    /// Count of declarations.
    #[must_use]
    pub fn decl_count(&self) -> usize {
        self.declarations.len()
    }

    /// Count of axioms/postulates.
    #[must_use]
    pub fn axiom_count(&self) -> usize {
        self.declarations.iter().filter(|d| d.is_axiom).count()
    }
}

// ---------------------------------------------------------------------------
// System-specific intermediate types
// ---------------------------------------------------------------------------

/// Agda JSON export entry (from `--interaction-json` output).
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct AgdaExport {
    /// Declaration name.
    pub name: String,
    /// Type as string (Agda's pretty-printed form).
    pub type_str: String,
    /// Definition body as string (None for postulates).
    pub def_str: Option<String>,
    /// Whether this is a postulate.
    pub is_postulate: bool,
    /// Whether this uses cubical primitives (Glue, hcomp, transport, etc.).
    pub is_cubical: bool,
    /// Module path.
    pub module: Option<String>,
    /// Universe level (parsed from type).
    pub universe_level: Option<u32>,
}

/// Idris 2 TT2 IR entry.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct IdrisTT {
    /// Declaration name.
    pub name: String,
    /// Type in TT2 format.
    pub type_tt: String,
    /// Definition in TT2 format (None for postulates).
    pub def_tt: Option<String>,
    /// Whether this is a postulate.
    pub is_postulate: bool,
    /// Whether this uses QTT (quantitative type theory) annotations.
    pub uses_qtt: bool,
    /// Totality status from Idris 2.
    pub totality: Option<IdrisTotality>,
    /// Namespace path.
    pub namespace: Option<String>,
}

/// Idris 2 totality classification.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum IdrisTotality {
    Total,
    Covering,
    Partial,
}

/// F* extraction entry.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct FstarExtraction {
    /// Declaration name.
    pub name: String,
    /// Type in F* syntax.
    pub type_str: String,
    /// Definition body (None for `assume val`).
    pub def_str: Option<String>,
    /// Whether this is an assumed value (`assume val`).
    pub is_assumed: bool,
    /// F* effect (Tot, Lemma, ST, etc.).
    pub effect: Option<String>,
    /// Module path.
    pub module: Option<String>,
}

// ---------------------------------------------------------------------------
// DttImportStats
// ---------------------------------------------------------------------------

/// Statistics for a DTT import batch.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct DttImportStats {
    /// Per-system declaration counts.
    pub agda_count: usize,
    pub idris2_count: usize,
    pub fstar_count: usize,
    /// Number of declarations axiomatized due to cubical features.
    pub cubical_axiomatized: usize,
    /// Number of declarations axiomatized due to QTT features.
    pub qtt_axiomatized: usize,
    /// Number of declarations axiomatized due to F* effects.
    pub effect_axiomatized: usize,
    /// Total parse errors encountered.
    pub parse_errors: usize,
}

impl DttImportStats {
    /// Total declarations imported across all systems.
    #[must_use]
    pub fn total(&self) -> usize {
        self.agda_count + self.idris2_count + self.fstar_count
    }

    /// Total axiomatized declarations.
    #[must_use]
    pub fn total_axiomatized(&self) -> usize {
        self.cubical_axiomatized + self.qtt_axiomatized + self.effect_axiomatized
    }

    /// Merge another stats batch into this one.
    pub fn merge(&mut self, other: &Self) {
        self.agda_count += other.agda_count;
        self.idris2_count += other.idris2_count;
        self.fstar_count += other.fstar_count;
        self.cubical_axiomatized += other.cubical_axiomatized;
        self.qtt_axiomatized += other.qtt_axiomatized;
        self.effect_axiomatized += other.effect_axiomatized;
        self.parse_errors += other.parse_errors;
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_dtt_system_to_source_system() {
        assert_eq!(DttSystem::Agda.to_source_system(), SourceSystem::Agda);
        assert_eq!(DttSystem::Idris2.to_source_system(), SourceSystem::Idris2);
        assert_eq!(DttSystem::Fstar.to_source_system(), SourceSystem::FStar);
    }

    #[test]
    fn test_dtt_system_label() {
        assert_eq!(DttSystem::Agda.label(), "agda");
        assert_eq!(DttSystem::Idris2.label(), "idris2");
        assert_eq!(DttSystem::Fstar.label(), "fstar");
    }

    #[test]
    fn test_dtt_declaration_has_value() {
        let decl = DttDeclaration {
            name: "Nat".to_owned(),
            type_expr: DttExpr::sort0(),
            value_expr: None,
            system: DttSystem::Agda,
            axiom_profile: AxiomProfile::NONE,
            is_axiom: true,
            source_file: None,
            module_name: None,
        };
        assert!(!decl.has_value());
        assert!(!decl.is_cubical());
    }

    #[test]
    fn test_dtt_declaration_cubical() {
        let decl = DttDeclaration {
            name: "transport".to_owned(),
            type_expr: DttExpr::opaque("Path A x y -> A"),
            value_expr: None,
            system: DttSystem::Agda,
            axiom_profile: AxiomProfile::AGDA_CUBICAL,
            is_axiom: true,
            source_file: Some("Cubical.agda".to_owned()),
            module_name: Some("Agda.Primitive.Cubical".to_owned()),
        };
        assert!(decl.is_cubical());
        assert!(!decl.is_qtt());
    }

    #[test]
    fn test_dtt_module_counts() {
        let module = DttModule {
            name: "Test".to_owned(),
            declarations: vec![
                DttDeclaration {
                    name: "ax1".to_owned(),
                    type_expr: DttExpr::sort0(),
                    value_expr: None,
                    system: DttSystem::Agda,
                    axiom_profile: AxiomProfile::NONE,
                    is_axiom: true,
                    source_file: None,
                    module_name: None,
                },
                DttDeclaration {
                    name: "def1".to_owned(),
                    type_expr: DttExpr::sort0(),
                    value_expr: Some(DttExpr::var("Unit")),
                    system: DttSystem::Agda,
                    axiom_profile: AxiomProfile::NONE,
                    is_axiom: false,
                    source_file: None,
                    module_name: None,
                },
            ],
            imports: vec!["Agda.Builtin.Nat".to_owned()],
            system: DttSystem::Agda,
        };
        assert_eq!(module.decl_count(), 2);
        assert_eq!(module.axiom_count(), 1);
    }

    #[test]
    fn test_dtt_import_stats_total() {
        let stats = DttImportStats {
            agda_count: 100,
            idris2_count: 50,
            fstar_count: 75,
            cubical_axiomatized: 10,
            qtt_axiomatized: 5,
            effect_axiomatized: 8,
            parse_errors: 3,
        };
        assert_eq!(stats.total(), 225);
        assert_eq!(stats.total_axiomatized(), 23);
    }

    #[test]
    fn test_dtt_import_stats_merge() {
        let mut a = DttImportStats {
            agda_count: 10,
            idris2_count: 5,
            ..Default::default()
        };
        let b = DttImportStats {
            agda_count: 20,
            fstar_count: 15,
            cubical_axiomatized: 3,
            ..Default::default()
        };
        a.merge(&b);
        assert_eq!(a.agda_count, 30);
        assert_eq!(a.idris2_count, 5);
        assert_eq!(a.fstar_count, 15);
        assert_eq!(a.cubical_axiomatized, 3);
    }

    #[test]
    fn test_dtt_expr_constructors() {
        let v = DttExpr::var("Nat");
        assert_eq!(v, DttExpr::Var("Nat".to_owned()));

        let s = DttExpr::sort0();
        assert_eq!(s, DttExpr::Sort(0));

        let o = DttExpr::opaque("complex expr");
        assert_eq!(o, DttExpr::Opaque("complex expr".to_owned()));
    }

    #[test]
    fn test_idris_totality_variants() {
        assert_ne!(IdrisTotality::Total, IdrisTotality::Partial);
        assert_ne!(IdrisTotality::Covering, IdrisTotality::Total);
    }

    #[test]
    fn test_dtt_declaration_serde_round_trip() {
        let decl = DttDeclaration {
            name: "test.decl".to_owned(),
            type_expr: DttExpr::Pi {
                binder_name: "x".to_owned(),
                domain: Box::new(DttExpr::var("Nat")),
                codomain: Box::new(DttExpr::var("Nat")),
            },
            value_expr: Some(DttExpr::Lam {
                binder_name: "x".to_owned(),
                binder_type: Box::new(DttExpr::var("Nat")),
                body: Box::new(DttExpr::var("x")),
            }),
            system: DttSystem::Agda,
            axiom_profile: AxiomProfile::NONE,
            is_axiom: false,
            source_file: Some("Test.agda".to_owned()),
            module_name: Some("Test".to_owned()),
        };
        let json = serde_json::to_string(&decl).expect("serialize");
        let restored: DttDeclaration = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(restored.name, "test.decl");
        assert_eq!(restored.system, DttSystem::Agda);
        assert!(restored.has_value());
    }
}
