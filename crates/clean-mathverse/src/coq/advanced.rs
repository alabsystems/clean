// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Advanced Coq features: coinductive types, SProp, primitive projections,
//! notations/abbreviations, and primitive types (Int63, Float64, PArray).

#[cfg(test)]
use crate::coq::alpha::parse_sexp;
use crate::coq::alpha::{cic_to_flat_expr, sexp_to_cic, CicSort, CicTerm, Sexp};
use crate::error::{MathverseError, MathverseResult};
use crate::shard::ShardWriter;
use crate::types::{
    AxiomProfile, ContentDomain, DeclKind, ImportConfidence, MathverseConstantHeader, SourceSystem,
    NO_VALUE,
};

use clean_kernel::flat::FlatExpr;

// ---------------------------------------------------------------------------
// Coinductive types
// ---------------------------------------------------------------------------

/// A Coq coinductive type definition (similar to inductive but with corecursive constructors).
#[derive(Clone, Debug)]
pub struct CoqCoinductive {
    pub name: String,
    pub params: Vec<(String, CicTerm)>,
    pub type_: CicTerm,
    pub constructors: Vec<(String, CicTerm)>,
}

/// Parse a coinductive type from `(CoInductive name (Params ...) type (Ctor ...)...)`.
pub fn parse_coinductive(sexp: &Sexp) -> Result<CoqCoinductive, MathverseError> {
    let items = match sexp {
        Sexp::List(v) if !v.is_empty() => v,
        _ => return Err(coq_adv_err("expected list for CoInductive")),
    };
    match &items[0] {
        Sexp::Atom(s) if s == "CoInductive" => {}
        _ => return Err(coq_adv_err("expected CoInductive head")),
    }
    if items.len() < 3 {
        return Err(coq_adv_err("CoInductive needs at least name and type"));
    }
    let name = match &items[1] {
        Sexp::Atom(s) => s.clone(),
        _ => return Err(coq_adv_err("expected atom name for CoInductive")),
    };

    let mut params = Vec::new();
    let mut type_sexp_idx = 2;

    // Optional (Params ...) block
    if let Some(Sexp::List(pv)) = items.get(2) {
        if !pv.is_empty() {
            if let Sexp::Atom(tag) = &pv[0] {
                if tag == "Params" {
                    for p in &pv[1..] {
                        if let Sexp::List(pair) = p {
                            if pair.len() >= 2 {
                                let pname = match &pair[0] {
                                    Sexp::Atom(s) => s.clone(),
                                    _ => continue,
                                };
                                params.push((pname, sexp_to_cic(&pair[1])?));
                            }
                        }
                    }
                    type_sexp_idx = 3;
                }
            }
        }
    }

    if type_sexp_idx >= items.len() {
        return Err(coq_adv_err("CoInductive missing type"));
    }
    let type_ = sexp_to_cic(&items[type_sexp_idx])?;

    let mut constructors = Vec::new();
    for item in &items[type_sexp_idx + 1..] {
        if let Sexp::List(cv) = item {
            if cv.len() >= 3 {
                if let Sexp::Atom(tag) = &cv[0] {
                    if tag == "Ctor" {
                        let cname = match &cv[1] {
                            Sexp::Atom(s) => s.clone(),
                            _ => continue,
                        };
                        constructors.push((cname, sexp_to_cic(&cv[2])?));
                    }
                }
            }
        }
    }

    Ok(CoqCoinductive {
        name,
        params,
        type_,
        constructors,
    })
}

/// Import a coinductive type. Gets BRIDGE_AXIOM since coinductive types require
/// axiomatized encoding in the Lean 5 kernel.
pub fn import_coinductive(
    coind: &CoqCoinductive,
    module_path: &str,
    writer: &mut ShardWriter,
) -> MathverseResult<Vec<u32>> {
    let _ = module_path; // reserved for future module-level classification
    let profile = AxiomProfile::BRIDGE_AXIOM | AxiomProfile::AXIOMATIZED;
    let mut indices = Vec::new();

    // Import the coinductive type itself
    let type_idx = cic_to_flat_expr(&coind.type_, writer);
    let name_idx = writer.add_string(&coind.name);
    indices.push(writer.add_constant(MathverseConstantHeader {
        name_idx,
        type_idx,
        value_idx: NO_VALUE,
        source_system: SourceSystem::Coq as u8,
        import_confidence: ImportConfidence::Axiomatized as u8,
        content_domain: ContentDomain::PureMath as u8,
        decl_kind: DeclKind::Inductive as u8,
        axiom_profile: profile,
        sidecar_digest: 0,
        provenance_idx: 0,
        level_params_start: 0,
        level_params_count: 0,
        _pad2: [0u8; 26],
    }));

    // Import each constructor
    for (ctor_name, ctor_ty) in &coind.constructors {
        let mangled = format!("{}.{}", coind.name, ctor_name);
        let ctor_type_idx = cic_to_flat_expr(ctor_ty, writer);
        let ctor_name_idx = writer.add_string(&mangled);
        indices.push(writer.add_constant(MathverseConstantHeader {
            name_idx: ctor_name_idx,
            type_idx: ctor_type_idx,
            value_idx: NO_VALUE,
            source_system: SourceSystem::Coq as u8,
            import_confidence: ImportConfidence::Axiomatized as u8,
            content_domain: ContentDomain::PureMath as u8,
            decl_kind: DeclKind::Constructor as u8,
            axiom_profile: profile,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        }));
    }

    Ok(indices)
}

// ---------------------------------------------------------------------------
// SProp (strict propositions)
// ---------------------------------------------------------------------------

/// SProp handling for Coq constants.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CoqSortRelevance {
    /// Normal types.
    Relevant,
    /// Strict propositions (proof irrelevance). Coq 8.10+.
    SProp,
    /// Prop (standard).
    Irrelevant,
}

/// Axiom bit for COQ_SPROP: the dedicated `AxiomProfile::COQ_SPROP` bit
/// (`1 << 17`, types.rs). Historically this constant was `1 << 10`, which
/// COLLIDED with `UNIVERSE_INCON` and conflated SProp usage with
/// universe-inconsistency gating; it now aliases the canonical bit.
pub const COQ_SPROP_BIT: u64 = AxiomProfile::COQ_SPROP.0;

/// Check if a CIC term uses SProp.
pub fn uses_sprop(term: &CicTerm) -> bool {
    match term {
        CicTerm::Sort(CicSort::Prop) => false,
        CicTerm::Sort(CicSort::Set) => false,
        CicTerm::Sort(CicSort::Type(_)) => false,
        CicTerm::Var(name) if name == "SProp" => true,
        CicTerm::Prod(_, ty, body) | CicTerm::Lambda(_, ty, body) => {
            uses_sprop(ty) || uses_sprop(body)
        }
        CicTerm::LetIn(_, val, ty, body) => uses_sprop(val) || uses_sprop(ty) || uses_sprop(body),
        CicTerm::App(f, args) => uses_sprop(f) || args.iter().any(uses_sprop),
        CicTerm::Case(case) => {
            uses_sprop(&case.discriminant)
                || uses_sprop(&case.motive)
                || case.params.iter().any(uses_sprop)
                || case.branches.iter().any(uses_sprop)
        }
        CicTerm::Fix(bodies, _) | CicTerm::CoFix(bodies, _) => bodies
            .iter()
            .any(|(_, ty, body)| uses_sprop(ty) || uses_sprop(body)),
        CicTerm::Proj(_, _, inner) => uses_sprop(inner),
        _ => false,
    }
}

/// When importing SProp constants, set the COQ_SPROP axiom bit.
/// SProp constants are axiomatized because Lean 5 doesn't have SProp natively.
pub fn sprop_axiom_profile() -> AxiomProfile {
    AxiomProfile::BRIDGE_AXIOM | AxiomProfile::COQ_SPROP
}

// ---------------------------------------------------------------------------
// Primitive projections
// ---------------------------------------------------------------------------

/// A primitive projection from a record type (Coq 8.5+).
#[derive(Clone, Debug)]
pub struct CoqPrimitiveProjection {
    pub record_name: String,
    pub field_name: String,
    pub field_index: u32,
    pub is_compatibility: bool,
}

/// Parse a primitive projection from `(PrimProj record field index [compat])`.
pub fn parse_primitive_projection(sexp: &Sexp) -> Result<CoqPrimitiveProjection, MathverseError> {
    let items = match sexp {
        Sexp::List(v) if !v.is_empty() => v,
        _ => return Err(coq_adv_err("expected list for PrimProj")),
    };
    match &items[0] {
        Sexp::Atom(s) if s == "PrimProj" => {}
        _ => return Err(coq_adv_err("expected PrimProj head")),
    }
    if items.len() < 4 {
        return Err(coq_adv_err("PrimProj needs record, field, and index"));
    }
    let record_name = match &items[1] {
        Sexp::Atom(s) => s.clone(),
        _ => return Err(coq_adv_err("expected atom record name")),
    };
    let field_name = match &items[2] {
        Sexp::Atom(s) => s.clone(),
        _ => return Err(coq_adv_err("expected atom field name")),
    };
    let field_index = match &items[3] {
        Sexp::Atom(s) => s
            .parse::<u32>()
            .map_err(|_| coq_adv_err("expected u32 field index"))?,
        _ => return Err(coq_adv_err("expected atom field index")),
    };
    let is_compatibility = items.get(4).is_some_and(|s| match s {
        Sexp::Atom(a) => a == "compat",
        _ => false,
    });
    Ok(CoqPrimitiveProjection {
        record_name,
        field_name,
        field_index,
        is_compatibility,
    })
}

/// Lower a primitive projection to `FlatExpr::proj`.
pub fn lower_primitive_projection(
    proj: &CoqPrimitiveProjection,
    arg_expr: u32,
    writer: &mut ShardWriter,
) -> u32 {
    let name_idx = writer.add_string(&format!("{}.{}", proj.record_name, proj.field_name));
    let field = proj.field_index.min(u16::MAX as u32) as u16;
    writer.add_expr(FlatExpr::proj(name_idx, field, arg_expr))
}

// ---------------------------------------------------------------------------
// Notation and abbreviation handling
// ---------------------------------------------------------------------------

/// Associativity for Coq notations.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Associativity {
    Left,
    Right,
    None,
}

/// Coq notation definition (for documentation, not for import).
/// Notations are purely syntactic and should be expanded before import.
#[derive(Clone, Debug)]
pub struct CoqNotation {
    pub syntax: String,
    pub interpretation: String,
    pub level: u32,
    pub associativity: Associativity,
}

/// Coq abbreviation (Notation that introduces a name).
#[derive(Clone, Debug)]
pub struct CoqAbbreviation {
    pub name: String,
    pub expansion: CicTerm,
    pub params: Vec<String>,
}

/// Parse notation from `(Notation syntax interp level assoc)`.
pub fn parse_notation(sexp: &Sexp) -> Result<CoqNotation, MathverseError> {
    let items = match sexp {
        Sexp::List(v) if !v.is_empty() => v,
        _ => return Err(coq_adv_err("expected list for Notation")),
    };
    match &items[0] {
        Sexp::Atom(s) if s == "Notation" => {}
        _ => return Err(coq_adv_err("expected Notation head")),
    }
    if items.len() < 5 {
        return Err(coq_adv_err("Notation needs syntax, interp, level, assoc"));
    }
    let syntax = match &items[1] {
        Sexp::Atom(s) => s.clone(),
        _ => return Err(coq_adv_err("expected atom syntax")),
    };
    let interpretation = match &items[2] {
        Sexp::Atom(s) => s.clone(),
        _ => return Err(coq_adv_err("expected atom interpretation")),
    };
    let level = match &items[3] {
        Sexp::Atom(s) => s
            .parse::<u32>()
            .map_err(|_| coq_adv_err("expected u32 level"))?,
        _ => return Err(coq_adv_err("expected atom level")),
    };
    let associativity = match &items[4] {
        Sexp::Atom(s) => match s.as_str() {
            "left" => Associativity::Left,
            "right" => Associativity::Right,
            _ => Associativity::None,
        },
        _ => Associativity::None,
    };
    Ok(CoqNotation {
        syntax,
        interpretation,
        level,
        associativity,
    })
}

/// Parse abbreviation from `(Abbreviation name (Params p1 p2 ...) expansion)`.
pub fn parse_abbreviation(sexp: &Sexp) -> Result<CoqAbbreviation, MathverseError> {
    let items = match sexp {
        Sexp::List(v) if !v.is_empty() => v,
        _ => return Err(coq_adv_err("expected list for Abbreviation")),
    };
    match &items[0] {
        Sexp::Atom(s) if s == "Abbreviation" => {}
        _ => return Err(coq_adv_err("expected Abbreviation head")),
    }
    if items.len() < 3 {
        return Err(coq_adv_err("Abbreviation needs name and expansion"));
    }
    let name = match &items[1] {
        Sexp::Atom(s) => s.clone(),
        _ => return Err(coq_adv_err("expected atom name for Abbreviation")),
    };

    let mut params = Vec::new();
    let mut expansion_idx = 2;

    // Optional (Params ...) block
    if let Some(Sexp::List(pv)) = items.get(2) {
        if !pv.is_empty() {
            if let Sexp::Atom(tag) = &pv[0] {
                if tag == "Params" {
                    for p in &pv[1..] {
                        if let Sexp::Atom(s) = p {
                            params.push(s.clone());
                        }
                    }
                    expansion_idx = 3;
                }
            }
        }
    }

    if expansion_idx >= items.len() {
        return Err(coq_adv_err("Abbreviation missing expansion"));
    }
    let expansion = sexp_to_cic(&items[expansion_idx])?;
    Ok(CoqAbbreviation {
        name,
        expansion,
        params,
    })
}

// ---------------------------------------------------------------------------
// Primitive types (Coq 8.13+)
// ---------------------------------------------------------------------------

/// Coq primitive type mapping.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CoqPrimitive {
    Int63,
    Float64,
    PArray,
}

/// Map Coq primitive types to Lean 5 equivalents.
pub fn map_primitive(prim: CoqPrimitive) -> &'static str {
    match prim {
        CoqPrimitive::Int63 => "UInt64",
        CoqPrimitive::Float64 => "Float",
        CoqPrimitive::PArray => "Array",
    }
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn coq_adv_err(reason: &str) -> MathverseError {
    MathverseError::ImportFailed {
        system: "Coq/advanced".into(),
        reason: reason.into(),
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    // -- Coinductive parsing --

    #[test]
    fn test_parse_coinductive_basic() {
        let input = r#"(CoInductive Stream (Sort (Type 0))
            (Ctor SCons (Prod x (Sort (Type 0)) (Sort (Type 0)))))"#;
        let coind = parse_coinductive(&parse_sexp(input).unwrap()).unwrap();
        assert_eq!(coind.name, "Stream");
        assert!(coind.params.is_empty());
        assert_eq!(coind.constructors.len(), 1);
        assert_eq!(coind.constructors[0].0, "SCons");
    }

    #[test]
    fn test_parse_coinductive_with_params() {
        let input = r#"(CoInductive CoList
            (Params (A (Sort (Type 0))))
            (Sort (Type 0))
            (Ctor CoNil (Sort (Type 0)))
            (Ctor CoCons (Prod x (Rel 0) (Sort (Type 0)))))"#;
        let coind = parse_coinductive(&parse_sexp(input).unwrap()).unwrap();
        assert_eq!(coind.name, "CoList");
        assert_eq!(coind.params.len(), 1);
        assert_eq!(coind.params[0].0, "A");
        assert_eq!(coind.constructors.len(), 2);
        assert_eq!(coind.constructors[0].0, "CoNil");
        assert_eq!(coind.constructors[1].0, "CoCons");
    }

    #[test]
    fn test_parse_coinductive_errors() {
        // Not a list
        assert!(parse_coinductive(&Sexp::Atom("bad".into())).is_err());
        // Wrong head
        assert!(parse_coinductive(&parse_sexp("(Inductive Stream (Sort Prop))").unwrap()).is_err());
        // Too short
        assert!(parse_coinductive(&parse_sexp("(CoInductive Stream)").unwrap()).is_err());
    }

    #[test]
    fn test_import_coinductive() {
        let input = r#"(CoInductive Stream (Sort (Type 0))
            (Ctor hd (Sort (Type 0)))
            (Ctor tl (Sort (Type 0))))"#;
        let coind = parse_coinductive(&parse_sexp(input).unwrap()).unwrap();
        let mut w = ShardWriter::new();
        let indices = import_coinductive(&coind, "Coq.Init", &mut w).unwrap();
        // 1 type + 2 constructors
        assert_eq!(indices.len(), 3);

        let mut buf = Vec::new();
        w.write(&mut buf).unwrap();
        let reader = crate::shard::ShardReader::from_bytes(&buf).unwrap();
        assert_eq!(reader.header.constant_count, 3);

        let names: Vec<&str> = reader
            .constants
            .iter()
            .map(|c| reader.strings[c.name_idx as usize].as_str())
            .collect();
        assert_eq!(names, vec!["Stream", "Stream.hd", "Stream.tl"]);

        // All should be axiomatized with BRIDGE_AXIOM
        for c in &reader.constants {
            let p = c.profile();
            assert!(p.has(AxiomProfile::BRIDGE_AXIOM));
            assert!(p.has(AxiomProfile::AXIOMATIZED));
            assert!(!c.has_value());
        }
    }

    // -- SProp detection --

    #[test]
    fn test_uses_sprop_false_for_normal_terms() {
        assert!(!uses_sprop(&CicTerm::Sort(CicSort::Prop)));
        assert!(!uses_sprop(&CicTerm::Sort(CicSort::Set)));
        assert!(!uses_sprop(&CicTerm::Sort(CicSort::type_at(0))));
        assert!(!uses_sprop(&CicTerm::Rel(0)));
        assert!(!uses_sprop(&CicTerm::Const("Nat.add".into())));
        assert!(!uses_sprop(&CicTerm::Int(42)));
    }

    #[test]
    fn test_uses_sprop_true_for_sprop_var() {
        assert!(uses_sprop(&CicTerm::Var("SProp".into())));
    }

    #[test]
    fn test_uses_sprop_nested() {
        // SProp nested in Prod
        let term = CicTerm::Prod(
            "x".into(),
            Box::new(CicTerm::Var("SProp".into())),
            Box::new(CicTerm::Rel(0)),
        );
        assert!(uses_sprop(&term));

        // SProp nested in Lambda body
        let term = CicTerm::Lambda(
            "x".into(),
            Box::new(CicTerm::Sort(CicSort::Prop)),
            Box::new(CicTerm::Var("SProp".into())),
        );
        assert!(uses_sprop(&term));

        // SProp nested in App args
        let term = CicTerm::App(
            Box::new(CicTerm::Const("f".into())),
            vec![CicTerm::Var("SProp".into())],
        );
        assert!(uses_sprop(&term));

        // SProp in LetIn
        let term = CicTerm::LetIn(
            "x".into(),
            Box::new(CicTerm::Var("SProp".into())),
            Box::new(CicTerm::Sort(CicSort::Prop)),
            Box::new(CicTerm::Rel(0)),
        );
        assert!(uses_sprop(&term));
    }

    #[test]
    fn test_sprop_axiom_profile() {
        let p = sprop_axiom_profile();
        assert!(p.has(AxiomProfile::BRIDGE_AXIOM));
        assert!(p.has_bit(COQ_SPROP_BIT));
    }

    // -- Primitive projection parsing --

    #[test]
    fn test_parse_primitive_projection() {
        let input = "(PrimProj Sigma fst 0)";
        let proj = parse_primitive_projection(&parse_sexp(input).unwrap()).unwrap();
        assert_eq!(proj.record_name, "Sigma");
        assert_eq!(proj.field_name, "fst");
        assert_eq!(proj.field_index, 0);
        assert!(!proj.is_compatibility);
    }

    #[test]
    fn test_parse_primitive_projection_with_compat() {
        let input = "(PrimProj Sigma snd 1 compat)";
        let proj = parse_primitive_projection(&parse_sexp(input).unwrap()).unwrap();
        assert_eq!(proj.record_name, "Sigma");
        assert_eq!(proj.field_name, "snd");
        assert_eq!(proj.field_index, 1);
        assert!(proj.is_compatibility);
    }

    #[test]
    fn test_parse_primitive_projection_errors() {
        assert!(parse_primitive_projection(&Sexp::Atom("bad".into())).is_err());
        assert!(parse_primitive_projection(&parse_sexp("(NotPrimProj x y 0)").unwrap()).is_err());
        assert!(parse_primitive_projection(&parse_sexp("(PrimProj x y)").unwrap()).is_err());
    }

    #[test]
    fn test_lower_primitive_projection() {
        let proj = CoqPrimitiveProjection {
            record_name: "Sigma".into(),
            field_name: "fst".into(),
            field_index: 0,
            is_compatibility: false,
        };
        let mut w = ShardWriter::new();
        // First add a dummy expression for the record value
        let arg = w.add_expr(FlatExpr::bvar(0));
        let result = lower_primitive_projection(&proj, arg, &mut w);
        assert!(result > arg);
    }

    // -- Notation parsing --

    #[test]
    fn test_parse_notation() {
        let input = r#"(Notation "_ + _" Nat.add 50 left)"#;
        let nota = parse_notation(&parse_sexp(input).unwrap()).unwrap();
        assert_eq!(nota.syntax, "_ + _");
        assert_eq!(nota.interpretation, "Nat.add");
        assert_eq!(nota.level, 50);
        assert_eq!(nota.associativity, Associativity::Left);
    }

    #[test]
    fn test_parse_notation_right_assoc() {
        let input = r#"(Notation "_ :: _" List.cons 60 right)"#;
        let nota = parse_notation(&parse_sexp(input).unwrap()).unwrap();
        assert_eq!(nota.associativity, Associativity::Right);
    }

    #[test]
    fn test_parse_notation_none_assoc() {
        let input = r#"(Notation "_ = _" eq 70 none)"#;
        let nota = parse_notation(&parse_sexp(input).unwrap()).unwrap();
        assert_eq!(nota.associativity, Associativity::None);
    }

    #[test]
    fn test_parse_notation_errors() {
        assert!(parse_notation(&Sexp::Atom("bad".into())).is_err());
        assert!(parse_notation(&parse_sexp("(NotNotation x y 0 left)").unwrap()).is_err());
        assert!(parse_notation(&parse_sexp("(Notation x)").unwrap()).is_err());
    }

    // -- Abbreviation parsing --

    #[test]
    fn test_parse_abbreviation_simple() {
        let input = "(Abbreviation not (Prod p (Sort Prop) (Sort Prop)))";
        let abbrev = parse_abbreviation(&parse_sexp(input).unwrap()).unwrap();
        assert_eq!(abbrev.name, "not");
        assert!(abbrev.params.is_empty());
        assert!(matches!(abbrev.expansion, CicTerm::Prod(..)));
    }

    #[test]
    fn test_parse_abbreviation_with_params() {
        let input = "(Abbreviation iff (Params A B) (Prod x (Rel 0) (Rel 1)))";
        let abbrev = parse_abbreviation(&parse_sexp(input).unwrap()).unwrap();
        assert_eq!(abbrev.name, "iff");
        assert_eq!(abbrev.params, vec!["A", "B"]);
        assert!(matches!(abbrev.expansion, CicTerm::Prod(..)));
    }

    #[test]
    fn test_parse_abbreviation_errors() {
        assert!(parse_abbreviation(&Sexp::Atom("bad".into())).is_err());
        assert!(
            parse_abbreviation(&parse_sexp("(NotAbbreviation x (Sort Prop))").unwrap()).is_err()
        );
        assert!(parse_abbreviation(&parse_sexp("(Abbreviation x)").unwrap()).is_err());
    }

    // -- Primitive type mapping --

    #[test]
    fn test_map_primitive_types() {
        assert_eq!(map_primitive(CoqPrimitive::Int63), "UInt64");
        assert_eq!(map_primitive(CoqPrimitive::Float64), "Float");
        assert_eq!(map_primitive(CoqPrimitive::PArray), "Array");
    }

    // -- Coinductive axiom bits --

    #[test]
    fn test_coinductive_axiom_bits() {
        let input = r#"(CoInductive Stream (Sort (Type 0))
            (Ctor hd (Sort (Type 0))))"#;
        let coind = parse_coinductive(&parse_sexp(input).unwrap()).unwrap();
        let mut w = ShardWriter::new();
        import_coinductive(&coind, "Coq.Coinductive", &mut w).unwrap();

        let mut buf = Vec::new();
        w.write(&mut buf).unwrap();
        let reader = crate::shard::ShardReader::from_bytes(&buf).unwrap();
        for c in &reader.constants {
            let p = c.profile();
            assert!(p.has(AxiomProfile::BRIDGE_AXIOM), "must have BRIDGE_AXIOM");
            assert!(p.has(AxiomProfile::AXIOMATIZED), "must have AXIOMATIZED");
            assert!(p.is_trust_gated(), "coinductives are trust-gated");
        }
    }

    // -- SProp axiom bits --

    #[test]
    fn test_sprop_axiom_bits() {
        let p = sprop_axiom_profile();
        assert!(p.has(AxiomProfile::BRIDGE_AXIOM));
        assert!(p.has_bit(COQ_SPROP_BIT));
        // Verify the raw bit value
        assert_eq!(p.0, AxiomProfile::BRIDGE_AXIOM.0 | COQ_SPROP_BIT);
        // The bit is the canonical types.rs COQ_SPROP bit and must NOT
        // collide with UNIVERSE_INCON (the historical 1<<10 collision).
        assert_eq!(COQ_SPROP_BIT, AxiomProfile::COQ_SPROP.0);
        assert!(p.has(AxiomProfile::COQ_SPROP));
        assert!(!p.has(AxiomProfile::UNIVERSE_INCON));
    }
}
