// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! CIC declaration extraction from SerAPI s-expression dumps.
//!
//! Takes the parsed [`SexpValue`] tree from [`super::sexp_parser`] and
//! extracts [`CicDeclaration`] records representing Coq global declarations
//! (definitions, theorems, inductives, records, instances). Detects
//! MathComp-specific patterns (canonical structures, packed classes) and
//! Flocq-specific patterns (floating-point formalization) and marks them
//! with axiom profile bits for trust tracking.

use crate::types::AxiomProfile;

use super::sexp_parser::SexpValue;

/// Kind of CIC global declaration.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum CicDeclKind {
    Definition,
    Theorem,
    Lemma,
    Inductive,
    CoInductive,
    Record,
    Class,
    Instance,
    Axiom,
    /// MathComp canonical structure.
    CanonicalStructure,
    /// Module or module type.
    Module,
    /// Module functor — axiomatized because clean kernel has no module system.
    ModuleFunctor,
}

/// A declaration extracted from a SerAPI s-expression dump.
#[derive(Clone, Debug)]
pub struct CicDeclaration {
    /// Fully qualified Coq name (e.g., `Coq.Init.Logic.eq`).
    pub name: String,
    /// Declaration kind.
    pub kind: CicDeclKind,
    /// Raw s-expression of the type (preserved for downstream translation).
    pub type_sexp: Option<SexpValue>,
    /// Raw s-expression of the body/proof term (None for axioms/opaque).
    pub body_sexp: Option<SexpValue>,
    /// Axiom profile bits detected from the declaration structure.
    pub axiom_profile: AxiomProfile,
    /// Source module path (e.g., `Coq.Init.Logic`).
    pub module_path: String,
}

/// Extract all CIC declarations from a top-level SerAPI s-expression.
///
/// Expects the sexp to be one of:
/// - `(VernacDefinition ...)` / `(VernacStartTheoremProof ...)`
/// - `(VernacInductive ...)`
/// - `(VernacInstance ...)`
/// - A list containing multiple such forms
///
/// Unknown forms are silently skipped.
pub fn extract_declarations(sexp: &SexpValue) -> Vec<CicDeclaration> {
    let mut out = Vec::new();
    extract_recursive(sexp, "", &mut out);
    out
}

/// Extract declarations from a stream of s-expressions.
pub fn extract_declarations_from_stream(sexps: &[SexpValue]) -> Vec<CicDeclaration> {
    let mut out = Vec::new();
    for sexp in sexps {
        extract_recursive(sexp, "", &mut out);
    }
    out
}

fn extract_recursive(sexp: &SexpValue, module_ctx: &str, out: &mut Vec<CicDeclaration>) {
    match sexp {
        SexpValue::Atom(_) => {}
        SexpValue::List(items) if items.is_empty() => {}
        SexpValue::List(items) => {
            let tag = items[0].as_atom().unwrap_or("");

            match tag {
                "Definition" | "VernacDefinition" => {
                    if let Some(decl) = parse_definition(items, module_ctx) {
                        out.push(decl);
                    }
                }
                "Theorem" | "Lemma" | "VernacStartTheoremProof" => {
                    if let Some(decl) = parse_theorem(items, tag, module_ctx) {
                        out.push(decl);
                    }
                }
                "Inductive" | "VernacInductive" => {
                    extract_inductive(items, module_ctx, out);
                }
                "CoInductive" => {
                    if let Some(decl) = parse_coinductive(items, module_ctx) {
                        out.push(decl);
                    }
                }
                "Record" => {
                    if let Some(decl) = parse_record(items, module_ctx) {
                        out.push(decl);
                    }
                }
                "Class" => {
                    if let Some(decl) = parse_class(items, module_ctx) {
                        out.push(decl);
                    }
                }
                "Instance" | "VernacInstance" => {
                    if let Some(decl) = parse_instance(items, module_ctx) {
                        out.push(decl);
                    }
                }
                "Axiom" | "Parameter" | "VernacAssumption" => {
                    if let Some(decl) = parse_axiom(items, module_ctx) {
                        out.push(decl);
                    }
                }
                "Module" | "VernacDefineModule" => {
                    parse_module(items, module_ctx, out);
                }
                "Canonical" | "VernacCanonical" => {
                    if let Some(decl) = parse_canonical(items, module_ctx) {
                        out.push(decl);
                    }
                }
                _ => {
                    // Recurse into list children that might contain declarations.
                    for child in &items[1..] {
                        extract_recursive(child, module_ctx, out);
                    }
                }
            }
        }
    }
}

// ---- Individual parsers ----------------------------------------------------

fn qualified_name(name: &str, module_ctx: &str) -> String {
    if module_ctx.is_empty() {
        name.to_owned()
    } else {
        format!("{module_ctx}.{name}")
    }
}

fn get_name(items: &[SexpValue], idx: usize) -> Option<String> {
    items.get(idx).and_then(|v| v.as_atom()).map(String::from)
}

fn parse_definition(items: &[SexpValue], module_ctx: &str) -> Option<CicDeclaration> {
    let name = get_name(items, 1)?;
    let type_sexp = items.get(2).cloned();
    let body_sexp = items.get(3).cloned();
    let profile = detect_axiom_profile_from_name(&name);

    Some(CicDeclaration {
        name: qualified_name(&name, module_ctx),
        kind: CicDeclKind::Definition,
        type_sexp,
        body_sexp,
        axiom_profile: profile,
        module_path: module_ctx.to_owned(),
    })
}

fn parse_theorem(items: &[SexpValue], tag: &str, module_ctx: &str) -> Option<CicDeclaration> {
    let name = get_name(items, 1)?;
    let type_sexp = items.get(2).cloned();
    let body_sexp = items.get(3).cloned();
    let kind = if tag == "Lemma" {
        CicDeclKind::Lemma
    } else {
        CicDeclKind::Theorem
    };
    let profile = detect_axiom_profile_from_name(&name);

    Some(CicDeclaration {
        name: qualified_name(&name, module_ctx),
        kind,
        type_sexp,
        body_sexp,
        axiom_profile: profile,
        module_path: module_ctx.to_owned(),
    })
}

fn extract_inductive(items: &[SexpValue], module_ctx: &str, out: &mut Vec<CicDeclaration>) {
    // Each sub-list after the tag is one inductive type in a mutual block.
    for item in &items[1..] {
        if let SexpValue::List(inner) = item {
            if let Some(name) = get_name(inner, 0) {
                let type_sexp = inner.get(1).cloned();
                let profile = detect_axiom_profile_from_name(&name);
                out.push(CicDeclaration {
                    name: qualified_name(&name, module_ctx),
                    kind: CicDeclKind::Inductive,
                    type_sexp,
                    body_sexp: None,
                    axiom_profile: profile,
                    module_path: module_ctx.to_owned(),
                });
            }
        } else if let Some(name) = item.as_atom() {
            // Simple (Inductive name type) form.
            let type_sexp = items.get(2).cloned();
            let profile = detect_axiom_profile_from_name(name);
            out.push(CicDeclaration {
                name: qualified_name(name, module_ctx),
                kind: CicDeclKind::Inductive,
                type_sexp,
                body_sexp: None,
                axiom_profile: profile,
                module_path: module_ctx.to_owned(),
            });
            break; // single-form: consumed
        }
    }
}

fn parse_coinductive(items: &[SexpValue], module_ctx: &str) -> Option<CicDeclaration> {
    let name = get_name(items, 1)?;
    let type_sexp = items.get(2).cloned();

    Some(CicDeclaration {
        name: qualified_name(&name, module_ctx),
        kind: CicDeclKind::CoInductive,
        type_sexp,
        body_sexp: None,
        axiom_profile: AxiomProfile::COQ_COINDUCTIVE,
        module_path: module_ctx.to_owned(),
    })
}

fn parse_record(items: &[SexpValue], module_ctx: &str) -> Option<CicDeclaration> {
    let name = get_name(items, 1)?;
    let type_sexp = items.get(2).cloned();
    let profile = detect_axiom_profile_from_name(&name);

    Some(CicDeclaration {
        name: qualified_name(&name, module_ctx),
        kind: CicDeclKind::Record,
        type_sexp,
        body_sexp: None,
        axiom_profile: profile,
        module_path: module_ctx.to_owned(),
    })
}

fn parse_class(items: &[SexpValue], module_ctx: &str) -> Option<CicDeclaration> {
    let name = get_name(items, 1)?;
    let type_sexp = items.get(2).cloned();

    Some(CicDeclaration {
        name: qualified_name(&name, module_ctx),
        kind: CicDeclKind::Class,
        type_sexp,
        body_sexp: None,
        axiom_profile: AxiomProfile::NONE,
        module_path: module_ctx.to_owned(),
    })
}

fn parse_instance(items: &[SexpValue], module_ctx: &str) -> Option<CicDeclaration> {
    let name = get_name(items, 1)?;
    let type_sexp = items.get(2).cloned();
    let body_sexp = items.get(3).cloned();

    Some(CicDeclaration {
        name: qualified_name(&name, module_ctx),
        kind: CicDeclKind::Instance,
        type_sexp,
        body_sexp,
        axiom_profile: AxiomProfile::NONE,
        module_path: module_ctx.to_owned(),
    })
}

fn parse_axiom(items: &[SexpValue], module_ctx: &str) -> Option<CicDeclaration> {
    let name = get_name(items, 1)?;
    let type_sexp = items.get(2).cloned();

    Some(CicDeclaration {
        name: qualified_name(&name, module_ctx),
        kind: CicDeclKind::Axiom,
        type_sexp,
        body_sexp: None,
        axiom_profile: AxiomProfile::AXIOMATIZED,
        module_path: module_ctx.to_owned(),
    })
}

fn parse_module(items: &[SexpValue], parent_ctx: &str, out: &mut Vec<CicDeclaration>) {
    let name = match get_name(items, 1) {
        Some(n) => n,
        None => return,
    };

    let new_ctx = qualified_name(&name, parent_ctx);

    // Check for functor parameters — if present, mark as module functor.
    let is_functor = items.iter().any(|item| item.is_tagged("ModuleParams"));

    if is_functor {
        out.push(CicDeclaration {
            name: new_ctx.clone(),
            kind: CicDeclKind::ModuleFunctor,
            type_sexp: None,
            body_sexp: None,
            axiom_profile: AxiomProfile::COQ_MODULE_FUNCTOR,
            module_path: parent_ctx.to_owned(),
        });
    } else {
        out.push(CicDeclaration {
            name: new_ctx.clone(),
            kind: CicDeclKind::Module,
            type_sexp: None,
            body_sexp: None,
            axiom_profile: AxiomProfile::NONE,
            module_path: parent_ctx.to_owned(),
        });
    }

    // Recurse into module body for nested declarations.
    for item in &items[2..] {
        extract_recursive(item, &new_ctx, out);
    }
}

fn parse_canonical(items: &[SexpValue], module_ctx: &str) -> Option<CicDeclaration> {
    let name = get_name(items, 1)?;
    let body_sexp = items.get(2).cloned();

    Some(CicDeclaration {
        name: qualified_name(&name, module_ctx),
        kind: CicDeclKind::CanonicalStructure,
        type_sexp: None,
        body_sexp,
        axiom_profile: AxiomProfile::NONE,
        module_path: module_ctx.to_owned(),
    })
}

// ---- Profile detection -----------------------------------------------------

/// Detect axiom profile bits from the fully qualified name.
///
/// Heuristic: if the name lives under known Flocq or MathComp namespaces,
/// attach the corresponding profile bits so trust tracking is accurate.
fn detect_axiom_profile_from_name(name: &str) -> AxiomProfile {
    let mut bits = AxiomProfile::NONE;

    // Flocq floating-point library: uses IEEE 754 axiomatization
    if name.starts_with("Flocq.")
        || name.starts_with("Flocq_")
        || name.contains("IEEE754")
        || name.contains("Float_prop")
    {
        bits = bits.union(AxiomProfile::FLOAT_APPROX);
    }

    // MathComp classical reasoning
    if name.starts_with("mathcomp.") || name.starts_with("MC.") {
        bits = bits.union(AxiomProfile::CLASSICAL);
    }

    // CompCert memory model axioms
    if name.starts_with("compcert.") || name.starts_with("CompCert.") {
        bits = bits.union(AxiomProfile::AXIOMATIZED);
    }

    // SProp usage (Coq 8.10+)
    if name.contains("SProp") || name.contains("sprop") {
        bits = bits.union(AxiomProfile::COQ_SPROP);
    }

    bits
}

#[cfg(test)]
#[path = "cic_extract_tests.rs"]
mod tests;
