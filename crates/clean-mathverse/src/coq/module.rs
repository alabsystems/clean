// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Coq module and section handling for the Mathverse Library.
//!
//! Handles Coq's module system (modules, module types, functors, sections)
//! and provides the pipeline for flattening module trees into qualified
//! constants that can be imported into `.mathverse` shards.

#[cfg(test)]
use crate::coq::alpha::parse_sexp;
use crate::coq::alpha::{
    cic_to_flat_expr, classify_coq_module, sexp_to_cic, CicTerm, CoqMutualInductive, Sexp,
};
use crate::error::{MathverseError, MathverseResult};
use crate::shard::ShardWriter;
use crate::types::{
    ContentDomain, DeclKind, ImportConfidence, MathverseConstantHeader, SourceSystem, NO_VALUE,
};

/// A Coq module (or module type).
#[derive(Clone, Debug)]
pub struct CoqModule {
    pub name: String,
    pub kind: ModuleKind,
    pub params: Vec<(String, CoqModuleType)>,
    pub body: CoqModuleBody,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ModuleKind {
    Module,
    ModuleType,
}

#[derive(Clone, Debug)]
pub enum CoqModuleBody {
    /// Concrete module with definitions.
    Struct(Vec<CoqModuleItem>),
    /// Functor application.
    FunctorApp { functor: String, args: Vec<String> },
    /// Module alias.
    Alias(String),
}

#[derive(Clone, Debug)]
pub enum CoqModuleType {
    /// Named module type reference.
    Named(String),
    /// Inline module type signature.
    Sig(Vec<CoqModuleItem>),
}

/// Items that can appear inside a module.
#[derive(Clone, Debug)]
pub enum CoqModuleItem {
    Definition {
        name: String,
        type_: CicTerm,
        body: Option<CicTerm>,
    },
    Axiom {
        name: String,
        type_: CicTerm,
    },
    Inductive(CoqMutualInductive),
    SubModule(CoqModule),
    Include(String),
    Export(String),
}

/// A Coq section with its local variables.
#[derive(Clone, Debug)]
pub struct CoqSection {
    pub name: String,
    pub variables: Vec<SectionVariable>,
    pub items: Vec<CoqModuleItem>,
}

#[derive(Clone, Debug)]
pub struct SectionVariable {
    pub name: String,
    pub kind: SectionVarKind,
    pub type_: CicTerm,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SectionVarKind {
    Variable,
    Hypothesis,
    Context,
    Let,
}

/// When a section closes, abstract the section variables over all definitions.
///
/// For each item in the section, wraps its type in `Prod` (forall) bindings
/// for each `Variable`/`Hypothesis`/`Context` variable, and wraps its body
/// in `Lambda` bindings. `Let` variables are wrapped with `LetIn`.
/// The result is a list of globally valid definitions.
pub fn close_section(section: &CoqSection) -> Vec<CoqModuleItem> {
    section
        .items
        .iter()
        .map(|item| abstract_item_over_vars(&section.variables, item))
        .collect()
}

fn abstract_item_over_vars(vars: &[SectionVariable], item: &CoqModuleItem) -> CoqModuleItem {
    match item {
        CoqModuleItem::Definition { name, type_, body } => {
            let abs_type = abstract_type_over_vars(vars, type_.clone());
            let abs_body = body
                .as_ref()
                .map(|b| abstract_body_over_vars(vars, b.clone()));
            CoqModuleItem::Definition {
                name: name.clone(),
                type_: abs_type,
                body: abs_body,
            }
        }
        CoqModuleItem::Axiom { name, type_ } => {
            let abs_type = abstract_type_over_vars(vars, type_.clone());
            CoqModuleItem::Axiom {
                name: name.clone(),
                type_: abs_type,
            }
        }
        // Inductives, submodules, includes, exports pass through unchanged.
        other => other.clone(),
    }
}

/// Wrap `inner` in forall/Pi bindings for each section variable.
fn abstract_type_over_vars(vars: &[SectionVariable], inner: CicTerm) -> CicTerm {
    vars.iter().rev().fold(inner, |acc, v| match v.kind {
        SectionVarKind::Let => CicTerm::LetIn(
            v.name.clone(),
            Box::new(CicTerm::Var(v.name.clone())),
            Box::new(v.type_.clone()),
            Box::new(acc),
        ),
        _ => CicTerm::Prod(v.name.clone(), Box::new(v.type_.clone()), Box::new(acc)),
    })
}

/// Wrap `inner` in lambda bindings for each section variable.
fn abstract_body_over_vars(vars: &[SectionVariable], inner: CicTerm) -> CicTerm {
    vars.iter().rev().fold(inner, |acc, v| match v.kind {
        SectionVarKind::Let => CicTerm::LetIn(
            v.name.clone(),
            Box::new(CicTerm::Var(v.name.clone())),
            Box::new(v.type_.clone()),
            Box::new(acc),
        ),
        _ => CicTerm::Lambda(v.name.clone(), Box::new(v.type_.clone()), Box::new(acc)),
    })
}

/// Qualify a name with its module path.
pub fn qualify_name(module_path: &[String], local_name: &str) -> String {
    if module_path.is_empty() {
        local_name.to_string()
    } else {
        format!("{}.{}", module_path.join("."), local_name)
    }
}

/// A flattened constant: `(qualified_name, type, optional_body, decl_kind)`.
pub type FlatConstant = (String, CicTerm, Option<CicTerm>, DeclKind);

/// Flatten a module tree into a list of qualified constants.
pub fn flatten_module(module: &CoqModule, prefix: &[String]) -> Vec<FlatConstant> {
    let mut path = prefix.to_vec();
    path.push(module.name.clone());
    flatten_body(&module.body, &path)
}

fn flatten_body(body: &CoqModuleBody, path: &[String]) -> Vec<FlatConstant> {
    match body {
        CoqModuleBody::Struct(items) => items.iter().flat_map(|i| flatten_item(i, path)).collect(),
        CoqModuleBody::FunctorApp { .. } | CoqModuleBody::Alias(_) => Vec::new(),
    }
}

fn flatten_item(item: &CoqModuleItem, path: &[String]) -> Vec<FlatConstant> {
    match item {
        CoqModuleItem::Definition { name, type_, body } => {
            // Definition with body → Definition; body-less (declared opaque) → Axiom.
            let kind = if body.is_some() {
                DeclKind::Definition
            } else {
                DeclKind::Axiom
            };
            vec![(qualify_name(path, name), type_.clone(), body.clone(), kind)]
        }
        CoqModuleItem::Axiom { name, type_ } => {
            vec![(
                qualify_name(path, name),
                type_.clone(),
                None,
                DeclKind::Axiom,
            )]
        }
        CoqModuleItem::Inductive(mind) => {
            let mut out = Vec::new();
            for body in &mind.bodies {
                out.push((
                    qualify_name(path, &body.name),
                    body.arity.clone(),
                    None,
                    DeclKind::Inductive,
                ));
                for (ctor, ty) in &body.constructors {
                    let mangled = format!("{}.{}", body.name, ctor);
                    out.push((
                        qualify_name(path, &mangled),
                        ty.clone(),
                        None,
                        DeclKind::Constructor,
                    ));
                }
            }
            out
        }
        CoqModuleItem::SubModule(sub) => flatten_module(sub, path),
        CoqModuleItem::Include(_) | CoqModuleItem::Export(_) => Vec::new(),
    }
}

/// Statistics from importing a Coq module tree.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ModuleImportStats {
    pub modules_processed: u32,
    pub definitions: u32,
    pub axioms: u32,
    pub inductives: u32,
    pub sections_closed: u32,
    pub functors_skipped: u32,
}

/// Import a Coq module tree into a shard.
pub fn import_module_tree(
    module: &CoqModule,
    module_path: &str,
    writer: &mut ShardWriter,
) -> MathverseResult<ModuleImportStats> {
    let mut stats = ModuleImportStats::default();
    count_module_stats(module, &mut stats);
    let profile = classify_coq_module(module_path);
    let flattened = flatten_module(module, &[]);
    for (qname, type_cic, body_cic, kind) in &flattened {
        let type_idx = cic_to_flat_expr(type_cic, writer);
        let (value_idx, confidence) = match body_cic {
            Some(b) => (cic_to_flat_expr(b, writer), ImportConfidence::Translated),
            None => (NO_VALUE, ImportConfidence::Axiomatized),
        };
        let name_idx = writer.add_string(qname);
        writer.add_constant(MathverseConstantHeader {
            name_idx,
            type_idx,
            value_idx,
            source_system: SourceSystem::Coq as u8,
            import_confidence: confidence as u8,
            content_domain: ContentDomain::PureMath as u8,
            decl_kind: *kind as u8,
            axiom_profile: profile,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        });
    }
    Ok(stats)
}

fn count_module_stats(module: &CoqModule, stats: &mut ModuleImportStats) {
    stats.modules_processed += 1;
    if !module.params.is_empty() {
        if let CoqModuleBody::FunctorApp { .. } = &module.body {
            stats.functors_skipped += 1;
            return;
        }
    }
    match &module.body {
        CoqModuleBody::Struct(items) => {
            for item in items {
                count_item_stats(item, stats);
            }
        }
        CoqModuleBody::FunctorApp { .. } => {
            stats.functors_skipped += 1;
        }
        CoqModuleBody::Alias(_) => {}
    }
}

fn count_item_stats(item: &CoqModuleItem, stats: &mut ModuleImportStats) {
    match item {
        CoqModuleItem::Definition { body, .. } => {
            if body.is_some() {
                stats.definitions += 1;
            } else {
                stats.axioms += 1;
            }
        }
        CoqModuleItem::Axiom { .. } => stats.axioms += 1,
        CoqModuleItem::Inductive(_) => stats.inductives += 1,
        CoqModuleItem::SubModule(sub) => count_module_stats(sub, stats),
        CoqModuleItem::Include(_) | CoqModuleItem::Export(_) => {}
    }
}

fn coq_err(reason: &str) -> MathverseError {
    MathverseError::ImportFailed {
        system: "Coq".into(),
        reason: reason.into(),
    }
}

fn get_atom(sexp: &Sexp) -> Option<&str> {
    match sexp {
        Sexp::Atom(s) => Some(s.as_str()),
        _ => None,
    }
}

fn require_list(sexp: &Sexp) -> Result<&[Sexp], MathverseError> {
    match sexp {
        Sexp::List(v) if !v.is_empty() => Ok(v),
        _ => Err(coq_err("expected non-empty list")),
    }
}

/// Parse a `CoqModule` from an s-expression.
///
/// Expected forms:
/// - `(Module name (Params ...) (Struct item ...))` — concrete module
/// - `(ModuleType name (Params ...) (Sig item ...))` — module type
/// - `(Module name (FunctorApp functor arg ...))` — functor application
/// - `(Module name (Alias target))` — module alias
pub fn parse_module(sexp: &Sexp) -> Result<CoqModule, MathverseError> {
    let items = require_list(sexp)?;
    let head = get_atom(&items[0]).ok_or_else(|| coq_err("expected Module/ModuleType head"))?;
    let kind = match head {
        "Module" => ModuleKind::Module,
        "ModuleType" => ModuleKind::ModuleType,
        other => {
            return Err(coq_err(&format!(
                "expected Module or ModuleType, got {other}"
            )))
        }
    };
    let name = get_atom(items.get(1).ok_or_else(|| coq_err("missing module name"))?)
        .ok_or_else(|| coq_err("module name must be atom"))?
        .to_string();

    let mut params = Vec::new();
    let mut body = CoqModuleBody::Struct(Vec::new());

    for child in &items[2..] {
        let ch = require_list(child)?;
        let tag = get_atom(&ch[0]).unwrap_or("");
        match tag {
            "Params" => {
                for p in &ch[1..] {
                    if let Sexp::List(pv) = p {
                        if pv.len() >= 2 {
                            let pn = get_atom(&pv[0])
                                .ok_or_else(|| coq_err("param name must be atom"))?
                                .to_string();
                            let pty = parse_module_type(&pv[1])?;
                            params.push((pn, pty));
                        }
                    }
                }
            }
            "Struct" | "Sig" => {
                let mut module_items = Vec::new();
                for it in &ch[1..] {
                    module_items.push(parse_module_item(it)?);
                }
                body = CoqModuleBody::Struct(module_items);
            }
            "FunctorApp" => {
                let functor = get_atom(ch.get(1).ok_or_else(|| coq_err("missing functor name"))?)
                    .ok_or_else(|| coq_err("functor name must be atom"))?
                    .to_string();
                let args: Vec<String> = ch[2..]
                    .iter()
                    .filter_map(|a| get_atom(a).map(String::from))
                    .collect();
                body = CoqModuleBody::FunctorApp { functor, args };
            }
            "Alias" => {
                let target = get_atom(ch.get(1).ok_or_else(|| coq_err("missing alias target"))?)
                    .ok_or_else(|| coq_err("alias target must be atom"))?
                    .to_string();
                body = CoqModuleBody::Alias(target);
            }
            _ => {}
        }
    }

    Ok(CoqModule {
        name,
        kind,
        params,
        body,
    })
}

fn parse_module_type(sexp: &Sexp) -> Result<CoqModuleType, MathverseError> {
    match sexp {
        Sexp::Atom(s) => Ok(CoqModuleType::Named(s.clone())),
        Sexp::List(items) if !items.is_empty() => {
            let tag = get_atom(&items[0]).unwrap_or("");
            if tag == "Sig" {
                let mut sig_items = Vec::new();
                for it in &items[1..] {
                    sig_items.push(parse_module_item(it)?);
                }
                Ok(CoqModuleType::Sig(sig_items))
            } else {
                Ok(CoqModuleType::Named(
                    get_atom(&items[0]).unwrap_or("?").to_string(),
                ))
            }
        }
        _ => Err(coq_err("invalid module type")),
    }
}

/// Parse a `CoqSection` from an s-expression.
///
/// Expected form: `(Section name (Variable x kind type) ... (Item ...) ...)`
pub fn parse_section(sexp: &Sexp) -> Result<CoqSection, MathverseError> {
    let items = require_list(sexp)?;
    let head = get_atom(&items[0]).ok_or_else(|| coq_err("expected Section head"))?;
    if head != "Section" {
        return Err(coq_err(&format!("expected Section, got {head}")));
    }
    let name = get_atom(
        items
            .get(1)
            .ok_or_else(|| coq_err("missing section name"))?,
    )
    .ok_or_else(|| coq_err("section name must be atom"))?
    .to_string();

    let mut variables = Vec::new();
    let mut section_items = Vec::new();

    for child in &items[2..] {
        let ch = match child {
            Sexp::List(v) if !v.is_empty() => v,
            _ => continue,
        };
        let tag = get_atom(&ch[0]).unwrap_or("");
        match tag {
            "Variable" | "Hypothesis" | "Context" | "Let" => {
                if ch.len() >= 3 {
                    let vname = get_atom(&ch[1])
                        .ok_or_else(|| coq_err("var name must be atom"))?
                        .to_string();
                    let vkind = match tag {
                        "Variable" => SectionVarKind::Variable,
                        "Hypothesis" => SectionVarKind::Hypothesis,
                        "Context" => SectionVarKind::Context,
                        "Let" => SectionVarKind::Let,
                        _ => unreachable!(),
                    };
                    let vtype = sexp_to_cic(&ch[2])?;
                    variables.push(SectionVariable {
                        name: vname,
                        kind: vkind,
                        type_: vtype,
                    });
                }
            }
            _ => {
                section_items.push(parse_module_item(child)?);
            }
        }
    }

    Ok(CoqSection {
        name,
        variables,
        items: section_items,
    })
}

/// Parse a single module item from an s-expression.
pub fn parse_module_item(sexp: &Sexp) -> Result<CoqModuleItem, MathverseError> {
    let items = require_list(sexp)?;
    let head = get_atom(&items[0]).ok_or_else(|| coq_err("expected item head"))?;
    match head {
        "Definition" => {
            let name = get_atom(items.get(1).ok_or_else(|| coq_err("missing def name"))?)
                .ok_or_else(|| coq_err("def name must be atom"))?
                .to_string();
            let type_ = sexp_to_cic(items.get(2).ok_or_else(|| coq_err("missing def type"))?)?;
            let body = items.get(3).map(sexp_to_cic).transpose()?;
            Ok(CoqModuleItem::Definition { name, type_, body })
        }
        "Axiom" => {
            let name = get_atom(items.get(1).ok_or_else(|| coq_err("missing axiom name"))?)
                .ok_or_else(|| coq_err("axiom name must be atom"))?
                .to_string();
            let type_ = sexp_to_cic(items.get(2).ok_or_else(|| coq_err("missing axiom type"))?)?;
            Ok(CoqModuleItem::Axiom { name, type_ })
        }
        "Inductive" => {
            // Re-use the existing mutual inductive parser by wrapping with MutualInductive tag
            let wrapped = Sexp::List(
                std::iter::once(Sexp::Atom("MutualInductive".into()))
                    .chain(items[1..].iter().cloned())
                    .collect(),
            );
            let mind = crate::coq::alpha::sexp_to_mutual_inductive(&wrapped)?;
            Ok(CoqModuleItem::Inductive(mind))
        }
        "Module" | "ModuleType" => {
            let sub = parse_module(sexp)?;
            Ok(CoqModuleItem::SubModule(sub))
        }
        "Include" => {
            let target = get_atom(
                items
                    .get(1)
                    .ok_or_else(|| coq_err("missing include target"))?,
            )
            .ok_or_else(|| coq_err("include target must be atom"))?
            .to_string();
            Ok(CoqModuleItem::Include(target))
        }
        "Export" => {
            let target = get_atom(
                items
                    .get(1)
                    .ok_or_else(|| coq_err("missing export target"))?,
            )
            .ok_or_else(|| coq_err("export target must be atom"))?
            .to_string();
            Ok(CoqModuleItem::Export(target))
        }
        other => Err(coq_err(&format!("unknown module item: {other}"))),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::coq::alpha::{CicSort, CicTerm};

    #[test]
    fn test_parse_module_struct() {
        let input = r#"(Module Nat (Params)
            (Struct (Definition add (Sort (Type 0)) (Rel 0))
                    (Axiom zero_ne_succ (Sort Prop))))"#;
        let m = parse_module(&parse_sexp(input).unwrap()).unwrap();
        assert_eq!(m.name, "Nat");
        assert_eq!(m.kind, ModuleKind::Module);
        assert!(m.params.is_empty());
        match &m.body {
            CoqModuleBody::Struct(items) => {
                assert_eq!(items.len(), 2);
                assert!(
                    matches!(&items[0], CoqModuleItem::Definition { name, .. } if name == "add")
                );
                assert!(
                    matches!(&items[1], CoqModuleItem::Axiom { name, .. } if name == "zero_ne_succ")
                );
            }
            _ => panic!("expected Struct body"),
        }
    }

    #[test]
    fn test_parse_module_type() {
        let input = r#"(ModuleType OrderedType (Params)
            (Struct (Axiom t (Sort (Type 0)))
                    (Axiom compare (Sort Prop))))"#;
        let m = parse_module(&parse_sexp(input).unwrap()).unwrap();
        assert_eq!(m.kind, ModuleKind::ModuleType);
        assert_eq!(m.name, "OrderedType");
    }

    #[test]
    fn test_parse_functor_app() {
        let input = r#"(Module NatMap (FunctorApp Map Nat))"#;
        let m = parse_module(&parse_sexp(input).unwrap()).unwrap();
        match &m.body {
            CoqModuleBody::FunctorApp { functor, args } => {
                assert_eq!(functor, "Map");
                assert_eq!(args, &["Nat".to_string()]);
            }
            _ => panic!("expected FunctorApp"),
        }
    }

    #[test]
    fn test_parse_alias() {
        let input = r#"(Module N (Alias Nat))"#;
        let m = parse_module(&parse_sexp(input).unwrap()).unwrap();
        assert!(matches!(&m.body, CoqModuleBody::Alias(t) if t == "Nat"));
    }

    #[test]
    fn test_parse_module_with_params() {
        let input = r#"(Module F (Params (X OrderedType)) (Struct (Axiom f (Sort Prop))))"#;
        let m = parse_module(&parse_sexp(input).unwrap()).unwrap();
        assert_eq!(m.params.len(), 1);
        assert_eq!(m.params[0].0, "X");
        assert!(matches!(&m.params[0].1, CoqModuleType::Named(n) if n == "OrderedType"));
    }

    #[test]
    fn test_parse_section() {
        let input = r#"(Section MySection
            (Variable A (Sort (Type 0)))
            (Hypothesis H (Sort Prop))
            (Definition f (Sort (Type 0)) (Rel 0)))"#;
        let s = parse_section(&parse_sexp(input).unwrap()).unwrap();
        assert_eq!(s.name, "MySection");
        assert_eq!(s.variables.len(), 2);
        assert_eq!(s.variables[0].name, "A");
        assert_eq!(s.variables[0].kind, SectionVarKind::Variable);
        assert_eq!(s.variables[1].name, "H");
        assert_eq!(s.variables[1].kind, SectionVarKind::Hypothesis);
        assert_eq!(s.items.len(), 1);
    }

    #[test]
    fn test_close_section_variable_abstraction() {
        let section = CoqSection {
            name: "S".into(),
            variables: vec![SectionVariable {
                name: "A".into(),
                kind: SectionVarKind::Variable,
                type_: CicTerm::Sort(CicSort::type_at(0)),
            }],
            items: vec![CoqModuleItem::Definition {
                name: "id".into(),
                type_: CicTerm::Rel(0),
                body: Some(CicTerm::Lambda(
                    "x".into(),
                    Box::new(CicTerm::Rel(0)),
                    Box::new(CicTerm::Rel(0)),
                )),
            }],
        };
        let closed = close_section(&section);
        assert_eq!(closed.len(), 1);
        match &closed[0] {
            CoqModuleItem::Definition { type_, body, .. } => {
                assert!(matches!(type_, CicTerm::Prod(n, _, _) if n == "A"));
                assert!(matches!(body, Some(CicTerm::Lambda(n, _, _)) if n == "A"));
            }
            _ => panic!("expected Definition"),
        }
    }

    #[test]
    fn test_close_section_hypothesis_abstraction() {
        let section = CoqSection {
            name: "S".into(),
            variables: vec![
                SectionVariable {
                    name: "A".into(),
                    kind: SectionVarKind::Variable,
                    type_: CicTerm::Sort(CicSort::type_at(0)),
                },
                SectionVariable {
                    name: "H".into(),
                    kind: SectionVarKind::Hypothesis,
                    type_: CicTerm::Sort(CicSort::Prop),
                },
            ],
            items: vec![CoqModuleItem::Axiom {
                name: "thm".into(),
                type_: CicTerm::Sort(CicSort::Prop),
            }],
        };
        let closed = close_section(&section);
        assert_eq!(closed.len(), 1);
        // Should have two Prod wrappers: forall A, forall H, Prop
        match &closed[0] {
            CoqModuleItem::Axiom { type_, .. } => match type_ {
                CicTerm::Prod(n1, _, inner) => {
                    assert_eq!(n1, "A");
                    assert!(matches!(inner.as_ref(), CicTerm::Prod(n2, _, _) if n2 == "H"));
                }
                _ => panic!("expected Prod(A, Prod(H, ...))"),
            },
            _ => panic!("expected Axiom"),
        }
    }

    #[test]
    fn test_close_section_let_binding() {
        let section = CoqSection {
            name: "S".into(),
            variables: vec![SectionVariable {
                name: "x".into(),
                kind: SectionVarKind::Let,
                type_: CicTerm::Sort(CicSort::type_at(0)),
            }],
            items: vec![CoqModuleItem::Definition {
                name: "f".into(),
                type_: CicTerm::Rel(0),
                body: Some(CicTerm::Rel(0)),
            }],
        };
        let closed = close_section(&section);
        match &closed[0] {
            CoqModuleItem::Definition { type_, body, .. } => {
                assert!(matches!(type_, CicTerm::LetIn(n, _, _, _) if n == "x"));
                assert!(matches!(body, Some(CicTerm::LetIn(n, _, _, _)) if n == "x"));
            }
            _ => panic!("expected Definition"),
        }
    }

    #[test]
    fn test_qualify_name() {
        assert_eq!(qualify_name(&[], "add"), "add");
        assert_eq!(qualify_name(&["Nat".into()], "add"), "Nat.add");
        assert_eq!(
            qualify_name(&["Coq".into(), "Init".into()], "nat"),
            "Coq.Init.nat"
        );
    }

    #[test]
    fn test_flatten_module_simple() {
        let m = CoqModule {
            name: "M".into(),
            kind: ModuleKind::Module,
            params: vec![],
            body: CoqModuleBody::Struct(vec![
                CoqModuleItem::Definition {
                    name: "x".into(),
                    type_: CicTerm::Sort(CicSort::Prop),
                    body: None,
                },
                CoqModuleItem::Axiom {
                    name: "ax".into(),
                    type_: CicTerm::Sort(CicSort::Prop),
                },
            ]),
        };
        let flat = flatten_module(&m, &[]);
        assert_eq!(flat.len(), 2);
        assert_eq!(flat[0].0, "M.x");
        assert_eq!(flat[1].0, "M.ax");
    }

    #[test]
    fn test_flatten_nested_modules() {
        let inner = CoqModule {
            name: "Inner".into(),
            kind: ModuleKind::Module,
            params: vec![],
            body: CoqModuleBody::Struct(vec![CoqModuleItem::Definition {
                name: "f".into(),
                type_: CicTerm::Sort(CicSort::Prop),
                body: Some(CicTerm::Rel(0)),
            }]),
        };
        let outer = CoqModule {
            name: "Outer".into(),
            kind: ModuleKind::Module,
            params: vec![],
            body: CoqModuleBody::Struct(vec![
                CoqModuleItem::Definition {
                    name: "g".into(),
                    type_: CicTerm::Sort(CicSort::Set),
                    body: None,
                },
                CoqModuleItem::SubModule(inner),
            ]),
        };
        let flat = flatten_module(&outer, &[]);
        assert_eq!(flat.len(), 2);
        assert_eq!(flat[0].0, "Outer.g");
        assert_eq!(flat[1].0, "Outer.Inner.f");
    }

    #[test]
    fn test_flatten_functor_skipped() {
        let m = CoqModule {
            name: "F".into(),
            kind: ModuleKind::Module,
            params: vec![("X".into(), CoqModuleType::Named("T".into()))],
            body: CoqModuleBody::FunctorApp {
                functor: "Map".into(),
                args: vec!["Nat".into()],
            },
        };
        let flat = flatten_module(&m, &[]);
        assert!(
            flat.is_empty(),
            "functor applications should produce no constants"
        );
    }

    #[test]
    fn test_import_module_tree() {
        let m = CoqModule {
            name: "Test".into(),
            kind: ModuleKind::Module,
            params: vec![],
            body: CoqModuleBody::Struct(vec![
                CoqModuleItem::Definition {
                    name: "f".into(),
                    type_: CicTerm::Sort(CicSort::type_at(0)),
                    body: Some(CicTerm::Rel(0)),
                },
                CoqModuleItem::Axiom {
                    name: "ax".into(),
                    type_: CicTerm::Sort(CicSort::Prop),
                },
            ]),
        };
        let mut w = ShardWriter::new();
        let stats = import_module_tree(&m, "Coq.Init.Test", &mut w).unwrap();
        assert_eq!(stats.modules_processed, 1);
        assert_eq!(stats.definitions, 1);
        assert_eq!(stats.axioms, 1);
        // Verify shard contents
        let mut buf = Vec::new();
        w.write(&mut buf).unwrap();
        let reader = crate::shard::ShardReader::from_bytes(&buf).unwrap();
        assert_eq!(reader.header.constant_count, 2);
        let names: Vec<&str> = reader
            .constants
            .iter()
            .map(|c| reader.strings[c.name_idx as usize].as_str())
            .collect();
        assert_eq!(names, vec!["Test.f", "Test.ax"]);
    }

    #[test]
    fn test_functor_skipped_in_stats() {
        let m = CoqModule {
            name: "Apply".into(),
            kind: ModuleKind::Module,
            params: vec![("X".into(), CoqModuleType::Named("T".into()))],
            body: CoqModuleBody::FunctorApp {
                functor: "Map".into(),
                args: vec!["Nat".into()],
            },
        };
        let mut w = ShardWriter::new();
        let stats = import_module_tree(&m, "Coq.Structures", &mut w).unwrap();
        assert_eq!(stats.functors_skipped, 1);
        assert_eq!(stats.definitions, 0);
    }

    #[test]
    fn test_include_export_handling() {
        let m = CoqModule {
            name: "M".into(),
            kind: ModuleKind::Module,
            params: vec![],
            body: CoqModuleBody::Struct(vec![
                CoqModuleItem::Include("Base".into()),
                CoqModuleItem::Export("Utils".into()),
                CoqModuleItem::Definition {
                    name: "x".into(),
                    type_: CicTerm::Sort(CicSort::Prop),
                    body: None,
                },
            ]),
        };
        let flat = flatten_module(&m, &[]);
        // Include/Export produce no constants; only the Definition does
        assert_eq!(flat.len(), 1);
        assert_eq!(flat[0].0, "M.x");
    }

    #[test]
    fn test_parse_module_item_all_kinds() {
        // Include
        let inc = parse_module_item(&parse_sexp("(Include Base)").unwrap()).unwrap();
        assert!(matches!(inc, CoqModuleItem::Include(t) if t == "Base"));

        // Export
        let exp = parse_module_item(&parse_sexp("(Export Utils)").unwrap()).unwrap();
        assert!(matches!(exp, CoqModuleItem::Export(t) if t == "Utils"));

        // Definition with body
        let def =
            parse_module_item(&parse_sexp("(Definition f (Sort Prop) (Rel 0))").unwrap()).unwrap();
        assert!(
            matches!(def, CoqModuleItem::Definition { name, body: Some(_), .. } if name == "f")
        );

        // Definition without body
        let def2 = parse_module_item(&parse_sexp("(Definition g (Sort Prop))").unwrap()).unwrap();
        assert!(matches!(def2, CoqModuleItem::Definition { name, body: None, .. } if name == "g"));

        // Axiom
        let ax = parse_module_item(&parse_sexp("(Axiom ax (Sort Prop))").unwrap()).unwrap();
        assert!(matches!(ax, CoqModuleItem::Axiom { name, .. } if name == "ax"));
    }

    #[test]
    fn test_parse_section_with_context_and_let() {
        let input = r#"(Section S
            (Context C (Sort (Type 0)))
            (Let x (Sort (Type 0)))
            (Axiom thm (Sort Prop)))"#;
        let s = parse_section(&parse_sexp(input).unwrap()).unwrap();
        assert_eq!(s.variables.len(), 2);
        assert_eq!(s.variables[0].kind, SectionVarKind::Context);
        assert_eq!(s.variables[1].kind, SectionVarKind::Let);
        assert_eq!(s.items.len(), 1);
    }

    #[test]
    fn test_close_section_preserves_inductives() {
        let section = CoqSection {
            name: "S".into(),
            variables: vec![SectionVariable {
                name: "A".into(),
                kind: SectionVarKind::Variable,
                type_: CicTerm::Sort(CicSort::type_at(0)),
            }],
            items: vec![CoqModuleItem::Inductive(CoqMutualInductive {
                params: vec![],
                bodies: vec![],
            })],
        };
        let closed = close_section(&section);
        assert_eq!(closed.len(), 1);
        assert!(matches!(&closed[0], CoqModuleItem::Inductive(_)));
    }

    #[test]
    fn test_flatten_module_with_inductive() {
        let m = CoqModule {
            name: "M".into(),
            kind: ModuleKind::Module,
            params: vec![],
            body: CoqModuleBody::Struct(vec![CoqModuleItem::Inductive(CoqMutualInductive {
                params: vec![],
                bodies: vec![crate::coq::alpha::CoqInductiveBody {
                    name: "nat".into(),
                    arity: CicTerm::Sort(CicSort::type_at(0)),
                    constructors: vec![
                        ("O".into(), CicTerm::Sort(CicSort::type_at(0))),
                        ("S".into(), CicTerm::Sort(CicSort::type_at(0))),
                    ],
                }],
            })]),
        };
        let flat = flatten_module(&m, &[]);
        assert_eq!(flat.len(), 3);
        assert_eq!(flat[0].0, "M.nat");
        assert_eq!(flat[1].0, "M.nat.O");
        assert_eq!(flat[2].0, "M.nat.S");
    }
}
