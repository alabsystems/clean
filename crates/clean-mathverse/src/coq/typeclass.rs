// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Coq type class, record, and canonical structure import.
//!
//! Coq records are single-constructor inductives. Type classes are records with
//! `is_class = true`. Canonical structures are MathComp unification hints.
//! Each record imports as: one inductive type + one `mk` ctor + N projections.

use crate::coq::alpha::{cic_to_flat_expr, classify_coq_module, sexp_to_cic, CicTerm, Sexp};
use crate::error::{MathverseError, MathverseResult};
use crate::shard::ShardWriter;
use crate::types::{
    AxiomProfile, ContentDomain, ImportConfidence, MathverseConstantHeader, SourceSystem, NO_VALUE,
};

/// Axiom profile bit marking a constant as a type class (bit 17, currently unused).
const TYPE_CLASS_BIT: u64 = 1 << 17;

// ── Data types ──────────────────────────────────────────────────────────

/// A Coq Record (syntactic sugar for an inductive with one constructor).
#[derive(Clone, Debug)]
pub struct CoqRecord {
    pub name: String,
    pub params: Vec<(String, CicTerm)>,
    pub fields: Vec<CoqField>,
    pub is_class: bool,
}

/// A single field in a Coq record.
#[derive(Clone, Debug)]
pub struct CoqField {
    pub name: String,
    pub type_: CicTerm,
    pub is_coercion: bool,
}

/// A Coq type class instance.
#[derive(Clone, Debug)]
pub struct CoqInstance {
    pub name: String,
    pub class_name: String,
    pub params: Vec<CicTerm>,
    pub body: CicTerm,
    pub priority: Option<u32>,
    pub is_global: bool,
}

/// A Coq canonical structure declaration.
#[derive(Clone, Debug)]
pub struct CoqCanonical {
    pub name: String,
    pub projection: String,
    pub value: CicTerm,
}

/// Result of importing a Coq record into a shard.
#[derive(Clone, Debug)]
pub struct RecordImportResult {
    pub type_idx: u32,
    pub ctor_idx: u32,
    pub field_indices: Vec<u32>,
}

// ── MathComp classification ─────────────────────────────────────────────

/// MathComp algebraic hierarchy structure classification.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MathCompStructure {
    Monoid,
    Group,
    Ring,
    ComRing,
    Field,
    Module,
    Algebra,
    Vector,
    Other(String),
}

/// Recognize MathComp algebraic hierarchy patterns from a fully-qualified name.
pub fn classify_mathcomp_structure(name: &str) -> Option<MathCompStructure> {
    let leaf = name.rsplit('.').next().unwrap_or(name);
    match leaf {
        "Monoid" | "MulMonoid" | "AddMonoid" => Some(MathCompStructure::Monoid),
        "Group" | "MulGroup" | "AddGroup" => Some(MathCompStructure::Group),
        "Ring" | "SemiRing" => Some(MathCompStructure::Ring),
        "ComRing" | "ComSemiRing" => Some(MathCompStructure::ComRing),
        "Field" | "NumField" | "ClosedField" => Some(MathCompStructure::Field),
        "Module" | "Lmodule" | "Rmodule" => Some(MathCompStructure::Module),
        "Algebra" | "ComAlgebra" | "UnitAlgebra" => Some(MathCompStructure::Algebra),
        "Vector" | "Vspace" => Some(MathCompStructure::Vector),
        _ if name.contains("GRing.") || name.contains("ssralg.") => {
            Some(MathCompStructure::Other(leaf.to_string()))
        }
        _ => None,
    }
}

// ── S-expression parsing ────────────────────────────────────────────────

fn tc_err(reason: &str) -> MathverseError {
    MathverseError::ImportFailed {
        system: "Coq".into(),
        reason: reason.into(),
    }
}

fn expect_atom(sexp: &Sexp) -> Result<&str, MathverseError> {
    match sexp {
        Sexp::Atom(s) => Ok(s.as_str()),
        _ => Err(tc_err("expected atom")),
    }
}

fn expect_list(sexp: &Sexp) -> Result<&[Sexp], MathverseError> {
    match sexp {
        Sexp::List(v) => Ok(v.as_slice()),
        _ => Err(tc_err("expected list")),
    }
}

fn opt_atom_eq(items: &[Sexp], idx: usize, val: &str) -> bool {
    items
        .get(idx)
        .and_then(|s| match s {
            Sexp::Atom(a) => Some(a.as_str() == val),
            _ => None,
        })
        .unwrap_or(false)
}

/// Parse `(Record name ((p1 t1)...) ((f1 t1 [coercion])...) [true|false])`.
pub fn parse_record(sexp: &Sexp) -> Result<CoqRecord, MathverseError> {
    let items = expect_list(sexp)?;
    if items.is_empty() {
        return Err(tc_err("empty Record form"));
    }
    let head = expect_atom(&items[0])?;
    if head != "Record" {
        return Err(tc_err(&format!("expected Record, got {head}")));
    }
    if items.len() < 4 {
        return Err(tc_err("Record needs name, params, fields"));
    }
    let name = expect_atom(&items[1])?.to_string();
    let mut params = Vec::new();
    for p in expect_list(&items[2])? {
        let pv = expect_list(p)?;
        if pv.len() < 2 {
            return Err(tc_err("param needs name and type"));
        }
        params.push((expect_atom(&pv[0])?.to_string(), sexp_to_cic(&pv[1])?));
    }
    let mut fields = Vec::new();
    for f in expect_list(&items[3])? {
        let fv = expect_list(f)?;
        if fv.len() < 2 {
            return Err(tc_err("field needs name and type"));
        }
        fields.push(CoqField {
            name: expect_atom(&fv[0])?.to_string(),
            type_: sexp_to_cic(&fv[1])?,
            is_coercion: opt_atom_eq(fv, 2, "coercion"),
        });
    }
    Ok(CoqRecord {
        name,
        params,
        fields,
        is_class: opt_atom_eq(items, 4, "true"),
    })
}

/// Parse `(Instance name class ((param)...) body [priority] [global|local])`.
pub fn parse_instance(sexp: &Sexp) -> Result<CoqInstance, MathverseError> {
    let items = expect_list(sexp)?;
    if items.is_empty() {
        return Err(tc_err("empty Instance form"));
    }
    let head = expect_atom(&items[0])?;
    if head != "Instance" {
        return Err(tc_err(&format!("expected Instance, got {head}")));
    }
    if items.len() < 5 {
        return Err(tc_err("Instance needs name, class, params, body"));
    }
    let name = expect_atom(&items[1])?.to_string();
    let class_name = expect_atom(&items[2])?.to_string();
    let params: Result<Vec<_>, _> = expect_list(&items[3])?.iter().map(sexp_to_cic).collect();
    let body = sexp_to_cic(&items[4])?;
    let priority = items.get(5).and_then(|s| match s {
        Sexp::Atom(a) => a.parse::<u32>().ok(),
        _ => None,
    });
    let is_global = !opt_atom_eq(items, 6, "local");
    Ok(CoqInstance {
        name,
        class_name,
        params: params?,
        body,
        priority,
        is_global,
    })
}

/// Parse `(Canonical name projection value)`.
pub fn parse_canonical(sexp: &Sexp) -> Result<CoqCanonical, MathverseError> {
    let items = expect_list(sexp)?;
    if items.is_empty() {
        return Err(tc_err("empty Canonical form"));
    }
    let head = expect_atom(&items[0])?;
    if head != "Canonical" {
        return Err(tc_err(&format!("expected Canonical, got {head}")));
    }
    if items.len() < 4 {
        return Err(tc_err("Canonical needs name, projection, value"));
    }
    Ok(CoqCanonical {
        name: expect_atom(&items[1])?.to_string(),
        projection: expect_atom(&items[2])?.to_string(),
        value: sexp_to_cic(&items[3])?,
    })
}

// ── Import pipeline ─────────────────────────────────────────────────────

fn make_header(
    name_idx: u32,
    type_idx: u32,
    value_idx: u32,
    profile: u64,
    kind: crate::types::DeclKind,
) -> MathverseConstantHeader {
    MathverseConstantHeader {
        name_idx,
        type_idx,
        value_idx,
        source_system: SourceSystem::Coq as u8,
        import_confidence: ImportConfidence::Translated as u8,
        content_domain: ContentDomain::PureMath as u8,
        decl_kind: kind as u8,
        axiom_profile: AxiomProfile(profile),
        sidecar_digest: 0,
        provenance_idx: 0,
        level_params_start: 0,
        level_params_count: 0,
        _pad2: [0u8; 26],
    }
}

/// Import a Coq record into a shard.
/// Creates: one inductive type + one `mk` constructor + N projection definitions.
/// If `is_class`, the type constant gets `TYPE_CLASS_BIT` in its axiom profile.
pub fn import_record(
    record: &CoqRecord,
    module_path: &str,
    writer: &mut ShardWriter,
) -> MathverseResult<RecordImportResult> {
    let mut profile = classify_coq_module(module_path).0;
    if record.is_class {
        profile |= TYPE_CLASS_BIT;
    }

    let record_type = CicTerm::Sort(crate::coq::alpha::CicSort::type_at(0));
    let ty = cic_to_flat_expr(&record_type, writer);
    let ni = writer.add_string(&record.name);
    // Record type → Inductive; its .mk → Constructor; field accessors → Definition.
    let type_idx = writer.add_constant(make_header(
        ni,
        ty,
        NO_VALUE,
        profile,
        crate::types::DeclKind::Inductive,
    ));

    let cn = writer.add_string(&format!("{}.mk", record.name));
    let ct = cic_to_flat_expr(&record_type, writer);
    let ctor_idx = writer.add_constant(make_header(
        cn,
        ct,
        NO_VALUE,
        profile,
        crate::types::DeclKind::Constructor,
    ));

    let mut field_indices = Vec::new();
    for field in &record.fields {
        let pn = writer.add_string(&format!("{}.{}", record.name, field.name));
        let pt = cic_to_flat_expr(&field.type_, writer);
        field_indices.push(writer.add_constant(make_header(
            pn,
            pt,
            NO_VALUE,
            profile,
            crate::types::DeclKind::Definition,
        )));
    }
    Ok(RecordImportResult {
        type_idx,
        ctor_idx,
        field_indices,
    })
}

/// Import a type class instance into a shard. Returns the constant index.
pub fn import_instance(instance: &CoqInstance, writer: &mut ShardWriter) -> MathverseResult<u32> {
    let body_idx = cic_to_flat_expr(&instance.body, writer);
    let type_idx = cic_to_flat_expr(&CicTerm::Var(instance.class_name.clone()), writer);
    let name_idx = writer.add_string(&instance.name);
    // A Coq typeclass instance is a definition producing a record of methods.
    Ok(writer.add_constant(make_header(
        name_idx,
        type_idx,
        body_idx,
        TYPE_CLASS_BIT,
        crate::types::DeclKind::Definition,
    )))
}

// ── Typeclass hierarchy traversal ────────────────────────────────────────

use std::collections::{HashMap, HashSet, VecDeque};

/// Information about a single type class.
#[derive(Clone, Debug)]
pub struct TypeclassInfo {
    pub name: String,
    pub params: Vec<String>,
    pub superclasses: Vec<String>,
    pub methods: Vec<String>,
    pub instances_count: usize,
}

/// Traversable hierarchy of Coq type classes.
#[derive(Clone, Debug, Default)]
pub struct TypeclassHierarchy {
    pub classes: HashMap<String, TypeclassInfo>,
    instances: HashMap<String, Vec<String>>,
}

impl TypeclassHierarchy {
    /// Create an empty hierarchy.
    pub fn new() -> Self {
        Self::default()
    }

    /// Register a class from parsed components.
    pub fn register_class(&mut self, info: TypeclassInfo) {
        let name = info.name.clone();
        self.classes.insert(name.clone(), info);
        self.instances.entry(name).or_default();
    }

    /// Register an instance for a class.
    pub fn register_instance(&mut self, class_name: &str, instance_name: &str) {
        self.instances
            .entry(class_name.to_string())
            .or_default()
            .push(instance_name.to_string());
        if let Some(info) = self.classes.get_mut(class_name) {
            info.instances_count += 1;
        }
    }

    /// Check if `sub` is a transitive subclass of `super_` via BFS on
    /// superclass edges.
    pub fn subclass_of(&self, sub: &str, super_: &str) -> bool {
        if sub == super_ {
            return true;
        }
        let mut visited = HashSet::new();
        let mut queue = VecDeque::new();
        queue.push_back(sub.to_string());
        visited.insert(sub.to_string());
        while let Some(current) = queue.pop_front() {
            let Some(info) = self.classes.get(&current) else {
                continue;
            };
            for sc in &info.superclasses {
                if sc == super_ {
                    return true;
                }
                if visited.insert(sc.clone()) {
                    queue.push_back(sc.clone());
                }
            }
        }
        false
    }

    /// Return all registered instance names for a class.
    pub fn all_instances(&self, class_name: &str) -> Vec<String> {
        self.instances.get(class_name).cloned().unwrap_or_default()
    }

    /// Build hierarchy from s-expressions of the form
    /// `(Class name (params...) (superclasses...) (methods...))`.
    pub fn build_from_sexp(sexps: &[Sexp]) -> Self {
        let mut hierarchy = Self::new();
        for sexp in sexps {
            let items = match sexp {
                Sexp::List(v) if !v.is_empty() => v,
                _ => continue,
            };
            let head = match &items[0] {
                Sexp::Atom(s) if s == "Class" => s.as_str(),
                _ => continue,
            };
            let _ = head;
            if items.len() < 5 {
                continue;
            }
            let name = match &items[1] {
                Sexp::Atom(s) => s.clone(),
                _ => continue,
            };
            let params = match &items[2] {
                Sexp::List(v) => v
                    .iter()
                    .filter_map(|s| match s {
                        Sexp::Atom(a) => Some(a.clone()),
                        _ => None,
                    })
                    .collect(),
                _ => Vec::new(),
            };
            let superclasses = match &items[3] {
                Sexp::List(v) => v
                    .iter()
                    .filter_map(|s| match s {
                        Sexp::Atom(a) => Some(a.clone()),
                        _ => None,
                    })
                    .collect(),
                _ => Vec::new(),
            };
            let methods = match &items[4] {
                Sexp::List(v) => v
                    .iter()
                    .filter_map(|s| match s {
                        Sexp::Atom(a) => Some(a.clone()),
                        _ => None,
                    })
                    .collect(),
                _ => Vec::new(),
            };
            hierarchy.register_class(TypeclassInfo {
                name,
                params,
                superclasses,
                methods,
                instances_count: 0,
            });
        }
        hierarchy
    }
}

// ── Canonical structure resolution ──────────────────────────────────────

/// Resolution table for Coq canonical structures.
///
/// Maps (projection_name, key_type) pairs to canonical instance names,
/// enabling MathComp-style unification hint resolution.
#[derive(Clone, Debug, Default)]
pub struct CanonicalProjectionTable {
    projections: HashMap<(String, String), String>,
}

impl CanonicalProjectionTable {
    /// Create an empty table.
    pub fn new() -> Self {
        Self::default()
    }

    /// Look up the canonical instance for a projection applied to a key type.
    pub fn resolve(&self, proj: &str, key: &str) -> Option<&str> {
        self.projections
            .get(&(proj.to_string(), key.to_string()))
            .map(|s| s.as_str())
    }

    /// Register a canonical structure declaration in the table.
    ///
    /// The projection name comes from `canonical.projection` and the key type
    /// is extracted from the value term (using the top-level constant name).
    pub fn register(&mut self, canonical: &CoqCanonical) {
        let key = extract_canonical_key(&canonical.value);
        self.projections
            .insert((canonical.projection.clone(), key), canonical.name.clone());
    }

    /// Return all (projection, instance) pairs that could unify with a
    /// given target type (i.e. all entries whose key matches `target_type`).
    pub fn unification_hints(&self, target_type: &str) -> Vec<(String, String)> {
        self.projections
            .iter()
            .filter(|((_, key), _)| key == target_type)
            .map(|((proj, _), inst)| (proj.clone(), inst.clone()))
            .collect()
    }
}

/// Extract a key name from a CIC term for canonical structure indexing.
fn extract_canonical_key(term: &CicTerm) -> String {
    match term {
        CicTerm::Const(s) | CicTerm::Var(s) => s.clone(),
        CicTerm::Ind(s, _) => s.clone(),
        CicTerm::Construct(s, _, _) => s.clone(),
        CicTerm::App(f, _) => extract_canonical_key(f),
        _ => "_".to_string(),
    }
}

// ── Record field accessor generation ────────────────────────────────────

/// Generate record accessor constants (projections + constructor) for a
/// Coq record and write them to a shard.
///
/// For each field, generates a projection constant (Pi type from record to
/// field type). Also generates the `mk` constructor (multi-arg function
/// building the record). Returns constant indices for all generated
/// accessors (constructor first, then projections in field order).
pub fn generate_record_accessors(record: &CoqRecord, writer: &mut ShardWriter) -> Vec<u32> {
    let mut indices = Vec::new();
    let record_type = CicTerm::Sort(crate::coq::alpha::CicSort::type_at(0));

    // Constructor: Record.mk : field1_type -> field2_type -> ... -> Record
    let ctor_name = format!("{}.mk", record.name);
    let mut ctor_type = record_type.clone();
    for field in record.fields.iter().rev() {
        ctor_type = CicTerm::Prod(
            field.name.clone(),
            Box::new(field.type_.clone()),
            Box::new(ctor_type),
        );
    }
    let ctor_ty_idx = cic_to_flat_expr(&ctor_type, writer);
    let ctor_ni = writer.add_string(&ctor_name);
    indices.push(writer.add_constant(make_header(
        ctor_ni,
        ctor_ty_idx,
        NO_VALUE,
        0,
        crate::types::DeclKind::Constructor,
    )));

    // Projections: Record.field : Record -> field_type
    for field in &record.fields {
        let proj_type = CicTerm::Prod(
            "_r".to_string(),
            Box::new(record_type.clone()),
            Box::new(field.type_.clone()),
        );
        let proj_ty_idx = cic_to_flat_expr(&proj_type, writer);
        let proj_name = format!("{}.{}", record.name, field.name);
        let proj_ni = writer.add_string(&proj_name);
        indices.push(writer.add_constant(make_header(
            proj_ni,
            proj_ty_idx,
            NO_VALUE,
            0,
            crate::types::DeclKind::Definition,
        )));
    }

    indices
}

// ── MathComp algebra hierarchy ──────────────────────────────────────────

/// Axiom profile configuration for a MathComp structure.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MathCompAxiomConfig {
    pub structure_name: String,
    pub profile_bits: u64,
}

/// Complete MathComp algebra hierarchy with coercion path computation.
///
/// Recognizes 15+ algebraic structures from MathComp and models the
/// coercion (sub-structure) relationships between them. Supports computing
/// coercion paths for implicit structure inheritance.
#[derive(Clone, Debug)]
pub struct MathCompAlgebraHierarchy {
    /// Adjacency list: structure -> list of parent structures (coercion targets).
    parents: HashMap<String, Vec<String>>,
    /// Axiom profile for each structure.
    configs: HashMap<String, MathCompAxiomConfig>,
}

/// All recognized MathComp algebra hierarchy structure names.
const MATHCOMP_STRUCTURES: &[&str] = &[
    "eqType",
    "choiceType",
    "countType",
    "finType",
    "zmodType",
    "ringType",
    "comRingType",
    "fieldType",
    "numFieldType",
    "closedFieldType",
    "lmodType",
    "lalgType",
    "algType",
    "unitRingType",
    "idomainType",
];

impl MathCompAlgebraHierarchy {
    /// Build the standard MathComp algebra hierarchy.
    pub fn new() -> Self {
        let mut parents: HashMap<String, Vec<String>> = HashMap::new();
        let mut configs: HashMap<String, MathCompAxiomConfig> = HashMap::new();

        // Register all structures
        for &name in MATHCOMP_STRUCTURES {
            parents.entry(name.to_string()).or_default();
            configs.insert(
                name.to_string(),
                MathCompAxiomConfig {
                    structure_name: name.to_string(),
                    profile_bits: 0,
                },
            );
        }

        // Coercion edges (child -> parent): child has all parent structure
        let edges: &[(&str, &str)] = &[
            ("choiceType", "eqType"),
            ("countType", "choiceType"),
            ("finType", "countType"),
            ("zmodType", "choiceType"),
            ("ringType", "zmodType"),
            ("comRingType", "ringType"),
            ("unitRingType", "ringType"),
            ("idomainType", "comRingType"),
            ("idomainType", "unitRingType"),
            ("fieldType", "idomainType"),
            ("numFieldType", "fieldType"),
            ("closedFieldType", "numFieldType"),
            ("lmodType", "zmodType"),
            ("lalgType", "lmodType"),
            ("algType", "lalgType"),
            ("algType", "ringType"),
        ];

        for &(child, parent) in edges {
            parents
                .entry(child.to_string())
                .or_default()
                .push(parent.to_string());
        }

        Self { parents, configs }
    }

    /// Compute the coercion path from one structure to another using BFS.
    ///
    /// Returns `None` if no path exists (i.e. `from` is not a sub-structure
    /// of `to`). The returned path includes both endpoints.
    pub fn hierarchy_path(&self, from: &str, to: &str) -> Option<Vec<String>> {
        if from == to {
            return Some(vec![from.to_string()]);
        }
        if !self.parents.contains_key(from) || !self.parents.contains_key(to) {
            return None;
        }

        // BFS from `from` following parent edges toward `to`.
        let mut visited: HashMap<String, String> = HashMap::new();
        let mut queue = VecDeque::new();
        queue.push_back(from.to_string());
        visited.insert(from.to_string(), String::new());

        while let Some(current) = queue.pop_front() {
            if current == to {
                // Reconstruct path
                let mut path = vec![to.to_string()];
                let mut node = to.to_string();
                while let Some(prev) = visited.get(&node) {
                    if prev.is_empty() {
                        break;
                    }
                    path.push(prev.clone());
                    node = prev.clone();
                }
                path.reverse();
                return Some(path);
            }
            let Some(parent_list) = self.parents.get(&current) else {
                continue;
            };
            for parent in parent_list {
                if !visited.contains_key(parent) {
                    visited.insert(parent.clone(), current.clone());
                    queue.push_back(parent.clone());
                }
            }
        }
        None
    }

    /// Check if a structure name is recognized.
    pub fn is_known(&self, name: &str) -> bool {
        self.parents.contains_key(name)
    }

    /// Get the axiom profile configuration for a structure.
    pub fn axiom_config(&self, name: &str) -> Option<&MathCompAxiomConfig> {
        self.configs.get(name)
    }

    /// Return all recognized structure names.
    pub fn all_structures(&self) -> Vec<&str> {
        MATHCOMP_STRUCTURES.to_vec()
    }
}

impl Default for MathCompAlgebraHierarchy {
    fn default() -> Self {
        Self::new()
    }
}

// ── Tests ───────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::coq::alpha::parse_sexp;

    fn p(input: &str) -> Sexp {
        parse_sexp(input).unwrap()
    }

    #[test]
    fn test_parse_record_basic() {
        let rec = parse_record(&p(r#"(Record Point ((A (Sort (Type 0)))) ((x (Sort (Type 0))) (y (Sort (Type 0)))) false)"#)).unwrap();
        assert_eq!(rec.name, "Point");
        assert_eq!((rec.params.len(), rec.fields.len()), (1, 2));
        assert_eq!(
            (rec.params[0].0.as_str(), rec.fields[0].name.as_str()),
            ("A", "x")
        );
        assert!(!rec.is_class);
    }

    #[test]
    fn test_parse_record_class_and_coercion() {
        let rec = parse_record(&p(
            r#"(Record Equiv ((A (Sort (Type 0)))) ((equiv_rel (Sort Prop))) true)"#,
        ))
        .unwrap();
        assert!(rec.is_class);
        assert_eq!(rec.fields.len(), 1);
        let rec2 = parse_record(&p(
            r#"(Record HasSort () ((sort (Sort (Type 0)) coercion)) true)"#,
        ))
        .unwrap();
        assert!(rec2.fields[0].is_coercion);
    }

    #[test]
    fn test_parse_record_errors() {
        assert!(parse_record(&p("(NotRecord foo () ())")).is_err());
        assert!(parse_record(&p("(Record foo)")).is_err());
        assert!(parse_record(&Sexp::Atom("x".into())).is_err());
    }

    #[test]
    fn test_parse_instance_variants() {
        let inst = parse_instance(&p(
            r#"(Instance nat_eq Eq ((Const nat)) (Const nat_eqb) 10)"#,
        ))
        .unwrap();
        assert_eq!(
            (inst.name.as_str(), inst.class_name.as_str()),
            ("nat_eq", "Eq")
        );
        assert_eq!(
            (inst.params.len(), inst.priority, inst.is_global),
            (1, Some(10), true)
        );

        let inst2 = parse_instance(&p(
            r#"(Instance ring_m Monoid ((Const Z)) (Const Z_m) none)"#,
        ))
        .unwrap();
        assert!(inst2.priority.is_none());

        let inst3 =
            parse_instance(&p(r#"(Instance ld Dec ((Const bool)) (Const bd) 5 local)"#)).unwrap();
        assert!(!inst3.is_global);
        assert_eq!(inst3.priority, Some(5));
    }

    #[test]
    fn test_parse_instance_errors() {
        assert!(parse_instance(&p("(Instance foo)")).is_err());
        assert!(parse_instance(&p("(NotInstance a b c d e)")).is_err());
    }

    #[test]
    fn test_parse_canonical_and_errors() {
        let can = parse_canonical(&p(r#"(Canonical nat_eqType eqType.sort (Const nat))"#)).unwrap();
        assert_eq!(
            (can.name.as_str(), can.projection.as_str()),
            ("nat_eqType", "eqType.sort")
        );
        assert!(matches!(can.value, CicTerm::Const(ref s) if s == "nat"));
        assert!(parse_canonical(&p("(Canonical x)")).is_err());
        assert!(parse_canonical(&p("(NotCanonical a b c)")).is_err());
    }

    #[test]
    fn test_import_record_type_ctor_projections() {
        let rec = parse_record(&p(
            r#"(Record Point () ((x (Sort (Type 0))) (y (Sort (Type 0)))) false)"#,
        ))
        .unwrap();
        let mut w = ShardWriter::new();
        let result = import_record(&rec, "Coq.Init.Datatypes", &mut w).unwrap();
        assert_eq!(result.field_indices.len(), 2);
        let mut buf = Vec::new();
        w.write(&mut buf).unwrap();
        let reader = crate::shard::ShardReader::from_bytes(&buf).unwrap();
        assert_eq!(reader.header.constant_count, 4);
        let names: Vec<&str> = reader
            .constants
            .iter()
            .map(|c| reader.strings[c.name_idx as usize].as_str())
            .collect();
        assert_eq!(names, vec!["Point", "Point.mk", "Point.x", "Point.y"]);
    }

    #[test]
    fn test_import_class_has_typeclass_bit() {
        // Class: bit set
        let rec = parse_record(&p(r#"(Record Dec () ((decide (Sort Prop))) true)"#)).unwrap();
        let mut w = ShardWriter::new();
        let res = import_record(&rec, "Coq.Init.Logic", &mut w).unwrap();
        let mut buf = Vec::new();
        w.write(&mut buf).unwrap();
        let rd = crate::shard::ShardReader::from_bytes(&buf).unwrap();
        assert_ne!(
            rd.constants[res.type_idx as usize].axiom_profile & TYPE_CLASS_BIT,
            0
        );
        // Non-class: bit clear
        let rec2 = parse_record(&p(r#"(Record Pair () ((fst (Sort (Type 0)))) false)"#)).unwrap();
        let mut w2 = ShardWriter::new();
        let res2 = import_record(&rec2, "Coq.Init.Datatypes", &mut w2).unwrap();
        let mut buf2 = Vec::new();
        w2.write(&mut buf2).unwrap();
        let rd2 = crate::shard::ShardReader::from_bytes(&buf2).unwrap();
        assert_eq!(
            rd2.constants[res2.type_idx as usize].axiom_profile & TYPE_CLASS_BIT,
            0
        );
    }

    #[test]
    fn test_import_instance() {
        let inst = parse_instance(&p(
            r#"(Instance nat_eq Eq ((Const nat)) (Const nat_eqb) 10)"#,
        ))
        .unwrap();
        let mut w = ShardWriter::new();
        let idx = import_instance(&inst, &mut w).unwrap();
        assert_eq!(idx, 0);
        let mut buf = Vec::new();
        w.write(&mut buf).unwrap();
        let rd = crate::shard::ShardReader::from_bytes(&buf).unwrap();
        assert_eq!(rd.header.constant_count, 1);
        let c = &rd.constants[0];
        assert_eq!(rd.strings[c.name_idx as usize], "nat_eq");
        assert!(c.has_value());
        assert_ne!(c.axiom_profile & TYPE_CLASS_BIT, 0);
    }

    #[test]
    fn test_classify_mathcomp() {
        use MathCompStructure::*;
        assert_eq!(classify_mathcomp_structure("GRing.Ring"), Some(Ring));
        assert_eq!(classify_mathcomp_structure("GRing.Field"), Some(Field));
        assert_eq!(classify_mathcomp_structure("GRing.ComRing"), Some(ComRing));
        assert_eq!(classify_mathcomp_structure("ssralg.Monoid"), Some(Monoid));
        assert_eq!(classify_mathcomp_structure("ssralg.Group"), Some(Group));
        assert_eq!(classify_mathcomp_structure("ssralg.Module"), Some(Module));
        assert_eq!(classify_mathcomp_structure("ssralg.Algebra"), Some(Algebra));
        assert_eq!(classify_mathcomp_structure("ssralg.Vector"), Some(Vector));
        assert_eq!(
            classify_mathcomp_structure("GRing.Zmodule"),
            Some(Other("Zmodule".into()))
        );
        assert_eq!(classify_mathcomp_structure("Coq.Init.nat"), None);
    }

    #[test]
    fn test_record_shard_roundtrip() {
        let rec = parse_record(&p(r#"(Record Sigma ((A (Sort (Type 0)))) ((proj1 (Sort (Type 0))) (proj2 (Sort Prop))) false)"#)).unwrap();
        let mut w = ShardWriter::new();
        import_record(&rec, "Coq.Init.Specif", &mut w).unwrap();
        let mut buf = Vec::new();
        w.write(&mut buf).unwrap();
        let rd = crate::shard::ShardReader::from_bytes(&buf).unwrap();
        assert_eq!(rd.header.constant_count, 4);
        for name in ["Sigma", "Sigma.mk", "Sigma.proj1", "Sigma.proj2"] {
            assert!(rd.lookup_name(name).is_some(), "missing {name}");
        }
        assert!(rd.lookup_name("Sigma.proj3").is_none());
        for c in &rd.constants {
            assert_eq!(c.source_system, SourceSystem::Coq as u8);
        }
    }

    // ── TypeclassHierarchy tests ────────────────────────────────────────

    #[test]
    fn test_hierarchy_build_from_sexp() {
        let input = r#"
            (Class Eq (A) () (eq_dec))
            (Class Ord (A) (Eq) (compare))
            (Class Show (A) () (show))
        "#;
        let sexps = crate::coq::alpha::parse_sexps(input).unwrap();
        let h = TypeclassHierarchy::build_from_sexp(&sexps);
        assert_eq!(h.classes.len(), 3);
        assert!(h.classes.contains_key("Eq"));
        assert!(h.classes.contains_key("Ord"));
        assert_eq!(h.classes["Ord"].superclasses, vec!["Eq"]);
        assert_eq!(h.classes["Eq"].methods, vec!["eq_dec"]);
    }

    #[test]
    fn test_hierarchy_subclass_direct() {
        let input = r#"
            (Class Eq (A) () (eq_dec))
            (Class Ord (A) (Eq) (compare))
        "#;
        let sexps = crate::coq::alpha::parse_sexps(input).unwrap();
        let h = TypeclassHierarchy::build_from_sexp(&sexps);
        assert!(h.subclass_of("Ord", "Eq"));
        assert!(h.subclass_of("Eq", "Eq"));
        assert!(!h.subclass_of("Eq", "Ord"));
    }

    #[test]
    fn test_hierarchy_subclass_transitive() {
        let input = r#"
            (Class A () () ())
            (Class B () (A) ())
            (Class C () (B) ())
            (Class D () (C) ())
        "#;
        let sexps = crate::coq::alpha::parse_sexps(input).unwrap();
        let h = TypeclassHierarchy::build_from_sexp(&sexps);
        assert!(h.subclass_of("D", "A"));
        assert!(h.subclass_of("C", "A"));
        assert!(h.subclass_of("D", "B"));
        assert!(!h.subclass_of("A", "D"));
    }

    #[test]
    fn test_hierarchy_subclass_unknown_class() {
        let h = TypeclassHierarchy::new();
        assert!(!h.subclass_of("Unknown", "AlsoUnknown"));
        assert!(h.subclass_of("X", "X")); // reflexive even if unknown
    }

    #[test]
    fn test_hierarchy_instances() {
        let mut h = TypeclassHierarchy::new();
        h.register_class(TypeclassInfo {
            name: "Eq".into(),
            params: vec!["A".into()],
            superclasses: vec![],
            methods: vec!["eq_dec".into()],
            instances_count: 0,
        });
        h.register_instance("Eq", "nat_eq");
        h.register_instance("Eq", "bool_eq");
        let insts = h.all_instances("Eq");
        assert_eq!(insts.len(), 2);
        assert!(insts.contains(&"nat_eq".to_string()));
        assert!(insts.contains(&"bool_eq".to_string()));
        assert_eq!(h.classes["Eq"].instances_count, 2);
        assert!(h.all_instances("Nonexistent").is_empty());
    }

    #[test]
    fn test_hierarchy_empty_sexp() {
        let h = TypeclassHierarchy::build_from_sexp(&[]);
        assert!(h.classes.is_empty());
    }

    // ── CanonicalProjectionTable tests ──────────────────────────────────

    #[test]
    fn test_canonical_table_register_and_resolve() {
        let mut table = CanonicalProjectionTable::new();
        let can = parse_canonical(&p(r#"(Canonical nat_eqType eqType.sort (Const nat))"#)).unwrap();
        table.register(&can);
        assert_eq!(table.resolve("eqType.sort", "nat"), Some("nat_eqType"));
        assert!(table.resolve("eqType.sort", "bool").is_none());
    }

    #[test]
    fn test_canonical_table_multiple_registrations() {
        let mut table = CanonicalProjectionTable::new();
        table.register(
            &parse_canonical(&p(r#"(Canonical nat_eqType eqType.sort (Const nat))"#)).unwrap(),
        );
        table.register(
            &parse_canonical(&p(r#"(Canonical bool_eqType eqType.sort (Const bool))"#)).unwrap(),
        );
        table.register(
            &parse_canonical(&p(r#"(Canonical nat_ringType ringType.sort (Const nat))"#)).unwrap(),
        );
        assert_eq!(table.resolve("eqType.sort", "nat"), Some("nat_eqType"));
        assert_eq!(table.resolve("eqType.sort", "bool"), Some("bool_eqType"));
        assert_eq!(table.resolve("ringType.sort", "nat"), Some("nat_ringType"));
    }

    #[test]
    fn test_canonical_table_unification_hints() {
        let mut table = CanonicalProjectionTable::new();
        table.register(
            &parse_canonical(&p(r#"(Canonical nat_eqType eqType.sort (Const nat))"#)).unwrap(),
        );
        table.register(
            &parse_canonical(&p(r#"(Canonical nat_ringType ringType.sort (Const nat))"#)).unwrap(),
        );
        table.register(
            &parse_canonical(&p(r#"(Canonical bool_eqType eqType.sort (Const bool))"#)).unwrap(),
        );
        let hints = table.unification_hints("nat");
        assert_eq!(hints.len(), 2);
        let proj_names: Vec<&str> = hints.iter().map(|(p, _)| p.as_str()).collect();
        assert!(proj_names.contains(&"eqType.sort"));
        assert!(proj_names.contains(&"ringType.sort"));
        assert!(table.unification_hints("unknown").is_empty());
    }

    #[test]
    fn test_canonical_table_app_key_extraction() {
        let mut table = CanonicalProjectionTable::new();
        // Value is (App (Const list) (Const nat)) -- key should be "list"
        table.register(
            &parse_canonical(&p(
                r#"(Canonical list_eqType eqType.sort (App (Const list) (Const nat)))"#,
            ))
            .unwrap(),
        );
        assert_eq!(table.resolve("eqType.sort", "list"), Some("list_eqType"));
    }

    // ── Record accessor generation tests ────────────────────────────────

    #[test]
    fn test_generate_record_accessors_basic() {
        let rec = parse_record(&p(
            r#"(Record Point () ((x (Sort (Type 0))) (y (Sort (Type 0)))) false)"#,
        ))
        .unwrap();
        let mut w = ShardWriter::new();
        let indices = generate_record_accessors(&rec, &mut w);
        // 1 constructor + 2 projections
        assert_eq!(indices.len(), 3);
        let mut buf = Vec::new();
        w.write(&mut buf).unwrap();
        let rd = crate::shard::ShardReader::from_bytes(&buf).unwrap();
        let names: Vec<&str> = rd
            .constants
            .iter()
            .map(|c| rd.strings[c.name_idx as usize].as_str())
            .collect();
        assert_eq!(names, vec!["Point.mk", "Point.x", "Point.y"]);
    }

    #[test]
    fn test_generate_record_accessors_single_field() {
        let rec = parse_record(&p(r#"(Record Wrap () ((value (Sort Prop))) false)"#)).unwrap();
        let mut w = ShardWriter::new();
        let indices = generate_record_accessors(&rec, &mut w);
        assert_eq!(indices.len(), 2); // mk + value
    }

    // ── MathCompAlgebraHierarchy tests ──────────────────────────────────

    #[test]
    fn test_mathcomp_hierarchy_known_structures() {
        let h = MathCompAlgebraHierarchy::new();
        assert!(h.is_known("eqType"));
        assert!(h.is_known("ringType"));
        assert!(h.is_known("fieldType"));
        assert!(h.is_known("closedFieldType"));
        assert!(!h.is_known("unknownType"));
        assert_eq!(h.all_structures().len(), 15);
    }

    #[test]
    fn test_mathcomp_hierarchy_path_identity() {
        let h = MathCompAlgebraHierarchy::new();
        let path = h.hierarchy_path("ringType", "ringType").unwrap();
        assert_eq!(path, vec!["ringType"]);
    }

    #[test]
    fn test_mathcomp_hierarchy_path_direct() {
        let h = MathCompAlgebraHierarchy::new();
        let path = h.hierarchy_path("choiceType", "eqType").unwrap();
        assert_eq!(path, vec!["choiceType", "eqType"]);
    }

    #[test]
    fn test_mathcomp_hierarchy_path_transitive() {
        let h = MathCompAlgebraHierarchy::new();
        // finType -> countType -> choiceType -> eqType
        let path = h.hierarchy_path("finType", "eqType").unwrap();
        assert_eq!(path.first().unwrap(), "finType");
        assert_eq!(path.last().unwrap(), "eqType");
        assert!(path.len() >= 3);
    }

    #[test]
    fn test_mathcomp_hierarchy_path_field_chain() {
        let h = MathCompAlgebraHierarchy::new();
        // fieldType -> idomainType -> comRingType -> ringType -> zmodType
        let path = h.hierarchy_path("fieldType", "zmodType").unwrap();
        assert_eq!(path.first().unwrap(), "fieldType");
        assert_eq!(path.last().unwrap(), "zmodType");
    }

    #[test]
    fn test_mathcomp_hierarchy_no_reverse_path() {
        let h = MathCompAlgebraHierarchy::new();
        // eqType is NOT a sub-structure of ringType
        assert!(h.hierarchy_path("eqType", "ringType").is_none());
    }

    #[test]
    fn test_mathcomp_hierarchy_unknown_structure() {
        let h = MathCompAlgebraHierarchy::new();
        assert!(h.hierarchy_path("unknownType", "eqType").is_none());
        assert!(h.hierarchy_path("eqType", "unknownType").is_none());
    }

    #[test]
    fn test_mathcomp_hierarchy_axiom_config() {
        let h = MathCompAlgebraHierarchy::new();
        let cfg = h.axiom_config("ringType").unwrap();
        assert_eq!(cfg.structure_name, "ringType");
        assert!(h.axiom_config("unknownType").is_none());
    }
}
