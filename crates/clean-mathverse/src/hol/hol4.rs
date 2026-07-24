// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// Variant names share an enum-prefix by design (e.g., 'KindFoo', 'KindBar' for KindKind enums); renaming is API-breaking.
#![allow(clippy::enum_variant_names)]

//! HOL4 specific importer configuration.
//!
//! HOL4 exports its proofs via the OpenTheory article (`.art`) format,
//! identical to HOL Light. This module provides a `Hol4Importer` that
//! wraps the generic [`OtMathverseBridge`] with HOL4-specific namespace and
//! source system tagging.

use std::path::Path;

use clean_kernel::Name as LeanName;

use crate::types::{AxiomProfile, SourceSystem, TrustLevel};

use super::error::{HolError, HolResult};
use super::opentheory_bridge::{
    ImportStatistics, ImportedConstantKind, MathverseImportedConstant, OtMathverseBridge,
};

/// Default namespace for HOL4 imports in the Mathverse library.
const HOL4_NAMESPACE: &str = "HOL4.Imported";

/// HOL4 importer configuration.
///
/// Wraps the OpenTheory bridge with HOL4-specific defaults:
/// - Namespace: `HOL4.Imported`
/// - Source system: `SourceSystem::Hol4`
/// - Axiom profile: `CLASSICAL | EXTENSIONALITY | HOL_EMBEDDING`
///   (same as HOL Light; both use the same OpenTheory pipeline)
pub struct Hol4Importer {
    namespace: LeanName,
}

impl Default for Hol4Importer {
    fn default() -> Self {
        Self {
            namespace: LeanName::from_string(HOL4_NAMESPACE),
        }
    }
}

impl Hol4Importer {
    /// Create a new HOL4 importer with a custom namespace.
    #[must_use]
    pub(crate) fn with_namespace(namespace: &str) -> Self {
        Self {
            namespace: LeanName::from_string(namespace),
        }
    }

    /// Import a single `.art` file.
    pub fn import_file(
        &self,
        path: &Path,
    ) -> HolResult<(Vec<MathverseImportedConstant>, ImportStatistics)> {
        let bridge = self.make_bridge(Some(path));
        bridge.import_file(path)
    }

    /// Import an OpenTheory article from raw text.
    pub(crate) fn import_text(
        &self,
        input: &str,
    ) -> HolResult<(Vec<MathverseImportedConstant>, ImportStatistics)> {
        let bridge = self.make_bridge(None);
        bridge.import_article_text(input)
    }

    /// Bulk-import all `.art` files from a directory.
    ///
    /// Returns the combined list of imported constants, aggregate statistics,
    /// and any per-file errors (non-fatal).
    pub fn import_directory(
        &self,
        dir: &Path,
    ) -> HolResult<(
        Vec<MathverseImportedConstant>,
        ImportStatistics,
        Vec<HolError>,
    )> {
        let art_files = collect_art_files(dir)?;
        if art_files.is_empty() {
            return Err(HolError::NoArticlesFound {
                path: dir.display().to_string(),
            });
        }

        let mut all_constants = Vec::new();
        let mut aggregate_stats = ImportStatistics::default();
        let mut errors = Vec::new();

        for file_path in &art_files {
            match self.import_file(file_path) {
                Ok((constants, stats)) => {
                    all_constants.extend(constants);
                    aggregate_stats.support_count += stats.support_count;
                    aggregate_stats.assumption_count += stats.assumption_count;
                    aggregate_stats.theorem_count += stats.theorem_count;
                }
                Err(e) => {
                    errors.push(e);
                }
            }
        }

        Ok((all_constants, aggregate_stats, errors))
    }

    /// Import a collection of OpenTheory article texts as a named HOL4 theory.
    ///
    /// HOL4 theories have a parent-child hierarchy. The `parents` parameter
    /// records which theories this one depends on (e.g., `["bool", "num"]`).
    /// Each article is processed through the OpenTheory bridge. Articles that
    /// fail to parse are counted in statistics but do not abort the import.
    pub(crate) fn import_theory(
        &self,
        theory_name: &str,
        parents: &[&str],
        articles: &[&str],
    ) -> HolResult<Hol4Theory> {
        let bridge = self.make_bridge(None);

        let mut types = Vec::new();
        let mut constants = Vec::new();
        let mut theorems = Vec::new();
        let mut stats = Hol4Statistics {
            total_articles: articles.len(),
            imported_constants: 0,
            failed_articles: 0,
            theorem_count: 0,
            type_count: 0,
            constant_count: 0,
        };

        for article_text in articles {
            match bridge.import_article_text(article_text) {
                Ok((imported, _import_stats)) => {
                    for constant in imported {
                        stats.imported_constants += 1;
                        match constant.kind {
                            ImportedConstantKind::Support => {
                                // In HOL4 terminology, support declarations are
                                // type operators and constant definitions.
                                // We split them: if the name looks like a type
                                // operator, it goes to types; otherwise constants.
                                if is_likely_type_operator(&constant.name.to_string()) {
                                    stats.type_count += 1;
                                    types.push(constant);
                                } else {
                                    stats.constant_count += 1;
                                    constants.push(constant);
                                }
                            }
                            ImportedConstantKind::Assumption => {
                                stats.constant_count += 1;
                                constants.push(constant);
                            }
                            ImportedConstantKind::Theorem => {
                                stats.theorem_count += 1;
                                theorems.push(constant);
                            }
                        }
                    }
                }
                Err(_) => {
                    stats.failed_articles += 1;
                }
            }
        }

        Ok(Hol4Theory {
            theory_name: theory_name.to_owned(),
            parents: parents.iter().map(|s| (*s).to_owned()).collect(),
            types,
            constants,
            theorems,
            statistics: stats,
        })
    }

    /// Build an `OtMathverseBridge` configured for HOL4.
    fn make_bridge(&self, source_path: Option<&Path>) -> OtMathverseBridge {
        let bridge = OtMathverseBridge::new(self.namespace.clone(), SourceSystem::Hol4);
        match source_path {
            Some(path) => bridge.with_source_file(&path.display().to_string()),
            None => bridge,
        }
    }
}

/// A complete HOL4 theory, aggregated from one or more OpenTheory articles.
///
/// HOL4 theories are organized in a parent-child hierarchy. Each theory
/// declares types, constants, and theorems. The parent list records
/// which theories this one depends on.
#[derive(Clone, Debug)]
pub(crate) struct Hol4Theory {
    /// Name of this theory (e.g., `"bool"`, `"num"`, `"list"`).
    pub(crate) theory_name: String,
    /// Parent theory names that this theory depends on.
    pub(crate) parents: Vec<String>,
    /// Type operator declarations from the articles.
    pub(crate) types: Vec<MathverseImportedConstant>,
    /// Constant declarations (including axioms) from the articles.
    pub(crate) constants: Vec<MathverseImportedConstant>,
    /// Proved theorems from the articles.
    pub(crate) theorems: Vec<MathverseImportedConstant>,
    /// Aggregate statistics for this theory import.
    pub(crate) statistics: Hol4Statistics,
}

impl Hol4Theory {
    /// Total number of declarations across all categories.
    #[must_use]
    pub(crate) fn total_declarations(&self) -> usize {
        self.types.len() + self.constants.len() + self.theorems.len()
    }

    /// The combined axiom profile for all declarations in the theory.
    #[must_use]
    pub(crate) fn combined_axiom_profile(&self) -> AxiomProfile {
        let all = self
            .types
            .iter()
            .chain(self.constants.iter())
            .chain(self.theorems.iter());

        let mut combined = AxiomProfile::NONE;
        for c in all {
            combined |= c.axiom_profile;
        }
        combined
    }

    /// The minimum trust level across all declarations.
    ///
    /// Returns `None` if the theory has no declarations.
    #[must_use]
    pub(crate) fn min_trust_level(&self) -> Option<TrustLevel> {
        self.types
            .iter()
            .chain(self.constants.iter())
            .chain(self.theorems.iter())
            .map(|c| c.trust_level)
            .min()
    }

    /// Names of all theorems in the theory.
    #[must_use]
    pub(crate) fn theorem_names(&self) -> Vec<String> {
        self.theorems.iter().map(|t| t.name.to_string()).collect()
    }

    /// Whether this theory has any parent dependencies.
    #[must_use]
    pub(crate) fn has_parents(&self) -> bool {
        !self.parents.is_empty()
    }
}

/// Statistics for a HOL4 theory import.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct Hol4Statistics {
    /// Total number of article texts provided for import.
    pub(crate) total_articles: usize,
    /// Total number of constants successfully imported.
    pub(crate) imported_constants: usize,
    /// Number of articles that failed to parse or import.
    pub(crate) failed_articles: usize,
    /// Number of proved theorems imported.
    pub(crate) theorem_count: usize,
    /// Number of type operators imported.
    pub(crate) type_count: usize,
    /// Number of constant declarations (including axioms) imported.
    pub(crate) constant_count: usize,
}

impl Hol4Statistics {
    /// Success rate as a fraction in [0.0, 1.0].
    ///
    /// Returns 1.0 if no articles were provided.
    #[must_use]
    pub(crate) fn success_rate(&self) -> f64 {
        if self.total_articles == 0 {
            return 1.0;
        }
        let successful = self.total_articles - self.failed_articles;
        successful as f64 / self.total_articles as f64
    }
}

/// HOL4 export format variants.
///
/// HOL4 can export its theories in several formats. The primary format
/// for cross-system interoperability is the OpenTheory article format,
/// but HOL4 also supports S-expression dumps and JSON for tooling.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) enum Hol4ExportFormat {
    /// OpenTheory article format (`.art` files).
    /// This is the primary interoperability format supported by the bridge.
    ArticleFormat,
    /// S-expression format used by HOL4's internal export.
    SExpFormat,
    /// JSON format for tooling and web-based viewers.
    JsonFormat,
}

impl Hol4ExportFormat {
    /// File extension associated with this format.
    #[must_use]
    pub(crate) fn extension(&self) -> &'static str {
        match self {
            Self::ArticleFormat => "art",
            Self::SExpFormat => "sexp",
            Self::JsonFormat => "json",
        }
    }

    /// Human-readable description of the format.
    #[must_use]
    pub(crate) fn description(&self) -> &'static str {
        match self {
            Self::ArticleFormat => "OpenTheory article format",
            Self::SExpFormat => "S-expression export format",
            Self::JsonFormat => "JSON export format",
        }
    }

    /// Whether this format is currently supported for import.
    #[must_use]
    pub(crate) fn is_import_supported(&self) -> bool {
        matches!(self, Self::ArticleFormat)
    }
}

/// HOL4 type operator constructors.
///
/// HOL4 has a fixed set of built-in type operators plus user-defined ones.
/// This enum represents the built-in operators that appear in the HOL4
/// theory hierarchy.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) enum Hol4TypeOp {
    /// Boolean type: `bool`.
    Bool,
    /// Function arrow type: `->` (written `fun` internally).
    Fun,
    /// Individual type (for HOL's type of individuals): `ind`.
    Ind,
    /// Natural number type: `num`.
    Num,
    /// List type constructor: `list`.
    List,
    /// Option/sum type: `option`.
    Option,
    /// Pair/product type: `prod`.
    Prod,
    /// Sum type: `sum`.
    Sum,
    /// User-defined type operator with the given name and arity.
    UserDefined {
        /// Name of the type operator.
        name: String,
        /// Number of type arguments.
        arity: usize,
    },
}

impl Hol4TypeOp {
    /// The name of this type operator as it appears in HOL4.
    #[must_use]
    pub(crate) fn name(&self) -> &str {
        match self {
            Self::Bool => "bool",
            Self::Fun => "fun",
            Self::Ind => "ind",
            Self::Num => "num",
            Self::List => "list",
            Self::Option => "option",
            Self::Prod => "prod",
            Self::Sum => "sum",
            Self::UserDefined { name, .. } => name,
        }
    }

    /// Arity (number of type arguments) of this operator.
    #[must_use]
    pub(crate) fn arity(&self) -> usize {
        match self {
            Self::Bool | Self::Ind | Self::Num => 0,
            Self::Fun | Self::Prod | Self::Sum => 2,
            Self::List | Self::Option => 1,
            Self::UserDefined { arity, .. } => *arity,
        }
    }

    /// Whether this is a built-in type operator (not user-defined).
    #[must_use]
    pub(crate) fn is_builtin(&self) -> bool {
        !matches!(self, Self::UserDefined { .. })
    }

    /// Try to parse a type operator name into a `Hol4TypeOp`.
    #[must_use]
    pub(crate) fn from_name(name: &str) -> Self {
        match name {
            "bool" => Self::Bool,
            "fun" | "->" => Self::Fun,
            "ind" => Self::Ind,
            "num" => Self::Num,
            "list" => Self::List,
            "option" => Self::Option,
            "prod" => Self::Prod,
            "sum" => Self::Sum,
            other => Self::UserDefined {
                name: other.to_owned(),
                arity: 0,
            },
        }
    }

    /// Try to parse with explicit arity for user-defined types.
    #[must_use]
    pub(crate) fn from_name_with_arity(name: &str, arity: usize) -> Self {
        let mut op = Self::from_name(name);
        if let Self::UserDefined {
            arity: ref mut a, ..
        } = op
        {
            *a = arity;
        }
        op
    }
}

/// A node in the HOL4 theory dependency graph.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Hol4TheoryNode {
    /// Theory name.
    pub(crate) name: String,
    /// Names of parent theories that this theory depends on.
    pub(crate) parents: Vec<String>,
    /// Number of theorems in this theory (if known).
    pub(crate) theorem_count: Option<usize>,
    /// Number of type operators defined in this theory (if known).
    pub(crate) type_count: Option<usize>,
    /// Number of constants defined in this theory (if known).
    pub(crate) constant_count: Option<usize>,
}

/// A graph of HOL4 theory dependencies.
///
/// HOL4 theories form a DAG where each theory declares its parent theories.
/// The root of the graph is typically `min` (the minimal theory).
#[derive(Clone, Debug)]
pub(crate) struct Hol4TheoryGraph {
    /// All theories in the graph, keyed by theory name.
    theories: std::collections::HashMap<String, Hol4TheoryNode>,
}

impl Hol4TheoryGraph {
    /// Create an empty theory graph.
    #[must_use]
    pub(crate) fn new() -> Self {
        Self {
            theories: std::collections::HashMap::new(),
        }
    }

    /// Add a theory node to the graph.
    pub(crate) fn add_theory(&mut self, node: Hol4TheoryNode) {
        self.theories.insert(node.name.clone(), node);
    }

    /// Add a theory by name with its parent list.
    pub(crate) fn add_theory_with_parents(&mut self, name: &str, parents: &[&str]) {
        self.theories.insert(
            name.to_owned(),
            Hol4TheoryNode {
                name: name.to_owned(),
                parents: parents.iter().map(|s| (*s).to_owned()).collect(),
                theorem_count: None,
                type_count: None,
                constant_count: None,
            },
        );
    }

    /// Get a theory node by name.
    #[must_use]
    pub(crate) fn get_theory(&self, name: &str) -> Option<&Hol4TheoryNode> {
        self.theories.get(name)
    }

    /// Number of theories in the graph.
    #[must_use]
    pub(crate) fn theory_count(&self) -> usize {
        self.theories.len()
    }

    /// Whether the graph is empty.
    #[must_use]
    pub(crate) fn is_empty(&self) -> bool {
        self.theories.is_empty()
    }

    /// All theory names, sorted alphabetically.
    #[must_use]
    pub(crate) fn theory_names(&self) -> Vec<&str> {
        let mut names: Vec<&str> = self.theories.keys().map(|s| s.as_str()).collect();
        names.sort();
        names
    }

    /// Get the direct parents of a theory.
    #[must_use]
    pub(crate) fn parents_of(&self, name: &str) -> Vec<&str> {
        self.theories
            .get(name)
            .map(|node| node.parents.iter().map(|s| s.as_str()).collect())
            .unwrap_or_default()
    }

    /// Get the direct children of a theory (theories that list `name` as a parent).
    #[must_use]
    pub(crate) fn children_of(&self, name: &str) -> Vec<&str> {
        self.theories
            .values()
            .filter(|node| node.parents.iter().any(|p| p == name))
            .map(|node| node.name.as_str())
            .collect()
    }

    /// Find root theories (theories with no parents in the graph).
    #[must_use]
    pub(crate) fn roots(&self) -> Vec<&str> {
        self.theories
            .values()
            .filter(|node| node.parents.is_empty())
            .map(|node| node.name.as_str())
            .collect()
    }

    /// Find leaf theories (theories with no children in the graph).
    #[must_use]
    pub(crate) fn leaves(&self) -> Vec<&str> {
        let has_children: std::collections::HashSet<&str> = self
            .theories
            .values()
            .flat_map(|node| node.parents.iter().map(|p| p.as_str()))
            .collect();

        self.theories
            .keys()
            .filter(|name| !has_children.contains(name.as_str()))
            .map(|s| s.as_str())
            .collect()
    }

    /// Compute the transitive closure of dependencies for a theory.
    ///
    /// Returns all ancestors (direct and indirect parents) sorted by name.
    #[must_use]
    pub(crate) fn transitive_dependencies(&self, name: &str) -> Vec<String> {
        let mut visited = std::collections::HashSet::new();
        let mut stack = vec![name.to_owned()];

        while let Some(current) = stack.pop() {
            if !visited.insert(current.clone()) {
                continue;
            }
            if let Some(node) = self.theories.get(&current) {
                for parent in &node.parents {
                    if !visited.contains(parent) {
                        stack.push(parent.clone());
                    }
                }
            }
        }

        // Remove the starting node itself from the result.
        visited.remove(name);

        let mut result: Vec<String> = visited.into_iter().collect();
        result.sort();
        result
    }

    /// Check whether the graph has any cycles.
    ///
    /// A well-formed HOL4 theory hierarchy should be a DAG.
    #[must_use]
    pub(crate) fn has_cycle(&self) -> bool {
        // Standard DFS cycle detection.
        let mut visited = std::collections::HashSet::new();
        let mut in_stack = std::collections::HashSet::new();

        for name in self.theories.keys() {
            if self.dfs_has_cycle(name, &mut visited, &mut in_stack) {
                return true;
            }
        }
        false
    }

    /// DFS helper for cycle detection.
    fn dfs_has_cycle(
        &self,
        name: &str,
        visited: &mut std::collections::HashSet<String>,
        in_stack: &mut std::collections::HashSet<String>,
    ) -> bool {
        if in_stack.contains(name) {
            return true; // Back edge = cycle.
        }
        if visited.contains(name) {
            return false; // Already fully explored.
        }

        visited.insert(name.to_owned());
        in_stack.insert(name.to_owned());

        if let Some(node) = self.theories.get(name) {
            for parent in &node.parents {
                if self.dfs_has_cycle(parent, visited, in_stack) {
                    return true;
                }
            }
        }

        in_stack.remove(name);
        false
    }
}

/// Parse a theory graph from a text description.
///
/// Expected format: one theory per line, as `theory_name: parent1, parent2, ...`.
/// Lines starting with `#` or empty lines are ignored.
///
/// Example:
/// ```text
/// min:
/// bool: min
/// num: min, bool
/// list: bool, num
/// ```
#[must_use]
pub(crate) fn parse_theory_graph(text: &str) -> Hol4TheoryGraph {
    let mut graph = Hol4TheoryGraph::new();

    for line in text.lines() {
        let trimmed = line.trim();
        if trimmed.is_empty() || trimmed.starts_with('#') {
            continue;
        }

        let parts: Vec<&str> = trimmed.splitn(2, ':').collect();
        if parts.is_empty() {
            continue;
        }

        let name = parts[0].trim();
        if name.is_empty() {
            continue;
        }

        let parents: Vec<&str> = if parts.len() > 1 && !parts[1].trim().is_empty() {
            parts[1]
                .split(',')
                .map(|p| p.trim())
                .filter(|p| !p.is_empty())
                .collect()
        } else {
            Vec::new()
        };

        graph.add_theory_with_parents(name, &parents);
    }

    graph
}

/// Heuristic: names containing "typeOp" or ending with "Type" are likely
/// type operators rather than term constants.
fn is_likely_type_operator(name: &str) -> bool {
    name.contains("typeOp") || name.ends_with("Type") || name.ends_with(".type")
}

/// Collect all `.art` files in a directory (non-recursive).
fn collect_art_files(dir: &Path) -> HolResult<Vec<std::path::PathBuf>> {
    let mut files = Vec::new();
    for entry in std::fs::read_dir(dir)? {
        let entry = entry?;
        let path = entry.path();
        if path.extension().and_then(|e| e.to_str()) == Some("art") && path.is_file() {
            files.push(path);
        }
    }
    files.sort();
    Ok(files)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hol::opentheory_bridge::HOL_BASE_PROFILE;

    /// Minimal refl article (x = x) for testing.
    const TEST_REFL: &str = r#"
6
version
"x"
"A"
varType
3
def
var
1
def
varTerm
2
def
refl
4
def
"bool"
typeOp
nil
opType
5
def
"->"
typeOp
3
ref
5
ref
nil
cons
cons
opType
6
def
"->"
typeOp
3
ref
6
ref
nil
cons
cons
opType
7
def
"="
const
7
ref
constTerm
2
ref
appTerm
2
ref
appTerm
8
def
4
ref
nil
8
ref
thm
"#;

    #[test]
    fn test_default_namespace() {
        let importer = Hol4Importer::default();
        assert_eq!(importer.namespace, LeanName::from_string(HOL4_NAMESPACE));
    }

    #[test]
    fn test_custom_namespace() {
        let importer = Hol4Importer::with_namespace("Custom.HOL4");
        assert_eq!(importer.namespace, LeanName::from_string("Custom.HOL4"));
    }

    #[test]
    fn test_import_theory_single_article() {
        let importer = Hol4Importer::default();
        let theory = importer
            .import_theory("boolTheory", &["min"], &[TEST_REFL])
            .expect("theory import should succeed");

        assert_eq!(theory.theory_name, "boolTheory");
        assert_eq!(theory.parents, vec!["min"]);
        assert_eq!(theory.statistics.total_articles, 1);
        assert_eq!(theory.statistics.failed_articles, 0);
        assert!(theory.statistics.imported_constants > 0);
    }

    #[test]
    fn test_import_theory_multiple_articles() {
        let importer = Hol4Importer::default();
        let theory = importer
            .import_theory("numTheory", &["bool"], &[TEST_REFL, TEST_REFL])
            .expect("theory import should succeed");

        assert_eq!(theory.statistics.total_articles, 2);
        assert_eq!(theory.statistics.failed_articles, 0);
        assert_eq!(theory.statistics.theorem_count, 2);
    }

    #[test]
    fn test_import_theory_with_bad_article() {
        let importer = Hol4Importer::default();
        let theory = importer
            .import_theory("mixedTheory", &[], &[TEST_REFL, "garbage\n"])
            .expect("theory import should succeed despite bad article");

        assert_eq!(theory.statistics.total_articles, 2);
        assert_eq!(theory.statistics.failed_articles, 1);
        assert_eq!(theory.statistics.theorem_count, 1);
    }

    #[test]
    fn test_import_theory_empty_articles() {
        let importer = Hol4Importer::default();
        let theory = importer
            .import_theory("emptyTheory", &["bool", "num"], &[])
            .expect("empty theory import should succeed");

        assert_eq!(theory.statistics.total_articles, 0);
        assert_eq!(theory.total_declarations(), 0);
        assert_eq!(theory.parents, vec!["bool", "num"]);
    }

    #[test]
    fn test_theory_total_declarations() {
        let importer = Hol4Importer::default();
        let theory = importer
            .import_theory("count", &[], &[TEST_REFL])
            .expect("theory import should succeed");

        let expected = theory.types.len() + theory.constants.len() + theory.theorems.len();
        assert_eq!(theory.total_declarations(), expected);
    }

    #[test]
    fn test_theory_combined_axiom_profile() {
        let importer = Hol4Importer::default();
        let theory = importer
            .import_theory("profile", &[], &[TEST_REFL])
            .expect("theory import should succeed");

        let profile = theory.combined_axiom_profile();
        assert!(profile.contains(AxiomProfile::CLASSICAL));
        assert!(profile.contains(AxiomProfile::HOL_EMBEDDING));
    }

    #[test]
    fn test_theory_min_trust_level() {
        let importer = Hol4Importer::default();
        let theory = importer
            .import_theory("trust", &[], &[TEST_REFL])
            .expect("theory import should succeed");

        assert!(theory.min_trust_level().is_some());
    }

    #[test]
    fn test_theory_min_trust_level_empty() {
        let importer = Hol4Importer::default();
        let theory = importer
            .import_theory("empty_trust", &[], &[])
            .expect("empty theory");

        assert!(theory.min_trust_level().is_none());
    }

    #[test]
    fn test_theory_has_parents() {
        let importer = Hol4Importer::default();
        let with_parents = importer
            .import_theory("child", &["parent1", "parent2"], &[])
            .expect("theory import");
        assert!(with_parents.has_parents());

        let no_parents = importer
            .import_theory("root", &[], &[])
            .expect("theory import");
        assert!(!no_parents.has_parents());
    }

    #[test]
    fn test_theory_theorem_names() {
        let importer = Hol4Importer::default();
        let theory = importer
            .import_theory("names", &[], &[TEST_REFL])
            .expect("theory import should succeed");

        let names = theory.theorem_names();
        assert_eq!(names.len(), theory.theorems.len());
        for name in &names {
            assert!(!name.is_empty());
        }
    }

    #[test]
    fn test_statistics_success_rate_all_good() {
        let stats = Hol4Statistics {
            total_articles: 3,
            imported_constants: 9,
            failed_articles: 0,
            theorem_count: 3,
            type_count: 3,
            constant_count: 3,
        };
        assert!((stats.success_rate() - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_statistics_success_rate_with_failures() {
        let stats = Hol4Statistics {
            total_articles: 4,
            imported_constants: 6,
            failed_articles: 2,
            theorem_count: 3,
            type_count: 1,
            constant_count: 2,
        };
        assert!((stats.success_rate() - 0.5).abs() < f64::EPSILON);
    }

    #[test]
    fn test_statistics_success_rate_empty() {
        let stats = Hol4Statistics::default();
        assert!((stats.success_rate() - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_is_likely_type_operator() {
        assert!(is_likely_type_operator("boolType"));
        assert!(is_likely_type_operator("nat.type"));
        assert!(is_likely_type_operator("some.typeOp.thing"));
        assert!(!is_likely_type_operator("add"));
        assert!(!is_likely_type_operator("HOL.True"));
    }
}
