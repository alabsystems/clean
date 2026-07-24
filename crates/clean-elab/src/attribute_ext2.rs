// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended attribute handling: parsing, validation, scoping, inheritance,
//! removal, custom registration, argument parsing, conflict detection, stats.
//!
//! Reference: Lean 4 `src/Lean/Attributes.lean`, `src/Lean/Elab/DeclModifiers.lean`

use crate::error::ElabError;
use clean_kernel::name::Name;
use std::collections::{HashMap, HashSet};

/// The kind of declaration an attribute is being applied to.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub(crate) enum DeclKind {
    Definition,
    Theorem,
    Inductive,
    Structure,
    Instance,
    Abbrev,
    Opaque,
    Axiom,
}

/// A parsed attribute with optional arguments from surface syntax.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ParsedAttribute {
    pub(crate) name: String,
    pub(crate) args: Vec<String>,
    pub(crate) is_removal: bool,
}

/// Parse a comma-separated attribute list from surface syntax.
///
/// Handles simple attrs (`simp`), with arguments (`priority 100`),
/// and removal syntax (`-simp`).
pub(crate) fn parse_attribute_list(input: &str) -> Result<Vec<ParsedAttribute>, ElabError> {
    let trimmed = input.trim();
    if trimmed.is_empty() {
        return Ok(Vec::new());
    }
    let mut attrs = Vec::new();
    for part in trimmed.split(',') {
        let part = part.trim();
        if part.is_empty() {
            continue;
        }
        let (is_removal, rest) = if let Some(stripped) = part.strip_prefix('-') {
            (true, stripped.trim())
        } else {
            (false, part)
        };
        let tokens = parse_attribute_tokens(rest)?;
        if tokens.is_empty() {
            return Err(ElabError::ParseError("empty attribute in list".to_owned()));
        }
        attrs.push(ParsedAttribute {
            name: tokens[0].clone(),
            args: tokens[1..].to_vec(),
            is_removal,
        });
    }
    Ok(attrs)
}

fn parse_attribute_tokens(input: &str) -> Result<Vec<String>, ElabError> {
    let mut tokens = Vec::new();
    let mut current = String::new();
    let mut in_quote = false;

    for ch in input.chars() {
        match ch {
            '"' => {
                in_quote = !in_quote;
            }
            c if c.is_whitespace() && !in_quote => {
                if !current.is_empty() {
                    tokens.push(std::mem::take(&mut current));
                }
            }
            c => current.push(c),
        }
    }

    if in_quote {
        return Err(ElabError::ParseError(
            "unterminated quoted attribute argument".to_owned(),
        ));
    }

    if !current.is_empty() {
        tokens.push(current);
    }

    Ok(tokens)
}

/// Pairs of mutually exclusive attributes.
const CONFLICT_PAIRS: &[(&str, &str)] = &[
    ("inline", "noinline"),
    ("reducible", "irreducible"),
    ("specialize", "nospecialize"),
    ("inline", "macro_inline"),
    ("always_inline", "noinline"),
    ("scoped", "local"),
];

fn valid_decl_kinds(attr_name: &str) -> Option<&'static [DeclKind]> {
    match attr_name {
        "simp" | "congr" | "ext" | "refl" | "symm" => {
            static K: &[DeclKind] = &[DeclKind::Theorem, DeclKind::Definition, DeclKind::Abbrev];
            Some(K)
        }
        "instance" | "default_instance" => {
            static K: &[DeclKind] = &[DeclKind::Instance, DeclKind::Definition, DeclKind::Abbrev];
            Some(K)
        }
        "class" => {
            static K: &[DeclKind] = &[DeclKind::Structure, DeclKind::Inductive];
            Some(K)
        }
        "init" => {
            static K: &[DeclKind] = &[DeclKind::Definition];
            Some(K)
        }
        _ => None,
    }
}

/// Check whether an attribute is valid for a given declaration kind.
pub(crate) fn validate_attribute_for_decl(
    attr_name: &str,
    decl_kind: DeclKind,
) -> Result<(), ElabError> {
    if let Some(allowed) = valid_decl_kinds(attr_name) {
        if !allowed.contains(&decl_kind) {
            return Err(ElabError::Unsupported {
                feature: format!("@[{attr_name}] cannot be applied to {decl_kind:?} declarations"),
            });
        }
    }
    Ok(())
}

/// Returns whether a file-scope `attribute [-attr] decl` command can remove
/// the given attribute from the current environment.
#[must_use]
pub(crate) fn supports_file_scope_attribute_removal(attr_name: &str) -> bool {
    matches!(attr_name, "simp")
}

/// Detect conflicts among a set of attributes. Returns first conflicting pair.
#[must_use]
pub(crate) fn detect_conflicts(attr_names: &[&str]) -> Option<(&'static str, &'static str)> {
    let set: HashSet<&str> = attr_names.iter().copied().collect();
    for &(a, b) in CONFLICT_PAIRS {
        if set.contains(a) && set.contains(b) {
            return Some((a, b));
        }
    }
    None
}

/// Scope qualifier for an extended attribute.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum Ext2Scope {
    Global,
    Scoped(Name),
    Local,
}

/// A user-defined attribute handler callback.
pub(crate) type CustomAttrHandler =
    Box<dyn Fn(&Name, &[String]) -> Result<(), String> + Send + Sync>;

/// A registered custom attribute.
pub(crate) struct CustomAttrDecl {
    pub(crate) name: String,
    pub(crate) description: String,
    pub(crate) handler: Option<CustomAttrHandler>,
}

impl std::fmt::Debug for CustomAttrDecl {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CustomAttrDecl")
            .field("name", &self.name)
            .field("description", &self.description)
            .field("handler", &self.handler.as_ref().map(|_| "<fn>"))
            .finish()
    }
}

/// A record of an attribute applied to a declaration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct AppliedAttribute {
    pub(crate) attr_name: String,
    pub(crate) decl_name: Name,
    pub(crate) args: Vec<String>,
    pub(crate) scope: Ext2Scope,
}

/// Collected statistics about attribute operations.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct AttributeStats {
    pub(crate) applied_by_kind: HashMap<String, u64>,
    pub(crate) conflicts_detected: u64,
    pub(crate) removals_processed: u64,
    pub(crate) custom_registered: u64,
    pub(crate) inherited: u64,
}

/// Extended attribute manager: parsing, validation, scoping, inheritance,
/// removal, custom registration, and statistics.
pub(crate) struct ExtendedAttributeManager {
    applied: HashMap<Name, Vec<AppliedAttribute>>,
    custom_attrs: HashMap<String, CustomAttrDecl>,
    parent_map: HashMap<Name, Name>,
    stats: AttributeStats,
}

impl std::fmt::Debug for ExtendedAttributeManager {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ExtendedAttributeManager")
            .field(
                "applied_count",
                &self.applied.values().map(Vec::len).sum::<usize>(),
            )
            .field("custom_attrs", &self.custom_attrs.len())
            .field("stats", &self.stats)
            .finish()
    }
}

impl Default for ExtendedAttributeManager {
    fn default() -> Self {
        Self::new()
    }
}

impl ExtendedAttributeManager {
    #[must_use]
    pub(crate) fn new() -> Self {
        Self {
            applied: HashMap::new(),
            custom_attrs: HashMap::new(),
            parent_map: HashMap::new(),
            stats: AttributeStats::default(),
        }
    }

    /// Apply an attribute to a declaration. Checks for conflicts.
    pub(crate) fn apply_attribute(&mut self, attr: AppliedAttribute) -> Result<(), ElabError> {
        let decl_entries = self.applied.entry(attr.decl_name.clone()).or_default();
        let existing: Vec<&str> = decl_entries.iter().map(|a| a.attr_name.as_str()).collect();
        let mut check = existing.clone();
        check.push(&attr.attr_name);
        if let Some((a, b)) = detect_conflicts(&check) {
            self.stats.conflicts_detected += 1;
            return Err(ElabError::Unsupported {
                feature: format!(
                    "@[{a}] and @[{b}] are mutually exclusive on '{}'",
                    attr.decl_name
                ),
            });
        }
        *self
            .stats
            .applied_by_kind
            .entry(attr.attr_name.clone())
            .or_default() += 1;
        decl_entries.push(attr);
        Ok(())
    }

    /// Remove a previously applied attribute (`attribute [-simp]`).
    pub(crate) fn remove_attribute(
        &mut self,
        decl_name: &Name,
        attr_name: &str,
    ) -> Result<(), ElabError> {
        let entries = self
            .applied
            .get_mut(decl_name)
            .ok_or_else(|| ElabError::Unsupported {
                feature: format!("cannot remove @[{attr_name}]: no attributes on '{decl_name}'"),
            })?;
        let before = entries.len();
        entries.retain(|a| a.attr_name != attr_name);
        if entries.len() == before {
            return Err(ElabError::Unsupported {
                feature: format!("cannot remove @[{attr_name}]: not applied to '{decl_name}'"),
            });
        }
        self.stats.removals_processed += 1;
        Ok(())
    }

    #[must_use]
    pub(crate) fn has_attribute(&self, decl_name: &Name, attr_name: &str) -> bool {
        self.applied
            .get(decl_name)
            .is_some_and(|entries| entries.iter().any(|a| a.attr_name == attr_name))
    }

    #[must_use]
    pub(crate) fn get_attributes(&self, decl_name: &Name) -> &[AppliedAttribute] {
        self.applied.get(decl_name).map_or(&[], Vec::as_slice)
    }

    /// Get attributes on a declaration filtered by scope.
    #[must_use]
    pub(crate) fn get_scoped_attributes(
        &self,
        decl_name: &Name,
        scope: &Ext2Scope,
    ) -> Vec<&AppliedAttribute> {
        self.applied.get(decl_name).map_or_else(Vec::new, |es| {
            es.iter().filter(|a| &a.scope == scope).collect()
        })
    }

    #[must_use]
    pub(crate) fn total_entries(&self) -> usize {
        self.applied.values().map(Vec::len).sum()
    }

    #[must_use]
    pub(crate) fn declaration_count(&self) -> usize {
        self.applied.len()
    }

    /// Register a custom (user-defined) attribute.
    pub(crate) fn register_custom_attribute(
        &mut self,
        name: &str,
        description: &str,
        handler: Option<CustomAttrHandler>,
    ) -> Result<(), ElabError> {
        if self.custom_attrs.contains_key(name) {
            return Err(ElabError::Unsupported {
                feature: format!("custom attribute '{name}' is already registered"),
            });
        }
        self.custom_attrs.insert(
            name.to_owned(),
            CustomAttrDecl {
                name: name.to_owned(),
                description: description.to_owned(),
                handler,
            },
        );
        self.stats.custom_registered += 1;
        Ok(())
    }

    #[must_use]
    pub(crate) fn is_custom_registered(&self, name: &str) -> bool {
        self.custom_attrs.contains_key(name)
    }

    /// Invoke a custom attribute handler.
    pub(crate) fn invoke_custom_handler(
        &self,
        attr_name: &str,
        decl_name: &Name,
        args: &[String],
    ) -> Result<(), ElabError> {
        let decl = self
            .custom_attrs
            .get(attr_name)
            .ok_or_else(|| ElabError::UnknownIdent(format!("custom attribute '{attr_name}'")))?;
        if let Some(handler) = &decl.handler {
            handler(decl_name, args).map_err(|msg| ElabError::Unsupported {
                feature: format!("custom attribute '{attr_name}' handler failed: {msg}"),
            })?;
        }
        Ok(())
    }

    /// Register a parent-child structure relationship for inheritance.
    pub(crate) fn register_parent(&mut self, child: Name, parent: Name) {
        self.parent_map.insert(child, parent);
    }

    /// Inherit attributes from parent. Skips existing and conflicting attrs.
    /// Returns the number of attributes inherited.
    pub(crate) fn inherit_from_parent(&mut self, child: &Name) -> usize {
        let parent = match self.parent_map.get(child) {
            Some(p) => p.clone(),
            None => return 0,
        };
        let parent_attrs: Vec<AppliedAttribute> =
            self.applied.get(&parent).cloned().unwrap_or_default();
        let mut count = 0;
        for pa in parent_attrs {
            if self.has_attribute(child, &pa.attr_name) {
                continue;
            }
            let inherited = AppliedAttribute {
                attr_name: pa.attr_name.clone(),
                decl_name: child.clone(),
                args: pa.args.clone(),
                scope: pa.scope.clone(),
            };
            if self.apply_attribute(inherited).is_ok() {
                count += 1;
                self.stats.inherited += 1;
            }
        }
        count
    }

    #[must_use]
    pub(crate) fn stats(&self) -> &AttributeStats {
        &self.stats
    }

    pub(crate) fn reset_stats(&mut self) {
        self.stats = AttributeStats::default();
    }
}

/// Parse a `@[priority N]` argument.
pub(crate) fn parse_priority_arg(args: &[String]) -> Result<u32, ElabError> {
    let s = args.first().ok_or_else(|| {
        ElabError::ParseError("@[priority] requires a numeric argument".to_owned())
    })?;
    s.parse::<u32>()
        .map_err(|_| ElabError::ParseError(format!("@[priority] expected integer, got '{s}'")))
}

/// Parse a `@[deprecated "msg"]` argument. Returns empty string if missing.
#[must_use]
pub(crate) fn parse_deprecated_arg(args: &[String]) -> String {
    args.first().cloned().unwrap_or_default()
}

/// Parse an `@[extern "abi"]` argument.
pub(crate) fn parse_extern_arg(args: &[String]) -> Result<String, ElabError> {
    args.first()
        .cloned()
        .ok_or_else(|| ElabError::ParseError("@[extern] requires an ABI name argument".to_owned()))
}
